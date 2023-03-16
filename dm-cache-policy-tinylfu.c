#include "dm-cache-background-tracker.h"
#include "dm-cache-policy-internal.h"
#include "dm-cache-policy.h"
#include "dm.h"

#include <linux/hash.h>
#include <linux/xxhash.h>
#include <linux/jiffies.h>
#include <linux/module.h>
#include <linux/mutex.h>
#include <linux/vmalloc.h>
#include <linux/math64.h>

#define DM_MSG_PREFIX "cache-policy-tinylfu"

#define NULL_ENTRY_IDX ((1<<28) - 1)
struct entry {
	unsigned int next:28;
	unsigned int prev:28;
	unsigned int hash_next:28;
	bool dirty:1;
	bool allocated:1;
	bool pending_work:1;

	dm_oblock_t oblock;
};

static void init_entry(struct entry *e) {
	if (!e)
		return ;

	e->next = NULL_ENTRY_IDX;
	e->prev = NULL_ENTRY_IDX;
	e->hash_next = NULL_ENTRY_IDX;
	e->dirty = false;
	e->allocated = true;
	e->pending_work = false;
	e->oblock = 0;
}

static void clear_pending(struct entry *e) {
	BUG_ON(!e->allocated);
	BUG_ON(!e->pending_work);

	e->pending_work = false;
}

static void set_pending(struct entry *e) {
	BUG_ON(!e->allocated);
	BUG_ON(e->pending_work);

	e->pending_work = true;
}

struct entry_space {
	struct entry *begin;
	struct entry *end;
};

static int space_init(struct entry_space *es, unsigned int nr_entries)
{
	if (nr_entries == 0) {
		es->begin = es->end = NULL;
		return 0;
	}

	es->begin = vzalloc(array_size(nr_entries, sizeof(struct entry)));
	if (!es->begin) {
		return -ENOMEM;
	}

	es->end = es->begin + nr_entries;
	return 0;
}

static void space_destroy(struct entry_space *es)
{
	kvfree(es->begin);
}

static struct entry *idx_to_entry(struct entry_space *es, unsigned int block)
{
	struct entry *e;

	if (block == NULL_ENTRY_IDX)
		return NULL;

	e = es->begin + block;
	BUG_ON(e >= es->end);

	return e;
}

static unsigned int entry_to_idx(struct entry_space *es, struct entry *e)
{
	BUG_ON(e < es->begin || e >= es->end);

	return (e - es->begin);
}

struct ilist {
	unsigned int head;
	unsigned int tail;
	unsigned int nr_elts;
};

static void ilist_init(struct ilist *list)
{
	list->head = list->tail = NULL_ENTRY_IDX;
	list->nr_elts = 0;
}

static struct entry *l_tail(struct entry_space *es, struct ilist *l)
{
	return idx_to_entry(es, l->tail);
}

static struct entry *l_head(struct entry_space *es, struct ilist *l)
{
	return idx_to_entry(es, l->head);
}

static struct entry *l_next(struct entry_space *es, struct entry *e)
{
	return idx_to_entry(es, e->next);
}

static struct entry *l_prev(struct entry_space *es, struct entry *e)
{
	return idx_to_entry(es, e->prev);
}

static bool l_empty(struct ilist *l)
{
	return l->head == NULL_ENTRY_IDX;
}

static void l_add_head(struct entry_space *es, struct ilist *l, struct entry *e)
{
	struct entry *head = l_head(es, l);

	e->next = l->head;
	e->prev = NULL_ENTRY_IDX;

	if (head)
		head->prev = l->head = entry_to_idx(es, e);
	else
		l->head = l->tail = entry_to_idx(es, e);

	l->nr_elts++;
}

static void l_add_tail(struct entry_space *es, struct ilist *l, struct entry *e)
{
	struct entry *tail = l_tail(es, l);

	e->next = NULL_ENTRY_IDX;
	e->prev = l->tail;

	if (tail)
		tail->next = l->tail = entry_to_idx(es, e);
	else
		l->head = l->tail = entry_to_idx(es, e);

	l->nr_elts++;
}

static void l_del(struct entry_space *es, struct ilist *l, struct entry *e)
{
	struct entry *prev = l_prev(es, e);
	struct entry *next = l_next(es, e);

	if (prev)
		prev->next = e->next;
	else
		l->head = e->next;

	if (next)
		next->prev = e->prev;
	else
		l->tail = e->prev;

	l->nr_elts--;
}

static struct entry *l_pop_head(struct entry_space *es, struct ilist *l)
{
	struct entry *e;

	for (e = l_head(es, l); e; e = l_next(es, e)) {
		l_del(es, l, e);
		return e;
	}

	return NULL;
}

static struct entry *l_pop_tail(struct entry_space *es, struct ilist *l)
{
	struct entry *e;

	for (e = l_tail(es, l); e; e = l_prev(es, e)) {
		l_del(es, l, e);
		return e;
	}

	return NULL;
}

static void l_move_front(struct entry_space *es, struct ilist *l, struct entry *e)
{
	l_del(es, l, e);
	l_add_head(es, l, e);
}

/*----------------------------------------------------------------*/

struct entry_alloc {
	struct entry_space *es;
	unsigned int nr_allocated;
	struct ilist free;
};

static void entry_alloc_init(struct entry_alloc *ea, struct entry_space *es,
			     unsigned int begin, unsigned int size)
{
	struct entry *e;

	if (!es)
		return;
	ea->es = es;
	for (e = ea->es->begin + begin; e != ea->es->begin + begin + size; e++) {
		l_add_tail(ea->es, &ea->free, e);
	}
}

static struct entry *alloc_get_entry_at(struct entry_alloc *ea, unsigned int block)
{
	struct entry *e = ea->es->begin + block;

	BUG_ON(e >= ea->es->end);

	return e;
}

static struct entry *alloc_get_entry(struct entry_alloc *ea)
{
	struct entry *e = l_pop_tail(ea->es, &ea->free);
	
	BUG_ON(e >= ea->es->end);
	BUG_ON(e->allocated);

	if (!e)
		return NULL;

	init_entry(e);
	ea->nr_allocated++;

	return e;
}

static void free_entry(struct entry_alloc *ea, struct entry *e)
{
	BUG_ON(!e->allocated);
	BUG_ON(!ea->nr_allocated);

	e->allocated = false;
	ea->nr_allocated--;
	l_add_tail(ea->es, &ea->free, e);
}

static dm_cblock_t infer_cblock(struct entry_alloc *ea, struct entry *e)
{
	return to_cblock(entry_to_idx(ea->es, e));
}

/*----------------------------------------------------------------*/

struct tinylfu_hash_table {
	struct entry_space *es;
	unsigned int *buckets;
	unsigned int nr_bucket;
	unsigned long long hash_bits;
};

static int h_init(struct tinylfu_hash_table *ht, struct entry_space *es, unsigned int nr_entries)
{
	unsigned int i, nr_buckets;

	ht->es = es;
	nr_buckets = roundup_pow_of_two(max(nr_entries / 4u, 16u));
	ht->hash_bits = __ffs(nr_buckets);

	ht->buckets = vmalloc(array_size(nr_buckets, sizeof(*ht->buckets)));
	if (!ht->buckets)
		return -ENOMEM;

	for (i = 0; i < nr_buckets; i++)
		ht->buckets[i] = NULL_ENTRY_IDX;

	return 0;
}

static void h_exit(struct tinylfu_hash_table *ht)
{
	vfree(ht->buckets);
}

static struct entry *h_head(struct tinylfu_hash_table *ht, unsigned int bucket)
{
	return idx_to_entry(ht->es, ht->buckets[bucket]);
}

static struct entry *h_next(struct tinylfu_hash_table *ht, struct entry *e)
{
	return idx_to_entry(ht->es, e->hash_next);
}

static void __h_insert(struct tinylfu_hash_table *ht, unsigned int bucket, struct entry *e)
{
	e->hash_next = ht->buckets[bucket];
	ht->buckets[bucket] = entry_to_idx(ht->es, e);
}

static void h_insert(struct tinylfu_hash_table *ht, struct entry *e)
{
	unsigned int h = hash_64(from_oblock(e->oblock), ht->hash_bits);

	__h_insert(ht, h, e);
}

static struct entry *__h_lookup(struct tinylfu_hash_table *ht, unsigned int h, dm_oblock_t oblock,
				struct entry **prev)
{
	struct entry *e;

	*prev = NULL;
	for (e = h_head(ht, h); e; e = h_next(ht, e)) {
		if (e->oblock == oblock)
			return e;

		*prev = e;
	}

	return NULL;
}

static void __h_unlink(struct tinylfu_hash_table *ht, unsigned int h,
		       struct entry *e, struct entry *prev)
{
	if (prev)
		prev->hash_next = e->hash_next;
	else
		ht->buckets[h] = e->hash_next;
}

/*
 * Also moves each entry to the front of the bucket.
 */
static struct entry *h_lookup(struct tinylfu_hash_table *ht, dm_oblock_t oblock)
{
	struct entry *e, *prev;
	unsigned int h = hash_64(from_oblock(oblock), ht->hash_bits);

	e = __h_lookup(ht, h, oblock, &prev);
	if (e && prev) {
		/*
		 * Move to the front because this entry is likely
		 * to be hit again.
		 */
		__h_unlink(ht, h, e, prev);
		__h_insert(ht, h, e);
	}

	return e;
}

static void h_remove(struct tinylfu_hash_table *ht, struct entry *e)
{
	unsigned int h = hash_64(from_oblock(e->oblock), ht->hash_bits);
	struct entry *prev;

	/*
	 * The down side of using a singly linked list is we have to
	 * iterate the bucket to remove an item.
	 */
	e = __h_lookup(ht, h, e->oblock, &prev);
	if (e)
		__h_unlink(ht, h, e, prev);
}

/* Count-Min sketch ------------------------------------------------*/

static unsigned long seed_hash(unsigned long value, unsigned long seed)
{
	return xxhash(&value, sizeof(value), seed);
}

struct cm4 {                                                                       
	// 4bit x 4counters x roundup_pow2(size)                                   
	uint16_t *table;                                                           
	size_t table_length;                                                       
	unsigned long table_mask;                                                  
	unsigned long sample;                                                      
	unsigned long w;                                                           
};

// The sample size is considered to be safe to be (size) * (max counter value)
static struct cm4 *cm4_create(size_t size, unsigned long sample)
{
	size_t length = roundup_pow_of_two(size);
	struct cm4 *sketch = kmalloc(sizeof(struct cm4), GFP_KERNEL);

	if (!sketch)
		return NULL;

	sketch->sample = sample;
	sketch->w = 0;
	sketch->table_length = length;
	sketch->table_mask = length - 1;
	sketch->table = vmalloc(array_size(length, sizeof(uint16_t)));
	if (!sketch->table)
		goto bad_table_alloc;

	return sketch;
bad_table_alloc:
	kvfree(sketch);
	return NULL;
}

static void cm4_destroy(struct cm4 *sketch)
{
	kvfree(sketch->table);
	kvfree(sketch);
}

static bool cm4_try_reset(struct cm4 *sketch)
{
	int i;
	if (sketch->w < sketch->sample)
		return false;

	for (i = 0; i < sketch->table_length; i++)
		sketch->table[i] = (sketch->table[i] >> 1) & 0x7777;

	sketch->w = 0;
	return true;
}

static bool cm4_inc(struct cm4 *sketch, unsigned long x)
{
	int i;
	unsigned long h;
	unsigned long val;
	unsigned long val_mask;

	sketch->w++;
	for (i = 0; i < 4; i++) {
		val_mask = (0xFF << (i*4));
		h = seed_hash(x, i) & sketch->table_mask;
		val = (sketch->table[h] >> (i*4)) & 0xFF;
		val = val == 15 ? 15 : (val + 1);
		sketch->table[h] = (sketch->table[h] & (~val_mask)) |
				   (val << (i*4));
	}

	return cm4_try_reset(sketch);
}

static unsigned int cm4_estimate(struct cm4 *sketch, unsigned long x)
{
	int i;
	unsigned long h;
	unsigned long val;
	unsigned long min_val;

	sketch->w++;
	min_val = 16;
	for (i = 0; i < 4; i++) {
		h = seed_hash(x, i) & sketch->table_mask;
		val = (sketch->table[h] >> (i*4)) & 0xFF;
		if (val < min_val)
			min_val = val;
	}

	return min_val;
}

struct doorkeeper {
	unsigned long *filter;
	size_t size;
};

static struct doorkeeper *dk_create(size_t size)
{
	size_t length = roundup_pow_of_two(10*size);
	struct doorkeeper *dk = kmalloc(sizeof(struct doorkeeper), GFP_KERNEL);

	if (!dk)
		return NULL;

	dk->size = length;
	dk->filter = alloc_bitset(length);
	if (!dk->filter)
		goto bad_filter_alloc;

	return dk;
bad_filter_alloc:
	kvfree(dk);
	return NULL;
}

static void dk_destroy(struct doorkeeper *dk)
{
	kvfree(dk->filter);
	kvfree(dk);
}

static bool dk_allow(struct doorkeeper *dk, unsigned long x)
{
	int i;
	unsigned long h;
	bool r = true;

	for (i = 0; i < 4; i++) {
		h = seed_hash(x, i) & (dk->size-1);
		r &= test_and_set_bit(h, dk->filter);
	}
	return r;
}

static void dk_reset(struct doorkeeper *dk)
{
	int i;
	int length = (dk->size >> 3) + 1;

	for (i = 0; i < length; i++) {
		dk->filter[i] = 0;
	}
}

/*----------------------------------------------------------------*/

struct tinylfu_stats {
	unsigned long long hit;
	unsigned long long miss;
};

static void tinylfu_stats_init(struct tinylfu_stats *s)
{
	BUG_ON(!s);

	s->hit = 0;
	s->miss = 0;
}

static void tinylfu_stats_hit(struct tinylfu_stats *s)
{
	if (!s)
		return ;
	s->hit++;
}

static void tinylfu_stats_miss(struct tinylfu_stats *s)
{
	if (!s)
		return ;
	s->miss++;
}

/*----------------------------------------------------------------*/

struct tinylfu_policy {
	struct dm_cache_policy policy;
	spinlock_t lock;
	struct tinylfu_hash_table htable;
	struct tinylfu_stats stats;

	struct entry_space es;
	struct entry_alloc cache_alloc;
	struct entry_alloc backlog_alloc;

	struct cm4 *sketch;
	struct doorkeeper *dk;
	struct ilist lru;
	struct ilist dirty;
	struct ilist promotion_backlog;
	unsigned int nr_dirty;
	dm_cblock_t cache_size;
	sector_t cache_block_size;

	bool migration_allowed;
	struct background_tracker *bg_work;
};

static struct tinylfu_policy *to_tinylfu_policy(struct dm_cache_policy *p) {
	return container_of(p, struct tinylfu_policy, policy);
}

static void tinylfu_destroy(struct dm_cache_policy *p)
{
	//TODO: destroy everything
}

static void tinylfu_remove_entry(struct tinylfu_policy *lfu, struct entry *e)
{
	if (e->dirty)
		l_del(lfu->cache_alloc.es, &lfu->dirty, e);
	else
		l_del(lfu->cache_alloc.es, &lfu->lru, e);
}

static void tinylfu_push_entry(struct tinylfu_policy *lfu, struct entry *e)
{
	l_add_head(lfu->cache_alloc.es, (e->dirty ? (&lfu->dirty) : (&lfu->lru)), e);
}

/*----------------------------------------------------------------*/

static bool try_promotion(struct tinylfu_policy *lfu, dm_oblock_t oblock,
			  bool must_alloc)
{
	int r;
	struct entry *e;
	struct policy_work work;

	if (!lfu->migration_allowed)
		return false;

	e = alloc_get_entry(&lfu->cache_alloc);
	if (!e) {
		BUG_ON(must_alloc);
		return false;
	}

	set_pending(e);

	work.op = POLICY_PROMOTE;
	work.oblock = oblock;
	work.cblock = infer_cblock(&lfu->cache_alloc, e);
	r = btracker_queue(lfu->bg_work, &work, NULL);

	if (r) {
		free_entry(&lfu->cache_alloc, e);
		return false;
	}

	return true;
}

static bool enqueue_eviction(struct tinylfu_policy *lfu, struct entry *victim,
			     dm_oblock_t replacement)
{
	int r;
	struct entry *e;
	struct policy_work work;

	if (!lfu->migration_allowed)
		return false;

	// We want to add the replacement into backlog and demote the victim
	// first, once the work done then we queue the promotion from the
	// backlog list.
	e = alloc_get_entry(&lfu->backlog_alloc);
	if (!e)
		return false;
	
	e->oblock = replacement;
	l_add_tail(lfu->backlog_alloc.es, &lfu->promotion_backlog, e);

	set_pending(victim);
	work.op = POLICY_DEMOTE;
	work.cblock = infer_cblock(&lfu->cache_alloc, victim);
	work.oblock = victim->oblock;
	tinylfu_remove_entry(lfu, victim);

	r = btracker_queue(lfu->bg_work, &work, NULL);
	if (r) {
		clear_pending(victim);
		tinylfu_push_entry(lfu, victim);
		l_del(lfu->backlog_alloc.es, &lfu->promotion_backlog, e);
		free_entry(&lfu->backlog_alloc, e);
		return false;
	}
	return true;
}

static void promote_backlog(struct tinylfu_policy *lfu)
{
	struct entry *e = l_head(lfu->backlog_alloc.es,
				&lfu->promotion_backlog);

	try_promotion(lfu, e->oblock, true);

	l_del(lfu->backlog_alloc.es, &lfu->promotion_backlog, e);
	free_entry(&lfu->backlog_alloc, e);
}

static void enqueue_writeback(struct tinylfu_policy *lfu, bool idle)
{
	int r;
	struct policy_work work;
	struct entry *e;

	e = l_head(lfu->cache_alloc.es, &lfu->dirty);
	if (!e)
		return ;

	set_pending(e);
	l_del(lfu->cache_alloc.es, &lfu->dirty, e);

	work.op = POLICY_WRITEBACK;
	work.cblock = infer_cblock(&lfu->cache_alloc, e);
	work.oblock = e->oblock;
	r = btracker_queue(lfu->bg_work, &work, NULL);	
	if (r) {
		clear_pending(e);
		l_add_head(lfu->cache_alloc.es, &lfu->dirty, e);
	}
}

static void complete_background_work_(struct tinylfu_policy *lfu,
				      struct policy_work *work, bool success)
{
	struct entry *e = alloc_get_entry_at(&lfu->cache_alloc,
					     from_cblock(work->cblock));

	switch(work->op) {
	case POLICY_PROMOTE:
		clear_pending(e);
		if (success) {
			e->oblock = work->oblock;
			l_add_head(lfu->cache_alloc.es, &lfu->lru, e);
			h_insert(&lfu->htable, e);
		} else {
			free_entry(&lfu->cache_alloc, e);
		}
		break;

	case POLICY_DEMOTE:
		if (success) {
			h_remove(&lfu->htable, e);
			free_entry(&lfu->cache_alloc, e);
			promote_backlog(lfu);
		} else {
			clear_pending(e);
			l_add_head(lfu->cache_alloc.es, &lfu->lru, e);
		}
		break;

	case POLICY_WRITEBACK:
		clear_pending(e);
		l_add_head(lfu->cache_alloc.es, &lfu->lru, e);
		break;
	}

	btracker_complete(lfu->bg_work, work);
}

/*----------------------------------------------------------------*/

static void tinylfu_update_hit_(struct tinylfu_policy *lfu, struct entry *e)
{
	bool need_reset;

	l_move_front(lfu->cache_alloc.es, &lfu->lru, e);

	need_reset = cm4_inc(lfu->sketch, e->oblock);
	if (need_reset)
		dk_reset(lfu->dk);
}

static bool tinylfu_update_miss_(struct tinylfu_policy *lfu,
				 dm_oblock_t oblock)
{
	bool r = false;
	bool allow;
	bool need_reset;
	unsigned long victim_cnt, new_cnt;
	struct entry *victim;

	allow = dk_allow(lfu->dk, oblock);

	need_reset = cm4_inc(lfu->sketch, oblock);
	if (need_reset)
		dk_reset(lfu->dk);

	if (allow) {
		if (try_promotion(lfu, oblock, false)) {
			return true;
		}

		victim = l_tail(lfu->cache_alloc.es, &lfu->lru);
		if (victim) {
			victim_cnt = cm4_estimate(lfu->sketch,
						from_oblock(victim->oblock));
			new_cnt = cm4_estimate(lfu->sketch,
						from_oblock(oblock));
			if (new_cnt > victim_cnt) {
				r = enqueue_eviction(lfu, victim, oblock);
			}
		}
	}
	return r;
}

static int tinylfu_lookup(struct dm_cache_policy *p, dm_oblock_t oblock,
			  dm_cblock_t *cblock, int data_dir, bool fast_copy,
			  bool *background_queued)
{
	struct tinylfu_policy *lfu = to_tinylfu_policy(p);
	struct entry *e;
	int ret;
	unsigned long flags;

	spin_lock_irqsave(&lfu->lock, flags);
	*background_queued = false;
	e = h_lookup(&lfu->htable, oblock);
	if (e) {
		tinylfu_stats_hit(&lfu->stats);

		tinylfu_update_hit_(lfu, e);
		*cblock = infer_cblock(&lfu->cache_alloc, e);
		ret = 0;
	} else {
		tinylfu_stats_miss(&lfu->stats);

		*background_queued = tinylfu_update_miss_(lfu, oblock);
		ret = -ENOENT;
	}
	spin_unlock_irqrestore(&lfu->lock, flags);

	return ret;
}

static int tinylfu_get_background_work(struct dm_cache_policy *p, bool idle,
				       struct policy_work **result)
{
	int r;
	unsigned long flags;
	struct tinylfu_policy *lfu = to_tinylfu_policy(p);

	spin_lock_irqsave(&lfu->lock, flags);
	r = btracker_issue(lfu->bg_work, result);
	if (r == -ENODATA) {
		if (idle && lfu->nr_dirty > 0) {
			enqueue_writeback(lfu, idle);
			r = btracker_issue(lfu->bg_work, result);
		}
	}
	spin_unlock_irqrestore(&lfu->lock, flags);

	return r;
}

static void tinylfu_complete_background_work(struct dm_cache_policy *p,
					     struct policy_work *work,
					     bool success)
{
	unsigned long flags;
	struct tinylfu_policy *lfu = to_tinylfu_policy(p);

	spin_lock_irqsave(&lfu->lock, flags);
	complete_background_work_(lfu, work, success);
	spin_unlock_irqrestore(&lfu->lock, flags);
}

static void tinylfu_set_dirty_(struct tinylfu_policy *lfu, dm_cblock_t cblock,
			       bool dirty)
{
	struct entry *e = alloc_get_entry_at(&lfu->cache_alloc,
					     from_cblock(cblock));

	BUG_ON(!e->allocated);
	if (e->pending_work) {
		e->dirty = dirty;
	} else {
		tinylfu_remove_entry(lfu, e);
		e->dirty = dirty;
		tinylfu_push_entry(lfu, e);
	}
}

static void tinylfu_set_dirty(struct dm_cache_policy *p, dm_cblock_t cblock)
{
	unsigned long flags;
	struct tinylfu_policy *lfu = to_tinylfu_policy(p);

	spin_lock_irqsave(&lfu->lock, flags);
	tinylfu_set_dirty_(lfu, cblock, true);
	spin_unlock_irqrestore(&lfu->lock, flags);
}

static void tinylfu_clear_dirty(struct dm_cache_policy *p, dm_cblock_t cblock)
{
	unsigned long flags;
	struct tinylfu_policy *lfu = to_tinylfu_policy(p);

	spin_lock_irqsave(&lfu->lock, flags);
	tinylfu_set_dirty_(lfu, cblock, true);
	spin_unlock_irqrestore(&lfu->lock, flags);
}

static int tinylfu_load_mapping(struct dm_cache_policy *p, dm_oblock_t oblock,
				dm_cblock_t cblock, bool dirty,
				uint32_t hint, bool hint_valid)
{
	unsigned long flags;
	struct tinylfu_policy *lfu = to_tinylfu_policy(p);
	struct entry *e = alloc_get_entry_at(&lfu->cache_alloc,
					     from_cblock(cblock));

	spin_lock_irqsave(&lfu->lock, flags);
	init_entry(e);
	e->oblock = oblock;
	e->dirty = dirty;
	h_insert(&lfu->htable, e);
	spin_unlock_irqrestore(&lfu->lock, flags);

	return 0;
}

static int tinylfu_invalidate_mapping(struct dm_cache_policy *p, dm_cblock_t cblock)
{
	struct tinylfu_policy *lfu = to_tinylfu_policy(p);
	struct entry *e = alloc_get_entry_at(&lfu->cache_alloc, from_cblock(cblock));

	if (!e->allocated)
		return -ENODATA;

	tinylfu_remove_entry(lfu, e);
	h_remove(&lfu->htable, e);
	free_entry(&lfu->cache_alloc, e);

	return 0;
}

static uint32_t tinylfu_get_hint(struct dm_cache_policy *p, dm_cblock_t cblock)
{
	return 0;
}

static dm_cblock_t tinylfu_residency(struct dm_cache_policy *p)
{
	unsigned long flags;
	struct tinylfu_policy *lfu = to_tinylfu_policy(p);
	dm_cblock_t ret = 0;

	spin_lock_irqsave(&lfu->lock, flags);
	ret = to_cblock(lfu->cache_alloc.nr_allocated);
	spin_unlock_irqrestore(&lfu->lock, flags);

	return ret;
}

static void tinylfu_tick(struct dm_cache_policy *p, bool can_block)
{
}

static int tinylfu_emit_config_values(struct dm_cache_policy *p, char *result,
				      unsigned maxlen, ssize_t *sz_ptr)
{
	return 0;
}

static int tinylfu_set_config_value(struct dm_cache_policy *p,
				    const char *key, const char *value)
{
	return 0;
}

static void tinylfu_allow_migrations(struct dm_cache_policy *p, bool allow)
{
	unsigned long flags;
	struct tinylfu_policy *lfu = to_tinylfu_policy(p);

	spin_lock_irqsave(&lfu->lock, flags);
	lfu->migration_allowed = allow;
	spin_unlock_irqrestore(&lfu->lock, flags);
}

static void init_policy_functions(struct tinylfu_policy *lfu)
{
	lfu->policy.destroy = tinylfu_destroy;
	lfu->policy.lookup = tinylfu_lookup;
	lfu->policy.get_background_work = tinylfu_get_background_work;
	lfu->policy.complete_background_work = tinylfu_complete_background_work;
	lfu->policy.set_dirty = tinylfu_set_dirty;
	lfu->policy.clear_dirty = tinylfu_clear_dirty;
	lfu->policy.load_mapping = tinylfu_load_mapping;
	lfu->policy.invalidate_mapping = tinylfu_invalidate_mapping;
	lfu->policy.get_hint = tinylfu_get_hint;
	lfu->policy.residency = tinylfu_residency;
	lfu->policy.tick = tinylfu_tick;
	lfu->policy.emit_config_values = tinylfu_emit_config_values;
	lfu->policy.set_config_value = tinylfu_set_config_value;
	lfu->policy.allow_migrations = tinylfu_allow_migrations;

}

static struct dm_cache_policy *tinylfu_create(dm_cblock_t cache_size,
					      sector_t origin_size,
                                              sector_t cache_block_size)
{
	int r;
	struct tinylfu_policy *lfu = kzalloc(sizeof(struct tinylfu_policy), GFP_KERNEL);
	if(!lfu) {
		return NULL;
	}
	init_policy_functions(lfu);
	lfu->cache_size = cache_size;
	lfu->cache_block_size = cache_block_size;
	r = space_init(&lfu->es, from_cblock(cache_size) +
		      ((from_cblock(cache_size) >> 2)));
	if (r) {
		DMERR("err initialize entry space");
		goto bad_pool_init;
	}

	entry_alloc_init(&lfu->cache_alloc, &lfu->es, 0, from_cblock(cache_size));
	entry_alloc_init(&lfu->backlog_alloc, &lfu->es, from_cblock(cache_size),
			from_cblock(cache_size) >> 2);

	lfu->sketch = cm4_create(from_cblock(cache_size), 15 * from_cblock(cache_size));
	if (!lfu->sketch) {
		DMERR("err allocating CountMin sketch");
		goto bad_cm4_alloc;
	}
	lfu->dk = dk_create(from_cblock(cache_size));
	if (!lfu->dk) {
		DMERR("err allocating Doorkeeper");
		goto bad_dk_alloc;
	}

	r = h_init(&lfu->htable, &lfu->es, from_cblock(cache_size));
	if (r) {
		DMERR("hash table allocation failed");
		goto bad_htable_alloc;
	}

	ilist_init(&lfu->lru);
	ilist_init(&lfu->promotion_backlog);
	
	tinylfu_stats_init(&lfu->stats);

	spin_lock_init(&lfu->lock);
	lfu->bg_work = btracker_create(4096); /* FIXME: hard coded value */
	lfu->migration_allowed = true;

	return &lfu->policy;
bad_pool_init:
	kfree(lfu);
bad_cm4_alloc:
	space_destroy(&lfu->es);
bad_dk_alloc:
	cm4_destroy(lfu->sketch);
bad_htable_alloc:
	dk_destroy(lfu->dk);
	return NULL;
}

static struct dm_cache_policy_type tinylfu_policy_type = {
	.name = "tinylfu",
	.version = {1, 0, 0},
	.hint_size = 0,
	.owner = THIS_MODULE,
	.create = tinylfu_create
};

static int __init tinylfu_init(void)
{
	int r;

	r = dm_cache_policy_register(&tinylfu_policy_type);
	if (r) {
		DMERR("register failed %d", r);
		return -ENOMEM;
	}
	return 0;
}

static void __exit tinylfu_exit(void)
{
	dm_cache_policy_unregister(&tinylfu_policy_type);
}

module_init(tinylfu_init);
module_exit(tinylfu_exit);
MODULE_LICENSE("GPL");
MODULE_AUTHOR("Austin Chang <austin880625@gmail.com>");
