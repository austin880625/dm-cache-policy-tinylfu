# dm-cache-policy-tinylfu
A work-in-progress TinyLFU policy implementation for dm-cache

# What is this?

This patch is an attempt to implement [TinyLFU](https://arxiv.org/abs/1512.00727) algorithm as a cache replacement policy in dm-cache. Just for practicing my own kernel programming skills in 2 weeks.

The patch is based on v6.3-rc1 linux kernel source tree. Some code are adopted from the default SMQ policy(linked list, allocation, hash tables...).

# Why do I write this?

- Having no experience on kernel programming, I have to pick something to start from.
- Cache policy is mostly about the algorithm itself, so I don't need to dig into those device or protocol stack stuffs(more friendly).
- I've heard of Stachastic Multi Queue and have no idea why this design is kept in kernel as the default. A good chance to study & compare.

# Cool, how does it perform?

Not very well. It compiles and allows effective read/write.

Not verified nor tested the performance.
