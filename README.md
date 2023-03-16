# dm-cache-policy-tinylfu
A work-in-progress TinyLFU policy implementation for dm-cache

# What is this?

This patch is an attempt to implement [TinyLFU](https://arxiv.org/abs/1512.00727) algorithm as a cache replacement policy in dm-cache. Just for practicing my own kernel programming skills in two weeks.

The patch is based on v6.3-rc1 linux kernel source tree. Some code are adapted from the default SMQ policy(linked list, allocation, hash tables...).

# Cool, how does it perform?

It compiles...

Not verified nor tested the performance.
