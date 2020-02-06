# ttl_cache

![build](https://github.com/stusmall/ttl_cache/workflows/build/badge.svg)
[![Documentation](https://docs.rs/ttl_cache/badge.svg)](https://docs.rs/ttl_cache)

This crate provides a time sensitive key-value FIFO cache.  When the cache is created it is
given a TTL.  Any value that are in the cache for longer than this duration are considered
invalid and will not be returned.  Supports 1.20 +
