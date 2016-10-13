# ttl_cache

[![Build Status](https://travis-ci.org/stusmall/ttl_cache.svg?branch=master)](https://travis-ci.org/stusmall/ttl_cache)
[![Documentation](https://docs.rs/ttl_cache/badge.svg)](https://docs.rs/ttl_cache)

This crate provides a time sensitive key-value FIFO cache.  When the cache is created it is
given a TTL.  Any value that are in the cache for longer than this duration are considered
invalid and will not be returned.
