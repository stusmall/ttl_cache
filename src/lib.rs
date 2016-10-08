extern crate linked_hash_map;
extern crate time;

use linked_hash_map::LinkedHashMap;
use std::time::{Duration, Instant};
use std::hash::{Hash, BuildHasher};
use std::collections::hash_map::RandomState;
use std::borrow::Borrow;


struct Entry<V> {
    value: V,
    expiration: Instant,
}

impl<V> Entry<V> {
    fn new(v: V, duration: Duration) -> Self {
        Entry {
            value: v,
            expiration: Instant::now() + duration,
        }
    }

    fn is_expired(&self) -> bool {
        Instant::now() > self.expiration
    }
}

pub struct TtlCache<K: Eq + Hash, V, S: BuildHasher = RandomState> {
    map: LinkedHashMap<K, Entry<V>, S>,
    max_size: usize,
    duration: Duration,
}

impl<K: Eq + Hash, V> TtlCache<K, V> {
    pub fn new(duration: Duration, capacity: usize) -> Self {
        TtlCache {
            map: LinkedHashMap::new(),
            max_size: capacity,
            duration: duration,
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> TtlCache<K, V, S> {
    pub fn with_hasher(duration: Duration, capacity: usize, hash_builder: S) -> Self {
        TtlCache {
            map: LinkedHashMap::with_hasher(hash_builder),
            max_size: capacity,
            duration: duration,
        }
    }

    pub fn contains_key<Q: ?Sized>(&mut self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        // Expiration check is handled by get_mut
        self.get_mut(key).is_some()
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let to_insert = Entry::new(v, self.duration);
        let old_val = self.map.insert(k, to_insert);
        if self.len() > self.capacity() {
            self.remove_oldest();
        }
        old_val.map(|x| x.value)
    }

    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        self.map.get_mut(k).and_then(|mut x| {
            if x.is_expired() {
                None
            } else {
                Some(&mut x.value)
            }
        })
    }

    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        self.map.remove(k).and_then(|x| { if x.is_expired() { None } else { Some(x.value) } })
    }

    pub fn capacity(&self) -> usize {
        self.max_size
    }

    pub fn set_capacity(&mut self, capacity: usize) {
        for _ in capacity..self.len() {
            self.remove_oldest();
        }
        self.max_size = capacity;
    }

    pub fn remove_expired(&mut self) {
        let should_pop_head = |map: &LinkedHashMap<K, Entry<V>, S>| {
            match map.front() {
                Some(entry) => entry.1.is_expired(),
                None => false,
            }
        };
        while should_pop_head(&self.map) {
            self.map.pop_front();
        }
    }

    pub fn remove_oldest(&mut self) -> Option<(K, V)> {
        self.map.pop_front().map(|x| (x.0, x.1.value))
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> Extend<(K, V)> for TtlCache<K, V, S> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}
