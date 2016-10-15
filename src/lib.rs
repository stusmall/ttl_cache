//! This crate provides a time sensitive key-value FIFO cache.  When the cache is created it is
//! given a TTL.  Any value that are in the cache for longer than this duration are considered
//! invalid and will not be returned.

extern crate linked_hash_map;

use linked_hash_map::LinkedHashMap;
use std::time::{Duration, Instant};
use std::hash::{Hash, BuildHasher};
use std::collections::hash_map::RandomState;
use std::borrow::Borrow;

#[derive(Clone)]
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



/// A time sensitive cache.
#[derive(Clone)]
pub struct TtlCache<K: Eq + Hash, V, S: BuildHasher = RandomState> {
    map: LinkedHashMap<K, Entry<V>, S>,
    max_size: usize,
    duration: Duration,
}

impl<K: Eq + Hash, V> TtlCache<K, V> {
    /// Creates an empty cache that can hold at most `capacity` items and will expire them
    /// after `duration`
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache: TtlCache<i32, &str> = TtlCache::new(Duration::from_secs(30), 10);
    /// ```
    pub fn new(duration: Duration, capacity: usize) -> Self {
        TtlCache {
            map: LinkedHashMap::new(),
            max_size: capacity,
            duration: duration,
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> TtlCache<K, V, S> {
    /// Creates an empty cache that can hold at most `capacity` items
    /// that expire after `duration` with the given hash builder.
    pub fn with_hasher(duration: Duration, capacity: usize, hash_builder: S) -> Self {
        TtlCache {
            map: LinkedHashMap::with_hasher(hash_builder),
            max_size: capacity,
            duration: duration,
        }
    }

    /// Check if the cache contains the given key.
    ///
    /// # Examples
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(Duration::from_secs(30), 10);
    /// cache.insert(1,"a");
    /// assert_eq!(cache.contains_key(&1), true);
    /// ```
    pub fn contains_key<Q: ?Sized>(&mut self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        // Expiration check is handled by get_mut
        self.get_mut(key).is_some()
    }



    /// Inserts a key-value pair into the cache. If the key already existed and hasn't expired,
    /// the old value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(Duration::from_secs(30), 2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// assert_eq!(cache.get_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.get_mut(&2), Some(&mut "b"));
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let to_insert = Entry::new(v, self.duration);
        let old_val = self.map.insert(k, to_insert);
        if self.len() > self.capacity() {
            self.remove_oldest();
        }
        old_val.and_then(|x| if x.is_expired() { None } else { Some(x.value) })
    }

    /// Returns a mutable reference to the value corresponding to the given key in the cache, if
    /// it contains an unexpired entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(Duration::from_secs(30), 2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(2, "c");
    /// cache.insert(3, "d");
    ///
    /// assert_eq!(cache.get_mut(&1), None);
    /// assert_eq!(cache.get_mut(&2), Some(&mut "c"));
    /// ```
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


    /// Removes the given key from the cache and returns its corresponding value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(Duration::from_secs(30), 2);
    ///
    /// cache.insert(2, "a");
    ///
    /// assert_eq!(cache.remove(&1), None);
    /// assert_eq!(cache.remove(&2), Some("a"));
    /// assert_eq!(cache.remove(&2), None);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        self.map.remove(k).and_then(|x| if x.is_expired() { None } else { Some(x.value) })
    }


    /// Returns the maximum number of key-value pairs the cache can hold.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache: TtlCache<i32, &str> = TtlCache::new(Duration::from_secs(30), 2);
    /// assert_eq!(cache.capacity(), 2);
    /// ```
    pub fn capacity(&self) -> usize {
        self.max_size
    }


    /// Sets the number of key-value pairs the cache can hold. Removes
    /// oldest key-value pairs if necessary.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(Duration::from_secs(30), 2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(3, "c");
    ///
    /// assert_eq!(cache.get_mut(&1), None);
    /// assert_eq!(cache.get_mut(&2), Some(&mut "b"));
    /// assert_eq!(cache.get_mut(&3), Some(&mut "c"));
    ///
    /// cache.set_capacity(3);
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    ///
    /// assert_eq!(cache.get_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.get_mut(&2), Some(&mut "b"));
    /// assert_eq!(cache.get_mut(&3), Some(&mut "c"));
    ///
    /// cache.set_capacity(1);
    ///
    /// assert_eq!(cache.get_mut(&1), None);
    /// assert_eq!(cache.get_mut(&2), Some(&mut "b"));
    /// assert_eq!(cache.get_mut(&3), None);
    /// ```
    pub fn set_capacity(&mut self, capacity: usize) {
        for _ in capacity..self.len() {
            self.remove_oldest();
        }
        self.max_size = capacity;
    }

    /// Clears all values out of the cache
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns an iterator over the cache's key-value pairs in oldest to youngest order.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(Duration::from_secs(30), 2);
    ///
    /// cache.insert(1, 10);
    /// cache.insert(2, 20);
    /// cache.insert(3, 30);
    ///
    /// let kvs: Vec<_> = cache.iter().collect();
    /// assert_eq!(kvs, [(&2, &20), (&3, &30)]);
    /// ```
    pub fn iter(&mut self) -> Iter<K, V> {
        self.remove_expired();
        Iter(self.map.iter())
    }

    /// Returns an iterator over the cache's key-value pairs in oldest to youngest order with
    /// mutable references to the values.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(Duration::from_secs(30), 2);
    ///
    /// cache.insert(1, 10);
    /// cache.insert(2, 20);
    /// cache.insert(3, 30);
    ///
    /// let mut n = 2;
    ///
    /// for (k, v) in cache.iter_mut() {
    ///     assert_eq!(*k, n);
    ///     assert_eq!(*v, n * 10);
    ///     *v *= 10;
    ///     n += 1;
    /// }
    ///
    /// assert_eq!(n, 4);
    /// assert_eq!(cache.get_mut(&2), Some(&mut 200));
    /// assert_eq!(cache.get_mut(&3), Some(&mut 300));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        self.remove_expired();
        IterMut(self.map.iter_mut())
    }

    // This isn't made pubic because the length returned isn't exact. It can include expired values.
    // If people find that they want this then I can include a length method that trims expired
    // entries then returns the size, but I'd rather now.  One wouldn't expect a len() operation
    // to change the contents of the structure.
    fn len(&self) -> usize {
        self.map.len()
    }

    fn remove_expired(&mut self) {
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

    fn remove_oldest(&mut self) -> Option<(K, V)> {
        self.map.pop_front().map(|x| (x.0, x.1.value))
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> Extend<(K, V)> for TtlCache<K, V, S> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

pub struct Iter<'a, K: 'a, V: 'a>(linked_hash_map::Iter<'a, K, Entry<V>>);

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Iter<'a, K, V> {
        Iter(self.0.clone())
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        match self.0.next() {
            Some(entry) => {
                if entry.1.is_expired() {
                    self.next()
                } else {
                    Some((entry.0, &entry.1.value))
                }
            }
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        match self.0.next_back() {
            Some(entry) => {
                if entry.1.is_expired() {
                    // The entries are in order of time.  So if the previous entry is expired, every
                    // else before it will be expired too.
                    None
                } else {
                    Some((entry.0, &entry.1.value))
                }
            }
            None => None,
        }
    }
}


pub struct IterMut<'a, K: 'a, V: 'a>(linked_hash_map::IterMut<'a, K, Entry<V>>);

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        match self.0.next() {
            Some(mut entry) => {
                if entry.1.is_expired() {
                    self.next()
                } else {
                    Some((entry.0, &mut entry.1.value))
                }
            }
            None => None,
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}


impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        match self.0.next_back() {
            Some(mut entry) => {
                if entry.1.is_expired() {
                    None
                } else {
                    Some((entry.0, &mut entry.1.value))
                }
            }
            None => None,
        }
    }
}
