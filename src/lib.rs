//! This crate provides a time sensitive key-value cache.  When an item is inserted it is
//! given a TTL.  Any value that are in the cache after their duration are considered invalid
//! and will not be returned on lookups.

extern crate linked_hash_map;

use std::borrow::Borrow;
use std::cmp;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::mem;
#[cfg(feature = "stats")]
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use linked_hash_map::LinkedHashMap;

/// A time sensitive value.
#[derive(Debug, Clone, Copy, Eq, Ord)]
pub struct TtlValue<T> {
    value: T,
    expiration: Instant,
}

impl<T> TtlValue<T> {
    /// Create a new time sensitive value which expires at `expiration`.
    pub fn new(value: T, expiration: Instant) -> Self {
        TtlValue {
            value: value,
            expiration: expiration
        }
    }

    /// Create a new time sensitive value which exists for the `duration`.
    pub fn new_duration(value: T, duration: Duration) -> Self {
        Self::new(value, Instant::now() + duration)
    }

    /// Whether the value has expired or not.
    ///
    /// Note that there is a TOCTOU (time-of-check, time-of-use) race when using this function.
    pub fn is_expired(&self) -> bool {
        Instant::now() > self.expiration
    }

    /// Update the expiration of the value.
    pub fn update_expiration(&mut self, expiration: Instant) {
        self.expiration = expiration;
    }

    /// Update the value and expiration.
    ///
    /// Returns the old value if it had not expired.
    pub fn update(&mut self, value: T, expiration: Instant) -> Option<T> {
        let old_value = if self.is_expired() {
            self.value = value;
            None
        } else {
            let old_value = mem::replace(&mut self.value, value);
            Some(old_value)
        };
        self.expiration = expiration;
        old_value
    }

    /// Update the value and expiration returning the new inner value.
    ///
    /// # Panics
    ///
    /// This panics if the new expiration has already elapsed.
    pub fn update_ref(&mut self, value: T, expiration: Instant) -> &mut T {
        mem::replace(&mut self.value, value);
        self.expiration = expiration;
        assert!(!self.is_expired());
        &mut self.value
    }

    /// Extracts the value if it is still valid.
    pub fn into_inner(self) -> Option<T> {
        if self.is_expired() {
            None
        } else {
            Some(self.value)
        }
    }

    /// Get a reference to the value if it is still valid.
    pub fn as_ref(&self) -> Option<&T> {
        if self.is_expired() {
            None
        } else {
            Some(&self.value)
        }
    }

    /// Get a reference to the value if it is still valid or an update it if not.
    ///
    /// # Panics
    ///
    /// This panics if the new expiration has already elapsed.
    pub fn as_ref_or_update<F>(&mut self, f: F) -> &T
    where
        F: FnOnce() -> (T, Instant),
    {
        if self.is_expired() {
            let (value, expiration) = f();
            self.value = value;
            self.expiration = expiration;
            assert!(!self.is_expired());
        }

        &self.value
    }

    /// Get a mutable reference to the value if it is still valid.
    pub fn as_mut(&mut self) -> Option<&mut T> {
        if self.is_expired() {
            None
        } else {
            Some(&mut self.value)
        }
    }

    /// Get a mutable reference to the value if it is still valid or an update it if not.
    ///
    /// # Panics
    ///
    /// This panics if the new expiration has already elapsed.
    pub fn as_mut_or_update<F>(&mut self, f: F) -> &mut T
    where
        F: FnOnce() -> (T, Instant),
    {
        if self.is_expired() {
            let (value, expiration) = f();
            self.value = value;
            self.expiration = expiration;
            assert!(!self.is_expired());
        }

        &mut self.value
    }
}

impl<T> PartialEq<Self> for TtlValue<T>
where
    T: PartialEq<T>,
{
    fn eq(&self, other: &TtlValue<T>) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T> PartialEq<T> for TtlValue<T>
where
    T: PartialEq<T>,
{
    fn eq(&self, other: &T) -> bool {
        self.as_ref() == Some(other)
    }
}

impl<T> PartialOrd<Self> for TtlValue<T>
where
    T: PartialOrd<T>,
{
    fn partial_cmp(&self, other: &TtlValue<T>) -> Option<cmp::Ordering> {
        self.as_ref().partial_cmp(&other.as_ref())
    }
}

impl<T> PartialOrd<T> for TtlValue<T>
where
    T: PartialOrd<T>,
{
    fn partial_cmp(&self, other: &T) -> Option<cmp::Ordering> {
        self.as_ref().partial_cmp(&Some(other))
    }
}

/// A time sensitive cache.
pub struct TtlCache<K: Eq + Hash, V, S: BuildHasher = RandomState> {
    map: LinkedHashMap<K, TtlValue<V>, S>,
    max_size: usize,
    #[cfg(feature = "stats")]
    hits: AtomicUsize,
    #[cfg(feature = "stats")]
    misses: AtomicUsize,
    #[cfg(feature = "stats")]
    since: Instant,
}

impl<K: Eq + Hash, V> TtlCache<K, V> {
    /// Creates an empty cache that can hold at most `capacity` items.
    ///
    /// # Examples
    ///
    /// ```
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache: TtlCache<i32, &str> = TtlCache::new(10);
    /// ```
    pub fn new(capacity: usize) -> Self {
        TtlCache {
            map: LinkedHashMap::new(),
            max_size: capacity,
            #[cfg(feature = "stats")]
            hits: AtomicUsize::new(0),
            #[cfg(feature = "stats")]
            misses: AtomicUsize::new(0),
            #[cfg(feature = "stats")]
            since: Instant::now(),
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> TtlCache<K, V, S> {
    /// Creates an empty cache that can hold at most `capacity` items
    /// with the given hash builder.
    pub fn with_hasher(capacity: usize, hash_builder: S) -> Self {
        TtlCache {
            map: LinkedHashMap::with_hasher(hash_builder),
            max_size: capacity,
            #[cfg(feature = "stats")]
            hits: AtomicUsize::new(0),
            #[cfg(feature = "stats")]
            misses: AtomicUsize::new(0),
            #[cfg(feature = "stats")]
            since: Instant::now(),
        }
    }

    /// Check if the cache contains the given key.
    ///
    /// # Examples
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(10);
    /// cache.insert(1, "a", Duration::from_secs(30));
    /// assert_eq!(cache.contains_key(&1), true);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        // Expiration check is handled by get
        self.get(key).is_some()
    }

    /// Inserts a key-value pair into the cache with an individual ttl for the key. If the key
    /// already existed and hasn't expired, the old value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(2);
    ///
    /// cache.insert(1, "a", Duration::from_secs(20));
    /// cache.insert(2, "b", Duration::from_secs(60));
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// ```
    pub fn insert(&mut self, k: K, v: V, ttl: Duration) -> Option<V> {
        let to_insert = TtlValue::new_duration(v, ttl);
        let old_val = self.map.insert(k, to_insert);
        if self.len() > self.capacity() {
            self.remove_oldest();
        }
        old_val.and_then(|x| if x.is_expired() { None } else { Some(x.value) })
    }

    /// Returns a reference to the value corresponding to the given key in the cache, if
    /// it contains an unexpired entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(2);
    /// let duration = Duration::from_secs(30);
    ///
    /// cache.insert(1, "a", duration);
    /// cache.insert(2, "b", duration);
    /// cache.insert(2, "c", duration);
    /// cache.insert(3, "d", duration);
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"c"));
    /// ```
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let to_ret = self.map
            .get(k)
            .and_then(|x| if x.is_expired() { None } else { Some(&x.value) });
        #[cfg(feature = "stats")]
        {
            if to_ret.is_some() {
                self.hits.fetch_add(1, Ordering::Relaxed);
            } else {
                self.misses.fetch_add(1, Ordering::Relaxed);
            }
        }
        to_ret
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
    /// let mut cache = TtlCache::new(2);
    /// let duration = Duration::from_secs(30);
    ///
    /// cache.insert(1, "a", duration);
    /// cache.insert(2, "b", duration);
    /// cache.insert(2, "c", duration);
    /// cache.insert(3, "d", duration);
    ///
    /// assert_eq!(cache.get_mut(&1), None);
    /// assert_eq!(cache.get_mut(&2), Some(&mut "c"));
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let to_ret = self.map.get_mut(k).and_then(|x| {
            if x.is_expired() {
                None
            } else {
                Some(&mut x.value)
            }
        });
        #[cfg(feature = "stats")]
        {
            if to_ret.is_some() {
                self.hits.fetch_add(1, Ordering::Relaxed);
            } else {
                self.misses.fetch_add(1, Ordering::Relaxed);
            }
        }
        to_ret
    }

    /// Removes the given key from the cache and returns its corresponding value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(2);
    ///
    /// cache.insert(2, "a", Duration::from_secs(30));
    ///
    /// assert_eq!(cache.remove(&1), None);
    /// assert_eq!(cache.remove(&2), Some("a"));
    /// assert_eq!(cache.remove(&2), None);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map
            .remove(k)
            .and_then(|x| if x.is_expired() { None } else { Some(x.value) })
    }

    /// Returns the maximum number of key-value pairs the cache can hold.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache: TtlCache<i32, &str> = TtlCache::new(2);
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
    /// let mut cache = TtlCache::new(2);
    /// let duration = Duration::from_secs(30);
    ///
    /// cache.insert(1, "a", duration);
    /// cache.insert(2, "b", duration);
    /// cache.insert(3, "c", duration);
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    ///
    /// cache.set_capacity(3);
    /// cache.insert(1, "a", duration);
    /// cache.insert(2, "b", duration);
    ///
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    ///
    /// cache.set_capacity(1);
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), None);
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
    /// let mut cache = TtlCache::new(2);
    /// let duration = Duration::from_secs(30);
    ///
    /// cache.insert(1, 10, duration);
    /// cache.insert(2, 20, duration);
    /// cache.insert(3, 30, duration);
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
    /// let mut cache = TtlCache::new(2);
    /// let duration = Duration::from_secs(30);
    ///
    /// cache.insert(1, 10, duration);
    /// cache.insert(2, 20, duration);
    /// cache.insert(3, 30, duration);
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
    /// assert_eq!(cache.get(&2), Some(&200));
    /// assert_eq!(cache.get(&3), Some(&300));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        self.remove_expired();
        IterMut(self.map.iter_mut())
    }

    /// The cache will keep track of some basic stats during its usage that can be helpful
    /// for performance tuning or monitoring.  This method will reset these counters.
    /// # Examples
    ///
    /// ```
    /// use std::thread::sleep;
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(2);
    ///
    /// cache.insert(1, "a", Duration::from_secs(20));
    /// cache.insert(2, "b", Duration::from_millis(1));
    /// sleep(Duration::from_millis(10));
    /// let _ = cache.get(&1);
    /// let _ = cache.get(&2);
    /// let _ = cache.get(&3);
    /// assert_eq!(cache.miss_count(), 2);
    /// cache.reset_stats_counter();
    /// assert_eq!(cache.miss_count(), 0);
    #[cfg(feature = "stats")]
    pub fn reset_stats_counter(&mut self) {
        self.hits = AtomicUsize::new(0);
        self.misses = AtomicUsize::new(0);
        self.since = Instant::now();
    }

    /// Returns the number of unexpired cache hits since the last time the counters were reset.
    /// # Examples
    ///
    /// ```
    /// use std::thread::sleep;
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(2);
    ///
    /// cache.insert(1, "a", Duration::from_secs(20));
    /// cache.insert(2, "b", Duration::from_millis(1));
    /// sleep(Duration::from_millis(10));
    /// assert!(cache.get(&1).is_some());
    /// assert!(cache.get(&2).is_none());
    /// assert!(cache.get(&3).is_none());
    /// assert_eq!(cache.hit_count(), 1);
    #[cfg(feature = "stats")]
    pub fn hit_count(&self) -> usize {
        self.hits.load(Ordering::Relaxed)
    }

    /// Returns the number of cache misses since the last time the counters were reset.  Entries
    /// that have expired count as a miss.
    /// # Examples
    ///
    /// ```
    /// use std::thread::sleep;
    /// use std::time::Duration;
    /// use ttl_cache::TtlCache;
    ///
    /// let mut cache = TtlCache::new(2);
    ///
    /// cache.insert(1, "a", Duration::from_secs(20));
    /// cache.insert(2, "b", Duration::from_millis(1));
    /// sleep(Duration::from_millis(10));
    /// let _ = cache.get(&1);
    /// let _ = cache.get(&2);
    /// let _ = cache.get(&3);
    /// assert_eq!(cache.miss_count(), 2);
    #[cfg(feature = "stats")]
    pub fn miss_count(&self) -> usize {
        self.misses.load(Ordering::Relaxed)
    }

    /// Returns the Instant when we started gathering stats.  This is either when the cache was
    /// created or when it was last reset, whichever happened most recently.
    #[cfg(feature = "stats")]
    pub fn stats_since(&self) -> Instant {
        self.since
    }

    // This isn't made pubic because the length returned isn't exact. It can include expired values.
    // If people find that they want this then I can include a length method that trims expired
    // entries then returns the size, but I'd rather now.  One wouldn't expect a len() operation
    // to change the contents of the structure.
    fn len(&self) -> usize {
        self.map.len()
    }

    fn remove_expired(&mut self) {
        let should_pop_head = |map: &LinkedHashMap<K, TtlValue<V>, S>| match map.front() {
            Some(entry) => entry.1.is_expired(),
            None => false,
        };
        while should_pop_head(&self.map) {
            self.map.pop_front();
        }
    }

    fn remove_oldest(&mut self) {
        self.map.pop_front();
    }
}

impl<K: Eq + Hash, V> Clone for TtlCache<K, V>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> TtlCache<K, V> {
        TtlCache {
            map: self.map.clone(),
            max_size: self.max_size,
            #[cfg(feature = "stats")]
            hits: AtomicUsize::new(self.hits.load(Ordering::Relaxed)),
            #[cfg(feature = "stats")]
            misses: AtomicUsize::new(self.misses.load(Ordering::Relaxed)),
            #[cfg(feature = "stats")]
            since: self.since,
        }
    }
}

pub struct Iter<'a, K: 'a, V: 'a>(linked_hash_map::Iter<'a, K, TtlValue<V>>);

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

pub struct IterMut<'a, K: 'a, V: 'a>(linked_hash_map::IterMut<'a, K, TtlValue<V>>);

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        match self.0.next() {
            Some(entry) => {
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
            Some(entry) => {
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
