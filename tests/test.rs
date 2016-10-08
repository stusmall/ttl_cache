extern crate ttl_cache;

use ttl_cache::TtlCache;
use std::time::Duration;
use std::thread::sleep;

#[test]
fn test_put_and_get(){
    let mut cache = TtlCache::new(Duration::from_secs(60*60),2);
    cache.insert(1, 10);
    cache.insert(2, 20);
    assert_eq!(cache.get_mut(&1), Some(&mut 10));
    assert_eq!(cache.get_mut(&2), Some(&mut 20));
    assert_eq!(cache.len(), 2);
}

#[test]
fn test_put_update() {
    let mut cache = TtlCache::new(Duration::from_secs(60*60),1);
    cache.insert("1", 10);
    cache.insert("1", 19);
    assert_eq!(cache.get_mut("1"), Some(&mut 19));
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_contains_key() {
    let mut cache = TtlCache::new(Duration::from_secs(60*60),1);
    cache.insert("1", 10);
    assert_eq!(cache.contains_key("1"), true);
}

#[test]
fn test_expire_value(){
    let mut cache = TtlCache::new(Duration::from_millis(1),1);
    cache.insert("1", 10);
    sleep(Duration::from_millis(10));
    assert_eq!(cache.contains_key("1"), false);
}

#[test]
fn test_pop() {
    let mut cache = TtlCache::new(Duration::from_secs(60*60),2);
    cache.insert(1, 10);
    cache.insert(2, 20);
    assert_eq!(cache.len(), 2);
    let opt1 = cache.remove(&1);
    assert!(opt1.is_some());
    assert_eq!(opt1.unwrap(), 10);
    assert!(cache.get_mut(&1).is_none());
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_change_capacity() {
    let mut cache = TtlCache::new(Duration::from_secs(60*60),2);
    assert_eq!(cache.capacity(), 2);
    cache.insert(1, 10);
    cache.insert(2, 20);
    cache.set_capacity(1);
    assert!(cache.get_mut(&1).is_none());
    assert_eq!(cache.capacity(), 1);
}

#[test]
fn test_remove() {
    let mut cache = TtlCache::new(Duration::from_secs(60*60),3);
    cache.insert(1, 10);
    cache.insert(2, 20);
    cache.insert(3, 30);
    cache.insert(4, 40);
    cache.insert(5, 50);
    cache.remove(&3);
    cache.remove(&4);
    assert!(cache.get_mut(&3).is_none());
    assert!(cache.get_mut(&4).is_none());
    cache.insert(6, 60);
    cache.insert(7, 70);
    cache.insert(8, 80);
    assert!(cache.get_mut(&5).is_none());
    assert_eq!(cache.get_mut(&6), Some(&mut 60));
    assert_eq!(cache.get_mut(&7), Some(&mut 70));
    assert_eq!(cache.get_mut(&8), Some(&mut 80));
}

#[test]
fn test_clear() {
    let mut cache = TtlCache::new(Duration::from_secs(60*60),2);
    cache.insert(1, 10);
    cache.insert(2, 20);
    cache.clear();
    assert!(cache.get_mut(&1).is_none());
    assert!(cache.get_mut(&2).is_none());
    assert_eq!(cache.len(), 0);
}
