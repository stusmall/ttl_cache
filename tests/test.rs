extern crate ttl_cache;

use ttl_cache::TtlCache;
use std::time::Duration;
use std::thread::sleep;

#[test]
fn test_put_and_get() {
    let duration = Duration::from_secs(60 * 60);
    let mut cache = TtlCache::new(2);
    cache.insert(1, 10, duration);
    cache.insert(2, 20, duration);
    assert_eq!(cache.get_mut(&1), Some(&mut 10));
    assert_eq!(cache.get_mut(&2), Some(&mut 20));
    assert_eq!(cache.get(&1), Some(&10));
    assert_eq!(cache.get(&2), Some(&20));
}

#[test]
fn test_put_update() {
    let duration = Duration::from_secs(60 * 60);
    let mut cache = TtlCache::new(1);
    cache.insert("1", 10, duration);
    cache.insert("1", 19, duration);
    assert_eq!(cache.get_mut("1"), Some(&mut 19));
}

#[test]
fn test_expire_value() {
    let duration = Duration::from_millis(1);
    let mut cache = TtlCache::new(1);
    cache.insert("1", 10, duration);
    sleep(Duration::from_millis(10));
    assert_eq!(cache.get("1"), None);
}

#[test]
fn test_pop() {
    let duration = Duration::from_secs(60 * 60);
    let mut cache = TtlCache::new(2);
    cache.insert(1, 10, duration);
    cache.insert(2, 20, duration);
    let opt1 = cache.remove(&1);
    assert!(opt1.is_some());
    assert_eq!(opt1.unwrap(), 10);
    assert!(cache.get_mut(&1).is_none());
}

#[test]
fn test_change_capacity() {
    let duration = Duration::from_secs(60 * 60);
    let mut cache = TtlCache::new(2);
    assert_eq!(cache.capacity(), 2);
    cache.insert(1, 10, duration);
    cache.insert(2, 20, duration);
    cache.set_capacity(1);
    assert!(cache.get_mut(&1).is_none());
    assert_eq!(cache.capacity(), 1);
}

#[test]
fn test_remove() {
    let duration = Duration::from_secs(60 * 60);
    let mut cache = TtlCache::new(3);
    cache.insert(1, 10, duration);
    cache.insert(2, 20, duration);
    cache.insert(3, 30, duration);
    cache.insert(4, 40, duration);
    cache.insert(5, 50, duration);
    cache.remove(&3);
    cache.remove(&4);
    assert!(cache.get_mut(&3).is_none());
    assert!(cache.get_mut(&4).is_none());
    cache.insert(6, 60, duration);
    cache.insert(7, 70, duration);
    cache.insert(8, 80, duration);
    assert!(cache.get_mut(&5).is_none());
    assert_eq!(cache.get_mut(&6), Some(&mut 60));
    assert_eq!(cache.get_mut(&7), Some(&mut 70));
    assert_eq!(cache.get_mut(&8), Some(&mut 80));
}

#[test]
fn test_clear() {
    let duration = Duration::from_secs(60 * 60);
    let mut cache = TtlCache::new(2);
    cache.insert(1, 10, duration);
    cache.insert(2, 20, duration);
    cache.clear();
    assert!(cache.get_mut(&1).is_none());
    assert!(cache.get_mut(&2).is_none());
}

#[test]
fn test_iter() {
    let duration = Duration::from_secs(60 * 60);
    let mut cache = TtlCache::new(3);
    cache.insert(1, 10, duration);
    cache.insert(2, 20, duration);
    cache.insert(3, 30, duration);
    cache.insert(4, 40, duration);
    cache.insert(5, 50, duration);
    assert_eq!(cache.iter().collect::<Vec<_>>(),
               [(&3, &30), (&4, &40), (&5, &50)]);
    assert_eq!(cache.iter_mut().collect::<Vec<_>>(),
               [(&3, &mut 30), (&4, &mut 40), (&5, &mut 50)]);
    assert_eq!(cache.iter().rev().collect::<Vec<_>>(),
               [(&5, &50), (&4, &40), (&3, &30)]);
    assert_eq!(cache.iter_mut().rev().collect::<Vec<_>>(),
               [(&5, &mut 50), (&4, &mut 40), (&3, &mut 30)]);
}


#[test]
fn test_iter_w_expired() {
    let duration = Duration::from_millis(100);
    let mut cache = TtlCache::new(3);
    cache.insert(1, 10, duration);
    sleep(Duration::from_millis(200));
    cache.insert(2, 20, duration);
    cache.insert(3, 30, duration);
    assert_eq!(cache.iter().collect::<Vec<_>>(), [(&2, &20), (&3, &30)]);
    assert_eq!(cache.iter_mut().collect::<Vec<_>>(),
               [(&2, &mut 20), (&3, &mut 30)]);
    assert_eq!(cache.iter().rev().collect::<Vec<_>>(),
               [(&3, &30), (&2, &20)]);
    assert_eq!(cache.iter_mut().rev().collect::<Vec<_>>(),
               [(&3, &mut 30), (&2, &mut 20)]);
}

#[test]
fn test() {
    let mut cache = TtlCache::new(3);
    cache.insert(1, 10, Duration::from_millis(300));
    cache.insert(2, 20, Duration::from_millis(10));
    cache.insert(3, 30, Duration::from_millis(300));
    sleep(Duration::from_millis(20));
    assert_eq!(cache.iter().collect::<Vec<_>>(), [(&1, &10), (&3, &30)]);
}

#[test]
fn renewal_moves_to_end() {
    let mut cache = TtlCache::new(3);
    cache.insert(1,1, Duration::from_millis(300));
    cache.insert(2,1, Duration::from_millis(300));
    cache.renew(&1, Duration::from_millis(300));
    let mut i = cache.iter();
    assert_eq!(i.next(), Some((&2,&1)));
    assert_eq!(i.next(), Some((&1,&1)));
}
