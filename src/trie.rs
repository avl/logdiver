use crate::{MatchSequence, Restore};
use memchr::memchr_iter;
use savefile::prelude::Savefile;
use std::{
    cell::Cell,
    fmt::{Debug, Formatter}
};
use std::sync::atomic::{AtomicU64, Ordering};

/// This is a little trie-based search structure.
///
/// Really, we should probably just use the machinery from the regex-crate.
/// It's battle tested and very fast. This may be buggy.
///
/// But it was really fun to write!
#[derive(Clone)]
enum TinyMap<K, V> {
    Inline(u8, [K; 8], [Option<V>; 8]),
    Heap(Vec<K>, Vec<V>),
}

impl<K: Debug, V: Debug> Debug for TinyMap<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TinyMap::Inline(count, keys, values) => f
                .debug_map()
                .entries(
                    keys[..*count as usize]
                        .iter()
                        .zip(values[..*count as usize].iter()),
                )
                .finish(),
            TinyMap::Heap(keys, values) => f
                .debug_map()
                .entries(keys.iter().zip(values.iter()))
                .finish(),
        }
    }
}

impl<K: Debug + Default + Copy + PartialEq, V> TinyMap<K, V> {
    fn new() -> TinyMap<K, V> {
        Self::Inline(0, Default::default(), Default::default())
    }
    #[allow(unused)]
    fn is_empty(&self) -> bool {
        match self {
            TinyMap::Inline(count, _, _) => *count == 0,
            TinyMap::Heap(keys, _) => keys.is_empty(),
        }
    }
    #[inline]
    fn visit<'a>(&'a mut self, mut visitor: impl FnMut(K, &mut V) -> bool) -> bool {
        match self {
            TinyMap::Inline(count, keys, values) => {
                for i in 0..*count {
                    if !visitor(keys[i as usize], values[i as usize].as_mut().unwrap()) {
                        return false;
                    }
                }
                true
            }
            TinyMap::Heap(keys, values) => {
                for (key, val) in keys.iter().zip(values.iter_mut()) {
                    if !visitor(*key, val) {
                        return false;
                    }
                }
                true
            }
        }
    }
    #[allow(unused)]
    fn remove(&mut self, key: K) {
        match self {
            TinyMap::Inline(count, keys, vals) => {
                if let Some(i) = keys[..*count as usize].iter().position(|x| *x == key) {
                    *count -= 1;
                    if *count as usize != i {
                        keys[i] = keys[*count as usize];
                        keys[*count as usize] = K::default();
                        vals[i] = vals[*count as usize].take();
                    }
                }
            }
            TinyMap::Heap(keys, vals) => {
                if let Some(i) = keys.iter().position(|x| *x == key) {
                    keys.swap_remove(i);
                    vals.swap_remove(i);
                }
            }
        }
    }
    #[inline]
    fn insert(&mut self, key: K, value: V) -> bool {
        match self {
            TinyMap::Inline(count, keys, values) => {
                if *count == 8 {
                    let keys = keys[..*count as usize].to_vec();
                    let values: Vec<V> = values[..*count as usize]
                        .iter_mut()
                        .map(|x| x.take().unwrap())
                        .collect();
                    *self = Self::Heap(keys, values);
                    return self.insert(key, value);
                }
                if keys[..*count as usize].contains(&key) {
                    return false;
                }
                keys[*count as usize] = key;
                values[*count as usize] = Some(value);
                *count += 1;
                true
            }
            TinyMap::Heap(keys, values) => {
                if keys.contains(&key) {
                    return false;
                }
                keys.push(key);
                values.push(value);
                true
            }
        }
    }
    #[inline]
    fn get(&self, key: K) -> Option<&V> {
        match self {
            TinyMap::Inline(count, keys, values) => {
                if let Some(index) = keys[..*count as usize].iter().position(|x| *x == key) {
                    values[index].as_ref()
                } else {
                    None
                }
            }
            TinyMap::Heap(keys, values) => {
                if let Some(index) = keys.iter().position(|x| *x == key) {
                    Some(&values[index])
                } else {
                    None
                }
            }
        }
    }
    #[inline]
    fn get_mut(&mut self, key: K) -> Option<&mut V> {
        match self {
            TinyMap::Inline(count, keys, values) => {
                if let Some(index) = keys[0..*count as usize].iter().position(|x| *x == key) {
                    values[index].as_mut()
                } else {
                    None
                }
            }
            TinyMap::Heap(keys, values) => {
                if let Some(index) = keys.iter().position(|x| *x == key) {
                    Some(&mut values[index])
                } else {
                    None
                }
            }
        }
    }
}


#[derive(Debug, PartialEq, Clone, Copy, Default, Savefile)]
pub enum TrieKey {
    #[default]
    Eof,
    Exact(u8),
    WildcardThen(u8),
    Any,
}

impl TrieKey {
    #[allow(unused)]
    fn exact(s: &str) -> Vec<TrieKey> {
        let mut ret = Vec::with_capacity(s.len());
        for (idx, c) in s.bytes().enumerate() {
            ret.push(if idx == 0 {
                TrieKey::WildcardThen(c)
            } else {
                TrieKey::Exact(c)
            });
        }
        ret
    }
    pub(crate) fn match_index(&self, key: &[u8], mut cb: impl FnMut(usize) -> bool) -> bool {
        match *self {
            TrieKey::Eof => {
                if key.is_empty() {
                    cb(0)
                } else {
                    true
                }
            }
            TrieKey::Exact(needle) => {
                if let Some(first) = key.first() {
                    if *first == needle {
                        cb(0)
                    } else {
                        true
                    }
                } else {
                    true
                }
            }
            TrieKey::WildcardThen(haystack_key) => {
                for index in memchr_iter(haystack_key, key) {
                    if !cb(index) {
                        return false;
                    }
                }
                true
            }
            TrieKey::Any => cb(0),
        }
    }
}

#[derive(Debug)]
enum TrieNode<V> {
    Empty,
    Head {
        map: Box<TinyMap<TrieKey, TrieNode<V>>>,
        value: Option<V>,
        generation: u64,
    },
    Tail {
        // Must not be empty
        tail: Vec<TrieKey>,
        value: Option<V>,
        generation: u64,
    },
}
impl<V:Clone> Clone for TrieNode<V> {
    fn clone(&self) -> Self {
        match self {
            TrieNode::Empty => {TrieNode::Empty}
            TrieNode::Head { map, value, generation } => {
                TrieNode::Head {
                    map: map.clone(),
                    value: value.clone(),
                    generation: *generation
                }
            }
            TrieNode::Tail { tail, value, generation } => {
                TrieNode::Tail {
                    tail: tail.clone(),
                    value: value.clone(),
                    generation: *generation
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct Trie<V> {
    top: TrieNode<V>,
    generation: AtomicU64,
    match_sequence: MatchSequence,
}
impl<V> Trie<V> {
    pub fn empty_trie(&self) -> bool {
        match &self.top {
            TrieNode::Empty => {true}
            _ => false,
        }
    }

}
impl<V> Clone for Trie<V> where V: Clone{
    fn clone(&self) -> Self {
        Self {
            top: self.top.clone(),
            generation: AtomicU64::new(self.generation.load(Ordering::Relaxed)),
            match_sequence: self.match_sequence.clone(),
        }
    }
}
impl<V> Default for Trie<V> {
    fn default() -> Self {
        Self::new()
    }
}

trait MatchSequenceCollector {
    type Restore;
    fn save(&mut self) -> Self::Restore;
    fn restore(&mut self, restore: Self::Restore);
    fn add(&mut self, i: u32);
}
struct DummyMatchSequenceCollector;
impl MatchSequenceCollector for DummyMatchSequenceCollector {
    type Restore = ();
    #[inline]
    fn save(&mut self) -> Self::Restore {
    }

    #[inline]
    fn restore(&mut self, _restore: Self::Restore) {
    }

    #[inline]
    fn add(&mut self, _i: u32) {
    }
}
impl MatchSequenceCollector for MatchSequence {
    type Restore = Restore;
    fn save(&mut self) -> Restore {
        self.save()
    }
    fn restore(&mut self, restore: Restore) {
        self.restore(restore)
    }

    fn add(&mut self, i: u32) {
        self.add(i)
    }
}


impl<V> TrieNode<V> {
    // return false to stop traversal
    #[inline]
    pub fn search<'a, M: MatchSequenceCollector>(
        &mut self,
        needle_key: &[u8],
        match_sequence: &mut M,
        hit: &mut impl FnMut(&V, &M) -> bool,
        cur_generation: u64,
    ) -> bool {
        match self {
            TrieNode::Head {
                map,
                value,
                generation,
            } => {
                if let Some(v) = value.as_ref() {
                    if *generation != cur_generation {
                        *generation = cur_generation;
                        if !hit(v, &match_sequence) {
                            return false;
                        }
                    }
                }
                if needle_key.is_empty() {
                    return true;
                }

                map.visit(|haystack_key, haystack_value| {
                    haystack_key.match_index(&needle_key[0..], |index| {
                        let restore = match_sequence.save();
                        match_sequence.add(index as u32);
                        if !haystack_value.search(
                            &needle_key[index + 1..],
                            match_sequence,
                            hit,
                            cur_generation,
                        ) {
                            return false;
                        }
                        match_sequence.restore(restore);
                        true
                    })
                })
            }
            //compile_error!("Support wildcards");
            TrieNode::Tail {
                tail,
                value: Some(value),
                generation,
            } => {
                if *generation == cur_generation {
                    return true;
                }

                #[inline]
                fn search_tail<'a, V, M: MatchSequenceCollector>(
                    key: &[u8],
                    tail: &[TrieKey],
                    match_sequence: &mut M,
                    hit: &'_ mut impl FnMut(&'a V, &'_ M) -> bool,
                    value: &'a V,
                    generation: &mut u64,
                    cur_generation: u64,
                ) -> bool {
                    if *generation == cur_generation {
                        return true;
                    }
                    if tail.is_empty() {
                        *generation = cur_generation;
                        hit(value, match_sequence);
                    } else if let Some(needle) = tail.get(0).cloned() {
                        if !needle.match_index(&key[..], |index| -> bool {
                            if *generation == cur_generation {
                                return true;
                            }
                            let saved = match_sequence.save();
                            match_sequence.add(index as u32);
                            let tail = &tail[1..];
                            if tail.is_empty() {
                                *generation = cur_generation;
                                if !hit(value, match_sequence) {
                                    return false;
                                }
                            } else {
                                let key = &key[index + 1..];
                                search_tail(
                                    key,
                                    tail,
                                    match_sequence,
                                    hit,
                                    value,
                                    generation,
                                    cur_generation,
                                );
                            }
                            match_sequence.restore(saved);
                            true
                        }) {
                            return false;
                        }
                    }
                    true
                }
                search_tail(
                    needle_key,
                    tail,
                    match_sequence,
                    &mut *hit,
                    value,
                    generation,
                    cur_generation,
                )
            }
            _ => {true}
        }
    }

    #[allow(unused)]
    pub fn get(&self, key: &[TrieKey]) -> Option<&V> {
        if key.is_empty() {
            return if let TrieNode::Head { value, .. } = self {
                value.as_ref()
            } else if let TrieNode::Tail {
                tail,
                value: Some(value),
                ..
            } = self
            {
                tail.is_empty().then_some(value)
            } else {
                None
            };
        }
        match self {
            TrieNode::Empty => None,
            TrieNode::Head { map, .. } => {
                if let Some(val) = map.get(key[0]) {
                    val.get(&key[1..])
                } else {
                    None
                }
            }
            TrieNode::Tail {
                tail,
                value: Some(value),
                ..
            } => (key == tail).then_some(value),
            TrieNode::Tail { value: None, .. } => None,
        }
    }

    pub fn push(&mut self, key: &[TrieKey], new_value: V) -> bool {
        if let TrieNode::Tail {
            tail,
            value,
            ..
        } = self
        {
            if tail == key {
                return false;
            }
            let old_tail = std::mem::replace(tail, Default::default());
            let old_value = value.take().unwrap();
            *self = TrieNode::Head {
                map: Box::new(TinyMap::new()),
                value: None,
                generation: 0
            };
            _ = self.push(&old_tail, old_value);
        }
        if let TrieNode::Empty = self {
            *self = TrieNode::Tail {
                tail: key.to_vec(),
                value: Some(new_value),
                generation: 0
            };
            return true;
        }
        if let TrieNode::Head {
            map,
            value,
            ..
        } = self
        {
            if key.is_empty() {
                if value.is_some() {
                    false
                } else {
                    *value = Some(new_value);
                    true
                }
            } else {
                let next = key[0];
                if let Some(child) = map.get_mut(next) {
                    child.push(&key[1..], new_value)
                } else {
                    map.insert(
                        next,
                        TrieNode::Tail {
                            tail: key[1..].to_vec(),
                            value: Some(new_value),
                            generation: 0
                        },
                    );
                    true
                }
            }
        } else {
            unreachable!();
        }
    }
}
impl<V> Trie<V> {
    pub fn new() -> Trie<V> {
        Self {
            top: TrieNode::Empty,
            generation: AtomicU64::new(1),
            match_sequence: Default::default(),
        }
    }
    #[allow(unused)]
    pub fn get(&self, key: &str) -> Option<&V> {
        let key = TrieKey::exact(key);
        self.top.get(&key)
    }

    pub fn search_fn(&mut self, key: &str, mut hit: impl FnMut(&V, &MatchSequence) -> bool) {
        let generation = self.generation.fetch_add(1, Ordering::Relaxed)+1;
        self.match_sequence.clear();
        self.top.search(
            key.as_bytes(),
            &mut self.match_sequence,
            &mut hit,
            generation,
        );
    }
    pub fn search_fn_fast(&mut self, key: &str, mut hit: impl FnMut(&V), max_hits: usize) {
        let generation = self.generation.fetch_add(1, Ordering::Relaxed)+1;
        let mut hit_count = 0;
        self.top.search(
            key.as_bytes(),
            &mut DummyMatchSequenceCollector,
            &mut |v,_|{
                hit(v);
                hit_count += 1;
                return hit_count < max_hits;
            },
            generation,
        );
    }
    pub fn push(&mut self, key: &[TrieKey], value: V) {
        self.top.push(&key, value);
    }
    #[allow(unused)]
    pub fn push_exact(&mut self, key: &str, value: V) {
        let key = TrieKey::exact(key);
        self.top.push(&key, value);
    }
}

#[cfg(test)]
mod tests {
    use super::{TinyMap, Trie};
    use crate::Fingerprint;

    fn verify_matches(needles: &[&str], haystack: &str) {
        let mut trie = Trie::new();
        for needle in needles {
            let fp = Fingerprint::parse(&needle);
            trie.push(&fp.0, true);
        }
        println!("Trie:\n{:#?}", trie);
        let mut hit = false;
        trie.search_fn(haystack, |v, _ms| {
            if *v {
                hit = true;
            }
            true
        });
        assert!(hit);
    }

    #[test]
    fn trie_test1() {
        verify_matches(&["a", "b"], "abcd");
    }
    #[test]
    fn trie_test2() {
        verify_matches(&["0", "1"], "0");
    }

    #[test]
    fn tiny_map_test() {
        let mut t = TinyMap::new();
        t.insert(1, 2);
        t.insert(1, 3);
        assert_eq!(t.get(1), Some(&2));
        t.insert(2, 22);
        t.remove(1);
        assert_eq!(t.get(1), None);
        assert_eq!(t.get(2), Some(&22));
    }
    #[test]
    fn tiny_map_test2() {
        let mut t = TinyMap::new();
        for i in 0..20 {
            t.insert(i, i);
        }
        for i in 0..20 {
            assert_eq!(t.get(i), Some(&i));
        }
    }

    #[test]
    fn simple_trie_test() {
        let mut trie = Trie::new();

        trie.push_exact("hej", 42);
        trie.push_exact("hejsansvejsan", 42);
        trie.push_exact("hes", 43);
        assert_eq!(trie.get("hej"), Some(&42));
        assert_eq!(trie.get("hes"), Some(&43));
        assert_eq!(trie.get("hejsansvejsan"), Some(&42));
    }

    #[test]
    fn simple_trie_test2() {
        let mut trie = Trie::new();

        trie.push_exact("hj", 1);
        trie.push_exact("hs", 2);
        trie.push_exact("ht", 3);
        trie.push_exact("åäö", 3);
        trie.push_exact("hlgnstd", 4);
    }
}
