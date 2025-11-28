use crate::MatchSequence;
use memchr::memchr_iter;
use savefile::prelude::Savefile;
use std::{
    cell::Cell,
    fmt::{Debug, Formatter}
};

/// This is a little trie-based search structure.
///
/// Really, we should probably just use the machinery from the regex-crate.
/// It's battle tested and very fast. This may be buggy.
///
/// But it was really fun to write!
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
    fn is_empty(&self) -> bool {
        match self {
            TinyMap::Inline(count, _, _) => *count == 0,
            TinyMap::Heap(keys, _) => keys.is_empty(),
        }
    }
    fn visit<'a>(&'a self, mut visitor: impl FnMut(K, &'a V)) {
        match self {
            TinyMap::Inline(count, keys, values) => {
                for i in 0..*count {
                    visitor(keys[i as usize], values[i as usize].as_ref().unwrap());
                }
            }
            TinyMap::Heap(keys, values) => {
                for (key, val) in keys.iter().zip(values.iter()) {
                    visitor(*key, val);
                }
            }
        }
    }
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
    pub(crate) fn match_index(&self, key: &[u8], mut cb: impl FnMut(usize)) {
        match *self {
            TrieKey::Eof => {
                if key.is_empty() {
                    cb(0)
                }
            }
            TrieKey::Exact(needle) => {
                if let Some(first) = key.first() {
                    if *first == needle {
                        cb(0);
                        return;
                    }
                }
            }
            TrieKey::WildcardThen(haystack_key) => {
                for index in memchr_iter(haystack_key, key) {
                    cb(index);
                }
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
        generation: Cell<u64>,
    },
    Tail {
        // Must not be empty
        tail: Vec<TrieKey>,
        value: Option<V>,
        generation: Cell<u64>,
    },
}

#[derive(Debug)]
pub struct Trie<V> {
    top: TrieNode<V>,
    generation: Cell<u64>,
}
impl<V> Default for Trie<V> {
    fn default() -> Self {
        Self::new()
    }
}
impl<V> TrieNode<V> {
    pub fn search<'a>(
        &'a self,
        mut key: &[u8],
        match_sequence: &mut MatchSequence,
        hit: &mut impl FnMut(&'a V, &MatchSequence),
        cur_generation: u64,
    ) {
        match self {
            TrieNode::Head {
                map,
                value,
                generation,
            } => {
                if generation.get() == cur_generation {
                    return;
                }
                if let Some(v) = value.as_ref() {
                    generation.set(cur_generation);
                    hit(v, &match_sequence);
                }
                if key.is_empty() {
                    return;
                }

                map.visit(|haystack_key, haystack_value| {
                    //println!("Matching key: {:?} against {:?}", haystack_key, key);
                    haystack_key.match_index(&key[0..], |index| {
                        //println!("Found it, at index {}, cont with  {:?}", index, &key[index+1..]);
                        let restore = match_sequence.save();
                        match_sequence.add(index as u32);
                        let r = haystack_value.search(
                            &key[index + 1..],
                            match_sequence,
                            hit,
                            cur_generation,
                        );
                        match_sequence.restore(restore);
                    });
                })
            }
            //compile_error!("Support wildcards");
            TrieNode::Tail {
                tail,
                value: Some(value),
                generation,
            } => {
                if generation.get() == cur_generation {
                    return;
                }

                fn search_tail<'a, V>(
                    key: &[u8],
                    tail: &[TrieKey],
                    match_sequence: &mut MatchSequence,
                    hit: &'_ mut impl FnMut(&'a V, &'_ MatchSequence),
                    value: &'a V,
                    generation: &Cell<u64>,
                    cur_generation: u64,
                ) {
                    if generation.get() == cur_generation {
                        return;
                    }
                    if tail.is_empty() {
                        hit(value, match_sequence);
                        generation.set(cur_generation);
                    } else if let Some(needle) = tail.get(0).cloned() {
                        needle.match_index(&key[..], |index| {
                            if generation.get() == cur_generation {
                                return;
                            }
                            let saved = match_sequence.save();
                            match_sequence.add(index as u32);
                            let tail = &tail[1..];
                            if tail.is_empty() {
                                hit(value, match_sequence);
                                generation.set(cur_generation);
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
                        });
                    }
                }
                search_tail(
                    key,
                    tail,
                    match_sequence,
                    &mut *hit,
                    value,
                    generation,
                    cur_generation,
                );
            }
            _ => {}
        }
    }

    pub fn get(&self, key: &[TrieKey]) -> Option<&V> {
        if key.is_empty() {
            return if let TrieNode::Head { value, .. } = self {
                value.as_ref()
            } else if let TrieNode::Tail {
                tail,
                value: Some(value),
                generation,
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
                generation,
            } => (key == tail).then_some(value),
            TrieNode::Tail { value: None, .. } => None,
        }
    }

    pub fn push(&mut self, key: &[TrieKey], new_value: V) -> bool {
        if let TrieNode::Tail {
            tail,
            value,
            generation,
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
                generation: Cell::new(0),
            };
            _ = self.push(&old_tail, old_value);
        }
        if let TrieNode::Empty = self {
            *self = TrieNode::Tail {
                tail: key.to_vec(),
                value: Some(new_value),
                generation: Cell::new(0),
            };
            return true;
        }
        if let TrieNode::Head {
            map,
            value,
            generation,
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
                            generation: Cell::new(0),
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
            generation: Cell::new(1),
        }
    }
    pub fn get(&self, key: &str) -> Option<&V> {
        let key = TrieKey::exact(key);
        self.top.get(&key)
    }
    /// 'grdmn' matches 'grodman', 'atn' matches 'attention' etc.
    /// Return false to stop search
    pub fn search_fn(&self, key: &str, mut hit: impl FnMut(&V, &MatchSequence)) {
        let generation = self.generation.get() + 1;
        self.generation.set(generation);
        self.top.search(
            key.as_bytes(),
            &mut MatchSequence::default(),
            &mut hit,
            generation,
        );
    }
    pub fn push(&mut self, key: &[TrieKey], value: V) {
        self.top.push(&key, value);
    }
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
