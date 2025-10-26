extern crate core;

use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::ffi::{OsStr, OsString};
use std::io::{BufRead, BufReader};
use std::panic::catch_unwind;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::{mpsc, Arc, Condvar, Mutex};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::Receiver;
use std::thread::available_parallelism;
use std::time::{Duration, Instant};
use anyhow::{anyhow, Context, Result};
use ratatui::crossterm::event::{self, Event, KeyCode};
use indexmap::IndexMap;
use indexmap::map::Entry;
use notify::{Config, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use ratatui::{DefaultTerminal, Frame};
use tui_textarea::TextArea;
use clap::{Parser, Subcommand};
use clap::parser::Values;
use ratatui::crossterm::event::{KeyEvent, KeyEventKind};
use ratatui::layout::{Flex, Margin, Size};
use ratatui::palette::{Hsl, RgbHue};
use ratatui::prelude::{Color, Constraint, Direction, Layout, Line, Rect, Style, Stylize};
use ratatui::style::Styled;
use ratatui::text::Span;
use ratatui::widgets::{Block, Borders, Clear, Paragraph, Row, Table, TableState};
use savefile::prelude::Savefile;
use crate::trie::Trie;

#[derive(Debug, Parser)]
#[command(version, about, long_about = None)]
struct LogdiverArgs {
    /// Path to source of application that is being run
    #[arg(short = 's', long)]
    source: Option<String>,

    #[arg(long)]
    debug_notify: Option<bool>,

    #[arg(required = true)]
    values: Vec<String>,

}

mod trie {
    use std::fmt::{Debug, Formatter};
    use std::sync::Mutex;
    use memchr::memchr;
    use crate::MatchSequence;

    enum TinyMap<V> {
        Inline(u8,[u8;8],[Option<V>;8]), //TODO: Use MaybeUninit
        Heap(Vec<u8>, Vec<V>)
    }

    impl<V:Debug> Debug for TinyMap<V> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            match self {
                TinyMap::Inline(count, keys, values) => {
                    f.debug_map().entries(keys[..*count as usize].iter().zip(values[..*count as usize].iter())).finish()
                }
                TinyMap::Heap(keys, values) => {
                    f.debug_map().entries(keys.iter().zip(values.iter())).finish()
                }
            }
        }
    }

    impl<V> TinyMap<V> {
        fn new() -> TinyMap<V> {
            Self::Inline(0,Default::default(), Default::default())
        }
        fn is_empty(&self) -> bool {
            match self {
                TinyMap::Inline(count, _, _) => {*count == 0}
                TinyMap::Heap(keys, _) => {keys.is_empty()}
            }
        }
        /// Return false from visitor to stop
        fn visit<'a>(&'a self, mut visitor: impl FnMut(u8, &'a V) -> bool) -> bool {
            match self {
                TinyMap::Inline(count, keys, values) => {
                    for i in 0..*count {
                        if !visitor(keys[i as usize], values[i as usize].as_ref().unwrap()) {
                            return false;
                        }
                    }
                }
                TinyMap::Heap(keys, values) => {
                    for (key,val) in keys.iter().zip(values.iter()) {
                        if !visitor(*key,val) {
                            return false;
                        }
                    }
                }
            }
            true
        }
        fn remove(&mut self, key: u8) {
            match self {
                TinyMap::Inline(count, keys, vals) => {
                    if let Some(i) = memchr(key, &keys[..*count as usize]) {
                        *count -= 1;
                        if *count as usize != i {
                            keys[i] = keys[*count as usize];
                            keys[*count as usize] = 0;
                            vals[i] = vals[*count as usize].take();
                        }
                    }
                }
                TinyMap::Heap(keys, vals) => {
                    if let Some(i) = memchr(key, &keys) {
                        keys.swap_remove(i);
                        vals.swap_remove(i);
                    }
                }
            }
        }
        fn insert(&mut self, key: u8, value: V) -> bool {
            match self {
                TinyMap::Inline(count,keys, values) => {
                    if *count == 8 {
                        let keys = keys[..*count as usize].to_vec();
                        let values:Vec<V> = values[..*count as usize].iter_mut().map(|x|x.take().unwrap()).collect();
                        *self = Self::Heap(keys, values);
                        return self.insert(key, value);
                    }
                    if memchr(key, &keys[..*count as usize]).is_some() {
                        return false;
                    }
                    keys[*count as usize] = key;
                    values[*count as usize] = Some(value);
                    *count += 1;
                    true
                }
                TinyMap::Heap(keys, values) => {
                    if memchr(key, keys).is_some() {
                        return false;
                    }
                    keys.push(key);
                    values.push(value);
                    true
                }
            }
        }
        fn get(&self, key: u8) -> Option<&V> {
            match self  {
                TinyMap::Inline(count, keys, values) => {
                    if let Some(index) = memchr(key, &keys[..*count as usize]) {
                        values[index].as_ref()
                    } else {
                        None
                    }
                }
                TinyMap::Heap(keys, values) => {
                    if let Some(index) = memchr(key, keys) {
                        Some(&values[index])
                    } else {
                        None
                    }
                }
            }
        }
        fn get_mut(&mut self, key: u8) -> Option<&mut V> {
            match self  {
                TinyMap::Inline(count, keys, values) => {
                    if let Some(index) = memchr(key, &keys[0..*count as usize]) {
                        values[index].as_mut()
                    } else {
                        None
                    }
                }
                TinyMap::Heap(keys, values) => {
                    if let Some(index) = memchr(key, keys) {
                        Some(&mut values[index])
                    } else {
                        None
                    }
                }
            }
        }
    }

    #[derive(Debug)]
    enum TrieNode<V> {
        Empty,
        Head {
            map: Box<TinyMap<TrieNode<V>>>,
            value: Option<V>,
        },
        Tail {
            // Must not be empty
            tail: Vec<u8>,
            value: Option<V>,
        }
    }

    #[derive(Debug)]
    pub struct Trie<V> {
        top: TrieNode<V>,
    }
    impl<V> Default for Trie<V> {
        fn default() -> Self {
            Self::new()
        }
    }
    impl<V> TrieNode<V> {
        pub fn contains(&self, key: &[u8]) -> bool {
            if key.is_empty() {
                return if let TrieNode::Head {value,..} = self {
                    value.is_some()
                } else if let TrieNode::Tail{tail, ..} = self {
                    tail.is_empty()
                } else {
                    false
                };
            }
            match self {
                TrieNode::Empty => {false}
                TrieNode::Head { map, value } => {
                    if let Some(val) = map.get(key[0]) {
                        val.contains(&key[1..])
                    } else {
                        false
                    }
                }
                TrieNode::Tail { tail, .. } => {
                    key == tail
                }
            }
        }
        pub fn smart_search<'a>(&'a self, mut key: &[u8], match_sequence: &mut MatchSequence, hit: &mut impl FnMut(&'a V, &MatchSequence) -> bool ) -> bool {
            match self {
                TrieNode::Head { map, value } => {
                    if let Some(v) = value.as_ref() {
                        if !hit(v, &match_sequence) {
                            return false;
                        }
                    }
                    if key.is_empty() {
                        return true;
                    }


                    map.visit(|haystack_key, haystack_value|{
                        //println!("Matching key: {:?} against {:?}", haystack_key, key);
                        if let Some(index) = memchr(haystack_key, &key[0..]) {
                            //println!("Found it, at index {}, cont with  {:?}", index, &key[index+1..]);
                            let restore = match_sequence.save();
                            match_sequence.add(index as u32);
                            let r = haystack_value.smart_search(&key[index+1..], match_sequence, hit);
                            match_sequence.restore(restore);
                            if !r {
                                return false;
                            } else {
                                return true;
                            }
                        }
                        true
                    })
                }
                TrieNode::Tail { tail, value:Some(value) } => {
                    let saved = match_sequence.save();
                    for needle in tail {
                        if let Some(index) = memchr(*needle, &key[0..]) {
                            match_sequence.add(index as u32);
                            key = &key[index+1..];
                        } else {
                            return true;
                        }
                    }
                    let t = hit(value, match_sequence);
                    match_sequence.restore(saved);
                    t
                }
                _ => {true}
            }
        }

        pub fn get(&self, key: &[u8]) -> Option<&V> {
            if key.is_empty() {
                return if let TrieNode::Head {value,..} = self {
                    value.as_ref()
                } else if let TrieNode::Tail{tail, value: Some(value)} = self {
                    tail.is_empty().then_some(value)
                } else {
                    None
                };
            }
            match self {
                TrieNode::Empty => {None}
                TrieNode::Head { map,.. } => {
                    if let Some(val) = map.get(key[0]) {
                        val.get(&key[1..])
                    } else {
                        None
                    }
                }
                TrieNode::Tail { tail, value: Some(value) } => {
                    (key == tail).then_some(value)
                }
                TrieNode::Tail { value: None, .. } => {
                    None
                }
            }
        }
        pub fn remove(&mut self, key: &[u8]) {
            match self {
                TrieNode::Empty => {}
                TrieNode::Head { map, value } => {

                    if key.is_empty() {
                        value.take();
                        return;
                    }

                    if let Some(x) = map.get_mut(key[0]) {
                        x.remove(&key[1..]);
                    }
                    if map.is_empty() {
                        *self = TrieNode::Empty;
                    }
                }
                TrieNode::Tail { tail, value } => {
                    if key == tail {
                        *self = TrieNode::Empty;
                    }
                }
            }
        }
        pub fn push(&mut self, key: &[u8], new_value: V) -> bool {
            if let TrieNode::Tail { tail, value } = self {
                if tail == key {
                    return false;
                }
                let old_tail = std::mem::replace(tail, Default::default());
                let old_value = value.take().unwrap();
                *self = TrieNode::Head {
                    map: Box::new(TinyMap::new()),
                    value: None,
                };
                _ = self.push(&old_tail, old_value);
            }
            if let TrieNode::Empty = self  {
                *self = TrieNode::Tail {
                    tail: key.to_vec(),
                    value: Some(new_value),
                };
                return true;
            }
            if let TrieNode::Head { map, value } = self {
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
                        map.insert(next, TrieNode::Tail {
                            tail: key[1..].to_vec(),
                            value: Some(new_value)
                        });
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
                top: TrieNode::Empty
            }
        }
        pub fn contains_key(&self, key: &str) -> bool {
            self.top.contains(key.as_bytes())
        }
        pub fn get(&self, key: &str) -> Option<&V> {
            self.top.get(key.as_bytes())
        }
        /// 'grdmn' matches 'grodman', 'atn' matches 'attention' etc.
        /// Return false to stop search
        pub fn smart_search_fn(&self, key: &str, mut hit: impl FnMut(&V, &MatchSequence) -> bool) {
            self.top.smart_search(key.as_bytes(), &mut MatchSequence::default(), &mut hit);
        }
        pub fn smart_search(&self, key: &str) -> Vec<&V> {
            let mut t = Vec::new();
            self.top.smart_search(key.as_bytes(), &mut MatchSequence::default(), &mut |v,m|{
                t.push(v);
                true
            });
            t
        }
        pub fn push(&mut self, key: &str, value: V) {
            self.top.push(key.as_bytes(), value);
        }
        pub fn remove(&mut self, key: &str) {
            self.top.remove(key.as_bytes());
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::trie::{TinyMap, Trie};

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

            trie.push("hej", 42);
            trie.push("hejsansvejsan", 42);
            trie.push("hes", 43);
            assert!(trie.contains_key("hej"));
            assert!(trie.contains_key("hejsansvejsan"));
            assert!(trie.contains_key("hes"));
            assert_eq!(trie.get("hej"), Some(&42));
            assert_eq!(trie.get("hes"), Some(&43));
            assert_eq!(trie.get("hejsansvejsan"), Some(&42));

        }

        #[test]
        fn simple_trie_test2() {
            let mut trie = Trie::new();

            trie.push("hj", 1);
            trie.push("hs", 2);
            trie.push("ht", 3);
            trie.push("åäö", 3);
            trie.push("hlgnstd", 4);
            assert_eq!(trie.smart_search("helgens_tid"),[&2,&3,&4]);
            trie.remove("hs");
            assert_eq!(trie.smart_search("helgens_tid"),[&3,&4]);
        }
    }
}



fn parse_delta(prev: &str, now: &str, path: &Arc<PathBuf>, tx: &mut mpsc::SyncSender<DiverEvent>, debug_notify: bool) {
    let mut prev_lines = HashMap::<&str, usize>::new();
    for line in prev.lines() {
        *prev_lines.entry(line).or_default() += 1;
    }
    for (line_number,line) in now.lines().enumerate() {
        let line_number = line_number + 1; //Editors count 1 as first line
        if let Some(x) = prev_lines.get_mut(line) {
            if *x >= 1 {
                *x -= 1;
                continue;
            }
        }
        let mut finger = String::new();
        let mut brackets = false;
        fingerprint(line, &mut finger, &mut brackets);
        if !finger.is_empty() {
            let tp = TracePoint {
                file: path.clone(),
                line_number,
                tracepoint: u32::MAX,
            };
            if debug_notify {
                println!("New tracepoint: {}", finger);
            }
            let tp = TracePointData {
                fingerprint: finger,
                tp,
                smart: brackets,
                active: false,
            };
            tx.send(DiverEvent::SourceChanged(tp)).unwrap();
        }
    }
}

fn fingerprint(line: &str, fingerprint: &mut String, brackets: &mut bool) -> Option<()> {
    let mut tokens = line.chars().peekable();
    loop {
        let tok = tokens.next()?;
        if tok == '"' {
            let mut depth = 0i32;
            loop {
                let tok = tokens.next()?;
                if tok == '\\' {
                    _ = tokens.next()?;
                    continue;
                }
                if tok == '"' {
                    break;
                } else if tok == '{' {
                    *brackets = true;
                    depth += 1;
                } else if tok == '}' {
                    depth -= 1;
                } else {
                    if depth == 0 {
                        fingerprint.push(tok);
                    }
                }
            }
        }
    }
    None
}

#[derive(Savefile, Default, Clone)]
struct MatchSequence {
    range: Vec<(u32,u32)>
}

impl MatchSequence {
    pub(crate) fn visit(&self, len: usize, mut visitor: impl FnMut(usize, usize, bool)) {
        let mut expected_start = 0;
        for (start,end) in &self.range {
            if *start as usize != expected_start {
                visitor(expected_start, *start as usize, false);
            }
            visitor(*start as usize, *end as usize, true);
            expected_start = *end as usize;
        }
        if expected_start != len {
            visitor(expected_start, len, false);
        }
    }
}

struct Restore {
    range_count: u32,
    end_at: u32,
}
impl MatchSequence {
    pub fn add(&mut self, index: u32) {
        if let Some(last) = self.range.last_mut() && index == 0 {
            last.1 += 1;
            return;
        }
        if let Some(last) = self.range.last().map(|x|x.1) {
            self.range.push((last + index, last  + index+1));
        } else {
            self.range.push((index, index+1));
        }
    }
    pub fn save(&mut self) -> Restore {
        Restore {
            range_count: self.range.len() as u32,
            end_at: self.range.last().map(|x|x.1).unwrap_or(0)
        }
    }
    pub fn restore(&mut self, restore: Restore)  {
        self.range.truncate(restore.range_count as usize);
        if let Some(last) = self.range.last_mut() {
            last.1 = restore.end_at;
        }
    }
}

impl State {
    fn check_matching(
        fingerprint_trie: &mut Trie<TracePoint>,
        matching_lines: &mut Vec<MatchingLine>,
        line: &LogLine) {
        fingerprint_trie.smart_search_fn(&line.message,|hit, m| -> bool {

            let m = MatchingLine {
                log_line: line.clone(),
                hits: m.clone(),
                tp: hit.tracepoint,
            };
            matching_lines.push(m);
            false
        });
    }
    fn add_tracepoint_trie(trie: &mut Trie<TracePoint>, tp: &TracePointData) {
        trie.push(&tp.fingerprint, tp.tp.clone());
    }
    fn rebuild_trie(&mut self) {
        self.fingerprint_trie = Trie::new();
        for tp in &self.tracepoints {
            Self::add_tracepoint_trie(&mut self.fingerprint_trie, tp);
        }

        self.rebuild_matches()
    }
    fn rebuild_matches(&mut self) {
        self.generation += 1;

        self.matching_lines.clear();
        for line in &self.all_lines {
            // Also, add a "recent fingerprints" section in ratatui
            State::check_matching(&mut self.fingerprint_trie, &mut self.matching_lines, line);
        }
    }
}

impl State {
    fn add_tracepoint(&mut self,
                      mut tp: TracePointData) {
        let mut indices:Vec<_>  = self.tracepoints.iter().map(|x|x.tp.tracepoint).collect();
        indices.sort();
        let tp_index = if let Some(hole) = indices.windows(2).find(|xs|xs[1] != xs[0]+1) {
            hole[0]+1
        } else {
             indices.len() as u32
        };

        tp.tp.tracepoint = tp_index;
        Self::add_tracepoint_trie(&mut self.fingerprint_trie, &tp);
        self.tracepoints.push(tp);
        self.rebuild_matches();
    }

}

fn mainloop(
    program_lines: mpsc::Receiver<DiverEvent>,
    state: Arc<Mutex<State>>
) {

    while let Ok(event) = program_lines.recv() {
        let mut state = state.lock().unwrap();
        let mut state = &mut *state;
        match event {
            DiverEvent::SourceChanged(tp) => {
                state.add_tracepoint(tp);
            }
            DiverEvent::ProgramOutput(line) => {
                State::check_matching(&mut state.fingerprint_trie, &mut state.matching_lines, &line);
                state.all_lines.push_back(line);
                state.generation += 1;
            }
        }
    }
}

fn capturer(child: Child, program_lines: mpsc::SyncSender<DiverEvent>) {
    use std::io::Read;
    //let mut all_lines = VecDeque::new();
    if let Some(child_out) = child.stdout {
        let child_out = BufReader::new(child_out);

        for line in child_out.lines() {
            let line = line.unwrap(); //TODO: Error handling

            let value = gjson::parse(&line);
            let mut message = String::new();
            let mut target = String::new();
            let mut level = String::new();
            let mut timestamp = String::new();
            let mut fields = String::new();
            value.each(|key, value| {
                match key.str() {
                    "fields" => {
                        value.each(|key,value|{
                            if key.str() == "message" {
                                message = value.to_string();
                            } else {
                                use std::fmt::Write;
                                write!(&mut fields, "{} = {}, ", key.str(), value.str()).unwrap();
                            }
                            true
                        });
                        //let value = value.get("message");
                        //println!("message: {}", value);
                    }
                    "target" => {
                        target = value.to_string();
                        //println!("target: {}", value);
                    }
                    "level" => {
                        level = value.to_string();
                        //println!("Level: {}", value);
                    }
                    "timestamp" => {
                        timestamp = value.to_string();
                        //println!("Time: {}", value);
                    }
                    _ => {}
                };
                true
            });
            //println!("Read line {}", line);
            program_lines.send(DiverEvent::ProgramOutput(LogLine {
                time: timestamp,
                target,
                level,
                message,
                fields
            })).unwrap();

        }
    }
}

#[derive(Savefile,Debug, Clone)]
struct TracePoint {
    file: Arc<PathBuf>,
    line_number: usize,
    tracepoint: u32,
}

pub enum DiverEvent {
    SourceChanged(TracePointData),
    ProgramOutput(LogLine),
}

#[derive(Savefile, Clone)]
struct TracePointData {
    fingerprint: String,
    tp: TracePoint,
    smart: bool,
    active: bool,
}

#[derive(Clone)]
struct LogLine {
    time: String,
    target: String,
    level: String,
    message: String,
    fields: String,
}

#[derive(Eq, PartialEq,Clone,Copy, Default, Savefile)]
enum Window {
    #[default]
    Filter,
    Output
}
impl Window  {
    fn next(&self) -> Window {
        match self {
            Window::Filter => {Self::Output}
            Window::Output => {Self::Filter}
        }
    }
}

struct MatchingLine {
    log_line: LogLine,
    hits: MatchSequence,
    tp: u32,
}

#[derive(Default, Savefile)]
struct State {
    #[savefile_ignore]
    #[savefile_introspect_ignore]
    fingerprint_trie: Trie<TracePoint>,
    #[savefile_ignore]
    #[savefile_introspect_ignore]
    all_lines: VecDeque<LogLine>,
    #[savefile_ignore]
    #[savefile_introspect_ignore]
    matching_lines: Vec<MatchingLine>,
    tracepoints: Vec<TracePointData>,
    #[savefile_ignore]
    #[savefile_introspect_ignore]
    generation: u64,
    active_window: Window,
    selected_filter: Option<usize>,
    selected_output: Option<usize>,
}
fn main() -> Result<()> {
    let res = match catch_unwind(run_main) {
        Ok(err) => {
            err
        }
        Err(err) => {
            if let Some(err) = err.downcast_ref::<String>() {
                Err(anyhow!("Panic: {err}"))
            }
            else if let Some(err) = err.downcast_ref::<&'static str>() {
                Err(anyhow!("Panic: {err}"))
            } else {
                Err(anyhow!("panic!"))
            }
        }
    };
    ratatui::restore();
    res
}

#[derive(Eq, PartialEq, Clone)]
struct Debounced {
    at: Instant,
    path: PathBuf,
    size: u64,
    debouncing_iterations: u64,
}

impl PartialOrd for Debounced {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Debounced {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (other.at, &other.path).cmp(&(self.at,&self.path))
    }
}

const LOGDIVER_FILE: &str = ".logdiver.bin";



fn run_main() -> Result<()> {

    let args = LogdiverArgs::parse();
    let src = args.source.clone().unwrap_or(".".into());
    // Add a path to be watched. All files and directories at that path and
    // below will be monitored for changes.
    let pathbuf = PathBuf::from(&src);

    let state = Arc::new(Mutex::new(
        savefile::load_file(LOGDIVER_FILE, 0)
            .map(|mut state: State|{
                state.rebuild_trie();
                state
            })
            .unwrap_or(State::default())
    ));

    let mut tasks = VecDeque::new();

    tasks.push_back(pathbuf.clone());
    let tasks = Arc::new(Mutex::new(tasks));
    let condvar = Arc::new(Condvar::new());
    let mut threads = vec![];
    let thread_count:u64 = ((std::thread::available_parallelism().map(|x|x.get()).unwrap_or(0usize) as u64)/2).max(1);
    let shift = (64 - thread_count.leading_zeros());
    let in_prog = Arc::new(AtomicUsize::new(1));
    for thread in 0..thread_count {
        let rs = OsString::from("rs");
        let tasks = tasks.clone();
        let condvar = condvar.clone();
        let in_prog = in_prog.clone();
        let mut results = IndexMap::new();
        threads.push(std::thread::spawn(move || {
            let mut process_now = Vec::new();
            let mut process_soon = Vec::new();
            loop {
                let mut tasks_guard = tasks.lock().unwrap();

                let work_remaining = tasks_guard.len();
                let mut count = (work_remaining >>shift).max(1).min(work_remaining);
                //println!("#{thread} grabbing {count} of {} (shifT={shift}, remain = {})", work_remaining, in_prog.load(Ordering::Relaxed));
                if count == 0 {
                    if (in_prog.load(Ordering::Relaxed) as u64) <= thread {
                        condvar.notify_all();
                        return results;
                    }
                    let _guard = condvar.wait(tasks_guard).unwrap();
                    continue;
                }
                process_now.clear();
                process_now.extend(tasks_guard.drain(0..count));
                drop(tasks_guard);

                for dir in process_now.drain(..) {
                    //println!("Thread #{} reading {:?}", thread, dir);
                    if let Ok(dir) = std::fs::read_dir(dir) {
                        for entry in dir.into_iter() {
                            if let Ok(entry) = entry {
                                //println!("{thread} found path {:?}", entry.path());
                                if let Ok(meta) = entry.metadata() {

                                    if meta.is_dir() {
                                        process_soon.push(entry.path());
                                    }
                                    if meta.is_file() {
                                        let path = entry.path();
                                        if path.extension() == Some(&rs) {
                                            let canon = std::fs::canonicalize(path).unwrap();
                                            let contents = std::fs::read_to_string(&canon).unwrap(); //TODO: Error handling
                                            results.insert(canon, contents);
                                        }
                                    }
                                }
                            }
                        }

                    }
                }
                in_prog.fetch_add(process_soon.len(), Ordering::Relaxed);
                in_prog.fetch_sub(count, Ordering::Relaxed);
                //println!("{thread} Taking lock");
                let mut tasks_guard = tasks.lock().unwrap();
                //println!("Adding {:?}", process_soon);
                let soon_count = process_soon.len() as u64;
                tasks_guard.extend(process_soon.drain(..));
                if soon_count > thread_count {
                    condvar.notify_all();
                } else {
                    for _ in 0..soon_count {
                        condvar.notify_one();
                    }
                }
            }
        }));
    }
    let mut tot_results = IndexMap::new();
    for mut thread in threads {
        tot_results.extend(thread.join().unwrap());
    }




    /*
result*/

    let (tx, rx) = std::sync::mpsc::channel();

    // Automatically select the best implementation for your platform.
    // You can also access each implementation directly e.g. INotifyWatcher.
    let mut watcher = RecommendedWatcher::new(tx, Config::default())?;
    watcher.watch(&pathbuf, RecursiveMode::Recursive)?;

    let (diver_events_tx, diver_events_rx) = mpsc::sync_channel(16384);
    let mut source_line_change_tx = diver_events_tx.clone();

    let mut debouncing = BinaryHeap::<Debounced>::new();

    let debug_notify = args.debug_notify.unwrap_or(false);
    std::thread::spawn(move||{

        let rs = OsString::from("rs");
        if debug_notify {
            println!("Starting watch");
        }
        loop {
            let mut next_debounce_at = Duration::from_secs(60);
            if let Some(top) = debouncing.peek() {
                next_debounce_at = top.at.saturating_duration_since(Instant::now());
            }

            let res = rx.recv_timeout(next_debounce_at);

            if let Ok( res) = res {
                match res {
                    Ok(event) => {

                        match event.kind {
                            EventKind::Any => {}
                            EventKind::Access(_) => {}
                            EventKind::Create(_) |
                            EventKind::Modify(_) => {

                                for path in event.paths {
                                    if path.extension() == Some(&rs) {
                                        let path = std::fs::canonicalize(path).unwrap(); //TODO: REmove unwrap
                                        if let Ok(meta) = std::fs::metadata(&path) {
                                            if !meta.is_file() {
                                                continue;
                                            }
                                            //println!("Scheduling {}", path.as_path().display());
                                            debouncing.push(Debounced {
                                                at: Instant::now() + Duration::from_millis(500),
                                                path,
                                                size: meta.len(),
                                                debouncing_iterations: 0,
                                            });
                                        }


                                        //tot_results
                                    }
                                }
                            }
                            EventKind::Other|EventKind::Remove(_) => {}
                        }

                    },
                    Err(error) => println!("Error: {error:?}"),
                }
            } else {
                if let Some(mut debounced) = debouncing.pop() {
                    //println!("Bounce-checking {}", debounced.path.as_path().display());

                    if let Ok(meta) = std::fs::metadata(&debounced.path) {
                        if meta.len() != debounced.size {
                            //println!("Size mismatch {} != {}", meta.len(), debounced.size);
                            
                            debounced.at = Instant::now() + Duration::from_millis((100*(1<<debounced.debouncing_iterations)).min(2000));
                            debounced.size = meta.len();
                            debounced.debouncing_iterations += 1;
                            debouncing.push(debounced);
                        } else {
                            if let Ok(contents) = std::fs::read_to_string(&debounced.path) {
                                match tot_results.entry(debounced.path.clone()) {
                                    Entry::Occupied(mut prev_entry) => {
                                        let prev_value = prev_entry.get();
                                        if contents.len() < prev_value.len().saturating_sub(40) && debounced.debouncing_iterations < 3 {
                                            debounced.at = Instant::now() + Duration::from_millis(2000);
                                            debounced.size = meta.len();
                                            debounced.debouncing_iterations = 3;
                                            debouncing.push(debounced);
                                            continue;
                                        }
                                        let path = Arc::new(debounced.path);
                                        if debug_notify {
                                            println!("Read {} byte {}", contents.len(), path.as_path().display());
                                        }

                                        parse_delta(prev_value, &contents, &path, &mut source_line_change_tx, debug_notify);

                                        *prev_entry.get_mut() = contents;
                                    }
                                    Entry::Vacant(v) => {
                                        v.insert(contents);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    });
    if debug_notify {
        std::thread::sleep(std::time::Duration::from_secs(86400));
        return Ok(());
    }

    //println!("Args values: {:?}", &args.values);
    let mut arg_iter = args.values.into_iter();
    let cmd = arg_iter.next().unwrap();
    let rest: Vec<_> = arg_iter.collect();
    let mut child = Command::new(&cmd)
        .args(&rest)
        .stdout(Stdio::piped())
        .spawn()
        .with_context(||format!("failed to spawn child process: '{}' with args: {}",
                                &cmd, rest.join(" "))
        )?;


    std::thread::spawn(move||capturer(child, diver_events_tx));

    let state2 = state.clone();
    std::thread::spawn(move||{
        mainloop(diver_events_rx, state2);
    });



    let terminal = ratatui::init();

    run(terminal,state)?;

    Ok(())
}

trait BlockExt: Sized {
    fn highlight<T:Eq>(self, our_index: T, active_highlight: T) -> Self;
}

impl<'a> BlockExt for Block<'a> {
    fn highlight<T:Eq>(self, our_index: T, active_highlight: T) -> Block<'a> {
        if our_index == active_highlight {
            self.border_style(Style::default().bg(Color::White).fg(Color::Black))
        } else {
            self
        }
    }
}
fn popup_area(area: Rect, percent_x: u16) -> Rect {
    let vertical = Layout::vertical([Constraint::Length(3)]).flex(Flex::Center);
    let horizontal = Layout::horizontal([Constraint::Percentage(percent_x)]).flex(Flex::Center);
    let [area] = vertical.areas(area);
    let [area] = horizontal.areas(area);
    area
}

fn color_by_index(index: u32) -> Color {
    let colour = (index.wrapping_mul(57)) as f32;
    Color::from_hsl(Hsl::new(RgbHue::from_degrees(colour),1.0,0.5))
}


fn run(mut terminal: DefaultTerminal, state: Arc<Mutex<State>>) -> Result<()> {
    let rows: [Row; 0] = [];

    enum GuiState {
        Normal,
        AddNewFilter(TextArea<'static>)
    }



    let mut filter_table_state = TableState::default();
    let mut output_table_state = TableState::default();
    let mut last_generation = u64::MAX;
    let mut render_cnt = 0;
    let mut lastsize = Size::default();
    let mut gui_state = GuiState::Normal;

    {
        let state = state.lock().unwrap();
        filter_table_state.select(state.selected_filter);
        output_table_state.select(state.selected_output);
    }

    loop {



        {
            let state = state.lock().unwrap();
            let filter_table = Table::new(rows.clone(), [Constraint::Percentage(50), Constraint::Percentage(50), Constraint::Length(5)])
                .block(Block::bordered()
                    .title("Filters")
                    .title_bottom("A - Add filter")
                    .highlight(Window::Filter, state.active_window))
                .header(Row::new(vec!["Fingerprint", "File", "Line", "Active"]))
                .row_highlight_style(Style::new().bg(Color::Rgb(60,60,60)))
                .highlight_symbol(">");

            let output_table = Table::new(rows.clone(), [Constraint::Length(15), Constraint::Length(10), Constraint::Fill(10), Constraint::Fill(30)])
                .block(Block::bordered().title("Output").highlight(Window::Output, state.active_window))
                .header(Row::new(vec!["Time", "Level", "Target", "Message"]))
                .row_highlight_style(Style::new().bg(Color::Rgb(60,60,60)))
                .highlight_symbol(">");



            let newsize = terminal.size()?;
            if last_generation != state.generation || lastsize != newsize {
                lastsize = newsize;
                terminal.draw( |frame|{

                    let main_vertical = Layout::default()
                        .direction(Direction::Vertical)
                        .constraints(vec![
                            Constraint::Fill(10),
                            Constraint::Length(14),
                        ])
                        .split(frame.area());

                    let lower_split = Layout::default()
                        .direction(Direction::Horizontal)
                        .constraints(vec![
                            Constraint::Length(20),
                            Constraint::Fill(10)
                        ]).split(main_vertical[1]);
                    let output_area: Rect = main_vertical[0];
                    let stats_area: Rect = lower_split[0];
                    let filter_area = lower_split[1];


                    let stats = [("Total", state.all_lines.len().to_string()), ("Shown", state.matching_lines.len().to_string()),
                        ("render", render_cnt.to_string())
                    ];
                    render_cnt += 1;
                    frame.render_widget(Block::bordered().title("stats"), stats_area);
                    let mut cur_stat_area = Rect::new(stats_area.x+1, stats_area.y+1, stats_area.width-2, 1);
                    for (key,val ) in stats {
                        let mut key_area = cur_stat_area;
                        key_area.width = 10;
                        let mut value_area = cur_stat_area;
                        value_area.x = 12;
                        value_area.width -= 12;
                        frame.render_widget(Paragraph::new(format!("{}:", key)), key_area);
                        frame.render_widget(Paragraph::new(val), value_area);
                        cur_stat_area.y += 1;
                    }

                    //let mut cur_output_area = Rect::new(output_area.x+1, output_area.y+1, output_area.width-2, 1);
                    //frame.render_widget(Block::bordered().title("Output"), output_area);
                    let mut rows = vec![];
                    for mline in &state.matching_lines {
                        let line = &mline.log_line;

                        let mut message_line = Line::default();
                        mline.hits.visit(mline.log_line.message.len(), |start,end,hit|{
                            message_line.push_span(Span::styled(
                                &line.message[start..end], if hit {
                                    Style::default().fg(color_by_index(mline.tp))
                                } else {
                                    Style::default()
                                }
                            ))
                        });

                        rows.push(Row::new([
                            Line::raw(&line.time),Line::raw(&line.level),Line::raw(&line.target), message_line
                        ]));
                        //frame.render_widget(Paragraph::new(line.to_string()), cur_output_area);
                        //cur_output_area.y += 1;
                        //if cur_output_area.y >= output_area.y + output_area.height-1 {
                         //   break;
                        //}
                    }
                    frame.render_stateful_widget(output_table.clone().
                        rows(rows.clone()), output_area, &mut output_table_state);

                    let mut rows = vec![];
                    for tracepoint in state.tracepoints.iter() {
                        rows.push(Row::new([
                            Line::raw(tracepoint.fingerprint.to_string()).set_style(Style::default().fg(color_by_index(tracepoint.tp.tracepoint))),
                            Line::raw(tracepoint.tp.file.as_path().display().to_string()),
                            Line::raw(tracepoint.tp.line_number.to_string()),
                            Line::raw(if tracepoint.active {"X".to_string()} else {"".to_string()}),
                        ]));
                    }

                    frame.render_stateful_widget(filter_table.clone().
                        rows(rows.clone()), filter_area, &mut filter_table_state);

                    match &mut gui_state {
                        GuiState::Normal => {}
                        GuiState::AddNewFilter(text) => {
                            let area = popup_area(frame.area(), 75);
                            frame.render_widget(Clear, area); //this clears out the background
                            frame.render_widget(&*text, area);
                        }
                    }

                })?;
                last_generation = state.generation;

            }
        }
        if event::poll(Duration::from_millis(100))? {
            let event = event::read()?;
            let mut state = state.lock().unwrap();
            last_generation = u64::MAX;
            match &event {
                Event::Key(KeyEvent{kind: KeyEventKind::Press,code, ..}) => {
                    match &mut gui_state {
                        GuiState::Normal => {
                            match code {
                                KeyCode::Esc | KeyCode::Char('Q')| KeyCode::Char('q')=> {
                                    break Ok(());
                                }
                                KeyCode::Delete if state.active_window == Window::Filter => {
                                    if let Some(index) = filter_table_state.selected() {
                                        state.tracepoints.remove(index);
                                        state.rebuild_trie();
                                        _ = savefile::save_file(LOGDIVER_FILE, 0, &*state);
                                    }
                                }
                                KeyCode::Tab => {
                                    state.active_window = state.active_window.next();
                                }
                                KeyCode::Char('A') | KeyCode::Char('a') => {
                                    let mut text = TextArea::default();
                                    text.set_block(Block::new().borders(Borders::ALL).title("Filter"));
                                    gui_state = GuiState::AddNewFilter(text);
                                }
                                KeyCode::Up => {
                                    match state.active_window {
                                        Window::Filter => {
                                            filter_table_state.select_previous();
                                            state.selected_filter = filter_table_state.selected();
                                        }
                                        Window::Output => {
                                            output_table_state.select_previous();
                                            state.selected_output = output_table_state.selected();
                                        }
                                    }
                                }
                                KeyCode::Down => {
                                    match state.active_window {
                                        Window::Filter => {
                                            filter_table_state.select_next();
                                            state.selected_filter = filter_table_state.selected();
                                        }
                                        Window::Output => {
                                            output_table_state.select_next();
                                            state.selected_output = output_table_state.selected();
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                        GuiState::AddNewFilter(text) => {
                            match code {
                                KeyCode::Esc => {
                                    gui_state = GuiState::Normal;
                                }
                                KeyCode::Enter => {
                                    let fingerprint = text.lines()[0].to_string();
                                    state.add_tracepoint(TracePointData {
                                        fingerprint,
                                        tp: TracePoint {
                                            file: Arc::new(Default::default()),
                                            line_number: 0,
                                            tracepoint: u32::MAX,
                                        },
                                        smart: false,
                                        active: true,
                                    });
                                    gui_state = GuiState::Normal;
                                    _ = savefile::save_file(LOGDIVER_FILE, 0, &*state);
                                }
                                _ => {
                                    text.input(event);
                                }
                            }

                        }
                    }
                }
                _ => {}
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use crate::trie::Trie;

    #[test]
    fn dotest() {
        let mut trie = Trie::new();

        trie.push("Binding to group ", 1);
        trie.push("Joining multicast group  on if ", 2);

        trie.smart_search_fn("Matching key: 66 against [114, 117, 110, 110, 105, 110, 103, 32, 49, 32, 116, 101, 115, 116]", |hit|{
            println!("{:?}", hit);
        });

    }
}