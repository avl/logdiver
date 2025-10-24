extern crate core;

use std::collections::{HashMap, HashSet, VecDeque};
use std::ffi::{OsStr, OsString};
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::{mpsc, Arc, Condvar, Mutex};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::Receiver;
use std::thread::available_parallelism;
use std::time::Duration;
use anyhow::Result;
use crossterm::event::{self, Event};
use indexmap::IndexMap;
use indexmap::map::Entry;
use notify::{Config, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use ratatui::{DefaultTerminal, Frame};

use clap::{Parser, Subcommand};
use clap::parser::Values;
use ratatui::layout::Constraint::Percentage;
use ratatui::prelude::{Color, Style, Stylize};
use ratatui::widgets::{Block, Borders, Row, Table, TableState};
use crate::trie::Trie;

#[derive(Debug, Parser)]
#[command(version, about, long_about = None)]
struct LogdiverArgs {
    /// Path to source of application that is being run
    #[arg(short = 's', long)]
    source: Option<String>,

    values: Vec<String>
}

mod trie {
    use std::fmt::{Debug, Formatter};
    use std::sync::Mutex;
    use memchr::memchr;


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
        fn visit<'a>(&'a self, mut visitor: impl FnMut(u8, &'a V)) {
            match self {
                TinyMap::Inline(count, keys, values) => {
                    for i in 0..*count {
                        visitor(keys[i as usize], values[i as usize].as_ref().unwrap());
                    }
                }
                TinyMap::Heap(keys, values) => {
                    for (key,val) in keys.iter().zip(values.iter()) {
                        visitor(*key,val);
                    }
                }
            }
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
        pub fn smart_search<'a>(&'a self, mut key: &[u8], hit: &mut impl FnMut(&'a V)) {
            match self {
                TrieNode::Head { map, value } => {
                    if let Some(v) = value.as_ref() {
                        hit(v);
                    }
                    if key.is_empty() {
                        return;
                    }

                    map.visit(|haystack_key, haystack_value|{
                        //println!("Matching key: {:?} against {:?}", haystack_key, key);
                        if let Some(index) = memchr(haystack_key, &key[0..]) {
                            //println!("Found it, at index {}, cont with  {:?}", index, &key[index+1..]);
                            haystack_value.smart_search(&key[index+1..], hit);
                        }
                    });
                }
                TrieNode::Tail { tail, value:Some(value) } => {
                    for needle in tail {
                        if let Some(index) = memchr(*needle, &key[0..]) {
                            key = &key[index+1..];
                        } else {
                            return;
                        }
                    }
                    hit(value)
                }
                _ => {}
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
        pub fn smart_search_fn(&self, key: &str, mut hit: impl FnMut(&V)) {
            self.top.smart_search(key.as_bytes(), &mut hit)
        }
        pub fn smart_search(&self, key: &str) -> Vec<&V> {
            let mut t = Vec::new();
            self.top.smart_search(key.as_bytes(), &mut |v|t.push(v));
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



fn parse_delta(prev: &str, now: &str, path: &Arc<PathBuf>, tx: &mut mpsc::SyncSender<DiverEvent>) {
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
        fingerprint(line, &mut finger);
        if !finger.is_empty() {
            let tp = TracePoint {
                file: path.clone(),
                line_number,
            };
            let tp = TracePointData {
                fingerprint: finger,
                tp,
                active: false,
            };
            tx.send(DiverEvent::SourceChanged(tp)).unwrap();
        }
    }
}

fn fingerprint(line: &str, fingerprint: &mut String) -> Option<()> {
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

impl State {
    fn check_matching(
        fingerprint_trie: &mut Trie<TracePoint>,
        matching_lines: &mut Vec<String>,
        line: &str) {
        fingerprint_trie.smart_search_fn(line,|hit|{
            matching_lines.push(line.to_string());
        });
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
                state.fingerprint_trie.push(&tp.fingerprint, tp.tp);
                state.generation += 1;

                state.matching_lines.clear();
                for line in &state.all_lines {
                    // Also, add a "recent fingerprints" section in ratatui
                    State::check_matching(&mut state.fingerprint_trie, &mut state.matching_lines, line);
                }
            }
            DiverEvent::ProgramOutput(line) => {
                State::check_matching(&mut state.fingerprint_trie, &mut state.matching_lines, &line);
                state.all_lines.push_back(line);
            }
        }
    }
}

fn capturer(args: LogdiverArgs, program_lines: mpsc::SyncSender<DiverEvent>) {
    println!("Args values: {:?}", &args.values);
    let mut arg_iter = args.values.into_iter();
    let cmd = arg_iter.next().unwrap();
    let rest: Vec<_> = arg_iter.collect();
    let mut child = Command::new(cmd)
        .args(&rest)
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to execute process"); //TODO, error handling
    use std::io::Read;
    //let mut all_lines = VecDeque::new();
    if let Some(child_out) = child.stdout {
        let child_out = BufReader::new(child_out);

        for line in child_out.lines() {
            let line = line.unwrap(); //TODO: Error handling

            /*let value = gjson::parse(&line);
            value.each(|key, value| {
                match key.str() {
                    "fields" => {
                        let value = value.get("message");
                        println!("message: {}", value);
                    }
                    "target" => {
                        println!("target: {}", value);
                    }
                    "level" => {
                        println!("Level: {}", value);
                    }
                    "timestamp" => {
                        println!("Time: {}", value);
                    }
                    _ => {}
                };
                true
            });*/
            //println!("Read line {}", line);
            program_lines.send(DiverEvent::ProgramOutput(line.clone())).unwrap();
        }
    }
}

#[derive(Debug)]
struct TracePoint {
    file: Arc<PathBuf>,
    line_number: usize,
}

pub enum DiverEvent {
    SourceChanged(TracePointData),
    ProgramOutput(String),
}

struct TracePointData {
    fingerprint: String,
    tp: TracePoint,
    active: bool,
}

#[derive(Default)]
struct State {
    fingerprint_trie: Trie<TracePoint>,
    all_lines: VecDeque<String>,
    matching_lines: Vec<String>,
    tracepoints: Vec<TracePointData>,
    generation: u64,
}

fn main() -> Result<()> {

    let args = LogdiverArgs::parse();
    let src = args.source.clone().unwrap_or(".".into());
    // Add a path to be watched. All files and directories at that path and
    // below will be monitored for changes.
    let pathbuf = PathBuf::from(&src);

    let state = Arc::new(Mutex::new(State::default()));

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



    compile_error!("Continue with some stats-printing, so we can troubleshoot")


    /*
result*/

    let (tx, rx) = std::sync::mpsc::channel();

    // Automatically select the best implementation for your platform.
    // You can also access each implementation directly e.g. INotifyWatcher.
    let mut watcher = RecommendedWatcher::new(tx, Config::default())?;
    watcher.watch(&pathbuf, RecursiveMode::Recursive)?;

    let (diver_events_tx, diver_events_rx) = mpsc::sync_channel(16384);
    let mut source_line_change_tx = diver_events_tx.clone();


    std::thread::spawn(move||capturer(args, diver_events_tx));


    let state2 = state.clone();
    std::thread::spawn(move||{
        mainloop(diver_events_rx, state2);
    });

    std::thread::spawn(move||{

        let rs = OsString::from("rs");
        for res in rx {
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

                                    if let Ok(contents) = std::fs::read_to_string(&path) {
                                        match tot_results.entry(path.clone()) {
                                            Entry::Occupied(mut prev_entry) => {
                                                let path = Arc::new(path);
                                                let prev_value = prev_entry.get();

                                                parse_delta(prev_value, &contents, &path, &mut source_line_change_tx);

                                                *prev_entry.get_mut() = contents;
                                            }
                                            Entry::Vacant(v) => {
                                                v.insert(contents);
                                            }
                                        }
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
        }

    });


    let terminal = ratatui::init();

    let result = run(terminal, state);
    ratatui::restore();


    Ok(())
}

trait BlockExt: Sized {
    fn highlight(self, our_index: usize, active_highlight: usize) -> Self;
}

impl<'a> BlockExt for Block<'a> {
    fn highlight(self, our_index: usize, active_highlight: usize) -> Block<'a> {
        if our_index == active_highlight {
            self.border_style(Style::default().bg(Color::White).fg(Color::Black))
        } else {
            self
        }
    }
}
fn run(mut terminal: DefaultTerminal, state: Arc<Mutex<State>>) -> Result<()> {
    let rows: [Row; 0] = [];

    let fingerprint_table = Table::new(rows.clone(), [Percentage(50), Percentage(50)])
        .block(Block::new().title("Fingerprints"))
        .header(Row::new(vec!["Fingerprint", "File", "Line"]))
        .row_highlight_style(Style::new().reversed());

    let fingerprint_block = Block::new()
        .borders(Borders::ALL)
        .title("Fingerprints")
        .highlight(0, 0);


    let mut fingerprint_table_state = TableState::default();
    let mut last_generation = u64::MAX;
    loop {


        {
            let state = state.lock().unwrap();
            if last_generation != state.generation {
                terminal.draw( |frame|{
                    let frame_area = frame.area();
                    let mut rows = vec![];
                    for tracepoint in state.tracepoints.iter() {
                        rows.push(Row::new([tracepoint.fingerprint.to_string(), tracepoint.tp.file.as_path().display().to_string(), tracepoint.tp.line_number.to_string() ]));
                    }

                    frame.render_stateful_widget(fingerprint_table.clone().
                        rows(rows.clone()).block(fingerprint_block.clone()), frame_area, &mut fingerprint_table_state);
                })?;
                last_generation = state.generation;

            }
        }
        if event::poll(Duration::from_millis(100))? {
            match event::read()? {
                Event::Key(key) => {
                    break Ok(());
                }
                _ => {}
            }
        }
    }
}
/*
fn render(frame: &mut Frame) {
    frame.render_widget("logdiver", frame.area());
}*/

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