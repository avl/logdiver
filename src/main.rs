extern crate core;

use anyhow::{Context, Result, anyhow, bail};
use clap::{Parser};
use indexmap::{IndexMap, map::Entry};
use itertools::Itertools;
use notify::{Config, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use ratatui::{
    DefaultTerminal,
    crossterm::event::{self, Event, KeyCode, KeyEvent, KeyEventKind},
    layout::{Flex, Size},
    palette::{Hsl, RgbHue, encoding::Srgb, rgb::Rgb},
    prelude::{Color, Constraint, Direction, Layout, Line, Rect, Style, Stylize},
    style::Styled,
    text::Span,
    widgets::{Block, Borders, Clear, Paragraph, Row, Table, TableState},
};
use savefile::{
    Deserialize, Deserializer, LittleEndian, Serialize, Serializer,
    prelude::{ReadBytesExt, Savefile},
};
use std::{
    collections::{BinaryHeap, HashMap, VecDeque},
    ffi::OsString,
    fmt::{Debug, Display, Formatter},
    fs::File,
    io::{BufRead, BufReader, BufWriter, Cursor, Read, Write},
    net::{TcpListener, TcpStream},
    panic::catch_unwind,
    path::PathBuf,
    process::{Child, Command, Stdio},
    sync::{
        Arc, Condvar, Mutex, Weak,
        atomic::{AtomicUsize, Ordering},
        mpsc,
    },
    time::{Duration, Instant},
};
use std::borrow::Cow;
use memchr::memchr;
use ratatui::crossterm::event::KeyModifiers;
use tui_textarea::TextArea;

mod line_parser;
mod trie;

use crate::trie::{Trie, TrieKey};

const MAX_LINES: usize = 1_000_000;

const AFTER_HELP: &str = "
Examples:
    logdiver path/to/some/executable
    logdiver -- path/to/some/executable --parameter-to-executable=1
";

#[derive(Debug, Parser)]
#[command(version, about, long_about = None, after_help = AFTER_HELP)]
struct LogdiverArgs {
    /// Path to source of application that is being run
    #[arg(short = 's', long)]
    source: Option<String>,

    #[arg(long, hide = true)]
    debug_notify: bool,

    #[arg(long, hide = true)]
    debug_capturer: bool,

    #[arg(long, hide = true)]
    daemon: bool,

    values: Vec<String>,
}

pub trait ReadSavefileExt: Read {
    fn read_msg<T: Deserialize>(&mut self) -> Result<T> {
        let size = self.read_u32::<LittleEndian>()?;
        let mut buf = vec![0; size as usize];
        self.read_exact(&mut buf[..])?;
        let t = Deserializer::bare_deserialize(&mut Cursor::new(buf), 0)?;
        Ok(t)
    }
}

pub trait WriteSavefileExt: Write {
    fn write_msg<T: Serialize>(&mut self, obj: &T) -> Result<()> {
        let mut buf = Vec::new();
        Serializer::bare_serialize(&mut buf, 0, obj)?;
        use byteorder::WriteBytesExt;
        self.write_u32::<LittleEndian>(buf.len() as u32)?;
        self.write_all(&buf)?;
        Ok(())
    }
}
impl<T> ReadSavefileExt for T where T: Read {}
impl<T> WriteSavefileExt for T where T: Write {}

fn defstyle() -> Style {
    Style::new()
        .bg(Color::Rgb(192, 192, 192))
        .fg(Color::Rgb(0, 0, 0))
}
fn parse_delta(prev: &str, now: &str, path: &Arc<PathBuf>, tx: &Buffer, debug_notify: bool) {
    let mut prev_lines = HashMap::<&str, usize>::new();
    for line in prev.lines() {
        *prev_lines.entry(line).or_default() += 1;
    }
    for (line_number, line) in now.lines().enumerate() {
        let line_number = line_number + 1; //Editors count 1 as first line
        if let Some(x) = prev_lines.get_mut(line) {
            if *x >= 1 {
                *x -= 1;
                continue;
            }
        }
        let mut finger = Vec::new();

        fingerprint(line, &mut finger);

        if !finger.is_empty() {
            let tp = TracePoint {
                file: path.clone(),
                line_number,
                tracepoint: u32::MAX,
            };
            if debug_notify {
                println!("New tracepoint: {:?}", finger);
            }
            let tp = TracePointData {
                fingerprint: Fingerprint(finger),
                tp,
                active: line.trim_end().ends_with("//"),
                matches: 0,
            };
            tx.push(tp);
        }
    }
}

fn fingerprint(line: &str, fingerprint: &mut Vec<TrieKey>) -> Option<()> {
    let mut tokens = line.chars().peekable();
    let mut wild = true;
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
                    wild = true;
                    depth += 1;
                } else if tok == '}' {
                    depth -= 1;
                } else {
                    if depth == 0 {
                        let mut buf = [0; 4];
                        let bytes = tok.encode_utf8(&mut buf).as_bytes();
                        for byt in bytes {
                            if wild {
                                fingerprint.push(TrieKey::WildcardThen(*byt));
                            } else {
                                fingerprint.push(TrieKey::Exact(*byt));
                            }
                            wild = false;
                        }
                    }
                }
            }
        }
    }
}

#[derive(Savefile, Default, Clone, Debug)]
struct MatchSequence {
    range: Vec<(u32, u32)>,
}

impl MatchSequence {
    pub fn clear(&mut self) {
        self.range.clear();
    }
    #[allow(unused)]
    pub fn is_empty(&self) -> bool {
        self.range.is_empty()
    }
    #[allow(unused)]
    pub(crate) fn visit(&self, len: usize, mut visitor: impl FnMut(usize, usize, bool)) {
        let mut expected_start = 0;
        for (start, end) in &self.range {
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
        if let Some(last) = self.range.last_mut()
            && index == 0
        {
            last.1 += 1;
            return;
        }
        if let Some(last) = self.range.last().map(|x| x.1) {
            self.range.push((last + index, last + index + 1));
        } else {
            self.range.push((index, index + 1));
        }
    }
    pub fn save(&mut self) -> Restore {
        Restore {
            range_count: self.range.len() as u32,
            end_at: self.range.last().map(|x| x.1).unwrap_or(0),
        }
    }
    pub fn restore(&mut self, restore: Restore) {
        self.range.truncate(restore.range_count as usize);
        if let Some(last) = self.range.last_mut() {
            last.1 = restore.end_at;
        }
    }
}

impl State {
    /// Return all matches of the expressions in Trie to the 'line'
    fn get_matches(fingerprint_trie: &mut Trie<TracePoint>, line: &LogLine) -> Vec<TpMatch> {

        let mut tps = Vec::new();
        fingerprint_trie.search_fn(&line.message, |hit, m| {
            tps.push((hit.tracepoint, m.clone()));
            true
        });

        if !tps.is_empty() {
            let matches = tps
                .into_iter()
                .map(|(tp, matchseq)| TpMatch { tp, hits: matchseq })
                .collect();

            matches
        } else {
            Vec::new()
        }
    }
    /// Check if 'line' matches the filter, and adds it to the `matching_lines`
    fn check_matching(
        fingerprint_trie: &mut Trie<TracePoint>,
        matching_lines: &mut VecDeque<Arc<LogLine>>,
        trace_point_data: &mut [TracePointData],
        line: &Arc<LogLine>,
    ) {

        let mut any_hit = false;
        let len = trace_point_data.iter().filter(|x|x.active).count();
        fingerprint_trie.search_fn_fast(&line.message, |hit| {
            trace_point_data[hit.tracepoint as usize].matches += 1;
            any_hit = true;
        }, len);

        if any_hit {
            matching_lines.push_back(line.clone());
        }
    }
    fn add_tracepoint_trie(trie: &mut Trie<TracePoint>, tp: &TracePointData) {
        trie.push(&tp.fingerprint.0, tp.tp.clone());
    }
    fn rebuild_trie(&mut self) {
        self.fingerprint_trie = Trie::new();
        for (i, tp) in self.tracepoints.iter_mut().enumerate() {
            tp.tp.tracepoint = i as u32;
            if tp.active {
                Self::add_tracepoint_trie(&mut self.fingerprint_trie, tp);
            }
        }

        self.rebuild_matches()
    }
    fn rebuild_matches(&mut self) {
        self.generation += 1;

        self.matching_lines.clear();
        for tp in &mut self.tracepoints {
            tp.matches = 0;
        }
        for line in &self.all_lines {
            // Also, add a "recent fingerprints" section in ratatui
            State::check_matching(
                &mut self.fingerprint_trie,
                &mut self.matching_lines,
                &mut self.tracepoints[..],
                line,
            );
        }
    }
}

impl State {
    fn add_tracepoint(&mut self, mut tp: TracePointData) {
        let any_active = self.tracepoints.iter().any(|x| x.active);

        if let Some(prev_tp) = self
            .tracepoints
            .iter_mut()
            .find(|x| x.fingerprint == tp.fingerprint && x.tp.file == tp.tp.file)
        {
            if prev_tp.active && tp.active {
                return;
            }
            if !prev_tp.active && !tp.active {
                return;
            }
            prev_tp.active = tp.active;
            drop(tp);
            if !prev_tp.active {
                // This tp was inactivated
                self.rebuild_trie();
            } else {
                // This tp was activated
                Self::add_tracepoint_trie(&mut self.fingerprint_trie, &prev_tp);
            }
        } else {
            let mut indices: Vec<_> = self.tracepoints.iter().map(|x| x.tp.tracepoint).collect();
            indices.sort();
            let tp_index = if let Some(_hole) = indices.windows(2).find(|xs| xs[1] != xs[0] + 1) {
                panic!("Holes shouldn't exist");
            } else {
                indices.len() as u32
            };

            tp.tp.tracepoint = tp_index;
            if tp.active {
                Self::add_tracepoint_trie(&mut self.fingerprint_trie, &tp);
            }

            self.tracepoints.push(tp);
        }
        if !any_active && !self.do_filter {
            self.do_filter = true;
        }
        self.rebuild_matches();
    }

    fn focus_current_tracepoint(&mut self, back: bool) -> Option<usize> {
        if let Some(filter) = self.selected_filter {
            if self.matching_lines.is_empty() {
                return None;
            }
            let mut start = self.selected_output.unwrap_or(if back  {0} else {self.matching_lines.len().saturating_sub(1)} );

            let mut trie = Trie::new();
            Self::add_tracepoint_trie(&mut trie, &self.tracepoints[filter]);
            let mut visited_count = 0;
            let total_count = self.matching_lines.len();
            let mut cur = start;
            let mut next = ||{
                if visited_count == total_count {
                    return None;
                }
                visited_count +=1;
                if back {
                    cur = cur.checked_sub(1).unwrap_or(total_count.saturating_sub(1));
                } else {
                    cur=cur + 1;
                    if cur >= total_count {
                        cur = 0;
                    }
                }
                Some(cur)
            };


            while let Some(i) = next() {
                let message = &self.matching_lines[i];
                let mut have_hit = false;
                trie.search_fn_fast(&message.message, |hit| {
                    have_hit = true;
                }, 1);
                if have_hit {
                    self.selected_output = Some(i);
                    return Some(i);
                }
            };
        }
        None
    }

    fn save(&self) {
        let mut f = BufWriter::new(File::create(LOGDIVER_FILE).unwrap());
        Serializer::save(&mut f, 0, self, false).unwrap();
        f.flush().unwrap();
    }
}

fn mainloop(program_lines: mpsc::Receiver<DiverEvent>, state: Arc<Mutex<State>>) {
    while let Ok(event) = program_lines.recv() {
        let mut state = state.lock().unwrap();
        let state = &mut *state;
        match event {
            DiverEvent::SourceChanged(tp) => {
                state.add_tracepoint(tp);
                state.save();
            }
            DiverEvent::ProgramOutput(lines) => {
                lines.with_each(|line|{
                    state.total += 1;
                    if state.pause {
                        return;
                    }
                    let line = Arc::new(line);
                    State::check_matching(
                        &mut state.fingerprint_trie,
                        &mut state.matching_lines,
                        &mut state.tracepoints,
                        &line,
                    );
                    state.all_lines.push_back(line);
                    if state.all_lines.len() > MAX_LINES {
                        state.all_lines.pop_front();
                    }
                    if state.matching_lines.len() > MAX_LINES {

                        let front = state.matching_lines.pop_front().unwrap();
                        for m in State::get_matches(&mut state.fingerprint_trie, &*front) {
                            state.tracepoints[m.tp as usize].matches -= 1;
                        }
                    }
                    state.generation += 1;
                });
            }
        }
    }
}

#[derive(Default)]
struct ReadManyLines {
    scratch: Vec<u8>,

}

impl ReadManyLines  {
    fn append(candidate: &[u8], f: &mut impl FnMut(&str)) {
        match String::from_utf8_lossy(candidate){
            Cow::Borrowed(x) => {
                f(x);
            }
            Cow::Owned(o) => {
                f(&o);
            }
        }
    }
    fn read_many_lines<T:Read>(&mut self, read: &mut BufReader<T>, mut f: impl FnMut(&str)) -> Result<()> {
        let mut buf = read.fill_buf()?;
        let mut l = 0;
        let mut limit = 0;
        while let Some(index) = memchr(b'\n', buf) {
            if !self.scratch.is_empty() {
                self.scratch.extend(&buf[..index]);
                Self::append(&self.scratch, &mut f);
                self.scratch.clear();
            } else {
                Self::append( &buf[..index], &mut f);
            }
            buf = &buf[index + 1..];
            l += index + 1;
            limit += 1;
            if limit > 200 {
                read.consume(l);
                return Ok(());
            }

        }
        if !buf.is_empty() {
            l += buf.len();
            self.scratch.extend(buf);
        }
        read.consume(l);

        Ok(())
    }
}

fn capturer(child_out: impl Read, program_lines: mpsc::SyncSender<DiverEvent>, _is_stdout: bool) -> Result<()>{


    let mut child_out = BufReader::new(child_out);

    let mut line_buf = ReadManyLines::default();


    loop {

        let mut loglines = LogLines::None;

        //let mut count = 0;
        line_buf.read_many_lines(&mut child_out, |raw_line|{
            {
                let line:&str;
                let temp;
                if memchr(b'\x1b', raw_line.as_bytes()).is_none() {
                    line = raw_line;
                } else {
                    temp = strip_ansi_codes(&raw_line);
                    line = &temp;
                };
                /*count += 1;
                let line = format!("{}:{}",line, count);*/

                let value = gjson::parse(&line);
                let mut message = String::new();
                let mut target = String::new();
                let mut level = String::new();
                let mut timestamp = String::new();
                let mut fields = String::new();
                value.each(|key, value| {
                    match key.str() {
                        "fields" => {
                            value.each(|key, value| {
                                if key.str() == "message" {
                                    message = value.to_string();
                                } else {
                                    use std::fmt::Write;
                                    write!(&mut fields, "{} = {}, ", key.str(), value.str()).unwrap();
                                }
                                true
                            });
                        }
                        "target" => {
                            target = value.to_string();
                        }
                        "level" => {
                            level = value.to_string();
                        }
                        "timestamp" => {
                            timestamp = value.to_string();
                        }
                        _ => {}
                    };
                    true
                });

                // If no message was extracted from JSON, use the entire line as the message
                if message.is_empty() {

                    // At some point we may figure out how to correctly parse "pretty" tracing
                    // output and/or "full" tracing output (i.e, non json based):
                    /*if let Some(line) = parse_log_line(&line) {
                        timestamp = line.time;
                        target = line.namespace;
                        level = line.level;
                        message = line.message;
                        fields = line.meta;
                    } else {*/

                    timestamp = "".to_string();
                    target = "".to_string();
                    level = "".to_string();
                    message = line.to_string();
                    fields = "".to_string();

                    //}
                }
                loglines.append(LogLine {
                    time: timestamp,
                    target,
                    level,
                    message,
                    fields,
                });
            }

        })?;



        program_lines
            .send(DiverEvent::ProgramOutput(loglines))
            .unwrap();
    }
}

#[derive(Savefile, Debug, Clone)]
struct TracePoint {
    file: Arc<PathBuf>,
    line_number: usize,
    tracepoint: u32,
}

pub enum DiverEvent {
    SourceChanged(TracePointData),
    ProgramOutput(LogLines),
}
enum LogLines {
    None,
    Line(LogLine),
    Lines(Vec<LogLine>)
}

impl LogLines {
    pub fn with_each(self, mut f: impl FnMut(LogLine)) {
        match self {
            LogLines::None => {}
            LogLines::Line(l) => {
                f(l);
            }
            LogLines::Lines(v) => {
                for x in v {
                    f(x)
                }

            }
        }
    }
    pub fn append(&mut self, logline: LogLine) {
        match self {
            LogLines::None => {
                *self = LogLines::Line(logline);
            }
            LogLines::Line(line0) => {
                let line = std::mem::replace(self, LogLines::None);
                if let LogLines::Line(line0) = line {
                    *self = LogLines::Lines(vec![
                        line0, logline
                    ]);
                } else {
                    unreachable!()
                };
            }
            LogLines::Lines(v) => {
                v.push(logline);
            }
        }
    }
}

#[derive(Savefile, Clone, PartialEq)]
pub struct Fingerprint(Vec<TrieKey>);

impl Debug for Fingerprint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Fingerprint({})", self)
    }
}
impl Fingerprint {
    pub fn parse(s: &str) -> Fingerprint {
        let mut t = Vec::new();
        let mut wild = true;

        for c in s.as_bytes() {
            if *c == b'*' {
                wild = true;
                continue;
            }
            if wild {
                wild = false;
                t.push(TrieKey::WildcardThen(*c));
            } else {
                t.push(TrieKey::Exact(*c));
            }
        }
        if t.is_empty() {
            if s.contains('*') {
                t.push(TrieKey::Any);
            }
        }

        Fingerprint(t)
    }
}

impl Display for Fingerprint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut output = Vec::new();
        for key in self.0.iter() {
            match *key {
                TrieKey::Eof => {
                    output.push(b'$');
                }
                TrieKey::Exact(b) => {
                    output.push(b);
                }
                TrieKey::WildcardThen(b) => {
                    output.push(b'*');
                    output.push(b);
                }
                TrieKey::Any => {
                    output.push(b'*');
                }
            }
        }
        let output = String::from_utf8(output).unwrap();
        write!(f, "{output}")
    }
}

#[derive(Savefile, Clone, Debug)]
pub struct TracePointData {
    fingerprint: Fingerprint,

    tp: TracePoint,
    active: bool,
    matches: usize,
}

#[derive(Clone)]
pub struct LogLine {
    time: String,
    target: String,
    level: String,
    message: String,
    fields: String,
}

#[derive(Eq, PartialEq, Clone, Copy, Default, Savefile)]
enum Window {
    #[default]
    Filter,
    Output,
}
impl Window {
    fn next(&self) -> Window {
        match self {
            Window::Filter => Self::Output,
            Window::Output => Self::Filter,
        }
    }
}

struct TpMatch {
    tp: u32,
    hits: MatchSequence,
}


#[derive(Default, Savefile)]
struct State {
    #[savefile_ignore]
    #[savefile_introspect_ignore]
    fingerprint_trie: Trie<TracePoint>,
    #[savefile_ignore]
    #[savefile_introspect_ignore]
    all_lines: VecDeque<Arc<LogLine>>,
    #[savefile_ignore]
    #[savefile_introspect_ignore]
    total: usize,
    #[savefile_ignore]
    #[savefile_introspect_ignore]
    matching_lines: VecDeque<Arc<LogLine>>,
    tracepoints: Vec<TracePointData>,
    #[savefile_ignore]
    generation: u64,
    active_window: Window,
    selected_filter: Option<usize>,
    #[savefile_ignore]
    selected_output: Option<usize>,
    show_target: bool,
    plain: bool,
    fields: bool,
    do_filter: bool,
    #[savefile_ignore]
    sidescroll: usize,
    light_mode: Option<bool>,
    #[savefile_ignore]
    pause: bool
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
        (other.at, &other.path).cmp(&(self.at, &self.path))
    }
}

const LOGDIVER_FILE: &str = ".logdiver.bin";

// Code credit: Claude
fn strip_ansi_codes(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars();

    while let Some(ch) = chars.next() {
        if ch == '\x1b' {
            // ANSI escape sequence starts with ESC ([)
            if chars.next() == Some('[') {
                // Skip until we find a letter (the command character)
                for ch in chars.by_ref() {
                    if ch.is_ascii_alphabetic() {
                        break;
                    }
                }
            }
        } else if ch == '\r' || ch == '\x08' {
            // Skip carriage return and backspace
            continue;
        } else if ch.is_control() && ch != '\n' && ch != '\t' {
            // Skip other control characters except newline and tab
            continue;
        } else {
            result.push(ch);
        }
    }

    result
}

#[derive(Clone)]
struct BufferElement {
    data: TracePointData,
    seen_by: usize,
}

#[derive(Default)]
struct BufferInner {
    clients: Arc<()>,
    start_index: usize,
    buffer: VecDeque<BufferElement>,
}
struct ClientHandle {
    // The handle must be retained to make the client count
    // knowable
    #[allow(unused)]
    handle: Weak<()>,
    next_index: usize,
}
#[derive(Default)]
struct Buffer {
    inner: Mutex<BufferInner>,
    cond: Condvar,
}
impl Buffer {
    fn new_client(&self) -> ClientHandle {
        let inner = self.inner.lock().unwrap();
        ClientHandle {
            handle: Arc::downgrade(&inner.clients),
            next_index: inner.start_index + inner.buffer.len(),
        }
    }
    fn push(&self, data: TracePointData) {
        let mut inner = self.inner.lock().unwrap();
        inner.buffer.push_back(BufferElement { data, seen_by: 0 });
        let count = Arc::weak_count(&inner.clients);
        while let Some(front) = inner.buffer.front() {
            if front.seen_by >= count {
                inner.start_index += 1;
                inner.buffer.pop_front();
            } else {
                break;
            }
        }
        self.cond.notify_all();
    }
    fn receive(&self, client: &mut ClientHandle) -> TracePointData {
        let mut inner = self.inner.lock().unwrap();
        loop {
            if client.next_index < inner.start_index {
                client.next_index = inner.start_index;
            }
            let idx = client.next_index - inner.start_index;
            if idx < inner.buffer.len() {
                let entry = &mut inner.buffer[idx];
                entry.seen_by += 1;
                client.next_index += 1;
                return entry.data.clone();
            }
            inner = self.cond.wait(inner).unwrap();
        }
    }
}

fn scan_source(pathbuf: PathBuf, buffer: Arc<Buffer>, debug: bool) {
    let mut tasks = VecDeque::new();
    let (tx, rx) = std::sync::mpsc::channel();

    tasks.push_back(pathbuf.clone());
    let tasks = Arc::new(Mutex::new(tasks));
    let condvar = Arc::new(Condvar::new());
    let mut threads = vec![];
    let thread_count: u64 = ((std::thread::available_parallelism()
        .map(|x| x.get())
        .unwrap_or(0usize) as u64)
        / 2)
    .max(1);
    let shift = 64 - thread_count.leading_zeros();
    let in_prog = Arc::new(AtomicUsize::new(1));
    for thread in 0..thread_count {
        let rs = OsString::from("rs");
        let tasks = tasks.clone();
        let condvar = condvar.clone();
        let in_prog = in_prog.clone();
        let mut results = IndexMap::new();
        threads.push(std::thread::spawn(move || {
            let target_dir = PathBuf::from("./target");
            let mut process_now = Vec::new();
            let mut process_soon = Vec::new();
            loop {
                let mut tasks_guard = tasks.lock().unwrap();

                let work_remaining = tasks_guard.len();
                let count = (work_remaining >> shift).max(1).min(work_remaining);

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
                    if dir == target_dir {
                        //TODO: At some point we may want to not hardcode this
                        continue;
                    }
                    if let Ok(dir) = std::fs::read_dir(dir) {
                        for entry in dir.into_iter() {
                            if let Ok(entry) = entry {
                                if let Ok(meta) = entry.metadata() {
                                    if meta.is_dir() {
                                        process_soon.push(entry.path());
                                    }
                                    if meta.is_file() {
                                        let path = entry.path();
                                        if path.extension() == Some(&rs) {
                                            if let Ok(canon) = std::fs::canonicalize(path) &&
                                                let Ok(contents) = std::fs::read_to_string(&canon) {
                                                results.insert(canon, contents);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                in_prog.fetch_add(process_soon.len(), Ordering::Relaxed);
                in_prog.fetch_sub(count, Ordering::Relaxed);
                let mut tasks_guard = tasks.lock().unwrap();
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
    for thread in threads {
        tot_results.extend(thread.join().unwrap());
    }
    if debug {
        println!("Initial scan done");
    }

    let mut watcher = RecommendedWatcher::new(tx, Config::default()).unwrap();
    watcher.watch(&pathbuf, RecursiveMode::Recursive).unwrap();

    let mut source_line_change_tx = buffer.clone();

    let mut debouncing = BinaryHeap::<Debounced>::new();

    let rs = OsString::from("rs");
    loop {
        let mut next_debounce_at = Duration::from_secs(60);
        if let Some(top) = debouncing.peek() {
            next_debounce_at = top.at.saturating_duration_since(Instant::now());
        }

        let res = rx.recv_timeout(next_debounce_at);

        if let Ok(res) = res {
            match res {
                Ok(event) => {
                    match event.kind {
                        EventKind::Any => {}
                        EventKind::Access(_) => {}
                        EventKind::Create(_) | EventKind::Modify(_) => {
                            for path in event.paths {
                                if path.extension() == Some(&rs) {
                                    if let Ok(path) = std::fs::canonicalize(path)
                                     && let Ok(meta) = std::fs::metadata(&path) {
                                        if !meta.is_file() {
                                            continue;
                                        }
                                        debouncing.push(Debounced {
                                            at: Instant::now() + Duration::from_millis(500),
                                            path,
                                            size: meta.len(),
                                            debouncing_iterations: 0,
                                        });
                                    }
                                }
                            }
                        }
                        EventKind::Other | EventKind::Remove(_) => {}
                    }
                }
                Err(_error) => {
                    //TODO: Log somewhere? (probably add '--debuglog' option
                }
            }
        } else {
            if let Some(mut debounced) = debouncing.pop() {
                if debug {
                    println!("Bounce-checking {}", debounced.path.as_path().display());
                }

                if let Ok(meta) = std::fs::metadata(&debounced.path) {
                    if meta.len() != debounced.size {

                        debounced.at = Instant::now()
                            + Duration::from_millis(
                                (100 * (1 << debounced.debouncing_iterations)).min(2000),
                            );
                        debounced.size = meta.len();
                        debounced.debouncing_iterations += 1;
                        debouncing.push(debounced);
                    } else {
                        if debug {
                            println!("Path: {}", debounced.path.as_path().display());
                        }
                        if let Ok(contents) = std::fs::read_to_string(&debounced.path) {
                            match tot_results.entry(debounced.path.clone()) {
                                Entry::Occupied(mut prev_entry) => {
                                    let prev_value = prev_entry.get();
                                    if contents.len() < prev_value.len().saturating_sub(40)
                                        && debounced.debouncing_iterations < 3
                                    {
                                        debounced.at = Instant::now() + Duration::from_millis(2000);
                                        debounced.size = meta.len();
                                        debounced.debouncing_iterations = 3;
                                        debouncing.push(debounced);
                                        continue;
                                    }
                                    let path = Arc::new(debounced.path);

                                    parse_delta(
                                        prev_value,
                                        &contents,
                                        &path,
                                        &mut source_line_change_tx,
                                        false,
                                    );

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
}

fn run_daemon(source: PathBuf, debug: bool) {
    let tcp = TcpListener::bind("127.0.0.1:0").unwrap();
    std::fs::write(
        ".logdiver.port",
        tcp.local_addr().unwrap().port().to_string(),
    )
    .unwrap();
    let buffer2 = Arc::new(Buffer::default());
    let buffer = buffer2.clone();
    {
        let source = source.clone();
        let buffer = buffer.clone();
        std::thread::spawn(move || {
            scan_source(source, buffer, debug);
        });
    }
    loop {
        if let Ok((mut client_stream, _)) = tcp.accept() {
            let source = source.clone();
            let buffer = buffer.clone();
            std::thread::spawn(move || {
                let mut client_obj = buffer.new_client();
                client_stream
                    .write_msg(&source.display().to_string())
                    .unwrap();
                let cmd = client_stream.read_msg::<String>().unwrap();
                if cmd == "QUIT" {
                    std::process::exit(1);
                }
                loop {
                    let next = buffer.receive(&mut client_obj);
                    if client_stream.write_msg(&next).is_err() {
                        break;
                    }
                }
            });
        }
    }
}

struct KillOnDrop(Child);

impl Drop for KillOnDrop {
    fn drop(&mut self) {
        _ = self.0.kill();
    }
}

fn main() -> Result<()> {

    let args = LogdiverArgs::parse();
    if args.values.is_empty() {
        eprintln!("Please provide the name of the application to run as an argument");
        std::process::exit(1);
    }
    let src = args.source.clone().unwrap_or(".".into());
    // Add a path to be watched. All files and directories at that path and
    // below will be monitored for changes.
    let pathbuf = PathBuf::from(&src);

    let state = Arc::new(Mutex::new(
        savefile::load_file(LOGDIVER_FILE, 0)
            .map(|mut state: State| {
                state.rebuild_trie();
                state
            })
            .unwrap_or_else(
                |_e|{let mut t = State::default();
                    t.plain = true;
                    t
                }),
    ));
    let light_mode =
        state.lock().unwrap().light_mode.unwrap_or_else(||
        terminal_light::luma().map(|luma| luma > 0.6).unwrap_or(false));

    if args.daemon {
        run_daemon(args.source.unwrap().into(), args.debug_notify);
    }

    let mut iter = 0;
    let (diver_events_tx, diver_events_rx) = mpsc::sync_channel(4096);

    loop {
        std::thread::sleep(Duration::from_millis(20));
        if let Ok(contents) = std::fs::read_to_string(".logdiver.port") {
            let tcpport: u16 = contents.parse::<u16>().unwrap();
            let port = tcpport;
            match TcpStream::connect(format!("127.0.0.1:{port}")) {
                Ok(mut stream) => {
                    let path = stream.read_msg::<String>().unwrap();
                    if path != pathbuf.as_path().display().to_string() {
                        stream.write_msg(&"QUIT".to_string()).unwrap();
                        continue;
                    }
                    stream.write_msg(&"GO".to_string()).unwrap();
                    let diver_events_tx = diver_events_tx.clone();
                    std::thread::spawn(move || {
                        loop {
                            let tpdata = stream.read_msg::<TracePointData>().unwrap();

                            diver_events_tx
                                .send(DiverEvent::SourceChanged(tpdata))
                                .unwrap();
                        }
                    });
                    break;
                }
                Err(error) => {
                    if iter > 0 {
                        eprintln!("Failed to connect to server, {}", error);
                    }
                }
            }
        }
        if iter == 0 {
            std::thread::sleep(Duration::from_secs(2));
            Command::new(std::env::current_exe()?)
                .args(&[
                    "-s".to_string(),
                    pathbuf.as_path().display().to_string(),
                    "--daemon".to_string(),
                ])
                .spawn()
                .unwrap();
        }
        iter += 1;
        if iter > 100 {
            bail!("Failed to start background daemon");
        }
    }

    let mut arg_iter = args.values.into_iter();
    let cmd = arg_iter.next().expect("need at least one argument");
    let rest: Vec<_> = arg_iter.collect();
    let mut child = Command::new(&cmd)
        .args(&rest)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("LOG_JSON", "1")
        .spawn()
        .with_context(|| {
            format!(
                "failed to spawn child process: '{}' with args: {}",
                &cmd,
                rest.join(" ")
            )
        })?;

    let diver_events_tx2 = diver_events_tx.clone();
    if let Some(stdout) = child.stdout.take() {
        std::thread::spawn(move || capturer(stdout, diver_events_tx2, true));
    }
    if let Some(stderr) = child.stderr.take() {
        std::thread::spawn(move || capturer(stderr, diver_events_tx, false));
    }
    let child = KillOnDrop(child);

    let debug_capturer = args.debug_capturer;
    if debug_capturer {
        std::thread::sleep(std::time::Duration::from_secs(86400));
        return Ok(());
    }

    let state2 = state.clone();
    std::thread::spawn(move || {
        mainloop(diver_events_rx, state2);
    });

    let res = match catch_unwind(||{
        let terminal = ratatui::init();
        run(terminal, state, child, light_mode)
    }) {
        Ok(err) => err,
        Err(err) => {
            if let Some(err) = err.downcast_ref::<String>() {
                Err(anyhow!("Panic: {err}"))
            } else if let Some(err) = err.downcast_ref::<&'static str>() {
                Err(anyhow!("Panic: {err}"))
            } else {
                Err(anyhow!("panic!"))
            }
        }
    };
    ratatui::restore();

    res
}



trait BlockExt: Sized {
    fn highlight<T: Eq>(self, our_index: T, active_highlight: T, color_style: &ColorStyle) -> Self;
}

impl<'a> BlockExt for Block<'a> {
    fn highlight<T: Eq>(self, our_index: T, active_highlight: T, style: &ColorStyle) -> Block<'a> {
        if our_index == active_highlight {
            self.border_style(style.default_selected_style)
        } else {
            self.border_style(style.default_style)
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


fn combine(color: &mut Rgb, other_color: Rgb) {
    color.red += other_color.red;
    color.green += other_color.green;
    color.blue += other_color.blue;
}

struct ColorScheme {
    light: bool,
    bg_color: Color,
    selected_bg_color: Color,
    base_text_color: Color,
}
struct ColorStyle {
    scheme: ColorScheme,
    default_style: Style,
    default_selected_style: Style,
}
impl ColorStyle {
    pub fn new(scheme: ColorScheme) -> Self {
        Self {
            default_style: Style::from((
                scheme.base_text_color,
                scheme.bg_color,
                )),
            default_selected_style: Style::from(
                (
                    scheme.base_text_color,
                    scheme.selected_bg_color,
                    )
            ),
            scheme,
        }
    }
    pub fn color_by_index(&self, index: u32) -> Rgb {
        let colour = (index.wrapping_mul(57)) as f32;
        let hsl = Hsl::new(RgbHue::from_degrees(colour), 1.0, 0.4);
        use ratatui::palette::convert::FromColorUnclamped;
        let rgb = Rgb::from_color_unclamped(hsl);
        self.scheme.normalize_text_color(rgb)
    }
}
impl ColorScheme {
    pub fn new(light: bool) -> Self {
        if light {
            Self {
                light,
                bg_color: Color::Rgb(255,255,255),
                selected_bg_color: Color::Rgb(215,215,215),
                base_text_color: Color::Rgb(0,0,0),
            }
        } else {
            Self {
                light,
                bg_color: Color::Rgb(0,0,0),
                selected_bg_color: Color::Rgb(70,70,70),
                base_text_color: Color::Rgb(192,192,192),
            }
        }
    }
    fn normalize_text_color(&self, color: Rgb) -> Rgb {
        let intensity = color.red + color.green + color.blue;
        if self.light {
            if intensity > 1.0 {
                let f = 1.0 / intensity;
                Rgb::new(f*color.red, f*color.green, f*color.blue)
            } else {
                color
            }
        } else {
            // DARK
            if intensity > 3.0 {
                let f = 3.0 / intensity;
                Rgb::new(f*color.red, f*color.green, f*color.blue)
            } else if intensity < 1e-3 {
                Rgb::new(0.75,0.75,0.75)
            } else if intensity < 1.0 {
                let f = 1.0 / intensity;
                Rgb::new(f*color.red, f*color.green, f*color.blue)
            }
            else
            {
                color
            }

        }
    }
}

fn run(
    mut terminal: DefaultTerminal,
    state: Arc<Mutex<State>>,
    mut child: KillOnDrop,
    mut light_mode: bool,
) -> Result<()> {
    let rows: [Row; 0] = [];

    enum GuiState {
        Normal,
        AddNewFilter(TextArea<'static>),
    }

    let mut color_scheme = ColorScheme::new(light_mode);
    let mut color_style = ColorStyle::new(color_scheme);
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



    let mut row_space = 0;
    loop {


        {
            let mut state = state.lock().unwrap();
            let state = &mut *state;
            let filter_table = Table::new(
                rows.clone(),
                [
                    Constraint::Length(7),
                    Constraint::Length(8),
                    Constraint::Percentage(100),
                ],
            )
            .block(
                Block::bordered()
                    .title("Filters")
                    .title_bottom("A - Add filter, O - Focus Selected")
                    .highlight(Window::Filter, state.active_window, &color_style)

                ,
            )
            .header(Row::new(vec!["Active", "Matches", "Fingerprint"]))
            .highlight_symbol(">")
                .style(color_style.default_style);

            let newsize = terminal.size()?;
            if (last_generation != state.generation || lastsize != newsize) &&
                newsize.width > 20 && newsize.height > 8

                {
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

                    row_space = (output_area.height as usize).saturating_sub(3);
                    let matching_line_count =
                        if state.do_filter {
                            state.matching_lines.len()
                        } else {
                            state.all_lines.len()
                        };

                    if output_table_state.selected().unwrap_or(0) >= matching_line_count {
                        output_table_state.select(matching_line_count.checked_sub(1));
                    }
                    let selected_opt = output_table_state.selected();
                    if let Some(selected) = selected_opt {
                        let offset = output_table_state.offset().min(matching_line_count.saturating_sub(1));
                        if selected < offset {
                            *output_table_state.offset_mut() = selected;
                        }
                        if selected >= offset + row_space {
                            *output_table_state.offset_mut() = selected.saturating_sub(row_space.saturating_sub(1));
                        }
                    }
                    let offset = output_table_state.offset().min(matching_line_count.saturating_sub(1));

                    let stats = [
                        ("Total", state.total.to_string()),
                        ("Captured", state.all_lines.len().to_string()), ("Shown", matching_line_count.to_string()),
                        ("Status",
                         {
                             match child.0.try_wait() {
                                 Ok(Some(exit_status)) => {
                                     match exit_status.code() {
                                         None => {
                                             "?".to_string()
                                         }
                                         Some(code) => {
                                             code.to_string()
                                         }
                                     }
                                 }
                                 Ok(None) => {
                                     "running".to_string()
                                 }
                                 Err(err) => {
                                     err.to_string()
                                 }
                             }
                         }
                        ),
                        ("Filter",
                        if state.do_filter {"active".to_string()} else {"no".to_string()}),
                        ("Light",
                            light_mode.to_string()
                        )
                    ];
                    render_cnt += 1;
                    frame.render_widget(Block::bordered().title("Stats")
                                            .style(color_style.default_style), stats_area)
                    ;
                    let mut cur_stat_area = Rect::new(stats_area.x+1, stats_area.y+1, stats_area.width.saturating_sub(2), 1);
                    for (key,val ) in stats {
                        let mut key_area = cur_stat_area;
                        key_area.width = 10;
                        let mut value_area = cur_stat_area;
                        value_area.x = 9;
                        value_area.width = value_area.width.saturating_sub(9);
                        frame.render_widget(Paragraph::new(format!("{}:", key)).style(color_style.default_style), key_area);
                        frame.render_widget(Paragraph::new(val).style(color_style.default_style), value_area);
                        cur_stat_area.y += 1;
                    }

                    let mut rows = vec![];
                    let mut fixed_output_table_state = output_table_state.clone();
                    *fixed_output_table_state.offset_mut() = 0;
                    if let Some(selected) = fixed_output_table_state.selected_mut() {
                        *selected -= offset;
                    }
                    let selected = fixed_output_table_state.selected();

                    if state.do_filter {
                        for (i,mline) in state.matching_lines.iter().skip(offset).take(row_space).enumerate() {
                            let line = &*mline;
                            let matches = State::get_matches(&mut state.fingerprint_trie, &*line);
                            let bgcolor = if Some(i) == selected {
                                color_style.scheme.selected_bg_color
                            }  else {
                                color_style.scheme.bg_color
                            };
                            let mut message_line = Line::default();

                            let byte_offset = mline.message.chars().take(state.sidescroll).map(|x|x.len_utf8()).sum::<usize>();

                            let mut char_colors = vec![Rgb::<Srgb>::new(0.0,0.0,0.0);line.message.len()];

                            if line.message.len() > 0 {
                                for tp_match in matches.iter()
                                {
                                    let col = color_style.color_by_index(tp_match.tp);
                                    for (start,end) in tp_match.hits.range.iter() {
                                        let end = (*end).min(char_colors.len() as u32); //TODO: Don't clamp here, it would be a bug if needed
                                        for c in &mut char_colors[*start as usize .. end as usize] {
                                            combine(c, col);
                                        }
                                    }
                                }
                            }

                            let  mut cur_index = 0;
                            for (chunk_key, contents) in char_colors.iter().chunk_by(|x|*x).into_iter() {

                                let l = contents.into_iter().count();

                                let mut start = cur_index;
                                let end = cur_index + l;
                                cur_index += l;
                                if end <= byte_offset {
                                    continue;
                                }
                                if start < byte_offset {
                                    start = byte_offset;
                                }
                                message_line.push_span(Span::styled(
                                    &line.message[start..end], {
                                        defstyle().fg(Color::from(color_style.scheme.normalize_text_color(*chunk_key)))
                                            .bg(bgcolor)
                                    }
                                ));
                            }

                            add_line(&state, &mut rows, &line, bgcolor, message_line);
                        }
                    } else {
                        for (i,line) in state.all_lines.iter().skip(offset).take(row_space).enumerate() {
                            let bgcolor = if Some(i) == selected {
                                color_style.scheme.selected_bg_color
                            }  else {
                                color_style.scheme.bg_color
                            };
                            add_line(&state, &mut rows, &line, bgcolor, Line::raw(&
                                line.message
                            ));
                        }
                    }


                    let mut output_cols = Vec::with_capacity(10);
                    if !state.plain {
                        output_cols.push(Constraint::Length(27));
                        output_cols.push(Constraint::Length(6));
                    }
                    if state.show_target {
                        output_cols.push(Constraint::Fill(10));
                    }
                    if state.fields {
                        output_cols.push(Constraint::Fill(30));
                    }
                    output_cols.push(Constraint::Fill(30));

                    let mut col_headings = Vec::new();
                    if !state.plain {
                        col_headings.push("Time");
                        col_headings.push("Level");
                    }
                    if state.show_target {
                        col_headings.push("Target");
                    }
                    if state.fields {
                        col_headings.push("Fields");
                    }
                    col_headings.push("Message");

                    let output_table = Table::new(rows.clone(),
                                                  output_cols
                    )
                        .block(Block::bordered().title("Output").highlight(Window::Output, state.active_window, &color_style)
                            .title_bottom(format!("{} / {}, T - show target, F - toggle filter, P - plain, I - fields",
                                                  selected_opt.map(|x|x.to_string()).unwrap_or_default(), matching_line_count
                            ))
                        )
                        .header(Row::new(
                            col_headings

                        ))
                        .highlight_symbol(">")
                        .style(color_style.default_style);

                    frame.render_stateful_widget(output_table.clone().
                        rows(rows.clone()), output_area, &mut fixed_output_table_state);

                    let mut rows = vec![];
                    let selected = filter_table_state.selected().map(|x|x.min(state.tracepoints.len().saturating_sub(1)));
                    for (i, tracepoint) in state.tracepoints.iter().enumerate() {

                        let bgcolor = if Some(i) == selected {
                            color_style.scheme.selected_bg_color
                        }  else {
                            color_style.scheme.bg_color
                        };
                        rows.push(Row::new([
                            Line::raw(if tracepoint.active {"X".to_string()} else {"".to_string()}),
                            Line::raw(tracepoint.matches.to_string()),
                            Line::raw(tracepoint.fingerprint.to_string()).set_style(

                                defstyle().fg(color_style.color_by_index(tracepoint.tp.tracepoint).into()).bg(bgcolor))
                            ,
                        ]).bg(bgcolor));
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
            if let Event::Key(_) = &event {
                state.generation += 1;
            }
            match &event {
                Event::Key(KeyEvent {
                    kind: KeyEventKind::Press,
                    code,
                    modifiers,
                    ..
                }) => match &mut gui_state {
                    GuiState::Normal => match code {
                        KeyCode::Esc | KeyCode::Char('Q') | KeyCode::Char('q') => {
                            break Ok(());
                        }
                        KeyCode::Delete if state.active_window == Window::Filter => {
                            if let Some(index) = filter_table_state.selected() {
                                state.tracepoints.remove(index);
                                state.rebuild_trie();
                                state.save();
                            }
                        }
                        KeyCode::Right | KeyCode::Left => match code {
                            KeyCode::Right => {
                                state.sidescroll = state.sidescroll.saturating_add(10);
                            }
                            KeyCode::Left => {
                                state.sidescroll = state.sidescroll.saturating_sub(10);
                            }
                            _ => {}
                        },
                        KeyCode::PageDown | KeyCode::PageUp => {
                            let change = match code {
                                KeyCode::PageDown => row_space as isize,
                                KeyCode::PageUp => -(row_space as isize),
                                _ => 0,
                            };
                            match state.active_window {
                                Window::Filter => {}
                                Window::Output => {
                                    if let Some(selected) = output_table_state.selected() {
                                        output_table_state
                                            .select(Some(selected.saturating_add_signed(change)));
                                    } else {
                                        output_table_state.select(Some(0));
                                    }
                                    state.selected_output = output_table_state.selected();
                                }
                            }
                        }
                        KeyCode::Home | KeyCode::End => match state.active_window {
                            Window::Filter => {}
                            Window::Output => {
                                match code {
                                    KeyCode::Home => {
                                        output_table_state.select(Some(0));
                                    }
                                    KeyCode::End => {
                                        output_table_state.select(Some(usize::MAX));
                                    }
                                    _ => {}
                                }
                                state.selected_output = output_table_state.selected();
                            }
                        },
                        KeyCode::Char('T') | KeyCode::Char('t') => {
                            state.show_target = !state.show_target;
                            state.save();
                        }
                        KeyCode::Char('P') | KeyCode::Char('p') => {
                            state.plain = !state.plain;
                            state.save();
                        }
                        KeyCode::Pause | KeyCode::Char('s') | KeyCode::Char('S') => {
                            state.pause = !state.pause;
                            state.save();
                        }
                        KeyCode::Char('I') | KeyCode::Char('i') => {
                            state.fields = !state.fields;
                            state.rebuild_matches();
                            state.save();
                        }
                        KeyCode::Char('F') | KeyCode::Char('f') => {
                            state.do_filter = !state.do_filter;
                            state.save();
                        }
                        KeyCode::Char('O') | KeyCode::Char('o') => {
                            if let Some(sel) = state.focus_current_tracepoint(
                                modifiers.contains(KeyModifiers::SHIFT)
                            ) {
                                state.do_filter= true;
                                output_table_state.select(Some(sel));
                            }
                            state.save();
                        }
                        KeyCode::Char('l') | KeyCode::Char('L') => {
                            light_mode = !light_mode;
                            state.light_mode = Some(light_mode);
                            color_scheme = ColorScheme::new(light_mode);
                            color_style = ColorStyle::new(color_scheme);
                            state.save();
                        }
                        KeyCode::Char(' ') if state.active_window == Window::Filter => {
                            if let Some(index) = filter_table_state.selected() {
                                if let Some(tracepoint) = state.tracepoints.get_mut(index) {
                                    tracepoint.active = !tracepoint.active;
                                    state.rebuild_trie();
                                    state.save();
                                }
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
                        KeyCode::Up => match state.active_window {
                            Window::Filter => {
                                filter_table_state.select_previous();
                                state.selected_filter = filter_table_state.selected();
                            }
                            Window::Output => {
                                output_table_state.select_previous();
                                state.selected_output = output_table_state.selected();
                            }
                        },
                        KeyCode::Down => match state.active_window {
                            Window::Filter => {
                                filter_table_state.select_next();
                                state.selected_filter = filter_table_state.selected();
                            }
                            Window::Output => {
                                output_table_state.select_next();
                                state.selected_output = output_table_state.selected();
                            }
                        },
                        _ => {}
                    },
                    GuiState::AddNewFilter(text) => match code {
                        KeyCode::Esc => {
                            gui_state = GuiState::Normal;
                        }
                        KeyCode::Enter => {
                            let fingerprint = text.lines()[0].to_string();
                            state.add_tracepoint(TracePointData {
                                fingerprint: Fingerprint::parse(&fingerprint),
                                tp: TracePoint {
                                    file: Arc::new(Default::default()),
                                    line_number: 0,
                                    tracepoint: u32::MAX,
                                },
                                active: true,
                                matches: 0,
                            });

                            gui_state = GuiState::Normal;
                            state.save();
                        }
                        _ => {
                            text.input(event);
                        }
                    },
                },
                _ => {}
            }
        }
    }
}

fn add_line<'a>(
    state: &State,
    rows: &mut Vec<Row<'a>>,
    line: &'a LogLine,
    bgcolor: Color,
    message_line: Line<'a>,
) {
    let mut lines = Vec::with_capacity(10);
    if !state.plain {
        lines.push(Line::raw(&line.time));
        lines.push(Line::raw(&line.level));
    }
    if state.show_target {
        lines.push(Line::raw(&line.target));
    }
    if state.fields {
        lines.push(Line::raw(&line.fields));
    }
    lines.push(message_line);
    rows.push(Row::new(lines).bg(bgcolor));
}

#[cfg(test)]
mod tests {
    use crate::trie::Trie;

    #[test]
    fn dotest() {
        let mut trie = Trie::new();

        trie.push_exact("Binding to group ", 1);
        trie.push_exact("Joining multicast group  on if ", 2);
    }
}
