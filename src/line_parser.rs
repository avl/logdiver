//! This module attempted to parse regular "pretty" log output.
//! This turned out to be hard to do and is a work-in-progress.
use memchr::memchr;

fn could_be_filename(path: &str) -> bool {
    if !path.ends_with(':') {
        return false;
    }
    let Some(prev_colon) = path[..path.len() - 1].rfind(':') else {
        return false;
    };
    let line_no = &path[prev_colon + 1..path.len() - 1];
    if line_no.is_empty() {
        return false;
    }
    line_no.chars().all(|c| c.is_ascii_digit())
}

#[derive(Clone)]
struct Tokens<'a> {
    s: &'a str,
}
impl<'a> Tokens<'a> {
    fn new(line: &'a str) -> Tokens<'a> {
        Self { s: line }
    }
    fn read_char(&mut self) -> Option<char> {
        if self.s.is_empty() {
            return None;
        }
        let c = self.s.chars().next().unwrap();
        self.s = &self.s[c.len_utf8()..];
        Some(c)
    }
    fn read_past_string_body(&mut self) {
        let mut escaped = false;
        while let Some(c) = self.read_char() {
            if escaped {
                escaped = false;
                continue;
            }
            if c == '\\' {
                escaped = true;
            } else if c == '"' {
                break;
            }
        }
    }
    fn read_past_meta(&mut self) {
        let mut bracket_level = 0;
        let mut previous_was_colon = false;
        while let Some(c) = self.read_char() {
            if c == '"' {
                self.read_past_string_body();
            } else if c == ' ' && bracket_level == 0 && previous_was_colon {
                break;
            } else if c == '{' {
                bracket_level += 1;
            } else if c == '}' {
                bracket_level -= 1;
            }
            previous_was_colon = c == ':';
        }
    }
    fn read_meta(&mut self) -> &'a str {
        let mut cpy = Tokens { s: self.s };
        cpy.read_past_meta();
        let remain_before = self.s.len();
        let remain_after = cpy.s.len();
        let meta_len = remain_before - remain_after;
        let ret = &self.s[..meta_len];
        self.s = &self.s[meta_len..];
        ret
    }
    fn read_to_end(self) -> &'a str {
        self.s
    }
    fn read_symbol(&mut self) -> Option<&str> {
        while self.s.starts_with(' ') {
            self.s = &self.s[1..];
        }
        if let Some(index) = memchr(b' ', self.s.as_bytes()) {
            let ret = &self.s[..index];
            self.s = &self.s[index + 1..];
            return Some(ret);
        } else {
            if self.s.is_empty() {
                return None;
            }
            let ret = self.s;
            self.s = "";
            return Some(ret);
        }
    }
}

#[derive(Debug)]
pub struct Line {
    pub time: String,
    pub level: String,
    pub thread: String,
    pub meta: String,
    pub namespace: String,
    pub path: String,
    pub message: String,
}
pub fn parse_log_line(line: &str) -> Option<Line> {
    let mut tokens = Tokens::new(line);
    let time = tokens.read_symbol()?.to_string();
    let level = tokens.read_symbol()?.to_string();
    let thread = tokens.read_symbol()?.to_string();

    let maybe_meta = tokens.read_meta().trim().to_string();
    let maybe_namespace = tokens.read_symbol()?.to_string();

    let meta;
    let mut namespace;
    let filename;

    if could_be_filename(&maybe_namespace) {
        meta = "".to_string();
        namespace = maybe_meta;
        filename = maybe_namespace;
    } else {
        meta = maybe_meta;
        namespace = maybe_namespace;

        let filename_candidate = tokens.clone().read_symbol()?.to_string();
        if !could_be_filename(&filename_candidate) {
            if namespace.ends_with(':') {
                filename = "".to_string();
            } else {
                return None;
            }
        } else {
            filename = tokens.read_symbol()?.to_string();
        }
    }
    if namespace.ends_with(':') {
        namespace.pop();
    }
    let message = tokens.read_to_end().to_string();
    Some(Line {
        time,
        level,
        thread,
        meta,
        namespace,
        path: filename,
        message,
    })
}

#[cfg(test)]
mod tests {
    use crate::line_parser::{could_be_filename, parse_log_line};
    use insta::{assert_debug_snapshot};

    #[test]
    fn parse_logline() {
        let line = parse_log_line("2025-11-15T21:03:16.997950Z TRACE tokio-runtime-worker request{method=GET uri=/brb/whoami version=HTTP/1.1}: tower_http::trace::on_response: /Users/anders.musikka/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/tower-http-0.6.6/src/trace/on_response.rs:114: finished processing request latency=1062 μs status=412")
        .unwrap();
        assert_debug_snapshot!(line);
    }
    #[test]
    fn check_is_file() {
        assert!(could_be_filename("abc:123:"));
        assert!(could_be_filename("abc:12:"));
        assert!(could_be_filename("abc:1:"));
        assert!(!could_be_filename("abc"));
        assert!(!could_be_filename("abc::"));
        assert!(!could_be_filename("abc:x:"));
        assert!(!could_be_filename("abc:43"));
        assert!(!could_be_filename("abc43:"));
    }
}
