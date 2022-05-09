// Copyright 2015 Nicholas Allegra (comex).
// Licensed under the Apache License, Version 2.0 <https://www.apache.org/licenses/LICENSE-2.0> or
// the MIT license <https://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Same idea as (but implementation not directly based on) the Python shlex module.  However, this
//! implementation does not support any of the Python module's customization because it makes
//! parsing slower and is fairly useless.  You only get the default settings of shlex.split, which
//! mimic the POSIX shell:
//! <https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html>
//!
//! This implementation also deviates from the Python version in not treating `\r` specially, which
//! I believe is more compliant.
//!
//! The algorithms in this crate are oblivious to UTF-8 high bytes, so they iterate over the bytes
//! directly as a micro-optimization.
//!
//! Disabling the `std` feature (which is enabled by default) will allow the crate to work in
//! `no_std` environments, where the `alloc` crate, and a global allocator, are available.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;
use alloc::vec::Vec;

use alloc::borrow::Cow;
#[cfg(test)]
use alloc::borrow::ToOwned;
use alloc::string::String;
#[cfg(test)]
use alloc::vec;

pub mod byte {
    use alloc::borrow::Borrow;
    use alloc::borrow::Cow;
    use alloc::vec::Vec;

    /// An iterator that takes an input string and splits it into the words using the same syntax as
    /// the POSIX shell.
    pub struct Shlex<'a, B> {
        in_iter: B,
        /// The number of newlines read so far, plus one.
        pub line_no: usize,
        /// An input string is erroneous if it ends while inside a quotation or right after an
        /// unescaped backslash.  Since Iterator does not have a mechanism to return an error, if that
        /// happens, Shlex just throws out the last token, ends the iteration, and sets 'had_error' to
        /// true; best to check it after you're done iterating.
        pub had_error: bool,
        _phantom: core::marker::PhantomData<&'a ()>,
    }

    impl<'a, II, I, B> From<II> for Shlex<'a, I>
    where
        II: IntoIterator<IntoIter = I>,
        I: Iterator<Item = B> + 'a,
        B: Borrow<u8>,
    {
        fn from(into_iter: II) -> Self {
            Self::new(into_iter.into_iter())
        }
    }

    impl<'a, I, B> Shlex<'a, I>
    where
        I: Iterator<Item = B> + 'a,
        B: Borrow<u8>,
    {
        pub fn new<II>(into_iter: II) -> Self
        where
            II: IntoIterator<IntoIter = I>,
        {
            Shlex {
                in_iter: into_iter.into_iter(),
                line_no: 1,
                had_error: false,
                _phantom: core::marker::PhantomData::default(),
            }
        }

        pub fn had_error(&self) -> bool {
            self.had_error
        }

        pub fn line_no(&self) -> usize {
            self.line_no
        }

        fn parse_word(&mut self, mut ch: u8) -> Option<Vec<u8>> {
            let mut result: Vec<u8> = Vec::new();
            loop {
                match ch {
                    b'"' => {
                        if let Err(()) = self.parse_double(&mut result) {
                            self.had_error = true;
                            return None;
                        }
                    }
                    b'\'' => {
                        if let Err(()) = self.parse_single(&mut result) {
                            self.had_error = true;
                            return None;
                        }
                    }
                    b'\\' => {
                        if let Some(ch2) = self.next_byte() {
                            if ch2 != b'\n' {
                                result.push(ch2);
                            }
                        } else {
                            self.had_error = true;
                            return None;
                        }
                    }
                    b' ' | b'\t' | b'\n' => {
                        break;
                    }
                    _ => {
                        result.push(ch);
                    }
                }
                if let Some(ch2) = self.next_byte() {
                    ch = ch2;
                } else {
                    break;
                }
            }
            Some(result)
        }

        fn parse_double(&mut self, result: &mut Vec<u8>) -> Result<(), ()> {
            loop {
                if let Some(ch2) = self.next_byte() {
                    match ch2 {
                        b'\\' => {
                            if let Some(ch3) = self.next_byte() {
                                match ch3 {
                                    // \$ => $
                                    b'$' | b'`' | b'"' | b'\\' => {
                                        result.push(ch3);
                                    }
                                    // \<newline> => nothing
                                    b'\n' => {}
                                    // \x => =x
                                    _ => {
                                        result.push(b'\\');
                                        result.push(ch3);
                                    }
                                }
                            } else {
                                return Err(());
                            }
                        }
                        b'"' => {
                            return Ok(());
                        }
                        _ => {
                            result.push(ch2);
                        }
                    }
                } else {
                    return Err(());
                }
            }
        }

        fn parse_single(&mut self, result: &mut Vec<u8>) -> Result<(), ()> {
            loop {
                if let Some(ch2) = self.next_byte() {
                    match ch2 {
                        b'\'' => {
                            return Ok(());
                        }
                        _ => {
                            result.push(ch2);
                        }
                    }
                } else {
                    return Err(());
                }
            }
        }

        pub(crate) fn next_byte(&mut self) -> Option<u8> {
            let res = self.in_iter.next().map(|b| *b.borrow());
            if res == Some('\n' as u8) {
                self.line_no += 1;
            }
            res
        }

        pub fn split(&mut self) -> Option<Vec<Vec<u8>>> {
            let res = self.collect();
            if self.had_error {
                None
            } else {
                Some(res)
            }
        }
    }

    impl<'a, I, B> Shlex<'a, I>
    where
        I: Iterator<Item = B> + ExactSizeIterator + AsRef<[u8]> + 'a,
        B: Borrow<u8>,
    {
        pub fn quote<'b, 'c>(&'b self) -> Cow<'c, [u8]>
        where
            'b: 'c,
            'a: 'c,
        {
            if self.in_iter.len() == 0 {
                b"\"\""[..].into()
            } else if self.in_iter.as_ref().iter().any(|&c| match c as char {
                '|' | '&' | ';' | '<' | '>' | '(' | ')' | '$' | '`' | '\\' | '"' | '\'' | ' '
                | '\t' | '\r' | '\n' | '*' | '?' | '[' | '#' | '~' | '=' | '%' => true,
                _ => false,
            }) {
                let mut out: Vec<u8> = Vec::new();
                out.push('"' as u8);
                for &c in self.in_iter.as_ref().iter() {
                    match c as char {
                        '$' | '`' | '"' | '\\' => out.push('\\' as u8),
                        _ => (),
                    }
                    out.push(c);
                }
                out.push('"' as u8);
                out.into()
            } else {
                Cow::from(self.in_iter.as_ref())
            }
        }
    }

    impl<'a, I, B> Iterator for Shlex<'a, I>
    where
        I: Iterator<Item = B> + 'a,
        B: Borrow<u8>,
    {
        type Item = Vec<u8>;
        fn next(&mut self) -> Option<Vec<u8>> {
            if let Some(mut ch) = self.next_byte() {
                // skip initial whitespace
                loop {
                    match ch {
                        b' ' | b'\t' | b'\n' => {}
                        b'#' => {
                            while let Some(ch2) = self.next_byte() {
                                if ch2 == b'\n' {
                                    break;
                                }
                            }
                        }
                        _ => {
                            break;
                        }
                    }
                    if let Some(ch2) = self.next_byte() {
                        ch = ch2;
                    } else {
                        return None;
                    }
                }
                self.parse_word(ch)
            } else {
                // no initial character
                None
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_split() {
            for &(input, output) in crate::SPLIT_TEST_ITEMS {
                assert_eq!(
                    Shlex::from(input.as_bytes()).split(),
                    output.map(|o| o.iter().map(|&x| x.as_bytes().to_vec()).collect())
                );
            }
        }

        #[test]
        fn test_lineno() {
            let mut sh = Shlex::new(b"\nfoo\nbar");
            while let Some(word) = sh.next() {
                if word == b"bar" {
                    assert_eq!(sh.line_no, 3);
                }
            }
        }

        #[test]
        fn test_quote() {
            assert_eq!(Shlex::from("foobar".as_bytes()).quote(), &b"foobar"[..]);
            assert_eq!(
                Shlex::from("foo bar".as_bytes()).quote(),
                &b"\"foo bar\""[..]
            );
            assert_eq!(Shlex::from("\"".as_bytes()).quote(), &b"\"\\\"\""[..]);
            assert_eq!(Shlex::from("".as_bytes()).quote(), &b"\"\""[..]);
        }
    }
}

pub mod str {
    use super::byte::Shlex as ByteShlex;

    pub struct Shlex<'a> {
        inner: ByteShlex<'a, core::str::Bytes<'a>>,
    }

    impl<'a> Shlex<'a> {
        pub fn new(in_str: &'a str) -> Self {
            Self {
                inner: ByteShlex::from(in_str.bytes()),
            }
        }

        pub fn had_error(&self) -> bool {
            self.inner.had_error()
        }

        pub fn line_no(&self) -> usize {
            self.inner.line_no()
        }

        pub fn split(&mut self) -> Option<Vec<String>> {
            self.inner.split().map(|split| {
                split
                    .into_iter()
                    .map(|bytes| unsafe { String::from_utf8_unchecked(bytes) })
                    .collect()
            })
        }
    }

    impl<'a> Iterator for Shlex<'a> {
        type Item = String;
        fn next(&mut self) -> Option<String> {
            self.inner
                .next()
                .map(|bytes| unsafe { String::from_utf8_unchecked(bytes) })
        }
    }
}

pub use str::Shlex;

/// Convenience function that consumes the whole string at once.  Returns None if the input was
/// erroneous.
pub fn split(in_str: &str) -> Option<Vec<String>> {
    let mut shl = Shlex::new(in_str);
    let res = shl.by_ref().collect();
    if shl.had_error() {
        None
    } else {
        Some(res)
    }
}

/// Given a single word, return a string suitable to encode it as a shell argument.
pub fn quote(in_str: &str) -> Cow<str> {
    if in_str.len() == 0 {
        "\"\"".into()
    } else if in_str.bytes().any(|c| match c as char {
        '|' | '&' | ';' | '<' | '>' | '(' | ')' | '$' | '`' | '\\' | '"' | '\'' | ' ' | '\t'
        | '\r' | '\n' | '*' | '?' | '[' | '#' | '~' | '=' | '%' => true,
        _ => false,
    }) {
        let mut out: Vec<u8> = Vec::new();
        out.push('"' as u8);
        for c in in_str.bytes() {
            match c as char {
                '$' | '`' | '"' | '\\' => out.push('\\' as u8),
                _ => (),
            }
            out.push(c);
        }
        out.push('"' as u8);
        unsafe { String::from_utf8_unchecked(out) }.into()
    } else {
        in_str.into()
    }
}

/// Convenience function that consumes an iterable of words and turns it into a single string,
/// quoting words when necessary. Consecutive words will be separated by a single space.
pub fn join<'a, I: IntoIterator<Item = &'a str>>(words: I) -> String {
    words.into_iter().map(quote).collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
static SPLIT_TEST_ITEMS: &'static [(&'static str, Option<&'static [&'static str]>)] = &[
    ("foo$baz", Some(&["foo$baz"])),
    ("foo baz", Some(&["foo", "baz"])),
    ("foo\"bar\"baz", Some(&["foobarbaz"])),
    ("foo \"bar\"baz", Some(&["foo", "barbaz"])),
    ("   foo \nbar", Some(&["foo", "bar"])),
    ("foo\\\nbar", Some(&["foobar"])),
    ("\"foo\\\nbar\"", Some(&["foobar"])),
    ("'baz\\$b'", Some(&["baz\\$b"])),
    ("'baz\\\''", None),
    ("\\", None),
    ("\"\\", None),
    ("'\\", None),
    ("\"", None),
    ("'", None),
    ("foo #bar\nbaz", Some(&["foo", "baz"])),
    ("foo #bar", Some(&["foo"])),
    ("foo#bar", Some(&["foo#bar"])),
    ("foo\"#bar", None),
    ("'\\n'", Some(&["\\n"])),
    ("'\\\\n'", Some(&["\\\\n"])),
];

#[test]
fn test_split() {
    for &(input, output) in SPLIT_TEST_ITEMS {
        assert_eq!(
            split(input),
            output.map(|o| o.iter().map(|&x| x.to_owned()).collect())
        );
    }
}

#[test]
fn test_lineno() {
    let mut sh = Shlex::new("\nfoo\nbar");
    while let Some(word) = sh.next() {
        if word == "bar" {
            assert_eq!(sh.line_no(), 3);
        }
    }
}

#[test]
fn test_quote() {
    assert_eq!(quote("foobar"), "foobar");
    assert_eq!(quote("foo bar"), "\"foo bar\"");
    assert_eq!(quote("\""), "\"\\\"\"");
    assert_eq!(quote(""), "\"\"");
}

#[test]
fn test_join() {
    assert_eq!(join(vec![]), "");
    assert_eq!(join(vec![""]), "\"\"");
    assert_eq!(join(vec!["a", "b"]), "a b");
    assert_eq!(join(vec!["foo bar", "baz"]), "\"foo bar\" baz");
}
