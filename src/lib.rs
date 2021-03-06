//! ## `numeric-sort`
//! 
//! A zero-allocation, human-readable sorting library.
//! 
//! The primary functions of interest are [`sort`] and [`cmp`].
//! 
//! ## `no-std`
//! 
//! `numeric-sort` is compatible with `no-std` projects by passing `default-features = false` to the dependency.
//! 
//! ```toml
//! [dependencies]
//! numeric-sort = { version = "...", default-features = false }
//! ```

#![forbid(unsafe_code)]
#![no_std]

extern crate no_std_compat as std;

use std::prelude::v1::*;
use std::cmp::{PartialOrd, Ord, PartialEq, Eq, Ordering};
use std::iter::FusedIterator;

/// A reference to a substring of one or more non- (decimal) digits.
/// 
/// [`Ord`] and [`Eq`] are implemented for this type, which is equivalent to comparing the raw [`str`] values.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct Text<'a>(&'a str);
impl<'a> Text<'a> {
    /// Greedily reads a (non-empty) [`Text`] segment from the beginning of the string.
    /// Returns [`None`] if the string is empty or starts with a (decimal) digit.
    pub fn read(src: &'a str) -> Option<Self> {
        match src.char_indices().find(|ch| ch.1.is_digit(10)).map(|x| x.0).unwrap_or(src.len()) {
            0 => None,
            stop => Some(Self(&src[..stop])),
        }
    }
    /// Returns the (non-empty) substring that was read via [`Text::read`].
    pub fn as_str(&self) -> &'a str { self.0 }
}

#[test]
fn test_text() {
    assert_eq!(Text::read("hello world").map(|v| v.0), Some("hello world"));
    assert_eq!(Text::read("hello wor4ld").map(|v| v.0), Some("hello wor"));
    assert_eq!(Text::read("h2ell wor4ld").map(|v| v.0), Some("h"));
    assert_eq!(Text::read("34hello wor4ld").map(|v| v.0), None);

    fn get(v: &str) -> &str { Text::read(v).unwrap().as_str() }
    assert_eq!(get("hello world"), "hello world");
    assert_eq!(get("hello wor4ld"), "hello wor");
    assert_eq!(get("h2ell wor4ld"), "h");
}

/// A reference to a substring of one or more (decimal) digits.
/// 
/// [`Ord`] and [`Eq`] are implemented for this type, which behave as if using arbitrary-precision integers, but performs no allocations.
/// Note that this means that leading zeros on a number will be ignored for the purpose of comparison.
#[derive(Debug, Clone, Copy)]
pub struct Number<'a>(&'a str, &'a str);
impl<'a> Number<'a> {
    /// Greedily reads a (non-empty) [`Number`] segment from the beginning of the string.
    /// Returns [`None`] if the string does not start with a (decimal) digit.
    pub fn read(src: &'a str) -> Option<Self> {
        match src.chars().position(|ch| !ch.is_digit(10)).unwrap_or(src.len()) {
            0 => None,
            stop => {
                let zeros = src.chars().position(|ch| ch != '0').unwrap_or(src.len());
                Some(Self(&src[..stop], &src[zeros..stop])) // ascii digits are 1 byte in utf8, so this is safe (otherwise we'd need char_indices())
            }
        }
    }
    /// Returns the (non-empty) substring that was read via [`Number::read`].
    pub fn as_str(&self) -> &'a str { self.0 }
}
impl Ord for Number<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.1.len().cmp(&other.1.len()) {
            Ordering::Equal => self.1.cmp(&other.1),
            x => x,
        }
    }
}
impl PartialOrd for Number<'_> { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
impl PartialEq for Number<'_> { fn eq(&self, other: &Self) -> bool { self.1 == other.1 } }
impl Eq for Number<'_> {}

#[test]
fn test_number() {
    assert_eq!(Number::read("53426").map(|v| (v.0, v.1)), Some(("53426", "53426")));
    assert_eq!(Number::read("053426").map(|v| (v.0, v.1)), Some(("053426", "53426")));
    assert_eq!(Number::read("00053426").map(|v| (v.0, v.1)), Some(("00053426", "53426")));
    assert_eq!(Number::read("00053d426").map(|v| (v.0, v.1)), Some(("00053", "53")));
    assert_eq!(Number::read("000g53d426").map(|v| (v.0, v.1)), Some(("000", "")));
    assert_eq!(Number::read("00g53d426").map(|v| (v.0, v.1)), Some(("00", "")));
    assert_eq!(Number::read("g53d426").map(|v| (v.0, v.1)), None);

    assert_eq!(Number::read("2345").unwrap().cmp(&Number::read("2345").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("2345").unwrap().cmp(&Number::read("0002345").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("234").unwrap().cmp(&Number::read("2345").unwrap()), Ordering::Less);
    assert_eq!(Number::read("000000234").unwrap().cmp(&Number::read("2345").unwrap()), Ordering::Less);
    assert_eq!(Number::read("000000234").unwrap().cmp(&Number::read("236521548").unwrap()), Ordering::Less);
    assert_eq!(Number::read("000000234").unwrap().cmp(&Number::read("000000236521548").unwrap()), Ordering::Less);
    assert_eq!(Number::read("01000000").unwrap().cmp(&Number::read("000000236521548").unwrap()), Ordering::Less);
    assert_eq!(Number::read("123").unwrap().cmp(&Number::read("101").unwrap()), Ordering::Greater);

    assert_eq!(Number::read("2345").unwrap(), Number::read("2345").unwrap());
    assert_eq!(Number::read("002345").unwrap(), Number::read("2345").unwrap());

    fn get(v: &str) -> &str { Number::read(v).unwrap().as_str() }
    assert_eq!(get("2345"), "2345");
    assert_eq!(get("002345"), "002345");
}

/// A reference to a homogenous segment of text in a string.
/// 
/// [`Ord`] and [`Eq`] are implemented for this type, which delegate to their respective types for same variant comparison,
/// and otherwise considers every [`Segment::Number`] to come before every [`Segment::Text`].
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum Segment<'a> {
    Number(Number<'a>),
    Text(Text<'a>),
}
impl<'a> Segment<'a> {
    /// Greedily reads a (non-empty) [`Text`] or [`Number`] segment from the beginning of the string.
    /// Returns [`None`] if the string is empty.
    pub fn read(src: &'a str) -> Option<Self> {
        if let Some(x) = Number::read(src) { return Some(Segment::Number(x)) }
        if let Some(x) = Text::read(src) { return Some(Segment::Text(x)) }
        debug_assert_eq!(src, "");
        None
    }
    /// Returns the (non-empty) substring that was read via [`Segment::read`].
    pub fn as_str(&self) -> &'a str {
        match self {
            Segment::Text(x) => x.as_str(),
            Segment::Number(x) => x.as_str(),
        }
    }
    /// Retrieves the value of the [`Segment::Number`] variant, or [`None`] if that is not the current variant.
    pub fn as_number(&self) -> Option<Number<'a>> {
        if let Segment::Number(x) = self { Some(*x) } else { None }
    }
    /// Retrieves the value of the [`Segment::Text`] variant, or [`None`] if that is not the current variant.
    pub fn as_text(&self) -> Option<Text<'a>> {
        if let Segment::Text(x) = self { Some(*x) } else { None }
    }
}

#[test]
fn test_segment() {
    assert_eq!(Segment::read("00453hello").unwrap().as_number().unwrap().as_str(), "00453");
    assert_eq!(Segment::read("453hello").unwrap().as_number().unwrap().as_str(), "453");
    assert_eq!(Segment::read("000hello").unwrap().as_number().unwrap().as_str(), "000");
    assert_eq!(Segment::read("hello 453").unwrap().as_text().unwrap().as_str(), "hello ");
    assert_eq!(Segment::read(" ").unwrap().as_text().unwrap().as_str(), " ");
    assert!(Segment::read("").is_none());

    fn get(v: &str) -> &str { Segment::read(v).unwrap().as_str() }
    assert_eq!(get("hello 69"), "hello ");
    assert_eq!(get("453 hello 69"), "453");
    assert_eq!(get("00453 hello 69"), "00453");
    assert_eq!(get("000"), "000");
    assert_eq!(get("abc"), "abc");

    assert_eq!(Segment::read("00000").unwrap().cmp(&Segment::read("aaaaa").unwrap()), Ordering::Less);
    assert_eq!(Segment::read("aaaaa").unwrap().cmp(&Segment::read("00000").unwrap()), Ordering::Greater);
    assert_eq!(Segment::read("0000").unwrap().cmp(&Segment::read("aaaaa").unwrap()), Ordering::Less);
    assert_eq!(Segment::read("aaaa").unwrap().cmp(&Segment::read("00000").unwrap()), Ordering::Greater);
    assert_eq!(Segment::read("00000").unwrap().cmp(&Segment::read("aaaa").unwrap()), Ordering::Less);
    assert_eq!(Segment::read("aaaaa").unwrap().cmp(&Segment::read("0000").unwrap()), Ordering::Greater);
}

/// An iterator over the [`Segment`] values within a string.
/// 
/// This is a potentially-empty sequence of alternating [`Segment::Number`] and [`Segment::Text`] values (not necessarily in that order).
#[derive(Clone, Copy)]
pub struct SegmentIter<'a>(&'a str);
impl<'a> SegmentIter<'a> {
    /// Constructs a new [`SegmentIter`] that iterates over the segments of the string.
    /// If the string is empty, the resulting iterator is likewise an empty sequence.
    pub fn new(src: &'a str) -> Self {
        Self(src)
    }
    /// Returns the remaining portion of the original string that has not yet been iterated.
    /// Returns an empty string if the iterator has been exhausted.
    pub fn as_str(&self) -> &'a str {
        self.0
    }
}
impl<'a> Iterator for SegmentIter<'a> {
    type Item = Segment<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let res = Segment::read(self.0)?;
        self.0 = &self.0[res.as_str().len()..];
        Some(res)
    }
}
impl FusedIterator for SegmentIter<'_> {}

#[test]
fn test_segment_iter() {
    let mut seq = SegmentIter::new("34543hello this is 00343 2 a test");
    assert_eq!(seq.as_str(), "34543hello this is 00343 2 a test");
    assert_eq!(seq.next().unwrap().as_number().unwrap().as_str(), "34543");
    assert_eq!(seq.as_str(), "hello this is 00343 2 a test");
    assert_eq!(seq.next().unwrap().as_text().unwrap().as_str(), "hello this is ");
    assert_eq!(seq.as_str(), "00343 2 a test");
    assert_eq!(seq.next().unwrap().as_number().unwrap().as_str(), "00343");
    assert_eq!(seq.as_str(), " 2 a test");
    assert_eq!(seq.next().unwrap().as_text().unwrap().as_str(), " ");
    assert_eq!(seq.as_str(), "2 a test");
    assert_eq!(seq.next().unwrap().as_number().unwrap().as_str(), "2");
    assert_eq!(seq.as_str(), " a test");
    assert_eq!(seq.next().unwrap().as_text().unwrap().as_str(), " a test");
    assert_eq!(seq.as_str(), "");
    for _ in 0..16 {
        assert!(seq.next().is_none());
        assert_eq!(seq.as_str(), "");
    }

    fn get(v: &str) -> &str { SegmentIter::new(v).as_str() }
    assert_eq!(get("hello world"), "hello world");
}

/// Performs a lexicographic comparison of the [`Segment`] sequences of two strings.
/// 
/// This has the effect of ordering the strings with respect to [`Number`] and [`Text`] substrings.
/// 
/// ```
/// # use numeric_sort::cmp;
/// # use std::cmp::Ordering;
/// assert_eq!(cmp("apple", "cable"), Ordering::Less);
/// assert_eq!(cmp("32454", "hello"), Ordering::Less);
/// assert_eq!(cmp("file-10", "file-3"), Ordering::Greater);
/// assert_eq!(cmp("test-v1.10.25", "test-v1.9.2"), Ordering::Greater);
/// assert_eq!(cmp("agent-007", "agent-7"), Ordering::Equal);
/// ```
pub fn cmp(a: &str, b: &str) -> Ordering {
    SegmentIter::new(a).cmp(SegmentIter::new(b))
}

#[test]
fn test_cmp() {
    assert_eq!(cmp("hello-456", "hello-0999"), Ordering::Less);
    assert_eq!(cmp("hellos-456", "hello-0999"), Ordering::Greater);
    assert_eq!(cmp("hello--456", "hello-0999"), Ordering::Greater);
}

/// Sorts an array via the [`cmp`] ordering.
/// 
/// ```
/// # use numeric_sort::sort;
/// let mut arr = ["file-1", "file-10", "file-2"];
/// sort(&mut arr);
/// assert_eq!(&arr, &["file-1", "file-2", "file-10"]);
/// ```
pub fn sort<T: AsRef<str>>(arr: &mut [T]) {
    arr.sort_by(|a, b| cmp(a.as_ref(), b.as_ref()))
}

#[test]
fn test_sort() {
    macro_rules! sorted { ($in:expr) => {{ let mut v = $in; sort(&mut v); v }} }
    assert_eq!(&sorted!(["file-1", "file-10", "file-2"]), &["file-1", "file-2", "file-10"]);
    assert_eq!(&sorted!(["file-1".to_string(), "file-10".to_string(), "file-2".to_string()]), &["file-1", "file-2", "file-10"]);
}
