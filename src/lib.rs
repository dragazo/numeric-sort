#![doc = include_str!("../README.md")]
#![forbid(unsafe_code)]
#![no_std]

#[cfg(any(test, feature = "alloc"))]
extern crate alloc;

#[cfg(test)]
use alloc::format;

use core::cmp::{PartialOrd, Ord, PartialEq, Eq, Ordering};
use core::iter::FusedIterator;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Sign {
    Negative, Positive,
}

/// A reference to a substring of one or more non- (decimal) digits.
/// 
/// [`Ord`] and [`Eq`] are implemented for this type, which is equivalent to comparing the raw [`str`] values.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct Text<'a> {
    content: &'a str,
}
impl<'a> Text<'a> {
    /// Greedily reads a (non-empty) [`Text`] segment from the beginning of the string.
    /// Returns [`None`] if the string is empty or starts with a (decimal) digit.
    pub fn read(src: &'a str) -> Option<Self> {
        if Number::read(src).is_some() { return None; }

        let mut pos = src.char_indices();
        loop {
            match pos.next() {
                None => return if !src.is_empty() { Some(Self { content: src }) } else { None },
                Some((i, ch)) => {
                    if ch.is_ascii_punctuation() && Number::read(&src[i + 1..]).is_some() {
                        return Some(Self { content: &src[..i + 1] });
                    }
                    if ch.is_digit(10) {
                        return if i != 0 { Some(Self { content: &src[..i] }) } else { None };
                    }
                }
            }
        }
    }
    /// Returns the (non-empty) substring that was read via [`Text::read`].
    pub fn as_str(&self) -> &'a str { self.content }
}

#[test]
fn test_text() {
    assert_eq!(Text::read("hello world-").map(|v| v.content), Some("hello world-"));
    assert_eq!(Text::read("hello world-4").map(|v| v.content), Some("hello world-"));
    assert_eq!(Text::read("hello world--4").map(|v| v.content), Some("hello world-"));
    assert_eq!(Text::read("hello world---4").map(|v| v.content), Some("hello world--"));
    assert_eq!(Text::read("hello world----4").map(|v| v.content), Some("hello world---"));
    assert_eq!(Text::read("hello world").map(|v| v.content), Some("hello world"));
    assert_eq!(Text::read("hello wor4ld").map(|v| v.content), Some("hello wor"));
    assert_eq!(Text::read("안영하세요 wor4ld").map(|v| v.content), Some("안영하세요 wor"));
    assert_eq!(Text::read("h2ell wor4ld").map(|v| v.content), Some("h"));
    assert_eq!(Text::read("34hello wor4ld").map(|v| v.content), None);
    assert_eq!(Text::read("-34hello wor4ld").map(|v| v.content), None);
    assert_eq!(Text::read("--34hello wor4ld").map(|v| v.content), Some("-"));
    assert_eq!(Text::read("+-34hello wor4ld").map(|v| v.content), Some("+"));
    assert_eq!(Text::read("+34hello wor4ld").map(|v| v.content), None);
    assert_eq!(Text::read("-+34hello wor4ld").map(|v| v.content), Some("-"));
    assert_eq!(Text::read("++34hello wor4ld").map(|v| v.content), Some("+"));
    assert_eq!(Text::read("").map(|v| v.content), None);

    for p in "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".chars() {
        assert_eq!(Text::read(&format!("hello world{p}-4")).map(|v| v.content), Some(format!("hello world{p}").as_str()));
    }

    fn get(v: &str) -> &str { Text::read(v).unwrap().as_str() }
    assert_eq!(get("hello world"), "hello world");
    assert_eq!(get("hello wor4ld"), "hello wor");
    assert_eq!(get("h2ell wor4ld"), "h");
    assert_eq!(get(" h2ell wor4ld"), " h");
    assert_eq!(get(" h 2ell wor4ld"), " h ");
}

/// A reference to a substring of one or more (decimal) digits.
/// 
/// [`Ord`] and [`Eq`] are implemented for this type, which behave as if using arbitrary-precision integers, but performs no allocations.
/// Note that this means that leading zeros on a number will be ignored for the purpose of comparison.
#[derive(Debug, Clone, Copy)]
pub struct Number<'a> {
    sign: Option<Sign>,
    leading_zeros: usize,
    content: &'a str,
}
impl<'a> Number<'a> {
    /// Greedily reads a (non-empty) [`Number`] segment from the beginning of the string.
    /// Returns [`None`] if the string does not start with a (decimal) digit.
    pub fn read(src: &'a str) -> Option<Self> {
        let (sign, tail) = match src.chars().next() {
            Some('+') => (Some(Sign::Positive), &src[1..]),
            Some('-') => (Some(Sign::Negative), &src[1..]),
            _ => (None, src),
        };

        match tail.chars().position(|ch| !ch.is_digit(10)).unwrap_or(tail.len()) {
            0 => None,
            stop => {
                let leading_zeros = tail.chars().position(|ch| ch != '0').unwrap_or(tail.len());
                Some(Self { sign, leading_zeros, content: &src[..stop + (src.len() - tail.len())] }) // ascii digits are 1 byte in utf8, so this is safe (otherwise we'd need char_indices())
            }
        }
    }
    /// Returns the (non-empty) substring that was read via [`Number::read`].
    pub fn as_str(&self) -> &'a str { self.content }
}
impl Ord for Number<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        let t = |x: &Self| (x.content.len() - if x.sign.is_some() { 1 } else { 0 } - x.leading_zeros, &x.content[if x.sign.is_some() { 1 } else { 0 } + x.leading_zeros..]);

        match (self.sign.unwrap_or(Sign::Positive), other.sign.unwrap_or(Sign::Positive)) {
            (Sign::Positive, Sign::Positive) => t(self).cmp(&t(other)),
            (Sign::Positive, Sign::Negative) => if t(self).0 == 0 && t(other).0 == 0 { Ordering::Equal } else { Ordering::Greater },
            (Sign::Negative, Sign::Positive) => if t(self).0 == 0 && t(other).0 == 0 { Ordering::Equal } else { Ordering::Less },
            (Sign::Negative, Sign::Negative) => t(other).cmp(&t(self)),
        }
    }
}
impl PartialOrd for Number<'_> { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
impl PartialEq for Number<'_> { fn eq(&self, other: &Self) -> bool { self.cmp(other) == Ordering::Equal } }
impl Eq for Number<'_> {}

#[test]
fn test_number() {
    assert_eq!(Number::read("0").map(|v| (v.content, v.leading_zeros)), Some(("0", 1)));
    assert_eq!(Number::read("+0").map(|v| (v.content, v.leading_zeros)), Some(("+0", 1)));
    assert_eq!(Number::read("-0").map(|v| (v.content, v.leading_zeros)), Some(("-0", 1)));
    assert_eq!(Number::read("00").map(|v| (v.content, v.leading_zeros)), Some(("00", 2)));
    assert_eq!(Number::read("+00").map(|v| (v.content, v.leading_zeros)), Some(("+00", 2)));
    assert_eq!(Number::read("-00").map(|v| (v.content, v.leading_zeros)), Some(("-00", 2)));
    assert_eq!(Number::read("53426").map(|v| (v.content, v.leading_zeros)), Some(("53426", 0)));
    assert_eq!(Number::read("-53426").map(|v| (v.content, v.leading_zeros)), Some(("-53426", 0)));
    assert_eq!(Number::read("-53426g").map(|v| (v.content, v.leading_zeros)), Some(("-53426", 0)));
    assert_eq!(Number::read("-053426").map(|v| (v.content, v.leading_zeros)), Some(("-053426", 1)));
    assert_eq!(Number::read("-053426f").map(|v| (v.content, v.leading_zeros)), Some(("-053426", 1)));
    assert_eq!(Number::read("+53426").map(|v| (v.content, v.leading_zeros)), Some(("+53426", 0)));
    assert_eq!(Number::read("+53426g").map(|v| (v.content, v.leading_zeros)), Some(("+53426", 0)));
    assert_eq!(Number::read("+053426").map(|v| (v.content, v.leading_zeros)), Some(("+053426", 1)));
    assert_eq!(Number::read("+053426f").map(|v| (v.content, v.leading_zeros)), Some(("+053426", 1)));
    assert_eq!(Number::read("053426").map(|v| (v.content, v.leading_zeros)), Some(("053426", 1)));
    assert_eq!(Number::read("00053426").map(|v| (v.content, v.leading_zeros)), Some(("00053426", 3)));
    assert_eq!(Number::read("00053d426").map(|v| (v.content, v.leading_zeros)), Some(("00053", 3)));
    assert_eq!(Number::read("000g53d426").map(|v| (v.content, v.leading_zeros)), Some(("000", 3)));
    assert_eq!(Number::read("00g53d426").map(|v| (v.content, v.leading_zeros)), Some(("00", 2)));
    assert_eq!(Number::read("g53d426").map(|v| (v.content, v.leading_zeros)), None);

    assert_eq!(Number::read("2345").unwrap().cmp(&Number::read("2346").unwrap()), Ordering::Less);
    assert_eq!(Number::read("-2345").unwrap().cmp(&Number::read("-2346").unwrap()), Ordering::Greater);
    assert_eq!(Number::read("-2345").unwrap().cmp(&Number::read("-2345").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("-2345").unwrap().cmp(&Number::read("+2345").unwrap()), Ordering::Less);
    assert_eq!(Number::read("-2345").unwrap().cmp(&Number::read("2345").unwrap()), Ordering::Less);
    assert_eq!(Number::read("+2345").unwrap().cmp(&Number::read("-2345").unwrap()), Ordering::Greater);
    assert_eq!(Number::read("2345").unwrap().cmp(&Number::read("-2345").unwrap()), Ordering::Greater);
    assert_eq!(Number::read("+2345").unwrap().cmp(&Number::read("+2345").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("+2345").unwrap().cmp(&Number::read("2345").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("2345").unwrap().cmp(&Number::read("+2345").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("2345").unwrap().cmp(&Number::read("2345").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("2345").unwrap().cmp(&Number::read("0002345").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("234").unwrap().cmp(&Number::read("2345").unwrap()), Ordering::Less);
    assert_eq!(Number::read("0").unwrap().cmp(&Number::read("0").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("0").unwrap().cmp(&Number::read("+0").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("0").unwrap().cmp(&Number::read("-0").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("+0").unwrap().cmp(&Number::read("0").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("+0").unwrap().cmp(&Number::read("+0").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("+0").unwrap().cmp(&Number::read("-0").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("-0").unwrap().cmp(&Number::read("0").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("-0").unwrap().cmp(&Number::read("+0").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("-0").unwrap().cmp(&Number::read("-0").unwrap()), Ordering::Equal);
    assert_eq!(Number::read("000000234").unwrap().cmp(&Number::read("2345").unwrap()), Ordering::Less);
    assert_eq!(Number::read("000000234").unwrap().cmp(&Number::read("236521548").unwrap()), Ordering::Less);
    assert_eq!(Number::read("000000234").unwrap().cmp(&Number::read("000000236521548").unwrap()), Ordering::Less);
    assert_eq!(Number::read("01000000").unwrap().cmp(&Number::read("000000236521548").unwrap()), Ordering::Less);
    assert_eq!(Number::read("123").unwrap().cmp(&Number::read("101").unwrap()), Ordering::Greater);

    assert_eq!(Number::read("2345").unwrap(), Number::read("2345").unwrap());
    assert_eq!(Number::read("2345").unwrap(), Number::read("02345").unwrap());
    assert_eq!(Number::read("002345").unwrap(), Number::read("2345").unwrap());

    assert_eq!(Number::read(""), None);
    assert_eq!(Number::read("help"), None);
    assert_eq!(Number::read("-"), None);
    assert_eq!(Number::read("+"), None);

    fn get(v: &str) -> &str { Number::read(v).unwrap().as_str() }
    assert_eq!(get("2345"), "2345");
    assert_eq!(get("002345"), "002345");
    assert_eq!(get("00000"), "00000");
    assert_eq!(get("0"), "0");

    for a in -128..=128 {
        for b in -128..=128 {
            assert_eq!(Number::read(&format!("{a}")).unwrap().cmp(&Number::read(&format!("{b}")).unwrap()), a.cmp(&b));
            assert_eq!(Number::read(&format!("{a}")).unwrap().cmp(&Number::read(&format!("{b:+}")).unwrap()), a.cmp(&b));
            assert_eq!(Number::read(&format!("{a:+}")).unwrap().cmp(&Number::read(&format!("{b}")).unwrap()), a.cmp(&b));
            assert_eq!(Number::read(&format!("{a:+}")).unwrap().cmp(&Number::read(&format!("{b:+}")).unwrap()), a.cmp(&b));
        }

        assert_eq!(Number::read("0").unwrap().cmp(&Number::read(&format!("{a:+}")).unwrap()), 0.cmp(&a));
        assert_eq!(Number::read("+0").unwrap().cmp(&Number::read(&format!("{a:+}")).unwrap()), 0.cmp(&a));
        assert_eq!(Number::read("-0").unwrap().cmp(&Number::read(&format!("{a:+}")).unwrap()), 0.cmp(&a));

        assert_eq!(Number::read(&format!("{a:+}")).unwrap().cmp(&Number::read("0").unwrap()), a.cmp(&0));
        assert_eq!(Number::read(&format!("{a:+}")).unwrap().cmp(&Number::read("+0").unwrap()), a.cmp(&0));
        assert_eq!(Number::read(&format!("{a:+}")).unwrap().cmp(&Number::read("-0").unwrap()), a.cmp(&0));
    }
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
    assert_eq!(Segment::read(""), None);

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
    assert_eq!(cmp("hello--456", "hello-0999"), Ordering::Less);
    assert_eq!(cmp("v1.4.12.3", "v1.4.4.3"), Ordering::Greater);
    assert_eq!(cmp("val[-1]", "val[0]"), Ordering::Less);
}

/// Sorts an array via the [`cmp`] ordering.
/// 
/// Because this function performs a stable sort, it must be allocating and so is only enabled with the `alloc` (default) feature.
/// If `alloc` is not enabled or you do not require a stable sort, you may instead consider using [`sort_unstable`].
/// 
/// ```
/// # use numeric_sort::sort;
/// let mut arr = ["file-1", "file-10", "file-2"];
/// sort(&mut arr);
/// assert_eq!(&arr, &["file-1", "file-2", "file-10"]);
/// ```
#[cfg(feature = "alloc")]
pub fn sort<T: AsRef<str>>(arr: &mut [T]) {
    arr.sort_by(|a, b| cmp(a.as_ref(), b.as_ref())) // [T]::sort_by is stable and so requires alloc
}

/// Equivalent to [`sort`], but performs an unstable sort.
/// 
/// Because this function works in-place, it is available even when the default `alloc` feature is disabled.
pub fn sort_unstable<T: AsRef<str>>(arr: &mut [T]) {
    arr.sort_unstable_by(|a, b| cmp(a.as_ref(), b.as_ref()))
}

#[test]
#[cfg(feature = "alloc")]
fn test_sort() {
    use alloc::borrow::ToOwned;

    macro_rules! sorted { ($in:expr) => {{ let mut v = $in; sort(&mut v); v }} }
    assert_eq!(&sorted!(["file-1", "file-10", "file-2"]), &["file-1", "file-2", "file-10"]);
    assert_eq!(&sorted!(["file-1".to_owned(), "file-10".to_owned(), "file-2".to_owned()]), &["file-1", "file-2", "file-10"]);

    macro_rules! sorted_unstable { ($in:expr) => {{ let mut v = $in; sort_unstable(&mut v); v }} }
    assert_eq!(&sorted_unstable!(["file-1", "file-10", "file-2"]), &["file-1", "file-2", "file-10"]);
    assert_eq!(&sorted_unstable!(["file-1".to_owned(), "file-10".to_owned(), "file-2".to_owned()]), &["file-1", "file-2", "file-10"]);
}

#[test]
fn test_sort_unstable() {
    macro_rules! sorted_unstable { ($in:expr) => {{ let mut v = $in; sort_unstable(&mut v); v }} }
    assert_eq!(&sorted_unstable!(["file-1", "file-10", "file-2"]), &["file-1", "file-2", "file-10"]);
}
