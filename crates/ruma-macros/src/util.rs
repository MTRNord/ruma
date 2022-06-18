use core::fmt;
use std::{fmt::Display, str::FromStr};

use proc_macro2::{Ident, Literal, Span, TokenStream};
use proc_macro_crate::{crate_name, FoundCrate};
use quote::{format_ident, quote};
use venial::Error;

pub(crate) fn import_ruma_common() -> TokenStream {
    if let Ok(FoundCrate::Name(name)) = crate_name("ruma-common") {
        let import = format_ident!("{name}");
        quote! { ::#import }
    } else if let Ok(FoundCrate::Name(name)) = crate_name("ruma") {
        let import = format_ident!("{name}");
        quote! { ::#import }
    } else if let Ok(FoundCrate::Name(name)) = crate_name("matrix-sdk") {
        let import = format_ident!("{name}");
        quote! { ::#import::ruma }
    } else if let Ok(FoundCrate::Name(name)) = crate_name("matrix-sdk-appservice") {
        let import = format_ident!("{name}");
        quote! { ::#import::ruma }
    } else {
        quote! { ::ruma_common }
    }
}

/// CamelCase's a field ident like "foo_bar" to "FooBar".
pub(crate) fn to_camel_case(name: &Ident) -> Ident {
    let span = name.span();
    let name = name.to_string();

    let s: String = name
        .split('_')
        .map(|s| s.chars().next().unwrap().to_uppercase().to_string() + &s[1..])
        .collect();
    Ident::new(&s, span)
}

/// Splits the given string on `.` and `_` removing the `m.` then camel casing to give a Rust type
/// name.
pub(crate) fn m_prefix_name_to_type_name(name: &LitStr) -> Result<Ident, venial::Error> {
    let span = name.span();
    let name = name.value();

    let name = name.strip_prefix("m.").ok_or_else(|| {
        venial::Error::new_at_span(
            span,
            format!("well-known matrix events have to start with `m.` found `{}`", name),
        )
    })?;

    let s: String = name
        .strip_suffix(".*")
        .unwrap_or(name)
        .split(&['.', '_'] as &[char])
        .map(|s| s.chars().next().unwrap().to_uppercase().to_string() + &s[1..])
        .collect();

    Ok(Ident::new(&s, span))
}

pub(crate) struct LitRepr {
    token: Literal,
    suffix: Box<str>,
}

/// A wrapper for Literal Strings around the proc-macro2::Literal
pub(crate) struct LitStr {
    repr: Box<LitRepr>,
}

impl LitStr {
    pub fn new(value: &str, span: Span) -> Self {
        let mut token = Literal::string(value);
        token.set_span(span);
        LitStr { repr: Box::new(LitRepr { token, suffix: Box::<str>::default() }) }
    }

    pub fn value(&self) -> String {
        let repr = self.repr.token.to_string();
        let (value, _suffix) = value::parse_lit_str(&repr);
        String::from(value)
    }

    pub fn span(&self) -> Span {
        self.repr.token.span()
    }

    pub fn set_span(&mut self, span: Span) {
        self.repr.token.set_span(span);
    }

    pub fn suffix(&self) -> &str {
        &self.repr.suffix
    }

    pub fn token(&self) -> Literal {
        self.repr.token.clone()
    }
}

/// A boolean literal: `true` or `false`.
pub struct LitBool {
    pub value: bool,
    pub span: Span,
}

impl LitBool {
    pub fn new(value: bool, span: Span) -> Self {
        LitBool { value, span }
    }

    pub fn value(&self) -> bool {
        self.value
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }

    pub fn token(&self) -> Ident {
        let s = if self.value { "true" } else { "false" };
        Ident::new(s, self.span)
    }
}

struct LitFloatRepr {
    token: Literal,
    digits: Box<str>,
    suffix: Box<str>,
}

/// A floating point literal: `1f64` or `1.0e10f64`.
///
/// Must be finite. May not be infinite or NaN.
pub struct LitFloat {
    repr: Box<LitFloatRepr>,
}

impl LitFloat {
    pub fn new(repr: &str, span: Span) -> Self {
        let (digits, suffix) = match value::parse_lit_float(repr) {
            Some(parse) => parse,
            None => panic!("Not a float literal: `{}`", repr),
        };

        let mut token = match value::to_literal(repr, &digits, &suffix) {
            Some(token) => token,
            None => panic!("Unsupported float literal: `{}`", repr),
        };

        token.set_span(span);
        LitFloat { repr: Box::new(LitFloatRepr { token, digits, suffix }) }
    }

    pub fn base10_digits(&self) -> &str {
        &self.repr.digits
    }

    pub fn base10_parse<N>(&self) -> Result<N>
    where
        N: FromStr,
        N::Err: Display,
    {
        self.base10_digits().parse().map_err(|err| Error::new_at_span(self.span(), err))
    }

    pub fn suffix(&self) -> &str {
        &self.repr.suffix
    }

    pub fn span(&self) -> Span {
        self.repr.token.span()
    }

    pub fn set_span(&mut self, span: Span) {
        self.repr.token.set_span(span);
    }

    pub fn token(&self) -> Literal {
        self.repr.token.clone()
    }
}

impl From<Literal> for LitFloat {
    fn from(token: Literal) -> Self {
        let repr = token.to_string();
        if let Some((digits, suffix)) = value::parse_lit_float(&repr) {
            LitFloat { repr: Box::new(LitFloatRepr { token, digits, suffix }) }
        } else {
            panic!("Not a float literal: `{}`", repr);
        }
    }
}

impl Display for LitFloat {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        self.repr.token.fmt(formatter)
    }
}

/// This is directly taken from syn https://github.com/dtolnay/syn/blob/1819d386f3015f70d51b95669ef2926070e99ef1/src/lit.rs
mod value {
    use std::ops::{Index, RangeFrom};

    use proc_macro2::Literal;

    // Returns base 10 digits and suffix.
    pub fn parse_lit_float(input: &str) -> Option<(Box<str>, Box<str>)> {
        // Rust's floating point literals are very similar to the ones parsed by
        // the standard library, except that rust's literals can contain
        // ignorable underscores. Let's remove those underscores.

        let mut bytes = input.to_owned().into_bytes();

        let start = (*bytes.get(0)? == b'-') as usize;
        match bytes.get(start)? {
            b'0'..=b'9' => {}
            _ => return None,
        }

        let mut read = start;
        let mut write = start;
        let mut has_dot = false;
        let mut has_e = false;
        let mut has_sign = false;
        let mut has_exponent = false;
        while read < bytes.len() {
            match bytes[read] {
                b'_' => {
                    // Don't increase write
                    read += 1;
                    continue;
                }
                b'0'..=b'9' => {
                    if has_e {
                        has_exponent = true;
                    }
                    bytes[write] = bytes[read];
                }
                b'.' => {
                    if has_e || has_dot {
                        return None;
                    }
                    has_dot = true;
                    bytes[write] = b'.';
                }
                b'e' | b'E' => {
                    match bytes[read + 1..].iter().find(|b| **b != b'_').unwrap_or(&b'\0') {
                        b'-' | b'+' | b'0'..=b'9' => {}
                        _ => break,
                    }
                    if has_e {
                        if has_exponent {
                            break;
                        } else {
                            return None;
                        }
                    }
                    has_e = true;
                    bytes[write] = b'e';
                }
                b'-' | b'+' => {
                    if has_sign || has_exponent || !has_e {
                        return None;
                    }
                    has_sign = true;
                    if bytes[read] == b'-' {
                        bytes[write] = bytes[read];
                    } else {
                        // Omit '+'
                        read += 1;
                        continue;
                    }
                }
                _ => break,
            }
            read += 1;
            write += 1;
        }

        if has_e && !has_exponent {
            return None;
        }

        let mut digits = String::from_utf8(bytes).unwrap();
        let suffix = digits.split_off(read);
        digits.truncate(write);
        if suffix.is_empty() || xid_ok(&suffix) {
            Some((digits.into_boxed_str(), suffix.into_boxed_str()))
        } else {
            None
        }
    }

    pub fn xid_ok(symbol: &str) -> bool {
        let mut chars = symbol.chars();
        let first = chars.next().unwrap();
        if !(first == '_' || unicode_ident::is_xid_start(first)) {
            return false;
        }
        for ch in chars {
            if !unicode_ident::is_xid_continue(ch) {
                return false;
            }
        }
        true
    }

    #[allow(clippy::unnecessary_wraps)]
    pub fn to_literal(repr: &str, digits: &str, suffix: &str) -> Option<Literal> {
        let _ = digits;
        let _ = suffix;
        Some(repr.parse::<Literal>().unwrap())
    }

    /// Get the byte at offset idx, or a default of `b'\0'` if we're looking
    /// past the end of the input buffer.
    pub fn byte<S: AsRef<[u8]> + ?Sized>(s: &S, idx: usize) -> u8 {
        let s = s.as_ref();
        if idx < s.len() {
            s[idx]
        } else {
            0
        }
    }

    // Returns (content, suffix).
    pub fn parse_lit_str(s: &str) -> (Box<str>, Box<str>) {
        match byte(s, 0) {
            b'"' => parse_lit_str_cooked(s),
            b'r' => parse_lit_str_raw(s),
            _ => unreachable!(),
        }
    }

    fn backslash_x<S>(s: &S) -> (u8, &S)
    where
        S: Index<RangeFrom<usize>, Output = S> + AsRef<[u8]> + ?Sized,
    {
        let mut ch = 0;
        let b0 = byte(s, 0);
        let b1 = byte(s, 1);
        ch += 0x10
            * match b0 {
                b'0'..=b'9' => b0 - b'0',
                b'a'..=b'f' => 10 + (b0 - b'a'),
                b'A'..=b'F' => 10 + (b0 - b'A'),
                _ => panic!("unexpected non-hex character after \\x"),
            };
        ch += match b1 {
            b'0'..=b'9' => b1 - b'0',
            b'a'..=b'f' => 10 + (b1 - b'a'),
            b'A'..=b'F' => 10 + (b1 - b'A'),
            _ => panic!("unexpected non-hex character after \\x"),
        };
        (ch, &s[2..])
    }

    fn backslash_u(mut s: &str) -> (char, &str) {
        if byte(s, 0) != b'{' {
            panic!("{}", "expected { after \\u");
        }
        s = &s[1..];

        let mut ch = 0;
        let mut digits = 0;
        loop {
            let b = byte(s, 0);
            let digit = match b {
                b'0'..=b'9' => b - b'0',
                b'a'..=b'f' => 10 + b - b'a',
                b'A'..=b'F' => 10 + b - b'A',
                b'_' if digits > 0 => {
                    s = &s[1..];
                    continue;
                }
                b'}' if digits == 0 => panic!("invalid empty unicode escape"),
                b'}' => break,
                _ => panic!("unexpected non-hex character after \\u"),
            };
            if digits == 6 {
                panic!("overlong unicode escape (must have at most 6 hex digits)");
            }
            ch *= 0x10;
            ch += u32::from(digit);
            digits += 1;
            s = &s[1..];
        }
        assert!(byte(s, 0) == b'}');
        s = &s[1..];

        if let Some(ch) = char::from_u32(ch) {
            (ch, s)
        } else {
            panic!("character code {:x} is not a valid unicode character", ch);
        }
    }

    fn next_chr(s: &str) -> char {
        s.chars().next().unwrap_or('\0')
    }

    // Clippy false positive
    // https://github.com/rust-lang-nursery/rust-clippy/issues/2329
    #[allow(clippy::needless_continue)]
    fn parse_lit_str_cooked(mut s: &str) -> (Box<str>, Box<str>) {
        assert_eq!(byte(s, 0), b'"');
        s = &s[1..];

        let mut content = String::new();
        'outer: loop {
            let ch = match byte(s, 0) {
                b'"' => break,
                b'\\' => {
                    let b = byte(s, 1);
                    s = &s[2..];
                    match b {
                        b'x' => {
                            let (byte, rest) = backslash_x(s);
                            s = rest;
                            assert!(byte <= 0x80, "Invalid \\x byte in string literal");
                            char::from_u32(u32::from(byte)).unwrap()
                        }
                        b'u' => {
                            let (chr, rest) = backslash_u(s);
                            s = rest;
                            chr
                        }
                        b'n' => '\n',
                        b'r' => '\r',
                        b't' => '\t',
                        b'\\' => '\\',
                        b'0' => '\0',
                        b'\'' => '\'',
                        b'"' => '"',
                        b'\r' | b'\n' => loop {
                            let ch = next_chr(s);
                            if ch.is_whitespace() {
                                s = &s[ch.len_utf8()..];
                            } else {
                                continue 'outer;
                            }
                        },
                        b => panic!("unexpected byte {:?} after \\ character in byte literal", b),
                    }
                }
                b'\r' => {
                    assert_eq!(byte(s, 1), b'\n', "Bare CR not allowed in string");
                    s = &s[2..];
                    '\n'
                }
                _ => {
                    let ch = next_chr(s);
                    s = &s[ch.len_utf8()..];
                    ch
                }
            };
            content.push(ch);
        }

        assert!(s.starts_with('"'));
        let content = content.into_boxed_str();
        let suffix = s[1..].to_owned().into_boxed_str();
        (content, suffix)
    }

    fn parse_lit_str_raw(mut s: &str) -> (Box<str>, Box<str>) {
        assert_eq!(byte(s, 0), b'r');
        s = &s[1..];

        let mut pounds = 0;
        while byte(s, pounds) == b'#' {
            pounds += 1;
        }
        assert_eq!(byte(s, pounds), b'"');
        let close = s.rfind('"').unwrap();
        for end in s[close + 1..close + 1 + pounds].bytes() {
            assert_eq!(end, b'#');
        }

        let content = s[pounds + 1..close].to_owned().into_boxed_str();
        let suffix = s[close + 1 + pounds..].to_owned().into_boxed_str();
        (content, suffix)
    }
}
