use nom::{
    branch::alt,
    bytes::complete::tag,
    error::{make_error, Error, ErrorKind},
    AsChar, IResult, Parser,
};
use std::fmt;

pub fn print_evcxr<T: fmt::Debug>(val: &T) {
    let val = format!("{:?}", val);
    parse(&val).to_evcxr()
}

pub fn parse(input: &str) -> Value {
    // cannot fail
    Value::parse(input).expect("unreachable").1
}

trait Parse: Sized {
    fn parse(input: &str) -> IResult<&str, Self>;
}

/// A parsed representation of debug output.
pub struct Value {
    pub name: Option<String>,
    pub kind: ValueKind,
}

impl Parse for Value {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (input, name) = match parse_ident(input) {
            Ok((i, n)) => (i, Some(n)),
            Err(_) => (input, None),
        };
        let (input, kind) = ValueKind::parse(input);
        Ok((input, Value { name, kind }))
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(name) = self.name.as_ref() {
            write!(f, "{} ", name)?;
        }
        fmt::Display::fmt(&self.kind, f)
    }
}

impl Value {
    pub fn to_evcxr(&self) {
        println!("EVCXR_BEGIN_CONTENT text/html");
        if let Some(name) = &self.name {
            println!("<h5>{}</h5>", html_escape::encode_text(&name));
        }
        if let Some(value) = self.find_list(1) {
            // we're gonna assume the list is homogeneous. If it isn't this will draw something
            // wierd
            println!("<table>");
            // inspect first element (look for map)
            if let Some(Value {
                name: _name,
                kind: ValueKind::Map(map),
            }) = value.as_list().next()
            {
                println!("<thead><tr>");
                // Use the keys as column headings
                for key in map.values.iter().map(|v| &v.key) {
                    println!("<th>{}</th>", html_escape::encode_text(&key.to_string()));
                }
                println!("</tr><thead>");
            }
            for row in value.as_list() {
                println!("<tr>");
                for cell in row.as_list() {
                    println!("<td>{}</td>", html_escape::encode_text(&cell.to_string()));
                }
                println!("</tr>");
            }

            println!("</table>");
        }
        println!("EVCXR_END_CONTENT");
    }

    /// Try to get a list from self. If nothing sensible is found, return None.
    ///
    /// The main job of this function is to recurse if the value contains a single element.
    fn find_list(&self, recurse: u8) -> Option<&Value> {
        match &self.kind {
            ValueKind::List(_) => Some(self),
            ValueKind::Set(set) => {
                if set.values.len() == 1 && recurse > 0 {
                    set.values[0].find_list(recurse - 1)
                } else {
                    Some(self)
                }
            }
            ValueKind::Tuple(tuple) => {
                if tuple.values.len() == 1 && recurse > 0 {
                    tuple.values[0].find_list(recurse - 1)
                } else {
                    Some(self)
                }
            }
            ValueKind::Map(map) => {
                if map.values.len() == 1 && recurse > 0 {
                    map.values[0].value.find_list(recurse - 1)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Return something sensible.
    fn as_list(&self) -> impl Iterator<Item = &Value> {
        enum Either<V1, V2, V3> {
            V1(V1),
            V2(V2),
            V3(V3),
        }

        impl<T, V1: Iterator<Item = T>, V2: Iterator<Item = T>, V3: Iterator<Item = T>> Iterator
            for Either<V1, V2, V3>
        {
            type Item = T;
            fn next(&mut self) -> Option<Self::Item> {
                match self {
                    Either::V1(v) => v.next(),
                    Either::V2(v) => v.next(),
                    Either::V3(v) => v.next(),
                }
            }
        }

        match &self.kind {
            ValueKind::List(list) => Either::V1(list.values.iter()),
            ValueKind::Set(set) => Either::V1(set.values.iter()),
            ValueKind::Tuple(tuple) => Either::V1(tuple.values.iter()),
            ValueKind::Map(map) => Either::V2(map.values.iter().map(|v| &v.value)),
            ValueKind::Term(_) => Either::V3(std::iter::once(self)),
        }
    }
}

/// The different kinds of values.
///
/// Destructure this to get at the value.
pub enum ValueKind {
    Set(Set),
    Map(Map),
    List(List),
    Tuple(Tuple),
    /// Something we couldn't parse any more.
    Term(String),
}

impl fmt::Display for ValueKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ValueKind::Set(v) => fmt::Display::fmt(v, f),
            ValueKind::Map(v) => fmt::Display::fmt(v, f),
            ValueKind::List(v) => fmt::Display::fmt(v, f),
            ValueKind::Tuple(v) => fmt::Display::fmt(v, f),
            ValueKind::Term(v) => fmt::Display::fmt(v, f),
        }
    }
}

impl ValueKind {
    fn parse(input: &str) -> (&str, Self) {
        let input = consume_ws(input);
        alt((
            (Map::parse).map(ValueKind::Map), // try map before set (because set will match map)
            (Set::parse).map(ValueKind::Set),
            (List::parse).map(ValueKind::List),
            (Tuple::parse).map(ValueKind::Tuple),
            parse_any.map(ValueKind::Term),
        ))(input)
        .expect("unreachable")
    }
}

pub struct Set {
    pub values: Vec<Value>,
}

impl Set {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (input, _) = tag("{")(input)?;
        // because we're gonna parse everything as a value (in the catch-all) we first need to
        // separate out at the "}".
        let (input, rest) =
            split_on('}', input).ok_or(nom::Err::Error(make_error(input, ErrorKind::Fail)))?;
        let values = parse_comma_separated(input)?;
        Ok((rest, Set { values }))
    }
}

impl fmt::Display for Set {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("{")?;
        let mut iter = self.values.iter();
        if let Some(v) = iter.next() {
            fmt::Display::fmt(v, f)?;
        }
        for v in iter {
            write!(f, ", {}", v)?;
        }
        f.write_str("}")
    }
}

pub struct Map {
    pub values: Vec<KeyValue>,
}

impl Map {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (input, _) = tag("{")(input)?;
        // because we're gonna parse everything as a value (in the catch-all) we first need to
        // separate out at the "}".
        let (input, rest) =
            split_on('}', input).ok_or(nom::Err::Error(make_error(input, ErrorKind::Fail)))?;
        let values = parse_comma_separated(input)?;
        Ok((rest, Self { values }))
    }
}

impl fmt::Display for Map {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("{")?;
        let mut iter = self.values.iter();
        if let Some(v) = iter.next() {
            fmt::Display::fmt(v, f)?;
        }
        for v in iter {
            write!(f, ", {}", v)?;
        }
        f.write_str("}")
    }
}

pub struct List {
    pub values: Vec<Value>,
}

impl List {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (input, _) = tag("[")(input)?;
        // because we're gonna parse everything as a value (in the catch-all) we first need to
        // separate out at the "}".
        let (input, rest) =
            split_on(']', input).ok_or(nom::Err::Error(make_error(input, ErrorKind::Fail)))?;
        let values = parse_comma_separated(input)?;
        Ok((rest, Self { values }))
    }
}

impl fmt::Display for List {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("[")?;
        let mut iter = self.values.iter();
        if let Some(v) = iter.next() {
            fmt::Display::fmt(v, f)?;
        }
        for v in iter {
            write!(f, ", {}", v)?;
        }
        f.write_str("]")
    }
}

pub struct Tuple {
    pub values: Vec<Value>,
}

impl Tuple {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (input, _) = tag("(")(input)?;
        // because we're gonna parse everything as a value (in the catch-all) we first need to
        // separate out at the "}".
        let (input, rest) =
            split_on(')', input).ok_or(nom::Err::Error(make_error(input, ErrorKind::Fail)))?;
        let values = parse_comma_separated(input)?;
        Ok((rest, Self { values }))
    }
}

impl fmt::Display for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("(")?;
        let mut iter = self.values.iter();
        if let Some(v) = iter.next() {
            fmt::Display::fmt(v, f)?;
        }
        for v in iter {
            write!(f, ", {}", v)?;
        }
        f.write_str(")")
    }
}

fn parse_comma_separated<T: Parse>(mut input: &str) -> Result<Vec<T>, nom::Err<Error<&str>>> {
    let mut out = vec![];
    while let Some((v, rest)) = split_on(',', input) {
        out.push(T::parse(v)?.1);
        input = rest; // skip ','
    }
    if !input.trim_end().is_empty() {
        out.push(T::parse(input)?.1);
    }
    Ok(out)
}

pub struct KeyValue {
    pub key: String,
    pub value: Value,
}

impl Parse for KeyValue {
    fn parse(input: &str) -> IResult<&str, Self> {
        let (key, value) =
            split_on(':', input).ok_or(nom::Err::Error(make_error(input, ErrorKind::Tag)))?;
        let (rest, key) = parse_ident(key.trim())?;
        if !rest.is_empty() {
            return Err(nom::Err::Error(make_error(input, ErrorKind::TooLarge)));
        }
        let (_, value) = Value::parse(value).unwrap();
        Ok(("", Self { key, value }))
    }
}

impl fmt::Display for KeyValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.key, self.value)
    }
}

/// parses an ident from a complete input.
fn parse_ident(input: &str) -> IResult<&str, String> {
    let mut chrs = input.char_indices().peekable();
    match chrs.next() {
        Some((_, ch)) if ch.is_alpha() => (),
        _ => return Err(nom::Err::Error(make_error(input, ErrorKind::Alpha))),
    }
    while matches!(chrs.peek(), Some((_, ch)) if ch.is_alphanumeric()) {
        let _ = chrs.next();
    }
    match chrs.next() {
        Some((idx, _)) => Ok((&input[idx..], input[..idx].to_string())),
        None => Ok(("", input.to_string())),
    }
}

/// A function that parses any string by returning it (minus any trailing whitespace
fn parse_any(input: &str) -> IResult<&str, String> {
    Ok(("", input.trim_end().to_string()))
}

/// Finds the next `ch` in the input and splits on it.
///
/// This function takes into account both nesting on `([{` and strings with escaping
fn split_on(split_ch: char, input: &str) -> Option<(&str, &str)> {
    macro_rules! ret {
        ($input:expr, $idx:expr) => {
            return Some((&$input[..$idx], &$input[$idx + split_ch.len()..]))
        };
    }

    let mut paren: u32 = 0; // ()
    let mut bracket: u32 = 0; // []
    let mut brace: u32 = 0; // {}
    let mut in_str = None;

    let mut iter = input.char_indices();
    while let Some((idx, ch)) = iter.next() {
        if let Some(s_end) = in_str {
            if ch == s_end {
                in_str = None;
            } else if ch == '\\' {
                // take the next character
                let _ = iter.next();
            } // else do nothing
        } else {
            if ch == split_ch && (paren | bracket | brace) == 0 {
                ret!(input, idx);
            }
            match ch {
                '(' => paren += 1,
                '[' => bracket += 1,
                '{' => brace += 1,
                ')' => paren = paren.saturating_sub(1),
                ']' => bracket = bracket.saturating_sub(1),
                '}' => brace = brace.saturating_sub(1),
                '"' => in_str = Some('"'),
                '\'' => in_str = Some('\''),
                _ => (),
            }
        }
    }
    None
}

fn consume_ws(input: &str) -> &str {
    let mut iter = input.char_indices();
    while let Some((idx, ch)) = iter.next() {
        if !ch.is_whitespace() {
            return &input[idx..];
        }
    }
    ""
}

#[test]
fn test_split_on() {
    assert_eq!(split_on(',', "test,"), Some(("test", "")));
    assert_eq!(split_on(',', "test"), None);
    assert_eq!(split_on(')', "())"), Some(("()", "")));
    assert_eq!(split_on('}', "{}}"), Some(("{}", "")));
    assert_eq!(split_on(',', r#""str,""#), None);
    assert_eq!(split_on(',', r#""str","#), Some((r#""str""#, "")));
    assert_eq!(split_on(')', r#""(")"#), Some((r#""(""#, "")));
    assert_eq!(split_on(',', "(,),)"), Some(("(,)", ")")));
}
