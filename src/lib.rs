use anyhow::anyhow;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{i128, u128},
    combinator::map,
    error::{make_error, Error, ErrorKind},
    number::complete::double,
    sequence::separated_pair,
    AsChar, IResult, Parser,
};
use std::fmt;

mod evcxr;
mod parse_string;

pub use self::evcxr::print_evcxr;
use self::parse_string::parse_string;

pub fn parse(input: &str) -> anyhow::Result<Value> {
    let (rest, value) = Value::parse(input).map_err(|e| anyhow!("{:?}", e))?;
    if !rest.is_empty() {
        return Err(anyhow!(
            "Failed to consume all of string!\nValue:\n{:?},\n\nRest:\n{:?}",
            value,
            rest
        ));
    }

    Ok(value)
}

trait Parse: Sized {
    fn parse(input: &str) -> IResult<&str, Self>;
}

/// The different kinds of values.
///
/// Destructure this to get at the value.
pub enum Value {
    Struct(Struct),
    Set(Set),
    Map(Map),
    List(List),
    Tuple(Tuple),
    Term(Term),
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Struct(v) => fmt::Debug::fmt(v, f),
            Value::Set(v) => fmt::Debug::fmt(v, f),
            Value::Map(v) => fmt::Debug::fmt(v, f),
            Value::List(v) => fmt::Debug::fmt(v, f),
            Value::Tuple(v) => fmt::Debug::fmt(v, f),
            Value::Term(v) => fmt::Debug::fmt(v, f),
        }
    }
}

impl Parse for Value {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        alt((
            (Struct::parse).map(Value::Struct),
            (Map::parse).map(Value::Map), // try map before set (because set will match map)
            (Set::parse).map(Value::Set),
            (List::parse).map(Value::List),
            (Tuple::parse).map(Value::Tuple),
            (Term::parse).map(Value::Term),
        ))(input)
    }
}

pub enum Term {
    I128(i128),
    U128(u128),
    F64(f64),
    Ident(String),
    String(String),
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::I128(v) => fmt::Debug::fmt(v, f),
            Term::U128(v) => fmt::Debug::fmt(v, f),
            Term::F64(v) => fmt::Debug::fmt(v, f),
            // Idents are displayed without surrounding quotation marks.
            Term::Ident(v) => fmt::Display::fmt(v, f),
            Term::String(v) => fmt::Debug::fmt(v, f),
        }
    }
}

impl Term {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        // If input parses as a double, we need to check if it would be parsable as
        // an integer first. We don't want to parse "0" as a f64.
        //
        // But we also don't want to parse "12.2" as "12" because there's more
        // information consumed when we parse it as a double.
        if let Ok((rest, v)) = double::<_, ()>(input) {
            if let Ok((other_rest, other_v)) = i128::<_, ()>(input) {
                if other_rest.len() <= rest.len() {
                    return Ok((other_rest, Term::I128(other_v)));
                }
            }

            if let Ok((other_rest, other_v)) = u128::<_, ()>(input) {
                if other_rest.len() <= rest.len() {
                    return Ok((other_rest, Term::U128(other_v)));
                }
            }

            return Ok((rest, Term::F64(v)));
        }

        alt((
            map(i128, Term::I128),
            map(u128, Term::U128),
            map(parse_ident, Term::Ident),
            map(parse_string, Term::String),
        ))(input)
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

impl fmt::Debug for Set {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.values.iter()).finish()
    }
}

pub struct Struct {
    pub name: String,
    pub values: Vec<IdentValue>,
}

impl Struct {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (input, name) = parse_ident(input)?;

        let input = consume_ws(input);
        let (input, _) = tag("{")(input)?;
        // because we're gonna parse everything as a value (in the catch-all) we first need to
        // separate out at the "}".
        let (input, rest) =
            split_on('}', input).ok_or(nom::Err::Error(make_error(input, ErrorKind::Fail)))?;

        let values = parse_comma_separated(input)?;
        Ok((rest, Self { name, values }))
    }
}

impl fmt::Debug for Struct {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut item = f.debug_struct(&self.name);
        for v in &self.values {
            item.field(&v.ident, &v.value);
        }
        item.finish()
    }
}

pub struct IdentValue {
    pub ident: String,
    pub value: Value,
}

impl Parse for IdentValue {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        separated_pair(
            parse_ident,
            |s| tag(":")(consume_ws(s)),
            |s| Value::parse(consume_ws(s)),
        )(input)
        .map(|(rest, (ident, value))| (rest, IdentValue { ident, value }))
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

impl fmt::Debug for Map {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map()
            .entries(self.values.iter().map(|v| (&v.key, &v.value)))
            .finish()
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

impl fmt::Debug for List {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.values.iter()).finish()
    }
}

pub struct Tuple {
    pub name: Option<String>,
    pub values: Vec<Value>,
}

impl Tuple {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (input, name) = if let Ok((rest, name)) = parse_ident(input) {
            (rest, Some(name))
        } else {
            (input, None)
        };
        let (input, _) = tag("(")(input)?;
        // because we're gonna parse everything as a value (in the catch-all) we first need to
        // separate out at the "}".
        let (input, rest) =
            split_on(')', input).ok_or(nom::Err::Error(make_error(input, ErrorKind::Fail)))?;
        let values = parse_comma_separated(input)?;
        Ok((rest, Self { name, values }))
    }
}

impl fmt::Debug for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut tuple = f.debug_tuple(self.name.as_deref().unwrap_or(""));
        for v in &self.values {
            tuple.field(v);
        }
        tuple.finish()
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
    pub key: Value,
    pub value: Value,
}

impl Parse for KeyValue {
    fn parse(input: &str) -> IResult<&str, Self> {
        separated_pair(
            Value::parse,
            |s| tag(":")(consume_ws(s)),
            |s| Value::parse(consume_ws(s)),
        )(input)
        .map(|(rest, (key, value))| (rest, KeyValue { key, value }))
    }
}

impl fmt::Debug for KeyValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.key, f)?;
        write!(f, ": ")?;
        fmt::Debug::fmt(&self.value, f)
    }
}

/// parses an ident from a complete input.
fn parse_ident(input: &str) -> IResult<&str, String> {
    let mut chrs = input.char_indices().peekable();
    match chrs.next() {
        Some((_, ch)) if ch.is_alpha() || ch == '_' => (),
        _ => return Err(nom::Err::Error(make_error(input, ErrorKind::Alpha))),
    }
    while matches!(chrs.peek(), Some((_, ch)) if ch.is_alphanumeric() || *ch == '_') {
        let _ = chrs.next();
    }
    match chrs.next() {
        Some((idx, _)) => Ok((&input[idx..], input[..idx].to_string())),
        None => Ok(("", input.to_string())),
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

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

    #[track_caller]
    fn assert_same_debug<T: std::fmt::Debug>(item: &T) {
        let parsed = parse(&format!("{:?}", item)).expect("can parse");
        assert_eq!(format!("{:#?}", parsed), format!("{:#?}", item));
        assert_eq!(format!("{:?}", parsed), format!("{:?}", item));
    }

    #[test]
    fn numbers() {
        assert_same_debug(&0);
        assert_same_debug(&2);
        assert_same_debug(&-2);
        assert_same_debug(&2.14);
        assert_same_debug(&u128::MAX);
        assert_same_debug(&i128::MAX);
        assert_same_debug(&i128::MIN);
        // Not supported.
        // assert_same_debug(&f64::NEG_INFINITY);
        // assert_same_debug(&f64::INFINITY);
    }

    #[test]
    fn simple_types() {
        assert_same_debug(&"Foo");
        assert_same_debug(&vec!["Foo", "Bar", "Zed"]);
        assert_same_debug(&{
            let mut map = HashMap::new();
            map.insert(2, "Foo");
            map.insert(200, "Hello world");
            map
        });
    }

    #[test]
    fn tuples() {
        assert_same_debug(&("Foo", 32, -12.0));
    }

    #[test]
    fn object_tuples() {
        #[derive(Debug)]
        struct Foo(&'static str, u32, f32);

        assert_same_debug(&Foo("Foo", 32, -12.0));
    }

    #[test]
    fn trivial_object() {
        #[derive(Debug)]
        struct Foo {
            value: f32,
        }

        let item = Foo { value: 12.2 };
        assert_same_debug(&item);
    }

    #[test]
    fn object() {
        #[derive(Debug)]
        struct Foo {
            value: f32,
            bar: Vec<Bar>,
        }

        #[derive(Debug)]
        struct Bar {
            elo: i32,
        }

        let item = Foo {
            value: 12.2,
            bar: vec![Bar { elo: 200 }, Bar { elo: -12 }],
        };
        assert_same_debug(&item);
    }

    #[test]
    fn hashmap_with_object_values() {
        #[derive(Debug)]
        struct Foo {
            value: f32,
            bar: Vec<Bar>,
        }

        #[derive(Debug)]
        struct Bar {
            elo: i32,
        }

        let item = {
            let mut map = HashMap::new();
            map.insert(
                "foo",
                Foo {
                    value: 12.2,
                    bar: vec![Bar { elo: 200 }, Bar { elo: -12 }],
                },
            );
            map.insert(
                "foo2",
                Foo {
                    value: -0.2,
                    bar: vec![],
                },
            );
            map
        };
        assert_same_debug(&item);
    }

    #[test]
    fn hashmap_with_object_keys() {
        #[derive(Debug, PartialEq, Eq, Hash)]
        struct Foo {
            value: i32,
            bar: Vec<Bar>,
        }

        #[derive(Debug, PartialEq, Eq, Hash)]
        struct Bar {
            elo: i32,
        }

        let item = {
            let mut map = HashMap::new();
            map.insert(
                Foo {
                    value: 12,
                    bar: vec![Bar { elo: 200 }, Bar { elo: -12 }],
                },
                "foo",
            );
            map.insert(
                Foo {
                    value: -2,
                    bar: vec![],
                },
                "foo2",
            );
            map
        };
        assert_same_debug(&item);
    }
}
