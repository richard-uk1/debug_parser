use anyhow::anyhow;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, multispace0, none_of},
    combinator::{map, recognize},
    error::{Error, ParseError},
    multi::{many0_count, many1, separated_list0},
    sequence::{delimited, pair, separated_pair},
    IResult, Parser,
};
use std::fmt;

mod parse_string;
use self::parse_string::parse_string;

pub fn parse(input: &str) -> anyhow::Result<Value> {
    let (rest, value) = Value::parse(input).map_err(|e| anyhow!("{:?}", e))?;
    if !rest.is_empty() {
        return Err(anyhow!(
            "Failed to consume all of string!\nValue:\n{:?}\n\nRest:\n{:?}",
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
#[derive(PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Ident(String),
    String(String),
    /// This variant supports basic numbers and also gives best-effort support for
    /// difficult edge cases like f64::INFINITY and custom Debug implementations (which
    /// work as long as they don't include whitespace or a number of special characters
    /// (":", ",", etc)).
    UnquotedRawString(String),
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Idents are displayed without surrounding quotation marks.
            Term::Ident(v) => fmt::Display::fmt(v, f),
            Term::String(v) => fmt::Debug::fmt(v, f),
            // Raw strings are displayed without surrounding quotation marks.
            Term::UnquotedRawString(v) => fmt::Display::fmt(v, f),
        }
    }
}

impl Term {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        alt((
            map(parse_ident, Term::Ident),
            map(parse_string, Term::String),
            map(many1(none_of(":, {}[]()")), |c| {
                Term::UnquotedRawString(c.into_iter().collect())
            }),
        ))(input)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Set {
    pub values: Vec<Value>,
}

impl Set {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (rest, values) = parse_comma_separated_wrapped(input, "{", "}")?;
        Ok((rest, Set { values }))
    }
}

impl fmt::Debug for Set {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.values.iter()).finish()
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Struct {
    pub name: String,
    pub values: Vec<IdentValue>,
}

impl Struct {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (input, name) = parse_ident(input)?;

        let input = consume_ws(input);
        let (rest, values) = parse_comma_separated_wrapped(input, "{", "}")?;
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

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct IdentValue {
    pub ident: String,
    pub value: Value,
}

impl Parse for IdentValue {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (rest, (ident, value)) = separated_pair(parse_ident, tag(":"), Value::parse)(input)?;
        Ok((rest, IdentValue { ident, value }))
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Map {
    pub values: Vec<KeyValue>,
}

impl Map {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (rest, values) = parse_comma_separated_wrapped(input, "{", "}")?;
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

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct List {
    pub values: Vec<Value>,
}

impl List {
    fn parse(input: &str) -> IResult<&str, Self> {
        let input = consume_ws(input);
        let (rest, values) = parse_comma_separated_wrapped(input, "[", "]")?;
        Ok((rest, Self { values }))
    }
}

impl fmt::Debug for List {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.values.iter()).finish()
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
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
        let (rest, values) = parse_comma_separated_wrapped(input, "(", ")")?;
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

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct KeyValue {
    pub key: Value,
    pub value: Value,
}

impl Parse for KeyValue {
    fn parse(input: &str) -> IResult<&str, Self> {
        separated_pair(ws(Value::parse), ws(tag(":")), ws(Value::parse))(input)
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

fn parse_ident(input: &str) -> IResult<&str, String> {
    // https://docs.rs/nom/latest/nom/recipes/index.html#rust-style-identifiers
    recognize(pair(
        alt((alpha1, tag("_"))),
        many0_count(alt((alphanumeric1, tag("_")))),
    ))(input)
    .map(|(rest, matched)| (rest, matched.to_string()))
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

/// A combinator that takes a parser `inner` and produces a parser that also consumes both leading and
/// trailing whitespace, returning the output of `inner`.
fn ws<'a, F: 'a, O, E: ParseError<&'a str>>(
    inner: F,
) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O, E>,
{
    delimited(multispace0, inner, multispace0)
}

fn parse_comma_separated<T: Parse>(input: &str) -> Result<(&str, Vec<T>), nom::Err<Error<&str>>> {
    separated_list0(tag(","), T::parse)(consume_ws(input))
}

fn parse_comma_separated_wrapped<'a, T: Parse>(
    input: &'a str,
    begin_wrap: &'static str,
    end_wrap: &'static str,
) -> Result<(&'a str, Vec<T>), nom::Err<Error<&'a str>>> {
    delimited(
        ws(tag(begin_wrap)),
        parse_comma_separated,
        ws(tag(end_wrap)),
    )(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashMap, HashSet};

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
        assert_same_debug(&f64::NEG_INFINITY);
        assert_same_debug(&f64::INFINITY);
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
        #[allow(unused)]
        struct Foo {
            value: f32,
        }

        let item = Foo { value: 12.2 };
        assert_same_debug(&item);
    }

    #[test]
    fn trivial_set() {
        let item = {
            let mut set = HashSet::new();
            set.insert("foo");
            set.insert("bar");
            set
        };
        assert_same_debug(&item);
    }

    #[test]
    fn set_with_objects() {
        #[derive(Debug, Hash, PartialEq, Eq)]
        #[allow(unused)]
        struct Foo {
            value: u32,
        }

        let item = {
            let mut set = HashSet::new();
            set.insert(Foo { value: 12 });
            set.insert(Foo { value: 2 });
            set
        };
        assert_same_debug(&item);
    }

    #[test]
    fn just_objects() {
        #[derive(Debug)]
        #[allow(unused)]
        struct Foo {
            value: f32,
            bar: Vec<Bar>,
        }

        #[derive(Debug)]
        #[allow(unused)]
        struct Bar {
            elo: i32,
        }

        let item = Foo {
            value: 12.2,
            bar: vec![Bar { elo: 200 }, Bar { elo: -12 }],
        };
        assert_same_debug(&item);

        let item = Foo {
            value: 1.0,
            bar: vec![],
        };
        assert_same_debug(&item);
    }

    #[test]
    fn hashmap_with_simple_object_values() {
        #[derive(Debug)]
        #[allow(unused)]
        struct Bar {
            elo: i32,
        }

        let item = {
            let mut map = HashMap::new();
            map.insert("foo", Bar { elo: 200 });
            map.insert("foo2", Bar { elo: -10 });
            map
        };
        assert_same_debug(&item);
    }

    #[test]
    fn hashmap_with_object_values() {
        #[derive(Debug)]
        #[allow(unused)]
        struct Foo {
            value: f32,
            bar: Vec<Bar>,
        }

        #[derive(Debug)]
        #[allow(unused)]
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

    #[test]
    fn hashmap_with_string_keys() {
        let item = {
            let mut map = HashMap::new();
            map.insert("2022-10-5", "foo");
            map.insert("2019-4-12", "foo");
            map
        };
        assert_same_debug(&item);
    }

    #[test]
    fn hashmap_with_unquoted_string_keys() {
        #[derive(PartialEq, Eq, Hash)]
        struct RawString(&'static str);

        impl fmt::Debug for RawString {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        let item = {
            let mut map = HashMap::new();
            map.insert(RawString("2022-10-5"), "foo");
            map.insert(RawString("2019-4-12"), "foo");
            map
        };
        assert_same_debug(&item);
    }
}
