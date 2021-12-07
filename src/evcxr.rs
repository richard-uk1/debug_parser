use super::*;

pub fn print_evcxr<T: fmt::Debug + ?Sized>(val: &T) -> anyhow::Result<()> {
    let val = format!("{:?}", val);
    parse(&val)?.print_evcxr();
    Ok(())
}

impl Value {
    fn print_evcxr(&self) {
        println!("EVCXR_BEGIN_CONTENT text/html");
        if let Value::Struct(Struct { name, .. }) = &self {
            println!("<h5>{}</h5>", html_escape::encode_text(&name));
        }
        if let Some(value) = self.find_list(1) {
            // we're gonna assume the list is homogeneous. If it isn't this will draw something
            // wierd
            println!("<table>");
            // inspect first element (look for map / struct)
            if let Some(header_strings) = match value.as_list().next() {
                Some(Value::Struct(s)) => Some(
                    s.values
                        .iter()
                        .map(|v| format!("{}", v.ident))
                        .collect::<Vec<_>>(),
                ),
                Some(Value::Map(m)) => {
                    Some(m.values.iter().map(|v| format!("{:?}", v.key)).collect())
                }
                _ => None,
            } {
                println!("<thead><tr>");
                for header in header_strings {
                    println!("<th>{}</th>", html_escape::encode_text(&header));
                }
                println!("</tr><thead>");
            }
            for row in value.as_list() {
                println!("<tr>");
                for cell in row.as_list() {
                    println!(
                        "<td>{}</td>",
                        html_escape::encode_text(&format!("{:?}", &cell))
                    );
                }
                println!("</tr>");
            }

            println!("</table>");
        } else {
            println!(
                "<code>{}</code>",
                html_escape::encode_text(&format!("{:?}", &self))
            );
        }
        println!("EVCXR_END_CONTENT");
    }

    /// Try to get a list from self. If nothing sensible is found, return None.
    ///
    /// The main job of this function is to recurse if the value contains a single element.
    fn find_list(&self, recurse: u8) -> Option<&Value> {
        match &self {
            Value::Struct(s) => {
                if s.values.len() == 1 && recurse > 0 {
                    s.values[0].value.find_list(recurse - 1)
                } else {
                    Some(self)
                }
            }
            Value::List(_) => Some(self),
            Value::Set(set) => {
                if set.values.len() == 1 && recurse > 0 {
                    set.values[0].find_list(recurse - 1)
                } else {
                    Some(self)
                }
            }
            Value::Tuple(tuple) => {
                if tuple.values.len() == 1 && recurse > 0 {
                    tuple.values[0].find_list(recurse - 1)
                } else {
                    Some(self)
                }
            }
            Value::Map(map) => {
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
        enum Either<V1, V2, V3, V4> {
            V1(V1),
            V2(V2),
            V3(V3),
            V4(V4),
        }

        impl<
                T,
                V1: Iterator<Item = T>,
                V2: Iterator<Item = T>,
                V3: Iterator<Item = T>,
                V4: Iterator<Item = T>,
            > Iterator for Either<V1, V2, V3, V4>
        {
            type Item = T;
            fn next(&mut self) -> Option<Self::Item> {
                match self {
                    Either::V1(v) => v.next(),
                    Either::V2(v) => v.next(),
                    Either::V3(v) => v.next(),
                    Either::V4(v) => v.next(),
                }
            }
        }

        match &self {
            Value::Struct(s) => Either::V4(s.values.iter().map(|v| &v.value)),
            Value::List(list) => Either::V1(list.values.iter()),
            Value::Set(set) => Either::V1(set.values.iter()),
            Value::Tuple(tuple) => Either::V1(tuple.values.iter()),
            Value::Map(map) => Either::V2(map.values.iter().map(|v| &v.value)),
            Value::Term(_) => Either::V3(std::iter::once(self)),
        }
    }
}
