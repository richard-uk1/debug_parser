use super::{parse, Value, ValueKind};
use std::fmt;

const MAX_ROWS: usize = 500;

pub fn show<T>(val: &T)
where
    T: fmt::Debug + ?Sized,
{
    let val = format!("{:?}", val);
    parse(&val).to_evcxr()
}

pub fn show_iter<I, T>(iter: I)
where
    I: IntoIterator<Item = T>,
    T: fmt::Debug,
{
    if MAX_ROWS == 0 {
        return;
    }

    let mut iter = iter.into_iter();
    let first = match iter.next() {
        Some(f) => f,
        None => {
            Value::empty_list().to_evcxr();
            return;
        }
    };
    println!("EVCXR_BEGIN_CONTENT text/html");
    println!("<table>");

    let first = parse(&format!("{:?}", first));
    if let Value {
        kind: ValueKind::Map(map),
        ..
    } = &first
    {
        println!("<thead><tr><th></th>");
        // Use the keys as column headings
        for key in map.values.iter().map(|v| &v.key) {
            println!("<th>{}</th>", html_escape::encode_text(&key.to_string()));
        }
        println!("</tr><thead>");
    }

    println!("<tr>");
    println!("<th>1</th>");
    for cell in first.as_list() {
        println!("<td>{}</td>", html_escape::encode_text(&cell.to_string()));
    }
    println!("</tr>");

    let mut count = 1;
    for row in iter {
        if count >= MAX_ROWS {
            break;
        }
        let row = parse(&format!("{:?}", row));
        println!("<tr>");
        println!("<th>{}</th>", count + 1);
        for cell in row.as_list() {
            println!("<td>{}</td>", html_escape::encode_text(&cell.to_string()));
        }
        println!("</tr>");
        count += 1;
    }

    println!("</table>");
    println!("EVCXR_END_CONTENT");
}

impl Value {
    fn to_evcxr(&self) {
        println!("EVCXR_BEGIN_CONTENT text/html");
        if let Some(name) = &self.name {
            println!("<h5>{}</h5>", html_escape::encode_text(&name));
        }
        if let Some(value) = self.find_list(1) {
            // if the list is empty, just diplay `[]` or similar
            if value.as_list().next().is_none() {
                println!("<code>{}</code>", value.kind);
            } else {
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
                for row in value.as_list().take(MAX_ROWS) {
                    println!("<tr>");
                    for cell in row.as_list() {
                        println!("<td>{}</td>", html_escape::encode_text(&cell.to_string()));
                    }
                    println!("</tr>");
                }

                println!("</table>");
            }
        } else {
            println!(
                "<code>{}</code>",
                html_escape::encode_text(&self.to_string())
            );
        }
        println!("EVCXR_END_CONTENT");
    }
}
