use std::{collections::HashMap, fmt::Write};

use crate::error::{Error, Result};

pub trait Display {
    fn print(&self, out: &mut Output) -> Result {
        if let Some((header, footer)) = self.header_footer() {
            if !header.is_empty() {
                writeln!(out, "{}", header)?;
            }
            self.print_content(&mut out.pad())?;
            if !footer.is_empty() {
                writeln!(out, "{}", footer)?
            }
        } else {
            self.print_content(out)?;
        }
        Ok(())
    }

    fn header_footer(&self) -> Option<(String, String)> {
        None
    }

    fn print_content(&self, out: &mut Output) -> Result;

    fn start_same_line(&self) -> bool {
        self.header_footer().is_some()
    }
}

pub struct Output<'a> {
    output: &'a mut dyn Write,
    padding: String,
}

impl<'a> Output<'a> {
    pub fn new(output: &'a mut dyn Write) -> Self {
        Self {
            output,
            padding: String::new(),
        }
    }

    pub fn new_with_padding(output: &'a mut dyn Write, padding: String) -> Self {
        Self { output, padding }
    }

    pub fn write_str(&mut self, s: &str) -> Result {
        if s.contains('\n') {
            for l in s.lines() {
                self.output
                    .write_str(&format!("{}{l}\n", self.padding))
                    .map_err(|e| Error::Fmt(e))?;
            }
        } else {
            self.output
                .write_str(&format!("{}{s}", self.padding))
                .map_err(|e| Error::Fmt(e))?;
        }

        Ok(())
    }

    pub fn write_char(&mut self, c: char) -> Result {
        let formated = format!("{}", c);
        self.write_str(&formated)
    }

    pub fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> Result {
        let formated = format!("{}", args);
        self.write_str(&formated)
    }

    pub fn pad(&mut self) -> Output {
        Output {
            output: self.output,
            padding: self.padding.clone() + "  ",
        }
    }

    pub fn clone(&mut self) -> Output {
        Output {
            output: self.output,
            padding: self.padding.clone(),
        }
    }

    pub fn mapping(&mut self, header: &str) -> Result<Mapping> {
        write!(self, "{header} (\n")?;
        Ok(Mapping {
            output: self.clone(),
        })
    }

    pub fn item(&mut self, name: &str, value: &impl Display) -> Result {
        let header = if name.is_empty() {
            "- ".to_string()
        } else {
            format!("- {name}:")
        };
        let value_str = display_to_string(value)?;
        let multi_line = value_str.contains('\n');
        if multi_line {
            if value.start_same_line() {
                let mut first = true;
                value_str
                    .lines()
                    .map(|l| {
                        if first {
                            first = false;
                            writeln!(self, "{header} {l}")
                        } else {
                            writeln!(self, "{l}")
                        }
                    })
                    .collect::<std::result::Result<_, _>>()?;
                Ok(())
            } else {
                writeln!(self, "{}", header)?;
                writeln!(self.pad(), "{value_str}")
            }
        } else {
            writeln!(self, "{header} {value_str}")
        }
    }
}

pub struct Mapping<'a> {
    output: Output<'a>,
}

impl Mapping<'_> {
    pub fn item(&mut self, name: &str, value: &impl Display) -> Result {
        let mut output = self.output.pad();
        output.item(name, value)
    }

    pub fn close(&mut self) -> Result {
        writeln!(self.output, ")")
    }
}

macro_rules! impl_display {
    ($ty:ty) => {
        impl Display for $ty {
            fn print_content(&self, out: &mut Output) -> Result {
                write!(out, "{}", self)
            }
        }
    };
    ($ty:ty, $($other:ty),+) => {
        impl_display!($ty);
        impl_display!($($other),+);
    }
}

impl_display!(
    String, usize, u128, u64, u32, u16, u8, isize, i128, i64, i32, i16, i8, f32, f64, bool
);

impl Display for &str {
    fn print_content(&self, out: &mut Output) -> Result {
        out.write_str(self)
    }
}

impl<T, U> Display for (T, U)
where
    T: Display,
    U: Display,
{
    fn print_content(&self, out: &mut Output) -> Result {
        let str_0 = display_to_string(&self.0)?;
        let str_1 = display_to_string(&self.1)?;
        let is_multi_line = str_0.contains('\n') || str_1.contains('\n');
        if is_multi_line {
            let sub_padding = out.padding.clone();
            write!(out, "(\n{sub_padding}{str_0}\n{sub_padding}{str_1})",)
        } else {
            write!(out, "({str_0}, {str_1})")
        }
    }
}

impl<T> Display for Vec<T>
where
    T: Display,
{
    fn print_content(&self, out: &mut Output) -> Result {
        for v in self.iter() {
            write!(out, "- {}\n", display_to_string(v)?)?;
        }
        Ok(())
    }
}

impl<T> Display for Option<T>
where
    T: Display,
{
    fn print_content(&self, out: &mut Output) -> Result {
        match self {
            None => out.write_str("None"),
            Some(v) => v.print(out),
        }
    }
}

impl<T> Display for std::rc::Rc<T>
where
    T: Display,
{
    fn print_content(&self, out: &mut Output) -> Result {
        self.as_ref().print(out)
    }
}

impl<T> Display for std::sync::Arc<T>
where
    T: Display,
{
    fn print_content(&self, out: &mut Output) -> Result {
        self.as_ref().print(out)
    }
}

impl<K, T> Display for HashMap<K, T>
where
    T: Display,
    K: AsRef<str>,
{
    fn print_content(&self, out: &mut Output) -> Result {
        for (key, val) in self.iter() {
            out.item(key.as_ref(), val)?;
        }
        Ok(())
    }
}

pub struct AsBytes<'a>(pub &'a [u8]);

impl Display for AsBytes<'_> {
    fn print_content(&self, out: &mut Output) -> Result {
        write!(out, "{:?}", &self.0)
    }
}

pub fn display(node: &dyn Display, out: &mut dyn Write) -> Result {
    let mut out = Output::new(out);
    node.print(&mut out)
}

pub fn display_to_string(node: &dyn Display) -> Result<String> {
    let mut output = String::new();
    display(node, &mut output)?;
    let end_of_content = output.trim_end().len();
    output.truncate(end_of_content);
    Ok(output)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn simple_value() {
        assert_eq!(display_to_string(&5_u8).unwrap(), "5");
        assert_eq!(display_to_string(&5_u64).unwrap(), "5");
        assert_eq!(display_to_string(&5.0).unwrap(), "5");
        assert_eq!(display_to_string(&5.1).unwrap(), "5.1");
        assert_eq!(display_to_string(&"Hello").unwrap(), "Hello");
        assert_eq!(display_to_string(&"World".to_string()).unwrap(), "World");
    }

    #[test]
    fn vec_value() {
        assert_eq!(
            display_to_string(&AsBytes(&vec![5_u8, 4_u8, 6_u8])).unwrap(),
            "[5, 4, 6]"
        );
        assert_eq!(
            display_to_string(&vec![5_u32, 4_u32, 6_u32]).unwrap(),
            "- 5\n- 4\n- 6"
        );
    }

    #[test]
    fn simple_hashmap() {
        let foo = HashMap::from([
            ("a", "Hello"),
            ("b", "World"),
            ("c", "Long content\non several lines"),
        ]);

        let expected = {
            // HashMap is not ordered (or at least known at compile time).
            // So we have to construct expected string in the same order than the hashmap
            let expected_map = HashMap::from([
                ("a", "- a: Hello"),
                ("b", "- b: World"),
                ("c", "- c:\n  Long content\n  on several lines"),
            ]);
            foo.iter()
                .map(|(k, _)| expected_map[k])
                .collect::<Vec<_>>()
                .join("\n")
        };
        assert_eq!(display_to_string(&foo).unwrap(), expected);
    }

    #[test]
    fn simple_tuple() {
        assert_eq!(display_to_string(&(5, "Hello")).unwrap(), "(5, Hello)");
    }

    #[test]
    fn simple_struct() {
        struct Foo {
            a: u32,
            b: i32,
        }

        impl Display for Foo {
            fn header_footer(&self) -> Option<(String, String)> {
                Some(("Foo:".to_string(), String::new()))
            }

            fn print_content(&self, out: &mut Output) -> Result {
                out.item("a", &self.a)?;
                out.item("b", &self.b)
            }
        }

        let f = Foo { a: 5, b: -5 };
        assert_eq!(display_to_string(&f).unwrap(), "Foo:\n  - a: 5\n  - b: -5");
    }

    #[test]
    fn multi_line_struct() {
        struct Foo {
            a: u32,
            b: Vec<i32>,
        }

        impl Display for Foo {
            fn header_footer(&self) -> Option<(String, String)> {
                Some(("Foo:".to_string(), String::new()))
            }
            fn print_content(&self, out: &mut Output) -> Result {
                out.item("a", &self.a)?;
                out.item("b", &self.b)
            }
        }

        let f = Foo {
            a: 5,
            b: vec![-5, 6],
        };
        assert_eq!(
            display_to_string(&f).unwrap(),
            "Foo:\n  - a: 5\n  - b:\n    - -5\n    - 6"
        );
    }

    #[test]
    fn multi_struct() {
        struct Foo {
            a: u32,
            b: Vec<String>,
        }

        struct Bar {
            a: Foo,
            b: Foo,
            c: Vec<u8>,
        }

        impl Display for Foo {
            fn header_footer(&self) -> Option<(String, String)> {
                Some(("Foo:".to_string(), String::new()))
            }
            fn print_content(&self, out: &mut Output) -> Result {
                out.item("a", &self.a)?;
                out.item("b", &self.b)
            }
        }

        impl Display for Bar {
            fn header_footer(&self) -> Option<(String, String)> {
                Some(("Bar:".to_string(), String::new()))
            }
            fn print_content(&self, out: &mut Output) -> Result {
                out.item("a", &self.a)?;
                out.item("b", &self.b)?;
                out.item("c", &AsBytes(&self.c))
            }
        }

        let fa = Foo {
            a: 42,
            b: vec!["Hello".to_string(), "World".to_string()],
        };
        let fb = Foo {
            a: 56,
            b: vec!["Bye".to_string(), "Bye".to_string(), "Home".to_string()],
        };
        let b = Bar {
            a: fa,
            b: fb,
            c: vec![56, 58, 75],
        };

        assert_eq!(
            display_to_string(&b).unwrap(),
            "Bar:
  - a: Foo:
    - a: 42
    - b:
      - Hello
      - World
  - b: Foo:
    - a: 56
    - b:
      - Bye
      - Bye
      - Home
  - c: [56, 58, 75]"
        )
    }
}
