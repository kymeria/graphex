use std::{collections::HashMap, fmt::Write};

use crate::error::{Error, Result};

/// Display the value to the user.
///
/// This trait is kind of similar to `std::fmt::Display`, although far more simple.
/// This is a different trait than `std::fmt::Display` as graph exploring display may
/// be different than "classical" display.
pub trait Display {
    /// Print the value to `out`.
    ///
    /// Default implementation reuse `header_footer` and `print_content` to display
    /// the value, using a format like:
    /// ```text
    /// header
    ///    content
    /// footer
    /// ```
    /// or simply (if not header/footer):
    /// ```text
    /// content
    /// ```
    ///
    /// User should probably not reimplement `print`.
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

    /// Return the header and footer of the value.
    ///
    /// Default implementation returns `None`.
    /// One may want to implement it as:
    /// - `Some((String::from("Foo:"), String::new()))`
    /// - `Some((String::from("Foo("), String::from(")")))`
    fn header_footer(&self) -> Option<(String, String)> {
        None
    }

    /// Print the content of the value.
    ///
    /// If value is kind of a struct, `header_footer` should be implemented and
    /// `print_content` should print only the fields of the value.
    /// Else, `print_content` should simply print the value.
    fn print_content(&self, out: &mut Output) -> Result;

    /// Tell if value display can start on same line than prefix.
    ///
    /// When the value render on several line and displayed as field value of parent structure,
    /// if `strat_same_line()` is `true`,
    /// the first line will be display on the same line of the field prefix:
    /// ```text
    /// foo: <first line>
    ///   <other lines>
    ///   ...
    /// ```
    ///
    /// When `start_same_line()` is `false`:
    /// ```text
    /// foo:
    ///    <first line>
    ///    <other lines>
    ///    ...
    /// ```
    fn start_same_line(&self) -> bool {
        self.header_footer().is_some()
    }
}

/// A output where to write the value.
///
/// Output mainly tracks the current padding and properly apply it to content to display.
/// This allow to print hierarchical content easily.
///
/// It implements `write_str` so it is possible to use `write!(out, "{}", value)` on it.
///
pub struct Output<'a> {
    output: &'a mut dyn Write,
    padding: String,
}

impl<'a> Output<'a> {
    /// Create a new output from a `std::fmt::Write`.
    pub fn new(output: &'a mut dyn Write) -> Self {
        Self {
            output,
            padding: String::new(),
        }
    }

    /// Apply padding to `s` before printing it to inner output.
    pub fn write_str(&mut self, s: &str) -> Result {
        if s.contains('\n') {
            for l in s.lines() {
                self.output
                    .write_str(&format!("{}{l}\n", self.padding))
                    .map_err(Error::Fmt)?;
            }
        } else {
            self.output
                .write_str(&format!("{}{s}", self.padding))
                .map_err(Error::Fmt)?;
        }

        Ok(())
    }

    /// Apply padding to `c` before printing it to inner output.
    pub fn write_char(&mut self, c: char) -> Result {
        let formated = format!("{}", c);
        self.write_str(&formated)
    }

    /// Apply padding to `args` before printing it to inner output.
    pub fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> Result {
        let formated = format!("{}", args);
        self.write_str(&formated)
    }

    /// Create a new (sub) output with a new level of indentation.
    pub fn pad(&mut self) -> Output {
        Output {
            output: self.output,
            padding: self.padding.clone() + "  ",
        }
    }

    /// Create a new (sub) ouptput with the same level of indentation.
    pub fn clone(&mut self) -> Output {
        Output {
            output: self.output,
            padding: self.padding.clone(),
        }
    }

    /// Display a value with a prefix.
    ///
    /// Mostly equivalent to `writeln!("{header} {value}")` but properly handle
    /// when `value` displays on several lines: correctly display first line of value in
    ///   same line of prefix if `start_same_line()` is `true` and apply padding.
    ///
    /// Prefer using this method in [Display::print_content] as
    /// ```ignore
    /// out.item("foo", &self.foo)
    /// ```
    /// instead of
    /// ```ignore
    /// writeln!(out, "foo {}", display_to_string(&self.foo))
    /// ```
    pub fn item(
        &mut self,
        header: &(impl std::fmt::Display + ?Sized),
        value: &impl Display,
    ) -> Result {
        let value_str = display_to_string(value)?;
        let multi_line = value_str.contains('\n');
        if multi_line {
            if value.start_same_line() {
                let mut first = true;
                value_str.lines().try_for_each(|l| {
                    if first {
                        first = false;
                        writeln!(self, "{header} {l}")
                    } else {
                        writeln!(self, "{l}")
                    }
                })?;
                Ok(())
            } else {
                writeln!(self, "{}", header)?;
                writeln!(self.pad(), "{value_str}")
            }
        } else {
            writeln!(self, "{header} {value_str}")
        }
    }

    /// Display a value with a name.
    ///
    /// Mostly equivalent to `writeln!("- {name}: {value}")` but properly handle
    /// when `value` displays on several lines: correctly display first line of value in
    ///   same line of prefix if `start_same_line()` is `true` and apply padding.
    ///
    /// Prefer using this method in [Display::print_content] as
    /// ```ignore
    /// out.field("foo", &self.foo)
    /// ```
    /// instead of
    /// ```ignore
    /// writeln!(out, "- foo: {}", display_to_string(&self.foo))
    /// ```
    pub fn field(
        &mut self,
        name: &(impl std::fmt::Display + ?Sized),
        value: &impl Display,
    ) -> Result {
        self.item(&format!("- {name}:"), value)
    }

    /// Display a value.
    ///
    /// Mostly equivalent to `writeln!("- {value}")` but properly handle
    /// when `value` displays on several lines: correctly display first line of value in
    ///   same line of prefix if `start_same_line()` is `true` and apply padding.
    ///
    /// Prefer using this method in [Display::print_content] as
    /// ```ignore
    /// out.entry(&self.foo)
    /// ```
    /// instead of
    /// ```ignore
    /// writeln!(out, "- {}", display_to_string(&self.foo))
    /// ```
    pub fn entry(&mut self, value: &impl Display) -> Result {
        self.item(&"-", value)
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
            out.entry(v)?;
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
            out.field(key.as_ref(), val)?;
        }
        Ok(())
    }
}

/// A wrapper structure on a `&[u8]` to display it as a bytes value instead of array of u8.
///
/// `Vec<T>` implement [Display] to display itself as :
/// ```text
/// - <self[0]>
/// - <self[1]>
/// - ...
/// ```
///
/// But when handling array (Vec or slice) of `u8`, we may want to display it as
/// `[5, 6, 42, 96, 254, ...]` instead.
/// `AsBytes` allow this:
/// ```
/// use graphex::*;
/// let data = vec![5_u8, 6_u8, 42_u8, 96_u8];
/// assert_eq!(display_to_string(&AsBytes(&data)).unwrap(), "[5, 6, 42, 96]");
/// ```
pub struct AsBytes<'a>(#[doc(hidden)] pub &'a [u8]);

impl Display for AsBytes<'_> {
    fn print_content(&self, out: &mut Output) -> Result {
        write!(out, "{:?}", &self.0)
    }
}

/// Display the node to whatever implement `std::fmt::Write`.
pub fn display(node: &dyn Display, out: &mut dyn Write) -> Result {
    let mut out = Output::new(out);
    node.print(&mut out)
}

/// Display the node to a String and return it.
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
                out.field("a", &self.a)?;
                out.field("b", &self.b)
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
                out.field("a", &self.a)?;
                out.field("b", &self.b)
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
                out.field("a", &self.a)?;
                out.field("b", &self.b)
            }
        }

        impl Display for Bar {
            fn header_footer(&self) -> Option<(String, String)> {
                Some(("Bar:".to_string(), String::new()))
            }
            fn print_content(&self, out: &mut Output) -> Result {
                out.field("a", &self.a)?;
                out.field("b", &self.b)?;
                out.field("c", &AsBytes(&self.c))
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
