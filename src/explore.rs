use crate::error::{Error, Result};

use crate::display::*;

pub type ExploreResult<'a> = Result<NodeObject<'a>>;

/// The trait each node must implement.
/// This trait is templated by the library error, as we may face this error while exploring.
pub trait Node {
    fn next(&self, key: &str) -> ExploreResult {
        Err(Error::key(key))
    }

    fn sep(&self) -> &str {
        "::"
    }

    fn explore<'k>(&self, key: &'k str) -> Result<(NodeObject, Option<&'k str>)> {
        if let Some((first, left)) = key.split_once(self.sep()) {
            self.next(first).map(|next_node| (next_node, Some(left)))
        } else {
            self.next(key).map(|next_node| (next_node, None))
        }
    }

    fn display(&self) -> &dyn Display;

    #[cfg(feature = "serde")]
    fn serde(&self) -> Option<&dyn erased_serde::Serialize> {
        None
    }
}

/// A actuall Node
///
/// May owned a Box or simply borrow it.
pub enum NodeObject<'a> {
    Borrowed(&'a dyn Node),
    Owned(Box<dyn Node>),
}

impl<'a, T> From<Box<T>> for NodeObject<'a>
where
    T: Node + 'static,
{
    fn from(b: Box<T>) -> Self {
        Self::Owned(b)
    }
}

impl<'a, T> From<&'a T> for NodeObject<'a>
where
    T: Node,
{
    fn from(r: &'a T) -> Self {
        Self::Borrowed(r)
    }
}

impl<'a> Node for NodeObject<'a> {
    fn next(&self, key: &str) -> ExploreResult {
        match self {
            Self::Borrowed(b) => b.next(key),
            Self::Owned(o) => o.next(key),
        }
    }

    fn explore<'k>(&self, key: &'k str) -> Result<(NodeObject, Option<&'k str>)> {
        match self {
            Self::Borrowed(b) => b.explore(key),
            Self::Owned(o) => o.explore(key),
        }
    }

    fn display(&self) -> &dyn Display {
        match self {
            Self::Borrowed(b) => b.display(),
            Self::Owned(o) => o.display(),
        }
    }
}

pub fn explore<Output, F>(node: &dyn Node, key: &str, mut display: F) -> Result<Output>
where
    F: FnMut(&dyn Node) -> Output,
{
    if key.is_empty() {
        Ok(display(node))
    } else {
        match node.explore(key)? {
            (node, Some(key)) => explore(&node, key, display),
            (node, None) => Ok(display(&node)),
        }
    }
}

pub fn explore_to_string(node: &dyn Node, key: &str) -> Result<String> {
    let d = |n: &dyn Node| display_to_string(n.display());
    explore(node, key, d)?
}

impl Node for String {
    fn display(&self) -> &dyn Display {
        self
    }

    fn next(&self, key: &str) -> ExploreResult {
        Err(Error::key(key))
    }
}

impl Node for &str {
    fn display(&self) -> &dyn Display {
        self
    }

    fn next(&self, key: &str) -> ExploreResult {
        Err(Error::key(key))
    }
}

impl Node for Vec<u8> {
    fn display(&self) -> &dyn Display {
        self
    }

    fn next(&self, key: &str) -> ExploreResult {
        Err(Error::key(key))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    struct StringNode(String);

    impl Display for StringNode {
        fn print_content(&self, out: &mut Output) -> Result {
            writeln!(out, "{}", self.0)
        }
    }

    impl Node for StringNode {
        fn next(&self, key: &str) -> ExploreResult {
            let index = key.parse::<usize>().map_err(|_e| Error::key(key))?;
            self.0
                .get(index..index + 1)
                .ok_or_else(|| Error::key(key))
                .map(|s| Box::new(s.to_string()).into())
        }

        fn display(&self) -> &dyn Display {
            self
        }
    }

    struct Child {
        name: String,
        value: u32,
    }

    impl Display for Child {
        fn print_content(&self, f: &mut Output) -> Result {
            writeln!(f, "{}: {}", self.name, self.value)
        }
    }

    impl Node for Child {
        fn next(&self, key: &str) -> ExploreResult {
            match key {
                "name" => {
                    let temp_node = Box::new(StringNode(self.name.clone()));
                    Ok(NodeObject::Owned(temp_node))
                }
                _ => Err(Error::key(key)),
            }
        }

        fn display(&self) -> &dyn Display {
            self
        }
    }

    struct Root {
        a: u32,
        b: Child,
        c: Child,
    }

    impl Display for Root {
        fn header_footer(&self) -> Option<(String, String)> {
            Some((format!("Root : {}", self.a), String::new()))
        }
        fn print_content(&self, f: &mut Output) -> Result {
            writeln!(f, "{}", &display_to_string(&self.b)?)?;
            writeln!(f, "{}", &display_to_string(&self.c)?)
        }
    }

    impl Node for Root {
        fn next(&self, key: &str) -> ExploreResult {
            match key {
                "b" => Ok(NodeObject::Borrowed(&self.b)),
                "c" => Ok(NodeObject::Borrowed(&self.c)),
                _ => Err(Error::key(key)),
            }
        }

        fn display(&self) -> &dyn Display {
            self
        }
    }

    #[test]
    fn test_explore() {
        let root = Root {
            a: 5,
            b: Child {
                name: "Child_b".to_owned(),
                value: 42,
            },
            c: Child {
                name: "Child_c".to_owned(),
                value: 56,
            },
        };

        assert_eq!(
            explore_to_string(&root, "").unwrap(),
            "Root : 5\n  Child_b: 42\n  Child_c: 56"
        );

        assert_eq!(explore_to_string(&root, "b").unwrap(), "Child_b: 42");
        assert_eq!(explore_to_string(&root, "c").unwrap(), "Child_c: 56");
        assert_eq!(explore_to_string(&root, "b::name").unwrap(), "Child_b");
        assert_eq!(explore_to_string(&root, "c::name").unwrap(), "Child_c");
        assert_eq!(explore_to_string(&root, "b::name::0").unwrap(), "C");
        assert_eq!(explore_to_string(&root, "b::name::1").unwrap(), "h");
        assert_eq!(explore_to_string(&root, "b::name::2").unwrap(), "i");
        assert_eq!(explore_to_string(&root, "b::name::3").unwrap(), "l");
        assert_eq!(explore_to_string(&root, "b::name::4").unwrap(), "d");

        assert!(explore_to_string(&root, "a").is_err());
        assert!(explore_to_string(&root, "d").is_err());
        assert!(explore_to_string(&root, "b::name::10").is_err());
    }
}
