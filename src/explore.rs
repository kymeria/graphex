use crate::error::{Error, Result};

use crate::display::*;

pub type ExploreResult<'a> = Result<Option<NodeObject<'a>>>;

/// The trait each node must implement.
/// This trait is templated by the library error, as we may face this error while exploring.
pub trait Node {
    fn next(&self, key: &str) -> ExploreResult;

    fn sep(&self) -> &str {
        "::"
    }

    fn explore<'k>(&self, key: &'k str) -> Result<(Option<NodeObject>, Option<&'k str>)> {
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

    fn explore<'k>(&self, key: &'k str) -> Result<(Option<NodeObject>, Option<&'k str>)> {
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
            (Some(node), Some(key)) => explore(&node, key, display),
            (Some(node), None) => Ok(display(&node)),
            (None, _) => Err(Error::Key(key.to_string())),
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

    fn next(&self, _key: &str) -> Result<Option<NodeObject>> {
        Ok(None)
    }
}

impl Node for &str {
    fn display(&self) -> &dyn Display {
        self
    }

    fn next(&self, _key: &str) -> Result<Option<NodeObject>> {
        Ok(None)
    }
}

impl Node for Vec<u8> {
    fn display(&self) -> &dyn Display {
        self
    }

    fn next(&self, _key: &str) -> Result<Option<NodeObject>> {
        Ok(None)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::display::DisplayResult;

    struct StringNode(String);

    impl Display for StringNode {
        fn print(&self, out: &mut Output) -> DisplayResult {
            out.write_str(&self.0)
        }
    }

    impl Node for StringNode {
        fn next(&self, key: &str) -> Result<Option<NodeObject>> {
            let index = key
                .parse::<usize>()
                .map_err(|_e| Error::Key(key.to_string()))?;
            Ok(self
                .0
                .get(index..index + 1)
                .map(|s| Box::new(s.to_string()).into()))
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
        fn print(&self, f: &mut Output) -> DisplayResult {
            write!(f, "{}: {}", self.name, self.value)
        }
    }

    impl Node for Child {
        fn next(&self, key: &str) -> Result<Option<NodeObject>> {
            match key {
                "name" => {
                    let temp_node = Box::new(StringNode(self.name.clone()));
                    Ok(Some(NodeObject::Owned(temp_node)))
                }
                _ => Ok(None),
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
        fn print(&self, f: &mut Output) -> DisplayResult {
            write!(f, "Root : {}\n", self.a)?;
            write!(f.pad(), "{}\n", &display_to_string(&self.b)?)?;
            write!(f.pad(), "{}", &display_to_string(&self.c)?)
        }
    }

    impl Node for Root {
        fn next(&self, key: &str) -> Result<Option<NodeObject>> {
            Ok(match key {
                "b" => Some(NodeObject::Borrowed(&self.b)),
                "c" => Some(NodeObject::Borrowed(&self.c)),
                _ => None,
            })
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
