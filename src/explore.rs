use crate::error::{Error, Result};

use crate::display::*;

pub type ExploreResult<'a> = Result<NodeObject<'a>>;

/// The trait each node must implement.
pub trait Node {
    /// Returns the next [NodeObject] for `key`.
    ///
    /// Must return `Err(Error::Key(...))` if the key is not valid.
    fn next(&self, key: &str) -> ExploreResult {
        Err(Error::key(key))
    }

    /// The separator to use (in [explore]) to split the full key.
    fn sep(&self) -> &str {
        "::"
    }

    /// Get the next node for the full `key`.
    ///
    /// This must consume part of the key and return the next node corresponding of the consumed key and part of the key not consumed.
    /// Returns a tuple (<next_node_object>, Some(<left_key>))
    ///
    /// Default implementation split the `key` at `sep` and call `next` using the part of the key before `sep()`.
    fn explore<'k>(&self, key: &'k str) -> Result<(NodeObject, Option<&'k str>)> {
        if let Some((first, left)) = key.split_once(self.sep()) {
            self.next(first).map(|next_node| (next_node, Some(left)))
        } else {
            self.next(key).map(|next_node| (next_node, None))
        }
    }

    /// Returns a `Display` representation of the node.
    /// Most of the time, implementation is simply :
    /// ```
    /// # use graphex::*;
    /// # struct T();
    /// # impl Display for T { fn print_content(&self, out: &mut Output) -> Result { Ok(()) } }
    /// # impl Node for T {
    /// fn display(&self) -> &dyn Display {
    ///     self
    /// }
    /// # }
    /// ```
    /// as Self will also implement `Display`.
    fn display(&self) -> &dyn Display;

    /// Returns a `erased_serde::Serialize` representation of the node.
    /// Most of the time, implementation is simply :
    /// ```
    /// # use graphex::*;
    /// # #[derive(serde::Serialize)]
    /// # struct T();
    /// # impl Display for T { fn print_content(&self, out: &mut Output) -> Result { Ok(()) } }
    /// # impl Node for T {
    /// # fn display(&self) -> &dyn Display { self }
    /// fn serde(&self) -> Option<&dyn erased_serde::Serialize> {
    ///     Some(self)
    /// }
    /// # }
    /// ```

    /// as Self will also implement `serde::Serialize`.
    ///
    /// Default implementation is provided (and returns `None`) to not break
    /// project not using serde (and not implementing this) used with other dependencies
    /// also using graphex wiht "serde" feature enabled.
    ///
    /// This method exists only with "serde" feature enabled.
    #[cfg(all(feature = "serde", feature = "serde_no_default_impl"))]
    //   #[doc(cfg(feature = "serde"))]
    fn serde(&self) -> Option<&dyn erased_serde::Serialize>;

    /// Returns a `erased_serde::Serialize` representation of the node.
    /// Most of the time, implementation is simply :
    /// ```
    /// # use graphex::*;
    /// # #[derive(serde::Serialize)]
    /// # struct T();
    /// # impl Display for T { fn print_content(&self, out: &mut Output) -> Result { Ok(()) } }
    /// # impl Node for T {
    /// # fn display(&self) -> &dyn Display { self }
    /// fn serde(&self) -> Option<&dyn erased_serde::Serialize> {
    ///     Some(self)
    /// }
    /// # }
    /// ```
    /// as Self will also implement `serde::Serialize`.
    ///
    /// Default implementation is provided (and returns `None`) to not break
    /// project not using serde (and not implementing this) used with other dependencies
    /// also using graphex wiht "serde" feature enabled.
    ///
    /// This method exists only with "serde" feature enabled.
    #[cfg(all(feature = "serde", not(feature = "serde_no_default_impl")))]
    //    #[doc(cfg(feature = "serde"))]
    fn serde(&self) -> Option<&dyn erased_serde::Serialize> {
        None
    }
}

/// A actual Node
///
/// While `Node::next()` could have been declared to return a `&dyn Node`, it would have
/// limiting implementation to only return borrowed values.
/// But we want to be able to generate the pseudo graph as we explore it and so we need
/// to return a owned value.
///
/// `NodeObject` solves this, it can be a borrowed or a owned value.
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

    #[cfg(feature = "serde")]
    fn serde(&self) -> Option<&dyn erased_serde::Serialize> {
        match self {
            Self::Borrowed(b) => b.serde(),
            Self::Owned(o) => o.serde(),
        }
    }
}

/// Explore a `node` following the `key`.
///
/// Once a final node is found, `display` is called on it.
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

/// Explore a `node` following the `key` and display it in a string using [display_to_string]
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

    #[cfg(feature = "serde")]
    fn serde(&self) -> Option<&dyn erased_serde::Serialize> {
        Some(self)
    }
}

impl Node for &str {
    fn display(&self) -> &dyn Display {
        self
    }

    fn next(&self, key: &str) -> ExploreResult {
        Err(Error::key(key))
    }

    #[cfg(feature = "serde")]
    fn serde(&self) -> Option<&dyn erased_serde::Serialize> {
        Some(self)
    }
}

impl Node for Vec<u8> {
    fn display(&self) -> &dyn Display {
        self
    }

    fn next(&self, key: &str) -> ExploreResult {
        Err(Error::key(key))
    }

    #[cfg(feature = "serde")]
    fn serde(&self) -> Option<&dyn erased_serde::Serialize> {
        Some(self)
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
