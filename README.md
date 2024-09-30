Graphex
=======

This library provide few traits to create a tool to explore a pseudo graph.

## Traits

- Impl `Node` to allow the node of your graph to be explored.
- Impl `Display` to display the result of the exploration.

## Faq

### Do all the graph must exists in memory ?

No, and this is why it is a **pseudo** graph.

`Node::next` can create node at runtime and return it.

### Why not using `std::fmt::Display` ?

`std::fmt::Display` is probably better implemented than `graphex::Display`.
However, there is only one impl possible for `std::fmt::Display`.
One may want to display different information (as potential key to explore next node) than `std::fmt::Display`.
Using two different traits make this possible.


## Contributing

Pull requests are welcome !!!
