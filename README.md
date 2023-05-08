# cons-rs

A crate containing a singly-linked list.

As of 0.4.1, cons-rs supports `#[no_std]` environments.
Note that it still depends on the [`alloc`] crate.

## 0.6.0
This version is a **full** rewrite of the entire crate. 
It has migrated from its past as a "list of nested pairs"
to what it has actually been the entire time, a singly-linked list.

The main reason I didn't publish this as a new crate is because
all the names are taken, and the *use cases* are mostly the same.

[`alloc`]: https://doc.rust-lang.org/stable/alloc
