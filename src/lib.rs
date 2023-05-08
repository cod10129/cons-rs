//! A crate that contains a singly linked list.
//!
//! Note:
//! This is different from the standard [`LinkedList`],
//! which is doubly linked.
//!
//! [`LinkedList`]: alloc::collections::LinkedList
#![no_std]
#![warn(missing_docs)]

// clippy settings
#![warn(clippy::alloc_instead_of_core)]
#![warn(clippy::std_instead_of_alloc)]
#![warn(clippy::std_instead_of_core)]
#![allow(clippy::must_use_candidate)]
#![allow(clippy::return_self_not_must_use)]

extern crate alloc;
use alloc::boxed::Box;

pub mod immutable;

/// A singly linked list.
/// See the [crate-level documentation](crate) for more.
#[derive(Default)]
pub struct List<T> {
    head: Link<T>,
}

struct Node<T> {
    elem: T,
    next: Link<T>,
}

type Link<T> = Option<Box<Node<T>>>;

impl<T> List<T> {
    /// Creates an empty `List`.
    #[inline]
    pub fn new() -> Self {
        List { head: None }
    }

    /// Prepends an element to the beginning of the `List`.
    pub fn push(&mut self, element: T) {
        let new = Node {
            elem: element,
            next: self.head.take(),
        };

        self.head = Some(Box::new(new));
    }

    /// Removes the element at the front of the `List`,
    /// and returns it.
    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.elem
        })
    }

    /// Checks if the `List` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Returns an immutable reference to the value
    /// at the head of the `List`, if it exists.
    #[inline]
    pub fn peek(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    /// Returns a mutable reference to the value
    /// at the head of the `List`, if it exists.
    #[inline]
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.elem)
    }

    /// Creates an [iterator that yields immutable references](Iter)
    /// to all the elements in the `List`.
    ///
    /// To get mutable references, see [`iter_mut`](List::iter_mut).
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            next: self.head.as_deref(),
        }
    }

    /// Creates an [iterator that yields mutable references](IterMut)
    /// to all the elements in the `List`.
    ///
    /// To get immutable references, see [`iter`](List::iter).
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            next: self.head.as_deref_mut(),
        }
    }
}

/// An [iterator](Iterator) that yields immutable references
/// to all the elements in a `List`.
///
/// For mutable references, see [`IterMut`].
pub struct Iter<'a, T> {
    next: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|node| {
            self.next = node.next.as_deref();
            &node.elem
        })
    }
}

/// An [iterator](Iterator) that yields mutable references
/// to all the elements in a `List`.
///
/// For immutable references, see [`Iter`].
pub struct IterMut<'a, T> {
    next: Option<&'a mut Node<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|node| {
            self.next = node.next.as_deref_mut();
            &mut node.elem
        })
    }
}

/// An [iterator](Iterator) that yields all the elements in a `List` by value.
pub struct IntoIter<T>(List<T>);

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}

impl<T> FromIterator<T> for List<T> {
    /// Creates a `List` from an Iterator.
    ///
    /// Note that the order of elements is REVERSED.
    /// This is subject to change in the future.
    /// ```
    /// use cons_rs::List;
    ///
    /// let mut list: List<i32> = vec![1, 2]::collect();
    ///
    /// assert_eq!(list.pop(), Some(2));
    /// assert_eq!(list.pop(), Some(1));
    /// assert_eq!(list.pop(), None);
    /// ```
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = List::new();
        for elem in iter {
            list.push(elem);
        }
        list
    }
}

impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut current = self.head.take();

        while let Some(mut node) = current {
            current = node.next.take();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::List;

    #[test]
    fn push_and_pop() {
        let mut list = List::new();

        assert_eq!(list.pop(), None);

        list.push(1);
        list.push(2);
        list.push(3);

        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), Some(2));

        list.push(4);
        list.push(5);

        assert_eq!(list.pop(), Some(5));
        assert_eq!(list.pop(), Some(4));
        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), None);
    }

    #[test]
    fn peek() {
        let mut list = List::new();
        assert_eq!(list.peek(), None);
        assert_eq!(list.peek_mut(), None);

        list.push(1);
        list.push(2);
        list.push(3);

        assert_eq!(list.peek(), Some(&3));
        assert_eq!(list.peek_mut(), Some(&mut 3));
        list.peek_mut().map(|val| *val = 42);

        assert_eq!(list.peek(), Some(&42));
        assert_eq!(list.peek_mut(), Some(&mut 42));
        assert_eq!(list.pop(), Some(42));
        assert_eq!(list.pop(), Some(2));
    }

    #[test]
    fn is_empty() {
        let mut list = List::new();
        assert!(list.is_empty());

        list.push(1);
        assert!(!list.is_empty());

        list.pop();
        assert!(list.is_empty());
    }

    #[test]
    fn default() {
        let mut list = List::default();
        assert!(list.is_empty());
        list.push(1);
        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), None);
    }

    #[test]
    fn into_iter() {
        let mut list = List::new();

        list.push(1);
        list.push(2);

        let mut iter = list.into_iter();
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn for_loop() {
        let mut list = List::new();

        list.push(0);
        list.push(1);

        let mut i = 1;
        for elem in list {
            assert_eq!(elem, i);
            i -= 1;
        }
    }

    #[test]
    fn iter() {
        let mut list = List::new();

        list.push(1);
        list.push(2);

        let mut iter = list.iter();

        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut list = List::new();

        list.push(1);
        list.push(2);
        list.push(3);

        let mut iter = list.iter_mut();

        assert_eq!(iter.next(), Some(&mut 3));
        assert_eq!(iter.next(), Some(&mut 2));
        iter.next().map(|val| *val = 10);
        assert_eq!(iter.next(), None);

        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), Some(2));
        assert_eq!(list.pop(), Some(10));
        assert_eq!(list.pop(), None);
    }

    #[test]
    fn from_iter() {
        let vec = alloc::vec![1, 2, 3];
        let mut list: List<_> = vec.into_iter().collect();

        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), Some(2));
        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), None);
    }
}
