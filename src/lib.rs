//! A crate that contains a singly linked list.
//!
//! Note:
//! This is different from the standard [`LinkedList`],
//! which is doubly linked.
//!
//! [`LinkedList`]: alloc::collections::LinkedList
#![no_std]
#![warn(missing_docs)]
#![forbid(unsafe_code)]

// clippy settings
#![warn(
    clippy::alloc_instead_of_core, 
    clippy::std_instead_of_alloc, 
    clippy::std_instead_of_core
)]
#![allow(
    clippy::must_use_candidate, 
    clippy::return_self_not_must_use
)]

extern crate alloc;
use alloc::boxed::Box;

use core::iter::FusedIterator;
use core::fmt::{self, Debug};

// Needs to be up here so it can be imported into immutable module.
macro_rules! into_iter_impl {
    ($type: ty, $item: ty, $iter: ty, $func: path) => {
        impl<'a, T> IntoIterator for $type {
            type Item = $item;
            type IntoIter = $iter;

            fn into_iter(self) -> Self::IntoIter {
                $func(self)
            }
        }
    };
    (ref, $iter: ty, $func: path) => {
        into_iter_impl!{&'a List<T>, &'a T, $iter, $func}
    };
    (ref mut, $iter: ty, $func: path) => {
        into_iter_impl!{&'a mut List<T>, &'a mut T, $iter, $func}
    }
}

#[cfg(feature = "immutable")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "immutable")))]
pub mod immutable;

/// A singly linked list.
/// See the [crate-level documentation](crate) for more.
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
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::List;
    ///
    /// let list: List<i32> = List::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        List { head: None }
    }

    /// Prepends an element to the beginning of the `List`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::List;
    /// 
    /// let mut list = List::new();
    ///
    /// list.push(1);
    /// assert_eq!(list.peek(), Some(&1));
    ///
    /// list.push(2);
    /// assert_eq!(list.peek(), Some(&2));
    /// ```
    pub fn push(&mut self, element: T) {
        let new = Node {
            elem: element,
            next: self.head.take(),
        };

        self.head = Some(Box::new(new));
    }

    /// Removes the element at the front of the `List`,
    /// and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::List;
    /// 
    /// let mut list = List::new();
    /// assert_eq!(list.pop(), None);
    ///
    /// list.push(1);
    ///
    /// assert_eq!(list.pop(), Some(1));
    /// assert_eq!(list.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.elem
        })
    }

    /// Checks if the `List` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::List;
    /// 
    /// let mut list = List::new();
    /// assert!(list.is_empty());
    ///
    /// list.push(1);
    /// assert!(!list.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Returns the length of the `List`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::List;
    ///
    /// let mut list = List::new();
    /// assert_eq!(list.len(), 0);
    ///
    /// list.push(1);
    /// assert_eq!(list.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.iter().len()
    }
    
    /// Returns an immutable reference to the value
    /// at the head of the `List`, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::List;
    /// 
    /// let mut list = List::new();
    /// assert_eq!(list.peek(), None);
    ///
    /// list.push(1);
    /// assert_eq!(list.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    /// Returns a mutable reference to the value
    /// at the head of the `List`, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::List;
    /// 
    /// let mut list = List::new();
    /// assert_eq!(list.peek_mut(), None);
    ///
    /// list.push(1);
    /// assert_eq!(list.peek_mut(), Some(&mut 1));
    ///
    /// *list.peek_mut().unwrap() = 50;
    /// assert_eq!(list.peek_mut(), Some(&mut 50));
    /// ```
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.elem)
    }

    /// Creates an [iterator that yields shared references](Iter)
    /// to all the elements in the `List`.
    ///
    /// To get mutable references, see [`iter_mut`](List::iter_mut).
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::List;
    /// 
    /// let mut list = List::new();
    ///
    /// list.push(1);
    /// list.push(2);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            next: self.head.as_deref(),
        }
    }

    /// Creates an [iterator that yields mutable references](IterMut)
    /// to all the elements in the `List`.
    ///
    /// To get shared references, see [`iter`](List::iter).
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::List;
    /// 
    /// let mut list = List::new();
    /// 
    /// list.push(1);
    /// list.push(2);
    ///
    /// for elem in list.iter_mut() {
    ///     *elem += 10;
    /// }
    ///
    /// assert_eq!(list.pop(), Some(12));
    /// assert_eq!(list.pop(), Some(11));
    /// assert_eq!(list.pop(), None);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            next: self.head.as_deref_mut(),
        }
    }
}

impl<T: Clone> Clone for List<T> {
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}

impl<T: Debug> Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T> Default for List<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: PartialEq> PartialEq for List<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }
}

impl<T: Eq> Eq for List<T> {}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut current = self.head.take();

        while let Some(mut node) = current {
            current = node.next.take();
        }
    }
}

impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = List::new();
        list.extend(iter);
        list
    }
}

impl<T> Extend<T> for List<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        use alloc::collections::VecDeque;
        
        let mut queue = VecDeque::new();
        queue.extend(iter);
        
        while let Some(elem) = queue.pop_back() {
            self.push(elem);
        }
    }
}

into_iter_impl!{List<T>, T, IntoIter<T>, IntoIter}
into_iter_impl!{ref, Iter<'a, T>, List::iter}
into_iter_impl!{ref mut, IterMut<'a, T>, List::iter_mut}

/// An [iterator](Iterator) that yields shared references
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut len = 0;
        let mut current = self.next;
        while let Some(node) = current {
            current = node.next.as_deref();
            len += 1;
        }
        (len, Some(len))
    }
}

// No methods because they all have default impls
// NOTE:
// Once ExactSizeIterator::is_empty is stablized (github.com/rust-lang/rust/issues/35428)
// forward List::is_empty to it.
impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

impl<'a, T> FusedIterator for Iter<'a, T> {}

/// An [iterator](Iterator) that yields mutable references
/// to all the elements in a `List`.
///
/// For shared references, see [`Iter`].
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        Iter { next: self.next.as_deref() }.size_hint()
    }
}

// No methods because they all have default impls
// NOTE:
// Once ExactSizeIterator::is_empty is stablized (github.com/rust-lang/rust/issues/35428)
// forward List::is_empty to it.
impl<'a, T> ExactSizeIterator for IterMut<'a, T> {}

impl<'a, T> FusedIterator for IterMut<'a, T> {}

/// An [iterator](Iterator) that yields all the elements in a `List` by value.
pub struct IntoIter<T>(List<T>);

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.iter().size_hint()
    }
}

// No methods because they all have default impls
// NOTE:
// Once ExactSizeIterator::is_empty is stablized (github.com/rust-lang/rust/issues/35428)
// forward List::is_empty to it.
impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> FusedIterator for IntoIter<T> {}

#[cfg(test)]
mod tests {
    use super::List;
    use alloc::format;

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
    fn len() {
        let mut list = List::new();
        assert_eq!(list.len(), 0);

        list.push(1);
        list.push(2);
        assert_eq!(list.len(), 2);

        list.pop();
        assert_eq!(list.len(), 1);
    }

    #[test]
    fn size_hints() {
        let empty = (0, Some(0));
        let one = (1, Some(1));
        
        let mut list: List<i32> = List::new();
        assert_eq!(list.iter().size_hint(), empty);
        assert_eq!(list.iter_mut().size_hint(), empty);
        assert_eq!(list.into_iter().size_hint(), empty);

        let mut list = List::new();
        list.push(1);

        assert_eq!(list.iter().size_hint(), one);
        assert_eq!(list.iter_mut().size_hint(), one);
        assert_eq!(list.into_iter().size_hint(), one);
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
    fn clone() {
        let mut list = List::new();
        
        list.push(1);
        list.push(2);

        let mut new_list = list.clone();
        
        assert_eq!(list.pop(), new_list.pop());
        assert_eq!(list.pop(), new_list.pop());
        assert_eq!(list.pop(), new_list.pop());
    }

    #[test]
    fn debug_fmt() {
        let mut list = List::new();
        assert_eq!(
            "[]",
            format!("{:?}", list)
        );

        list.push(1);
        list.push(2);
        list.push(-3);

        assert_eq!(
            "[-3, 2, 1]",
            format!("{:?}", list)
        );
    }

    #[test]
    fn into_iters() {
        let mut list = List::new();

        list.push(1);
        list.push(2);

        let mut expected_val = 2;
        
        for elem in list.clone() {
            assert_eq!(elem, expected_val);
            expected_val -= 1;
        }
        expected_val = 2;
        
        for elem in &list {
            assert_eq!(elem, &expected_val);
            expected_val -= 1;
        }
        expected_val = 2;

        for elem in &mut list {
            assert_eq!(elem, &mut expected_val);
            expected_val -= 1;
        }
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
    fn extend() {
        let mut list = List::new();

        list.extend([1, 2]);

        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), Some(2));
        assert_eq!(list.pop(), None);
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
        let mut list: List<_> = [1, 2, 3].into_iter().collect();

        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), Some(2));
        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), None);
    }
}
