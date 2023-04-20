//! A list of nested pairs.
//! 
//! The type [`List`] represents a Cons-style structure.
//! Every [`List`] is either [`Cons`] and contains a value and
//! another [`List`], or [`Nil`], which contains nothing.
#![warn(missing_docs)]
pub use List::{Cons, Nil};

/// An enum that represents a `Cons` list.
/// See [the module level documentation](self) for more.
#[derive(Debug, PartialEq, Eq)]
pub enum List<T> {
    /// A value of type `T`, and a Box containing another list.
    Cons(T, Box<List<T>>),
    /// Nothing.
    Nil
}

impl<T> List<T> {
    /// Returns true if the List is a [`Cons`] value.
    ///
    /// # Examples
    /// ```
    /// use cons_rs::{List, Cons, Nil};
    ///
    /// let x: List<i32> = Cons(5, Box::new(Nil));
    /// assert_eq!(x.is_cons(), true);
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.is_cons(), false);
    /// ```
    pub const fn is_cons(&self) -> bool {
        matches!(self, Cons(_, _))
    }

    /// Returns true if the List is a [`Nil`] value.
    ///
    /// # Examples:
    /// ```
    /// use cons_rs::{List, Cons, Nil};
    ///
    /// let x: List<i32> = Cons(5, Box::new(Nil));
    /// assert_eq!(x.is_nil(), false);
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.is_nil(), true);
    /// ```
    pub const fn is_nil(&self) -> bool {
        !self.is_cons()
    }

    /// Returns an iterator over the List.
    ///
    /// It yields all items in the List, start to end.
    ///
    /// # Panics
    ///
    /// Panics if the list is Nil.
    pub fn iter<'a>(&'a self) -> ListIterator<'a, T> {
        ListIterator::new(self).unwrap()
    }
}

/// An iterator over a List<T>.
/// 
/// It is created by the [`iter`] method on [`List<T>`].
///
/// [`iter`]: List::iter
pub struct ListIterator<'a, T> {
    next: Option<&'a List<T>>
}

impl<'a, T> ListIterator<'a, T> {
    fn new(list: &'a List<T>) -> Option<ListIterator<'a, T>> {
        if list.is_cons() {
            Some(ListIterator {
                next: Some(list)
            })
        } else {
            None
        }
    }
}

impl<'a, T> Iterator for ListIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next {
            Some(Cons(val, next)) => {
                self.next = Some(next);
                Some(val)
            },
            _ => None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn is_cons() {
        let list = Cons(3, Box::new(Nil));
        assert!(list.is_cons());
        assert!(!list.is_nil());
    }

    #[test]
    fn is_nil() {
        let list: List<i32> = Nil;
        assert!(list.is_nil());
        assert!(!list.is_cons());
    }
}
