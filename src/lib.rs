//! A list of nested pairs.
//! 
//! The type [`List`] represents a Cons-style structure.
//! Every [`List`] is either [`Cons`] and contains a value and
//! another [`List`], or [`Nil`], which contains nothing.
#![warn(missing_docs)]
pub use List::{Cons, Nil};

/// An enum that represents a `Cons` list.
/// See [the module level documentation](self) for more.
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub enum List<T> {
    /// A value of type `T`, and a Box containing another list.
    Cons(T, Box<List<T>>),
    /// Nothing.
    #[default]
    Nil
}

impl<T> List<T> {
    /// Returns true if the List is a [`Cons`] value.
    ///
    /// # Examples
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
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
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x: List<i32> = Cons(5, Box::new(Nil));
    /// assert_eq!(x.is_nil(), false);
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.is_nil(), true);
    /// ```
    pub const fn is_nil(&self) -> bool {
        !self.is_cons()
    }

    /// Returns the [`Cons`] value and next [`List`], consuming `self`.
    ///
    /// Usage of this function is discouraged, as it may panic.
    /// Instead, prefer to use pattern matching, [`unwrap_or`] or [`unwrap_or_default`].
    ///
    /// # Panics
    ///
    /// Panics if `self` is [`Nil`].
    ///
    /// # Examples
    /// ```
    /// # use cons_rs::{Cons, Nil};
    /// #
    /// let x = Cons(5, Box::new(Nil));
    /// assert_eq!(x.unwrap(), (5, Nil));
    /// ```
    ///
    /// ```should_panic
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.unwrap(), (5, Nil)); // fails
    /// ```
    ///
    /// [`unwrap_or`]: List::unwrap_or
    /// [`unwrap_or_default`]: List::unwrap_or_default
    pub fn unwrap(self) -> (T, List<T>) {
        match self {
            Cons(val, next) => (val, *next),
            Nil => panic!("Called List::unwrap() on a Nil value.")
        }
    }

    /// Returns the contained [`Cons`] value and [`List`],
    /// or a provided default.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x = Cons(5, Box::new(Nil));
    /// assert_eq!(x.unwrap_or((6, Nil)), (5, Nil));
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.unwrap_or((6, Nil)), (6, Nil));
    /// ```
    pub fn unwrap_or(self, default: (T, List<T>)) -> (T, List<T>) {
        match self {
            Cons(val, next) => (val, *next),
            Nil => default
        }
    }

    /// Returns the contained [`Cons`] value and [`List`], or a default.
    ///
    /// Consumes `self`, and if `self` is [`Cons`], returns the contained
    /// value and list, otherwise, returns the [default value] 
    /// for T and [`Nil`].
    ///
    /// # Examples
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x = Cons(3, Box::new(Nil));
    /// assert_eq!(x.unwrap_or_default(), (3, Nil));
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.unwrap_or_default(), (0, Nil));
    /// ```
    ///
    /// [default value]: Default::default
    pub fn unwrap_or_default(self) -> (T, List<T>) where T: Default {
        match self {
            Cons(val, next) => (val, *next),
            Nil => (Default::default(), Nil)
        }
    }
}

impl<T: Clone> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = ListIterator<T>;

    fn into_iter(self) -> Self::IntoIter {
        ListIterator::new(self)
    }
}

/// An iterator over a List<T>.
/// 
/// It is created by the [`into_iter`] method on [`List<T>`].
///
/// [`into_iter`]: List::into_iter
pub struct ListIterator<T> {
    next: Box<List<T>>
}

impl<T> ListIterator<T> {
    fn new(list: List<T>) -> ListIterator<T> {
        ListIterator {
            next: Box::new(list)
        }
    }
}

impl<T: Clone> Iterator for ListIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Cons(val, next) = &*self.next {
            let tmp = val.clone();
            self.next = next.clone();
            Some(tmp)
        } else {
            None
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

    #[test]
    fn unwrap() {
        let x = Cons(2, Box::new(Nil));
        assert_eq!(x.unwrap(), (2, Nil));
    }

    #[test]
    #[should_panic]
    fn unwrap_panic() {
        let x: List<u32> = Nil;
        x.unwrap(); // panics
    }

    #[test]
    fn unwrap_or() {
        let x: List<u32> = Nil;
        assert_eq!(x.unwrap_or((3, Nil)), (3, Nil));
    }

    #[test]
    fn unwrap_or_default() {
        let x: List<u32> = Nil;
        assert_eq!(x.unwrap_or_default(), (0, Nil));
    }
    
    #[test]
    fn iter() {
        let list = Cons(2, Box::new(Cons(4, Box::new(Nil))));
        let mut iterator = list.into_iter();
        assert_eq!(iterator.next(), Some(2));
        assert_eq!(iterator.next(), Some(4));
        assert_eq!(iterator.next(), None);
    }

    #[test]
    fn iter_loop() {
        let list = Cons(0, Box::new(Cons(2, Box::new(Cons(4, Box::new(Nil))))));
        for (i, val) in list.into_iter().enumerate() {
            assert_eq!(val, i * 2);
        }
    }

    #[test]
    fn for_loop() {
        let list = Cons(0, Box::new(Cons(1, Box::new(Cons(2, Box::new(Nil))))));
        let mut i = 0;
        for val in list {
            assert_eq!(val, i);
            i += 1;
        }
    }
}
