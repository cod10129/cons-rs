//! A list of nested pairs.
//! 
//! The type [`List`] represents an immutable singly linked list.
//! Every [`List`] is either [`Cons`] and contains a value and
//! another [`List`], or [`Nil`], which contains nothing.
#![no_std]
#![warn(missing_docs)]

extern crate alloc;
use alloc::boxed::Box;

pub use List::{Cons, Nil};

/// An enum that represents a `Cons` list.
/// See [the module level documentation](self) for more.
#[derive(Debug, PartialEq, Clone, Default)]
pub enum List<T> {
    /// A value of type `T`, and a Box containing another [`List`].
    Cons(T, Box<List<T>>),
    /// Nothing.
    #[default]
    Nil
}

/// An alias for the data contained by a [`Cons`],
/// `(T, List<T>)`.
pub type ConsData<T> = (T, List<T>);

impl<T> List<T> {
    /// Returns a new [`Cons`] where `x` is the only value
    /// in the [`List`].
    ///
    /// This is equivalent to `Cons(x, Box::new(Nil))`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x = List::new(5);
    /// assert_eq!(x, Cons(5, Box::new(Nil)));
    /// ```
    #[inline]
    pub fn new(x: T) -> List<T> {
        Cons(x, Box::new(Nil))
    }

    /// Returns true if the List is a [`Cons`] value.
    ///
    /// # Examples
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x: List<i32> = List::new(5);
    /// assert_eq!(x.is_cons(), true);
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.is_cons(), false);
    /// ```
    #[inline]
    pub const fn is_cons(&self) -> bool {
        matches!(self, Cons(_, _))
    }

    /// Returns true if the List is a [`Nil`] value.
    ///
    /// # Examples:
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x: List<i32> = List::new(5);
    /// assert_eq!(x.is_nil(), false);
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.is_nil(), true);
    /// ```
    #[inline]
    pub const fn is_nil(&self) -> bool {
        !self.is_cons()
    }

    /// Converts from `&List<T>` to `List<&T>`.
    pub fn as_ref(&self) -> List<&T> {
        match *self {
            Cons(ref val, ref next) => Cons(val, Box::new((**next).as_ref())),
            Nil => Nil
        }
    }

    /// Converts from `&mut List<T>` to `List<&mut T>`.
    pub fn as_mut(&mut self) -> List<&mut T> {
        match *self {
            Cons(ref mut val, ref mut next) => Cons(val, Box::new((**next).as_mut())),
            Nil => Nil
        }
    }

    /// Returns the [`Cons`] value and next [`List`], 
    /// consuming `self`.
    ///
    /// # Panics
    ///
    /// Panics if `self` is [`Nil`].
    ///
    /// # Examples
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x = List::new(5);
    /// assert_eq!(x.expect("foo"), (5, Nil));
    /// ```
    ///
    /// ```should_panic
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x: List<i32> = Nil;
    /// x.expect("foo"); // panics with "foo"
    /// ```
    #[inline]
    pub fn expect(self, msg: &str) -> ConsData<T> {
        match self {
            Cons(val, next) => (val, *next),
            Nil => panic!("{msg}")
        }
    }
    
    /// Returns the [`Cons`] value and next [`List`], 
    /// consuming `self`.
    ///
    /// Usage of this function is discouraged, as it may panic.
    /// Instead, prefer to use pattern matching, 
    /// [`unwrap_or`] or [`unwrap_or_default`].
    ///
    /// # Panics
    ///
    /// Panics if `self` is [`Nil`].
    ///
    /// # Examples
    /// ```
    /// # use cons_rs::{List, Nil};
    /// #
    /// let x = List::new(5);
    /// assert_eq!(x.unwrap(), (5, Nil));
    /// ```
    ///
    /// ```should_panic
    /// # use cons_rs::{List, Nil};
    /// #
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.unwrap(), (5, Nil)); // fails
    /// ```
    ///
    /// [`unwrap_or`]: List::unwrap_or
    /// [`unwrap_or_default`]: List::unwrap_or_default
    #[inline]
    pub fn unwrap(self) -> ConsData<T> {
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
    /// let x = List::new(5);
    /// assert_eq!(x.unwrap_or((6, Nil)), (5, Nil));
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.unwrap_or((6, Nil)), (6, Nil));
    /// ```
    #[inline]
    pub fn unwrap_or(self, default: ConsData<T>) -> ConsData<T> {
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
    /// let x = List::new(3);
    /// assert_eq!(x.unwrap_or_default(), (3, Nil));
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.unwrap_or_default(), (0, Nil));
    /// ```
    ///
    /// [default value]: Default::default
    #[inline]
    pub fn unwrap_or_default(self) -> ConsData<T> 
    where T: Default {
        match self {
            Cons(val, next) => (val, *next),
            Nil => (Default::default(), Nil)
        }
    }

    /// Maps [`List<T>`] to [`List<U>`] by applying a function to the contained value
    /// (if [`Cons`], discarding the `next` value), or if [`Nil`], returns [`Nil`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x = List::new("Hello World".to_string());
    /// let x_len = x.map(|s| s.len());
    /// assert_eq!(x_len, List::new(11));
    ///
    /// let x: List<String> = Nil;
    /// let x_len = x.map(|s| s.len());
    /// assert_eq!(x_len, Nil);
    /// ```
    pub fn map<U, F>(self, f: F) -> List<U>
    where F: FnOnce(T) -> U
    {
        match self {
            Cons(val, _) => Cons(f(val), Box::new(Nil)),
            Nil => Nil
        }
    }

    /// Maps [`List<T>`] to [`List<U>`] by applying a function to the contained value
    /// (if [`Cons`]), or returns [`Nil`] (if [`Nil`]).
    ///
    /// # Examples
    ///
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// // you can unpack with a pattern
    /// let f = |(x, list)| (x + 1, list);
    /// let x = List::new(5).map_next(f);
    /// assert_eq!(x, Cons(6, Box::new(Nil)));
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.map_next(f), Nil);
    /// ```
    pub fn map_next<U, F>(self, f: F) -> List<U>
    where F: FnOnce(ConsData<T>) -> ConsData<U>
    {
        match self {
            Cons(val, next) => {
                let result = f((val, *next));
                Cons(result.0, Box::new(result.1))
            },
            Nil => Nil
        }
    }
}

// if anyone reads this and knows how to make it better,
// please tell me. raise an issue on the repo
impl<T> FromIterator<T> for List<T> {
    fn from_iter<U: IntoIterator<Item = T>>(iter: U) -> Self {
        let mut container = alloc::collections::VecDeque::new();
        // have to use a loop to make it List<T> instead of T
        for item in iter {
            container.push_back(Cons(item, Box::new(Nil)));
        }
        let mut list: List<T> = Nil;
        while let Some(Cons(val, _)) = container.pop_back() {
            list = Cons(val, Box::new(list));
        }
        list
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = ListIterator<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        ListIterator::new(self)
    }
}

/// An iterator over a `List<T>`.
/// 
/// It is created by the `into_iter` method on [`List<T>`],
/// provided by the `IntoIterator` trait.
pub struct ListIterator<'a, T> {
    next: &'a List<T>
}

impl<'a, T> ListIterator<'a, T> {
    // private to the library, List::into_iter is the public API
    #[inline]
    fn new(list: &'a List<T>) -> Self {
        ListIterator { next: list }
    }
}

impl<'a, T> Iterator for ListIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Cons(val, next) = self.next {
            self.next = &**next;
            Some(val)
        } else {
            None
        }
    }
}

impl<T> List<&T> {
    /// Maps a `List<&T>` to a `List<T>` by copying the contents of the list.
    ///
    /// # Examples
    /// 
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x = 3;
    /// let list_x = List::new(&x);
    /// assert_eq!(list_x, List::new(&3));
    ///
    /// let copy_x = list_x.copied();
    /// assert_eq!(copy_x, List::new(3));
    /// ```
    pub fn copied(self) -> List<T> 
    where T: Copy {
        self.map(|x| *x)
    }

    /// Maps a `List<&T>` to a `List<T>` by cloning the contents of the list.
    ///
    /// # Examples
    /// 
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x = 3;
    /// let list_x = List::new(&x);
    /// assert_eq!(list_x, List::new(&3));
    ///
    /// let clone_x = list_x.cloned();
    /// assert_eq!(clone_x, List::new(3));
    /// ```
    pub fn cloned(self) -> List<T>
    where T: Clone {
        self.map(|x| x.clone())
    }
}

impl<T> List<&mut T> {
    /// Maps a `List<&mut T>` to a `List<T>` by copying the contents of the list.
    ///
    /// # Examples
    /// 
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let mut x = 3;
    /// let list_x = List::new(&mut x);
    /// assert_eq!(list_x, List::new(&mut 3));
    ///
    /// let copy_x = list_x.copied();
    /// assert_eq!(copy_x, List::new(3));
    /// ```
    pub fn copied(self) -> List<T> 
    where T: Copy {
        self.map(|x| *x)
    }

    /// Maps a `List<&mut T>` to a `List<T>` by cloning the contents of the list.
    ///
    /// # Examples
    /// 
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let mut x = 3;
    /// let list_x = List::new(&mut x);
    /// assert_eq!(list_x, List::new(&mut 3));
    ///
    /// let clone_x = list_x.cloned();
    /// assert_eq!(clone_x, List::new(3));
    /// ```
    pub fn cloned(self) -> List<T>
    where T: Clone {
        self.map(|x| x.clone())
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
    fn expect() {
        let x = List::new(5);
        assert_eq!(x.expect("foo"), (5, Nil));
    }

    #[test]
    #[should_panic(expected = "foobar")]
    fn expect_panic() {
        let x: List<i32> = Nil;
        x.expect("foobar");
    }
    
    #[test]
    fn unwrap() {
        let x = Cons(2, Box::new(Nil));
        assert_eq!(x.unwrap(), (2, Nil));
    }

    #[test]
    #[should_panic(expected = "List::unwrap")]
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
    fn map() {
        use alloc::string::String;
        let x: List<String> = Cons(String::from("Hello"), Box::new(Nil));
        assert_eq!(x.map(|s| s.len()), List::new(5));
        assert_eq!(Nil.map(|s: String| s.len()), Nil);
    }

    #[test]
    fn map_next() {
        let f = |(x, y)| (x + 1, y);
        let x = Cons(2, Box::new(List::new(3)));
        assert_eq!(x.map_next(f), Cons(3, Box::new(List::new(3))));
        assert_eq!(Nil.map_next(f), Nil);
    }

    #[test]
    fn as_ref() {
        use alloc::string::ToString;
        let x = Cons("air".to_string(), Box::new(List::new("hello".to_string())));
        assert_eq!(x.as_ref(), Cons(&"air".to_string(), Box::new(List::new(&"hello".to_string()))));
    }

    #[test]
    fn as_mut() {
        let mut x = List::new(6);
        assert_eq!(x.as_mut(), List::new(&mut 6));
    }

    #[test]
    fn cl_ref() {
        let x = List::new(&4);
        assert_eq!(x.cloned(), List::new(4));
    }

    #[test]
    fn cp_ref() {
        let x = List::new(&4);
        assert_eq!(x.copied(), List::new(4));
    }

    #[test]
    fn cl_mut() {
        let mut v = 4;
        let x = List::new(&mut v);
        assert_eq!(x.cloned(), List::new(v));
    }

    #[test]
    fn cp_mut() {
        let mut v = 4;
        let x = List::new(&mut v);
        assert_eq!(x.copied(), List::new(v));
    }
    
    #[test]
    fn iter() {
        let list = Cons(2, Box::new(Cons(4, Box::new(Nil))));
        let mut iterator = list.into_iter();
        assert_eq!(iterator.next(), Some(&2));
        assert_eq!(iterator.next(), Some(&4));
        assert_eq!(iterator.next(), None);
    }
   
    
    #[test]
    fn iter_loop() {
        let list = Cons(0, Box::new(Cons(2, Box::new(Cons(4, Box::new(Nil))))));
        for (i, &val) in list.into_iter().enumerate() {
            assert_eq!(val, i * 2);
        }
    }

    #[test]
    fn for_loop() {
        let list = Cons(0, Box::new(Cons(1, Box::new(Cons(2, Box::new(Nil))))));
        let mut i = 0;
        for val in &list {
            assert_eq!(val, &i);
            i += 1;
        }
    }

    #[test]
    fn from_iter() {
        let list: List<_> = List::from_iter(1..=5);

        assert_eq!(list, 
                  Cons(1, Box::new(
                      Cons(2, Box::new(
                          Cons(3, Box::new(
                              Cons(4, Box::new(
                                  Cons(5, Box::new(Nil))
                              ))
                          ))
                      ))
                  )));
                // that was 11 close-parens in a row
    }
}
