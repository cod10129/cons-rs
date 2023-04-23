//! A list of nested pairs.
//! 
//! The type [`List`] represents a Cons-style structure.
//! Every [`List`] is either [`Cons`] and contains a value and
//! another [`List`], or [`Nil`], which contains nothing.
#![warn(missing_docs)]
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
    /// let x = List::new_val(5);
    /// assert_eq!(x, Cons(5, Box::new(Nil)));
    /// ```
    #[inline]
    pub fn new_val(x: T) -> List<T> {
        Cons(x, Box::new(Nil))
    }

    /// Returns true if the List is a [`Cons`] value.
    ///
    /// # Examples
    /// ```
    /// # use cons_rs::{List, Cons, Nil};
    /// #
    /// let x: List<i32> = List::new_val(5);
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
    /// let x: List<i32> = List::new_val(5);
    /// assert_eq!(x.is_nil(), false);
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.is_nil(), true);
    /// ```
    #[inline]
    pub const fn is_nil(&self) -> bool {
        !self.is_cons()
    }

    /// Converts from `&List<T>` to `List<&T>`. If `self` is [`Cons`],
    /// `next` is always `Nil`. To preserve `next`, use [`as_ref`].
    ///
    /// [`as_ref`]: List::as_ref
    pub fn val_as_ref(&self) -> List<&T> {
        match *self {
            Cons(ref val, _) => List::new_val(val),
            Nil => Nil
        }
    }

    /// Converts from `&List<T>` to `List<&T>`. If `self` is [`Cons`],
    /// a `List` containing a reference to `val` and `next` is returned.
    /// To ignore `next`, use [`val_as_ref`].
    ///
    /// [`val_as_ref`]: List::val_as_ref
    pub fn as_ref(&self) -> List<&T> {
        match *self {
            Cons(ref val, ref next) => Cons(val, Box::new(next.val_as_ref())),
            Nil => Nil
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
    /// let x = List::new_val(5);
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
    /// let x = List::new_val(5);
    /// assert_eq!(x.unwrap_or((6, Nil)), (5, Nil));
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.unwrap_or((6, Nil)), (6, Nil));
    /// ```
    #[inline]
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
    /// let x = List::new_val(3);
    /// assert_eq!(x.unwrap_or_default(), (3, Nil));
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.unwrap_or_default(), (0, Nil));
    /// ```
    ///
    /// [default value]: Default::default
    #[inline]
    pub fn unwrap_or_default(self) -> (T, List<T>) where T: Default {
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
    /// let x = List::new_val("Hello World".to_string());
    /// let x_len = x.map(|s| s.len());
    /// assert_eq!(x_len, List::new_val(11));
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
    /// let f = |x, list| (x + 1, list);
    /// let x = List::new_val(5).map_next(f);
    /// assert_eq!(x, Cons(6, Box::new(Nil)));
    ///
    /// let x: List<i32> = Nil;
    /// assert_eq!(x.map_next(f), Nil);
    /// ```
    pub fn map_next<U, F>(self, f: F) -> List<U>
    where F: FnOnce(T, List<T>) -> (U, List<U>)
    {
        match self {
            Cons(val, next) => {
                let result = f(val, *next);
                Cons(result.0, Box::new(result.1))
            },
            Nil => Nil
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

// if anyone reads this and knows how to make it better,
// please tell me. raise an issue on the repo
impl<T> FromIterator<T> for List<T> {
    fn from_iter<U: IntoIterator<Item = T>>(iter: U) -> Self {
        let mut container = std::collections::VecDeque::new();
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

/// An iterator over a `List<T>`.
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
    fn map() {
        let x: List<String> = Cons(String::from("Hello"), Box::new(Nil));
        assert_eq!(x.map(|s| s.len()), List::new_val(5));
        assert_eq!(Nil.map(|s: String| s.len()), Nil);
    }

    #[test]
    fn map_next() {
        let f = |x, y| (x + 1, y);
        let x = Cons(2, Box::new(List::new_val(3)));
        assert_eq!(x.map_next(f), Cons(3, Box::new(List::new_val(3))));
        assert_eq!(Nil.map_next(f), Nil);
    }

    #[test]
    fn val_as_ref() {
        let x = &List::new_val("Hello World".to_string());
        assert_eq!(x.val_as_ref(), Cons(&"Hello World".to_string(), Box::new(Nil)));
        // we still own x
        println!("{x:?}");
    }

    #[test]
    fn as_ref() {
        let x = Cons("air".to_string(), Box::new(List::new_val("hello".to_string())));
        assert_eq!(x.as_ref(), Cons(&"air".to_string(), Box::new(List::new_val(&"hello".to_string()))));
    }
    
    #[test]
    fn new_val() {
        let x = List::new_val(8);
        assert_eq!(x, Cons(8, Box::new(Nil)));
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
