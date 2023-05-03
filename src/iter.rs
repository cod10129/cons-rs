use crate::{List, Cons, Nil};
use alloc::boxed::Box;

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
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

/// An iterator over a `List<T>`.
/// 
/// It is created by the [`iter`] method on [`List`].
///
/// [`iter`]: List::iter
pub struct Iter<'a, T> {
    next: &'a List<T>
}

// This function exists so List::iter can be defined in the outer scope,
// while having access to Iter::new().
// WITHOUT exporting Iter::new() to the main space
pub fn new_iter<'a, T>(list: &'a List<T>) -> Iter<'a, T> {
    Iter::new(list)
}

impl<'a, T> Iter<'a, T> {
    // private to the library, List::iter is the public API
    #[inline]
    fn new(list: &'a List<T>) -> Self {
        Iter { next: list }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Cons(val, next) = self.next {
            self.next = next.as_ref();
            Some(val)
        } else { None }
    }
}
