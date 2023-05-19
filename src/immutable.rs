//! An immutable list using [`Rc`](Rc).
//!
//! This list does not allow direct modification of its elements,
//! but modification of the [pointers](Rc) between them.
use alloc::rc::Rc;

use super::FusedIterator;

/// A singly linked immutable list.
/// See the [module-level documentation](self) for more.
pub struct List<T> {
    head: Link<T>,
}

struct Node<T> {
    elem: T,
    next: Link<T>,
}

type Link<T> = Option<Rc<Node<T>>>;

impl<T> List<T> {
    /// Creates a new `List`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::immutable::List;
    /// 
    /// let list: List<i32> = List::new();
    /// ```
    #[inline]
    pub const fn new() -> List<T> {
        List { head: None }
    }

    /// Prepends a given element to the list,
    /// returning a copy of the list with the added element.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::immutable::List;
    /// 
    /// let list = List::new().prepend(1);
    ///
    /// assert_eq!(list.head(), Some(&1));
    /// ```
    pub fn prepend(&self, element: T) -> List<T> {
        List { head: Some(Rc::new(Node {
            elem: element,
            next: self.head.clone()
        }))}
    }

    /// Returns a copy of the list with the first element removed.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::immutable::List;
    /// 
    /// let list = List::new().prepend(1);
    /// assert_eq!(list.tail().head(), None);
    ///
    /// let list = List::new().prepend(1).prepend(2);
    /// assert_eq!(list.tail().head(), Some(&1));
    /// ```
    pub fn tail(&self) -> List<T> {
        List {
            head: self.head.as_ref().and_then(|node| node.next.clone()) 
        }
    }

    /// Returns a reference to the first element in the list,
    /// if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::immutable::List;
    /// 
    /// let list = List::new().prepend(1);
    ///
    /// assert_eq!(list.head(), Some(&1));
    /// ```
    pub fn head(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    /// Returns the length of the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::immutable::List;
    /// 
    /// let list = List::new();
    /// assert_eq!(list.len(), 0);
    ///
    /// let list = list.prepend(3);
    /// assert_eq!(list.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.iter().len()
    }

    /// Checks if the list is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::immutable::List;
    /// 
    /// let list = List::new();
    /// assert!(list.is_empty());
    ///
    /// let list = list.prepend(1);
    /// assert!(!list.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }
    
    /// Creates an [iterator that yields references](Iter)
    /// to all the elements in the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use cons_rs::immutable::List;
    /// 
    /// let list = List::new().prepend(1).prepend(2);
    ///
    /// let mut iter = list.iter();
    ///
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter { next: self.head.as_deref() }
    }
}

impl<T> Default for List<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut head = self.head.take();
        while let Some(node) = head {
            if let Ok(mut node) = Rc::try_unwrap(node) {
                head = node.next.take();
            } else {
                break;
            }
        }
    }
}

/// An [iterator](Iterator) that yields references
/// to all the elements in a list.
pub struct Iter<'a, T> {
    next: Option<&'a Node<T>>
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|node| {
            self.next = node.next.as_deref();
            &node.elem
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut len = 0;
        let mut curr = self.next;
        while let Some(node) = curr {
            curr = node.next.as_deref();
            len += 1;
        }
        (len, Some(len))
    }
}

// No methods because default impls are fine
impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

impl<'a, T> FusedIterator for Iter<'a, T> {}

#[cfg(test)]
mod tests {
    use super::List;

    #[test]
    fn head_tail_prepend() {
        let list = List::new();

        let list = list.prepend(1).prepend(2);
        assert_eq!(list.head(), Some(&2));

        let list = list.tail();
        assert_eq!(list.head(), Some(&1));

        let list = list.tail();
        assert_eq!(list.head(), None);
        
        let list = list.tail();
        assert_eq!(list.head(), None);
    }

    #[test]
    fn len() {
        let list = List::new();
        assert_eq!(list.len(), 0);
        assert_eq!(list.iter().size_hint(), (0, Some(0)));

        let list = list.prepend(1);
        assert_eq!(list.len(), 1);
        assert_eq!(list.iter().size_hint(), (1, Some(1)));
    }
    
    #[test]
    fn iter() {
        let list = List::new().prepend(1).prepend(2);

        let mut iter = list.iter();
        
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
    }
}
