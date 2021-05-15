//! This crate makes it possible to initialise arrays from iterators.
//!
//! # Examples:
//!
//! ```rust
//! use from_iter::FromIterator;
//!
//! let iter = (0..).map(|i| i * 2);
//! let array = <[i32; 8]>::from_iter(iter);
//! assert_eq!(array, [0, 2, 4, 6, 8, 10, 12, 14]);
//! ```
//!
//! ```rust
//! use from_iter::FromIterator;
//!
//! let first = vec![1, 1, 2, 3, 5, 8, 13, 21, 34].into_iter();
//! let even_fibonaccis = first.filter(|n| n % 2 == 0);
//! let array = <[i32; 3]>::from_iter(even_fibonaccis);
//! ```
//!
//! ```rust
//! use from_iter::FromIterator;
//!
//! let short_iterator = vec![1, 2, 3].into_iter();
//! let long_array = match <[i32; 1000]>::try_from_iter(short_iterator) {
//!     Ok(long_array) => long_array,
//!     Err(e) => {
//!         eprintln!("{}", e);
//!         return;
//!     }
//! };
//! ```
//!
//! Note that the [from_iter](crate::FromIterator::from_iter) method will panic if the iterator
//! does not provide enough elements to fill the entire array. To avoid this, consider using the
//! [try_from_iter](crate::FromIterator::try_from_iter) method instead.
//!
//! Both methods will ignore any extra elements in the iterator.
//!

use std::{error, fmt, mem};

/// This trait contains the [from_iter](crate::FromIterator::from_iter) and
/// [try_from_iter](crate::FromIterator::try_from_iter) methods.
///
/// Example:
/// ```rust
/// use from_iter::FromIterator;
///
/// let iter = (0..).map(|i| i * 2);
/// let array = <[i32; 8]>::from_iter(iter);
/// assert_eq!(array, [0, 2, 4, 6, 8, 10, 12, 14]);
/// ```
pub trait FromIterator<A>: Sized {
    /// This method fills an array using the given iterator. Note that it
    /// will panic if the iterator doesn't contain enough items.
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self;

    /// This method fills an array using the given iterator. If there aren't
    /// enough items available, it will return a [FromIteratorError].
    fn try_from_iter<T: IntoIterator<Item = A>>(iter: T) -> Result<Self, FromIteratorError>;
}

/// This represents the error when there aren't enough items available to fill the
/// entire array.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FromIteratorError;

impl fmt::Display for FromIteratorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "iterator exhausted unexpectedly")
    }
}

impl error::Error for FromIteratorError {}

impl<A, const N: usize> FromIterator<A> for [A; N] {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        Self::try_from_iter(iter).expect("iterator exhausted unexpectedly")
    }

    fn try_from_iter<T: IntoIterator<Item = A>>(iter: T) -> Result<Self, FromIteratorError> {
        let mut iterator = iter.into_iter();

        // use [MaybeUninit::uninit_array] when that method stabilizes
        let mut array: [mem::MaybeUninit<A>; N] = unsafe {
            // This `assume_init` call is safe because we are initialising
            // a bunch of `MaybeUninit`s, which do not require initialisation.
            mem::MaybeUninit::uninit().assume_init()
        };

        for elem in &mut array[..] {
            // now fill the array using the iterator
            *elem = mem::MaybeUninit::new(iterator.next().ok_or(FromIteratorError)?);
        }

        let array_ptr = &array as *const _ as *const [A; N];

        // use [MaybeUninit::array_assume_init] when that method stabilizes
        Ok(unsafe {
            // This requires the pointer to be valid, properly aligned, and correctly
            // initialised. It would be better to use [std::mem::transmute] here,
            // but that is not possible because the types depend on the const
            // parameter `N`.
            array_ptr.read()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::FromIterator;

    #[test]
    fn it_works() {
        let iter = (0..).map(|i| i * 2);
        let arr = <[i32; 8]>::from_iter(iter);
        assert_eq!(arr, [0, 2, 4, 6, 8, 10, 12, 14]);
    }

    #[test]
    #[allow(unused_imports)]
    fn no_conflict() {
        use std::iter::FromIterator;
        let _arr = <[i32; 8]>::from_iter(0..);
    }

    #[test]
    fn try_from_iter() {
        let huge_array = <[i32; 1000]>::try_from_iter(0..).unwrap();
        assert_eq!(huge_array[0], 0);
        assert_eq!(huge_array[1], 1);
        assert_eq!(huge_array[2], 2);
        assert_eq!(huge_array[999], 999);
    }

    #[test]
    fn try_from_iter_error() {
        <[i32; 1000]>::try_from_iter(std::iter::once(5)).unwrap_err();
    }
}
