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

    /// This method fills an array using the given iterator. Note that it
    /// will panic if the iterator doesn't contain enough items, or there are more elements than
    /// expected.
    fn from_iter_exact<T: IntoIterator<Item = A>>(iter: T) -> Self;

    /// This method fills an array using the given iterator.
    ///
    /// - If there aren't enough items available,it will return [FromIteratorExactError::NotEnoughElement].
    /// - If there are more elements than expected, it will return [FromIteratorExactError::TooManyElements].
    ///   This variant contains the last value returned from the given iterator,
    ///   since we consume the excessive element from the iterator (if any)
    ///   in order to check if the length matches.
    fn try_from_iter_exact<T: IntoIterator<Item = A>>(
        iter: T,
    ) -> Result<Self, FromIteratorExactError<A>>;
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

/// This represents the error when there aren't enough items available to fill the
/// entire array, or there are more elements than expected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FromIteratorExactError<T> {
    NotEnoughElement,
    TooManyElements(T),
}

impl<T> fmt::Display for FromIteratorExactError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FromIteratorExactError::NotEnoughElement => {
                write!(f, "iterator exhausted unexpectedly")
            }
            FromIteratorExactError::TooManyElements(_) => {
                write!(f, "iterator has more elements than expected")
            }
        }
    }
}

impl error::Error for FromIteratorError {}

impl<A, const N: usize> FromIterator<A> for [A; N] {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        Self::try_from_iter(iter).expect("iterator exhausted unexpectedly")
    }

    fn try_from_iter<T: IntoIterator<Item = A>>(iter: T) -> Result<Self, FromIteratorError> {
        try_from_iter_impl(iter, false).map_err(|_| FromIteratorError)
    }

    fn from_iter_exact<T: IntoIterator<Item = A>>(iter: T) -> Self {
        use FromIteratorExactError::*;
        match Self::try_from_iter_exact(iter) {
            Ok(ret) => ret,
            Err(NotEnoughElement) => panic!("iterator exhausted unexpectedly"),
            Err(TooManyElements(_)) => panic!("iterator has more elements than expected"),
        }
    }

    fn try_from_iter_exact<T: IntoIterator<Item = A>>(
        iter: T,
    ) -> Result<Self, FromIteratorExactError<A>> {
        try_from_iter_impl(iter, true)
    }
}

fn try_from_iter_impl<A, T: IntoIterator<Item = A>, const N: usize>(
    iter: T,
    check_next: bool,
) -> Result<[A; N], FromIteratorExactError<A>> {
    use FromIteratorExactError::*;

    let mut iterator = iter.into_iter();

    // use [MaybeUninit::uninit_array] when that method stabilizes
    let mut array: [mem::MaybeUninit<A>; N] = unsafe {
        // This `assume_init` call is safe because we are initialising
        // a bunch of `MaybeUninit`s, which do not require initialisation.
        mem::MaybeUninit::uninit().assume_init()
    };

    for elem in &mut array[..] {
        // now fill the array using the iterator
        *elem = mem::MaybeUninit::new(iterator.next().ok_or(NotEnoughElement)?);
    }

    if check_next {
        if let Some(next) = iterator.next() {
            return Err(TooManyElements(next));
        }
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

#[cfg(test)]
mod tests {
    use super::{FromIterator, FromIteratorExactError::*};

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

    #[test]
    fn test_from_iter_exact() {
        assert_eq!(
            <[i32; 6]>::from_iter_exact((0..6).map(|i| i * 2)),
            [0, 2, 4, 6, 8, 10]
        );
    }

    #[test]
    fn test_try_from_iter_exact() {
        assert_eq!(
            <[i32; 6]>::try_from_iter_exact((0..6).map(|i| i * 2)),
            Ok([0, 2, 4, 6, 8, 10])
        );
        assert_eq!(
            <[i32; 6]>::try_from_iter_exact((0..5).map(|i| i * 2)),
            Err(NotEnoughElement)
        );
        let mut even_numbers = (0..).map(|i| i * 2);
        assert_eq!(
            <[i32; 6]>::try_from_iter_exact(&mut even_numbers),
            Err(TooManyElements(12))
        );
        assert_eq!(even_numbers.next(), Some(14));
    }
}
