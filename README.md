This crate makes it possible to initialise arrays from iterators.

# Examples:

```rust
use from_iter::FromIterator;

let iter = (0..).map(|i| i * 2);
let array = <[i32; 8]>::from_iter(iter);
assert_eq!(array, [0, 2, 4, 6, 8, 10, 12, 14]);
```

```rust
use from_iter::FromIterator;

let first = vec![1, 1, 2, 3, 5, 8, 13, 21, 34].into_iter();
let even_fibonaccis = first.filter(|n| n % 2 == 0);
let array = <[i32; 3]>::from_iter(even_fibonaccis);
```

```rust
use from_iter::FromIterator;

let short_iterator = vec![1, 2, 3].into_iter();
let long_array = match <[i32; 1000]>::try_from_iter(short_iterator) {
    Ok(long_array) => long_array,
    Err(e) => {
        eprintln!("{}", e);
        return;
    }
};
```

Note that the `from_iter` method will panic if the iterator does not provide
enough elements to fill the entire array. To avoid this, consider using the
`try_from_iter` method instead.

Both methods will ignore any extra elements in the iterator.
