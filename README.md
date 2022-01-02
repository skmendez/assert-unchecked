# assert-unchecked
Unsafe assertions that allow for optimizations in release mode.

[![build_status](https://github.com/skmendez/assert-unchecked/actions/workflows/rust.yml/badge.svg)](https://github.com/skmendez/assert-unchecked/actions)
[![Documentation](https://docs.rs/assert-unchecked/badge.svg)](https://docs.rs/assert-unchecked)
[![crates.io](https://img.shields.io/crates/v/assert-unchecked.svg)](https://crates.io/crates/assert-unchecked)

These macros use `core::hint::unreachable_unchecked`, which make it possible to write assertions that simultaneously clarify code as well as hint at optimizations to LLVM.
### Usage

Add this to your `Cargo.toml`

```toml
[dependencies]
assert_unchecked = "0.1.1"
```

### Examples

```rust
use assert_unchecked::{
    assert_eq_unchecked, assert_ne_unchecked, assert_unchecked, unreachable_unchecked,
};

fn copy(from_arr: &[u8], to_arr: &mut [u8]) {
    assert_eq!(from_arr.len(), to_arr.len());
    for i in 0..to_arr.len() {
        // SAFETY: bounds of to_arr is checked outside of loop
        // Without this line, the compiler isn't smart enough to remove the bounds check
        unsafe { assert_unchecked!(i <= to_arr.len()) };
        to_arr[i] = from_arr[i];
    }
}

fn get_last(len: usize) -> usize {
    if len == 0 {
        return 0;
    }
    let mut v = vec![0];
    for i in 1..len {
        v.push(i)
    }
    // SAFETY: `len` elements have been added to v at this point
    // Without this line, the compiler isn't smart enough to remove the bounds check
    unsafe { assert_eq_unchecked!(len, v.len()) };
    v[len - 1]
}

// Modifies `a[0]` and `a[delta]`, and then returns `a[0]`.
// delta must be non-zero and delta < a.len().
unsafe fn modify_start_and_delta(a: &mut [u8], delta: usize) -> u8 {
    // SAFETY: requirements are invariants of the unsafe function.
    assert_unchecked!(delta < a.len());
    // With this assertion, we know that a[delta] does not modify a[0],
    // which means the function can optimize the return value to always be 0.
    // This also means that all bounds checks can be removed.
    assert_ne_unchecked!(delta, 0);
    a[0] = 0;
    a[delta] = 1;
    a[0]
}

fn div_1(a: u32, b: u32) -> u32 {
    // `b.saturating_add(1)` is always positive (not zero),
    // hence `checked_div` will never return `None`.
    // Therefore, the else branch is unreachable.
    a.checked_div(b.saturating_add(1))
        .unwrap_or_else(|| unsafe { unreachable_unchecked!("division by zero isn't possible") })
}
```