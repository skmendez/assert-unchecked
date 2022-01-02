//! Unsafe assertions that allow for optimizations in release mode. All of these
//! assertions if incorrect will invoke *undefined behavior* (UB) when
//! `debug_assertions` are disabled, so all usage of these macros must ensure
//! that they will truly never fail.
#![no_std]

/// Asserts that a boolean expression is `true` at runtime.
///
/// In builds with `debug-assertions` enabled, this will function equivalent to
/// [`assert`]. However, in an optimized build without `debug_assertions`
/// enabled, this assertion serves as an optimization hint; the boolean
/// expression itself will likely not appear in the generated code, but instead
/// will be assumed in a way that allows for optimizing the surrounding code.
///
/// # Safety
///
/// In release mode, the assertion failing is completely *undefined behavior*
/// (UB). Since the compiler assumes that all UB must never happen, it may use
/// the assumption that this assertion is true to optimize other sections of the
/// code.
///
/// If this assumption turns out to be wrong, i.e. the assertion can fail in
/// practice, the compiler will apply the wrong optimization strategy, and
/// may sometimes even corrupt seemingly unrelated code, causing
/// difficult-to-debug problems.
///
/// Use this function only when you can prove that the assertion will never be
/// false. Otherwise, consider just using [`assert`], or if assertions are
/// undesired in optimized code, use [`debug_assert`].
/// # Example
///
/// ```
/// use assert_unchecked::assert_unchecked;
/// fn copy(from_arr: &[u8], to_arr: &mut [u8]) {
///     assert_eq!(from_arr.len(), to_arr.len());
///     for i in 0..to_arr.len() {
///         // SAFETY: bounds of to_arr is checked outside of loop
///         // Without this line, the compiler isn't smart enough to remove the bounds check
///         unsafe { assert_unchecked!(i <= to_arr.len()) };
///         to_arr[i] = from_arr[i];
///     }
/// }
/// ```
#[macro_export]
macro_rules! assert_unchecked {
    ($cond:expr) => (assert_unchecked!($cond,));
    ($expr:expr, $($arg:tt)*) => ({
        #[cfg(debug_assertions)]
        {
            unsafe fn __needs_unsafe(){}
            __needs_unsafe();
            assert!($expr, $($arg)*);
        }
        #[cfg(not(debug_assertions))]
        {
            if !($expr) { core::hint::unreachable_unchecked() }
        }
    })
}

/// Asserts that two expressions are equal to each other (using [`PartialEq`]).
///
/// In builds with `debug-assertions` enabled, this will function equivalent to
/// [`assert_eq`]. However, in an optimized build without `debug_assertions`
/// enabled, this assertion serves as an optimization hint; the equality check
/// itself will likely not appear in the generated code, but instead will be
/// assumed in a way that allows for optimizing the surrounding code.
///
/// # Safety
///
/// In release mode, the assertion failing is completely *undefined behavior*
/// (UB). Since the compiler assumes that all UB must never happen, it may use
/// the assumption that this assertion is true to optimize other sections of the
/// code.
///
/// If this assumption turns out to be wrong, i.e. the assertion can fail in
/// practice, the compiler will apply the wrong optimization strategy, and
/// may sometimes even corrupt seemingly unrelated code, causing
/// difficult-to-debug problems.
///
/// Use this function only when you can prove that the assertion will never be
/// false. Otherwise, consider just using [`assert_eq`], or if assertions are
/// undesired in optimized code, use [`debug_assert_eq`].
///
/// # Example
///
/// ```
/// use assert_unchecked::assert_eq_unchecked;
/// fn get_last(len: usize) -> usize {
///     if len == 0 {
///         return 0;
///     }
///     let mut v = vec![0];
///     for i in 1..len {
///         v.push(i)
///     }
///     // SAFETY: `len` elements have been added to v at this point
///     // Without this line, the compiler isn't smart enough to remove the bounds check
///     unsafe { assert_eq_unchecked!(len, v.len()) };
///     v[len - 1]
/// }
/// ```
#[macro_export]
macro_rules! assert_eq_unchecked {
    ($left:expr, $right:expr) => (assert_eq_unchecked!($left, $right,));
    ($left:expr, $right:expr, $($arg:tt)*) => ({
        #[cfg(debug_assertions)]
        {
            unsafe fn __needs_unsafe(){}
            __needs_unsafe();
            assert_eq!($left, $right, $($arg)*);
        }
        #[cfg(not(debug_assertions))]
        {
            if !($left == $right) {
                core::hint::unreachable_unchecked()
            }
        }
    })
}

/// Asserts that two expressions are not equal to each other (using
/// [`PartialEq`]).
///
/// In builds with `debug-assertions` enabled, this will function equivalent to
/// [`assert_ne`]. However, in an optimized build without `debug_assertions`
/// enabled, this assertion serves as an optimization hint; the inequality check
/// itself will likely not appear in the generated code, but instead will be
/// assumed in a way that allows for optimizing the surrounding code.
///
/// # Safety
///
/// In release mode, the assertion failing is completely *undefined behavior*
/// (UB). Since the compiler assumes that all UB must never happen, it may use
/// the assumption that this assertion is true to optimize other sections of the
/// code.
///
/// If this assumption turns out to be wrong, i.e. the assertion can fail in
/// practice, the compiler will apply the wrong optimization strategy, and
/// may sometimes even corrupt seemingly unrelated code, causing
/// difficult-to-debug problems.
///
/// Use this function only when you can prove that the assertion will never be
/// false. Otherwise, consider just using [`assert_ne`], or if assertions are
/// undesired in optimized code, use [`debug_assert_ne`].
///
/// # Example
///
/// ```
/// use assert_unchecked::{assert_unchecked, assert_ne_unchecked};
/// // Modifies `a[0]` and `a[delta]`, and then returns `a[0]`.
/// // delta must be non-zero and delta < a.len().
/// // This also means that all bounds checks can be removed.
/// unsafe fn modify_start_and_delta(a: &mut [u8], delta: usize) -> u8 {
///     // SAFETY: requirements are invariants of the unsafe function.
///     assert_unchecked!(delta < a.len());
///     // With this assertion, we know that a[delta] does not modify a[0],
///     // which means the function can optimize the return value to always be 0.
///     assert_ne_unchecked!(delta, 0);
///     a[0] = 0;
///     a[delta] = 1;
///     a[0]
/// }
/// ```
#[macro_export]
macro_rules! assert_ne_unchecked {
    ($left:expr, $right:expr) => (assert_ne_unchecked!($left, $right,));
    ($left:expr, $right:expr, $($arg:tt)*) => ({
        #[cfg(debug_assertions)]
        {
            unsafe fn __needs_unsafe(){}
            __needs_unsafe();
            assert_ne!($left, $right, $($arg)*);
        }
        #[cfg(not(debug_assertions))]
        {
            if $left == $right {
                core::hint::unreachable_unchecked()
            }
        }
    })
}

/// Equivalent to the [`unreachable!`] macro in builds with `debug_assertions`
/// on, and otherwise calls [`unreachable_unchecked`].
///
/// # Safety
///
/// In release mode, reaching this function is completely *undefined behavior*
/// (UB). For more details, see the documentation for [`unreachable_unchecked`].
///
/// Use this function only when you can prove that the code will never call it.
/// Otherwise, consider using the [`unreachable!`] macro, which does not allow
/// optimizations but will panic when executed.
///
/// # Example
///
/// ```
/// use assert_unchecked::unreachable_unchecked;
/// fn div_1(a: u32, b: u32) -> u32 {
///     // `b.saturating_add(1)` is always positive (not zero),
///     // hence `checked_div` will never return `None`.
///     // Therefore, the else branch is unreachable.
///     a.checked_div(b.saturating_add(1))
///         .unwrap_or_else(|| unsafe { unreachable_unchecked!("division by zero isn't possible") })
/// }
///
/// assert_eq!(div_1(7, 0), 7);
/// assert_eq!(div_1(9, 1), 4);
/// assert_eq!(div_1(11, u32::MAX), 0);
/// ```
///
/// [`unreachable_unchecked`]: core::hint::unreachable_unchecked
#[macro_export]
macro_rules! unreachable_unchecked {
    ($($arg:tt)*) => ({
        #[cfg(debug_assertions)]
        {
            unsafe fn __needs_unsafe(){}
            __needs_unsafe();
            unreachable!($($arg)*);
        }
        #[cfg(not(debug_assertions))]
        {
            core::hint::unreachable_unchecked()
        }
    })
}

#[cfg(test)]
mod debug_assertion_tests {
    /// For tests that panic, we only test them when debug_assertions are on,
    /// as otherwise we'd be invoking UB.

    // Ensures that the expression isn't emplaced twice
    #[derive(Eq, PartialEq, Debug)]
    struct NoCopy(usize);

    #[test]
    fn test_assert_success() {
        unsafe {
            assert_unchecked!(NoCopy(0) == NoCopy(0));
            assert_unchecked!(NoCopy(1) == NoCopy(1),);
            assert_unchecked!(NoCopy(2) == NoCopy(2), "message won't appear");
            assert_unchecked!(NoCopy(3) == NoCopy(3), "{} won't {}", "message", "appear");
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion failed: NoCopy(0) == NoCopy(1)")]
    fn test_assert_fail_no_message() {
        unsafe { assert_unchecked!(NoCopy(0) == NoCopy(1)) }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion message")]
    fn test_assert_fail_message() {
        unsafe { assert_unchecked!(NoCopy(0) == NoCopy(1), "assertion message") }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion message")]
    fn test_assert_fail_message_format() {
        unsafe { assert_unchecked!(NoCopy(0) == NoCopy(1), "assertion {}", "message") }
    }

    #[test]
    fn test_assert_eq_success() {
        unsafe {
            assert_eq_unchecked!(NoCopy(0), NoCopy(0));
            assert_eq_unchecked!(NoCopy(1), NoCopy(1),);
            assert_eq_unchecked!(NoCopy(2), NoCopy(2), "message won't appear");
            assert_eq_unchecked!(NoCopy(3), NoCopy(3), "{} won't {}", "message", "appear");
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion failed: `(left == right)`")]
    fn test_assert_eq_fail_no_message() {
        unsafe { assert_eq_unchecked!(NoCopy(0), NoCopy(1)) }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion message")]
    fn test_assert_eq_fail_message() {
        unsafe { assert_eq_unchecked!(NoCopy(0), NoCopy(1), "assertion message") }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion message")]
    fn test_assert_eq_fail_message_format() {
        unsafe { assert_eq_unchecked!(NoCopy(0), NoCopy(1), "assertion {}", "message") }
    }

    #[test]
    fn test_assert_ne_success() {
        unsafe {
            assert_ne_unchecked!(NoCopy(0), NoCopy(1));
            assert_ne_unchecked!(NoCopy(1), NoCopy(2),);
            assert_ne_unchecked!(NoCopy(2), NoCopy(3), "message won't appear");
            assert_ne_unchecked!(NoCopy(3), NoCopy(4), "{} won't {}", "message", "appear");
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion failed: `(left != right)`")]
    fn test_assert_ne_fail_no_message() {
        unsafe { assert_ne_unchecked!(NoCopy(0), NoCopy(0)) }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion message")]
    fn test_assert_ne_fail_message() {
        unsafe { assert_ne_unchecked!(NoCopy(0), NoCopy(0), "assertion message") }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion message")]
    fn test_assert_ne_fail_message_format() {
        unsafe { assert_ne_unchecked!(NoCopy(0), NoCopy(0), "assertion {}", "message") }
    }

    #[test]
    fn test_unreachable_unreachable() {
        match Some(0) {
            Some(_) => {}
            // SAFETY: this is clearly unreachable
            None => unsafe { unreachable_unchecked!() },
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "internal error: entered unreachable code")]
    fn test_unreachable_no_message() {
        unsafe { unreachable_unchecked!() }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion message")]
    fn test_unreachable_message() {
        unsafe { unreachable_unchecked!("assertion message") }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion message")]
    fn test_unreachable_message_format() {
        unsafe { unreachable_unchecked!("assertion {}", "message") }
    }
}
