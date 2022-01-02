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
            match (&$left, &$right) {
                (left_val, right_val) => {
                    if !(*left_val == *right_val) {
                        core::hint::unreachable_unchecked()
                    }
                }
            }
        }
    })
}

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
            match (&$left, &$right) {
                (left_val, right_val) => {
                    if *left_val == *right_val {
                        core::hint::unreachable_unchecked()
                    }
                }
            }
        }
    })
}

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
    #[should_panic(expected="assertion failed: NoCopy(0) == NoCopy(1)")]
    fn test_assert_fail_no_message() {
        unsafe { assert_unchecked!(NoCopy(0) == NoCopy(1)) }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected="assertion message")]
    fn test_assert_fail_message() {
        unsafe { assert_unchecked!(NoCopy(0) == NoCopy(1), "assertion message") }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected="assertion message")]
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
    #[should_panic(expected="assertion failed: `(left == right)`")]
    fn test_assert_eq_fail_no_message() {
        unsafe { assert_eq_unchecked!(NoCopy(0), NoCopy(1)) }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected="assertion message")]
    fn test_assert_eq_fail_message() {
        unsafe { assert_eq_unchecked!(NoCopy(0), NoCopy(1), "assertion message") }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected="assertion message")]
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
    #[should_panic(expected="assertion failed: `(left != right)`")]
    fn test_assert_ne_fail_no_message() {
        unsafe { assert_ne_unchecked!(NoCopy(0), NoCopy(0)) }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected="assertion message")]
    fn test_assert_ne_fail_message() {
        unsafe { assert_ne_unchecked!(NoCopy(0), NoCopy(0), "assertion message") }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected="assertion message")]
    fn test_assert_ne_fail_message_format() {
        unsafe { assert_ne_unchecked!(NoCopy(0), NoCopy(0), "assertion {}", "message") }
    }

    #[test]
    fn test_unreachable_unreachable() {
        match Some(0) {
            Some(_) => {}
            // SAFETY: this is clearly unreachable
            None => unsafe { unreachable_unchecked!() }
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected="internal error: entered unreachable code")]
    fn test_unreachable_no_message() {
        unsafe { unreachable_unchecked!()}
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected="assertion message")]
    fn test_unreachable_message() {
        unsafe { unreachable_unchecked!("assertion message") }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected="assertion message")]
    fn test_unreachable_message_format() {
        unsafe { unreachable_unchecked!("assertion {}", "message") }
    }
}