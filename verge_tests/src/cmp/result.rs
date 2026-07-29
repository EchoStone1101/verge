//! Tests for `Result<T, E>` comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_result_comparison_methods_are_callable() {
    proof {
        broadcast use group_result_ordering;
    }

    let err2: Result<u32, u32> = Err(2u32);
    let err4: Result<u32, u32> = Err(4u32);
    let ok3: Result<u32, u32> = Ok(3u32);
    let ok5: Result<u32, u32> = Ok(5u32);

    test!(ok3 == ok3);

    test!(err2 < err4);
    test!(ok3 < ok5);

    test!(err2.partial_cmp(&err4) == Some(Ordering::Less));
    test!(ok3.partial_cmp(&ok5) == Some(Ordering::Less));

    test!(err2.cmp(&err4) == Ordering::Less);
    test!(ok3.cmp(&ok5) == Ordering::Less);

    test!(err2.max(err4) == err4);
    test!(err2.min(err4) == err2);
    test!(err4.clamp(err2, Err(5u32)) == err4);
    test!(ok3.max(ok5) == ok5);
    test!(ok3.min(ok5) == ok3);
    test!(Ok(4u32).clamp(ok3, ok5) == Ok(4u32));

    test!(ok3 < err4);
    test!(ok3 <= err4);
    test!(err4 > ok3);
    test!(err4 >= ok3);
    test!(!(err4 < ok3));
    test!(!(ok3 > err4));
    test!(ok3.partial_cmp(&err4) == Some(Ordering::Less));
    test!(err4.partial_cmp(&ok3) == Some(Ordering::Greater));
    test!(ok3.cmp(&err4) == Ordering::Less);
    test!(err4.cmp(&ok3) == Ordering::Greater);
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::result::comparison_methods_are_callable",
        test_result_comparison_methods_are_callable,
    );
    count
}
