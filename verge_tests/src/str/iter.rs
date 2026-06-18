//! Tests for string iterator APIs.

use vstd::prelude::*;
use vstd::assert_by_contradiction;
use vstd::std_specs::iter::*;
use verge::prelude::*;
use verge::str::*;

verus! {

fn test_char_indices() {
    broadcast use verge::str::group_str_view;
    proof { reveal_strlit("ab"); }

    let s = "ab";
    for (i, c) in iter: s.char_indices_iter()
        invariant
            iter.seq() == seq![(0usize, 'a'), (1usize, 'b')],
    {
        assert(c.is_ascii());
    }
    for (i, c) in iter: s.char_indices_iter().rev()
        invariant
            iter.seq() == seq![(1usize, 'b'), (0usize, 'a')],
    {
        assert(c.is_ascii());
    }
}

// fn test_split_once() {
//     broadcast use verge::str::group_str_view;
//     proof {
//         reveal_strlit("aa,b,c");
//         reveal_strlit(",");
//         reveal_strlit(".");
//         reveal_strlit("aa");
//         reveal_strlit("b,c");
//     }

//     let s = "aa,b,c";
//     let result = str_split_once(s, ",");
//     assert(2 + ","@.len() as int == 3);
//     assert(s@.subrange(2, 3) =~= ","@) by {
//         assert(s@[2] == ',');
//         assert(","@[0] == ',');
//     }
//     assert(result.is_some());

//     match result {
//         Some((head, tail)) => {
//             assert(s@ =~= head@ + ","@ + tail@);
//             assert(head@ =~= "aa"@) by {
//                 assert_by_contradiction!(head@.len() <= 2, {
//                     assert(head@.subrange(2, 3) =~= s@.subrange(2, 3));
//                 });
//                 assert_by_contradiction!(head@.len() > 1, {
//                     let i = head@.len() as int;
//                     assert(s@[i] != ',') by { assert(0 <= i <= 1); };
//                 });
//                 assert(head@.len() == 2);
//                 assert(s@.subrange(0, 2) =~= head@.subrange(0, 2));
//             }
//             assert(tail@ =~= "b,c"@) by {
//                 assert(s@.subrange(3, 6) =~= "b,c"@);
//             }
//         }
//         None => { assert(false); }
//     }

//     let none = str_split_once(s, ".");
//     assert(forall |i: int| 0 <= i < s@.len() ==> #[trigger] s@[i] != '.');

//     proof {
//         assert_by_contradiction!(none.is_none(), {
//             assert(none.is_some());
//             match none {
//                 Some((h, t)) => {
//                     let i = h@.len() as int;
//                     assert(s@ =~= h@ + "."@ + t@);
//                     assert(s@[i] == '.');
//                 }
//                 None => { assert(false) }
//             }
//         });
//     }

//     assert(none.is_none());
// }

// fn test_splitn() {
//     broadcast use verge::str::group_str_view;
//     proof {
//         reveal_strlit("a,b,c");
//         reveal_strlit(",");
//         reveal_strlit("a");
//         reveal_strlit("b,c");
//     }

//     assert("a,b,c"@.len() == 5);
//     assert(","@.len() == 1);
//     assert(1 + ","@.len() == 2);
//     assert("a,b,c"@.subrange(1, 2) =~= ","@) by {
//         assert("a,b,c"@[1] == ',');
//         assert(","@[0] == ',');
//     }

//     let mut it = str_splitn("a,b,c", 2usize, ",");
//     let ghost seq = it.seq();

//     proof {
//         assert_by_contradiction!(seq.len() == 2, {   
//             assert(seq.last()@ =~= "a,b,c"@);
//             assert(seq.last()@.subrange(1, 2) =~= ","@);
//             assert(!(seq.last()@.subrange(1, 2) =~= ","@)) by { assert(seq.len() < 2); }
//         });

//         assert(seq.drop_first().fold_left(
//             seq.first()@, |sum: Seq<char>, ss: &str| sum + ","@ + ss@
//         ) =~= seq.first()@ + ","@ + seq[1]@) by {
//             reveal_with_fuel(Seq::<_>::fold_left, 3);
//         }
//         assert("a,b,c"@ =~= seq[0]@ + ","@ + seq[1]@);

//         assert(seq[0]@ =~= "a"@) by {
//             assert_by_contradiction!(seq[0]@.len() <= 1, {
//                 assert((seq[0]@ + ","@).subrange(1, 2) =~= "a,b,c"@.subrange(1, 2));
//             });
//             assert_by_contradiction!(seq[0]@.len() > 0, {
//                 assert((seq[0]@ + ","@)[0] == ',');
//                 assert("a,b,c"@[0] == 'a');
//             });
//             assert(seq[0]@.len() == 1);
//             assert(seq[0]@[0] == "a,b,c"@[0]);
//             assert(seq[0]@[0] == 'a');
//         }

//         assert(seq[1]@ =~= "b,c"@) by {
//             assert("a,b,c"@.subrange(2, 5) =~= "b,c"@);
//         }
//     }

//     match it.next() {
//         Some(part) => {
//             assert(part == seq[0]);
//             assert(part@ =~= "a"@);
//             assert(it.idx() == 1);
//         }
//         None => { assert(false); }
//     }
//     match it.next() {
//         Some(part) => {
//             assert(part == seq[1]);
//             assert(part@ =~= "b,c"@);
//             assert(it.idx() == 2);
//         }
//         None => { assert(false); }
//     }
//     match it.next() {
//         Some(_) => { assert(false); }
//         None => {
//             assert(it.idx() == seq.len());
//             assert(it.seq() == seq);
//         }
//     }
// }

} // verus!
