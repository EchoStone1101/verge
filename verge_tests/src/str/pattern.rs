//! Executable downstream-style tests for public string pattern APIs.

use vstd::prelude::*;
use vstd::assert_by_contradiction;
use vstd::assert_seqs_equal;
use vstd::std_specs::cmp::PartialEqSpec;
use vstd::utf8::{decode_utf8, is_char_boundary};
use verge::cmp::lexico_eq;
use verge::prelude::*;
use verge::seq::SeqAdditionalSpec;
use verge::str::*;

verus! {

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, ch; ret)]
proof fn test_link_str_find_char(s: Seq<char>, ch: char, ret: Option<usize>)
    requires
        #[trigger] str_find_post(s, ch, ret),
    ensures
        ret is None || ret is Some,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, pat@; ret)]
proof fn test_link_str_find_string<'b>(s: Seq<char>, pat: &'b str, ret: Option<usize>)
    requires
        #[trigger] str_find_post(s, pat, ret),
    ensures
        ret is None || ret is Some,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, ch; ret)]
proof fn test_link_str_rfind_char(s: Seq<char>, ch: char, ret: Option<usize>)
    requires
        #[trigger] str_rfind_post(s, ch, ret),
    ensures
        ret is None || ret is Some,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, pat@; ret)]
proof fn test_link_str_rfind_string<'b>(s: Seq<char>, pat: &'b str, ret: Option<usize>)
    requires
        #[trigger] str_rfind_post(s, pat, ret),
    ensures
        ret is None || ret is Some,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, ch; (ret is Some, if ret is Some { ((ret->0).0@, (ret->0).1@) } else { (Seq::<char>::empty(), Seq::<char>::empty()) }))]
proof fn test_link_str_split_once_char<'a>(s: Seq<char>, ch: char, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_split_once_post(s, ch, ret),
    ensures
        ret is None || ret is Some,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, pat@; (ret is Some, if ret is Some { ((ret->0).0@, (ret->0).1@) } else { (Seq::<char>::empty(), Seq::<char>::empty()) }))]
proof fn test_link_str_split_once_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_split_once_post(s, pat, ret),
    ensures
        ret is None || ret is Some,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, ch; (ret is Some, if ret is Some { ((ret->0).0@, (ret->0).1@) } else { (Seq::<char>::empty(), Seq::<char>::empty()) }))]
proof fn test_link_str_rsplit_once_char<'a>(s: Seq<char>, ch: char, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_rsplit_once_post(s, ch, ret),
    ensures
        ret is None || ret is Some,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, pat@; (ret is Some, if ret is Some { ((ret->0).0@, (ret->0).1@) } else { (Seq::<char>::empty(), Seq::<char>::empty()) }))]
proof fn test_link_str_rsplit_once_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_rsplit_once_post(s, pat, ret),
    ensures
        ret is None || ret is Some,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, ch; ret)]
proof fn test_link_str_trim_matches_char(s: Seq<char>, ch: char, ret: Seq<char>)
    requires
        #[trigger] str_trim_matches_post(s, ch, ret),
    ensures
        ret == ret,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, ch; ret)]
proof fn test_link_str_trim_start_matches_char(s: Seq<char>, ch: char, ret: Seq<char>)
    requires
        #[trigger] str_trim_start_matches_post(s, ch, ret),
    ensures
        ret == ret,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, pat@; ret)]
proof fn test_link_str_trim_start_matches_string<'b>(s: Seq<char>, pat: &'b str, ret: Seq<char>)
    requires
        #[trigger] str_trim_start_matches_post(s, pat, ret),
    ensures
        ret == ret,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, ch; ret)]
proof fn test_link_str_trim_end_matches_char(s: Seq<char>, ch: char, ret: Seq<char>)
    requires
        #[trigger] str_trim_end_matches_post(s, ch, ret),
    ensures
        ret == ret,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, pat@; ret)]
proof fn test_link_str_trim_end_matches_string<'b>(s: Seq<char>, pat: &'b str, ret: Seq<char>)
    requires
        #[trigger] str_trim_end_matches_post(s, pat, ret),
    ensures
        ret == ret,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, pat@; (ret is Some, if ret is Some { ret->0@ } else { Seq::<char>::empty() }))]
proof fn test_link_str_strip_prefix_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_prefix_post(s, pat, ret),
    ensures
        ret is None || ret is Some,
{
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s, pat@; (ret is Some, if ret is Some { ret->0@ } else { Seq::<char>::empty() }))]
proof fn test_link_str_strip_suffix_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_suffix_post(s, pat, ret),
    ensures
        ret is None || ret is Some,
{
}

proof fn prove_str_eq(actual: &str, expected: &str)
    requires
        actual@ =~= expected@,
    ensures
        <str as PartialEqSpec>::eq_spec(actual, expected),
{
    broadcast use group_str_axioms;
    assert_seqs_equal!(actual@.as_bytes() == expected@.as_bytes());
    verge::cmp::lemma_lexico_eq_reflexive::<u8>(actual@.as_bytes());
    assert(verge::cmp::lexico_eq::<u8>(actual@.as_bytes(), expected@.as_bytes()));
    lemma_str_eq_spec(actual, expected);
    reveal_with_fuel(verge::cmp::lexico_eq, 16);
    assert(<str as PartialEqSpec>::eq_spec(actual, expected));
}

proof fn prove_find_char_eq(s: &str, ch: char, ret: Option<usize>, expected: usize)
    requires
        s@.is_ascii(),
        str_find_post(s@, ch, ret),
        str_find_post(s@, ch, Some(expected)),
    ensures
        ret == Some(expected),
{
    test_link_str_find_char(s@, ch, ret);
    test_link_str_find_char(s@, ch, Some(expected));
    test_link_str_find_char_injective(s@, ch, ret, s@, ch, Some(expected));
}

proof fn prove_find_string_eq(s: &str, pat: &str, ret: Option<usize>, expected: usize)
    requires
        s@.is_ascii(),
        pat@.is_ascii(),
        str_find_post(s@, pat, ret),
        str_find_post(s@, pat, Some(expected)),
    ensures
        ret == Some(expected),
{
    test_link_str_find_string(s@, pat, ret);
    test_link_str_find_string(s@, pat, Some(expected));
    test_link_str_find_string_injective(s@, pat, ret, s@, pat, Some(expected));
}

proof fn prove_rfind_char_eq(s: &str, ch: char, ret: Option<usize>, expected: usize)
    requires
        s@.is_ascii(),
        str_rfind_post(s@, ch, ret),
        str_rfind_post(s@, ch, Some(expected)),
    ensures
        ret == Some(expected),
{
    test_link_str_rfind_char(s@, ch, ret);
    test_link_str_rfind_char(s@, ch, Some(expected));
    test_link_str_rfind_char_injective(s@, ch, ret, s@, ch, Some(expected));
}

proof fn prove_rfind_string_eq(s: &str, pat: &str, ret: Option<usize>, expected: usize)
    requires
        s@.is_ascii(),
        pat@.is_ascii(),
        str_rfind_post(s@, pat, ret),
        str_rfind_post(s@, pat, Some(expected)),
    ensures
        ret == Some(expected),
{
    test_link_str_rfind_string(s@, pat, ret);
    test_link_str_rfind_string(s@, pat, Some(expected));
    test_link_str_rfind_string_injective(s@, pat, ret, s@, pat, Some(expected));
}

proof fn prove_split_once_char_eq(
    s: &str,
    ch: char,
    ret: Option<(&str, &str)>,
    expected_head: &str,
    expected_tail: &str,
)
    requires
        str_split_once_post(s@, ch, ret),
        str_split_once_post(s@, ch, Some((expected_head, expected_tail))),
    ensures
        ret is Some,
        (ret->0).0@ =~= expected_head@,
        (ret->0).1@ =~= expected_tail@,
{
    test_link_str_split_once_char(s@, ch, ret);
    test_link_str_split_once_char(s@, ch, Some((expected_head, expected_tail)));
    test_link_str_split_once_char_injective(
        s@,
        ch,
        ret,
        s@,
        ch,
        Some((expected_head, expected_tail)),
    );
}

proof fn prove_split_once_string_eq(
    s: &str,
    pat: &str,
    ret: Option<(&str, &str)>,
    expected_head: &str,
    expected_tail: &str,
)
    requires
        str_split_once_post(s@, pat, ret),
        str_split_once_post(s@, pat, Some((expected_head, expected_tail))),
    ensures
        ret is Some,
        (ret->0).0@ =~= expected_head@,
        (ret->0).1@ =~= expected_tail@,
{
    test_link_str_split_once_string(s@, pat, ret);
    test_link_str_split_once_string(s@, pat, Some((expected_head, expected_tail)));
    test_link_str_split_once_string_injective(
        s@,
        pat,
        ret,
        s@,
        pat,
        Some((expected_head, expected_tail)),
    );
}

proof fn prove_rsplit_once_char_eq(
    s: &str,
    ch: char,
    ret: Option<(&str, &str)>,
    expected_head: &str,
    expected_tail: &str,
)
    requires
        str_rsplit_once_post(s@, ch, ret),
        str_rsplit_once_post(s@, ch, Some((expected_head, expected_tail))),
    ensures
        ret is Some,
        (ret->0).0@ =~= expected_head@,
        (ret->0).1@ =~= expected_tail@,
{
    test_link_str_rsplit_once_char(s@, ch, ret);
    test_link_str_rsplit_once_char(s@, ch, Some((expected_head, expected_tail)));
    test_link_str_rsplit_once_char_injective(
        s@,
        ch,
        ret,
        s@,
        ch,
        Some((expected_head, expected_tail)),
    );
}

proof fn prove_rsplit_once_string_eq(
    s: &str,
    pat: &str,
    ret: Option<(&str, &str)>,
    expected_head: &str,
    expected_tail: &str,
)
    requires
        str_rsplit_once_post(s@, pat, ret),
        str_rsplit_once_post(s@, pat, Some((expected_head, expected_tail))),
    ensures
        ret is Some,
        (ret->0).0@ =~= expected_head@,
        (ret->0).1@ =~= expected_tail@,
{
    test_link_str_rsplit_once_string(s@, pat, ret);
    test_link_str_rsplit_once_string(s@, pat, Some((expected_head, expected_tail)));
    test_link_str_rsplit_once_string_injective(
        s@,
        pat,
        ret,
        s@,
        pat,
        Some((expected_head, expected_tail)),
    );
}

proof fn prove_split_once_string_none(s: &str, pat: &str, ret: Option<(&str, &str)>)
    requires
        str_split_once_post(s@, pat, ret),
        str_split_once_post(s@, pat, None),
    ensures
        ret is None,
{
    test_link_str_split_once_string(s@, pat, ret);
    test_link_str_split_once_string(s@, pat, None);
    test_link_str_split_once_string_injective(s@, pat, ret, s@, pat, None);
}

proof fn prove_rsplit_once_string_none(s: &str, pat: &str, ret: Option<(&str, &str)>)
    requires
        str_rsplit_once_post(s@, pat, ret),
        str_rsplit_once_post(s@, pat, None),
    ensures
        ret is None,
{
    test_link_str_rsplit_once_string(s@, pat, ret);
    test_link_str_rsplit_once_string(s@, pat, None);
    test_link_str_rsplit_once_string_injective(s@, pat, ret, s@, pat, None);
}

proof fn prove_strip_prefix_string_eq(
    s: &str,
    pat: &str,
    ret: Option<&str>,
    expected: &str,
)
    requires
        str_strip_prefix_post(s@, pat, ret),
        str_strip_prefix_post(s@, pat, Some(expected)),
    ensures
        ret is Some,
        ret->0@ =~= expected@,
{
    test_link_str_strip_prefix_string(s@, pat, ret);
    test_link_str_strip_prefix_string(s@, pat, Some(expected));
    test_link_str_strip_prefix_string_injective(s@, pat, ret, s@, pat, Some(expected));
}

proof fn prove_strip_suffix_string_eq(
    s: &str,
    pat: &str,
    ret: Option<&str>,
    expected: &str,
)
    requires
        str_strip_suffix_post(s@, pat, ret),
        str_strip_suffix_post(s@, pat, Some(expected)),
    ensures
        ret is Some,
        ret->0@ =~= expected@,
{
    test_link_str_strip_suffix_string(s@, pat, ret);
    test_link_str_strip_suffix_string(s@, pat, Some(expected));
    test_link_str_strip_suffix_string_injective(s@, pat, ret, s@, pat, Some(expected));
}

proof fn prove_trim_matches_char_eq(s: &str, ch: char, actual: &str, expected: &str)
    requires
        str_trim_matches_post(s@, ch, actual@),
        str_trim_matches_post(s@, ch, expected@),
    ensures
        actual@ =~= expected@,
{
    test_link_str_trim_matches_char(s@, ch, actual@);
    test_link_str_trim_matches_char(s@, ch, expected@);
    test_link_str_trim_matches_char_injective(s@, ch, actual@, s@, ch, expected@);
}

proof fn prove_trim_start_matches_char_eq(s: &str, ch: char, actual: &str, expected: &str)
    requires
        str_trim_start_matches_post(s@, ch, actual@),
        str_trim_start_matches_post(s@, ch, expected@),
    ensures
        actual@ =~= expected@,
{
    test_link_str_trim_start_matches_char(s@, ch, actual@);
    test_link_str_trim_start_matches_char(s@, ch, expected@);
    test_link_str_trim_start_matches_char_injective(s@, ch, actual@, s@, ch, expected@);
}

proof fn prove_trim_start_matches_string_eq(s: &str, pat: &str, actual: &str, expected: &str)
    requires
        str_trim_start_matches_post(s@, pat, actual@),
        str_trim_start_matches_post(s@, pat, expected@),
    ensures
        actual@ =~= expected@,
{
    test_link_str_trim_start_matches_string(s@, pat, actual@);
    test_link_str_trim_start_matches_string(s@, pat, expected@);
    test_link_str_trim_start_matches_string_injective(s@, pat, actual@, s@, pat, expected@);
}

proof fn prove_trim_end_matches_char_eq(s: &str, ch: char, actual: &str, expected: &str)
    requires
        str_trim_end_matches_post(s@, ch, actual@),
        str_trim_end_matches_post(s@, ch, expected@),
    ensures
        actual@ =~= expected@,
{
    test_link_str_trim_end_matches_char(s@, ch, actual@);
    test_link_str_trim_end_matches_char(s@, ch, expected@);
    test_link_str_trim_end_matches_char_injective(s@, ch, actual@, s@, ch, expected@);
}

proof fn prove_trim_end_matches_string_eq(s: &str, pat: &str, actual: &str, expected: &str)
    requires
        str_trim_end_matches_post(s@, pat, actual@),
        str_trim_end_matches_post(s@, pat, expected@),
    ensures
        actual@ =~= expected@,
{
    test_link_str_trim_end_matches_string(s@, pat, actual@);
    test_link_str_trim_end_matches_string(s@, pat, expected@);
    test_link_str_trim_end_matches_string_injective(s@, pat, actual@, s@, pat, expected@);
}

/// Migrated from Rust core/std `test_contains`, `test_contains_char`, `test_starts_with`, `test_ends_with`,
/// `starts_with_in_unicode`, `starts_short_long`, and `contains_weird_cases`.
/// Port status: partial; exact for the migrated executable claims here. Full upstream semantics were attempted;
/// deferred rows are recorded below with `ISSUE TODO(Verge):` notes.
fn test_contains_starts_ends_exact_representatives() {
    broadcast use group_str_contains;
    broadcast use group_str_starts_with;
    broadcast use group_str_ends_with;

    proof {
        reveal_strlit("Mary had a little lamb");
        reveal_strlit("little");
        reveal_strlit("z");
        reveal_strlit("abcde");
        reveal_strlit("abcd");
        reveal_strlit("bcd");
        reveal_strlit("bcde");
        reveal_strlit("def");
        reveal_strlit("abc");
        reveal_strlit("a");
        reveal_strlit("c");
        reveal_strlit("");
        reveal_strlit("##");
        reveal_strlit("####");
        reveal_strlit("* \t");
    }

    let text = "Mary had a little lamb";

    test!(text.contains('M'));
    test!(text.contains("little"), {
        proof {
        assert(text@.subrange(11, 17) =~= "little"@);
        }
    });
    test!(!text.contains('z'));
    test!(text.starts_with('M'));
    test!(!text.starts_with('a'));
    test!(text.ends_with('b'));
    test!(!text.ends_with('z'));

    test!("".starts_with(""));
    test!("abc".starts_with(""));
    test!("abc".starts_with("a"));
    test!(!"a".starts_with("abc"));
    test!(!"".starts_with("abc"));

    test!("".ends_with(""));
    test!("abc".ends_with(""));
    test!("abc".ends_with("c"));
    test!(!"a".ends_with("abc"));
    test!(!"".ends_with("abc"));

    test!(!"".starts_with("##"));
    test!(!"##".starts_with("####"));
    test!("####".starts_with("##"));

    // ISSUE TODO(Verge): Upstream `test_contains` rows beyond the active representative checks
    // were attempted but are not active. Even fixed ASCII rows such as `"abcde".contains("bcd")`,
    // `"abc".contains('b')`, and the weird `"* \t".contains(' ')` case currently need additional
    // downstream witness lemmas for `contains` rather than bare boolean assertions. Unicode rows
    // (`ประเทศไทย中华Việt Nam` contains `ประเ`, `ะเ`, `中华`, and not `ไท华`) add heavy UTF-8
    // boundary reasoning. Upstream `starts_with`/`ends_with` Unicode rows (`ödd`/`ddö`,
    // `├── Cargo.toml`, and `##ä` variants) were also deferred for the same multibyte-literal cost.
}

/// Migrated from Rust core/std `test_find`, `test_rfind`, and `test_find_str`.
/// Port status: partial; exact for these byte-offset assertions. Full upstream semantics were attempted;
/// deferred rows are recorded below with `ISSUE TODO(Verge):` notes.
fn test_find_and_rfind_exact_offsets() {
    broadcast use group_str_axioms;
    broadcast use group_str_find;
    broadcast use group_str_rfind;

    proof {
        reveal_strlit("hello");
        reveal_strlit("bananas");
        reveal_strlit("banana");
        reveal_strlit("apple pie");
        reveal_strlit("abcabc");
        reveal_strlit("cabc");
        reveal_strlit("ca");
        reveal_strlit("ab");
        reveal_strlit("na");
        reveal_strlit("");
    }

    let hello = "hello";
    let find_l = hello.find('l');
    test!(find_l == Some(2usize), {
        proof {
        test_link_str_find_char_surjective(hello@, 'l', Some(2usize));
        prove_find_char_eq(hello, 'l', find_l, 2usize);
        }
    });
    let find_hello_x = hello.find('x');
    test!(find_hello_x.is_none());

    let rfind_l = hello.rfind('l');
    test!(rfind_l == Some(3usize), {
        proof {
        test_link_str_rfind_char_surjective(hello@, 'l', Some(3usize));
        prove_rfind_char_eq(hello, 'l', rfind_l, 3usize);
        }
    });
    let rfind_hello_x = hello.rfind('x');
    test!(rfind_hello_x.is_none());

    let text = "bananas";
    let empty = "";

    let find_a = text.find('a');
    test!(find_a == Some(1usize), {
        proof {
        test_link_str_find_char_surjective(text@, 'a', Some(1usize));
        prove_find_char_eq(text, 'a', find_a, 1usize);
        }
    });
    let find_na = text.find("na");
    test!(find_na == Some(2usize), {
        proof {
        assert(text@.subrange(2, 4) =~= "na"@);
        test_link_str_find_string_surjective(text@, "na", Some(2usize));
        prove_find_string_eq(text, "na", find_na, 2usize);
        }
    });
    test!(text.find('z').is_none());

    let rfind_a = text.rfind('a');
    test!(rfind_a == Some(5usize), {
        proof {
        test_link_str_rfind_char_surjective(text@, 'a', Some(5usize));
        prove_rfind_char_eq(text, 'a', rfind_a, 5usize);
        }
    });
    let rfind_na = text.rfind("na");
    test!(rfind_na == Some(4usize), {
        proof {
        assert(text@.subrange(4, 6) =~= "na"@);
        test_link_str_rfind_string_surjective(text@, "na", Some(4usize));
        prove_rfind_string_eq(text, "na", rfind_na, 4usize);
        }
    });
    test!(text.rfind('z').is_none());

    let empty_find = text.find(empty);
    test!(empty_find == Some(0usize), {
        proof {
        test_link_str_find_string_surjective(text@, empty, Some(0usize));
        prove_find_string_eq(text, empty, empty_find, 0usize);
        }
    });
    let rfind_empty = text.rfind(empty);
    test!(rfind_empty == Some(7usize), {
        proof {
        test_link_str_rfind_string_surjective(text@, empty, Some(7usize));
        prove_rfind_string_eq(text, empty, rfind_empty, 7usize);
        }
    });

    let absent_phrase = "banana".find("apple pie");
    test!(absent_phrase.is_none());

    let repeated = "abcabc";
    let repeated_first = repeated.find("ab");
    test!(repeated_first == Some(0usize), {
        proof {
        test_link_str_find_string_surjective(repeated@, "ab", Some(0usize));
        prove_find_string_eq(repeated, "ab", repeated_first, 0usize);
        }
    });
    let repeated_second = "cabc".find("ab");
    test!(repeated_second == Some(1usize), {
        proof {
        test_link_str_find_string_surjective("cabc"@, "ab", Some(1usize));
        prove_find_string_eq("cabc", "ab", repeated_second, 1usize);
        }
    });
    test!("ca".find("ab").is_none());

    // ISSUE TODO(Verge): Upstream `test_find` / `test_rfind` closure-pattern assertions
    // (`find(|c| c == 'o')`, `find(|c| c == 'x')`, and matching `rfind` rows) were attempted
    // but are not active because proving `FnMut(char) -> bool` pattern determinism/totality for
    // inline closures in downstream executable tests is not currently lightweight.
    // ISSUE TODO(Verge): Upstream `test_find` / `test_rfind` Unicode byte-offset rows for `华`
    // and upstream `test_find_str` rows over `ประเทศไทย中华Việt Nam` were attempted but are not
    // active because the exact equality helpers require ASCII (`s@.is_ascii()` / `pat@.is_ascii()`)
    // and proving multibyte byte offsets directly is too heavy here.
    // ISSUE TODO(Verge): Upstream `test_find_str` substring-loop property over
    // `Việt Namacbaabcaabaaba` was attempted but is not active because it requires quantified
    // dynamic slicing, allocation/`String` mutation, and relational `find`/`rfind` inequalities
    // rather than fixed literal outputs.
}

/// Migrated from Rust core/std `test_split_once` and `test_rsplit_once`.
/// Port status: partial; exact for the active string and char-pattern rows, with deferred upstream `None` rows marked ISSUE below.
fn test_split_once_and_rsplit_once_exact_views() {
    broadcast use group_str_axioms;
    broadcast use group_str_split_once;
    broadcast use group_str_rsplit_once;

    proof {
        reveal_strlit("-");
        reveal_strlit("->");
        reveal_strlit("a->");
        reveal_strlit("->b");
        reveal_strlit("b");
        reveal_strlit("a->b");
        reveal_strlit("a->b->c");
        reveal_strlit("b->c");
        reveal_strlit("a->b");
        reveal_strlit("---");
        reveal_strlit("--");
        reveal_strlit("a=b=c");
        reveal_strlit("a");
        reveal_strlit("b=c");
        reveal_strlit("a=b");
        reveal_strlit("c");
        reveal_strlit("::");
        reveal_strlit(":");
        reveal_strlit("");
    }

    test!("".split_once("->").is_none());
    // ISSUE TODO(Verge): Upstream `split_once` / `rsplit_once` absent-pattern rows for `"-"`
    // and the empty `rsplit_once("->")` row were attempted but are not active; proving the exact
    // `None` return requires a lightweight downstream contradiction lemma for string patterns.

    let arrow = "->";
    let arrow_split = arrow.split_once("->");
    match arrow_split {
        Some((head, tail)) => {
            test!(head == "", {
                proof {
                test_link_str_split_once_string(arrow@, "->", arrow_split);
                test_link_str_split_once_string_surjective(arrow@, "->", Some(("", "")));
                prove_split_once_string_eq(arrow, "->", arrow_split, "", "");
                prove_str_eq(head, "");
                }
            });
            test!(tail == "", {
                proof {
                test_link_str_split_once_string(arrow@, "->", arrow_split);
                test_link_str_split_once_string_surjective(arrow@, "->", Some(("", "")));
                prove_split_once_string_eq(arrow, "->", arrow_split, "", "");
                prove_str_eq(tail, "");
                }
            });
        }
        None => {},
    }

    let arrow_rsplit = arrow.rsplit_once("->");
    match arrow_rsplit {
        Some((head, tail)) => {
            test!(head == "", {
                proof {
                test_link_str_rsplit_once_string(arrow@, "->", arrow_rsplit);
                test_link_str_rsplit_once_string_surjective(arrow@, "->", Some(("", "")));
                prove_rsplit_once_string_eq(arrow, "->", arrow_rsplit, "", "");
                prove_str_eq(head, "");
                }
            });
            test!(tail == "", {
                proof {
                test_link_str_rsplit_once_string(arrow@, "->", arrow_rsplit);
                test_link_str_rsplit_once_string_surjective(arrow@, "->", Some(("", "")));
                prove_rsplit_once_string_eq(arrow, "->", arrow_rsplit, "", "");
                prove_str_eq(tail, "");
                }
            });
        }
        None => {},
    }

    let trailing = "a->";
    let trailing_split = trailing.split_once("->");
    match trailing_split {
        Some((head, tail)) => {
            test!(head == "a", {
                proof {
                test_link_str_split_once_string(trailing@, "->", trailing_split);
                test_link_str_split_once_string_surjective(trailing@, "->", Some(("a", "")));
                prove_split_once_string_eq(trailing, "->", trailing_split, "a", "");
                prove_str_eq(head, "a");
                }
            });
            test!(tail == "", {
                proof {
                test_link_str_split_once_string(trailing@, "->", trailing_split);
                test_link_str_split_once_string_surjective(trailing@, "->", Some(("a", "")));
                prove_split_once_string_eq(trailing, "->", trailing_split, "a", "");
                prove_str_eq(tail, "");
                }
            });
        }
        None => {},
    }

    let leading = "->b";
    let leading_split = leading.split_once("->");
    match leading_split {
        Some((head, tail)) => {
            test!(head == "", {
                proof {
                test_link_str_split_once_string(leading@, "->", leading_split);
                test_link_str_split_once_string_surjective(leading@, "->", Some(("", "b")));
                prove_split_once_string_eq(leading, "->", leading_split, "", "b");
                prove_str_eq(head, "");
                }
            });
            test!(tail == "b", {
                proof {
                test_link_str_split_once_string(leading@, "->", leading_split);
                test_link_str_split_once_string_surjective(leading@, "->", Some(("", "b")));
                prove_split_once_string_eq(leading, "->", leading_split, "", "b");
                prove_str_eq(tail, "b");
                }
            });
        }
        None => {},
    }

    let pair = "a->b";
    let pair_split = pair.split_once("->");
    match pair_split {
        Some((head, tail)) => {
            test!(head == "a", {
                proof {
                test_link_str_split_once_string(pair@, "->", pair_split);
                test_link_str_split_once_string_surjective(pair@, "->", Some(("a", "b")));
                prove_split_once_string_eq(pair, "->", pair_split, "a", "b");
                prove_str_eq(head, "a");
                }
            });
            test!(tail == "b", {
                proof {
                test_link_str_split_once_string(pair@, "->", pair_split);
                test_link_str_split_once_string_surjective(pair@, "->", Some(("a", "b")));
                prove_split_once_string_eq(pair, "->", pair_split, "a", "b");
                prove_str_eq(tail, "b");
                }
            });
        }
        None => {},
    }

    let pair_rsplit = pair.rsplit_once("->");
    match pair_rsplit {
        Some((head, tail)) => {
            test!(head == "a", {
                proof {
                test_link_str_rsplit_once_string(pair@, "->", pair_rsplit);
                test_link_str_rsplit_once_string_surjective(pair@, "->", Some(("a", "b")));
                prove_rsplit_once_string_eq(pair, "->", pair_rsplit, "a", "b");
                prove_str_eq(head, "a");
                }
            });
            test!(tail == "b", {
                proof {
                test_link_str_rsplit_once_string(pair@, "->", pair_rsplit);
                test_link_str_rsplit_once_string_surjective(pair@, "->", Some(("a", "b")));
                prove_rsplit_once_string_eq(pair, "->", pair_rsplit, "a", "b");
                prove_str_eq(tail, "b");
                }
            });
        }
        None => {},
    }

    let chain = "a->b->c";
    let chain_split = chain.split_once("->");
    match chain_split {
        Some((head, tail)) => {
            test!(head == "a", {
                proof {
                test_link_str_split_once_string(chain@, "->", chain_split);
                test_link_str_split_once_string_surjective(chain@, "->", Some(("a", "b->c")));
                prove_split_once_string_eq(chain, "->", chain_split, "a", "b->c");
                prove_str_eq(head, "a");
                }
            });
            test!(tail == "b->c", {
                proof {
                test_link_str_split_once_string(chain@, "->", chain_split);
                test_link_str_split_once_string_surjective(chain@, "->", Some(("a", "b->c")));
                prove_split_once_string_eq(chain, "->", chain_split, "a", "b->c");
                prove_str_eq(tail, "b->c");
                }
            });
        }
        None => {},
    }

    let chain_rsplit = chain.rsplit_once("->");
    match chain_rsplit {
        Some((head, tail)) => {
            test!(head == "a->b", {
                proof {
                test_link_str_rsplit_once_string(chain@, "->", chain_rsplit);
                test_link_str_rsplit_once_string_surjective(chain@, "->", Some(("a->b", "c")));
                prove_rsplit_once_string_eq(chain, "->", chain_rsplit, "a->b", "c");
                prove_str_eq(head, "a->b");
                }
            });
            test!(tail == "c", {
                proof {
                test_link_str_rsplit_once_string(chain@, "->", chain_rsplit);
                test_link_str_rsplit_once_string_surjective(chain@, "->", Some(("a->b", "c")));
                prove_rsplit_once_string_eq(chain, "->", chain_rsplit, "a->b", "c");
                prove_str_eq(tail, "c");
                }
            });
        }
        None => {},
    }

    let overlap = "---";
    let overlap_split = overlap.split_once("--");
    match overlap_split {
        Some((head, tail)) => {
            test!(head == "", {
                proof {
                test_link_str_split_once_string(overlap@, "--", overlap_split);
                test_link_str_split_once_string_surjective(overlap@, "--", Some(("", "-")));
                prove_split_once_string_eq(overlap, "--", overlap_split, "", "-");
                prove_str_eq(head, "");
                }
            });
            test!(tail == "-", {
                proof {
                test_link_str_split_once_string(overlap@, "--", overlap_split);
                test_link_str_split_once_string_surjective(overlap@, "--", Some(("", "-")));
                prove_split_once_string_eq(overlap, "--", overlap_split, "", "-");
                prove_str_eq(tail, "-");
                }
            });
        }
        None => {},
    }

    let overlap_rsplit = overlap.rsplit_once("--");
    match overlap_rsplit {
        Some((head, tail)) => {
            test!(head == "-", {
                proof {
                test_link_str_rsplit_once_string(overlap@, "--", overlap_rsplit);
                test_link_str_rsplit_once_string_surjective(overlap@, "--", Some(("-", "")));
                prove_rsplit_once_string_eq(overlap, "--", overlap_rsplit, "-", "");
                prove_str_eq(head, "-");
                }
            });
            test!(tail == "", {
                proof {
                test_link_str_rsplit_once_string(overlap@, "--", overlap_rsplit);
                test_link_str_rsplit_once_string_surjective(overlap@, "--", Some(("-", "")));
                prove_rsplit_once_string_eq(overlap, "--", overlap_rsplit, "-", "");
                prove_str_eq(tail, "");
                }
            });
        }
        None => {},
    }

    let text = "a=b=c";

    let first = text.split_once('=');
    test!(first.is_some(), {
        proof {
        test_link_str_split_once_char_surjective(text@, '=', Some(("a", "b=c")));
        prove_split_once_char_eq(text, '=', first, "a", "b=c");
        }
    });
    match first {
        Some((head, tail)) => {
            test!(head == "a", {
                proof {
                test_link_str_split_once_char(text@, '=', first);
        test_link_str_split_once_char_surjective(text@, '=', Some(("a", "b=c")));
                prove_split_once_char_eq(text, '=', first, "a", "b=c");
                prove_str_eq(head, "a");
                }
            });
            test!(tail == "b=c", {
                proof {
                test_link_str_split_once_char(text@, '=', first);
        test_link_str_split_once_char_surjective(text@, '=', Some(("a", "b=c")));
                prove_split_once_char_eq(text, '=', first, "a", "b=c");
                prove_str_eq(tail, "b=c");
                }
            });
        }
        None => {},
    }

    let last = text.rsplit_once('=');
    test!(last.is_some(), {
        proof {
        test_link_str_rsplit_once_char_surjective(text@, '=', Some(("a=b", "c")));
        prove_rsplit_once_char_eq(text, '=', last, "a=b", "c");
        }
    });
    match last {
        Some((head, tail)) => {
            test!(head == "a=b", {
                proof {
                test_link_str_rsplit_once_char(text@, '=', last);
        test_link_str_rsplit_once_char_surjective(text@, '=', Some(("a=b", "c")));
                prove_rsplit_once_char_eq(text, '=', last, "a=b", "c");
                prove_str_eq(head, "a=b");
                }
            });
            test!(tail == "c", {
                proof {
                test_link_str_rsplit_once_char(text@, '=', last);
        test_link_str_rsplit_once_char_surjective(text@, '=', Some(("a=b", "c")));
                prove_rsplit_once_char_eq(text, '=', last, "a=b", "c");
                prove_str_eq(tail, "c");
                }
            });
        }
        None => {},
    }

    let edge = "::";
    let split_empty_head = edge.split_once(':');
    match split_empty_head {
        Some((head, tail)) => {
            test!(head == "", {
                proof {
                test_link_str_split_once_char(edge@, ':', split_empty_head);
                test_link_str_split_once_char_surjective(edge@, ':', Some(("", ":")));
                prove_split_once_char_eq(edge, ':', split_empty_head, "", ":");
                prove_str_eq(head, "");
                }
            });
            test!(tail == ":", {
                proof {
                test_link_str_split_once_char(edge@, ':', split_empty_head);
                test_link_str_split_once_char_surjective(edge@, ':', Some(("", ":")));
                prove_split_once_char_eq(edge, ':', split_empty_head, "", ":");
                prove_str_eq(tail, ":");
                }
            });
        }
        None => {},
    }
}

/// Migrated from Rust core/std `test_trim_start_matches`, `test_trim_end_matches`, and `test_trim_matches`.
/// Port status: partial; exact for the selected output strings. Full upstream semantics were attempted;
/// deferred rows are recorded below with `ISSUE TODO(Verge):` notes.
fn test_trim_matches_exact_outputs() {
    broadcast use group_str_axioms;
    broadcast use group_str_trim_start_matches;
    broadcast use group_str_trim_end_matches;
    broadcast use group_str_trim_matches;

    proof {
        reveal_strlit("111foo111");
        reveal_strlit("foo111");
        reveal_strlit("111foo");
        reveal_strlit("foo");
        reveal_strlit("ababcoreab");
        reveal_strlit("coreab");
        reveal_strlit("ababcore");
        reveal_strlit(" *** foo *** ");
        reveal_strlit("foo *** ");
        reveal_strlit(" *** foo");
        reveal_strlit(" ***  *** ");
        reveal_strlit("11foo1bar11");
        reveal_strlit("foo1bar11");
        reveal_strlit("11foo1bar");
        reveal_strlit("foo1bar");
        reveal_strlit("12foo1bar12");
        reveal_strlit("foo1bar12");
        reveal_strlit("12foo1bar");
        reveal_strlit("foo1bar");
    }

    // ISSUE TODO(Verge): Upstream char-slice rows for `trim_start_matches`,
    // including the empty-slice no-op row (`" *** foo *** ".trim_start_matches(&[])`),
    // `trim_end_matches`, and `trim_matches` with `&['*', ' ']` and `&['1', '2']`
    // were attempted but are not active. Direct `prove_str_eq` calls for rows such as
    // `" *** foo *** ".trim_start_matches(&['*', ' ']) == "foo *** "` fail because
    // the current downstream test helpers only provide injectivity wrappers for char and string
    // patterns, not char-slice pattern outputs. These attempts also triggered rlimit pressure.

    let numeric = "111foo111";

    let trim_start_char = numeric.trim_start_matches('1');
    test!(trim_start_char == "foo111", {
        proof {
        test_link_str_trim_start_matches_char_surjective(numeric@, '1', "foo111"@);
        prove_trim_start_matches_char_eq(numeric, '1', trim_start_char, "foo111");
        prove_str_eq(trim_start_char, "foo111");
        }
    });
    let trim_end_char = numeric.trim_end_matches('1');
    test!(trim_end_char == "111foo", {
        proof {
        test_link_str_trim_end_matches_char_surjective(numeric@, '1', "111foo"@);
        prove_trim_end_matches_char_eq(numeric, '1', trim_end_char, "111foo");
        prove_str_eq(trim_end_char, "111foo");
        }
    });
    let trim_char = numeric.trim_matches('1');
    test!(trim_char == "foo", {
        proof {
        test_link_str_trim_matches_char_surjective(numeric@, '1', "foo"@);
        prove_trim_matches_char_eq(numeric, '1', trim_char, "foo");
        prove_str_eq(trim_char, "foo");
        }
    });

    let repeated = "ababcoreab";

    let trim_start_string = repeated.trim_start_matches("ab");
    test!(trim_start_string == "coreab", {
        proof {
        test_link_str_trim_start_matches_string_surjective(repeated@, "ab", "coreab"@);
        prove_trim_start_matches_string_eq(repeated, "ab", trim_start_string, "coreab");
        prove_str_eq(trim_start_string, "coreab");
        }
    });
    let trim_end_string = repeated.trim_end_matches("ab");
    test!(trim_end_string == "ababcore", {
        proof {
        test_link_str_trim_end_matches_string_surjective(repeated@, "ab", "ababcore"@);
        prove_trim_end_matches_string_eq(repeated, "ab", trim_end_string, "ababcore");
        prove_str_eq(trim_end_string, "ababcore");
        }
    });

    // ISSUE TODO(Verge): Upstream `trim_*_matches(|c: char| c.is_numeric())` rows and
    // upstream `trim_ws` closure rows (`is_whitespace`) were attempted but are not active because
    // closure-pattern determinism/totality and the `is_numeric` / `is_whitespace` call specs are
    // not lightweight in these downstream executable tests.
}

/// Migrated from Rust core/std `strip_prefix` / `strip_suffix` behavior examples.
/// Port status: partial; exact for the selected `Some` views and `None` outcomes. Full upstream semantics
/// were attempted; deferred rows are recorded below with `ISSUE TODO(Verge):` notes.
fn test_strip_prefix_and_suffix_exact_outputs() {
    broadcast use group_str_axioms;
    broadcast use group_str_strip_prefix;
    broadcast use group_str_strip_suffix;

    proof {
        reveal_strlit("foobar");
        reveal_strlit("foo");
        reveal_strlit("bar");
        reveal_strlit("");
        reveal_strlit("z");
    }

    let text = "foobar";

    let prefix = text.strip_prefix("foo");
    match prefix {
        Some(rest) => {
            test!(rest == "bar", {
                proof {
                test_link_str_strip_prefix_string(text@, "foo", prefix);
                test_link_str_strip_prefix_string_surjective(text@, "foo", Some("bar"));
                prove_strip_prefix_string_eq(text, "foo", prefix, "bar");
                prove_str_eq(rest, "bar");
                }
            });
        }
        None => {},
    }
    test!(text.strip_prefix('z').is_none());

    let suffix = text.strip_suffix("bar");
    match suffix {
        Some(rest) => {
            test!(rest == "foo", {
                proof {
                test_link_str_strip_suffix_string(text@, "bar", suffix);
                test_link_str_strip_suffix_string_surjective(text@, "bar", Some("foo"));
                prove_strip_suffix_string_eq(text, "bar", suffix, "foo");
                prove_str_eq(rest, "foo");
                }
            });
        }
        None => {},
    }
    test!(text.strip_suffix('z').is_none());

    // ISSUE TODO(Verge): `third-party/rust/library/alloctests/tests/str.rs` has no direct
    // `strip_prefix` / `strip_suffix` test block to migrate. Full Rust semantics over all supported
    // pattern types were attempted here; only fixed string-pattern `Some` cases and char-pattern
    // `None` cases are active because exact helpers currently cover `&str` outputs, while exhaustive
    // char/closure/char-slice variants would need additional local injectivity helpers.
}

/// Fresh downstream smoke test for slice-pattern matching.
/// It is not a direct Rust core/std migration; Port status: fresh/non-migrated; partial representative boolean coverage, not a full slice-pattern matrix.
fn test_char_slice_pattern_representatives() {
    broadcast use group_str_contains;
    broadcast use group_str_starts_with;
    broadcast use group_str_ends_with;
    broadcast use group_str_trim_matches;

    proof {
        reveal_strlit("-+-core-+");
    }

    let marks: &[char] = &['-', '+'];
    let text = "-+-core-+";

    test!(text.contains(marks));
    test!(text.starts_with(marks));
    test!(text.ends_with(marks));

    let trimmed = text.trim_matches(marks);
    test!(!trimmed.starts_with(marks));
    test!(!trimmed.ends_with(marks));
}

/// Migrated from Rust core/std empty-pattern behavior around `contains`, `starts_with`, `ends_with`, `find`,
/// `rfind`, `split_once`, `rsplit_once`, `strip_prefix`, and `strip_suffix`.
/// Port status: partial; exact for the selected byte offsets and returned views. Full upstream semantics were
/// attempted; deferred rows are recorded below with `ISSUE TODO(Verge):` notes.
fn test_empty_pattern_corner_case_exact() {
    broadcast use group_str_axioms;
    broadcast use group_str_contains;
    broadcast use group_str_starts_with;
    broadcast use group_str_ends_with;
    broadcast use group_str_find;
    broadcast use group_str_rfind;
    broadcast use group_str_split_once;
    broadcast use group_str_rsplit_once;
    broadcast use group_str_strip_prefix;
    broadcast use group_str_strip_suffix;

    proof {
        reveal_strlit("abc");
        reveal_strlit("");
    }

    let text = "abc";
    let empty = "";

    test!(text.contains(empty));
    test!("".contains(empty));
    test!(text.starts_with(empty));
    test!("".starts_with(empty));
    test!(text.ends_with(empty));
    test!("".ends_with(empty));

    let empty_find = text.find(empty);
    test!(empty_find == Some(0usize), {
        proof {
        test_link_str_find_string_surjective(text@, empty, Some(0usize));
        prove_find_string_eq(text, empty, empty_find, 0usize);
        }
    });
    let empty_rfind = text.rfind(empty);
    test!(empty_rfind == Some(3usize), {
        proof {
        test_link_str_rfind_string_surjective(text@, empty, Some(3usize));
        prove_rfind_string_eq(text, empty, empty_rfind, 3usize);
        }
    });

    let split = text.split_once(empty);
    match split {
        Some((head, tail)) => {
            test!(head == "", {
                proof {
                test_link_str_split_once_string(text@, empty, split);
                test_link_str_split_once_string_surjective(text@, empty, Some(("", "abc")));
                prove_split_once_string_eq(text, empty, split, "", "abc");
                prove_str_eq(head, "");
                }
            });
            test!(tail == "abc", {
                proof {
                test_link_str_split_once_string(text@, empty, split);
                test_link_str_split_once_string_surjective(text@, empty, Some(("", "abc")));
                prove_split_once_string_eq(text, empty, split, "", "abc");
                prove_str_eq(tail, "abc");
                }
            });
        }
        None => {},
    }

    let rsplit = text.rsplit_once(empty);
    match rsplit {
        Some((head, tail)) => {
            test!(head == "abc", {
                proof {
                test_link_str_rsplit_once_string(text@, empty, rsplit);
                test_link_str_rsplit_once_string_surjective(text@, empty, Some(("abc", "")));
                prove_rsplit_once_string_eq(text, empty, rsplit, "abc", "");
                prove_str_eq(head, "abc");
                }
            });
            test!(tail == "", {
                proof {
                test_link_str_rsplit_once_string(text@, empty, rsplit);
                test_link_str_rsplit_once_string_surjective(text@, empty, Some(("abc", "")));
                prove_rsplit_once_string_eq(text, empty, rsplit, "abc", "");
                prove_str_eq(tail, "");
                }
            });
        }
        None => {},
    }

    let prefix = text.strip_prefix(empty);
    match prefix {
        Some(rest) => {
            test!(rest == "abc", {
                proof {
                test_link_str_strip_prefix_string(text@, empty, prefix);
                test_link_str_strip_prefix_string_surjective(text@, empty, Some("abc"));
                prove_strip_prefix_string_eq(text, empty, prefix, "abc");
                prove_str_eq(rest, "abc");
                }
            });
        }
        None => {},
    }

    let suffix = text.strip_suffix(empty);
    match suffix {
        Some(rest) => {
            test!(rest == "abc", {
                proof {
                test_link_str_strip_suffix_string(text@, empty, suffix);
                test_link_str_strip_suffix_string_surjective(text@, empty, Some("abc"));
                prove_strip_suffix_string_eq(text, empty, suffix, "abc");
                prove_str_eq(rest, "abc");
                }
            });
        }
        None => {},
    }

    // ISSUE TODO(Verge): Upstream empty-pattern searcher/match-indices semantics
    // (`match_indices("")` byte-boundary stream for `aä中!`, `Pattern::into_searcher` forward and
    // reverse `SearchStep::{Match, Reject, Done}` sequences for empty needle over ASCII/multibyte
    // haystacks, and repeated `Done` after exhaustion) were attempted but are not active because
    // `Searcher`/`SearchStep` construction and iterator collection are not exposed by the current
    // Verge test helpers. The active assertions cover the public empty-pattern methods currently
    // modeled in this file.
}

/// Fresh downstream corner-case test for overlapping string patterns.
/// It is not a direct Rust core/std migration; Port status: fresh/non-migrated; partial coverage of one overlapping-pattern corner case with exact offsets and split views.
fn test_overlapping_pattern_corner_case_exact() {
    broadcast use group_str_axioms;
    broadcast use group_str_contains;
    broadcast use group_str_find;
    broadcast use group_str_rfind;
    broadcast use group_str_split_once;
    broadcast use group_str_rsplit_once;
    broadcast use group_str_trim_start_matches;

    proof {
        reveal_strlit("aaaa");
        reveal_strlit("aa");
        reveal_strlit("");
    }

    let text = "aaaa";
    let pat = "aa";

    test!(text.contains(pat));
    let overlap_find = text.find(pat);
    test!(overlap_find == Some(0usize), {
        proof {
        test_link_str_find_string_surjective(text@, pat, Some(0usize));
        prove_find_string_eq(text, pat, overlap_find, 0usize);
        }
    });
    let overlap_rfind = text.rfind(pat);
    test!(overlap_rfind == Some(2usize), {
        proof {
        test_link_str_rfind_string_surjective(text@, pat, Some(2usize));
        prove_rfind_string_eq(text, pat, overlap_rfind, 2usize);
        }
    });

    let split = text.split_once(pat);
    match split {
        Some((head, tail)) => {
            test!(head == "", {
                proof {
                test_link_str_split_once_string(text@, pat, split);
                test_link_str_split_once_string_surjective(text@, pat, Some(("", "aa")));
                prove_split_once_string_eq(text, pat, split, "", "aa");
                prove_str_eq(head, "");
                }
            });
            test!(tail == "aa", {
                proof {
                test_link_str_split_once_string(text@, pat, split);
                test_link_str_split_once_string_surjective(text@, pat, Some(("", "aa")));
                prove_split_once_string_eq(text, pat, split, "", "aa");
                prove_str_eq(tail, "aa");
                }
            });
        }
        None => {},
    }

    let rsplit = text.rsplit_once(pat);
    match rsplit {
        Some((head, tail)) => {
            test!(head == "aa", {
                proof {
                test_link_str_rsplit_once_string(text@, pat, rsplit);
                test_link_str_rsplit_once_string_surjective(text@, pat, Some(("aa", "")));
                prove_rsplit_once_string_eq(text, pat, rsplit, "aa", "");
                prove_str_eq(head, "aa");
                }
            });
            test!(tail == "", {
                proof {
                test_link_str_rsplit_once_string(text@, pat, rsplit);
                test_link_str_rsplit_once_string_surjective(text@, pat, Some(("aa", "")));
                prove_rsplit_once_string_eq(text, pat, rsplit, "aa", "");
                prove_str_eq(tail, "");
                }
            });
        }
        None => {},
    }

    let overlap_trim_start = text.trim_start_matches(pat);
    test!(overlap_trim_start == "", {
        proof {
        test_link_str_trim_start_matches_string_surjective(text@, pat, ""@);
        prove_trim_start_matches_string_eq(text, pat, overlap_trim_start, "");
        prove_str_eq(overlap_trim_start, "");
        }
    });
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::pattern::contains_starts_ends_exact_representatives",
        test_contains_starts_ends_exact_representatives,
    );
    count += crate::run_test(
        "str::pattern::find_and_rfind_exact_offsets",
        test_find_and_rfind_exact_offsets,
    );
    count += crate::run_test(
        "str::pattern::split_once_and_rsplit_once_exact_views",
        test_split_once_and_rsplit_once_exact_views,
    );
    count += crate::run_test(
        "str::pattern::trim_matches_exact_outputs",
        test_trim_matches_exact_outputs,
    );
    count += crate::run_test(
        "str::pattern::strip_prefix_and_suffix_exact_outputs",
        test_strip_prefix_and_suffix_exact_outputs,
    );
    count += crate::run_test(
        "str::pattern::char_slice_pattern_representatives",
        test_char_slice_pattern_representatives,
    );
    count += crate::run_test(
        "str::pattern::empty_pattern_corner_case_exact",
        test_empty_pattern_corner_case_exact,
    );
    count += crate::run_test(
        "str::pattern::overlapping_pattern_corner_case_exact",
        test_overlapping_pattern_corner_case_exact,
    );
    count
}
