//! Tests for string formatting APIs.

use vstd::prelude::*;
use verge::prelude::*;
use verge::str::*;
use std::rc::Rc;

verus! {

struct CustomToken {
}

#[derive(Debug)]
struct DebugToken {
    value: bool,
}

impl ToStringSpecImpl for CustomToken {
    open spec fn to_string_ensures(&self, s: String) -> bool {
        s@ =~= seq!['o', 'k']
    }
}

impl ToString for CustomToken {
    fn to_string(&self) -> (s: String)
        ensures
            s@ == seq!['o', 'k'],
    {
        proof { reveal_strlit("ok"); }
        String::from_str("ok")
    }
}

fn test_custom_to_string() {
    let token = CustomToken { };
    let s = token.to_string();
    assert(s@ == seq!['o', 'k']);
}

fn test_display_backed_to_string_specs() {
    let b = true;
    let bool_s = b.to_string();
    proof { lemma_bool_to_string(&b, bool_s); }
    assert(bool_s@ == seq!['t', 'r', 'u', 'e']);

    let b_false = false;
    let false_s = b_false.to_string();
    proof { lemma_bool_to_string(&b_false, false_s); }
    assert(false_s@ == seq!['f', 'a', 'l', 's', 'e']);

    let c = 'z';
    let char_s = c.to_string();
    proof { lemma_char_to_string(&c, char_s); }
    assert(char_s@ == seq!['z']);
}

fn test_string_to_string_spec() {
    proof { reveal_strlit("copy"); }
    let source = String::from_str("copy");
    let s = source.to_string();
    proof { lemma_string_to_string(&source, s); }
    assert(s@ == seq!['c', 'o', 'p', 'y']);
}

fn test_int_to_string_specs() {
    let zero: i32 = 0;
    let zero_s = zero.to_string();
    proof {
        lemma_int_to_string(&zero, zero_s);
        reveal(spec_int_to_str);
    }
    assert(zero_s@ == seq!['0']);

    let positive: u32 = 7;
    let positive_s = positive.to_string();
    proof {
        lemma_int_to_string(&positive, positive_s);
        reveal(spec_int_to_str);
        reveal_with_fuel(spec_int_to_str_rec, 4);
    }
    assert(positive_s@ == seq!['7']);

    let negative: i32 = -3;
    let negative_s = negative.to_string();
    proof {
        lemma_int_to_string(&negative, negative_s);
        reveal(spec_int_to_str);
        reveal_with_fuel(spec_int_to_str_rec, 4);
    }
    assert(negative_s@ == seq!['-', '3']);
}

fn test_ref_to_string_delegates_to_underlying_display() {
    let b = true;
    let b_ref = &b;
    let s = b_ref.to_string();
    proof {
        lemma_ref_to_string::<bool>(&b_ref, s);
        lemma_bool_to_string(b_ref, s);
    }
    assert(s@ == seq!['t', 'r', 'u', 'e']);
}

fn test_mut_ref_to_string_delegates_to_underlying_display() {
    let mut b = true;
    let b_mut = &mut b;
    let s = b_mut.to_string();
    proof {
        lemma_mut_ref_to_string::<bool>(&b_mut, s);
        lemma_bool_to_string(&*b_mut, s);
    }
    assert(s@ == seq!['t', 'r', 'u', 'e']);
}

fn test_box_char_to_string_delegates_to_underlying_display() {
    let b = Box::new('b');
    let s = b.to_string();
    proof {
        lemma_box_to_string::<char>(&b, s);
        lemma_char_to_string(&*b, s);
    }
    assert(s@ == seq!['b']);
}

fn test_rc_char_to_string_delegates_to_underlying_display() {
    let r = Rc::new('r');
    let s = r.to_string();
    proof {
        lemma_rc_to_string::<char>(&r, s);
        lemma_char_to_string(&*r, s);
    }
    assert(s@ == seq!['r']);
}

fn test_debug_format_callability() {
    let token = DebugToken { value: true };
    let s = debug_format(&token);
    assert(debug_format_ensures::<DebugToken>(&token, s));
}

} // verus!
