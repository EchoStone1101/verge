//! Tests for string formatting APIs.

use vstd::prelude::*;
use verge::prelude::*;
use verge::str::*;

verus! {

struct CustomToken {
}

impl ToStringSpecImpl for CustomToken {
    open spec fn to_string_ensures(&self, s: String) -> bool {
        s@ == seq!['o', 'k']
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

    let c = 'z';
    let char_s = c.to_string();
    proof { lemma_char_to_string(&c, char_s); }
    assert(char_s@ == seq!['z']);
}

} // verus!
