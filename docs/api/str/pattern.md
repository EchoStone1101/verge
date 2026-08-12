# `verge::str::pattern`

Monomorphic specifications for string pattern operations.

Rust's `str` pattern APIs are generic over the unstable `Pattern` trait.
Verge exposes a concrete extension-trait surface instead: every supported
pattern kind has its own method suffix (`_ch`, `_chars`, `_fn`, or `_str`),
and each method carries a monomorphic specification respectively.


## Traits


### `StrPatternFns`

```rust
pub trait StrPatternFns: View<V = Seq<char>>
```


#### `contains_ch`

```rust
fn contains_ch(&self, ch: char) -> (ret: bool)
    ensures
        ret == exists |i: int| 0 <= i < self@.len() && self@[i] == ch;
```


#### `contains_chars`

```rust
fn contains_chars<'a>(&self, chars: &'a [char]) -> (ret: bool)
    ensures
        ret == exists |i: int| 0 <= i < self@.len() && #[trigger] chars@.contains(self@[i]);
```


#### `contains_fn`

```rust
fn contains_fn<F>(&self, f: F) -> (ret: bool)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        ret == exists |i: int| 0 <= i < self@.len() && #[trigger] call_ensures(f, (self@[i],), true);
```


#### `contains_str`

```rust
fn contains_str<'a>(&self, pat: &'a str) -> (ret: bool)
    ensures
        ret == pat@.is_subrange_of(self@);
```


#### `starts_with_ch`

```rust
fn starts_with_ch(&self, ch: char) -> (ret: bool)
    ensures
        ret == (self@.len() > 0 && self@.first() == ch);
```


#### `starts_with_chars`

```rust
fn starts_with_chars<'a>(&self, chars: &'a [char]) -> (ret: bool)
    ensures
        ret == (self@.len() > 0 && #[trigger] chars@.contains(self@.first()));
```


#### `starts_with_fn`

```rust
fn starts_with_fn<F>(&self, f: F) -> (ret: bool)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        ret == (self@.len() > 0 && #[trigger] call_ensures(f, (self@.first(),), true));
```


#### `starts_with_str`

```rust
fn starts_with_str<'a>(&self, pat: &'a str) -> (ret: bool)
    ensures
        ret == pat@.is_prefix_of(self@);
```


#### `ends_with_ch`

```rust
fn ends_with_ch(&self, ch: char) -> (ret: bool)
    ensures
        ret == (self@.len() > 0 && self@.last() == ch);
```


#### `ends_with_chars`

```rust
fn ends_with_chars<'a>(&self, chars: &'a [char]) -> (ret: bool)
    ensures
        ret == (self@.len() > 0 && #[trigger] chars@.contains(self@.last()));
```


#### `ends_with_fn`

```rust
fn ends_with_fn<F>(&self, f: F) -> (ret: bool)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        ret == (self@.len() > 0 && #[trigger] call_ensures(f, (self@.last(),), true));
```


#### `ends_with_str`

```rust
fn ends_with_str<'a>(&self, pat: &'a str) -> (ret: bool)
    ensures
        ret == pat@.is_suffix_of(self@);
```


#### `find_ch`

```rust
fn find_ch(&self, ch: char) -> (ret: Option<usize>)
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> self@[i] != ch,
        Some(k) => {
        let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
        &&& is_char_boundary(self@.as_bytes(), k as int)
        &&& i < self@.len()
        &&& self@[i] == ch
        &&& forall |j: int| 0 <= j < i ==> self@[j] != ch
        },
        };
```


#### `find_chars`

```rust
fn find_chars<'a>(&self, chars: &'a [char]) -> (ret: Option<usize>)
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] chars@.contains(self@[i]),
        Some(k) => {
        let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
        &&& is_char_boundary(self@.as_bytes(), k as int)
        &&& i < self@.len()
        &&& chars@.contains(self@[i])
        &&& forall |j: int| 0 <= j < i ==> !#[trigger] chars@.contains(self@[j])
        },
        };
```


#### `find_fn`

```rust
fn find_fn<F>(&self, f: F) -> (ret: Option<usize>)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] call_ensures(f, (self@[i],), true),
        Some(k) => {
        let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
        &&& is_char_boundary(self@.as_bytes(), k as int)
        &&& i < self@.len()
        &&& call_ensures(f, (self@[i],), true)
        &&& forall |j: int| 0 <= j < i ==> !#[trigger] call_ensures(f, (self@[j],), true)
        },
        };
```


#### `find_str`

```rust
fn find_str<'a>(&self, pat: &'a str) -> (ret: Option<usize>)
    ensures
        match ret {
        None => !pat@.is_subrange_of(self@),
        Some(k) => {
        let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
        &&& is_char_boundary(self@.as_bytes(), k as int)
        &&& i + pat@.len() <= self@.len()
        &&& pat@ == self@.subrange(i, i + pat@.len())
        &&& forall |j: int| 0 <= j < i ==> pat@ != #[trigger] self@.subrange(j, j + pat@.len())
        },
        };
```


#### `rfind_ch`

```rust
fn rfind_ch(&self, ch: char) -> (ret: Option<usize>)
    ensures
        match ret {
            None => forall |i: int| 0 <= i < self@.len() ==> self@[i] != ch,
            Some(k) => {
                let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
                &&& is_char_boundary(self@.as_bytes(), k as int)
                &&& i < self@.len()
                &&& self@[i] == ch
                &&& forall |j: int| i < j < self@.len() ==> self@[j] != ch
            },
        };
```


#### `rfind_chars`

```rust
fn rfind_chars<'a>(&self, chars: &'a [char]) -> (ret: Option<usize>)
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] chars@.contains(self@[i]),
        Some(k) => {
        let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
        &&& is_char_boundary(self@.as_bytes(), k as int)
        &&& i < self@.len()
        &&& chars@.contains(self@[i])
        &&& forall |j: int| i < j < self@.len() ==> !#[trigger] chars@.contains(self@[j])
        },
        };
```


#### `rfind_fn`

```rust
fn rfind_fn<F>(&self, f: F) -> (ret: Option<usize>)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] call_ensures(f, (self@[i],), true),
        Some(k) => {
        let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
        &&& is_char_boundary(self@.as_bytes(), k as int)
        &&& i < self@.len()
        &&& call_ensures(f, (self@[i],), true)
        &&& forall |j: int| i < j < self@.len() ==> !#[trigger] call_ensures(f, (self@[j],), true)
        },
        };
```


#### `rfind_str`

```rust
fn rfind_str<'a>(&self, pat: &'a str) -> (ret: Option<usize>)
    ensures
        match ret {
        None => !pat@.is_subrange_of(self@),
        Some(k) => {
        let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
        &&& is_char_boundary(self@.as_bytes(), k as int)
        &&& i + pat@.len() <= self@.len()
        &&& pat@ == self@.subrange(i, i + pat@.len())
        &&& forall |j: int| i < j <= self@.len() - pat@.len()
            ==> pat@ != #[trigger] self@.subrange(j, j + pat@.len())
        },
        };
```


#### `split_once_ch`

```rust
fn split_once_ch<'a>(&'a self, ch: char) -> (ret: Option<(&'a str, &'a str)>)
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> self@[i] != ch,
        Some((head, tail)) => {
        &&& self@ =~= head@ + seq![ch] + tail@
        &&& forall |i: int| 0 <= i < head@.len() ==> self@[i] != ch
        },
        };
```


#### `split_once_chars`

```rust
fn split_once_chars<'a, 'b>(&'a self, chars: &'b [char]) -> (ret: Option<(&'a str, &'a str)>)
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] chars@.contains(self@[i]),
        Some((head, tail)) => {
        let i = head@.len() as int;
        &&& i < self@.len()
        &&& self@ =~= head@ + seq![self@[i]] + tail@
        &&& chars@.contains(self@[i])
        &&& forall |j: int| 0 <= j < i ==> !#[trigger] chars@.contains(self@[j])
        },
        };
```


#### `split_once_fn`

```rust
fn split_once_fn<'a, F>(&'a self, f: F) -> (ret: Option<(&'a str, &'a str)>)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] call_ensures(f, (self@[i],), true),
        Some((head, tail)) => {
        let i = head@.len() as int;
        &&& i < self@.len()
        &&& self@ =~= head@ + seq![self@[i]] + tail@
        &&& call_ensures(f, (self@[i],), true)
        &&& forall |j: int| 0 <= j < i ==> !#[trigger] call_ensures(f, (self@[j],), true)
        },
        };
```


#### `split_once_str`

```rust
fn split_once_str<'a, 'b>(&'a self, pat: &'b str) -> (ret: Option<(&'a str, &'a str)>)
    ensures
        match ret {
        None => !pat@.is_subrange_of(self@),
        Some((head, tail)) => {
        &&& pat@.len() == 0 ==> (head@.len() == 0 && tail@ =~= self@)
        &&& pat@.len() > 0 ==> {
            let i = head@.len() as int;
            &&& i + pat@.len() <= self@.len()
            &&& self@ =~= head@ + pat@ + tail@
            &&& forall |j: int| 0 <= j < i ==> pat@ != #[trigger] self@.subrange(j, j + pat@.len())
        }
        },
        };
```


#### `rsplit_once_ch`

```rust
fn rsplit_once_ch<'a>(&'a self, ch: char) -> (ret: Option<(&'a str, &'a str)>)
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> self@[i] != ch,
        Some((head, tail)) => {
        &&& self@ =~= head@ + seq![ch] + tail@
        &&& forall |i: int| head@.len() + 1 <= i < self@.len() ==> self@[i] != ch
        },
        };
```


#### `rsplit_once_chars`

```rust
fn rsplit_once_chars<'a, 'b>(&'a self, chars: &'b [char]) -> (ret: Option<(&'a str, &'a str)>)
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] chars@.contains(self@[i]),
        Some((head, tail)) => {
        let i = head@.len() as int;
        &&& i < self@.len()
        &&& self@ =~= head@ + seq![self@[i]] + tail@
        &&& chars@.contains(self@[i])
        &&& forall |j: int| i < j < self@.len() ==> !#[trigger] chars@.contains(self@[j])
        },
        };
```


#### `rsplit_once_fn`

```rust
fn rsplit_once_fn<'a, F>(&'a self, f: F) -> (ret: Option<(&'a str, &'a str)>)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] call_ensures(f, (self@[i],), true),
        Some((head, tail)) => {
        let i = head@.len() as int;
        &&& i < self@.len()
        &&& self@ =~= head@ + seq![self@[i]] + tail@
        &&& call_ensures(f, (self@[i],), true)
        &&& forall |j: int| i < j < self@.len() ==> !#[trigger] call_ensures(f, (self@[j],), true)
        },
        };
```


#### `rsplit_once_str`

```rust
fn rsplit_once_str<'a, 'b>(&'a self, pat: &'b str) -> (ret: Option<(&'a str, &'a str)>)
    ensures
        match ret {
        None => !pat@.is_subrange_of(self@),
        Some((head, tail)) => {
        &&& pat@.len() == 0 ==> (head@ =~= self@ && tail@.len() == 0)
        &&& pat@.len() > 0 ==> {
            let i = head@.len() as int;
            &&& i + pat@.len() <= self@.len()
            &&& self@ =~= head@ + pat@ + tail@
            &&& forall |j: int| i < j <= self@.len() - pat@.len()
                ==> pat@ != #[trigger] self@.subrange(j, j + pat@.len())
        }
        },
        };
```


#### `trim_matches_ch`

```rust
fn trim_matches_ch(&self, ch: char) -> (ret: &str)
    ensures
        ret@ == self@.skip_while(|c: char| c == ch).rskip_while(|c: char| c == ch);
```


#### `trim_matches_chars`

```rust
fn trim_matches_chars<'a>(&self, chars: &'a [char]) -> (ret: &str)
    ensures
        ret@ == self@.skip_while(|c: char| chars@.contains(c)).rskip_while(|c: char| chars@.contains(c));
```


#### `trim_matches_fn`

```rust
fn trim_matches_fn<F>(&self, f: F) -> (ret: &str)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        ret@ == self@.skip_while(|c: char| call_ensures(f, (c,), true))
        .rskip_while(|c: char| call_ensures(f, (c,), true));
```


#### `trim_matches_str`

```rust
fn trim_matches_str<'a>(&self, pat: &'a str) -> (ret: &str)
    ensures
        (pat@.len() == 0 && ret@ == self@) || (pat@.len() > 0 && ret@.is_subrange_of(self@)
        && (ret@.len() == 0 || (!pat@.is_prefix_of(ret@) && !pat@.is_suffix_of(ret@))));
```


#### `trim_start_matches_ch`

```rust
fn trim_start_matches_ch(&self, ch: char) -> (ret: &str)
    ensures
        ret@ == self@.skip_while(|c: char| c == ch);
```


#### `trim_start_matches_chars`

```rust
fn trim_start_matches_chars<'a>(&self, chars: &'a [char]) -> (ret: &str)
    ensures
        ret@ == self@.skip_while(|c: char| chars@.contains(c));
```


#### `trim_start_matches_fn`

```rust
fn trim_start_matches_fn<F>(&self, f: F) -> (ret: &str)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        ret@ == self@.skip_while(|c: char| call_ensures(f, (c,), true));
```


#### `trim_start_matches_str`

```rust
fn trim_start_matches_str<'a>(&self, pat: &'a str) -> (ret: &str)
    ensures
        (pat@.len() == 0 && ret@ == self@) || (pat@.len() > 0 && ret@.is_suffix_of(self@)
        && (ret@.len() == 0 || !pat@.is_prefix_of(ret@)));
```


#### `trim_end_matches_ch`

```rust
fn trim_end_matches_ch(&self, ch: char) -> (ret: &str)
    ensures
        ret@ == self@.rskip_while(|c: char| c == ch);
```


#### `trim_end_matches_chars`

```rust
fn trim_end_matches_chars<'a>(&self, chars: &'a [char]) -> (ret: &str)
    ensures
        ret@ == self@.rskip_while(|c: char| chars@.contains(c));
```


#### `trim_end_matches_fn`

```rust
fn trim_end_matches_fn<F>(&self, f: F) -> (ret: &str)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        ret@ == self@.rskip_while(|c: char| call_ensures(f, (c,), true));
```


#### `trim_end_matches_str`

```rust
fn trim_end_matches_str<'a>(&self, pat: &'a str) -> (ret: &str)
    ensures
        (pat@.len() == 0 && ret@ == self@) || (pat@.len() > 0 && ret@.is_prefix_of(self@)
        && (ret@.len() == 0 || !pat@.is_suffix_of(ret@)));
```


#### `strip_prefix_ch`

```rust
fn strip_prefix_ch<'a>(&'a self, ch: char) -> (ret: Option<&'a str>)
    ensures
        match ret {
        Some(rest) => self@ =~= seq![ch] + rest@,
        None => self@.len() == 0 || self@.first() != ch,
        };
```


#### `strip_prefix_chars`

```rust
fn strip_prefix_chars<'a, 'b>(&'a self, chars: &'b [char]) -> (ret: Option<&'a str>)
    ensures
        match ret {
        Some(rest) => self@.len() > 0 && chars@.contains(self@.first()) && self@ =~= seq![self@.first()] + rest@,
        None => self@.len() == 0 || !chars@.contains(self@.first()),
        };
```


#### `strip_prefix_fn`

```rust
fn strip_prefix_fn<'a, F>(&'a self, f: F) -> (ret: Option<&'a str>)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        match ret {
        Some(rest) => self@.len() > 0 && call_ensures(f, (self@.first(),), true)
        && self@ =~= seq![self@.first()] + rest@,
        None => self@.len() == 0 || !call_ensures(f, (self@.first(),), true),
        };
```


#### `strip_prefix_str`

```rust
fn strip_prefix_str<'a, 'b>(&'a self, pat: &'b str) -> (ret: Option<&'a str>)
    ensures
        match ret {
        Some(rest) => self@ =~= pat@ + rest@,
        None => !pat@.is_prefix_of(self@),
        };
```


#### `strip_suffix_ch`

```rust
fn strip_suffix_ch<'a>(&'a self, ch: char) -> (ret: Option<&'a str>)
    ensures
        match ret {
        Some(rest) => self@ =~= rest@ + seq![ch],
        None => self@.len() == 0 || self@.last() != ch,
        };
```


#### `strip_suffix_chars`

```rust
fn strip_suffix_chars<'a, 'b>(&'a self, chars: &'b [char]) -> (ret: Option<&'a str>)
    ensures
        match ret {
        Some(rest) => self@.len() > 0 && chars@.contains(self@.last()) && self@ =~= rest@ + seq![self@.last()],
        None => self@.len() == 0 || !chars@.contains(self@.last()),
        };
```


#### `strip_suffix_fn`

```rust
fn strip_suffix_fn<'a, F>(&'a self, f: F) -> (ret: Option<&'a str>)
    where F: FnMut(char) -> bool,
    requires is_deterministic(f) && is_total(f),
    ensures
        match ret {
        Some(rest) => self@.len() > 0 && call_ensures(f, (self@.last(),), true)
        && self@ =~= rest@ + seq![self@.last()],
        None => self@.len() == 0 || !call_ensures(f, (self@.last(),), true),
        };
```


#### `strip_suffix_str`

```rust
fn strip_suffix_str<'a, 'b>(&'a self, pat: &'b str) -> (ret: Option<&'a str>)
    ensures
        match ret {
        Some(rest) => self@ =~= rest@ + pat@,
        None => !pat@.is_suffix_of(self@),
        };
```


## Functions


### `join`

Joins alternating result pieces and separators.

```rust
pub open spec fn join(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> Seq<char>
    recommends seq.len() + 1 == gap.len(),
        {
        gap.first()
        + gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten()
        }
```


### `rjoin`

Joins alternating result pieces and separators from the right.

```rust
pub open spec fn rjoin(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> Seq<char>
    recommends seq.len() + 1 == gap.len(),
        {
        gap.last()
        + gap.drop_last().map(|i: int, ss: Seq<char>| ss + seq[i]).reverse().flatten()
        }
```
