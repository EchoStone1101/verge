# `verge::str::pattern`

Specifications and lemmas for string pattern related operations.

## Specification Methodology
To specify `str::split`, `str::contains`, and other methods that make use of
the `std::str::Pattern` trait, Verus adopts the "linking lemma" pattern,
where generic post-conditions are captured via `uninterp spec` functions
(e.g., `str_contains_post`). Then, broadcast lemmas use the general
specs as triggers to automatically introduce actual specs per pattern type
(e.g., `lemma_str_contains_str` for `&str` patterns, `lemma_str_contains_char`
for `char` patterns). This design minimizes both spec redundancy and user burden
(thanks to automatic broadcasting).

Additionally, while the lemma post-conditions are meant to be complete (in that they
uniquely define the output), Verge cannot predict all forms of wanted specs,
which can be particularly a problem for the more intricate APIs (e.g., `str::split`
with `&str` patterns). In this case, it is helpful to understand that all the
immediate post-conditions are internally derived from the forward and backward
pattern matching operations (`spec_matches` and `spec_rmatches`), serving as
a complete and basic spec foundation.
By default this is hidden by `#[verifier::opaque]`, but could be `reveal`-ed
to help prove alternative specs in certain contexts (e.g., more intuitive `str::split`
specs when `pat@.len() == 1`), or show consistency between APIs (e.g., `str::split` and
`str::matches` join into the original string).


## Traits


### `ExPattern`

Enables `std::str::pattern::Pattern`.

```rust
pub trait ExPattern: Sized
```


### `ExSearcher`

```rust
pub trait ExSearcher<'a>
```


### `ExReverseSearcher`

```rust
pub trait ExReverseSearcher<'a>: Searcher<'a>
```


### `ExDoubleEndedSearcher`

```rust
pub trait ExDoubleEndedSearcher<'a>: ReverseSearcher<'a>
```


## Functions


### `char_matches_post`

Post-conditions for matching by the `char` pattern, aside from the joining.

```rust
pub open spec fn char_matches_post(
    s: Seq<char>, c: char, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool
{
        // gaps are never empty
        &&& gap.len() > 0
        // gaps cannot contain the pattern
        &&& forall |i: int| 0 <= i < gap.len() ==> !(#[trigger] gap[i].contains(c))
        // matches have one item less than gaps
        &&& seq.len() + 1 == gap.len()
        // matches match the pattern
        &&& forall |i: int| 0 <= i < seq.len() ==> #[trigger] (seq[i] =~= seq![c])
}
```


### `closure_matches_post`

Post-conditions for matching by the closure pattern, aside from the joining.

```rust
pub open spec fn closure_matches_post<F>(
    s: Seq<char>, f: F, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool
    where
    F: FnMut(char) -> bool,
    recommends
        is_deterministic(f) && is_total(f),
        {
        // gaps are never empty
        &&& gap.len() > 0
        // gaps cannot contain the pattern
        &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() ==>
        gap[i].all(|c: char| call_ensures(f, (c,), false))
        // matches have one item less than gaps
        &&& seq.len() + 1 == gap.len()
        // matches match the pattern
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==>
        seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true)
        }
```


### `chars_matches_post`

Post-conditions for matching by the char slice pattern, aside from the joining.

```rust
pub open spec fn chars_matches_post(
    s: Seq<char>, chars: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool
{
        // gaps are never empty
        &&& gap.len() > 0
        // gaps cannot contain the pattern
        &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() ==>
            gap[i].all(|c: char| !chars.contains(c))
        // matches have one item less than gaps
        &&& seq.len() + 1 == gap.len()
        // matches match the pattern
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==>
            seq[i].len() == 1 && chars.contains(seq[i][0])
}
```


### `empty_string_matches_post`

Post-conditions for matching by the empty string pattern, aside from the joining.

```rust
pub open spec fn empty_string_matches_post(
    s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool
{
        // "ab..z" => gap = ["", "a", "b", ..., "z", ""]
        &&& seq.len() == s.len() + 1
        &&& gap.len() == s.len() + 2
        &&& forall |i: int| 0 <= i < seq.len() ==>
            #[trigger] seq[i].len() == 0
        &&& gap.first().len() == 0 && gap.last().len() == 0
        &&& forall |i: int| 1 <= i < gap.len() - 1 ==>
            #[trigger] gap[i] == seq![s[i-1]]
}
```


### `string_matches_post`

Post-conditions for forward matching by the string pattern, aside from the joining.

```rust
pub open spec fn string_matches_post(
    s: Seq<char>, pat: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool
{
        // corner case: empty string matching
        &&& pat.len() == 0 ==> empty_string_matches_post(s, seq, gap)
        // general matching
        &&& pat.len() > 0 ==> {
            // gaps are never empty
            &&& gap.len() > 0
            // `gap + pat` (apart from the last) cannot have `pat` as a prefix or infix
            &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
                ==> gap[i].len() > 0
                    ==> !pat.is_prefix_of(gap[i] + pat) && !pat.is_infix_of(gap[i] + pat)
            // last gap cannot have `pat` as a substring
            &&& !(pat.is_subrange_of(gap.last()))
            // matches have one item less than gaps
            &&& seq.len() + 1 == gap.len()
            // matches match the pattern
            &&& forall |i: int| 0 <= i < seq.len() ==> #[trigger] (seq[i] =~= pat)
}
    }
```


### `string_rmatches_post`

Post-conditions for backward matching by the string pattern, aside from the joining.

```rust
pub open spec fn string_rmatches_post(
    s: Seq<char>, pat: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool
{
        // corner case: empty string matching
        &&& pat.len() == 0 ==> empty_string_matches_post(s, seq, gap)
        // general matching
        &&& pat.len() > 0 ==> {
            // gaps are never empty, and there are at most `n` splits
            &&& gap.len() > 0
            // `pat + gap` (apart from the last) cannot have `pat` as a suffix or infix
            &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
                ==> gap[i].len() > 0
                    ==> !pat.is_suffix_of(pat + gap[i]) && !pat.is_infix_of(pat + gap[i])
            // last gap cannot have `pat` as a substring
            &&& !(pat.is_subrange_of(gap.last()))
            // matches have one item less than gaps
            &&& seq.len() + 1 == gap.len()
            // matches match the pattern
            &&& forall |i: int| 0 <= i < seq.len() ==> #[trigger] (seq[i] =~= pat)
}
    }
```


### `join`

Forward joining `seq` and `gap`.

```rust
pub open spec fn join(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> Seq<char>
    recommends
        seq.len() + 1 == gap.len(),
        {
        gap.first()
        + gap
        .drop_first()
        .map(|i: int, ss: Seq<char>| seq[i] + ss)
        .flatten()
        }
```


### `rjoin`

Backward joining `seq` and `gap`.

```rust
pub open spec fn rjoin(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> Seq<char>
    recommends
        seq.len() + 1 == gap.len(),
        {
        gap
        .drop_first()
        .map(|i: int, ss: Seq<char>| ss + seq[i])
        .reverse()
        .flatten_alt()
        + gap.first()
        }
```


### `spec_matches`

Encodes forward matching `s` by the general pattern `pat`,
returning the matches and gaps.

```rust
pub uninterp spec fn spec_matches<P: Pattern>(s: Seq<char>, pat: P) -> (Seq<Seq<char>>, Seq<Seq<char>>);
```


### `spec_rmatches`

Encodes backward matching `s` by the general pattern `pat`,
returning the matches and gaps.

```rust
pub uninterp spec fn spec_rmatches<P: Pattern>(s: Seq<char>, pat: P) -> (Seq<Seq<char>>, Seq<Seq<char>>);
```


### `str_contains_post`

Encodes `str::contains` for general patterns.

```rust
pub open spec fn str_contains_post<P: Pattern>(s: Seq<char>, pat: P, ret: bool) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    ret == (seq.len() > 0)
    }
```


### `str_starts_with_post`

Encodes `str::starts_with` for general patterns.

```rust
pub open spec fn str_starts_with_post<P: Pattern>(s: Seq<char>, pat: P, ret: bool) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    ret == (seq.len() > 0 && gap.first().len() == 0)
    }
```


### `str_ends_with_post`

Encodes `str::ends_with` for general patterns.

```rust
pub open spec fn str_ends_with_post<P>(s: Seq<char>, pat: P, ret: bool) -> bool
    where
    P: Pattern,
    for<'b> <P as Pattern>::Searcher<'b>: ReverseSearcher<'b>,
{
        let (seq, gap) = spec_rmatches(s, pat);
        ret == (seq.len() > 0 && gap.first().len() == 0)
}
```


### `str_find_post`

Encodes `str::find` for general patterns.

```rust
pub open spec fn str_find_post<P: Pattern>(s: Seq<char>, pat: P, ret: Option<usize>) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& ret is None ==> seq.len() == 0
    &&& ret is Some ==> (seq.len() > 0 && ret->0 == gap.first().as_bytes().len())
    }
```


### `str_rfind_post`

Encodes `str::rfind` for general patterns.

```rust
pub open spec fn str_rfind_post<P>(s: Seq<char>, pat: P, ret: Option<usize>) -> bool
    where
    P: Pattern,
    for<'a> <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
        let (seq, gap) = spec_rmatches(s, pat);
        &&& ret is None ==> seq.len() == 0
        &&& ret is Some ==> (seq.len() > 0 && ret->0 == s.as_bytes().len() - gap.first().as_bytes().len() - seq.first().as_bytes().len())
}
```


### `str_split_iter_post`

Encodes `str::split_iter` for general patterns.

```rust
pub open spec fn str_split_iter_post<'a, P: Pattern>(s: Seq<char>, pat: P, iter_seq: Seq<&'a str>) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& iter_seq.len() == gap.len()
    &&& forall |i: int| 0 <= i < iter_seq.len() ==>
    #[trigger] iter_seq[i]@ == gap[i]
    }
```


### `str_split_inclusive_iter_post`

Encodes `str::split_inclusive_iter` for general patterns.

```rust
pub open spec fn str_split_inclusive_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
    ) -> bool {
    let (seq, gap) = spec_matches(s, pat);
```


### `str_rsplit_iter_post`

Encodes `str::rsplit_iter` for general patterns.

```rust
pub open spec fn str_rsplit_iter_post<'a, P>(s: Seq<char>, pat: P, iter_seq: Seq<&'a str>) -> bool
    where
    P: Pattern,
    <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
        let (seq, gap) = spec_rmatches(s, pat);
        &&& iter_seq.len() == gap.len()
        &&& forall |i: int| 0 <= i < iter_seq.len() ==>
                #[trigger] iter_seq[i]@ == gap[i]
}
```


### `str_split_terminator_iter_post`

Encodes `str::split_terminator_iter` for general patterns.

```rust
pub open spec fn str_split_terminator_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
    ) -> bool {
    let (seq, gap) = spec_matches(s, pat);
```
