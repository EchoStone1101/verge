# `verge::str::iter`

Iterator methods and types for strings.


## Functions


### `impl_iterator!(Bytes)`

Specifies the iterator `VergeBytes` which wraps `Bytes`,
contructed via `str::bytes_iter()`.

```rust
impl_iterator!(
    [ Bytes['a] as VergeBytes['_] :: Item = u8 ]
    [ [str as View<V=Seq<char>>] :: bytes_iter via bytes ]
    (&self,) -> |seq| {
    seq == self@.as_bytes()
    }
    );
```


### `impl_double_ended_iterator!`

Specifies the iterator `VergeBytes` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    Bytes as VergeBytes ['a] :: Item = u8
    );
```


### `impl_iterator!(CharIndices)`

Specifies the iterator `VergeCharIndices` which wraps `CharIndices`,
contructed via `str::char_indices_iter()`.

```rust
impl_iterator!(
    [ CharIndices['a] as VergeCharIndices['_] :: Item = (usize, char) ]
    [ [str as View<V=Seq<char>>] :: char_indices_iter via char_indices ]
    (&self,) -> |seq| {
    seq == self@.map(|i: int, c: char| (self@.take(i).as_bytes().len() as usize, c))
    }
    );
```


### `impl_double_ended_iterator!`

Specifies the iterator `VergeCharIndices` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    CharIndices as VergeCharIndices ['a] :: Item = (usize, char)
    );
```


### `impl_iterator!(Lines)`

Specifies the iterator `VergeLines` which wraps `Lines`,
contructed via `str::lines_iter()`.

```rust
impl_iterator!(
    [ Lines['a] as VergeLines['_] :: Item = &'a str ]
    [ [str as View<V=Seq<char>>] :: lines_iter via lines ]
    (&self,) -> |seq| {
    // lines cannot have `\n`
    &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==>
    forall |j: int| #![trigger seq[i]@[j]] 0 <= j < seq[i]@.len() ==>
    !(seq[i]@[j] == '\n')
    &&& exists |nls: Seq<Seq<char>>| #![trigger nls.len()] {
    &&& nls.len() == seq.len() || nls.len() + 1 == seq.len()
    &&& nls.len() + 1 == seq.len() ==> seq.last()@.len() > 0
    // delimeters are all `\n` or `\r\n`
    &&& forall |j: int| #![trigger nls[j]] 0 <= j < nls.len() ==> {
    &&& nls[j] == seq!['\n'] || nls[j] == seq!['\r', '\n'] || (j == nls.len() - 1 && nls[j].len() == 0 )
    &&& nls[j] == seq!['\n'] ==> !seq!['\r'].is_suffix_of(seq[j]@)
    }
    // delimeters and lines make up the original string
    &&& self@ =~= join(Seq::new(seq.len(), |j: int| seq[j]@) + seq![Seq::<char>::empty()], nls)
    }
    }
    );
```


### `impl_double_ended_iterator!`

Specifies the iterator `VergeLines` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    Lines as VergeLines ['a] :: Item = &'a str
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeSplit` which wraps `Split`,
contructed via `str::split_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ Split['a, P] as VergeSplit['_, P] :: Item = &'a str
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: split_iter via split ]
    (&self, pat: P) -> |iter| {
    str_split_iter_post(self@, pat, iter)
    }
    );
```


### `impl_double_ended_iterator!(specialized_next)`

Specifies the iterator `VergeSplit` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    Split as VergeSplit ['a, P] :: Item = &'a str
    where P: Pattern,
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeSplitInclusive` which wraps `SplitInclusive`,
contructed via `str::split_inclusive_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ SplitInclusive['a, P] as VergeSplitInclusive['_, P] :: Item = &'a str
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: split_inclusive_iter via split_inclusive
    ] (&self, pat: P) -> |iter| {
    str_split_inclusive_iter_post(self@, pat, iter)
    }
    );
```


### `impl_double_ended_iterator!(specialized_next)`

Specifies the iterator `VergeSplitInclusive` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    SplitInclusive as VergeSplitInclusive ['a, P] :: Item = &'a str
    where P: Pattern,
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeRSplit` which wraps `RSplit`,
contructed via `str::rsplit_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RSplit['a, P] as VergeRSplit['_, P] :: Item = &'a str
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: rsplit_iter via rsplit
    where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ]
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, pat: P) -> |iter| {
    str_rsplit_iter_post(self@, pat, iter)
    }
    );
```


### `impl_double_ended_iterator!(specialized_next)`

Specifies the iterator `VergeRSplit` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RSplit as VergeRSplit ['a, P] :: Item = &'a str
    where P: Pattern,
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeSplitTerminator` which wraps `SplitTerminator`,
contructed via `str::split_terminator_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ SplitTerminator['a, P] as VergeSplitTerminator['_, P] :: Item = &'a str
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: split_terminator_iter via split_terminator
    ] (&self, pat: P) -> |iter| {
    str_split_terminator_iter_post(self@, pat, iter)
    }
    );
```


### `impl_double_ended_iterator!(specialized_next)`

Specifies the iterator `VergeSplitTerminator` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    SplitTerminator as VergeSplitTerminator ['a, P] :: Item = &'a str
    where P: Pattern,
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeRSplitTerminator` which wraps `RSplitTerminator`,
contructed via `str::rsplit_terminator_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RSplitTerminator['a, P] as VergeRSplitTerminator['_, P] :: Item = &'a str
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: rsplit_terminator_iter via rsplit_terminator
    where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ]
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, pat: P) -> |iter| {
    str_rsplit_terminator_iter_post(self@, pat, iter)
    }
    );
```


### `impl_double_ended_iterator!(specialized_next)`

Specifies the iterator `VergeRSplitTerminator` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RSplitTerminator as VergeRSplitTerminator ['a, P] :: Item = &'a str
    where P: Pattern,
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeSplitN` which wraps `SplitN`,
contructed via `str::splitn_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ SplitN['a, P] as VergeSplitN['_, P] :: Item = &'a str
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: splitn_iter via splitn
    ] (&self, n: usize, pat: P) -> |iter| {
    str_splitn_iter_post(self@, n, pat, iter)
    }
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeRSplitN` which wraps `RSplitN`,
contructed via `str::rsplitn_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RSplitN['a, P] as VergeRSplitN['_, P] :: Item = &'a str
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: rsplitn_iter via rsplitn
    where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ]
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, n: usize, pat: P) -> |iter| {
    str_rsplitn_iter_post(self@, n, pat, iter)
    }
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeMatches` which wraps `Matches`,
contructed via `str::matches_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ Matches['a, P] as VergeMatches['_, P] :: Item = &'a str
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: matches_iter via matches ]
    (&self, pat: P) -> |iter| {
    str_matches_iter_post(self@, pat, iter)
    }
    );
```


### `impl_double_ended_iterator!(specialized_next)`

Specifies the iterator `VergeMatches` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    Matches as VergeMatches ['a, P] :: Item = &'a str
    where P: Pattern,
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeRMatches` which wraps `RMatches`,
contructed via `str::rmatches_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RMatches['a, P] as VergeRMatches['_, P] :: Item = &'a str
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: rmatches_iter via rmatches
    where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ]
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, pat: P) -> |iter| {
    str_rmatches_iter_post(self@, pat, iter)
    }
    );
```


### `impl_double_ended_iterator!(specialized_next)`

Specifies the iterator `VergeRMatches` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RMatches as VergeRMatches ['a, P] :: Item = &'a str
    where P: Pattern,
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeMatchIndices` which wraps `MatchIndices`,
contructed via `str::match_indices_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ MatchIndices['a, P] as VergeMatchIndices['_, P] :: Item = (usize, &'a str)
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: match_indices_iter via match_indices ]
    (&self, pat: P) -> |iter| {
    str_match_indices_iter_post(self@, pat, iter)
    }
    );
```


### `impl_double_ended_iterator!(specialized_next)`

Specifies the iterator `VergeMatchIndices` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    MatchIndices as VergeMatchIndices ['a, P] :: Item = (usize, &'a str)
    where P: Pattern,
    );
```


### `impl_iterator!(verifier)`

Specifies the iterator `VergeRMatchIndices` which wraps `RMatchIndices`,
contructed via `str::rmatch_indices_iter()`.

```rust
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RMatchIndices['a, P] as VergeRMatchIndices['_, P] :: Item = (usize, &'a str)
    where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: rmatch_indices_iter via rmatch_indices
    where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ]
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, pat: P) -> |iter| {
    str_rmatch_indices_iter_post(self@, pat, iter)
    }
    );
```


### `impl_double_ended_iterator!(specialized_next)`

Specifies the iterator `VergeRMatchIndices` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RMatchIndices as VergeRMatchIndices ['a, P] :: Item = (usize, &'a str)
    where P: Pattern,
    );
```


### `impl_iterator!(SplitWhitespace)`

Specifies the iterator `VergeSplitWhitespace` which wraps `SplitWhitespace`,
contructed via `str::split_whitespace_iter()`.

```rust
impl_iterator!(
    [ SplitWhitespace['a] as VergeSplitWhitespace['_] :: Item = &'a str ]
    [ [str as View<V=Seq<char>>] :: split_whitespace_iter via split_whitespace ]
    (&self,) -> |iter| {
    str_split_whitespace_iter_post(self@, iter)
    }
    );
```


### `impl_double_ended_iterator!`

Specifies the iterator `VergeSplitWhitespace` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    SplitWhitespace as VergeSplitWhitespace ['a] :: Item = &'a str
    );
```


### `impl_iterator!(SplitAsciiWhitespace)`

Specifies the iterator `VergeSplitAsciiWhitespace` which wraps `SplitAsciiWhitespace`,
contructed via `str::split_ascii_whitespace_iter()`.

```rust
impl_iterator!(
    [ SplitAsciiWhitespace['a] as VergeSplitAsciiWhitespace['_] :: Item = &'a str ]
    [ [str as View<V=Seq<char>>] :: split_ascii_whitespace_iter via split_ascii_whitespace ]
    (&self,) -> |iter| {
    str_split_ascii_whitespace_iter_post(self@, iter)
    }
    );
```


### `impl_double_ended_iterator!`

Specifies the iterator `VergeSplitAsciiWhitespace` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    SplitAsciiWhitespace as VergeSplitAsciiWhitespace ['a] :: Item = &'a str
    );
```
