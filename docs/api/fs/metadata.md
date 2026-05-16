# `verge::fs::metadata`

Specifications for file system metadata.


## Structs


### `ExMetadata`

Metadata information about a file.

```rust
pub struct ExMetadata(Metadata);
```


## Traits


### `MetadataSpec`

The `MetadataSpec` trait specifies `Metadata`s.

```rust
pub trait MetadataSpec
```


#### `epoch`

Epoch of the file metadata when it is queried.

```rust
spec fn epoch(&self) -> int;
```


#### `path`

Path of the file metadata as it is queried.

```rust
spec fn path(&self) -> PathView;
```


#### `inv`

Invariant of the metadata.

```rust
spec fn inv(&self) -> bool;
```


## Functions


### `Metadata::is_dir`

Enable `Metadata::is_dir`.

```rust
pub assume_specification [ Metadata::is_dir ] (m: &Metadata) -> (ret: bool)
    returns
        Fs::file_is_dir(m.epoch(), m.path()),
    no_unwind
        ;
```


### `Metadata::len`

Enable `Metadata::len`.

```rust
pub assume_specification [ Metadata::len ] (m: &Metadata) -> (ret: u64)
    ensures
        ret as nat == Fs::file_when(m.epoch(), m.path()).len(),
    no_unwind
        ;
```


### `<Metadata as Clone>::clone`

Enable `<Metadata as Clone>::clone`.

```rust
pub assume_specification [ <Metadata as Clone>::clone ] (this: &Metadata) -> (ret: Metadata)
    ensures
        ret == *this,
        ;
```
