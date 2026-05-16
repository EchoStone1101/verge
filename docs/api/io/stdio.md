# `verge::io::stdio`

Specifications and lemmas for standard I/O.

Note that Verge requires any function that does standard I/O to have `&mut Stdin/Stdout/Stderr<'_>` as
an argument.

Example usage:
```rust
let (stdin, stdout, stderr) = verge::io::stdio::init();
let mut buf = vec![0u8; 32];
stdin.read(&mut buf, None);
stdout.write(&buf);
stderr.write("no error\n");
```


## Structs


### `ExStdin`

```rust
pub struct ExStdin(std::io::Stdin);
```


### `ExStdinLock`

```rust
pub struct ExStdinLock<'a>(std::io::StdinLock<'a>);
```


### `ExStdout`

```rust
pub struct ExStdout(std::io::Stdout);
```


### `ExStdoutLock`

```rust
pub struct ExStdoutLock<'a>(std::io::StdoutLock<'a>);
```


### `ExStderr`

```rust
pub struct ExStderr(std::io::Stderr);
```


### `ExStderrLock`

```rust
pub struct ExStderrLock<'a>(std::io::StderrLock<'a>);
```


## Traits


### `StdinSpec`

Specification for `std::io::Stdin` (disguised `StdinLock`).

```rust
pub trait StdinSpec
```


#### `inv`

```rust
spec fn inv(&self) -> bool;
```


#### `stream`

```rust
spec fn stream() -> Seq<u8>;
```


#### `nbyte`

```rust
spec fn nbyte(&self) -> nat;
```


#### `buf`

```rust
spec fn buf(&self) -> Seq<u8>;
```


### `StdoutSpec`

Specification for `std::io::Stdout` (disguised `StdoutLock`).

```rust
pub trait StdoutSpec
```


#### `inv`

```rust
spec fn inv(&self) -> bool;
```


#### `stream`

```rust
spec fn stream() -> Seq<u8>;
```


#### `nbyte`

```rust
spec fn nbyte(&self) -> nat;
```


#### `buf`

```rust
spec fn buf(&self) -> Seq<u8>;
```


### `StderrSpec`

Specification for `std::io::Stderr` (disguised `StderrLock`).

Note that `Stderr` is unbuffered.

```rust
pub trait StderrSpec
```


#### `inv`

```rust
spec fn inv(&self) -> bool;
```


#### `stream`

```rust
spec fn stream() -> Seq<u8>;
```


#### `nbyte`

```rust
spec fn nbyte(&self) -> nat;
```


## Functions


### `init`

Initialize unique handles for accessing `Stdin`, `Stdout`, and `Stderr`.

NOTE: this function should not be called multiple times. Any subsequent invocation
will result in a panic.

```rust
pub fn init() -> (ret: (Stdin<'static>, Stdout<'static>, Stderr<'static>))
    ensures
        ret.0.nbyte() == 0,
        ret.0.buf().len() == 0,
        ret.0.inv(),
```
