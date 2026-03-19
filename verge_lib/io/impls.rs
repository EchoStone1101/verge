//! Default implementations of I/O traits.

#[allow(unused_imports)]
use crate::impl_maybe_generic;
use crate::fs::{Fs, File, FileSpec};
use super::*;
use vstd::math::{min, max};
use vstd::calc;

verus! {

// Helper macros

macro_rules! impl_read_for {
    ($ty:ty) => {
        impl_read_for!(@internal $ty []);
    };

    ($ty:ty where $($gen:tt)+) => {
        impl_read_for!(@internal $ty [$($gen)+]);
    };

    // Common implementation
    (@internal $ty:ty [$($gen:tt)*]) => {
        impl_maybe_generic!([$($gen)*] Read for $ty {
            #[inline]
            #[verifier::external_body]
            fn read<B: ReadBuf + ?Sized>(&mut self, buf: &mut B, range: Option<Range<usize>>) -> (res: Result<usize>)
                ensures Self::read_ok_extra_ensures(old(self), self, old(buf)@, buf@, range, res),
            {
                <Self as std::io::Read>::read(self, buf.as_mut(range))
            }
            #[inline]
            #[verifier::external_body]
            fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize> {
                <Self as std::io::Read>::read_to_end(self, buf)
            }
            #[inline]
            #[verifier::external_body]
            fn read_to_string(&mut self, buf: &mut String) -> Result<usize> {
                <Self as std::io::Read>::read_to_string(self, buf)
            }
            #[inline]
            #[verifier::external_body]
            fn read_exact<B: ReadBuf>(&mut self, buf: &mut B) -> Result<()> {
                <Self as std::io::Read>::read_exact(self, buf.as_mut(None))
            }
        });
    };
}

macro_rules! impl_buf_read_for {
    ($ty:ty) => {
        impl_buf_read_for!(@internal $ty []);
    };

    ($ty:ty where $($gen:tt)+) => {
        impl_buf_read_for!(@internal $ty [$($gen)+]);
    };

    // Common implementation
    (@internal $ty:ty [$($gen:tt)*]) => {
        impl_maybe_generic!([$($gen)*] BufRead for $ty {
            #[inline]
            #[verifier::external_body]
            fn fill_buf(&mut self) -> Result<&[u8]> {
                <Self as std::io::BufRead>::fill_buf(self)
            }
            #[inline]
            #[verifier::external_body]
            fn consume(&mut self, amt: usize) 
                ensures Self::consume_extra_ensures(old(self), self, amt),
            {
                <Self as std::io::BufRead>::consume(self, amt)
            }
            #[inline]
            #[verifier::external_body]
            fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> Result<usize> {
                <Self as std::io::BufRead>::read_until(self, byte, buf)
            }
            #[inline]
            #[verifier::external_body]
            fn skip_until(&mut self, byte: u8) -> Result<usize> {
                <Self as std::io::BufRead>::skip_until(self, byte)
            }
            #[inline]
            #[verifier::external_body]
            fn read_line(&mut self, buf: &mut String) -> Result<usize> {
                <Self as std::io::BufRead>::read_line(self, buf)
            }
        });
    };
}

macro_rules! impl_write_for {
    ($ty:ty) => {
        impl_write_for!(@internal $ty []);
    };

    ($ty:ty where $($gen:tt)+) => {
        impl_write_for!(@internal $ty [$($gen)+]);
    };

    // Common implementation
    (@internal $ty:ty [$($gen:tt)*]) => {
        impl_maybe_generic!([$($gen)*] Write for $ty {
            #[inline]
            #[verifier::external_body]
            fn write(&mut self, buf: &[u8]) -> (res: Result<usize>)
                ensures Self::write_ok_extra_ensures(old(self), self, buf@, res),
            {
                <Self as std::io::Write>::write(self, buf)
            }
            #[inline]
            #[verifier::external_body]
            fn flush(&mut self) -> (res: Result<()>)
                ensures Self::flush_extra_ensures(old(self), self, res),
            {
                <Self as std::io::Write>::flush(self)
            }
            #[inline]
            #[verifier::external_body]
            fn write_all(&mut self, buf: &[u8]) -> Result<()> {
                <Self as std::io::Write>::write_all(self, buf)
            }
        });
    };
}

// `Read` implementations

impl ReadSpec for &[u8] {
    /// This works by consuming the length of the slice each time it is read. 

    #[verifier::inline]
    open spec fn bytes(&self) -> Seq<u8> 
        { self@ }
    
    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool
        { true } // no extra post-conditions
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { false } // should not fail

    open spec fn read_eof(&self) -> bool 
        { self.bytes().len() == 0 }

    #[verifier::inline]
    open spec fn read_ok_extra_ensures(
        pre_self: &Self, post_self: &Self, 
        pre_buf: Seq<u8>, post_buf: Seq<u8>, 
        range: Option<Range<usize>>, res: Result<usize>,
    ) -> bool 
    { 
        // no short reads
        let (start, end) = match range {
            Some(range) => (range.start as int, range.end as int),
            _ => (0int, post_buf.len() as int),
        }; 
        spec_unwrap(res) == min(pre_self.bytes().len() as int, end - start)
    }

    proof fn read_ok_is_reflexive(inst: &Self) {}

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_read_for!(&[u8]);

impl ReadSpec for VecDeque<u8> {
    /// This works by consuming bytes from the front of the deque.

    #[verifier::inline]
    open spec fn bytes(&self) -> Seq<u8> 
        { self@ }
    
    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool
        { true } // no extra post-conditions
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { false } // should not fail

    open spec fn read_eof(&self) -> bool 
        { ReadSpec::bytes(self).len() == 0 }

    proof fn read_ok_is_reflexive(inst: &Self) {}

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_read_for!(VecDeque<u8>);

impl ReadSpec for Empty {

    #[verifier::inline]
    open spec fn bytes(&self) -> Seq<u8> 
        { Seq::<u8>::empty() }
    
    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool
        { true } // no extra post-conditions
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { false } // should not fail

    open spec fn read_eof(&self) -> bool 
        { ReadSpec::bytes(self).len() == 0 } 

    proof fn read_ok_is_reflexive(inst: &Self) {}

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_read_for!(Empty);

impl ReadSpec for Repeat {
    /// ### Proving Termination 
    /// Note that while `Repeat::read_to_end()` results in a dead loop, it is actually impossible
    /// to call it because of its `require` clause cannot be proved (`old(self).bytes().len() <= isize::MAX`). 

    uninterp spec fn bytes(&self) -> Seq<u8>;

    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool { 
        let nread = (pre_self.bytes().len() - post_self.bytes().len()) as nat;
        &&& post_self.byte() == pre_self.byte()
        &&& pre_self.bytes() =~= seq![pre_self.byte(); nread] + post_self.bytes()
    } 
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { false } // should not fail

    open spec fn read_eof(&self) -> bool 
        { false } // cannot EOF

    proof fn read_ok_is_reflexive(inst: &Self) {}

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_read_for!(Repeat);

impl ReadSpec for Stdin<'_> {

    open spec fn bytes(&self) -> Seq<u8> {
        Stdin::stream().skip(self.nbyte() as int)
    }

    open spec fn read_inv(&self) -> bool 
        { self.inv() }

    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool 
        { true } 
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { true } // No error semantics modeled yet

    open spec fn read_eof(&self) -> bool 
        { true } // EOF does not imply input stream is exhausted forever 

    proof fn read_ok_is_reflexive(inst: &Self) {}

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_read_for!(Stdin<'_>);

impl ReadSpec for File {
    /// This works by moving `self.offset()` over `Fs::file()`.

    open spec fn bytes(&self) -> Seq<u8> 
        { Fs::file(self.otime(), self.path()).skip(self.offset()) }

    open spec fn read_inv(&self) -> bool 
        { self.inv() }

    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool { 
        // the precise change to `offset` is implied by the change to `bytes()`
        &&& post_self.offset() >= pre_self.offset()
        &&& post_self.otime() == pre_self.otime()
        &&& post_self.atime() >= pre_self.atime()
        &&& post_self.path() == pre_self.path()
        &&& post_self.maxofs() == max(post_self.offset(), pre_self.maxofs())
    } 
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool { 
        // XXX: This does not mention `ErrorKind::IsADirectory` and it's by design: 
        // Verge performs checks against opening directories at `open`.
        true
    } 
    
    open spec fn read_eof(&self) -> bool { 
        // EOF does not imply file is exhausted forever 
        Fs::file_when(self.atime(), self.path()).len() == self.offset() 
    } 

    #[verifier::inline]
    open spec fn read_ok_extra_ensures(
        pre_self: &Self, post_self: &Self, 
        pre_buf: Seq<u8>, post_buf: Seq<u8>, 
        range: Option<Range<usize>>, res: Result<usize>,
    ) -> bool 
    { 
        // late-bind `Fs::file` with `Fs::file_when`
        &&& Fs::file(post_self.otime(), post_self.path()).subrange(pre_self.offset(), post_self.offset()) 
            =~= Fs::file_when(pre_self.atime(), pre_self.path()).subrange(pre_self.offset(), post_self.offset()) 
        // `File` guarantees no short reads
        &&& {
            let (start, end) = match range {
                Some(range) => (range.start as int, range.end as int),
                _ => (0int, post_buf.len() as int),
            }; 
            let rem = Fs::file_when(pre_self.atime(), pre_self.path()).len() - pre_self.offset();
            spec_unwrap(res) == min(rem, end - start)
        }
    }

    proof fn read_ok_is_reflexive(inst: &Self) {}

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_read_for!(File);

impl<R: Read + ?Sized> ReadSpec for Box<R> {

    open spec fn bytes(&self) -> Seq<u8> 
        { R::bytes(&*self) }

    open spec fn read_inv(&self) -> bool 
        { R::read_inv(&*self) }
    
    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool 
        { R::read_ok(pre_self, post_self) } 
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool 
        { R::read_err(error, pre_self, post_self) }

    open spec fn read_eof(&self) -> bool 
        { R::read_eof(self) }

    #[verifier::inline]
    open spec fn read_ok_extra_ensures(
        pre_self: &Self, post_self: &Self, 
        pre_buf: Seq<u8>, post_buf: Seq<u8>, 
        range: Option<Range<usize>>, res: Result<usize>,
    ) -> bool { 
        R::read_ok_extra_ensures(
            &*pre_self, &*post_self,
            pre_buf, post_buf,
            range, res,
        ) 
    }

    proof fn read_ok_is_reflexive(inst: &Self) {
        R::read_ok_is_reflexive(inst);
    }

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {
        R::read_ok_is_composable(pre_self, mid_self, post_self);
    }

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {
        R::read_ok_err_are_composable(pre_self, mid_self, post_self, error);
    }

}
impl_read_for!(Box<R> where R: Read + ?Sized + std::io::Read);

impl<R: Read> ReadSpec for BufReader<R> {
    /// This works by first reading from the internal buffer, then (if empty) calling 
    /// `read` on the inner read instance.

    open spec fn bytes(&self) -> Seq<u8> 
        { self.valid_buf() + self.inner().bytes() }

    open spec fn read_inv(&self) -> bool 
        { self.inv() && self.inner().read_inv() }
    
    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool { 
        &&& post_self.inner().bytes().is_suffix_of(pre_self.inner().bytes())
        &&& R::read_ok(pre_self.inner(), post_self.inner()) 
    } 
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool { 
        &&& post_self.inner().bytes().is_suffix_of(pre_self.inner().bytes())
        &&& R::read_err(error, pre_self.inner(), post_self.inner()) 
    }

    open spec fn read_eof(&self) -> bool 
        { self.valid_buf().len() == 0 && R::read_eof(self.inner()) }

    proof fn read_ok_is_reflexive(inst: &Self) {
        R::read_ok_is_reflexive(inst.inner());
    }

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {
        R::read_ok_is_composable(pre_self.inner(), mid_self.inner(), post_self.inner());
    }

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {
        R::read_ok_err_are_composable(pre_self.inner(), mid_self.inner(), post_self.inner(), error);
    }

}
impl_read_for!(BufReader<R> where R: Read + std::io::Read);

impl<T: AsRef<[u8]> + View<V = Seq<u8>>> ReadSpec for Cursor<T> {
    /// This works by moving the cursor within the buffer.

    open spec fn bytes(&self) -> Seq<u8> 
        { self.inner()@.skip(min(self.inner()@.len() as int, self.pos() as int)) }
    
    open spec fn read_inv(&self) -> bool 
        { self.inv() }

    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool 
        { post_self.inner()@.len() == pre_self.inner()@.len() } 
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool 
        { false } // never fails

    open spec fn read_eof(&self) -> bool 
        { self.pos() >= self.inner()@.len() }

    #[verifier::inline]
    open spec fn read_ok_extra_ensures(
        pre_self: &Self, post_self: &Self, 
        pre_buf: Seq<u8>, post_buf: Seq<u8>, 
        range: Option<Range<usize>>, res: Result<usize>,
    ) -> bool 
    { 
        // no short reads
        let (start, end) = match range {
            Some(range) => (range.start as int, range.end as int),
            _ => (0int, post_buf.len() as int),
        }; 
        spec_unwrap(res) == min(pre_self.bytes().len() as int, end - start)
    }

    proof fn read_ok_is_reflexive(inst: &Self) {}

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_read_for!(Cursor<T> where T: AsRef<[u8]> + View<V = Seq<u8>>);


// `BufRead` implementations

impl BufReadSpec for &[u8] {
    /// This works by using the slice itself as the buffer.

    open spec fn buffer(&self) -> Seq<u8> {
        self@
    }

    proof fn buffer_is_prefix_of_bytes(inst: &Self) {}
}
impl_buf_read_for!(&[u8]);

impl BufReadSpec for Empty {
    open spec fn buffer(&self) -> Seq<u8> {
        Seq::<u8>::empty()
    }

    proof fn buffer_is_prefix_of_bytes(inst: &Self) {}
}
impl_buf_read_for!(Empty);

impl BufReadSpec for Stdin<'_> {
    open spec fn buffer(&self) -> Seq<u8> {
        self.buf()
    }

    proof fn buffer_is_prefix_of_bytes(inst: &Self) {}
}
impl_buf_read_for!(Stdin<'_>);

impl<B: BufRead + ?Sized> BufReadSpec for Box<B> {

    open spec fn buffer(&self) -> Seq<u8> 
        { B::buffer(&*self) }

    open spec fn consume_extra_ensures(
        pre_self: &Self, post_self: &Self, amt: usize
    ) -> bool 
        { B::consume_extra_ensures(&*pre_self, &*post_self, amt) }

    proof fn buffer_is_prefix_of_bytes(inst: &Self) {
        B::buffer_is_prefix_of_bytes(&*inst)
    }
}
impl_buf_read_for!(Box<B> where B: BufRead + ?Sized + std::io::BufRead);

impl<R: Read> BufReadSpec for BufReader<R> {

    open spec fn buffer(&self) -> Seq<u8> {
        self.valid_buf()
    }

    open spec fn consume_extra_ensures(
        pre_self: &Self, post_self: &Self, amt: usize
    ) -> bool 
    { 
        pre_self.inner() == post_self.inner()
    }

    proof fn buffer_is_prefix_of_bytes(inst: &Self) {}
}
impl_buf_read_for!(BufReader<R> where R: Read + std::io::Read);

impl<T: AsRef<[u8]> + View<V = Seq<u8>>> BufReadSpec for Cursor<T> {
    /// This works by using the unread part itself as the buffer.

    open spec fn buffer(&self) -> Seq<u8> {
        self.bytes()
    }

    open spec fn consume_extra_ensures(
        pre_self: &Self, post_self: &Self, amt: usize
    ) -> bool 
    { 
        pre_self.inner() == post_self.inner()
    }

    proof fn buffer_is_prefix_of_bytes(inst: &Self) {}
}
impl_buf_read_for!(Cursor<T> where T: AsRef<[u8]> + View<V = Seq<u8>>);


// `Write` implementations

impl WriteSpec for Vec<u8> {
    /// This works by appending bytes to the end of the vector.

    #[verifier::inline]
    open spec fn bytes(&self) -> Seq<u8> 
        { self@ }

    open spec fn buffer(&self) -> Seq<u8> 
        { Seq::<u8>::empty() }

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool
        { true } // no extra post-conditions
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { false } // should not fail
    
    open spec fn write_eof(&self) -> bool 
        { false } // never EOF
    
    #[verifier::inline]
    open spec fn write_ok_extra_ensures(pre_self: &Self, post_self: &Self, buf: Seq<u8>, res: Result<usize>) -> bool { 
        // no short writes
        spec_unwrap(res) == buf.len()
    }

    #[verifier::inline]
    open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool { 
        // flush cannot fail 
        res.is_ok() && *post_self == *pre_self
    }

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {}

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_write_for!(Vec<u8>);

impl WriteSpec for VecDeque<u8> {
    /// This works by appending bytes to the end of the `VecDeque`.

    #[verifier::inline]
    open spec fn bytes(&self) -> Seq<u8> 
        { self@ }

    open spec fn buffer(&self) -> Seq<u8> 
        { Seq::<u8>::empty() }

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool
        { true } // no extra post-conditions
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { false } // should not fail
    
    open spec fn write_eof(&self) -> bool 
        { false } // never EOF
    
    #[verifier::inline]
    open spec fn write_ok_extra_ensures(pre_self: &Self, post_self: &Self, buf: Seq<u8>, res: Result<usize>) -> bool { 
        // no short writes
        spec_unwrap(res) == buf.len()
    }

    #[verifier::inline]
    open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool { 
        // flush cannot fail 
        res.is_ok() && *post_self == *pre_self
    }

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {}

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_write_for!(VecDeque<u8>);

impl WriteSpec for Stdout<'_> {

    open spec fn bytes(&self) -> Seq<u8> {
        Stdout::stream().take(self.nbyte() as int)
    }

    open spec fn buffer(&self) -> Seq<u8> {
        self.buf()
    }

    open spec fn write_inv(&self) -> bool 
        { self.inv() }

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool 
        { true } 
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { true } // No error semantics modeled yet

    open spec fn write_eof(&self) -> bool 
        { true } // Typically not for TTY or files, so not modeled yet

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {}

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_write_for!(Stdout<'_>);

impl WriteSpec for Stderr<'_> {

    open spec fn bytes(&self) -> Seq<u8> {
        Stderr::stream().take(self.nbyte() as int)
    }

    open spec fn buffer(&self) -> Seq<u8> {
        Seq::<u8>::empty() // `Stderr` is unbuffered
    }

    open spec fn write_inv(&self) -> bool 
        { self.inv() }

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool 
        { true } 
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { true } // No error semantics modeled yet

    open spec fn write_eof(&self) -> bool 
        { true } // Typically not for TTY or files, so not modeled yet

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {}

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_write_for!(Stderr<'_>);

impl WriteSpec for File {
    /// This works by moving `self.offset()` over `Fs::file()`.

    open spec fn bytes(&self) -> Seq<u8> 
        { Fs::file(self.otime(), self.path()).take(self.offset()) }

    open spec fn buffer(&self) -> Seq<u8> 
        { Seq::<u8>::empty() } // `File` is unbuffered

    open spec fn write_inv(&self) -> bool 
        { self.inv() }

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool { 
        // the precise change to `offset` is implied by the change to `bytes()`
        &&& post_self.offset() >= pre_self.offset()
        &&& post_self.otime() == pre_self.otime()
        &&& post_self.atime() >= pre_self.atime()
        &&& post_self.path() == pre_self.path() 
        &&& post_self.maxofs() == max(post_self.offset(), pre_self.maxofs())
    } 
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool 
        { true }

    open spec fn write_eof(&self) -> bool 
        { true } // Typically not for TTY or files, so not modeled yet

    #[verifier::inline]
    open spec fn write_ok_extra_ensures(pre_self: &Self, post_self: &Self, buf: Seq<u8>, res: Result<usize>) -> bool { 
        // late-bind `Fs::file` with `Fs::file_when`
        &&& Fs::file(post_self.otime(), post_self.path()).subrange(pre_self.offset(), post_self.offset()) 
            =~= Fs::file_when(post_self.atime(), post_self.path()).subrange(pre_self.offset(), post_self.offset()) 
    }

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {}

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_write_for!(File);

impl<W: Write> WriteSpec for Box<W> {

    open spec fn bytes(&self) -> Seq<u8> 
        { W::bytes(&*self) }

    open spec fn buffer(&self) -> Seq<u8> 
        { W::buffer(&*self) }

    open spec fn write_inv(&self) -> bool
        { W::write_inv(&*self) }

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool
        { W::write_ok(pre_self, post_self) } 
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { W::write_err(error, pre_self, post_self) } 
    
    open spec fn write_eof(&self) -> bool 
        { W::write_eof(self) } 
    
    #[verifier::inline]
    open spec fn write_ok_extra_ensures(pre_self: &Self, post_self: &Self, buf: Seq<u8>, res: Result<usize>) -> bool { 
        W::write_ok_extra_ensures(&*pre_self, &*post_self, buf, res)
    }

    #[verifier::inline]
    open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool { 
        W::flush_extra_ensures(&*pre_self, &*post_self, res)
    }

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {
        W::buffer_is_suffix_of_bytes(&*inst)
    }

    proof fn write_ok_is_reflexive(inst: &Self) {
        W::write_ok_is_reflexive(&*inst)
    }

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {
        W::write_ok_is_composable(&*pre_self, &*mid_self, &*post_self)
    }

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {
        W::write_ok_err_are_composable(&*pre_self, &*mid_self, &*post_self, error)
    }

}
impl_write_for!(Box<W> where W: Write + std::io::Write);

impl<W: Write + std::io::Write> WriteSpec for BufWriter<W> {
    /// This works by first writing into the internal buffer, then (if full) flushing to 
    /// the inner write instance by calling `write`.

    open spec fn bytes(&self) -> Seq<u8> 
        { self.inner().bytes() + self.valid_buf() }

    open spec fn buffer(&self) -> Seq<u8> 
        { self.valid_buf() }

    open spec fn write_inv(&self) -> bool
        { self.inv() && self.inner().write_inv() }

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool { 
        &&& pre_self.inner().bytes().is_prefix_of(post_self.inner().bytes())
        &&& W::write_ok(pre_self.inner(), post_self.inner()) 
    } 
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool { 
        &&& pre_self.inner().bytes().is_prefix_of(post_self.inner().bytes())
        &&& W::write_err(error, pre_self.inner(), post_self.inner()) 
    } 
    
    open spec fn write_eof(&self) -> bool 
        { W::write_eof(self.inner()) } 

    #[verifier::inline]
    open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool { 
        &&& WriteSpec::buffer(pre_self).len() == 0 ==> pre_self.inner() == post_self.inner() // no writes if no buffer to flush
        &&& W::flush_extra_ensures(pre_self.inner(), post_self.inner(), res)
    }

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {
        W::write_ok_is_reflexive(inst.inner())
    }

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {
        W::write_ok_is_composable(pre_self.inner(), mid_self.inner(), post_self.inner())
    }

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {
        W::write_ok_err_are_composable(pre_self.inner(), mid_self.inner(), post_self.inner(), error)
    }

}
impl_write_for!(BufWriter<W> where W: Write + std::io::Write);

impl<W: Write + std::io::Write> WriteSpec for LineWriter<W> {
    /// This works by first writing into the internal buffer, then (if full or encounters a new line) 
    /// flushing to the inner write instance by calling `write`.

    open spec fn bytes(&self) -> Seq<u8> 
        { self.inner().bytes() + self.valid_buf() }

    open spec fn buffer(&self) -> Seq<u8> 
        { self.valid_buf() }

    open spec fn write_inv(&self) -> bool
        { self.inv() && self.inner().write_inv() }

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool { 
        &&& pre_self.inner().bytes().is_prefix_of(post_self.inner().bytes())
        &&& W::write_ok(pre_self.inner(), post_self.inner()) 
    } 
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool { 
        &&& pre_self.inner().bytes().is_prefix_of(post_self.inner().bytes())
        &&& W::write_err(error, pre_self.inner(), post_self.inner()) 
    } 
    
    open spec fn write_eof(&self) -> bool 
        { W::write_eof(self.inner()) } 

    #[verifier::inline]
    open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool { 
        &&& WriteSpec::buffer(pre_self).len() == 0 ==> pre_self.inner() == post_self.inner() // no writes if no buffer to flush
        &&& W::flush_extra_ensures(pre_self.inner(), post_self.inner(), res)
    }

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {
        W::write_ok_is_reflexive(inst.inner())
    }

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {
        W::write_ok_is_composable(pre_self.inner(), mid_self.inner(), post_self.inner())
    }

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {
        W::write_ok_err_are_composable(pre_self.inner(), mid_self.inner(), post_self.inner(), error)
    }

}
impl_write_for!(LineWriter<W> where W: Write + std::io::Write);

impl<const N: usize> WriteSpec for Cursor<[u8; N]> {
    /// This works by moving the cursor within the buffer.

    open spec fn bytes(&self) -> Seq<u8> 
        { self.inner()@.take(self.pos() as int) }

    open spec fn buffer(&self) -> Seq<u8> 
        { Seq::<u8>::empty() } // `Cursor` is unbuffered
    
    open spec fn write_inv(&self) -> bool 
        { self.inv() && self.pos() <= N } // Verge requires `pos()` to be in-range for `write`

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool 
        { true } // no extra post-conditions 
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool 
        { false } // never fails
    
    open spec fn write_eof(&self) -> bool 
        { self.pos() >= N } 

    #[verifier::inline]
    open spec fn write_ok_extra_ensures(pre_self: &Self, post_self: &Self, buf: Seq<u8>, res: Result<usize>) -> bool { 
        // no short writes up to N 
        spec_unwrap(res) == min(buf.len() as int, N - pre_self.pos())
    }

    #[verifier::inline]
    open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool { 
        // flush cannot fail 
        res.is_ok() && *post_self == *pre_self
    }

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {}

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_write_for!(Cursor<[u8; N]> where const N: usize);

impl WriteSpec for Cursor<Box<[u8]>> {
    /// This works by moving the cursor within the buffer.

    open spec fn bytes(&self) -> Seq<u8> 
        { self.inner()@.take(self.pos() as int) }

    open spec fn buffer(&self) -> Seq<u8> 
        { Seq::<u8>::empty() } // `Cursor` is unbuffered
    
    open spec fn write_inv(&self) -> bool 
        { self.inv() && self.pos() <= self.inner()@.len() } // Verge requires `pos()` to be in-range for `write`

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool 
        {  post_self.inner()@.len() == pre_self.inner()@.len() } 
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool 
        { false } // never fails
    
    open spec fn write_eof(&self) -> bool 
        { self.pos() >= self.inner()@.len() } 

    #[verifier::inline]
    open spec fn write_ok_extra_ensures(pre_self: &Self, post_self: &Self, buf: Seq<u8>, res: Result<usize>) -> bool { 
        // no short writes up to N 
        spec_unwrap(res) == min(buf.len() as int, pre_self.inner()@.len() - pre_self.pos())
    }

    #[verifier::inline]
    open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool { 
        // flush cannot fail 
        res.is_ok() && *post_self == *pre_self
    }

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {}

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_write_for!(Cursor<Box<[u8]>>);

impl WriteSpec for Cursor<Vec<u8>> {
    /// This works by moving the cursor within the buffer, growing the vector if needed.

    open spec fn bytes(&self) -> Seq<u8> 
        { self.inner()@.take(self.pos() as int) }

    open spec fn buffer(&self) -> Seq<u8> 
        { Seq::<u8>::empty() } // `Cursor` is unbuffered
    
    open spec fn write_inv(&self) -> bool 
        { self.inv() && self.pos() <= self.inner()@.len() } // Verge requires `pos()` to be in-range for `write`

    open spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool { 
        &&& pre_self.pos() <= post_self.pos()
        &&& pre_self.inner()@.len() <= post_self.inner()@.len()
        &&& post_self.pos() <= pre_self.inner()@.len() 
            ==> post_self.inner()@.len() == pre_self.inner()@.len() 
        &&& post_self.pos() > pre_self.inner()@.len() 
            ==> post_self.inner()@.len() == post_self.pos()
    } 
    
    open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool 
        { false } // never fails, so long as `pos()` is within `usize` (guaranteed by `inv()`)
    
    open spec fn write_eof(&self) -> bool 
        { false } // never EOF

    #[verifier::inline]
    open spec fn write_ok_extra_ensures(pre_self: &Self, post_self: &Self, buf: Seq<u8>, res: Result<usize>) -> bool { 
        // no short writes 
        spec_unwrap(res) == buf.len()
    }

    #[verifier::inline]
    open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool { 
        // flush cannot fail 
        res.is_ok() && *post_self == *pre_self
    }

    proof fn buffer_is_suffix_of_bytes(inst: &Self) {}

    proof fn write_ok_is_reflexive(inst: &Self) {}

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_write_for!(Cursor<Vec<u8>>);

mod tests {
    use super::*;

    fn read_slice_should_exhaust(dest: &mut Vec<u8>, src: &[u8]) -> (nread: usize)
        ensures
            nread == min(dest.len() as int, src.len() as int),
    {
        assert(vstd::slice::spec_slice_len(src) <= usize::MAX);
        let mut src = src;
        src.read(dest, None).unwrap()
    }

    fn read_vecdeque_not_empty() -> (nread: usize) 
        ensures nread > 0,
    {
        let mut v = VecDeque::new();
        v.push_back(1u8);
        v.push_front(2u8);
        let mut dest = [0u8; 1];
        v.read(&mut dest, None).unwrap()
    }

    fn read_empty_to_end_is_noop(dest: &mut Vec<u8>)
        requires old(dest)@.len() <= isize::MAX,
        ensures old(dest)@ =~= dest@,
    {
        let mut empty = std::io::empty();
        empty.read_to_end(dest).unwrap();
    }

    fn read_vecdeque_to_end_should_exhaust(dest: &mut Vec<u8>, src: &mut VecDeque<u8>)
        requires
            old(dest)@.len() == 0,
            old(src)@.len() <= 1024,
        ensures
            dest@ == old(src)@,
    {
        src.read_to_end(dest).unwrap();
    }

    fn read_exact_repeat(byte: u8) -> (ret: Vec<u8>)
        ensures ret@ == seq![byte; 1024],
    {
        let mut vec = vec![0u8; 1024];
        let mut tap = repeat(byte);
        tap.read_exact(&mut vec).unwrap();
        vec
    }

    fn read_stdin_basic(stdin: &mut Stdin<'_>, buf: &mut [u8]) -> (nread: usize)
        requires
            old(stdin).inv(),
        ensures 
            stdin.nbyte() == old(stdin).nbyte() + nread,
            buf@.take(nread as int) 
                =~= Stdin::stream().subrange(old(stdin).nbyte() as int, stdin.nbyte() as int),
    {
        stdin.read(buf, None).ok().unwrap_or(0)
    }

    fn read_slice_until(src: &[u8], delim: u8) 
        requires src@.len() <= 1024,
    {
        let mut src = src;
        let mut buf = Vec::<u8>::new();
        let cnt = src.read_until(delim, &mut buf).unwrap();
        if cnt > 2 && src.len() > 0 {
            assert(buf[cnt - 1] == delim);
            assert(buf[0] != delim);
        }
    }

    // TODO(rilin): test more functions
}

} // verus!