//! Default implementations of I/O traits.

#[allow(unused_imports)]
use crate::impl_maybe_generic;
use super::*;
use vstd::math::min;

verus! {

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
        });
    };
}

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
        { self.bytes().len() == 0 }

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
        { self.bytes().len() == 0 } 

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

impl ReadSpec for Stdin {

    open spec fn bytes(&self) -> Seq<u8> {
        Stdin::stream().skip(self.nbyte() as int)
    }

    open spec fn read_inv(&self) -> bool 
        { self.inv() }

    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool 
        { true } 
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool
        { true } // TODO: stdin read errors

    open spec fn read_eof(&self) -> bool 
        { true } // EOF does not imply input stream is exhausted forever 

    proof fn read_ok_is_reflexive(inst: &Self) {}

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self) {}

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error) {}

}
impl_read_for!(Stdin);

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
    
    open spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool 
        { R::read_ok(pre_self.inner(), post_self.inner()) } 
    
    open spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool 
        { R::read_err(error, pre_self.inner(), post_self.inner()) }

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

impl BufReadSpec for &[u8] {
    /// This works by using the slice itself as the buffer.

    open spec fn buffer(&self) -> Seq<u8> {
        self@
    }
}
impl_buf_read_for!(&[u8]);

// TODO: VecDeque: needs spec for VecDeque::as_slices

impl BufReadSpec for Empty {
    open spec fn buffer(&self) -> Seq<u8> {
        Seq::<u8>::empty()
    }
}
impl_buf_read_for!(Empty);

impl<B: BufRead + ?Sized> BufReadSpec for Box<B> {

    open spec fn buffer(&self) -> Seq<u8> 
        { B::buffer(&*self) }

    open spec fn consume_extra_ensures(
        pre_self: &Self, post_self: &Self, amt: usize
    ) -> bool 
        { B::consume_extra_ensures(&*pre_self, &*post_self, amt) }
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
}
impl_buf_read_for!(BufReader<R> where R: Read + std::io::Read);

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

    fn read_stdin_basic(stdin: &mut Stdin, buf: &mut [u8]) -> (nread: usize)
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

    // TODO: test BufReader
}

} // verus!