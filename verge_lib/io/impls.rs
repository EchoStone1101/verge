//! Default implementations of I/O traits.

#[allow(unused_imports)]
use super::*;

verus! {

#[verifier::external_body]
fn vecdeque_as_slices<T>(deque: &VecDeque<T>) -> (ret: (&[T], &[T])) 
    ensures 
        deque@ =~= ret.0@ + ret.1@,
        deque@.len() > 0 ==> ret.0@.len() > 0,
{
    // SOUNDNESS: see https://doc.rust-lang.org/1.93.0/src/alloc/collections/vec_deque/mod.rs.html#103 
    deque.as_slices()
}

#[verifier::external_body]
fn vecdeque_drain_front<T>(deque: &mut VecDeque<T>, n: usize)
    requires 
        n <= old(deque)@.len(),
    ensures 
        deque@ =~= old(deque)@.skip(n as int),
{
    // SOUNDNESS: pre-condition
    _ = deque.drain(..n);
}

unsafe impl ReadBuf for [u8] {
    
    #[verifier::external_body]
    fn read_from(&mut self, src: &[u8], range: Option<Range<usize>>) -> usize {
        // SAFETY: no out-of-bound && memory layout
        let (start, end) = match range {
            Some(range) => (range.start, range.end),
            _ => (0, self.len()),
        };
        let count = std::cmp::min(src.len(), end - start);
        unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr().add(start), count); }
        count
    }

    #[verifier::external_body]
    fn fill(&mut self, byte: u8, range: Option<Range<usize>>) -> usize {
        // SAFETY: no out-of-bound && memory layout
        let (start, end) = match range {
            Some(range) => (range.start, range.end),
            _ => (0, self.len()),
        };
        unsafe { core::ptr::write_bytes(self.as_mut_ptr().add(start), byte, end - start); }
        end - start
    }

    fn buf_len(&self) -> usize {
        self.len()
    }

    #[verifier::external_body]
    unsafe fn as_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_ptr()
    }

}

unsafe impl<const N: usize> ReadBuf for [u8; N] {
    
    #[verifier::external_body]
    fn read_from(&mut self, src: &[u8], range: Option<Range<usize>>) -> usize {
        // SAFETY: no out-of-bound && memory layout
        let (start, end) = match range {
            Some(range) => (range.start, range.end),
            _ => (0, self.len()),
        };
        let count = std::cmp::min(src.len(), end - start);
        unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr().add(start), count); }
        count
    }

    #[verifier::external_body]
    fn fill(&mut self, byte: u8, range: Option<Range<usize>>) -> usize {
        // SAFETY: no out-of-bound && memory layout
        let (start, end) = match range {
            Some(range) => (range.start, range.end),
            _ => (0, self.len()),
        };
        unsafe { core::ptr::write_bytes(self.as_mut_ptr().add(start), byte, end - start); }
        end - start
    }

    fn buf_len(&self) -> usize {
        self.len()
    }

    #[verifier::external_body]
    unsafe fn as_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_slice().as_mut_ptr()
    }

}

unsafe impl ReadBuf for Vec<u8> {
    
    #[verifier::external_body]
    fn read_from(&mut self, src: &[u8], range: Option<Range<usize>>) -> usize {
        // SAFETY: no out-of-bound && memory layout
        let (start, end) = match range {
            Some(range) => (range.start, range.end),
            _ => (0, self.len()),
        };
        let count = std::cmp::min(src.len(), end - start);
        unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr().add(start), count); }
        count
    }

    #[verifier::external_body]
    fn fill(&mut self, byte: u8, range: Option<Range<usize>>) -> usize {
        // SAFETY: no out-of-bound && memory layout
        let (start, end) = match range {
            Some(range) => (range.start, range.end),
            _ => (0, self.len()),
        };
        unsafe { core::ptr::write_bytes(self.as_mut_ptr().add(start), byte, end - start); }
        end - start
    }

    fn buf_len(&self) -> usize {
        self.len()
    }

    #[verifier::external_body]
    unsafe fn as_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_ptr()
    }

}

impl Read for &[u8] {
    /// This works by consuming the length of the slice each time it is read. 

    #[verifier::inline]
    open spec fn bytes(&self) -> Seq<u8> 
        { self@ }
    
    open spec fn read_ok(nread: nat, pre_self: Self, post_self: Self) -> bool
        { true } // no extra post-conditions
    
    open spec fn read_err(error: Error, pre_self: Self, post_self: Self) -> bool
        { false } // should not fail

    open spec fn read_eof(inst: Self) -> bool 
        { inst.bytes().len() == 0 }

    #[inline]
    fn read<B: ReadBuf + ?Sized>(&mut self, buf: &mut B, range: Option<Range<usize>>) -> (res: Result<usize>) 
        ensures 
            // no short reads
            ({
                let (start, end) = match range {
                    Some(range) => (range.start as int, range.end as int),
                    _ => (0int, buf@.len() as int),
                }; 
                spec_unwrap(res) == min(old(self).bytes().len() as int, end - start)
            })
    {
        let nread = buf.read_from(self, range);
        let (_, remaining) = self.split_at(nread);
        *self = remaining;
        Ok(nread)
    }

    proof fn read_ok_is_reflexive(inst: Self) {}

    proof fn read_ok_is_composable(
        pre_self: Self, nread1: nat, 
        mid_self: Self, nread2: nat, 
        post_self: Self,
    ) {}

    proof fn read_ok_err_are_composable(
        pre_self: Self, nread: nat, 
        mid_self: Self, error: Error,
        post_self: Self,
    ) {}

}
impl ReadAdditionalSpecs for &[u8] {}

impl Read for VecDeque<u8> {
    /// This works by consuming bytes from the front of the deque.

    #[verifier::inline]
    open spec fn bytes(&self) -> Seq<u8> 
        { self@ }
    
    open spec fn read_ok(nread: nat, pre_self: Self, post_self: Self) -> bool
        { true } // no extra post-conditions
    
    open spec fn read_err(error: Error, pre_self: Self, post_self: Self) -> bool
        { false } // should not fail

    open spec fn read_eof(inst: Self) -> bool 
        { inst.bytes().len() == 0 }

    #[inline]
    fn read<B: ReadBuf + ?Sized>(&mut self, buf: &mut B, range: Option<Range<usize>>) -> (res: Result<usize>) {
        proof { vstd::std_specs::vecdeque::axiom_spec_len(self); }
        let (front, _) = vecdeque_as_slices(self);
        let nread = buf.read_from(front, range);
        vecdeque_drain_front(self, nread);
        Ok(nread)
    }

    proof fn read_ok_is_reflexive(inst: Self) {}

    proof fn read_ok_is_composable(
        pre_self: Self, nread1: nat, 
        mid_self: Self, nread2: nat, 
        post_self: Self,
    ) {}

    proof fn read_ok_err_are_composable(
        pre_self: Self, nread: nat, 
        mid_self: Self, error: Error,
        post_self: Self,
    ) {}

}
impl ReadAdditionalSpecs for VecDeque<u8> {}

impl Read for Empty {

    #[verifier::inline]
    open spec fn bytes(&self) -> Seq<u8> 
        { Seq::<u8>::empty() }
    
    open spec fn read_ok(nread: nat, pre_self: Self, post_self: Self) -> bool
        { true } // no extra post-conditions
    
    open spec fn read_err(error: Error, pre_self: Self, post_self: Self) -> bool
        { false } // should not fail

    open spec fn read_eof(inst: Self) -> bool 
        { inst.bytes().len() == 0 } 

    #[inline]
    fn read<B: ReadBuf + ?Sized>(&mut self, buf: &mut B, range: Option<Range<usize>>) -> (res: Result<usize>) {
        Ok(0)
    }

    proof fn read_ok_is_reflexive(inst: Self) {}

    proof fn read_ok_is_composable(
        pre_self: Self, nread1: nat, 
        mid_self: Self, nread2: nat, 
        post_self: Self,
    ) {}

    proof fn read_ok_err_are_composable(
        pre_self: Self, nread: nat, 
        mid_self: Self, error: Error,
        post_self: Self,
    ) {}

}
impl ReadAdditionalSpecs for Empty {}

impl Read for Repeat {
    /// ### Proving Termination 
    /// Note that while `Repeat::read_to_end()` results in a dead loop, it is actually impossible
    /// to call it because of its `require` clause cannot be proved (`old(self).bytes().len() <= usize::MAX`). 

    uninterp spec fn bytes(&self) -> Seq<u8>;

    open spec fn read_ok(nread: nat, pre_self: Self, post_self: Self) -> bool { 
        &&& post_self.byte() == pre_self.byte()
        &&& nread <= pre_self.bytes().len()
        &&& pre_self.bytes() =~= seq![pre_self.byte(); nread] + post_self.bytes()
    } 
    
    open spec fn read_err(error: Error, pre_self: Self, post_self: Self) -> bool
        { false } // should not fail

    open spec fn read_eof(inst: Self) -> bool 
        { false } // cannot EOF

    #[inline]
    fn read<B: ReadBuf + ?Sized>(&mut self, buf: &mut B, range: Option<Range<usize>>) -> (res: Result<usize>) {        
        let nread = buf.fill(self.0, range);
        // SOUNDNESS: by the semantics of `fill`
        assume(Self::read_ok(nread as nat, *old(self), *self));
        Ok(nread)
    }

    proof fn read_ok_is_reflexive(inst: Self) {}

    proof fn read_ok_is_composable(
        pre_self: Self, nread1: nat, 
        mid_self: Self, nread2: nat, 
        post_self: Self,
    ) {}

    proof fn read_ok_err_are_composable(
        pre_self: Self, nread: nat, 
        mid_self: Self, error: Error,
        post_self: Self,
    ) {}
}
impl ReadAdditionalSpecs for Repeat {}

impl Read for Stdin {

    open spec fn bytes(&self) -> Seq<u8> {
        Stdin::stream().skip(self.nbyte() as int)
    }

    open spec fn read_inv(&self) -> bool 
        { self.nbyte() <= Stdin::stream().len() }

    open spec fn read_ok(nread: nat, pre_self: Self, post_self: Self) -> bool 
        { true } 
    
    open spec fn read_err(error: Error, pre_self: Self, post_self: Self) -> bool
        { true } 

    open spec fn read_eof(inst: Self) -> bool 
        { true } // EOF does not imply input stream is empty forever 
                 // TODO: refine when input stream is piped; then it does mean empty forever

    fn read<B: ReadBuf + ?Sized>(&mut self, buf: &mut B, range: Option<Range<usize>>) -> (res: Result<usize>) {        
        self.read_raw(buf, range)
    }

    proof fn read_ok_is_reflexive(inst: Self) {}

    proof fn read_ok_is_composable(
        pre_self: Self, nread1: nat, 
        mid_self: Self, nread2: nat, 
        post_self: Self,
    ) {}

    proof fn read_ok_err_are_composable(
        pre_self: Self, nread: nat, 
        mid_self: Self, error: Error,
        post_self: Self,
    ) {}
}
impl ReadAdditionalSpecs for Stdin {}

// TODO: BufRead and BufReader? File?




// impl Write for Empty, Sink, Vec<u8>, VecDeque<u8>; BufWriter; Stdout; PipeWriter; File


// impl Write for [u8] {
//     /// This works by overwriting the existing bytes in the slice.

//     #[verifier::inline]
//     open spec fn bytes(&self) -> Seq<u8> 
//         { self@ }

//     open spec fn write_ok(nwritten: usize, pre_self: &Self, post_self: &Self, buf: Seq<u8>) -> bool
//     {
//         post_self.bytes() =~= buf.take(nwritten as int) + pre_self.bytes().skip(nwritten as int)
//     }
    
//     #[allow(unused)]
//     open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self, buf: Seq<u8>) -> bool 
//         { false } // should never fail

//     #[inline]
//     fn write(&mut self, buf: &[u8]) -> (res: Result<usize>)
//         ensures
//             ({
//                 match res {
//                     Ok(nwritten) => 
//                         nwritten <= buf.len() 
//                         && Self::write_ok(nwritten, old(self), self, buf@),
//                     Err(error) => Self::write_err(error, old(self), self, buf@),
//                 }
//             }),
//     {
//         let amt = if buf.len() < self.len() { buf.len() } else { self.len() };
//         copy_from_slice_partial(self, buf);
//         Ok(amt)
//     }
// }

// impl Write for Vec<u8> {
//     /// This works by appending the written bytes to the vector, potentially growing it.

//     #[verifier::inline]
//     open spec fn bytes(&self) -> Seq<u8> 
//         { self@ }

//     open spec fn write_ok(nwritten: usize, pre_self: &Self, post_self: &Self, buf: Seq<u8>) -> bool
//     {
//         &&& nwritten == buf.len()
//         &&& post_self.bytes() =~= pre_self.bytes() + buf
//     }
    
//     #[allow(unused)]
//     open spec fn write_err(error: Error, pre_self: &Self, post_self: &Self, buf: Seq<u8>) -> bool 
//         { false } // should never fail

//     #[inline]
//     fn write(&mut self, buf: &[u8]) -> (res: Result<usize>)
//         ensures
//             ({
//                 match res {
//                     Ok(nwritten) => 
//                         nwritten <= buf.len() 
//                         && Self::write_ok(nwritten, old(self), self, buf@),
//                     Err(error) => Self::write_err(error, old(self), self, buf@),
//                 }
//             }),
//     {
//         self.extend_from_slice(buf);
//         Ok(buf.len())
//     }

// }

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
        let mut empty = empty();
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
        ensures 
            stdin.nbyte() == old(stdin).nbyte() + nread,
            buf@.take(nread as int) 
                =~= Stdin::stream().subrange(old(stdin).nbyte() as int, stdin.nbyte() as int),
    {
        proof { use_type_invariant(&*stdin) }
        stdin.read(buf, None).ok().unwrap_or(0)
    }
}

} // verus!