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

// #[verifier::external_trait_specification]
// pub trait ExRead {
//     type ExternalTraitSpecificationFor: std::io::Read;

//     fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize>;
// }

impl ReadBuf for [u8] {
    
    #[verifier::external_body]
    fn read_from(&mut self, src: &[u8]) -> usize {
        // SAFETY: no out-of-bound && memory layout
        let count = std::cmp::min(src.len(), self.len());
        unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr(), count); }
        count
    }

    #[verifier::external_body]
    fn fill(&mut self, byte: u8) -> usize {
        // SAFETY: no out-of-bound && memory layout
        unsafe { core::ptr::write_bytes(self.as_mut_ptr(), byte, self.len()); }
        self.len()
    }
}

impl<const N: usize> ReadBuf for [u8; N] {
    
    #[verifier::external_body]
    fn read_from(&mut self, src: &[u8]) -> usize {
        // SAFETY: no out-of-bound && memory layout
        let count = std::cmp::min(src.len(), self.len());
        unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr(), count); }
        count
    }

    #[verifier::external_body]
    fn fill(&mut self, byte: u8) -> usize {
        // SAFETY: no out-of-bound && memory layout
        unsafe { core::ptr::write_bytes(self.as_mut_ptr(), byte, self.len()); }
        self.len()
    }
}

impl ReadBuf for Vec<u8> {
    
    #[verifier::external_body]
    fn read_from(&mut self, src: &[u8]) -> usize {
        // SAFETY: no out-of-bound && memory layout
        let count = std::cmp::min(src.len(), self.len());
        unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr(), count); }
        count
    }

    #[verifier::external_body]
    fn fill(&mut self, byte: u8) -> usize {
        // SAFETY: no out-of-bound && memory layout
        unsafe { core::ptr::write_bytes(self.as_mut_ptr(), byte, self.len()); }
        self.len()
    }
}

impl Read for &[u8] {
    /// This works by consuming the length of the slice each time it is read. 

    #[verifier::inline]
    open spec fn bytes(&self) -> Seq<u8> 
        { self@ }
    
    open spec fn read_ok(nread: nat, pre_self: Self, post_self: Self) -> bool
        { true } // no extra post-conditions
    
    #[allow(unused_variables)]
    open spec fn read_err(error: Error, pre_self: Self, post_self: Self) -> bool
        { false } // should not fail

    open spec fn read_eof(inst: Self) -> bool 
        { inst.bytes().len() == 0 }

    #[inline]
    fn read<B: ReadBuf>(&mut self, buf: &mut B) -> (res: Result<usize>) 
        ensures 
            // no short reads
            spec_unwrap(res) as int == min(old(self).bytes().len() as int, buf@.len() as int)
    {
        let nread = buf.read_from(self);
        let (_, remaining) = self.split_at(nread);
        *self = remaining;
        Ok(nread)
    }

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

    fn read_eof_is_possible() {
        let inst = [0u8; 0].as_slice();
        assert(Self::read_eof(inst));
    }

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
    fn read<B: ReadBuf>(&mut self, buf: &mut B) -> (res: Result<usize>) {
        proof { vstd::std_specs::vecdeque::axiom_spec_len(self); }
        let (front, _) = vecdeque_as_slices(self);
        let nread = buf.read_from(front);
        vecdeque_drain_front(self, nread);
        Ok(nread)
    }

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

    fn read_eof_is_possible() {
        let inst = VecDeque::<u8>::new();
        assert(Self::read_eof(inst));
    }

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
        { true } // always EOF

    #[inline]
    fn read<B: ReadBuf>(&mut self, buf: &mut B) -> (res: Result<usize>) {
        Ok(0)
    }

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

    fn read_eof_is_possible() {
        let inst = empty();
        assert(Self::read_eof(inst));
    }

}
impl ReadAdditionalSpecs for Empty {}


// XXX(xyx): Unfortunately it is currently impossible to `impl Write for &mut [u8]` because Verus 
// does not yet support trait implementation for any `&mut` type.
// This should become viable once the `new-mut-ref` feature lands.

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
        let mut src = src;
        src.read(dest).unwrap()
    }

    fn read_vecdeque_not_empty() -> (nread: usize) 
        ensures nread > 0,
    {
        let mut v = VecDeque::new();
        v.push_back(1u8);
        v.push_front(2u8);
        let mut dest = [0u8; 1];
        v.read(&mut dest).unwrap()
    }

    fn read_empty_to_end_is_noop(dest: &mut Vec<u8>) 
        ensures old(dest)@ =~= dest@,
    {
        let mut empty = empty();
        empty.read_to_end(dest);
    }
}

} // verus!