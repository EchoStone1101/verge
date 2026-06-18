//! Tests for default I/O trait implementations.

use std::collections::VecDeque;

use vstd::math::min;
use vstd::prelude::*;
use verge::io::*;
use verge::prelude::*;

verus! {

fn read_slice_should_exhaust(dest: &mut Vec<u8>, src: &[u8]) -> (nread: usize)
    ensures
        nread == min(final(dest).len() as int, src.len() as int),
{
    assert(vstd::slice::spec_slice_len(src) <= usize::MAX);
    let mut src = src;
    src.read(dest.as_mut_slice()).unwrap()
}

fn read_vecdeque_not_empty() -> (nread: usize)
    ensures nread > 0,
{
    let mut v = VecDeque::new();
    v.push_back(1u8);
    v.push_front(2u8);
    let mut dest = [0u8; 1];
    let dest_slice = vstd::array::ref_mut_array_unsizing_coercion(&mut dest);
    v.read(dest_slice).unwrap()
}

fn read_empty_to_end_is_noop(dest: &mut Vec<u8>)
    requires old(dest)@.len() <= isize::MAX,
    ensures old(dest)@ =~= final(dest)@,
{
    let mut empty = std::io::empty();
    empty.read_to_end(dest).unwrap();
}

fn read_vecdeque_to_end_should_exhaust(dest: &mut Vec<u8>, src: &mut VecDeque<u8>)
    requires
        old(dest)@.len() == 0,
        old(src)@.len() <= 1024,
    ensures
        final(dest)@ == old(src)@,
{
    src.read_to_end(dest).unwrap();
}

fn read_exact_repeat(byte: u8) -> (ret: Vec<u8>)
    ensures ret@ == seq![byte; 1024],
{
    let mut vec = vec![0u8; 1024];
    let mut tap = repeat(byte);
    tap.read_exact(vec.as_mut_slice()).unwrap();
    vec
}

fn read_stdin_basic(stdin: &mut Stdin<'_>, buf: &mut [u8]) -> (nread: usize)
    requires
        old(stdin).inv(),
    ensures
        final(stdin).nbyte() == old(stdin).nbyte() + nread,
        final(buf)@.take(nread as int)
            =~= Stdin::stream().subrange(old(stdin).nbyte() as int, final(stdin).nbyte() as int),
{
    stdin.read(buf).ok().unwrap_or(0)
}

fn read_slice_into_subrange(src: &[u8], buf: &mut [u8]) -> (nread: usize)
    requires
        old(buf)@.len() >= 4,
        src@.len() >= 2,
    ensures
        nread == min(src.len() as int, (old(buf)@.len() - 2) as int),
{
    assert(vstd::slice::spec_slice_len(src) <= usize::MAX);
    let mut src = src;
    let (_, target) = buf.split_at_mut(2);
    src.read(target).unwrap()
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

} // verus!
