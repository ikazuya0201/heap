#[cfg(test)]
extern crate std;
#[cfg(test)]
use std::dbg;

use core::marker::PhantomData;

use generic_array::{ArrayLength, GenericArray};

use crate::vec::Vec;

#[derive(Debug)]
pub struct BinaryHeap<K, V, N>
where
    N: ArrayLength<(K, V)> + ArrayLength<Option<usize>>,
{
    raw: Vec<GenericArray<(K, V), N>>,
    table: GenericArray<Option<usize>, N>,
    _key: PhantomData<fn() -> K>,
    _value: PhantomData<fn() -> V>,
}

impl<K, V, N> BinaryHeap<K, V, N>
where
    N: ArrayLength<(K, V)> + ArrayLength<Option<usize>>,
    K: Into<usize> + Clone + Copy,
    V: Ord,
{
    pub fn new() -> Self {
        Self {
            raw: Vec::new(),
            table: Self::init_table(),
            _key: PhantomData,
            _value: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.raw.len
    }

    pub fn capacity(&self) -> usize {
        self.raw.capacity()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn contains_key(&self, key: K) -> bool {
        self.table[key.into()].is_some()
    }

    pub fn clear(&mut self) {
        self.raw.clear();
        self.table = Self::init_table();
    }

    fn init_table() -> GenericArray<Option<usize>, N> {
        core::iter::repeat(None).take(N::to_usize()).collect()
    }

    pub fn peek(&self) -> Option<&(K, V)> {
        self.raw.get(0)
    }

    pub fn pop(&mut self) -> Option<(K, V)> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.pop_unchecked() })
        }
    }

    unsafe fn pop_unchecked(&mut self) -> (K, V) {
        if self.len() > 1 {
            self.swap(0, self.len() - 1);
        }
        let item = self.raw.pop_unchecked();
        self.table[item.0.into()] = None;
        self.sift_down(0);
        item
    }

    pub fn push_or_update(&mut self, key: K, value: V) -> Result<(), (K, V)> {
        if let Some(index) = self.table[key.into()] {
            self.update_unchecked(index, key, value)
        } else if self.raw.is_full() {
            return Err((key, value));
        } else {
            unsafe { self.push_unchecked(key, value) }
        }
        Ok(())
    }

    pub fn update(&mut self, key: K, value: V) -> Result<(), (K, V)> {
        if let Some(index) = self.table[key.into()] {
            self.update_unchecked(index, key, value);
            Ok(())
        } else {
            Err((key, value))
        }
    }

    fn update_unchecked(&mut self, index: usize, key: K, value: V) {
        if self.raw[index].1 < value {
            self.raw[index] = (key, value);
            self.sift_up(index);
        } else if self.raw[index].1 > value {
            self.raw[index] = (key, value);
            self.sift_down(index);
        }
    }

    pub fn push(&mut self, key: K, value: V) -> Result<(), (K, V)> {
        if self.table[key.into()].is_some() {
            Err((key, value))
        } else {
            unsafe { self.push_unchecked(key, value) }
            Ok(())
        }
    }

    unsafe fn push_unchecked(&mut self, key: K, value: V) {
        let old_len = self.len();
        self.raw.push_unchecked((key, value));
        self.table[key.into()] = Some(old_len);
        self.sift_up(old_len);
    }

    pub fn remove_key(&mut self, key: K) -> Result<V, K> {
        if let Some(index) = self.table[key.into()] {
            Ok(unsafe { self.remove_key_unchecked(index) })
        } else {
            Err(key)
        }
    }

    unsafe fn remove_key_unchecked(&mut self, index: usize) -> V {
        let mut item = self.raw.pop_unchecked();

        if !self.is_empty() {
            core::mem::swap(&mut item, self.raw.as_mut_slice().get_unchecked_mut(index));
            self.sift_down(index);
        }
        self.table[item.0.into()] = None;
        item.1
    }

    fn sift_up(&mut self, mut pos: usize) {
        while pos > 0 {
            let parent = (pos - 1) / 2;
            if self.raw[pos].1 <= self.raw[parent].1 {
                break;
            }
            self.swap(pos, parent);
            pos = parent;
        }
    }

    fn sift_down(&mut self, mut pos: usize) {
        let end = self.len();
        let mut child = 2 * pos + 1;
        while child < end {
            let right = child + 1;
            if right < end && self.raw[child].1 < self.raw[right].1 {
                child = right;
            }
            if self.raw[child].1 < self.raw[pos].1 {
                break;
            }
            self.swap(pos, child);
            pos = child;
            child = 2 * pos + 1;
        }
    }

    fn swap(&mut self, i: usize, j: usize) {
        let ki = self.raw[i].0.into();
        let kj = self.raw[j].0.into();
        self.raw.swap(i, j);
        self.table.swap(ki, kj);
    }
}

#[cfg(test)]
mod tests {
    use super::BinaryHeap;
    use generic_array::typenum::consts::*;
    extern crate std;
    use std::dbg;

    #[test]
    fn test_push() {
        let mut heap = BinaryHeap::<u8, u8, U4>::new();
        assert_eq!(heap.push(0, 2), Ok(()));
        assert_eq!(heap.push(1, 2), Ok(()));
        assert_eq!(heap.push(2, 2), Ok(()));
        assert_eq!(heap.push(2, 2), Err((2, 2)));
        assert_eq!(heap.push(3, 2), Ok(()));
        assert_eq!(heap.push(3, 2), Err((3, 2)));
    }

    #[test]
    fn test_pop() {
        let mut heap = BinaryHeap::<u8, u8, U8>::new();
        heap.push(2, 1).unwrap();
        heap.push(5, 3).unwrap();
        heap.push(4, 4).unwrap();
        heap.push(3, 5).unwrap();
        assert_eq!(heap.pop(), Some((3, 5)));
        assert_eq!(heap.pop(), Some((4, 4)));
        assert_eq!(heap.pop(), Some((5, 3)));
        assert_eq!(heap.pop(), Some((2, 1)));
        assert_eq!(heap.pop(), None);

        heap.push(3, 5).unwrap();
        heap.push(4, 4).unwrap();
        heap.push(5, 3).unwrap();
        heap.push(2, 1).unwrap();
        assert_eq!(heap.pop(), Some((3, 5)));
        assert_eq!(heap.pop(), Some((4, 4)));
        assert_eq!(heap.pop(), Some((5, 3)));
        assert_eq!(heap.pop(), Some((2, 1)));
        assert_eq!(heap.pop(), None);

        heap.push(5, 3).unwrap();
        heap.push(4, 4).unwrap();
        heap.push(3, 5).unwrap();
        heap.push(2, 1).unwrap();
        assert_eq!(heap.pop(), Some((3, 5)));
        assert_eq!(heap.pop(), Some((4, 4)));
        assert_eq!(heap.pop(), Some((5, 3)));
        assert_eq!(heap.pop(), Some((2, 1)));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_update() {
        let mut heap = BinaryHeap::<u8, u8, U8>::new();
        heap.push(2, 1).unwrap();
        assert_eq!(heap.peek(), Some(&(2, 1)));
        assert_eq!(heap.update(2, 4), Ok(()));
        assert_eq!(heap.peek(), Some(&(2, 4)));
        heap.push(5, 3).unwrap();
        assert_eq!(heap.peek(), Some(&(2, 4)));
        assert_eq!(heap.update(5, 5), Ok(()));
        assert_eq!(heap.peek(), Some(&(5, 5)));
        assert_eq!(heap.update(3, 2), Err((3, 2)));
    }

    #[test]
    fn test_push_or_update() {
        let mut heap = BinaryHeap::<u8, u8, U8>::new();
        heap.push_or_update(2, 1).unwrap();
        heap.push_or_update(2, 4).unwrap();
        heap.push_or_update(5, 17).unwrap();
        heap.push_or_update(4, 3).unwrap();
        assert_eq!(heap.pop(), Some((5, 17)));
        assert_eq!(heap.pop(), Some((2, 4)));
        assert_eq!(heap.pop(), Some((4, 3)));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_remove() {
        let mut heap = BinaryHeap::<u8, u8, U8>::new();
        heap.push(3, 2).unwrap();
        assert_eq!(heap.remove_key(2), Err(2));
        assert_eq!(heap.remove_key(3), Ok(2));
    }

    #[test]
    fn test_peek() {
        let mut heap = BinaryHeap::<u8, u8, U8>::new();
        heap.push(1, 2).unwrap();
        assert_eq!(heap.peek(), Some(&(1, 2)));
        heap.push(2, 4).unwrap();
        assert_eq!(heap.peek(), Some(&(2, 4)));
        heap.push(3, 3).unwrap();
        assert_eq!(heap.peek(), Some(&(2, 4)));
    }

    #[test]
    fn test_clear() {
        let mut heap = BinaryHeap::<u8, u8, U8>::new();
        heap.push(1, 2).unwrap();
        heap.push(2, 4).unwrap();
        assert_eq!(heap.peek(), Some(&(2, 4)));
        heap.clear();
        assert_eq!(heap.peek(), None);
    }
}
