use core::marker::PhantomData;

use generic_array::{ArrayLength, GenericArray};

use crate::vec::Vec;

/// A heapless binary heap implementation.
///
/// This binary heap provides update, remove and push_or_update in addition to
/// push and pop.
///
/// ## Time Complexity
/// |         | push(peek) | pop      | update   | remove   | push_or_update |
/// |---------|------------|----------|----------|----------|----------------|
/// | worst   | O(log n)   | O(1)     | O(log n) | O(log n) | O(log n)       |
///
/// NOTE: This binary heap has a table of size N inside (like a hash table).  
/// Then, type K should be convertable to unique ID which is smaller than N.

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
        self.raw.len()
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
        let item = self.raw.swap_remove_unchecked(0);
        *self.table.get_unchecked_mut(item.0.into()) = None;
        self.sift_down(0);
        item
    }

    pub fn push_or_update(&mut self, key: K, value: V) -> Result<(), (K, V)> {
        if let Some(index) = self.table[key.into()] {
            unsafe { self.update_unchecked(index, key, value) }
        } else if self.raw.is_full() {
            return Err((key, value));
        } else {
            unsafe { self.push_unchecked(key, value) }
        }
        Ok(())
    }

    pub fn update(&mut self, key: K, value: V) -> Result<(), (K, V)> {
        if let Some(index) = self.table[key.into()] {
            unsafe { self.update_unchecked(index, key, value) }
            Ok(())
        } else {
            Err((key, value))
        }
    }

    unsafe fn update_unchecked(&mut self, index: usize, key: K, value: V) {
        if self.raw.get_unchecked(index).1 < value {
            *self.raw.get_unchecked_mut(index) = (key, value);
            self.sift_up(index);
        } else if self.raw.get_unchecked(index).1 > value {
            *self.raw.get_unchecked_mut(index) = (key, value);
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
        *self.table.get_unchecked_mut(key.into()) = Some(old_len);
        self.sift_up(old_len);
    }

    pub fn remove(&mut self, key: K) -> Result<V, K> {
        if let Some(index) = self.table[key.into()] {
            Ok(unsafe { self.remove_unchecked(index) })
        } else {
            Err(key)
        }
    }

    unsafe fn remove_unchecked(&mut self, index: usize) -> V {
        let item = self.raw.swap_remove_unchecked(index);
        self.sift_down(index);
        *self.table.get_unchecked_mut(item.0.into()) = None;
        item.1
    }

    unsafe fn sift_up(&mut self, mut pos: usize) {
        while pos > 0 {
            let parent = (pos - 1) / 2;
            if self.raw.get_unchecked(pos).1 <= self.raw.get_unchecked(parent).1 {
                break;
            }
            self.swap_unchecked(pos, parent);
            pos = parent;
        }
    }

    unsafe fn sift_down(&mut self, mut pos: usize) {
        let end = self.len();
        let mut child = 2 * pos + 1;
        while child < end {
            let right = child + 1;
            if right < end && self.raw.get_unchecked(child).1 < self.raw.get_unchecked(right).1 {
                child = right;
            }
            if self.raw.get_unchecked(child).1 < self.raw.get_unchecked(pos).1 {
                break;
            }
            self.swap_unchecked(pos, child);
            pos = child;
            child = 2 * pos + 1;
        }
    }

    unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        let ka = self.raw.get_unchecked(a).0.into();
        let kb = self.raw.get_unchecked(b).0.into();
        self.raw.swap_unchecked(a, b);
        self.swap_table_unchecked(ka, kb);
    }

    unsafe fn swap_table_unchecked(&mut self, a: usize, b: usize) {
        core::ptr::swap(
            self.table.as_mut_slice().get_unchecked_mut(a),
            self.table.as_mut_slice().get_unchecked_mut(b),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::BinaryHeap;
    use generic_array::typenum::consts::*;

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
        assert_eq!(heap.remove(2), Err(2));
        assert_eq!(heap.remove(3), Ok(2));
        assert_eq!(heap.remove(3), Err(3));
    }

    #[test]
    fn test_peek() {
        let mut heap = BinaryHeap::<u8, u8, U8>::new();
        heap.push(1, 2).unwrap();
        assert_eq!(heap.peek(), Some(&(1, 2)));
        heap.push(2, 4).unwrap();
        assert_eq!(heap.peek(), Some(&(2, 4)));
        heap.push(3, 3).unwrap();
        assert_eq!(heap.pop(), Some((2, 4)));
        assert_eq!(heap.peek(), Some(&(3, 3)));
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
