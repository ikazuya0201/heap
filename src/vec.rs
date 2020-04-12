use core::{mem::MaybeUninit, ptr, slice};

use generic_array::{ArrayLength, GenericArray};

pub struct Vec<A> {
    buffer: MaybeUninit<A>,
    len: usize,
}

impl<A> Vec<A> {
    pub const fn new() -> Self {
        Self {
            buffer: MaybeUninit::uninit(),
            len: 0,
        }
    }
}

impl<T, N> Vec<GenericArray<T, N>>
where
    N: ArrayLength<T>,
{
    pub fn as_slice(&self) -> &[T] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &buffer[..self.len]
        unsafe { slice::from_raw_parts(self.buffer.as_ptr() as *const T, self.len) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &mut buffer[..len]
        unsafe { slice::from_raw_parts_mut(self.buffer.as_mut_ptr() as *mut T, self.len) }
    }

    pub fn capacity(&self) -> usize {
        N::to_usize()
    }

    pub fn clear(&mut self) {
        self.truncate(0);
    }

    pub fn is_full(&self) -> bool {
        self.len == self.capacity()
    }

    pub fn extend_from_slice(&mut self, other: &[T]) -> Result<(), ()>
    where
        T: Clone,
    {
        if self.len + other.len() > self.capacity() {
            Err(())
        } else {
            for element in other {
                unsafe {
                    self.push_unchecked(element.clone());
                }
            }
            Ok(())
        }
    }

    pub unsafe fn pop_unchecked(&mut self) -> T {
        debug_assert!(!self.as_slice().is_empty());

        self.len -= 1;
        (self.buffer.as_ptr() as *const T).add(self.len).read()
    }

    pub unsafe fn push_unchecked(&mut self, item: T) {
        // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
        // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
        (self.buffer.as_mut_ptr() as *mut T)
            .add(self.len)
            .write(item);

        self.len += 1;
    }

    pub unsafe fn swap_remove_unchecked(&mut self, index: usize) -> T {
        let length = self.len;
        debug_assert!(index < length);
        self.swap_unchecked(index, length - 1);
        self.pop_unchecked()
    }

    pub unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        ptr::swap(
            self.as_mut_slice().get_unchecked_mut(a),
            self.as_mut_slice().get_unchecked_mut(b),
        );
    }

    pub fn truncate(&mut self, len: usize) {
        unsafe {
            // drop any extra elements
            while len < self.len {
                // decrement len before the drop_in_place(), so a panic on Drop
                // doesn't re-drop the just-failed value.
                self.len -= 1;
                let len = self.len;
                ptr::drop_in_place(self.as_mut_slice().get_unchecked_mut(len));
            }
        }
    }
}

impl<T, N> Clone for Vec<GenericArray<T, N>>
where
    T: Clone,
    N: ArrayLength<T>,
{
    fn clone(&self) -> Self
    where
        T: Clone,
    {
        let mut new = Self::new();
        new.extend_from_slice(&self).unwrap();
        new
    }
}

impl<T, N> core::ops::Deref for Vec<GenericArray<T, N>>
where
    N: ArrayLength<T>,
{
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, N> core::ops::DerefMut for Vec<GenericArray<T, N>>
where
    N: ArrayLength<T>,
{
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}
