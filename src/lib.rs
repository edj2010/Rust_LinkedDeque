use std::marker::PhantomData;
use std::ptr::NonNull;
use std::mem;
use std::fmt;
use std::iter::FromIterator;
use std::cmp::Ordering;
use std::ops::Drop;

type NodePtr<T> = Option<NonNull<Node<T>>>;
type NodePtrOwn<T> = Box<Node<T>>;

/// Node datatype
struct Node<T> {
    next: NodePtr<T>,
    prev: NodePtr<T>,
    data: T
}

impl<T> Node<T> {
    unsafe fn set_prev(node_ptr: &mut NodePtr<T>, prev: &NodePtr<T>) {
        if let Some(ptr) = node_ptr { (*ptr).as_mut().prev = *prev }
    }

    unsafe fn set_next(node_ptr: &mut NodePtr<T>, next: &NodePtr<T>) {
        if let Some(ptr) = node_ptr { (*ptr).as_mut().next = *next }
    }

    fn swap_prev(node_ptr: &mut NodePtr<T>, prev: &mut NodePtr<T>) {
        if let Some(ptr) = node_ptr { unsafe{ mem::swap(&mut ptr.as_mut().prev, prev) } }
    }

    fn swap_next(node_ptr: &mut NodePtr<T>, next: &mut NodePtr<T>) {
        if let Some(ptr) = node_ptr { unsafe{ mem::swap(&mut ptr.as_mut().next, next) } }
    }
}

impl<T> Node<T> {
    pub fn new(data: T) -> Self { Node{next: None, prev: None, data} }

    pub fn unwrap(heap_node: Box<Self>) -> T {heap_node.data}

    pub fn peek<'a>(node_ptr: NonNull<Node<T>>) -> &'a T {
        &unsafe{ &*node_ptr.as_ptr() }.data
    }

    pub fn peek_mut<'a>(node_ptr: NonNull<Node<T>>) -> &'a mut T {
        &mut unsafe{ &mut *node_ptr.as_ptr() }.data
    }

    pub fn from_ptr(node_ptr: NodePtr<T>) -> Option<NodePtrOwn<T>> {
        node_ptr.map(|ptr| unsafe{ Box::from_raw(ptr.as_ptr()) })
    }

    pub fn to_ptr(self: Box<Self>) -> NodePtr<T> {
        Some(Box::leak(self).into())
    }

    pub fn get_prev(node_ptr: &NodePtr<T>) -> NodePtr<T> {
        node_ptr.and_then(|ptr| unsafe{ ptr.as_ref().prev })
    }

    pub fn get_next(node_ptr: &NodePtr<T>) -> NodePtr<T> {
        node_ptr.and_then(|ptr| unsafe{ ptr.as_ref().next })
    }
    
    pub unsafe fn link(left: &mut NodePtr<T>, right: &mut NodePtr<T>) {
        Node::set_next(left, right);
        Node::set_prev(right, left);
    }

    pub fn unlink_next(node_ptr: &mut NodePtr<T>) -> NodePtr<T> {
        let mut ret = None;
        Node::swap_next(node_ptr, &mut ret);
        unsafe { Node::set_prev(&mut ret, &None) };
        ret
    }
    
    pub fn unlink_prev(node_ptr: &mut NodePtr<T>) -> NodePtr<T> {
        let mut ret = None;
        Node::swap_prev(node_ptr, &mut ret);
        unsafe { Node::set_next(&mut ret, &None) };
        ret
    }
}

/// Linked Deque datatype
pub struct LinkedDeque<T> {
    head: NodePtr<T>,
    tail: NodePtr<T>,
    len: usize,
    _marker: PhantomData<T>
}

impl<T> Default for LinkedDeque<T> {
    fn default() -> Self {
        LinkedDeque{head: None, tail: None, len: 0, _marker: PhantomData}
    }
}

impl<T: fmt::Debug> fmt::Debug for LinkedDeque<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T> IntoIterator for LinkedDeque<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter { IntoIter{ deque: self } }
}

impl<T> FromIterator<T> for LinkedDeque<T> {
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
        let mut d = LinkedDeque::new();
        for el in iter { d.push_back(el) }
        d
    }
}

impl<T: PartialEq> PartialEq for LinkedDeque<T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T: PartialEq> Eq for LinkedDeque<T> {}

impl<T: PartialOrd> PartialOrd for LinkedDeque<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord> Ord for LinkedDeque<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Copy> LinkedDeque<T> {
    pub fn from(data: &[T]) -> Self {
        let mut d = LinkedDeque::new();
        for el in data { d.push_back(*el) };
        d
    }
}

impl<T> Drop for LinkedDeque<T> {
    fn drop(&mut self) {
        struct DropGuard<'a, T>(&'a mut LinkedDeque<T>);

        while let Some(node) = self.pop_back() {
            let guard = DropGuard(self);
            drop(node);
            mem::forget(guard);
        }
    }
}

impl<T: Clone> Clone for LinkedDeque<T> {
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}

impl<T> LinkedDeque<T> {
    
    fn push_back_node(&mut self, mut node: NodePtrOwn<T>) {
        node.prev = self.tail;
        let node_ptr = node.to_ptr();

        match self.tail {
            None => self.head = node_ptr,
            Some(mut ptr) => unsafe { ptr.as_mut().next = node_ptr }
        };

        self.tail = node_ptr;
        self.len += 1;
    }

    fn push_front_node(&mut self, mut node: NodePtrOwn<T>) {
        node.next = self.head;
        let node_ptr = node.to_ptr();

        match self.head {
            None => self.tail = node_ptr,
            Some(mut ptr) => unsafe { ptr.as_mut().prev = node_ptr }
        };

        self.head = node_ptr;
        self.len += 1;
    }

    
    fn pop_front_node(&mut self) -> Option<NodePtrOwn<T>> {
        let head = Node::unlink_next(&mut self.head);
        self.head.and_then(|head_ptr| {
            let node = Node::from_ptr(Some(head_ptr));
            self.len -= 1;
            self.head = head;
            if self.head.is_none() { self.tail = None; }
            node
        })
    }

    fn pop_back_node(&mut self) -> Option<NodePtrOwn<T>> {
        let tail = Node::unlink_prev(&mut self.tail);
        self.tail.and_then(|tail_ptr| {
            let node = Node::from_ptr(Some(tail_ptr));
            self.len -= 1;
            self.tail = tail;
            if self.tail.is_none() { self.head = None; }
            node
        })
    }
}

impl<T> LinkedDeque<T> {
    /// Creates a new empty list
    pub fn new() -> Self { LinkedDeque::default() }

    /// Clears the entire list, leaving it empty
    pub fn clear(&mut self) { *self = Self::new(); }

    /// Returns a reference to the head of the list if the list has elements
    pub fn front(&self) -> Option<&T> {self.head.map(Node::peek)}

    /// Returns a reference to the tail of the list if the list has elements
    pub fn back(&self) -> Option<&T> {self.tail.map(Node::peek)}

    /// Returns a mutable reference to the head of the list if the list has elements    
    pub fn front_mut(&mut self) -> Option<&mut T> {self.head.map(Node::peek_mut)}

    /// Returns a mutable reference to the tail of the list if the list has elements
    pub fn back_mut(&mut self) -> Option<&mut T> {self.tail.map(Node::peek_mut)}

    /// Returns the number of items in the deque
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut d: LinkedDeque<i32> = LinkedDeque::new();
    /// assert_eq!(d.len(), 0);
    /// 
    /// d.push_back(5);
    /// d.push_front(4);
    /// assert_eq!(d.len(), 2);
    /// ```
    pub fn len(&self) -> usize { self.len }

    /// Returns whether your deque is empty
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut d: LinkedDeque<i32> = LinkedDeque::new();
    /// assert!(d.is_empty());
    /// 
    /// d.push_back(5);
    /// d.push_front(4);
    /// assert!(!d.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.len == 0 }

    /// Adds element to the end of the deque
    /// 
    /// # Arguments
    /// 
    /// `val` - data to be added to the deque
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut d: LinkedDeque<i32> = LinkedDeque::new();
    /// d.push_back(1);
    /// d.push_back(2);
    /// d.push_back(3);
    /// 
    /// assert_eq!(d.pop_front(), Some(1));
    /// assert_eq!(d.pop_front(), Some(2));
    /// assert_eq!(d.pop_front(), Some(3));
    /// ```
    pub fn push_back(&mut self, val: T) { self.push_back_node(Box::new(Node::new(val))); }

    /// Adds element to the beginning of the deque
    /// 
    /// # Arguments
    /// 
    /// `val` - data to be added to the deque
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut d: LinkedDeque<i32> = LinkedDeque::new();
    /// d.push_front(1);
    /// d.push_front(2);
    /// d.push_front(3);
    /// 
    /// assert_eq!(d.pop_front(), Some(3));
    /// assert_eq!(d.pop_front(), Some(2));
    /// assert_eq!(d.pop_front(), Some(1));
    /// ```
    pub fn push_front(&mut self, val: T) { self.push_front_node(Box::new(Node::new(val))); }

    /// Removes element from the end of the deque, returning it
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut d: LinkedDeque<i32> = LinkedDeque::new();
    /// d.push_back(1);
    /// d.push_back(2);
    /// d.push_back(3);
    /// 
    /// assert_eq!(d.pop_back(), Some(3));
    /// assert_eq!(d.pop_back(), Some(2));
    /// assert_eq!(d.pop_back(), Some(1));
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {self.pop_back_node().map(Node::unwrap)}

    /// Removes element from the beginning of the deque, returning it.
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut d: LinkedDeque<i32> = LinkedDeque::new();
    /// d.push_back(1);
    /// d.push_back(2);
    /// d.push_back(3);
    /// 
    /// assert_eq!(d.pop_front(), Some(1));
    /// assert_eq!(d.pop_front(), Some(2));
    /// assert_eq!(d.pop_front(), Some(3));
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {self.pop_front_node().map(Node::unwrap)}

    /// Adds all elements from the other list to the end of our list.
    /// Leaves the other list empty.
    /// Reuses the data from inside the other list, so happens in constant time.
    /// 
    /// # Arguments
    /// 
    /// `other` - another LinkedDeque to add into ours
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut d_front = LinkedDeque::from(&[1,2,3]);
    /// let mut d_back = LinkedDeque::from(&[4,5,6]);
    /// 
    /// let mut d_full = LinkedDeque::from(&[1,2,3,4,5,6]);
    /// 
    /// d_front.append(&mut d_back);
    /// 
    /// assert!(d_back.is_empty());
    /// assert_eq!(d_front, d_full);
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        if self.tail.is_none() { mem::swap(self, other) } 
        else if other.head.is_some() {
            let mut other_head = other.head.take();
            unsafe { Node::link(&mut self.tail, &mut other_head) }
            self.tail = other.tail.take();
            self.len += mem::replace(&mut other.len, 0);
        }
    }

    /// Adds all elements from the other list to the beginning of our list.
    /// Leaves the other list empty.
    /// Reuses the data from inside the other list, so happens in constant time.
    /// 
    /// # Arguments
    /// 
    /// `other` - another LinkedDeque to add into ours
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut d_front = LinkedDeque::from(&[1,2,3]);
    /// let mut d_back = LinkedDeque::from(&[4,5,6]);
    /// 
    /// let mut d_full = LinkedDeque::from(&[1,2,3,4,5,6]);
    /// 
    /// d_back.prepend(&mut d_front);
    /// 
    /// assert!(d_front.is_empty());
    /// assert_eq!(d_back, d_full);
    /// ```
    pub fn prepend(&mut self, other: &mut Self) {
        if self.head.is_none() { mem::swap(self, other) }
        else if other.tail.is_some() {
            let mut other_tail = other.tail.take();
            unsafe { Node::link(&mut other_tail, &mut self.head) }
            self.head = other.head.take();
            self.len += mem::replace(&mut other.len, 0);
        }
    }

    /// Returns a double ended iterator to the deque contents
    pub fn iter(&self) -> Iter<T> {
        Iter{ head: self.head, tail: self.tail, rem: self.len, _marker: PhantomData}
    }

    /// Returns a mutable double ended iterator to the deque contents
    pub fn iter_mut(&self) -> IterMut<T> {
        IterMut{ head: self.head, tail: self.tail, rem: self.len, _marker: PhantomData}
    }

    /// Returns a cursor at the head of the list
    pub fn cursor_head(&self) -> Cursor<T> {
        Cursor{curr: self.head, idx: 0, deque: self}
    }

    /// Returns a cursor at the tail of the list
    pub fn cursor_tail(&self) -> Cursor<T> {
        Cursor{curr: self.tail, idx: self.len - 1, deque: self}
    }

    /// Returns a mutable cursor at the head of the list
    pub fn cursor_head_mut(&mut self) -> CursorMut<T> {
        CursorMut{curr: self.head, idx: 0, deque: self}
    }

    /// Returns a mutable cursor at the tail of the list
    pub fn cursor_tail_mut(&mut self) -> CursorMut<T> {
        CursorMut{curr: self.tail, idx: self.len - 1, deque: self}
    }
}


/// Bi-Directional Iterator for LinkedDeque.
/// Conceptually lives 'between' next and prev
pub struct Iter<'a, T> {
    head: NodePtr<T>,
    tail: NodePtr<T>,
    rem: usize,
    _marker: PhantomData<&'a T>
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.rem == 0 { return None }
        self.head.map(|ptr| {
            self.head = Node::get_next(&self.head);
            self.rem -= 1;
            Node::peek(ptr)
        })
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.rem == 0 { return None }
        self.tail.map(|ptr| {
            self.tail = Node::get_prev(&self.tail);
            self.rem -= 1;
            Node::peek(ptr)
        })
    }
}

pub struct IterMut<'a, T> {
    head: NodePtr<T>,
    tail: NodePtr<T>,
    rem: usize,
    _marker: PhantomData<&'a mut T>
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.rem == 0 { return None }
        self.head.map(|ptr| {
            self.head = Node::get_next(&self.head);
            self.rem -= 1;
            Node::peek_mut(ptr)
        })
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.rem == 0 { return None }
        self.tail.map(|ptr| {
            self.tail = Node::get_prev(&self.tail);
            self.rem -= 1;
            Node::peek_mut(ptr)
        })
    }
}

pub struct IntoIter<T> {
    deque: LinkedDeque<T>
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> { self.deque.pop_front() }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> { self.deque.pop_back() }
}

/// A cursor to a location in the linked deque.
/// Can exist "between" the front and back, where the next node is the deques head and the previous node is the deques tail.
/// Seeks around the deque as if it were a circle
pub struct Cursor<'a, T: 'a> {
    curr: NodePtr<T>,
    deque: &'a LinkedDeque<T>,
    idx: usize
}

impl<'a, T> Cursor<'a, T> {

    /// Shifts cursor head one spot to the right
    /// Cycles to a null element off the right before returning to the start of the deque
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// use std::iter::FromIterator;
    /// 
    /// let deque = LinkedDeque::from_iter(1..20);
    /// let mut cursor = deque.cursor_head();
    /// cursor.seek_next();
    /// 
    /// assert_eq!(cursor.as_ref(), Some(&2));
    /// ```
    pub fn seek_next(&mut self) {
        if self.curr.is_none() {
            self.curr = self.deque.head;
            self.idx = 0;
        } else {
            self.curr = Node::get_next(&self.curr);
            self.idx += 1;
        }
    }

    /// Shifts cursor head one spot to the right
    /// Cycles to a null element off the right before returning to the start of the deque
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// use std::iter::FromIterator;
    /// 
    /// let deque = LinkedDeque::from_iter(1..20);
    /// let mut cursor = deque.cursor_tail();
    /// cursor.seek_prev();
    /// 
    /// assert_eq!(cursor.as_ref(), Some(&18));
    /// ```
    pub fn seek_prev(&mut self) {
        if self.curr.is_none() {
            self.curr = self.deque.tail;
        } else {
            self.curr = Node::get_prev(&self.curr);
        }
        if self.idx == 0 {
            self.idx = self.deque.len();
        } else { self.idx -= 1; }
    }

    /// returns a reference to the item the cursor is at
    pub fn as_ref(&self) -> Option<&T> {
        self.curr.map(Node::peek)
    }
}

/// A mutable cursor to a location in the linked deque.
/// Can exist "between" the front and back, where the next node is the deques head and the previous node is the deques tail.
/// Seeks around the deque as if it were a circle
pub struct CursorMut<'a, T: 'a> {
    curr: NodePtr<T>,
    deque: &'a mut LinkedDeque<T>,
    idx: usize
}

impl<'a, T> CursorMut<'a, T> {
    
    /// Shifts cursor head one spot to the right
    /// Cycles to a null element off the right before returning to the start of the deque
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// use std::iter::FromIterator;
    /// 
    /// let mut deque = LinkedDeque::from_iter(1..20);
    /// let mut cursor = deque.cursor_head_mut();
    /// cursor.seek_next();
    /// 
    /// assert_eq!(cursor.as_ref(), Some(&2));
    /// ```
    pub fn seek_next(&mut self) {
        if self.curr.is_none() {
            self.curr = self.deque.head;
            self.idx = 0;
        } else {
            self.curr = Node::get_next(&self.curr);
            self.idx += 1;
        }
    }

    /// Shifts cursor head one spot to the right
    /// Cycles to a null element off the right before returning to the start of the deque
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// use std::iter::FromIterator;
    /// 
    /// let mut deque = LinkedDeque::from_iter(1..20);
    /// let mut cursor = deque.cursor_tail_mut();
    /// cursor.seek_prev();
    /// 
    /// assert_eq!(cursor.as_ref(), Some(&18));
    /// ```
    pub fn seek_prev(&mut self) {
        if self.curr.is_none() {
            self.curr = self.deque.tail;
            self.idx = self.deque.len() - 1;
        } else {
            self.curr = Node::get_prev(&self.curr);
            self.idx = if self.idx > 0 { self.idx - 1 } else { self.deque.len() }
        }
    }

    /// Returns an optional reference to the value pointed to by the cursor
    /// None if cursor is off the end of the deque
    pub fn as_ref(&self) -> Option<&T> {
        self.curr.map(Node::peek)
    }

    /// Returns an optional mutable reference to the value pointed to by the cursor
    /// None if cursor is off the end of the deque
    pub fn as_mut(&self) -> Option<&mut T> {
        self.curr.map(Node::peek_mut)
    }

    /// Inserts an element after the value pointed to by the cursor
    /// Inserts at the front if off the end of the deque
    /// 
    /// # Arguments
    /// 
    /// `val` - the value to insert into the deque
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut deque      = LinkedDeque::from(&[1,3,4,5]);
    /// let mut deque_full = LinkedDeque::from(&[1,2,3,4,5]);
    /// 
    /// let mut cursor = deque.cursor_head_mut();
    /// cursor.insert_after(2);
    /// 
    /// assert_eq!(deque, deque_full);
    /// ```
    pub fn insert_after(&mut self, val: T) {
        if self.curr.is_none() { self.deque.push_front(val) } else {
            let mut node_ptr = Node::to_ptr(Box::new(Node::new(val)));
            let mut next = Node::unlink_next(&mut self.curr);
            unsafe {
                Node::link(&mut self.curr, &mut node_ptr);
                Node::link(&mut node_ptr, &mut next);
            }
            self.deque.len += 1;
        }
    }

    /// Inserts an element before the value pointed to by the cursor
    /// Inserts at the back if off the end of the deque
    /// 
    /// # Arguments
    /// 
    /// `val` - the value to insert into the deque
    /// 
    /// # Example
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut deque      = LinkedDeque::from(&[1,3,4,5]);
    /// let mut deque_full = LinkedDeque::from(&[1,2,3,4,5]);
    /// 
    /// let mut cursor = deque.cursor_head_mut();
    /// cursor.seek_next();
    /// cursor.insert_before(2);
    /// 
    /// assert_eq!(deque, deque_full);
    /// ```
    pub fn insert_before(&mut self, val: T) {
        if self.curr.is_none() { self.deque.push_back(val) } else {
            let mut node_ptr = Node::to_ptr(Box::new(Node::new(val)));
            let mut prev = Node::unlink_prev(&mut self.curr);
            unsafe {
                Node::link(&mut prev, &mut node_ptr);
                Node::link(&mut node_ptr, &mut self.curr);
            }
            self.deque.len += 1;
            self.idx += 1;
        }
    }

    /// Removes the currently pointed to value.
    /// The cursor will then point to the next value (or off the end of the list) and the removed value will be returned.
    /// Returns None if already off the end of the list.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut deque      = LinkedDeque::from(&[1,3,4,5]);
    /// let mut deque_full = LinkedDeque::from(&[1,2,3,4,5]);
    /// 
    /// let mut cursor = deque_full.cursor_head_mut();
    /// cursor.seek_next();
    /// assert_eq!(cursor.remove(), Some(2));
    /// assert_eq!(cursor.as_ref(), Some(&3));
    /// assert_eq!(deque, deque_full);
    /// ```
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut deque       = LinkedDeque::from(&[2,3,4,5]);
    /// let mut deque_full  = LinkedDeque::from(&[1,2,3,4,5]);
    /// 
    /// let mut cursor = deque_full.cursor_head_mut();
    /// 
    /// assert_eq!(cursor.remove(), Some(1));
    /// assert_eq!(cursor.as_ref(), Some(&2));
    /// assert_eq!(deque, deque_full);
    /// ```
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut deque = LinkedDeque::from(&[1]);
    /// let empty_deque = LinkedDeque::new();
    /// 
    /// let mut cursor = deque.cursor_head_mut();
    /// 
    /// assert_eq!(cursor.remove(), Some(1));
    /// assert_eq!(cursor.as_ref(), None);
    /// assert_eq!(deque, empty_deque);
    /// ```
    pub fn remove(&mut self) -> Option<T> {
        self.curr?;
        
        let mut prev = Node::unlink_prev(&mut self.curr);
        let mut next = Node::unlink_next(&mut self.curr);
        unsafe{ Node::link(&mut prev, &mut next); }
        
        let mut ret_node = None;
        mem::swap(&mut self.curr, &mut ret_node);
        self.curr = next;

        self.deque.len -= 1;

        if self.idx == 0 { self.deque.head = next; }
        if self.idx == self.deque.len { self.deque.tail = prev }
        
        Node::from_ptr(ret_node).map(Node::unwrap)
    }

    /// Removes all elements from the list after the cursor, putting them in a new list.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let d_front     = LinkedDeque::from(&[1,2,3]);
    /// let d_back      = LinkedDeque::from(&[4,5,6]);
    /// let mut d_full  = LinkedDeque::from(&[1,2,3,4,5,6]);
    /// 
    /// let mut cursor = d_full.cursor_head_mut();
    /// cursor.seek_next();
    /// cursor.seek_next();
    /// 
    /// let rest = cursor.split_after();
    /// assert_eq!(d_full.len(), 3);
    /// assert_eq!(rest.len(), 3);
    /// assert_eq!(d_full, d_front);
    /// assert_eq!(rest, d_back);
    /// ```
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut deque = LinkedDeque::from(&[1,2,3,4]);
    /// let deque_copy = LinkedDeque::from(&[1,2,3,4]);
    /// let mut cursor = deque.cursor_head_mut();
    /// cursor.seek_prev();
    /// 
    /// let whole_deque = cursor.split_after();
    /// assert!(deque.is_empty());
    /// assert_eq!(whole_deque, deque_copy);
    /// ```
    pub fn split_after(&mut self) -> LinkedDeque<T> {
        let mut new_deque = LinkedDeque::new();

        if self.curr.is_none() {
            mem::swap(&mut new_deque, self.deque);
            self.idx = 0;
            return new_deque;
        }

        let next = Node::unlink_next(&mut self.curr);
        if next.is_some() {
            new_deque.head = next;
            new_deque.tail = self.deque.tail;
            new_deque.len = self.deque.len - self.idx - 1;
            self.deque.tail = self.curr;
            self.deque.len = self.idx + 1;
        }
        new_deque
    }

    /// Removes all elements from the list after the cursor, putting them in a new list.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let d_front     = LinkedDeque::from(&[1,2,3]);
    /// let d_back      = LinkedDeque::from(&[4,5,6]);
    /// let mut d_full  = LinkedDeque::from(&[1,2,3,4,5,6]);
    /// 
    /// let mut cursor = d_full.cursor_head_mut();
    /// cursor.seek_next();
    /// cursor.seek_next();
    /// cursor.seek_next();
    /// 
    /// let before = cursor.split_before();
    /// assert_eq!(d_full.len(), 3);
    /// assert_eq!(before.len(), 3);
    /// assert_eq!(d_full, d_back);
    /// assert_eq!(before, d_front);
    /// ```
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut deque = LinkedDeque::from(&[1,2,3,4]);
    /// let deque_copy = LinkedDeque::from(&[1,2,3,4]);
    /// let mut cursor = deque.cursor_head_mut();
    /// cursor.seek_prev();
    /// 
    /// let whole_deque = cursor.split_before();
    /// assert!(deque.is_empty());
    /// assert_eq!(whole_deque, deque_copy);
    /// ```
    pub fn split_before(&mut self) -> LinkedDeque<T> {
        let mut new_deque = LinkedDeque::new();

        if self.curr.is_none() {
            mem::swap(&mut new_deque, self.deque);
            self.idx = 0;
            return new_deque;
        }

        let prev = Node::unlink_prev(&mut self.curr);
        if prev.is_some(){
            new_deque.head = self.deque.head;
            new_deque.tail = prev;
            new_deque.len = self.idx;
            self.deque.head = self.curr;
            self.deque.len -= self.idx;
            self.idx = 0;
        }

        new_deque
    }

    /// Splices the provided deque into our deque after the cursor.
    /// This 'consumes' the other list, leaving it empty (similar to append).
    /// 
    /// # Arguments
    /// 
    /// 'other' - deque to insert into our deque
    /// 
    /// # Examples
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let deque_full = LinkedDeque::from(&[1,2,3,4,5,6]);
    /// let mut partial_deque = LinkedDeque::from(&[1,2,6]);
    /// let mut missing_elems = LinkedDeque::from(&[3,4,5]);
    /// 
    /// let mut cursor = partial_deque.cursor_tail_mut();
    /// cursor.seek_prev();
    /// cursor.splice_after(&mut missing_elems);
    /// 
    /// assert_eq!(partial_deque, deque_full);
    /// assert!(missing_elems.is_empty());
    /// ```
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let deque_full = LinkedDeque::from(&[1,2,3,4]);
    /// let mut deque_empty = LinkedDeque::new();
    /// let mut missing_elems = LinkedDeque::from(&[1,2,3,4]);
    /// 
    /// // tail should also work
    /// let mut cursor = deque_empty.cursor_head_mut();
    /// 
    /// cursor.splice_after(&mut missing_elems);
    /// assert_eq!(deque_full, deque_empty);
    /// assert!(missing_elems.is_empty());
    /// ```
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut deque_front = LinkedDeque::from(&[1,2,3]);
    /// let mut deque_back  = LinkedDeque::from(&[4,5,6]);
    /// let deque_full      = LinkedDeque::from(&[1,2,3,4,5,6]);
    /// 
    /// let mut cursor = deque_back.cursor_tail_mut();
    /// cursor.seek_next();
    /// cursor.splice_after(&mut deque_front);
    /// 
    /// assert!(deque_front.is_empty());
    /// assert_eq!(deque_back, deque_full);
    /// ```
    pub fn splice_after(&mut self, other: &mut LinkedDeque<T>) {
        let mut after = self.split_after();
        self.deque.append(other);
        self.deque.append(&mut after);
    }

    /// Splices the provided deque into our deque before the cursor.
    /// This 'consumes' the other list, leaving it empty (similar to append).
    /// 
    /// # Arguments
    /// 
    /// 'other' - deque to insert into our deque
    /// 
    /// # Examples
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let deque_full = LinkedDeque::from(&[1,2,3,4,5,6]);
    /// let mut partial_deque = LinkedDeque::from(&[1,2,6]);
    /// let mut missing_elems = LinkedDeque::from(&[3,4,5]);
    /// 
    /// let mut cursor = partial_deque.cursor_tail_mut();
    /// cursor.splice_before(&mut missing_elems);
    /// 
    /// assert!(missing_elems.is_empty());
    /// assert_eq!(partial_deque, deque_full);
    /// ```
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let deque_full = LinkedDeque::from(&[1,2,3,4]);
    /// let mut deque_empty = LinkedDeque::new();
    /// let mut missing_elems = LinkedDeque::from(&[1,2,3,4]);
    /// 
    /// // tail should also work
    /// let mut cursor = deque_empty.cursor_head_mut();
    /// 
    /// cursor.splice_before(&mut missing_elems);
    /// assert!(missing_elems.is_empty());
    /// assert_eq!(deque_full, deque_empty);
    /// ```
    /// 
    /// ```
    /// use linked_deque::LinkedDeque;
    /// 
    /// let mut deque_front = LinkedDeque::from(&[1,2,3]);
    /// let mut deque_back  = LinkedDeque::from(&[4,5,6]);
    /// let deque_full      = LinkedDeque::from(&[1,2,3,4,5,6]);
    /// 
    /// let mut cursor = deque_front.cursor_tail_mut();
    /// cursor.seek_next();
    /// cursor.splice_before(&mut deque_back);
    /// 
    /// assert!(deque_back.is_empty());
    /// assert_eq!(deque_front, deque_full);
    /// ```
    pub fn splice_before(&mut self, other: &mut LinkedDeque<T>) {
        let mut before = self.split_before();
        self.idx = other.len + before.len;
        self.deque.prepend(other);
        self.deque.prepend(&mut before);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::LinkedList;

    #[test]
    fn push_pop_back() {
        let mut l: LinkedDeque<i32> = LinkedDeque::new();
        l.push_back(1);
        l.push_back(2);
        l.push_back(3);

        assert_eq!(l.pop_back(), Some(3));
        assert_eq!(l.pop_back(), Some(2));
        assert_eq!(l.pop_back(), Some(1));

        assert_eq!(l.pop_back(), None);
        assert_eq!(l.pop_back(), None);
    }

    #[test]
    fn push_pop_front() {
        let mut l: LinkedDeque<i32> = LinkedDeque::new();
        l.push_front(1);
        l.push_front(2);
        l.push_front(3);

        assert_eq!(l.pop_front(), Some(3));
        assert_eq!(l.pop_front(), Some(2));
        assert_eq!(l.pop_front(), Some(1));

        assert_eq!(l.pop_front(), None);
        assert_eq!(l.pop_front(), None);
    }

    #[test]
    fn push_pop_many() {
        let mut my_l: LinkedDeque<i32> = LinkedDeque::new();
        let mut std_l: LinkedList<i32> = LinkedList::new();
        for i in 1..100 {
            match i {
                _ if i%3 == 0 => {
                    my_l.push_back(i);
                    std_l.push_back(i);
                },
                _ => {
                    my_l.push_front(i);
                    std_l.push_front(i);
                }
            }
        }
        for i in 1..100 {
            match i {
                _ if i%2 == 0 => assert_eq!(my_l.pop_back(), std_l.pop_back()),
                _             => assert_eq!(my_l.pop_front(), std_l.pop_front())
            }
            println!("{}",i);
        }
    }

    #[test]
    fn append_empty() {
        let mut d1 = LinkedDeque::from(&[1,2,3]);
        let d1_copy = LinkedDeque::from(&[1,2,3]);
        let mut empty = LinkedDeque::new();
        d1.append(&mut empty);
        assert_eq!(d1, d1_copy);
    }

    #[test]
    fn prepend_empty() {
        let mut d1 = LinkedDeque::from(&[1,2,3]);
        let d1_copy = LinkedDeque::from(&[1,2,3]);
        let mut empty = LinkedDeque::new();
        d1.prepend(&mut empty);
        assert_eq!(d1, d1_copy);
    }
}