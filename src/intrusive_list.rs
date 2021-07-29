use core::marker::PhantomData;
use core::hint::unreachable_unchecked;
use core::ptr;

use concurrency_toolkit::maybe_async;
use concurrency_toolkit::sync::RwLock;
use concurrency_toolkit::atomic::AtomicPtr;
use concurrency_toolkit::{obtain_read_lock, obtain_write_lock};

use crate::utility::*;

/// Doubly linked intrusive list node.
///
/// **`self.get_next_ptr()` and `self.get_prev_ptr()` must return different pointers.**
///
/// `T` can either be an immutable reference or a `Sized` object, it is not recommended
/// to return a mutable reference.
pub trait IntrusiveListNode<T> {
    fn get_next_ptr(&self) -> &AtomicPtr<()>;
    fn get_prev_ptr(&self) -> &AtomicPtr<()>;

    fn get_elem(&self) -> T;
}

/// IntrusiveList guarantees that
///  - push and read can be done concurrently while allowing stale read;
///  - deletion can only be done sequentially when there is no
///    writer (excluding the thread doing deletion) or reader.
pub struct IntrusiveList<'a, Node: IntrusiveListNode<T>, T> {
    first_ptr: AtomicPtr<Node>,
    last_ptr: AtomicPtr<Node>,
    rwlock: RwLock<()>,
    phantom0: PhantomData<T>,
    phantom1: PhantomData<&'a Node>,
}
impl<'a, Node: IntrusiveListNode<T>, T> Default for IntrusiveList<'a, Node, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, Node: IntrusiveListNode<T>, T> IntrusiveList<'a, Node, T> {
    pub fn new() -> Self {
        Self {
            first_ptr: AtomicPtr::new(ptr::null_mut()),
            last_ptr: AtomicPtr::new(ptr::null_mut()),
            rwlock: RwLock::new(()),
            phantom0: PhantomData,
            phantom1: PhantomData,
        }
    }

    /// # Safety
    ///
    /// * `node` - it must not be added twice!
    #[maybe_async]
    pub async unsafe fn push_back(&self, node: &'a Node) {
        let _read_guard = obtain_read_lock!(&self.rwlock);
        let null = ptr::null_mut();

        loop {
            let last = self.last_ptr.load(R_ORD);

            node.get_next_ptr().store(null, W_ORD);
            node.get_prev_ptr().store(last as *mut (), W_ORD);

            if last.is_null() {
                let null = ptr::null_mut();
                let node = node as *const Node as *mut Node;
                match self.first_ptr.compare_exchange_weak(null, node, RW_ORD, R_ORD) {
                    Ok(_) => (),
                    Err(_) => continue,
                }
                assert_store_ptr(&self.last_ptr, null, node);
            } else {
                let node = node as *const Node as *mut Node as *mut ();
                match (*last)
                    .get_next_ptr()
                    .compare_exchange_weak(null, node, RW_ORD, R_ORD)
                {
                    Ok(_) => (),
                    Err(_) => continue,
                }
                let node = node as *mut Node;
                assert_store_ptr(&self.last_ptr, last, node);
            }
        }
    }

    /// # Safety
    ///
    /// * `node` - it must not be added twice!
    #[maybe_async]
    pub async unsafe fn push_front(&self, node: &'a Node) {
        let _read_guard = obtain_read_lock!(&self.rwlock);
        let null = ptr::null_mut();

        loop {
            let first = self.first_ptr.load(R_ORD);

            node.get_next_ptr().store(first as *mut (), W_ORD);
            node.get_prev_ptr().store(null, W_ORD);

            if first.is_null() {
                let null = ptr::null_mut();
                let node = node as *const Node as *mut Node;
                match self.first_ptr.compare_exchange_weak(null, node, RW_ORD, R_ORD) {
                    Ok(_) => (),
                    Err(_) => continue,
                }
                assert_store_ptr(&self.last_ptr, null, node);
            } else {
                let node = node as *const Node as *mut Node as *mut ();
                match (*first)
                    .get_prev_ptr()
                    .compare_exchange_weak(null, node, RW_ORD, R_ORD)
                {
                    Ok(_) => (),
                    Err(_) => continue,
                }
                let node = node as *mut Node;
                assert_store_ptr(&self.first_ptr, first, node);
            }
        }
    }

    /// Returns `true` if `node` is indeed inside `self`, otherwise `false`.
    ///
    /// # Safety
    ///
    /// * `node` - it must be in one of the following state:
    ///  - `node.get_next_ptr().is_null() && node.get_prev_ptr().is_null()`
    ///  - `node` is added to `self`
    #[maybe_async]
    pub async unsafe fn remove_node(&self, node: &'a Node) -> bool {
        let _write_guard = obtain_write_lock!(&self.rwlock);

        let prev_node = node.get_prev_ptr().load(R_ORD) as *mut Node;
        let next_node = node.get_next_ptr().load(R_ORD) as *mut Node;

        let node = node as *const _ as *mut _;

        if next_node.is_null() {
            let node = node as *mut _;
            match self.last_ptr
                .compare_exchange_weak(node, prev_node, RW_ORD, R_ORD)
            {
                Ok(_) => (),
                Err(_) => {
                    if prev_node.is_null() {
                        return false
                    } else {
                        #[cfg(debug)]
                        panic!(
                            "node {:#?} does not belong to list {:#?}",
                            node,
                            self as *const _
                        );
                        unreachable_unchecked()
                    }
                },
            }
        } else {
            let prev_node = prev_node as *mut ();
            assert_store_ptr((*next_node).get_prev_ptr(), node, prev_node);
        }

        if prev_node.is_null() {
            let node = node as *mut _;
            assert_store_ptr(&self.first_ptr, node, next_node);
        } else {
            let next_node = next_node as *mut ();
            assert_store_ptr((*prev_node).get_next_ptr(), node, next_node);
        }

        true
    }
}
