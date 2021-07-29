use core::marker::PhantomData;
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
///
/// # Safety
///
/// __**YOU MUST NOT USE THE SAME NODE IN TWO LISTS SIMULTANEOUSLY OR
/// ADD/REMOVE THE SAME NODE SIMULTANEOUSLY**__
pub unsafe trait IntrusiveListNode<T> {
    fn get_next_ptr(&self) -> &AtomicPtr<()>;
    fn get_prev_ptr(&self) -> &AtomicPtr<()>;

    fn get_elem(&self) -> T;
}

/// IntrusiveList guarantees that
///  - push and read can be done concurrently while allowing stale read;
///  - deletion can only be done sequentially when there is no
///    writer (excluding the thread doing deletion) or reader.
pub struct IntrusiveList<'a, Node: IntrusiveListNode<T>, T> {
    first_ptr: AtomicPtr<()>,
    last_ptr: AtomicPtr<()>,
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
    ///  * `node` -  __**YOU MUST NOT USE IT IN TWO LISTS SIMULTANEOUSLY OR
    ///    ADD/REMOVE IT SIMULTANEOUSLY**__
    #[maybe_async]
    pub async unsafe fn push_back(&self, node: &'a Node) {
        let _read_guard = obtain_read_lock!(&self.rwlock);
        let null = ptr::null_mut();

        node.get_next_ptr().store(null, W_ORD);

        loop {
            let last = self.last_ptr.load(R_ORD);

            node.get_prev_ptr().store(last, W_ORD);

            let node = node as *const _ as *mut ();
            if last.is_null() {
                match self.first_ptr.compare_exchange_weak(null, node, RW_ORD, R_ORD) {
                    Ok(_) => (),
                    Err(_) => continue,
                }
                assert_store_ptr(&self.last_ptr, null, node);
            } else {
                match (*(last as *mut Node))
                    .get_next_ptr()
                    .compare_exchange_weak(null, node, RW_ORD, R_ORD)
                {
                    Ok(_) => (),
                    Err(_) => continue,
                }
                assert_store_ptr(&self.last_ptr, last, node);
            }
        }
    }

    /// # Safety
    ///
    ///  * `node` -  __**YOU MUST NOT USE IT IN TWO LISTS SIMULTANEOUSLY OR
    ///    ADD/REMOVE IT SIMULTANEOUSLY**__
    #[maybe_async]
    pub async unsafe fn push_front(&self, node: &'a Node) {
        let _read_guard = obtain_read_lock!(&self.rwlock);
        let null = ptr::null_mut();

        node.get_prev_ptr().store(null, W_ORD);

        loop {
            let first = self.first_ptr.load(R_ORD);

            node.get_next_ptr().store(first, W_ORD);

            let node = node as *const _ as *mut ();
            if first.is_null() {
                match self.first_ptr.compare_exchange_weak(null, node, RW_ORD, R_ORD) {
                    Ok(_) => (),
                    Err(_) => continue,
                }
                assert_store_ptr(&self.last_ptr, null, node);
            } else {
                match (*(first as *mut Node))
                    .get_prev_ptr()
                    .compare_exchange_weak(null, node, RW_ORD, R_ORD)
                {
                    Ok(_) => (),
                    Err(_) => continue,
                }
                assert_store_ptr(&self.first_ptr, first, node);
            }
        }
    }

    /// Insert `node` after `anchor`.
    ///
    /// # Safety 
    ///
    ///  * `anchor` - it must be in this list!
    ///  * `node` -  __**YOU MUST NOT USE IT IN TWO LISTS SIMULTANEOUSLY OR
    ///    ADD/REMOVE IT SIMULTANEOUSLY**__
    #[maybe_async]
    pub async unsafe fn insert_after(&self, anchor: &'a Node, node: &'a Node) {
        let _read_guard = obtain_read_lock!(&self.rwlock);

        let anchor_next_ptr = anchor.get_next_ptr();
        let anchor = anchor as *const _ as *mut ();

        node.get_prev_ptr().store(anchor, W_ORD);

        let node_next_ptr = node.get_next_ptr();
        let node = node as *const _ as *mut ();

        loop {
            let next = anchor_next_ptr.load(R_ORD);

            node_next_ptr.store(next, W_ORD);
            match anchor_next_ptr.compare_exchange_weak(next, node, RW_ORD, R_ORD) {
                Ok(_) => {
                    if next.is_null() {
                        assert_store_ptr(&self.last_ptr, anchor, node);
                    }
                    break
                },
                Err(_) => continue,
            }
        }
    }

    /// Insert `node` before `anchor`.
    ///
    /// # Safety 
    ///
    ///  * `anchor` - it must be in this list!
    ///  * `node` -  __**YOU MUST NOT USE IT IN TWO LISTS SIMULTANEOUSLY OR
    ///    ADD/REMOVE IT SIMULTANEOUSLY**__
    #[maybe_async]
    pub async unsafe fn insert_before(&self, anchor: &'a Node, node: &'a Node) {
        let _read_guard = obtain_read_lock!(&self.rwlock);

        let anchor_prev_ptr = anchor.get_prev_ptr();
        let anchor = anchor as *const _ as *mut ();

        node.get_next_ptr().store(anchor, W_ORD);

        let node_prev_ptr = node.get_prev_ptr();
        let node = node as *const _ as *mut ();

        loop {
            let prev = anchor_prev_ptr.load(R_ORD);

            node_prev_ptr.store(prev, W_ORD);
            match anchor_prev_ptr.compare_exchange_weak(prev, node, RW_ORD, R_ORD) {
                Ok(_) => {
                    if prev.is_null() {
                        assert_store_ptr(&self.first_ptr, anchor, node);
                    }
                    break
                },
                Err(_) => continue,
            }
        }
    }

    /// Returns `true` if `node` is indeed inside `self`, otherwise `false`.
    ///
    /// # Safety
    ///
    ///  * `node` - it must be in one of the following state:
    ///     - `node.get_next_ptr().is_null() && node.get_prev_ptr().is_null()`
    ///     - `node` is added to `self`
    ///    and, __**YOU MUST NOT USE IT IN TWO LISTS SIMULTANEOUSLY OR
    ///    ADD/REMOVE IT SIMULTANEOUSLY**__
    #[maybe_async]
    pub async unsafe fn remove_node(&self, node: &'a Node) -> bool {
        let _write_guard = obtain_write_lock!(&self.rwlock);

        let prev_node = node.get_prev_ptr().load(R_ORD);
        let next_node = node.get_next_ptr().load(R_ORD);

        let node = node as *const _ as *mut _;

        if next_node.is_null() {
            match self.last_ptr.compare_exchange_weak(node, prev_node, RW_ORD, R_ORD) {
                Ok(_) => (),
                Err(_) => {
                    #[cfg(debug)]
                    if !prev_node.is_null() {
                        panic!(
                            "node {:#?} belongs to another list other than {:#?}",
                            node,
                            self as *const _
                        );
                    }
                    return false
                },
            }
        } else {
            let next_node = next_node as *mut Node;
            assert_store_ptr((*next_node).get_prev_ptr(), node, prev_node);
        }

        if prev_node.is_null() {
            assert_store_ptr(&self.first_ptr, node, next_node);
        } else {
            let prev_node = prev_node as *mut Node;
            assert_store_ptr((*prev_node).get_next_ptr(), node, next_node);
        }

        true
    }
}
