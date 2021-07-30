use concurrency_toolkit::atomic::{self, AtomicPtr, Ordering};

pub const RW_ORD: Ordering = Ordering::AcqRel;
pub const R_ORD: Ordering = Ordering::Acquire;
pub const W_ORD: Ordering = Ordering::Release;

pub fn assert_store_ptr<T>(atomic: &AtomicPtr<T>, old_val: *mut T, new_val: *mut T) {
    atomic::assert_store_ptr(atomic, old_val, new_val, RW_ORD, W_ORD);
}

pub fn assert_store_ptr_relaxed<T>(
    atomic: &AtomicPtr<T>,
    old_val: *mut T,
    new_val: *mut T
) {
    use Ordering::Relaxed;

    atomic::assert_store_ptr(atomic, old_val, new_val, Relaxed, Relaxed);
}
