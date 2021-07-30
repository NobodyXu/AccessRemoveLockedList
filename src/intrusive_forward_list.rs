use concurrency_toolkit::atomic::AtomicPtr;

/// Singly linked intrusive list node.
///
/// `T` can either be an immutable reference or a `Sized` object, it is not recommended
/// to return a mutable reference.
///
/// # Safety
///
/// __**YOU MUST NOT USE THE SAME NODE IN TWO LISTS SIMULTANEOUSLY OR
/// ADD/REMOVE THE SAME NODE SIMULTANEOUSLY**__
pub unsafe trait IntrusiveForwardListNode {
    type Target;

    fn get_next_ptr(&self) -> &AtomicPtr<()>;

    fn get_elem(&self) -> Self::Target;
}

