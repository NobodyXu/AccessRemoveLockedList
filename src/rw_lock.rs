#[cfg(not(feature = "async"))]
#[macro_use]
mod inline {
    pub(crate) use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};

    pub(crate) fn read<T: ?Sized>(rwlock: &RwLock<T>) -> RwLockReadGuard<'_, T> {
        rwlock.read().expect("Failed to lock std::sync::RwLock for reading")
    }

    pub(crate) fn write<T: ?Sized>(rwlock: &RwLock<T>) -> RwLockWriteGuard<'_, T> {
        rwlock.write().expect("Failed to lock std::sync::RwLock for writing")
    }

    macro_rules! read {
        ( $lock:expr ) => {
            $crate::rw_lock::read($lock)
        };
    }

    macro_rules! write {
        ( $lock:expr ) => {
            $crate::rw_lock::write($lock)
        };
    }
}

#[cfg(feature = "async")]
#[macro_use]
mod inline {
    pub(crate) use tokio::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};

    pub(crate) async fn read<T: ?Sized>(rwlock: &RwLock<T>) -> RwLockReadGuard<'_, T> {
        rwlock.read()
    }

    pub(crate) async fn write<T: ?Sized>(rwlock: &RwLock<T>) -> RwLockWriteGuard<'_, T> {
        rwlock.write()
    }

    macro_rules! read {
        ( $lock:expr ) => {
            $crate::rw_lock::read($lock).await
        };
    }

    macro_rules! write {
        ( $lock:expr ) => {
            $crate::rw_lock::write($lock).await
        };
    }
}

#[cfg(feature = "permutation_testing")]
#[macro_use]
mod inline {
    pub(crate) use loom::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};

    pub(crate) fn read<T: ?Sized>(rwlock: &RwLock<T>) -> RwLockReadGuard<'_, T> {
        rwlock.read().expect("Failed to lock std::sync::RwLock for reading")
    }

    pub(crate) fn write<T: ?Sized>(rwlock: &RwLock<T>) -> RwLockWriteGuard<'_, T> {
        rwlock.write().expect("Failed to lock std::sync::RwLock for writing")
    }

    macro_rules! read {
        ( $lock:expr ) => {
            $crate::rw_lock::read($lock)
        };
    }

    macro_rules! write {
        ( $lock:expr ) => {
            $crate::rw_lock::write($lock)
        };
    }
}

pub(crate) use inline::*;
