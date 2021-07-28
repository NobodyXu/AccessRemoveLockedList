#[cfg(all(feature = "async", feature = "permutation_testing"))]
compile_error!("feature async cannot be used with feature permutation_testing");

#[cfg(feature = "async")]
pub extern crate tokio;

#[cfg(feature = "permutation_testing")]
pub extern crate loom;

#[macro_use]
mod rw_lock;

pub mod intrusive_list;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
