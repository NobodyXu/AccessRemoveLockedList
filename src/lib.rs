#[cfg(feature = "async")]
pub extern crate tokio;

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
