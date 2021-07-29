pub extern crate concurrency_toolkit;

mod utility;
pub mod intrusive_forward_list;
pub mod intrusive_list;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
