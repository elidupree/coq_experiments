#![feature(default_free_fn, array_methods)]

//pub mod incomplete_term;
pub mod inductive_type;
pub mod term;
pub mod term_variable;
pub mod types;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
