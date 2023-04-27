#![allow(unused_imports)]
use easybench::{bench, bench_env, bench_gen_env};
use cons_rs::{List, Cons, Nil};

fn main() {
    println!("List::new: {}", bench(|| List::new(3_u128)));
    println!("List::is_cons: {}", bench_env(
        List::new(7), |x| x.is_cons()));
    println!("List::is_nil: {}", bench_env(
        Nil::<u32>, |x| x.is_nil()));
}
