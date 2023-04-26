#![allow(unused_imports)]
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use cons_rs::{List, Cons, Nil};

fn bench(c: &mut Criterion) {
    c.bench_function("List::new", |b| b.iter(|| List::new(7)));
    c.bench_function("List::is_cons - Cons", |b| b.iter(|| {
        assert!(Cons(3, Box::new(Nil)).is_cons())
    }));
    c.bench_function("List::is_cons - Nil", |b| b.iter(|| {
        let _ = Cons(3, Box::new(Nil)); // allocating, like is_cons - Cons
        assert!(!Nil::<u8>.is_cons())
    }));
}

criterion_group!(benches, bench);
criterion_main!(benches);
