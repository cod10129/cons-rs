#![allow(unused_imports)]
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use cons_rs::{List, Cons, Nil};

fn benchmark(c: &mut Criterion) {
    c.bench_function("List::new", |b| b.iter(|| List::new(black_box(7))));
    c.bench_function("List::is_cons - Cons", |b| b.iter(|| {
        assert!(Cons(black_box(3), Box::new(Nil)).is_cons())
    }));
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
