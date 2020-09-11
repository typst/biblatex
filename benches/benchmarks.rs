use criterion::{criterion_group, criterion_main, Criterion};

use biblatex::Bibliography;

const GRAL: &str = include_str!("../test/gral.bib");

fn parsing_benchmark(c: &mut Criterion) {
    c.bench_function("gral-parse", |b| {
        b.iter(|| Bibliography::from_str(GRAL, true))
    });

    let bib = Bibliography::from_str(GRAL, true);
    c.bench_function("gral-get-last-entry", |b| b.iter(|| bib.get("adedeji2017")));

    let entry = bib.get("kim2009").unwrap();
    c.bench_function("gral-get-author", |b| b.iter(|| entry.get_author()));
}

criterion_group!(benches, parsing_benchmark);
criterion_main!(benches);
