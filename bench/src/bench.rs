use criterion::{criterion_group, criterion_main, Criterion};

use biblatex::Bibliography;

const GRAL: &str = include_str!("../../tests/gral.bib");

fn benchmarks(c: &mut Criterion) {
    macro_rules! bench {
        ($name:literal: $($tts:tt)*) => {
            c.bench_function($name, |b| b.iter(|| $($tts)*));
        };
    }

    let bib = Bibliography::from_str(GRAL, true);
    let entry = bib.get("kim2009").unwrap();

    bench!("parse-gral": Bibliography::from_str(GRAL, true));
    bench!("get-last-gral": bib.get("adedeji2017"));
    bench!("get-author-gral": entry.get_author());
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
