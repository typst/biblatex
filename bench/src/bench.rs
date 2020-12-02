use criterion::{criterion_group, criterion_main, Criterion};

use biblatex::Bibliography;

const GRAL: &str = include_str!("../../tests/gral.bib");
const CROSS: &str = include_str!("../../tests/cross.bib");

fn benchmarks(c: &mut Criterion) {
    macro_rules! bench {
        ($name:literal: $($tts:tt)*) => {
            c.bench_function($name, |b| b.iter(|| $($tts)*));
        };
    }

    let bib = Bibliography::parse(GRAL);
    let entry = bib.get("kim2009").unwrap();

    bench!("parse-gral": Bibliography::parse(GRAL));
    bench!("get-last-gral": bib.get("adedeji2017"));
    bench!("get-author-gral": entry.author());

    let bib = Bibliography::parse(CROSS);
    let entry = bib.get("issue201").unwrap();
    bench!("get-date-cross": entry.date());
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
