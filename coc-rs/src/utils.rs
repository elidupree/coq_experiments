use serde::de::DeserializeOwned;
use serde::Serialize;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;

pub fn read_json_file<P: AsRef<Path>, T: DeserializeOwned>(path: P) -> anyhow::Result<T> {
    Ok(serde_json::from_reader(BufReader::new(File::open(path)?))?)
}

pub fn write_json_file<P: AsRef<Path>, T: Serialize>(path: P, value: &T) -> anyhow::Result<()> {
    Ok(serde_json::to_writer_pretty(
        BufWriter::new(File::create(path)?),
        value,
    )?)
}

pub fn todo<T, U>(_arg: U) -> T {
    todo!()
}

#[macro_export]
macro_rules! ad_hoc_lazy_static {
    ($T: ty) => {{
        static AD_HOC_LAZY_STATIC: std::sync::OnceLock<$T> = std::sync::OnceLock::<$T>::new();
        (|f| AD_HOC_LAZY_STATIC.get_or_init(f))
    }};
}
