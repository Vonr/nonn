# nonn [![Crates.io](https://img.shields.io/crates/v/nonn)](https://crates.io/crates/nonn)

Integer types that are known not to equal any single N, enabling some memory layout optimization.

Most of nonn's code is lifted from [core::num::nonzero](https://doc.rust-lang.org/src/core/num/nonzero.rs.html)
and slightly adapted.

nonn is backed by `core::num::NonZero*`, ensuring
```rs
use std::mem::size_of;

assert_eq!(size_of::<Option<nonn::NonNU8<0>>>(), size_of::<u8>());
assert_eq!(size_of::<Option<nonn::NonNU16<1>>>(), size_of::<u16>());
assert_eq!(size_of::<Option<nonn::NonNU32<2>>>(), size_of::<u32>());
assert_eq!(size_of::<Option<nonn::NonNU64<3>>>(), size_of::<u64>());
assert_eq!(size_of::<Option<nonn::NonNU128<4>>>(), size_of::<u128>());
assert_eq!(size_of::<Option<nonn::NonNUsize<5>>>(), size_of::<usize>());
assert_eq!(size_of::<Option<nonn::NonNI8<6>>>(), size_of::<u8>());
assert_eq!(size_of::<Option<nonn::NonNI16<7>>>(), size_of::<u16>());
assert_eq!(size_of::<Option<nonn::NonNI32<8>>>(), size_of::<u32>());
assert_eq!(size_of::<Option<nonn::NonNI64<9>>>(), size_of::<u64>());
assert_eq!(size_of::<Option<nonn::NonNI128<10>>>(), size_of::<u128>());
assert_eq!(size_of::<Option<nonn::NonNIsize<11>>>(), size_of::<usize>());
```

nonn functions in no_std environments.

### Limitations

`NonN*` types will inevitably introduce many branches in most methods. If you require higher performance, it is
advisable to use either [core::num::nonzero](https://doc.rust-lang.org/src/core/num/nonzero.rs.html) or
the [nonmax](https://docs.rs/nonmax/latest/nonmax/) crate. These alternative options are more specialized
and can thus avoid many of the checks nonn uses.

nonn currently does not implement `Neg` for its types, as `Neg` on `NonNU*<N>` should in theory result in `NonNI*<-N>`.
This is currently not possible to my knowledge, even on nightly.

nonn requires at least Rust 1.57.0 to compile, but 1.67.0 or above is required for `ilog10`.
