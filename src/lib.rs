#![feature(maybe_uninit_slice)]
#![feature(generic_const_exprs)]
#![cfg_attr(bench, feature(test))]
#![cfg_attr(bench, feature(bench_black_box))]

use std::fmt;
use std::mem::MaybeUninit;

#[cfg(bench)]
extern crate test;

pub struct HexTrivial<const N: usize>(pub [u8; N]);

impl<const N: usize> fmt::Display for HexTrivial<N> where [(); N * 2]: Sized {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for b in &self.0 {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

fn byte_to_hex_digits(byte: u8) -> [u8; 2] {
    static HEX: [u8; 16] = [b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd', b'e', b'f'];
    [HEX[usize::from(byte.wrapping_shr(4))], HEX[usize::from(byte & 0x0F)]]
}

pub struct HexWithBuf<const N: usize>(pub [u8; N]);

impl<const N: usize> fmt::Display for HexWithBuf<N> where [(); N * 2]: Sized {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = [0u8; N * 2];
        for (dst, src) in buf.chunks_exact_mut(2).zip(&self.0) {
            dst.copy_from_slice(&byte_to_hex_digits(*src));
        }
        f.write_str(std::str::from_utf8(&buf).unwrap())
    }
}

pub struct UnsafeHex<const N: usize>(pub [u8; N]);

impl<const N: usize> fmt::Display for UnsafeHex<N> where [(); N * 2]: Sized {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = [0u8; N * 2];
        for (dst, src) in buf.chunks_exact_mut(2).zip(&self.0) {
            dst.copy_from_slice(&byte_to_hex_digits(*src));
        }
        f.write_str(unsafe { std::str::from_utf8_unchecked(&buf) })
    }
}

pub struct MaybeUninitHex<const N: usize>(pub [u8; N]);

impl<const N: usize> fmt::Display for MaybeUninitHex<N> where [(); N * 2]: Sized {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = [MaybeUninit::uninit(); N * 2];
        for (dst, src) in buf.chunks_exact_mut(2).zip(&self.0) {
            let bytes = byte_to_hex_digits(*src);
            dst[0] = MaybeUninit::new(bytes[0]);
            dst[1] = MaybeUninit::new(bytes[1]);
        }
        f.write_str(unsafe { std::str::from_utf8_unchecked(MaybeUninit::slice_assume_init_ref(&buf)) })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(bench)]
    struct Sink;

    #[cfg(bench)]
    impl fmt::Write for Sink {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            std::hint::black_box(s);
            Ok(())
        }
    }

    macro_rules! measure {
        ($bench_name:ident, $array:expr) => {
            #[cfg(bench)]
            mod $bench_name {
                use test::Bencher;
                use super::*;

                #[bench]
                fn sink(bencher: &mut Bencher) {
                    use std::fmt::Write;

                    let mut sink = Sink;
                    let bytes = $array;
                    bencher.iter(|| {
                        write!(sink, "{}", bytes).unwrap();
                    })
                }

                #[bench]
                fn string(bencher: &mut Bencher) {
                    let bytes = $array;
                    bencher.iter(|| {
                        std::hint::black_box(bytes.to_string());
                    })
                }
            }
        }
    }

    macro_rules! bench_and_test {
        ($test_name:ident, $array:expr) => {
            mod $test_name {
                use super::*;

                #[test]
                fn check_equal() {
                    let array = $array;
                    let a = HexTrivial(array).to_string();
                    let b = HexWithBuf(array).to_string();
                    let c = UnsafeHex(array).to_string();
                    let d = MaybeUninitHex(array).to_string();
                    assert_eq!(a, b, "a");
                    assert_eq!(b, c, "b");
                    assert_eq!(c, d, "c");
                }

                measure!(trivial, HexTrivial($array));
                measure!(with_buf, HexWithBuf($array));
                measure!(with_unsafe, UnsafeHex($array));
                measure!(maybe_uninit, MaybeUninitHex($array));
            }
        }
    }

    bench_and_test!(empty, []);
    bench_and_test!(one, [1]);
    bench_and_test!(two, [1, 2]);
    bench_and_test!(four, [1, 2, 3, 4]);
    bench_and_test!(eight, [1, 2, 3, 4, 5, 6, 7, 8]);
    bench_and_test!(sixteen, [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8]);
    bench_and_test!(thirtytwo, [1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8]);
}
