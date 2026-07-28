//! Known designs, as literal data (spec section 7: "hardcode the designs as
//! literal data ... Do not generate them").
//!
//! Both are stored as bitmasks over the ground set `[2k-1]` and are perfect
//! 1-codes in the corresponding odd graph. They are the only two cases where a
//! real design exists to test the structure-theorem targets against.

/// The 7 lines of the Fano plane `PG(2,2)` as 3-subsets of `[7]`.
/// A perfect 1-code in `O_4` (35 vertices, m = 7).
pub const FANO: [u32; 7] = [
    0x07, // {0,1,2}
    0x19, // {0,3,4}
    0x61, // {0,5,6}
    0x2A, // {1,3,5}
    0x52, // {1,4,6}
    0x4C, // {2,3,6}
    0x34, // {2,4,5}
];

/// The 66 blocks of the Witt design `S(4,5,11)` as 5-subsets of `[11]`.
/// A perfect 1-code in `O_6` (462 vertices, m = 66).
///
/// Obtained as the derived design of `S(5,6,12)` at the point `∞` of
/// `PG(1,11)`; listed here in colex order of the point sets.
pub const WITT_S4_5_11: [u32; 66] = [
    0x20F, 0x097, 0x067, 0x507, 0x11B, 0x0AB, // {0,1,2,3,9} {0,1,2,4,7} {0,1,2,5,6} {0,1,2,8,10} {0,1,3,4,8} {0,1,3,5,7}
    0x44B, 0x433, 0x253, 0x323, 0x1C3, 0x683, // {0,1,3,6,10} {0,1,4,5,10} {0,1,4,6,9} {0,1,5,8,9} {0,1,6,7,8} {0,1,7,9,10}
    0x03D, 0x14D, 0x48D, 0x455, 0x315, 0x1A5, // {0,2,3,4,5} {0,2,3,6,8} {0,2,3,7,10} {0,2,4,6,10} {0,2,4,8,9} {0,2,5,7,8}
    0x625, 0x2C5, 0x0D9, 0x619, 0x269, 0x529, // {0,2,5,9,10} {0,2,6,7,9} {0,3,4,6,7} {0,3,4,9,10} {0,3,5,6,9} {0,3,5,8,10}
    0x389, 0x171, 0x2B1, 0x591, 0x4E1, 0x741, // {0,3,7,8,9} {0,4,5,6,8} {0,4,5,7,9} {0,4,7,8,10} {0,5,6,7,10} {0,6,8,9,10}
    0x41E, 0x12E, 0x0CE, 0x236, 0x156, 0x4A6, // {1,2,3,4,10} {1,2,3,5,8} {1,2,3,6,7} {1,2,4,5,9} {1,2,4,6,8} {1,2,5,7,10}
    0x646, 0x386, 0x07A, 0x29A, 0x62A, 0x34A, // {1,2,6,9,10} {1,2,7,8,9} {1,3,4,5,6} {1,3,4,7,9} {1,3,5,9,10} {1,3,6,8,9}
    0x58A, 0x1B2, 0x4D2, 0x712, 0x2E2, 0x562, // {1,3,7,8,10} {1,4,5,7,8} {1,4,6,7,10} {1,4,8,9,10} {1,5,6,7,9} {1,5,6,8,10}
    0x25C, 0x19C, 0x46C, 0x2AC, 0x70C, 0x0F4, // {2,3,4,6,9} {2,3,4,7,8} {2,3,5,6,10} {2,3,5,7,9} {2,3,8,9,10} {2,4,5,6,7}
    0x534, 0x694, 0x364, 0x5C4, 0x4B8, 0x338, // {2,4,5,8,10} {2,4,7,9,10} {2,5,6,8,9} {2,6,7,8,10} {3,4,5,7,10} {3,4,5,8,9}
    0x558, 0x1E8, 0x6C8, 0x670, 0x3D0, 0x7A0, // {3,4,6,8,10} {3,5,6,7,8} {3,6,7,9,10} {4,5,6,9,10} {4,6,7,8,9} {5,7,8,9,10}
];

/// The known design for `k`, if there is one.
#[allow(dead_code)]
pub fn known_code(k: u32) -> Option<&'static [u32]> {
    match k {
        4 => Some(&FANO),
        6 => Some(&WITT_S4_5_11),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shapes_are_right() {
        assert!(FANO.iter().all(|b| b.count_ones() == 3 && *b < 128));
        assert!(WITT_S4_5_11.iter().all(|b| b.count_ones() == 5 && *b < (1 << 11)));
        let mut s: Vec<u32> = WITT_S4_5_11.to_vec();
        s.sort_unstable();
        s.dedup();
        assert_eq!(s.len(), 66, "Witt blocks must be distinct");
    }

    #[test]
    fn fano_is_a_projective_plane() {
        // every pair of points lies on exactly one line
        for a in 0..7u32 {
            for b in a + 1..7u32 {
                let pair = (1 << a) | (1 << b);
                let hits = FANO.iter().filter(|l| *l & pair == pair).count();
                assert_eq!(hits, 1, "pair {a},{b}");
            }
        }
    }

    #[test]
    fn witt_is_an_s4_5_11() {
        // every 4-subset of [11] lies in exactly one block
        for a in 0..11u32 {
            for b in a + 1..11 {
                for c in b + 1..11 {
                    for d in c + 1..11 {
                        let q = (1 << a) | (1 << b) | (1 << c) | (1 << d);
                        let hits = WITT_S4_5_11.iter().filter(|bl| *bl & q == q).count();
                        assert_eq!(hits, 1, "quad {a},{b},{c},{d}");
                    }
                }
            }
        }
    }
}
