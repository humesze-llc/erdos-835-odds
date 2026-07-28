//! Optional stronger propagator (`--propagator matching`, spec section 3).
//!
//! Each closed neighbourhood is a perfect matching constraint between `k+1`
//! vertices and `k+1` colours. Régin-style filtering removes every value that
//! lies in no perfect matching, which prunes strictly more than counting:
//! counting is exactly the "a colour has one supporter" special case.
//!
//! With equal sides and a required *perfect* matching there are no free
//! vertices, so the standard characterisation collapses to: a non-matching edge
//! survives iff its two endpoints lie in the same strongly connected component
//! of the digraph that orients matching edges colour -> member and every other
//! edge member -> colour.

/// `doms[i]` is the candidate colour set of member `i`. On success `keep[i]`
/// receives the filtered domain. Returns `false` if no perfect matching exists
/// (a Hall violator).
///
/// The bipartite SCC computation is done on a graph contracted to the `n`
/// members: since the matching is perfect, every colour node has exactly one
/// incoming (matched) edge, so `member i -> colour c -> member m_color[c]` can
/// be collapsed to `i -> m_color[c]`. That turns a 34-node closure into a
/// 17-node one, which matters because this runs in the hot loop.
pub fn filter(doms: &[u32], ncol: usize, keep: &mut [u32]) -> bool {
    let n = doms.len();
    debug_assert_eq!(n, ncol);
    debug_assert!(n <= 18);

    // Cheap exits before any matching work.
    let mut union = 0u32;
    let mut total_bits = 0u32;
    let mut singletons = 0usize;
    for i in 0..n {
        let d = doms[i];
        if d == 0 {
            return false;
        }
        union |= d;
        let pc = d.count_ones();
        total_bits += pc;
        if pc == 1 {
            singletons += 1;
        }
        keep[i] = d;
    }
    if (union.count_ones() as usize) < n {
        return false; // Hall violator on the whole set
    }
    if singletons == n {
        // a permutation already, or a duplicate that Rule B has flagged
        return union.count_ones() as usize == n;
    }
    if total_bits as usize == n * n {
        return true; // every colour open to everyone: nothing is filterable
    }

    let mut m_member = [usize::MAX; 18]; // member -> colour
    let mut m_color = [usize::MAX; 18]; // colour -> member
    for i in 0..n {
        let mut seen = 0u32;
        if !augment(i, doms, &mut m_member, &mut m_color, &mut seen, ncol) {
            return false;
        }
    }

    // Contracted digraph on members: i -> j iff member i could take the colour
    // currently matched to member j.
    let mut adj = [0u32; 18];
    for i in 0..n {
        let mut rest = doms[i] & !(1u32 << m_member[i]);
        let mut a = 1u32 << i; // reflexive
        while rest != 0 {
            let c = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            if c < ncol && m_color[c] != usize::MAX {
                a |= 1u32 << m_color[c];
            }
        }
        adj[i] = a;
    }
    // transitive closure over 17 nodes
    for p in 0..n {
        let bit = 1u32 << p;
        let rp = adj[p];
        for a in adj.iter_mut().take(n) {
            if *a & bit != 0 {
                *a |= rp;
            }
        }
    }

    let mut changed = false;
    for i in 0..n {
        let mut k = 1u32 << m_member[i];
        let mut rest = doms[i] & !k;
        while rest != 0 {
            let c = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            if c >= ncol {
                continue;
            }
            let j = m_color[c];
            // (i,c) lies on an alternating cycle iff j reaches i
            if j != usize::MAX && adj[j] & (1u32 << i) != 0 {
                k |= 1u32 << c;
            }
        }
        if k != doms[i] {
            changed = true;
        }
        keep[i] = k;
    }
    let _ = changed;
    true
}

fn augment(
    i: usize,
    doms: &[u32],
    m_member: &mut [usize; 18],
    m_color: &mut [usize; 18],
    seen: &mut u32,
    ncol: usize,
) -> bool {
    let mut rest = doms[i];
    while rest != 0 {
        let c = rest.trailing_zeros() as usize;
        rest &= rest - 1;
        if c >= ncol || *seen & (1u32 << c) != 0 {
            continue;
        }
        *seen |= 1u32 << c;
        if m_color[c] == usize::MAX || augment(m_color[c], doms, m_member, m_color, seen, ncol) {
            m_color[c] = i;
            m_member[i] = c;
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_hall_violator() {
        // three members, three colours, but two members share a single colour
        let doms = [0b001u32, 0b001, 0b110];
        let mut keep = [0u32; 3];
        assert!(!filter(&doms, 3, &mut keep));
    }

    #[test]
    fn identity_is_a_fixpoint() {
        let doms = [0b001u32, 0b010, 0b100];
        let mut keep = [0u32; 3];
        assert!(filter(&doms, 3, &mut keep));
        assert_eq!(keep, doms);
    }

    #[test]
    fn prunes_beyond_counting() {
        // members 0,1 both restricted to {0,1}; member 2 open to {0,1,2}.
        // Counting sees colour 2 supported once and forces member 2 = 2 but
        // does not remove colours 0 and 1 from member 2. Matching does.
        let doms = [0b011u32, 0b011, 0b111];
        let mut keep = [0u32; 3];
        assert!(filter(&doms, 3, &mut keep));
        assert_eq!(keep[0], 0b011);
        assert_eq!(keep[1], 0b011);
        assert_eq!(keep[2], 0b100);
    }

    #[test]
    fn matching_never_removes_a_supported_value() {
        // exhaustive small check: every kept value must extend to a perfect
        // matching, and every removed value must not.
        for bits in 0u32..(1 << 9) {
            let doms = [bits & 7, (bits >> 3) & 7, (bits >> 6) & 7];
            let mut keep = [0u32; 3];
            let ok = filter(&doms, 3, &mut keep);
            let mut brute = [0u32; 3];
            let mut any = false;
            for p in [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
                if (0..3).all(|i| doms[i] & (1 << p[i]) != 0) {
                    any = true;
                    for i in 0..3 {
                        brute[i] |= 1 << p[i];
                    }
                }
            }
            assert_eq!(ok, any, "doms {doms:?}");
            if ok {
                assert_eq!(keep, brute, "doms {doms:?}");
            }
        }
    }
}
