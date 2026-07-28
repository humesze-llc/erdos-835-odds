//! Maximum matching in a **general** (non-bipartite) graph — Edmonds' blossom.
//!
//! This is the propagator core for S(4,5,v). For every 3-subset `T` of `[v]`
//! the blocks through `T` induce a perfect matching on the `v-3` remaining
//! points, and those graphs are not bipartite, so Régin/Hall filtering (which
//! is what `alldifferent` uses, and what odd835 used for its closed
//! neighbourhoods) does not apply. Tutte/Edmonds does.
//!
//! Sized for `n <= 32` so adjacency is a `u32` bitmask per vertex; at `v = 21`
//! every graph has 18 vertices and at most 153 edges.

const MAXN: usize = 32;

pub struct Blossom {
    n: usize,
    adj: [u32; MAXN],
    mate: [i32; MAXN],
    p: [i32; MAXN],
    base: [usize; MAXN],
    used: [bool; MAXN],
    blos: [bool; MAXN],
    lca_seen: [bool; MAXN],
    queue: Vec<usize>,
}

impl Default for Blossom {
    fn default() -> Self {
        Self::new()
    }
}

impl Blossom {
    pub fn new() -> Blossom {
        Blossom {
            n: 0,
            adj: [0; MAXN],
            mate: [-1; MAXN],
            p: [-1; MAXN],
            base: [0; MAXN],
            used: [false; MAXN],
            blos: [false; MAXN],
            lca_seen: [false; MAXN],
            queue: Vec::with_capacity(MAXN),
        }
    }

    pub fn reset(&mut self, n: usize) {
        debug_assert!(n <= MAXN);
        self.n = n;
        for i in 0..n {
            self.adj[i] = 0;
            self.mate[i] = -1;
        }
    }

    #[inline]
    pub fn add_edge(&mut self, a: usize, b: usize) {
        self.adj[a] |= 1u32 << b;
        self.adj[b] |= 1u32 << a;
    }

    /// Lowest common ancestor of `a` and `b` in the alternating forest,
    /// walking by blossom base.
    fn lca(&mut self, a: usize, b: usize) -> usize {
        for i in 0..self.n {
            self.lca_seen[i] = false;
        }
        let mut cur = a;
        loop {
            cur = self.base[cur];
            self.lca_seen[cur] = true;
            if self.mate[cur] < 0 {
                break;
            }
            cur = self.p[self.mate[cur] as usize] as usize;
        }
        let mut cur = b;
        loop {
            cur = self.base[cur];
            if self.lca_seen[cur] {
                return cur;
            }
            cur = self.p[self.mate[cur] as usize] as usize;
        }
    }

    fn mark_path(&mut self, mut v: usize, b: usize, mut child: usize) {
        while self.base[v] != b {
            self.blos[self.base[v]] = true;
            let m = self.mate[v];
            debug_assert!(m >= 0);
            let m = m as usize;
            self.blos[self.base[m]] = true;
            self.p[v] = child as i32;
            child = m;
            debug_assert!(self.p[m] >= 0);
            v = self.p[m] as usize;
        }
    }

    /// Grow an alternating tree from `root`; returns the far endpoint of an
    /// augmenting path, or -1.
    fn find_path(&mut self, root: usize) -> i32 {
        for i in 0..self.n {
            self.used[i] = false;
            self.p[i] = -1;
            self.base[i] = i;
        }
        self.used[root] = true;
        self.queue.clear();
        self.queue.push(root);
        let mut qi = 0;
        while qi < self.queue.len() {
            let v = self.queue[qi];
            qi += 1;
            let mut rest = self.adj[v];
            while rest != 0 {
                let to = rest.trailing_zeros() as usize;
                rest &= rest - 1;
                if self.base[v] == self.base[to] || self.mate[v] == to as i32 {
                    continue;
                }
                if to == root || (self.mate[to] >= 0 && self.p[self.mate[to] as usize] >= 0) {
                    // odd cycle -> contract the blossom
                    let curbase = self.lca(v, to);
                    for i in 0..self.n {
                        self.blos[i] = false;
                    }
                    self.mark_path(v, curbase, to);
                    self.mark_path(to, curbase, v);
                    for i in 0..self.n {
                        if self.blos[self.base[i]] {
                            self.base[i] = curbase;
                            if !self.used[i] {
                                self.used[i] = true;
                                self.queue.push(i);
                            }
                        }
                    }
                } else if self.p[to] < 0 {
                    self.p[to] = v as i32;
                    if self.mate[to] < 0 {
                        return to as i32;
                    }
                    let m = self.mate[to] as usize;
                    self.used[m] = true;
                    self.queue.push(m);
                }
            }
        }
        -1
    }

    fn augment(&mut self, endpoint: usize) {
        let mut u = endpoint;
        loop {
            let pv = self.p[u] as usize;
            let ppv = self.mate[pv];
            self.mate[u] = pv as i32;
            self.mate[pv] = u as i32;
            if ppv < 0 {
                break;
            }
            u = ppv as usize;
        }
    }

    pub fn max_matching(&mut self) -> usize {
        // greedy seed, so augmentation has less to do
        for v in 0..self.n {
            if self.mate[v] < 0 {
                let mut rest = self.adj[v];
                while rest != 0 {
                    let to = rest.trailing_zeros() as usize;
                    rest &= rest - 1;
                    if self.mate[to] < 0 {
                        self.mate[v] = to as i32;
                        self.mate[to] = v as i32;
                        break;
                    }
                }
            }
        }
        for v in 0..self.n {
            if self.mate[v] < 0 {
                let e = self.find_path(v);
                if e >= 0 {
                    self.augment(e as usize);
                }
            }
        }
        (0..self.n).filter(|&i| self.mate[i] >= 0).count() / 2
    }

    pub fn has_perfect_matching(&mut self) -> bool {
        if self.n % 2 != 0 {
            return false;
        }
        if self.n == 0 {
            return true;
        }
        self.max_matching() * 2 == self.n
    }

    /// The matching found by the last `max_matching` call.
    pub fn mate_of(&self, v: usize) -> i32 {
        self.mate[v]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pm(n: usize, edges: &[(usize, usize)]) -> bool {
        let mut b = Blossom::new();
        b.reset(n);
        for &(x, y) in edges {
            b.add_edge(x, y);
        }
        b.has_perfect_matching()
    }

    #[test]
    fn trivial_cases() {
        assert!(pm(0, &[]));
        assert!(!pm(2, &[]));
        assert!(pm(2, &[(0, 1)]));
        assert!(!pm(3, &[(0, 1), (1, 2), (0, 2)]), "odd order has no perfect matching");
    }

    #[test]
    fn needs_blossom_contraction() {
        // Two triangles joined by a bridge: 0-1-2-0, 3-4-5-3, bridge 2-3.
        // A bipartite-only algorithm mishandles the odd cycles; the true
        // answer is that no perfect matching exists (6 vertices, but each
        // triangle needs an odd number matched outward and only one bridge).
        let e = [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (2, 3)];
        assert!(pm(6, &e));
        // remove the bridge -> two odd components, impossible
        let e2 = [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)];
        assert!(!pm(6, &e2));
    }

    #[test]
    fn tutte_violation_is_detected() {
        // star K_{1,3} plus pendant: vertex 0 joined to 1,2,3; 4,5 joined.
        // Removing 0 leaves 3 isolated odd components -> no perfect matching.
        assert!(!pm(6, &[(0, 1), (0, 2), (0, 3), (4, 5)]));
    }

    #[test]
    fn complete_even_graphs_always_match() {
        for n in [2usize, 4, 6, 8, 10, 12, 16, 18] {
            let mut e = Vec::new();
            for a in 0..n {
                for b in a + 1..n {
                    e.push((a, b));
                }
            }
            assert!(pm(n, &e), "K_{n} must have a perfect matching");
        }
    }

    /// Cross-check blossom against exhaustive search on random small graphs.
    #[test]
    fn agrees_with_brute_force() {
        fn brute(n: usize, adj: &[u32]) -> bool {
            fn go(rem: u32, adj: &[u32]) -> bool {
                if rem == 0 {
                    return true;
                }
                let u = rem.trailing_zeros() as usize;
                let mut cand = adj[u] & rem & !(1 << u);
                while cand != 0 {
                    let w = cand.trailing_zeros();
                    cand &= cand - 1;
                    if go(rem & !(1 << u) & !(1 << w), adj) {
                        return true;
                    }
                }
                false
            }
            go((1u32 << n) - 1, adj)
        }

        let mut state = 0x243F6A8885A308D3u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for n in [4usize, 6, 8, 10] {
            for _ in 0..300 {
                let mut adj = vec![0u32; n];
                let mut edges = Vec::new();
                for a in 0..n {
                    for b in a + 1..n {
                        if next() % 100 < 45 {
                            adj[a] |= 1 << b;
                            adj[b] |= 1 << a;
                            edges.push((a, b));
                        }
                    }
                }
                assert_eq!(
                    pm(n, &edges),
                    brute(n, &adj),
                    "disagreement on n={n} edges={edges:?}"
                );
            }
        }
    }
}
