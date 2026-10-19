//! One-signer tiers: a pruned key generated once and stored with a node cache of bounded size, from which every
//! signature recomputes only what is not cached (sphincs-art, "One signer, leanSphincs-S").
//!
//! | Tier       | kept subtree | cache  | plan              | auth path per signature: calls | permutations |
//! |------------|-------------:|-------:|-------------------|-------------------------------:|-------------:|
//! | `Light`    | `2^13`       | 16 KiB | level 3 only      | 2,830                          | 2,886        |
//! | `Standard` | `2^20`       | 1 MiB  | top levels 5..20  | 7,231                          | 7,455        |
//! | `Full`     | `2^26`       | 16 MiB | top levels 7..26  | 28,927                         | 29,823       |
//!
//! Any `b <= h` and budget also works ([`Tier::Custom`]). The keys, the randomizer grind and the counter are those of
//! [`key_gen`] and [`sign`]: [`sign_with_cache`] gives the same bytes as `sign(&key_gen(seed, b).0, m)`. Only where the
//! authentication path comes from changes.
//!
//! # The cache plan
//!
//! The budget buys `cache_bytes / 16` nodes of the kept subtree (levels `0..=b`, level 0 the leaves). The plan is the
//! cheapest by `tree_cost` of sphincs-art's `sweep_leansphincs_pruned.py`, counted in keccak256 calls (a WOTS leaf is
//! [`WOTS_LEAF_CALLS`] `= 225`, a node 1). Counted in Keccak-f permutations, as sphincs-art's `keccak_model.py` calls
//! `tree_cost` (a WOTS leaf is [`WOTS_LEAF_PERMUTATIONS`] `= 232`, a node 1), the same plan is the cheapest for every
//! `b` and budget. The only comparison the leaf's cost can decide is `top levels c + 1..b` against `level c only`
//! (`level c only` is the cheaper iff `2^(b - 2c) <= leaf + 1`), and no power of two lies in `226..=233`.
//!
//! - the whole subtree, `2^(b+1) - 1` nodes, if it fits: a signature recomputes nothing (0 calls);
//! - top levels `c..=b`, `2^(b-c+1) - 1` nodes: a signature recomputes the `2^c`-leaf bottom subtree that holds its leaf
//!   (`2^c * 225 + 2^c - 1` calls) and reads the path's levels `c..b` from the cache;
//! - level `c` only, `2^(b-c)` nodes: the bottom subtree as above, plus the `2^(b-c) - 1` nodes above level `c`;
//! - none: a signature recomputes the whole kept subtree (`2^b * 225 + 2^b - 1` calls).
//!
//! Tie-breaking: the candidates are taken in the sweep's order (none; then for `c = 1, 2, ..., b`: top levels `c..=b`,
//! then level `c` only), and one replaces the best so far only if it is strictly cheaper, as Python's `min` keeps the
//! first of equal values. The only ties are top levels `b..=b` and level `b` (the kept subtree's root alone) against no
//! cache, and none wins them: the key stores that root anyway (below).
//!
//! The path's levels `b..h` are the stored surrogates.
//!
//! # What is checked
//!
//! Loading a key file checks every cached node (see [`keyfile`] for what that does and does not prove). At signing,
//! the recomputed bottom subtree is checked against the cached node at its root (or, with no cache, against the kept
//! subtree's root), and with a `level c only` cache the rehashed levels above `c` are checked against the kept
//! subtree's root, at no extra hash. A `top levels` path reads its levels `c..b` straight from the
//! cache, and a `whole subtree` path reads everything from it. Last, [`sign_with_cache`] verifies the signature under
//! the key's public key ([`VERIFY_KECCAK_CALLS`] calls, [`VERIFY_PERMUTATIONS`] permutations, reported apart from the
//! signature's cost) and returns an error rather than a signature that does not verify under the key's root.
//!
//! # Keygen
//!
//! [`keygen_cached`] streams the kept subtree: it splits it into `2^t` chunks (about four per thread), runs a
//! stack-based treehash per chunk on its own thread that records only the nodes the plan keeps, then hashes the chunk
//! roots up the last `t` levels. Its memory is the cache, the `2^t` chunk roots and a `b + 1`-node stack per thread
//! (and writing the key file streams it: [`CachedKey::write_to`]). It spends exactly what [`key_gen`] spends,
//! [`keygen_calls`]`(b) = 2^b * 226 + 2 (26 - b)` keccak256 calls and [`keygen_permutations`]`(b) = 2^b * 233 +
//! 2 (26 - b)` permutations, and reaches the same root. (sphincs-art's `tier_costs` counts `2^b` nodes in a
//! `2^b`-leaf tree, which has `2^b - 1`: its keygen figures, `1 + 2^b * 226 + 2 (26 - b)` calls and
//! `1 + 2^b * 233 + 2 (26 - b)` permutations, are one more.)
//!
//! # One seed, one key
//!
//! `P`, the WOTS and FORS keys and the real tree nodes depend on the seed and the leaf index only, not on `b`. Keys
//! from one seed at two different `b` (or this signer and the stateless [`sign`] at another `b`) are related: where
//! their kept subtrees overlap (always, against a full key), a signature of one becomes a signature of the other by
//! swapping in public path nodes, so the stronger key falls to the weaker one's lifetime. Use one fresh seed per key.
//!
//! The key file's byte layout is in [`keyfile`].

use std::cell::Cell;
use std::fmt;
use std::ops::Range;
use std::sync::Mutex;

use crate::*;

/// A signer tier: the kept subtree's height `b` and the node cache's budget in bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Tier {
    /// A kept subtree of `2^13` leaves and a 16 KiB cache: the page's Ledger Nano S+ class tier. (The page's Keccak
    /// times for it, 5.5 min to generate and 27 s to sign at 5.8K permutations per second, are estimates; this crate is
    /// a host-side reference signer.)
    Light,
    /// `2^20` leaves and a 1 MiB cache.
    Standard,
    /// The whole tree, `2^26` leaves, and a 16 MiB cache.
    Full,
    /// Any `b <= h` and budget.
    Custom { b: usize, cache_bytes: u64 },
}

impl Tier {
    pub const PRESETS: [Tier; 3] = [Tier::Light, Tier::Standard, Tier::Full];

    pub fn b(self) -> usize {
        match self {
            Tier::Light => 13,
            Tier::Standard => 20,
            Tier::Full => H,
            Tier::Custom { b, .. } => b,
        }
    }

    pub fn cache_bytes(self) -> u64 {
        match self {
            Tier::Light => 16 << 10,
            Tier::Standard => 1 << 20,
            Tier::Full => 16 << 20,
            Tier::Custom { cache_bytes, .. } => cache_bytes,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Tier::Light => "light",
            Tier::Standard => "standard",
            Tier::Full => "full",
            Tier::Custom { .. } => "custom",
        }
    }

    /// A preset by its [`name`](Self::name).
    pub fn preset(name: &str) -> Option<Self> {
        Self::PRESETS.into_iter().find(|tier| tier.name() == name)
    }

    /// The nodes the budget buys: whole 16-byte nodes.
    pub fn cache_nodes(self) -> u64 {
        self.cache_bytes() / N as u64
    }

    pub fn plan(self) -> CachePlan {
        CachePlan::choose(self.b(), self.cache_nodes())
    }
}

/// Which levels of the kept subtree (`0..=b`, level 0 the leaves) a key stores, and so what a signature recomputes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CachePlan {
    /// No node: a signature recomputes the whole kept subtree.
    None,
    /// Levels `c..=b`: a signature recomputes the `2^c`-leaf bottom subtree that holds its leaf.
    Top(usize),
    /// Level `c`: a signature recomputes its bottom subtree, and the levels above `c` from the cached ones.
    Level(usize),
    /// Levels `0..=b`: a signature recomputes nothing.
    Whole,
}

impl CachePlan {
    /// The plan of least [`auth_path_calls`](Self::auth_path_calls) that fits in `cache_nodes` nodes (module doc). It is
    /// also the plan of least [`auth_path_permutations`](Self::auth_path_permutations).
    pub fn choose(b: usize, cache_nodes: u64) -> Self {
        assert!(b <= H);
        if CachePlan::Whole.nodes(b) <= cache_nodes {
            return CachePlan::Whole;
        }
        let mut best = CachePlan::None;
        for c in 1..=b {
            for plan in [CachePlan::Top(c), CachePlan::Level(c)] {
                if plan.nodes(b) <= cache_nodes && plan.auth_path_calls(b) < best.auth_path_calls(b) {
                    best = plan;
                }
            }
        }
        best
    }

    /// Whether the plan exists for a kept subtree of height `b`.
    pub fn fits(self, b: usize) -> bool {
        match self {
            CachePlan::Top(c) | CachePlan::Level(c) => (1..=b).contains(&c),
            CachePlan::None | CachePlan::Whole => true,
        }
    }

    /// The cached levels, lowest first.
    pub fn levels(self, b: usize) -> Range<usize> {
        debug_assert!(self.fits(b));
        match self {
            CachePlan::None => 0..0,
            CachePlan::Top(c) => c..b + 1,
            CachePlan::Level(c) => c..c + 1,
            CachePlan::Whole => 0..b + 1,
        }
    }

    /// The number of cached nodes.
    pub fn nodes(self, b: usize) -> u64 {
        self.levels(b).map(|level| 1u64 << (b - level)).sum()
    }

    /// The height of the bottom subtree that a signature recomputes from the seed.
    fn bottom(self, b: usize) -> usize {
        match self {
            CachePlan::None => b,
            CachePlan::Top(c) | CachePlan::Level(c) => c,
            CachePlan::Whole => 0,
        }
    }

    /// keccak256 calls of one authentication path: sphincs-art's `tree_cost` for this plan.
    pub fn auth_path_calls(self, b: usize) -> u64 {
        self.auth_path_cost(b, WOTS_LEAF_CALLS)
    }

    /// Keccak-f permutations of one authentication path: `keccak_model.py`'s `tree_cost` for this plan.
    pub fn auth_path_permutations(self, b: usize) -> u64 {
        self.auth_path_cost(b, WOTS_LEAF_PERMUTATIONS)
    }

    /// The authentication path's cost when a WOTS leaf costs `leaf` and a node 1.
    fn auth_path_cost(self, b: usize, leaf: u64) -> u64 {
        let subtree = |height: usize| (1u64 << height) * leaf + (1 << height) - 1;
        match self {
            CachePlan::Whole => 0,
            CachePlan::Level(c) => subtree(c) + (1 << (b - c)) - 1,
            plan => subtree(plan.bottom(b)),
        }
    }

    /// [`auth_path_calls`](Self::auth_path_calls) and [`auth_path_permutations`](Self::auth_path_permutations).
    pub fn auth_path_work(self, b: usize) -> Work {
        Work { calls: self.auth_path_calls(b), permutations: self.auth_path_permutations(b) }
    }

    /// `none`, `top levels c..b`, `level c only` or `whole subtree`.
    pub fn describe(self, b: usize) -> String {
        match self {
            CachePlan::None => "none".into(),
            CachePlan::Top(c) => format!("top levels {c}..{b}"),
            CachePlan::Level(c) => format!("level {c} only"),
            CachePlan::Whole => "whole subtree".into(),
        }
    }
}

/// sphincs-art's `tree_cost(b, cache_nodes)` in keccak256 calls: the authentication-path work of one signature.
pub fn tree_cost(b: usize, cache_nodes: u64) -> u64 {
    CachePlan::choose(b, cache_nodes).auth_path_calls(b)
}

/// keccak256 calls of [`key_gen`] and [`keygen_cached`]: `P`, `2^b` leaves, `2^b - 1` nodes, and a derivation and a node
/// per surrogate.
pub fn keygen_calls(b: usize) -> u64 {
    assert!(b <= H);
    (1u64 << b) * (WOTS_LEAF_CALLS + 1) + 2 * (H - b) as u64
}

/// Keccak-f permutations of the same: every call is one permutation but a leaf's, [`WOTS_LEAF_PERMUTATIONS`].
pub fn keygen_permutations(b: usize) -> u64 {
    assert!(b <= H);
    (1u64 << b) * (WOTS_LEAF_PERMUTATIONS + 1) + 2 * (H - b) as u64
}

/// [`keygen_calls`] and [`keygen_permutations`].
pub fn keygen_work(b: usize) -> Work {
    Work { calls: keygen_calls(b), permutations: keygen_permutations(b) }
}

/// A key generated once and kept with its node cache: everything a signature needs. The fields are checked against
/// each other when the key is generated or loaded, so they are read-only.
#[derive(Clone, PartialEq, Eq)]
pub struct CachedKey {
    pub(crate) tier: Tier,
    pub(crate) b: usize,
    pub(crate) s: u64,
    pub(crate) plan: CachePlan,
    pub(crate) public_param: PublicParam,
    pub(crate) root: Digest,
    /// The kept subtree's root (level `b`): what the cache and every recomputed bottom subtree are checked against.
    pub(crate) subtree_root: Digest,
    /// Levels `b..h`.
    pub(crate) surrogates: Vec<Digest>,
    pub(crate) master: MasterSecret,
    /// The plan's levels, lowest first: `cache[k][j]` is node `j` from the left of level `plan.levels(b).start + k`.
    pub(crate) cache: Vec<Vec<Digest>>,
}

/// The secret stays out of `{:?}`.
impl fmt::Debug for CachedKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CachedKey")
            .field("tier", &self.tier)
            .field("b", &self.b)
            .field("s", &self.s)
            .field("plan", &self.plan)
            .field("public_key", &self.public_key())
            .finish_non_exhaustive()
    }
}

impl CachedKey {
    pub fn tier(&self) -> Tier {
        self.tier
    }

    pub fn b(&self) -> usize {
        self.b
    }

    /// The kept subtree holds leaves `s * 2^b .. (s + 1) * 2^b`.
    pub fn s(&self) -> u64 {
        self.s
    }

    pub fn plan(&self) -> CachePlan {
        self.plan
    }

    pub fn public_key(&self) -> PublicKey {
        PublicKey { root: self.root, public_param: self.public_param }
    }

    pub fn subtree_root(&self) -> Digest {
        self.subtree_root
    }

    pub fn surrogates(&self) -> &[Digest] {
        &self.surrogates
    }

    pub fn cache_nodes(&self) -> u64 {
        self.plan.nodes(self.b)
    }

    pub fn contains(&self, idx: u64) -> bool {
        idx >> self.b == self.s
    }

    /// Cached level `level`, which the plan must keep.
    fn level(&self, level: usize) -> &[Digest] {
        &self.cache[level - self.plan.levels(self.b).start]
    }

    /// The authentication path of leaf `idx`, which must be kept, in exactly [`CachePlan::auth_path_calls`] keccak256
    /// calls and [`CachePlan::auth_path_permutations`] permutations: levels below `c` from the bottom subtree recomputed
    /// from the seed, levels `c..b` from the cache, levels `b..h` the surrogates. `Err` if a recomputed node does not
    /// match the cache.
    pub fn auth_path(&self, idx: u64) -> Result<[Digest; H], KeyError> {
        assert!(self.contains(idx), "leaf {idx} is not in the kept subtree");
        let (pp, b, plan) = (&self.public_param, self.b, self.plan);
        let local = (idx - (self.s << b)) as usize;
        let mut path = [[0u8; N]; H];
        path[b..].copy_from_slice(&self.surrogates);
        if plan == CachePlan::Whole {
            for level in 0..b {
                path[level] = self.level(level)[(local >> level) ^ 1];
            }
            return Ok(path);
        }
        let c = plan.bottom(b);
        let is_sibling = |level: usize, j: u64| level < c && j == (idx >> level) ^ 1;
        let threads = available_threads().min(MAX_THREADS);
        let jobs = vec![Vec::new(); 1 << chunk_bits(c, threads)];
        let (bottom_root, found) = par_treehash(
            pp,
            &self.master,
            (idx >> c) << c,
            threads,
            c,
            jobs,
            |found: &mut Vec<(usize, Digest)>, level, j, node| {
                if is_sibling(level, j) {
                    found.push((level, *node));
                }
            },
            |level, j, node| {
                if is_sibling(level, j) {
                    path[level] = *node;
                }
            },
        );
        for (level, node) in found.into_iter().flatten() {
            path[level] = node;
        }
        let expected = if plan == CachePlan::None { self.subtree_root } else { self.level(c)[local >> c] };
        if bottom_root != expected {
            return Err(KeyError::Cache { level: c, index: idx >> c });
        }
        match plan {
            CachePlan::Top(c) => {
                for level in c..b {
                    path[level] = self.level(level)[(local >> level) ^ 1];
                }
            }
            CachePlan::Level(c) => {
                // The first row is read in place: the rows hashed above it are half the cache at most.
                let mut computed: Vec<Digest>;
                let mut row: &[Digest] = self.level(c);
                for level in c..b {
                    path[level] = row[(local >> level) ^ 1];
                    let first = self.s << (b - level - 1);
                    computed = (0..row.len() / 2)
                        .map(|j| xmss_node(pp, level + 1, first + j as u64, &row[2 * j], &row[2 * j + 1]))
                        .collect();
                    row = &computed;
                }
                if row[0] != self.subtree_root {
                    return Err(KeyError::Cache { level: b, index: self.s });
                }
            }
            CachePlan::None | CachePlan::Whole => {}
        }
        Ok(path)
    }
}

/// The most threads [`keygen_cached`] and [`CachedKey::auth_path`] use; more are clamped to it. (`lssk keygen
/// --threads` refuses more.)
pub const MAX_THREADS: usize = 1024;

/// `log2` of the number of chunks a subtree of height `height` is split into: about four per thread, which keeps the
/// cores busy when one falls behind, and never more than its leaves. `ceil(log2(threads)) + 2`, with no overflow for
/// any `threads`.
fn chunk_bits(height: usize, threads: usize) -> usize {
    let ceil_log2 = (usize::BITS - (threads.max(1) - 1).leading_zeros()) as usize;
    (ceil_log2 + 2).min(height)
}

/// The root of the subtree of height `height` whose leaves are the one-time keys `first..first + 2^height`, by the
/// stack-based treehash: at most `height + 1` nodes live at a time. `visit(level, j, node)` sees every node, the leaves
/// (level 0) and the root included, with its tree-wide index `j` at its level.
fn treehash(
    pp: &PublicParam,
    master: &MasterSecret,
    first: u64,
    height: usize,
    mut visit: impl FnMut(usize, u64, &Digest),
) -> Digest {
    debug_assert_eq!(first % (1 << height), 0);
    let mut stack: Vec<(usize, Digest)> = Vec::with_capacity(height + 1);
    for e in first..first + (1 << height) {
        let mut node = wots_leaf(pp, master, e as u32);
        visit(0, e, &node);
        let mut level = 0;
        while stack.last().is_some_and(|&(below, _)| below == level) {
            let (_, left) = stack.pop().unwrap();
            level += 1;
            node = xmss_node(pp, level, e >> level, &left, &node);
            visit(level, e >> level, &node);
        }
        stack.push((level, node));
    }
    stack.pop().unwrap().1
}

/// [`treehash`] of the subtree of height `height` at leaf `first`, on `threads` threads. The subtree is split into
/// `jobs.len() = 2^t` chunks of height `height - t`, each a treehash on one thread with its own state `jobs[i]` for
/// `visit`; `visit_top` sees the nodes of the last `t` levels, which hash the chunk roots together. The keccak256 calls
/// and the permutations of the workers are added to this thread's counts ([`par_map_on`]).
fn par_treehash<J: Send>(
    pp: &PublicParam,
    master: &MasterSecret,
    first: u64,
    threads: usize,
    height: usize,
    jobs: Vec<J>,
    visit: impl Fn(&mut J, usize, u64, &Digest) + Sync,
    mut visit_top: impl FnMut(usize, u64, &Digest),
) -> (Digest, Vec<J>) {
    assert!(jobs.len().is_power_of_two() && jobs.len() <= 1 << height);
    let chunk = height - jobs.len().trailing_zeros() as usize;
    let jobs: Vec<Mutex<Option<J>>> = jobs.into_iter().map(|job| Mutex::new(Some(job))).collect();
    let done = par_map_on(threads, jobs.len(), |i| {
        let mut job = jobs[i].lock().unwrap().take().unwrap();
        let root = treehash(pp, master, first + ((i as u64) << chunk), chunk, |level, j, node| {
            visit(&mut job, level, j, node)
        });
        (root, job)
    });
    let (mut row, jobs): (Vec<Digest>, Vec<J>) = done.into_iter().unzip();
    for level in chunk + 1..=height {
        let first = first >> level;
        row = (0..row.len() / 2)
            .map(|j| {
                let node = xmss_node(pp, level, first + j as u64, &row[2 * j], &row[2 * j + 1]);
                visit_top(level, first + j as u64, &node);
                node
            })
            .collect();
    }
    (row[0], jobs)
}

/// `Gen` for a tier, streaming (module doc): the key [`key_gen`] gives for `(seed, tier.b())`, with the cache of
/// `tier.plan()`, on `threads` threads (at most [`MAX_THREADS`]), in [`keygen_calls`] keccak256 calls and
/// [`keygen_permutations`] permutations. The key does not depend on `threads`.
pub fn keygen_cached(seed: &MasterSecret, tier: Tier, threads: usize) -> CachedKey {
    let b = tier.b();
    assert!(b <= H, "b = {b} is above h = {H}");
    let threads = threads.clamp(1, MAX_THREADS);
    let plan = tier.plan();
    let public_param = derive_public_param(seed);
    let pp = &public_param;
    let s = subtree_position(pp, b);
    let levels = plan.levels(b);
    let mut cache: Vec<Vec<Digest>> = levels.clone().map(|level| vec![[0; N]; 1 << (b - level)]).collect();
    let t = chunk_bits(b, threads);
    let chunk = b - t;
    // The cached levels up to the chunks' height are filled by the chunks, each its own run of every such level; the
    // levels above, from the chunk roots.
    let in_chunks = (chunk + 1).saturating_sub(levels.start).min(levels.len());
    let (low, high) = cache.split_at_mut(in_chunks);
    let mut runs: Vec<_> =
        low.iter_mut().zip(levels.clone()).map(|(row, level)| row.chunks_mut(1 << (chunk - level))).collect();
    let jobs: Vec<Vec<&mut [Digest]>> =
        (0..1 << t).map(|_| runs.iter_mut().map(|run| run.next().unwrap()).collect()).collect();
    let (subtree_root, _) = par_treehash(
        pp,
        seed,
        s << b,
        threads,
        b,
        jobs,
        |runs: &mut Vec<&mut [Digest]>, level, j, node| {
            if let Some(run) = level.checked_sub(levels.start).and_then(|k| runs.get_mut(k)) {
                run[j as usize & ((1 << (chunk - level)) - 1)] = *node;
            }
        },
        |level, j, node| {
            if let Some(row) = level.checked_sub(levels.start + in_chunks).and_then(|k| high.get_mut(k)) {
                row[(j - (s << (b - level))) as usize] = *node;
            }
        },
    );
    let surrogates = derive_surrogates(pp, seed, b);
    let root = fold_surrogates(pp, b, s, subtree_root, &surrogates);
    CachedKey { tier, b, s, plan, public_param, root, subtree_root, surrogates, master: *seed, cache }
}

/// What one signature spent, in keccak256 calls and Keccak-f permutations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignCost {
    /// The signature itself: what [`sign`] spends for the same key and message, with the authentication path's work in
    /// place of reading it from the in-memory tree. The verification below is not in it.
    pub total: Work,
    /// Of which the authentication path: [`CachePlan::auth_path_work`].
    pub auth_path: Work,
    /// Randomizers tried, `i + 1` (one call and one permutation each).
    pub attempts: u64,
    /// The check that the signature verifies under the key's public key: [`VERIFY_KECCAK_CALLS`] calls and
    /// [`VERIFY_PERMUTATIONS`] permutations.
    pub verify: Work,
}

/// `Sign` from a cached key: [`sign`]'s bytes for the same seed, `b` and message, with the path from
/// [`CachedKey::auth_path`]. The signature is verified under the key's public key before it is returned:
/// `Err(`[`KeyError::Signature`]`)` if it does not verify, which happens only if the key's root or cache is not its
/// seed's (a consistently re-sealed key file, or memory corrupted after loading).
pub fn sign_with_cache(key: &CachedKey, m: &Message) -> Result<Signature, KeyError> {
    sign_with_cache_cost(key, m).map(|(sig, _)| sig)
}

/// [`sign_with_cache`], and what it spent.
pub fn sign_with_cache_cost(key: &CachedKey, m: &Message) -> Result<(Signature, SignCost), KeyError> {
    let (before, attempts, auth_path) = (work(), Cell::new(0), Cell::new(Work::default()));
    let contains = |idx| {
        attempts.set(attempts.get() + 1);
        key.contains(idx)
    };
    let path = |idx| {
        let before = work();
        let path = key.auth_path(idx);
        auth_path.set(work() - before);
        path
    };
    let sig = sign_with(&key.public_param, &key.master, m, contains, path)?;
    let total = work() - before;
    let before = work();
    let verified = verify(&key.public_key(), m, &sig);
    let verify_work = work() - before;
    verified.map_err(|_| KeyError::Signature)?;
    Ok((sig, SignCost { total, auth_path: auth_path.get(), attempts: attempts.get(), verify: verify_work }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed(x: u8) -> MasterSecret {
        std::array::from_fn(|i| x.wrapping_mul(29).wrapping_add(3 * i as u8))
    }

    /// `tree_cost` of sweep_leansphincs_pruned.py, transcribed line for line (NODE = 1). keccak256 calls take
    /// LEAF = 225; keccak_model.py calls it in permutations with LEAF = 232.
    fn sweep_tree_cost(height: usize, cache_nodes: u64, leaf: u64) -> u64 {
        let node = 1u64;
        if (1u64 << (height + 1)) - 1 <= cache_nodes {
            return 0;
        }
        let mut best = (1u64 << height) * leaf + ((1u64 << height) - 1) * node;
        for c in 1..=height {
            let below = (1u64 << c) * leaf + ((1u64 << c) - 1) * node;
            if (1u64 << (height - c + 1)) - 1 <= cache_nodes {
                best = best.min(below);
            }
            if 1u64 << (height - c) <= cache_nodes {
                best = best.min(below + ((1u64 << (height - c)) - 1) * node);
            }
        }
        best
    }

    /// sphincs-art's keygen figure (`tier_costs`, keccak_model.py's `tiers`), for a WOTS leaf of `leaf`: one more node
    /// than a `2^b`-leaf tree has.
    fn sweep_keygen(b: usize, leaf: u64) -> u64 {
        1 + (1u64 << b) * (leaf + 1) + 2 * (H - b) as u64
    }

    /// 0 and 1 node, every threshold of the rule and its neighbours, and a large cache.
    fn cache_sizes(b: usize) -> Vec<u64> {
        let mut thresholds = vec![0, 1, (1u64 << (b + 1)) - 1];
        for c in 1..=b {
            thresholds.extend([(1u64 << (b - c + 1)) - 1, 1u64 << (b - c)]);
        }
        let mut sizes: Vec<u64> = thresholds.iter().flat_map(|&t| [t.saturating_sub(1), t, t + 1]).collect();
        sizes.push(1 << 40);
        sizes.sort_unstable();
        sizes.dedup();
        sizes
    }

    #[test]
    fn plan_is_the_sweeps_tree_cost() {
        for b in 0..=H {
            for nodes in cache_sizes(b) {
                let plan = CachePlan::choose(b, nodes);
                assert!(plan.fits(b) && plan.nodes(b) <= nodes, "b {b}, {nodes} nodes: {plan:?}");
                assert_eq!(plan.auth_path_calls(b), sweep_tree_cost(b, nodes, 225), "b {b}, {nodes} nodes: {plan:?}");
                assert_eq!(tree_cost(b, nodes), sweep_tree_cost(b, nodes, 225));
                // Chosen by calls, the plan is also the cheapest in permutations (module doc).
                let permutations = sweep_tree_cost(b, nodes, 232);
                assert_eq!(plan.auth_path_permutations(b), permutations, "b {b}, {nodes} nodes: {plan:?}");
            }
            // The ties: the kept subtree's root alone recomputes as much as no cache.
            assert_eq!(CachePlan::choose(b, 0), CachePlan::None);
            if b > 0 {
                assert_eq!(CachePlan::choose(b, 1), CachePlan::None);
                assert_eq!(CachePlan::Top(b).auth_path_calls(b), CachePlan::None.auth_path_calls(b));
                assert_eq!(CachePlan::Level(b).auth_path_calls(b), CachePlan::None.auth_path_calls(b));
            }
            assert_eq!(CachePlan::choose(b, (1 << (b + 1)) - 1), CachePlan::Whole);
            assert_eq!(keygen_calls(b) + 1, sweep_keygen(b, 225));
            assert_eq!(keygen_permutations(b) + 1, sweep_keygen(b, 232));
        }
        // Every pair of distinct plans other than those differs in cost.
        for b in 1..=H {
            let mut plans = vec![CachePlan::Whole];
            plans.extend((1..b).flat_map(|c| [CachePlan::Top(c), CachePlan::Level(c)]));
            plans.push(CachePlan::None);
            for cost in [CachePlan::auth_path_calls, CachePlan::auth_path_permutations] {
                let mut costs: Vec<u64> = plans.iter().map(|&plan| cost(plan, b)).collect();
                costs.sort_unstable();
                costs.dedup();
                assert_eq!(costs.len(), plans.len(), "b {b}");
            }
        }
    }

    #[test]
    fn tier_presets() {
        let path = |calls, permutations| Work { calls, permutations };
        let expected = [
            (Tier::Light, 13, 16 << 10, CachePlan::Level(3), 1024, path(2_830, 2_886), path(1_851_418, 1_908_762)),
            (
                Tier::Standard,
                20,
                1 << 20,
                CachePlan::Top(5),
                65_535,
                path(7_231, 7_455),
                path(236_978_188, 244_318_220),
            ),
            (
                Tier::Full,
                26,
                16 << 20,
                CachePlan::Top(7),
                (1 << 20) - 1,
                path(28_927, 29_823),
                path(15_166_603_264, 15_636_365_312),
            ),
        ];
        for (tier, b, bytes, plan, nodes, path_work, keygen) in expected {
            assert_eq!((tier.b(), tier.cache_bytes(), tier.plan()), (b, bytes, plan), "{tier:?}");
            assert_eq!((plan.nodes(b), plan.auth_path_work(b), keygen_work(b)), (nodes, path_work, keygen), "{tier:?}");
            assert_eq!(Tier::preset(tier.name()), Some(tier));
        }
        let file_bytes = Tier::PRESETS.map(|tier| key_file_len(tier.b(), tier.plan()));
        assert_eq!(file_bytes, [16_736, 1_048_800, 16_777_344]);
        assert_eq!(Tier::Light.plan().describe(13), "level 3 only");
        assert_eq!(Tier::Standard.plan().describe(20), "top levels 5..20");
        assert_eq!(Tier::Full.plan().describe(26), "top levels 7..26");
        assert_eq!(Tier::preset("custom"), None);
        // sphincs-art's figures: keygen 1.85e6, 2.37e8, 1.52e10 calls, and keccak_model.py's 1,908,763, 244,318,221 and
        // 15,636,365,313 permutations (the page's 1.91M, 244M, 15.6B).
        assert_eq!([13, 20, 26].map(|b| sweep_keygen(b, 225)), [1_851_419, 236_978_189, 15_166_603_265]);
        assert_eq!([13, 20, 26].map(|b| sweep_keygen(b, 232)), [1_908_763, 244_318_221, 15_636_365_313]);
    }

    /// The streaming keygen is `key_gen`'s tree on any number of threads, in the same keccak256 calls and permutations.
    #[test]
    fn streaming_keygen_is_key_gen() {
        for (b, x) in [(0usize, 1u8), (1, 2), (7, 3)] {
            let (sk, pk) = key_gen(&seed(x), b);
            for threads in [1, 2, 3, 5, 32, 100] {
                let before = work();
                let key = keygen_cached(&seed(x), Tier::Custom { b, cache_bytes: u64::MAX }, threads);
                assert_eq!(work() - before, keygen_work(b), "b {b}, {threads} threads");
                assert_eq!((key.plan, key.public_key(), key.s), (CachePlan::Whole, pk, sk.tree.s));
                for level in 0..=b {
                    assert_eq!(key.level(level), sk.tree.level(level), "b {b}, {threads} threads, level {level}");
                }
                assert_eq!(key.subtree_root, sk.tree.level(b)[0]);
                assert_eq!(key.surrogates, sk.tree.surrogates);
            }
        }
    }

    /// Messages whose grind takes at most `1/64` of the mean `2^(26 - b)` attempts. Finding one costs about one mean
    /// grind; every signature of it after that is cheap, which keeps the small-`b` cases (one signature per cache plan)
    /// fast.
    fn quick_messages(sk: &SecretKey, count: usize) -> Vec<Message> {
        let (pp, b) = (&sk.public_param, sk.tree.b);
        let cap = (1u32 << (H - b)) / 64 + 1;
        (0u64..)
            .map(|j| keccak256(&[&b"lssk tiers test"[..], &j.to_le_bytes()].concat()))
            .filter(|m| {
                let base = randomizer_base(pp, &sk.master, m);
                (0..cap).any(|i| sk.tree.contains(digest_index(pp, &randomizer(&base, i), m)))
            })
            .take(count)
            .collect()
    }

    /// For every cache size of [`cache_sizes`]: the keygen spends [`keygen_work`] and reaches `key_gen`'s key,
    /// `sign_with_cache` gives `sign`'s bytes at `sign`'s cost plus the authentication path, and the path costs exactly
    /// `tree_cost`, in calls and in permutations. A key is generated, and signs every message, once per distinct plan
    /// (the budget is the only other difference between the cache sizes that select it).
    fn check_cached_signer(b: usize) {
        let x = 40 + b as u8;
        let before = work();
        let (sk, pk) = key_gen(&seed(x), b);
        assert_eq!(work() - before, keygen_work(b));
        let messages = quick_messages(
            &sk,
            if b <= 2 {
                1
            } else if b <= 4 {
                2
            } else {
                3
            },
        );
        let reference: Vec<(Signature, Work)> = messages
            .iter()
            .map(|m| {
                let before = work();
                let sig = sign(&sk, m);
                (sig, work() - before)
            })
            .collect();
        for (m, (sig, _)) in messages.iter().zip(&reference) {
            assert_eq!(verify(&pk, m, sig), Ok(()));
        }
        let mut keys: Vec<CachedKey> = Vec::new();
        for nodes in cache_sizes(b) {
            let tier = Tier::Custom { b, cache_bytes: nodes.saturating_mul(N as u64) };
            if !keys.iter().any(|key| key.plan == tier.plan()) {
                let before = work();
                let key = keygen_cached(&seed(x), tier, 4);
                assert_eq!(work() - before, keygen_work(b), "b {b}, {:?}", key.plan);
                assert_eq!(key.public_key(), pk, "b {b}, {:?}", key.plan);
                assert_eq!(key.cache_nodes(), key.plan.nodes(b));
                keys.push(key);
            }
        }
        let (messages, reference) = (&messages, &reference);
        let path_work: Vec<Work> = std::thread::scope(|scope| {
            let workers: Vec<_> = keys
                .iter()
                .map(|key| {
                    scope.spawn(move || {
                        let mut path_work = None;
                        for (m, (sig, sign_work)) in messages.iter().zip(reference) {
                            let (cached, cost) = sign_with_cache_cost(key, m).unwrap();
                            assert_eq!(cached.to_bytes(), sig.to_bytes(), "b {b}, {:?}", key.plan);
                            assert_eq!(cost.total, *sign_work + cost.auth_path, "b {b}, {:?}", key.plan);
                            let verify = Work { calls: VERIFY_KECCAK_CALLS, permutations: VERIFY_PERMUTATIONS };
                            assert_eq!(cost.verify, verify, "b {b}, {:?}", key.plan);
                            assert!(path_work.is_none_or(|work| work == cost.auth_path));
                            path_work = Some(cost.auth_path);
                            let base = randomizer_base(&key.public_param, &key.master, m);
                            assert_eq!(randomizer(&base, cost.attempts as u32 - 1), sig.randomizer);
                        }
                        path_work.unwrap()
                    })
                })
                .collect();
            workers.into_iter().map(|worker| worker.join().unwrap()).collect()
        });
        for nodes in cache_sizes(b) {
            let k = keys.iter().position(|key| key.plan == CachePlan::choose(b, nodes)).unwrap();
            let sweep = Work { calls: sweep_tree_cost(b, nodes, 225), permutations: sweep_tree_cost(b, nodes, 232) };
            assert_eq!(path_work[k], sweep, "b {b}, {nodes} nodes, {:?}", keys[k].plan);
        }
    }

    macro_rules! cached_signer_tests {
        ($($name:ident: $b:expr,)*) => {$(
            #[test]
            fn $name() {
                check_cached_signer($b);
            }
        )*};
    }

    cached_signer_tests! {
        cached_signer_b1: 1, cached_signer_b2: 2, cached_signer_b3: 3, cached_signer_b4: 4,
        cached_signer_b5: 5, cached_signer_b6: 6, cached_signer_b7: 7, cached_signer_b8: 8,
        cached_signer_b9: 9, cached_signer_b10: 10, cached_signer_b11: 11, cached_signer_b12: 12,
    }

    /// A cache corrupted after loading fails the signature wherever a signature recomputes over it: the bottom
    /// subtree's root against the cached node (or, with no cache, the kept subtree's root), and the levels above a
    /// `level c only` cache against the kept subtree's root. (A `top levels` node read straight into the path is caught
    /// when the key is loaded, and by the verification of the signature.)
    #[test]
    fn corrupt_caches_fail_the_signature() {
        let b = 8;
        let (sk, _) = key_gen(&seed(7), b);
        let m = quick_messages(&sk, 1)[0];
        let idx = message_digest(&sk.public_param, &sign(&sk, &m).randomizer, &m).0;
        let local = (idx - (sk.tree.s << b)) as usize;
        for nodes in [0, 7, 8, 31] {
            let key = keygen_cached(&seed(7), Tier::Custom { b, cache_bytes: N as u64 * nodes }, 8);
            assert!(key.auth_path(idx).is_ok());
            let c = key.plan.bottom(b);
            let mut bad = key.clone();
            if key.plan == CachePlan::None {
                bad.subtree_root[0] ^= 1;
            } else {
                bad.cache[0][local >> c][3] ^= 0x40;
            }
            assert_eq!(bad.auth_path(idx), Err(KeyError::Cache { level: c, index: idx >> c }), "{:?}", key.plan);
            assert!(sign_with_cache(&bad, &m).is_err());
            if let CachePlan::Level(c) = key.plan {
                let mut bad = key.clone();
                bad.cache[0][(local >> c) ^ 1][0] ^= 1;
                assert_eq!(bad.auth_path(idx), Err(KeyError::Cache { level: b, index: key.s }));
            }
        }
    }

    /// `key` with node `j` of its cached level `k` changed and everything above it recomputed: the cached levels above
    /// it, the kept subtree's root and the root. The edit is consistent, so the key file it writes loads (and a
    /// re-sealed file needs the seed, which the checksum covers): load cannot tell, since binding the cache to the seed
    /// would cost a keygen.
    fn consistent_edit(key: &CachedKey, k: usize, j: usize) -> CachedKey {
        let (pp, b, start) = (&key.public_param, key.b, key.plan.levels(key.b).start);
        let mut fake = key.clone();
        fake.cache[k][j][0] ^= 0x5a;
        let mut row = fake.cache[k].clone();
        for level in start + k + 1..=b {
            let first = key.s << (b - level);
            row = (0..row.len() / 2)
                .map(|i| xmss_node(pp, level, first + i as u64, &row[2 * i], &row[2 * i + 1]))
                .collect();
            if let Some(cached) = fake.cache.get_mut(level - start) {
                cached.clone_from(&row);
            }
        }
        fake.subtree_root = row[0];
        fake.root = fold_surrogates(pp, b, key.s, row[0], &key.surrogates);
        fake
    }

    /// Whatever the key file holds, a signature that `sign_with_cache` returns verifies under the key's public key
    /// (the root it holds). A consistently re-sealed edit of a `whole subtree` cache at the signed leaf used to sign
    /// with no check (its path is read straight from the cache) and return a signature that fails under the key's root:
    /// it is refused now. Edits that the signature's recomputation catches are refused as before, and edits off the
    /// signed leaf's ancestors give a signature that verifies under the (wrong) root the file holds, which is why the
    /// printed key words must be compared with the registered key.
    #[test]
    fn returned_signatures_verify_under_the_keys_root() {
        let b = 6;
        let (sk, pk) = key_gen(&seed(9), b);
        let m = quick_messages(&sk, 1)[0];
        let idx = message_digest(&sk.public_param, &sign(&sk, &m).randomizer, &m).0;
        let local = (idx - (sk.tree.s << b)) as usize;
        let mut refused_by_verification = 0;
        for nodes in [u64::MAX, 7, 8, 31] {
            let key = keygen_cached(&seed(9), Tier::Custom { b, cache_bytes: nodes.saturating_mul(N as u64) }, 2);
            let c = key.plan.levels(b).start;
            // The signed leaf's ancestor at the lowest cached level, its sibling, and a node far from it.
            let width = 1usize << (b - c);
            for j in [local >> c, (local >> c) ^ 1, ((local >> c) + width / 2) % width] {
                let fake = consistent_edit(&key, 0, j);
                let loaded = CachedKey::from_bytes(&fake.to_bytes()).expect("a consistent edit loads");
                assert_ne!(loaded.public_key(), pk);
                match sign_with_cache(&loaded, &m) {
                    Ok(sig) => {
                        assert_eq!(verify(&loaded.public_key(), &m, &sig), Ok(()), "{:?}, node {j}", key.plan);
                        assert_ne!(j, local >> c, "{:?}: the ancestor's edit must not sign", key.plan);
                    }
                    Err(KeyError::Signature) => {
                        assert_eq!(key.plan, CachePlan::Whole, "node {j}");
                        assert_eq!(j, local, "only the signed leaf itself is never recomputed");
                        refused_by_verification += 1;
                    }
                    Err(err) => {
                        assert_eq!(err, KeyError::Cache { level: c, index: idx >> c }, "{:?}, node {j}", key.plan)
                    }
                }
            }
        }
        assert_eq!(refused_by_verification, 1, "the whole-subtree edit at the signed leaf");
    }

    /// `chunk_bits` is `ceil(log2(threads)) + 2`, capped at the height, for every `threads`: no overflow (which panicked
    /// with overflow checks on and wrapped to 0 or to the height in release), and `keygen_cached` clamps the threads it
    /// spawns to `MAX_THREADS`.
    #[test]
    fn chunk_bits_and_thread_counts_have_no_overflow() {
        for (threads, bits) in [(0, 2), (1, 2), (2, 3), (3, 4), (4, 4), (8, 5), (9, 6), (32, 7), (100, 9), (1024, 12)] {
            assert_eq!(chunk_bits(H, threads), bits, "{threads} threads");
            assert_eq!(chunk_bits(H, threads), ((threads.max(1) * 4).next_power_of_two().trailing_zeros() as usize));
        }
        for threads in [1 << 20, (1 << 61) + 1, (1 << 62) - 1, 1 << 62, usize::MAX - 3, usize::MAX] {
            assert_eq!(chunk_bits(13, threads), 13, "{threads} threads");
            assert_eq!(chunk_bits(H, threads), if threads == 1 << 20 { 22 } else { H }, "{threads} threads");
        }
        let tier = Tier::Custom { b: 3, cache_bytes: 0 };
        let key = keygen_cached(&seed(1), tier, usize::MAX);
        assert_eq!(key, keygen_cached(&seed(1), tier, 8));
    }

    /// The Light tier end to end: the streaming keygen, the key file, and two signatures, against `key_gen` and `sign`.
    #[test]
    fn light_tier_end_to_end() {
        check_tier_end_to_end(Tier::Light, 2);
    }

    /// The Standard tier (`b = 20`, about 2.4e8 keccak256 calls per keygen, twice: `key_gen` and `keygen_cached`).
    #[test]
    #[ignore = "slow: two b = 20 keygens"]
    fn standard_tier_end_to_end() {
        check_tier_end_to_end(Tier::Standard, 2);
    }

    fn check_tier_end_to_end(tier: Tier, signatures: usize) {
        let b = tier.b();
        let seed = seed(13);
        let (sk, pk) = key_gen(&seed, b);
        let before = work();
        let key = keygen_cached(&seed, tier, available_threads());
        assert_eq!(work() - before, keygen_work(b));
        assert_eq!(key.public_key(), pk);
        let loaded = CachedKey::from_bytes(&key.to_bytes()).unwrap();
        assert_eq!(loaded, key);
        for t in 0..signatures as u8 {
            let m: Message = std::array::from_fn(|i| t.wrapping_mul(17) ^ i as u8);
            let (sig, cost) = sign_with_cache_cost(&loaded, &m).unwrap();
            assert_eq!(sig.to_bytes(), sign(&sk, &m).to_bytes());
            assert_eq!(cost.auth_path, tier.plan().auth_path_work(b));
            assert_eq!(verify(&pk, &m, &sig), Ok(()));
        }
    }
}
