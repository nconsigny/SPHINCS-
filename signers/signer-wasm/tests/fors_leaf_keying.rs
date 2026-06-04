//! Regression test: FORS instances are keyed per hypertree leaf.
//!
//! The FORS+C family keys each FORS instance by the per-message hypertree leaf
//! via the FIPS 205 field split — tree = idxTree0 (htIdx >> SUBTREE_H),
//! kp = idxLeaf0 (htIdx & (2^SUBTREE_H-1)), the FORS tree number folded into
//! tree_index, and the leaf-secret PRF folded with the same leaf index. This
//! test pins that behaviour so a future change can't silently regress it:
//!
//!   * `fors_pk` and the revealed leaf secrets are a function of the hypertree
//!     leaf — two messages on different leaves produce different FORS public
//!     keys and different secrets at the same (tree, index).
//!   * An opening (secret + auth path) produced under one leaf reconstructs
//!     that leaf's `fors_pk`, but not a different leaf's — i.e. the 2^h
//!     hypertree leaves use independent FORS instances.
//!
//! If FORS were keyed by tree number alone (layer = tree = 0, as in the
//! pre-migration addressing) `fors_pk` would be identical across leaves and
//! these assertions would fail.
//!
//! Run:
//!   cargo test --release --test fors_leaf_keying -- --nocapture            # fast
//!   cargo test --release --test fors_leaf_keying -- --ignored --nocapture  # + full-param C13

use sphincs_c13_signer::fors;
use sphincs_c13_signer::hash::{self, U256};
use sphincs_c13_signer::params::{A, H, K};

/// Set a `width`-bit field at bit offset `off` in a U256, using the bit
/// indexing `hash::u256_shr` reads back — lets us hand-craft a digest with
/// chosen FORS indices and hypertree index.
fn set_field(d: &mut U256, off: usize, width: usize, val: u64) {
    for b in 0..width {
        if (val >> b) & 1 == 1 {
            let bit = off + b;
            d[3 - bit / 64] |= 1u64 << (bit % 64);
        }
    }
}

/// Craft a digest with the given per-tree FORS indices and hypertree index,
/// matching the layout sphincs::sign / the verifier parse out of H_msg.
fn craft_digest(fors_idx: &[u64; K], ht_idx: u64) -> U256 {
    let mut d: U256 = [0; 4];
    for i in 0..K {
        set_field(&mut d, i * A, A, fors_idx[i]);
    }
    set_field(&mut d, K * A, H, ht_idx);
    d
}

fn ht_idx_of(d: &U256) -> u64 {
    hash::u256_shr(d, K * A) & ((1u64 << H) - 1)
}

// ── Part 1: real, full-parameter C13 code ───────────────────────────────────

#[test]
#[ignore = "slow: builds 7 full 2^19-leaf FORS trees twice (~seconds in --release)"]
fn fors_pk_is_per_hypertree_leaf_full_c13() {
    let seed = hash::mask_n(hash::keccak256(b"regression pk seed"));
    let sk_seed = hash::keccak256(b"regression sk seed");

    // Two messages on different hypertree leaves that share the FORS index in
    // tree 0 (= 3) and tree 3 (= 42). Last FORS index is forced to 0.
    let d1 = craft_digest(&[3, 100, 9001, 42, 77, 250000, 0], 0x0AAAAA);
    let d2 = craft_digest(&[3, 12345, 8, 42, 500000, 1, 0], 0x155555);
    assert_ne!(ht_idx_of(&d1), ht_idx_of(&d2), "test setup: leaves must differ");

    let (secrets1, _ap1, fors_pk1) = fors::sign_fors(seed, sk_seed, d1).unwrap();
    let (secrets2, _ap2, fors_pk2) = fors::sign_fors(seed, sk_seed, d2).unwrap();

    // fors_pk is a function of the hypertree leaf.
    assert_ne!(fors_pk1, fors_pk2, "fors_pk must differ across hypertree leaves");
    // The secret at the same (tree, index) is leaf-specific.
    assert_ne!(secrets1[0], secrets2[0], "tree-0 secret at shared index must be leaf-specific");
    assert_ne!(secrets1[3], secrets2[3], "tree-3 secret at shared index must be leaf-specific");

    println!("Part 1 (full C13): fors_pk and leaf secrets are per-hypertree-leaf.");
}

// ── Part 2: reduced height, mirrors the library's FIPS-split addressing ──────

const A_DEMO: usize = 10;
const SH_DEMO: u32 = 8; // demo SUBTREE_H for the htIdx → (idxTree0, idxLeaf0) split

/// FIPS 205 FORS field split of a hypertree leaf (mirrors the library).
fn split_leaf(ht_idx: u32) -> (u32, u64) {
    (ht_idx & ((1u32 << SH_DEMO) - 1), (ht_idx >> SH_DEMO) as u64)
}

/// Build one FORS tree at reduced height, mirroring fors::build_fors_tree
/// (tree=idxTree0, kp=idxLeaf0, tree_index=(tree_idx<<(a-height))|node) plus the
/// leaf-keyed secret.
fn build_fors_tree(seed: U256, sk_seed: U256, tree_idx: u32, ht_idx: u32, a: usize) -> (Vec<Vec<U256>>, U256) {
    let (idx_leaf0, idx_tree0) = split_leaf(ht_idx);
    let n_leaves = 1usize << a;
    let mut leaves = Vec::with_capacity(n_leaves);
    for j in 0..n_leaves {
        let secret = fors::fors_secret(sk_seed, tree_idx, j as u32, ht_idx);
        let leaf_adrs = hash::make_adrs(0, idx_tree0, 3, idx_leaf0, 0, 0, (tree_idx << a) | j as u32);
        leaves.push(hash::th(seed, leaf_adrs, secret));
    }
    let mut nodes = vec![leaves];
    for h in 0..a {
        let prev = &nodes[h];
        let mut level = Vec::with_capacity(prev.len() / 2);
        for idx in (0..prev.len()).step_by(2) {
            let parent_idx = idx / 2;
            let ti = (tree_idx << (a - 1 - h)) | parent_idx as u32;
            let adrs = hash::make_adrs(0, idx_tree0, 3, idx_leaf0, 0, (h + 1) as u32, ti);
            level.push(hash::th_pair(seed, adrs, prev[idx], prev[idx + 1]));
        }
        nodes.push(level);
    }
    let root = nodes[a][0];
    (nodes, root)
}

fn auth_path(nodes: &[Vec<U256>], leaf_idx: usize, a: usize) -> Vec<U256> {
    let mut path = Vec::with_capacity(a);
    let mut idx = leaf_idx;
    for h in 0..a {
        path.push(nodes[h][idx ^ 1]);
        idx >>= 1;
    }
    path
}

/// Recompute a FORS tree root from a (secret, auth_path) opening, the way the
/// verifier would for hypertree leaf `ht_idx`. Uses only the public pk seed and
/// the supplied opening — no secret-key derivation.
fn root_from_opening(seed: U256, ht_idx: u32, tree_idx: u32, idx: usize, secret: U256, path: &[U256], a: usize) -> U256 {
    let (idx_leaf0, idx_tree0) = split_leaf(ht_idx);
    let leaf_adrs = hash::make_adrs(0, idx_tree0, 3, idx_leaf0, 0, 0, (tree_idx << a) | idx as u32);
    let mut node = hash::th(seed, leaf_adrs, secret);
    let mut m = idx;
    for h in 0..a {
        let parent = m >> 1;
        let ti = (tree_idx << (a - 1 - h)) | parent as u32;
        let adrs = hash::make_adrs(0, idx_tree0, 3, idx_leaf0, 0, (h + 1) as u32, ti);
        node = if m & 1 == 0 {
            hash::th_pair(seed, adrs, node, path[h])
        } else {
            hash::th_pair(seed, adrs, path[h], node)
        };
        m = parent;
    }
    node
}

/// Build the FORS forest for one hypertree leaf (k-1 normal trees + forced-zero
/// last tree), returning fors_pk and each tree's nodes. Mirrors sign_fors.
fn build_forest(seed: U256, sk_seed: U256, ht_idx: u32, a: usize) -> (U256, Vec<Vec<Vec<U256>>>) {
    let (idx_leaf0, idx_tree0) = split_leaf(ht_idx);
    let mut roots = Vec::with_capacity(K);
    let mut trees = Vec::with_capacity(K);
    for t in 0..K {
        let (nodes, root) = build_fors_tree(seed, sk_seed, t as u32, ht_idx, a);
        if t == K - 1 {
            let last_adrs = hash::make_adrs(0, idx_tree0, 3, idx_leaf0, 0, 0, ((K - 1) as u32) << a);
            roots.push(hash::th(seed, last_adrs, root));
        } else {
            roots.push(root);
        }
        trees.push(nodes);
    }
    let roots_adrs = hash::make_adrs(0, idx_tree0, 4, idx_leaf0, 0, 0, 0);
    (hash::th_multi(seed, roots_adrs, &roots), trees)
}

/// Recompute fors_pk for hypertree leaf `ht_idx` from a set of openings (one per
/// normal tree) plus the revealed last-tree root.
fn recompute_pk(seed: U256, ht_idx: u32, open: &[(usize, U256, Vec<U256>)], root_last: U256, a: usize) -> U256 {
    let (idx_leaf0, idx_tree0) = split_leaf(ht_idx);
    let mut roots = Vec::with_capacity(K);
    for t in 0..(K - 1) {
        let (idx, secret, ref path) = open[t];
        roots.push(root_from_opening(seed, ht_idx, t as u32, idx, secret, path, a));
    }
    let last_adrs = hash::make_adrs(0, idx_tree0, 3, idx_leaf0, 0, 0, ((K - 1) as u32) << a);
    roots.push(hash::th(seed, last_adrs, root_last));
    hash::th_multi(seed, hash::make_adrs(0, idx_tree0, 4, idx_leaf0, 0, 0, 0), &roots)
}

#[test]
fn openings_are_leaf_specific() {
    let a = A_DEMO;
    let seed = hash::mask_n(hash::keccak256(b"regression pk seed"));
    let sk_seed = hash::keccak256(b"regression sk seed");

    let leaf_a: u32 = 0x1111;
    let leaf_b: u32 = 0x2222;
    assert_ne!(leaf_a, leaf_b);

    let (pk_a, trees_a) = build_forest(seed, sk_seed, leaf_a, a);
    let (pk_b, trees_b) = build_forest(seed, sk_seed, leaf_b, a);

    // Distinct leaves ⇒ distinct FORS public keys.
    assert_ne!(pk_a, pk_b, "distinct hypertree leaves must yield distinct fors_pk");
    // The leaf secret at the same (tree, index) is leaf-specific.
    assert_ne!(
        fors::fors_secret(sk_seed, 0, 5, leaf_a),
        fors::fors_secret(sk_seed, 0, 5, leaf_b),
        "leaf secrets must be hypertree-leaf-specific"
    );

    // Indices for a message on leaf B (last tree forced 0).
    let idx_b: [usize; K] = [7, 19, 3, 100, 250, 88, 0];
    let root_last_b = build_fors_tree(seed, sk_seed, (K - 1) as u32, leaf_b, a).1;

    // Openings drawn from leaf A at those indices do NOT reconstruct leaf B's
    // fors_pk — the instances are independent across leaves.
    let openings_from_a: Vec<(usize, U256, Vec<U256>)> = (0..(K - 1))
        .map(|t| {
            let idx = idx_b[t];
            (idx, fors::fors_secret(sk_seed, t as u32, idx as u32, leaf_a), auth_path(&trees_a[t], idx, a))
        })
        .collect();
    let pk_from_a_openings = recompute_pk(seed, leaf_b, &openings_from_a, root_last_b, a);
    assert_ne!(pk_from_a_openings, pk_b, "leaf-A openings must not reconstruct leaf-B fors_pk");

    // Positive control: leaf B's own openings DO reconstruct pk_b — confirming
    // the recompute path is faithful (so the assertion above is meaningful).
    let openings_from_b: Vec<(usize, U256, Vec<U256>)> = (0..(K - 1))
        .map(|t| {
            let idx = idx_b[t];
            (idx, fors::fors_secret(sk_seed, t as u32, idx as u32, leaf_b), auth_path(&trees_b[t], idx, a))
        })
        .collect();
    assert_eq!(recompute_pk(seed, leaf_b, &openings_from_b, root_last_b, a), pk_b,
        "leaf-B openings must reconstruct pk_b (recompute path is faithful)");

    println!("Part 2: FORS openings are leaf-specific; instances are independent across hypertree leaves.");
}
