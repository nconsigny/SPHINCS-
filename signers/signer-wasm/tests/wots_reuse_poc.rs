//! Regression guard for WOTS+C target-sum reuse (review C13-X-f3).
//!
//! At the 2^22 signature cap, hypertree-leaf (`ht_idx`) collisions are EXPECTED
//! (~2^21 colliding pairs by the birthday bound), so one layer-0 WOTS keypair
//! signs two distinct `fors_pk` values — a WOTS one-time-use violation that the
//! FORS few-time layer absorbs. This test models that reuse at the WOTS-keypair
//! level and checks the two properties the security argument relies on (see
//! docs/SECURITY-ANALYSIS.md §4):
//!
//!   1. SINGLE-USE forward soundness (deterministic): from one signature you
//!      cannot open a DIFFERENT target — any same-sum digit vector that
//!      dominates the signed one must equal it.
//!   2. TWO-REUSE gating (empirical, fixed seed): from the chains revealed by
//!      two reused signatures (known from the per-chain minimum height
//!      min(d1,d2) upward), a third, independently-derived target `fors_pk`
//!      cannot be WOTS-opened by count grinding alone — some chain always needs
//!      a height BELOW what was revealed. A WOTS-level forgery would require the
//!      attacker to CHOOSE the target `fors_pk`, i.e. forge the FORS layer (the
//!      gate). This guard does not replace the analytic bound; it catches a
//!      regression that made layer-0 reuse trivially forgeable.

use sphincs_c13_signer::hash::{self, U256};
use sphincs_c13_signer::wots;
use sphincs_c13_signer::params::{L, TARGET_SUM, W};

fn mk(label: &[u8]) -> U256 { hash::mask_n(hash::keccak256(label)) }

#[test]
fn wots_plus_c_single_use_is_forward_sound() {
    let seed = mk(b"wots reuse poc seed");
    let sk_seed = hash::keccak256(b"wots reuse poc sk_seed");
    let (layer, tree, kp) = (0u32, 0u64, 0u32);
    let (sks, _pk) = wots::keygen(seed, sk_seed, layer, tree, kp);

    let m1 = mk(b"target message 1 fors_pk");
    let (sigma1, count1) = wots::sign(seed, &sks, layer, tree, kp, m1).unwrap();
    let d1 = wots::extract_digits(&wots::wots_digest(seed, layer, tree, kp, m1, count1));
    assert_eq!(d1.iter().map(|&x| x as usize).sum::<usize>(), TARGET_SUM);
    assert_eq!(sigma1.len(), L);

    // A different target's sum-208 digit vector must NOT dominate d1: for d' ≠ d1
    // with Σd' = Σd1, d' ≥ d1 elementwise is impossible (Σ(d'-d1)=0 with all
    // terms ≥ 0 ⟹ d'=d1). So a single signature opens only its own value.
    let m2 = mk(b"different target fors_pk");
    let (_c2, _d, d2) = wots::find_count(seed, layer, tree, kp, m2).unwrap();
    assert_ne!(d1, d2, "distinct targets should give distinct digit vectors");
    let dominates = (0..L).all(|j| d2[j] >= d1[j]);
    assert!(!dominates, "single-use violated: a different target dominates the signed digits");
}

#[test]
fn wots_plus_c_two_reuse_does_not_open_third_target() {
    let seed = mk(b"wots reuse poc seed 2");
    let (layer, tree, kp) = (0u32, 0u64, 0u32);

    // Two distinct fors_pk signed by the SAME layer-0 WOTS keypair (an ht_idx
    // collision). We only need the digit vectors here, so grind counts directly.
    let m1 = mk(b"collision target A");
    let m2 = mk(b"collision target B");
    let (_c1, _, d1) = wots::find_count(seed, layer, tree, kp, m1).unwrap();
    let (_c2, _, d2) = wots::find_count(seed, layer, tree, kp, m2).unwrap();
    assert_ne!(d1, d2);

    // Chain j is known from height min(d1[j], d2[j]) upward.
    let m_min: [u8; L] = std::array::from_fn(|j| d1[j].min(d2[j]));
    let slack: usize = TARGET_SUM - m_min.iter().map(|&x| x as usize).sum::<usize>();
    // slack = (1/2) Σ|d1-d2|
    let l1: usize = (0..L).map(|j| (d1[j] as i32 - d2[j] as i32).unsigned_abs() as usize).sum();
    assert_eq!(slack, l1 / 2);

    // Positive control: the two genuinely-signed targets ARE reconstructable
    // (their digits dominate the revealed minima — trivially).
    assert!((0..L).all(|j| d1[j] >= m_min[j]));
    assert!((0..L).all(|j| d2[j] >= m_min[j]));

    // A THIRD independently-derived target fors_pk: grind count over a large
    // budget; no candidate covers ALL chains (some chain needs a height below the
    // revealed minimum), so no WOTS+C opening assembles from the harvested chains.
    let m3 = mk(b"third independent target fors_pk");
    let mut best_covered = 0usize;
    let mut openable = false;
    for count in 0..300_000u32 {
        let d3 = wots::extract_digits(&wots::wots_digest(seed, layer, tree, kp, m3, count));
        if d3.iter().map(|&x| x as usize).sum::<usize>() != TARGET_SUM { continue; }
        let covered = (0..L).filter(|&j| d3[j] >= m_min[j]).count();
        if covered > best_covered { best_covered = covered; }
        if covered == L { openable = true; break; }
    }
    assert!(!openable,
        "WOTS+C reuse opened a third independent target by count-grind alone \
         (best_covered={best_covered}/{L}); layer-0 reuse must remain FORS-gated");
    assert_eq!(W, 8);
}
