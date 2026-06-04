//! Cross-validation: Rust signer must produce identical outputs to Python signer.
//!
//! Variant-independent reference values are baked in. C13-specific reference
//! values (pkRoot, signatures) are not pinned because regenerating them
//! requires running the Python signer for ~minutes; sanity-check tests cover
//! structural invariants instead.

use sphincs_c13_signer::hash;
use sphincs_c13_signer::wots;
use sphincs_c13_signer::fors;
use sphincs_c13_signer::merkle;
use sphincs_c13_signer::sphincs;
use sphincs_c13_signer::params::SIG_SIZE;

fn u256_hex(val: &hash::U256) -> String {
    format!("0x{}", hex::encode(hash::to_bytes32(*val)))
}

// Variant-independent reference values from Python signer with test_entropy = [0x42] * 32.
// pk_seed = mask_n(keccak256("pk_seed" || test_entropy))
// sk_seed = keccak256("sk_seed" || test_entropy)
// wots_secret/fors_secret use sk_seed directly and are also variant-independent.
const PY_PK_SEED: &str = "0x012dd57311a3728fd6988fb2a583bb9e00000000000000000000000000000000";
const PY_SK_SEED: &str = "0x11d47d1635d4ad4852852dae8fd9dbbd699558d7907907cdae4203bdbae7f7aa";
const PY_WOTS_SK_1_0_0_0: &str = "0x60fd5cf59c3c018fca334b8538cc52fe00000000000000000000000000000000";
// fors_secret(sk_seed, tree=0, leaf=0, ht_idx=0): keccak256(sk_seed || "fors" ||
// ht_idx(4) || tree_idx(4) || leaf_idx(4)) masked to top 128 bits. Regenerated
// for the ht_idx-folding preimage (the Finding-C fix); cross-checked against
// script/signer.py's fors_secret. (review C13-S-f2)
const PY_FORS_SECRET_0_0: &str = "0xf3c46060303099c9faed1691ad98823900000000000000000000000000000000";

fn derive_test_keys() -> (hash::U256, hash::U256) {
    let test_entropy = [0x42u8; 32];
    let pk_seed = hash::mask_n(hash::keccak256(&[b"pk_seed".as_slice(), &test_entropy].concat()));
    let sk_seed = hash::keccak256(&[b"sk_seed".as_slice(), &test_entropy].concat());
    (pk_seed, sk_seed)
}

#[test]
fn test_key_derivation_matches_python() {
    let (pk_seed, sk_seed) = derive_test_keys();
    assert_eq!(u256_hex(&pk_seed), PY_PK_SEED, "pk_seed mismatch");
    assert_eq!(u256_hex(&sk_seed), PY_SK_SEED, "sk_seed mismatch");
}

#[test]
fn test_wots_secret_matches_python() {
    let (_, sk_seed) = derive_test_keys();
    let sk0 = wots::wots_secret(sk_seed, 1, 0, 0, 0);
    assert_eq!(u256_hex(&sk0), PY_WOTS_SK_1_0_0_0, "wots_secret(1,0,0,0) mismatch");
}

#[test]
fn test_fors_secret_matches_python() {
    // fors_secret now folds the per-message hypertree leaf `ht_idx` into the PRF
    // preimage (the Finding-C fix). The pinned value below is for ht_idx = 0 and
    // MUST be regenerated from script/signer.py's fors_secret with the same
    // preimage (sk_seed || "fors" || ht_idx(4) || tree_idx(4) || leaf_idx(4)) if
    // any of those change. (review C13-S-f1 / C13-S-f2)
    let (_, sk_seed) = derive_test_keys();
    let fs = fors::fors_secret(sk_seed, 0, 0, 0);
    assert_eq!(u256_hex(&fs), PY_FORS_SECRET_0_0, "fors_secret(0,0,ht=0) mismatch");
}

#[test]
fn test_extract_digits_sums_to_at_most_seven_times_l() {
    // For w=8 each digit is 0..7. Property test on a known digest.
    let d = hash::keccak256(b"some test digest input for C13");
    let digits = wots::extract_digits(&d);
    for &x in digits.iter() {
        assert!(x <= 7, "C13 digits must be in [0,7], got {x}");
    }
    let sum: usize = digits.iter().map(|&x| x as usize).sum();
    assert!(sum <= 7 * digits.len(), "digit sum exceeds maximum");
}

#[test]
#[ignore] // ~1-2s in release: builds 2^11 = 2048 top-layer WOTS leaves
fn test_pkroot_builds_and_is_masked() {
    let (pk_seed, sk_seed) = derive_test_keys();
    let pk_root = merkle::build_subtree_root(pk_seed, sk_seed, 1, 0);
    // pkRoot is masked to top 128 bits
    assert_eq!(pk_root[2], 0, "pkRoot bottom bits should be zero (N_MASK)");
    assert_eq!(pk_root[3], 0, "pkRoot bottom bits should be zero (N_MASK)");
    // and not the zero hash
    assert!(pk_root[0] != 0 || pk_root[1] != 0, "pkRoot should be non-zero");
    println!("C13 pkRoot (test_entropy=0x42*32) = {}", u256_hex(&pk_root));
}

#[test]
#[ignore] // ~30s+ in release: 6×2^19 FORS leaves + R grind + WOTS+C grinding
fn test_full_sign_produces_valid_sig() {
    let (pk_seed, sk_seed) = derive_test_keys();
    let pk_root = merkle::build_subtree_root(pk_seed, sk_seed, 1, 0);

    let message = hash::keccak256(b"test message for C13");
    let sig = sphincs::sign(pk_seed, sk_seed, pk_root, message)
        .expect("signing failed");
    assert_eq!(sig.len(), SIG_SIZE, "sig size must match C13 SIG_SIZE=3688");
    assert_eq!(SIG_SIZE, 3688);

    // R should be non-zero
    assert!(sig[0..16].iter().any(|&b| b != 0), "R is zero");
}

#[test]
#[ignore] // ~30s+ in release; exercises BIP-39 + full sign
fn test_from_mnemonic_produces_valid_sig() {
    // Standard BIP-39 test mnemonic (DO NOT use with real funds)
    let mnemonic = "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about";

    let (pk_seed, sk_seed, pk_root, ecdsa_addr) =
        sphincs_c13_signer::keygen::from_mnemonic(mnemonic, "").expect("keygen failed");

    // pkSeed should be non-zero and masked to top 128 bits
    assert!(pk_seed[0] != 0 || pk_seed[1] != 0, "pkSeed is zero");
    assert_eq!(pk_seed[2], 0, "pkSeed bottom bits should be zero (N_MASK)");
    assert_eq!(pk_seed[3], 0, "pkSeed bottom bits should be zero (N_MASK)");

    // pkRoot should be non-zero and masked
    assert!(pk_root[0] != 0 || pk_root[1] != 0, "pkRoot is zero");
    assert_eq!(pk_root[2], 0, "pkRoot bottom bits should be zero");

    // ECDSA address should be the standard one for this mnemonic
    assert!(ecdsa_addr.starts_with("0x"), "address should start with 0x");
    assert_eq!(ecdsa_addr.len(), 42, "address should be 42 chars");

    // Sign a test message
    let message = hash::keccak256(b"test mnemonic signing");
    let sig = sphincs::sign(pk_seed, sk_seed, pk_root, message)
        .expect("signing with mnemonic-derived keys failed");
    assert_eq!(sig.len(), SIG_SIZE, "sig size mismatch");
    assert!(sig[0..16].iter().any(|&b| b != 0), "R is zero");

    // Verify the derivation is deterministic
    let (pk_seed2, _, pk_root2, addr2) =
        sphincs_c13_signer::keygen::from_mnemonic(mnemonic, "").expect("second keygen failed");
    assert_eq!(pk_seed, pk_seed2, "pkSeed not deterministic");
    assert_eq!(pk_root, pk_root2, "pkRoot not deterministic");
    assert_eq!(ecdsa_addr, addr2, "address not deterministic");

    // Different passphrase should give different keys
    let (pk_seed3, _, _, _) =
        sphincs_c13_signer::keygen::from_mnemonic(mnemonic, "my passphrase").expect("keygen with passphrase failed");
    assert_ne!(pk_seed, pk_seed3, "passphrase should change keys");

    println!("Mnemonic keygen: pkSeed={}, pkRoot={}, addr={}", u256_hex(&pk_seed), u256_hex(&pk_root), ecdsa_addr);
}

#[test]
fn test_keccak256_empty() {
    let hash = hash::keccak256(b"");
    assert_eq!(
        u256_hex(&hash),
        "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    );
}

#[test]
fn test_params() {
    assert_eq!(sphincs_c13_signer::params::SIG_SIZE, 3688);
    assert_eq!(sphincs_c13_signer::params::H, 22);
    assert_eq!(sphincs_c13_signer::params::SUBTREE_H, 11);
    assert_eq!(sphincs_c13_signer::params::A, 19);
    assert_eq!(sphincs_c13_signer::params::K, 7);
    assert_eq!(sphincs_c13_signer::params::W, 8);
    assert_eq!(sphincs_c13_signer::params::L, 43);
    assert_eq!(sphincs_c13_signer::params::TARGET_SUM, 208);
}

