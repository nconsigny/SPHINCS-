//! C13 signer CLI.
//!
//! Subcommands:
//!   sign <msg>                              # derive keys from <msg>, sign <msg>
//!   keygen <seed_material_hex>              # derive (seed, sk_seed, root) from <seed_material>
//!   sign-with <seed> <sk_seed> <root> <msg> # sign <msg> with the given keypair
//!
//! Output formats:
//!   sign      → ABI-encoded (bytes32 seed, bytes32 root, bytes sig), hex on stdout
//!   keygen    → JSON {"seed": "0x...", "sk_seed": "0x...", "root": "0x..."} on stdout
//!   sign-with → raw signature bytes as hex on stdout

use sphincs_c13_signer::{hash, sphincs, u256_from_be};

fn keccak256_concat(parts: &[&[u8]]) -> [u8; 32] {
    let mut total = Vec::new();
    for p in parts { total.extend_from_slice(p); }
    let h = hash::keccak256(&total);
    hash::to_bytes32(h)
}

/// derive_keys matches script/signer.py's derive_keys(message_int).
fn derive_keys(seed_material: &[u8; 32]) -> (hash::U256, hash::U256) {
    let entropy = keccak256_concat(&[b"sphincs_signer_v1", seed_material]);
    let seed_full = hash::keccak256(&[b"pk_seed".as_slice(), &entropy].concat());
    let seed = hash::mask_n(seed_full);
    let sk_seed = hash::keccak256(&[b"sk_seed".as_slice(), &entropy].concat());
    (seed, sk_seed)
}

fn abi_encode(seed: hash::U256, root: hash::U256, sig: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(96 + 32 + sig.len() + 31);
    out.extend_from_slice(&hash::to_bytes32(seed));
    out.extend_from_slice(&hash::to_bytes32(root));
    let mut off = [0u8; 32];
    off[31] = 0x60;
    out.extend_from_slice(&off);
    let mut len_word = [0u8; 32];
    len_word[24..32].copy_from_slice(&(sig.len() as u64).to_be_bytes());
    out.extend_from_slice(&len_word);
    out.extend_from_slice(sig);
    let pad = (32 - sig.len() % 32) % 32;
    out.extend(std::iter::repeat(0u8).take(pad));
    out
}

fn parse_b32_hex(s: &str, label: &str) -> [u8; 32] {
    let bytes = hex::decode(s.trim_start_matches("0x"))
        .unwrap_or_else(|e| die(&format!("{label}: bad hex: {e}")));
    if bytes.len() != 32 {
        die(&format!("{label}: must be 32 bytes, got {}", bytes.len()));
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&bytes);
    out
}

fn die(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(1);
}

fn cmd_keygen(seed_material: [u8; 32]) {
    let (seed, sk_seed) = derive_keys(&seed_material);
    eprintln!("[c13 keygen] building pkRoot (subtree h=11)…");
    let t0 = std::time::Instant::now();
    let pk_root = sphincs_c13_signer::merkle::build_subtree_root(seed, sk_seed, 1, 0);
    eprintln!("[c13 keygen] done in {:.1}s", t0.elapsed().as_secs_f64());
    println!(
        r#"{{"seed":"0x{}","sk_seed":"0x{}","root":"0x{}"}}"#,
        hex::encode(hash::to_bytes32(seed)),
        hex::encode(hash::to_bytes32(sk_seed)),
        hex::encode(hash::to_bytes32(pk_root)),
    );
}

fn cmd_sign(msg: [u8; 32]) {
    let (seed, sk_seed) = derive_keys(&msg);
    eprintln!("[c13 sign] keys derived from msg; building pkRoot…");
    let t0 = std::time::Instant::now();
    let pk_root = sphincs_c13_signer::merkle::build_subtree_root(seed, sk_seed, 1, 0);
    eprintln!("[c13 sign] pkRoot in {:.1}s", t0.elapsed().as_secs_f64());
    let t1 = std::time::Instant::now();
    let sig = sphincs::sign(seed, sk_seed, pk_root, u256_from_be(&msg))
        .unwrap_or_else(|e| die(&format!("sign failed: {e}")));
    eprintln!("[c13 sign] signed in {:.1}s; sig={} B", t1.elapsed().as_secs_f64(), sig.len());
    println!("0x{}", hex::encode(&abi_encode(seed, pk_root, &sig)));
}

fn cmd_sign_with(seed_b: [u8; 32], sk_seed_b: [u8; 32], root_b: [u8; 32], msg_b: [u8; 32]) {
    let seed = u256_from_be(&seed_b);
    let sk_seed = u256_from_be(&sk_seed_b);
    let pk_root = u256_from_be(&root_b);
    let message = u256_from_be(&msg_b);
    let t0 = std::time::Instant::now();
    let sig = sphincs::sign(seed, sk_seed, pk_root, message)
        .unwrap_or_else(|e| die(&format!("sign failed: {e}")));
    eprintln!("[c13 sign-with] signed in {:.1}s; sig={} B", t0.elapsed().as_secs_f64(), sig.len());
    println!("0x{}", hex::encode(&sig));
}

fn usage() -> ! {
    eprintln!("Usage:");
    eprintln!("  signer-c13 sign <msg_hex>                                   # derive keys from msg, sign msg");
    eprintln!("  signer-c13 keygen <seed_material_hex>                       # emit (seed, sk_seed, root) JSON");
    eprintln!("  signer-c13 sign-with <seed> <sk_seed> <root> <msg>          # sign msg with given keypair, emit raw sig hex");
    eprintln!();
    eprintln!("Compat (deprecated):");
    eprintln!("  signer-c13 c13 <msg_hex>                                    # same as `sign <msg>`");
    std::process::exit(1);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 { usage(); }
    match args[1].as_str() {
        "sign" => {
            if args.len() != 3 { usage(); }
            cmd_sign(parse_b32_hex(&args[2], "msg"));
        }
        "keygen" => {
            if args.len() != 3 { usage(); }
            cmd_keygen(parse_b32_hex(&args[2], "seed_material"));
        }
        "sign-with" => {
            if args.len() != 6 { usage(); }
            cmd_sign_with(
                parse_b32_hex(&args[2], "seed"),
                parse_b32_hex(&args[3], "sk_seed"),
                parse_b32_hex(&args[4], "root"),
                parse_b32_hex(&args[5], "msg"),
            );
        }
        // Back-compat: the existing forge tests + crosscheck.py call us as
        // `signer-c13 c13 <msg>`.
        "c13" => {
            if args.len() != 3 { usage(); }
            cmd_sign(parse_b32_hex(&args[2], "msg"));
        }
        _ => usage(),
    }
}
