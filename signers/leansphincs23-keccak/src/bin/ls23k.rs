// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

//! `ls23k`: the leanSphincs-23-keccak signer, for the Forge FFI tests and the cross-checks.
//!
//! ```text
//! ls23k sign   <seed_hex64> <b> <msg_hex64>                       0x || hex(abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig))
//! ls23k kat    <seed_hex64> <b> <msg_hex64>                       one JSON object: key, signature and digest fields
//! ls23k verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>  true | false
//! ```
//!
//! `b` is the height of the kept subtree (`0..=25`; `25` is a full key, about 7.6e9 keccak256 calls). The key words are
//! high-aligned, as the on-chain verifier takes them (spec sections 12 and 13): `pkSeed = P || 0^16`, `pkRoot = root || 0^16`.
//! Hex arguments are accepted with or without `0x`. `verify` mirrors the verifier: a signature that is not 4148 bytes or
//! a key word with nonzero low 128 bits (where the contract reverts) prints `false`, with the contract's revert reason
//! on stderr; like the contract, it checks the length first.

use std::process::ExitCode;

use leansphincs23_keccak::*;

const USAGE: &str = "usage:
  ls23k sign   <seed_hex64> <b> <msg_hex64>
  ls23k kat    <seed_hex64> <b> <msg_hex64>
  ls23k verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>";

fn parse_hex(s: &str) -> Result<Vec<u8>, String> {
    let digits = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")).unwrap_or(s);
    if digits.len() % 2 != 0 {
        return Err(format!("odd-length hex: {s}"));
    }
    (0..digits.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(digits.get(i..i + 2).unwrap_or("?"), 16).map_err(|_| format!("bad hex: {s}")))
        .collect()
}

fn parse_fixed<const L: usize>(s: &str, what: &str) -> Result<[u8; L], String> {
    let bytes = parse_hex(s)?;
    bytes.try_into().map_err(|b: Vec<u8>| format!("{what}: expected {L} bytes, got {}", b.len()))
}

fn parse_b(s: &str) -> Result<usize, String> {
    match s.parse::<usize>() {
        Ok(b) if b <= H => Ok(b),
        _ => Err(format!("b: expected an integer in 0..={H}, got {s}")),
    }
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(2 + 2 * bytes.len());
    out.push_str("0x");
    for b in bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// A 16-byte value as the high half of an EVM word: `value || 0^16`.
fn high_word(value: &[u8; N]) -> [u8; 32] {
    let mut word = [0u8; 32];
    word[..N].copy_from_slice(value);
    word
}

/// `(pkSeed, pkRoot)` as the verifier takes them: `P || 0^16` and `root || 0^16`.
fn key_words(pk: &PublicKey) -> ([u8; 32], [u8; 32]) {
    (high_word(&pk.public_param), high_word(&pk.root))
}

fn u256_word(x: usize) -> [u8; 32] {
    let mut word = [0u8; 32];
    word[24..].copy_from_slice(&(x as u64).to_be_bytes());
    word
}

/// `abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig)`: the two words, the offset of `sig` (`0x60`), then its
/// length and its bytes, zero-padded to a whole word.
fn abi_encode(pk_seed: &[u8; 32], pk_root: &[u8; 32], sig: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(4 * 32 + sig.len().next_multiple_of(32));
    out.extend_from_slice(pk_seed);
    out.extend_from_slice(pk_root);
    out.extend_from_slice(&u256_word(0x60));
    out.extend_from_slice(&u256_word(sig.len()));
    out.extend_from_slice(sig);
    out.resize(out.len().next_multiple_of(32), 0);
    out
}

fn sign_args(args: &[String]) -> Result<(MasterSecret, usize, Message), String> {
    let [seed, b, msg] = args else { return Err(USAGE.into()) };
    Ok((parse_fixed(seed, "seed")?, parse_b(b)?, parse_fixed(msg, "message")?))
}

fn run(args: &[String]) -> Result<String, String> {
    let (command, rest) = args.split_first().ok_or(USAGE)?;
    match command.as_str() {
        "sign" => {
            let (seed, b, m) = sign_args(rest)?;
            let (sk, pk) = key_gen(&seed, b);
            let sig = sign(&sk, &m);
            let (pk_seed, pk_root) = key_words(&pk);
            Ok(hex(&abi_encode(&pk_seed, &pk_root, &sig.to_bytes())))
        }
        "kat" => {
            let (seed, b, m) = sign_args(rest)?;
            let (sk, pk) = key_gen(&seed, b);
            let sig = sign(&sk, &m);
            let (idx, u) = message_digest(&pk.public_param, &sig.randomizer, &m);
            let (pk_seed, pk_root) = key_words(&pk);
            let indices: Vec<String> = u.iter().map(u32::to_string).collect();
            Ok(format!(
                "{{\"scheme\":\"leanSphincs-23-keccak\",\"seed\":\"{}\",\"b\":{b},\"message\":\"{}\",\"pkSeed\":\"{}\",\
                 \"pkRoot\":\"{}\",\"sig\":\"{}\",\"idx\":{idx},\"counter\":{},\"randomizer\":\"{}\",\"fors_indices\":[{}]}}",
                hex(&seed),
                hex(&m),
                hex(&pk_seed),
                hex(&pk_root),
                hex(&sig.to_bytes()),
                sig.counter,
                hex(&sig.randomizer),
                indices.join(",")
            ))
        }
        "verify" => {
            let [pk_seed, pk_root, msg, sig] = rest else { return Err(USAGE.into()) };
            let (pk_seed, pk_root) = (parse_fixed(pk_seed, "pkSeed")?, parse_fixed(pk_root, "pkRoot")?);
            let (m, sig) = (parse_fixed(msg, "message")?, parse_hex(sig)?);
            match verify_words(&pk_seed, &pk_root, &m, &sig) {
                Ok(valid) => Ok(valid.to_string()),
                Err(reason) => {
                    eprintln!("{reason}");
                    Ok("false".into())
                }
            }
        }
        _ => Err(USAGE.into()),
    }
}

/// The verifier's `verify(pkSeed, pkRoot, message, sig)`: `Err` with the contract's revert reason, in the contract's
/// order (the length first, then the key words), or whether a well-formed signature is valid.
fn verify_words(pk_seed: &[u8; 32], pk_root: &[u8; 32], m: &Message, sig: &[u8]) -> Result<bool, &'static str> {
    let sig = Signature::from_bytes(sig).ok_or("Invalid sig length")?;
    if pk_seed[N..] != [0; 32 - N] || pk_root[N..] != [0; 32 - N] {
        return Err("Invalid public key");
    }
    let pk = PublicKey { root: pk_root[..N].try_into().unwrap(), public_param: pk_seed[..N].try_into().unwrap() };
    Ok(verify(&pk, m, &sig).is_ok())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(out) => {
            println!("{out}");
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("{err}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex_with_or_without_prefix() {
        assert_eq!(parse_hex("0x00ff10").unwrap(), [0, 255, 16]);
        assert_eq!(parse_hex("00FF10").unwrap(), [0, 255, 16]);
        assert_eq!(parse_hex("0x").unwrap(), [0u8; 0]);
        assert!(parse_hex("0x0").is_err());
        assert!(parse_hex("0xzz").is_err());
        assert!(parse_hex("0xé0").is_err());
        assert!(parse_fixed::<32>(&"11".repeat(31), "seed").is_err());
        assert_eq!(parse_fixed::<2>("0xabcd", "x").unwrap(), [0xab, 0xcd]);
        assert_eq!(hex(&[0, 0xab]), "0x00ab");
        assert!(parse_b("25").is_ok() && parse_b("26").is_err() && parse_b("-1").is_err());
    }

    /// The head is two key words and the offset `0x60`; the tail is the length and the padded signature.
    #[test]
    fn abi_encoding_layout() {
        let sig: Vec<u8> = (0..SIG_SIZE).map(|i| (i % 251) as u8 + 1).collect();
        let (pk_seed, pk_root) = ([0xaau8; 32], [0xbbu8; 32]);
        let out = abi_encode(&pk_seed, &pk_root, &sig);
        assert_eq!(out.len(), 4 * 32 + 4160);
        assert_eq!(out[..32], pk_seed);
        assert_eq!(out[32..64], pk_root);
        assert_eq!(out[64..96], u256_word(0x60));
        assert_eq!(out[95], 0x60);
        assert_eq!(out[96..128], u256_word(4148));
        assert_eq!(out[126..128], [0x10, 0x34]);
        assert_eq!(out[128..128 + SIG_SIZE], sig[..]);
        assert!(out[128 + SIG_SIZE..].iter().all(|&b| b == 0));
    }

    #[test]
    fn key_words_are_high_aligned() {
        let pk = PublicKey { root: [1; N], public_param: [2; N] };
        let (pk_seed, pk_root) = key_words(&pk);
        assert_eq!(pk_seed[..N], [2; N]);
        assert_eq!(pk_root[..N], [1; N]);
        assert_eq!(pk_seed[N..], [0; N]);
        assert_eq!(pk_root[N..], [0; N]);
    }

    /// `sign` output decodes back to a key and a signature that `verify` accepts, and `verify` mirrors the verifier's
    /// rejections.
    #[test]
    fn sign_then_verify_roundtrip() {
        let args = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        let (seed, msg) = (format!("0x{}", "42".repeat(32)), "ab".repeat(32));
        let encoded = parse_hex(&run(&args(&["sign", &seed, "6", &msg])).unwrap()).unwrap();
        let (pk_seed, pk_root, sig) = (hex(&encoded[..32]), hex(&encoded[32..64]), hex(&encoded[128..128 + SIG_SIZE]));
        assert_eq!(run(&args(&["verify", &pk_seed, &pk_root, &msg, &sig])).unwrap(), "true");
        let other_msg = format!("cd{}", "ab".repeat(31));
        assert_eq!(run(&args(&["verify", &pk_seed, &pk_root, &other_msg, &sig])).unwrap(), "false");
        let short = hex(&encoded[128..128 + SIG_SIZE - 1]);
        assert_eq!(run(&args(&["verify", &pk_seed, &pk_root, &msg, &short])).unwrap(), "false");
        let mut low = parse_hex(&pk_root).unwrap();
        low[31] = 1;
        assert_eq!(run(&args(&["verify", &pk_seed, &hex(&low), &msg, &sig])).unwrap(), "false");
        // The revert reasons, in the contract's order: a wrong length wins over a dirty key word.
        let words = |s: &str| -> [u8; 32] { parse_fixed(s, "word").unwrap() };
        let (seed_w, root_w, low_w) = (words(&pk_seed), words(&pk_root), words(&hex(&low)));
        let (m, sig_bytes) = (parse_fixed(&msg, "message").unwrap(), &encoded[128..128 + SIG_SIZE]);
        assert_eq!(verify_words(&seed_w, &root_w, &m, sig_bytes), Ok(true));
        assert_eq!(verify_words(&seed_w, &root_w, &m, &sig_bytes[1..]), Err("Invalid sig length"));
        assert_eq!(verify_words(&seed_w, &low_w, &m, sig_bytes), Err("Invalid public key"));
        assert_eq!(verify_words(&low_w, &root_w, &m, sig_bytes), Err("Invalid public key"));
        assert_eq!(verify_words(&seed_w, &low_w, &m, &sig_bytes[1..]), Err("Invalid sig length"));
        let kat = run(&args(&["kat", &seed, "6", &msg])).unwrap();
        assert!(kat.starts_with("{\"scheme\":\"leanSphincs-23-keccak\""));
        assert!(kat.contains(&format!("\"pkSeed\":\"{pk_seed}\"")) && kat.contains(&format!("\"sig\":\"{sig}\"")));
        assert!(run(&args(&["sign", &seed, "26", &msg])).is_err());
        assert!(run(&args(&["nope"])).is_err());
    }
}
