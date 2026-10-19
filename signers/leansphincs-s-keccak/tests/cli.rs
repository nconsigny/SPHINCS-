//! `lssk` as a process: what a kill part way through `keygen`, a refused `sign-key` and the error paths leave on disk
//! and print.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use leansphincs_s_keccak::*;

const LSSK: &str = env!("CARGO_BIN_EXE_lssk");

/// A fresh, empty directory for one test.
fn test_dir(what: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("lssk-it-{what}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// Runs `program args`, with `stdin` on its standard input.
fn run(program: &str, args: &[&str], stdin: &str) -> Output {
    let mut child = Command::new(program)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // The child may exit before it reads.
    let _ = child.stdin.take().unwrap().write_all(stdin.as_bytes());
    child.wait_with_output().unwrap()
}

fn lssk(args: &[&str], stdin: &str) -> Output {
    run(LSSK, args, stdin)
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// A `keygen` killed while it writes the key file (here by a file size limit, `SIGXFSZ`, as a full disk or a kill
/// would) leaves nothing at the key file's path: only its private temporary file, which the next `keygen` to the same
/// path names. That run is not blocked by a partial file. (The key file used to be written in place: the kill left a
/// truncated key file holding the seed at the key file's path, which also blocked the next `keygen`.)
#[cfg(unix)]
#[test]
fn a_killed_keygen_leaves_no_partial_key_file() {
    use std::os::unix::fs::PermissionsExt;
    use std::os::unix::process::ExitStatusExt;
    let dir = test_dir("killed");
    let key = dir.join("k");
    let key_str = key.to_str().unwrap();
    let seed = "7e".repeat(32);
    // The Light key file is 16,736 bytes; 8 KiB is about half of it. No core dump: it would hold the seed.
    let script = r#"ulimit -c 0 && ulimit -f 8 && exec "$0" "$@""#;
    let keygen = ["keygen", "--seed-stdin", "--tier", "light", "-o", key_str];
    let killed = run("bash", &[&["-c", script, LSSK][..], &keygen].concat(), &seed);
    assert!(!killed.status.success() && killed.status.signal().is_some(), "{killed:?}");
    assert!(!key.exists(), "a partial key file at the key file's path");
    let left: Vec<PathBuf> = fs::read_dir(&dir).unwrap().map(|entry| entry.unwrap().path()).collect();
    assert_eq!(left.len(), 1, "{left:?}");
    let tmp = left[0].file_name().unwrap().to_str().unwrap().to_string();
    assert!(tmp.starts_with(".k.") && tmp.ends_with(".tmp"), "{tmp}");
    assert_eq!(fs::metadata(&left[0]).unwrap().permissions().mode() & 0o777, 0o600);
    let again = lssk(&keygen, &seed);
    assert!(again.status.success(), "{again:?}");
    let stderr = text(&again.stderr);
    assert!(stderr.contains(&tmp) && stderr.contains("holds a seed: delete it"), "{stderr}");
    assert!(lssk(&["info", key_str], "").status.success());
    fs::remove_dir_all(&dir).unwrap();
}

/// The seed reaches neither standard output nor standard error, on success or on any error.
#[test]
fn the_seed_is_never_printed() {
    let dir = test_dir("printed");
    let key = dir.join("k");
    let key_str = key.to_str().unwrap();
    let seed = "c0ffee".repeat(10) + "c0ff";
    let leaks = |output: &Output| {
        let all = text(&output.stdout) + &text(&output.stderr);
        (0..seed.len() - 15).any(|i| all.contains(&seed[i..i + 16]))
    };
    let other = dir.join("other");
    let keygen = ["keygen", "--seed-stdin", "--b", "6", "--cache-bytes", "64", "-o", key_str];
    let keygen_other = ["keygen", "--seed-stdin", "--b", "6", "--cache-bytes", "64", "-o", other.to_str().unwrap()];
    let msg = "11".repeat(32);
    let runs = [
        lssk(&keygen, &seed),
        lssk(&keygen, &seed),
        lssk(&["sign-key", key_str, &msg], ""),
        lssk(&["info", key_str], ""),
        lssk(&keygen_other, &format!("{}g", &seed[..63])),
        lssk(&["keygen", &seed, "--tier", "light", "-o", key_str], ""),
        lssk(&["sign", &format!("{}z", &seed[..63]), "6", &msg], ""),
        lssk(&["keygen", "--seed-stdin", "--tier", "light", "-o", key_str, "--threads", "18446744073709551615"], &seed),
    ];
    let codes: Vec<Option<i32>> = runs.iter().map(|output| output.status.code()).collect();
    assert_eq!(codes, [Some(0), Some(2), Some(0), Some(0), Some(2), Some(2), Some(2), Some(2)]);
    for (i, output) in runs.iter().enumerate() {
        assert!(!leaks(output), "run {i}: {output:?}");
    }
    assert!(!other.exists());
    fs::remove_dir_all(&dir).unwrap();
}

/// A key file whose whole-subtree cache was edited at the signed leaf and re-sealed consistently (which needs the
/// seed) loads, and `info` reports its root. `sign-key` refuses it: exit 2 and nothing on standard output, where it
/// used to exit 0 with a signature that fails under the key words it printed. The genuine key file signs as `sign`.
#[test]
fn sign_key_prints_nothing_when_the_signature_does_not_verify() {
    let dir = test_dir("reseal");
    let (seed, msg) = ("3c".repeat(32), "a1".repeat(32));
    let path = dir.join("whole");
    let path_str = path.to_str().unwrap();
    let b = 8usize;
    let keygen = lssk(&["keygen", "--seed-stdin", "--b", "8", "--cache-bytes", "1000000", "-o", path_str], &seed);
    assert!(keygen.status.success(), "{keygen:?}");
    let words = text(&keygen.stdout).trim().to_string();
    assert!(text(&lssk(&["info", path_str], "").stdout).contains("\"plan\":\"whole subtree\""));
    // The signed leaf, from the stateless signer's signature.
    let signed = text(&lssk(&["sign", &seed, "8", &msg], "").stdout).trim().to_string();
    let encoded: Vec<u8> =
        (2..signed.len()).step_by(2).map(|i| u8::from_str_radix(&signed[i..i + 2], 16).unwrap()).collect();
    let sig = Signature::from_bytes(&encoded[128..128 + SIG_SIZE]).unwrap();
    let mut file = fs::read(&path).unwrap();
    let pp: PublicParam = file[32..48].try_into().unwrap();
    let s = u64::from_le_bytes(file[16..24].try_into().unwrap());
    let m: Message = [0xa1; 32];
    let local = (message_digest(&pp, &sig.randomizer, &m).0 - (s << b)) as usize;
    // Edit that leaf (level 0, the first cached level), then rehash every level above it, the kept subtree's root and
    // the root, and re-checksum.
    let surrogates: Vec<Digest> = (0..H - b).map(|t| file[112 + 16 * t..][..16].try_into().unwrap()).collect();
    let cache_at = 112 + 16 * (H - b);
    file[cache_at + 16 * local] ^= 0x5a;
    let mut row: Vec<Digest> = (0..1 << b).map(|i| file[cache_at + 16 * i..][..16].try_into().unwrap()).collect();
    let mut at = cache_at;
    for level in 1..=b {
        at += 16 * row.len();
        row = (0..row.len() / 2)
            .map(|j| xmss_node(&pp, level, (s << (b - level)) + j as u64, &row[2 * j], &row[2 * j + 1]))
            .collect();
        for (j, node) in row.iter().enumerate() {
            file[at + 16 * j..][..16].copy_from_slice(node);
        }
    }
    file[64..80].copy_from_slice(&row[0]);
    file[48..64].copy_from_slice(&fold_surrogates(&pp, b, s, row[0], &surrogates));
    let n = file.len();
    let checksum = keccak256(&file[..n - 32]);
    file[n - 32..].copy_from_slice(&checksum);
    let resealed = dir.join("resealed");
    write_private(&resealed, &file);
    let resealed = resealed.to_str().unwrap();
    let info = lssk(&["info", resealed], "");
    assert!(info.status.success(), "{info:?}");
    assert!(!text(&info.stdout).contains(&words[66..]), "the re-sealed file reports another root");
    let refused = lssk(&["sign-key", resealed, &msg], "");
    assert_eq!((refused.status.code(), refused.stdout.as_slice()), (Some(2), &b""[..]), "{refused:?}");
    assert!(text(&refused.stderr).contains("refusing to output a signature that does not verify"), "{refused:?}");
    let genuine = lssk(&["sign-key", path_str, &msg], "");
    assert_eq!(text(&genuine.stdout).trim(), signed, "the genuine key file signs as `sign`");
    fs::remove_dir_all(&dir).unwrap();
}

/// Writes `bytes` to a new file at `path` with mode `0600`.
fn write_private(path: &Path, bytes: &[u8]) {
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    std::os::unix::fs::OpenOptionsExt::mode(&mut options, 0o600);
    options.open(path).unwrap().write_all(bytes).unwrap();
}
