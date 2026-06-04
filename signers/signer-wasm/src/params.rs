//! C13 parameter constants: W+C_F+C h=22 d=2 a=19 k=7 w=8 target_sum=208

pub const N: usize = 16; // hash output bytes (128 bits)
pub const H: usize = 22;
pub const D: usize = 2;
pub const SUBTREE_H: usize = 11; // H / D
pub const A: usize = 19;
pub const K: usize = 7;
pub const W: usize = 8;
pub const LOG_W: usize = 3;
pub const L: usize = 43; // ceil(128 / LOG_W)
pub const TARGET_SUM: usize = 208;
pub const W_MASK: u64 = 0x7;

// Signature layout (R=N=16)
pub const FORS_START: usize = N;
pub const AUTH_START: usize = N + K * N; // 16 + 7*16 = 128
pub const HT_START: usize = AUTH_START + (K - 1) * A * N; // 128 + 6*19*16 = 1952
pub const LAYER_SIZE: usize = L * N + 4 + SUBTREE_H * N; // 688 + 4 + 176 = 868
pub const SIG_SIZE: usize = HT_START + D * LAYER_SIZE; // 1952 + 2*868 = 3688

// BIP-44 derivation path for Ethereum
pub const BIP44_PATH: &str = "m/44'/60'/0'/0/0";
