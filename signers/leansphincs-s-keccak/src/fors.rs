//! FORS: `k = 13` Merkle trees of `2^a = 4096` secret leaves; the digest opens one leaf per tree.
//! A tree has no root hash: the WOTS+C encoding hashes the two nodes below the root of every tree.

use crate::*;

pub const FORS_LEAVES: usize = 1 << A;

/// What a signature carries for FORS: the opened secret and the Merkle path of each tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForsOpening {
    pub secrets: [Digest; K],
    pub paths: [[Digest; A]; K],
}

/// The `hi` field of a FORS address: tree `kappa < 32`, `level < 16`, and the leaf or node `j < 2^12`.
/// The three fields are disjoint bit ranges (0..5, 5..9, 9..21), so the position is injective and below `2^24`.
fn fors_position(kappa: usize, level: usize, j: usize) -> u32 {
    debug_assert!(kappa < 32 && level < 16 && j < 1 << 12);
    (kappa + 32 * level + 512 * j) as u32
}

/// The address of the hash that gives the secrets of leaves `2 t` and `2 t + 1` of tree `kappa`.
pub fn fors_secret_tweak(idx: u64, kappa: usize, t: usize) -> Tweak {
    tweak(TWEAK_FTS_PRF, fors_position(kappa, 0, t), idx as u32)
}

/// The secrets of leaves `2 t` and `2 t + 1`: the two halves of one hash of the seed.
pub fn fors_secret_pair(pp: &PublicParam, master: &MasterSecret, idx: u64, kappa: usize, t: usize) -> [Digest; 2] {
    th_pair(pp, &fors_secret_tweak(idx, kappa, t), master)
}

/// The secret of leaf `j` of tree `kappa`.
pub fn fors_secret(pp: &PublicParam, master: &MasterSecret, idx: u64, kappa: usize, j: usize) -> Digest {
    fors_secret_pair(pp, master, idx, kappa, j / 2)[j % 2]
}

pub fn fors_leaf_tweak(idx: u64, kappa: usize, j: usize) -> Tweak {
    tweak(TWEAK_FTS_LEAF, fors_position(kappa, 0, j), idx as u32)
}

pub fn fors_leaf(pp: &PublicParam, idx: u64, kappa: usize, j: usize, secret: &Digest) -> Digest {
    th(pp, &fors_leaf_tweak(idx, kappa, j), secret)
}

fn fors_node(
    pp: &PublicParam,
    idx: u64,
    kappa: usize,
    level: usize,
    j: usize,
    left: &Digest,
    right: &Digest,
) -> Digest {
    th_digests(pp, &tweak(TWEAK_FTS_NODE, fors_position(kappa, level, j), idx as u32), &[*left, *right])
}

/// The FORS tops of an instance: the two nodes below the root (level `a - 1`) of each of the `k` trees, in the order
/// `top_{0,0} | top_{0,1} | ... | top_{12,1}` (416 bytes). No hash folds them into a key: the WOTS+C encoding absorbs
/// them (see [`encoding_midstate`]).
pub type ForsTops = [[Digest; 2]; K];

/// A FORS instance whose leaves are known: every tree level, kept for the openings.
pub struct ForsForest {
    /// `levels[kappa][level][j]`, level 0 being the leaves and level `a - 1` the two top nodes.
    levels: Vec<Vec<Vec<Digest>>>,
    pub tops: ForsTops,
}

impl ForsForest {
    /// Builds the forest of instance `idx` from its `k * 2^a` leaves, one tree per thread.
    pub fn from_leaves(pp: &PublicParam, idx: u64, leaves: &[Digest]) -> Self {
        assert_eq!(leaves.len(), K * FORS_LEAVES);
        let levels: Vec<Vec<Vec<Digest>>> = par_map(K, |kappa| {
            let mut tree = vec![leaves[kappa * FORS_LEAVES..(kappa + 1) * FORS_LEAVES].to_vec()];
            for level in 1..A {
                let below = &tree[level - 1];
                let up = (0..below.len() / 2)
                    .map(|j| fors_node(pp, idx, kappa, level, j, &below[2 * j], &below[2 * j + 1]))
                    .collect();
                tree.push(up);
            }
            tree
        });
        let tops = std::array::from_fn(|kappa| [levels[kappa][A - 1][0], levels[kappa][A - 1][1]]);
        Self { tops, levels }
    }

    pub fn leaf(&self, kappa: usize, j: usize) -> Digest {
        self.levels[kappa][0][j]
    }

    /// The Merkle path of leaf `u[kappa]` in every tree.
    pub fn paths(&self, u: &[u32; K]) -> [[Digest; A]; K] {
        std::array::from_fn(|kappa| {
            std::array::from_fn(|level| self.levels[kappa][level][(u[kappa] as usize >> level) ^ 1])
        })
    }
}

/// The FORS leaves of instance `idx` from the master secret, tree after tree (one tree per thread).
pub fn fors_leaves(pp: &PublicParam, master: &MasterSecret, idx: u64) -> Vec<Digest> {
    par_map(K, |kappa| {
        (0..FORS_LEAVES / 2)
            .flat_map(|t| {
                let secrets = fors_secret_pair(pp, master, idx, kappa, t);
                [0, 1].map(|half| fors_leaf(pp, idx, kappa, 2 * t + half, &secrets[half]))
            })
            .collect::<Vec<_>>()
    })
    .concat()
}

/// `Fts.recover`: the FORS tops an opening reaches.
pub fn fors_recover(pp: &PublicParam, idx: u64, u: &[u32; K], opening: &ForsOpening) -> ForsTops {
    std::array::from_fn(|kappa| {
        let opened = u[kappa] as usize;
        let leaf = fors_leaf(pp, idx, kappa, opened, &opening.secrets[kappa]);
        let ordered = |node: Digest, level: usize| {
            let sibling = opening.paths[kappa][level];
            if (opened >> level) & 1 == 0 { [node, sibling] } else { [sibling, node] }
        };
        let top = (0..A - 1).fold(leaf, |node, level| {
            let [left, right] = ordered(node, level);
            fors_node(pp, idx, kappa, level + 1, opened >> (level + 1), &left, &right)
        });
        ordered(top, A - 1)
    })
}
