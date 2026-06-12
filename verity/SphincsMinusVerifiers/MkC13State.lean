/-
  MkC13State — the frozen Phase-1 interface contract (STRATEGY.md §3).

  `mkC13State pkSeed pkRoot message sig` is the bytes→`RuntimeState` constructor
  that the (still-opaque) `execC13` will run `c13VerifyBody` over once the Phase-3
  atomic flip lands.  It is defined here STANDALONE — it is NOT yet wired into
  `execC13`; `execC13` stays `opaque` and `c13_refines_byte_spec` stays an
  `axiom` until the full-body equality composes (soundness rule).

  The construction mirrors `PreflightC13.mkState` exactly, but parameterised over
  the four byte inputs of the byte spec (`verifyBytes p v pkSeed pkRoot message
  sig`):

    * the three contract params resolve to the SAME word forms the byte spec's
      `hMsgC13` hashes — `pkSeed`/`pkRoot` via `wordOfHash16` (16-byte hash in the
      HIGH half of a 256-bit word), `message` via `baToNatBE message % wordMod`;
    * the two ABI locals (`sig_length`, `sig_data_offset`) resolve to `sig.size`
      and the real EVM `sig.offset = 4 + 32*5 = 164`;
    * `calldata` is the byte-faithful EVM image: the five ABI-head words followed
      by `sig` chunked into big-endian 32-byte words (`bytesToWords`).

  This file freezes that contract and proves the param/ABI-local resolution
  lemmas (`mkC13State_resolves_*`).  The deeper calldata↔`read16` correspondence
  (the sig-word reads) is consumed by the S2/Sn segment lemmas; here we pin the
  first aligned sig read (`mkC13State_resolves_R_raw`).

  No `sorry`, no `native_decide`, no new `axiom`.
-/

import SphincsMinusVerifiers.Model
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.MkC13State

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr)
open SphincsMinusVerifierSpec.C13Concrete (wordOfHash16 baToNatBE wordMod)

/-! ## 1. Byte image of a signature: chunk into big-endian 32-byte words. -/

/-- Chunk a `ByteArray` into big-endian 32-byte words (the EVM calldata data
region image): word `q` is the big-endian value of bytes `[32*q, 32*q+32)`,
zero-padded past the end.  `⌈size/32⌉` words. -/
def bytesToWords (ba : ByteArray) : List Nat :=
  (List.range ((ba.size + 31) / 32)).map (fun q =>
    (List.range 32).foldl (fun acc j => acc * 256 + ((ba[32 * q + j]?).getD 0).toNat) 0)

/-! ## 2. The frozen bytes→RuntimeState constructor. -/

/-- The real EVM `sig.offset` for the C13 ABI head `(pkSeed, pkRoot, message,
sigHeadOffset, sigLength)`: byte `4 + 32*5 = 164`. -/
def sigDataOffset : Nat := 164

/-- The ABI-head calldata words preceding the signature data region:
`pkSeed`/`pkRoot` packed into the high half, the full `message` word, the
sig head-offset `0x80`, and the sig byte length. -/
def headWords (pkSeed pkRoot message : ByteArray) (sigLen : Nat) : List Nat :=
  [ wordOfHash16 pkSeed
  , wordOfHash16 pkRoot
  , baToNatBE message % wordMod
  , 0x80
  , sigLen ]

/-- **Frozen Phase-1 contract.**  `mkC13State pkSeed pkRoot message sig`: bind the
three contract params to their byte-spec word forms and the two ABI locals to
`sig.size` / `164`, and install the byte-faithful calldata image.  Memory starts
all-zero (EVM convention). -/
def mkC13State (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  let cd := headWords pkSeed pkRoot message sig.size ++ bytesToWords sig
  { world := { Verity.defaultState with
                 calldata := cd
                 calldataSize := (4 + cd.length * 32 : Nat)
                 memory := fun _ => 0 }
    bindings :=
      bindValue (bindValue (bindValue (bindValue (bindValue []
        "pkSeed" (wordOfHash16 pkSeed)) "pkRoot" (wordOfHash16 pkRoot))
        "message" (baToNatBE message % wordMod))
        "sig_length" sig.size) "sig_data_offset" sigDataOffset
    selector := 0 }

/-! ## 3. Param / ABI-local resolution lemmas.

These pin the frozen contract's binding word-forms: every interpreter `.param`
read of the five bound names returns exactly the byte-spec value the H_msg /
length-guard / sig-base computations expect. -/

theorem mkC13State_resolves_pkSeed (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (mkC13State pkSeed pkRoot message sig) (.param "pkSeed")
      = some (wordOfHash16 pkSeed) := rfl

theorem mkC13State_resolves_pkRoot (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (mkC13State pkSeed pkRoot message sig) (.param "pkRoot")
      = some (wordOfHash16 pkRoot) := rfl

theorem mkC13State_resolves_message (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (mkC13State pkSeed pkRoot message sig) (.param "message")
      = some (baToNatBE message % wordMod) := rfl

theorem mkC13State_resolves_sigLength (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (mkC13State pkSeed pkRoot message sig) (.param "sig_length")
      = some sig.size := rfl

theorem mkC13State_resolves_sigOffset (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (mkC13State pkSeed pkRoot message sig) (.param "sig_data_offset")
      = some sigDataOffset := rfl

/-- The first aligned signature read: `calldataload(sig_data_offset)` resolves to
the first 32-byte big-endian word of `sig` (mod `2^256`) — the raw `R`-word the
H_msg block masks with `N_MASK`.  `sig.offset = 164` is byte-aligned to data
word 0, so the byte-addressed `calldataloadWord` reduces to `bytesToWords sig`'s
head. -/
theorem mkC13State_resolves_R_raw (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (mkC13State pkSeed pkRoot message sig)
        (.calldataload (.param "sig_data_offset"))
      = some (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig) sigDataOffset) := rfl

/-! ## 4. Axiom audit. -/

#print axioms mkC13State_resolves_pkSeed
#print axioms mkC13State_resolves_pkRoot
#print axioms mkC13State_resolves_message
#print axioms mkC13State_resolves_sigLength
#print axioms mkC13State_resolves_sigOffset
#print axioms mkC13State_resolves_R_raw

end SphincsMinusVerifiers.MkC13State
