/-
  Shared verifier proof core.

  This module contains the concrete primitive packages and executable observable
  runners used by both the final refinement theorem layer and the segment-level
  bridge lemmas.  Keeping these definitions out of `Proofs.lean` avoids an import
  cycle: segment lemmas can depend on the concrete runners without depending on
  the final `*_refines_byte_spec` theorem layer.
-/

import SphincsMinusVerifierSpec.Spec
import SphincsMinusVerifierSpec.C13Concrete
import SphincsMinusVerifiers.Model
import SphincsMinusVerifiers.MkC13State

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics

/-- Concrete primitive semantics for the C13 Keccak/SPHINCS- variant. -/
def c13Primitives : Primitives := C13Concrete.c13PrimitivesConcrete

/-- Concrete primitive semantics for the SHA2 SLH-DSA verifier variant. -/
axiom slhDsaSha2_128_24_Primitives : Primitives

/-- Observable verifier result for a completed source-semantics run.  Only the
EVM boolean words `0` and `1` are accepted as normal boolean returns; reverts and
non-boolean exits map to `none`, matching `ByteLevel.verifyBytes`. -/
def observeStmtResultBool (r : StmtResult) : Option Bool :=
  match r with
  | .return value _ =>
      if value = 0 then some false
      else if value = 1 then some true
      else none
  | .revert => none
  | .continue _ => none
  | .stop _ => none

/-- Observable semantics of the compiled C13 Verity model: `none` means revert,
`some b` means normal boolean return. This runs the real source-semantics body
over the frozen byte-facing C13 entry state. -/
def execC13Concrete :
    Bytes → Bytes → Bytes → Bytes → Option Bool :=
  fun pkSeed pkRoot message sig =>
    observeStmtResultBool
      (execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig) c13VerifyBody)

/-- Exported C13 runner, definitionally the concrete source-semantics runner. -/
def execC13 : Bytes → Bytes → Bytes → Bytes → Option Bool :=
  execC13Concrete

theorem observeStmtResultBool_return_boolWord
    (b : Bool) (st : RuntimeState) :
    observeStmtResultBool (.return (wordNormalize (boolWord b)) st) = some b := by
  cases b <;> rfl

theorem observeStmtResultBool_revert :
    observeStmtResultBool .revert = none := rfl

/-- Observable semantics of the compiled SHA2 SLH-DSA Verity model. -/
opaque execSlhDsaSha2_128_24 :
  Bytes → Bytes → Bytes → Bytes → Option Bool

end SphincsMinusVerifiers
