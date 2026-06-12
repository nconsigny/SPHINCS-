/- 
  Verity compilation models for the production verifier contracts reviewed in
  nconsigny/SPHINCS-:

  * src/SPHINCs-C13Asm.sol
  * src/SLH-DSA-SHA2-128-24verifier.sol

  These models intentionally mirror the handwritten assembly structure.  They
  use Verity's ABI-aware `Bytes` parameter locals:

    sig_length      = Solidity `sig.length`
    sig_data_offset = Solidity `sig.offset`

  Remaining fidelity gaps are tracked in `SphincsMinusVerifiers/README.md`.
-/

import Compiler.CompilationModel
import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SphincsMinusVerifiers

open Compiler.CompilationModel

private def u (n : Nat) : Expr := .literal n
private def p (name : String) : Expr := .param name
private def v (name : String) : Expr := .localVar name

private def notE (x : Expr) : Expr := .logicalNot x
private def eqE (a b : Expr) : Expr := .eq a b
private def iszero (x : Expr) : Expr := .eq x (u 0)
private def addE (a b : Expr) : Expr := .add a b
private def subE (a b : Expr) : Expr := .sub a b
private def mulE (a b : Expr) : Expr := .mul a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def xorE (a b : Expr) : Expr := .bitXor a b
private def shlE (a b : Expr) : Expr := .shl a b
private def shrE (a b : Expr) : Expr := .shr a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def cdload (off : Expr) : Expr := .calldataload off
private def mload (off : Nat) : Expr := .mload (u off)
private def mloadE (off : Expr) : Expr := .mload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val
private def gas : Expr := .intrinsic "gas" (.builtin "gas") .cancun []
private def sha256Call (inOffset inSize outOffset outSize : Nat) : Expr :=
  .staticcall gas (u 0x02) (u inOffset) (u inSize) (u outOffset) (u outSize)
private def yulLit (n : Nat) : Compiler.Yul.YulExpr := .lit n
private def revert0 : List Stmt := [
  .unsafeYul <|
    UnsafeYulFragment.rawRevert (yulLit 0) (yulLit 0)
      { name := "raw_yul_revert_0_0_refines_solidity_assembly"
        obligation := "The handwritten Yul revert(0, 0) must match the Solidity assembly observable revert behavior."
        proofStatus := .assumed }
      "raw_yul_revert_0_0"
]
private def errorSelector : Expr :=
  u 0x08c379a000000000000000000000000000000000000000000000000000000000
private def invalidSigLengthWord : Expr :=
  u 0x496e76616c696420736967206c656e6774680000000000000000000000000000
private def invalidPublicKeyWord : Expr :=
  u 0x496e76616c6964207075626c6963206b65790000000000000000000000000000
private def errorStringRevert (word : Expr) : List Stmt := [
  mstore 0x00 errorSelector,
  mstore 0x04 (u 0x20),
  mstore 0x24 (u 18),
  mstore 0x44 word,
  .unsafeYul <|
    UnsafeYulFragment.rawRevert (yulLit 0x00) (yulLit 0x64)
      { name := "raw_yul_revert_0_100_refines_solidity_assembly"
        obligation := "The handwritten Yul revert(0, 100) must match the Solidity assembly observable revert behavior."
        proofStatus := .assumed }
      "raw_yul_revert_0_100"
]

def N_MASK : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

private def verifyParams : List Param := [
  { name := "pkSeed", ty := .bytes32 },
  { name := "pkRoot", ty := .bytes32 },
  { name := "message", ty := .bytes32 },
  { name := "sig", ty := .bytes }
]

private def returnBoolFromWord (name : String) : List Stmt := [
  mstore 0x00 (v name),
  .return (mload 0x00)
]

def c13LengthGuard : Stmt :=
  .ite (notE (eqE (v "sig_length") (u 3688))) (errorStringRevert invalidSigLengthWord) []

def publicKeyCanonicalityGuard : Stmt :=
  .ite
    (orE
      (notE (eqE (p "pkSeed") (andE (p "pkSeed") (u N_MASK))))
      (notE (eqE (p "pkRoot") (andE (p "pkRoot") (u N_MASK)))))
    (errorStringRevert invalidPublicKeyWord) []

/-- Model of `SPHINCs-C13Asm.verify`.

The code follows the Yul loops and memory layout from `SPHINCs-C13Asm.sol`.
It is not factored into helpers because the Solidity implementation is also a
single inlined assembly block, and line-by-line refinement is the proof target.
-/
def c13VerifyBodyTail : List Stmt := [
  .letVar "seed" (p "pkSeed"),
  .letVar "root" (p "pkRoot"),
  mstore 0x00 (v "seed"),

  .letVar "R" (andE (cdload (v "sig_data_offset")) (u N_MASK)),
  mstore 0x20 (v "root"),
  mstore 0x40 (v "R"),
  mstore 0x60 (p "message"),
  mstore 0x80 (u 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
  .letVar "digest" (keccak 0x00 0xA0),
  .letVar "htIdx" (andE (shrE (u 133) (v "digest")) (u 0x3FFFFF)),

  .letVar "dVal" (v "digest"),
  .ite (andE (shrE (u 114) (v "dVal")) (u 0x7FFFF)) revert0 [],
  .letVar "sigBase" (v "sig_data_offset"),

  .letVar "idxLeaf0" (andE (v "htIdx") (u 0x7FF)),
  .letVar "idxTree0" (shrE (u 11) (v "htIdx")),
  .letVar "forsBase"
    (orE (shlE (u 128) (v "idxTree0"))
      (orE (shlE (u 96) (u 3)) (shlE (u 64) (v "idxLeaf0")))),

  .forEach "i" (u 6) [
    .letVar "treeIdx" (andE (shrE (mulE (v "i") (u 19)) (v "dVal")) (u 0x7FFFF)),
    .letVar "secretVal" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (v "i"))))) (u N_MASK)),
    .letVar "leafAdrs" (orE (v "forsBase") (orE (shlE (u 19) (v "i")) (v "treeIdx"))),
    mstore 0x20 (v "leafAdrs"),
    mstore 0x40 (v "secretVal"),
    .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK)),
    .letVar "pathIdx" (v "treeIdx"),
    .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304)))),
    .forEach "h" (u 19) [
      .letVar "sibling" (andE (cdload (addE (v "authPtr") (shlE (u 4) (v "h")))) (u N_MASK)),
      .letVar "parentIdx" (shrE (u 1) (v "pathIdx")),
      mstore 0x20 (orE (v "forsBase")
        (orE (shlE (u 32) (addE (v "h") (u 1)))
          (orE (shlE (subE (u 18) (v "h")) (v "i")) (v "parentIdx")))),
      .letVar "s" (shlE (u 5) (andE (v "pathIdx") (u 1))),
      mstoreE (xorE (u 0x40) (v "s")) (v "node"),
      mstoreE (xorE (u 0x60) (v "s")) (v "sibling"),
      .assignVar "node" (andE (keccak 0x00 0x80) (u N_MASK)),
      .assignVar "pathIdx" (v "parentIdx")
    ],
    mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node")
  ],

  .letVar "lastSecret" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (u 6))))) (u N_MASK)),
  mstore 0x20 (orE (v "forsBase") (shlE (u 19) (u 6))),
  mstore 0x40 (v "lastSecret"),
  mstore 0x140 (andE (keccak 0x00 0x60) (u N_MASK)),

  mstore 0x20
    (orE (shlE (u 128) (v "idxTree0"))
      (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0")))),
  .forEach "i" (u 7) [
    mstoreE (addE (u 0x40) (shlE (u 5) (v "i"))) (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
  ],
  .letVar "forsPk" (andE (keccak 0x00 0x120) (u N_MASK)),
  .letVar "currentNode" (v "forsPk"),
  .letVar "idxTree" (v "htIdx"),
  .letVar "sigOff" (u 1952),

  .forEach "layer" (u 2) [
    .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF)),
    .assignVar "idxTree" (shrE (u 11) (v "idxTree")),
    .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf")))),
    .letVar "countOff" (addE (v "sigOff") (u 688)),
    .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff")))),
    mstore 0x20 (v "wotsAdrs"),
    mstore 0x40 (v "currentNode"),
    mstore 0x60 (v "count"),
    .letVar "d" (keccak 0x00 0x80),
    .letVar "digitSum" (u 0),
    .forEach "ii" (u 43) [
      .assignVar "digitSum" (addE (v "digitSum") (andE (shrE (mulE (v "ii") (u 3)) (v "d")) (u 0x7)))
    ],
    .ite (notE (eqE (v "digitSum") (u 208))) revert0 [],
    .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")),
    .forEach "i" (u 43) [
      .letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 0x7)),
      .letVar "steps" (subE (u 7) (v "digit")),
      .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)),
      .letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i"))),
      .forEach "step" (v "steps") [
        mstore 0x20 (orE (v "chainBase") (addE (v "digit") (v "step"))),
        mstore 0x40 (v "val"),
        .assignVar "val" (andE (keccak 0x00 0x60) (u N_MASK))
      ],
      mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
    ],
    .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf"))))),
    mstore 0x20 (v "pkAdrs"),
    .forEach "i" (u 43) [
      mstoreE (addE (u 0x40) (shlE (u 5) (v "i"))) (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
    ],
    .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK)),
    .letVar "authOff" (addE (v "countOff") (u 4)),
    .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2)))),
    .letVar "merkleNode" (v "wotsPk"),
    .letVar "mIdx" (v "idxLeaf"),
    .letVar "merklePtr" (addE (v "sigBase") (v "authOff")),
    .forEach "h" (u 11) [
      .letVar "sibling" (andE (cdload (addE (v "merklePtr") (shlE (u 4) (v "h")))) (u N_MASK)),
      .letVar "parentIdx" (shrE (u 1) (v "mIdx")),
      mstore 0x20 (orE (v "treeAdrs") (orE (shlE (u 32) (addE (v "h") (u 1))) (v "parentIdx"))),
      .letVar "s" (shlE (u 5) (andE (v "mIdx") (u 1))),
      mstoreE (xorE (u 0x40) (v "s")) (v "merkleNode"),
      mstoreE (xorE (u 0x60) (v "s")) (v "sibling"),
      .assignVar "merkleNode" (andE (keccak 0x00 0x80) (u N_MASK)),
      .assignVar "mIdx" (v "parentIdx")
    ],
    .assignVar "currentNode" (v "merkleNode"),
    .assignVar "sigOff" (addE (v "authOff") (u 176))
  ],
  .letVar "valid" (eqE (v "currentNode") (v "root"))
] ++ returnBoolFromWord "valid"

/-- The C13 body after the length guard.  This keeps the public-key guard and
the algorithmic body tail named separately, so proof scripts can expose the
preflight surface without unfolding the full verifier body. -/
def c13PublicKeyGuardTail : List Stmt :=
  publicKeyCanonicalityGuard :: c13VerifyBodyTail

def c13VerifyBody : List Stmt :=
  c13LengthGuard :: c13PublicKeyGuardTail

private def verifierFunction (body : List Stmt) (pure : Bool := true) : FunctionSpec := {
  name := "verify",
  params := verifyParams,
  returnType := some .uint256,
  returns := [.bool],
  isPure := pure,
  isView := !pure,
  noExternalCalls := pure,
  body := body,
  localObligations := [
    { name := "assembly_refinement",
      obligation := "The EDSL body is intended to refine the single handwritten assembly block in the corresponding Solidity verifier.",
      proofStatus := .assumed },
    { name := "linear_memory_aliasing",
      obligation := "The model preserves the Solidity scratch-memory layout and branchless mstore aliasing; a future proof must show each dynamic mstore offset matches the assembly offsets.",
      proofStatus := .assumed }
  ]
}

/-- Model of `SLH-DSA-SHA2-128-24verifier.verify`.

The control flow, memory offsets, digest parsing, and precompile invocations
mirror the Solidity assembly block.  The remaining proof blocker is semantic:
Verity's `Expr.staticcall` records the SHA-256 precompile call but does not yet
state the memory postcondition for the 32-byte digest written by precompile 2. -/
def slhDsaSha2VerifyBody : List Stmt := [
  .ite (notE (eqE (v "sig_length") (u 3856))) (errorStringRevert invalidSigLengthWord) [],
  .ite
    (orE
      (notE (eqE (p "pkSeed") (andE (p "pkSeed") (u N_MASK))))
      (notE (eqE (p "pkRoot") (andE (p "pkRoot") (u N_MASK)))))
    (errorStringRevert invalidPublicKeyWord) [],
  .letVar "seed" (p "pkSeed"),
  .letVar "root" (p "pkRoot"),
  .letVar "sigBase" (v "sig_data_offset"),
  mstore 0x00 (cdload (v "sigBase")),
  mstore 0x10 (v "seed"),
  mstore 0x20 (v "root"),
  mstore 0x30 (p "message"),
  .letVar "innerOk" (sha256Call 0x00 0x50 0x20 0x20),
  .ite (iszero (v "innerOk")) revert0 [],
  mstore 0x40 (u 0),
  .letVar "outerOk" (sha256Call 0x00 0x44 0x100 0x20),
  .ite (iszero (v "outerOk")) revert0 [],
  .letVar "dWord" (mload 0x100),
  .letVar "leafIdx" (andE (shrE (u 88) (v "dWord")) (u 0x3FFFFF)),

  mstore 0x00 (v "seed"),
  mstore 0x20 (u 0),
  .letVar "forsBase" (orE (shlE (u 176) (u 3)) (shlE (u 144) (v "leafIdx"))),
  .letVar "wotsBase" (shlE (u 144) (v "leafIdx")),
  .letVar "forsOff" (u 16),

  .forEach "t" (u 6) [
    .letVar "mdT" (andE (shrE (subE (u 232) (mulE (u 24) (v "t"))) (v "dWord")) (u 0xFFFFFF)),
    .letVar "treeOff" (addE (v "forsOff") (mulE (v "t") (u 400))),
    .letVar "sk" (andE (cdload (addE (v "sigBase") (v "treeOff"))) (u N_MASK)),
    mstore 0x40 (orE (v "forsBase") (shlE (u 80) (orE (shlE (u 24) (v "t")) (v "mdT")))),
    mstore 0x56 (v "sk"),
    .letVar "forsLeafOk" (sha256Call 0x00 0x66 0x80 0x20),
    .ite (iszero (v "forsLeafOk")) revert0 [],
    .letVar "node" (andE (mload 0x80) (u N_MASK)),

    .letVar "authPtr" (addE (v "sigBase") (addE (v "treeOff") (u 16))),
    .letVar "pathIdx" (v "mdT"),
    .forEach "j" (u 24) [
      .letVar "sibling" (andE (cdload (addE (v "authPtr") (shlE (u 4) (v "j")))) (u N_MASK)),
      .letVar "parentIdx" (shrE (u 1) (v "pathIdx")),
      .letVar "globalY" (orE (shlE (subE (u 23) (v "j")) (v "t")) (v "parentIdx")),
      mstore 0x40 (orE (v "forsBase") (orE (shlE (u 112) (addE (v "j") (u 1))) (shlE (u 80) (v "globalY")))),
      .ite (eqE (andE (v "pathIdx") (u 1)) (u 0))
        [mstore 0x56 (v "node"), mstore 0x66 (v "sibling")]
        [mstore 0x56 (v "sibling"), mstore 0x66 (v "node")],
      .letVar "forsAuthOk" (sha256Call 0x00 0x76 0x80 0x20),
      .ite (iszero (v "forsAuthOk")) revert0 [],
      .assignVar "node" (andE (mload 0x80) (u N_MASK)),
      .assignVar "pathIdx" (v "parentIdx")
    ],
    mstoreE (addE (u 0x100) (shlE (u 5) (v "t"))) (v "node")
  ],

  mstore 0x40 (orE (shlE (u 176) (u 4)) (shlE (u 144) (v "leafIdx"))),
  .forEach "t" (u 6) [
    mstoreE (addE (u 0x56) (shlE (u 4) (v "t"))) (mloadE (addE (u 0x100) (shlE (u 5) (v "t"))))
  ],
  .letVar "forsRootsOk" (sha256Call 0x00 0xB6 0x80 0x20),
  .ite (iszero (v "forsRootsOk")) revert0 [],
  .letVar "currentNode" (andE (mload 0x80) (u N_MASK)),

  .letVar "wotsPtr" (addE (v "sigBase") (addE (v "forsOff") (u 2400))),
  .letVar "csum" (u 0),
  .forEach "i" (u 64) [
    .letVar "digit" (andE (shrE (subE (u 254) (shlE (u 1) (v "i"))) (v "currentNode")) (u 3)),
    .assignVar "csum" (addE (v "csum") (subE (u 3) (v "digit"))),
    .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)),
    .letVar "chainBase" (orE (v "wotsBase") (shlE (u 112) (v "i"))),
    .letVar "steps" (subE (u 3) (v "digit")),
    .forEach "s" (v "steps") [
      mstore 0x40 (orE (v "chainBase") (shlE (u 80) (addE (v "digit") (v "s")))),
      mstore 0x56 (v "val"),
      .letVar "wotsMsgOk" (sha256Call 0x00 0x66 0x80 0x20),
      .ite (iszero (v "wotsMsgOk")) revert0 [],
      .assignVar "val" (andE (mload 0x80) (u N_MASK))
    ],
    mstoreE (addE (u 0x100) (shlE (u 5) (v "i"))) (v "val")
  ],

  .forEach "j" (u 4) [
    .letVar "digit" (andE (shrE (subE (u 6) (shlE (u 1) (v "j"))) (v "csum")) (u 3)),
    .letVar "i" (addE (u 64) (v "j")),
    .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)),
    .letVar "chainBase" (orE (v "wotsBase") (shlE (u 112) (v "i"))),
    .letVar "steps" (subE (u 3) (v "digit")),
    .forEach "s" (v "steps") [
      mstore 0x40 (orE (v "chainBase") (shlE (u 80) (addE (v "digit") (v "s")))),
      mstore 0x56 (v "val"),
      .letVar "wotsCsumOk" (sha256Call 0x00 0x66 0x80 0x20),
      .ite (iszero (v "wotsCsumOk")) revert0 [],
      .assignVar "val" (andE (mload 0x80) (u N_MASK))
    ],
    mstoreE (addE (u 0x100) (shlE (u 5) (v "i"))) (v "val")
  ],

  mstore 0x40 (orE (shlE (u 176) (u 1)) (shlE (u 144) (v "leafIdx"))),
  .forEach "i" (u 68) [
    mstoreE (addE (u 0x56) (shlE (u 4) (v "i"))) (mloadE (addE (u 0x100) (shlE (u 5) (v "i"))))
  ],
  .letVar "wotsPkOk" (sha256Call 0x00 0x496 0x4A0 0x20),
  .ite (iszero (v "wotsPkOk")) revert0 [],
  .letVar "wotsPk" (andE (mload 0x4A0) (u N_MASK)),

  .letVar "authPtr" (addE (v "wotsPtr") (u 1088)),
  .letVar "merkleNode" (v "wotsPk"),
  .letVar "mIdx" (v "leafIdx"),
  .forEach "hh" (u 22) [
    .letVar "sibling" (andE (cdload (addE (v "authPtr") (shlE (u 4) (v "hh")))) (u N_MASK)),
    .letVar "parentIdx" (shrE (u 1) (v "mIdx")),
    mstore 0x40 (orE (shlE (u 176) (u 2)) (orE (shlE (u 112) (addE (v "hh") (u 1))) (shlE (u 80) (v "parentIdx")))),
    .ite (eqE (andE (v "mIdx") (u 1)) (u 0))
      [mstore 0x56 (v "merkleNode"), mstore 0x66 (v "sibling")]
      [mstore 0x56 (v "sibling"), mstore 0x66 (v "merkleNode")],
    .letVar "xmssOk" (sha256Call 0x00 0x76 0x80 0x20),
    .ite (iszero (v "xmssOk")) revert0 [],
    .assignVar "merkleNode" (andE (mload 0x80) (u N_MASK)),
    .assignVar "mIdx" (v "parentIdx")
  ],

  .letVar "valid" (eqE (v "merkleNode") (v "root"))
] ++ returnBoolFromWord "valid"

def c13Model : CompilationModel := {
  name := "SphincsC13Asm_VerityModel",
  fields := [],
  «constructor» := none,
  functions := [verifierFunction c13VerifyBody true]
}

def slhDsaSha2_128_24_Model : CompilationModel := {
  name := "SLH_DSA_SHA2_128_24_VerityModel",
  fields := [],
  «constructor» := none,
  functions := [verifierFunction slhDsaSha2VerifyBody false]
}

/-! ## Executable-semantics slice of MODEL-EXEC-BRIDGE: malformed-length revert

The MODEL-EXEC-BRIDGE obligation (see `SphincsMinusVerifiers/README.md`) asks us
to connect Verity's executable source semantics
(`Compiler.Proofs.IRGeneration.SourceSemantics`) to the byte-level verifier
contract over the raw `bytes`/calldata surface.  The full obligation (the
accept-path keccak/SHA hypertree-climb equivalence) remains the carried axiom.

The lemmas below discharge one *sound, unconditional* slice of that obligation
directly through the interpreter: each compiled verifier body, when run with the
production field layout (`fields := []`), **reverts** whenever the ABI-decoded
`sig.length` local does not equal the verifier's expected signature length.  This
is the first stmt of every body — the length guard — and the proof runs the real
`execStmtList`/`execStmt`/`evalExpr` interpreter over the actual `*VerifyBody`
terms (no `exec* := verifyBytes` shortcut, no `sorry`).  `#print axioms` on these
lemmas shows only `[propext]`. -/

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- If a statement reverts, the whole statement list reverts (the walker
short-circuits on `.revert`). -/
theorem execStmtList_cons_revert
    (st : RuntimeState) (s : Stmt) (rest : List Stmt)
    (h : execStmt [] st s = .revert) :
    execStmtList [] st (s :: rest) = .revert := by
  show (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = .revert
  rw [h]

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- Generic length-guard revert: any body whose head statement is the standard
`sig_length`-mismatch guard reverts when `sig_length` is not the expected value. -/
theorem verifyBody_reverts_on_bad_length
    (body : List Stmt) (expectedLen : Nat) (st : RuntimeState)
    (hhead : body =
      (.ite (notE (eqE (v "sig_length") (u expectedLen)))
        (errorStringRevert invalidSigLengthWord) []) :: body.tail)
    (hlen : lookupValue st.bindings "sig_length" ≠ wordNormalize expectedLen) :
    execStmtList [] st body = .revert := by
  have he : decide (lookupValue st.bindings "sig_length" = wordNormalize expectedLen) = false :=
    decide_eq_false hlen
  have hcond :
      evalExpr [] st (notE (eqE (v "sig_length") (u expectedLen))) = some 1 := by
    show some (boolWord (decide (boolWord (decide
        (lookupValue st.bindings "sig_length" = wordNormalize expectedLen)) = 0))) = some 1
    rw [he]; rfl
  have hfrag :
      execStmtList [] st (errorStringRevert invalidSigLengthWord) = .revert := rfl
  have hite : execStmt [] st
      (.ite (notE (eqE (v "sig_length") (u expectedLen)))
        (errorStringRevert invalidSigLengthWord) []) = .revert := by
    show (match evalExpr [] st (notE (eqE (v "sig_length") (u expectedLen))) with
          | some resolved =>
              if resolved != 0 then execStmtList [] st (errorStringRevert invalidSigLengthWord)
              else execStmtList [] st []
          | none => .revert) = .revert
    rw [hcond, hfrag]; rfl
  rw [hhead]
  exact execStmtList_cons_revert st _ _ hite

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- C13 verifier body reverts when the ABI-decoded `sig.length ≠ 3688`. -/
theorem c13VerifyBody_reverts_on_bad_length
    (st : RuntimeState)
    (hlen : lookupValue st.bindings "sig_length" ≠ wordNormalize 3688) :
    execStmtList [] st c13VerifyBody = .revert :=
  verifyBody_reverts_on_bad_length c13VerifyBody 3688 st rfl hlen

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- SLH-DSA-SHA2-128-24 verifier body reverts when `sig.length ≠ 3856`. -/
theorem slhDsaSha2VerifyBody_reverts_on_bad_length
    (st : RuntimeState)
    (hlen : lookupValue st.bindings "sig_length" ≠ wordNormalize 3856) :
    execStmtList [] st slhDsaSha2VerifyBody = .revert :=
  verifyBody_reverts_on_bad_length slhDsaSha2VerifyBody 3856 st rfl hlen

/-! ### Length-guard pass-through (the first accept-path step)

The dual of `verifyBody_reverts_on_bad_length`: when the ABI-decoded
`sig_length` local *does* equal the expected signature length, the standard
length guard is a no-op (its condition evaluates to `0`, the else-branch is
`[]`), so the real interpreter falls through to the remainder of the body with
the state unchanged. This is the first step of the accept-path refinement and is
proved unconditionally through the actual `execStmtList`/`execStmt`/`evalExpr`
interpreter — no bridge axiom, no `sorry`. It is the companion that makes the
accept subdomain *reachable* now that `evalExpr` models `keccak256`: before the
keccak semantics landed, execution would still revert at the first hash; these
lemmas establish that the guard itself does not block the accept path. -/

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- Generic length-guard pass-through: a body whose head statement is the
standard `sig_length`-mismatch guard falls through to the tail when
`sig_length` equals the expected value. -/
theorem verifyBody_passes_length_guard
    (expectedLen : Nat) (st : RuntimeState) (rest : List Stmt)
    (hlen : lookupValue st.bindings "sig_length" = wordNormalize expectedLen) :
    execStmtList [] st
        ((.ite (notE (eqE (v "sig_length") (u expectedLen)))
          (errorStringRevert invalidSigLengthWord) []) :: rest)
      = execStmtList [] st rest := by
  have he : decide (lookupValue st.bindings "sig_length" = wordNormalize expectedLen) = true :=
    decide_eq_true hlen
  have hcond :
      evalExpr [] st (notE (eqE (v "sig_length") (u expectedLen))) = some 0 := by
    show some (boolWord (decide (boolWord (decide
        (lookupValue st.bindings "sig_length" = wordNormalize expectedLen)) = 0))) = some 0
    rw [he]; rfl
  have hite : execStmt [] st
      (.ite (notE (eqE (v "sig_length") (u expectedLen)))
        (errorStringRevert invalidSigLengthWord) []) = .continue st := by
    show (match evalExpr [] st (notE (eqE (v "sig_length") (u expectedLen))) with
          | some resolved =>
              if resolved != 0 then execStmtList [] st (errorStringRevert invalidSigLengthWord)
              else execStmtList [] st []
          | none => .revert) = .continue st
    rw [hcond]; rfl
  show (match execStmt [] st
          (.ite (notE (eqE (v "sig_length") (u expectedLen)))
            (errorStringRevert invalidSigLengthWord) []) with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = execStmtList [] st rest
  rw [hite]

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- C13: with `sig.length = 3688`, the length guard is a no-op and execution
proceeds to the public-key guard tail. -/
theorem c13VerifyBody_passes_length_guard
    (st : RuntimeState)
    (hlen : lookupValue st.bindings "sig_length" = wordNormalize 3688) :
    execStmtList [] st c13VerifyBody = execStmtList [] st c13PublicKeyGuardTail := by
  rw [show c13VerifyBody = c13LengthGuard :: c13PublicKeyGuardTail from rfl]
  rw [show c13LengthGuard =
    (.ite (notE (eqE (v "sig_length") (u 3688)))
      (errorStringRevert invalidSigLengthWord) [] : Stmt) from rfl]
  exact verifyBody_passes_length_guard 3688 st c13PublicKeyGuardTail hlen

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- C13: if both ABI public-key words are already canonical high-16-byte values,
the public-key canonicality guard is a no-op and execution proceeds into the
named algorithmic body tail. -/
theorem c13PublicKeyGuardTail_passes_public_key_guard
    (st : RuntimeState)
    (hpkSeed : lookupValue st.bindings "pkSeed" =
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkSeed") (wordNormalize N_MASK)).val)
    (hpkRoot : lookupValue st.bindings "pkRoot" =
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkRoot") (wordNormalize N_MASK)).val) :
    execStmtList [] st c13PublicKeyGuardTail = execStmtList [] st c13VerifyBodyTail := by
  change execStmtList [] st (publicKeyCanonicalityGuard :: c13VerifyBodyTail) =
    execStmtList [] st c13VerifyBodyTail
  have hseedEq : decide (lookupValue st.bindings "pkSeed" =
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkSeed") (wordNormalize N_MASK)).val) = true :=
    decide_eq_true hpkSeed
  have hrootEq : decide (lookupValue st.bindings "pkRoot" =
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkRoot") (wordNormalize N_MASK)).val) = true :=
    decide_eq_true hpkRoot
  have hcond :
      evalExpr [] st
        (orE
          (notE (eqE (p "pkSeed") (andE (p "pkSeed") (u N_MASK))))
          (notE (eqE (p "pkRoot") (andE (p "pkRoot") (u N_MASK)))))
        = some 0 := by
    show some (Verity.Core.Uint256.or
          (boolWord (decide (boolWord (decide
              (lookupValue st.bindings "pkSeed" =
                (Verity.Core.Uint256.and (lookupValue st.bindings "pkSeed") (wordNormalize N_MASK)).val)) = 0)))
          (boolWord (decide (boolWord (decide
              (lookupValue st.bindings "pkRoot" =
                (Verity.Core.Uint256.and (lookupValue st.bindings "pkRoot") (wordNormalize N_MASK)).val)) = 0)))).val
        = some 0
    rw [hseedEq, hrootEq]
    rfl
  have hite : execStmt [] st publicKeyCanonicalityGuard = .continue st := by
    show (match evalExpr [] st
          (orE
            (notE (eqE (p "pkSeed") (andE (p "pkSeed") (u N_MASK))))
            (notE (eqE (p "pkRoot") (andE (p "pkRoot") (u N_MASK))))) with
        | some resolved =>
            if resolved != 0 then execStmtList [] st (errorStringRevert invalidPublicKeyWord)
            else execStmtList [] st []
        | none => .revert) = .continue st
    rw [hcond]
    rfl
  show (match execStmt [] st publicKeyCanonicalityGuard with
        | .continue n => execStmtList [] n c13VerifyBodyTail
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = execStmtList [] st c13VerifyBodyTail
  rw [hite]

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- C13: with `sig.length = 3688` and canonical public-key words, both preflight
guards are no-ops and execution proceeds into the named body tail. -/
theorem c13VerifyBody_passes_preflight_guards
    (st : RuntimeState)
    (hlen : lookupValue st.bindings "sig_length" = wordNormalize 3688)
    (hpkSeed : lookupValue st.bindings "pkSeed" =
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkSeed") (wordNormalize N_MASK)).val)
    (hpkRoot : lookupValue st.bindings "pkRoot" =
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkRoot") (wordNormalize N_MASK)).val) :
    execStmtList [] st c13VerifyBody = execStmtList [] st c13VerifyBodyTail := by
  calc
    execStmtList [] st c13VerifyBody = execStmtList [] st c13PublicKeyGuardTail :=
      c13VerifyBody_passes_length_guard st hlen
    _ = execStmtList [] st c13VerifyBodyTail :=
      c13PublicKeyGuardTail_passes_public_key_guard st hpkSeed hpkRoot

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- C13 public-key guard helper: after an already-passed length guard, the named
guard tail reverts when `pkSeed` is not masked by `N_MASK`. -/
theorem c13PublicKeyGuardTail_reverts_on_bad_pkSeed
    (st : RuntimeState)
    (hpkSeed : lookupValue st.bindings "pkSeed" ≠
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkSeed") (wordNormalize N_MASK)).val) :
    execStmtList [] st c13PublicKeyGuardTail = .revert := by
  change execStmtList [] st (publicKeyCanonicalityGuard :: c13VerifyBodyTail) = .revert
  have hseedEq : decide (lookupValue st.bindings "pkSeed" =
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkSeed") (wordNormalize N_MASK)).val) = false :=
    decide_eq_false hpkSeed
  have hcond :
      evalExpr [] st
        (orE
          (notE (eqE (p "pkSeed") (andE (p "pkSeed") (u N_MASK))))
          (notE (eqE (p "pkRoot") (andE (p "pkRoot") (u N_MASK)))))
        = some 1 := by
    show some (Verity.Core.Uint256.or
          (boolWord (decide (boolWord (decide
              (lookupValue st.bindings "pkSeed" =
                (Verity.Core.Uint256.and (lookupValue st.bindings "pkSeed") (wordNormalize N_MASK)).val)) = 0)))
          (boolWord (decide (boolWord (decide
              (lookupValue st.bindings "pkRoot" =
                (Verity.Core.Uint256.and (lookupValue st.bindings "pkRoot") (wordNormalize N_MASK)).val)) = 0)))).val
        = some 1
    rw [hseedEq]
    by_cases hroot : lookupValue st.bindings "pkRoot" =
        (Verity.Core.Uint256.and (lookupValue st.bindings "pkRoot") (wordNormalize N_MASK)).val
    · rw [decide_eq_true hroot]; rfl
    · rw [decide_eq_false hroot]; rfl
  have hite : execStmt [] st publicKeyCanonicalityGuard = .revert := by
    show (match evalExpr [] st
          (orE
            (notE (eqE (p "pkSeed") (andE (p "pkSeed") (u N_MASK))))
            (notE (eqE (p "pkRoot") (andE (p "pkRoot") (u N_MASK))))) with
        | some resolved =>
            if resolved != 0 then execStmtList [] st (errorStringRevert invalidPublicKeyWord)
            else execStmtList [] st []
        | none => .revert) = .revert
    rw [hcond]
    rfl
  show (match execStmt [] st publicKeyCanonicalityGuard with
        | .continue n => execStmtList [] n c13VerifyBodyTail
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = .revert
  rw [hite]

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- C13 public-key guard helper: after an already-passed length guard, the named
guard tail reverts when `pkRoot` is not masked by `N_MASK`. -/
theorem c13PublicKeyGuardTail_reverts_on_bad_pkRoot
    (st : RuntimeState)
    (hpkRoot : lookupValue st.bindings "pkRoot" ≠
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkRoot") (wordNormalize N_MASK)).val) :
    execStmtList [] st c13PublicKeyGuardTail = .revert := by
  change execStmtList [] st (publicKeyCanonicalityGuard :: c13VerifyBodyTail) = .revert
  have hrootEq : decide (lookupValue st.bindings "pkRoot" =
      (Verity.Core.Uint256.and (lookupValue st.bindings "pkRoot") (wordNormalize N_MASK)).val) = false :=
    decide_eq_false hpkRoot
  have hcond :
      evalExpr [] st
        (orE
          (notE (eqE (p "pkSeed") (andE (p "pkSeed") (u N_MASK))))
          (notE (eqE (p "pkRoot") (andE (p "pkRoot") (u N_MASK)))))
        = some 1 := by
    show some (Verity.Core.Uint256.or
          (boolWord (decide (boolWord (decide
              (lookupValue st.bindings "pkSeed" =
                (Verity.Core.Uint256.and (lookupValue st.bindings "pkSeed") (wordNormalize N_MASK)).val)) = 0)))
          (boolWord (decide (boolWord (decide
              (lookupValue st.bindings "pkRoot" =
                (Verity.Core.Uint256.and (lookupValue st.bindings "pkRoot") (wordNormalize N_MASK)).val)) = 0)))).val
        = some 1
    rw [hrootEq]
    by_cases hseed : lookupValue st.bindings "pkSeed" =
        (Verity.Core.Uint256.and (lookupValue st.bindings "pkSeed") (wordNormalize N_MASK)).val
    · rw [decide_eq_true hseed]; rfl
    · rw [decide_eq_false hseed]; rfl
  have hite : execStmt [] st publicKeyCanonicalityGuard = .revert := by
    show (match evalExpr [] st
          (orE
            (notE (eqE (p "pkSeed") (andE (p "pkSeed") (u N_MASK))))
            (notE (eqE (p "pkRoot") (andE (p "pkRoot") (u N_MASK))))) with
        | some resolved =>
            if resolved != 0 then execStmtList [] st (errorStringRevert invalidPublicKeyWord)
            else execStmtList [] st []
        | none => .revert) = .revert
    rw [hcond]
    rfl
  show (match execStmt [] st publicKeyCanonicalityGuard with
        | .continue n => execStmtList [] n c13VerifyBodyTail
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = .revert
  rw [hite]

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- SLH-DSA-SHA2-128-24: with `sig.length = 3856` the length guard is a no-op and
execution proceeds into the body. Proved, no bridge axiom. -/
theorem slhDsaSha2VerifyBody_passes_length_guard
    (st : RuntimeState)
    (hlen : lookupValue st.bindings "sig_length" = wordNormalize 3856) :
    execStmtList [] st slhDsaSha2VerifyBody = execStmtList [] st slhDsaSha2VerifyBody.tail :=
  verifyBody_passes_length_guard 3856 st slhDsaSha2VerifyBody.tail hlen

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- Continue-step combinator (the dual of `execStmtList_cons_revert`): if the head
statement steps to `.continue st'`, the walker continues from `st'` over the tail.
This is the basic forward step for threading the accept-path straight-line prefix
through the real interpreter. -/
theorem execStmtList_cons_continue
    (st st' : RuntimeState) (s : Stmt) (rest : List Stmt)
    (h : execStmt [] st s = .continue st') :
    execStmtList [] st (s :: rest) = execStmtList [] st' rest := by
  show (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = execStmtList [] st' rest
  rw [h]

open Compiler.Proofs.IRGeneration.SourceSemantics in
set_option maxHeartbeats 2000000 in
/-- Accept-path keccak content: running the C13 Hmsg keccak `letVar`
(`.letVar "digest" (.keccak256 (.literal 0x00) (.literal 0xA0))`, the statement at
the head of the digest-extraction block) over the *real* interpreter binds the
local `"digest"` to the **genuine** Keccak-256 digest of the 0xA0-byte memory slice
(`keccakMemorySlice`, backed by the in-tree `KeccakEngine`) — not `none`/revert.
This is the concrete fruit of the `evalExpr` keccak modeling: before that landed
the body reverted at its first hash; now the accept-path hash is computed.  Proved
unconditionally through `execStmt`/`evalExpr`, no bridge axiom, no `sorry`. -/
theorem c13_keccak_letVar_binds_real_digest (st : RuntimeState) :
    ∃ st',
      execStmt [] st (.letVar "digest" (.keccak256 (.literal 0x00) (.literal 0xA0)))
        = .continue st'
      ∧ lookupValue st'.bindings "digest" = keccakMemorySlice st.world.memory 0 0xA0 := by
  refine ⟨_, rfl, ?_⟩
  rfl

end SphincsMinusVerifiers
