// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

/// SphincsFrameVerify — EIP-8141 VERIFY-frame module for SphincsFrameAccount.
///
/// Spec: EIP-8141 "Frame Transaction" (Draft), checked against ethereum/EIPs
/// master af3a7802c8ea (2026-10-09). Since ead1a3603551 (2026-08-18) SIGPARAM
/// only reads metadata (params 0x00..0x03; any other param halts) and raw
/// ARBITRARY signature bytes are copied with SIGDATACOPY (0xb5). The module
/// cannot be swapped once an account is deployed, so re-check this against the
/// spec revision a chain implements before deploying an account.
///
/// WHY YUL. This module needs five instructions that solc does not know:
///   TXPARAM (0xb0), FRAMEPARAM (0xb3), SIGPARAM (0xb4), SIGDATACOPY (0xb5),
///   APPROVE (0xaa).
/// They are reachable only through Yul's `verbatim_*` builtins, which are NOT
/// available in Solidity inline assembly (solc 0.8.30 rejects them outright).
/// Hence a standalone Yul object, DELEGATECALLed by the Solidity account.
///
/// WHY DELEGATECALL. `APPROVE` reverts unless `ADDRESS == resolved_target`, and
/// the resolved target of the verify frame is the account. DELEGATECALL keeps
/// ADDRESS equal to the account, so the approval is attributed correctly. The
/// spec blesses exactly this shape for the public mempool:
///   · "This permits helper contracts and libraries during validation,
///      including via DELEGATECALL, so long as they do not introduce additional
///      mutable-state dependencies."
///
/// NO STORAGE. The module executes no SLOAD. The account keeps pkSeed, pkRoot
/// and verifier as immutables (PUSH32 in its code) and forwards them as the
/// DELEGATECALL input. Reading them from storage instead would cost three cold
/// SLOADs (3 x 2100 gas) on every verify, because a frame transaction's
/// accessed_storage_keys starts empty.
///
/// INPUTS. The digest comes from TXPARAM(0x08) = compute_sig_hash(tx) and the
/// witness from an ARBITRARY entry of tx.signatures via SIGDATACOPY — the shape the
/// spec mandates: "Bespoke signature schemes must place their witness bytes in
/// an ARBITRARY signature entry rather than in frame data when the witness signs
/// the canonical transaction signature hash." Nothing in frame calldata is
/// trusted. The only calldata this module reads is the DELEGATECALL input,
/// which the account builds from its own immutables and, optionally, the
/// signature index its frame data names:
///   0x00 pkSeed   0x20 pkRoot   0x40 verifier (address, left-padded)
///   0x60 sigIndex (only when the input is 0x80 bytes long)
/// The index is not trusted for soundness: it only picks which entry's bytes are
/// checked against this account's key over compute_sig_hash(tx), and that hash
/// covers every frame's data, so the witness also commits to the index.
///
/// DELEGATECALL ONLY. Because the keys arrive as calldata, a VERIFY frame aimed
/// at the module itself could otherwise supply the attacker's own keys and
/// verifier and APPROVE with ADDRESS == module. The runtime therefore reverts
/// first when ADDRESS equals the module's own address. That address is stored
/// as an immutable at deploy time. The check runs before any EIP-8141 opcode,
/// so it also holds on a pre-8141 EVM.
///
/// NOT RUNNABLE on a pre-8141 EVM: 0xaa / 0xb0 / 0xb3 / 0xb4 / 0xb5 are undefined
/// opcodes today, so any execution past the delegatecall-only guard halts
/// exceptionally. Verified by bytecode assertions in
/// test/SphincsFrameAccountC13Test.t.sol, and run end to end under the current
/// spec text by the mini-EVM in test/py/frame8141_emu.py
/// (test/SphincsFrameModuleEmuTest.t.sol, real C13 verifier and witnesses).
object "SphincsFrameVerify" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        // The runtime's own address, used by the delegatecall-only guard below.
        setimmutable(0, "self", address())
        return(0, datasize("runtime"))
    }

    object "runtime" {
        code {
            // ───────────────────────── frame introspection ─────────────────────────
            //
            // Every verbatim blob below takes AT MOST ONE stack input and pushes all
            // of its constant operands itself. That is deliberate: with n=1 the input
            // is unambiguously the single item on the stack when the blob starts, so
            // none of this depends on how verbatim orders multiple arguments.

            // TXPARAM(param):  PUSH1 param ; TXPARAM
            function txSigHash()    -> v { v := verbatim_0i_1o(hex"6008b0") } // 0x08 compute_sig_hash(tx)
            function txFrameIndex() -> v { v := verbatim_0i_1o(hex"600ab0") } // 0x0A current frame index
            function txNumSigs()    -> v { v := verbatim_0i_1o(hex"600bb0") } // 0x0B len(signatures)

            // SIGPARAM(param, i):  [i] PUSH1 param ; SWAP1 ; SIGPARAM
            //   after SWAP1 the stack is param, i with i on top — the order the
            //   spec specifies ("signatureIndex on top, param second from top").
            function sigScheme(i) -> v { v := verbatim_1i_1o(hex"600190b4", i) } // 0x01 scheme
            function sigMsg(i)    -> v { v := verbatim_1i_1o(hex"600290b4", i) } // 0x02 msg
            function sigLen(i)    -> v { v := verbatim_1i_1o(hex"600390b4", i) } // 0x03 len(signature)

            // FRAMEPARAM(0x06, idx) = allowed_scope = frame.flags & APPROVE_SCOPE_MASK
            function frameAllowedScope(idx) -> v { v := verbatim_1i_1o(hex"600690b3", idx) }

            // SIGDATACOPY (0xb5): copy ARBITRARY signature `i` into memory at
            // ARGS_SIG (0xa4), dataOffset 0, length = SIGPARAM(0x03, i). The opcode
            // wants, top-down: memOffset, dataOffset, length, signatureIndex.
            // (The SIGPARAM(0x04) copy form of the 2026-07-28 draft no longer
            // exists; under the current spec that param is an exceptional halt.)
            //
            //   [i]
            //   DUP1       -> i i
            //   PUSH1 03   -> i i 3
            //   SWAP1      -> i 3 i          (top = i)
            //   SIGPARAM   -> i len          (len = SIGPARAM(0x03, i))
            //   PUSH1 00   -> i len 0
            //   PUSH2 00a4 -> i len 0 mo     (top-down: mo, 0, len, i)
            //   SIGDATACOPY -> consumes all four, copies, returns nothing
            //
            // The 0x00a4 immediate MUST equal ARGS_SIG below.
            function sigCopyToArgs(i) {
                verbatim_1i_0o(hex"80600390b460006100a4b5", i)
            }

            // APPROVE(offset=0, length=0, scope):  [scope] PUSH1 00 ; PUSH1 00 ; APPROVE
            // Exits this call frame successfully and records the approval.
            function approve(scope) { verbatim_1i_0o(hex"60006000aa", scope) }

            // Error(string) revert, for strings of at most 32 bytes.
            function revertStr(len, str) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, len)
                mstore(0x44, str)
                revert(0x00, 0x64)
            }

            // ───────────────── delegatecall-only guard ─────────────────
            //
            // pkSeed, pkRoot and verifier come from calldata (see header). Run only
            // inside an account's DELEGATECALL, never as a frame target in our own
            // right, or the caller's keys would let the module APPROVE for itself.
            if eq(address(), loadimmutable("self")) { revertStr(17, "delegatecall only") }

            // ───────────────── pick the witness over the canonical hash ─────────────────
            //
            // scheme 0x0 is ARBITRARY. `msg == 0` means len(msg) == 0, i.e. the witness
            // signs compute_sig_hash(tx): the spec reserves the zero stack value for
            // exactly that case ("The explicit 32-byte zero digest is invalid. This
            // reserves the zero stack value as the EVM-visible representation of the
            // transaction signing hash case"). A non-zero msg means the witness signs
            // some other digest, which would reintroduce the unbound-digest problem
            // this module exists to remove — so it is rejected, not accepted.
            //
            // Which entry: the account forwards the index named by its frame data
            // (`verifyFrameAndApprove(uint256 sigIndex)`) as input word 0x60. Every
            // SphincsFrameAccount shares this module, so with two of them in one
            // transaction (e.g. sender + sponsor) each frame must point at its own
            // witness. That entry must be ARBITRARY with an empty msg. Without an
            // index (`verifyFrameAndApprove()`, 0x60-byte input) the FIRST such entry
            // is used, which only works when this account's witness is the first
            // ARBITRARY empty-msg entry. A wrong pick fails verification rather than
            // approving anything. (review frame-first-arbitrary-entry)
            let numSigs := txNumSigs()
            let idx := not(0) // sentinel: none found
            switch gt(calldatasize(), 0x60)
            case 1 {
                idx := calldataload(0x60)
                if iszero(lt(idx, numSigs)) { revertStr(28, "signature index out of range") }
                if iszero(and(iszero(sigScheme(idx)), iszero(sigMsg(idx)))) {
                    revertStr(29, "not an ARBITRARY tx signature")
                }
            }
            default {
                for { let i := 0 } lt(i, numSigs) { i := add(i, 1) } {
                    if and(iszero(sigScheme(i)), iszero(sigMsg(i))) {
                        idx := i
                        break
                    }
                }
                if eq(idx, not(0)) { revertStr(25, "no ARBITRARY tx signature") }
            }

            // ───────────────── call the shared verifier ─────────────────
            //
            // verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes sig)
            // selector 0x2bf6eda8. Calldata laid out from 0x00:
            //   0x00 selector
            //   0x04 pkSeed            (DELEGATECALL input 0x00)
            //   0x24 pkRoot            (DELEGATECALL input 0x20)
            //   0x44 message           = compute_sig_hash(tx)
            //   0x64 bytes offset      = 0x80, relative to the args block at 0x04
            //   0x84 bytes length
            //   0xa4 witness bytes     = ARGS_SIG
            // Memory above 0xa4 is untouched and therefore already zero, so the
            // ABI tail padding needs no explicit write.
            let ARGS_SIG := 0xa4
            let witnessLen := sigLen(idx)

            mstore(0x00, shl(224, 0x2bf6eda8))
            calldatacopy(0x04, 0x00, 0x40) // pkSeed, pkRoot
            mstore(0x44, txSigHash())
            mstore(0x64, 0x80)
            mstore(0x84, witnessLen)
            sigCopyToArgs(idx)

            let argsLen := add(ARGS_SIG, and(add(witnessLen, 31), not(31)))
            // *CALL uses only the low 160 bits of the address operand, so no mask.
            let verifier := calldataload(0x40)

            // `gas()` is the first argument, so Yul evaluates it last and GAS lands
            // immediately before STATICCALL — the one form the validation-prefix
            // opcode ban explicitly exempts ("GAS ... Except when followed
            // immediately by a *CALL instruction").
            // Every live verifier RETURNS false for a soundness rejection (bad root,
            // FORS+C forced-zero, WOTS+C target sum), so those reach "invalid SPHINCS+
            // signature" below; a revert here means malformed input (wrong length,
            // non-canonical key).
            let ok := staticcall(gas(), verifier, 0x00, argsLen, 0x00, 0x20)
            if iszero(ok) { revertStr(18, "verify call failed") }
            // Fail-closed on a short return: the output region still holds the
            // selector word written above, which is never 1, so a verifier that
            // returns fewer than 32 bytes is rejected rather than read as `true`.
            if iszero(eq(mload(0x00), 1)) { revertStr(26, "invalid SPHINCS+ signature") }

            // ───────────────── approve ─────────────────
            //
            // Approve exactly what this frame is permitted to approve, rather than
            // taking a scope from calldata: `self_verify` has flags 0x3 and must call
            // APPROVE(APPROVE_EXECUTION_AND_PAYMENT); `only_verify` has flags 0x2 and
            // must call APPROVE(APPROVE_EXECUTION). Structural rule 3 requires the
            // APPROVE scope to match frame.flags, so deriving the scope from
            // FRAMEPARAM(0x06) satisfies that by construction.
            let scope := frameAllowedScope(txFrameIndex())
            if iszero(scope) { revertStr(21, "frame may not approve") }
            approve(scope)
        }
    }
}
