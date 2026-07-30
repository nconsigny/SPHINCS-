/// SphincsFrameVerify — EIP-8141 VERIFY-frame module for SphincsFrameAccount.
///
/// Spec: EIP-8141 "Frame Transaction" (Draft, last updated 2026-07-28).
///
/// WHY YUL. This module needs four instructions that solc does not know:
///   TXPARAM (0xb0), FRAMEPARAM (0xb3), SIGPARAM (0xb4), APPROVE (0xaa).
/// They are reachable only through Yul's `verbatim_*` builtins, which are NOT
/// available in Solidity inline assembly (solc 0.8.30 rejects them outright).
/// Hence a standalone Yul object, DELEGATECALLed by the Solidity account.
///
/// WHY DELEGATECALL. `APPROVE` reverts unless `ADDRESS == resolved_target`, and
/// the resolved target of the verify frame is the account. DELEGATECALL keeps
/// ADDRESS equal to the account, so the approval is attributed correctly, and
/// the storage reads below hit the account's own slots. The spec blesses exactly
/// this shape for the public mempool:
///   · "This permits helper contracts and libraries during validation,
///      including via DELEGATECALL, so long as they do not introduce additional
///      mutable-state dependencies."
///   · "SLOAD can be used only to access tx.sender storage, including when
///      reached transitively via CALL* or DELEGATECALL."
///
/// WHAT IT FIXES. The legacy entry point takes `sigHash` from frame calldata,
/// so a witness is reusable for any transaction presenting the same digest.
/// Here the digest comes from TXPARAM(0x08) = compute_sig_hash(tx) and the
/// witness from an ARBITRARY entry of tx.signatures via SIGPARAM — the shape the
/// spec mandates: "Bespoke signature schemes must place their witness bytes in
/// an ARBITRARY signature entry rather than in frame data when the witness signs
/// the canonical transaction signature hash." Nothing in frame calldata is
/// trusted; the module reads no calldata at all.
///
/// Storage layout, inherited from SphincsFrameAccount:
///   slot 0 = pkSeed   slot 1 = pkRoot   slot 2 = verifier
///
/// NOT RUNNABLE on a pre-8141 EVM: 0xaa / 0xb0 / 0xb3 / 0xb4 are undefined
/// opcodes today, so any execution halts exceptionally. Verified by inspection
/// and by bytecode assertions in test/SphincsFrameAccountC13Test.t.sol.
object "SphincsFrameVerify" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
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

            // SIGPARAM copy form (param 0x04): copy ARBITRARY signature `i` into
            // memory at ARGS_SIG (0xa4), dataOffset 0, length = SIGPARAM(0x03, i).
            // The opcode wants, top-down: i, param, length, dataOffset, memOffset.
            //
            //   [i]
            //   DUP1       -> i i
            //   PUSH1 03   -> i i 3
            //   SWAP1      -> i 3 i          (top = i)
            //   SIGPARAM   -> i len          (len = SIGPARAM(0x03, i))
            //   PUSH2 00a4 -> i len mo
            //   SWAP2      -> mo len i
            //   PUSH1 00   -> mo len i 0
            //   SWAP2      -> mo 0 i len
            //   SWAP1      -> mo 0 len i
            //   PUSH1 04   -> mo 0 len i 4
            //   SWAP1      -> mo 0 len 4 i   (top-down: i, 4, len, 0, mo)
            //   SIGPARAM   -> consumes all five, copies, returns nothing
            //
            // The 0x00a4 immediate MUST equal ARGS_SIG below.
            function sigCopyToArgs(i) {
                verbatim_1i_0o(hex"80600390b46100a49160009190600490b4", i)
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
            // The FIRST such entry is used. With several PQ witnesses in one
            // transaction the author must order theirs first; a mismatch fails
            // verification rather than approving anything.
            let numSigs := txNumSigs()
            let idx := not(0) // sentinel: none found
            for { let i := 0 } lt(i, numSigs) { i := add(i, 1) } {
                if and(iszero(sigScheme(i)), iszero(sigMsg(i))) {
                    idx := i
                    break
                }
            }
            if eq(idx, not(0)) { revertStr(25, "no ARBITRARY tx signature") }

            // ───────────────── call the shared verifier ─────────────────
            //
            // verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes sig)
            // selector 0x2bf6eda8. Calldata laid out from 0x00:
            //   0x00 selector
            //   0x04 pkSeed            (slot 0)
            //   0x24 pkRoot            (slot 1)
            //   0x44 message           = compute_sig_hash(tx)
            //   0x64 bytes offset      = 0x80, relative to the args block at 0x04
            //   0x84 bytes length
            //   0xa4 witness bytes     = ARGS_SIG
            // Memory above 0xa4 is untouched and therefore already zero, so the
            // ABI tail padding needs no explicit write.
            let ARGS_SIG := 0xa4
            let witnessLen := sigLen(idx)

            mstore(0x00, shl(224, 0x2bf6eda8))
            mstore(0x04, sload(0))
            mstore(0x24, sload(1))
            mstore(0x44, txSigHash())
            mstore(0x64, 0x80)
            mstore(0x84, witnessLen)
            sigCopyToArgs(idx)

            let argsLen := add(ARGS_SIG, and(add(witnessLen, 31), not(31)))
            let verifier := and(sload(2), 0xffffffffffffffffffffffffffffffffffffffff)

            // `gas()` is the first argument, so Yul evaluates it last and GAS lands
            // immediately before STATICCALL — the one form the validation-prefix
            // opcode ban explicitly exempts ("GAS ... Except when followed
            // immediately by a *CALL instruction").
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
