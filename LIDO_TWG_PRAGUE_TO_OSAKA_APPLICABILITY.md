# Lido CircuitBreaker × TWG: Prague→Osaka applicability ledger

**Boundary date:** 2026-09-02

**Network target:** Ethereum mainnet BPO2, the Osaka execution rules plus the
BPO2 blob schedule

**Artifacts:** Blanc's compiler-owned Lido CircuitBreaker runtime at
`officialParams` and TriggerableWithdrawalsGateway runtime at
`Composition.LidoCircuitBreakerTwg.controlDeployParams`

This ledger classifies every EIP included by final
[EIP-7607](https://eips.ethereum.org/EIPS/eip-7607). It asks a deliberately
narrow question: can the Prague→Osaka rule delta change the opcodes,
precompiles, message execution, storage, logs, returndata, or admissibility of
the finite `pauseFor`/`isPaused` and composed public-pause transactions replayed
by this goal?

`Touches` does not mean that contract logic changes. It means that a fork rule
lies on the scenario's validation envelope and must be checked explicitly.
`Does not touch` means the rule's trigger is absent from both artifacts and
from the replay envelope. The ledger is model-boundary evidence only: no row is
a premise of a Lean theorem.

## Artifact and scenario footprint

- The family rows execute the exact compiled gateway's `pauseFor(uint256)` and
  `isPaused()` entries. They use ordinary calldata, storage reads/writes,
  timestamp comparison, one `Paused(uint256)` log, and canonical word return.
- The composed rows execute the exact compiled CircuitBreaker calling the exact
  installed gateway with `CALL` and then `STATICCALL`. The target is an ordinary
  account, not a precompile. Both the finite duration and `2^256 - 1` sentinel
  duration are replayed.
- The lane authors no blob transaction and invokes neither MODEXP (`0x05`) nor
  P256VERIFY (`0x100`). The source programs contain no `CLZ` instruction.
- Each row is a singleton ordinary transaction with explicit gas, timestamp,
  base fee and block gas-limit inputs. The checker owns the transaction-gas and
  encoded-size bounds; it does not infer them from a client default.

## Complete Fusaka applicability table

| EIP | Osaka rule surface | Verdict | Reason for this footprint | Premise for a future schedule-parametric statement |
|---|---|---|---|---|
| [7594](https://eips.ethereum.org/EIPS/eip-7594) PeerDAS | Blob data-availability networking, cell proofs, and at most six blobs per blob transaction | Does not touch | Every lane transaction is non-blob and carries zero blob hashes. No contract opcode or precompile rule changes. | `tx.blobVersionedHashes = []`; no blob wrapper or cell-proof input. |
| [7823](https://eips.ethereum.org/EIPS/eip-7823) MODEXP input bounds | Rejects a MODEXP call when a base, exponent or modulus length exceeds 1024 bytes | Does not touch | Neither runtime calls precompile address `0x05`; no descendant in the selected pause/query paths does so. | Selected call trace contains no target `0x05`. |
| [7825](https://eips.ethereum.org/EIPS/eip-7825) transaction gas cap | Rejects a transaction whose declared gas limit exceeds `2^24` | **Touches the envelope** | It can reject an otherwise unchanged transaction before EVM entry. Every lane row must therefore pin and check `tx.gasLimit ≤ 16,777,216`; below the cap it changes no opcode price or message result. | `tx.gasLimit ≤ 2^24`, separate from the proved child/message gas schedule. |
| [7883](https://eips.ethereum.org/EIPS/eip-7883) MODEXP repricing | Reprices only precompile address `0x05` | Does not touch | The selected traces contain no MODEXP call, so neither child cost nor the CircuitBreaker parent schedule receives this price. | Selected call trace contains no target `0x05`; no MODEXP gas term. |
| [7917](https://eips.ethereum.org/EIPS/eip-7917) proposer lookahead | Consensus-layer proposer selection/state | Does not touch | It supplies no EVM field consumed by either program and changes no EL transaction or opcode rule. | None; this remains outside the EL transition statement. |
| [7918](https://eips.ethereum.org/EIPS/eip-7918) blob base-fee floor | Changes `calc_excess_blob_gas` using the active blob schedule and execution base fee | Does not touch | The rows are non-blob transactions and neither runtime reads `BLOBBASEFEE`; ordinary `baseFeePerGas` remains an explicit unchanged environment input. | No blob gas and no `BLOBBASEFEE` instruction in the selected programs. |
| [7934](https://eips.ethereum.org/EIPS/eip-7934) RLP block-size cap | Rejects an oversized RLP-encoded execution block | **Touches the envelope** | It does not alter message execution, but an oversized authored block would be inadmissible. Independently of gas, the lane derives a conservative `8,435`-byte RLP upper bound from at most 32 header fields of at most 256 bytes, one legacy transaction with at most 36 calldata bytes, empty ommers and empty withdrawals, then checks it against the `8,388,608`-byte Osaka cap. | Explicit current-header field/count bounds, singleton legacy envelope and exact calldata maximum; no claim from gas alone. |
| [7939](https://eips.ethereum.org/EIPS/eip-7939) `CLZ` | Adds opcode `0x1e` with fixed gas | Does not touch | Neither compiler-owned source program contains `Ninst.clz`; the selected artifacts therefore execute no new opcode. Raw byte occurrence is not used as an opcode census. | Source/compiled-instruction census excludes `CLZ`; no new opcode-cost term. |
| [7951](https://eips.ethereum.org/EIPS/eip-7951) P256VERIFY | Adds precompile `0x100` at 6900 gas | Does not touch | The composed target is the installed gateway account and the family entries make no external call. No selected descendant targets `0x100`. | Selected call trace contains no target `0x100`; target-not-precompile remains explicit. |
| [7892](https://eips.ethereum.org/EIPS/eip-7892) blob-parameter-only forks | Moves blob `target`, `max`, and `baseFeeUpdateFraction` into the activated schedule | Does not touch | The rows have no blobs and read no blob fee. This EIP is nevertheless the rule-data bridge from Osaka to BPO2 and is pinned by the shared current-mainnet profile. | Active fork/profile carries a blob schedule, while the transaction has zero blob inputs. |
| [7642](https://eips.ethereum.org/EIPS/eip-7642) `eth/69` history expiry and receipts | Execution-network protocol and historical receipt representation | Does not touch | The finite state transition consumes neither peer history nor the networking receipt format; the lane checks the transition result returned by the isolated target. | None; networking/history availability is outside the theorem and lane state transition. |
| [7910](https://eips.ethereum.org/EIPS/eip-7910) `eth_config` | JSON-RPC configuration reporting | Does not touch | The lane invokes the locked execution transition entrypoint, not `eth_config`; runtime semantics and the authored environment are unchanged. | Profile identity is a gate input, never an RPC-derived theorem premise. |
| [7935](https://eips.ethereum.org/EIPS/eip-7935) 60M default gas limit | Client default block-gas-limit configuration | Does not touch | It is informational and the lane authors an explicit block gas limit. Transaction admissibility is owned separately by EIP-7825's cap. | Explicit `env.currentGasLimit`; no reliance on a client default. |

## Osaka→BPO2

Final [EIP-8135](https://eips.ethereum.org/EIPS/eip-8135) states that BPO2
modifies only the EIP-7892 blob parameters and no other protocol behavior. Its
mainnet values are target `14`, maximum `21`, and base-fee update fraction
`11,684,671`, active at timestamp `1767747671`. Because every row above carries
zero blobs and executes no `BLOBBASEFEE`, Osaka→BPO2 does not change the
scenario's storage, events, returndata, call trace, or gas schedule. The lane
still executes the literal BPO2 module and binds the shared runtime lock; it
does not emulate BPO2 by running Osaka with copied constants.

## Claim boundary

This is a finite, dated compatibility classification for the two named
compiler-owned artifacts and the registered scenarios. It is not a claim about
current chain code, roles or storage; it is not universal fork equivalence; and
it is not a liveness or universal-gas theorem. A future change in any row is a
Jaune pin-movement and proof-revalidation decision. It must not be repaired by
silently changing the lane, reference lock, or this verdict table.
