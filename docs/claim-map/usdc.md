# Deployed-bytecode claim map: USDC

## 5.10 USDC: proxy forwarding, signature laws and history replay

USDC is three certified runtimes (Section 2): the FiatTokenProxy, which forwards
every non-admin call by `DELEGATECALL` to the implementation its implementation
slot names; the FiatTokenV2_2 implementation, which runs over the proxy's storage;
and the SignatureChecker library the implementation reaches by `DELEGATECALL`
for authorizer-signed messages (`permit`, transferWithAuthorization,
receiveWithAuthorization, cancelAuthorization). The history rows take `UsdcHist`;
the governance, tracked-key and excluded-position premises remain stated below.
These rows do not establish the planned Curve composition with actual DAI, USDC
and USDT bytes.

**Shared token vocabulary**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| The laws a token's pure book (an abstract ledger, its step on one entered frame's message, the decoded operation, balances, allowances, and a well-formedness predicate `Good`) must satisfy: a step from a good ledger lowers a holder's balance only if its caller is the holder or a spender to which the holder had granted a positive allowance; only the owner raises its own allowances; a holder's own `balanceOf`, `transfer` or credit-only call debits it at most by the declared amount and raises none of its allowances; a step decoded as `transfer` to someone else debits the caller exactly; a good ledger's balances are below 2^256 | `Blanc.Lift.Token.BookLaws` (`Blanc/Lift/Token/Core.lean:62`) over `Blanc.Lift.Token.Book` (`Blanc/Lift/Token/Core.lean:48`) | Interface / definition | — | No storage layout appears |
| The token core, what a token's **address** answers along a configured history: under a trace-local premise `Hist` the instance chooses, at the entry of every settled frame the booked ledger is the book run over exactly the non-static entry frames at the token before it, and at the end over all of them; the ledger is good at the checkpoint and at every settled frame's entry; a settled `balanceOf(h)` entry frame, static or not, answers the booked balance for every holder the instance vouches for; a settled `transfer` entry frame answers empty output or a nonzero first word; a settled frame at the token that is not an entry frame (`IsEntry`: storage owner and code address both the token) is a child only of settled frames at the token | `Blanc.Lift.Token.Core` (`Blanc/Lift/Token/Core.lean:98`); entry frames `Blanc.Lift.Token.IsEntry` (`Blanc/Lift/Token/Core.lean:85`) | History / interface | the instance's own `Hist` | Further facts are separate structures over the book or the core, added without editing it: `Blanc.Lift.Token.Erc20Abi` (`Blanc/Lift/Token/Abi.lean:17`) (the standard `transfer` and `balanceOf` selectors decode as those operations for every calldata of at least 68 and 36 bytes respectively and below 2^256), `SelfCaller` and `TransferLive` below. The non-entry clause admits a proxy's delegated implementation frames |
| Facet: every entry-frame child of a settled non-static frame at the token has the token itself as caller | `Blanc.Lift.Token.SelfCaller` (`Blanc/Lift/Token/SelfCaller.lean:18`) | History / interface | the core's `Hist` | No forwarded caller reaches a booked entry |
| Facet: at any world the instance accepts, a fresh entry frame (value 0, non-static, covered fork, the token's code) decoding a `transfer` of at most the caller's booked balance runs to success at an exact instance-given cost, answers the word 1, leaves an accepted world, and, when the recipient is not the caller, debits the caller exactly | `Blanc.Lift.Token.TransferLive` (`Blanc/Lift/Token/Core.lean:145`) | Frame / interface | the instance's world and frame conditions; ENV: gas at least the cost plus the 2,300-gas stipend | |

**The proxy and the `DELEGATECALL` lift**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| A certificate node claiming `CALL` where the code holds `DELEGATECALL` (`0xf4`) is rejected by the checker | `Blanc.Lift.checkNode_call_at_delegatecall` (`Blanc/Lift/DelegatecallControl.lean:16`) | Control / certificate | the byte at the node is `0xf4` | `DELEGATECALL` keeps the caller and the storage owner, so a certificate cannot pass it off as `CALL` |
| The proxy certificate with `CALL` claimed at the proxy's `DELEGATECALL` site (byte 1,680) fails `Cert.check` | `Blanc.Lift.Usdc.Proxy.proxy_cert_call_mutant_rejected` (`Blanc/Lift/Usdc/Proxy/Control.lean:24`) | Control / certificate | none | Kernel evaluation on the lifted proxy bytes |
| A frame running the proxy code from pc 0 whose caller is not the admin word: every external instruction it executes is `DELEGATECALL`; every child runs at the proxy with the implementation address `I` the slot names as code address, the frame's caller, value, calldata and static flag, and `I`'s code; on success the frame's output and world are a child's | `Blanc.Lift.Usdc.proxy_forwards` (`Blanc/Lift/Usdc/ProxyOk.lean:275`) | Frame / safety | CODE; covered fork; the implementation slot holds `I`; caller not the admin word; `I` carries no EIP-7702 designator and is no precompile; calldata below 2^256 bytes | `CALLDATASIZE` pushes the length modulo 2^256, hence the calldata bound |
| With the slot naming `J ≠ I`, no child runs with code address `I` | `Blanc.Lift.Usdc.proxy_forwards_control` (`Blanc/Lift/Usdc/ProxyForward.lean:123`) | Control / frame | as `proxy_forwards`, for `J` | The slot premise is load-bearing |
| A frame running the proxy code whose caller is the admin word: every external instruction is `CALL`, every child runs at the proxy with the proxy as caller, and a selector other than upgradeTo, upgradeToAndCall and changeAdmin spawns no child and leaves the proxy's storage unchanged | `Blanc.Lift.Usdc.proxy_admin_rule` (`Blanc/Lift/Usdc/ProxyForward.lean:224`) | Frame / safety | CODE; covered fork; caller is the admin word | The admin branch never reaches the implementation |
| The implementation's children are either library frames (at the same storage owner, with the frame's caller, value and static flag, running the library code) or frames whose caller is the storage owner, with value 0 | `Blanc.Lift.Usdc.impl_children` (`Blanc/Lift/Usdc/ImplSpawns.lean:298`) | Frame / safety | CODE; covered fork; the library code installed at its address | The second kind is rescueERC20's token call |
| The library's children are static, with the storage owner as caller, and a successful library frame leaves its storage owner's storage unchanged | `Blanc.Lift.Usdc.lib_children` (`Blanc/Lift/Usdc/LibSpawns.lean:30`) | Frame / safety | CODE; covered fork | The ERC-1271 isValidSignature call and the `ecrecover` call |

**USDC's model, its history and the signature laws**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| USDC's pure book (its ledger model read through the implementation's own decoder) satisfies the signature variant of the token laws, `BookLawsS`: as `BookLaws` (the shared vocabulary above), except that a step may also lower a holder's balance, or raise its allowances, by a message the holder signed | `Blanc.Lift.Usdc.usdcBook_lawsS` (`Blanc/Lift/Usdc/Book.lean:140`), the book `Blanc.Lift.Usdc.usdcBookS` (`Blanc/Lift/Usdc/Book.lean:48`) | Model / safety | none | The signer is the third authorizer |
| Under `NeverSigner T S tr p` (no settled non-static entry of `T` along the history has `p` as signer), `BookLawsS` gives the holder-indexed laws the composition consumes, for `p` | `Blanc.Lift.Token.BookLawsS.holderLaws` (`Blanc/Lift/Token/Signed.lean:59`) | Model / bridge | `NeverSigner` | The never-signer premise is required for this holder-indexed bridge |
| Under `UsdcHist` (USDC's three runtimes and its implementation slot installed at the checkpoint, the governance premise, the footprint invariant at the checkpoint, HASH-T over the keys the history touches), at every settled position not `UsdcShadowed` the book run over the earlier entry frames at the proxy is the footprint ledger at that frame's entry | `Blanc.Lift.Usdc.usdc_history_replayAt` (`Blanc/Lift/Usdc/HistoryReplay.lean:320`) | History / replay | `UsdcHist` | Positional replay |
| Under `UsdcHist`, the implementation slot and the admin word are unchanged at every settled frame's entry and at the end | `Blanc.Lift.Usdc.usdc_history_slots` (`Blanc/Lift/Usdc/HistorySlots.lean:168`) | History / safety | `UsdcHist` | This is what the governance premise buys |
| Under `UsdcHist`, at the history's end USDC's three runtimes and its implementation slot are installed, the footprint invariant holds over the history's key universe, and the admin word is unchanged | `Blanc.Lift.Usdc.usdc_history_end` (`Blanc/Lift/Usdc/HistoryEndFoot.lean:21`) | History / invariant | `UsdcHist` | The footprint invariant is retained |
| USDC at any proxy address is an instance of the writer-shadowed token core `CoreW`: its `Hist` is `UsdcHist`, its booked ledger is the footprint ledger over the history's key universe, its shadowed positions are `UsdcShadowed`, its answerable holders are the history's tracked balance rows | `Blanc.Composition.UsdcToken.usdcCore` (`Blanc/Composition/UsdcToken.lean:225`) | History / instance | `UsdcHist` | `CoreW` is `Core` with shadowed positions excluded |
| USDC discharges the self-caller facet: no foreign caller is forwarded into USDC's own entry | `Blanc.Composition.UsdcToken.usdcSelfCaller` (`Blanc/Composition/UsdcToken.lean:243`) | History / instance | as `usdcCore` | From the three spawn theorems above |
| USDC's book decodes `transfer` and `balanceOf` calldata as the ERC-20 ABI does | `Blanc.Composition.UsdcToken.usdcBook_erc20Abi` (`Blanc/Composition/UsdcToken.lean:268`) | Model / ABI | none | |
| USDC's budgeted transfer facet: at a world holding USDC's runtimes with the footprint core over `U`, a fresh entry frame at the proxy whose keys lie in `U`, whose caller is not the admin word and whose `transfer` meets USDC's state conditions, runs to success through the proxy and the implementation at an exact cost, given a gas budget that covers the proxy's 63/64 cut | `Blanc.Composition.UsdcToken.usdcTransferLive` (`Blanc/Composition/UsdcTokenLive.lean:159`) | Frame / instance | INIT footprint core; HASH-T frame keys in `U`; ENV gas and state conditions | From the proxy-to-implementation exact walk of `transfer` |

**A retained trace-local premise**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| The trace-local quiet premise | `Blanc.Composition.UniswapV2PairUsdcWeth9.PairUsdcAllowQuiet` (`Blanc/Lift/Usdc/AllowanceQuiet.lean:14`) | History / premise | the history's touched keys | Every touched allowance row of the supplied holder reads zero at the checkpoint |

Its declaration is owned by USDC despite its historical namespace. It states a
premise, not a surviving Pair composition theorem.

**Statement controls**

| What it shows | Control | Altitude |
|---|---|---|
| The laws reject USDC models that debit without authority: a mutant whose `transferFrom` skips the allowance, and an implementation whose `transfer` debits a third party | `Blanc.Lift.Usdc.control_usdc_mutant_not_lawsS` (`Blanc/Lift/Usdc/ModelControls.lean:175`), `Blanc.Lift.Usdc.control_usdc_thirdParty_not_lawsS` (`Blanc/Lift/Usdc/ModelControls.lean:194`) | definitional |
| `NeverSigner` is needed: a toy book satisfies `BookLawsS`, and when the holder may sign, any other caller's message lowers the holder's balance with no allowance | `Blanc.Lift.Token.control_signer_breaks_holder` (`Blanc/Lift/Token/SignedControl.lean:28`) | definitional |

USDC's own finite checkpoint checker rejects a synthetic storage with a stray
word: `Blanc.Lift.Usdc.checkUsdc_rejects_stray` (`Blanc/Lift/Usdc/FiniteFootprint.lean:87`).
Its soundness theorem, `Blanc.Lift.Usdc.checkUsdc_sound` (`Blanc/Lift/Usdc/FiniteFootprint.lean:47`),
takes `checkUsdc P rows w = true` and yields the installed-code facts and footprint
invariant over the row keys. These are conditional checkpoint facts, not an
attestation of live state.

**Non-claims.** The closed single-block USDC instance; live USDC or pool-state
assurance; USDC versions other than FiatTokenV2_2 at the stated implementation
address; results at positions excluded by `UsdcShadowed`. No actual-coin Curve
flagship or full deployed DAI/USDC/USDT composition is established here.

## Artifacts

| Contract | Address | Runtime bytes | keccak256 codehash | Creation transaction | Block |
|---|---|---:|---|---|---:|
| USDC FiatTokenProxy | 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48 | 2,186 | 0xd80d4b7c890cb9d6a4893e6b52bc34b56b25335cb13716e0d1d31383e6b41505 | not recorded (runtime read at a finalized block, below) | not recorded |
| USDC FiatTokenV2_2 implementation | 0x43506849D7C04F9138D1A2050bbF3A0c054402dd | 23,464 | 0xcdfb7d322961af3acae7a8f7ee8b69c205b36f576cc5b077f170c7eb8ecbe3ea | not recorded (runtime read at a finalized block, below) | not recorded |
| USDC SignatureChecker library | 0x800C32EaA2a6c93cF4CB51794450ED77fBfbB172 | 1,741 | 0x76cfc2ce63b1f05cb58ae553090665c2aabf2e13cf8a0e6da755c096fc5295dd | not recorded (runtime read at a finalized block, below) | not recorded |

**The USDC rows.** The USDC proxy, implementation and library runtimes were read
by `eth_getCode` at finalized block 26,213,219 (block hash 0xa79841b4ef0d00bcd0b0c8dc6b405efd4ab1ac3182b1a9a4877f873673e24b6c)
and are equal byte for byte across six separately operated providers: Allnodes PublicNode,
dRPC, Bware BlastAPI, Tenderly, Nodies and bloXroute; no creation transaction of these
instances is recorded, and the lifted inputs are `scripts/lift/inputs/usdc-proxy-runtime.hex`,
`scripts/lift/inputs/usdc-impl-runtime.hex` and `scripts/lift/inputs/usdc-lib-runtime.hex`.
The proxy holds the implementation address in its implementation slot
0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3
(`keccak256("org.zeppelinos.proxy.implementation")`), agreed across all six providers.
The library address is linked into the implementation runtime at two
PUSH20 sites (bytes 18,390 and 20,105), each reaching a DELEGATECALL. No Solidity recompilation.

## Disclosures and limits

35. **USDC: the governance premise.** `UsdcGovernance`: no settled
    entry frame at USDC's proxy whose caller is the checkpoint's admin word calls
    upgradeTo, upgradeToAndCall or changeAdmin. It names an actor and three entry
    points, not an outcome; from it the implementation slot and the admin word are
    proved unchanged along the history. Every Section 5.10 history row takes it.

36. **USDC: the never-signer premise.** The holder-indexed bridge from
    `BookLawsS` takes `NeverSigner`; it is not established here for an arbitrary
    holder. The retained signer control shows why that premise is load-bearing.

37. **USDC: excluded positions.** The positional replay is stated only at
    settled positions that are not `UsdcShadowed`: a frame at the proxy that is not an
    entry frame (an implementation or library frame running over the proxy's storage,
    static or not), and a position inside the block of an earlier library frame at the
    proxy (the ERC-1271 and `ecrecover` static calls a signed message makes, at which
    part of its effect, such as `permit`'s nonce increment, may already be written).
    Settled frame values need not be unique, so the exclusion is by position.

38. **USDC: liveness premises.** The transfer facet takes the footprint core,
    HASH-T for the frame's keys, a caller distinct from the admin word, USDC's
    transfer state conditions and a budget covering the proxy's 63/64 cut. It is
    a frame-level statement under these premises, not a closed single-block instance.

39. **USDC: the key universe.** USDC's history key
    universe is the checkpoint's tracked keys extended by the keys every frame at the
    proxy may touch, read from its calldata and caller, whether or not the frame
    commits; HASH-T is stated over that universe. In the general statements the
    checkpoint's tracked set is any predicate; a checkpoint the checker accepts tracks
    exactly its finite rows.

40. **USDC: not claimed.** Anything about the live state of USDC or of any pool;
    the closed single-block USDC instance, which is not built; USDC versions other
    than FiatTokenV2_2 at the stated implementation address; and anything at the
    excluded positions item 37 describes.

## Named premises and definitions

| Name | Declaration | Role |
|---|---|---|
| `UsdcGovernance` | `Blanc.Lift.Usdc.UsdcGovernance` (`Blanc/Lift/Usdc/Governance.lean:21`) | USDC's governance premise: no settled entry frame at the proxy from the admin word calls upgradeTo, upgradeToAndCall or changeAdmin |
| `UsdcShadowed` | `Blanc.Lift.Usdc.UsdcShadowed` (`Blanc/Lift/Usdc/HistoryReplay.lean:39`) | a non-entry frame at the proxy (implementation or library), or a position inside the block of an earlier library frame |
| `checkUsdc` | `Blanc.Lift.Usdc.checkUsdc` (`Blanc/Lift/Usdc/FiniteFootprint.lean:37`) | USDC's checkpoint checker on fetched rows: codes, implementation slot, layout and fixed words |
| `usdcBookS` | `Blanc.Lift.Usdc.usdcBookS` (`Blanc/Lift/Usdc/Book.lean:48`) | the pure book of USDC at a given proxy address |

## Uses of the shared API

### From `docs/COMMON_API.md`: E1. I need to construct a source or compiled execution term

A concrete source-fragment consumer is `ProxyCreation.isContract_runExact`
  in [`Blanc/Lift/Usdc/ProxyCreation/CodeSize.lean`](../../Blanc/Lift/Usdc/ProxyCreation/CodeSize.lean):
  the registered constructor entry returns the actual B256 code-size predicate
  at the flat charge plus 47 gas. This is an exact compiled source walk;
  actual bytecode entry/return and whole-constructor execution remain separate.

### From `docs/COMMON_API.md`: E2. The walk crosses a child frame

Worked uses: `Blanc/Lift/QuietDelegateSkip.lean`,
  `Blanc/Lift/Usdc/ProxyForward.lean`, `Blanc/Lift/Usdc/ImplSpawns.lean`.

The raw USDC proxy consumer
  [`Blanc/Lift/Usdc/ProxyRawCallers.lean`](../../Blanc/Lift/Usdc/ProxyRawCallers.lean)
  proves `Proxy.proxy_rawChild_inheritsH` and `proxy_rawChild_caller_selectorH`:
  a child called by an address apart from the proxy target must inherit the
  proxy caller through DELEGATECALL.

### From `docs/COMMON_API.md`: E3. I must carry a predicate over all entered child roots

Worked uses: USDC
(`Blanc/Lift/Usdc/HistorySlots.lean`, `HistoryFamily.lean`).

Worked use: `Blanc/Lift/Usdc/HistorySlotsCore.lean`.

### From `docs/COMMON_API.md`: S7. I need a token-ledger conservation invariant

Worked use: USDC's footprint
(`Blanc/Lift/Usdc/Footprint.lean`).

For old USDC blacklist writes, use `HistoricalMappingKey` in
[`Blanc/Lift/Usdc/HistoricalMappingKeys.lean`](../../Blanc/Lift/Usdc/HistoricalMappingKeys.lean).
It embeds modern keys unchanged and adds the historical mapping at slot 3.
[`Blanc/Lift/Usdc/V1MappingTouches.lean`](../../Blanc/Lift/Usdc/V1MappingTouches.lean)'s
`actualV1OldBlacklistKeys` collects actual successful writes from the same
history, retaining order and duplicates. Its soundness theorem derives their
slot identities from the checked V1 write sites. The off-implementation-slot
consumer requires initial apartness and freshness of this exact list; modern
balance-slot freshness does not establish historical blacklist freshness.
`ConfiguredHistoryTraceIn.actualV1OldBlacklistKeys_hash` additionally retains
the original frame, actual successful base-3 hash, its exact 64-byte
calldata-account/base input, and its successful edge before the same store.
`V1BlacklistReach.successfulSstore_hash` supplies this witness by following
both original selectors through the blacklister guard and packed Boolean
update; no final-call success or hash-injectivity premise is needed. The
existing key-only interfaces project this stronger source proof.

`ConfiguredHistoryTraceIn.v1_write_ne_implSlot` in
[`V1WriteApart.lean`](../../Blanc/Lift/Usdc/V1WriteApart.lean) closes every family,
including transferFrom. `V1MappingFreshKeys` bundles freshness of the seven
exact actual mapping collectors; initial apartness remains explicit.
The earlier `v1_write_ne_implSlot_or_transferFrom` interface is retained.
[`V1RetainedContext.lean`](../../Blanc/Lift/Usdc/V1RetainedContext.lean)'s
`settledRoot_v1_write_ne_implSlot` derives the retained-root premise from
same-history raw membership. `settledRoot_proxyV1_context_of_freshKeys`
then supplies the coupled retained code/slot context, and
`settledRoot_proxyV1_preserves_of_freshKeys` preserves both deletion exclusion
and the exact implementation word at settlement. These consumers retain the
actual root-entry Proxy/V1 code, implementation address, absent retained upgrade
log and initial NoDel premises; they do not yet propagate those entry facts
between successive roots or authenticate a historical creation cut.
`settledRoot_proxyV1_implSlot_eq_of_freshKeys` exposes the cell conclusion
without an incoming NoDel premise. In
[`V1TransactionContinuity.lean`](../../Blanc/Lift/Usdc/V1TransactionContinuity.lean),
`v1_transaction_preserves_retained` and `v1_transactions_preserve_retained`
derive both installed entry codes and the implementation word through the
actual ordered transaction sequence, without created-account exclusions for
either account. The actual retained Proxy/V1 classifier supplies proxy terminal
safety; V1's checked installed certificate supplies implementation safety.
Initial code/slot, exact-list freshness, same-history root inclusion and absent
retained upgrade logs remain explicit. The older `v1_transaction_preserves`
and `v1_transactions_preserve` statements retain their extra exclusions and
project these stronger results; historical creation binding is still separate.
[`V1HistoryContinuity.lean`](../../Blanc/Lift/Usdc/V1HistoryContinuity.lean)'s
`v1_block_preserves` and `v1_history_preserves` extend this to actual block
settlement and configured segments whose rule bits disable system stages.
Withdrawals, rewards and finalization use the existing shared cell transport.
Every retained root's entry control is derived from the segment's initial
control.

For genuine transaction boundaries,
[`V1MidHistoryContinuity.lean`](../../Blanc/Lift/Usdc/V1MidHistoryContinuity.lean)'s
`v1_tail_preserves` begins at the original `TxSplit.afterBenv`, including a
proxy created by that selected transaction. `v1_mid_preserves` appends actual
later blocks; `v1_before_txSplit_preserves` stops at the original before-trace.
`v1_between_txSplits_preserves` composes these into the exact after-C/before-D
interval, deriving deletion exclusions and every intervening root's entry
control from the initial state. Its conditions exclude the final selected
transaction and its suffix. In
[`V1MainnetContinuity.lean`](../../Blanc/Lift/Usdc/V1MainnetContinuity.lean),
`v1_between_txSplits_preserves_mainnet` derives all stage bits from the final
block's actual pre-Cancun timestamp, mainnet selection and accepted-header
chronology. Historical-domain capabilities and absent state gas/BAL are supplied
by their existing theorems. Historical C/D identities, constructor state, the
endpoint timestamp and receipt evidence for absent upgrade logs still require
their own binding. [`V1ReceiptContinuity.lean`](../../Blanc/Lift/Usdc/V1ReceiptContinuity.lean)'s
`v1_between_txSplits_preserves_from_receipts` consumes absence of proxy Upgraded
logs from the actual first-block suffix, every actual intermediate receipt, and
the last-block prefix. It derives the retained-root absence needed for the same
V1 continuity conclusion, with no separate per-root absence premise. The first
and last selected transactions stay outside the scan; historical identities,
constructor state and factual receipt-log absence are still caller obligations.
`V1RetainedAllowanceZero`'s `settledRoot_v1_allowanceWrite_nonInc` and
`settledRoot_v1_allowance_zero` reuse the retained Proxy/V1 context to classify
actual stores and preserve a tracked zero row. They require no code restriction
on discarded execution. V1's only caller exception is approve; initializer
stores consume the existing calldata-key separation proof. In
`V1ReceiptAllowanceZero`, `v1_allowance_zero_between_txSplits_from_receipts`
composes these laws with the exact-cut cell fold, deriving zero at the later
before-state from zero at the original after-state. Receipt absence supplies
all root code/slot and deletion facts.

For the original USDC boundary bloom literals, use
[`Blanc/Lift/Usdc/HistoricalBloomExclusion.lean`](../../Blanc/Lift/Usdc/HistoricalBloomExclusion.lean).
The checked literals exclude USDC logs in both boundary blocks only when an
application identifies them with the blooms supplied by its original execution.
Intermediate blocks and actual historical header authentication remain separate
obligations; these conditional literal identities are not historical adoption.

For V1 `approve`, use
[`Blanc/Lift/Usdc/V1ApproveMappingTouches.lean`](../../Blanc/Lift/Usdc/V1ApproveMappingTouches.lean)'s
`actualV1ApproveKeys`. It collects the allowance key of each actual successful
store at the requested target with exact V1 code and the approve selector,
preserving history order and duplicates. The checked V1 site fixes the caller
and calldata spender; the recognizer does not test equality with the written
key. Its separation consumer requires initial apartness and freshness of this
same list. `ConfiguredHistoryTraceIn.actualV1ApproveKeys_hashes` additionally
retains the original frame prefix and both successful nested-mapping hashes,
with exact caller/base-10 and spender/inner-digest inputs before the store.
Its producer in [`Blanc/Lift/Usdc/V1ApproveReach.lean`](../../Blanc/Lift/Usdc/V1ApproveReach.lean)
walks the checked dispatcher, guards and body; no final call success or hash
injectivity is assumed. The hash PCs are the actual witnessed PCs, not a
separate fixed-PC classification. Both collectors share `v1_store_site` and
`v1Mapping_site_iff`; selectors with multiple mapping sites still require
finer source attribution.

For V2 `approve`, use
[`Blanc/Lift/Usdc/V2ApproveMappingTouches.lean`](../../Blanc/Lift/Usdc/V2ApproveMappingTouches.lean)'s
`actualV2ApproveKeys`. Soundness and completeness cover every successful
selected approve store in the original history's `rawNodes`, retaining order
and duplicates. The recognizer tests target, exact code, selector and store
success. [`Blanc/Lift/Usdc/V2ApproveReach.lean`](../../Blanc/Lift/Usdc/V2ApproveReach.lean)'s
`successfulSstore_ordered_hashes` derives its caller/spender nested slot10 key
and the shared `KeccakPairBefore` witnesses from the same original frame
prefix, without final-frame success, descriptor separation or hash injectivity.
The off-implementation-slot consumer keeps initial apartness and freshness of
this exact collected list explicit.

For `approve`, `increaseAllowance` and `decreaseAllowance` in all three modern
runtimes, use
[`Blanc/Lift/Usdc/ModernCallerMappingTouches.lean`](../../Blanc/Lift/Usdc/ModernCallerMappingTouches.lean).
`ModernVersion` selects the exact existing code, certificate, annotations and
selector table. `modernCaller_store_key` obtains the caller/calldata-spender
slot-10 key from the certified site of the original successful store.
`actualModernCallerKeys` filters the original `rawNodes` by target, exact code,
caller selector and successful store, preserving order and duplicates. Its
soundness/completeness theorems retain the actual root and store; recognition
does not compare the written key. Under `checkFaithfulOn` for the exact
observed Pair/spender list and this collected list, `modernCaller_write_source`
derives the Pair caller and exact spender, and `modernCaller_write_allowed`
supplies the existing `AllowedFrame` caller arm. Check truth remains an
explicit premise. For successful hash-occurrence provenance, use
[`ModernCallerReach`](../../Blanc/Lift/Usdc/ModernCallerReach.lean) and its
[`ModernCallerHashBodies`](../../Blanc/Lift/Usdc/ModernCallerHashBodies.lean)
inner-path lemmas. `successfulSstore_ordered_hashes` follows the original
dispatcher, ABI decoder and guards in every version/method combination. It
produces `KeccakPairBefore` for caller/base-10 followed by masked-spender/inner
digest before the same successful store. The history adapters
`modernCallerKey?_ordered_hashes` and `actualModernCallerKeys_ordered_hashes`
retain the original root, node, written key and both successful hashes for
the unchanged collector. The existing V2 approve witness is preserved.
Other modern selectors and the full classifier remain outside this family.

For V2.1 owner writes, use
[`V2_1PermitReach`](../../Blanc/Lift/Usdc/V2_1PermitReach.lean)'s
`successfulSstore_source`: it reuses the original pre-nonce prefix and separates
the nonce increment at pc `0x41ae` from the approval setter. Both alternatives
retain actual successful hash occurrences; the allowance pair is ordered.
`ModernCallerReach.approval_core_source` generalizes the existing setter proof
to its actual owner argument across all three modern versions while preserving
`approve_core_hashes` as its caller specialization. The permit recovery helper
must return on the observed path; no signature-success or final-frame-success
premise is introduced.
[`V2_1PermitMappingTouches`](../../Blanc/Lift/Usdc/V2_1PermitMappingTouches.lean)'s
`actualV2_1PermitKeys` selects exactly successful stores by target, code and
selector, then uses the actual pc to choose nonce or allowance arguments.
It preserves raw order and duplicates and never compares hash values in
recognition. Soundness retains the original root and hash provenance;
finite `checkFaithfulOn` identifies the Pair owner and exact spender and
supplies the existing `AllowedFrame` owner arm. Fork-domain neutrality
is discharged by `HistFork.neutral` on the historical domain.
[`V2_1AllowanceWriteLocality`](../../Blanc/Lift/Usdc/V2_1AllowanceWriteLocality.lean)
combines that exact population with the covered modern population.
`v2_1_allowance_write_locality` leaves only existing allowed frames or actual
nonincrease, with no owner-selector residual for V2.1. Finite-check truth,
initializer exclusion, retained owner-query exclusion and historical binding
remain obligations; V2/V2.2 owner classification is separate.

For V2's four owner routes, use
[`V2PermitReach`](../../Blanc/Lift/Usdc/V2PermitReach.lean) and
[`V2OwnerAuthorizationReach`](../../Blanc/Lift/Usdc/V2OwnerAuthorizationReach.lean).
Their `successfulSstore_source` laws follow the original pc-zero dispatcher,
ABI, guards and actual returning helpers, including frames that later revert.
Permit separates nonce pc `0x47fd` from the allowance setter; the three
approval/increase/decrease authorizations separate flag pc `0x4eb8` from
that setter. Every selected store retains its actual hash inputs, with
ordered pairs for authorization and allowance rows.
[`V2AllowanceSetterReach`](../../Blanc/Lift/Usdc/V2AllowanceSetterReach.lean)
transports the actual owner/spender through returning addition/subtraction
helpers and reuses the shared approval setter; it does not infer arguments
from hash values or assume a signature result.
[`V2PermitMappingTouches`](../../Blanc/Lift/Usdc/V2PermitMappingTouches.lean) and
[`V2OwnerAuthorizationMappingTouches`](../../Blanc/Lift/Usdc/V2OwnerAuthorizationMappingTouches.lean)
collect exactly the corresponding original successful-store keys, preserving
raw order and duplicates. Recognition uses target, code, selector and pc;
finite faithful-key separation identifies the protected owner and spender.
[`V2AllowanceWriteLocality`](../../Blanc/Lift/Usdc/V2AllowanceWriteLocality.lean)'s
`v2_allowance_write_locality` combines these with the covered modern keys and
concludes the existing `AllowedFrame` or actual same-node nonincrease, with
no V2 owner-selector residual. Finite-check truth, retained owner exclusion
and historical binding remain explicit obligations; V2.2 permit coverage
is separate.

For exhaustive modern successful-store coverage, use
[`ModernWriteFamilies`](../../Blanc/Lift/Usdc/ModernWriteFamilies.lean).
`modern_store_fixed_nonInc_or_family` applies the unchanged certified root
tables to the actual store: its key is a listed literal slot, its value is
non-increasing at that same node, or its original selector is in a listed
version-specific family. `actualModernCoveredKeys` concatenates the actual V2 transfer keys, increasing
older-transferFrom credits, exact configure/mint family, cancellation and caller
collectors and the applicable blacklist collector: old base-3 keys for V2/V2_1 and packed balance keys for V2_2;
soundness retains the original root, node, successful store, owner and key.
Under finite faithfulness for that exact list and apartness from
`modernFixedWriteSlots`, `modern_allowance_write_reduction` eliminates fixed,
cancellation, blacklist and established configure/mint aliases and attributes caller writes,
leaving existing allowed exceptions, actual nonincrease or owner selectors.
The covered list also includes both inherited initializers and all seven
authorization-transfer collectors across V2, V2.1 and V2.2. Their original-store
coverage removes the residual mapping-writer alternative entirely. Owner
classification, finite check truth and historical input binding remain open.
Both V2_2 packed-blacklist selectors are discharged;
`initializeV2_1` is not promoted to an allowed exception.

For `cancelAuthorization` in all three modern versions, including both V2_2
overloads, use
[`ModernCancelMappingTouches`](../../Blanc/Lift/Usdc/ModernCancelMappingTouches.lean).
`modernCancel_store_key` obtains the authorization-state key at base slot 16
from the original successful store: masked calldata owner at word 4 and the
full nonce at word 36. `actualModernCancelKeys` filters original `rawNodes`
by target, exact runtime, cancellation selector and successful store, without
testing the written key. Completeness and soundness retain the original root,
node and actual write. `modernCancel_write_ne_allowSlot` consumes finite
faithfulness for exactly this list; its key constructors distinguish an
authorization entry from an allowance entry. Cancellation selectors are now
discharged by the exhaustive family reduction. Finite-check truth remains
an explicit obligation.

[`ModernCancelReach`](../../Blanc/Lift/Usdc/ModernCancelReach.lean) supplies the
original ordered successful hashes for all four cancellation routes.
`successfulSstore_ordered_hashes` follows the original entry, dispatcher,
ABI decoding and pause guard into the unused-authorization check. The first
hash consumes the masked calldata owner with base slot 16; the second consumes
the full calldata nonce with that first result. Both occur before the same
successful store, with no final-frame-success or signature-result premise.
The history adapters `modernCancelKey?_ordered_hashes` and
`actualModernCancelKeys_ordered_hashes` retain the original root, raw node,
write owner and exact key from the unchanged collector. This proves occurrence
and order within that prefix, without assuming hash injectivity or changing
the finite population.

[`ModernRemoveMinterReach`](../../Blanc/Lift/Usdc/ModernRemoveMinterReach.lean)
proves `successfulSstore_nonInc` for every actual removeMinter store in
V2, V2_1 and V2_2. The original dispatcher, ABI bounds and master-minter
guard lead to a masked same-key reload or a literal-zero store. Each value
is bounded by that same node's current cell, including when earlier writes
alias it. `modernRemoveMinter_nonInc` supplies the raw-history adapter.
`modern_allowance_write_reduction` in `ModernWriteFamilies` consumes this result
directly, removing selector 0x3092afd5 from the unresolved families without
adding hash-separation premises or changing the actual-key population.

For the balance-writing suffixes of modern burn, use
[`ModernBurnStores`](../../Blanc/Lift/Usdc/ModernBurnStores.lean).
`caller_key_hash` covers V2 and V2_1's final caller-balance writer;
`packed_setBalance_key_hash` covers V2_2's shared setBalance helper,
including its cap, blacklist query and original internal return.
Each retains the actual base-9 key and successful `ObservedKeccak` before
that store under the original edge observation, without final-frame success
or hash-separation premises. These are suffix producers; they do not alone
establish an original-entry or history theorem. The complete nonincrease route
below avoids needing a separate burn key collector.

For complete original-entry V2_2 burn nonincrease, use
[`V22BurnNonIncBodies`](../../Blanc/Lift/Usdc/V22BurnNonIncBodies.lean) and
[`V22BurnNonIncReach`](../../Blanc/Lift/Usdc/V22BurnNonIncReach.lean).
`successfulSstore_nonInc` follows the original dispatcher, ABI and role checks,
actual balance/supply reads and checked subtractions. Each actual write is
bounded by its own node's pre-state word. If the supply slot and balance hash
coincide, the masked balance bound and monotone subtraction still discharge
the second store after the first. No key-separation or final-frame-success
premise is needed. `ConfiguredHistoryTraceIn.v22Burn_nonInc` supplies the
raw-history adapter.

For V2 and V2_1, use
[`OldBurnNonIncCallees`](../../Blanc/Lift/Usdc/OldBurnNonIncCallees.lean) and
[`OldBurnNonIncBodies`](../../Blanc/Lift/Usdc/OldBurnNonIncBodies.lean).
The actual returning subtraction helpers preserve the storage base while
changing scratch memory, and their guards prove the nonwrapping bound.
The caller-balance read and exact first-store effect discharge both
same-node bounds, including when its hash equals the supply slot.
[`ModernBurnNonIncReach`](../../Blanc/Lift/Usdc/ModernBurnNonIncReach.lean)
combines all three original dispatchers and body proofs in
`successfulSstore_nonInc`. `ConfiguredHistoryTraceIn.modernBurn_nonInc`
connects this to actual raw-history nodes. The full
`modern_allowance_write_reduction` consumes this theorem directly, removing
burn from every modern residual selector list without a new collector,
hash-separation premise or change to the finite actual-key populations.
No final-frame-success or additional covered-fork premise is introduced.

For V2_2 packed-blacklist updates, use
[`V22BlacklistReach`](../../Blanc/Lift/Usdc/V22BlacklistReach.lean) and
[`V22BlacklistMappingTouches`](../../Blanc/Lift/Usdc/V22BlacklistMappingTouches.lean).
`successfulSstore_key_hash` follows the original dispatcher, public ABI,
blacklister guard and both flag-update branches to the shared packed-word
store. It proves the actual written key is the masked calldata address's
base-9 balance slot and retains a successful `KeccakBefore` in that same
original prefix, with no final-frame-success or hash-separation premise.
`actualV22BlacklistKeys` collects one logical balance key per original
matching successful store, preserving order and duplicates without testing
the written digest. Its soundness carries the original root, node, owner,
exact key and hash; completeness covers both selectors. Finite faithfulness
for that exact population lets `v22Blacklist_write_ne_allowSlot` exclude
these writes from protected allowance rows. The full modern family
reduction consumes this collector alongside the unchanged older collectors.

For V2 and V2_1 old-blacklist writes, use
[`Blanc/Lift/Usdc/V2BlacklistMappingTouches.lean`](../../Blanc/Lift/Usdc/V2BlacklistMappingTouches.lean)'s
`actualV2OldBlacklistKeys` with its explicit version. The certificate and
same original prefix derive the masked calldata address at slot 3. The
collector selects actual successful blacklist/unblacklist stores, preserving
raw-node order and duplicates, with soundness and completeness.
`v2OldBlacklist_write_ne_allowSlot` consumes the exact finite
observed-versus-collected-key check; its truth remains an explicit obligation.
For successful hash provenance, import
[`Blanc/Lift/Usdc/V2BlacklistReach.lean`](../../Blanc/Lift/Usdc/V2BlacklistReach.lean).
Its `successfulSstore_hash` follows the original dispatcher, ABI wrapper, role
guard and memory writes in either version. The exact masked address/base-3
input is hashed successfully before the same store. The history adapters
`v2OldBlacklistKey?_hash` and `actualV2OldBlacklistKeys_hash` retain that
original root, prefix, actual store and key equality for the unchanged
collector. Final-frame success, hash injectivity and finite-check truth are
not required to obtain these witnesses. Initializer writes are outside this
two-selector collector.

[`OldTransferBodyReach`](../../Blanc/Lift/Usdc/OldTransferBodyReach.lean)
owns the shared V2/V2.1 balance-transfer walk. `body_reach_bounded` retains
the owner store's actual subtraction bound or the recipient store, together
with each branch's own original hash. `recipient_v21` checks equality of the
complete recipient suffix; the owner/debit walks use their exact version's
return addresses and helper indices. The V2 interfaces in `V2TransferReach`
remain specializations of this shared proof.

[`OldTransferFromCallee`](../../Blanc/Lift/Usdc/OldTransferFromCallee.lean)
uses that walk with an arbitrary original caller continuation in V2 or V2.1.
`body_bounded_source_or_return` retains the balance-store evidence or a return
along the same observed path. `subtraction_return` derives the actual bound
and unchanged storage base while retaining both observed cuts. Neither
requires an assumed bound or a store-free caller. The V2 interfaces in
[`V2TransferFromCallee`](../../Blanc/Lift/Usdc/V2TransferFromCallee.lean)
remain specializations. V2.2 is explicitly excluded from these older-version
theorems.

[`V22TransferFromCallee`](../../Blanc/Lift/Usdc/V22TransferFromCallee.lean)
uses the same observed split for the V2.2 balance body: either an original
balance store carries its own successful mapping hash and setter return tag,
or the actual callee returns into the original caller with both path segments.
Its subtraction return retains storage and the checked arithmetic bound.
[`V22TransferFromEntry`](../../Blanc/Lift/Usdc/V22TransferFromEntry.lean)
follows the original dispatcher, ABI wrapper and public guards into that body
with the exact saved caller stack. Neither result assumes eventual frame
success or hash separation.
[`V22TransferFromAllowance`](../../Blanc/Lift/Usdc/V22TransferFromAllowance.lean)
checks the complete final writer equal to the shared older allowance suffix,
then derives nonincrease from the actual post-balance reload and subtraction.
[`V22TransferFromContinuation`](../../Blanc/Lift/Usdc/V22TransferFromContinuation.lean)
recovers the original caller stack from the checked body return and classifies
every original successful store as a same-node nonincrease or one of the two
balance setters with its own successful hash.
[`V22TransferFromMappingTouches`](../../Blanc/Lift/Usdc/V22TransferFromMappingTouches.lean)
collects only actual strict increases, using the actual setter return tags to
distinguish owner and recipient. `actualV22TransferFromKeys_sound` retains the
original store, root and earlier successful hash; the complement is already
non-increasing. No comparison between a written key and a proposed digest
selects a source. `actualModernTransferFromKeys` combines these exact populations
by version, and the modern-family reduction now handles every transferFrom case.

The V2.1 signed-transfer and receive-authorization collectors in
[`V2_1TransferWithAuthorizationMappingTouches`](../../Blanc/Lift/Usdc/V2_1TransferWithAuthorizationMappingTouches.lean)
and [`V2_1ReceiveWithAuthorizationMappingTouches`](../../Blanc/Lift/Usdc/V2_1ReceiveWithAuthorizationMappingTouches.lean)
derive all three reached stores from the original entry and the actual validity
and recovery helper returns. The receive route retains its caller guard.
The authorization flag has its ordered owner/base-16 and nonce/inner hash pair;
each balance store has its original account/base-9 hash. Recognition tests the
actual target, code, selector, store pc and successful store, never a digest.
Their `actual...Keys_sound` and `actual...Keys_complete` theorems retain raw
occurrences, including repeated keys. Finite separation truth and historical
input binding remain separate obligations.
The matching V2 collector is
[`V2TransferWithAuthorizationMappingTouches`](../../Blanc/Lift/Usdc/V2TransferWithAuthorizationMappingTouches.lean).
V2.2 uses
[`V22TransferWithAuthorizationMappingTouches`](../../Blanc/Lift/Usdc/V22TransferWithAuthorizationMappingTouches.lean),
[`V22ReceiveWithAuthorizationMappingTouches`](../../Blanc/Lift/Usdc/V22ReceiveWithAuthorizationMappingTouches.lean),
[`V22TransferWithAuthorizationBytesMappingTouches`](../../Blanc/Lift/Usdc/V22TransferWithAuthorizationBytesMappingTouches.lean)
and [`V22ReceiveWithAuthorizationBytesMappingTouches`](../../Blanc/Lift/Usdc/V22ReceiveWithAuthorizationBytesMappingTouches.lean).
Its authorization flag is identified by actual pc5060, and its balance stores
by actual setter-return tags40e8/40f9. Source proofs preserve static-signature
packing or dynamic ABI decoding and the receive caller guard before the same
observed helper returns. No selector collector compares a written key with a
proposed hash. `actualModernAuthorizationKeys` selects these exact populations
by version; their soundness and completeness close every authorization arm in
`modern_allowance_write_reduction` under its existing finite-check premises.

[`V21InitializerReach`](../../Blanc/Lift/Usdc/V21InitializerReach.lean) follows
inherited `initializeV2_1` through its original dispatcher and optional transfer,
recovers the checked returning stack and observes the target-blacklist hash.
Every store is at fixed slot18, a same-node nonincrease, or an actual recipient
balance/target blacklist write with its own successful hash.
[`V21InitializerMappingTouches`](../../Blanc/Lift/Usdc/V21InitializerMappingTouches.lean)
collects exactly nonliteral strict increases at these two actual store pcs.
It never selects an input by comparing a written key with a digest. Its original
history soundness and fixed/nonincrease/collected completeness feed
`actualModernInitializerKeys` and the modern-family allowance reduction. V2.1's
inherited initializer is thereby covered without a new `AllowedFrame` exception.

[`V22InitializerReach`](../../Blanc/Lift/Usdc/V22InitializerReach.lean) covers the
inherited initializer's original V2.2 entry, optional transfer return and packed
blacklist return. `V22BlacklistReach.store_source` retains the actual value,
flag and stack tail while `store_key_hash` preserves its existing interface.
The source proof distinguishes transfer tags from the blacklist flag and gives
the exact original address/base-9 hash before every nonliteral store.
[`V22InitializerMappingTouches`](../../Blanc/Lift/Usdc/V22InitializerMappingTouches.lean)
collects only actual nonfixed increases, with original-root/hash soundness and
store completeness. The modern family consumes this exact V2.2 population;
both inherited initializer variants are covered without an AllowedFrame exception.

[`OldTransferFromEntry`](../../Blanc/Lift/Usdc/OldTransferFromEntry.lean) derives
the original V2/V2.1 dispatcher, ABI and public-guard paths while retaining
the exact caller stack below the balance helper. The actual runtime trees,
helper indices and return tags are selected by version.
[`OldTransferFromAllowance`](../../Blanc/Lift/Usdc/OldTransferFromAllowance.lean)
proves the allowance continuation non-increasing at the same original store.
It reloads allowance after the balance helper and uses the actual checked
subtraction return, so the bound tolerates balance/allowance hash aliasing.
The complete final allowance tails are checked equal by `tail_v21`.
[`V2TransferFromEntry`](../../Blanc/Lift/Usdc/V2TransferFromEntry.lean) preserves
its existing interface by specializing the shared entry proof.

[`V2TransferFromContinuation`](../../Blanc/Lift/Usdc/V2TransferFromContinuation.lean)
and [`V2_1TransferFromContinuation`](../../Blanc/Lift/Usdc/V2_1TransferFromContinuation.lean)
use the checked frame return to recover the original caller stack.
Their `successfulSstore_credit_or_nonInc` excludes actual owner debits and
allowance writes, leaving only the recipient store and its own successful
hash. The exact recipient sites are `0x40e8` and `0x3d11`, respectively.
[`V2TransferFromCreditHashes`](../../Blanc/Lift/Usdc/V2TransferFromCreditHashes.lean)
and [`V2_1TransferFromCreditHashes`](../../Blanc/Lift/Usdc/V2_1TransferFromCreditHashes.lean)
connect each member of the unchanged `actualOldTransferFromCreditKeys` list
for its version to the actual increasing store and original successful
recipient hash occurrence in the same raw history. No digest comparison,
final-frame-success premise, hash injectivity or finite-population widening
is introduced.

For modern `transferFrom`, use
[`ModernTransferFromSites`](../../Blanc/Lift/Usdc/ModernTransferFromSites.lean)
to reuse the unchanged root certificates at the same original successful store.
`modernTransferFrom_store_nonInc_or_balance` derives nonincrease, the recipient
balance key, or (only in V2.2) the sender balance key. V2/V2.1 sender debits and
all three allowance writes already have certified nonincrease.
[`OldTransferFromMappingTouches`](../../Blanc/Lift/Usdc/OldTransferFromMappingTouches.lean)
collects only actual increasing V2/V2.1 writes by testing the actual pre-word
and written value, without comparing a key to a proposed digest. Soundness
identifies the exact recipient key at that original store; completeness proves
all omitted selected writes non-increasing. `ModernWriteFamilies` adds this
exact list to its finite faithful check and discharges the two older transferFrom
cases. V2.2 transferFrom remains explicit. The two credit-hash modules above
supply original successful hash occurrences for the old-version collector; certificate key
denotation alone does not provide them or prove finite-check truth.

All three modern transfer and mint producers are consumed by
[`ModernWriteFamilies`](../../Blanc/Lift/Usdc/ModernWriteFamilies.lean) and
[`ModernMinterFamilies`](../../Blanc/Lift/Usdc/ModernMinterFamilies.lean).
Their exact per-version actual lists extend `actualModernCoveredKeys`; supply
writes stay in the literal-word branch. The faithful check now removes ordinary
transfer and mint from every modern residual-selector list. It remains an
explicit check obligation, and authorization, initializer and V2.2 transferFrom
families remain separate. The received V2.1 transfer body and recipient
interfaces reuse `OldTransferBodyReach`, preserving the newer shared proof.

For the combined configure/mint family, use
[`ModernMinterFamilies`](../../Blanc/Lift/Usdc/ModernMinterFamilies.lean).
`actualModernMinterKeys` selects the version's actual configureMinter and mint keys. `modernMinter_write_source` derives either
literal supply slot 11 or a collected logical key distinct from every allowance
key. It assumes no hash separation. `ModernWriteFamilies` includes this exact
list in `actualModernCoveredKeys`; its existing finite faithful/apart checks
then eliminate configureMinter and mint in all three versions from the residual
families. No AllowedFrame exception,
spender population, or global hash-injectivity premise is added.

For V2 `configureMinter`, use
[`Blanc/Lift/Usdc/V2ConfigureMinterMappingTouches.lean`](../../Blanc/Lift/Usdc/V2ConfigureMinterMappingTouches.lean)'s
`actualV2ConfigureMinterKeys`. The collector preserves the original history's
order and duplicates. Its completeness theorem derives the reached store site
for every selected successful store; recognition never compares the written key
with a proposed hash. `V2ConfigureMinterReach.successfulSstore_source` derives
the minter flag at base 12 or allowance at base 13, retaining that store's own
successful original hash strictly before it. No final-frame success or hash
injectivity is required. Initial apartness and freshness of this exact list
remain explicit in the implementation-slot separation consumer.

V2.1 uses
[`Blanc/Lift/Usdc/V2_1ConfigureMinterMappingTouches.lean`](../../Blanc/Lift/Usdc/V2_1ConfigureMinterMappingTouches.lean)'s
`actualV2_1ConfigureMinterKeys` with the same exact-history guarantees.
`V2_1ConfigureMinterReach` proves its own dispatcher, ABI, guard and source-PC
coverage. It reuses `V2ConfigureMinterReach.body_reach_observed`, generalized
over the surrounding program, because the two concrete body trees are
definitionally equal. The existing V2 body walk and store-tail definitions
remain the single owners; each runtime has its own source-location proof.

V2.2 uses
[`Blanc/Lift/Usdc/V22ConfigureMinterMappingTouches.lean`](../../Blanc/Lift/Usdc/V22ConfigureMinterMappingTouches.lean)'s
`actualV22ConfigureMinterKeys` for the same exact-history interface.
`V22ConfigureMinterReach` proves the route and source locations in `Impl.code`,
then reuses the identical V2 body without another generalization. Each collected
row retains its own original successful hash before that actual store.

For V2 `mint`, use
[`Blanc/Lift/Usdc/V2MintMappingTouches.lean`](../../Blanc/Lift/Usdc/V2MintMappingTouches.lean)'s
`actualV2MintKeys`. The actual-store completeness theorem classifies the literal
total-supply write at slot 11 separately, deriving its exclusion from the
mapping collector. The recipient balance at base 9 and caller minter allowance
at base 13 retain their own successful original hashes before their stores.
`V2MintReach.successfulSstore_source` traverses the checked dispatcher, guards
and arithmetic returns; its subtraction bound comes from the actual earlier
mint guard. Recognition tests source PCs and actual store success, never a
proposed key digest. Order, duplicates and original history membership remain
explicit, as do initial apartness and freshness for slot separation.

For V2 `transfer`, use
[`Blanc/Lift/Usdc/V2TransferMappingTouches.lean`](../../Blanc/Lift/Usdc/V2TransferMappingTouches.lean)'s
`actualV2TransferKeys`. Original entry coverage derives the caller and recipient
base9 balance stores, each with its own earlier successful hash. The actual
balance guard supplies the subtraction bound through the unchanged storage
read; the source theorem adds no bound premise. The collector preserves raw-node
order and duplicates and derives source sites without testing proposed hashes.

For V2.1 mint, use
[`Blanc/Lift/Usdc/V2_1MintMappingTouches.lean`](../../Blanc/Lift/Usdc/V2_1MintMappingTouches.lean)'s
`actualV2_1MintKeys`. Original entry coverage derives supply at `0x1fd6`,
recipient balance at `0x202c`, and caller minter allowance at `0x204d`.
The mapping collector preserves raw-node order and duplicates, excludes the
literal supply store, and retains each mapping store's own successful earlier
hash in the same history. The arithmetic bound comes from the original mint
guard. `V2_1MintReach` follows its own ABI and arithmetic helper paths;
`V2MintReach.minter_store_reach_observed` shares only the identical final store
tail over an arbitrary surrounding program. `ObservedSourceFor` shares the
three-way classification with the version-specific balance tail as a parameter.
The existing V2 interface remains
available. Separation consumes freshness for exactly this collected list.

For V2.2 `mint`, use
[`Blanc/Lift/Usdc/V22MintMappingTouches.lean`](../../Blanc/Lift/Usdc/V22MintMappingTouches.lean)'s
`actualV22MintKeys`. The original-entry proof separates the literal supply write
at `0x21b8`, caller minter allowance at `0x21f5`, and recipient balance through
the guarded shared setter. Its retained immediate return excludes the first two
source sites, so the recognizer needs no separate exact balance PC or digest
comparison. Completeness covers every successful selected store and excludes
supply from the mapping list; history soundness retains each row's own original
successful hash. `V22TransferReach.StoreSource` now also retains that actual
terminal tree, with the existing public transfer producer unchanged. Mint reuses
its packed query, arithmetic and setter helpers and the identical V2 final
minter-store helper. Freshness and initial apartness remain explicit for exactly
the collected mapping list.

For V2.2 `transfer`, use
[`Blanc/Lift/Usdc/V22TransferMappingTouches.lean`](../../Blanc/Lift/Usdc/V22TransferMappingTouches.lean)'s
`actualV22TransferKeys`. Both writes use the same setter; the actual stack word
at index 2 distinguishes its caller-balance return tag `0x40e8` from its
recipient-balance return tag `0x40f9`. `V22TransferReach.successfulSstore_source`
derives those tags, the written account key and its own successful earlier hash
from original entry. Recognition checks target/code/selector, the retained tag
and successful store, without a digest comparison or separate PC requirement.
Completeness exhausts both tags, and history soundness binds the original frame,
store and hash. Packed-balance queries, arithmetic and setter guards are traversed
internally; no arithmetic or final-frame-success premise is added. Initial
apartness and freshness remain explicit for the exact collected list.

For V2.1 `transfer`, use
[`Blanc/Lift/Usdc/V2_1TransferMappingTouches.lean`](../../Blanc/Lift/Usdc/V2_1TransferMappingTouches.lean)'s
`actualV2_1TransferKeys`. Its original entry proof derives the caller's balance
store at `0x3cd2` and the recipient's at `0x3d11`, each with its own successful
hash earlier in the same frame. It reuses the V2 transfer source shapes and the
V2.1 mint arithmetic helpers; the actual balance guard supplies the debit bound.
The collector preserves original raw-node order and duplicates and establishes
completeness and same-history hash provenance without testing key digests.
Separation requires explicit initial apartness and freshness of this exact list.

For V1 `burn`, use
[`Blanc/Lift/Usdc/V1BurnMappingTouches.lean`](../../Blanc/Lift/Usdc/V1BurnMappingTouches.lean)'s
`actualV1BurnBalanceKeys`. The recognizer selects actual successful balance
stores at 0x1f27, preserving history order and duplicates without comparing
the digest. `V1BurnReach.successfulSstore_source` follows the checked selector,
guards and two subtraction returns, classifying the supply store at 0x1ed1
separately from the caller's base-9 balance write. The balance arm retains
the successful hash at 0x1f24 and its exact caller/base input before that store;
the earlier supply-store arm requires no later hash. The history soundness
and completeness theorems bind this exact collector, and implementation-slot
separation requires its explicit initial apartness and freshness. No final
call success or hash injectivity is assumed.

For V1 `mint`, use
[`Blanc/Lift/Usdc/V1MintMappingTouches.lean`](../../Blanc/Lift/Usdc/V1MintMappingTouches.lean)'s
`actualV1MintKeys`. Its two recognized source PCs select the calldata recipient's
base-9 balance row and the caller's base-13 minter-allowance row. The actual
prefix producer `V1MintReach.successfulSstore_source` separates the supply
write at 0x1bcc, balance write at 0x1c61 and allowance write at 0x1cb7; the
mapping arms retain the successful hash at 0x1c5e or 0x1cb4, respectively.
Each earlier write requires no later hash or final call success. The collector
preserves actual history order and duplicates, never compares the written digest,
and has same-history soundness, completeness and explicit exact-list freshness
consumers for implementation-slot separation.

For V1 ordinary transfers, use
[`Blanc/Lift/Usdc/V1TransferMappingTouches.lean`](../../Blanc/Lift/Usdc/V1TransferMappingTouches.lean)'s
`actualV1TransferKeys`. It selects both actual successful balance writes by
selector and source PC, preserving raw-history order and duplicates without
recognizing a digest. `V1TransferReach.successfulSstore_source` proves the
caller and calldata-recipient keys and each successful 64-byte hash on the
same original prefix, including early writes before a later failure.
`ConfiguredHistoryTraceIn.actualV1TransferKeys_sound` retains both occurrences,
their actual frame, and their prefix order; `mem_actualV1TransferKeys_of_site`
is complete for either site. `v1Transfer_write_ne_implSlot` uses freshness of
exactly that collected list and an explicitly separated initial footprint.

For V1 transferFrom, use
[`Blanc/Lift/Usdc/V1TransferFromMappingTouches.lean`](../../Blanc/Lift/Usdc/V1TransferFromMappingTouches.lean)'s
`actualV1TransferFromKeys`. Its exact `filterMap` recognizes target, code,
selector, source pc and successful SSTORE, never the written digest. It covers
the calldata owner's balance, recipient's balance and owner/caller allowance.
`V1TransferFromReach.successfulSstore_source` supplies each computed key and
successful own-prefix hash, plus the allowance's linked inner→outer→store
chronology. Its early balance-store alternatives need no later hash or call
success. `ConfiguredHistoryTraceIn.actualV1TransferFromKeys_sound` retains the
original frame, store and hash in the same history;
`v1TransferFrom_allowance_ordered_hashes` exposes both original nested hash
witnesses and their order. `mem_actualV1TransferFromKeys_of_successfulSstore`
collects every selected successful row, while
`v1TransferFrom_successfulSstore_ne_implSlot` derives separation directly from
initial apartness and freshness of exactly this producer list. No key
injectivity, final-state invariant or never-signer premise is inferred.

For the actual V1 transferFrom allowance value, use
[`Blanc/Lift/Usdc/V1TransferFromNonInc.lean`](../../Blanc/Lift/Usdc/V1TransferFromNonInc.lean)'s
`allowanceStore_nonInc`: at pc 0x14e2, a successful store writes no more than
that same node's current cell under the original raw `ParentPrefix`.
`successfulSstore_source` retains both balance-site alternatives and reuses the
existing mapping-key and ordered-hash witnesses, adding the bound only to the
allowance alternative. The proof follows the allowance reload after both
balance writes and the checked subtraction; it needs no row separation or
final-frame outcome. Its focused body walk is
[`Blanc/Lift/Usdc/V1TransferFromNonIncReach.lean`](../../Blanc/Lift/Usdc/V1TransferFromNonIncReach.lean).

For V1 `removeMinter` and `configureMinter`, use
[`Blanc/Lift/Usdc/V1MinterMappingTouches.lean`](../../Blanc/Lift/Usdc/V1MinterMappingTouches.lean)'s
`actualV1MinterKeys`. It recognizes each of the four successful store PCs
separately, preserving order and duplicates without testing the written digest.
`ConfiguredHistoryTraceIn.actualV1MinterKeys_sound` retains the original store
and its successful earlier hash, exact input, and membership in the same
history. The first store requires no later hash or final call success.
`mem_actualV1MinterKeys_of_site` collects every matching actual row;
`ConfiguredHistoryTraceIn.v1Minter_write_ne_implSlot` requires initial apartness
and freshness of exactly this list. It reuses the modern minter and minter
allowance keys without changing the modern collectors.

### From `docs/COMMON_API.md`: M1. The goal is a `sliceD` normalization

The concrete `Usdc.recoveryV2_1_consumes` specialization in
  [`Blanc/Lift/Usdc/RecoveryV2_1.lean`](../../Blanc/Lift/Usdc/RecoveryV2_1.lean)
  follows the actual checked V2_1 recovery entry to STATICCALL at PC `0x4a78`,
  derives its four-word input from the entry registers and memory writes,
  and connects the actual native invocation and nonzero canonical answer to
  the original checked caller's returned stack. Its entry, pointer,
  nondelegation and `NeutralFork` premises remain local producer
  obligations. It does not enumerate flag-zero invocations or establish
  complete historical permit coverage.

For a later actual SSTORE with arbitrary final frame outcome,
  `Usdc.permitV2_1_recovery_answer_toward_sstore` in
  [`Blanc/Lift/Usdc/PermitRowRecoveryV2_1.lean`](../../Blanc/Lift/Usdc/PermitRowRecoveryV2_1.lean)
  follows the real recovery return through the `0x471c` epilogue to the
  `0x421e` owner comparison, deriving that the native answer equals the saved
  owner. Its companion `permitV2_1_owner_comparison_toward_sstore` excludes
  the actual rejecting branch. Recovery-entry registers, pointer bounds,
  continuations and nondelegation remain local premises; root-to-entry
  coverage and pre-authentication nonce-slot separation are separate work.
  The actual original-frame producer is
  `Usdc.permitV2_1_root_recovery_toward_sstore` in
  [`Blanc/Lift/Usdc/PermitRowPrefixV2_1.lean`](../../Blanc/Lift/Usdc/PermitRowPrefixV2_1.lean).
  From the fresh PC-zero permit frame and an observed later SSTORE, it derives
  the actual recovery entry, original prefix, calldata-derived owner/signature
  words, pointer geometry and preservation of address-1 code. It assumes no
  successful final outcome. The target stack head and explicit inequality
  between its key and the calldata owner's nonce slot remain premises of this
  local producer; the history consumer must discharge finite separation.
  `Usdc.permitV2_1_tracked_sstore_native` in
  [`Blanc/Lift/Usdc/PermitRowNativeV2_1.lean`](../../Blanc/Lift/Usdc/PermitRowNativeV2_1.lean)
  discharges that inequality from the existing finite `RowSep.other` nonce site.

`RetainedOldOwnerNativeQuery` in
  [`Blanc/Lift/Usdc/RetainedOldRecovery.lean`](../../Blanc/Lift/Usdc/RetainedOldRecovery.lean)
  is the independent actual native-query carrier for globally retained old
  owner-route parents. It keeps the parent position, original occurrence,
  version/site, message and arbitrary child result; membership never tests the
  desired answer or a tracked write. `global_retention` derives the same node's
  retention under an actual settled root. `retained_old_owner_pair_query_at`
  reuses the successful old-owner producer for both V2 and V2_1, deriving fresh
  entry from history. `retained_old_owner_not_pair` applies exclusion only over
  that retained universe. The corresponding `_effective` variants carry the
  actual parent fork's `delegatedCodeAddress(code1) = none` readiness through
  both recovery specializations, `ownerV2_query_consumed_effective` and
  `permitV2_1_query_consumed_effective`, the shared old-owner backend and all
  three retained endpoints (`retained_old_owner_pair_query_at_effective`,
  `retained_old_owner_has_pair_query_effective`,
  `retained_old_owner_not_pair_effective`).
  Original pure-nondelegation APIs project to that same implementation; the
  independent query carrier is unchanged. Domain capabilities, BAL absence
  and actual routing readiness remain explicit producer obligations. This
  does not constrain discarded raw frames or finish the allowance-history fold.
  [`RetainedAllowanceWrites.lean`](../../Blanc/Lift/Usdc/RetainedAllowanceWrites.lean)
  connects an actual retained storage write under an original settled root to
  its globally retained parent. `usdc_retainedRowWrite_nonInc_or_v2_2_owner`
  reuses the raw writer classifier and transports its exception by same-frame
  `sevm` equality, then applies retained old-query exclusion and initializer
  separation. The actual caller producer and scoped old routing readiness
  remain inputs; the exact V2_2 owner case remains in the conclusion.
  `usdc_retainedRowWrite_nonInc` closes that case with a separate retained
  V2_2 owner producer. These are local write inequalities, not a storage fold
  or a proof of the endpoint zero seed.
  `usdc_rawRowWrite_of_nodeCode` factors the implementation classifier at one
  actual write; the original raw-code interface is a compatibility wrapper.
  `usdc_retainedRowWrite_nonInc_of_retainedCode` consumes that local code fact,
  preserving the original native-query population and retained parent witness.
  The `_of_rootCallers` variant restricts caller exclusion to committed frames
  of that actual root; native-query and old-owner evidence retain their original
  full-history scope. The original theorem is a compatibility wrapper.
  `settledRoot_allowanceWrite_nonInc_from_installations` derives the code fact
  from retained F2′ governance, the initially selected runtime, and installations
  at actual upgrade positions. It does not require the raw upgrade checker or
  all future runtimes installed at root entry. Modern row separation, the V1
  actual-write classifier, initializer separation, caller exclusion, R3/R4 and
  the separate V2_2 owner producer remain explicit.

`Usdc.recoveryV2_consumes` in
  [`Blanc/Lift/Usdc/RecoveryV2.lean`](../../Blanc/Lift/Usdc/RecoveryV2.lean)
  specializes the same engine at V2's actual `0x50a4` entry and `0x50ef` call.
  Its actual caller remains a producer obligation, including the `0x4d93`
  epilogue before any owner comparison.

The concrete fresh-entry producer in
  [`Blanc/Lift/Usdc/PermitQueryV2_1.lean`](../../Blanc/Lift/Usdc/PermitQueryV2_1.lean),
  `Usdc.permitV2_1_query_entry`, derives the recovery registers, pointer and
  actual continuations from PC zero, empty stack/memory and the permit selector
  on a successful checked V2_1 execution. Its digest uses the domain word
  after the actual nonce write, without a storage-separation premise.
  `Usdc.permitV2_1_query_consumed` connects that query's original native call
  slot and answer through the real `0x471c` return to the `0x421e` owner check,
  deriving the nonzero calldata-owner answer. Existing fork coverage and
  address-1 nondelegation remain local premises; proxy/history entry, other
  selectors and failed-call enumeration remain separate obligations.
  The V2 family in
  [`Blanc/Lift/Usdc/OwnerQueriesV2.lean`](../../Blanc/Lift/Usdc/OwnerQueriesV2.lean)
  derives all four registered owner-selector prefixes through
  `Usdc.ownerV2_source_prefix`; `ownerV2_source_prefix_of_owner_selector`
  uses the existing `selV2.owners` table, including signed decrease.
  Fresh successful execution yields the decoded arguments, pause/blacklist
  facts, exact scratch memory, state, pointer and actual continuations.
  Permit reaches the source tail after its nonce increment; the other three
  paths return from authorization validation with strict time bounds,
  unused authorization state and no storage write. `ownerV2_query_entry`
  derives the actual six- or seven-word struct hash, typed-data digest,
  signature-guard route, full registers and continuations at `0x50a4`.
  `ownerV2_query_consumed` uses existing owner-selector membership to connect
  the actual `0x50ef` native call, its original slot, paid gas and canonical
  nonzero answer through `0x4d93` and each real owner comparison. The answer
  is the calldata owner; the native message and return observations remain
  in the conclusion. Fork coverage and address-1 nondelegation are explicit
  local premises. Historical transport, complete retained-query relevance
  and failed-call enumeration remain separate obligations.

`Usdc.old_owner_query_nativeH` (on a `NeutralFork`; `old_owner_query_native` is its
  `CoveredFork` corollary) in
  [`Blanc/Lift/Usdc/OldRecoveryRelevance.lean`](../../Blanc/Lift/Usdc/OldRecoveryRelevance.lean)
  composes both version families at their original fresh execution root. It
  preserves the actual call node, recursive slot, step result and returned
  derivation through `CallOccurrenceStep.reRoot`, and derives the real
  `initEvm msg` ECRECOVER answer, native entry, settlement and resume equations.
  Its version-specific conclusion retains exact inputs, call sites and owner
  comparisons.

### From `docs/COMMON_API.md`: T2c. I need that ledger replay on every wrapper up to a whole configured history

Worked use:
USDC (`Blanc/Lift/Usdc/HistoryFamily.lean`, `HistoryReplay.lean`).

Worked
use: `Blanc/Lift/Usdc/HistoryReplayFrames.lean`.

### From `docs/COMMON_API.md`: C9.1. I need the lifted language and a checked certificate

Worked use: `Blanc/Lift/Usdc/ImplFp/Check.lean`,
  `Blanc/Lift/Usdc/ImplFp.lean`.

Worked use: `Blanc/Lift/Usdc/ImplWs/Check.lean`,
  `Blanc/Lift/Usdc/ImplWs.lean`.

Worked use:
  `Blanc/Lift/Usdc/ImplFrames.lean`.

### From `docs/COMMON_API.md`: C9.3. I need the free-pointer or write-site checker's soundness

The USDC worked specialization `implRun_fp_noStateGas` in
  `Blanc/Lift/Usdc/ImplFp.lean` applies that capability to the existing checked
  annotations and the same original successful implementation run.

### From `docs/COMMON_API.md`: C9.5. I need hashed storage slots, write locality or demanded zero cells

The
  concrete [`OldInitializerV1Clearing`](../../Blanc/Lift/Usdc/OldInitializerV1Clearing.lean)
  theorems `v1Clear_zeroStores_noExec` and `v1ClearEntry_zeroStores_noExec`
  instantiate the actual V1 clearing head and helper prefix, retaining the
  original `StepIn R` relation and outcome. They require no memory bounds,
  nonwrapping arithmetic or initial zero seed; whole-initializer coverage
  and historical execution remain separate obligations.

`Blanc/Lift/Usdc/OldInitializerV1Staging.lean`
  (`wrapper_strengthen`, `wrapper_stage`) is the worked three-string example
  and `Blanc/Lift/Usdc/OldInitializerV1Callee.lean` (`initialize_observed`)
  uses the rebuild to classify the whole wrapper run.

The concrete V2 consumer in
  [`Blanc/Lift/Usdc/OldInitializerEffects.lean`](../../Blanc/Lift/Usdc/OldInitializerEffects.lean)
  derives `implV2_initializeV2_observed` from successful fresh execution with
  `stateGas = none` and the actual initializer selector: every store targets metadata key4/15/18,
  writes zero, or targets a bounded modular payload word of the actual long
  decoded name; the same route has no external instruction. The wrapper
  derives its calldata bounds. `implV2_initializeV2_writeClass` projects
  the write classification. `implV2_initializeV2_short_nonInc` and
  `implV2_initializeV2_short_zero` require an actual decoded length at most31
  and separation from the three fixed keys; the latter also requires the
  initial zero seed. They do not establish the historical name profile,
  seed, long-payload separation or arbitrary nonzero-word preservation.

[`Blanc/Lift/Usdc/OldInitializerV1Callee.lean`](../../Blanc/Lift/Usdc/OldInitializerV1Callee.lean)
  is the worked V1 consumer (`callee_obs`).

[`Blanc/Lift/Usdc/OldInitializerV1Root.lean`](../../Blanc/Lift/Usdc/OldInitializerV1Root.lean)
  composes it with the original successful fresh V1 execution as V2 does:
  `implV1_initialize_observed` walks the actual dispatcher (free-pointer
  store, `div`/`and` selector, comparison chain, nonpayable entry 60), which
  derives the wrapper-entry seams, and lifts by `lift_sound_in_noStateGas`
  and `FreePtr.SFunc.RunP.withPot`. Its local premises are `stateGas = none`
  (`_hist` discharges it from `HistFork`) and the initial potential
  `pre.gasMeasure < 2 ^ 256`.

For historical initializer writes, use
  `ConfiguredHistoryTraceIn.initFrame_sstore` and `initRowWritesNonInc` in
  [`Blanc/Lift/Usdc/InitRowsHistory.lean`](../../Blanc/Lift/Usdc/InitRowsHistory.lean):
  the node-level classifier covers prefixes of raw frames, including delegated
  children and reverted executions, with the explicit finite `InitRowsApart`
  separation premise.

The allowance-locality laws have the same historical form in
  [`Blanc/Lift/Usdc/AllowLocalityHistory.lean`](../../Blanc/Lift/Usdc/AllowLocalityHistory.lean):
  `implV1Run_ws_noStateGas`, `implV2Run_ws_noStateGas`,
  `implV2_1Run_ws_noStateGas` and `implRun_ws_noStateGas` instantiate
  `lift_sound_ws_noStateGas`; `implV1/V2/V2_1/V2_2_allowLocality_noStateGas`
  and `implV1_allowLocality_observed_noStateGas` take `stateGas = none` in
  place of `CoveredFork` with unchanged conclusions.

### From `docs/COMMON_API.md`: C9.6. I need the calls, child frames and logs of a lifted frame

- Selected permit consumers `ric_seg_e8digest_noStateGas` in
  `Blanc/Lift/Usdc/ShuffleSegments.lean` and `ric_seg_w149_noStateGas` in
  `Blanc/Lift/Usdc/RefineSignedPermitFrames.lean` reuse the original shuffle
  checks.

### From `docs/COMMON_API.md`: C9.7. I need every execution prefix to a node, whatever the outcome

Worked use: USDC
  `Proxy.proxy_sstoreNodeH` in `Blanc/Lift/Usdc/ProxySstoreH.lean`.
  The shared `Proxy.proxy_sstoreCursorH` also retains the checked cursor and
  continuation geometry. `Proxy.proxy_implSstore_emitsUpgraded` in
  [`Blanc/Lift/Usdc/ProxyUpgradeLog.lean`](../../Blanc/Lift/Usdc/ProxyUpgradeLog.lean)
  follows that continuation to an actual retained `Upgraded` log for a committing
  proxy frame (`stateGas = none`, `bal = none`). Its same-frame prefix identifies
  an implementation-slot write; the result specifies address and topic with an
  existential payload. It does not assert receipt correspondence or history-wide
  implementation continuity. `ConfiguredHistoryTraceIn.implSlot_change_emitsUpgraded`
  in [`Blanc/Lift/Usdc/ProxyCommittedUpgradeLog.lean`](../../Blanc/Lift/Usdc/ProxyCommittedUpgradeLog.lean)
  composes this with retained-write attribution and frame-log inclusion: a
  committing raw frame changing the implementation slot yields that log at the
  proxy address. Its premises include nonempty proxy code at the frame entry,
  `ImplSlotApart`, and the history's body-stage capabilities and BAL restriction.
  The same module's `retained_implSstore_emitsUpgraded_of_proxyCode` instead
  takes the actual retained node's proxy-code identity directly and proves
  the log occurs in the same committed root. It does not require global
  implementation-slot separation; establishing the node's code remains the
  caller's obligation.
  [`Blanc/Lift/Usdc/ProxyRetainedContextCodes.lean`](../../Blanc/Lift/Usdc/ProxyRetainedContextCodes.lean)'s
  `ConfiguredHistoryTraceIn.retained_proxyV1_context` couples strict earlier
  retained-write exclusion with current Proxy/V1 code classification in one
  committing root. It derives the unchanged implementation word and excludes
  each current write using the same root's absence of an Upgraded log. Its
  explicit remaining inputs are installed Proxy/V1 code and implementation
  address at that root, own-code at the actual input root, and local separation
  for actual writes already known to run V1. It requires no global raw-write
  apartness; supplying that local V1 separation and the actual root/receipt
  facts remains a separate obligation.

USDC's `InitReachV1.tail7_reach_range` and `helper46_reach_range` in
  [`Blanc/Lift/Usdc/InitReachV1.lean`](../../Blanc/Lift/Usdc/InitReachV1.lean)
  carry the clearing interval through the old initializer helper, retaining
  the old endpoint computed from its actual input storage word. Their original
  interfaces remain projections. These range facts do not by themselves prove
  that a clearing key differs from a control slot.
  [`Blanc/Lift/Usdc/InitV1KeyBounds.lean`](../../Blanc/Lift/Usdc/InitV1KeyBounds.lean)
  bounds the decoded old length and clearing count for any stored header.
  `helper46_reach_ne_implSlot` consumes the helper range with explicit numeric
  hash-base bounds and the new-length cap.
  [`Blanc/Lift/Usdc/InitV1ConcreteBounds.lean`](../../Blanc/Lift/Usdc/InitV1ConcreteBounds.lean)
  proves the exact Keccak values for initializer headers 4, 5 and 7 in the kernel.
  Its `bounds` theorem supplies header separation, the hash-base margin and
  the implementation-slot exclusion interval for those three headers.
  `InitReachV1.callFrag_reach_range`, `callee_reach_range`, `wrapper_reach_range`
  and `initV1_reach_range` propagate the actual clearing ranges through the
  initializer; `BoundedRange` retains the three length caps derived from actual
  staging. The original caller interfaces project that same traversal.
  `InitV1KeyBounds.initV1_reach_ne_implSlot_concrete` combines these ranges and
  checked hashes to exclude the implementation slot at every reached initializer
  store, with no numerical-bound, length-cap or old-header-format premise.

The solc ABI string decoder
  fragments of `Blanc/Lift/SolcAbiStringStaging.lean` on a reach (`ReachAbi.strFrag_reach`,
  `rotFrag_reach`, `staticFrag_reach`; the allocation is `allocMem` by `strFrag_mem`, its size
  bounded by the potential) are there too; worked use: USDC `InitReachV1.wrapper_reach` in
  `Blanc/Lift/Usdc/InitReachV1.lean`.

Worked uses: USDC (`Blanc/Lift/Usdc/RefineSignedAuth.lean`,
  `RefineSignedPermitNodes.lean`, `RefineAdminRescue.lean`, `HistoryFamilyProxy.lean`).

### From `docs/COMMON_API.md`: C9.8. I need facts at a checked cursor of an actual successful execution

Worked
  uses: `Blanc/Lift/QuietDelegateSkip.lean`, `Blanc/Lift/Usdc/ImplFrames.lean`.

The concrete [`Usdc/V1MinterReach.lean`](../../Blanc/Lift/Usdc/V1MinterReach.lean)
  consumer derives the V1 removeMinter dispatcher/body path and retains the
  same final cursor: `successfulSstore_source` pairs each actual source pc
  with its computed base-12/base-13 key and exact SSTORE tail. Its first-store
  stop branch precedes any continuation to the second hash.
  [`Usdc/V1ConfigureMinterReach.lean`](../../Blanc/Lift/Usdc/V1ConfigureMinterReach.lean)
  proves the configureMinter twin through its distinct V1 entry-65 wrapper,
  paused/master-minter guards and body, pairing 0x20b2/base12 or 0x20f6/base13
  at the same actual cursor, with the same first-store stopping boundary.
  Both family walks have observed variants; the original interfaces project them.
  [`Usdc/V1MinterHashOccurrences.lean`](../../Blanc/Lift/Usdc/V1MinterHashOccurrences.lean)
  uses one synchronized prefix and the same final cursor to derive actual
  successful hashes before each reached store. `remove_successfulSstore_hashes`
  pairs 0x15f5→0x160b/base12 or 0x164d→0x1650/base13;
  `configure_successfulSstore_hashes` pairs 0x209c→0x20b2/base12 or
  0x20f3→0x20f6/base13. Each retains the exact account-word/base-word 64-byte
  input and original parent-prefix cuts. Hash pcs come from the same checked
  hash cursor's literal lead and the existing singleton store anchors.
  Collection and freshness remain separate.

### From `docs/COMMON_API.md`: C9.9. I need to walk a successful lifted run

Worked use: the USDC proxy (`Blanc/Lift/Usdc/ProxyWalk.lean`, `ProxyHalt.lean`).

Worked uses: USDC (`Blanc/Lift/Usdc/RefineTransferCallees.lean`,
  `RefineAdminBits.lean`).

Worked uses: USDC (`Blanc/Lift/Usdc/ShuffleSegments.lean`,
  `SignedSkip.lean`, `RefineSignedPermitNodes.lean`).

### From `docs/COMMON_API.md`: C9.11. I need deployment, CREATE, CREATE2 or a clone

The contract-specific V1 binding is in
  [`Usdc/ImplV1Origin`](../../Blanc/Lift/Usdc/ImplV1Origin.lean).
  `create_address` proves nonce18 at the already registered proxy creator
  yields the registered initial implementation address.
  `constructor_effects_of_original_receipt` specializes the shared result to
  the original index30 cut and derives its admitted sender from recovery.
  `constructor_effects_of_original_slot` binds fields through the actual body
  slot and decoder; `constructor_effects_of_signed_slot` supplies recovery from
  explicit signature fields and a signing-hash equality via
  `recoveredSender_of_signingHash`. That hash equality remains a caller
  obligation, not a proved payload computation. Creation code and certificate
  stay parameters with checked entry and runtime-window identities; no new
  input, original field correspondence or historical inclusion is adopted.

`ProxyCreation.runtimeReturn_runExact` in
  [`Blanc/Lift/Usdc/ProxyCreation/RuntimeReturn.lean`](../../Blanc/Lift/Usdc/ProxyCreation/RuntimeReturn.lean)
  is the existing concrete specialization, retaining its exact 2186-byte window
  at offset 671 and 226 fixed gas plus actual memory expansion. The original
  `ProxyCreation.runtimeReturn_effects` is likewise a projection of the common
  inverse. The separate kernel-checked `ProxyCreation.runtime_window` in
  [`Blanc/Lift/Usdc/ProxyCreation/RuntimeWindow.lean`](../../Blanc/Lift/Usdc/ProxyCreation/RuntimeWindow.lean)
  identifies that window in the registered creation input with the registered
  proxy runtime.

The companion `ProxyCreation.prefix_runExact` and
  `adminPrefix_runExact` in
  [`Blanc/Lift/Usdc/ProxyCreation/Prefix.lean`](../../Blanc/Lift/Usdc/ProxyCreation/Prefix.lean)
  consume the shared `rx_callRet` API to compose the actual registered entry
  and admin-label guard with their actual internal callees and continuations.
  They derive the constructor argument, fixed label hashes, memory image and
  gas charges; the admin argument is the executing message's caller.
  `terminal_runtimeReturn` connects the final caller continuation to the
  accepted runtime return.

For inversion of a successful whole registered
  constructor run, `ProxyCreation.constructor_effects_of_run` in
  [`Blanc/Lift/Usdc/ProxyCreation/Effects.lean`](../../Blanc/Lift/Usdc/ProxyCreation/Effects.lean)
  derives the implementation-slot write, admin-slot write using the actual
  caller, returned runtime window, and preservation of every other account's
  storage. Its internal-callee inversions consume actual successful runs and
  work without a fork restriction. `ProxyCreation.constructor_message_zero` in
  [`Blanc/Lift/Usdc/ProxyCreation/Settlement.lean`](../../Blanc/Lift/Usdc/ProxyCreation/Settlement.lean)
  composes the actual zero-value CREATE entry, the source constructor run at
  that same entry and raw result, and successful touch/code-charge settlement.
  A row distinct from both literal slots is zero in the installed result,
  including the empty-account deletion branch of code installation.
  `ProxyCreation.constructor_message_effects` uses the same actual entry,
  source run, raw result and successful charging to derive the installed
  registered proxy runtime and the entire target storage: empty storage with
  the initial implementation and actual caller admin written. Runtime length
  rules out account deletion and preserves those administrative words; no new
  nonempty-code, nonce, fork or desired-state premise is required. Actual
  bytecode-to-source lifting, historical occurrence and transaction settlement
  remain separate obligations; the local source run is an explicit premise.

At a raw frame of a `ConfiguredHistoryTraceIn`,
  [`Blanc/Lift/Usdc/ProxyCreation/HistoryFrame.lean`](../../Blanc/Lift/Usdc/ProxyCreation/HistoryFrame.lean)
  derives that source run from the frame (`constructor_run_of_exec` over
  `lift_sound_noStateGas`, entry facts from `rawFrame_entryFacts`):
  `constructor_effects_rawFrame` and `constructor_row_preserved_rawFrame`
  need only success and the registered creation code.

`ProxyCreation.original_constructor_effects_after_cut22` in
  [`Blanc/Lift/Usdc/ProxyCreation/HistoryCut.lean`](../../Blanc/Lift/Usdc/ProxyCreation/HistoryCut.lean)
  applies those effects to the selected head of a configured block's actual
  `TxSplit 22`, at `cut.afterBenv.state` immediately after settlement.
  `original_constructor_seed_after_cut22` packages that code, exact two-slot
  storage and tracked zero allowance rows as `OriginalConstructorSeed`, using
  explicit separation from the implementation and admin slots.
  `original_constructor_seed_of_receipt_cut22` derives that same head's clean
  message outcome from a successful receipt at the final block output, through
  the existing bounded receipt-preservation API. Constructor receiver, input,
  value, recovered sender and nonce remain explicit; identifying the supplied
  block with historical C, authenticating its receipt commitment and placing
  it in the consumed history remain caller obligations. No C-to-D continuity
  or pre-D governance restriction follows from this seed adapter.

### From `docs/COMMON_API.md`: C9.15. I need the USDC proxy-history adapters

For the exact value of an actual retained USDC proxy implementation write, use
`ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_data_of_proxyCode`
in `Blanc/Lift/Usdc/ProxyCommittedUpgradeLog.lean`; the `_data` sibling derives
proxy code from existing `ImplSlotApart`. The same original committed root
contains an `Upgraded` log whose data equals `write.value.toBytes`, including
same-value or later-restored writes. Actual prefix classification carries the
duplicate stack word and memory initialization through `UpgradeStoreDataConf`;
the history theorem derives memory well-formedness from original `FreshEntry`.
No memory or free-pointer premise should be added to a final history consumer.
Existing address/topic APIs remain compatible projections. Provider census
correspondence and deployment chronology are separate producer obligations.

In `Blanc/Lift/Usdc/ProxyRetainedNoDel.lean`, `UsdcEntriesReady` records
runtime availability at a genuine interval start, for only the entries already
created there. `UsdcUpgradeTargetsIn` is an address-only restriction on actual
retained proxy implementation writes. `TransactionTrace.usdc_origins_of_available_targets`
derives local readiness and transaction-entry origins; the configured-history
`transactions_origins_of_available_targets` carries those entries through the
original transaction list, yielding all origins, guarded installations and
final availability. Neither producer assumes final runtime or allowance facts.
In the same runtime-producer module,
`upgradeTargetsIn_between_txSplits_of_census` supplies that address restriction
from original ranged receipt evidence, and
`transactions_origins_between_txSplits_of_census` composes it with the actual
transaction-list producer. Earlier-cut availability and actual root membership
remain explicit; selected boundary transactions need separate constructor
proofs. These are internal producers, not replacement fields in a final
original-history assumption record. Census correspondence remains unadopted.

The available-runtime producer in `Blanc/Lift/Usdc/ProxyRetainedNoDel.lean`
also covers actual system messages, both request messages, optional beacon,
history and request stages, withdrawals and rewards via the `usdc_available_targets`
family and `usdc_available_targets_after_transactions`. Configured-history
`block_origins_of_available_targets`, `after_txSplit_origins_of_available_targets`,
`before_txSplit_origins_of_available_targets` and `mid_origins_of_available_targets`
compose those stages with the original transaction lists. Their conclusion
contains the derived origins and guarded installations, plus final availability.
`origins_between_txSplits_of_census` covers the complete original interval:
source-cut suffix, intervening blocks, and target-block opening/prefix. It
requires availability only at the actual source cut and derives availability
at the target cut; all root membership and target restrictions come from the
same original history/census. Selected boundary transactions remain separate.
The general stage/mid producers handle enabled system calls; the receipt-census
adapter retains its existing pre-Cancun bound. No original observation has been
adopted and no final origin/readiness fields have replaced the concrete producers.

`Blanc/Lift/Usdc/V1WriteApart.lean` supplies
`ConfiguredHistoryTraceIn.usdc_rawRowWrite_of_actualKeys_of_nodeCode`: the
original four faithful-key checks and two fixed-slot separation checks classify
one actual node with its own `UsdcContextCode`, preserving parent attribution.
The existing whole-scope classifier remains a compatible wrapper.
`Blanc/Lift/Usdc/RetainedAllowanceWrites.lean` exposes `_of_actualKeys` versions
of the retained write, root non-increase and root zero endpoints. They derive
code locally from the original guarded installations and use these same actual
successful-store populations, without descriptor-wide modern row separation.

For an original selected creation between available-runtime intervals,
`TransactionTrace.usdc_origins_of_create_noExecs` in
`Blanc/Lift/Usdc/ProxyRetainedNoDel.lean` discharges guarded origin and installation
obligations using the common constructor target exclusion.
`ConfiguredHistoryTraceIn.creation_txSplit_origins_and_available_targets`
applies it to the actual supplied cut and transports already-created runtimes
through complete transaction settlement. `UsdcEntriesReady.cons` extends that
family only with the new original constructor's derived installation/library facts.
`UsdcTransactionsOrigins.append`, `.cast` and `.of_txSplit` reassemble the actual
ordered trace by determinism. `UsdcMidHistoryOrigins.splice` and
`UsdcGuardedInstallations.splice` join the two intervals across that selected
head, preserving its original prefix, suffix and all system roots. These are
producer compositions; concrete signed creation/census correspondence and
initial selected-zero evidence still need their existing original observations.

`UpgradedTargetSatisfies` decodes the target of an actual proxy Upgraded log.
`retained_implSstore_target_of_logs` transfers any such address predicate to
each actual retained implementation write in the same root.
`retained_implSstore_target_between_txSplits_of_census` combines that result
with the original census-to-cut adapter and derives full-history root membership.
Instantiate the predicate with target inequality to exclude selection before
creation, or with membership in an already-created family. The theorem covers
same-value/restored writes and requires no earlier address-emptiness, final
runtime-readiness or additional temporal F2prime assumption. Actual ranged
census correspondence remains explicit; both selected cut transactions are
outside this interval and need their own producer evidence.

For concrete original USDC creation boundaries, `CreationHistory.lean` connects
`ImplV2Creation`, `ImplV2_1Creation`, `LibCreation` and `ImplV2_2Creation` original
observations to guarded transaction origins and runtime availability. Each
`OriginalObservation.origins_and_available_targets` preserves older available
entries and adds the checked runtime at its actual after-cut state. V2.2 also
uses the already-created library entry. Entry metadata remains unchanged;
these results establish runtime availability, not historical boundary adoption.
`OriginalModernCreationChain` records the four original blocks and five actual
intervening histories; its entry definitions retain the actual after-cut state
and canonical raw-node prefix. The chain definition alone asserts no runtime,
origin or installation property across the intervening intervals.
The shared `ProxyRetainedNoDel` adapter
`ConfiguredHistoryTraceIn.txSplit_origins_and_available_of_retainedTargets_ne`
accepts a concrete observation's checked retained-target exclusion, so callers
do not repeat its signed-input, CREATE-address or no-external-instruction proof.
`OriginalModernCreationChain.Censuses` states the four original receipt ranges,
with only entries already created at each interval. Its
`origins_and_available_of_censuses` composes all four intervals and constructor
heads, then the continuation after V2.2, deriving guarded origins, installations
and final family availability from initial V1 availability. The result retains
the actual trace and every enabled system root. A subset argument permits the
consumer's entry ordering without changing the original evidence population.
In `ProxyCompleteAvailable.lean`,
`ConfiguredHistoryTraceIn.mid_origins_of_complete_available_family` supplies the
last interval once all allowed implementation addresses have available runtimes;
it needs no later upgrade census. The concrete chain derives that availability
at the V2.2 cut using its original constructor observations.
