# Deployed-bytecode claim map: Curve 3Crv

## 5.3 Curve 3Crv: model refinement, exact committed replay, conservation

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| **History:** the final storage abstracts the model state reached by `Curve3Crv.step` over **exactly the settlement-committed writer invocations** at the contract, in trace order, and that model state is conserving (`totalSupply = Σ balances`) | `Blanc.Lift.Curve3Crv.c3crv_history_committed_derived` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:230`); base form `Blanc.Lift.Curve3Crv.c3crv_history_committed` (`Blanc/Lift/Curve3Crv/CommittedHistory.lean:191`) (takes the calldata bound as a hypothesis) | History / safety, exact extraction | CODE; INIT `VyInv … initialKeys`; **HASH-T** `FreshKeys initialKeys (historyTouchedKeys ca trace)` (rolled-back frames included); the calldata bound is derived | No static filter: `Blanc.Lift.Curve3Crv.c3crv_writer_nonstatic` (`Blanc/Lift/Curve3Crv/Safe.lean:283`) proves a writer cannot succeed in a static frame |
| **Conservation from the actual deployment:** at any checkpoint after the 3Crv token's deployment, the supply word equals the sum of the balance words of every holder whose balance key the history's raw token frames touched. Intermediate: **Deployment-rooted history:** from the recorded creation transaction of the 3Crv token, in its retained mainnet block 10,809,467, to a later checkpoint: the runtime is still installed, and the final storage abstracts the model state reached by `Curve3Crv.step` from the constructor's state (minter the deployer, supply and balances zero) over **exactly the settlement-committed writer invocations** at the contract after the creation, in trace order, each accepted with the owner word that the frame's own `owner()` static call answered under the frame's actual delegation rules; and that model state is conserving | `Blanc.Lift.Curve3Crv.c3crv_conserved` (`Blanc/Lift/Curve3Crv/Headline.lean:118`), with conclusion `Blanc.Lift.Curve3Crv.SupplyConserved` (`Blanc/Lift/Curve3Crv/Headline.lean:48`); via the frame-by-frame replay `Blanc.Lift.Curve3Crv.C3crvDeploymentTo.frames` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:105`), over the record `Blanc.Lift.Curve3Crv.C3crvDeploymentTo` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:37`) | Deployment-rooted history / safety, exact extraction | DEPLOYMENT: a retained configured `HistFork` mainnet block with header number 10,809,467 and timestamp of 1,599,414,946, whose transaction at index 76 is the recorded signed creation transaction (hash 0xa7d90e46...053694f8) and whose receipt at that index reports success; HISTORY: the retained configured `HistFork` history from that block's end to the checkpoint; **HASH-T** `FreshKeys` over the keys the raw token frames of the rest of that block and of that history touch. No installed-code premise, no INIT premise, no gas premise | INIT is the actual deployment, not an arbitrary `VyInv` checkpoint (the checkpoint form is the row above). Funds, gas, nonce, sender code, target freshness, the installed runtime, the deployed storage and the initial `VyInv` are derived (`Blanc.Lift.Curve3Crv.C3crvDeploymentTo.created` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:78`)). Owner evidence is `Blanc.Lift.Curve3Crv.OwnerAnswerH` (`Blanc/Lift/Curve3Crv/SafeBodies.lean:41`), which on a covered fork is `OwnerAnswer`. Rooted in the retained block, not in a header, block hash or state root |
| **The creation transaction in its block:** in a retained `HistFork` mainnet block at those coordinates, a transaction cut whose transaction is the recorded signed CREATE and whose receipt reports success leaves, right after it, the certified 3Crv runtime at the token address with storage `deployedStor deployer`; the block's log list gains exactly the creation log and its gas used grows by exactly 678,343 (intrinsic 97,992 + constructor 125,151 + code deposit 455,200) | `Blanc.Lift.Curve3Crv.Creation.HistoricalTx.actual_block_cut` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxTrace.lean:229`) | Block / transaction, deployment | DEPLOYMENT as in the row above (block, coordinates, transaction at the cut, receipt success); no hash, funds, gas or nonce premise | The recorded raw bytes hash to the observed transaction hash, decode strictly to the transaction used here, and recover the deployer [`Blanc.Lift.Curve3Crv.Creation.HistoricalTx.raw_binding` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxRecover.lean:44`), `Blanc.Lift.Curve3Crv.Creation.HistoricalTx.recoveredSender` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxRecover.lean:37`)]. The fork (Muir Glacier) and zero base fee are derived from the header; the pre-EIP-155 signature (v = 28) is recovered in the kernel; the receipt status is used only to exclude a CREATE collision. The gas figure is a theorem (`Blanc.Lift.Curve3Crv.Creation.HistoricalTx.muirGasUsed_eq_limit` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxSettle.lean:50`)), not an observation |
| A successful frame from a fresh entry is exactly the model step: writers (events, storage abstraction, owner answer for `set_name`, and the return bytes: the ABI word `true` for `transfer`, `transferFrom`, `approve`, `mint` and `burnFrom`, empty for `setMinter` and `setName`), **and views (storage and logs unchanged, return bytes equal the model output)** | `Blanc.Lift.Curve3Crv.c3crv_frame_refines` (`Blanc/Lift/Curve3Crv/Safe.lean:291`); raw form `Blanc.Lift.Curve3Crv.c3crv_frame_refines_raw` (`Blanc/Lift/Curve3Crv/Safe.lean:193`) (output stated relative to the entry output) | Frame / safety | CODE; covered fork; calldata bound below 2^256 (a frame-level hypothesis); **fresh entry as explicit premises** `pre.stack = []`, `pre.memory = Mem.empty`, `pre.output = []`; INIT-shaped `VyInv pre`; HASH-T `FreshKeys` (call keys); a successful `Exec 0 sevm pre (.ok post)` | Every successful selector is covered (misses and short calldata have no successful run). The fresh-entry facts are hypotheses here, not derived from a `Frame.enter` equation |
| Token-model properties: `step` preserves conservation; the initial state is conserving; supply and minter change only by the minter; non-minter `transferFrom` spends allowance even at the maximum value, while the minter retains allowances; zero-first approve; authorized allowance and balance changes | `Blanc.Curve3Crv.step_conserved` (`Blanc/Curve3Crv/Properties.lean:160`), `Blanc.Curve3Crv.init_conserved` (`Blanc/Curve3Crv/Properties.lean:165`), `Blanc.Curve3Crv.supply_change_by_minter` (`Blanc/Curve3Crv/Properties.lean:182`), `Blanc.Curve3Crv.minter_change_by_minter` (`Blanc/Curve3Crv/Properties.lean:201`), `Blanc.Curve3Crv.transferFrom_spends_allowance` (`Blanc/Curve3Crv/Properties.lean:223`), `Blanc.Curve3Crv.transferFrom_spends_max_allowance` (`Blanc/Curve3Crv/Properties.lean:233`), `Blanc.Curve3Crv.transferFrom_minter_keeps_allowances` (`Blanc/Curve3Crv/Properties.lean:249`), `Blanc.Curve3Crv.approve_zero_first` (`Blanc/Curve3Crv/Properties.lean:258`), `Blanc.Curve3Crv.allowance_change_authorized` (`Blanc/Curve3Crv/Properties.lean:267`), `Blanc.Curve3Crv.balance_debit_authorized` (`Blanc/Curve3Crv/Properties.lean:307`) | Model / safety | the model only | bridged to the bytes by the frame row above and the history rows, and four of them lifted to the bytes by the row below |
| **The policy at the bytes, from the actual deployment:** every settlement-committed writer frame at the token after the deployment obeys four facts over its own opening and closing storage words: only the address in the minter word moves the supply word, and only by `mint` or `burnFrom`; only that address moves the minter word; a `transferFrom` by any other caller spends exactly its value of the caller's allowance word, which covers it; and the allowance word of a tracked pair (one the history's raw token frames touched) moves only by its owner's `approve` of that spender or that spender's `transferFrom` from that owner | `Blanc.Lift.Curve3Crv.c3crv_policy` (`Blanc/Lift/Curve3Crv/Headline.lean:146`), with conclusion `Blanc.Lift.Curve3Crv.C3crvFramePolicy` (`Blanc/Lift/Curve3Crv/Headline.lean:89`) | Deployment-rooted history / safety, per frame | as the deployment-rooted row above (the record only) | Committed writer frames only: view and unknown-selector frames are not in the statement (the frame refinement shows they change no storage). The allowance fact covers tracked pairs only, since an untracked pair's slot may coincide with a live key's. Lifts `supply_change_by_minter`, `minter_change_by_minter`, `transferFrom_spends_allowance` and `allowance_change_authorized`; the other model properties stay at the model level |

**Liveness.** Frame: `Blanc.Lift.Curve3Crv.c3crv_step_exec` (`Blanc/Lift/Curve3Crv/Exec.lean:53`). A model-accepted call (every selector
except `set_name`) executes with **an exact but existentially quantified
cost**: `∃ c, ∀ G > gCallStipend, … exec at G + c … gasLeft = G`, ending in the
model's step with exact logs and return bytes. **No closed cost formula is
claimed.** `Blanc.Lift.Curve3Crv.c3crv_setName_exec` (`Blanc/Lift/Curve3Crv/Exec.lean:86`): `∃ R P` such that any callee answering under
`OwnerCallOk` (the minter's `owner()` STATICCALL answers the caller and leaves
`R`) at `Gc` makes every frame with at least `Gc + P` gas succeed; this is a
**callee premise**. Reachable state: `Blanc.Lift.Curve3Crv.c3crv_history_live` (`Blanc/Lift/Curve3Crv/Liveness.lean:23`) and
`Blanc.Lift.Curve3Crv.c3crv_history_setName_live` (`Blanc/Lift/Curve3Crv/Liveness.lean:70`) say that after any configured history every
model-accepted call executes at the future storage (premises: the history
premises plus `FreshKeys` for the new call's own keys, and `pre.output = []`).
No transaction-level liveness.

**Deployment / INIT.** `Blanc.Lift.Curve3Crv.Creation.curve_deploy_covered` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:304`), for every covered fork
`f`: a nonce-42 CREATE from the recorded deployer installs the runtime and
leaves `deployedStor deployer` with `VyInv … (curveDeployedState deployer) (fun _
=> False)`. The recorded deployment therefore satisfies the history theorem's
checkpoint predicate (name, symbol, decimals 18, supply 0, minter = deployer)
with no hash premise; the constructor's write of 0 at `keccak(3‖caller)` is
discharged by kernel evaluation. General form `Blanc.Lift.Curve3Crv.Creation.curve_create` (`Blanc/Lift/Curve3Crv/Creation/Deploy.lean:207`) (storage
`deployedStor`). `Blanc.Lift.Curve3Crv.curve_init_vyInv` (`Blanc/Lift/Curve3Crv/Init.lean:37`) is a satisfiability instance.
The recorded creation transaction is also shown inside its retained block:
`Blanc.Lift.Curve3Crv.Creation.HistoricalTx.actual_block_cut` (`Blanc/Lift/Curve3Crv/Creation/HistoricalTxTrace.lean:229`)
derives the installed runtime, the storage `deployedStor deployer`, the creation log and the exact gas used from the
recorded Muir Glacier transaction and the block's success receipt, with no hash premise, and
`Blanc.Lift.Curve3Crv.C3crvDeploymentTo.created` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:78`) states the resulting
`VyInv` at `curveDeployedState deployer`. `Blanc.Lift.Curve3Crv.C3crvDeploymentTo.frames` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:105`) carries it to a checkpoint.

**Fork coverage.** History and liveness on covered forks;
`curve_deploy_covered` quantifies over covered forks. The deployment-rooted row and the creation-transaction row range over `HistFork` (Byzantium through BPO2; Amsterdam is not covered).

**Non-claims.** Log and return bytes at the *history* level (only at frame
level); replay equal to the *raw* trace's writer sequence (rolled-back frames
are, by design, not in it); a closed cost formula; `set_name` without the
owner-call premise. That the retained block and history are the chain's own, or that the header coordinates bind to a block hash or state root.

## Artifacts

| Contract | Address | Runtime bytes | keccak256 codehash | Creation transaction | Block |
|---|---|---:|---|---|---:|
| Curve 3Crv LP token | 0x6c3F90f043a72FA612cbac8115EE7e52BDe6E490 | 2,276 | 0xb731b7a9a74c6c60d715f0c791d663f1530743a48337e7fab9cf3481afdd9feb | 0xa7d90e460bed56181e41b74d143ec98fe097c8391700e4e0788f5282053694f8 (deployer 0xbabe61887f1de2713c6f97e567623453d3c79f67, nonce 42) | 10,809,467 |

Compiler, from the certificate provenance: Vyper 0.2.4. Runtime identity: `eth_getCode`
agreement across five separately operated public providers at one finalized block; the creation
input fetched from two providers and equal byte for byte.

## Summary matrix

| | M1 | M2 | M3 | M4 | M5 | M6 | M7 | M8 |
|---|---|---|---|---|---|---|---|---|
| Curve | ✓ | ✓ | ✓ | ✓ HASH-T | ✓ [b] [ak] | ~ [g] | ✗ | ✓ |

[g] `set_name` needs the `OwnerCallOk` callee premise; the cost
is existential.

[ak] For 3Crv the deployment is also chained: the recorded creation transaction in its retained Muir Glacier block is the root of a configured history (Section 5.3), so [b]'s "not chained" describes the modeled `_covered` message only.

## Disclosures and limits

2. **Curve cost.** No closed Curve cost formula is claimed for 3Crv: its cost is exact but existential.

3. **Deployments are modeled, not historical inclusion.** Curve 3Crv (10,809,467) predates Prague too; its `curve_deploy_covered` is a modeled deployment like the others, and Section 5.3 in addition states its recorded creation transaction inside its retained Muir Glacier block, which is still not an inclusion proof (no header, block hash or state-root binding). The modeled deployment theorems execute
   the recorded creation input as a CREATE message under current rules
   (`deployMsg`, an empty world, 1M–3M gas). The deployment results are messages,
   not validated transactions. The reachable V± chains (Sections 5.5 and 5.6)
   are modeled messages too but have a different shape: they start from a world
   holding a funded, code-free creator, place each implementation at its
   registered address by a supplied CREATE target, and continue through
   initialization, funding and the experiment, each message from the previous
   settled world (item 25).

9. **Callee premises.** `OwnerCallOk` (Curve `set_name`) assumes the callee's behaviour.

12. **Curve cost is exact but existential** (`∃ c`), with no closed formula.

The 3Crv deployment-rooted rows use `HistFork` (Byzantium through BPO2), which includes the Muir
Glacier rules the deployment block ran under; the Jaune conformance figures of Section 3 begin at
Prague and do not cover them.

## Named premises and definitions

| Name | Declaration | Role |
|---|---|---|
| `VyInv` | `Blanc.Lift.Curve3Crv.VyInv` (`Blanc/Lift/Curve3Crv/Layout.lean:95`) | Curve 3Crv's storage abstraction over the live keys |
| `FreshKeys` | `Blanc.Lift.Curve3Crv.FreshKeys` (`Blanc/Lift/Curve3Crv/Layout.lean:115`) | the frame-local premise for the keys a Curve frame touches: each is fresh and their slots are pairwise distinct (HASH-T) |
| `Curve3Crv.historyTouchedKeys` | `Blanc.Lift.Curve3Crv.historyTouchedKeys` (`Blanc/Lift/Curve3Crv/CarriedHistory.lean:27`) | the keys a Curve history touches |
| `OwnerCallOk` | `Blanc.Lift.Curve3Crv.OwnerCallOk` (`Blanc/Lift/Curve3Crv/LiveBodies.lean:1866`) | the callee premise of Curve `set_name`: its static `owner()` call answers whenever it is given enough gas, and leaves at least `R` gas |
| `C3crvDeploymentTo` | `Blanc.Lift.Curve3Crv.C3crvDeploymentTo` (`Blanc/Lift/Curve3Crv/HistDeployment.lean:37`) | the 3Crv deployment record: the retained Muir Glacier block that created the token, its transaction at index 76 and successful receipt, the configured history to the checkpoint, and HASH-T freshness |
| `OwnerAnswerH` | `Blanc.Lift.Curve3Crv.OwnerAnswerH` (`Blanc/Lift/Curve3Crv/SafeBodies.lean:41`) | `OwnerAnswer` under the frame's actual delegation rules: the frame's static `owner()` call succeeded and returned a word starting with the recorded one |

## Uses of the shared API

### From `docs/COMMON_API.md`: S7. I need a token-ledger conservation invariant

Worked instance: 3Crv
(`Blanc/Composition/Curve3CrvTokenCore.lean`, `c3crvSupply`, `c3crv_history_supply`), composed with
the Curve 3pool over one history in `Blanc/Composition/Curve3PoolSupply.lean` (`pool_3crv_history`).

### From `docs/COMMON_API.md`: T2a. I need a frame invariant under trace-local entry premises

Worked
  consumer: `Lift.Curve3Crv.c3crv_history_committed_derived`.

### From `docs/COMMON_API.md`: T2c. I need that ledger replay on every wrapper up to a whole configured history

Curve 3Crv observes the
ordered writer invocations of its settlement-committed frames, with the storage
boundary as carrier and a model replay universally quantified over the opening
abstraction (`Blanc/Lift/Curve3Crv/CommittedReplay.lean`,
`CommittedHistory.lean`).

## See also

- [Disclosures and limits: item 6](vyper-nonreentrant-deployed.md#disclosures-and-limits)
