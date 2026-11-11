# Deployed-bytecode claim map: Beacon deposit

## 5.2 Beacon deposit: exact committed deposit history

**Safety, refinement and history**

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| After any configured history, storage is the accumulator of the initial history followed by exactly the deposits whose frames were committed (rollback-filtered by settlement), in order. **The mainnet-satisfiable form** | `Blanc.Lift.BeaconDeposit.configuredHistory_solInv_sys` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:139`); base form `Blanc.Lift.BeaconDeposit.configuredHistory_solInv` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:73`) | History / safety, exact extraction | CODE `installed`; INIT `SolInv … initialHistory`; ENV (trace-local, finite): `SystemCodeInstalled checkpoint` (canonical bytes at the four system addresses), `NoAuthorityAt` and no CREATE frame at those four addresses and at `0x02`, `getCode 2 = empty` at the checkpoint. **No hash premise.** The calldata bound, system exclusion [`Blanc.Lift.BeaconDeposit.system_of_installed` (`Blanc/Lift/BeaconDeposit/BeaconEnv.lean:124`), `Blanc.ExecutionTrace.ConfiguredHistoryTrace.systemFrames_of_installed` (`Blanc/ExecutionTraceSystemCode.lean:274`)], `0x02` warmth and no-delegation are derived | the `0x02` warmth is derived from EIP-2929 pre-warming, preserved across rollback |
| **From the actual deployment block:** over the whole retained history from the deposit contract's deployment block 11,052,984 to a later modern block, the count word is the number of committed deposits, as a number, and the root computed from the stored branch and count words is the reference root of exactly those deposits, in order. Intermediate: at that block the storage satisfies `SolInv` for exactly the committed deposits of the whole span | `Blanc.Lift.BeaconDeposit.beacon_deposits` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:166`), with conclusion `Blanc.Lift.BeaconDeposit.DepositHistory` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:157`); via `Blanc.Lift.BeaconDeposit.BeaconDeploymentTo.solInv` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:122`), from the whole-span seam composition `Blanc.Lift.BeaconDeposit.historicalSeam_wholeSpan_solInv` (`Blanc/Lift/BeaconDeposit/HistoricalSeam.lean:256`); the count word by `Blanc.Lift.BeaconDeposit.solCount_eq_of_solInv` (`Blanc/Lift/BeaconDeposit/Views.lean:86`); reference correctness `Blanc.BeaconDeposit.root_correct` (`Blanc/BeaconDepositCorrectness.lean:284`) | Deployment-rooted history / safety | DEPLOYMENT `Blanc.Lift.BeaconDeposit.BeaconDeploymentTo` (`Blanc/Lift/BeaconDeposit/HistDeployment.lean:40`): the retained Muir Glacier deployment block whose body slot 2 decodes to the recorded creation transaction, with its successful receipt and no log at the deposit address; the configured histories through the adopted Shanghai, Cancun and Prague seam anchors to the modern block; empty `0x02` code after the deployment block; no frame without a code address targeting `0x02`, and over the modern span no authorization recovering to a system contract or `0x02`. No INIT, CODE or `SystemCodeInstalled` premise | INIT is the actual deployment (the empty deposit history at the deployment boundary is derived), not an arbitrary initial history |
| `get_deposit_count` and `get_deposit_root` on the final state succeed with those outputs, at exact gas | `Blanc.Lift.BeaconDeposit.configuredHistory_count_view` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:92`), `Blanc.Lift.BeaconDeposit.configuredHistory_root_view` (`Blanc/Lift/BeaconDeposit/CommittedHistory.lean:119`) | History and frame / live | **per-frame `beaconEntry`** (ENV: `0x02` warm, undelegated), depth, gas | there is no `_sys` form of the views |
| A successful frame is exactly the model step (decode, accumulator, event, storage shape); other selectors change no storage or logs | `Blanc.Lift.BeaconDeposit.deposit_frame_refines` (`Blanc/Lift/BeaconDeposit/Safe.lean:104`) | Frame / safety | CODE; ENV `ShaReady`; INIT-shaped `SolInv pre` | |

**Liveness.** Frame: `Blanc.Lift.BeaconDeposit.deposit_exec_solInv` (`Blanc/Lift/BeaconDeposit/DepositExec.lean:73`). A model-accepted deposit executes
at exactly `G + depositGasOf origLive origCount`, with `depositGasOf = 656 + bodyGasOf` and `bodyGasOf =
14551 + sloadCost(count) + countStoreCostOf origCount + bodyInsertGasOf origLive`, where `origLive` and `origCount`
are the entry machine's original reads `base.getOrigStorVal` of the stored branch slot and of the count slot (the
price Jaune charges: `0` at an owner created in the same transaction; Option A, decision
blanc-repin-os-optionA-delegation-20261012) [`Blanc.Lift.BeaconDeposit.depositGasOf` (`Blanc/Lift/BeaconDeposit/DepositExec.lean:29`),
`Blanc.Lift.BeaconDeposit.bodyGasOf` (`Blanc/Lift/BeaconDeposit/BodySpec.lean:225`)], appending the model node and event. `get_deposit_count` costs
1,514 with its count slot warm [`Blanc.Lift.BeaconDeposit.get_deposit_count_warm_exec` (`Blanc/Lift/BeaconDeposit/Views.lean:20`)] (no cold-slot cost is stated); `supportsInterface(id)` succeeds at exact gas `erc165Gas` and returns true exactly when `id` is the ERC-165 or the deposit interface id [`Blanc.Lift.BeaconDeposit.supportsInterface_exec` (`Blanc/Lift/BeaconDeposit/Views.lean:38`)]; `get_deposit_root` costs `Blanc.Lift.BeaconDeposit.rootViewGas` (`Blanc/Lift/BeaconDeposit/RootView.lean:611`). Reachable
state: `Blanc.Lift.BeaconDeposit.configuredHistory_deposit_live` (`Blanc/Lift/BeaconDeposit/Liveness.lean:24`) says that after any configured history a
model-accepted deposit executes at exact gas and appends exactly the new node
(premises: per-frame `beaconEntry`, `DepositDecodable`, `ShaReady`, sentry and
bound side conditions, all priced from the same machine original reads). **There is no transaction-level Beacon liveness**: a
deposit carries value, which needs a value-carrying envelope.

**Deployment / INIT.** `Blanc.Lift.BeaconDeposit.Creation.beacon_deploy_covered` (`Blanc/Lift/BeaconDeposit/Creation/Deploy.lean:155`), for every covered fork
`f`: the address is the CREATE address of the recorded deployer at nonce 0, and
the deployment message `deployMsg.withFork f` installs the certified runtime
and leaves `SolInv (getStor post) []`. General form `Blanc.Lift.BeaconDeposit.Creation.beacon_create` (`Blanc/Lift/BeaconDeposit/Creation/Deploy.lean:53`). No
hash premise. Satisfiability: `Blanc.Lift.BeaconDeposit.beacon_zero_init` (`Blanc/Lift/BeaconDeposit/Init.lean:71`) (`SolInv beaconZeroStor []`).

**Fork coverage.** History and `_sys` theorems on all covered forks;
`beacon_deploy_covered` quantifies over covered forks.

**Non-claims.** Revert routes and payloads; BLS validity; authenticated
deposit history; historical inclusion of the constructor. The premises are the
honest form of the environment: trace-local and finite, but
`SystemCodeInstalled` posits the canonical bytes on the chain (Section 2).

## Artifacts

The runtime bytes are the lifted inputs in `scripts/lift/inputs/`; the codehash
column is recomputed from those files by the checker (Section 10), and each
creation transaction is recorded in the entry's `provenance` in
`scripts/lift/certificates.json`.

| Contract | Address | Runtime bytes | keccak256 codehash | Creation transaction | Block |
|---|---|---:|---|---|---:|
| Beacon deposit | 0x00000000219ab540356cBB839Cbe05303d7705Fa | 6,358 | 0x6c029a231254fadb724d63be769f75eedd66362df034a3e663252b49d062a666 | 0xe75fb554e433e03763a1560646ee22dcb74e5274b34c5ad644e7c0f619a7e1d0 (deployer 0xb20a608c624ca5003905aa834de7156c68b2e1d0, nonce 0) | 11,052,984 |
