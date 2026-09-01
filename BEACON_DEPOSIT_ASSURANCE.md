# BeaconDeposit assurance register

This is the fail-closed claim map for Blanc's BeaconDeposit opening model,
compiled port, exact direct deployment, and admitted open history.  It does not
create evidence.  Every declaration below is independently elaborated by the
repository axiom audit and statement-pinned by the claims gate; the finite
channels are corroboration at named concrete cases, not premises of the Lean
theorems.

The protected artifact is Blanc's own 2,891-byte runtime and 3,037-byte
creation code.  Runtime Verification's KEVM work and this development concern
different artifacts and independent proof developments.  This register is not
a verification claim about the deployed r2 bytecode.  Finite evidence is not a
universal theorem.  Across all rows there is no hash injectivity or collision
freedom and no universal liveness claim.

Each protected row has seven load-bearing fields in a frozen order.  Axiom
expectations are exact sets, not upper bounds.  The **Gate** field names every
repository gate needed to own the cited theorem statement/axioms and the
row-specific finite evidence.  **Differential channel** says `no direct finite
channel` where the closure theorem is intentionally proof-only instead of
inventing an observation that does not exist.

## Pillar — Opening model

#### OPEN-1 — The hash-parametric incremental Merkle model preserves its history invariant and computes the mixed root represented by that history

- **Declarations:** `Blanc.BeaconDeposit.root_correct`, `Blanc.BeaconDeposit.deposit_ok_spec`, `Blanc.BeaconDeposit.deposit_inv`
- **Premises:** `root_correct` and `deposit_inv` consume the opening model's explicit `Inv H state history`; successful deposit additionally exposes the exact pre-count, inserted node, event tuple, capacity bound, and returned state fixed by `deposit_ok_spec`.  Closure instantiates `H` with `Bytes.sha256`; no cryptographic property of `H` is assumed.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`, `scripts/check-beacon-deposit-model.sh`
- **Differential channel:** the committed pure-model oracle vectors exercise empty and nonempty insertion/root regimes under Keccak for an independent executable comparison; the compiled bridge uses SHA-256 and does not infer a theorem from these vectors.
- **Non-claims:** model partial correctness only.  It proves neither collision resistance nor unique-history commitment, reference bytecode correctness, precompile implementation correctness, or that any transaction occurs.
- **Source:** `Blanc/BeaconDepositCorrectness.lean`, `Blanc/BeaconDepositModel.lean`, `scripts/reference/beacon-deposit/vectors.json`

## Pillar — Compiled port

#### P1 — The compiler emits the named Blanc runtime and constructor prefix, and the exact runtime and complete creation artifact satisfy their protocol size ceilings

- **Declarations:** `Blanc.BeaconDeposit.code_compile`, `Blanc.BeaconDeposit.code_eip170`, `Blanc.BeaconDeposit.constructorInitPrefix_compile`, `Blanc.BeaconDeposit.creationCode_eip3860`
- **Premises:** the declarations name the frozen production `runtime`, `constructorProgram`, `code`, `constructorInitPrefix`, and `creationCode` constants.  The exact hashes are independently pinned by the Prague and BPO2 manifests rather than reflected into these proofs.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`, `scripts/check-beacon-deposit-differential.sh`, `scripts/check-beacon-deposit-current-mainnet.sh`
- **Differential channel:** both Beacon manifests byte-pin the 2,891-byte runtime and 3,037-byte creation artifact; the Prague creation measurement and BPO2 fresh deployments execute each side's own artifact.
- **Non-claims:** no byte, code-hash, metadata, raw-layout, storage-root, or gas identity with the Solidity reference.  Smaller measured artifacts do not imply semantic equivalence outside the credited channels.
- **Source:** `Blanc/BeaconDepositCode.lean`, `Blanc/BeaconDepositDeploy.lean`, `scripts/fixtures/beacon-deposit/manifest.json`, `scripts/fixtures/beacon-deposit-current-mainnet/manifest.json`

#### P2 — A model-approved decoded deposit executes and settles with the model-linked storage update, exact committing chronology, and byte-exact event

- **Declarations:** `Blanc.BeaconDeposit.deposit_success_settled_effects`, `Blanc.BeaconDeposit.deposit_success_retainedStorageEffectTriples`
- **Premises:** canonical machine bounds, decoded calldata, exact selector and production bytes, a successful `deposit Bytes.sha256` result, concrete storage/count/access facts, sufficient gas, nonstatic depth, and enabled warm undelegated native SHA-256 at address `0x2`; settlement starts from the actual successful transfer result and ordinary non-precompile code address.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`, `scripts/check-beacon-deposit-differential.sh`
- **Differential channel:** `selector-deposit-success`, the accepted noncanonical ABI rows, all successful value edges, and `chained-deposits-1-through-8` compare status, returndata, logical state, ETH, ordered logs, and the full SHA STATICCALL trace.
- **Non-claims:** partial correctness for the stated success premises, not success for every input, termination, or universal equivalence.  The event index is the pre-increment count; raw storage coordinates intentionally differ from Solidity.
- **Source:** `Blanc/BeaconDepositSuccessSettlement.lean`, `Blanc/BeaconDepositSuccessChronology.lean`, `scripts/fixtures/beacon-deposit/manifest.json`

#### P3 — Decoded model errors, structural ABI failure, and selector miss revert through their exact compiled routes without retained storage effects

- **Declarations:** `Blanc.BeaconDeposit.deposit_ne_assert_false`, `Blanc.BeaconDeposit.deposit_error_runCompiledTo`, `Blanc.BeaconDeposit.deposit_malformed_noRawSstore`, `Blanc.BeaconDeposit.unmatched_selector_noRawSstore`
- **Premises:** the decoded error theorem is indexed by an actual model `.error reason` plus exact environment and machine bounds; malformed calldata supplies failure of the explicit structural decoder; selector miss is nonempty dispatch input outside the four-selector census.  The model theorem alone licenses omission of the terminal `assert(false)` arm.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`, `scripts/check-beacon-deposit-differential.sh`
- **Differential channel:** all eight `guard-01` through `guard-08` tags, `guard-precedence`, malformed ABI rows, accepted noncanonical controls, empty and unknown fallback rows, byte-exact revert channels, failed/short SHA responses, and bounded OOG rows.
- **Non-claims:** the malformed matrix is finite agreement, not universal Solidity-decoder equivalence.  Empty calldata is a distinct proved route, and rolled-back writes are not misreported as absence of raw instruction occurrence.
- **Source:** `Blanc/BeaconDepositCorrectness.lean`, `Blanc/BeaconDepositErrors.lean`, `Blanc/BeaconDepositSelectorMiss.lean`, `BEACON_DEPOSIT_DEVIATIONS.md`

#### P4 — ERC-165 and both views return their exact interface encodings without raw or retained storage writes on the named successful routes

- **Declarations:** `Blanc.BeaconDeposit.supportsInterface_runCompiled_noRawSstore`, `Blanc.BeaconDeposit.getDepositRoot_zero_runCompiled_noRawSstore`, `Blanc.BeaconDeposit.getDepositCount_warm_runCompiled_noRawSstore`
- **Premises:** exact selector, production code, calldata and machine bounds, zero call value, and route-specific storage/access facts.  The root view additionally needs `ZeroHashesCorrect`, count bounds, sufficient gas, and enabled warm undelegated SHA-256 at `0x2`; the count row is the warm specialization and a separately audited cold theorem exists.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`, `scripts/check-beacon-deposit-differential.sh`
- **Differential channel:** `selector-get-deposit-root-empty`, `selector-get-deposit-count-empty`, ERC-165/deposit/`ffffffff`/dirty-padding support rows, chained root/count readback, and the three nonpayable value-rejection rows.
- **Non-claims:** the `zero` in the root theorem means zero call value, not empty storage or zero count.  Read-only route proofs do not imply liveness, historical use, or correctness of the deployed reference.
- **Source:** `Blanc/BeaconDepositRootPublic.lean`, `Blanc/BeaconDepositCountEffects.lean`, `Blanc/BeaconDepositEffects.lean`

#### P5 — Every same-frame runtime SSTORE site is classified, successful deposit commits count before its one live branch cell, and construction has exactly the 31 zero-hash writes

- **Declarations:** `Blanc.BeaconDeposit.Exec.NinstOccurrence.beaconRuntime_sstore_pc_of_rawFrameRoot`, `Blanc.BeaconDeposit.Exec.Deriv.beaconConstructor_sstore_coordinate`, `Blanc.BeaconDeposit.constructor_success_retainedStorageEffectTriples`
- **Premises:** occurrence conclusions are relative to actual derivations rooted in the exact production runtime or constructor.  The success chronology retains the route-specific calldata/model/SHA/gas/storage premises; constructor execution starts from empty target storage with an enabled undelegated warm SHA precompile and exact creation bytes.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`, `scripts/check-beacon-deposit-differential.sh`
- **Differential channel:** successful and chained deposit rows compare logical storage and logs while recording full SHA traces; the separate Prague creation measurement checks 31 SHA calls and exact constructor logical poststate for each artifact.
- **Non-claims:** same-frame instruction occurrence is not a whole-transaction authority theorem.  A reverting route may traverse a raw store later rolled back; retained-effect emptiness and raw-site absence are deliberately different claims.
- **Source:** `Blanc/BeaconDepositWriteSites.lean`, `Blanc/BeaconDepositSuccessChronology.lean`, `Blanc/BeaconDepositConstructorEffects.lean`

#### P6 — The compiled storage abstraction is established by construction, extended by successful deposits, and projects the model's exact count and mixed root

- **Declarations:** `Blanc.BeaconDeposit.constructorFinalStorage_artifactInv`, `Blanc.BeaconDeposit.deposit_success_artifactInv`, `Blanc.BeaconDeposit.ArtifactInv.root_eq_mixedRootOf`, `Blanc.BeaconDeposit.ArtifactInv.count_eq_history_length`
- **Premises:** construction uses the exact final storage; deposit preservation consumes an entry `ArtifactInv`, the exact compiled successful execution premises, and the same reconstructed deposit-data node used by the model.  Projection theorems consume `ArtifactInv stor history` rather than an unrelated poststate witness.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`, `scripts/check-beacon-deposit-differential.sh`
- **Differential channel:** `chained-deposits-1-through-8`, `root-readback`, `count-readback`, `seeded-cap-layouts`, and the constructor logical-state projection corroborate the abstraction at finite states on each side's own raw layout.
- **Non-claims:** the root equation is relative to `Bytes.sha256` and the witnessed list.  It establishes no inclusion proof, collision resistance, unique history, or raw-slot/storage-root equality.
- **Source:** `Blanc/BeaconDepositBridge.lean`, `Blanc/BeaconDepositBridgeCompiled.lean`, `Blanc/BeaconDepositSuccessStorageEffects.lean`

## Pillar — Deployment and open history

#### P7 — One exact configured Prague-only transition over the strict direct deployment envelope establishes the installed artifact, empty-history invariant, receipt, settlement, and constructor occurrence witnesses

- **Declarations:** `Blanc.BeaconDeposit.canonicalDeploymentStep_establishes_root`, `Blanc.BeaconDeposit.DeploymentRoot.constructorOccurrence`
- **Premises:** an explicit `CanonicalDeploymentBase`, exact strict singleton zero-value type-2 transaction/block envelope, derived sender/nonce target with collision freedom, state-neutral Prague system calls, direct CREATE gas/access/receipt conditions, and the actual `stateTransitionUsing (ChainConfig.pragueOnly chainId) ... = .ok deployed`; no deployed poststate or artifact invariant is assumed.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`, `scripts/check-beacon-deposit-deployment.sh`
- **Differential channel:** the independent deployment control authors one exact-gas singleton Prague block, checks 15 projections including installed runtime and all 31 storage words, replays it through Jaune, and requires wrong-target, wrong-runtime, and wrong-storage mutants to fail before green reversion.
- **Non-claims:** this is a direct singleton zero-value type-2 CREATE result.  There is no CREATE2, factory, proxy, or nonzero-endowment deployment; no co-block interaction, historical inclusion, signing, propagation, or other-fork result.
- **Source:** `Blanc/BeaconDepositDeploymentRoot.lean`, `Blanc/BeaconDepositDeploymentTransaction.lean`, `Blanc/BeaconDepositDeploymentBlock.lean`, `scripts/gen-beacon-deposit-deployment-fixture.py`

#### P8-FRAME — The exact compiled four-selector dispatcher preserves a baseline-relative history witness under trace-local fresh-frame and native-SHA admission

- **Declarations:** `Blanc.BeaconDeposit.historySpec_sound`, `Blanc.BeaconDeposit.historySpec_preserves`
- **Premises:** exact installed runtime through `ContractSpec`, the entry `ArtifactInv`/history prefix, fresh frame entry, and `NativeShaEntry` for actual admitted frame roots.  Success is inverted through the real ABI, guards, event, seven reconstruction calls, insertion loop, and `STATICCALL 0x2` settlement; read-only, malformed, error, selector-miss, child-failure, OOG, and rollback outcomes preserve storage/history.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`
- **Differential channel:** no direct finite channel — this is the proof-only open-frame theorem; the Prague hostile SHA/OOG rows corroborate selected concrete outcomes but are not used to establish or delimit preservation.
- **Non-claims:** native SHA admission is positive entry evidence, not a poststate or result-equivalent preservation premise.  The theorem does not quantify over delegated address-`0x2` code and introduces no blanket callback axiom.
- **Source:** `Blanc/BeaconDepositHistory.lean`, `Blanc/BeaconDepositSuccessSource.lean`, `Blanc/BeaconDepositHistorySound.lean`

#### P8-HISTORY — Every admitted Prague-only future extends the same baseline by one existential suffix, with an empty-baseline specialization rooted at deployment

- **Declarations:** `Blanc.BeaconDeposit.pragueOnly_history_extends`, `Blanc.BeaconDeposit.DeploymentRoot.future_history_extends`
- **Premises:** actual `BlockChain.ReachUsing` under the exact Prague-only schedule, a retained `ConfiguredHistoryTrace` projecting to that same reach witness, pointwise fresh/native-SHA frame admission, installed compiled runtime at the checkpoint, and its `ArtifactInv stor baseline`; the deployment specialization supplies installed code and `ArtifactInv _ []` from P7.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`
- **Differential channel:** no direct finite channel — arbitrary finite configured reachability and hostile outer frames are theorem scope, not extrapolated from the bounded Prague/BPO2 matrices.
- **Non-claims:** the suffix is existential and not transaction-indexed or unique.  Reachability does not say a deposit occurs, any strict increase eventually happens, or every environment admits native SHA evidence.
- **Source:** `Blanc/BeaconDepositHistoryChain.lean`, `Blanc/ExecutionHistoryAdmission.lean`, `Blanc/ExecutionTraceFresh.lean`

#### P8-READ — The deployment-rooted future witness simultaneously exposes exact concrete count, strictness iff its suffix is nonempty, and the mixed-root equation for that same suffix

- **Declarations:** `Blanc.BeaconDeposit.DeploymentRoot.future_count_root`
- **Premises:** the same deployment root, exact Prague-only reach witness, and retained native-SHA admission as P8-HISTORY.  Count and root are read from `future.state.getStor ca` through the single `ArtifactInv` carried by the one existential suffix.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`, `scripts/check-claims.sh`
- **Differential channel:** no direct finite channel — `chained-deposits-1-through-8` corroborates finite count/root readbacks, but the arbitrary-history conclusion and strictness equivalence are Lean-only.
- **Non-claims:** strictness is an equivalence about the witnessed suffix, not liveness or a transaction census.  The root equation does not assert inclusion, collision resistance, historical mainnet state, or a unique committed history.
- **Source:** `Blanc/BeaconDepositHistoryChain.lean`, `Blanc/BeaconDepositBridge.lean`
