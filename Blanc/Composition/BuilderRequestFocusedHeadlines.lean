import Blanc.Composition.BuilderRequestJointGFateFocused
import Blanc.Composition.BuilderRequestJointGRegistration
import Blanc.Composition.BuilderRequestJointGExitUnique
import Blanc.Composition.BuilderRequestJointGChargeOnce
import Blanc.Composition.BuilderRequestJointGDebitOnce
import Blanc.Composition.BuilderRequestJointGValue
import Blanc.Composition.BuilderRequestApplicability.Checks
import Blanc.Composition.Corpus.Proofs.BuilderCheckpoint

/-!
# Focused minimal-premise builder-request joint headlines and applicability bridges (`P2`, `P5`)

Goal `protocol-contract-corpus-v1` (rev 6, §14, Wave 3):

1. **P5 computational applicability bridges**: connects `Checks.FullCheckpointAt`,
   `Checks.ConfigBounds`, `Checks.RegistryBounds`, and `Checks.FiniteApplicability` to
   `ValidJointG` and `BuilderCheckpointObservation`.
2. **P2 focused minimal-premise corollaries**: factors the `ValidJointG` joint headlines into the
   exact execution and consensus premises each property actually consumes:
   - `full_output_focused`, `emitting_source_focused` (`ParentTied` only);
   - `deposit_position_focused`, `deposit_fate_focused`, `deposit_fate_no_pre_anchor_focused`
     (`ParentTied` + `Deposit.Indexed.Clean` only — no exit contract, consensus invariant, witness,
     config, registry, or balance-conservation premises);
   - `exit_position_focused`, `exit_fate_focused`, `exit_fate_no_pre_anchor_focused`
     (`ParentTied` + `Exit.Indexed.Clean` only — no deposit contract, `depositBudget`, consensus
     invariant, witness, config, registry, or balance-conservation premises);
   - `registration_authorization_focused` (`2 ≤ SLOTS_PER_EPOCH`, `bls = true`, `ParentTied`,
     `Deposit.Indexed.Clean`, `RegisteredRecordKept` — no exit contract or witness premises);
   - `exit_authorization_focused`, `exit_authorization_caller_focused` (`2 ≤ SLOTS_PER_EPOCH`,
     `ParentTied`, `Exit.Indexed.Clean` — no deposit contract, `bls = true`, consensus invariant,
     witness, or registry premises), and `exit_resolution_unique_focused` (adding only
     `Inv.BuilderPubkeysUnique D.preB`);
   - `slot_appended_at_most_once_focused`, `bid_appended_at_most_once_focused` (consensus-only
     `GJointRun` with `NoLiveWeightOnLatestBid`, `LatestBidCoherence`, `FutureEmpty` — zero
     execution or witness premises);
   - `deposit_value_focused` (execution-only `CodesKept` + `HistoryClean` + `HistoryRootsFit` +
     `NoSender` + `HistoryCreditsFit` — zero consensus run, `depositBudget`, or `exitFew` premises).
3. **`ValidJointG` compatibility bridges**: every original `ValidJointG.*` theorem signature is
   preserved untouched and recovered directly from its focused counterpart.
-/

namespace Blanc.Composition.BuilderRequestFocusedHeadlines

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts.Gloas
open Blanc.Lift.BuilderRequest
open ChainLink
open Blanc.Lift.BuilderRequest.Occurrence
open Blanc.Composition.BuilderRequestApplicability
open Blanc.Composition.BuilderRequestPublic
  (CodesKept depositAddr exitAddr keptAt feesPaidAt
   value_kept_bridge history_exit_source_bridge)
open Blanc.Corpus.Freeze.Builder (BuilderCheckpointObservation)

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## Section 1: P5 computational applicability bridges -/

/-- `Checks.stateValidatorCount` agrees definitionally by cases with `GJointState.validatorCount`. -/
theorem stateValidatorCount_eq (st : GJointState P) :
    Checks.stateValidatorCount st = st.validatorCount := by
  cases st <;> rfl

/-- `Checks.stateBuilderCount` agrees definitionally by cases with `GJointState.builderCount`. -/
theorem stateBuilderCount_eq (st : GJointState P) :
    Checks.stateBuilderCount st = st.builderCount := by
  cases st <;> rfl

/-- Every `ValidJointG` witness satisfies the computational `FullCheckpointAt` predicate. -/
theorem fullCheckpointAt_of_validJointG {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    Checks.FullCheckpointAt checkpoint :=
  ⟨v.noSystemCode, v.depositInstalled, v.depositFresh, v.exitInstalled, v.exitFresh⟩

/-- Every `BuilderCheckpointObservation` record satisfies the computational `FullCheckpointAt` predicate. -/
theorem fullCheckpointAt_of_observed {expectedStateRoot : B256} {checkpoint : BlockChain}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint) :
    Checks.FullCheckpointAt checkpoint :=
  ⟨obs.systemEmpty, obs.depositCode, obs.depositStorage, obs.exitCode, obs.exitStorage⟩

/-- Converse bridge: `FullCheckpointAt` supplies the five whole-account/storage equalities of `ValidJointG`. -/
theorem fullCheckpointAt_iff {checkpoint : BlockChain} :
    Checks.FullCheckpointAt checkpoint ↔
      checkpoint.state.getCode systemAddress = ByteArray.empty ∧
      checkpoint.state.getCode Deposit.Creation.address = Deposit.code ∧
      checkpoint.state.getStor Deposit.Creation.address = Stor.empty ∧
      checkpoint.state.getCode Exit.Creation.address = Exit.code ∧
      checkpoint.state.getStor Exit.Creation.address = Exit.deployedStorage :=
  Iff.rfl

/-- Every `ValidJointG` witness satisfies the computational `ConfigBounds` predicate. -/
theorem configBounds_of_validJointG {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    Checks.ConfigBounds P ccfg :=
  ⟨v.quorumPositive, v.inclusionDelay, v.exitDelayPos, v.exitDelayBelow, v.slotsPerEpoch⟩

/-- Equivalence between `Checks.RegistryBounds` and the `validatorsBound` / `buildersBound` fields of `ValidJointG`. -/
theorem registryBounds_iff_validJointG (states : List (GJointState P)) :
    Checks.RegistryBounds states ↔
      (∀ st ∈ states, st.validatorCount ≤ 2 ^ 40) ∧
      (∀ st ∈ states, st.builderCount ≤ 2 ^ 40) := by
  unfold Checks.RegistryBounds
  simp only [stateValidatorCount_eq, stateBuilderCount_eq]

/-- Every `ValidJointG` witness satisfies the computational `RegistryBounds` check over `v.run.states`. -/
theorem registryBounds_of_validJointG {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    Checks.RegistryBounds v.run.states :=
  (registryBounds_iff_validJointG v.run.states).mpr ⟨v.validatorsBound, v.buildersBound⟩

/-- Every `ValidJointG` witness satisfies the combined 12-field computational `FiniteApplicability` check. -/
theorem finiteApplicability_of_validJointG {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    Checks.FiniteApplicability ccfg checkpoint v.run.states :=
  ⟨fullCheckpointAt_of_validJointG v, configBounds_of_validJointG v, registryBounds_of_validJointG v⟩

/-! ## Section 2: Focused seam and positional clauses (`ParentTied` + single-contract `Clean`) -/

/-- Every step's pre-state is tied whenever the anchor is tied. -/
theorem pre_tied_focused {anchor final : GJointState P}
    (run : GJointRun cfg ccfg bls anchor final) (htied : ParentTied cfg anchor) {j : Nat}
    {D : GJointRunStep (P := P) cfg ccfg bls} (hD : run.steps[j]? = some D) :
    ParentTied cfg D.preState :=
  GJointRun.pre_of_post htied GJointRunStep.postState_tied run hD

/-- **Focused settled-payload request output.** Needs only `ParentTied cfg anchor` on the run. -/
theorem full_output_focused {anchor final : GJointState P}
    (run : GJointRun cfg ccfg bls anchor final) (htied : ParentTied cfg anchor) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (hD : run.steps[j]? = some (.gloas D))
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P} {post : BlockChain}
    (hs : D.settle = .full env req post) {b : KeptBlock} (hk : D.kept = [b]) :
    b.output.requests = Gloas.getExecutionRequestsList D.requests := by
  obtain ⟨-, hp, hreq, -⟩ := D.view.full_iff.mp hs
  have tied : ParentTied cfg (.gloas D.preB D.preExec D.preParent) := pre_tied_focused run htied hD
  rw [hp] at tied
  obtain ⟨hv, hx⟩ := tied
  obtain ⟨st, bout, hbody, hr, -⟩ := engineVerdictG_requests hv
  obtain ⟨b', hb', hblk, hf'⟩ := D.kept_of_full hs
  rw [hk] at hb'
  obtain rfl := List.head_eq_of_cons_eq hb'
  have hkh := D.keptHistory
  rw [hk] at hkh
  obtain ⟨hnil, step⟩ := KeptHistory.snoc_inv (blocks := []) hkh
  have hpar := KeptHistory.nil_inv hnil
  have happ := step.body.applied
  simp only [KeptBlock.benv, hpar, hf', hblk] at happ
  rw [hbody] at happ
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj happ)
  rw [hr, hx]
  exact congrArg _ hreq.symm

/-- Focused payload block lookup in `preBlocks ++ run.blocks`. -/
theorem blocks_getElem?_full_focused (preBlocks : List KeptBlock) {anchor final : GJointState P}
    (run : GJointRun cfg ccfg bls anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (hD : run.steps[j]? = some (.gloas D)) {b : KeptBlock}
    (hk : D.kept = [b]) :
    (preBlocks ++ run.blocks)[preBlocks.length + run.payloadIndex j]? = some b := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact run.blocks_getElem?_payloadIndex hD hk

/-- Two FULL Gloas steps at the same payload index are the same step. -/
theorem full_step_unique_focused {anchor final : GJointState P}
    (run : GJointRun cfg ccfg bls anchor final) {j j' : Nat}
    {D D' : GloasStepData (P := P) cfg ccfg bls} (hD : run.steps[j]? = some (.gloas D))
    (hD' : run.steps[j']? = some (.gloas D')) {b b' : KeptBlock} (hk : D.kept = [b]) (hk' : D'.kept = [b'])
    (he : run.payloadIndex j = run.payloadIndex j') : j = j' :=
  run.eq_of_payloadIndex_eq hD hD'
    (by simp only [GJointRunStep.kept, hk]; exact List.cons_ne_nil _ _)
    (by simp only [GJointRunStep.kept, hk']; exact List.cons_ne_nil _ _) he

/-- **Focused emitting-block source.** Needs only `ParentTied cfg anchor` and covered-fork silence. -/
theorem emitting_source_focused (preBlocks : List KeptBlock) {anchor final : GJointState P}
    (run : GJointRun cfg ccfg bls anchor final) (htied : ParentTied cfg anchor)
    {c : Delivery.Contract} {R : Reading c} {ty : UInt8}
    (hcov : ∀ b ∈ preBlocks ++ run.blocks, b.fork ≠ .amsterdam → blockEmissions R ty b = [])
    {bj k : Nat} (hbj : bj < (preBlocks ++ run.blocks).length) (hpre : preBlocks.length ≤ bj)
    (hk : k < (blockEmissions R ty (preBlocks ++ run.blocks)[bj]).length) :
    ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (env : Gloas.SignedExecutionPayloadEnvelope P)
      (req : Gloas.NewPayloadRequest P) (post : BlockChain),
      run.steps[j]? = some (.gloas D) ∧ D.settle = .full env req post ∧
      run.payloadIndex j = bj - preBlocks.length ∧ D.kept = [(preBlocks ++ run.blocks)[bj]] ∧
      (preBlocks ++ run.blocks)[bj].output.requests = Gloas.getExecutionRequestsList D.requests := by
  have hi : bj - preBlocks.length < run.blocks.length := by
    have : (preBlocks ++ run.blocks).length = preBlocks.length + run.blocks.length := List.length_append
    omega
  have hget : (preBlocks ++ run.blocks)[bj] = run.blocks[bj - preBlocks.length] :=
    List.getElem_append_right hpre
  obtain ⟨j, hj, hsrc⟩ := run.block_source hi
  rcases hsrc with ⟨D, -, hf⟩ | ⟨D, env, req, post, hD, hs, hk'⟩
  · rw [← hget] at hf
    rw [hcov _ (List.getElem_mem hbj) hf] at hk
    exact absurd hk (Nat.not_lt_zero _)
  · rw [← hget] at hk'
    exact ⟨j, D, env, req, post, hD, hs, hj, hk', full_output_focused run htied hD hs hk'⟩

/-- Covered-fork deposit silence under `Deposit.Indexed.Clean` alone. -/
theorem deposit_covered_focused {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    (hclean : Deposit.Indexed.Clean cfg checkpoint blocks stop) :
    ∀ b ∈ blocks, b.fork ≠ .amsterdam → Deposit.Indexed.blockEmissions b = [] := fun b hb hf => by
  obtain ⟨pre, post, split⟩ := List.append_of_mem hb
  exact ((Deposit.Indexed.history_block hclean split).2.1 hf).1

/-- Covered-fork exit silence under `Exit.Indexed.Clean` alone. -/
theorem exit_covered_focused {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    (hclean : Exit.Indexed.Clean cfg checkpoint blocks stop) :
    ∀ b ∈ blocks, b.fork ≠ .amsterdam → Exit.Indexed.blockEmissions b = [] := fun b hb hf => by
  obtain ⟨pre, post, split⟩ := List.append_of_mem hb
  exact ((Exit.Indexed.history_block hclean split).2.1 hf).1

/-- **Focused B1 positional clause.** Depends only on `ParentTied cfg anchor` and `Deposit.Indexed.Clean`. -/
theorem deposit_position_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (htied : ParentTied cfg anchor)
    (hclean : Deposit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (hD : run.steps[j]? = some (.gloas D))
    {k : Nat} {req : Gloas.BuilderDepositRequest} (hreq : D.builderDeposits[k]? = some req) :
    D.isFull ∧ ∃ bi b, run.payloadIndex j = bi ∧
      (preBlocks ++ run.blocks)[preBlocks.length + bi]? = some b ∧
      (Deposit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
      (Deposit.Indexed.submissions (preBlocks ++ run.blocks))[(Deposit.Indexed.emissions
        ((preBlocks ++ run.blocks).take (preBlocks.length + bi))).length + k]? = some (Ssz.serialize req) := by
  obtain ⟨env, r, post, hs⟩ := D.view.full_of_requests (Or.inl (by
    intro h
    change D.builderDeposits = [] at h
    rw [h, List.getElem?_nil] at hreq
    cases hreq))
  obtain ⟨b, hk, -, -⟩ := D.kept_of_full hs
  have hem := RequestCodecG.deposit_blockEmissions (full_output_focused run htied hD hs hk)
  have hek : (Deposit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) := by
    rw [hem, List.getElem?_map, hreq]
    rfl
  refine ⟨⟨env, r, post, hs⟩, _, b, rfl, blocks_getElem?_full_focused preBlocks run hD hk, hek, ?_⟩
  exact Occurrence.submission_of_emission Deposit.Indexed.reading Deposit.linked hclean.premises
    Deposit.Indexed.start_queue (blocks_getElem?_full_focused preBlocks run hD hk) hek

/-- **Focused B3 positional clause.** Depends only on `ParentTied cfg anchor` and `Exit.Indexed.Clean`. -/
theorem exit_position_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (htied : ParentTied cfg anchor)
    (hclean : Exit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (hD : run.steps[j]? = some (.gloas D))
    {k : Nat} {req : Gloas.BuilderExitRequest} (hreq : D.builderExits[k]? = some req) :
    D.isFull ∧ ∃ bi b, run.payloadIndex j = bi ∧
      (preBlocks ++ run.blocks)[preBlocks.length + bi]? = some b ∧
      (Exit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
      (Exit.Indexed.submissions (preBlocks ++ run.blocks))[(Exit.Indexed.emissions
        ((preBlocks ++ run.blocks).take (preBlocks.length + bi))).length + k]? = some (Ssz.serialize req) := by
  obtain ⟨env, r, post, hs⟩ := D.view.full_of_requests (Or.inr (by
    intro h
    change D.builderExits = [] at h
    rw [h, List.getElem?_nil] at hreq
    cases hreq))
  obtain ⟨b, hk, -, -⟩ := D.kept_of_full hs
  have hem := RequestCodecG.exit_blockEmissions (full_output_focused run htied hD hs hk)
  have hek : (Exit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) := by
    rw [hem, List.getElem?_map, hreq]
    rfl
  refine ⟨⟨env, r, post, hs⟩, _, b, rfl, blocks_getElem?_full_focused preBlocks run hD hk, hek, ?_⟩
  exact Occurrence.submission_of_emission Exit.Indexed.reading Exit.linked hclean.premises
    Exit.Indexed.start_queue (blocks_getElem?_full_focused preBlocks run hD hk) hek

/-! ## Section 3: Focused B2/B4 deposit and exit fate -/

/-- **Focused B2 deposit fate (`P2`).** Uses only `ParentTied cfg anchor` and `Deposit.Indexed.Clean`
(no exit contract premises, no `exitFew`, no consensus state invariants, witnesses, config, registry,
or value-conservation fields). -/
theorem deposit_fate_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (htied : ParentTied cfg anchor)
    (hclean : Deposit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    {n : Nat} (_hn : n < (Deposit.Indexed.submissions (preBlocks ++ run.blocks)).length) :
    (n < (Deposit.Indexed.emissions preBlocks).length ∧
      (Deposit.Indexed.emissions preBlocks)[n]? =
        (Deposit.Indexed.submissions (preBlocks ++ run.blocks))[n]?) ∨
    ((Deposit.Indexed.emissions preBlocks).length ≤ n ∧
      n < (Deposit.Indexed.emissions (preBlocks ++ run.blocks)).length ∧
      ∃ bj k, ∃ hbj : bj < (preBlocks ++ run.blocks).length,
        k < (Deposit.Indexed.blockEmissions (preBlocks ++ run.blocks)[bj]).length ∧
        (Deposit.Indexed.emissions ((preBlocks ++ run.blocks).take bj)).length + k = n ∧
        (Deposit.Indexed.blockEmissions (preBlocks ++ run.blocks)[bj])[k]? =
          (Deposit.Indexed.submissions (preBlocks ++ run.blocks))[n]? ∧
        preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderDepositRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ run.payloadIndex j = bj - preBlocks.length ∧
        D.builderDeposits[k]? = some req ∧
        Ssz.serialize req = (Deposit.Indexed.submissions (preBlocks ++ run.blocks))[n]! ∧
        builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderDeposit ccfg bls m req = .ok o ∧
          (∀ o', classifyBuilderDeposit ccfg bls m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderDepositOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req',
            run.steps[j']? = some (.gloas D') →
            D'.builderDeposits[k']? = some req' →
            (Deposit.Indexed.emissions
              ((preBlocks ++ run.blocks).take (preBlocks.length + run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Deposit.Indexed.emissions (preBlocks ++ run.blocks)).length ≤ n ∧
      (Deposit.Indexed.remainingQueue final.exec)[n -
        (Deposit.Indexed.emissions (preBlocks ++ run.blocks)).length]? =
        (Deposit.Indexed.submissions (preBlocks ++ run.blocks))[n]?) := by
  have fifo := Deposit.Indexed.history_fifo hclean
  have fate := Occurrence.history_fate Deposit.Indexed.reading Deposit.linked hclean.premises n
  rw [Deposit.Indexed.start_queue, List.nil_append] at fate
  have hpre : (preBlocks ++ run.blocks).take preBlocks.length = preBlocks := List.take_left' rfl
  have hemis : Deposit.Indexed.emissions (preBlocks ++ run.blocks) =
      Deposit.Indexed.emissions preBlocks ++ Deposit.Indexed.emissions run.blocks :=
    emissions_append _ _ _
  rcases fate with ⟨hE, bj, k, hbj, hk, pos, get, anchorIff, uniq⟩ | ⟨hE, hq⟩
  · by_cases ha : n < (Deposit.Indexed.emissions preBlocks).length
    · left
      refine ⟨ha, ?_⟩
      rw [fifo, List.getElem?_append_left hE]
      show _ = (Deposit.Indexed.emissions (preBlocks ++ run.blocks))[n]?
      rw [hemis, List.getElem?_append_left ha]
    · right; left
      have hge : preBlocks.length ≤ bj := by
        by_contra hlt
        have := (anchorIff preBlocks.length).mp (by omega)
        rw [hpre] at this
        exact ha this
      obtain ⟨j, D, env, req, post, hD, hs, hidx, hkD, hout⟩ :=
        emitting_source_focused preBlocks run htied (deposit_covered_focused hclean) hbj hge hk
      have hem : blockEmissions Deposit.Indexed.reading 3 (preBlocks ++ run.blocks)[bj] =
          D.requests.builder_deposits.toArray.toList.map Ssz.serialize :=
        RequestCodecG.deposit_blockEmissions hout
      have hkl : k < D.builderDeposits.length := by
        have := hk
        rw [hem, List.length_map] at this
        exact this
      obtain ⟨req0, hreq0⟩ : ∃ r, D.builderDeposits[k]? = some r := ⟨_, List.getElem?_eq_getElem hkl⟩
      have hser : (submissions Deposit.contract (preBlocks ++ run.blocks))[n]? =
          some (Ssz.serialize req0) := by
        rw [← get, hem, List.getElem?_map, hreq0]
        rfl
      obtain ⟨-, -, -, tr, m, m', o, -, -, -, -, -, htr, hm, hc, hu, hm', happ⟩ :=
        D.view.builderDeposit_applied hreq0
      refine ⟨Nat.le_of_not_lt ha, hE, bj, k, hbj, hk, pos, get, hge, j, D, req0, tr, m, hD,
        ⟨env, req, post, hs⟩, hidx, hreq0, ?_, htr, hm, o, hc, hu, m', hm', happ, ?_⟩
      · show _ = (submissions Deposit.contract (preBlocks ++ run.blocks))[n]!
        rw [List.getElem!_eq_getElem?_getD, hser]
        rfl
      · intro j' k' D' r' hD' hr' pos'
        obtain ⟨env2, req2, post2, -, -, -, -, hs2, -, -, -, -, -, -, -, -, -, -⟩ :=
          D'.view.builderDeposit_applied hr'
        obtain ⟨b', hb', -, -⟩ := D'.kept_of_full hs2
        have hem' : blockEmissions Deposit.Indexed.reading 3 b' =
            D'.requests.builder_deposits.toArray.toList.map Ssz.serialize :=
          RequestCodecG.deposit_blockEmissions (full_output_focused run htied hD' hs2 hb')
        obtain ⟨hi', hbi⟩ := List.getElem?_eq_some_iff.mp
          (blocks_getElem?_full_focused preBlocks run hD' hb')
        have hk' : k' < (blockEmissions Deposit.Indexed.reading 3
            (preBlocks ++ run.blocks)[preBlocks.length + run.payloadIndex j']).length := by
          rw [hbi, hem', List.length_map]
          exact (List.getElem?_eq_some_iff.mp hr').1
        obtain ⟨h1, rfl⟩ := uniq _ k' hi' hk' pos'
        exact ⟨(full_step_unique_focused run hD hD' hkD hb' (by omega)).symm, rfl⟩
  · right; right
    exact ⟨hE, hq⟩

/-- Focused deposit fate when `preBlocks` contains no Amsterdam block. -/
theorem deposit_fate_no_pre_anchor_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (htied : ParentTied cfg anchor)
    (hclean : Deposit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    (noAmsterdam : ∀ b ∈ preBlocks, b.fork ≠ .amsterdam)
    {n : Nat} (hn : n < (Deposit.Indexed.submissions (preBlocks ++ run.blocks)).length) :
    ((Deposit.Indexed.emissions preBlocks).length ≤ n ∧
      n < (Deposit.Indexed.emissions (preBlocks ++ run.blocks)).length ∧
      ∃ bj k, ∃ hbj : bj < (preBlocks ++ run.blocks).length,
        k < (Deposit.Indexed.blockEmissions (preBlocks ++ run.blocks)[bj]).length ∧
        (Deposit.Indexed.emissions ((preBlocks ++ run.blocks).take bj)).length + k = n ∧
        (Deposit.Indexed.blockEmissions (preBlocks ++ run.blocks)[bj])[k]? =
          (Deposit.Indexed.submissions (preBlocks ++ run.blocks))[n]? ∧
        preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderDepositRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ run.payloadIndex j = bj - preBlocks.length ∧
        D.builderDeposits[k]? = some req ∧
        Ssz.serialize req = (Deposit.Indexed.submissions (preBlocks ++ run.blocks))[n]! ∧
        builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderDeposit ccfg bls m req = .ok o ∧
          (∀ o', classifyBuilderDeposit ccfg bls m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderDepositOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req',
            run.steps[j']? = some (.gloas D') →
            D'.builderDeposits[k']? = some req' →
            (Deposit.Indexed.emissions
              ((preBlocks ++ run.blocks).take (preBlocks.length + run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Deposit.Indexed.emissions (preBlocks ++ run.blocks)).length ≤ n ∧
      (Deposit.Indexed.remainingQueue final.exec)[n -
        (Deposit.Indexed.emissions (preBlocks ++ run.blocks)).length]? =
        (Deposit.Indexed.submissions (preBlocks ++ run.blocks))[n]?) := by
  have hnil : Deposit.Indexed.emissions preBlocks = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro b hb
    exact deposit_covered_focused hclean b (List.mem_append_left _ hb) (noAmsterdam b hb)
  rcases deposit_fate_focused run htied hclean hn with ⟨before, -⟩ | later
  · rw [hnil, List.length_nil] at before
    exact (Nat.not_lt_zero _ before).elim
  · exact later

/-- **Focused B4 exit fate (`P2`).** Uses only `ParentTied cfg anchor` and `Exit.Indexed.Clean`
(no deposit contract premises, no `depositBudget`, no consensus state invariants, witnesses,
config, registry, or value-conservation fields). -/
theorem exit_fate_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (htied : ParentTied cfg anchor)
    (hclean : Exit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    {n : Nat} (_hn : n < (Exit.Indexed.submissions (preBlocks ++ run.blocks)).length) :
    (n < (Exit.Indexed.emissions preBlocks).length ∧
      (Exit.Indexed.emissions preBlocks)[n]? =
        (Exit.Indexed.submissions (preBlocks ++ run.blocks))[n]?) ∨
    ((Exit.Indexed.emissions preBlocks).length ≤ n ∧
      n < (Exit.Indexed.emissions (preBlocks ++ run.blocks)).length ∧
      ∃ bj k, ∃ hbj : bj < (preBlocks ++ run.blocks).length,
        k < (Exit.Indexed.blockEmissions (preBlocks ++ run.blocks)[bj]).length ∧
        (Exit.Indexed.emissions ((preBlocks ++ run.blocks).take bj)).length + k = n ∧
        (Exit.Indexed.blockEmissions (preBlocks ++ run.blocks)[bj])[k]? =
          (Exit.Indexed.submissions (preBlocks ++ run.blocks))[n]? ∧
        preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderExitRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ run.payloadIndex j = bj - preBlocks.length ∧
        D.builderExits[k]? = some req ∧
        Ssz.serialize req = (Exit.Indexed.submissions (preBlocks ++ run.blocks))[n]! ∧
        builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderExit ccfg m req = .ok o ∧
          (∀ o', classifyBuilderExit ccfg m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderExitOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req',
            run.steps[j']? = some (.gloas D') →
            D'.builderExits[k']? = some req' →
            (Exit.Indexed.emissions
              ((preBlocks ++ run.blocks).take (preBlocks.length + run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Exit.Indexed.emissions (preBlocks ++ run.blocks)).length ≤ n ∧
      (Exit.Indexed.remainingQueue final.exec)[n -
        (Exit.Indexed.emissions (preBlocks ++ run.blocks)).length]? =
        (Exit.Indexed.submissions (preBlocks ++ run.blocks))[n]?) := by
  have fifo := Exit.Indexed.history_fifo hclean
  have fate := Occurrence.history_fate Exit.Indexed.reading Exit.linked hclean.premises n
  rw [Exit.Indexed.start_queue, List.nil_append] at fate
  have hpre : (preBlocks ++ run.blocks).take preBlocks.length = preBlocks := List.take_left' rfl
  have hemis : Exit.Indexed.emissions (preBlocks ++ run.blocks) =
      Exit.Indexed.emissions preBlocks ++ Exit.Indexed.emissions run.blocks :=
    emissions_append _ _ _
  rcases fate with ⟨hE, bj, k, hbj, hk, pos, get, anchorIff, uniq⟩ | ⟨hE, hq⟩
  · by_cases ha : n < (Exit.Indexed.emissions preBlocks).length
    · left
      refine ⟨ha, ?_⟩
      rw [fifo, List.getElem?_append_left hE]
      show _ = (Exit.Indexed.emissions (preBlocks ++ run.blocks))[n]?
      rw [hemis, List.getElem?_append_left ha]
    · right; left
      have hge : preBlocks.length ≤ bj := by
        by_contra hlt
        have := (anchorIff preBlocks.length).mp (by omega)
        rw [hpre] at this
        exact ha this
      obtain ⟨j, D, env, req, post, hD, hs, hidx, hkD, hout⟩ :=
        emitting_source_focused preBlocks run htied (exit_covered_focused hclean) hbj hge hk
      have hem : blockEmissions Exit.Indexed.reading 4 (preBlocks ++ run.blocks)[bj] =
          D.requests.builder_exits.toArray.toList.map Ssz.serialize :=
        RequestCodecG.exit_blockEmissions hout
      have hkl : k < D.builderExits.length := by
        have := hk
        rw [hem, List.length_map] at this
        exact this
      obtain ⟨req0, hreq0⟩ : ∃ r, D.builderExits[k]? = some r := ⟨_, List.getElem?_eq_getElem hkl⟩
      have hser : (submissions Exit.contract (preBlocks ++ run.blocks))[n]? =
          some (Ssz.serialize req0) := by
        rw [← get, hem, List.getElem?_map, hreq0]
        rfl
      obtain ⟨-, -, -, tr, m, m', o, -, -, -, -, -, htr, hm, hc, hu, hm', happ⟩ :=
        D.view.builderExit_applied hreq0
      refine ⟨Nat.le_of_not_lt ha, hE, bj, k, hbj, hk, pos, get, hge, j, D, req0, tr, m, hD,
        ⟨env, req, post, hs⟩, hidx, hreq0, ?_, htr, hm, o, hc, hu, m', hm', happ, ?_⟩
      · show _ = (submissions Exit.contract (preBlocks ++ run.blocks))[n]!
        rw [List.getElem!_eq_getElem?_getD, hser]
        rfl
      · intro j' k' D' r' hD' hr' pos'
        obtain ⟨env2, req2, post2, -, -, -, -, hs2, -, -, -, -, -, -, -, -, -, -⟩ :=
          D'.view.builderExit_applied hr'
        obtain ⟨b', hb', -, -⟩ := D'.kept_of_full hs2
        have hem' : blockEmissions Exit.Indexed.reading 4 b' =
            D'.requests.builder_exits.toArray.toList.map Ssz.serialize :=
          RequestCodecG.exit_blockEmissions (full_output_focused run htied hD' hs2 hb')
        obtain ⟨hi', hbi⟩ := List.getElem?_eq_some_iff.mp
          (blocks_getElem?_full_focused preBlocks run hD' hb')
        have hk' : k' < (blockEmissions Exit.Indexed.reading 4
            (preBlocks ++ run.blocks)[preBlocks.length + run.payloadIndex j']).length := by
          rw [hbi, hem', List.length_map]
          exact (List.getElem?_eq_some_iff.mp hr').1
        obtain ⟨h1, rfl⟩ := uniq _ k' hi' hk' pos'
        exact ⟨(full_step_unique_focused run hD hD' hkD hb' (by omega)).symm, rfl⟩
  · right; right
    exact ⟨hE, hq⟩

/-- Focused exit fate when `preBlocks` contains no Amsterdam block. -/
theorem exit_fate_no_pre_anchor_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (htied : ParentTied cfg anchor)
    (hclean : Exit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    (noAmsterdam : ∀ b ∈ preBlocks, b.fork ≠ .amsterdam)
    {n : Nat} (hn : n < (Exit.Indexed.submissions (preBlocks ++ run.blocks)).length) :
    ((Exit.Indexed.emissions preBlocks).length ≤ n ∧
      n < (Exit.Indexed.emissions (preBlocks ++ run.blocks)).length ∧
      ∃ bj k, ∃ hbj : bj < (preBlocks ++ run.blocks).length,
        k < (Exit.Indexed.blockEmissions (preBlocks ++ run.blocks)[bj]).length ∧
        (Exit.Indexed.emissions ((preBlocks ++ run.blocks).take bj)).length + k = n ∧
        (Exit.Indexed.blockEmissions (preBlocks ++ run.blocks)[bj])[k]? =
          (Exit.Indexed.submissions (preBlocks ++ run.blocks))[n]? ∧
        preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderExitRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ run.payloadIndex j = bj - preBlocks.length ∧
        D.builderExits[k]? = some req ∧
        Ssz.serialize req = (Exit.Indexed.submissions (preBlocks ++ run.blocks))[n]! ∧
        builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderExit ccfg m req = .ok o ∧
          (∀ o', classifyBuilderExit ccfg m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderExitOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req',
            run.steps[j']? = some (.gloas D') →
            D'.builderExits[k']? = some req' →
            (Exit.Indexed.emissions
              ((preBlocks ++ run.blocks).take (preBlocks.length + run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Exit.Indexed.emissions (preBlocks ++ run.blocks)).length ≤ n ∧
      (Exit.Indexed.remainingQueue final.exec)[n -
        (Exit.Indexed.emissions (preBlocks ++ run.blocks)).length]? =
        (Exit.Indexed.submissions (preBlocks ++ run.blocks))[n]?) := by
  have hnil : Exit.Indexed.emissions preBlocks = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro b hb
    exact exit_covered_focused hclean b (List.mem_append_left _ hb) (noAmsterdam b hb)
  rcases exit_fate_focused run htied hclean hn with ⟨before, -⟩ | later
  · rw [hnil, List.length_nil] at before
    exact (Nat.not_lt_zero _ before).elim
  · exact later

/-! ## Section 4: Focused B1/B3/B4 authorization and unique resolution -/

/-- **Focused B1 registration authorization (`P2`).** Consumes only `2 ≤ P.SLOTS_PER_EPOCH`,
`bls = true`, `ParentTied cfg anchor`, `Deposit.Indexed.Clean`, and `RegisteredRecordKept run`. -/
theorem registration_authorization_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (hspe : 2 ≤ P.SLOTS_PER_EPOCH) (hbls : bls = true) (htied : ParentTied cfg anchor)
    (hclean : Deposit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    (hkept : RegisteredRecordKept run)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : run.steps[j]? = some (.gloas D))
    {i : Nat} (created : BuilderCreated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderDepositRequest) (tr : List (Gloas.BeaconState P))
      (m m' : Gloas.BeaconState P) (amount : Gwei) (dom : Domain) (addr : ExecutionAddress) (e : Epoch),
      D.builderDeposits[k]? = some req ∧
      builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
      classifyBuilderDeposit ccfg bls m req = .ok (.register i amount) ∧ amount = req.amount ∧
      (D.isFull ∧ ∃ bi b, run.payloadIndex j = bi ∧
        (preBlocks ++ run.blocks)[preBlocks.length + bi]? = some b ∧
        (Deposit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
        (Deposit.Indexed.submissions (preBlocks ++ run.blocks))[(Deposit.Indexed.emissions
          ((preBlocks ++ run.blocks).take (preBlocks.length + bi))).length + k]? =
          some (Ssz.serialize req)) ∧
      req.withdrawal_credentials.toBytes.head? = some 0xB0 ∧
      builderDepositDomain ccfg = some dom ∧
      blsVerify true req.pubkey (computeSigningRoot (builderDepositMessage req) dom) req.signature = true ∧
      Jaune.Bytes.toAdr? (req.withdrawal_credentials.toBytes.drop 12) = some addr ∧
      computeEpochAtSlot P m.slot = .ok e ∧
      m'.builders.toArray[i]? = some (freshBuilder req.pubkey addr req.amount e) ∧
      ∃ b' : Gloas.Builder, D.postB.builders.toArray[i]? = some b' ∧
        b'.pubkey = req.pubkey ∧ b'.version = Gloas.PAYLOAD_BUILDER_VERSION ∧ b'.execution_address = addr ∧
        b'.deposit_epoch = e ∧ b'.withdrawable_epoch = FAR_FUTURE_EPOCH ∧
        b'.balance.toNat = req.amount.toNat +
          (((D.builderDeposits.drop (k + 1)).filter (fun r' => r'.pubkey == req.pubkey &&
            Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials)).map (·.amount.toNat)).sum := by
  subst hbls
  have hcr : BuilderCreated D.view.postSlots D.postB i := by
    unfold BuilderCreated at created ⊢
    change (D.postB.builders.toArray[i]?).isSome ∧
      (D.postSlots.builders.toArray[i]?).map (·.pubkey) ≠ (D.postB.builders.toArray[i]?).map (·.pubkey)
    rw [Inv.processSlots_identityStable D.slots]
    exact created
  obtain ⟨k, req, tr, m, m', dom, addr, e, bal, hreq, htr, hm, hm', -, hcl, hpre, hdom, hv, haddr, he, hat,
    hlast, hbal⟩ := D.view.registration hspe hcr
  have hpost := hkept stepD htr created
  change (traceLast D.postSlots tr).builders.toArray[i]? = _ at hlast
  rw [hlast] at hpost
  refine ⟨k, req, tr, m, m', req.amount, dom, addr, e, hreq, htr, hm, hm', hcl, rfl,
    deposit_position_focused run htied hclean stepD hreq,
    hpre, hdom, hv, haddr, he, hat, _, hpost, rfl, rfl, rfl, rfl, rfl, hbal⟩

/-- **Focused B3 exit authorization (`P2`).** Consumes only `2 ≤ P.SLOTS_PER_EPOCH`,
`ParentTied cfg anchor`, and `Exit.Indexed.Clean` (any `bls`, no deposit contract, witness,
invariant, or registry premises). -/
theorem exit_authorization_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (hspe : 2 ≤ P.SLOTS_PER_EPOCH) (htied : ParentTied cfg anchor)
    (hclean : Exit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : run.steps[j]? = some (.gloas D))
    {i : Nat} (initiated : ExitInitiated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderExitRequest) (tr : List (Gloas.BeaconState P)) (m m' : Gloas.BeaconState P),
      D.builderExits[k]? = some req ∧
      builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
      classifyBuilderExit ccfg m req = .ok (.initiate i) ∧
      (D.isFull ∧ ∃ bi b, run.payloadIndex j = bi ∧
        (preBlocks ++ run.blocks)[preBlocks.length + bi]? = some b ∧
        (Exit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
        (Exit.Indexed.submissions (preBlocks ++ run.blocks))[(Exit.Indexed.emissions
          ((preBlocks ++ run.blocks).take (preBlocks.length + bi))).length + k]? =
          some (Ssz.serialize req)) ∧
      firstMatch m.builders req.pubkey = some i ∧
      (∃ (b : Gloas.Builder) (bi : Gloas.BuilderIndex), m.builders.toArray[i]? = some b ∧
        b.execution_address = req.source_address ∧ U64.ofNat? i "BuilderIndex" = .ok bi ∧
        Gloas.isActiveBuilder m bi = .ok true) ∧
      (Ssz.serialize req).take 20 = req.source_address.toBytes ∧
      ∃ (r : Exit.Record) (f : Exec.Frame), f ∈ keptAt (preBlocks ++ run.blocks) exitAddr ∧
        submittedBy Exit.contract f = some r ∧ Ssz.serialize req = Exit.Record.out r ∧
        r.source = f.sevm.caller := by
  have hin : ExitInitiated D.view.postSlots D.postB i :=
    (exitInitiated_congr_left D.postSlots_builders).mpr initiated
  obtain ⟨k, req, tr, m, m', hreq, htr, hm, hm', -, hcl⟩ := D.view.exitInitiated hspe hin
  have hpos := exit_position_focused run htied hclean stepD hreq
  obtain ⟨-, -, -, -, -, hinit, -⟩ := classifyBuilderExit_meaning hcl
  obtain ⟨b, bi, hfm, hb, hbi, hact, haddr, -⟩ := (hinit i).mp rfl
  have hlen : req.source_address.toBytes.length = 20 := by
    simp only [Adr.toBytes, List.length_append, UInt32.length_toBytes, B128.length_toBytes]
  refine ⟨k, req, tr, m, m', hreq, htr, hm, hm', hcl, hpos, hfm, ⟨b, bi, hb, haddr, hbi, hact⟩, ?_, ?_⟩
  · rw [RequestCodecG.serialize_builderExitRequest]
    exact List.take_left' hlen
  · obtain ⟨-, bj, -, -, -, -, hsub⟩ := hpos
    simp only [Exit.Indexed.submissions, Occurrence.submissions, List.getElem?_map] at hsub
    cases hr : (History.submitted Exit.contract (preBlocks ++ run.blocks))[(Exit.Indexed.emissions
        ((preBlocks ++ run.blocks).take (preBlocks.length + bj))).length + k]? with
    | none => rw [hr] at hsub; cases hsub
    | some r =>
      rw [hr] at hsub
      have hout : Exit.Record.out r = Ssz.serialize req := Option.some.inj hsub
      obtain ⟨f, hf, hsf⟩ := List.mem_filterMap.mp (List.mem_of_getElem? hr)
      exact ⟨r, f, hf, hsf, hout.symm, (history_exit_source_bridge hf hsf).1⟩

/-- **Focused B3 exit authorization with caller identity (`P2`).** -/
theorem exit_authorization_caller_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (hspe : 2 ≤ P.SLOTS_PER_EPOCH) (htied : ParentTied cfg anchor)
    (hclean : Exit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : run.steps[j]? = some (.gloas D))
    {i : Nat} (initiated : ExitInitiated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderExitRequest) (tr : List (Gloas.BeaconState P)) (m m' : Gloas.BeaconState P),
      D.builderExits[k]? = some req ∧
      builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
      classifyBuilderExit ccfg m req = .ok (.initiate i) ∧
      (D.isFull ∧ ∃ bi b, run.payloadIndex j = bi ∧
        (preBlocks ++ run.blocks)[preBlocks.length + bi]? = some b ∧
        (Exit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
        (Exit.Indexed.submissions (preBlocks ++ run.blocks))[(Exit.Indexed.emissions
          ((preBlocks ++ run.blocks).take (preBlocks.length + bi))).length + k]? =
          some (Ssz.serialize req)) ∧
      firstMatch m.builders req.pubkey = some i ∧
      (∃ (b : Gloas.Builder) (bi : Gloas.BuilderIndex), m.builders.toArray[i]? = some b ∧
        b.execution_address = req.source_address ∧ U64.ofNat? i "BuilderIndex" = .ok bi ∧
        Gloas.isActiveBuilder m bi = .ok true) ∧
      (Ssz.serialize req).take 20 = req.source_address.toBytes ∧
      ∃ (r : Exit.Record) (f : Exec.Frame), f ∈ keptAt (preBlocks ++ run.blocks) exitAddr ∧
        submittedBy Exit.contract f = some r ∧ Ssz.serialize req = Exit.Record.out r ∧
        r.source = f.sevm.caller ∧ req.source_address = f.sevm.caller := by
  obtain ⟨k, req, tr, m, m', hreq, htr, hm, hm', hcl, hpos, hfm, hb, htake, r, f, hf, hsub, hout, hsrc⟩ :=
    exit_authorization_focused run hspe htied hclean stepD initiated
  refine ⟨k, req, tr, m, m', hreq, htr, hm, hm', hcl, hpos, hfm, hb, htake, r, f, hf, hsub, hout, hsrc, ?_⟩
  have hlen : r.source.toBytes.length = 20 := by
    simp only [Adr.toBytes, List.length_append, UInt32.length_toBytes, B128.length_toBytes]
  have h20 : (Ssz.serialize req).take 20 = r.source.toBytes := by
    rw [hout]; unfold Exit.Record.out; exact List.take_left' hlen
  rw [← hsrc]
  exact Blanc.ConsensusSsz.adr_toBytes_injective (htake.symm.trans h20)

/-- **Focused B4 unique exit resolution (`P2`).** Adds only `Inv.BuilderPubkeysUnique D.preB` at the
step's pre-state to `exit_authorization_focused`. -/
theorem exit_resolution_unique_focused {checkpoint : BlockChain} {preBlocks : List KeptBlock}
    {anchor final : GJointState P} (run : GJointRun cfg ccfg bls anchor final)
    (hspe : 2 ≤ P.SLOTS_PER_EPOCH) (htied : ParentTied cfg anchor)
    (hclean : Exit.Indexed.Clean cfg checkpoint (preBlocks ++ run.blocks) final.exec)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : run.steps[j]? = some (.gloas D))
    (huniq : Inv.BuilderPubkeysUnique D.preB)
    {i : Nat} (initiated : ExitInitiated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderExitRequest) (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
      D.builderExits[k]? = some req ∧
      builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
      classifyBuilderExit ccfg m req = .ok (.initiate i) ∧
      ∀ (i' : Nat) (b' : Gloas.Builder), m.builders.toArray[i']? = some b' → b'.pubkey = req.pubkey → i' = i := by
  obtain ⟨k, req, tr, m, -, hreq, htr, hm, -, hcl, -, hfm, -⟩ :=
    exit_authorization_focused run hspe htied hclean stepD initiated
  have hu0 : Inv.BuilderPubkeysUnique D.postSlots :=
    Inv.pubkeysUnique_of_eq D.postSlots_builders huniq
  have hu := builderExitTrace_pubkeysUnique htr hu0 k m hm
  obtain ⟨⟨b, hb, hpk⟩, hlt⟩ := firstMatch_some hfm
  refine ⟨k, req, tr, m, hreq, htr, hm, hcl, fun i' b' hb' hpk' => ?_⟩
  rcases Nat.lt_trichotomy i' i with h | h | h
  · exact absurd hpk' (hlt i' h b' hb')
  · exact h
  · exact absurd (hpk.trans hpk'.symm) (hu i i' b b' h hb hb')

/-! ## Section 5: Focused consensus-only payment append bounds (`P2`) -/

/-- **Focused per-slot append bound (`P2`).** Purely consensus-side over `GJointRun`, requiring no
execution history, checkpoint, builder contract installation, `AnchorBidWitness`, or registry bounds. -/
theorem slot_appended_at_most_once_focused
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {anchor final : GJointState P}
    (run : GJointRun cfg ccfg bls anchor final)
    (hinv : ∀ {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      Inv.NoLiveWeightOnLatestBid B.preB ∧ Inv.LatestBidCoherence B.preB ∧ Inv.FutureEmpty B.preB)
    (s : Nat) :
    (run.pushes.filter (fun e => decide (e.slot = s))).length ≤ 1 :=
  slot_pushes_le_one hq hspe run hinv s

/-- **Focused per-bid append bound (`P2`).** Purely consensus-side specialization of
`slot_appended_at_most_once_focused` to `D.paySlot`. -/
theorem bid_appended_at_most_once_focused
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {anchor final : GJointState P}
    (run : GJointRun cfg ccfg bls anchor final)
    (hinv : ∀ {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      Inv.NoLiveWeightOnLatestBid B.preB ∧ Inv.LatestBidCoherence B.preB ∧ Inv.FutureEmpty B.preB)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (_stepD : run.steps[j]? = some (.gloas D)) :
    (run.pushes.filter (fun e => decide (e.slot = D.paySlot))).length ≤ 1 :=
  slot_pushes_le_one hq hspe run hinv D.paySlot

/-! ## Section 6: Focused execution-only deposit value (`P2`) -/

/-- **Focused B2 value clause (`P2`).** Purely execution-side over any `CodesKept` history: needs no
consensus `GJointRun`, no `depositBudget ≤ 2 ^ 256`, and no `exitFew ≤ 2 ^ 64`. -/
theorem deposit_value_focused {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    (hcodes : CodesKept cfg checkpoint blocks stop)
    (hdepFresh : checkpoint.state.getStor Deposit.Creation.address = Stor.empty)
    (hnoSys : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (hclean : HistoryClean blocks)
    (hroots : HistoryRootsFit blocks)
    (hdepSender : History.NoSender depositAddr blocks)
    (hexSender : History.NoSender exitAddr blocks)
    (hcredits : HistoryCreditsFit depositAddr blocks ∧ HistoryCreditsFit exitAddr blocks) :
    ((checkpoint.state.get depositAddr).bal).toNat + feesPaidAt blocks depositAddr ≤
        ((stop.state.get depositAddr).bal).toNat ∧
      ((checkpoint.state.get exitAddr).bal).toNat + feesPaidAt blocks exitAddr ≤
        ((stop.state.get exitAddr).bal).toNat ∧
      ∀ f ∈ keptAt blocks depositAddr, ∀ h : f.sevm.data.length = 184,
        Bytes.toNat (Deposit.recordOf f.sevm h).amount * 10 ^ 9 ≤ f.sevm.value.toNat ∧
          ∃ fee : B256, Deposit.Admits f.sevm.data f.sevm.value fee := by
  refine ⟨value_kept_bridge hcodes hroots depositAddr List.mem_cons_self hdepSender hcredits.1,
    value_kept_bridge hcodes hroots exitAddr (List.mem_cons_of_mem _ List.mem_cons_self)
      hexSender hcredits.2, fun f hmem hlen => ?_⟩
  obtain ⟨frames, -, corr, -⟩ := Deposit.history_chain hcodes.linked hcodes.deposit hdepFresh
    hnoSys hclean.senders hclean.authorities hclean.creates
  obtain ⟨xs, ys, hsplit0⟩ := List.mem_iff_append.mp hmem
  have hsplit : ChainLink.History.kept Deposit.contract.address blocks = xs ++ f :: ys := hsplit0
  have hcorr : ChainLink.Corresponds Deposit.contract frames (xs ++ f :: ys) := by
    rw [← hsplit]
    exact corr
  obtain ⟨gs, g, hs, rfl, left, m, -⟩ := hcorr.split
  have hlen' : f.sevm.data.length = Deposit.contract.payload := hlen
  have hkev : ChainLink.keptEvent Deposit.contract f =
      .submission (Deposit.contract.recordOf f.sevm hlen') :=
    ChainLink.keptEvent_of_length hlen'
  cases hg : g with
  | submission sevm pre post l i o rules tgt caller law =>
    have hval : sevm.value.toNat ≤ f.sevm.value.toNat := by
      have h := m.value
      rw [hg] at h
      exact h
    have h1 := m.event
    rw [hg, hkev] at h1
    change Delivery.Event.submission _ = _ at h1
    injection h1 with hr
    have hd : sevm.data = f.sevm.data := by
      have := congrArg Deposit.Record.data hr
      rwa [Deposit.recordOf_data, Deposit.recordOf_data] at this
    have hco := law.admitted.covered
    have hcr := law.admitted.credited
    rw [Deposit.creditedWei_eq, hd] at hco hcr
    rw [← Deposit.creditOf_eq_amount f.sevm hlen]
    exact ⟨by omega, o / 17, hcr, by omega⟩
  | feeRead sevm pre post l i o rules tgt caller law =>
    have h1 := m.event
    rw [hg, hkev] at h1
    change Delivery.Event.feeRead = .submission _ at h1
    cases h1
  | system benv data post out fork installed length run =>
    have h1 := m.event
    rw [hg, hkev] at h1
    change Delivery.Event.system _ = .submission _ at h1
    cases h1

/-! ## Section 7: `ValidJointG` compatibility bridges -/

/-- Compatibility bridge recovering `ValidJointG.deposit_fate` from `deposit_fate_focused`. -/
theorem deposit_fate_of_focused {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) {n : Nat}
    (hn : n < (Deposit.Indexed.submissions v.blocks).length) :
    (n < (Deposit.Indexed.emissions v.preBlocks).length ∧
      (Deposit.Indexed.emissions v.preBlocks)[n]? = (Deposit.Indexed.submissions v.blocks)[n]?) ∨
    ((Deposit.Indexed.emissions v.preBlocks).length ≤ n ∧
      n < (Deposit.Indexed.emissions v.blocks).length ∧
      ∃ bj k, ∃ hbj : bj < v.blocks.length,
        k < (Deposit.Indexed.blockEmissions v.blocks[bj]).length ∧
        (Deposit.Indexed.emissions (v.blocks.take bj)).length + k = n ∧
        (Deposit.Indexed.blockEmissions v.blocks[bj])[k]? = (Deposit.Indexed.submissions v.blocks)[n]? ∧
        v.preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderDepositRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        v.run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ v.run.payloadIndex j = bj - v.preBlocks.length ∧
        D.builderDeposits[k]? = some req ∧ Ssz.serialize req = (Deposit.Indexed.submissions v.blocks)[n]! ∧
        builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderDeposit ccfg bls m req = .ok o ∧
          (∀ o', classifyBuilderDeposit ccfg bls m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderDepositOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req',
            v.run.steps[j']? = some (.gloas D') →
            D'.builderDeposits[k']? = some req' →
            (Deposit.Indexed.emissions
              (v.blocks.take (v.preBlocks.length + v.run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Deposit.Indexed.emissions v.blocks).length ≤ n ∧
      (Deposit.Indexed.remainingQueue final.exec)[n - (Deposit.Indexed.emissions v.blocks).length]? =
        (Deposit.Indexed.submissions v.blocks)[n]?) :=
  deposit_fate_focused v.run v.anchorPending.tied v.depositClean hn

/-- Compatibility bridge recovering `ValidJointG.exit_fate` from `exit_fate_focused`. -/
theorem exit_fate_of_focused {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) {n : Nat}
    (hn : n < (Exit.Indexed.submissions v.blocks).length) :
    (n < (Exit.Indexed.emissions v.preBlocks).length ∧
      (Exit.Indexed.emissions v.preBlocks)[n]? = (Exit.Indexed.submissions v.blocks)[n]?) ∨
    ((Exit.Indexed.emissions v.preBlocks).length ≤ n ∧
      n < (Exit.Indexed.emissions v.blocks).length ∧
      ∃ bj k, ∃ hbj : bj < v.blocks.length,
        k < (Exit.Indexed.blockEmissions v.blocks[bj]).length ∧
        (Exit.Indexed.emissions (v.blocks.take bj)).length + k = n ∧
        (Exit.Indexed.blockEmissions v.blocks[bj])[k]? = (Exit.Indexed.submissions v.blocks)[n]? ∧
        v.preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderExitRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        v.run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ v.run.payloadIndex j = bj - v.preBlocks.length ∧
        D.builderExits[k]? = some req ∧ Ssz.serialize req = (Exit.Indexed.submissions v.blocks)[n]! ∧
        builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderExit ccfg m req = .ok o ∧
          (∀ o', classifyBuilderExit ccfg m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderExitOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req',
            v.run.steps[j']? = some (.gloas D') →
            D'.builderExits[k']? = some req' →
            (Exit.Indexed.emissions
              (v.blocks.take (v.preBlocks.length + v.run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Exit.Indexed.emissions v.blocks).length ≤ n ∧
      (Exit.Indexed.remainingQueue final.exec)[n - (Exit.Indexed.emissions v.blocks).length]? =
        (Exit.Indexed.submissions v.blocks)[n]?) :=
  exit_fate_focused v.run v.anchorPending.tied v.exitClean hn

/-- Compatibility bridge recovering `ValidJointG.registration_authorization` from `registration_authorization_focused`. -/
theorem registration_authorization_of_focused {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) (hbls : bls = true)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {i : Nat} (created : BuilderCreated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderDepositRequest) (tr : List (Gloas.BeaconState P))
      (m m' : Gloas.BeaconState P) (amount : Gwei) (dom : Domain) (addr : ExecutionAddress) (e : Epoch),
      D.builderDeposits[k]? = some req ∧
      builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
      classifyBuilderDeposit ccfg bls m req = .ok (.register i amount) ∧ amount = req.amount ∧
      (D.isFull ∧ ∃ bi b, v.run.payloadIndex j = bi ∧ v.blocks[v.preBlocks.length + bi]? = some b ∧
        (Deposit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
        (Deposit.Indexed.submissions v.blocks)[(Deposit.Indexed.emissions
          (v.blocks.take (v.preBlocks.length + bi))).length + k]? = some (Ssz.serialize req)) ∧
      req.withdrawal_credentials.toBytes.head? = some 0xB0 ∧
      builderDepositDomain ccfg = some dom ∧
      blsVerify true req.pubkey (computeSigningRoot (builderDepositMessage req) dom) req.signature = true ∧
      Jaune.Bytes.toAdr? (req.withdrawal_credentials.toBytes.drop 12) = some addr ∧
      computeEpochAtSlot P m.slot = .ok e ∧
      m'.builders.toArray[i]? = some (freshBuilder req.pubkey addr req.amount e) ∧
      ∃ b' : Gloas.Builder, D.postB.builders.toArray[i]? = some b' ∧
        b'.pubkey = req.pubkey ∧ b'.version = Gloas.PAYLOAD_BUILDER_VERSION ∧ b'.execution_address = addr ∧
        b'.deposit_epoch = e ∧ b'.withdrawable_epoch = FAR_FUTURE_EPOCH ∧
        b'.balance.toNat = req.amount.toNat +
          (((D.builderDeposits.drop (k + 1)).filter (fun r' => r'.pubkey == req.pubkey &&
            Gloas.isBuilderWithdrawalCredential r'.withdrawal_credentials)).map (·.amount.toNat)).sum :=
  registration_authorization_focused v.run v.slotsPerEpoch hbls v.anchorPending.tied v.depositClean
    (v.registeredRecordKept hbls) stepD created

/-- Compatibility bridge recovering `ValidJointG.exit_authorization_caller` from `exit_authorization_caller_focused`. -/
theorem exit_authorization_caller_of_focused {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {i : Nat} (initiated : ExitInitiated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderExitRequest) (tr : List (Gloas.BeaconState P)) (m m' : Gloas.BeaconState P),
      D.builderExits[k]? = some req ∧
      builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
      classifyBuilderExit ccfg m req = .ok (.initiate i) ∧
      (D.isFull ∧ ∃ bi b, v.run.payloadIndex j = bi ∧ v.blocks[v.preBlocks.length + bi]? = some b ∧
        (Exit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
        (Exit.Indexed.submissions v.blocks)[(Exit.Indexed.emissions
          (v.blocks.take (v.preBlocks.length + bi))).length + k]? = some (Ssz.serialize req)) ∧
      firstMatch m.builders req.pubkey = some i ∧
      (∃ (b : Gloas.Builder) (bi : Gloas.BuilderIndex), m.builders.toArray[i]? = some b ∧
        b.execution_address = req.source_address ∧ U64.ofNat? i "BuilderIndex" = .ok bi ∧
        Gloas.isActiveBuilder m bi = .ok true) ∧
      (Ssz.serialize req).take 20 = req.source_address.toBytes ∧
      ∃ (r : Exit.Record) (f : Exec.Frame), f ∈ keptAt v.blocks exitAddr ∧
        submittedBy Exit.contract f = some r ∧ Ssz.serialize req = Exit.Record.out r ∧
        r.source = f.sevm.caller ∧ req.source_address = f.sevm.caller :=
  exit_authorization_caller_focused v.run v.slotsPerEpoch v.anchorPending.tied v.exitClean stepD initiated

/-- Compatibility bridge recovering `ValidJointG.exit_resolution_unique` from `exit_resolution_unique_focused`. -/
theorem exit_resolution_unique_of_focused {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {i : Nat} (initiated : ExitInitiated D.preB D.postB i) :
    ∃ (k : Nat) (req : Gloas.BuilderExitRequest) (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
      D.builderExits[k]? = some req ∧
      builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
      classifyBuilderExit ccfg m req = .ok (.initiate i) ∧
      ∀ (i' : Nat) (b' : Gloas.Builder), m.builders.toArray[i']? = some b' → b'.pubkey = req.pubkey → i' = i :=
  exit_resolution_unique_focused v.run v.slotsPerEpoch v.anchorPending.tied v.exitClean stepD
    (v.gInv_pre stepD).1 initiated

/-- Compatibility bridge recovering `ValidJointG.slot_appended_at_most_once` from `slot_appended_at_most_once_focused`. -/
theorem slot_appended_at_most_once_of_focused {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) (s : Nat) :
    (v.run.pushes.filter (fun e => decide (e.slot = s))).length ≤ 1 :=
  slot_appended_at_most_once_focused v.quorumPositive (by have := v.slotsPerEpoch; omega) v.run
    (fun hB => by
      obtain ⟨-, -, -, -, -, g7, g8, -, fe⟩ := v.gInv_pre hB
      exact ⟨g7, g8, fe⟩) s

/-- Compatibility bridge recovering `ValidJointG.bid_appended_at_most_once` from `bid_appended_at_most_once_focused`. -/
theorem bid_appended_at_most_once_of_focused {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D)) :
    (v.run.pushes.filter (fun e => decide (e.slot = D.paySlot))).length ≤ 1 :=
  bid_appended_at_most_once_focused v.quorumPositive (by have := v.slotsPerEpoch; omega) v.run
    (fun hB => by
      obtain ⟨-, -, -, -, -, g7, g8, -, fe⟩ := v.gInv_pre hB
      exact ⟨g7, g8, fe⟩) stepD

/-- Compatibility bridge recovering `ValidJointG.payment_debit_at_most_once` from `payment_debit_at_most_once_focused`. -/
theorem payment_debit_at_most_once_of_focused {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    (v.run.debitSpent ++ v.run.debitLeft = v.run.debitSource ∧
      v.run.debitLeft.map Prod.snd = final.builderQueue ∧
      (v.run.debitSource.map Prod.fst).Nodup ∧
      (v.run.debitSpent.map Prod.fst).Nodup) ∧
    (∀ {i k : Nat} {D : GloasStepData (P := P) cfg ccfg bls},
      v.run.steps[i]? = some (.gloas D) → k < (GJointRunStep.gloas D).drops →
      ∃ origin e, DebitStepEvent v.run i D k origin e) ∧
    (∀ {p : Nat} {origin : DebitOrigin} {e : Gloas.BuilderPendingWithdrawal},
      v.run.debitSpent[p]? = some (origin, e) →
      ∃ i D k, p = v.run.debitCursor i + k ∧ DebitStepEvent v.run i D k origin e) ∧
    (∀ {i i' k k' : Nat} {D D' : GloasStepData (P := P) cfg ccfg bls}
        {origin : DebitOrigin} {e e' : Gloas.BuilderPendingWithdrawal},
      v.run.steps[i]? = some (.gloas D) → k < (GJointRunStep.gloas D).drops →
      v.run.debitSpent[v.run.debitCursor i + k]? = some (origin, e) →
      v.run.steps[i']? = some (.gloas D') → k' < (GJointRunStep.gloas D').drops →
      v.run.debitSpent[v.run.debitCursor i' + k']? = some (origin, e') →
      i = i' ∧ k = k' ∧ e = e') ∧
    (∀ {k : Nat} {e : Gloas.BuilderPendingWithdrawal},
      anchor.builderQueue[k]? = some e →
      ((Sum.inl k, e) ∈ v.run.debitSpent ∧ (Sum.inl k, e) ∉ v.run.debitLeft) ∨
        ((Sum.inl k, e) ∈ v.run.debitLeft ∧ (Sum.inl k, e) ∉ v.run.debitSpent)) ∧
    (∀ slot : Nat,
      ((v.run.debitSpent.filterMap (fun r => v.run.lookupPush r.1)).filter
        (fun p => decide (p.slot = slot))).length ≤ 1) ∧
    (∀ {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls}
        {origin : DebitOrigin} {e : Gloas.BuilderPendingWithdrawal} {p : Push},
      v.run.steps[j]? = some (.gloas D) → U64.zero < D.bid.value →
      (origin, e) ∈ v.run.debitSpent → v.run.lookupPush origin = some p → p.slot = D.paySlot →
      e = D.payW ∧ p.w = D.payW ∧
        ∃ j_app k_app D_app (f : PaymentFate v.run j),
          origin = Sum.inr (j_app, k_app) ∧
          v.run.steps[j_app]? = some (.gloas D_app) ∧
          D_app.pushes[k_app]? = some p ∧
          f.holdsFor D ∧
          f.pushKey? = some (p.path, j_app)) :=
  v.payment_debit_at_most_once

/-- Compatibility bridge recovering `ValidJointG.deposit_value` from `deposit_value_focused`. -/
theorem deposit_value_of_focused {checkpoint : BlockChain} {anchor final : GJointState P}
    (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    ((checkpoint.state.get depositAddr).bal).toNat + feesPaidAt v.blocks depositAddr ≤
        ((final.exec.state.get depositAddr).bal).toNat ∧
      ((checkpoint.state.get exitAddr).bal).toNat + feesPaidAt v.blocks exitAddr ≤
        ((final.exec.state.get exitAddr).bal).toNat ∧
      ∀ f ∈ keptAt v.blocks depositAddr, ∀ h : f.sevm.data.length = 184,
        Bytes.toNat (Deposit.recordOf f.sevm h).amount * 10 ^ 9 ≤ f.sevm.value.toNat ∧
          ∃ fee : B256, Deposit.Admits f.sevm.data f.sevm.value fee :=
  deposit_value_focused v.codes v.depositFresh v.noSystemCode ⟨v.senders, v.authorities, v.creates⟩
    v.roots v.depositNoSender v.exitNoSender v.creditsFit

end Blanc.Composition.BuilderRequestFocusedHeadlines
