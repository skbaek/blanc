import Blanc.Composition.BuilderRequestJointGFate

/-!
# The position of a builder request on the joint history (B1, B3)

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` §0.7, B1, B3): the
positional clause the run-level B1 and B3 share. A builder deposit (exit) request at position `k` of a Gloas run
step's `parent_execution_requests` makes the step settle FULL; the payload block it builds upon is block
`preBlocks.length + payloadIndex j` of the joint history, whose type-3 (type-4) record `k` is the request's
serialization; and that record is the history's committed paid submission occurrence
`|emissions before the block| + k` (`Occurrence.history_fate`'s indexing).

* `Occurrence.submission_of_emission`: the generic execution half, over any linked contract with an empty start
  queue: record `k` of block `bj` is submission occurrence `|emissions (take bj)| + k`.
* `ValidJointG.deposit_position`, `ValidJointG.exit_position`: the run-level clause, from RBA's seam
  (`GStepView.full_of_requests`, `GloasStepData.kept_of_full`, `ValidJointG.full_output`,
  `RequestCodecG.deposit_blockEmissions` / `exit_blockEmissions`).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace ChainLink Blanc JauneConsensus.Facts.Gloas Occurrence

/-! ## The execution half: an emitted record is a submission occurrence -/

/-- **An emitted record is the submission occurrence at its index.** Over a linked contract whose start queue is
empty in output form, record `k` of block `bj` of the history is submission occurrence
`|emissions (blocks.take bj)| + k`. -/
theorem Occurrence.submission_of_emission {c : Delivery.Contract} {ty : UInt8} {cfg : ChainConfig}
    {start stop : BlockChain} {blocks : List KeptBlock} {st : QueueState c.Record} (R : Reading c)
    (L : Linked c ty) (P : Premises c cfg start blocks stop st) (hq : st.queue.map c.out = [])
    {bj k : Nat} {b : KeptBlock} {x : Bytes} (hb : blocks[bj]? = some b)
    (hk : (blockEmissions R ty b)[k]? = some x) :
    (submissions c blocks)[(emissions R ty (blocks.take bj)).length + k]? = some x := by
  have hbj : bj < blocks.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbe : blocks[bj] = b := (List.getElem?_eq_some_iff.mp hb).2
  have hkl : k < (blockEmissions R ty b).length := (List.getElem?_eq_some_iff.mp hk).1
  have fate := history_fate R L P ((emissions R ty (blocks.take bj)).length + k)
  rw [hq, List.nil_append] at fate
  rcases fate with ⟨-, j', k', hj', hk', pos, get, -, uniq⟩ | ⟨hE, -⟩
  · obtain ⟨rfl, rfl⟩ := uniq bj k hbj (by rw [hbe]; exact hkl) rfl
    rw [← get]
    simp only [hbe, hk]
  · exfalso
    have succ := congrArg List.length (emissions_take_succ (ty := ty) R hb)
    rw [List.length_append] at succ
    have mono := emissions_take_mono (blocks := blocks) (ty := ty) R (show bj + 1 ≤ blocks.length by omega)
    rw [List.take_length] at mono
    omega

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## States with the same builders -/

theorem exitInitiated_congr_left {s t u : Gloas.BeaconState P} (h : s.builders = t.builders) {i : Nat} :
    ExitInitiated s u i ↔ ExitInitiated t u i := by
  unfold ExitInitiated
  rw [h]

theorem builderCreated_congr_left {s t u : Gloas.BeaconState P} (h : s.builders = t.builders) {i : Nat} :
    BuilderCreated s u i ↔ BuilderCreated t u i := by
  unfold BuilderCreated
  rw [h]

/-- A Gloas run step's post-slots state has its pre-state's builders. -/
theorem _root_.Blanc.GloasStepData.postSlots_builders (D : GloasStepData (P := P) cfg ccfg bls) :
    D.postSlots.builders = D.preB.builders :=
  Inv.processSlots_identityStable D.slots


namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- **B1's positional clause.** A builder deposit request at position `k` of a Gloas run step's
`parent_execution_requests`: the step settles FULL; record `k` of the type-3 records of the payload block it
builds upon (block `preBlocks.length + payloadIndex j`) is the request's serialization; and that record is the
deposit contract's committed paid submission occurrence at index `|emissions before the block| + k`. -/
theorem deposit_position (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (hD : v.run.steps[j]? = some (.gloas D)) {k : Nat}
    {req : Gloas.BuilderDepositRequest} (hreq : D.builderDeposits[k]? = some req) :
    D.isFull ∧ ∃ bi b, v.run.payloadIndex j = bi ∧ v.blocks[v.preBlocks.length + bi]? = some b ∧
      (Deposit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
      (Deposit.Indexed.submissions v.blocks)[(Deposit.Indexed.emissions
        (v.blocks.take (v.preBlocks.length + bi))).length + k]? = some (Ssz.serialize req) := by
  obtain ⟨env, r, post, hs⟩ := D.view.full_of_requests (Or.inl (by
    intro h
    change D.builderDeposits = [] at h
    rw [h, List.getElem?_nil] at hreq
    cases hreq))
  obtain ⟨b, hk, -, -⟩ := D.kept_of_full hs
  have hem := RequestCodecG.deposit_blockEmissions (v.full_output hD hs hk)
  have hek : (Deposit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) := by
    rw [hem, List.getElem?_map, hreq]
    rfl
  refine ⟨⟨env, r, post, hs⟩, _, b, rfl, v.blocks_getElem?_full hD hk, hek, ?_⟩
  have H := v.depositClean
  exact Occurrence.submission_of_emission Deposit.Indexed.reading Deposit.linked H.premises
    Deposit.Indexed.start_queue (v.blocks_getElem?_full hD hk) hek

/-- **B3's positional clause.** As `deposit_position`, for a builder exit request and the exit contract's type-4
records. -/
theorem exit_position (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (hD : v.run.steps[j]? = some (.gloas D)) {k : Nat}
    {req : Gloas.BuilderExitRequest} (hreq : D.builderExits[k]? = some req) :
    D.isFull ∧ ∃ bi b, v.run.payloadIndex j = bi ∧ v.blocks[v.preBlocks.length + bi]? = some b ∧
      (Exit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) ∧
      (Exit.Indexed.submissions v.blocks)[(Exit.Indexed.emissions
        (v.blocks.take (v.preBlocks.length + bi))).length + k]? = some (Ssz.serialize req) := by
  obtain ⟨env, r, post, hs⟩ := D.view.full_of_requests (Or.inr (by
    intro h
    change D.builderExits = [] at h
    rw [h, List.getElem?_nil] at hreq
    cases hreq))
  obtain ⟨b, hk, -, -⟩ := D.kept_of_full hs
  have hem := RequestCodecG.exit_blockEmissions (v.full_output hD hs hk)
  have hek : (Exit.Indexed.blockEmissions b)[k]? = some (Ssz.serialize req) := by
    rw [hem, List.getElem?_map, hreq]
    rfl
  refine ⟨⟨env, r, post, hs⟩, _, b, rfl, v.blocks_getElem?_full hD hk, hek, ?_⟩
  have H := v.exitClean
  exact Occurrence.submission_of_emission Exit.Indexed.reading Exit.linked H.premises
    Exit.Indexed.start_queue (v.blocks_getElem?_full hD hk) hek

end ValidJointG

end Blanc.Lift.BuilderRequest
