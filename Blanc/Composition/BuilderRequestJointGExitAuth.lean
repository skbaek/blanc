import Blanc.Composition.BuilderRequestJointGPosition
import Blanc.Composition.BuilderRequestPublicFindings
import JauneConsensus.Facts.Gloas.StepB3

/-!
# B3 over a valid Gloas joint chain: exit authorization, no other path

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B3), traces read at the
step's post-slots state (erratum 2026-11-10).

* `ValidJointG.exit_authorization`: every builder exit initiated at a Gloas step of the run consumes the builder
  exit request at exit-trace position `k`, classified `initiate i` (first match, active, source equal to the
  builder's `execution_address`); that request is the exit contract's committed paid submission occurrence
  `|emissions before the payload block| + k` (R1's `history_fate`, through `ValidJointG.exit_position`), its
  serialization starts with the source address, and the contract recorded it from a kept frame whose caller is that
  source (`history_exit_source_bridge`).
* `ValidJointG.no_exit_elsewhere`: a pre-Gloas step and the crossing step initiate no exit
  (`jointStepG_pre_noBuilders`, `jointStepG_crossing_noExit`); `ValidJointG.exit_authorization_all` is the headline
  over every step of the run.
* `GloasStepData.withdrawableEpoch_writers`: a builder's `withdrawable_epoch` changes at a Gloas step only by an
  initiated exit, a reset top-up, or a fresh record (MBS's `GStepView.withdrawableEpoch_writers`).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace ChainLink Blanc JauneConsensus.Facts.Gloas Occurrence
open Blanc.Composition.BuilderRequestPublic (keptAt exitAddr history_exit_source_bridge)

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## The writers of `withdrawable_epoch` -/

/-- A reset top-up of builder `i` by the builder deposit request at deposit-trace position `k` of the step
(statements.md's `topUpResetAt`). -/
def _root_.Blanc.GloasStepData.topUpResetAt (D : GloasStepData (P := P) cfg ccfg bls) (i k : Nat) : Prop :=
  ∃ (r : Gloas.BuilderDepositRequest) (tr : List (Gloas.BeaconState P)) (m m' : Gloas.BeaconState P),
    D.builderDeposits[k]? = some r ∧ builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧
    tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
    Gloas.processBuilderDepositRequest (gloasCtx ccfg bls) m r = .ok m' ∧
    classifyBuilderDeposit ccfg bls m r = .ok (.topUp i r.amount true)

/-- **B3: no other path writes a builder's `withdrawable_epoch`.** At a Gloas run step, a change of builder `i`'s
`withdrawable_epoch` is an initiated exit, a reset top-up at some deposit-trace position, or a fresh record. -/
theorem _root_.Blanc.GloasStepData.withdrawableEpoch_writers (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    (D : GloasStepData (P := P) cfg ccfg bls) {i : Nat} {b b' : Gloas.Builder}
    (hb : D.preB.builders.toArray[i]? = some b) (hb' : D.postB.builders.toArray[i]? = some b')
    (hne : b.withdrawable_epoch ≠ b'.withdrawable_epoch) :
    ExitInitiated D.preB D.postB i ∨ (∃ k, D.topUpResetAt i k) ∨ BuilderCreated D.preB D.postB i := by
  have hbs := D.postSlots_builders
  obtain ⟨trD, trE, hD, -, hcase⟩ :=
    D.view.withdrawableEpoch_writers hspe (x := b) (by change D.postSlots.builders.toArray[i]? = _; rw [hbs]; exact hb)
      hb' hne
  rcases hcase with ⟨hin, -⟩ | ⟨k, r, m, m', hr, hm, hm', hcall, hcl⟩ | hcr
  · exact Or.inl ((exitInitiated_congr_left hbs).mp hin)
  · exact Or.inr (Or.inl ⟨k, r, trD, m, m', hr, hD, hm, hm', hcall, hcl⟩)
  · exact Or.inr (Or.inr ((builderCreated_congr_left hbs).mp hcr))

/-! ## B3 at a Gloas step -/

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- **B3: exit authorization.** Every builder exit initiated at a Gloas step `j` of a valid joint chain consumes
the builder exit request `req` at exit-trace position `k` of the step block's `parent_execution_requests`
(the trace read at the step's post-slots state), classified `initiate i` at `tr[k]`, its call running
`tr[k] → tr[k+1]`; `i` is the first builder with `req`'s pubkey, active, with `execution_address` equal to
`req`'s source address. Positionally, the step settles FULL and `req` is record `k` of the type-4 records of the
payload block it builds upon, which is the exit contract's committed paid submission occurrence
`|emissions before that block| + k`. Its serialization starts with the source address, and the contract recorded it
from a kept frame of the joint history whose caller is that source. Any `bls`. -/
theorem exit_authorization (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D)) {i : Nat}
    (initiated : ExitInitiated D.preB D.postB i) :
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
        r.source = f.sevm.caller := by
  have hin : ExitInitiated D.view.postSlots D.postB i := (exitInitiated_congr_left D.postSlots_builders).mpr initiated
  obtain ⟨k, req, tr, m, m', hreq, htr, hm, hm', -, hcl⟩ := D.view.exitInitiated v.slotsPerEpoch hin
  have hpos := v.exit_position stepD hreq
  obtain ⟨-, -, -, -, -, hinit, -⟩ := classifyBuilderExit_meaning hcl
  obtain ⟨b, bi, hfm, hb, hbi, hact, haddr, -⟩ := (hinit i).mp rfl
  have hlen : req.source_address.toBytes.length = 20 := by
    simp only [Adr.toBytes, List.length_append, UInt32.length_toBytes, B128.length_toBytes]
  refine ⟨k, req, tr, m, m', hreq, htr, hm, hm', hcl, hpos, hfm, ⟨b, bi, hb, haddr, hbi, hact⟩, ?_, ?_⟩
  · rw [RequestCodecG.serialize_builderExitRequest]
    exact List.take_left' hlen
  · obtain ⟨-, bj, -, -, -, -, hsub⟩ := hpos
    simp only [Exit.Indexed.submissions, Occurrence.submissions, List.getElem?_map] at hsub
    cases hr : (History.submitted Exit.contract v.blocks)[(Exit.Indexed.emissions
        (v.blocks.take (v.preBlocks.length + bj))).length + k]? with
    | none => rw [hr] at hsub; cases hsub
    | some r =>
      rw [hr] at hsub
      have hout : Exit.Record.out r = Ssz.serialize req := Option.some.inj hsub
      obtain ⟨f, hf, hsf⟩ := List.mem_filterMap.mp (List.mem_of_getElem? hr)
      exact ⟨r, f, hf, hsf, hout.symm, (history_exit_source_bridge hf hsf).1⟩

/-! ## No exit elsewhere -/

/-- The builder at index `i` of a joint state (none before Gloas). -/
def _root_.JauneConsensus.GJointState.builderAt : GJointState P → Nat → Option Gloas.Builder
  | .pre _, _ => none
  | .gloas b _ _, i => b.builders.toArray[i]?

/-- Builder `i`'s exit is initiated across a run step: from its pre-state to its post-state the same incarnation
leaves `FAR_FUTURE_EPOCH` (statements.md's `ExitInitiatedAt`; a pre-Gloas state has no builder). -/
def _root_.Blanc.GJointRunStep.ExitInitiatedAt (C : GJointRunStep (P := P) cfg ccfg bls) (i : Nat) : Prop :=
  ∃ b b', C.preState.builderAt i = some b ∧ C.postState.builderAt i = some b' ∧ b.pubkey = b'.pubkey ∧
    b.withdrawable_epoch = FAR_FUTURE_EPOCH ∧ b'.withdrawable_epoch ≠ FAR_FUTURE_EPOCH

/-- **The crossing step initiates no exit**, from any registry before it: every builder after the crossing is at
`FAR_FUTURE_EPOCH` (MBS's `jointStepG_crossing_noExit`). -/
theorem _root_.Blanc.CrossingData.noExit (C : CrossingData (P := P) cfg ccfg bls) :
    BuildersFar C.postB ∧ ∀ (s : Gloas.BeaconState P) (i : Nat), ¬ ExitInitiated s C.postB i := by
  obtain ⟨_, _, post, _, _, _, _, hs, _, _, _, _, hfp, _, _, _⟩ :=
    jointStepG_crossing_noExit (GJointRunStep.crossing C).ok
  injection hs with hp
  subst hp
  exact ⟨hfp, fun s i ⟨_, x', _, hx', _, _, hn⟩ => hn (hfp i x' hx')⟩

/-- **B3: the other steps initiate no exit.** A pre-Gloas step ends in a pre-Gloas state, which has no builder
(`jointStepG_pre_noBuilders`); the crossing step ends with every builder at `FAR_FUTURE_EPOCH`
(`CrossingData.noExit`). -/
theorem no_exit_elsewhere (_v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {C : GJointRunStep (P := P) cfg ccfg bls} (_stepC : _v.run.steps[j]? = some C)
    (notGloas : ∀ D, C ≠ .gloas D) (i : Nat) : ¬ C.ExitInitiatedAt i := by
  rintro ⟨b, b', -, hb', -, -, hn⟩
  cases C with
  | pre D =>
    obtain ⟨s', hs'⟩ := jointStepG_pre_noBuilders (GJointRunStep.pre D).ok
    rw [hs'] at hb'
    cases hb'
  | crossing D => exact hn ((D.noExit).1 i b' hb')
  | gloas D => exact notGloas D rfl

/-- **B3 over every step of the chain.** A builder exit initiated at any step of a valid joint chain was
initiated at a Gloas step, where it is `exit_authorization`'s. -/
theorem exit_authorization_all (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {C : GJointRunStep (P := P) cfg ccfg bls} (stepC : v.run.steps[j]? = some C) {i : Nat}
    (initiated : C.ExitInitiatedAt i) :
    ∃ D : GloasStepData (P := P) cfg ccfg bls, C = .gloas D ∧ ExitInitiated D.preB D.postB i := by
  cases C with
  | gloas D => exact ⟨D, rfl, initiated⟩
  | pre D => exact absurd initiated (v.no_exit_elsewhere stepC (fun _ h => by cases h) i)
  | crossing D => exact absurd initiated (v.no_exit_elsewhere stepC (fun _ h => by cases h) i)

end ValidJointG

end Blanc.Lift.BuilderRequest
