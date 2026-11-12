import Blanc.Composition.BuilderRequestJointGChargeOnce
import Blanc.GloasWithdrawalPrefix
import Blanc.Lift.RequestQueue.Batch

/-!
# Actual withdrawal prefixes meet the tagged cap-one queue model

Each step witness comes from its original successful parent/header/withdrawal calls.
The local erasure law uses the same processed count as that actual apply phase.
Run occurrence attribution is developed here; builder sweeps and natural balance loss
are separate from the pending-prefix events.
-/

namespace Blanc.Lift.BuilderRequest
open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv
variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
theorem _root_.Blanc.GloasStepData.withdrawal_prefix
    (D : GloasStepData (P := P) cfg ccfg bls) (hspe : 0 < P.SLOTS_PER_EPOCH) :
    ∃ (s1 s2 s3 : Gloas.BeaconState P) (ws : Array JauneConsensus.Withdrawal) (d : Nat),
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1 ∧
      Gloas.processBlockHeader s1 D.block.message = .ok s2 ∧
      Gloas.processWithdrawals s2 = .ok s3 ∧
      GloasWithdrawalPrefix.PrefixSpec s2 s3 ws d ∧
      s2.builder_pending_withdrawals.toArray.toList =
        D.preB.builder_pending_withdrawals.toArray.toList ++ D.pushes.map (·.w) ∧
      D.Drops d ∧ D.postB.builder_pending_withdrawals.toArray.toList =
        s2.builder_pending_withdrawals.toArray.toList.drop d := by
  obtain ⟨s1, s2, s3, -, -, -, -, h1, h2, h3, -⟩ := processBlock_phases D.processBlock
  obtain ⟨ws, d, hp⟩ := GloasWithdrawalPrefix.processWithdrawals_prefix h3
  have hd : D.Drops d := ⟨s1, s2, s3, h1, h2, h3, hp.2.1, hp.1⟩
  obtain ⟨-, -, hm2⟩ := processBlockHeader_post h2
  have e2 : s2.builder_pending_withdrawals = s1.builder_pending_withdrawals := by rw [hm2]
  have hq : s2.builder_pending_withdrawals.toArray.toList =
      D.preB.builder_pending_withdrawals.toArray.toList ++ D.pushes.map (·.w) := by
    rw [e2, parent_pushes hspe h1, slotLoop_pushes _ _ _ (processSlots_slotLoop D.slots).2,
      GloasStepData.pushes, List.map_append, List.append_assoc]
  obtain ⟨d', hd', -, he⟩ := D.pushes_exhaustive hspe
  have hdd : d' = d := D.drops_unique hd' hd
  rw [hdd] at he
  refine ⟨s1, s2, s3, ws, d, h1, h2, h3, hp, hq, hd, ?_⟩
  rw [hq]
  exact he

theorem _root_.Blanc.GloasStepData.tagged_batch_erasure
    {Tag : Type} (D : GloasStepData (P := P) cfg ccfg bls) (hspe : 0 < P.SLOTS_PER_EPOCH)
    (st : QueueState (Tag × Gloas.BuilderPendingWithdrawal))
    (rs : List (Tag × Gloas.BuilderPendingWithdrawal))
    (pre : st.queue.map Prod.snd = D.preB.builder_pending_withdrawals.toArray.toList)
    (app : rs.map Prod.snd = D.pushes.map (·.w)) :
    ∃ d, D.Drops d ∧
      ((RequestQueue.run 1 st (rs.map RequestQueue.Effect.push ++
        List.replicate d (.drain (fun _ _ => 0)))).queue.map Prod.snd) =
        D.postB.builder_pending_withdrawals.toArray.toList := by
  obtain ⟨s1, s2, s3, ws, d, -, -, -, -, hq, hd, he⟩ := D.withdrawal_prefix hspe
  refine ⟨d, hd, ?_⟩
  rw [RequestQueue.run_append, RequestQueue.run_unit_drains_queue, RequestQueue.run_pushes_queue,
    List.map_drop, List.map_append, pre, app, ← hq, ← he]
end Blanc.Lift.BuilderRequest
