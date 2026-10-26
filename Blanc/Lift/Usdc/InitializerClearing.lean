import Blanc.Lift.Usdc.Impl.Cert
import Blanc.Lift.SolcStorageClear
import Blanc.Lift.RunPWalk
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.WriteSiteZero

/-! # The compiled USDC storage-string clearing loop

The actual clear-loop body pushes literal zero before its SSTORE. This
observation needs no slot separation and preserves a demanded zero even if
the cleared string cell aliases it. It does not preserve arbitrary nonzero
administrative words and does not supply an initial zero seed.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- The actual zero-tail iteration retains its genuine write and continuation.
The stack shape is derived from the successful compiled prefix. -/
theorem impl_clearTail_body_store_cut
    {R : Exec.Deriv} {sevm : Sevm} {pre : Devm} {C : List Nat} {out : Seg}
    (run : SFunc.RunCutP (StepIn R) Impl.cert.prog sevm C pre
      Impl.t_55e1_c108 out) :
    ∃ (key : B256) (tail : List B256) (pushed storePre storePost : Devm),
      pre.stack = key :: tail ∧
      StepIn R sevm pre (.push [0x00] (by decide)) pushed ∧
      StepIn R sevm pushed (.reg (.dup 1)) storePre ∧
      storePre.stack = key :: 0 :: key :: tail ∧
      (∀ a x, storePre.getStorVal a x = pre.getStorVal a x) ∧
      StepIn R sevm storePre (.reg .sstore) storePost ∧
      (∀ K : B256 → Prop, GuardObs K False sevm storePre (.reg .sstore)) ∧
      SFunc.RunCutP (StepIn R) Impl.cert.prog sevm C storePost
        (.next (.push [0x01] (by decide)) (.next (.reg .add)
          (.next (.push [0x55, 0xd8] (by decide)) (.jump 108)))) out := by
  obtain ⟨key, tail, pushed, storePre, storePost, stack, push, dup, shape,
    storage, store, zero, rest⟩ :=
    SolcStorageClear.body_store_cut (back := [0x55, 0xd8])
      (backBound := by decide) (k := 108) (fun step => StepIn.toRun step) run
  refine ⟨key, tail, pushed, storePre, storePost, stack, push, dup, shape,
    storage, store, ?_, rest⟩
  intro K _ key value tail shape _
  rw [zero key value tail shape]
  exact Or.inr (Nat.zero_le _)

/-- Every write in the actual compiled clearing component is non-increasing.
The original derivation provenance, program, initial state and outcome remain
unchanged; no string bound, storage separation or zero seed is assumed. -/
theorem impl_clearTail_nonInc
    {R : Exec.Deriv} {K : B256 → Prop} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) Impl.cert.prog sevm pre
      Impl.t_55d8_c108 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ GuardObs K False s d n)
      Impl.cert.prog sevm pre Impl.t_55d8_c108 out := by
  exact SolcStorageClear.runP_nonInc (back := [0x55, 0xd8]) (exit := [0x55, 0x47])
    (backBound := by decide) (exitBound := by decide) (k := 108)
    (fun step => StepIn.toRun step) rfl run

/-- The actually reached clearing store preserves the internal demanded-zero
seed even on alias. The actual prefix and post-store continuation are retained;
no administrative-word equality or historical zero seed is asserted. -/
theorem impl_clearTail_body_zero
    {R : Exec.Deriv} {K : B256 → Prop} {sevm : Sevm} {pre : Devm}
    {C : List Nat} {out : Seg}
    (run : SFunc.RunCutP (StepIn R) Impl.cert.prog sevm C pre
      Impl.t_55e1_c108 out)
    (zero : ZeroSlots K sevm.currentTarget pre) :
    ∃ storePre storePost,
      StepIn R sevm storePre (.reg .sstore) storePost ∧
      ZeroSlots K sevm.currentTarget storePre ∧
      ZeroSlots K sevm.currentTarget storePost ∧
      SFunc.RunCutP (StepIn R) Impl.cert.prog sevm C storePost
        (.next (.push [0x01] (by decide)) (.next (.reg .add)
          (.next (.push [0x55, 0xd8] (by decide)) (.jump 108)))) out := by
  obtain ⟨_, _, _, storePre, storePost, _, _, _, _, storage, store, observed, rest⟩ :=
    impl_clearTail_body_store_cut run
  have atStore : ZeroSlots K sevm.currentTarget storePre := by
    intro x tracked
    rw [storage]
    exact zero x tracked
  exact ⟨storePre, storePost, store, atStore,
    (observed K).sstore_zero (StepIn.toRun store) atStore, rest⟩

end Blanc.Lift.Usdc
