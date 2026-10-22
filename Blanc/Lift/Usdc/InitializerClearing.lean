import Blanc.Lift.Usdc.Impl.Cert
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
  unfold Impl.t_55e1_c108 at run
  rw [St.self' pre] at run
  obtain ⟨pushed, push, run⟩ := ric_nextP run
  obtain ⟨gas₁, rfl⟩ := ri_push (StepIn.toRun push)
  obtain ⟨duplicated, dup, run⟩ := ric_nextP run
  obtain ⟨key, get, gas₂, rfl⟩ := ri_dup_any (StepIn.toRun dup)
  change pre.stack[0]? = some key at get
  cases shape : pre.stack with
  | nil => simp only [shape, List.getElem?_nil, reduceCtorEq] at get
  | cons head tail =>
    simp only [shape, List.getElem?_cons_zero,
      Option.some.injEq] at get
    subst key
    obtain ⟨storePost, store, run⟩ := ric_nextP run
    refine ⟨head, tail, _, _, storePost, rfl, ?_, dup, ?_, ?_, store, ?_, run⟩
    · simpa only [← St.self' pre] using push
    · simp only [St.stack, shape]
      rfl
    · intro a x
      exact St.getStorVal
    · intro K _ key value rest stack _
      simp only [St.stack, shape, List.cons.injEq] at stack
      obtain ⟨rfl, rfl, _⟩ := stack
      exact Or.inr (Nat.zero_le _)

private theorem clearTail_pass
    {R : Exec.Deriv} {K : B256 → Prop} {sevm : Sevm} {pre : Devm}
    {seg : Seg} {out : Outcome}
    (run : SFunc.RunCutP (StepIn R) Impl.cert.prog sevm [108] pre
      Impl.t_55d8_c108 seg)
    (back : ∀ d, seg = .at 108 d →
      SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ GuardObs K False s d n)
        Impl.cert.prog sevm d Impl.t_55d8_c108 out)
    (done : ∀ o, seg = .done o → o = out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ GuardObs K False s d n)
      Impl.cert.prog sevm pre Impl.t_55d8_c108 out := by
  unfold Impl.t_55d8_c108 at run ⊢
  cases run with
  | dest burn run =>
    refine SFunc.RunP.dest burn ?_
    iterate 5
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine SFunc.RunP.next ⟨step, by intro impossible; cases impossible⟩ ?_
    cases run with
    | zero dest pop run =>
      refine SFunc.RunP.zero dest pop ?_
      obtain ⟨key, tail, pushed, storePre, storePost, _, push, dup, _, _, store,
        observed, run⟩ := impl_clearTail_body_store_cut run
      unfold Impl.t_55e1_c108
      refine SFunc.RunP.next ⟨push, by intro impossible; cases impossible⟩
        (SFunc.RunP.next ⟨dup, by intro impossible; cases impossible⟩
          (SFunc.RunP.next ⟨store, observed K⟩ ?_))
      iterate 3
        obtain ⟨next, step, run⟩ := ric_nextP run
        refine SFunc.RunP.next ⟨step, by intro impossible; cases impossible⟩ ?_
      cases run with
      | jumpCut dest _ pop => exact SFunc.RunP.jump dest rfl pop (back _ rfl)
      | jump dest notCut _ _ _ => exact (notCut (by decide)).elim
    | succ dest word nonzero pop run =>
      refine SFunc.RunP.succ dest word nonzero pop ?_
      unfold Impl.t_5547_c108 at run ⊢
      cases run with
      | dest burn run =>
        refine SFunc.RunP.dest burn ?_
        iterate 2
          obtain ⟨next, step, run⟩ := ric_nextP run
          refine SFunc.RunP.next ⟨step, by intro impossible; cases impossible⟩ ?_
        cases run with
        | ret dest pop =>
          have final := done _ rfl
          subst out
          exact SFunc.RunP.ret dest pop

/-- Every write in the actual compiled clearing component is non-increasing.
The original derivation provenance, program, initial state and outcome remain
unchanged; no string bound, storage separation or zero seed is assumed. -/
theorem impl_clearTail_nonInc
    {R : Exec.Deriv} {K : B256 → Prop} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP (StepIn R) Impl.cert.prog sevm pre
      Impl.t_55d8_c108 out) :
    SFunc.RunP (fun s d n d' => StepIn R s d n d' ∧ GuardObs K False s d n)
      Impl.cert.prog sevm pre Impl.t_55d8_c108 out := by
  let observed := fun s d n d' => StepIn R s d n d' ∧ GuardObs K False s d n
  let I := fun d => ∀ o, SFunc.RunP observed Impl.cert.prog sevm d Impl.t_55d8_c108 o →
    SFunc.RunP observed Impl.cert.prog sevm pre Impl.t_55d8_c108 o
  have step : ∀ d, I d → ∀ seg,
      SFunc.RunCutP (StepIn R) Impl.cert.prog sevm [108] d Impl.t_55d8_c108 seg →
      match seg with
      | .at _ middle => I middle
      | .done o => SFunc.RunP observed Impl.cert.prog sevm pre Impl.t_55d8_c108 o := by
    intro d continuation seg pass
    cases seg with
    | «at» index middle =>
      intro o rest
      apply continuation o
      exact clearTail_pass pass (by intro d equal; cases equal; exact rest)
        (by intro o equal; cases equal)
    | done o =>
      apply continuation o
      exact clearTail_pass pass (by intro d equal; cases equal)
        (by intro o equal; cases equal; rfl)
  exact SFunc.RunP.loop (k := 108) rfl I
    (fun o => SFunc.RunP observed Impl.cert.prog sevm pre Impl.t_55d8_c108 o)
    step pre out (by intro o rest; exact rest) run

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
