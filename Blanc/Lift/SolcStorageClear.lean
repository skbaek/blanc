import Blanc.Lift.RunPWalk
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.WriteSiteZero

/-!
# The solc storage-string zero-tail component

This source-shaped generalization owns the clearing proof shared by deployed
versions. Its only semantic input is erasure of the actual step relation.
-/

namespace Blanc.Lift.SolcStorageClear

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- The real increment and back edge after the zero store. -/
def tail (back : Bytes) (bound : back.length ≤ 32) (k : Nat) : SFunc :=
  .next (.push [0x01] (by decide)) (.next (.reg .add)
    (.next (.push back bound) (.jump k)))

/-- The actual zero-writing iteration. -/
def body (back : Bytes) (bound : back.length ≤ 32) (k : Nat) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 1))
    (.next (.reg .sstore) (tail back bound k)))

/-- The actual return after the key-range test is finished. -/
def exitTree : SFunc := .dest (.next (.reg .pop) (.next (.reg (.swap 0)) .ret))

/-- The solc comparison and branch, retaining its literal destination words. -/
def head (back exit : Bytes) (backBound : back.length ≤ 32)
    (exitBound : exit.length ≤ 32) (k : Nat) : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .gt)
    (.next (.reg .iszero) (.next (.push exit exitBound)
      (.branch (body back backBound k) exitTree))))))

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc}
  {back exit : Bytes} {backBound : back.length ≤ 32} {exitBound : exit.length ≤ 32}
  {k : Nat}

/-- Recover the actual store and remaining cut, deriving its literal zero. -/
theorem body_store_cut
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {pre : Devm} {C : List Nat} {out : Seg}
    (run : SFunc.RunCutP P fs sevm C pre (body back backBound k) out) :
    ∃ (key : B256) (rest : List B256) (pushed storePre storePost : Devm),
      pre.stack = key :: rest ∧
      P sevm pre (.push [0x00] (by decide)) pushed ∧
      P sevm pushed (.reg (.dup 1)) storePre ∧
      storePre.stack = key :: 0 :: key :: rest ∧
      (∀ a x, storePre.getStorVal a x = pre.getStorVal a x) ∧
      P sevm storePre (.reg .sstore) storePost ∧
      (∀ key value rest, storePre.stack = key :: value :: rest → value = 0) ∧
      SFunc.RunCutP P fs sevm C storePost (tail back backBound k) out := by
  unfold body at run
  rw [St.self' pre] at run
  obtain ⟨pushed, push, run⟩ := ric_nextP run
  obtain ⟨gas₁, rfl⟩ := ri_push (erase push)
  obtain ⟨duplicated, dup, run⟩ := ric_nextP run
  obtain ⟨key, get, gas₂, rfl⟩ := ri_dup_any (erase dup)
  change pre.stack[0]? = some key at get
  cases shape : pre.stack with
  | nil => simp only [shape, List.getElem?_nil, reduceCtorEq] at get
  | cons first rest =>
    simp only [shape, List.getElem?_cons_zero, Option.some.injEq] at get
    subst key
    obtain ⟨storePost, store, run⟩ := ric_nextP run
    refine ⟨first, rest, _, _, storePost, rfl, ?_, dup, ?_, ?_, store, ?_, run⟩
    · simpa only [← St.self' pre] using push
    · simp only [St.stack, shape]
      rfl
    · intro a x
      exact St.getStorVal
    · intro key value rest stack
      simp only [St.stack, shape, List.cons.injEq] at stack
      exact stack.2.1.symm

private theorem pass
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (head back exit backBound exitBound k))
    {sevm : Sevm} {pre : Devm} {seg : Seg} {out : Outcome}
    (run : SFunc.RunCutP P fs sevm [k] pre
      (head back exit backBound exitBound k) seg)
    (recur : ∀ d, seg = .at k d →
      SFunc.RunP (fun s d n d' => P s d n d' ∧ (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧ ∀ x, n ≠ .exec x)
        fs sevm d (head back exit backBound exitBound k) out)
    (done : ∀ o, seg = .done o → o = out) :
    SFunc.RunP (fun s d n d' => P s d n d' ∧ (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧ ∀ x, n ≠ .exec x)
      fs sevm pre (head back exit backBound exitBound k) out := by
  unfold head at run ⊢
  cases run with
  | dest burn run =>
    refine SFunc.RunP.dest burn ?_
    iterate 5
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    cases run with
    | zero dest pop run =>
      refine SFunc.RunP.zero dest pop ?_
      obtain ⟨key, rest, pushed, storePre, storePost, _, push, dup, _, _, store,
        observed, run⟩ := body_store_cut erase run
      unfold body
      refine SFunc.RunP.next ⟨push, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩
        (SFunc.RunP.next ⟨dup, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩
          (SFunc.RunP.next ⟨store, (fun _ => observed), by intro x impossible; cases impossible⟩ ?_))
      unfold tail at run ⊢
      iterate 3
        obtain ⟨next, step, run⟩ := ric_nextP run
        refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
      cases run with
      | jumpCut dest _ pop => exact SFunc.RunP.jump dest entry pop (recur _ rfl)
      | jump dest notCut _ _ _ => exact (notCut (by simp only [List.mem_singleton])).elim
    | succ dest word nonzero pop run =>
      refine SFunc.RunP.succ dest word nonzero pop ?_
      unfold exitTree at run ⊢
      cases run with
      | dest burn run =>
        refine SFunc.RunP.dest burn ?_
        iterate 2
          obtain ⟨next, step, run⟩ := ric_nextP run
          refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        cases run with
        | ret dest pop =>
          have final := done _ rfl
          subst out
          exact SFunc.RunP.ret dest pop

/-- The actual source/table/back-edge run is strengthened with literal-zero
observations. No chosen write list or desired endpoint is supplied. -/
theorem runP_zeroStores_noExec
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (head back exit backBound exitBound k))
    {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP P fs sevm pre (head back exit backBound exitBound k) out) :
    SFunc.RunP (fun s d n d' => P s d n d' ∧ (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧ ∀ x, n ≠ .exec x)
      fs sevm pre (head back exit backBound exitBound k) out := by
  let observed := fun s d n d' => P s d n d' ∧ (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧ ∀ x, n ≠ .exec x
  let I := fun d => ∀ o,
    SFunc.RunP observed fs sevm d (head back exit backBound exitBound k) o →
    SFunc.RunP observed fs sevm pre (head back exit backBound exitBound k) o
  have step : ∀ d, I d → ∀ seg,
      SFunc.RunCutP P fs sevm [k] d (head back exit backBound exitBound k) seg →
      match seg with
      | .at _ middle => I middle
      | .done o => SFunc.RunP observed fs sevm pre (head back exit backBound exitBound k) o := by
    intro d continuation seg passRun
    cases seg with
    | «at» index middle =>
      intro o rest
      apply continuation o
      exact pass erase entry passRun (by intro d equal; cases equal; exact rest)
        (by intro o equal; cases equal)
    | done o =>
      apply continuation o
      exact pass erase entry passRun (by intro d equal; cases equal)
        (by intro o equal; cases equal; rfl)
  exact SFunc.RunP.loop (k := k) entry I
    (fun o => SFunc.RunP observed fs sevm pre (head back exit backBound exitBound k) o)
    step pre out (by intro o rest; exact rest) run

/-- Literal-zero stores of the actual clearing component, forgetting its
additional source-derived external-instruction exclusion. -/
theorem runP_zeroStores
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (head back exit backBound exitBound k))
    {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP P fs sevm pre (head back exit backBound exitBound k) out) :
    SFunc.RunP (fun s d n d' => P s d n d' ∧ (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0))
      fs sevm pre (head back exit backBound exitBound k) out := by
  exact SFunc.RunP.mono (fun step => ⟨step.1, step.2.1⟩)
    (runP_zeroStores_noExec erase entry run)

/-- Literal-zero stores give the existing demanded-row nonincrease interface. -/
theorem runP_nonInc
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (head back exit backBound exitBound k))
    {K : B256 → Prop} {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP P fs sevm pre (head back exit backBound exitBound k) out) :
    SFunc.RunP (fun s d n d' => P s d n d' ∧ GuardObs K False s d n)
      fs sevm pre (head back exit backBound exitBound k) out := by
  refine SFunc.RunP.mono ?_ (runP_zeroStores erase entry run)
  intro s d n d' step
  refine ⟨step.1, ?_⟩
  intro store key value rest stack _
  rw [step.2 store key value rest stack]
  exact Or.inr (Nat.zero_le _)

end Blanc.Lift.SolcStorageClear
