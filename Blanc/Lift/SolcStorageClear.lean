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

/-- The literal-zero/no-external-execution enrichment shared by the compact
and legacy clearing layouts. -/
private abbrev enrichZeroNoExec (P : Sevm → Devm → Ninst → Devm → Prop) :
    Sevm → Devm → Ninst → Devm → Prop :=
  fun s d n d' => P s d n d' ∧
    (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧
    ∀ x, n ≠ .exec x

/-- The comparison head both clearing layouts share: invert the destination,
the five test instructions and the branch, then delegate each arm to its
layout-specific case. -/
private theorem headBranchPass
    {headTree storeArm exitArm : SFunc} {exitBytes : Bytes} {exitBound : exitBytes.length ≤ 32}
    (hunfold : headTree = .dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .gt)
      (.next (.reg .iszero) (.next (.push exitBytes exitBound)
        (.branch storeArm exitArm)))))))
    {sevm pre seg out}
    (run : SFunc.RunCutP P fs sevm [k] pre headTree seg)
    (recur : ∀ d, seg = .at k d →
      SFunc.RunP (enrichZeroNoExec P) fs sevm d headTree out)
    (done : ∀ o, seg = .done o → o = out)
    (storeCase : ∀ {mid}, SFunc.RunCutP P fs sevm [k] mid storeArm seg →
      (∀ d, seg = .at k d → SFunc.RunP (enrichZeroNoExec P) fs sevm d headTree out) →
      SFunc.RunP (enrichZeroNoExec P) fs sevm mid storeArm out)
    (exitCase : ∀ {mid}, SFunc.RunCutP P fs sevm [k] mid exitArm seg →
      (∀ o, seg = .done o → o = out) →
      SFunc.RunP (enrichZeroNoExec P) fs sevm mid exitArm out) :
    SFunc.RunP (enrichZeroNoExec P) fs sevm pre headTree out := by
  subst hunfold
  cases run with
  | dest burn run =>
    refine SFunc.RunP.dest burn ?_
    iterate 5
      obtain ⟨next, step, run⟩ := ric_nextP run
      refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    cases run with
    | zero dest pop run =>
      refine SFunc.RunP.zero dest pop ?_
      exact storeCase run recur
    | succ dest word nonzero pop run =>
      refine SFunc.RunP.succ dest word nonzero pop ?_
      exact exitCase run done

private theorem compactStoreCase
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (head back exit backBound exitBound k))
    {mid seg out}
    (run : SFunc.RunCutP P fs sevm [k] mid (body back backBound k) seg)
    (recur : ∀ d, seg = .at k d →
      SFunc.RunP (enrichZeroNoExec P) fs sevm d (head back exit backBound exitBound k) out) :
    SFunc.RunP (enrichZeroNoExec P) fs sevm mid (body back backBound k) out := by
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

private theorem compactExitCase
    {mid seg out}
    (run : SFunc.RunCutP P fs sevm [k] mid exitTree seg)
    (done : ∀ o, seg = .done o → o = out) :
    SFunc.RunP (enrichZeroNoExec P) fs sevm mid exitTree out := by
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

private theorem pass
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (head back exit backBound exitBound k))
    {sevm : Sevm} {pre : Devm} {seg : Seg} {out : Outcome}
    (run : SFunc.RunCutP P fs sevm [k] pre
      (head back exit backBound exitBound k) seg)
    (recur : ∀ d, seg = .at k d →
      SFunc.RunP (enrichZeroNoExec P)
        fs sevm d (head back exit backBound exitBound k) out)
    (done : ∀ o, seg = .done o → o = out) :
    SFunc.RunP (enrichZeroNoExec P)
      fs sevm pre (head back exit backBound exitBound k) out := by
  exact headBranchPass rfl run recur done
    (compactStoreCase erase entry) compactExitCase

/-- The back-edge fold both clearing layouts share: one per-iteration pass
supplies every loop iteration, `SFunc.RunP.loop` closes the loop. -/
private theorem runP_zeroStores_noExec_of_pass
    {g : SFunc}
    (entry : fs[k]? = some g)
    (passRun : ∀ {sevm pre seg out}, SFunc.RunCutP P fs sevm [k] pre g seg →
      (∀ d, seg = .at k d →
        SFunc.RunP (enrichZeroNoExec P) fs sevm d g out) →
      (∀ o, seg = .done o → o = out) →
      SFunc.RunP (enrichZeroNoExec P) fs sevm pre g out)
    {sevm pre out}
    (run : SFunc.RunP P fs sevm pre g out) :
    SFunc.RunP (enrichZeroNoExec P) fs sevm pre g out := by
  let I := fun d => ∀ o,
    SFunc.RunP (enrichZeroNoExec P) fs sevm d g o →
    SFunc.RunP (enrichZeroNoExec P) fs sevm pre g o
  have step : ∀ d, I d → ∀ seg,
      SFunc.RunCutP P fs sevm [k] d g seg →
      match seg with
      | .at _ middle => I middle
      | .done o => SFunc.RunP (enrichZeroNoExec P) fs sevm pre g o := by
    intro d continuation seg passRunCut
    cases seg with
    | «at» index middle =>
      intro o rest
      apply continuation o
      exact passRun passRunCut (by intro d equal; cases equal; exact rest)
        (by intro o equal; cases equal)
    | done o =>
      apply continuation o
      exact passRun passRunCut (by intro d equal; cases equal)
        (by intro o equal; cases equal; rfl)
  exact SFunc.RunP.loop (k := k) entry I
    (fun o => SFunc.RunP (enrichZeroNoExec P) fs sevm pre g o)
    step pre out (by intro o rest; exact rest) run

/-- The actual source/table/back-edge run is strengthened with literal-zero
observations. No chosen write list or desired endpoint is supplied. -/
theorem runP_zeroStores_noExec
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (head back exit backBound exitBound k))
    {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP P fs sevm pre (head back exit backBound exitBound k) out) :
    SFunc.RunP (fun s d n d' => P s d n d' ∧ (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧ ∀ x, n ≠ .exec x)
      fs sevm pre (head back exit backBound exitBound k) out := by
  exact runP_zeroStores_noExec_of_pass entry (pass erase entry) run

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

/-! ## Legacy indirect-exit layout

The legacy solc clearing loop keeps the same comparison head but stages its
store as `.push [0x00]`, `.dup 1` (DUP2), `.push [0x00]`, `.swap 0` (SWAP1),
`.sstore`, leaving a spare zero the tail pops after the store. Its exit does
not return inline: it jumps through the shared return table entry `j`
(`.dest`, `.swap 0` (SWAP1), `.ret`). -/

variable {j : Nat}

/-- The legacy increment and back edge after the zero store, popping the
spare zero the legacy staging leaves above the key. -/
def legacyStoreTail (back : Bytes) (bound : back.length ≤ 32) (k : Nat) : SFunc :=
  .next (.reg .pop) (.next (.push [0x01] (by decide)) (.next (.reg .add)
    (.next (.push back bound) (.jump k))))

/-- The legacy zero-writing iteration. The spare push-zero/swap pair keeps
the key on top across the store: `.push [0x00]` after `.dup 1` (DUP2), then
`.swap 0` (SWAP1) before `.sstore`. -/
def legacyBody (back : Bytes) (bound : back.length ≤ 32) (k : Nat) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 1))
    (.next (.push [0x00] (by decide)) (.next (.reg (.swap 0))
      (.next (.reg .sstore) (legacyStoreTail back bound k)))))

/-- The legacy exit through the shared return table entry `j`. -/
def legacyExit (j : Nat) : SFunc :=
  .dest (.next (.reg .pop) (.next (.reg (.swap 0)) (.jump j)))

/-- The shared return table entry the legacy exit jumps through. -/
def legacyRet : SFunc := .dest (.next (.reg (.swap 0)) .ret)

/-- The legacy solc comparison and branch, retaining its literal destination
words and routing the exit through table entry `j`. -/
def legacyHead (back exit : Bytes) (backBound : back.length ≤ 32)
    (exitBound : exit.length ≤ 32) (k j : Nat) : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .gt)
    (.next (.reg .iszero) (.next (.push exit exitBound)
      (.branch (legacyBody back backBound k) (legacyExit j)))))))

/-- Recover the legacy store and remaining cut, deriving its literal zero. -/
theorem legacyBody_store_cut
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {pre : Devm} {C : List Nat} {out : Seg}
    (run : SFunc.RunCutP P fs sevm C pre (legacyBody back backBound k) out) :
    ∃ (key : B256) (rest : List B256) (pushed duped pushed2 swapped storePost : Devm),
      pre.stack = key :: rest ∧
      P sevm pre (.push [0x00] (by decide)) pushed ∧
      P sevm pushed (.reg (.dup 1)) duped ∧
      P sevm duped (.push [0x00] (by decide)) pushed2 ∧
      P sevm pushed2 (.reg (.swap 0)) swapped ∧
      swapped.stack = key :: 0 :: 0 :: key :: rest ∧
      (∀ a x, swapped.getStorVal a x = pre.getStorVal a x) ∧
      P sevm swapped (.reg .sstore) storePost ∧
      (∀ key value rest, swapped.stack = key :: value :: rest → value = 0) ∧
      SFunc.RunCutP P fs sevm C storePost (legacyStoreTail back backBound k) out := by
  unfold legacyBody at run
  rw [St.self' pre] at run
  obtain ⟨pushed, push, run⟩ := ric_nextP run
  obtain ⟨gas₁, rfl⟩ := ri_push (erase push)
  obtain ⟨duped, dup, run⟩ := ric_nextP run
  obtain ⟨key, get, gas₂, rfl⟩ := ri_dup_any (erase dup)
  change pre.stack[0]? = some key at get
  cases shape : pre.stack with
  | nil => simp only [shape, List.getElem?_nil, reduceCtorEq] at get
  | cons first rest =>
    simp only [shape, List.getElem?_cons_zero, Option.some.injEq] at get
    subst key
    obtain ⟨pushed2, push2, run⟩ := ric_nextP run
    obtain ⟨gas₃, rfl⟩ := ri_push (erase push2)
    obtain ⟨swapped, swap, run⟩ := ric_nextP run
    simp only [shape] at push dup push2 swap run
    have hswap : Jaune.List.swap (0 :: first :: 0 :: first :: rest) ((0 : Fin 16).val) =
        some (first :: 0 :: 0 :: first :: rest) := rfl
    obtain ⟨gas₄, rfl⟩ := ri_swap hswap (erase swap)
    obtain ⟨storePost, store, run⟩ := ric_nextP run
    refine ⟨first, rest, _, _, _, _, _, rfl, ?_, dup, push2, swap, ?_, ?_, store, ?_, run⟩
    · have hpre : pre = St pre (first :: rest) pre.memory pre.gasLeft :=
        (St.self' pre).trans (by rw [shape])
      rw [hpre]
      exact push
    · simp only [St.stack]
    · intro a x
      exact St.getStorVal
    · intro key value rest stack
      simp only [St.stack, List.cons.injEq] at stack
      exact stack.2.1.symm

private theorem legacyStoreCase
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (legacyHead back exit backBound exitBound k j))
    {mid seg out}
    (run : SFunc.RunCutP P fs sevm [k] mid (legacyBody back backBound k) seg)
    (recur : ∀ d, seg = .at k d →
      SFunc.RunP (enrichZeroNoExec P) fs sevm d (legacyHead back exit backBound exitBound k j) out) :
    SFunc.RunP (enrichZeroNoExec P) fs sevm mid (legacyBody back backBound k) out := by
  obtain ⟨key, rest, pushed, duped, pushed2, swapped, storePost, _, push, dup,
    push2, swap, _, _, store, observed, run⟩ := legacyBody_store_cut erase run
  unfold legacyBody
  refine SFunc.RunP.next ⟨push, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩
    (SFunc.RunP.next ⟨dup, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩
      (SFunc.RunP.next ⟨push2, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩
        (SFunc.RunP.next ⟨swap, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩
          (SFunc.RunP.next ⟨store, (fun _ => observed), by intro x impossible; cases impossible⟩ ?_))))
  unfold legacyStoreTail at run ⊢
  iterate 4
    obtain ⟨next, step, run⟩ := ric_nextP run
    refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
  cases run with
  | jumpCut dest _ pop => exact SFunc.RunP.jump dest entry pop (recur _ rfl)
  | jump dest notCut _ _ _ => exact (notCut (by simp only [List.mem_singleton])).elim

private theorem legacyExitCase
    (retEntry : fs[j]? = some legacyRet)
    (jk : j ≠ k)
    {mid seg out}
    (run : SFunc.RunCutP P fs sevm [k] mid (legacyExit j) seg)
    (done : ∀ o, seg = .done o → o = out) :
    SFunc.RunP (enrichZeroNoExec P) fs sevm mid (legacyExit j) out := by
  unfold legacyExit at run ⊢
  cases run with
  | dest burn run =>
    refine SFunc.RunP.dest burn ?_
    obtain ⟨next, step, run⟩ := ric_nextP run
    refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    obtain ⟨next, step, run⟩ := ric_nextP run
    refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
    cases run with
    | jumpCut _ mem _ => exact (jk (List.mem_singleton.mp mem)).elim
    | jump d _ get pop cont =>
      cases Option.some.inj (get.symm.trans retEntry)
      refine SFunc.RunP.jump d retEntry pop ?_
      unfold legacyRet at cont ⊢
      cases cont with
      | dest burn run =>
        refine SFunc.RunP.dest burn ?_
        obtain ⟨next, step, run⟩ := ric_nextP run
        refine SFunc.RunP.next ⟨step, (by intro impossible; cases impossible), by intro x impossible; cases impossible⟩ ?_
        cases run with
        | ret dest pop =>
          have final := done _ rfl
          subst out
          exact SFunc.RunP.ret dest pop

private theorem legacyPass
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (legacyHead back exit backBound exitBound k j))
    (retEntry : fs[j]? = some legacyRet)
    (jk : j ≠ k)
    {sevm : Sevm} {pre : Devm} {seg : Seg} {out : Outcome}
    (run : SFunc.RunCutP P fs sevm [k] pre
      (legacyHead back exit backBound exitBound k j) seg)
    (recur : ∀ d, seg = .at k d →
      SFunc.RunP (enrichZeroNoExec P)
        fs sevm d (legacyHead back exit backBound exitBound k j) out)
    (done : ∀ o, seg = .done o → o = out) :
    SFunc.RunP (enrichZeroNoExec P)
      fs sevm pre (legacyHead back exit backBound exitBound k j) out := by
  exact headBranchPass rfl run recur done
    (legacyStoreCase erase entry) (legacyExitCase retEntry jk)

/-- The actual legacy source/table/back-edge run is strengthened with
literal-zero observations. No chosen write list or desired endpoint is
supplied; the exit is followed through the shared return entry `j`. -/
theorem legacyRunP_zeroStores_noExec
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (entry : fs[k]? = some (legacyHead back exit backBound exitBound k j))
    (retEntry : fs[j]? = some legacyRet)
    (jk : j ≠ k)
    {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.RunP P fs sevm pre (legacyHead back exit backBound exitBound k j) out) :
    SFunc.RunP (fun s d n d' => P s d n d' ∧ (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧ ∀ x, n ≠ .exec x)
      fs sevm pre (legacyHead back exit backBound exitBound k j) out := by
  exact runP_zeroStores_noExec_of_pass entry (legacyPass erase entry retEntry jk) run

end Blanc.Lift.SolcStorageClear
