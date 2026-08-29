import Blanc.LinearDispatch
import Blanc.CompiledWalkInversion
import Blanc.SourceAttainment

/-!
  Generic selection correctness for `Blanc.linearDispatchWith`.

  The compiled-run witness packages the exact `Func.RunCompiledTo` body walk
  recovered by the selector route.  Its constructor theorem performs the
  opcode inversions for arbitrary terminal outcomes without mentioning any
  contract's ABI, storage, roles, or outbound calls.
-/

namespace Blanc

open Jaune

def Devm.DispatchFramePreserved (pre post : Devm) : Prop :=
  Devm.Rel
    { Devm.Rels.eq with
      stack := fun _ _ => True
      gasLeft := fun _ _ => True }
    pre post

/-- Dispatch-frame preservation composes across adjacent route segments. -/
theorem Devm.DispatchFramePreserved.trans {a b c : Devm}
    (hab : Devm.DispatchFramePreserved a b)
    (hbc : Devm.DispatchFramePreserved b c) :
    Devm.DispatchFramePreserved a c := by
  constructor
  · trivial
  · exact hab.memory.trans hbc.memory
  · trivial
  · exact hab.logs.trans hbc.logs
  · exact hab.refundCounter.trans hbc.refundCounter
  · exact hab.output.trans hbc.output
  · exact hab.accountsToDelete.trans hbc.accountsToDelete
  · exact hab.returnData.trans hbc.returnData
  · exact hab.error.trans hbc.error
  · exact hab.accessedAddresses.trans hbc.accessedAddresses
  · exact hab.accessedStorageKeys.trans hbc.accessedStorageKeys
  · exact hab.state.trans hbc.state
  · exact hab.createdAccounts.trans hbc.createdAccounts
  · exact hab.transientStorage.trans hbc.transientStorage

theorem dispatchFrame_of_pushBurn {xs : List B256} {a b : Devm}
    (h : Devm.PushBurn xs a b) : Devm.DispatchFramePreserved a b := by
  constructor
  · trivial
  · exact h.memory
  · trivial
  · exact h.logs
  · exact h.refundCounter
  · exact h.output
  · exact h.accountsToDelete
  · exact h.returnData
  · exact h.error
  · exact h.accessedAddresses
  · exact h.accessedStorageKeys
  · exact h.state
  · exact h.createdAccounts
  · exact h.transientStorage

theorem dispatchFrame_of_popBurnBy {xs : List B256} {cost : Nat}
    {a b : Devm} (h : Devm.PopBurnBy xs cost a b) :
    Devm.DispatchFramePreserved a b := by
  constructor
  · trivial
  · exact h.memory
  · trivial
  · exact h.logs
  · exact h.refundCounter
  · exact h.output
  · exact h.accountsToDelete
  · exact h.returnData
  · exact h.error
  · exact h.accessedAddresses
  · exact h.accessedStorageKeys
  · exact h.state
  · exact h.createdAccounts
  · exact h.transientStorage

private theorem dispatchFrame_of_popBurn {xs : List B256} {a b : Devm}
    (h : Devm.PopBurn xs a b) : Devm.DispatchFramePreserved a b := by
  constructor
  · trivial
  · exact h.memory
  · trivial
  · exact h.logs
  · exact h.refundCounter
  · exact h.output
  · exact h.accountsToDelete
  · exact h.returnData
  · exact h.error
  · exact h.accessedAddresses
  · exact h.accessedStorageKeys
  · exact h.state
  · exact h.createdAccounts
  · exact h.transientStorage

theorem dispatchFrame_of_diffBurn {xs ys : List B256} {a b : Devm}
    (h : Devm.DiffBurn xs ys a b) : Devm.DispatchFramePreserved a b := by
  constructor
  · trivial
  · exact h.memory
  · trivial
  · exact h.logs
  · exact h.refundCounter
  · exact h.output
  · exact h.accountsToDelete
  · exact h.returnData
  · exact h.error
  · exact h.accessedAddresses
  · exact h.accessedStorageKeys
  · exact h.state
  · exact h.createdAccounts
  · exact h.transientStorage

private theorem dupFrame {e : Sevm} {a b : Devm}
    (h : Ninst.Run e a (Ninst.dup 0) b) : Devm.DispatchFramePreserved a b := by
  rcases of_run_dup h with ⟨_, _, hpush⟩
  exact dispatchFrame_of_pushBurn hpush

private theorem pushFrame {e : Sevm} {a b : Devm} {x : B256}
    (h : Ninst.Run e a (Ninst.pushB256 x) b) :
    Devm.DispatchFramePreserved a b :=
  dispatchFrame_of_pushBurn (of_run_pushB256 h)

private theorem eqFrame {e : Sevm} {a b : Devm}
    (h : Ninst.Run e a Ninst.eq b) : Devm.DispatchFramePreserved a b := by
  rcases of_run_reg h with ⟨_, hr⟩
  simp only [Rinst.run, Rinst.runCore] at hr
  rcases Devm.diffBurn_of_applyBinary hr with ⟨_, _, hdiff⟩
  exact dispatchFrame_of_diffBurn hdiff

private theorem stack_of_pushBurn {x : B256} {a b : Devm} {xs : Stack}
    (h : Devm.PushBurn [x] a b) (ha : a.stack = xs) :
    b.stack = x :: xs := by
  simpa [Devm.PushBurn, Stack.Push, Split, ha] using h.stack

private theorem stack_of_popBurnBy {x : B256} {cost : Nat} {a b : Devm}
    {xs : Stack} (h : Devm.PopBurnBy [x] cost a b)
    (ha : a.stack = x :: xs) : b.stack = xs := by
  simpa [Devm.PopBurnBy, Stack.Pop, Split, ha] using h.stack.symm

private theorem stack_of_popBurn {x : B256} {a b : Devm} {xs : Stack}
    (h : Devm.PopBurn [x] a b) (ha : a.stack = x :: xs) : b.stack = xs := by
  simpa [Devm.PopBurn, Stack.Pop, Split, ha] using h.stack.symm

private theorem stack_of_dup {e : Sevm} {a b : Devm} {x : B256}
    {xs : Stack} (h : Ninst.Run e a (Ninst.dup 0) b)
    (ha : a.stack = x :: xs) : b.stack = x :: x :: xs := by
  rcases of_run_dup h with ⟨v, hv, hpush⟩
  have hv' : v = x := by simpa [ha] using hv.symm
  subst v
  exact stack_of_pushBurn hpush ha

private theorem stack_of_popRun {e : Sevm} {a b : Devm} {x : B256}
    {xs : Stack} (h : Ninst.Run e a Ninst.pop b)
    (ha : a.stack = x :: xs) : b.stack = xs := by
  rcases of_run_pop h with ⟨v, hpop⟩
  have hv : v = x := by
    have : a.stack = v :: b.stack := by
      simpa [Devm.PopBurn, Stack.Pop, Split] using hpop.stack
    rw [ha] at this
    exact (List.cons.inj this).1.symm
  subst v
  simpa [Devm.PopBurn, Stack.Pop, Split, ha] using hpop.stack.symm

private theorem stack_of_diffBurn {x y z : B256} {a b : Devm} {xs : Stack}
    (h : Devm.DiffBurn [x, y] [z] a b)
    (ha : a.stack = x :: y :: xs) : b.stack = z :: xs := by
  rcases h.stack with ⟨mid, hpop, hpush⟩
  simp only [Stack.Pop, Stack.Push, Split] at hpop hpush
  rw [ha] at hpop
  have hpop' : x :: y :: xs = x :: y :: mid := by
    simpa [List.cons_append, List.nil_append] using hpop
  have htail : xs = mid := by
    exact (List.cons.inj (List.cons.inj hpop').2).2
  subst mid
  simpa [List.cons_append, List.nil_append] using hpush

private theorem stack_of_eqRun {e : Sevm} {a b : Devm}
    {x y : B256} {xs : Stack} (h : Ninst.Run e a Ninst.eq b)
    (ha : a.stack = x :: y :: xs) : b.stack = (x =? y) :: xs := by
  rcases of_run_reg h with ⟨_, hr⟩
  simp only [Rinst.run, Rinst.runCore] at hr
  rcases Devm.diffBurn_of_applyBinary hr with ⟨x', y', hdiff⟩
  rcases hdiff.stack with ⟨mid, hpop, hpush⟩
  simp only [Stack.Pop, Stack.Push, Split] at hpop hpush
  have hpre : x :: y :: xs = x' :: y' :: mid := by
    simpa [ha, List.cons_append, List.nil_append] using hpop
  have hxy : x = x' := (List.cons.inj hpre).1
  have htail' : y :: xs = y' :: mid := (List.cons.inj hpre).2
  have hy : y = y' := (List.cons.inj htail').1
  have htail : xs = mid := (List.cons.inj htail').2
  subst x'
  subst y'
  subst mid
  simpa only [List.cons_append, List.nil_append] using hpush

private theorem runCompiledTo_three_inv
    {fs : List Func} {sevm : Sevm} {a : Devm}
    {i j k : Ninst} {f : Func} {out : Execution}
    (h : Func.RunCompiledTo fs sevm a (i ::: j ::: k ::: f) out) :
    ∃ a1 a2 a3,
      Ninst.Run sevm a i a1 ∧
        Ninst.Run sevm a1 j a2 ∧
          Ninst.Run sevm a2 k a3 ∧
            Func.RunCompiledTo fs sevm a3 f out := by
  obtain ⟨a1, hi, h⟩ := runCompiledTo_next_inv h
  obtain ⟨a2, hj, h⟩ := runCompiledTo_next_inv h
  obtain ⟨a3, hk, h⟩ := runCompiledTo_next_inv h
  exact ⟨a1, a2, a3, Ninst.Run.of_runCompiled hi,
    Ninst.Run.of_runCompiled hj, Ninst.Run.of_runCompiled hk, h⟩

def DispatchBodyWitness
    (fs : List Func) (sevm : Sevm) (entry : Devm)
    (entries : List (B256 × Func))
    (selector : B256) (tail : Stack) (body : Func)
    (out : Execution) : Prop :=
  ∃ bodyPre,
    (selector, body) ∈ entries ∧
      Func.RunCompiledTo fs sevm bodyPre body out ∧
      bodyPre.stack = tail ∧
      Devm.DispatchFramePreserved entry bodyPre

theorem exists_selected_split
    {α : Type} {entries : List α} {selected : α}
    (hmem : selected ∈ entries) :
    ∃ pre suffix, entries = pre ++ selected :: suffix := by
  induction entries with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact ⟨[], tail, rfl⟩
      · rcases ih htail with ⟨pre, suffix, hs⟩
        exact ⟨head :: pre, suffix, by simp [hs]⟩

theorem selectorUnique_prefix_ne
    {pre suffix : List (B256 × Func)} {selected candidate : B256 × Func}
    (huniq : selectorUnique (pre ++ selected :: suffix))
    (hmem : candidate ∈ pre) :
    candidate.1 ≠ selected.1 := by
  induction pre with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      have hpairs :
          (head :: (tail ++ selected :: suffix)).Pairwise
            (fun a b : B256 × Func => a.1 ≠ b.1) := by
        simpa [selectorUnique] using huniq
      rcases hmem with rfl | htail
      · exact (List.pairwise_cons.mp hpairs).1 selected (by simp)
      · exact ih (List.pairwise_cons.mp hpairs).2 htail

private theorem dispatch_select_prefix
    {fs : List Func} {sevm : Sevm}
    {fallback : Nat} {selector : B256} {tail : Stack}
    {body : Func} {out : Execution} :
    ∀ (pre suffix : List (B256 × Func)),
      (entry : Devm) →
      (∀ candidate ∈ pre, candidate.1 ≠ selector) →
      Func.RunCompiledTo fs sevm entry
        (Blanc.linearDispatchWith fallback
          (pre ++ (selector, body) :: suffix)) out →
      entry.stack = selector :: tail →
      ∃ bodyPre, Func.RunCompiledTo fs sevm bodyPre body out ∧
        bodyPre.stack = tail ∧
        Devm.DispatchFramePreserved entry bodyPre := by
  intro pre
  induction pre with
  | nil =>
      intro suffix entry hbefore hrun hstack
      cases suffix with
      | nil =>
          change Func.RunCompiledTo fs sevm entry
            ([Ninst.pushB256 selector, Ninst.eq] +++
              (body <?> .call fallback)) out at hrun
          obtain ⟨afterLine, hline, hbranch⟩ :=
            runCompiledTo_prepend_inv hrun
          rcases Line.of_run_cons hline with
            ⟨afterPush, hpush, hrest⟩
          rcases Line.of_run_cons hrest with
            ⟨afterEq, heq, hnil⟩
          have hlineEq : afterLine = afterEq := by cases hnil; rfl
          subst afterLine
          have hpushStack : afterPush.stack = selector :: selector :: tail :=
            stack_of_pushBurn (of_run_pushB256 hpush) hstack
          have hflagStack : afterEq.stack = (selector =? selector) :: tail :=
            stack_of_eqRun heq hpushStack
          have hflag : afterEq.stack = (1 : B256) :: tail := by
            rw [hflagStack]
            simp [B256.eqCheck]
          have hlineFrame : Devm.DispatchFramePreserved entry afterEq :=
            (pushFrame hpush).trans (eqFrame heq)
          rcases runCompiledTo_branch_inv hbranch with
            ⟨armPre, hzero, hpop, harm⟩ |
            ⟨w, armPre, hw, hwstack, hpop, harm⟩
          · have : (1 : B256) = 0 :=
              (List.cons.inj (hflag.symm.trans hzero)).1
            exact ((by decide : (1 : B256) ≠ 0) this).elim
          · have hw' : w = 1 := by
              exact (List.cons.inj (hflag.symm.trans hwstack)).1.symm
            subst w
            have hbodyStack : armPre.stack = tail :=
              stack_of_popBurnBy hpop hflag
            exact ⟨armPre, harm, hbodyStack,
              hlineFrame.trans
                (dispatchFrame_of_popBurnBy hpop)⟩
      | cons head suffix' =>
          rcases head with ⟨headSelector, headBody⟩
          have hrun' : Func.RunCompiledTo fs sevm entry
              (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.eq :::
                ((Ninst.pop ::: body) <?>
                  Blanc.linearDispatchWith fallback
                    ((headSelector, headBody) :: suffix'))) out := by
            simpa [Blanc.linearDispatchWith] using hrun
          obtain ⟨afterDup, afterPush, afterEq, hdup, hpush, heq, hbranch⟩ :=
            runCompiledTo_three_inv hrun'
          have hdupStack : afterDup.stack = selector :: selector :: tail :=
            stack_of_dup hdup hstack
          have hpushStack : afterPush.stack = selector :: selector :: selector :: tail :=
            stack_of_pushBurn (of_run_pushB256 hpush) hdupStack
          have hflagStack : afterEq.stack =
              (selector =? selector) :: selector :: tail :=
            stack_of_eqRun heq hpushStack
          have hflag : afterEq.stack = (1 : B256) :: selector :: tail := by
            rw [hflagStack]
            simp [B256.eqCheck]
          have hlineFrame : Devm.DispatchFramePreserved entry afterEq :=
            (dupFrame hdup).trans
              ((pushFrame hpush).trans (eqFrame heq))
          rcases runCompiledTo_branch_inv hbranch with
            ⟨armPre, hzero, hpop, harm⟩ |
            ⟨w, armPre, hw, hwstack, hpop, harm⟩
          · have : (1 : B256) = 0 :=
              (List.cons.inj (hflag.symm.trans hzero)).1
            exact ((by decide : (1 : B256) ≠ 0) this).elim
          · have hw' : w = 1 := by
              exact (List.cons.inj (hflag.symm.trans hwstack)).1.symm
            subst w
            have harmStack : armPre.stack = selector :: tail :=
              stack_of_popBurnBy hpop hflag
            obtain ⟨afterPop, hpopCompiled, hbody⟩ :=
              runCompiledTo_next_inv harm
            have hpopRun := Ninst.Run.of_runCompiled hpopCompiled
            let bodyPre := afterPop
            rcases of_run_pop hpopRun with ⟨v, hpopBurn⟩
            have hv : v = selector := by
              have : armPre.stack = v :: afterPop.stack := by
                simpa [Devm.PopBurn, Stack.Pop, Split] using hpopBurn.stack
              rw [harmStack] at this
              exact (List.cons.inj this).1.symm
            subst v
            have hbodyStack : bodyPre.stack = tail := by
              exact stack_of_popBurn hpopBurn harmStack
            exact ⟨bodyPre, hbody, hbodyStack,
              hlineFrame.trans
                ((dispatchFrame_of_popBurnBy hpop).trans
                  (dispatchFrame_of_popBurn hpopBurn))⟩
  | cons head pre ih =>
      intro suffix entry hbefore hrun hstack
      rcases head with ⟨headSelector, headBody⟩
      have hrun' : Func.RunCompiledTo fs sevm entry
          (Ninst.dup 0 ::: Ninst.pushB256 headSelector ::: Ninst.eq :::
            ((Ninst.pop ::: headBody) <?>
              Blanc.linearDispatchWith fallback
                (pre ++ (selector, body) :: suffix))) out := by
        simpa [Blanc.linearDispatchWith] using hrun
      obtain ⟨afterDup, afterPush, afterEq, hdup, hpush, heq, hbranch⟩ :=
        runCompiledTo_three_inv hrun'
      have hdupStack : afterDup.stack = selector :: selector :: tail :=
        stack_of_dup hdup hstack
      have hpushStack : afterPush.stack =
          headSelector :: selector :: selector :: tail :=
        stack_of_pushBurn (of_run_pushB256 hpush) hdupStack
      have hflagStack : afterEq.stack =
          (headSelector =? selector) :: selector :: tail :=
        stack_of_eqRun heq hpushStack
      have hne : headSelector ≠ selector := by
        exact hbefore (headSelector, headBody) (by simp)
      have hflag : afterEq.stack = (0 : B256) :: selector :: tail := by
        rw [hflagStack]
        simp [B256.eqCheck, hne]
      have hlineFrame : Devm.DispatchFramePreserved entry afterEq :=
        (dupFrame hdup).trans
          ((pushFrame hpush).trans (eqFrame heq))
      rcases runCompiledTo_branch_inv hbranch with
        ⟨armPre, hzero, hpop, harm⟩ |
        ⟨w, armPre, hw, hwstack, hpop, harm⟩
      · have harmStack : armPre.stack = selector :: tail :=
          stack_of_popBurnBy hpop hflag
        obtain ⟨bodyPre, hbody, hbodyStack, hbodyFrame⟩ :=
          ih suffix armPre (fun candidate hmem =>
            hbefore candidate (by simp [hmem])) harm harmStack
        exact ⟨bodyPre, hbody, hbodyStack,
          hlineFrame.trans
            ((dispatchFrame_of_popBurnBy hpop).trans
              hbodyFrame)⟩
      · have : (0 : B256) ≠ w := by
          exact fun h => hw h.symm
        have hbad : (0 : B256) = w :=
          (List.cons.inj (hflag.symm.trans hwstack)).1
        exact False.elim (this hbad)

/-- An exact compiled walk through a selector-unique linear dispatcher reaches
the caller-supplied selected body, with the selector removed and every entry
frame field except stack and gas preserved. -/
theorem dispatchBodyWitness_of_runCompiledTo
    {fs : List Func} {sevm : Sevm} {entry : Devm}
    {fallback : Nat} {entries : List (B256 × Func)}
    {selector : B256} {tail : Stack} {body : Func} {out : Execution}
    (huniq : selectorUnique entries)
    (hmember : (selector, body) ∈ entries)
    (hstack : entry.stack = selector :: tail)
    (hwalk : Func.RunCompiledTo fs sevm entry
      (Blanc.linearDispatchWith fallback entries) out) :
    DispatchBodyWitness fs sevm entry entries selector tail body out := by
  obtain ⟨pre, suffix, hsplit⟩ := exists_selected_split hmember
  rw [hsplit] at hwalk
  have hbefore : ∀ candidate ∈ pre, candidate.1 ≠ selector := by
    intro candidate hcandidate
    exact selectorUnique_prefix_ne (by simpa [hsplit] using huniq) hcandidate
  obtain ⟨bodyPre, hbody, hbodyStack, hframe⟩ :=
    dispatch_select_prefix pre suffix entry hbefore hwalk hstack
  exact ⟨bodyPre, hmember, hbody, hbodyStack, hframe⟩

end Blanc
