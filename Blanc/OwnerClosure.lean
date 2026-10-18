import Blanc.OwnerDiscipline
import Blanc.ExecutionSettledOwnCode

/-!
# Storage-owner discipline for a code family closed under delegation

`Exec.ownerCode_of_world` (`Blanc/OwnerDiscipline.lean`) covers one level of delegation: an
EIP-1167 forwarder in front of a code that delegates nowhere.  This module covers any number of
levels.  A predicate `S` on codes is *delegation-closed* along a run when every committed frame
owning `P`'s storage that runs a code of `S` decodes no `CALLCODE`, and each `DELEGATECALL` it
decodes names an undelegated account holding a code of `S` (`Exec.DelegationClosed`).  Then every
committed frame owning `P`'s storage runs a code of `S` (`Exec.ownerCode_of_closed`), given that `P`
holds a code of `S`, the root runs one when it owns `P`, and the codes of `S` are nonempty and no
EIP-7702 designators.

The induction runs over committed frames (`Exec.descendantFrames`), not raw frame roots: the closure
premise is stated only for committed frames, so a reverted subtree is never entered.  Owner-`P`
frames arise from a `CALL`/`STATICCALL` into `P` (the code at `P`, preserved because it is nonempty),
a `DELEGATECALL` from an owner-`P` frame (a code of `S` by closure), or a message from a frame at
another account into `P` (the code at `P` again); `CALLCODE` is excluded by closure, and a create
never targets `P`, which has code.
-/

namespace Blanc

open Jaune

/-- Along `run`, every committed frame owning `P`'s storage that runs a code of `S` decodes no
`CALLCODE`, and each `DELEGATECALL` it decodes names an undelegated account holding a code of `S`. -/
def Exec.DelegationClosed {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (P : Adr) (S : ByteArray → Prop) : Prop :=
  ∀ F ∈ Exec.committedFrames run, F.sevm.currentTarget = P → S F.sevm.code →
    ∀ n, Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv F) n →
      ¬ Xinst.At n.sevm.code n.pc .callcode ∧
      (Xinst.At n.sevm.code n.pc .delegatecall → ∀ (g a : B256) (rest : List B256),
        n.devm.stack = g :: a :: rest →
          S (n.devm.getCode a.toAdr) ∧ getDelegatedCodeAddress (n.devm.getCode a.toAdr) = none)

/-- A spawning `DELEGATECALL` had at least its gas and address operands on the stack. -/
theorem Xinst.step_delegatecall_spawn_stack {sevm : Sevm} {devm : Devm} {f : Frame}
    {rsm : Resume} (spawn : Xinst.step sevm devm .delegatecall = .spawn f rsm) :
    ∃ (g a : B256) (rest : List B256), devm.stack = g :: a :: rest := by
  rcases hs : devm.stack with _ | ⟨g, _ | ⟨a, rest⟩⟩
  · have h1 : devm.pop = .error ⟨.halt (.stackUnderflow .none), devm⟩ := by
      rw [Devm.pop_def, hs]
    cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_error,
        reduceCtorEq] at spawn
  · have h1 := Devm.pop_eq_ok hs
    have hs1 : (devm.setMach ⟨[], devm.memory, devm.gasLeft, devm.stateGas⟩).stack = [] := rfl
    generalize devm.setMach ⟨[], devm.memory, devm.gasLeft, devm.stateGas⟩ = d1 at h1 hs1
    have h2 : d1.popToAdr = .error ⟨.halt (.stackUnderflow .none), d1⟩ := by
      rw [Devm.popToAdr_def, Devm.pop_def, hs1]; rfl
    cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, h2, bind_pure_comp, Except.bind_ok,
        Except.bind_error, reduceCtorEq] at spawn
  · exact ⟨g, a, rest, rfl⟩

/-- The closure condition at one same-frame node `n`. -/
private def DelegatesWithin (S : ByteArray → Prop) (n : Exec.Deriv) : Prop :=
  ¬ Xinst.At n.sevm.code n.pc .callcode ∧
  (Xinst.At n.sevm.code n.pc .delegatecall → ∀ (g a : B256) (rest : List B256),
    n.devm.stack = g :: a :: rest →
      S (n.devm.getCode a.toAdr) ∧ getDelegatedCodeAddress (n.devm.getCode a.toAdr) = none)

private theorem size_pos_toList_ne_nil {c : ByteArray} (h : 0 < c.size) : c.toList ≠ [] := by
  intro hnil
  have := ByteArray.size_eq_length_toList c
  rw [hnil, List.length_nil] at this
  omega

private theorem size_pos_ne_empty {c : ByteArray} (h : 0 < c.size) : c ≠ .empty := by
  rintro rfl; exact absurd h (by decide)

/-- **Owner closure below a frame.**  Along the chain of a frame `R` whose world holds `c₀ ∈ S` at
`P`, which runs a code of `S` if it owns `P`, and whose own nodes (and those of every committed
descendant owning `P` with a code of `S`) satisfy the closure condition, every committed descendant
frame owning `P` runs a code of `S`. -/
private theorem Exec.descendantFrames_closed {P : Adr} {S : ByteArray → Prop} {c₀ : ByteArray}
    (nonempty : ∀ c, S c → 0 < c.size) (undesignated : ∀ c, S c → ¬ isValidDelegation c)
    (hc₀ : S c₀) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
      {R : Exec.Deriv}, Exec.Deriv.ParentPrefix R ⟨pc, sevm, pre, out, run⟩ →
      R.devm.getCode P = c₀ → (R.sevm.currentTarget = P → S R.sevm.code) →
      (R.sevm.currentTarget = P → S R.sevm.code →
        ∀ n, Exec.Deriv.ParentPrefix R n → DelegatesWithin S n) →
      (∀ F ∈ Exec.descendantFrames run, F.sevm.currentTarget = P → S F.sevm.code →
        ∀ n, Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv F) n → DelegatesWithin S n) →
      ∀ G ∈ Exec.descendantFrames run, G.sevm.currentTarget = P → S G.sevm.code := by
  have c₀ne : c₀ ≠ .empty := size_pos_ne_empty (nonempty _ hc₀)
  have c₀nd : ¬ isValidDelegation c₀ := undesignated _ hc₀
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ _ _ _ _ _ G member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro R chain code own free closed
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.cont step next)) code own free (by
          simpa only [Exec.descendantFrames] using closed)
  | doneErr _ _ _ =>
      intro _ _ _ _ _ _ G member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro R chain code own free closed
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.doneOk step enter resume next)) code own free (by
          simpa only [Exec.descendantFrames] using closed)
  | runErr _ _ _ _ =>
      intro _ _ _ _ _ _ G member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro R chain code own free closed G member
      have sevmEq : nodeSevm = R.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
      have nodeCode : nodePre.getCode P = c₀ :=
        ((Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 P
          (by rw [code]; exact size_pos_toList_ne_nil (nonempty _ hc₀))).trans code
      obtain ⟨pcZero', getCode, codeSource⟩ := Evm.step_spawn_child hstep henter
      have childCode : cevm.dyna.getCode P = c₀ := (getCode P).trans nodeCode
      have childOwn : cevm.sta.currentTarget = P → S cevm.sta.code := by
        intro target
        have frameTarget : frame.inner.currentTarget = P := by
          rw [← Frame.enter_run_currentTarget henter, target]
        rw [Frame.enter_run_code henter]
        by_cases same : nodeSevm.currentTarget = P
        · have ownCode : S R.sevm.code := own (sevmEq ▸ same)
          have nodeOk := free (sevmEq ▸ same) ownCode _ chain
          obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv hstep
          have notDel : ¬ isValidDelegation (nodePre.getCode frame.inner.currentTarget) := by
            rw [frameTarget, nodeCode]; exact c₀nd
          cases x with
          | call =>
              rw [Xinst.step_directCall_spawn_code (Or.inl rfl) spawn notDel, frameTarget,
                nodeCode]
              exact hc₀
          | staticcall =>
              rw [Xinst.step_directCall_spawn_code (Or.inr rfl) spawn notDel, frameTarget,
                nodeCode]
              exact hc₀
          | callcode => exact (nodeOk.1 hat).elim
          | delegatecall =>
              obtain ⟨g, a, rest, stack⟩ := Xinst.step_delegatecall_spawn_stack spawn
              have inS := (nodeOk.2 hat g a rest stack).1
              rw [Xinst.step_delegatecall_spawn_code spawn stack (undesignated _ inS)]
              exact inS
          | create =>
              have fresh := Xinst.step_create_spawn_fresh (Or.inl rfl) spawn
              rw [frameTarget, nodeCode] at fresh
              exact (c₀ne fresh).elim
          | create2 =>
              have fresh := Xinst.step_create_spawn_fresh (Or.inr rfl) spawn
              rw [frameTarget, nodeCode] at fresh
              exact (c₀ne fresh).elim
        · rw [← Frame.enter_run_code henter,
            codeSource (by rw [target]; exact same) (by rw [target, nodeCode]; exact c₀ne)
              (by rw [target, nodeCode]; exact c₀nd), target, nodeCode]
          exact hc₀
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume next
          settles] at member closed
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with (rfl | inChild) | inNext
        · exact childOwn
        · exact childIh (R := ⟨_, _, _, _, child⟩) (.refl _) childCode childOwn
            (closed _ (List.mem_cons_self ..))
            (fun F hF => closed F (List.mem_cons_of_mem _ (List.mem_append_left _ hF)))
            G inChild
        · exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) code own free
            (fun F hF => closed F (List.mem_cons_of_mem _ (List.mem_append_right _ hF)))
            G inNext
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child hresume next
          settles] at member closed
        exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) code own free closed
          G member

/-- **Owner closure.**  If `P` holds a code of `S`, every code of `S` is nonempty and no
designator, the root runs a code of `S` when it owns `P`, and `S` is delegation-closed, then every
committed frame owning `P`'s storage runs a code of `S`. -/
theorem Exec.ownerCode_of_closed {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) {P : Adr} {S : ByteArray → Prop}
    (nonempty : ∀ c, S c → 0 < c.size) (undesignated : ∀ c, S c → ¬ isValidDelegation c)
    (hP : S (pre.getCode P)) (hroot : sevm.currentTarget = P → S sevm.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (closed : Exec.DelegationClosed run P S) :
    ∀ G ∈ Exec.committedFrames run, G.sevm.currentTarget = P → S G.sevm.code := by
  intro G member target
  by_cases committed : Execution.commits out = true
  · have frames : Exec.committedFrames run =
        Exec.Frame.ofRun run committed :: Exec.descendantFrames run := by
      rw [Exec.committedFrames, dite_eq_left committed]
    unfold Exec.DelegationClosed at closed
    rw [frames] at member closed
    rcases List.mem_cons.mp member with rfl | deeper
    · exact hroot target
    · exact Exec.descendantFrames_closed nonempty undesignated hP run
        (R := ⟨0, sevm, pre, out, run⟩) (.refl _) rfl hroot
        (closed _ (List.mem_cons_self ..))
        (fun F hF => closed F (List.mem_cons_of_mem _ hF)) G deeper target
  · rw [Exec.committedFrames_eq_nil_of_not_commits run committed] at member
    exact (List.not_mem_nil member).elim

end Blanc
