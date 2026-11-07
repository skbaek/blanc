import Blanc.Lift.Exact
import Blanc.Lift.NodeWalk
import Blanc.Lift.FrameWalkCut

/-!
# A failing frame, from an exact walk up to the failure

`SFunc.RunExact` ends only in a successful terminal, so `lift_exact` gives only `.ok` executions, and a walk cannot
end at `REVERT` or out of gas. This module reuses exact walks up to a point instead. A *cut tree* is a certificate tree
with the part past the point of interest replaced: `.last .stop` where the walk stops, at byte offset `e`, and
`.undefined` on arms the walk does not take. `cutOk` checks such a tree against the bytes, by evaluation, with
`es` giving the byte offset of each program entry. `exec_of_cut` then turns a run of the cut tree into any execution
that continues from `e`, whatever it ends in. The exact lemmas are generic in their outcome, so a contract's existing
walks apply unchanged to its cut trees.
-/

namespace Blanc.Lift

open Jaune

/-- The word a node leaves on top of the stack, when the checker knows it. -/
def pushedWord : Ninst → Option B256
  | .push xs _ => some xs.toB256
  | _ => none

/-- A cut tree against the bytes. `top` is the stack's top word when known: a `JUMP` or `JUMPI` is checked only
right after a `PUSH`, whose word then names the destination. -/
def cutOk (code : ByteArray) (es : List Nat) (e : Nat) : Nat → Option B256 → SFunc → Bool
  | pc, _, .last .stop => pc == e
  | _, _, .undefined => true
  | pc, _, .dest f =>
    match code.getInst pc with
    | some (.jump .jumpdest) => cutOk code es e (pc + 1) none f
    | _ => false
  | pc, _, .next n f =>
    match code.getInst pc with
    | some (.next m) =>
      if m = n ∧ nodeNoExec n = true then cutOk code es e (pc + n.size) (pushedWord n) f else false
    | _ => false
  | pc, some w, .branch f g =>
    match code.getInst pc with
    | some (.jump .jumpi) =>
      jumpable code w.toNat && cutOk code es e (pc + 1) none f && cutOk code es e w.toNat none g
    | _ => false
  | pc, some w, .jump k =>
    match code.getInst pc with
    | some (.jump .jump) => jumpable code w.toNat && es[k]? == some w.toNat
    | _ => false
  | _, _, _ => false

theorem pushedWord_stack {s : Sevm} {d d' : Devm} {n : Ninst} (h : Ninst.RunCompiled s d n d') (w : B256)
    (hw : pushedWord n = some w) : d'.stack.head? = some w := by
  cases n with
  | push xs le =>
    cases hw
    have hp := of_run_push (Ninst.Run.of_runCompiled h)
    have hstack := hp.stack
    simp only [Stack.Push, Split, List.cons_append, List.nil_append] at hstack
    rw [hstack]
    rfl
  | _ => simp only [pushedWord, reduceCtorEq] at hw

variable {s : Sevm} {fs : List SFunc} {es : List Nat} {e : Nat} {ex : Execution}

/-- **A run of a cut tree is a prefix of any execution that continues from the cut.** -/
theorem exec_of_cut
    (hes : ∀ (k : Nat) (f : SFunc), fs[k]? = some f →
      ∃ pc, es[k]? = some pc ∧ cutOk s.code es e pc none f = true)
    {d : Devm} {f : SFunc} {o : Outcome} (run : SFunc.RunExact fs s d f o) :
    ∀ {d' : Devm}, o = .halted d' → ∀ (pc : Nat) (top : Option B256), cutOk s.code es e pc top f = true →
      (∀ w, top = some w → d.stack.head? = some w) → Nonempty (Exec e s d' ex) →
      Nonempty (Exec pc s d ex) := by
  induction run with
  | @zero devm devm' f g o d0 hpop hrest ih =>
    intro d' ho pc top hc htop k
    cases top with
    | none => simp only [cutOk, Bool.false_eq_true] at hc
    | some w =>
      simp only [cutOk] at hc
      split at hc
      · rename_i hm
        simp only [Bool.and_eq_true] at hc
        obtain ⟨hex⟩ := ih ho (pc + 1) none hc.1.2 (fun _ h => by cases h) k
        have hat : Jinst.At s.code pc .jumpi := hm
        have hstep := Evm.jumpi_cont_zero hat (popBurnBy_two_stack' hpop)
          (by have := hpop.gasLeft; omega)
        rw [popBurnBy_setMach hpop] at hstep
        exact ⟨Exec.cont hstep hex⟩
      · simp only [Bool.false_eq_true] at hc
  | @succ devm devm' f g o d0 w hne hpop hrest ih =>
    intro d' ho pc top hc htop k
    cases top with
    | none => simp only [cutOk, Bool.false_eq_true] at hc
    | some w' =>
      simp only [cutOk] at hc
      split at hc
      · rename_i hm
        simp only [Bool.and_eq_true] at hc
        have hs := popBurnBy_two_stack' hpop
        have hw : d0 = w' := by
          have := htop w' rfl
          rw [hs] at this
          simpa only [List.head?_cons, Option.some.injEq] using this
        subst hw
        obtain ⟨hex⟩ := ih ho d0.toNat none hc.2 (fun _ h => by cases h) k
        have hat : Jinst.At s.code pc .jumpi := hm
        have hstep := Evm.jumpi_cont_jump hat hs hne (by have := hpop.gasLeft; omega) hc.1.1
        rw [popBurnBy_setMach hpop] at hstep
        exact ⟨Exec.cont hstep hex⟩
      · simp only [Bool.false_eq_true] at hc
  | toZero => intro d' ho pc top hc; cases top <;> simp only [cutOk, Bool.false_eq_true] at hc
  | toSucc => intro d' ho pc top hc; cases top <;> simp only [cutOk, Bool.false_eq_true] at hc
  | @last devm devm' l h =>
    intro d' ho pc top hc htop k
    cases ho
    cases l with
    | stop =>
      simp only [cutOk, beq_iff_eq] at hc
      subst hc
      have hd : devm = devm' := by
        change Except.ok _ = Except.ok _ at h
        cases h
        rfl
      rw [hd]
      exact k
    | _ => simp only [cutOk, Bool.false_eq_true] at hc
  | @next devm devm' n f o h hrest ih =>
    intro d' ho pc top hc htop k
    simp only [cutOk] at hc
    split at hc
    · rename_i m hm
      split at hc
      · rename_i hcond
        obtain ⟨rfl, hn⟩ := hcond
        obtain ⟨hex⟩ := ih ho (pc + m.size) (pushedWord m) hc (fun w hw => pushedWord_stack h w hw) k
        have hat : Ninst.At s.code pc m := hm
        exact ⟨Exec.cont ((Evm.step_next hat).trans
          (NodeWalk.ninst_step_of_runCompiled (nodeNe_of_noExec hn) h pc)) hex⟩
      · simp only [Bool.false_eq_true] at hc
    · simp only [Bool.false_eq_true] at hc
  | @dest devm devm' f o h hrest ih =>
    intro d' ho pc top hc htop k
    simp only [cutOk] at hc
    split at hc
    · rename_i hm
      obtain ⟨hex⟩ := ih ho (pc + 1) none hc (fun _ h => by cases h) k
      have hat : Jinst.At s.code pc .jumpdest := hm
      exact ⟨Exec.cont (Evm.jumpdest_cont hat h) hex⟩
    · simp only [Bool.false_eq_true] at hc
  | @jump devm devm' k' f o d0 hk hpop hrest ih =>
    intro d' ho pc top hc htop k
    cases top with
    | none => simp only [cutOk, Bool.false_eq_true] at hc
    | some w' =>
      simp only [cutOk] at hc
      split at hc
      · rename_i hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        have hs : devm.stack = d0 :: devm'.stack := by
          simpa only [Stack.Pop, Split, List.cons_append, List.nil_append] using hpop.stack
        have hw : d0 = w' := by
          have := htop w' rfl
          rw [hs] at this
          simpa only [List.head?_cons, Option.some.injEq] using this
        subst hw
        obtain ⟨pc', hes', hc'⟩ := hes k' f hk
        have hpc : pc' = d0.toNat := by
          rw [hes'] at hc
          exact Option.some.inj hc.2
        subst hpc
        obtain ⟨hex⟩ := ih ho d0.toNat none hc' (fun _ h => by cases h) k
        have hat : Jinst.At s.code pc .jump := hm
        have hstep := Evm.jump_cont hat hs (by have := hpop.gasLeft; omega) hc.1
        have hset : devm.setMach ⟨devm'.stack, devm.memory, devm.gasLeft - gMid, devm.stateGas⟩ = devm' :=
          popBurnBy_setMach hpop
        rw [hset] at hstep
        exact ⟨Exec.cont hstep hex⟩
      · simp only [Bool.false_eq_true] at hc
  | ret => intro d' ho; cases ho
  | callHalt => intro d' ho pc top hc; cases top <;> simp only [cutOk, Bool.false_eq_true] at hc
  | callRet => intro d' ho pc top hc; cases top <;> simp only [cutOk, Bool.false_eq_true] at hc
  | pcAt => intro d' ho pc top hc; cases top <;> simp only [cutOk, Bool.false_eq_true] at hc

end Blanc.Lift
