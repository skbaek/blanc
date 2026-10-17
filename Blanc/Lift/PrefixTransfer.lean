import Blanc.Lift.Transfer
import Blanc.Lift.Sound

/-!
# Exact-word stack transfer over a stack prefix

`prefixTransfer` runs the lift's natural instruction transfer (`ninstTransfer`) on a *prefix* pattern of
the operand stack, keeping exact words where they are known: a `PUSH` pushes its literal, an `AND` of two
known words pushes their conjunction, and `DUP`/`SWAP` reaching below the prefix extend it with unknown
words first (the actual run had them).  `prefixTransfer_run` is its success-only soundness: an actual
run of the instruction from a stack matching `p ++ rest` leaves a stack matching `p' ++ rest'`.
Contract-neutral.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- Extend a prefix pattern with unknown words up to length `k`. -/
def padPattern (k : Nat) (p : Pattern) : Pattern := p ++ List.replicate (k - p.length) none

/-- Transfer of a prefix pattern, exact on literals and on `AND` of known words. -/
def prefixTransfer (n : Ninst) (p : Pattern) : Option Pattern :=
  match n with
  | .push bs _ => some (some (Bytes.toB256 bs) :: p)
  | .reg (.dup i) => ninstTransfer (.reg (.dup i)) (padPattern (i.val + 1) p)
  | .reg (.swap i) => ninstTransfer (.reg (.swap i)) (padPattern (i.val + 2) p)
  | .reg .and =>
      match p with
      | some x :: some y :: q => some (some (x &&& y) :: q)
      | _ => ninstTransfer (.reg .and) p
  | n => ninstTransfer n p

private theorem matches_replicate_none : ∀ (l : Stack), Matches (List.replicate l.length none) l
  | [] => matches_nil
  | _ :: l => ⟨Or.inl rfl, matches_replicate_none l⟩

private theorem matches_prefix_split : ∀ {p : Pattern} {rest s : Stack},
    Matches (p ++ rest.map some) s → s = s.take p.length ++ rest ∧ Matches p (s.take p.length)
  | [], rest, s, h => by
      simp only [List.nil_append] at h
      rw [matches_some_map_eq h]
      exact ⟨rfl, matches_nil⟩
  | w :: p, rest, s, h => by
      match s, h with
      | v :: s, ⟨hw, hs⟩ =>
          obtain ⟨eq, hp⟩ := matches_prefix_split hs
          refine ⟨?_, ⟨hw, hp⟩⟩
          simp only [List.length_cons, List.take_succ_cons, List.cons_append]
          exact congrArg (v :: ·) eq

/-- Padding a prefix pattern within the actual stack depth keeps the match. -/
theorem matches_padPattern {p : Pattern} {rest s : Stack} {k : Nat}
    (h : Matches (p ++ rest.map some) s) (depth : k ≤ s.length) :
    Matches (padPattern k p ++ (rest.drop (k - p.length)).map some) s := by
  obtain ⟨eq, hp⟩ := matches_prefix_split h
  have len : s.length = p.length + rest.length := by
    rw [(Matches.length h), List.length_append, List.length_map]
  have hm : k - p.length ≤ rest.length := by omega
  rw [eq, padPattern, List.append_assoc, ← List.take_append_drop (k - p.length) rest]
  rw [List.drop_append_of_le_length (by rw [List.length_take]; omega), List.drop_take_self,
    List.nil_append]
  refine matches_append hp (matches_append ?_ (matches_some_map _))
  have := matches_replicate_none (rest.take (k - p.length))
  rwa [List.length_take, Nat.min_eq_left hm] at this

private theorem swap_length : ∀ {l l' : Stack} {i : Nat}, Jaune.List.swap l i = some l' →
    i + 2 ≤ l.length
  | [], _, _, h => by simp only [Jaune.List.swap, reduceCtorEq] at h
  | x :: l, _, i, h => by
      simp only [Jaune.List.swap, Option.bind_eq_bind] at h
      rcases e : l[i]? with _ | y
      · simp only [e, Option.bind_none, reduceCtorEq] at h
      · have := (List.getElem?_eq_some_iff.mp e).1
        simp only [List.length_cons]
        omega

/-- **Soundness of the prefix transfer.** -/
theorem prefixTransfer_run {sevm : Sevm} {d d' : Devm} {n : Ninst} {p p' : Pattern}
    {rest : Stack} (hfork : CoveredFork sevm.benvStat.fork)
    (matched : Matches (p ++ rest.map some) d.stack) (checked : prefixTransfer n p = some p')
    (run : Ninst.Run sevm d n d') : ∃ rest' : Stack, Matches (p' ++ rest'.map some) d'.stack := by
  have generic : ∀ {q : Pattern} {rest : Stack}, Matches (q ++ rest.map some) d.stack →
      ninstTransfer n q = some p' → ∃ rest' : Stack, Matches (p' ++ rest'.map some) d'.stack :=
    fun {q} {rest} m t => ⟨rest, ninstTransfer_run hfork m (ninstTransfer_append (rest.map some) t) run⟩
  cases n with
  | push bs fits =>
      simp only [prefixTransfer, Option.some.injEq] at checked
      subst checked
      exact ⟨rest, by rw [push_run_stack run]; exact ⟨Or.inr rfl, matched⟩⟩
  | reg r =>
      cases r with
      | dup i =>
          obtain ⟨x, hx, -⟩ := of_run_dup run
          have depth : i.val + 1 ≤ d.stack.length := (List.getElem?_eq_some_iff.mp hx).1
          exact generic (matches_padPattern matched depth) checked
      | swap i => exact generic (matches_padPattern matched (swap_length (of_run_swap run))) checked
      | and =>
          match p, matched, checked with
          | some x :: some y :: q, matched, checked =>
              simp only [prefixTransfer, Option.some.injEq] at checked
              subst checked
              rcases of_run_reg run with ⟨pc, hr⟩
              simp only [Rinst.run, Rinst.runCore] at hr
              obtain ⟨a, b, hd⟩ := Devm.diffBurn_of_applyBinary hr
              obtain ⟨mid, pop, push⟩ := hd.stack
              simp only [Stack.Pop, Stack.Push, Split, List.nil_append, List.cons_append] at pop push
              rw [pop] at matched
              obtain ⟨hxw, hyw, hq⟩ := matched
              rw [push, hxw.eq_of_some, hyw.eq_of_some]
              exact ⟨rest, Or.inr rfl, hq⟩
          | [], matched, checked => exact generic matched checked
          | [none], matched, checked => exact generic matched checked
          | [some x], matched, checked => exact generic matched checked
          | none :: _ :: q, matched, checked => exact generic matched checked
          | some x :: none :: q, matched, checked => exact generic matched checked
      | _ => exact generic matched checked
  | _ => exact generic matched checked

/-! ## The word a `CREATE2` leaves -/

private theorem create_resume_result {parent : Devm} {na : Adr}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {sf : Devm}
    (h : (Resume.create parent na).run r = .ok sf) :
    ∃ w, sf.stack = w :: parent.stack ∧ (w = 0 ∨ w = na.toB256) := by
  cases r with
  | error e => exact (Resume.create_run_error h).elim
  | ok child =>
    unfold Resume.run liftToExecution at h
    dsimp only [bind, Except.bind] at h
    split at h
    · exact ⟨0, by rw [(Devm.push_of_push h).stack]; rfl, Or.inl rfl⟩
    · exact ⟨_, by rw [(Devm.push_of_push h).stack]; rfl, Or.inr rfl⟩

/-- A successful `genericCreate` step pushes `0`, or the new address when that address was unprotected. -/
theorem genericCreate_result {sevm : Sevm} {d : Devm} {v : B256} {na : Adr} {mi ms : Nat}
    {xl : Xlot} {sf : Devm} (h : XStep.Run (genericCreate.step sevm d v na mi ms) xl (.ok sf)) :
    ∃ w, sf.stack = w :: d.stack ∧ (w = 0 ∨ (w = na.toB256 ∧ ¬ State.Protected d.state na)) := by
  cases e : genericCreate.step sevm d v na mi ms with
  | spawn frame rsm =>
      rw [e] at h
      obtain ⟨r, -, hres⟩ := h
      rw [(genericCreate_step_spawn_exact e).2] at hres
      obtain ⟨w, hw, cases⟩ := create_resume_result hres.symm
      refine ⟨w, hw, ?_⟩
      rcases cases with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, genericCreate_step_spawn_target_unprotected e⟩
  | done ex =>
      rw [e] at h
      obtain ⟨-, rfl⟩ := h
      simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert, assertDynamic,
        Pure.pure, Except.pure] at e
      repeat' split at e
      all_goals simp only [XStep.ofExcept, XStep.done.injEq, reduceCtorEq, Except.ok.injEq] at e
      all_goals subst e; rename_i hpush
      all_goals exact ⟨0, by rw [(Devm.push_of_push hpush).stack]; rfl, Or.inl rfl⟩

/-- **The word a `CREATE2` leaves.**  A successful `CREATE2` replaces its four operands by `0` or by the
new address, which was unprotected in the spawning world. -/
theorem create2_run_result {sevm : Sevm} {d d' : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (run : Ninst.Run sevm d (.exec .create2) d') :
    ∃ (v i sz salt w : B256) (xs : Stack), d.stack = v :: i :: sz :: salt :: xs ∧
      d'.stack = w :: xs ∧ (w = 0 ∨ ∃ na, w = na.toB256 ∧ ¬ State.Protected d.state na) := by
  rcases run with ⟨xl, -, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    hfork.rules_stateGas_none, Bind.bind, Except.bind] at h_run
  rcases eq1 : Devm.pop d with _ | ⟨v1, s1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e1 := (Devm.pop_of_pop eq1)
  rcases eq2 : Devm.popToNat s1 with _ | ⟨n2, s2⟩ <;> simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq2 with ⟨x2, f2, -⟩
  rcases eq3 : Devm.popToNat s2 with _ | ⟨n3, s3⟩ <;> simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq3 with ⟨x3, f3, -⟩
  rcases eq4 : Devm.pop s3 with _ | ⟨v4, s4⟩ <;> simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e4 := (Devm.pop_of_pop eq4)
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i s5 eq5
  have b5 := Devm.burn_of_chargeGas eq5
  obtain ⟨w, hw, result⟩ := genericCreate_result h_run
  have stack : d.stack = v1 :: x2 :: x3 :: v4 :: s4.stack := by
    have a := e1.stack
    have b := f2.stack
    have c := f3.stack
    have d4 := e4.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at a b c d4
    rw [a, b, c, d4]
  have state : (s5.memExtends [(n2, n3)]).state = d.state := by
    rw [show (s5.memExtends [(n2, n3)]).state = s5.state from rfl, ← b5.state, ← e4.state,
      ← f3.state, ← f2.state, ← e1.state]
  refine ⟨v1, x2, x3, v4, w, s4.stack, stack, ?_, ?_⟩
  · rw [hw, show (s5.memExtends [(n2, n3)]).stack = s5.stack from rfl, ← b5.stack]
  · rcases result with rfl | ⟨rfl, unprotected⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, state ▸ unprotected⟩

end Blanc.Lift
