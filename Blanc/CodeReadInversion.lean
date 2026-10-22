import Blanc.CommonProofs

/-!
# Exact stack observations for code reads

Access warming and BAL read metadata do not change EXTCODESIZE's stack arity.
-/

namespace Blanc

open Jaune

/-- Every successful EXTCODESIZE replaces one word with one word. -/
theorem Ninst.extcodesize_stack_length
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre (.reg .extcodesize) post) :
    post.stack.length = pre.stack.length := by
  obtain ⟨pc, run⟩ := of_run_reg run
  simp only [Rinst.run, Rinst.runCore] at run
  obtain ⟨⟨adr, popped⟩, popAdr, run⟩ := Except.bind_eq_ok run
  rw [Devm.popToAdr_def] at popAdr
  dsimp only [Functor.mapRev, Functor.map, Except.map] at popAdr
  rcases pop : Devm.pop pre with _ | ⟨word, base⟩ <;>
    simp only [pop, reduceCtorEq, Except.ok.injEq] at popAdr
  obtain ⟨rfl, rfl⟩ := popAdr
  have popStack := (Devm.pop_of_pop pop).stack
  change pre.stack = word :: base.stack at popStack
  cases access : sevm.benvStat.rules.access <;> simp only [access] at run
  all_goals (try split at run)
  all_goals
    obtain ⟨charged, gas, push⟩ := Except.bind_eq_ok run
    have burnStack := (Devm.burn_of_chargeGas gas).stack
    change base.stack = charged.stack at burnStack
    have pushStack := (Devm.push_of_push push).stack
    simp only [Stack.Push, Split, List.cons_append, List.nil_append,
      Devm.balReadAccount_stack] at pushStack
    rw [pushStack, List.length_cons, ← burnStack, popStack, List.length_cons]

/-- The exact successful stack image, read from the instruction's actual input state. -/
theorem Ninst.extcodesize_stack
    {sevm : Sevm} {pre post : Devm} {x : B256} {S : List B256}
    (stack : pre.stack = x :: S)
    (run : Ninst.Run sevm pre (.reg .extcodesize) post) :
    post.stack = (pre.getCode x.toAdr).size.toB256 :: S := by
  have inputPrefix : x :: S <<+ pre.stack := ⟨[], by
    simp only [Split, stack, List.append_nil]⟩
  have observed := (prefix_of_extcodesize_val inputPrefix run).1
  have length := Ninst.extcodesize_stack_length run
  apply List.pref_unique (zs := post.stack)
    (by simpa only [stack, List.length_cons] using length)
  · exact ⟨[], by simp only [Split, List.append_nil]⟩
  · exact observed

end Blanc
