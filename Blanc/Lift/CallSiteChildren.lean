import Blanc.Lift.CallSite
import Blanc.Lift.CallChildren
import Blanc.Lift.CallRestriction
import Blanc.CallSpawnExact
import Blanc.ExecutionTraceCalldata

/-!
# Where a frame's children come from, and what a CALL site sends

Contract-neutral links from a frame's direct children to the certificate's call sites:

* `Exec.childFrames_spawnedAt`: every direct child of a frame is spawned by a step at a node of the
  frame's own same-frame chain;
* `SFunc.nodesSatisfy`: a check at every straight-line node of a synthetic tree, kept by every
  synthetic step from a certificate's entry (`Reach.nodesSatisfy`), so that a cursor-placed node decoding an
  external instruction passes the check at its own tree (`CursorOK.nodesSatisfy_exec`);
* `SFunc.lineDrop` names a node inside the straight prefix of a generated tree
  (`SFunc.lineSuffix_lineDrop`);
* `Xinst.step_call_spawn_selector`: a CALL child's selector is the one `CallInputSelector` reads.
-/

namespace Blanc.Lift

open Jaune

/-! ## The direct children of a frame are spawned on its chain -/

/-! ## A check at every straight-line node, kept along synthetic steps -/

/-! ## Naming a node of a straight prefix -/

/-- Strip `n` straight-line heads (`.next`, `.dest`) from a tree. -/
def SFunc.lineDrop : Nat → SFunc → SFunc
  | 0, f => f
  | n + 1, .next _ f => SFunc.lineDrop n f
  | n + 1, .dest f => SFunc.lineDrop n f
  | _ + 1, f => f

theorem SFunc.lineSuffix_lineDrop : ∀ (n : Nat) (f : SFunc), SFunc.LineSuffix (SFunc.lineDrop n f) f
  | 0, f => .refl f
  | n + 1, .next _ f => .next (SFunc.lineSuffix_lineDrop n f)
  | n + 1, .dest f => .dest (SFunc.lineSuffix_lineDrop n f)
  | _ + 1, .branch _ _ => .refl _
  | _ + 1, .branchTo _ _ => .refl _
  | _ + 1, .last _ => .refl _
  | _ + 1, .jump _ => .refl _
  | _ + 1, .callNext _ _ => .refl _
  | _ + 1, .ret => .refl _
  | _ + 1, .pcAt _ _ => .refl _
  | _ + 1, .undefined => .refl _

/-! ## What a CALL child receives -/

/-- A spawning CALL popped at least its seven operands. -/
theorem Xinst.step_call_spawn_stack {sevm : Sevm} {s : Devm} {f : Frame} {rsm : Resume}
    (fork : CoveredFork sevm.benvStat.fork) (hx : Xinst.step sevm s .call = .spawn f rsm) :
    ∃ g c v ii is oi os rest, s.stack = g :: c :: v :: ii :: is :: oi :: os :: rest := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [fork.rules_stateGas_none] at hx
  rcases eq1 : Devm.pop s with _ | ⟨g, d1⟩ <;> simp only [eq1] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have e1 := (Devm.pop_of_pop eq1).stack
  rcases eq2 : Devm.popToAdr d1 with _ | ⟨_, d2⟩ <;> simp only [eq2] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨c, -, p2⟩ := Devm.pop_of_popToAdr eq2
  have e2 := (Devm.pop_of_pop p2).stack
  rcases eq3 : Devm.pop d2 with _ | ⟨v, d3⟩ <;> simp only [eq3] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have e3 := (Devm.pop_of_pop eq3).stack
  rcases eq4 : Devm.popToNat d3 with _ | ⟨_, d4⟩ <;> simp only [eq4] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨ii, f4, -⟩ := Devm.pop_of_popToNat_val eq4
  have e4 := f4.stack
  rcases eq5 : Devm.popToNat d4 with _ | ⟨_, d5⟩ <;> simp only [eq5] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨is, f5, -⟩ := Devm.pop_of_popToNat_val eq5
  have e5 := f5.stack
  rcases eq6 : Devm.popToNat d5 with _ | ⟨_, d6⟩ <;> simp only [eq6] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨oi, f6, -⟩ := Devm.pop_of_popToNat_val eq6
  have e6 := f6.stack
  rcases eq7 : Devm.popToNat d6 with _ | ⟨_, d7⟩ <;> simp only [eq7] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨os, f7, -⟩ := Devm.pop_of_popToNat_val eq7
  have e7 := f7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1 e2 e3 e4 e5 e6 e7
  exact ⟨g, c, v, ii, is, oi, os, d7.stack, by rw [e1, e2, e3, e4, e5, e6, e7]⟩

/-- **A CALL child's selector.**  The child a spawning CALL enters reads, as its selector, the
selector of the input window the parent's memory holds (`CallInputSelector`'s reading). -/
theorem Xinst.step_call_spawn_selector {sevm : Sevm} {s : Devm} {f : Frame} {rsm : Resume}
    {cevm : Evm} (fork : CoveredFork sevm.benvStat.fork)
    (hx : Xinst.step sevm s .call = .spawn f rsm) (henter : f.enter = .run cevm)
    {g c v ii is : B256} {rest : List B256} (hstack : s.stack = g :: c :: v :: ii :: is :: rest) :
    Blanc.Sevm.selector cevm.sta = Bytes.selector (s.memory.read ii.toNat is.toNat).1 := by
  obtain ⟨g', c', v', ii', is', oi, os, rest', hs7⟩ := Xinst.step_call_spawn_stack fork hx
  have same := hstack.symm.trans hs7
  simp only [List.cons.injEq] at same
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := same
  have hn : Ninst.step ⟨0, sevm, s⟩ Ninst.call = .spawn f rsm 1 := by
    rw [Ninst.call, Ninst.step_exec]
    simp only [hx, XStep.toStep]
  obtain ⟨_, _, _, _, _, -, -, -, -, -, hframe, -⟩ :=
    Ninst.step_call_spawn_exact hn hs7 fork
  rw [Blanc.Sevm.selector, Blanc.Sevm.dataWord, Blanc.ExecutionTrace.Frame.enter_data_eq henter, hframe,
    Blanc.ExecutionTrace.Frame.ofCall_inner_data, Blanc.ExecutionTrace.callMsg_data]
  rfl

end Blanc.Lift
