import Blanc.Lift.CursorKeccak
import Blanc.Lift.FrameWalkNode

/-! Ordered successful hash pairs from one observed synthetic prefix. -/

namespace Blanc.Lift

open Jaune Blanc

/-- Each observed edge also retains the prefix from the original starting configuration. -/
theorem ObservedReach.withPrefix {P : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop} {fs : List SFunc} {sevm : Sevm} {a b : Conf}
    (run : ObservedReach P observe fs sevm a b) :
    ObservedReach P (fun before after => observe before after ∧
      ObservedReach P observe fs sevm a before) fs sevm a b := by
  induction run with
  | refl => exact .refl
  | tail segment edge ih => exact .tail ih ⟨edge.1, edge.2, segment⟩

/-- Retain the actual after-configuration of this hash for a later observation. -/
theorem ObservedKeccak.of_next_linked {P : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop} {fs : List SFunc} {sevm : Sevm}
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach P observe fs sevm ⟨St b (0 :: 64 :: S) M G, .next (.reg .keccak256) f, K⟩ T)
    (hT : AtSstore T) {input : Bytes} {shape : SFunc → Prop}
    (read : (M.read 0 64).1 = input) (source : shape (.next (.reg .keccak256) f)) :
    ∃ G', let middle : Conf :=
      ⟨St b ((M.read 0 64).1.keccak :: S) (M.read 0 64).2 G', f, K⟩
      ObservedKeccak P (fun before after => observe before after ∧ after = middle)
        sevm input shape ∧ ObservedReach P observe fs sevm middle T := by
  obtain ⟨d', runtime, observed, run⟩ := ObservedReach.nextS (by intro h; cases h) run hT
  obtain ⟨G', rfl⟩ := ri_keccak (erase runtime)
  exact ⟨G', ⟨_, _, runtime, ⟨observed, rfl⟩, ⟨f, rfl, rfl, rfl⟩,
    ⟨S, rfl⟩, read, source⟩, run⟩

/-- Two successful hash observations joined by the same observed prefix. -/
def ObservedKeccakPair (P : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (fs : List SFunc) (sevm : Sevm)
    (innerInput outerInput : Bytes) : Prop :=
  ∃ middle : Conf,
    ObservedKeccak P (fun before after => observe before after ∧ after = middle)
      sevm innerInput (fun _ => True) ∧
    ObservedKeccak P (fun before after => observe before after ∧
      ObservedReach P observe fs sevm middle before) sevm outerInput (fun _ => True)

/-- Forget only the relation between the pair, keeping both successful observations. -/
theorem ObservedKeccakPair.forget {P : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop} {fs : List SFunc} {sevm : Sevm} {i o : Bytes}
    (pair : ObservedKeccakPair P observe fs sevm i o) :
    ObservedKeccak P observe sevm i (fun _ => True) ∧
      ObservedKeccak P observe sevm o (fun _ => True) := by
  obtain ⟨middle, ⟨a, b, run, obs, tree, stack, read, shape⟩,
    ⟨c, d, run', obs', tree', stack', read', shape'⟩⟩ := pair
  exact ⟨⟨a, b, run, obs.1, tree, stack, read, shape⟩,
    ⟨c, d, run', obs'.1, tree', stack', read', shape'⟩⟩

/-- Raw driver edges strictly decrease gas; this orders their actual derivation positions. -/
theorem Cursor.RawEdgeAt.gasMeasure_lt {code : ByteArray} {cert : Cert}
    {root stop : Exec.Deriv} {before after : Conf}
    (edge : Cursor.RawEdgeAt code cert root stop before after) :
    after.d.gasMeasure < before.d.gasMeasure := by
  obtain ⟨node, next, here, there, _, step, _, _, beforeEq, afterEq, _⟩ := edge
  rw [beforeEq, afterEq]
  exact Exec.Deriv.Prec.gasMeasure_lt step.prec

/-- The gas measure cannot increase along an observed actual-prefix segment. -/
theorem ObservedReach.raw_gasMeasure_le {code : ByteArray} {cert : Cert}
    {root stop : Exec.Deriv} {a b : Conf}
    (run : ObservedReach (StepIn root) (Cursor.RawEdgeAt code cert root stop)
      cert.prog root.sevm a b) : b.d.gasMeasure ≤ a.d.gasMeasure := by
  induction run with
  | refl => exact Nat.le_refl _
  | tail _ edge ih => exact Nat.le_trans (Cursor.RawEdgeAt.gasMeasure_lt edge.2).le ih

/-- Comparable positions in one parent prefix follow their actual gas order. -/
theorem parentPrefix_of_gasMeasure_le {root first second : Exec.Deriv}
    (one : Exec.Deriv.ParentPrefix root first) (two : Exec.Deriv.ParentPrefix root second)
    (gas : second.devm.gasMeasure ≤ first.devm.gasMeasure) :
    Exec.Deriv.ParentPrefix first second := by
  rcases Exec.Deriv.ParentPrefix.linear one two with ordered | reverse
  · exact ordered
  cases reverse with
  | refl => exact .refl _
  | step head tail =>
    have small := Exec.Deriv.ParentPrefix.gasMeasure_le tail
    have strict := Exec.Deriv.Prec.gasMeasure_lt head.prec
    omega

/-- The actual successful opcode occurrence at a named raw-prefix node. -/
theorem keccakOccurrence_of_parentPrefix {root node next : Exec.Deriv}
    (reached : Exec.Deriv.ParentPrefix root node)
    (decoded : Ninst.At node.sevm.code node.pc (.reg .keccak256))
    (runtime : Ninst.Run node.sevm node.devm (.reg .keccak256) next.devm) :
    ∃ occurrence : Exec.NinstOccurrence root, occurrence.node = node ∧
      occurrence.instruction = .reg .keccak256 ∧ occurrence.stepResult = .ok next.devm := by
  have raw : node ∈ Exec.rawNodes root.exc := by
    obtain ⟨earlier, decomposition⟩ := Exec.Deriv.ParentPrefix.rawNodes_decomposition reached
    rw [decomposition]
    exact List.mem_append_right earlier (Exec.mem_rawNodes_self node.exc)
  obtain ⟨occurrence, sameNode, instruction⟩ := Exec.exists_ninstOccurrence_of_mem_rawNodes raw decoded
  obtain ⟨slot, filled, pc, stepRun⟩ := runtime
  have actual : Ninst.StepRun occurrence.node.pc occurrence.node.sevm occurrence.node.devm
      occurrence.instruction slot (.ok next.devm) := by
    rw [sameNode, instruction]
    exact Ninst.stepRun_pc_irrel rfl stepRun
  exact ⟨occurrence, sameNode, instruction, (occurrence_stepRun_unique occurrence filled actual).2⟩

/-- Both actual successful hashes, with the first completed before the second begins. -/
def KeccakPairBefore (root stop : Exec.Deriv) (innerInput outerInput : Bytes) : Prop :=
  ∃ (inner outer : Exec.NinstOccurrence root) (innerNext outerNext : Exec.Deriv),
    inner.instruction = .reg .keccak256 ∧ inner.stepResult = .ok innerNext.devm ∧
    outer.instruction = .reg .keccak256 ∧ outer.stepResult = .ok outerNext.devm ∧
    Exec.Deriv.ParentPrefix root inner.node ∧ Exec.Deriv.ParentStep innerNext inner.node ∧
    Exec.Deriv.ParentPrefix innerNext outer.node ∧ Exec.Deriv.ParentStep outerNext outer.node ∧
    Exec.Deriv.ParentPrefix outerNext stop ∧
    (∃ rest, inner.node.devm.stack = 0 :: 64 :: rest) ∧
    (inner.node.devm.memory.read 0 64).1 = innerInput ∧
    (∃ rest, outer.node.devm.stack = 0 :: 64 :: rest) ∧
    (outer.node.devm.memory.read 0 64).1 = outerInput

/-- Project both earlier-occurrence witnesses from the ordered pair. -/
theorem KeccakPairBefore.forget {root stop : Exec.Deriv} {i o : Bytes}
    (pair : KeccakPairBefore root stop i o) :
    ∃ innerPc outerPc, KeccakBefore root stop i innerPc ∧ KeccakBefore root stop o outerPc := by
  obtain ⟨inner, outer, innerNext, outerNext, innerInst, innerResult, outerInst, outerResult,
    reached, innerStep, between, outerStep, suffix, innerStack, innerRead, outerStack, outerRead⟩ := pair
  exact ⟨inner.node.pc, outer.node.pc,
    ⟨inner, innerNext, rfl, innerInst, innerResult, reached, innerStep,
      (between.snoc outerStep).trans suffix, innerStack, innerRead⟩,
    ⟨outer, outerNext, rfl, outerInst, outerResult, (reached.snoc innerStep).trans between,
      outerStep, suffix, outerStack, outerRead⟩⟩

/-- The pair's observed segment fixes the order of the original raw hash occurrences. -/
theorem ObservedKeccakPair.actual {code : ByteArray} {cert : Cert} {root stop : Exec.Deriv}
    {i o : Bytes}
    (pair : ObservedKeccakPair (StepIn root) (Cursor.RawEdgeAt code cert root stop)
      cert.prog root.sevm i o) : KeccakPairBefore root stop i o := by
  obtain ⟨middle, ⟨a, b, run, ⟨edge, after⟩, ⟨tail, tree, _, _⟩, stack, read, _⟩,
    ⟨c, d, run', ⟨edge', between⟩, ⟨tail', tree', _, _⟩, stack', read', _⟩⟩ := pair
  subst middle
  have gas := ObservedReach.raw_gasMeasure_le between
  obtain ⟨node, next, here, there, reached, step, _, same, beforeEq, afterEq, _, placed, _⟩ := edge
  obtain ⟨node', next', here', there', reached', step', suffix', same', beforeEq', afterEq',
    _, placed', _⟩ := edge'
  rw [beforeEq, afterEq] at run
  rw [beforeEq] at tree stack read
  rw [beforeEq', afterEq'] at run'
  rw [beforeEq'] at tree' stack' read'
  rw [afterEq, beforeEq'] at gas
  have ordered := parentPrefix_of_gasMeasure_le (reached.snoc step) reached' gas
  have runtime : Ninst.Run node.sevm node.devm (.reg .keccak256) next.devm := by
    rw [same]
    exact StepIn.toRun run
  have runtime' : Ninst.Run node'.sevm node'.devm (.reg .keccak256) next'.devm := by
    rw [same']
    exact StepIn.toRun run'
  obtain ⟨inner, innerEq, innerInst, innerResult⟩ := keccakOccurrence_of_parentPrefix
    reached (placed.ninstAt_of_next tree) runtime
  obtain ⟨outer, outerEq, outerInst, outerResult⟩ := keccakOccurrence_of_parentPrefix
    reached' (placed'.ninstAt_of_next tree') runtime'
  refine ⟨inner, outer, next, next', innerInst, innerResult, outerInst, outerResult, ?_⟩
  rw [innerEq, outerEq]
  exact ⟨reached, step, ordered, step', suffix', stack, read, stack', read'⟩

end Blanc.Lift
