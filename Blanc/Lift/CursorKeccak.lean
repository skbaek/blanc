import Blanc.Lift.ReachSstoreLoops
import Blanc.Lift.CursorOccurrence

/-! Successful observed hashes at their original raw-prefix positions. -/

namespace Blanc.Lift

open Jaune

/-- Cross one hash while retaining the runtime witness and its full edge observation. -/
theorem ObservedKeccak.of_next {P : Sevm → Devm → Ninst → Devm → Prop}
    {observe : Conf → Conf → Prop} {fs : List SFunc} {sevm : Sevm}
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach P observe fs sevm ⟨St b (0 :: 64 :: S) M G, .next (.reg .keccak256) f, K⟩ T)
    (hT : AtSstore T) {input : Bytes} {shape : SFunc → Prop}
    (read : (M.read 0 64).1 = input) (source : shape (.next (.reg .keccak256) f)) :
    ∃ G', ObservedKeccak P observe sevm input shape ∧
      ObservedReach P observe fs sevm
        ⟨St b ((M.read 0 64).1.keccak :: S) (M.read 0 64).2 G', f, K⟩ T := by
  obtain ⟨d', runtime, observed, run⟩ := ObservedReach.nextS (by intro h; cases h) run hT
  obtain ⟨G', rfl⟩ := ri_keccak (erase runtime)
  exact ⟨G', ⟨_, _, runtime, observed, ⟨f, rfl, rfl, rfl⟩, ⟨S, rfl⟩, read, source⟩, run⟩

/-- A successful hash occurrence at its actual source cursor, strictly before the original stop. -/
theorem ObservedKeccak.actual {code : ByteArray} {c : Cert} {R stop : Exec.Deriv}
    {input : Bytes} {shape : SFunc → Prop}
    (hash : ObservedKeccak (StepIn R) (Cursor.RawEdgeAt code c R stop) R.sevm input shape) :
    ∃ (occurrence : Exec.NinstOccurrence R) (next : Exec.Deriv) (here : Cursor),
      occurrence.instruction = .reg .keccak256 ∧ occurrence.stepResult = .ok next.devm ∧
      Exec.Deriv.ParentPrefix R occurrence.node ∧ Exec.Deriv.ParentStep next occurrence.node ∧
      Exec.Deriv.ParentPrefix next stop ∧ CursorOK code c occurrence.node here ∧ shape here.f ∧
      (∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest) ∧
      (occurrence.node.devm.memory.read 0 64).1 = input := by
  rcases hash with ⟨before, after, runtime, observed, ⟨tail, tree, postTree, sameK⟩, stack, read, source⟩
  rcases observed with ⟨node, next, here, there, reached, edge, suffix, sameEnv,
    beforeEq, afterEq, synthetic, placed, placedNext⟩
  subst before
  subst after
  change here.f = .next (.reg .keccak256) tail at tree
  have decoded := placed.ninstAt_of_next tree
  have raw : node ∈ Exec.rawNodes R.exc := by
    obtain ⟨earlier, decomposition⟩ := Blanc.Exec.Deriv.ParentPrefix.rawNodes_decomposition reached
    rw [decomposition]
    exact List.mem_append_right earlier (Exec.mem_rawNodes_self node.exc)
  obtain ⟨occurrence, sameNode, instruction⟩ := Exec.exists_ninstOccurrence_of_mem_rawNodes raw decoded
  have primitive : Ninst.Run node.sevm node.devm (.reg .keccak256) next.devm := by
    rw [sameEnv]
    exact StepIn.toRun runtime
  obtain ⟨slot, filled, pc, stepRun⟩ := primitive
  have actual : Ninst.StepRun occurrence.node.pc occurrence.node.sevm occurrence.node.devm
      occurrence.instruction slot (.ok next.devm) := by
    rw [sameNode, instruction]
    exact Ninst.stepRun_pc_irrel rfl stepRun
  have result := (occurrence_stepRun_unique occurrence filled actual).2
  refine ⟨occurrence, next, here, instruction, result, ?_⟩
  rw [sameNode]
  exact ⟨reached, edge, suffix, placed, source, stack, read⟩

/-- One actual successful hash, with its exact input and ordered edge before the given stop. -/
def KeccakBefore (root stop : Exec.Deriv) (input : Bytes) (pc : Nat) : Prop :=
  ∃ (occurrence : Exec.NinstOccurrence root) (next : Exec.Deriv),
    occurrence.node.pc = pc ∧ occurrence.instruction = .reg .keccak256 ∧
    occurrence.stepResult = .ok next.devm ∧
    Exec.Deriv.ParentPrefix root occurrence.node ∧ Exec.Deriv.ParentStep next occurrence.node ∧
    Exec.Deriv.ParentPrefix next stop ∧
    (∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest) ∧
    (occurrence.node.devm.memory.read 0 64).1 = input

end Blanc.Lift
