import Blanc.OwnerClosure

/-!
# Owner closure is not vacuous: a two-code family

A toy instance of `Exec.ownerCode_of_closed`: the family `{toyForwarder, toyLeaf}`, where
`toyForwarder` is the EIP-1167 forwarder `DELEGATECALL`ing the fixed address `toyImpl` and
`toyLeaf` is the one-byte `STOP`.  From world premises alone (`P` holds a family code, `toyImpl`
holds the leaf, the root runs accordingly), `Exec.DelegationClosed` is discharged for every run,
so every committed frame owning `P`'s storage runs the forwarder or the leaf.
-/

namespace Blanc.OwnerClosureControl

open Jaune Blanc

/-- The toy forwarder's fixed implementation address. -/
def toyImpl : Adr := 0x00000000000000000000000000000000000000aa

/-- The leaf: a single `STOP`. -/
def toyLeaf : ByteArray := ⟨#[0x00]⟩

/-- The EIP-1167 forwarder to `toyImpl`. -/
def toyForwarder : ByteArray := forwarderCode toyImpl

/-- The two-code family. -/
def ToyFamily (c : ByteArray) : Prop := c = toyForwarder ∨ c = toyLeaf

/-- The external instruction a decoded instruction is, if any. -/
private def execKind : Option Inst → Option Xinst
  | some (.next (.exec x)) => some x
  | _ => none

private theorem forwarderShape_toy : ForwarderShape toyForwarder toyImpl := by
  decide +kernel

/-- In the forwarder's bytes, the only external instruction is the `DELEGATECALL` at `31`. -/
private theorem forwarder_scan :
    ∀ pc, pc < 45 → execKind (toyForwarder.getInst pc) = none ∨
      (pc = 31 ∧ execKind (toyForwarder.getInst pc) = some .delegatecall) := by
  decide +kernel

private theorem getInst_out {c : ByteArray} {pc : Nat} (h : c.size ≤ pc) :
    c.getInst pc = some (.last .stop) := by
  have hout : ¬ pc < c.size := by omega
  unfold ByteArray.getInst
  simp only [hout, ↓reduceDIte]

private theorem forwarder_exec {pc : Nat} {x : Xinst} (hat : Xinst.At toyForwarder pc x) :
    pc = 31 ∧ x = .delegatecall := by
  unfold Xinst.At at hat
  by_cases hpc : pc < 45
  · rcases forwarder_scan pc hpc with h | ⟨h31, h⟩ <;>
      simp only [hat, execKind, reduceCtorEq, Option.some.injEq] at h
    exact ⟨h31, h⟩
  · rw [getInst_out (by rw [forwarderShape_toy.1]; omega)] at hat
    cases hat

private theorem leaf_exec {pc : Nat} {x : Xinst} : ¬ Xinst.At toyLeaf pc x := by
  unfold Xinst.At
  by_cases hpc : pc < 1
  · obtain rfl : pc = 0 := by omega
    rw [show toyLeaf.getInst 0 = some (.last .stop) from rfl]
    exact fun h => nomatch h
  · rw [getInst_out (by change 1 ≤ pc; omega)]
    exact fun h => nomatch h

private theorem leaf_ne_nil : toyLeaf.toList ≠ [] := by decide +kernel

private theorem leaf_nd : ¬ isValidDelegation toyLeaf := fun hd => absurd hd.1 (by decide)

/-- Along a forwarder frame, the stack at its pcs follows `ForwarderReach`. -/
private theorem toy_reach {R n : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix R n) :
    R.sevm.code = toyForwarder → R.devm.getCode toyImpl = toyLeaf →
      ForwarderReach toyImpl R.pc R.devm.stack → ForwarderReach toyImpl n.pc n.devm.stack := by
  induction chain with
  | refl => exact fun _ _ h => h
  | step head _ ih =>
      intro code leaf reach
      have nd := leaf_nd
      rw [← leaf] at nd
      have keep := Blanc.Exec.Deriv.ParentStep.codePreserve head toyImpl
        (by rw [leaf]; exact leaf_ne_nil)
      refine ih (by rw [Blanc.Exec.Deriv.ParentStep.sevm_eq head]; exact code)
        (keep.trans leaf) ?_
      cases head with
      | cont hstep _ => exact forwarderShape_toy.reach_cont code reach hstep
      | doneOk hstep _ _ _ =>
          exact Or.inr (Or.inr (Or.inr
            (le_of_eq (forwarderShape_toy.reach_spawn code reach hstep nd).1.symm)))
      | runOk hstep _ _ _ _ =>
          exact Or.inr (Or.inr (Or.inr
            (le_of_eq (forwarderShape_toy.reach_spawn code reach hstep nd).1.symm)))

/-- Every committed frame starts at pc `0` and finds the leaf installed at `toyImpl`. -/
private theorem toy_frames {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (hI : pre.getCode toyImpl = toyLeaf)
    (hrootI : sevm.currentTarget = toyImpl → sevm.code = toyLeaf)
    (fork : CoveredFork sevm.benvStat.fork) :
    ∀ F ∈ Exec.committedFrames run, F.pc = 0 ∧ F.pre.getCode toyImpl = toyLeaf := by
  have spawns : OwnSpawns toyImpl toyLeaf := by
    intro R N x _ code _ _ chain hat
    rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain, code] at hat
    exact (leaf_exec hat).elim
  intro F member
  by_cases committed : Execution.commits out = true
  · rw [Exec.committedFrames, dite_eq_left committed] at member
    rcases List.mem_cons.mp member with rfl | deeper
    · exact ⟨rfl, hI⟩
    · obtain ⟨code, pcZero, -⟩ := Exec.descendantFrames_ownCode leaf_ne_nil leaf_nd spawns run
        (R := ⟨0, sevm, pre, out, run⟩) (.refl _) rfl fork hI hrootI F deeper
      exact ⟨pcZero, code⟩
  · rw [Exec.committedFrames_eq_nil_of_not_commits run committed] at member
    exact (List.not_mem_nil member).elim

/-- **The toy instance.**  With `P` holding the forwarder or the leaf and `toyImpl` holding the
leaf, every committed frame owning `P`'s storage runs the forwarder or the leaf. -/
theorem toy_ownerCode {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) {P : Adr} (hP : ToyFamily (pre.getCode P))
    (hI : pre.getCode toyImpl = toyLeaf)
    (hroot : sevm.currentTarget = P → ToyFamily sevm.code)
    (hrootI : sevm.currentTarget = toyImpl → sevm.code = toyLeaf)
    (fork : CoveredFork sevm.benvStat.fork) :
    ∀ G ∈ Exec.committedFrames run, G.sevm.currentTarget = P → ToyFamily G.sevm.code := by
  have family_nonempty : ∀ c, ToyFamily c → 0 < c.size := by
    rintro c (rfl | rfl)
    · rw [forwarderShape_toy.1]; decide
    · decide
  have family_nd : ∀ c, ToyFamily c → ¬ isValidDelegation c := by
    rintro c (rfl | rfl)
    · exact fun hd => absurd hd.1 (by rw [forwarderShape_toy.1]; decide)
    · exact leaf_nd
  refine Exec.ownerCode_of_closed run family_nonempty family_nd hP hroot fork ?_
  intro F member _ family n chain
  obtain ⟨pcZero, implLeaf⟩ := toy_frames run hI hrootI fork F member
  have codeEq : n.sevm.code = F.sevm.code :=
    congrArg Sevm.code (Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain)
  have nodeLeaf : n.devm.getCode toyImpl = toyLeaf :=
    ((Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 toyImpl
      (by rw [show (Blanc.Exec.Frame.rootDeriv F).devm = F.pre from rfl, implLeaf];
          exact leaf_ne_nil)).trans implLeaf
  rw [codeEq]
  rcases family with forwarder | leaf
  · rw [forwarder]
    refine ⟨fun hat => absurd (forwarder_exec hat).2 (by decide), fun hat g a rest stack => ?_⟩
    have reach := toy_reach chain forwarder implLeaf (Or.inl (by
      rw [show (Blanc.Exec.Frame.rootDeriv F).pc = F.pc from rfl, pcZero]; omega))
    rw [(forwarder_exec hat).1] at reach
    rcases reach with h | ⟨h, -⟩ | ⟨-, g', w, s, hs, hw⟩ | h
    · omega
    · omega
    rotate_left
    · omega
    rw [stack] at hs
    obtain ⟨-, rfl, -⟩ := List.cons.inj hs
    rw [hw, nodeLeaf]
    exact ⟨Or.inr rfl, by simp only [getDelegatedCodeAddress, leaf_nd, ↓reduceIte]⟩
  · rw [leaf]
    exact ⟨leaf_exec, fun hat => (leaf_exec hat).elim⟩

end Blanc.OwnerClosureControl
