import Blanc.Lift.LockCheck
import Blanc.Lift.SymTransfer
import Blanc.Lift.Cursor
import Blanc.LockExclusion

/-!
# Soundness of the reentrancy-lock checker

`LockCheck.dominance` (proved in `Blanc/Lift/LockCheckFlow.lean` from this
module): for any certificate `c` with `Cert.check code c` and
`lockCert sp c ann`, every frame running `code` from pc `0` on a covered fork
whose executed hashes avoid the slot meets the dominance obligation of
`Blanc/LockExclusion.lean` (every body start and every slot-addressed
`SSTORE` has an earlier node of the frame where the lock was not held; every
mutating body start holds it), plus its strong form (inside a guarded mutating
body only release pcs write the slot) and the absence of `DELEGATECALL`,
`CALLCODE`, `CREATE`, `CREATE2` and `SELFDESTRUCT`.

The proof is one induction along the frame's same-frame chain
(`Exec.Deriv.ParentPrefix`), whatever the frame's outcome: the invariant
`LockOK` pairs the certificate cursor (`CursorOK`, re-established here step by
step exactly as `cursor_step` does, so the synthetic branch taken is the
concrete one) with the lock walk (`lockNode … = true`), the meaning of the
abstract lock state (`LSt.Val`, `LSt.Flags`) and one saved lock state per
pending `callNext` continuation (`LConts`).
-/

namespace Blanc.Lift.LockCheck

open Jaune AbstractStackSafety Blanc.LockExclusion Blanc.Lift.SymTransfer

local notation "PP" => Exec.Deriv.ParentPrefix

/-! ## Facts and their meaning -/

section Facts

variable (sp : Spec) (F n : Exec.Deriv) (ρ : Nat → B256)

/-- The meaning of one fact in the frame rooted at `F`, at its node `n`,
under the symbol valuation `ρ`. -/
def Fact.Holds : Fact → Prop
  | .bnd s lo hi => lo ≤ (ρ s).toNat ∧ (ρ s).toNat ≤ hi
  | .nsl s => ρ s ≠ sp.slot
  | .lt s t => (ρ s).toNat < (ρ t).toNat
  | .le s t => (ρ s).toNat ≤ (ρ t).toNat
  | .gt r s k => (ρ r = 0 → (ρ s).toNat ≤ k) ∧ (ρ r ≠ 0 → k < (ρ s).toNat)
  | .isz r s => (ρ r = 0 → ρ s ≠ 0) ∧ (ρ r ≠ 0 → ρ s = 0)
  | .xor r s t => ρ r ≠ 0 → ρ s ≠ ρ t
  | .lockv s => ∃ m, PP F m ∧ PP m n ∧
      ρ s = lockAt F.sevm.currentTarget sp.slot m.devm
  | .lockeq r => ρ r = 0 → ∃ m, PP F m ∧ PP m n ∧
      lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked

def AllHold (fs : List Fact) : Prop := ∀ f ∈ fs, Fact.Holds sp F n ρ f

end Facts

/-! ## Entailment is sound -/

section Entails

variable {sp : Spec} {F n : Exec.Deriv} {ρ : Nat → B256} {fs : List Fact}

/-- A projected `bnd` bound holds under the valuation. -/
private theorem bndProj_sound (hf : AllHold sp F n ρ fs) {f : Fact}
    (hmem : f ∈ fs) {s' lo hi : Nat} (h : bndProj f = some (s', lo, hi)) :
    lo ≤ (ρ s').toNat ∧ (ρ s').toNat ≤ hi := by
  have hH := hf f hmem
  cases f with
  | bnd s'' lo' hi' =>
    simp only [Fact.Holds] at hH
    simp only [bndProj] at h
    obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
    exact hH
  | nsl _ =>
    simp only [bndProj] at h
    cases h
  | lt _ _ =>
    simp only [bndProj] at h
    cases h
  | le _ _ =>
    simp only [bndProj] at h
    cases h
  | gt _ _ _ =>
    simp only [bndProj] at h
    cases h
  | isz _ _ =>
    simp only [bndProj] at h
    cases h
  | xor _ _ _ =>
    simp only [bndProj] at h
    cases h
  | lockv _ =>
    simp only [bndProj] at h
    cases h
  | lockeq _ =>
    simp only [bndProj] at h
    cases h

/-- Every symbol value fits in the checker's largest word. -/
private theorem val_le_maxW (ρ : Nat → B256) (t : Nat) : (ρ t).toNat ≤ maxW := by
  have := B256.toNat_lt (ρ t); unfold maxW; omega

theorem bndOf_sound (hf : AllHold sp F n ρ fs) (s : Nat) :
    (bndOf fs s).1 ≤ (ρ s).toNat ∧ (ρ s).toNat ≤ (bndOf fs s).2 :=
  BndInterval.bndOfG_sound (val_le_maxW ρ)
    (fun _f hmem _ _ _ h => bndProj_sound hf hmem h) s

end Entails

/-! ## Symbols and valuations -/

/-- The words `S` carry the symbols `kv` under a valuation satisfying `fs`. -/
def Val (sp : Spec) (F n : Exec.Deriv) (kv : List Nat) (fs : List Fact) (S : List B256) :
    Prop :=
  ∃ ρ : Nat → B256, List.Forall₂ (fun s w => ρ s = w) kv S ∧ AllHold sp F n ρ fs

/-! ## Concrete results of the instructions with fact rules -/

section Ops

variable {sevm : Sevm} {d d' : Devm} {x y : B256} {rest : List B256}

end Ops

/-! ## The fact rules are sound -/

section OpFacts

variable {sp : Spec} {F n n' : Exec.Deriv} {ρ : Nat → B256} {fs : List Fact} {r : Nat}
  {w : B256}

end OpFacts

end Blanc.Lift.LockCheck
