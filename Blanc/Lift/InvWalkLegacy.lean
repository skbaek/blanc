import Blanc.Lift.InvWalkStep
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.AccumulatedWalk
import Blanc.Lift.CodeSizeWalk
import Blanc.Lift.MutableCallPost
import Blanc.Lift.HistStaticCall
import Blanc.Lift.MemGlue
import Blanc.Lift.WalkCutKit

/-!
# Inversion walks of old-solc frames

The step, branch and normalization tactics shared by the inversion walks of pre-0.5 solc runtimes:
`EXP`-based packed reads, `MUL`, `div`-and-mask selector extraction, mapping hashes whose offsets
are `ADD`-chained literals, and memory a storage walk never reads back.  Nothing here names a
contract.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- A straight-line step: `istep`, or the `EXP`/`MUL` steps it does not cover, or an unconditional
goto. -/
macro "ustep " h:ident : tactic => `(tactic|
  first
  | istep $h
  | (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_exp hd
     subst e; clear hd)
  | (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_mul hd
     subst e; clear hd)
  | (have h' := ric_jump List.not_mem_nil rfl $h; clear $h; obtain ⟨_, $h:ident⟩ := h'))

/-- An `EXTCODESIZE` step, over the frame's actual access schedule. -/
macro "ucodesize " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_extcodesizeH (HistFork.bal_none ‹HistFork _›) hd
   subst e; clear hd))

/-- A `GAS` step. -/
macro "ugas " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, _, e⟩ := ri_gas hd
   subst e; clear hd))

/-- A conditional goto whose target stays in the walk: both arms are kept. -/
macro "ubranchTo " h:ident c:ident : tactic => `(tactic|
  (have h' := ric_branchTo List.not_mem_nil rfl $h; clear $h
   rcases h' with ⟨$c, _, $h⟩ | ⟨$c, _, $h⟩))

/-- One comparison of a linear or binary-search dispatcher on a known selector. -/
macro "udisp " h:ident : tactic => `(tactic| first
  | (have h' := ric_cmp_gt $h; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (rw [if_pos (by decide)] at $h:ident)
     | (rw [if_neg (by decide)] at $h:ident))
  | (have h' := ric_cmp_eq List.not_mem_nil rfl $h; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (rw [if_pos (by decide)] at $h:ident)
     | (rw [if_neg (by decide)] at $h:ident))
  | (have h' := ric_dest $h; clear $h; obtain ⟨_, $h:ident⟩ := h'))

/-- **A debit-then-credit lowers no slot but the debited one**: the shape of optimized solc's
balance move, read through the consumer's slot apartness. -/
theorem move_slots_ge {σ : Stor} {ks kd k w v : B256}
    (hnof : v.toNat + ((σ.set ks w).get kd).toNat < 2 ^ 256) (hk : k ≠ ks) :
    (σ.get k).toNat ≤ (((σ.set ks w).set kd (v + (σ.set ks w).get kd)).get k).toNat := by
  by_cases hkd : k = kd
  · subst hkd
    rw [Stor.get_set_self, Stor.get_set_ne _ (Ne.symm hk)] at *
    rw [B256.toNat_add_eq_of_nof _ _ hnof]
    omega
  · rw [Stor.get_set_ne _ (Ne.symm hkd), Stor.get_set_ne _ (Ne.symm hk)]

theorem Mem.Wf.read_snd {μ : Mem} (h : Mem.Wf μ) (i n : Nat) : Mem.Wf (μ.read i n).2 :=
  Nat.le_trans h (memExtSize_ge _ _ _)

/-- Mem well-formedness of a walk's memory term. -/
macro "uwf" : tactic => `(tactic|
  repeat (first
    | with_reducible apply Mem.Wf.write
    | with_reducible apply Mem.Wf.read_snd
    | with_reducible assumption))

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- `umem`, carrying the memory's well-formedness `wf`. -/
elab "umemw " h:ident wf:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some st := ty.find? (fun x => x.isAppOfArity ``Blanc.Lift.St 4)
    | throwError "umemw: no walk state"
  let ms ← Term.exprToSyntax (st.getArg! 2)
  let mn := mkIdent (← mkFreshUserName `M)
  let wn := mkIdent (← mkFreshUserName `wfn)
  evalTactic (← `(tactic| (have $wn:ident : Mem.Wf $ms := by uwf)))
  evalTactic (← `(tactic| clear $wf:ident))
  evalTactic (← `(tactic| generalize $ms = $mn:ident at $h:ident $wn:ident))
  evalTactic (← `(tactic| rename_i $wf:ident))

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- Generalize the memory of the walk state of cut run `h`: a storage walk reads only the words its
hashes already left on the stack. -/
elab "umem " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some st := ty.find? (fun x => x.isAppOfArity ``Blanc.Lift.St 4)
    | throwError "umem: no walk state"
  let ms ← Term.exprToSyntax (st.getArg! 2)
  let mn := mkIdent (← mkFreshUserName `M)
  evalTactic (← `(tactic| generalize $ms = $mn:ident at $h:ident))

end Blanc.Lift
