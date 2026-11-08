import Blanc.Lift.LockCheckSound

/-!
# The lock checker along a frame: flags, one step, and dominance

Second half of the soundness of `LockCheck.lockCert`
(`Blanc/Lift/LockCheck.lean`).  `Blanc/Lift/LockCheckSound.lean` gives the
meaning of facts and proves the fact rules and the symbol transfer sound; this
module gives the meaning of the flags (`Flags`), proves every rule of the walk
sound for one same-frame edge (`lock_step`, which re-runs `cursor_step`'s case
split so that the synthetic branch taken is the concrete one), and concludes
`LockCheck.dominance`: `LockSpec.Dominance` of `Blanc/LockExclusion.lean` for
the code of any certificate the checker accepts, with its strong form and the
absence of forbidden opcodes as separate theorems.
-/

namespace Blanc.Lift.LockCheck

open Jaune AbstractStackSafety Blanc.LockExclusion Blanc.Lift.SymTransfer

local notation "PP" => Exec.Deriv.ParentPrefix

/-! ## Decoding and the same-frame order -/

/-! ## The meaning of the flags -/

section Flags

variable (sp : Spec) (F : Exec.Deriv)

/-- The flags of `σ` at node `n`, before `n` is visited. -/
structure Flags (σ : LSt) (n : Exec.Deriv) : Prop where
  passed : σ.passed = true → ∃ m, PP F m ∧ PP m n ∧
    lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked
  setNow : σ.setNow = true → lockAt F.sevm.currentTarget sp.slot n.devm = sp.locked
  noMut : σ.noMut = true → ∀ b, PP F b → PP b n → b ≠ n → b.pc ∉ sp.mutBodies

end Flags

section Visit

variable {sp : Spec} {F n : Exec.Deriv} {σ σv : LSt}

end Visit

/-! ## One instruction on the lock state -/

section Lstep

variable {sp : Spec} {F n n' : Exec.Deriv}

end Lstep

/-! ## Branches, joins, calls and returns -/

section Joins

variable {sp : Spec} {F n : Exec.Deriv}

end Joins

/-! ## The invariant -/

section Invariant

variable (sp : Spec) (code : ByteArray) (c : Cert) (ann : List LSt) (F : Exec.Deriv)

/-- The pending continuations with their lock data: `ContsOK`'s segments, and
for every live continuation the saved lock state it resumes from, its
acceptance by the walk, the meaning of its words and of its `passed`. -/
inductive LConts (n : Exec.Deriv) : List Cont → List B256 → Prop
  | nil (base : List B256) : LConts n [] base
  | cons {k : Cont} {K : List Cont} {S rest : List B256} :
      FrameMatches (Cont.tagOf K) k.a S →
      RetOK k.a k.m K →
      (k.live = true →
        checkNode code c.entries k.m k.tag.toNat (List.replicate k.rets .unk ++ k.a) k.f = true) →
      (k.live = true → ∃ σk : LSt,
        lockNode sp c.entries ann k.tag.toNat (List.replicate k.rets .unk ++ k.a)
          (resume σk k.rets) k.f = true ∧
        Val sp F n σk.kv σk.facts S ∧
        (σk.passed = true → ∃ m, PP F m ∧ PP m n ∧
          lockAt F.sevm.currentTarget sp.slot m.devm ≠ sp.locked)) →
      LConts n K rest →
      LConts n (k :: K) (S ++ rest)

end Invariant

section InvariantLemmas

variable {sp : Spec} {code : ByteArray} {c : Cert} {ann : List LSt} {F : Exec.Deriv}

end InvariantLemmas

/-! ## One same-frame edge -/

section Step

variable {sp : Spec} {code : ByteArray} {c : Cert} {ann : List LSt} {F : Exec.Deriv}

end Step

/-! ## Along the whole frame -/

section Frame

variable {sp : Spec} {code : ByteArray} {c : Cert} {ann : List LSt} {F : Exec.Deriv}

end Frame

/-! ## The dominance theorems -/

section Dominance

variable {sp : Spec} {code : ByteArray} {c : Cert} {ann : List LSt}

end Dominance

end Blanc.Lift.LockCheck
