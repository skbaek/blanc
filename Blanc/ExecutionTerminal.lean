import Blanc.ForwardCall

/-!
# Common compiled terminal walks

Small, contract-neutral specializations of the general RETURN and REVERT
compiled-walk constructors for the offset-zero shapes used by contract proofs.
-/

namespace Blanc

open Jaune

/-- Return a known 32-byte word from memory offset zero. -/
theorem Func.runCompiledTo_ret_word_at_zero
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (memory : Mem) (gas : Nat) (output : Bytes)
    (hext :
      (base.setMach ⟨[0, 32], memory, gas⟩).extCost [⟨0, 32⟩] = 0)
    (hread : (memory.read 0 32).1 = output) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[0, 32], memory, gas⟩)
      (Func.last .ret)
      (.ok (((base.setMach ⟨[], memory, gas⟩).memRead 0 32).2.withOutput
        output)) := by
  have hrun := Func.runCompiledTo_ret_word
    (fs := fs) (sevm := sevm)
    (devm := base.setMach ⟨[0, 32], memory, gas⟩)
    (i := 0) (sz := 32) (s := []) (e := 0) (G := gas) (out := output)
    rfl hext rfl (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.memRead_fst,
        show (B256.toNat (0 : B256)) = 0 by decide,
        show (B256.toNat (32 : B256)) = 32 by decide] using hread)
  simpa only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach,
    show (B256.toNat (0 : B256)) = 0 by decide,
    show (B256.toNat (32 : B256)) = 32 by decide] using hrun

/-- Revert with the empty memory window at offset zero. -/
theorem Func.runCompiledTo_rev_empty_at_zero
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (memory : Mem) (gas : Nat) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[0, 0], memory, gas⟩)
      (Func.last .rev)
      (.error (.revert,
        (base.setMach ⟨[], memory, gas⟩).withOutput [])) := by
  have hrun := Func.runCompiledTo_rev
    (fs := fs) (sevm := sevm)
    (devm := base.setMach ⟨[0, 0], memory, gas⟩)
    (i := 0) (sz := 0) (s := []) (out := []) (G := gas)
    (d' := base.setMach ⟨[], memory, gas⟩)
    rfl (by
      change gas = gas +
        (base.setMach ⟨[0, 0], memory, gas⟩).extCost [⟨0, 0⟩]
      rw [Devm.extCost_empty_window]
      simp) (by exact Devm.memRead_zero)
  simpa only [Devm.setMach_setMach,
    show Nat.toB256 0 = (0 : B256) by decide] using hrun

end Blanc
