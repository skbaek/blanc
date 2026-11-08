import Blanc.Lift.ExactCallProfile

/-!
# Transport across the static initial-gas coordinate

Changing `Sevm.gas` retains each instruction's complete dynamic input and output.
In spawning steps the child message and execution slot stay the same. Dynamic
`Devm.gasLeft`, including the value observed by GAS, is not changed here.
-/

namespace Blanc.Lift

open Jaune

/-- Transport a profile with the identical debit, successor and fixed predicates. -/
theorem ExactCallProfile.withStaticGas
    {s : Sevm} {op : Ninst}
    {entry : Devm → List B256 → Mem → Nat → Devm}
    {Ready : Devm → List B256 → Mem → Nat → Prop}
    {After : Devm → List B256 → Mem → Devm → Prop} {U : Nat}
    {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (h : ExactCallProfile s op entry Ready After U debit next) (F : Nat) :
    ExactCallProfile {s with gas := F} op entry Ready After U debit next := by
  exact ⟨h.entry_gas, h.congr, h.sound⟩

/-! ## Storage and calldata reads

A storage access's charge and its post world, and a calldata word, read no static gas. -/

section Reads

variable (sevm : Sevm) (F : Nat)

theorem sloadCost_withStaticGas (b : Devm) (k : B256) :
    sloadCost {sevm with gas := F} b k = sloadCost sevm b k := rfl

theorem sstoreCost_withStaticGas (b : Devm) (k v : B256) :
    sstoreCost {sevm with gas := F} b k v = sstoreCost sevm b k v := rfl

theorem afterSload_withStaticGas (b : Devm) (k : B256) :
    afterSload {sevm with gas := F} b k = afterSload sevm b k := rfl

theorem dataWord_withStaticGas (i : B256) :
    Sevm.dataWord {sevm with gas := F} i = Sevm.dataWord sevm i := rfl

end Reads

end Blanc.Lift
