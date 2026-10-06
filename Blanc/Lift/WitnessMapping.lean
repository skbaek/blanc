import Blanc.Lift.Witness
import Blanc.Lift.Vyper

/-! Symbolic mapping scratch and selected storage effects for the witness interpreter.
The memory and worlds remain variables; no concrete memory image is unfolded. -/

namespace Blanc.Lift.WitnessMapping

open Jaune Blanc.Lift Blanc.Lift.Witness

def slotEntry (b : Devm) (M : Mem) (G : Nat) (slot key : B256) (S : List B256)
    (f : SFunc) (K : List SFunc) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow) : Cfg :=
  ⟨St b (key :: slot :: S) M (G + 60), vySlot f, K, keys, adrs, stor, acs⟩

def slotPost (b : Devm) (M : Mem) (G : Nat) (slot key : B256) (S : List B256)
    (f : SFunc) (K : List SFunc) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow) : Cfg :=
  ⟨St b (mapSlot slot key :: S) ((M.write 224 key.toBytes).write 192 slot.toBytes) G,
    f, K, keys, adrs, stor, acs⟩

/-- The seven actual scratch/hash instructions, for any covered aligned memory.
The resulting hash is computed from the symbolic recipient, not supplied as a
successful-cut premise. -/
theorem slot_run (fs : List SFunc) (s : Sevm) (b : Devm) (M : Mem) (G : Nat)
    (slot key : B256) (S : List B256) (f : SFunc) (K : List SFunc)
    (keys : List (Adr × B256)) (adrs : List Adr) (stor : StorShadow) (acs : AcctShadow)
    (hroom : S.length + 4 < 1024) (hcover : 256 ≤ M.size) (halign : M.size % 32 = 0) :
    wrun fs s 7 (slotEntry b M G slot key S f K keys adrs stor acs) =
      .cont (slotPost b M G slot key S f K keys adrs stor acs) := by
  have hs1 : (M.write 224 key.toBytes).size = M.size := by
    rw [Mem.size_write_word_at, ite_eq_left (by omega)]
  have hs2 : ((M.write 224 key.toBytes).write 192 slot.toBytes).size = M.size := by
    rw [Mem.size_write_word_at, hs1, ite_eq_left (by omega)]
  have hc1 := Devm.extCost_zero_of_le (devm := b) (S := S) (G := 0)
    (i := 224) (sz := 32) halign (by omega)
  have hc2 := Devm.extCost_zero_of_le (devm := b) (S := S) (G := 0)
    (N := M.write 224 key.toBytes) (i := 192) (sz := 32) (by rw [hs1]; exact halign)
    (by rw [hs1]; omega)
  have hc3 := Devm.extCost_zero_of_le (devm := b) (S := S) (G := 0)
    (N := (M.write 224 key.toBytes).write 192 slot.toBytes) (i := 192) (sz := 64)
    (by rw [hs2]; exact halign) (by rw [hs2]; omega)
  simp only [Devm.extCost, Devm.memory_setMach] at hc1 hc2 hc3
  have hm : ((M.write 224 key.toBytes).write 192 slot.toBytes).extend 192 64 =
      (M.write 224 key.toBytes).write 192 slot.toBytes :=
    Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs2]; exact halign) (by rw [hs2]; omega))
  have hh := vySlot_keccak M slot key
  simp only [Mem.read, array_sliceD_eq_list] at hh
  have he0 : Bytes.toB256 [224] = 224 := rfl
  have hc0 : Bytes.toB256 [192] = 192 := rfl
  have h40 : Bytes.toB256 [64] = 64 := rfl
  have hne0 : (224 : B256).toNat = 224 := rfl
  have hnc0 : (192 : B256).toNat = 192 := rfl
  have hn40 : (64 : B256).toNat = 64 := rfl
  have hgas : G + 60 - 3 - 3 - 3 - 3 - 3 - 3 - 42 = G := by omega
  have hg1 : 3 ≤ G + 60 - 3 := by omega
  have hg2 : 3 ≤ G + 60 - 3 - 3 - 3 := by omega
  have hg3 : 42 ≤ G + 60 - 3 - 3 - 3 - 3 - 3 - 3 ∧ S.length < 1024 := by
    constructor <;> omega
  simp (disch := simp only [Devm.gasLeft, Devm.stack, Devm.setMach, List.length_cons]; first | omega | constructor <;> omega) only
    [slotEntry, slotPost, vySlot, wrun, wstep, ninstAccKeeps,
    Ninst.step_push, St, Devm.setMach,
    Devm.gasLeft, Devm.stack, Devm.memory, Devm.stateGas, chargeGas_eq_ok,
    Devm.push_eq_ok, gVerylow, gKeccak256, gasKeccak256Word, bind, Except.bind,
    Step.ofExecution, mstoreStep, keccakStep, Devm.extCost,
    he0, hc0, h40, hne0, hnc0, hn40, hc1, hc2, hc3, ← mem_write_eq_B,
    hm, hh, ceilDiv, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul,
    List.length_cons, List.length_nil, List.cons_ne_nil, ite_false, ite_true,
    and_true, Nat.reduceMod, hgas, hg1, hg2, hg3]

end Blanc.Lift.WitnessMapping
