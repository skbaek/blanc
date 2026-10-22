import Blanc.Lift.WalkSteps
import Blanc.Lift.MemMap

/-!
# Vyper 0.2.x fixed-array storage slots

Vyper 0.2.x addresses element `i` of a fixed-size storage array declared at slot `s` as
`keccak256(s) + i`, computed through the scratch word at `0xc0`:

```
PUSH1 s  PUSH1 0xc0  MSTORE  PUSH1 0x20  PUSH1 0xc0  SHA3  ADD
```

with `i` on the stack beneath (then `SLOAD` or `SSTORE`).  The hashing core
`PUSH1 0xc0 MSTORE PUSH1 0x20 PUSH1 0xc0 SHA3` also occurs with the slot brought up by
`DUP`, and without the trailing `ADD` (element `0`); `vyArrayBase` is that core and
`vyArraySlot` the full pushed-slot form.

* `ric_vyArrayBase` / `ric_vyArraySlot`: inversion over cut runs; the pushed word is
  `Bytes.keccak s.toBytes` (resp. `Bytes.keccak s.toBytes + i`);
* `rxc_vyArrayBase` / `rxc_vyArraySlot`: the forward twins over exact cut runs, over a
  word-aligned memory that already covers `0xe0` (no expansion; 48 resp. 54 gas).

The digest is not interpreted here: storage-layout facts such as `coinsBase_eq` name it.
Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- A word written at `n` reads back as its bytes, on any memory (no `Mem.Wf`). -/
theorem Mem.read_write_word_self (μ : Mem) (n : Nat) (v : B256) :
    ((μ.write n v.toBytes).read n 32).1 = v.toBytes := by
  have hw := (Mem.memWord_write_word μ n v).1
  have hlen : ((μ.write n v.toBytes).read n 32).1.length = 32 := by
    simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
  unfold memWord at hw
  rw [← Bytes.toBytes_toB256_of_length hlen, hw]

/-- The hashing core: from `[slot, …]`, `mstore(0xc0, slot); keccak(0xc0, 0x20)`, then `f`. -/
def vyArrayBase (f : SFunc) : SFunc :=
  .next (.push [0xc0] (by decide)) (.next (.reg .mstore)
    (.next (.push [0x20] (by decide)) (.next (.push [0xc0] (by decide))
      (.next (.reg .keccak256) f))))

/-- The pushed-slot element address: from `[i, …]`, push the slot `s`, hash it, add `i`. -/
def vyArraySlot (s : UInt8) (f : SFunc) : SFunc :=
  .next (.push [s] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_le_ofNat])) (vyArrayBase (.next (.reg .add) f))

/-- The memory the hashing core leaves: the slot in the scratch word, the hashed window's
(no-op on an aligned memory covering `0xe0`) extension. -/
def vyArrayMem (M : Mem) (slot : B256) : Mem :=
  ((M.write 0xc0 slot.toBytes).read 0xc0 32).2

section Inv

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f : SFunc} {r : Seg}

/-- **The hashing core, inverted.** -/
theorem ric_vyArrayBase {slot : B256}
    (run : SFunc.RunCut fs sevm C (St b (slot :: S) M G) (vyArrayBase f) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b (Bytes.keccak slot.toBytes :: S) (vyArrayMem M slot) G') f r := by
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 0xc0 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  unfold vyArrayBase at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_keccak s1
  rw [hc0, h20, Mem.read_write_word_self] at run
  exact ⟨G5, run⟩

/-- **The pushed-slot element address, inverted**: the pushed word is `keccak(s) + i`. -/
theorem ric_vyArraySlot {s : UInt8} {i : B256}
    (run : SFunc.RunCut fs sevm C (St b (i :: S) M G) (vyArraySlot s f) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b ((Bytes.keccak (Bytes.toB256 [s]).toBytes + i) :: S)
        (vyArrayMem M (Bytes.toB256 [s])) G') f r := by
  unfold vyArraySlot at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨G2, run⟩ := ric_vyArrayBase run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_add s1
  exact ⟨G3, run⟩

end Inv

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f : SFunc} {r : Seg}

/-- **The hashing core, forward**, over a word-aligned memory of size `n ≥ 0xe0`
(3 + 3 + 3 + 3 + 36 = 48 gas, no expansion; the memory keeps its size). -/
theorem rxc_vyArrayBase {slot : B256} {n : Nat} (hM : M.size = n) (hn : 0xe0 ≤ n)
    (h32 : n % 32 = 0) (hroom : S.length + 2 < 1024)
    (k : SFunc.RunExactCut fs sevm C
      (St b (Bytes.keccak slot.toBytes :: S) (M.write 0xc0 slot.toBytes) G) f r) :
    SFunc.RunExactCut fs sevm C (St b (slot :: S) M (G + 48)) (vyArrayBase f) r := by
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 0xc0 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have hs1 : (M.write 0xc0 slot.toBytes).size = n := by
    rw [Mem.size_write_word_at, hM]
    split_ifs with h
    · rfl
    · omega
  unfold vyArrayBase
  refine rxc_push (G := G + 45) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mstore (c := 3) (M' := M.write 0xc0 slot.toBytes) ?_ (by rw [hc0]) ?_
  · rw [hc0, St, Devm.extCost_zero_of_le (by rw [hM]; exact h32) (by rw [hM]; omega)]; rfl
  refine rxc_push (G := G + 39) rfl (by omega) ?_
  refine rxc_push (G := G + 36) rfl (by simp only [List.length_cons]; omega) ?_
  refine .next (Ninst.runCompiled_keccak256_of
    (devm := St b (Bytes.toB256 [0xc0] :: Bytes.toB256 [0x20] :: S)
      (M.write 0xc0 slot.toBytes) (G + 36)) (G := G) (c := 36) rfl ?_ ?_ ?_ rfl
      (by omega)) k
  · rw [hc0, h20, St, Devm.extCost_zero_of_le (by rw [hs1]; exact h32) (by rw [hs1]; omega)]
    decide
  · rw [hc0, h20, St.memory, Mem.read_write_word_self]
  · rw [hc0, h20, St.memory]
    exact Mem.read_snd_eq_self (by rw [hs1]; exact memExtSize_of_le h32 (by omega))

/-- **The pushed-slot element address, forward** (54 gas, no expansion). -/
theorem rxc_vyArraySlot {s : UInt8} {i : B256} {n : Nat} (hM : M.size = n) (hn : 0xe0 ≤ n)
    (h32 : n % 32 = 0) (hroom : S.length + 3 < 1024)
    (k : SFunc.RunExactCut fs sevm C
      (St b ((Bytes.keccak (Bytes.toB256 [s]).toBytes + i) :: S)
        (M.write 0xc0 (Bytes.toB256 [s]).toBytes) G) f r) :
    SFunc.RunExactCut fs sevm C (St b (i :: S) M (G + 54)) (vyArraySlot s f) r := by
  unfold vyArraySlot
  refine rxc_push (G := G + 51) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_vyArrayBase (G := G + 3) hM hn h32 (by simp only [List.length_cons]; omega) ?_
  exact rxc_add (by omega) k

end Fwd

end Blanc.Lift
