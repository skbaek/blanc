import Blanc.Lift.MemMap
import Blanc.Lift.MemPotential
import Blanc.WordArithmetic

/-!
# Solidity dynamic-string allocation: header store plus payload copy

Contract-neutral unit for Solidity dynamic-string allocation staging. It
proves single-allocation bounds and header facts, plus the actual `MSTORE` /
`CALLDATACOPY` bridge. It does not prove any enclosing multi-allocation
wrapper.

A Solidity dynamic string (or bytes) allocation at free pointer `p` with
length `len` performs two memory writes: an `MSTORE` of `len` at `p` (the
length header) and a copy of `len` payload bytes at `p + 32`. The
allocation's next free pointer rounds the payload up to a word:

* `allocWord len = 32 + (32 * ((31 + len) / 32))` (`ADD31`, `DIV32`,
  `MUL32`, then the header word, in source op order, all `B256` ops);
* `nextWord p len = allocWord len + p`;
* `roundedBytes lenN = ((lenN + 31) / 32) * 32` (the `Nat` round-up).

`allocation_facts` derives, from the two writes' post memory and a
`2 ^ 160` post-size bound (the existing `FreePtr.Pot` seam), the destination
unwrap, the header readback, the exact `nextWord` value with its no-wrap
bounds, and survival of every prior recorded word. `allocation_of_run` is
the actual-execution corollary over a real `MSTORE` run and a real
`CALLDATACOPY` run; `allocation_of_runP` is the same fact over a generic
`P`/`PotStep` pair via erasure. `allocation_fp64` preserves the
free-pointer word at `64` through both writes when `p` sits above it.

Reused (nothing re-proved): `Mem.memWord_write_word`, `Mem.write_agree`,
`Mem.write_base`, `memWord_congr`, `mstore_run_memory`,
`calldatacopy_run_memory`, `FreePtr.Pot.size_lt`, and the
`wordAdd_eq_toB256_add` / `wordDiv_eq_toB256_div` bridges with `Nat`
arithmetic. No `Mem.Wf` premise anywhere. No new gas, profile, endpoint,
or hash assumptions.

Remaining caller seams (not this file): the local memory equality between
the two steps (discharged by the caller's pure-step tracking) and the
post-`Pot` (the existing `withPot` seam).
-/

namespace Blanc.Lift.SolcStringAllocation

open Jaune Blanc Blanc.Lift

/-- Solidity allocation size for a payload of `len` bytes, in source op
order: `ADD31`, `DIV32`, `MUL32`, then the header word. All literals are
`B256`, and `+`, `/`, `*` are the word ops (`wordAdd_eq_toB256_add`,
`wordDiv_eq_toB256_div`, `B256.toNat_mul` describe them). -/
def allocWord (len : B256) : B256 :=
  32 + (32 * ((31 + len) / 32))

/-- Allocation next-pointer: allocation size plus base. -/
def nextWord (p len : B256) : B256 :=
  allocWord len + p

/-- `Nat` word round-up: payload bytes reserved for `lenN` bytes. -/
def roundedBytes (lenN : Nat) : Nat :=
  ((lenN + 31) / 32) * 32

/-- Word addition with its no-wrap certificate. -/
private theorem addNat {x y : B256} (h : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [wordAdd_eq_toB256_add]
  exact B256.toNat_toB256_of_lt h

/-- Word multiplication with its no-wrap certificate. -/
private theorem mulNat {x y : B256} (h : x.toNat * y.toNat < 2 ^ 256) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [B256.toNat_mul]
  exact Nat.lo_eq_of_lt h

/-- Word division by a nonzero divisor. -/
private theorem divNat {x y : B256} (hne : y ≠ 0) :
    (x / y).toNat = x.toNat / y.toNat := by
  rw [B256.toNat_div hne]

/-- Core header/copy fact. `Mout` is the memory after the length-header
store at `p` and the payload copy at `p + 32`; the `2 ^ 160` post-size
bound comes from the actual post-`Pot`. Proof order matters: the header
store already forces `p.toNat + 32` below the header size, the copy is
size-monotone, so the post bound unwraps the copy destination; the
nonempty-copy `write_base` bound (or the header bound in the
empty/`len = 0` case) then forces every later word op below `2 ^ 256`.
Never asserts that an empty copy expands memory. -/
theorem allocation_facts {M : Mem} {p len : B256} {ys : Bytes}
    (hlen : ys.length = len.toNat)
    (hPost : ((M.write p.toNat len.toBytes).write (p + 32).toNat ys).size < 2 ^ 160) :
    (p + 32).toNat = p.toNat + 32 ∧
    p.toNat + 32 + len.toNat < 2 ^ 160 ∧
    p.toNat + 32 ≤ ((M.write p.toNat len.toBytes).write (p + 32).toNat ys).size ∧
    p.toNat + 32 + len.toNat ≤
      ((M.write p.toNat len.toBytes).write (p + 32).toNat ys).size ∧
    memWord ((M.write p.toNat len.toBytes).write (p + 32).toNat ys) p.toNat = len ∧
    (nextWord p len).toNat = p.toNat + 32 + roundedBytes len.toNat ∧
    p.toNat + 32 + len.toNat ≤ (nextWord p len).toNat ∧
    p.toNat + 32 ≤ (nextWord p len).toNat ∧
    p.toNat + 32 + roundedBytes len.toNat < 2 ^ 160 + 31 ∧
    ∀ o, o + 32 ≤ p.toNat → o + 32 ≤ M.size →
      memWord ((M.write p.toNat len.toBytes).write (p + 32).toNat ys) o
        = memWord M o := by
  have h32 : (32 : B256).toNat = 32 := rfl
  have h31 : (31 : B256).toNat = 31 := rfl
  obtain ⟨hHead0, hH⟩ := Mem.memWord_write_word M p.toNat len
  have hmono : (M.write p.toNat len.toBytes).size ≤
      ((M.write p.toNat len.toBytes).write (p + 32).toNat ys).size :=
    (Mem.write_agree _ _ _).1
  have hle : p.toNat + 32 ≤
      ((M.write p.toNat len.toBytes).write (p + 32).toNat ys).size :=
    le_trans hH hmono
  have hbD : p.toNat + (32 : B256).toNat < 2 ^ 256 := by rw [h32]; omega
  have hD : (p + 32).toNat = p.toNat + 32 := (addNat hbD).trans (by rw [h32])
  rw [hD] at hPost hmono hle ⊢
  -- Copy window fits: nonempty copies via `write_base`, empty ones (so
  -- `len.toNat = 0`) via the header bound alone.
  have hfitAll : p.toNat + 32 + len.toNat ≤
      ((M.write p.toNat len.toBytes).write (p.toNat + 32) ys).size := by
    by_cases hne : ys = []
    · subst hne
      simp only [List.length_nil] at hlen
      omega
    · obtain ⟨_, _, _, _, hfit, _⟩ :=
        Mem.write_base (M.write p.toNat len.toBytes) (p.toNat + 32) hne
      omega
  have hlt : p.toNat + 32 + len.toNat < 2 ^ 160 :=
    lt_of_le_of_lt hfitAll hPost
  -- Inner word ops unwrap: everything sits below `2 ^ 160`.
  have hb31 : (31 : B256).toNat + len.toNat < 2 ^ 256 := by rw [h31]; omega
  have h31len : (31 + len).toNat = 31 + len.toNat := (addNat hb31).trans (by rw [h31])
  have hdiv : ((31 + len) / 32).toNat = (31 + len.toNat) / 32 := by
    rw [divNat (by decide), h31len, h32]
  have hle32 : 32 * ((31 + len.toNat) / 32) ≤ 31 + len.toNat := by
    have hdm := Nat.div_add_mod (31 + len.toNat) 32
    omega
  have hbm : (32 : B256).toNat * ((31 + len) / 32).toNat < 2 ^ 256 := by
    rw [h32, hdiv]; omega
  have hmul : (32 * ((31 + len) / 32)).toNat = 32 * ((31 + len.toNat) / 32) := by
    rw [mulNat hbm, h32, hdiv]
  have hround_le : roundedBytes len.toNat ≤ len.toNat + 31 := by
    simp only [roundedBytes]
    have hdm := Nat.div_add_mod (len.toNat + 31) 32
    omega
  have hround_ge : len.toNat ≤ roundedBytes len.toNat := by
    simp only [roundedBytes]
    have hdm := Nat.div_add_mod (len.toNat + 31) 32
    omega
  have hba : (32 : B256).toNat + (32 * ((31 + len) / 32)).toNat < 2 ^ 256 := by
    rw [h32, hmul]; omega
  have halloc : (allocWord len).toNat = 32 + roundedBytes len.toNat := by
    simp only [allocWord, roundedBytes]
    rw [addNat hba, h32, hmul, Nat.add_comm len.toNat 31,
      Nat.mul_comm ((31 + len.toNat) / 32) 32]
  have hbp : (allocWord len).toNat + p.toNat < 2 ^ 256 := by rw [halloc]; omega
  have hnext : (nextWord p len).toNat = p.toNat + 32 + roundedBytes len.toNat := by
    simp only [nextWord]
    rw [addNat hbp, halloc]
    omega
  have hle1 : p.toNat + 32 + len.toNat ≤ (nextWord p len).toNat := by
    rw [hnext]; omega
  have hle2 : p.toNat + 32 ≤ (nextWord p len).toNat := by rw [hnext]; omega
  have hround160 : p.toNat + 32 + roundedBytes len.toNat < 2 ^ 160 + 31 := by omega
  -- Header readback: the copy window starts at `p.toNat + 32`, disjoint
  -- from the header bytes.
  have hag2 := Mem.write_agree (M.write p.toNat len.toBytes) (p.toNat + 32) ys
  have hcongr : ∀ j, j < 32 →
      ((M.write p.toNat len.toBytes).write (p.toNat + 32) ys).data.getD (p.toNat + j) 0 =
      (M.write p.toNat len.toBytes).data.getD (p.toNat + j) 0 :=
    fun j hj => hag2.2 _ (by omega) (Or.inl (by omega))
  have hHead : memWord ((M.write p.toNat len.toBytes).write (p.toNat + 32) ys) p.toNat
      = len :=
    (memWord_congr hcongr).trans hHead0
  -- Prior words survive both writes: both windows sit at or above `p`.
  have hag1 := Mem.write_agree M p.toNat len.toBytes
  rw [B256.length_toBytes] at hag1
  have hPrior : ∀ o, o + 32 ≤ p.toNat → o + 32 ≤ M.size →
      memWord ((M.write p.toNat len.toBytes).write (p.toNat + 32) ys) o
        = memWord M o := by
    intro o ho1 ho2
    have c1 : ∀ j, j < 32 →
        (M.write p.toNat len.toBytes).data.getD (o + j) 0 = M.data.getD (o + j) 0 :=
      fun j hj => hag1.2 _ (by omega) (Or.inl (by omega))
    have c2 : ∀ j, j < 32 →
        ((M.write p.toNat len.toBytes).write (p.toNat + 32) ys).data.getD (o + j) 0 =
        (M.write p.toNat len.toBytes).data.getD (o + j) 0 :=
      fun j hj => hag2.2 _ (by omega) (Or.inl (by omega))
    exact (memWord_congr c2).trans (memWord_congr c1)
  exact ⟨rfl, hlt, hle, hfitAll, hHead, hnext, hle1, hle2, hround160, hPrior⟩

/-- Actual-execution corollary: a real `MSTORE` of `len` at `p` followed by
a real `CALLDATACOPY` of `len` bytes to `p + 32`, with the same memory at
the copy entry (a local producer seam the caller's pure-step tracking
discharges next) and `Pot` at the actual poststate (the existing `withPot`
seam). The two stack tails are independent (`rest1`, `rest2`); the proof
uses no relationship between them. Concludes the `allocation_facts` facts
about that same poststate. Nothing about the desired post memory, header,
or bound is assumed. -/
theorem allocation_of_run {sevm : Sevm} {pre1 mid pre2 post : Devm} {p len src : B256}
    {rest1 rest2 : List B256}
    (hs1 : pre1.stack = p :: len :: rest1)
    (hmem : mid.memory = pre2.memory)
    (run1 : Ninst.Run sevm pre1 (.reg .mstore) mid)
    (hs2 : pre2.stack = (p + 32) :: src :: len :: rest2)
    (run2 : Ninst.Run sevm pre2 (.reg .calldatacopy) post)
    (pot : FreePtr.Pot post) :
    (p + 32).toNat = p.toNat + 32 ∧
    p.toNat + 32 + len.toNat < 2 ^ 160 ∧
    p.toNat + 32 ≤ post.memory.size ∧
    p.toNat + 32 + len.toNat ≤ post.memory.size ∧
    memWord post.memory p.toNat = len ∧
    (nextWord p len).toNat = p.toNat + 32 + roundedBytes len.toNat ∧
    p.toNat + 32 + len.toNat ≤ (nextWord p len).toNat ∧
    p.toNat + 32 ≤ (nextWord p len).toNat ∧
    p.toNat + 32 + roundedBytes len.toNat < 2 ^ 160 + 31 ∧
    ∀ o, o + 32 ≤ p.toNat → o + 32 ≤ pre1.memory.size →
      memWord post.memory o = memWord pre1.memory o := by
  obtain ⟨ys, hlen, hcc⟩ := calldatacopy_run_memory run2 hs2
  have hms := mstore_run_memory run1 hs1
  have hMout : post.memory
      = (pre1.memory.write p.toNat len.toBytes).write (p + 32).toNat ys := by
    rw [hcc, ← hmem, hms]
  have hPost : ((pre1.memory.write p.toNat len.toBytes).write (p + 32).toNat ys).size
      < 2 ^ 160 := by
    rw [← hMout]
    exact FreePtr.Pot.size_lt pot
  rw [hMout]
  exact allocation_facts hlen hPost

/-- Generic `P`/`PotStep` version of `allocation_of_run` by erasure: the
`PotStep` witnesses carry `Pot` at every step, and `hP` erases them to the
real `Ninst.Run`s. -/
theorem allocation_of_runP {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {pre1 mid pre2 post : Devm} {p len src : B256}
    {rest1 rest2 : List B256}
    (hs1 : pre1.stack = p :: len :: rest1)
    (hmem : mid.memory = pre2.memory)
    (w1 : FreePtr.PotStep P sevm pre1 (.reg .mstore) mid)
    (hs2 : pre2.stack = (p + 32) :: src :: len :: rest2)
    (w2 : FreePtr.PotStep P sevm pre2 (.reg .calldatacopy) post) :
    (p + 32).toNat = p.toNat + 32 ∧
    p.toNat + 32 + len.toNat < 2 ^ 160 ∧
    p.toNat + 32 ≤ post.memory.size ∧
    p.toNat + 32 + len.toNat ≤ post.memory.size ∧
    memWord post.memory p.toNat = len ∧
    (nextWord p len).toNat = p.toNat + 32 + roundedBytes len.toNat ∧
    p.toNat + 32 + len.toNat ≤ (nextWord p len).toNat ∧
    p.toNat + 32 ≤ (nextWord p len).toNat ∧
    p.toNat + 32 + roundedBytes len.toNat < 2 ^ 160 + 31 ∧
    ∀ o, o + 32 ≤ p.toNat → o + 32 ≤ pre1.memory.size →
      memWord post.memory o = memWord pre1.memory o := by
  exact allocation_of_run hs1 hmem (hP w1.1) hs2 (hP w2.1) w2.2.2

/-- Free-pointer word preservation for callers staging several allocations:
when the pre-memory holds an `fp` update at `64` and `p` sits at or above
`96`, the header and payload writes keep `memWord · 64`. Via the
`allocation_facts` prior-word fact at `o = 64`; no `Mem.Wf`. Only one
allocation is covered here. -/
theorem allocation_fp64 {M M0 : Mem} {p len : B256} {ys : Bytes} {fp : B256}
    (hM : M = M0.write 64 fp.toBytes)
    (hp : 96 ≤ p.toNat)
    (hlen : ys.length = len.toNat)
    (hPost : ((M.write p.toNat len.toBytes).write (p + 32).toNat ys).size < 2 ^ 160) :
    memWord ((M.write p.toNat len.toBytes).write (p + 32).toNat ys) 64 = fp := by
  obtain ⟨hfp, h64⟩ := Mem.memWord_write_word M0 64 fp
  obtain ⟨_, _, _, _, _, _, _, _, _, hprior⟩ := allocation_facts hlen hPost
  have hfpM : memWord M 64 = fp := by rw [hM]; exact hfp
  have h := hprior 64 (by omega) (by rw [hM]; exact h64)
  exact h.trans hfpM

end Blanc.Lift.SolcStringAllocation
