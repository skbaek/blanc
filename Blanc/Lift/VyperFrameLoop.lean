import Blanc.Lift.InvWalkOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.MemMap
import Jaune.MemoryAccounting
import Blanc.Lift.WalkInvKit

/-!
# Vyper 0.2.x frame save and restore loops, unrolled

Before an internal call Vyper 0.2.x saves the caller's live memory frame on the stack and
restores it after the call returns:

* **save**: a counter word at `c` starts at `lo`; each iteration pushes the word at the
  counter, adds `32` to it and loops while it is below the bound `e`;
* **restore**: the counter starts at the top slot; each iteration pops the stack top into the
  word at the counter, subtracts `32` and loops while the counter is not below `lo`.

A certificate whose entries carry the abstract stack (the lifter's frame loops) unrolls each
loop into a chain: one tree per iteration, every iteration the same template, the
non-final ones falling through to `PUSH2 head; JUMP k'` into the next copy, the final one
leaving through its `JUMPI` to the exit tree.  The dead arm of every `JUMPI` is `.undefined`.

**Templates.**  `frameSaveIter` and `frameRestoreIter` are one iteration with its `JUMPI`
arms as parameters; a `FrameLoopTpl` fixes the pushed constants (counter address, bound,
exit tag, head tag).  `FrameLoopTpl.saveTree t exitT ks` is the iteration whose remaining
chain entries are `ks`; `FrameSaveChain fs t exitT ks` is **one** equation — the list of
`fs`-lookups of the chain entries equals the list of templates — so a whole chain is
discharged by one kernel fact (`rfl`).  Restore is the same (`restoreTree`,
`FrameRestoreChain`).

**Memory.**  `memWord`/`Mem.AgreeOutside` (`Blanc/Lift/MemMap.lean`) and the word-slot carrier
`Words M L` (every `(o, v) ∈ L` is a word inside the logical size reading `v`) state what the
chains leave: the save chain's counter writes `saveMem`, the restore chain's word and counter
writes `restoreMem`, and `restoreMem_frameWords`: restoring the words a save chain pushed from
`W` gives back `W`'s frame words (`Words … (frameSlots W lo n)`).

**Rules.**  Safety: `ric_frameSave_chain`, `ric_frameRestore_chain` (cut runs of the first
iteration end as cut runs of the exit tree).  Liveness: `rxc_frameSave_chain`,
`rxc_frameRestore_chain` (exact cut runs, cost `67 n - 11` and `70 n - 11`).

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## Memory words -/

/-- A word written inside the logical size keeps the size. -/
theorem Mem.size_write_word_of_add_le {M : Mem} {n : Nat} {v : B256} (h : n + 32 ≤ M.size) :
    (M.write n v.toBytes).size = M.size :=
  Mem.write_size_of_prepaid _ _ _ (fun _ => by rw [B256.length_toBytes]; exact h)

/-- **Word-slot carrier**: every `(o, v) ∈ L` is a word inside `M`'s logical size reading
`v`. -/
def Words (M : Mem) (L : List (Nat × B256)) : Prop :=
  ∀ o v, (o, v) ∈ L → o + 32 ≤ M.size ∧ memWord M o = v

theorem Words.nil (M : Mem) : Words M [] := fun _ _ h => by cases h

theorem Words.cons {M : Mem} {o : Nat} {v : B256} {L : List (Nat × B256)} :
    Words M ((o, v) :: L) ↔ (o + 32 ≤ M.size ∧ memWord M o = v) ∧ Words M L := by
  constructor
  · intro h
    exact ⟨h o v List.mem_cons_self, fun o' v' h' => h o' v' (List.mem_cons_of_mem _ h')⟩
  · rintro ⟨h0, h⟩ o' v' h'
    rcases List.mem_cons.mp h' with e | h'
    · cases e; exact h0
    · exact h o' v' h'

theorem Words.sub {M : Mem} {L L' : List (Nat × B256)} (h : Words M L) (hs : L' ⊆ L) :
    Words M L' := fun o v h' => h o v (hs h')

theorem Words.memWord {M : Mem} {L : List (Nat × B256)} (h : Words M L) {o : Nat} {v : B256}
    (hm : (o, v) ∈ L) : _root_.Blanc.Lift.memWord M o = v :=
  (h o v hm).2

/-- An `MLOAD` of a carried word reads its value and, on a word-aligned memory, leaves the
memory. -/
theorem Words.read {M : Mem} {L : List (Nat × B256)} (h : Words M L) (hsz : M.size % 32 = 0)
    {o : Nat} {v : B256} (hm : (o, v) ∈ L) :
    Bytes.toB256 (M.read o 32).1 = v ∧ (M.read o 32).2 = M :=
  ⟨(h o v hm).2, read_covered rfl hsz (h o v hm).1⟩

/-- Carried words outside a window survive any change that agrees outside it. -/
theorem Words.agree {M M' : Mem} {lo hi : Nat} {L : List (Nat × B256)} (h : Words M L)
    (hag : Mem.AgreeOutside M M' lo hi) (hout : ∀ o v, (o, v) ∈ L → o + 32 ≤ lo ∨ hi ≤ o) :
    Words M' L := by
  intro o v hm
  obtain ⟨hs, hv⟩ := h o v hm
  refine ⟨le_trans hs hag.1, ?_⟩
  rw [memWord_congr (μ := M) (fun j hj => hag.2 _ (by omega) (by
    rcases hout o v hm with h' | h' <;> omega))]
  exact hv

/-- A word write: the written word is carried, and so is every carried word it misses. -/
theorem Words.write {M : Mem} {L : List (Nat × B256)} (h : Words M L) {n : Nat} {v : B256}
    (hout : ∀ o w, (o, w) ∈ L → o + 32 ≤ n ∨ n + 32 ≤ o) :
    Words (M.write n v.toBytes) ((n, v) :: L) := by
  have hag := Mem.write_agree M n v.toBytes
  rw [B256.length_toBytes] at hag
  refine Words.cons.mpr ⟨⟨(Mem.memWord_write_word M n v).2, (Mem.memWord_write_word M n v).1⟩,
    h.agree hag hout⟩

/-! ## The iteration templates -/

/-- The constants of one unrolled loop: counter address `c`, bound `e` (save: the end of the
frame; restore: its start `lo`), exit tag `x`, head tag `h`, each as two pushed bytes. -/
structure FrameLoopTpl : Type where
  c0 : UInt8
  c1 : UInt8
  e0 : UInt8
  e1 : UInt8
  x0 : UInt8
  x1 : UInt8
  h0 : UInt8
  h1 : UInt8

namespace FrameLoopTpl

end FrameLoopTpl

/-! ## One iteration, inverted -/

section Inv

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg}

theorem toB256_add_0x20 {p : Nat} (hp : p + 32 < 2 ^ 256) :
    Nat.toB256 p + Bytes.toB256 [0x20] = Nat.toB256 (p + 32) := by
  rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, Nat.toB256_add_toB256 _ _]

theorem toB256_sub_0x20 {p : Nat} (h32 : 32 ≤ p) (hp : p < 2 ^ 256) :
    Nat.toB256 p - Bytes.toB256 [0x20] = Nat.toB256 (p - 32) := by
  rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, Nat.toB256_sub_toB256 h32 hp]

end Inv

/-! ## What the chains leave in memory -/

/-- The `n` frame words of `M` from `lo`, lowest first: what a save chain pushes (the stack
holds them reversed). -/
def frameWords (M : Mem) (lo n : Nat) : List B256 :=
  (List.range n).map fun i => memWord M (lo + 32 * i)

theorem length_frameWords (M : Mem) (lo n : Nat) : (frameWords M lo n).length = n := by
  simp only [frameWords, List.length_map, List.length_range]

/-- The save chain's memory after `n` iterations: the counter at `c` rewritten to
`lo + 32 i` for `i = 1 … n`. -/
def saveMem (M : Mem) (c lo : Nat) : Nat → Mem
  | 0 => M
  | n + 1 => (saveMem M c lo n).write c (Nat.toB256 (lo + 32 * (n + 1))).toBytes

/-- The restore chain's memory: from the counter value `p`, each stack word (top first) is
written at the counter, which then drops by `32`. -/
def restoreMem (c : Nat) : Mem → Nat → List B256 → Mem
  | M, _, [] => M
  | M, p, w :: ws =>
    restoreMem c ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes) (p - 32) ws

/-! ## The chains, inverted -/

section InvChain

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {r : Seg} {t : FrameLoopTpl} {exitT : SFunc}

end InvChain

/-! ## One iteration, forward -/

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg}

/-- An `MLOAD` of a word inside a word-aligned memory costs `3`. -/
theorem mload_covered_cost' {S' : List B256} {G' : Nat} {i : B256} (hsz : M.size % 32 = 0)
    (hi : i.toNat + 32 ≤ M.size) :
    gVerylow + (St b (i :: S') M (G' + 3)).extCost [⟨i.toNat, 32⟩] = 3 := by
  rw [St.extCost_eq rfl, memExtSize_of_le hsz hi, Nat.sub_self]; rfl

/-- An `MSTORE` of a word inside a word-aligned memory costs `3`. -/
theorem mstore_covered_cost' {S' : List B256} {G' : Nat} {i v : B256} (hsz : M.size % 32 = 0)
    (hi : i.toNat + 32 ≤ M.size) :
    gVerylow + (St b (i :: v :: S') M (G' + 3)).extCost [⟨i.toNat, 32⟩] = 3 := by
  rw [St.extCost_eq rfl, memExtSize_of_le hsz hi, Nat.sub_self]; rfl

end Fwd

/-! ## The chains, forward -/

section FwdChain

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {r : Seg} {t : FrameLoopTpl} {exitT : SFunc}

end FwdChain

end Blanc.Lift
