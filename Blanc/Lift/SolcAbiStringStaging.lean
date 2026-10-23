import Blanc.Lift.SolcStringAllocation
import Blanc.Lift.MemMap
import Blanc.Lift.RunPWalk
import Blanc.Lift.InvWalkOps
import Blanc.MachineDataFacts

/-!
# Solidity ABI dynamic-string staging from calldata (contract-neutral)

Generic companion to `Blanc.Lift.SolcStringAllocation`, which proves the
single-allocation facts. This module has two layers.

**Memory layer.** `allocMem M p L ys` is the memory after one solc
string allocation as the code performs it: the free-pointer `MLOAD` at `64`
(memory expansion `(M.read 64 32).2`), the free-pointer `MSTORE` of
`nextWord p L` at `64`, the length-header `MSTORE` of `L` at `p`, and the
payload copy `ys` at `p + 32`. `stage1` gives the facts of one allocation and
`stage3` chains three of them into `Staged3`: headers read back in the final
memory, the final free pointer, exact `nextWord` equations, ordered
non-overlap bounds and prior-word transport from the original memory. The
only inputs are the initial-pointer bound `96 ≤ p1`, the payload lengths,
the free pointer each stage reads, and the final `2 ^ 160` post-size bound
(the existing `FreePtr.Pot` seam, available at every `PotStep`).

**Code layer.** `strFrag`, `rotFrag` and `staticFrag` are the exact solc ABI
calldata-decoder fragments (dynamic `string` head/length decode plus
allocation; the cursor rotation after it; one masked static head), and
`strFrag_runP`, `rotFrag_runP`, `staticFrag_runP` invert a `PotStep` run
through each of them over an *abstract* stack tail, memory and continuation.
A wrapper with several decodes therefore never unfolds one long walk with
nested memory writes: it composes these lemmas. Arithmetic is the `B256`
word arithmetic of the code; no calldata validation, gas, profile, endpoint
or hash premise is introduced. No `Mem.Wf` premise anywhere.
-/

namespace Blanc.Lift.SolcAbiStringStaging

open Jaune Blanc Blanc.Lift
open SolcStringAllocation

/-! ## Memory layer -/

/-- Memory after one solc dynamic-string allocation at free pointer `p` with
length `L` and payload `ys`, in code order: free-pointer read expansion,
free-pointer update, length header, payload copy. -/
def allocMem (M : Mem) (p L : B256) (ys : Bytes) : Mem :=
  ((((M.read 64 32).2).write 64 (nextWord p L).toBytes).write p.toNat L.toBytes).write
    (p + 32).toNat ys

/-- The free-pointer read expansion keeps every recorded byte. -/
private theorem memWord_read64 (M : Mem) (o : Nat) :
    memWord (M.read 64 32).2 o = memWord M o := rfl

/-- A word at or above `96` survives a free-pointer write at `64`. -/
private theorem memWord_write64_disjoint {M : Mem} {o : Nat} {v : B256}
    (hdis : 96 ≤ o) (hsz : o + 32 ≤ M.size) :
    memWord (M.write 64 v.toBytes) o = memWord M o := by
  have hlen : v.toBytes.length = 32 := B256.length_toBytes v
  apply memWord_congr
  intro j hj
  exact (Mem.write_agree M 64 v.toBytes).2 _ (by omega) (Or.inr (by omega))

/-- One allocation's facts, about its post memory. -/
theorem stage1 {M : Mem} {p L : B256} {ys : Bytes}
    (hp96 : 96 ≤ p.toNat) (hlen : ys.length = L.toNat)
    (hpost : (allocMem M p L ys).size < 2 ^ 160) :
    memWord (allocMem M p L ys) p.toNat = L ∧
    memWord (allocMem M p L ys) 64 = nextWord p L ∧
    (nextWord p L).toNat = p.toNat + 32 + roundedBytes L.toNat ∧
    p.toNat + 32 + L.toNat ≤ (allocMem M p L ys).size ∧
    p.toNat + 32 + L.toNat ≤ (nextWord p L).toNat ∧
    p.toNat + 32 ≤ (nextWord p L).toNat ∧
    M.size ≤ (allocMem M p L ys).size ∧
    ∀ o, 96 ≤ o → o + 32 ≤ p.toNat → o + 32 ≤ M.size →
      memWord (allocMem M p L ys) o = memWord M o := by
  obtain ⟨_hD, _hlt, _hle, hfit, hhdr, hnext, hle1, hle2, _hcap, hprior⟩ :=
    allocation_facts (M := ((M.read 64 32).2).write 64 (nextWord p L).toBytes)
      (p := p) (len := L) hlen hpost
  have hr : M.size ≤ (M.read 64 32).2.size := memExtSize_ge M.size 64 32
  have hw : (M.read 64 32).2.size ≤
      ((M.read 64 32).2.write 64 (nextWord p L).toBytes).size :=
    (Mem.write_agree _ _ _).1
  have h96 : 96 ≤ ((M.read 64 32).2.write 64 (nextWord p L).toBytes).size :=
    (Mem.memWord_write_word _ 64 (nextWord p L)).2
  have hm : ((M.read 64 32).2.write 64 (nextWord p L).toBytes).size ≤
      (allocMem M p L ys).size :=
    le_trans (Mem.write_agree _ _ _).1 (Mem.write_agree _ _ _).1
  refine ⟨hhdr, ?_, hnext, hfit, hle1, hle2, le_trans hr (le_trans hw hm), ?_⟩
  · exact (hprior 64 (by omega) h96).trans
      (Mem.memWord_write_word _ 64 (nextWord p L)).1
  · intro o ho96 ho hoM
    have h1 := hprior o ho (le_trans hoM (le_trans hr hw))
    exact h1.trans ((memWord_write64_disjoint ho96 (le_trans hoM hr)).trans
      (memWord_read64 M o))

/-- Staged facts for three chained allocations, all about the final memory
`M3`: length headers, final free pointer, the pointer chain, exact
next-pointer values with bounds, ordered non-overlap, and survival of every
word of the original memory at or above `96` and below `p1`. -/
structure Staged3 (M0 M3 : Mem) (p1 p2 p3 p4 L1 L2 L3 : B256) : Prop where
  hdr1 : memWord M3 p1.toNat = L1
  hdr2 : memWord M3 p2.toNat = L2
  hdr3 : memWord M3 p3.toNat = L3
  fp64 : memWord M3 64 = p4
  eq2 : p2 = nextWord p1 L1
  eq3 : p3 = nextWord p2 L2
  eq4 : p4 = nextWord p3 L3
  next1 : p2.toNat = p1.toNat + 32 + roundedBytes L1.toNat
  next2 : p3.toNat = p2.toNat + 32 + roundedBytes L2.toNat
  next3 : p4.toNat = p3.toNat + 32 + roundedBytes L3.toNat
  fit1 : p1.toNat + 32 + L1.toNat ≤ M3.size
  fit2 : p2.toNat + 32 + L2.toNat ≤ M3.size
  fit3 : p3.toNat + 32 + L3.toNat ≤ M3.size
  ord12 : p1.toNat + 32 + L1.toNat ≤ p2.toNat
  ord23 : p2.toNat + 32 + L2.toNat ≤ p3.toNat
  ord34 : p3.toNat + 32 + L3.toNat ≤ p4.toNat
  below4 : p4.toNat < 2 ^ 160 + 31
  prior : ∀ o, 96 ≤ o → o + 32 ≤ p1.toNat → o + 32 ≤ M0.size →
    memWord M3 o = memWord M0 o

/-- Three chained allocations. Each stage allocates at the free pointer it
read (`memWord M(i-1) 64`); only the first pointer's bound `96 ≤ p1` and the
final post-size bound are inputs. -/
theorem stage3 {M0 : Mem} {p1 p2 p3 L1 L2 L3 : B256} {y1 y2 y3 : Bytes}
    (hp96 : 96 ≤ p1.toNat)
    (hlen1 : y1.length = L1.toNat) (hlen2 : y2.length = L2.toNat)
    (hlen3 : y3.length = L3.toNat)
    (hW2 : memWord (allocMem M0 p1 L1 y1) 64 = p2)
    (hW3 : memWord (allocMem (allocMem M0 p1 L1 y1) p2 L2 y2) 64 = p3)
    (hpost : (allocMem (allocMem (allocMem M0 p1 L1 y1) p2 L2 y2) p3 L3 y3).size
      < 2 ^ 160) :
    Staged3 M0 (allocMem (allocMem (allocMem M0 p1 L1 y1) p2 L2 y2) p3 L3 y3)
      p1 p2 p3 (nextWord p3 L3) L1 L2 L3 := by
  generalize hM1 : allocMem M0 p1 L1 y1 = M1 at hW2 hW3 hpost
  generalize hM2 : allocMem M1 p2 L2 y2 = M2 at hW3 hpost
  generalize hM3 : allocMem M2 p3 L3 y3 = M3 at hpost
  -- Sizes grow, so the final bound reaches every stage.
  have mono : ∀ (M : Mem) (p L : B256) (ys : Bytes), M.size ≤ (allocMem M p L ys).size :=
    fun M p L ys => le_trans (memExtSize_ge M.size 64 32)
      (le_trans (Mem.write_agree (M.read 64 32).2 64 (nextWord p L).toBytes).1
      (le_trans (Mem.write_agree _ _ _).1 (Mem.write_agree _ _ _).1))
  have m23 : M2.size ≤ M3.size := hM3 ▸ mono _ _ _ _
  have m12 : M1.size ≤ M2.size := hM2 ▸ mono _ _ _ _
  have hpost2 : M2.size < 2 ^ 160 := lt_of_le_of_lt m23 hpost
  have hpost1 : M1.size < 2 ^ 160 := lt_of_le_of_lt m12 hpost2
  subst hM1
  obtain ⟨h1hdr, h1fp, h1next, h1fit, h1le, h1le2, _h1mono, h1prior⟩ :=
    stage1 hp96 hlen1 hpost1
  have e2 : p2 = nextWord p1 L1 := hW2.symm.trans h1fp
  have hp2 : 96 ≤ p2.toNat := by rw [e2]; omega
  subst hM2
  obtain ⟨h2hdr, h2fp, h2next, h2fit, h2le, h2le2, _h2mono, h2prior⟩ :=
    stage1 hp2 hlen2 hpost2
  have e3 : p3 = nextWord p2 L2 := hW3.symm.trans h2fp
  have hp3 : 96 ≤ p3.toNat := by rw [e3]; omega
  subst hM3
  obtain ⟨h3hdr, h3fp, h3next, h3fit, h3le, h3le2, _h3mono, h3prior⟩ :=
    stage1 hp3 hlen3 hpost
  have n1 : p2.toNat = p1.toNat + 32 + roundedBytes L1.toNat := by rw [e2]; exact h1next
  have n2 : p3.toNat = p2.toNat + 32 + roundedBytes L2.toNat := by rw [e3]; exact h2next
  have o12 : p1.toNat + 32 + L1.toNat ≤ p2.toNat := by rw [e2]; exact h1le
  have o23 : p2.toNat + 32 + L2.toNat ≤ p3.toNat := by rw [e3]; exact h2le
  have b12 : p1.toNat + 32 ≤ p2.toNat := by rw [e2]; exact h1le2
  have b23 : p2.toNat + 32 ≤ p3.toNat := by rw [e3]; exact h2le2
  have hbelow : (nextWord p3 L3).toNat < 2 ^ 160 + 31 := by
    have := h3fit
    have hr : roundedBytes L3.toNat ≤ L3.toNat + 31 := by
      simp only [roundedBytes]
      have hdm := Nat.div_add_mod (L3.toNat + 31) 32
      omega
    omega
  -- Earlier headers survive the later stages.
  have k1 : memWord (allocMem (allocMem M0 p1 L1 y1) p2 L2 y2) p1.toNat = L1 :=
    (h2prior _ hp96 b12 (by have := h1fit; omega)).trans h1hdr
  have m1 := mono (allocMem M0 p1 L1 y1) p2 L2 y2
  refine
    { hdr1 := (h3prior _ hp96 (by omega) (by have := h1fit; have := m1; omega)).trans k1
      hdr2 := (h3prior _ hp2 b23 (by have := h2fit; omega)).trans h2hdr
      hdr3 := h3hdr
      fp64 := h3fp
      eq2 := e2
      eq3 := e3
      eq4 := rfl
      next1 := n1
      next2 := n2
      next3 := h3next
      fit1 := le_trans h1fit (le_trans m1 m23)
      fit2 := le_trans h2fit m23
      fit3 := h3fit
      ord12 := o12
      ord23 := o23
      ord34 := h3le
      below4 := hbelow
      prior := ?_ }
  intro o ho96 ho hoM
  have s1 := h1prior o ho96 ho hoM
  have s2 := h2prior o ho96 (by omega) (by have := h1fit; omega)
  have s3 := h3prior o ho96 (by omega) (by have := h2fit; omega)
  exact s3.trans (s2.trans s1)

/-! ## Code layer: solc ABI calldata decoder fragments -/

/-- Dynamic `string` decode and allocation, from the head cursor `h` over the
decoder base `base` (stack `h :: base :: E :: T`): read the head word `W`, the
length `L` at `base + W`, allocate at the free pointer, store the header and
copy the payload; ends with the source pointer, the allocated pointer and
the advanced cursor `32 + h` on top. -/
def strFrag (k : SFunc) : SFunc :=
  .next (.reg (.dup 0)) <| .next (.reg .calldataload) <| .next (.reg (.swap 0)) <|
  .next (.push [0x20] (by decide)) <| .next (.reg .add) <| .next (.reg (.swap 0)) <|
  .next (.reg (.dup 2)) <| .next (.reg .add) <| .next (.reg (.dup 0)) <|
  .next (.reg .calldataload) <| .next (.reg (.swap 0)) <|
  .next (.push [0x20] (by decide)) <| .next (.reg .add) <| .next (.reg (.swap 0)) <|
  .next (.reg (.dup 0)) <| .next (.reg (.dup 0)) <| .next (.push [0x1f] (by decide)) <|
  .next (.reg .add) <| .next (.push [0x20] (by decide)) <| .next (.reg (.dup 0)) <|
  .next (.reg (.swap 1)) <| .next (.reg .div) <| .next (.reg .mul) <|
  .next (.push [0x20] (by decide)) <| .next (.reg .add) <|
  .next (.push [0x40] (by decide)) <| .next (.reg .mload) <| .next (.reg (.swap 0)) <|
  .next (.reg (.dup 1)) <| .next (.reg .add) <| .next (.push [0x40] (by decide)) <|
  .next (.reg .mstore) <| .next (.reg (.dup 0)) <| .next (.reg (.swap 3)) <|
  .next (.reg (.swap 2)) <| .next (.reg (.swap 1)) <| .next (.reg (.swap 0)) <|
  .next (.reg (.dup 1)) <| .next (.reg (.dup 1)) <| .next (.reg .mstore) <|
  .next (.push [0x20] (by decide)) <| .next (.reg .add) <| .next (.reg (.dup 3)) <|
  .next (.reg (.dup 3)) <| .next (.reg (.dup 0)) <| .next (.reg (.dup 2)) <|
  .next (.reg (.dup 4)) <| .next (.reg .calldatacopy) <| .next (.reg (.dup 2)) <|
  .next (.reg .add) <| .next (.reg (.swap 1)) <| .next (.reg .pop) <|
  .next (.reg .pop) <| .next (.reg .pop) <| .next (.reg .pop) <| .next (.reg .pop) k

/-- Cursor rotation after a decoded value `v`: drop the source pointer and
move `v` under the decoder triple. -/
def rotFrag (k : SFunc) : SFunc :=
  .next (.reg .pop) <| .next (.reg (.swap 1)) <| .next (.reg (.swap 2)) <|
  .next (.reg (.swap 1)) <| .next (.reg (.swap 2)) <| .next (.reg (.swap 0)) k

/-- One static head decode masked by the pushed constant, then the same
rotation shape as `rotFrag` without the drop. -/
def staticFrag (xs : Bytes) (le : xs.length ≤ 32) (k : SFunc) : SFunc :=
  .next (.reg (.dup 0)) <| .next (.reg .calldataload) <| .next (.push xs le) <|
  .next (.reg .and) <| .next (.reg (.swap 0)) <| .next (.push [0x20] (by decide)) <|
  .next (.reg .add) <| .next (.reg (.swap 0)) <| .next (.reg (.swap 2)) <|
  .next (.reg (.swap 1)) <| .next (.reg (.swap 0)) k

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {b : Devm}
  {T : List B256} {M : Mem} {G : Nat} {k : SFunc} {out : Outcome}

private theorem lit20 : Bytes.toB256 [0x20] = (32 : B256) := by decide
private theorem lit1f : Bytes.toB256 [0x1f] = (31 : B256) := by decide
private theorem lit40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide

/-- Length of a zero-padded calldata window. -/
theorem sliceD_length (xs : Bytes) (m n : Nat) : (xs.sliceD m n 0).length = n :=
  List.takeD_length _ _ _

/-- The fragment's memory, in the code's literal and operand order, is
`allocMem` at the free pointer it read. -/
private theorem code_mem (M : Mem) (L : B256) (ys : Bytes) :
    ((((M.read (Bytes.toB256 [0x40]).toNat 32).2.write (Bytes.toB256 [0x40]).toNat
      ((M.read (Bytes.toB256 [0x40]).toNat 32).1.toB256 +
        (Bytes.toB256 [0x20] + (Bytes.toB256 [0x1f] + L) / Bytes.toB256 [0x20] *
          Bytes.toB256 [0x20])).toBytes).write
      (M.read (Bytes.toB256 [0x40]).toNat 32).1.toB256.toNat L.toBytes).write
      (Bytes.toB256 [0x20] + (M.read (Bytes.toB256 [0x40]).toNat 32).1.toB256).toNat ys) =
    allocMem M (memWord M 64) L ys := by
  rw [lit40, lit20, lit1f]
  have e1 : (M.read 64 32).1.toB256 + (32 + (31 + L) / 32 * 32) =
      nextWord (memWord M 64) L := by
    unfold nextWord allocWord memWord
    rw [B256.mul_comm _ 32]
    exact B256.add_comm
  have e2 : (32 : B256) + (M.read 64 32).1.toB256 = memWord M 64 + 32 := B256.add_comm
  rw [e1, e2]
  rfl

/-- The dynamic-string fragment, inverted over an abstract tail, memory and
continuation. The allocation happens at the free pointer read at `64`; the
post memory is `allocMem`; its size bound is the actual post-`Pot` of the
payload copy. -/
theorem strFrag_runP (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {h base E : B256}
    (run : SFunc.RunP (FreePtr.PotStep P) fs sevm (St b (h :: base :: E :: T) M G)
      (strFrag k) out) :
    ∃ G' : Nat,
      (allocMem M (memWord M 64) (Sevm.dataWord sevm (base + Sevm.dataWord sevm h))
        (sevm.data.sliceD (32 + (base + Sevm.dataWord sevm h)).toNat
          (Sevm.dataWord sevm (base + Sevm.dataWord sevm h)).toNat 0)).size < 2 ^ 160 ∧
      SFunc.RunP (FreePtr.PotStep P) fs sevm
        (St b ((32 + (base + Sevm.dataWord sevm h)) :: memWord M 64 :: (32 + h) :: base ::
          E :: T)
          (allocMem M (memWord M 64) (Sevm.dataWord sevm (base + Sevm.dataWord sevm h))
            (sevm.data.sliceD (32 + (base + Sevm.dataWord sevm h)).toNat
              (Sevm.dataWord sevm (base + Sevm.dataWord sevm h)).toNat 0)) G')
        k out := by
  unfold strFrag at run
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_calldataload (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_calldataload (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_div (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_mul (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_mload (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_mstore (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_mstore (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, wc, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_calldatacopy (erase wc.1)
  have hpot := FreePtr.Pot.size_lt wc.2.2
  clear wc
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  rw [code_mem] at run hpot
  rw [lit20] at run hpot
  exact ⟨_, hpot, run⟩

/-- The cursor rotation, inverted: the dropped source pointer is gone and
the decoded value `v` sits under the decoder triple. -/
theorem rotFrag_runP (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {x v h base E : B256}
    (run : SFunc.RunP (FreePtr.PotStep P) fs sevm (St b (x :: v :: h :: base :: E :: T) M G)
      (rotFrag k) out) :
    ∃ G' : Nat, SFunc.RunP (FreePtr.PotStep P) fs sevm
      (St b (h :: base :: E :: v :: T) M G') k out := by
  unfold rotFrag at run
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_pop (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  exact ⟨_, run⟩

/-- One masked static head decode, inverted: the masked word
`m &&& dataWord h` (with `m` the pushed constant) sits under the decoder
triple and the cursor advances by `32`. -/
theorem staticFrag_runP (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {xs : Bytes} {le : xs.length ≤ 32} {h base E : B256}
    (run : SFunc.RunP (FreePtr.PotStep P) fs sevm (St b (h :: base :: E :: T) M G)
      (staticFrag xs le k) out) :
    ∃ G' : Nat, SFunc.RunP (FreePtr.PotStep P) fs sevm
      (St b ((32 + h) :: base :: E :: (xs.toB256 &&& Sevm.dataWord sevm h) :: T) M G') k out := by
  unfold staticFrag at run
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_dup rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_calldataload (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_and (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_push (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_add (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  obtain ⟨d, w, run⟩ := rpw_next run
  obtain ⟨G, rfl⟩ := ri_swap rfl (erase w.1)
  clear w
  rw [lit20] at run
  exact ⟨_, run⟩

end Blanc.Lift.SolcAbiStringStaging
