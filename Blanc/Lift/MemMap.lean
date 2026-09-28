import Blanc.Lift.CheckMem
import Blanc.LadderSem
import Blanc.ExecutionFrames

/-!
# A constant memory map for lifted frames (piece D, foundations)

A `MemMap` records abstract words at fixed memory offsets: `(o, v)` says the
32-byte word at offset `o` is described by `v` (a constant, or the current
function's return address `ρ` for `.ret`).  `MemMatches ρ mem μ` is the
invariant a memory-tracking lift keeps beside `FrameMatches`: every recorded
word lies inside the memory's logical size and reads as its abstract value.

Nothing here assumes `Mem.Wf` (backing array no longer than the logical
size).  The invariant keeps every recorded word below the logical size, and
`Mem.write` preserves every byte below the old logical size outside the written
window in all three of its branches (`Mem.write_agree`), so the map survives
disjoint writes on any memory, well-formed or not.

The transfer (`absMem`, `memTop`, in `Blanc/Lift/CheckMem.lean`) is sound
instruction by instruction (`absMem_sound`, `memTop_sound`).  `AVal.Matches`
and `FrameMatches`, the frame invariant of `Blanc/Lift/Sound.lean`, live here so
that the memory invariant can be stated beside them.
-/

namespace Blanc.Lift

open Jaune

/-- One abstract word describes one concrete word, reading `.ret` as `ρ`. -/
def AVal.Matches (ρ : B256) : AVal → B256 → Prop
  | .const c, w => w = c
  | .ret, w => w = ρ
  | .unk, _ => True

def FrameMatches (ρ : B256) (a : List AVal) (s : List B256) : Prop :=
  List.Forall₂ (AVal.Matches ρ) a s

/-- The word memory holds at offset `o`, as `MLOAD` reads it. -/
def memWord (μ : Mem) (o : Nat) : B256 := Bytes.toB256 (μ.read o 32).1

/-- Every recorded word lies below the logical size and reads as recorded. -/
def MemMatches (ρ : B256) (mem : MemMap) (μ : Mem) : Prop :=
  ∀ o v, (o, v) ∈ mem → o + 32 ≤ μ.size ∧ AVal.Matches ρ v (memWord μ o)

/-- `μ'` is at least as large as `μ` and agrees with it below `μ`'s size outside
`[lo, hi)`. -/
def Mem.AgreeOutside (μ μ' : Mem) (lo hi : Nat) : Prop :=
  μ.size ≤ μ'.size ∧
    ∀ i, i < μ.size → (i < lo ∨ hi ≤ i) → μ'.data.getD i 0 = μ.data.getD i 0

theorem memMatches_nil (ρ : B256) (μ : Mem) : MemMatches ρ [] μ := by
  intro o v h; cases h

theorem memKill_zero (mem : MemMap) (lo : Nat) : memKill mem lo 0 = mem := by
  simp [memKill]

theorem memWord_congr {μ μ' : Mem} {o : Nat}
    (h : ∀ j, j < 32 → μ'.data.getD (o + j) 0 = μ.data.getD (o + j) 0) :
    memWord μ' o = memWord μ o := by
  unfold memWord Mem.read
  simp only [Array.sliceD_eq_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.mp hj)

theorem MemMatches.agree {ρ : B256} {mem : MemMap} {μ μ' : Mem} {lo hi : Nat}
    (hag : Mem.AgreeOutside μ μ' lo hi) (hm : MemMatches ρ mem μ) :
    MemMatches ρ (memKill mem lo hi) μ' := by
  intro o v hov
  simp only [memKill, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq] at hov
  obtain ⟨hmem, hout⟩ := hov
  obtain ⟨hsz, hv⟩ := hm o v hmem
  refine ⟨le_trans hsz hag.1, ?_⟩
  rw [memWord_congr (μ := μ) (fun j hj => hag.2 _ (by omega) (by omega))]
  exact hv

theorem Mem.AgreeOutside.refl (μ : Mem) (lo hi : Nat) : Mem.AgreeOutside μ μ lo hi :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

/-- A memory whose bytes are unchanged and whose size did not shrink keeps
every recorded word. -/
theorem MemMatches.of_data_eq {ρ : B256} {mem : MemMap} {μ μ' : Mem}
    (hdata : μ'.data = μ.data) (hsize : μ.size ≤ μ'.size) (hm : MemMatches ρ mem μ) :
    MemMatches ρ mem μ' := by
  have h := MemMatches.agree (lo := 0) (hi := 0) ⟨hsize, fun i _ _ => by rw [hdata]⟩ hm
  rwa [memKill_zero] at h

theorem memExtSize_ge (s i n : Nat) : s ≤ memExtSize s i n := by
  unfold memExtSize
  split
  · exact Nat.le_refl _
  · exact le_trans (Nat.le_mul_ceilDiv s 32 (by omega))
      (Nat.mul_le_mul_left _ (Nat.le_max_left _ _))

theorem memExtsSize_ge : ∀ (s : Nat) (ps : List (Nat × Nat)), s ≤ memExtsSize s ps
  | _, [] => Nat.le_refl _
  | s, ⟨i, n⟩ :: ps => le_trans (memExtSize_ge s i n) (memExtsSize_ge _ ps)

/-- `Mem.write`'s backing array, before the payload is laid over it: it holds
the payload's window and agrees with the old bytes below the old logical size.
Unlike `Mem.write_aux` this needs no `Mem.Wf`. -/
theorem Mem.write_base (μ : Mem) (n : Nat) {ys : Bytes} (hne : ys ≠ []) :
    ∃ A : Array UInt8,
      (μ.write n ys).data = Array.writeD A n ys ∧
      n + ys.length ≤ A.size ∧
      μ.size ≤ (μ.write n ys).size ∧
      n + ys.length ≤ (μ.write n ys).size ∧
      ∀ i, i < μ.size → A.getD i 0 = μ.data.getD i 0 := by
  cases ys with
  | nil => exact absurd rfl hne
  | cons y ys =>
    simp only [Mem.write]
    by_cases h1 : n + (y :: ys).length ≤ μ.size
    · rw [if_pos h1]
      by_cases h2 : n + (y :: ys).length ≤ μ.data.size
      · rw [if_pos h2]
        exact ⟨μ.data, rfl, h2, Nat.le_refl _, h1, fun _ _ => rfl⟩
      · rw [if_neg h2]
        refine ⟨Array.copyD μ.data
          (Array.replicate (n + (y :: ys).length) 0x00), rfl, ?_, Nat.le_refl _, h1, ?_⟩
        · rw [Array.size_copyD, Array.size_replicate]
        · intro i _
          rw [Array.getD_copyD _ _ _ (by rw [Array.size_replicate]; omega)]
          by_cases hi : i < μ.data.size
          · rw [if_pos hi]
          · rw [if_neg hi, Array.getD_replicate_zero,
              Array.getD_of_size_le 0 (Nat.not_lt.mp hi)]
    · rw [if_neg h1]
      have hle : n + (y :: ys).length ≤ ceil32 (n + (y :: ys).length) :=
        Nat.le_ceil32 _
      refine ⟨Array.copyD μ.data
        (Array.replicate (ceil32 (n + (y :: ys).length)) 0x00), rfl, ?_, ?_, ?_, ?_⟩
      · rw [Array.size_copyD, Array.size_replicate]; exact hle
      · show μ.size ≤ ceil32 (n + (y :: ys).length); omega
      · exact hle
      · intro i hi
        by_cases hd : i < μ.data.size
        · rw [Array.getD_copyD_of_lt _ _ _ _ hd (by rw [Array.size_replicate]; omega)]
        · rw [Array.getD_copyD_of_size_le _ _ _ _ (Nat.not_lt.mp hd),
            Array.getD_replicate_zero, Array.getD_of_size_le 0 (Nat.not_lt.mp hd)]

/-- A write agrees with the old memory outside its window. -/
theorem Mem.write_agree (μ : Mem) (n : Nat) (ys : Bytes) :
    Mem.AgreeOutside μ (μ.write n ys) n (n + ys.length) := by
  cases ys with
  | nil => exact Mem.AgreeOutside.refl μ _ _
  | cons y ys =>
    obtain ⟨A, hdata, hA, hsz, _, hagree⟩ := Mem.write_base μ n (ys := y :: ys) (by simp)
    refine ⟨hsz, fun i hi hout => ?_⟩
    rw [hdata, Array.getD_writeD 0 _ A n i hA, if_neg (by omega)]
    exact hagree i hi

/-- A written word reads back, on any memory. -/
theorem Mem.memWord_write_word (μ : Mem) (n : Nat) (v : B256) :
    memWord (μ.write n v.toBytes) n = v ∧ n + 32 ≤ (μ.write n v.toBytes).size := by
  have hlen : v.toBytes.length = 32 := B256.length_toBytes v
  have hne : v.toBytes ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen
  obtain ⟨A, hdata, hA, _, hfit, _⟩ := Mem.write_base μ n hne
  refine ⟨?_, by rw [← hlen]; exact hfit⟩
  unfold memWord Mem.read
  rw [Array.sliceD_eq_map, hdata]
  have hmap : (List.range 32).map (fun j => (Array.writeD A n v.toBytes).getD (n + j) 0) =
      v.toBytes := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [Array.getD_writeD 0 _ A n (n + j) hA, if_pos (by simp at h1; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rw [hmap]
  exact B256.toB256_toBytes v

/-- An `MSTORE` of `v` at `n`, with its abstract value recorded. -/
theorem MemMatches.write_word {ρ : B256} {mem : MemMap} {μ : Mem} {n : Nat} {v : B256}
    {av : AVal} (hv : AVal.Matches ρ av v) (hm : MemMatches ρ mem μ) :
    MemMatches ρ ((n, av) :: memKill mem n (n + 32)) (μ.write n v.toBytes) := by
  intro o w how
  rcases List.mem_cons.mp how with h | h
  · cases h
    obtain ⟨hw, hs⟩ := Mem.memWord_write_word μ n v
    exact ⟨hs, by rw [hw]; exact hv⟩
  · have hag := Mem.write_agree μ n v.toBytes
    rw [B256.length_toBytes] at hag
    exact MemMatches.agree hag hm o w h

/-- Any write, forgetting the words its window overlaps. -/
theorem MemMatches.write {ρ : B256} {mem : MemMap} {μ : Mem} (n : Nat) (ys : Bytes)
    (hm : MemMatches ρ mem μ) :
    MemMatches ρ (memKill mem n (n + ys.length)) (μ.write n ys) :=
  MemMatches.agree (Mem.write_agree μ n ys) hm

/-! ## Instructions that keep memory -/

/-- `d'`'s memory has `d`'s bytes and is at least as large. -/
def MemKeep (d d' : Devm) : Prop :=
  d'.memory.data = d.memory.data ∧ d.memory.size ≤ d'.memory.size

theorem MemKeep.of_eq {d d' : Devm} (h : d.memory = d'.memory) : MemKeep d d' :=
  ⟨by rw [h], by rw [h]⟩

theorem MemKeep.trans {d d' d'' : Devm} (h1 : MemKeep d d') (h2 : MemKeep d' d'') :
    MemKeep d d'' := ⟨h2.1.trans h1.1, le_trans h1.2 h2.2⟩

theorem MemKeep.memRead (d : Devm) (i n : Nat) : MemKeep d (d.memRead i n).2 :=
  ⟨rfl, memExtSize_ge _ _ _⟩

theorem memKeep_pop {d d' : Devm} {x : B256} (h : Devm.pop d = .ok ⟨x, d'⟩) : MemKeep d d' :=
  .of_eq (Devm.pop_of_pop h).memory

theorem memKeep_popToNat {d d' : Devm} {k : Nat} (h : Devm.popToNat d = .ok ⟨k, d'⟩) :
    MemKeep d d' := by
  obtain ⟨_, hp⟩ := Devm.pop_of_popToNat h
  exact .of_eq hp.memory

theorem memKeep_chargeGas {d d' : Devm} {c : Nat} (h : chargeGas c d = .ok d') : MemKeep d d' :=
  .of_eq (Devm.burn_of_chargeGas h).memory

theorem memKeep_push {d d' : Devm} {x : B256} (h : Devm.push x d = .ok d') : MemKeep d d' :=
  .of_eq (Devm.push_of_push h).memory

theorem memKeep_pushItem {d d' : Devm} {x : B256} {c : Nat} (h : pushItem x c d = .ok d') :
    MemKeep d d' := by
  rw [pushItem_def] at h
  exact .of_eq (Devm.pushBurn_of_run h).memory

theorem rinstMemKeeps_run {pc : Nat} {sevm : Sevm} {devm devm' : Devm} {r : Rinst}
    (hr : rinstMemKeeps r = true) (h : Rinst.runCore pc devm sevm r = .ok devm') :
    MemKeep devm devm' := by
  cases r <;> simp [rinstMemKeeps] at hr <;> simp only [Rinst.runCore] at h
  case add | mul | sub | div | sdiv | mod | smod | signextend | lt | gt | slt | sgt | eq
      | and | or | xor | byte | shl | shr | sar =>
    obtain ⟨_, _, hd⟩ := Devm.diffBurn_of_applyBinary h
    exact .of_eq hd.memory
  case iszero | not =>
    obtain ⟨_, hd⟩ := Devm.diffBurn_of_applyUnary h
    exact .of_eq hd.memory
  case address | origin | caller | callvalue | calldatasize | codesize | gasprice
      | returndatasize | coinbase | timestamp | number | prevrandao | gaslimit | chainid
      | basefee | blobbasefee | msize =>
    exact memKeep_pushItem h
  case keccak256 =>
    obtain ⟨⟨i, d1⟩, h1, h'⟩ := Except.bind_eq_ok h
    obtain ⟨⟨n, d2⟩, h2, h''⟩ := Except.bind_eq_ok h'
    obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h''
    exact (memKeep_popToNat h1).trans ((memKeep_popToNat h2).trans
      ((memKeep_chargeGas h3).trans ((MemKeep.memRead d3 i n).trans (memKeep_push h4))))
  case calldataload =>
    obtain ⟨⟨x, d1⟩, h1, h'⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h'
    exact (memKeep_pop h1).trans ((memKeep_chargeGas h2).trans (memKeep_push h3))
  case pop =>
    cases hp : devm.pop with
    | error e => simp [hp] at h
    | ok r =>
      obtain ⟨x, d1⟩ := r
      simp only [hp] at h
      exact (memKeep_pop hp).trans (memKeep_chargeGas h)
  case mload =>
    obtain ⟨⟨i, d1⟩, h1, h'⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h'
    exact (memKeep_popToNat h1).trans ((memKeep_chargeGas h2).trans
      ((MemKeep.memRead d2 i 32).trans (memKeep_push h3)))
  case dup =>
    obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
    split at h2
    · cases h2
    · exact (memKeep_chargeGas h1).trans (memKeep_push h2)
  case swap =>
    obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
    split at h2
    · cases h2
    · cases h2
      exact (memKeep_chargeGas h1).trans ⟨rfl, Nat.le_refl _⟩
  case sload =>
    obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
    split at e1
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok e1
      have k3 := memKeep_push h3
      have k2 : MemKeep d2 (Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget x d2) :=
        MemKeep.of_eq rfl
      exact (memKeep_pop h1).trans ((memKeep_chargeGas h2).trans (k2.trans k3))
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok e1
      have k3 := memKeep_push h3
      have k2 : MemKeep d2 (Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget x d2) :=
        MemKeep.of_eq rfl
      have k1 : MemKeep d1 (addAccessedStorageKey d1 sevm.currentTarget x) := MemKeep.of_eq rfl
      exact (memKeep_pop h1).trans (k1.trans ((memKeep_chargeGas h2).trans (k2.trans k3)))
  case tload =>
    obtain ⟨⟨x, d1⟩, h1, h2⟩ := Except.bind_eq_ok h
    exact (memKeep_pop h1).trans (memKeep_pushItem h2)
  case log n =>
    obtain ⟨⟨mi, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
    obtain ⟨⟨sz, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
    obtain ⟨⟨tp, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
    obtain ⟨d4, h4, e4⟩ := Except.bind_eq_ok e3
    obtain ⟨_, h5, h6⟩ := Except.bind_eq_ok e4
    cases h6
    have hk3 : MemKeep d2 d3 := .of_eq (Devm.pop_of_popN h3).2.memory
    exact (memKeep_popToNat h1).trans ((memKeep_popToNat h2).trans (hk3.trans
      ((memKeep_chargeGas h4).trans ((MemKeep.memRead d4 mi sz).trans ⟨rfl, Nat.le_refl _⟩))))
  case tstore =>
    split at h
    · obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
      obtain ⟨⟨y, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
      obtain ⟨d3, h3, e3⟩ := Except.bind_eq_ok e2
      obtain ⟨_, _, h5⟩ := Except.bind_eq_ok e3
      cases h5
      have k4 : MemKeep d3 (d3.setTransVal sevm.currentTarget x y) := MemKeep.of_eq rfl
      exact (memKeep_pop h1).trans ((memKeep_pop h2).trans ((memKeep_chargeGas h3).trans k4))
    · obtain ⟨_, _, e0⟩ := Except.bind_eq_ok h
      obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok e0
      obtain ⟨⟨y, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
      obtain ⟨d3, h3, h5⟩ := Except.bind_eq_ok e2
      cases h5
      have k4 : MemKeep d3 (d3.setTransVal sevm.currentTarget x y) := MemKeep.of_eq rfl
      exact (memKeep_pop h1).trans ((memKeep_pop h2).trans ((memKeep_chargeGas h3).trans k4))
  case sstore =>
    split at h
    · obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
      obtain ⟨⟨y, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
      obtain ⟨_, _, e3⟩ := Except.bind_eq_ok e2
      obtain ⟨⟨d3, g⟩, h4, e4⟩ := Except.bind_eq_ok e3
      obtain ⟨g3, h5, e5⟩ := Except.bind_eq_ok e4
      obtain ⟨d4, h6, e6⟩ := Except.bind_eq_ok e5
      obtain ⟨d5, h7, e7⟩ := Except.bind_eq_ok e6
      obtain ⟨_, _, h9⟩ := Except.bind_eq_ok e7
      cases h9
      have m3 : d3.memory = d2.memory := by
        injection h4 with eq
        split at eq <;> (injection eq with eq _; subst eq; rfl)
      have m4 : d4.memory = d3.memory := by
        injection h6 with eq; rw [← eq]; rfl
      apply MemKeep.of_eq
      show devm.memory = d5.memory
      rw [← (Devm.burn_of_chargeGas h7).memory, m4, m3, ← (Devm.pop_of_pop h2).memory,
        ← (Devm.pop_of_pop h1).memory]
    · obtain ⟨_, _, e0⟩ := Except.bind_eq_ok h
      obtain ⟨⟨x, d1⟩, h1, e1⟩ := Except.bind_eq_ok e0
      obtain ⟨⟨y, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
      obtain ⟨_, _, e3⟩ := Except.bind_eq_ok e2
      obtain ⟨d3, hchg, e4⟩ := Except.bind_eq_ok e3
      obtain ⟨d4, hstg, h9⟩ := Except.bind_eq_ok e4
      cases h9
      have mc := (Devm.burn_of_chargeGas hchg).memory
      have ms := Devm.chargeStateGas_memory hstg
      apply MemKeep.of_eq
      show devm.memory = d4.memory
      rw [ms, ← mc]
      have e1 : ∀ (a : Nat) (d : Devm), (Devm.creditStateGasRefund a d).memory = d.memory :=
        fun _ _ => rfl
      have e2 : ∀ (r : Int) (d : Devm), (d.withRefundCounter r).memory = d.memory :=
        fun _ _ => rfl
      have e3 : ∀ (rl : ForkRules) (a : Adr) (k : B256) (d : Devm),
          (Devm.balReadStorage rl a k d).memory = d.memory := fun _ _ _ _ => rfl
      have e4 : ∀ (d : Devm) (a : Adr) (k : B256),
          (addAccessedStorageKey d a k).memory = d.memory := fun _ _ _ => rfl
      rw [e1, e2, e3]
      split
      · rw [e4, ← (Devm.pop_of_pop h2).memory, ← (Devm.pop_of_pop h1).memory]
      · rw [← (Devm.pop_of_pop h2).memory, ← (Devm.pop_of_pop h1).memory]

theorem ninstMemKeeps_run {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hn : ninstMemKeeps n = true) (run : Ninst.Run sevm pre n post) : MemKeep pre post := by
  cases n with
  | push bs fits =>
    rcases run with ⟨xl, _, pc, hstep⟩
    rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hstep
    obtain ⟨d, h1, h2⟩ := Except.bind_eq_ok hstep.2.symm
    exact (memKeep_chargeGas h1).trans (memKeep_push h2)
  | reg r =>
    rcases of_run_reg run with ⟨pc, h⟩
    exact rinstMemKeeps_run hn h
  | exec _ => simp [ninstMemKeeps] at hn
  | dupn _ => simp [ninstMemKeeps] at hn
  | swapn _ => simp [ninstMemKeeps] at hn
  | exchange _ => simp [ninstMemKeeps] at hn

/-- `MSTORE` writes its second operand's bytes at its first operand. -/
theorem mstore_run_memory {sevm : Sevm} {pre post : Devm} {o v : B256} {rest : List B256}
    (run : Ninst.Run sevm pre (.reg .mstore) post) (hs : pre.stack = o :: v :: rest) :
    post.memory = pre.memory.write o.toNat v.toBytes := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨w, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok e2
  cases h4
  obtain ⟨x, hp1, hi⟩ := Devm.pop_of_popToNat_val h1
  have hp2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  have hs1 := hp1.stack
  have hs2 := hp2.stack
  simp only [Stack.Pop, Split, List.cons_append, List.nil_append] at hs1 hs2
  rw [hs] at hs1
  simp only [List.cons.injEq] at hs1
  obtain ⟨rfl, hs1⟩ := hs1
  rw [← hs1] at hs2
  simp only [List.cons.injEq] at hs2
  obtain ⟨rfl, _⟩ := hs2
  subst hi
  simp only [Devm.memWrite_memory]
  rw [← hb.memory, ← hp2.memory, ← hp1.memory]

/-- `CALLDATACOPY` writes `size` bytes at its first operand. -/
theorem calldatacopy_run_memory {sevm : Sevm} {pre post : Devm} {d src z : B256}
    {rest : List B256}
    (run : Ninst.Run sevm pre (.reg .calldatacopy) post)
    (hs : pre.stack = d :: src :: z :: rest) :
    ∃ ys : Bytes, ys.length = z.toNat ∧ post.memory = pre.memory.write d.toNat ys := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨j, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨⟨k, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
  obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok e3
  cases h5
  obtain ⟨x, hp1, hi⟩ := Devm.pop_of_popToNat_val h1
  obtain ⟨y, hp2, _⟩ := Devm.pop_of_popToNat_val h2
  obtain ⟨w, hp3, hk⟩ := Devm.pop_of_popToNat_val h3
  have hb := Devm.burn_of_chargeGas h4
  have hs1 := hp1.stack
  have hs2 := hp2.stack
  have hs3 := hp3.stack
  simp only [Stack.Pop, Split, List.cons_append, List.nil_append] at hs1 hs2 hs3
  rw [hs] at hs1
  simp only [List.cons.injEq] at hs1
  obtain ⟨rfl, hs1⟩ := hs1
  rw [← hs1] at hs2
  simp only [List.cons.injEq] at hs2
  obtain ⟨rfl, hs2⟩ := hs2
  rw [← hs2] at hs3
  simp only [List.cons.injEq] at hs3
  obtain ⟨rfl, _⟩ := hs3
  subst hi hk
  refine ⟨List.sliceD sevm.data j z.toNat 0, List.takeD_length _ _ _, ?_⟩
  simp only [Devm.memWrite_memory]
  rw [← hb.memory, ← hp3.memory, ← hp2.memory, ← hp1.memory]

/-- `MLOAD` pushes the word at its operand. -/
theorem mload_run_stack {sevm : Sevm} {pre post : Devm} {o : B256} {rest : List B256}
    (run : Ninst.Run sevm pre (.reg .mload) post) (hs : pre.stack = o :: rest) :
    post.stack = memWord pre.memory o.toNat :: rest := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok e1
  obtain ⟨x, hp1, hi⟩ := Devm.pop_of_popToNat_val h1
  have hb := Devm.burn_of_chargeGas h2
  have hpu := (Devm.push_of_push h3).stack
  have hs1 := hp1.stack
  simp only [Stack.Pop, Stack.Push, Split, List.cons_append, List.nil_append] at hs1 hpu
  rw [hs] at hs1
  simp only [List.cons.injEq] at hs1
  obtain ⟨rfl, hs1⟩ := hs1
  subst hi
  rw [hpu]
  have hmem : d2.memory = pre.memory := by rw [← hb.memory, ← hp1.memory]
  have hst : d2.stack = rest := by rw [← hb.stack, hs1]
  simp only [Devm.memRead, memWord, hmem, List.cons.injEq, true_and]
  exact hst

/-! ## The memory transfer -/

theorem mem_of_lookup_eq_some {mem : MemMap} {o : Nat} {v : AVal}
    (h : mem.lookup o = some v) : (o, v) ∈ mem := by
  induction mem with
  | nil => simp at h
  | cons p mem ih =>
    obtain ⟨o', v'⟩ := p
    by_cases ho : o = o'
    · subst ho
      simp [List.lookup] at h
      subst h
      exact List.mem_cons_self
    · have hb : (o == o') = false := by simpa using ho
      have h' : mem.lookup o = some v := by simpa [List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (ih h')

theorem absMem_sound {sevm : Sevm} {pre post : Devm} {n : Ninst} {a : List AVal}
    {mem : MemMap} {ρ : B256} {S base : List B256}
    (hframe : FrameMatches ρ a S) (hstack : pre.stack = S ++ base)
    (hm : MemMatches ρ mem pre.memory) (run : Ninst.Run sevm pre n post) :
    MemMatches ρ (absMem n a mem) post.memory := by
  unfold absMem
  split
  · rcases hframe with _ | ⟨h0, _ | ⟨h1, _⟩⟩
    simp only [AVal.Matches] at h0
    subst h0
    rw [mstore_run_memory run (by simpa using hstack)]
    exact MemMatches.write_word h1 hm
  · rcases hframe with _ | ⟨h0, _ | ⟨_, _ | ⟨h2, _⟩⟩⟩
    simp only [AVal.Matches] at h0 h2
    subst h0 h2
    obtain ⟨ys, hlen, hmem⟩ := calldatacopy_run_memory run (by simpa using hstack)
    rw [hmem, ← hlen]
    exact MemMatches.write _ _ hm
  · split
    · rename_i hk
      obtain ⟨hd, hsz⟩ := ninstMemKeeps_run hk run
      exact MemMatches.of_data_eq hd hsz hm
    · exact memMatches_nil _ _

theorem memTop_sound {sevm : Sevm} {pre post : Devm} {n : Ninst} {a : List AVal}
    {mem : MemMap} {ρ : B256} {S base : List B256} {v : AVal}
    (ht : memTop n a mem = some v) (hframe : FrameMatches ρ a S)
    (hstack : pre.stack = S ++ base) (hm : MemMatches ρ mem pre.memory)
    (run : Ninst.Run sevm pre n post) :
    ∃ w rest, post.stack = w :: rest ∧ AVal.Matches ρ v w := by
  unfold memTop at ht
  split at ht
  · rcases hframe with _ | ⟨h0, _⟩
    simp only [AVal.Matches] at h0
    subst h0
    exact ⟨_, _, mload_run_stack run (by simpa using hstack),
      (hm _ _ (mem_of_lookup_eq_some ht)).2⟩
  · cases ht

/-- One checked instruction step keeps both invariants: the frame refined by a
recorded `MLOAD` result still describes the stack, and the transferred map
still describes memory. -/
theorem step_mem_sound (b : Bool) {sevm : Sevm} {pre post : Devm} {n : Ninst}
    {a a' : List AVal} {μ : MemMap} {ρ : B256} {S S' base : List B256}
    (hframe : FrameMatches ρ a S) (hstack : pre.stack = S ++ base)
    (hm : MemMatches ρ μ pre.memory) (run : Ninst.Run sevm pre n post)
    (hpost : post.stack = S' ++ base) (h' : FrameMatches ρ a' S') :
    FrameMatches ρ (if b then memFold (memTop n a μ) a' else a') S' ∧
      MemMatches ρ (if b then absMem n a μ else []) post.memory := by
  cases b with
  | false => exact ⟨h', memMatches_nil _ _⟩
  | true =>
    refine ⟨?_, absMem_sound hframe hstack hm run⟩
    simp only [if_true]
    cases ht : memTop n a μ with
    | none => cases a' <;> exact h'
    | some v =>
      obtain ⟨w, rest, hw, hv⟩ := memTop_sound ht hframe hstack hm run
      cases h' with
      | nil => exact List.Forall₂.nil
      | @cons x s t T _ htail =>
        refine List.Forall₂.cons ?_ htail
        have := hpost.symm.trans hw
        simp only [List.cons_append, List.cons.injEq] at this
        rw [this.1]
        exact hv

/-- A goto's declared map is recorded identically by the current one. -/
theorem MemMatches.of_memCompat {ρ : B256} {cur decl : MemMap} {μ : Mem}
    (hc : memCompat cur decl = true) (hm : MemMatches ρ cur μ) : MemMatches ρ decl μ := by
  intro o v hov
  have h := List.all_eq_true.mp hc (o, v) hov
  simp only [beq_iff_eq] at h
  exact hm o v (mem_of_lookup_eq_some h)

theorem MemMatches.of_memory_eq {ρ : B256} {mem : MemMap} {μ μ' : Mem} (h : μ = μ')
    (hm : MemMatches ρ mem μ) : MemMatches ρ mem μ' := h ▸ hm

/-! ## Where the return address can be -/

/-- The current function's return address occurs in the frame or the map. -/
def RetIn (a : List AVal) (μ : MemMap) : Prop :=
  AVal.ret ∈ a ∨ AVal.ret ∈ μ.map Prod.snd

theorem RetIn.of_frame {a a' : List AVal} {μ : MemMap} (h : AVal.ret ∈ a' → AVal.ret ∈ a)
    (hr : RetIn a' μ) : RetIn a μ := hr.imp_left h

theorem retIn_nil_nil : ¬ RetIn [] [] := by simp [RetIn]

theorem mem_snd_memKill {mem : MemMap} {lo hi : Nat} {v : AVal}
    (h : v ∈ (memKill mem lo hi).map Prod.snd) : v ∈ mem.map Prod.snd := by
  simp only [List.mem_map] at h ⊢
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, List.mem_of_mem_filter hp, rfl⟩

theorem mem_snd_absMem {n : Ninst} {a : List AVal} {mem : MemMap} {v : AVal}
    (h : v ∈ (absMem n a mem).map Prod.snd) : v ∈ a ∨ v ∈ mem.map Prod.snd := by
  unfold absMem at h
  split at h
  · rw [List.map_cons] at h
    rcases List.mem_cons.mp h with h | h
    · left; subst h; simp
    · right; exact mem_snd_memKill h
  · right; exact mem_snd_memKill h
  · split at h
    · exact .inr h
    · simp at h

/-- The return address after a checked step was already in the frame or the map. -/
theorem RetIn.of_step (b : Bool) {n : Ninst} {a a' : List AVal} {μ : MemMap}
    (h : RetIn (if b then memFold (memTop n a μ) a' else a') (if b then absMem n a μ else [])) :
    AVal.ret ∈ a' ∨ AVal.ret ∈ a ∨ AVal.ret ∈ μ.map Prod.snd := by
  cases b with
  | false =>
    rcases h with h | h
    · exact .inl (by simpa using h)
    · simp at h
  | true =>
    simp only [if_true] at h
    rcases h with h | h
    · cases ht : memTop n a μ with
      | none => rw [ht] at h; exact .inl (by cases a' <;> exact h)
      | some v =>
        rw [ht] at h
        cases a' with
        | nil => exact .inl h
        | cons x t =>
          rcases List.mem_cons.mp h with h | h
          · subst h
            unfold memTop at ht
            split at ht
            · exact .inr (.inr (List.mem_map.mpr ⟨_, mem_of_lookup_eq_some ht, rfl⟩))
            · cases ht
          · exact .inl (List.mem_cons_of_mem _ h)
    · exact .inr (mem_snd_absMem h)

/-- A goto's declared map is contained in the current one. -/
theorem mem_snd_of_memCompat {cur decl : MemMap} {v : AVal} (hc : memCompat cur decl = true)
    (h : v ∈ decl.map Prod.snd) : v ∈ cur.map Prod.snd := by
  simp only [List.mem_map] at h ⊢
  obtain ⟨⟨o, w⟩, hp, rfl⟩ := h
  have hl := List.all_eq_true.mp hc (o, w) hp
  simp only [beq_iff_eq] at hl
  exact ⟨(o, w), mem_of_lookup_eq_some hl, rfl⟩

end Blanc.Lift
