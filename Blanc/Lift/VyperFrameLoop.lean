import Blanc.Lift.InvWalkOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.MemMap
import Jaune.MemoryAccounting

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

/-- A write that misses a word inside the logical size leaves it. -/
theorem memWord_write_of_disjoint {M : Mem} {n o : Nat} {ys : Bytes} (ho : o + 32 ≤ M.size)
    (hd : o + 32 ≤ n ∨ n + ys.length ≤ o) : memWord (M.write n ys) o = memWord M o :=
  memWord_congr fun j hj => (Mem.write_agree M n ys).2 _ (by omega) (by omega)

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

theorem Words.append {M : Mem} {L L' : List (Nat × B256)} :
    Words M (L ++ L') ↔ Words M L ∧ Words M L' := by
  constructor
  · intro h
    exact ⟨fun o v h' => h o v (List.mem_append_left _ h'),
      fun o v h' => h o v (List.mem_append_right _ h')⟩
  · rintro ⟨h1, h2⟩ o v h'
    rcases List.mem_append.mp h' with h' | h'
    · exact h1 o v h'
    · exact h2 o v h'

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

theorem frameLoop_len2 (a b : UInt8) : [a, b].length ≤ 32 := by
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff]

/-- One save iteration: push the word at the counter (`c`), add `32` to the counter, and
`JUMPI` to `exit` (tag `x`) once the counter reached the bound `e`, else fall to `fall`. -/
def frameSaveIter (c0 c1 e0 e1 x0 x1 : UInt8) (fall exit : SFunc) : SFunc :=
  .dest (.next (.push [c0, c1] (frameLoop_len2 c0 c1)) (.next (.reg .mload) (.next (.reg .mload)
  (.next (.push [0x20] (by decide)) (.next (.push [c0, c1] (frameLoop_len2 c0 c1)) (.next (.reg .mload)
  (.next (.reg .add) (.next (.push [c0, c1] (frameLoop_len2 c0 c1)) (.next (.reg .mstore)
  (.next (.push [e0, e1] (frameLoop_len2 e0 e1)) (.next (.push [c0, c1] (frameLoop_len2 c0 c1)) (.next (.reg .mload)
  (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [x0, x1] (frameLoop_len2 x0 x1))
  (.branch fall exit))))))))))))))))

/-- One restore iteration: pop the stack top into the word at the counter (`c`), subtract `32`
from the counter, and `JUMPI` to `exit` (tag `x`) once the counter fell below `lo` (bytes
`l0 l1`), else fall to `fall`. -/
def frameRestoreIter (c0 c1 l0 l1 x0 x1 : UInt8) (fall exit : SFunc) : SFunc :=
  .dest (.next (.push [c0, c1] (frameLoop_len2 c0 c1)) (.next (.reg .mload) (.next (.reg .mstore)
  (.next (.push [0x20] (by decide)) (.next (.push [c0, c1] (frameLoop_len2 c0 c1)) (.next (.reg .mload)
  (.next (.reg .sub) (.next (.push [c0, c1] (frameLoop_len2 c0 c1)) (.next (.reg .mstore)
  (.next (.push [l0, l1] (frameLoop_len2 l0 l1)) (.next (.push [c0, c1] (frameLoop_len2 c0 c1)) (.next (.reg .mload)
  (.next (.reg .lt) (.next (.reg .iszero) (.next (.reg .iszero) (.next (.push [x0, x1] (frameLoop_len2 x0 x1))
  (.branch fall exit)))))))))))))))))

/-- The back edge into the next unrolled copy: `PUSH2 head; JUMP` into entry `k`. -/
def frameLoopNext (h0 h1 : UInt8) (k : Nat) : SFunc :=
  .next (.push [h0, h1] (frameLoop_len2 h0 h1)) (.jump k)

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

/-- The counter address. -/
def c (t : FrameLoopTpl) : Nat := (Bytes.toB256 [t.c0, t.c1]).toNat

/-- The bound. -/
def e (t : FrameLoopTpl) : Nat := (Bytes.toB256 [t.e0, t.e1]).toNat

/-- The save iteration whose remaining chain entries are `ks` (the last one leaves to
`exitT`). -/
def saveTree (t : FrameLoopTpl) (exitT : SFunc) : List Nat → SFunc
  | [] => frameSaveIter t.c0 t.c1 t.e0 t.e1 t.x0 t.x1 .undefined exitT
  | k :: _ => frameSaveIter t.c0 t.c1 t.e0 t.e1 t.x0 t.x1 (frameLoopNext t.h0 t.h1 k) .undefined

/-- The restore iteration whose remaining chain entries are `ks`. -/
def restoreTree (t : FrameLoopTpl) (exitT : SFunc) : List Nat → SFunc
  | [] => frameRestoreIter t.c0 t.c1 t.e0 t.e1 t.x0 t.x1 .undefined exitT
  | k :: _ => frameRestoreIter t.c0 t.c1 t.e0 t.e1 t.x0 t.x1 (frameLoopNext t.h0 t.h1 k)
      .undefined

/-- The trees the chain entries `ks` must hold, in order. -/
def saveTrees (t : FrameLoopTpl) (exitT : SFunc) : List Nat → List (Option SFunc)
  | [] => []
  | _ :: ks => some (t.saveTree exitT ks) :: t.saveTrees exitT ks

def restoreTrees (t : FrameLoopTpl) (exitT : SFunc) : List Nat → List (Option SFunc)
  | [] => []
  | _ :: ks => some (t.restoreTree exitT ks) :: t.restoreTrees exitT ks

end FrameLoopTpl

/-- **The chain fact**: entry `ks[i]` holds the save iteration continuing to `ks[i+1]`, the last
one the iteration leaving to `exitT`.  One equation, discharged by `rfl`. -/
def FrameSaveChain (fs : List SFunc) (t : FrameLoopTpl) (exitT : SFunc) (ks : List Nat) : Prop :=
  ks.map (fun k => fs[k]?) = t.saveTrees exitT ks

def FrameRestoreChain (fs : List SFunc) (t : FrameLoopTpl) (exitT : SFunc) (ks : List Nat) :
    Prop :=
  ks.map (fun k => fs[k]?) = t.restoreTrees exitT ks

theorem FrameSaveChain.cons {fs : List SFunc} {t : FrameLoopTpl} {exitT : SFunc} {k : Nat}
    {ks : List Nat} (h : FrameSaveChain fs t exitT (k :: ks)) :
    fs[k]? = some (t.saveTree exitT ks) ∧ FrameSaveChain fs t exitT ks := by
  simp only [FrameSaveChain, List.map_cons, FrameLoopTpl.saveTrees, List.cons.injEq] at h
  exact h

theorem FrameRestoreChain.cons {fs : List SFunc} {t : FrameLoopTpl} {exitT : SFunc} {k : Nat}
    {ks : List Nat} (h : FrameRestoreChain fs t exitT (k :: ks)) :
    fs[k]? = some (t.restoreTree exitT ks) ∧ FrameRestoreChain fs t exitT ks := by
  simp only [FrameRestoreChain, List.map_cons, FrameLoopTpl.restoreTrees, List.cons.injEq] at h
  exact h

/-! ## One iteration, inverted -/

section Inv

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg}

theorem toB256_add_0x20 {p : Nat} (hp : p + 32 < 2 ^ 256) :
    Nat.toB256 p + Bytes.toB256 [0x20] = Nat.toB256 (p + 32) := by
  rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, toB256_add_toB256 hp]

theorem toB256_sub_0x20 {p : Nat} (h32 : 32 ≤ p) (hp : p < 2 ^ 256) :
    Nat.toB256 p - Bytes.toB256 [0x20] = Nat.toB256 (p - 32) := by
  rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, toB256_sub_toB256 h32 hp]

/-- **One save iteration, inverted**: the word at the counter's value `p` is pushed and the
counter becomes `p + 32`; the run goes on in one of the `JUMPI` arms. -/
theorem ric_frameSaveIter {c0 c1 e0 e1 x0 x1 : UInt8} {fall exit : SFunc} {p c : Nat}
    (hc : (Bytes.toB256 [c0, c1]).toNat = c)
    (hsz : M.size % 32 = 0) (hcs : c + 32 ≤ M.size)
    (hps : p + 32 ≤ M.size) (hp : p + 32 < 2 ^ 256)
    (hctr : memWord M c = Nat.toB256 p)
    (run : SFunc.RunCut fs sevm C (St b S M G) (frameSaveIter c0 c1 e0 e1 x0 x1 fall exit) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (memWord M p :: S)
        (M.write c (Nat.toB256 (p + 32)).toBytes) G') fall r ∨
      SFunc.RunCut fs sevm C (St b (memWord M p :: S)
        (M.write c (Nat.toB256 (p + 32)).toBytes) G') exit r := by
  subst hc
  have hR : ∀ o, o + 32 ≤ M.size → (M.read o 32).2 = M := fun o ho => read_covered rfl hsz ho
  have hpn : (Nat.toB256 p).toNat = p := B256.toNat_toB256_of_lt (by omega)
  have hctr' : Bytes.toB256 (M.read (Bytes.toB256 [c0, c1]).toNat 32).1 = Nat.toB256 p := hctr
  have hM1 := Mem.size_write_word_of_add_le (v := Nat.toB256 (p + 32)) hcs
  unfold frameSaveIter at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_mload s1
  rw [hR _ hcs, hctr'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mload s1
  rw [hpn, hR _ hps] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_mload s1
  rw [hR _ hcs, hctr'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_add s1
  rw [toB256_add_0x20 hp] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_mload s1
  rw [read_covered rfl (by rw [hM1]; exact hsz) (by rw [hM1]; exact hcs)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G17, run⟩ | ⟨-, G17, run⟩
  · exact ⟨G17, .inl run⟩
  · exact ⟨G17, .inr run⟩

/-- **One restore iteration, inverted**: the stack top `w` is written at the counter's value
`p` and the counter becomes `p - 32`; the run goes on in one of the `JUMPI` arms. -/
theorem ric_frameRestoreIter {c0 c1 l0 l1 x0 x1 : UInt8} {fall exit : SFunc} {p c : Nat}
    {w : B256} (hc : (Bytes.toB256 [c0, c1]).toNat = c) (hsz : M.size % 32 = 0) (hcs : c + 32 ≤ M.size)
    (hpc : p + 32 ≤ c) (h32 : 32 ≤ p)
    (hctr : memWord M c = Nat.toB256 p)
    (run : SFunc.RunCut fs sevm C (St b (w :: S) M G)
      (frameRestoreIter c0 c1 l0 l1 x0 x1 fall exit) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b S ((M.write p w.toBytes).write
        c (Nat.toB256 (p - 32)).toBytes) G') fall r ∨
      SFunc.RunCut fs sevm C (St b S ((M.write p w.toBytes).write
        c (Nat.toB256 (p - 32)).toBytes) G') exit r := by
  subst hc
  have hR : ∀ o, o + 32 ≤ M.size → (M.read o 32).2 = M := fun o ho => read_covered rfl hsz ho
  have hcb : (Bytes.toB256 [c0, c1]).toNat < 2 ^ 256 := B256.toNat_lt _
  have hpn : (Nat.toB256 p).toNat = p := B256.toNat_toB256_of_lt (by omega)
  have hctr' : Bytes.toB256 (M.read (Bytes.toB256 [c0, c1]).toNat 32).1 = Nat.toB256 p := hctr
  have hM1 : (M.write p w.toBytes).size = M.size := Mem.size_write_word_of_add_le (by omega)
  have hctr1 : Bytes.toB256 ((M.write p w.toBytes).read (Bytes.toB256 [c0, c1]).toNat 32).1 =
      Nat.toB256 p := by
    show memWord _ _ = _
    rw [memWord_write_of_disjoint hcs (by rw [B256.length_toBytes]; omega), hctr]
  have hM2 := Mem.size_write_word_of_add_le (M := M.write p w.toBytes) (v := Nat.toB256 (p - 32))
    (by rw [hM1]; exact hcs)
  unfold frameRestoreIter at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_mload s1
  rw [hR _ hcs, hctr'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mstore s1
  rw [hpn] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_mload s1
  rw [read_covered rfl (by rw [hM1]; exact hsz) (by rw [hM1]; exact hcs), hctr1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_sub s1
  rw [toB256_sub_0x20 h32 (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_mload s1
  rw [read_covered rfl (by rw [hM2, hM1]; exact hsz) (by rw [hM2, hM1]; exact hcs)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G18, run⟩ | ⟨-, G18, run⟩
  · exact ⟨G18, .inl run⟩
  · exact ⟨G18, .inr run⟩

end Inv

/-! ## What the chains leave in memory -/

/-- The `n` frame words of `M` from `lo`, lowest first: what a save chain pushes (the stack
holds them reversed). -/
def frameWords (M : Mem) (lo n : Nat) : List B256 :=
  (List.range n).map fun i => memWord M (lo + 32 * i)

/-- The frame words as carried slots. -/
def frameSlots (M : Mem) (lo n : Nat) : List (Nat × B256) :=
  (List.range n).map fun i => (lo + 32 * i, memWord M (lo + 32 * i))

theorem frameWords_succ (M : Mem) (lo n : Nat) :
    frameWords M lo (n + 1) = frameWords M lo n ++ [memWord M (lo + 32 * n)] := by
  simp only [frameWords, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem length_frameWords (M : Mem) (lo n : Nat) : (frameWords M lo n).length = n := by
  simp only [frameWords, List.length_map, List.length_range]

/-- The save chain's memory after `n` iterations: the counter at `c` rewritten to
`lo + 32 i` for `i = 1 … n`. -/
def saveMem (M : Mem) (c lo : Nat) : Nat → Mem
  | 0 => M
  | n + 1 => (saveMem M c lo n).write c (Nat.toB256 (lo + 32 * (n + 1))).toBytes

theorem saveMem_size {M : Mem} {c lo : Nat} (h : c + 32 ≤ M.size) :
    ∀ n, (saveMem M c lo n).size = M.size
  | 0 => rfl
  | n + 1 => by
    simp only [saveMem]
    rw [Mem.size_write_word_of_add_le (by rw [saveMem_size h n]; exact h), saveMem_size h n]

theorem saveMem_agree (M : Mem) (c lo : Nat) :
    ∀ n, Mem.AgreeOutside M (saveMem M c lo n) c (c + 32)
  | 0 => Mem.AgreeOutside.refl M _ _
  | n + 1 => by
    have h := Mem.write_agree (saveMem M c lo n) c (Nat.toB256 (lo + 32 * (n + 1))).toBytes
    rw [B256.length_toBytes] at h
    exact (saveMem_agree M c lo n).trans h

theorem saveMem_ctr {M : Mem} {c lo : Nat} (hctr : memWord M c = Nat.toB256 lo) :
    ∀ n, memWord (saveMem M c lo n) c = Nat.toB256 (lo + 32 * n)
  | 0 => by simpa only [saveMem, Nat.mul_zero, Nat.add_zero] using hctr
  | n + 1 => (Mem.memWord_write_word _ _ _).1

theorem saveMem_word {M : Mem} {c lo o : Nat} (ho : o + 32 ≤ M.size)
    (hd : o + 32 ≤ c ∨ c + 32 ≤ o) (n : Nat) : memWord (saveMem M c lo n) o = memWord M o :=
  memWord_congr fun j hj => (saveMem_agree M c lo n).2 _ (by omega) (by omega)

/-- The restore chain's memory: from the counter value `p`, each stack word (top first) is
written at the counter, which then drops by `32`. -/
def restoreMem (c : Nat) : Mem → Nat → List B256 → Mem
  | M, _, [] => M
  | M, p, w :: ws =>
    restoreMem c ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes) (p - 32) ws

theorem restoreMem_size {c : Nat} :
    ∀ {M : Mem} {p : Nat} (ws : List B256), c + 32 ≤ M.size → p + 32 ≤ M.size →
      (restoreMem c M p ws).size = M.size
  | _, _, [], _, _ => rfl
  | M, p, w :: ws, hc, hp => by
    have h1 : (M.write p w.toBytes).size = M.size := Mem.size_write_word_of_add_le hp
    have h2 : ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes).size = M.size := by
      rw [Mem.size_write_word_of_add_le (by rw [h1]; exact hc), h1]
    simp only [restoreMem]
    rw [restoreMem_size ws (by rw [h2]; exact hc) (by rw [h2]; omega), h2]

/-- The restore chain changes memory only in `[p + 32 - 32 |ws|, c + 32)`. -/
theorem restoreMem_agree {c : Nat} :
    ∀ {M : Mem} {p : Nat} (ws : List B256), p + 32 ≤ c →
      Mem.AgreeOutside M (restoreMem c M p ws) (p + 32 - 32 * ws.length) (c + 32)
  | M, _, [], _ => Mem.AgreeOutside.refl M _ _
  | M, p, w :: ws, hp => by
    have a1 := Mem.write_agree M p w.toBytes
    have a2 := Mem.write_agree (M.write p w.toBytes) c (Nat.toB256 (p - 32)).toBytes
    rw [B256.length_toBytes] at a1 a2
    have a3 : Mem.AgreeOutside ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes)
        (restoreMem c ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes) (p - 32) ws)
        (p - 32 + 32 - 32 * ws.length) (c + 32) :=
      restoreMem_agree ws (by omega)
    simp only [restoreMem, List.length_cons]
    exact ((a1.mono (lo' := p + 32 - 32 * (ws.length + 1)) (hi' := c + 32) (by omega)
      (by omega)).trans (a2.mono (by omega) (by omega))).trans (a3.mono (by omega) (by omega))

/-- Words at or above `p + 32` and off the counter survive the restore chain. -/
theorem restoreMem_word {c o : Nat} :
    ∀ {M : Mem} {p : Nat} (ws : List B256), o + 32 ≤ M.size → p + 32 ≤ o →
      (o + 32 ≤ c ∨ c + 32 ≤ o) → memWord (restoreMem c M p ws) o = memWord M o
  | _, _, [], _, _, _ => rfl
  | M, p, w :: ws, ho, hp, hd => by
    have h1 : (M.write p w.toBytes).size = M.size := by
      rcases Nat.lt_or_ge M.size (p + 32) with h | h
      · exact absurd (lt_of_lt_of_le h (by omega : p + 32 ≤ o + 32)) (by omega)
      · exact Mem.size_write_word_of_add_le h
    have hw1 : memWord (M.write p w.toBytes) o = memWord M o :=
      memWord_write_of_disjoint ho (by rw [B256.length_toBytes]; omega)
    have hs1 : o + 32 ≤ (M.write p w.toBytes).size := by rw [h1]; exact ho
    have hw2 : memWord ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes) o =
        memWord M o := by
      rw [memWord_write_of_disjoint hs1 (by rw [B256.length_toBytes]; omega), hw1]
    have hs2 : o + 32 ≤ ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes).size :=
      le_trans hs1 (Mem.write_agree _ _ _).1
    simp only [restoreMem]
    rw [restoreMem_word ws hs2 (by omega) hd, hw2]

/-- The restore chain writes its `j`-th stack word at `p - 32 j`. -/
theorem restoreMem_getElem {c : Nat} :
    ∀ {M : Mem} {p : Nat} (ws : List B256), c + 32 ≤ M.size → p + 32 ≤ c →
      32 * ws.length ≤ p + 32 → ∀ j (hj : j < ws.length),
      memWord (restoreMem c M p ws) (p - 32 * j) = ws[j]
  | _, _, [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | M, p, w :: ws, hc, hp, hl, j, hj => by
    simp only [List.length_cons] at hl hj
    have h1 : (M.write p w.toBytes).size = M.size := Mem.size_write_word_of_add_le (by omega)
    have h2 : ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes).size = M.size := by
      rw [Mem.size_write_word_of_add_le (by rw [h1]; exact hc), h1]
    cases j with
    | zero =>
      simp only [restoreMem, Nat.mul_zero, Nat.sub_zero, List.getElem_cons_zero]
      have hw : memWord ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes) p = w := by
        rw [memWord_write_of_disjoint (by rw [h1]; omega) (by rw [B256.length_toBytes]; omega)]
        exact (Mem.memWord_write_word M p w).1
      rcases ws with _ | ⟨w', ws⟩
      · exact hw
      · rw [restoreMem_word _ (by rw [h2]; omega) (by simp only [List.length_cons] at hl; omega)
          (by omega), hw]
    | succ j =>
      simp only [restoreMem, List.getElem_cons_succ]
      rw [show p - 32 * (j + 1) = p - 32 - 32 * j by omega]
      exact restoreMem_getElem ws (by rw [h2]; exact hc) (by omega) (by omega) j (by omega)

/-- **The frame comes back**: restoring, from the top slot `lo + 32 (n - 1)`, the words a save
chain pushed from `W` makes the frame words read as `W`'s. -/
theorem restoreMem_frameWords {c lo n : Nat} {M W : Mem} (hc : c + 32 ≤ M.size)
    (hreg : lo + 32 * n ≤ c) :
    Words (restoreMem c M (lo + 32 * (n - 1)) (frameWords W lo n).reverse) (frameSlots W lo n) := by
  intro o v hm
  simp only [frameSlots, List.mem_map, List.mem_range, Prod.mk.injEq] at hm
  obtain ⟨i, hi, rfl, rfl⟩ := hm
  have hsz := restoreMem_size (c := c) (M := M) (p := lo + 32 * (n - 1))
    (frameWords W lo n).reverse hc (by omega)
  refine ⟨by rw [hsz]; omega, ?_⟩
  have hl : (frameWords W lo n).reverse.length = n := by
    rw [List.length_reverse, length_frameWords]
  have h := restoreMem_getElem (c := c) (M := M) (p := lo + 32 * (n - 1))
    (frameWords W lo n).reverse hc (by omega) (by rw [hl]; omega) (n - 1 - i) (by rw [hl]; omega)
  rw [show lo + 32 * (n - 1) - 32 * (n - 1 - i) = lo + 32 * i by omega] at h
  rw [h, List.getElem_reverse]
  simp only [frameWords, List.getElem_map, List.getElem_range]
  congr 2
  simp only [List.length_map, List.length_range]
  omega

/-- Carried words off the counter survive a save chain. -/
theorem Words.saveMem {M : Mem} {L : List (Nat × B256)} {c lo : Nat} (h : Words M L)
    (hout : ∀ o v, (o, v) ∈ L → o + 32 ≤ c ∨ c + 32 ≤ o) (n : Nat) :
    Words (_root_.Blanc.Lift.saveMem M c lo n) L :=
  h.agree (saveMem_agree M c lo n) hout

/-- Carried words below the restored frame or above the counter survive a restore chain. -/
theorem Words.restoreMem {M : Mem} {L : List (Nat × B256)} {c p : Nat} {ws : List B256}
    (h : Words M L) (hp : p + 32 ≤ c)
    (hout : ∀ o v, (o, v) ∈ L → o + 32 ≤ p + 32 - 32 * ws.length ∨ c + 32 ≤ o) :
    Words (_root_.Blanc.Lift.restoreMem c M p ws) L :=
  h.agree (restoreMem_agree ws hp) hout

/-! ## The chains, inverted -/

section InvChain

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {r : Seg} {t : FrameLoopTpl} {exitT : SFunc}

theorem FrameLoopTpl.c_lt (t : FrameLoopTpl) : t.c < 2 ^ 256 := B256.toNat_lt _

/-- The back edge into the next copy, inverted. -/
theorem ric_frameLoopNext {h0 h1 : UInt8} {k : Nat} {g : SFunc} {G : Nat} (hkC : k ∉ C)
    (hk : fs[k]? = some g)
    (run : SFunc.RunCut fs sevm C (St b S M G) (frameLoopNext h0 h1 k) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b S M G') g r := by
  unfold frameLoopNext at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  exact ric_jump hkC hk run

private theorem ric_frameSave_aux {lo : Nat} (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size)
    (hctr : memWord M t.c = Nat.toB256 lo) :
    ∀ (ks : List Nat) (i G : Nat), FrameSaveChain fs t exitT ks → (∀ k ∈ ks, k ∉ C) →
      lo + 32 * (i + ks.length + 1) ≤ t.c →
      SFunc.RunCut fs sevm C (St b ((frameWords M lo i).reverse ++ S) (saveMem M t.c lo i) G)
        (t.saveTree exitT ks) r →
      ∃ G', SFunc.RunCut fs sevm C (St b ((frameWords M lo (i + ks.length + 1)).reverse ++ S)
        (saveMem M t.c lo (i + ks.length + 1)) G') exitT r := by
  intro ks
  induction ks with
  | nil =>
    intro i G _ _ hreg run
    have hc := t.c_lt
    simp only [List.length_nil, Nat.add_zero] at hreg ⊢
    obtain ⟨G', run | run⟩ := ric_frameSaveIter (p := lo + 32 * i) (c := t.c) rfl
      (by rw [saveMem_size hcs]; exact hsz) (by rw [saveMem_size hcs]; exact hcs)
      (by rw [saveMem_size hcs]; omega) (by omega) (saveMem_ctr hctr i) run
    · exact (ric_undefined run).elim
    · refine ⟨G', ?_⟩
      rw [saveMem_word (by omega) (by omega) i] at run
      rw [frameWords_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons_append]
      simpa only [saveMem, show lo + 32 * i + 32 = lo + 32 * (i + 1) by omega] using run
  | cons k ks ih =>
    intro i G hch hC hreg run
    have hc := t.c_lt
    obtain ⟨hk, hch⟩ := hch.cons
    simp only [List.length_cons] at hreg ⊢
    obtain ⟨G', run | run⟩ := ric_frameSaveIter (p := lo + 32 * i) (c := t.c) rfl
      (by rw [saveMem_size hcs]; exact hsz) (by rw [saveMem_size hcs]; exact hcs)
      (by rw [saveMem_size hcs]; omega) (by omega) (saveMem_ctr hctr i) run
    · obtain ⟨G'', run⟩ := ric_frameLoopNext (hC k List.mem_cons_self) hk run
      rw [saveMem_word (by omega) (by omega) i] at run
      have run' : SFunc.RunCut fs sevm C (St b ((frameWords M lo (i + 1)).reverse ++ S)
          (saveMem M t.c lo (i + 1)) G'') (t.saveTree exitT ks) r := by
        rw [frameWords_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.cons_append]
        simpa only [saveMem, show lo + 32 * i + 32 = lo + 32 * (i + 1) by omega] using run
      obtain ⟨G3, h⟩ := ih (i + 1) G'' hch (fun k' hk' => hC k' (List.mem_cons_of_mem _ hk'))
        (by omega) run'
      exact ⟨G3, by simpa only [show i + 1 + ks.length + 1 = i + (ks.length + 1) + 1 by omega]
        using h⟩
    · exact (ric_undefined run).elim

/-- **A save chain, inverted.**  A cut run of the first iteration (`t.saveTree exitT ks`, the
remaining copies `ks` forming a `FrameSaveChain`) from a memory whose counter word at `t.c`
holds `lo`, with the frame `[lo, lo + 32 n)` (`n = |ks| + 1`) below the counter, goes on as a
cut run of `exitT` with the `n` frame words pushed (lowest deepest) and the counter at
`lo + 32 n`. -/
theorem ric_frameSave_chain {ks : List Nat} {lo G : Nat} (hchain : FrameSaveChain fs t exitT ks)
    (hC : ∀ k ∈ ks, k ∉ C) (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size)
    (hctr : memWord M t.c = Nat.toB256 lo) (hreg : lo + 32 * (ks.length + 1) ≤ t.c)
    (run : SFunc.RunCut fs sevm C (St b S M G) (t.saveTree exitT ks) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b ((frameWords M lo (ks.length + 1)).reverse ++ S)
      (saveMem M t.c lo (ks.length + 1)) G') exitT r := by
  have h := ric_frameSave_aux hsz hcs hctr ks 0 G hchain hC (by omega) (by simpa only
    [frameWords, List.range_zero, List.map_nil, List.reverse_nil, List.nil_append, saveMem]
    using run)
  simpa only [Nat.zero_add] using h

private theorem ric_frameRestore_aux {lo : Nat} (hlo : 32 ≤ lo) :
    ∀ (ks : List Nat) (M : Mem) (ts : List B256) (G : Nat), FrameRestoreChain fs t exitT ks →
      (∀ k ∈ ks, k ∉ C) → ts.length = ks.length + 1 → M.size % 32 = 0 → t.c + 32 ≤ M.size →
      lo + 32 * (ks.length + 1) ≤ t.c → memWord M t.c = Nat.toB256 (lo + 32 * ks.length) →
      SFunc.RunCut fs sevm C (St b (ts ++ S) M G) (t.restoreTree exitT ks) r →
      ∃ G', SFunc.RunCut fs sevm C
        (St b S (restoreMem t.c M (lo + 32 * ks.length) ts) G') exitT r := by
  intro ks
  induction ks with
  | nil =>
    intro M ts G _ _ hts hsz hcs hreg hctr run
    rcases ts with _ | ⟨w, _ | ⟨w', ts⟩⟩
    · simp only [List.length_nil] at hts; omega
    swap
    · simp only [List.length_nil, List.length_cons] at hts; omega
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hreg hctr ⊢
    obtain ⟨G', run | run⟩ := ric_frameRestoreIter (p := lo) (c := t.c) rfl hsz hcs (by omega) hlo hctr run
    · exact (ric_undefined run).elim
    · exact ⟨G', run⟩
  | cons k ks ih =>
    intro M ts G hch hC hts hsz hcs hreg hctr run
    obtain ⟨hk, hch⟩ := hch.cons
    obtain ⟨w, ts, rfl⟩ : ∃ w ts', ts = w :: ts' := by
      rcases ts with _ | ⟨w, ts⟩
      · simp only [List.length_nil, List.length_cons] at hts; omega
      · exact ⟨w, ts, rfl⟩
    simp only [List.length_cons] at hts hreg hctr ⊢
    have hp32 : lo + 32 * (ks.length + 1) - 32 = lo + 32 * ks.length := by omega
    obtain ⟨G', run | run⟩ := ric_frameRestoreIter (p := lo + 32 * (ks.length + 1)) (c := t.c) rfl hsz hcs
      (by omega) (by omega) hctr run
    · obtain ⟨G'', run⟩ := ric_frameLoopNext (hC k List.mem_cons_self) hk run
      rw [hp32] at run
      have h1 : (M.write (lo + 32 * (ks.length + 1)) w.toBytes).size = M.size :=
        Mem.size_write_word_of_add_le (by omega)
      have h2 : ((M.write (lo + 32 * (ks.length + 1)) w.toBytes).write t.c
          (Nat.toB256 (lo + 32 * ks.length)).toBytes).size = M.size := by
        rw [Mem.size_write_word_of_add_le (by rw [h1]; exact hcs), h1]
      obtain ⟨G3, h⟩ := ih _ ts G'' hch (fun k' hk' => hC k' (List.mem_cons_of_mem _ hk'))
        (by omega) (by rw [h2]; exact hsz) (by rw [h2]; exact hcs) (by omega)
        (Mem.memWord_write_word _ _ _).1 run
      exact ⟨G3, by simpa only [restoreMem, hp32] using h⟩
    · exact (ric_undefined run).elim

/-- **A restore chain, inverted.**  A cut run of the first iteration (`t.restoreTree exitT ks`,
`ks` a `FrameRestoreChain`) from a stack `ts ++ S` with `|ts| = n = |ks| + 1` and the counter
word at `t.c` holding the top slot `lo + 32 (n - 1)` goes on as a cut run of `exitT` over `S`,
the words `ts` written down from the top slot (`restoreMem`; see `restoreMem_frameWords`). -/
theorem ric_frameRestore_chain {ks : List Nat} {lo G : Nat} {ts : List B256}
    (hchain : FrameRestoreChain fs t exitT ks) (hC : ∀ k ∈ ks, k ∉ C)
    (hts : ts.length = ks.length + 1) (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size)
    (hlo : 32 ≤ lo) (hreg : lo + 32 * (ks.length + 1) ≤ t.c)
    (hctr : memWord M t.c = Nat.toB256 (lo + 32 * ks.length))
    (run : SFunc.RunCut fs sevm C (St b (ts ++ S) M G) (t.restoreTree exitT ks) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b S (restoreMem t.c M (lo + 32 * ks.length) ts) G') exitT r :=
  ric_frameRestore_aux hlo ks M ts G hchain hC hts hsz hcs hreg hctr run

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

/-- One save iteration up to its `JUMPI`, forward. -/
private theorem rxc_frameSaveBody {c0 c1 e0 e1 x0 x1 : UInt8} {fall exit : SFunc} {p c : Nat}
    (hc : (Bytes.toB256 [c0, c1]).toNat = c) (hsz : M.size % 32 = 0) (hcs : c + 32 ≤ M.size)
    (hps : p + 32 ≤ M.size) (hp : p + 32 < 2 ^ 256) (hctr : memWord M c = Nat.toB256 p)
    (hroom : S.length + 4 < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b (Bytes.toB256 [x0, x1] ::
        B256.eqCheck (B256.ltCheck (Nat.toB256 (p + 32)) (Bytes.toB256 [e0, e1])) 0 ::
        memWord M p :: S) (M.write c (Nat.toB256 (p + 32)).toBytes) G) (.branch fall exit) r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 46))
      (frameSaveIter c0 c1 e0 e1 x0 x1 fall exit) r := by
  subst hc
  have hpn : (Nat.toB256 p).toNat = p := B256.toNat_toB256_of_lt (by omega)
  have hM1 := Mem.size_write_word_of_add_le (v := Nat.toB256 (p + 32)) hcs
  have hsz1 : (M.write (Bytes.toB256 [c0, c1]).toNat (Nat.toB256 (p + 32)).toBytes).size % 32 = 0 := by
    rw [hM1]; exact hsz
  have hcs1 : (Bytes.toB256 [c0, c1]).toNat + 32 ≤
      (M.write (Bytes.toB256 [c0, c1]).toNat (Nat.toB256 (p + 32)).toBytes).size := by
    rw [hM1]; exact hcs
  unfold frameSaveIter
  refine rxc_dest ?_
  refine rxc_push rfl (by omega) ?_
  refine rxc_mload (c := 3) (mload_covered_cost' hsz hcs) hctr (read_covered rfl hsz hcs)
    (by omega) ?_
  refine rxc_mload (c := 3) (v := memWord M p) (mload_covered_cost' hsz (by rw [hpn]; exact hps))
    (by rw [hpn]; rfl) (by rw [hpn]; exact read_covered rfl hsz hps) (by omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (mload_covered_cost' hsz hcs) hctr (read_covered rfl hsz hcs)
    (by simp only [List.length_cons]; omega) ?_
  refine rxc_add (by simp only [List.length_cons]; omega) ?_
  rw [toB256_add_0x20 hp]
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mstore (c := 3) (mstore_covered_cost' hsz hcs) rfl ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (mload_covered_cost' hsz1 hcs1) (Mem.memWord_write_word _ _ _).1
    (read_covered rfl hsz1 hcs1) (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero rfl (by simp only [List.length_cons]; omega) ?_
  exact rxc_push rfl (by simp only [List.length_cons]; omega) kk

/-- **A save iteration that continues**, forward: the counter `p + 32` is still below the
bound. -/
theorem rxc_frameSaveIter_next {c0 c1 e0 e1 x0 x1 : UInt8} {fall exit : SFunc} {p c : Nat}
    (hc : (Bytes.toB256 [c0, c1]).toNat = c) (hsz : M.size % 32 = 0) (hcs : c + 32 ≤ M.size)
    (hps : p + 32 ≤ M.size) (hp : p + 32 < 2 ^ 256) (hctr : memWord M c = Nat.toB256 p)
    (hroom : S.length + 4 < 1024) (hlt : p + 32 < (Bytes.toB256 [e0, e1]).toNat)
    (kk : SFunc.RunExactCut fs sevm C (St b (memWord M p :: S)
      (M.write c (Nat.toB256 (p + 32)).toBytes) G) fall r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 56))
      (frameSaveIter c0 c1 e0 e1 x0 x1 fall exit) r := by
  refine rxc_frameSaveBody hc hsz hcs hps hp hctr hroom ?_
  have hl : B256.ltCheck (Nat.toB256 (p + 32)) (Bytes.toB256 [e0, e1]) = 1 := by
    have h : Nat.toB256 (p + 32) < Bytes.toB256 [e0, e1] := by
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hp]; exact hlt
    simp only [B256.ltCheck, h, ↓reduceIte]
  rw [hl, show B256.eqCheck 1 0 = 0 by decide]
  exact rxc_branch_zero kk

/-- **The last save iteration**, forward: the counter `p + 32` reached the bound. -/
theorem rxc_frameSaveIter_last {c0 c1 e0 e1 x0 x1 : UInt8} {fall exit : SFunc} {p c : Nat}
    (hc : (Bytes.toB256 [c0, c1]).toNat = c) (hsz : M.size % 32 = 0) (hcs : c + 32 ≤ M.size)
    (hps : p + 32 ≤ M.size) (hp : p + 32 < 2 ^ 256) (hctr : memWord M c = Nat.toB256 p)
    (hroom : S.length + 4 < 1024) (hge : (Bytes.toB256 [e0, e1]).toNat ≤ p + 32)
    (kk : SFunc.RunExactCut fs sevm C (St b (memWord M p :: S)
      (M.write c (Nat.toB256 (p + 32)).toBytes) G) exit r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 56))
      (frameSaveIter c0 c1 e0 e1 x0 x1 fall exit) r := by
  refine rxc_frameSaveBody hc hsz hcs hps hp hctr hroom ?_
  have hl : B256.ltCheck (Nat.toB256 (p + 32)) (Bytes.toB256 [e0, e1]) = 0 := by
    have h : ¬ Nat.toB256 (p + 32) < Bytes.toB256 [e0, e1] := by
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hp]; omega
    simp only [B256.ltCheck, h, ↓reduceIte]
  rw [hl, show B256.eqCheck 0 0 = 1 by decide]
  exact rxc_branch_succ (by decide) kk

/-- One restore iteration up to its `JUMPI`, forward. -/
private theorem rxc_frameRestoreBody {c0 c1 l0 l1 x0 x1 : UInt8} {fall exit : SFunc} {p c : Nat}
    {w : B256} (hc : (Bytes.toB256 [c0, c1]).toNat = c) (hsz : M.size % 32 = 0)
    (hcs : c + 32 ≤ M.size) (hpc : p + 32 ≤ c) (h32 : 32 ≤ p) (hctr : memWord M c = Nat.toB256 p)
    (hroom : S.length + 4 < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b (Bytes.toB256 [x0, x1] ::
        B256.eqCheck (B256.eqCheck (B256.ltCheck (Nat.toB256 (p - 32)) (Bytes.toB256 [l0, l1]))
          0) 0 :: S)
        ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes) G) (.branch fall exit) r) :
    SFunc.RunExactCut fs sevm C (St b (w :: S) M (G + 49))
      (frameRestoreIter c0 c1 l0 l1 x0 x1 fall exit) r := by
  subst hc
  have hcb : (Bytes.toB256 [c0, c1]).toNat < 2 ^ 256 := B256.toNat_lt _
  have hpn : (Nat.toB256 p).toNat = p := B256.toNat_toB256_of_lt (by omega)
  have hM1 : (M.write p w.toBytes).size = M.size := Mem.size_write_word_of_add_le (by omega)
  have hsz1 : (M.write p w.toBytes).size % 32 = 0 := by rw [hM1]; exact hsz
  have hcs1 : (Bytes.toB256 [c0, c1]).toNat + 32 ≤ (M.write p w.toBytes).size := by
    rw [hM1]; exact hcs
  have hctr1 : memWord (M.write p w.toBytes) (Bytes.toB256 [c0, c1]).toNat = Nat.toB256 p := by
    rw [memWord_write_of_disjoint hcs (by rw [B256.length_toBytes]; omega), hctr]
  have hM2 := Mem.size_write_word_of_add_le (M := M.write p w.toBytes) (v := Nat.toB256 (p - 32))
    hcs1
  have hsz2 : ((M.write p w.toBytes).write (Bytes.toB256 [c0, c1]).toNat
      (Nat.toB256 (p - 32)).toBytes).size % 32 = 0 := by rw [hM2]; exact hsz1
  have hcs2 : (Bytes.toB256 [c0, c1]).toNat + 32 ≤ ((M.write p w.toBytes).write
      (Bytes.toB256 [c0, c1]).toNat (Nat.toB256 (p - 32)).toBytes).size := by rw [hM2]; exact hcs1
  unfold frameRestoreIter
  refine rxc_dest ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (mload_covered_cost' hsz hcs) hctr (read_covered rfl hsz hcs)
    (by simp only [List.length_cons]; omega) ?_
  refine rxc_mstore (c := 3) (mstore_covered_cost' hsz (by rw [hpn]; omega)) (by rw [hpn]) ?_
  refine rxc_push rfl (by omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (mload_covered_cost' hsz1 hcs1) hctr1 (read_covered rfl hsz1 hcs1)
    (by simp only [List.length_cons]; omega) ?_
  refine rxc_sub' (toB256_sub_0x20 h32 (by omega)) (by omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mstore (c := 3) (mstore_covered_cost' hsz1 hcs1) rfl ?_
  refine rxc_push rfl (by omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_mload (c := 3) (mload_covered_cost' hsz2 hcs2) (Mem.memWord_write_word _ _ _).1
    (read_covered rfl hsz2 hcs2) (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt rfl (by omega) ?_
  refine rxc_iszero rfl (by omega) ?_
  refine rxc_iszero rfl (by omega) ?_
  exact rxc_push rfl (by simp only [List.length_cons]; omega) kk

/-- **A restore iteration that continues**, forward: the counter `p - 32` is not below `lo`. -/
theorem rxc_frameRestoreIter_next {c0 c1 l0 l1 x0 x1 : UInt8} {fall exit : SFunc} {p c : Nat}
    {w : B256} (hc : (Bytes.toB256 [c0, c1]).toNat = c) (hsz : M.size % 32 = 0)
    (hcs : c + 32 ≤ M.size) (hpc : p + 32 ≤ c) (h32 : 32 ≤ p) (hctr : memWord M c = Nat.toB256 p)
    (hroom : S.length + 4 < 1024) (hge : (Bytes.toB256 [l0, l1]).toNat ≤ p - 32)
    (kk : SFunc.RunExactCut fs sevm C (St b S
      ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes) G) fall r) :
    SFunc.RunExactCut fs sevm C (St b (w :: S) M (G + 59))
      (frameRestoreIter c0 c1 l0 l1 x0 x1 fall exit) r := by
  refine rxc_frameRestoreBody hc hsz hcs hpc h32 hctr hroom ?_
  have hl : B256.ltCheck (Nat.toB256 (p - 32)) (Bytes.toB256 [l0, l1]) = 0 := by
    have hcb := B256.toNat_lt (Bytes.toB256 [c0, c1])
    have h : ¬ Nat.toB256 (p - 32) < Bytes.toB256 [l0, l1] := by
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)]; omega
    simp only [B256.ltCheck, h, ↓reduceIte]
  rw [hl, show B256.eqCheck (B256.eqCheck 0 0) 0 = 0 by decide]
  exact rxc_branch_zero kk

/-- **The last restore iteration**, forward: the counter `p - 32` fell below `lo`. -/
theorem rxc_frameRestoreIter_last {c0 c1 l0 l1 x0 x1 : UInt8} {fall exit : SFunc} {p c : Nat}
    {w : B256} (hc : (Bytes.toB256 [c0, c1]).toNat = c) (hsz : M.size % 32 = 0)
    (hcs : c + 32 ≤ M.size) (hpc : p + 32 ≤ c) (h32 : 32 ≤ p) (hctr : memWord M c = Nat.toB256 p)
    (hroom : S.length + 4 < 1024) (hlt : p - 32 < (Bytes.toB256 [l0, l1]).toNat)
    (kk : SFunc.RunExactCut fs sevm C (St b S
      ((M.write p w.toBytes).write c (Nat.toB256 (p - 32)).toBytes) G) exit r) :
    SFunc.RunExactCut fs sevm C (St b (w :: S) M (G + 59))
      (frameRestoreIter c0 c1 l0 l1 x0 x1 fall exit) r := by
  refine rxc_frameRestoreBody hc hsz hcs hpc h32 hctr hroom ?_
  have hl : B256.ltCheck (Nat.toB256 (p - 32)) (Bytes.toB256 [l0, l1]) = 1 := by
    have hcb := B256.toNat_lt (Bytes.toB256 [c0, c1])
    have h : Nat.toB256 (p - 32) < Bytes.toB256 [l0, l1] := by
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)]; exact hlt
    simp only [B256.ltCheck, h, ↓reduceIte]
  rw [hl, show B256.eqCheck (B256.eqCheck 1 0) 0 = 1 by decide]
  exact rxc_branch_succ (by decide) kk

/-- The back edge into the next copy, forward. -/
theorem rxc_frameLoopNext {h0 h1 : UInt8} {k : Nat} {g : SFunc} (hk : fs[k]? = some g)
    (hkC : k ∉ C) (hroom : S.length < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b S M G) g r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 11)) (frameLoopNext h0 h1 k) r := by
  unfold frameLoopNext
  exact rxc_push rfl hroom (rxc_jump hk hkC kk)

end Fwd

/-! ## The chains, forward -/

section FwdChain

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {r : Seg} {t : FrameLoopTpl} {exitT : SFunc}

private theorem rxc_frameSave_aux {lo : Nat} (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size)
    (hctr : memWord M t.c = Nat.toB256 lo) :
    ∀ (ks : List Nat) (i G : Nat), FrameSaveChain fs t exitT ks → (∀ k ∈ ks, k ∉ C) →
      lo + 32 * (i + ks.length + 1) ≤ t.c → t.e = lo + 32 * (i + ks.length + 1) →
      S.length + i + ks.length + 5 < 1024 →
      SFunc.RunExactCut fs sevm C (St b ((frameWords M lo (i + ks.length + 1)).reverse ++ S)
        (saveMem M t.c lo (i + ks.length + 1)) G) exitT r →
      SFunc.RunExactCut fs sevm C (St b ((frameWords M lo i).reverse ++ S) (saveMem M t.c lo i)
        (G + 67 * ks.length + 56)) (t.saveTree exitT ks) r := by
  intro ks
  induction ks with
  | nil =>
    intro i G _ _ hreg he hroom kk
    have hc := t.c_lt
    have he' : (Bytes.toB256 [t.e0, t.e1]).toNat = lo + 32 * (i + 1) := he
    simp only [List.length_nil, Nat.add_zero, Nat.mul_zero] at hreg he' hroom kk ⊢
    refine rxc_frameSaveIter_last (p := lo + 32 * i) (c := t.c) rfl
      (by rw [saveMem_size hcs]; exact hsz) (by rw [saveMem_size hcs]; exact hcs)
      (by rw [saveMem_size hcs]; omega) (by omega) (saveMem_ctr hctr i)
      (by rw [List.length_append, List.length_reverse, length_frameWords]; omega) (by omega) ?_
    rw [saveMem_word (by omega) (by omega) i]
    rw [frameWords_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.cons_append] at kk
    simpa only [saveMem, show lo + 32 * (i + 1) = lo + 32 * i + 32 by omega] using kk
  | cons k ks ih =>
    intro i G hch hC hreg he hroom kk
    have hc := t.c_lt
    obtain ⟨hk, hch⟩ := hch.cons
    have he' : (Bytes.toB256 [t.e0, t.e1]).toNat = lo + 32 * (i + (ks.length + 1) + 1) := he
    simp only [List.length_cons] at hreg he hroom kk ⊢
    have kk' : SFunc.RunExactCut fs sevm C
        (St b ((frameWords M lo (i + 1 + ks.length + 1)).reverse ++ S)
        (saveMem M t.c lo (i + 1 + ks.length + 1)) G) exitT r := by
      simpa only [show i + 1 + ks.length + 1 = i + (ks.length + 1) + 1 by omega] using kk
    have hnext := ih (i + 1) G hch (fun k' hk' => hC k' (List.mem_cons_of_mem _ hk')) (by omega)
      (by omega) (by omega) kk'
    rw [show G + 67 * (ks.length + 1) + 56 = G + 67 * ks.length + 56 + 11 + 56 by omega]
    refine rxc_frameSaveIter_next (p := lo + 32 * i) (c := t.c) rfl
      (by rw [saveMem_size hcs]; exact hsz) (by rw [saveMem_size hcs]; exact hcs)
      (by rw [saveMem_size hcs]; omega) (by omega) (saveMem_ctr hctr i)
      (by rw [List.length_append, List.length_reverse, length_frameWords]; omega) (by omega) ?_
    refine rxc_frameLoopNext hk (hC k List.mem_cons_self)
      (by rw [List.length_cons, List.length_append, List.length_reverse, length_frameWords]; omega) ?_
    rw [saveMem_word (by omega) (by omega) i]
    rw [frameWords_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.cons_append] at hnext
    simpa only [saveMem, show lo + 32 * (i + 1) = lo + 32 * i + 32 by omega] using hnext

/-- **A save chain, forward**: with the counter at `lo`, the bound `t.e = lo + 32 n`
(`n = |ks| + 1`), an exact run of `exitT` with the `n` frame words pushed and the counter at
`lo + 32 n` makes an exact run of the first iteration, at cost `67 (n - 1) + 56`. -/
theorem rxc_frameSave_chain {ks : List Nat} {lo G : Nat} (hchain : FrameSaveChain fs t exitT ks)
    (hC : ∀ k ∈ ks, k ∉ C) (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size)
    (hctr : memWord M t.c = Nat.toB256 lo) (hreg : lo + 32 * (ks.length + 1) ≤ t.c)
    (he : t.e = lo + 32 * (ks.length + 1)) (hroom : S.length + ks.length + 5 < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b ((frameWords M lo (ks.length + 1)).reverse ++ S)
      (saveMem M t.c lo (ks.length + 1)) G) exitT r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 67 * ks.length + 56)) (t.saveTree exitT ks) r := by
  have h := rxc_frameSave_aux hsz hcs hctr ks 0 G hchain hC (by omega) (by omega) (by omega)
    (by simpa only [Nat.zero_add] using kk)
  simpa only [frameWords, List.range_zero, List.map_nil, List.reverse_nil, List.nil_append,
    saveMem] using h

private theorem rxc_frameRestore_aux {lo : Nat} (hlo : 32 ≤ lo) (hlt : t.e = lo) :
    ∀ (ks : List Nat) (M : Mem) (ts : List B256) (G : Nat), FrameRestoreChain fs t exitT ks →
      (∀ k ∈ ks, k ∉ C) → ts.length = ks.length + 1 → M.size % 32 = 0 → t.c + 32 ≤ M.size →
      lo + 32 * (ks.length + 1) ≤ t.c → memWord M t.c = Nat.toB256 (lo + 32 * ks.length) →
      S.length + ks.length + 5 < 1024 →
      SFunc.RunExactCut fs sevm C
        (St b S (restoreMem t.c M (lo + 32 * ks.length) ts) G) exitT r →
      SFunc.RunExactCut fs sevm C (St b (ts ++ S) M (G + 70 * ks.length + 59))
        (t.restoreTree exitT ks) r := by
  have he' : (Bytes.toB256 [t.e0, t.e1]).toNat = lo := hlt
  intro ks
  induction ks with
  | nil =>
    intro M ts G _ _ hts hsz hcs hreg hctr hroom kk
    rcases ts with _ | ⟨w, _ | ⟨w', ts⟩⟩
    · simp only [List.length_nil] at hts; omega
    swap
    · simp only [List.length_nil, List.length_cons] at hts; omega
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hreg hctr kk hroom ⊢
    exact rxc_frameRestoreIter_last (p := lo) (c := t.c) rfl hsz hcs (by omega) hlo hctr
      (by simp only [List.append_eq, List.nil_append]; omega) (by omega) kk
  | cons k ks ih =>
    intro M ts G hch hC hts hsz hcs hreg hctr hroom kk
    obtain ⟨hk, hch⟩ := hch.cons
    rcases ts with _ | ⟨w, ts⟩
    · simp only [List.length_nil, List.length_cons] at hts; omega
    simp only [List.length_cons] at hts hreg hctr kk hroom ⊢
    have hp32 : lo + 32 * (ks.length + 1) - 32 = lo + 32 * ks.length := by omega
    have h1 : (M.write (lo + 32 * (ks.length + 1)) w.toBytes).size = M.size :=
      Mem.size_write_word_of_add_le (by omega)
    have h2 : ((M.write (lo + 32 * (ks.length + 1)) w.toBytes).write t.c
        (Nat.toB256 (lo + 32 * ks.length)).toBytes).size = M.size := by
      rw [Mem.size_write_word_of_add_le (by rw [h1]; exact hcs), h1]
    have hnext := ih _ ts G hch (fun k' hk' => hC k' (List.mem_cons_of_mem _ hk')) (by omega)
      (by rw [h2]; exact hsz) (by rw [h2]; exact hcs) (by omega)
      (Mem.memWord_write_word _ _ _).1 (by omega) (by simpa only [restoreMem, hp32] using kk)
    rw [show G + 70 * (ks.length + 1) + 59 = G + 70 * ks.length + 59 + 11 + 59 by omega]
    refine rxc_frameRestoreIter_next (p := lo + 32 * (ks.length + 1)) (c := t.c) rfl hsz hcs
      (by omega) (by omega) hctr (by simp only [List.append_eq, List.length_append]; omega)
      (by omega) ?_
    refine rxc_frameLoopNext hk (hC k List.mem_cons_self)
      (by simp only [List.append_eq, List.length_append]; omega) ?_
    exact hnext

/-- **A restore chain, forward**: with `|ts| = n = |ks| + 1`, the counter at the top slot
`lo + 32 (n - 1)` and the bound `t.e = lo`, an exact run of `exitT` over `S` with the words
`ts` written back (`restoreMem`) makes an exact run of the first iteration, at cost
`70 (n - 1) + 59`. -/
theorem rxc_frameRestore_chain {ks : List Nat} {lo G : Nat} {ts : List B256}
    (hchain : FrameRestoreChain fs t exitT ks) (hC : ∀ k ∈ ks, k ∉ C)
    (hts : ts.length = ks.length + 1) (hsz : M.size % 32 = 0) (hcs : t.c + 32 ≤ M.size)
    (hlo : 32 ≤ lo) (he : t.e = lo) (hreg : lo + 32 * (ks.length + 1) ≤ t.c)
    (hctr : memWord M t.c = Nat.toB256 (lo + 32 * ks.length))
    (hroom : S.length + ks.length + 5 < 1024)
    (kk : SFunc.RunExactCut fs sevm C
      (St b S (restoreMem t.c M (lo + 32 * ks.length) ts) G) exitT r) :
    SFunc.RunExactCut fs sevm C (St b (ts ++ S) M (G + 70 * ks.length + 59))
      (t.restoreTree exitT ks) r :=
  rxc_frameRestore_aux hlo he ks M ts G hchain hC hts hsz hcs hreg hctr hroom kk

end FwdChain

end Blanc.Lift
