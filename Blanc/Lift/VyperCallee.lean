import Blanc.Lift.VyperFrameLoop
import Blanc.Lift.MemGlue
import Blanc.Lift.WalkSteps
import Blanc.Lift.StableSwapNewton.Defs
import Blanc.ForwardStorageAccess

/-!
# Walking Vyper 0.2.x internal callees: memory windows and checked arithmetic

A Vyper 0.2.x internal function keeps its frame in a fixed memory window (and the scratch words
at `0` and `0xc0`), and checks its `uint256` arithmetic with fixed instruction patterns.  This
module gives a callee walk the vocabulary to state and prove its value contract without tracking
concrete memory terms:

* windows are `Mem.KeepsOff M M' W` of `Blanc/Lift/MemGlue.lean`; `Mem.KeepsOff.extend`,
  `.write_word` (a store inside a window, `coversWord`) and `.agreeOutside` add to it;
* `MemTrack M₀ M W L`: the walk's memory `M` is well formed, keeps `M₀` off `W` and carries the
  words `L`.  `ric_mloadT` / `ric_mstoreT` / `ric_mstoreO` / `ric_keccakT` step it through
  `MLOAD`, `MSTORE` (fresh or overwriting) and `KECCAK256` of carried words.
* `SloadsOnly sevm b B`: the base `B` is `b` after selected storage loads (`afterSload`), so
  state, storage, logs and output are `b`'s (`SloadsOnly.state`, `.getStor`, `.logs`,
  `.output`).
* The checked-arithmetic guards, read back as the checked operations on naturals of
  `Blanc/Lift/StableSwapNewton/Defs.lean`: `vyChkSub` (`ISZERO (LT x y)`), `vyChkAdd`
  (`ISZERO (LT (x + y) x)`), `vyChkMul` (`ISZERO x OR (x * y) / x == y`) and `vyChkDiv`
  (nonzero divisor); `ltCheck_iszero_ne`/`ltCheck_iszero_eq` and the `GT` forms read branch
  conditions.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune
open Blanc.StableSwapNewton

/-! ## Memory windows

`Mem.KeepsOff M M' W` (`Blanc/Lift/MemGlue.lean`): `M'` is no smaller and reads as `M` off the
half-open windows `W`. -/

/-- A window list given as a literal covers the word at `o`. -/
def coversWord (W : List (Nat × Nat)) (o : Nat) : Bool :=
  W.any fun w => decide (w.1 ≤ o) && decide (o + 32 ≤ w.2)

theorem not_offWindows_of_covers {W : List (Nat × Nat)} {o j : Nat} (hW : coversWord W o = true)
    (h1 : o ≤ j) (h2 : j < o + 32) : ¬ Mem.OffWindows W j := by
  intro hoff
  obtain ⟨w, hw, hc⟩ := List.any_eq_true.mp hW
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have := hoff w hw
  omega

namespace Mem.KeepsOff

theorem extend (M : Mem) (i n : Nat) (W : List (Nat × Nat)) : Mem.KeepsOff M (M.extend i n) W :=
  ⟨memExtSize_ge _ _ _, fun _ _ => rfl⟩

/-- A word store inside a window, on a well-formed memory, keeps it off the windows. -/
theorem write_word {M : Mem} (hwf : Mem.Wf M) (o : Nat) (v : B256) {W : List (Nat × Nat)}
    (hW : coversWord W o = true) : Mem.KeepsOff M (M.write o v.toBytes) W := by
  have hsz := (Mem.write_agree M o v.toBytes).1
  refine ⟨hsz, fun i hi => ?_⟩
  have hr := (Mem.reads_data M).write hwf o v.toBytes
  rw [hr i, Bytes.getD_writeAt, ite_eq_right, ← Mem.reads_data M i]
  rw [B256.length_toBytes]
  exact fun h => not_offWindows_of_covers hW h.1 h.2 hi

/-- Windows inside `[lo, hi)` give `Mem.AgreeOutside`. -/
theorem agreeOutside {M M' : Mem} {W : List (Nat × Nat)} {lo hi : Nat} (h : Mem.KeepsOff M M' W)
    (hW : ∀ w ∈ W, lo ≤ w.1 ∧ w.2 ≤ hi) : Mem.AgreeOutside M M' lo hi :=
  ⟨h.1, fun i _ hout => h.2 i fun w hw => by have := hW w hw; omega⟩

end Mem.KeepsOff

/-- **The callee walk's memory**: well formed, kept off the windows `W` from the entry memory
`M₀`, carrying the words `L`. -/
structure MemTrack (M₀ M : Mem) (W : List (Nat × Nat)) (L : List (Nat × B256)) : Prop where
  keeps : Mem.KeepsOff M₀ M W
  words : Words M L
  wf : Mem.Wf M
  /-- Word alignment of the logical size is kept. -/
  aligned : M₀.size % 32 = 0 → M.size % 32 = 0

/-- A word store keeps an aligned logical size aligned. -/
theorem Mem.size_write_word_mod {N : Mem} {i : Nat} {w : B256} (h : N.size % 32 = 0) :
    (N.write i w.toBytes).size % 32 = 0 := by
  rw [Mem.size_write_word_at]
  split
  · exact h
  · unfold ceil32; split <;> omega

/-- An expansion keeps an aligned logical size aligned. -/
theorem Mem.size_extend_mod {N : Mem} (i n : Nat) (h : N.size % 32 = 0) :
    (N.extend i n).size % 32 = 0 :=
  memExtSize_mod_32 h

theorem MemTrack.init {M₀ : Mem} (hwf : Mem.Wf M₀) (W : List (Nat × Nat)) : MemTrack M₀ M₀ W [] :=
  ⟨Mem.KeepsOff.refl M₀ W, Words.nil M₀, hwf, id⟩

theorem MemTrack.sub {M₀ M : Mem} {W : List (Nat × Nat)} {L L' : List (Nat × B256)}
    (h : MemTrack M₀ M W L) (hs : L' ⊆ L) : MemTrack M₀ M W L' :=
  ⟨h.keeps, h.words.sub hs, h.wf, h.aligned⟩

theorem MemTrack.mem_size {M₀ M : Mem} {W : List (Nat × Nat)} {L : List (Nat × B256)}
    (h : MemTrack M₀ M W L) {o : Nat} {v : B256} (hm : (o, v) ∈ L) : o + 32 ≤ M.size :=
  (h.words o v hm).1

section Steps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M M₀ : Mem}
  {G : Nat} {f : SFunc} {r : Seg} {P : List (Nat × Nat)} {L : List (Nat × B256)}

/-- `MLOAD` of a carried word, inverted over a tracked memory. -/
theorem ric_mloadT {i v : B256} {o : Nat} (hT : MemTrack M₀ M P L)
    (run : SFunc.RunCut fs sevm C (St b (i :: S) M G) (.next (.reg .mload) f) r)
    (hm : (o, v) ∈ L) (hi : i.toNat = o) :
    ∃ M' G', MemTrack M₀ M' P L ∧ SFunc.RunCut fs sevm C (St b (v :: S) M' G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G1, rfl⟩ := ri_mload s1
  rw [hi] at run
  have hk := Mem.KeepsOff.extend M o 32 P
  refine ⟨_, G1, ⟨hT.keeps.trans hk, ?_, hT.wf.extend _ _,
    fun h => Mem.size_extend_mod _ _ (hT.aligned h)⟩, ?_⟩
  · intro o' v' hm'
    obtain ⟨hs, hv⟩ := hT.words o' v' hm'
    exact ⟨le_trans hs hk.1, hv⟩
  · have hv : Bytes.toB256 (M.read o 32).1 = v := hT.words.memWord hm
    rw [hv] at run
    exact run

/-- `MSTORE` of a word into a window, inverted over a tracked memory: the word is carried, and
so is every carried word it misses. -/
theorem ric_mstoreT {i v : B256} {o : Nat} (hT : MemTrack M₀ M P L)
    (run : SFunc.RunCut fs sevm C (St b (i :: v :: S) M G) (.next (.reg .mstore) f) r)
    (hi : i.toNat = o) (hP : coversWord P o = true)
    (hout : (L.map Prod.fst).all (fun p => decide (p + 32 ≤ o) || decide (o + 32 ≤ p)) = true) :
    ∃ M' G', MemTrack M₀ M' P ((o, v) :: L) ∧ SFunc.RunCut fs sevm C (St b S M' G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G1, rfl⟩ := ri_mstore s1
  rw [hi] at run
  refine ⟨_, G1, ⟨hT.keeps.trans (Mem.KeepsOff.write_word hT.wf o v hP), ?_,
    hT.wf.write _ _, fun h => Mem.size_write_word_mod (hT.aligned h)⟩, run⟩
  refine hT.words.write fun o' w hm => ?_
  have h := List.all_eq_true.mp hout o' (List.mem_map.mpr ⟨(o', w), hm, rfl⟩)
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using h

/-- The carried words a store at `o` misses. -/
def wordsOff (o : Nat) (L : List (Nat × B256)) : List (Nat × B256) :=
  L.filter fun p => decide (p.1 + 32 ≤ o) || decide (o + 32 ≤ p.1)

/-- `MSTORE` of a word into a window, inverted over a tracked memory, overwriting: the word is
carried, and so is every carried word it misses (`wordsOff`). -/
theorem ric_mstoreO {i v : B256} {o : Nat} (hT : MemTrack M₀ M P L)
    (run : SFunc.RunCut fs sevm C (St b (i :: v :: S) M G) (.next (.reg .mstore) f) r)
    (hi : i.toNat = o) (hP : coversWord P o = true) :
    ∃ M' G', MemTrack M₀ M' P ((o, v) :: wordsOff o L) ∧
      SFunc.RunCut fs sevm C (St b S M' G') f r := by
  have hT' := hT.sub (L' := wordsOff o L) (List.filter_subset_self _)
  refine ric_mstoreT hT' run hi hP ?_
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (List.mem_filter.mp hq).2

/-- `KECCAK256` of a carried word, inverted over a tracked memory: the digest of its bytes. -/
theorem ric_keccakT {i n : B256} {o : Nat} {w : B256} (hT : MemTrack M₀ M P L)
    (run : SFunc.RunCut fs sevm C (St b (i :: n :: S) M G) (.next (.reg .keccak256) f) r)
    (hm : (o, w) ∈ L) (hi : i.toNat = o) (hn : n.toNat = 32) :
    ∃ M' G', MemTrack M₀ M' P L ∧
      SFunc.RunCut fs sevm C (St b (Bytes.keccak w.toBytes :: S) M' G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G1, rfl⟩ := ri_keccak s1
  rw [hi, hn] at run
  have hk := Mem.KeepsOff.extend M o 32 P
  refine ⟨_, G1, ⟨hT.keeps.trans hk, ?_, hT.wf.extend _ _,
    fun h => Mem.size_extend_mod _ _ (hT.aligned h)⟩, ?_⟩
  · intro o' v' hm'
    obtain ⟨hs, hv⟩ := hT.words o' v' hm'
    exact ⟨le_trans hs hk.1, hv⟩
  · have hv : Bytes.toB256 (M.read o 32).1 = w := hT.words.memWord hm
    have hlen : (M.read o 32).1.length = 32 := by
      simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
    rw [← Bytes.toBytes_toB256_of_length hlen, hv] at run
    exact run

end Steps

/-! ## Forward steps

A forward callee walk proves a goal `∃ M', SFunc.RunExactCut fs sevm C d f (R M') ∧ Q M'`: the
final memory is named only at the callee's return (`rxc_retT`), where the tracked memory hands
over its facts.  `xlift` lifts every memory-free step to that shape; the memory steps are stated
in it directly.  Memory is covered (`M.size = n`, word aligned), so loads and stores cost `3` and
leave the size. -/

theorem MemTrack.writeO {M₀ M : Mem} {W : List (Nat × Nat)} {L : List (Nat × B256)} {o : Nat}
    (hT : MemTrack M₀ M W L) (v : B256) (hW : coversWord W o = true) :
    MemTrack M₀ (M.write o v.toBytes) W ((o, v) :: wordsOff o L) := by
  refine ⟨hT.keeps.trans (Mem.KeepsOff.write_word hT.wf o v hW), ?_, hT.wf.write _ _,
    fun h => Mem.size_write_word_mod (hT.aligned h)⟩
  refine (hT.words.sub (L' := wordsOff o L) (List.filter_subset_self _)).write fun o' w hm => ?_
  have h := (List.mem_filter.mp hm).2
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using h

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M M₀ : Mem}
  {G n : Nat} {f : SFunc} {W : List (Nat × Nat)} {L : List (Nat × B256)}
  {R : Mem → Seg} {Q : Mem → Prop}

/-- Lift a step that does not touch the final memory through the `∃ M'` goal. -/
theorem xlift {P P' : Mem → Prop} (h : ∀ M', P M' → P' M') (k : ∃ M', P M' ∧ Q M') :
    ∃ M', P' M' ∧ Q M' :=
  let ⟨M', hp, hq⟩ := k
  ⟨M', h M' hp, hq⟩

theorem rxc_mul {x y v : B256} {r : Seg} (hv : x * y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 5)) (.next (.reg .mul) f) r :=
  rxc_binary (fn := (· * ·)) (c := gLow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_gt {x y v : B256} {r : Seg} (hv : B256.gtCheck x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 3)) (.next (.reg .gt) f) r :=
  rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_timestamp {r : Seg} (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (sevm.benvStat.time :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 2)) (.next (.reg .timestamp) f) r :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (r := .timestamp)
    (x := sevm.benvStat.time) (G := G) (cost := gBase) (by rintro ⟨⟩) rfl rfl hroom) k

theorem rxc_branch_zeroOf {d w : B256} {g : SFunc} {r : Seg} (hw : w = 0)
    (k : SFunc.RunExactCut fs sevm C (St b S M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (d :: w :: S) M (G + 10)) (.branch f g) r := by
  subst hw; exact rxc_branch_zero k

theorem rxc_branchTo_succ {d w : B256} {g : SFunc} {j : Nat} {r : Seg} (hw : w ≠ 0)
    (hj : fs[j]? = some g) (hjC : j ∉ C)
    (k : SFunc.RunExactCut fs sevm C (St b S M G) g r) :
    SFunc.RunExactCut fs sevm C (St b (d :: w :: S) M (G + 10)) (.branchTo f j) r :=
  .toSucc d w hw hjC hj popBurnBy_St2 k

theorem rxc_swap0 {x y : B256} {r : Seg}
    (k : SFunc.RunExactCut fs sevm C (St b (y :: x :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 3)) (.next (.reg (.swap 0)) f) r :=
  rxc_swap rfl k

theorem rxc_swap1 {x y z : B256} {r : Seg}
    (k : SFunc.RunExactCut fs sevm C (St b (z :: y :: x :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: z :: S) M (G + 3)) (.next (.reg (.swap 1)) f) r :=
  rxc_swap rfl k

/-- `MLOAD` of a carried word, forward, over a covered tracked memory. -/
theorem rxc_mloadT {i v : B256} {o : Nat} {r : Seg} (hT : MemTrack M₀ M W L)
    (hS : M.size = n) (hn : n % 32 = 0) (hm : (o, v) ∈ L) (hi : i.toNat = o)
    (hroom : S.length < 1024) (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (i :: S) M (G + 3)) (.next (.reg .mload) f) r := by
  have hsz : M.size % 32 = 0 := by rw [hS]; exact hn
  have ho := hT.mem_size hm
  subst hi
  exact rxc_mload (mload_covered_cost' hsz ho) (hT.words.memWord hm) (read_covered rfl hsz ho)
    hroom k

/-- `MSTORE` into a window, forward, over a covered tracked memory (overwriting). -/
theorem rxc_mstoreT {i v : B256} {o : Nat} (hT : MemTrack M₀ M W L) (hS : M.size = n)
    (hn : n % 32 = 0) (hi : i.toNat = o) (hcov : o + 32 ≤ n) (hW : coversWord W o = true)
    (k : MemTrack M₀ (M.write o v.toBytes) W ((o, v) :: wordsOff o L) →
      (M.write o v.toBytes).size = n →
      ∃ M', SFunc.RunExactCut fs sevm C (St b S (M.write o v.toBytes) G) f (R M') ∧ Q M') :
    ∃ M', SFunc.RunExactCut fs sevm C (St b (i :: v :: S) M (G + 3)) (.next (.reg .mstore) f)
      (R M') ∧ Q M' := by
  have hsz : M.size % 32 = 0 := by rw [hS]; exact hn
  subst hi
  obtain ⟨M', run, hq⟩ := k (hT.writeO v hW)
    (by rw [Mem.size_write_word_of_add_le (by rw [hS]; exact hcov), hS])
  exact ⟨M', rxc_mstore (mstore_covered_cost' hsz (by rw [hS]; exact hcov)) rfl run, hq⟩

/-- `KECCAK256` of a carried word, forward, over a covered tracked memory (`36` gas). -/
theorem rxc_keccakT {i m w : B256} {o : Nat} {r : Seg} (hT : MemTrack M₀ M W L)
    (hS : M.size = n) (hn : n % 32 = 0) (hm : (o, w) ∈ L) (hi : i.toNat = o)
    (hm32 : m.toNat = 32) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (Bytes.keccak w.toBytes :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (i :: m :: S) M (G + 36)) (.next (.reg .keccak256) f) r := by
  have hsz : M.size % 32 = 0 := by rw [hS]; exact hn
  have ho := hT.mem_size hm
  subst hi
  have hlen : (M.read i.toNat 32).1.length = 32 := by
    simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
  have hv : (M.read i.toNat 32).1 = w.toBytes := by
    have h := hT.words.memWord hm
    unfold memWord at h
    rw [← Bytes.toBytes_toB256_of_length hlen, h]
  refine .next (Ninst.runCompiled_keccak256_of (devm := St b (i :: m :: S) M (G + 36)) (G := G)
    (c := 36) rfl ?_ ?_ ?_ rfl hroom) k
  · rw [hm32, St, Devm.extCost_zero_of_le hsz ho]
    decide
  · rw [hm32, St.memory, hv]
  · rw [hm32, St.memory]
    exact read_covered rfl hsz ho

/-- The callee's return, forward: the tracked memory's facts for the final memory. -/
theorem rxc_retT {d : B256} (hT : MemTrack M₀ M W L) (hS : M.size = n) :
    ∃ M', SFunc.RunExactCut fs sevm C (St b (d :: S) M (G + 8)) .ret
      (.done (.returned (St b S M' G))) ∧
      (Mem.KeepsOff M₀ M' W ∧ Mem.Wf M' ∧ M'.size = n) :=
  ⟨M, rxc_ret, hT.keeps, hT.wf, hS⟩

end Fwd

/-! ## Bases reached by storage loads only -/

/-- `B` is `b` after a chain of selected `SLOAD`s (`afterSload`): only the warm-key set moved. -/
inductive SloadsOnly (sevm : Sevm) (b : Devm) : Devm → Prop
  | refl : SloadsOnly sevm b b
  | sload {B : Devm} (h : SloadsOnly sevm b B) (k : B256) : SloadsOnly sevm b (afterSload sevm B k)

theorem afterSload_getStorVal (sevm : Sevm) (b : Devm) (k : B256) (a : Adr) (x : B256) :
    (afterSload sevm b k).getStorVal a x = b.getStorVal a x := by
  rw [getStorVal_eq_getStor, getStorVal_eq_getStor, afterSload_getStor]

namespace SloadsOnly

variable {sevm : Sevm} {b B : Devm}

theorem state (h : SloadsOnly sevm b B) : B.state = b.state := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [← ih]; unfold afterSload; split <;> rfl

theorem getStor (h : SloadsOnly sevm b B) (a : Adr) : B.getStor a = b.getStor a := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [afterSload_getStor, ih]

theorem logs (h : SloadsOnly sevm b B) : B.logs = b.logs := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [afterSload_logs, ih]

theorem output (h : SloadsOnly sevm b B) : B.output = b.output := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [afterSload_output, ih]

theorem trans {B' : Devm} (h : SloadsOnly sevm b B) (h' : SloadsOnly sevm B B') :
    SloadsOnly sevm b B' := by
  induction h' with
  | refl => exact h
  | sload _ k ih => exact ih.sload k

end SloadsOnly

/-! ## Checked arithmetic -/

theorem eqCheck_ne_zero {a c : B256} (h : B256.eqCheck a c ≠ 0) : a = c := by
  unfold B256.eqCheck at h; split at h
  · assumption
  · exact absurd rfl h

theorem eqCheck_zero_eq_zero {a : B256} (h : B256.eqCheck a 0 = 0) : a ≠ 0 := by
  unfold B256.eqCheck at h; split at h
  · exact absurd h (by decide)
  · assumption

theorem ltCheck_eq_zero {x y : B256} (h : B256.ltCheck x y = 0) : ¬ x.toNat < y.toNat := by
  unfold B256.ltCheck at h; split at h
  · exact absurd h (by decide)
  · rename_i hn; rwa [B256.lt_iff_toNat_lt_toNat] at hn

theorem ltCheck_ne_zero {x y : B256} (h : B256.ltCheck x y ≠ 0) : x.toNat < y.toNat := by
  unfold B256.ltCheck at h; split at h
  · rename_i hl; rwa [B256.lt_iff_toNat_lt_toNat] at hl
  · exact absurd rfl h

/-- `ISZERO (LT x y)` taken: `y ≤ x`. -/
theorem ltCheck_iszero_ne {x y : B256} (h : B256.eqCheck (B256.ltCheck x y) 0 ≠ 0) :
    ¬ x.toNat < y.toNat :=
  ltCheck_eq_zero (eqCheck_ne_zero h)

/-- `ISZERO (LT x y)` not taken: `x < y`. -/
theorem ltCheck_iszero_eq {x y : B256} (h : B256.eqCheck (B256.ltCheck x y) 0 = 0) :
    x.toNat < y.toNat :=
  ltCheck_ne_zero (eqCheck_zero_eq_zero h)

theorem gtCheck_iszero_ne {x y : B256} (h : B256.eqCheck (B256.gtCheck x y) 0 ≠ 0) :
    ¬ y.toNat < x.toNat := by
  have h' := eqCheck_ne_zero h
  unfold B256.gtCheck at h'; split at h'
  · exact absurd h' (by decide)
  · rename_i hn; rwa [gt_iff_lt, B256.lt_iff_toNat_lt_toNat] at hn

theorem gtCheck_iszero_eq {x y : B256} (h : B256.eqCheck (B256.gtCheck x y) 0 = 0) :
    y.toNat < x.toNat := by
  have h' := eqCheck_zero_eq_zero h
  unfold B256.gtCheck at h'; split at h'
  · rename_i hl; rwa [gt_iff_lt, B256.lt_iff_toNat_lt_toNat] at hl
  · exact absurd rfl h'

theorem ltCheck_iszero_of_lt {x y : B256} (h : x.toNat < y.toNat) :
    B256.eqCheck (B256.ltCheck x y) 0 = 0 := by
  unfold B256.ltCheck
  rw [ite_eq_left (B256.lt_iff_toNat_lt_toNat.mpr h)]; decide

theorem ltCheck_iszero_of_not_lt {x y : B256} (h : ¬ x.toNat < y.toNat) :
    B256.eqCheck (B256.ltCheck x y) 0 ≠ 0 := by
  unfold B256.ltCheck
  rw [ite_eq_right (fun h' => h (B256.lt_iff_toNat_lt_toNat.mp h'))]; decide

theorem gtCheck_iszero_of_lt {x y : B256} (h : y.toNat < x.toNat) :
    B256.eqCheck (B256.gtCheck x y) 0 = 0 := by
  unfold B256.gtCheck
  rw [ite_eq_left (show x > y from B256.lt_iff_toNat_lt_toNat.mpr h)]; decide

theorem gtCheck_iszero_of_not_lt {x y : B256} (h : ¬ y.toNat < x.toNat) :
    B256.eqCheck (B256.gtCheck x y) 0 ≠ 0 := by
  unfold B256.gtCheck
  rw [ite_eq_right (fun h' : x > y => h (B256.lt_iff_toNat_lt_toNat.mp h'))]; decide

/-- Vyper's checked subtraction `ISZERO (LT x y)`, read back. -/
theorem vyChkSub {x y : B256} (h : B256.eqCheck (B256.ltCheck x y) 0 ≠ 0) :
    chkSub x.toNat y.toNat = some (x - y).toNat := by
  have hle := ltCheck_iszero_ne h
  rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat (by omega))]
  unfold chkSub
  rw [ite_eq_left (by omega)]

/-- Vyper's checked addition `ISZERO (LT (x + y) x)`, read back. -/
theorem vyChkAdd {x y : B256} (h : B256.eqCheck (B256.ltCheck (x + y) x) 0 ≠ 0) :
    chkAdd x.toNat y.toNat = some (x + y).toNat := by
  have hle := ltCheck_iszero_ne h
  have hx := B256.toNat_lt x
  have hy := B256.toNat_lt y
  rw [B256.toNat_add] at hle ⊢
  unfold Nat.lo at hle ⊢
  have hlt : x.toNat + y.toNat < 2 ^ 256 := by
    by_contra hc
    have e : (x.toNat + y.toNat) % 2 ^ 256 = x.toNat + y.toNat - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  unfold chkAdd wordSize
  rw [ite_eq_left hlt, Nat.mod_eq_of_lt hlt]

/-- Vyper's checked multiplication `ISZERO x OR (x * y) / x == y`, read back. -/
theorem vyChkMul {x y : B256} (h : (B256.eqCheck ((x * y) / x) y ||| B256.eqCheck x 0) ≠ 0) :
    chkMul x.toNat y.toNat = some (x * y).toNat := by
  have hN : (0 : Nat) < 2 ^ 256 := Nat.two_pow_pos 256
  rw [B256.toNat_mul]
  unfold Nat.lo chkMul wordSize
  by_cases hx : x = 0
  · subst hx
    rw [show (0 : B256).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_mod, ite_eq_left hN]
  · have hx0 : B256.eqCheck x 0 = 0 := by unfold B256.eqCheck; rw [ite_eq_right hx]
    rw [hx0] at h
    have hq : (x * y) / x = y := by
      unfold B256.eqCheck at h; split at h
      · assumption
      · exact absurd h (by decide)
    have hxn := B256.toNat_pos hx
    have hq' := congrArg B256.toNat hq
    rw [B256.toNat_div hx, B256.toNat_mul] at hq'
    unfold Nat.lo at hq'
    have hlt : x.toNat * y.toNat < 2 ^ 256 := by
      by_contra hc
      have h1 : x.toNat * y.toNat % 2 ^ 256 < x.toNat * y.toNat :=
        lt_of_lt_of_le (Nat.mod_lt _ hN) (Nat.le_of_not_lt hc)
      have h2 : x.toNat * y.toNat % 2 ^ 256 / x.toNat < y.toNat :=
        (Nat.div_lt_iff_lt_mul hxn).mpr (by rw [Nat.mul_comm y.toNat]; exact h1)
      exact absurd hq' (Nat.ne_of_lt h2)
    rw [ite_eq_left hlt, Nat.mod_eq_of_lt hlt]

/-- Vyper's checked division (a nonzero divisor), read back. -/
theorem vyChkDiv {x y : B256} (h : y ≠ 0) : chkDiv x.toNat y.toNat = some (x / y).toNat := by
  unfold chkDiv
  rw [ite_eq_right (fun h0 => h (B256.toNat_inj _ _ (by rw [h0]; rfl))), B256.toNat_div h]

/-! ### The guards, forward: a checked operation that succeeds passes its guard -/

theorem eqCheck_self (a : B256) : B256.eqCheck a a = 1 := by
  unfold B256.eqCheck; rw [ite_eq_left rfl]

theorem one_ne_zero_b256 : (1 : B256) ≠ 0 := by decide

theorem fwdChkSub {x y : B256} {z : Nat} (h : chkSub x.toNat y.toNat = some z) :
    B256.eqCheck (B256.ltCheck x y) 0 ≠ 0 ∧ (x - y).toNat = z := by
  have hle : y.toNat ≤ x.toNat := by
    unfold chkSub at h; split at h
    · assumption
    · cases h
  have hg : B256.eqCheck (B256.ltCheck x y) 0 ≠ 0 := by
    have : B256.ltCheck x y = 0 := by
      unfold B256.ltCheck
      rw [ite_eq_right (by rw [B256.lt_iff_toNat_lt_toNat]; omega)]
    rw [this, eqCheck_self]; exact one_ne_zero_b256
  exact ⟨hg, Option.some.inj ((vyChkSub hg).symm.trans h)⟩

theorem fwdChkAdd {x y : B256} {z : Nat} (h : chkAdd x.toNat y.toNat = some z) :
    B256.eqCheck (B256.ltCheck (x + y) x) 0 ≠ 0 ∧ (x + y).toNat = z := by
  have hlt : x.toNat + y.toNat < 2 ^ 256 := by
    unfold chkAdd wordSize at h; split at h
    · assumption
    · cases h
  have hg : B256.eqCheck (B256.ltCheck (x + y) x) 0 ≠ 0 := by
    have : B256.ltCheck (x + y) x = 0 := by
      unfold B256.ltCheck
      rw [ite_eq_right (by rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_add_eq_of_nof _ _ hlt]; omega)]
    rw [this, eqCheck_self]; exact one_ne_zero_b256
  exact ⟨hg, Option.some.inj ((vyChkAdd hg).symm.trans h)⟩

theorem fwdChkMul {x y : B256} {z : Nat} (h : chkMul x.toNat y.toNat = some z) :
    (B256.eqCheck ((x * y) / x) y ||| B256.eqCheck x 0) ≠ 0 ∧ (x * y).toNat = z := by
  have hlt : x.toNat * y.toNat < 2 ^ 256 := by
    unfold chkMul wordSize at h; split at h
    · assumption
    · cases h
  have hg : (B256.eqCheck ((x * y) / x) y ||| B256.eqCheck x 0) ≠ 0 := by
    by_cases hx : x = 0
    · subst hx
      rw [eqCheck_self]
      unfold B256.eqCheck; split <;> decide
    · have hq : (x * y) / x = y := by
        apply B256.toNat_inj
        rw [B256.toNat_div hx, B256.toNat_mul_eq_of_nofm hlt,
          Nat.mul_div_cancel_left _ (B256.toNat_pos hx)]
      rw [hq, eqCheck_self]
      unfold B256.eqCheck; split <;> decide
  exact ⟨hg, Option.some.inj ((vyChkMul hg).symm.trans h)⟩

theorem fwdChkDiv {x y : B256} {z : Nat} (h : chkDiv x.toNat y.toNat = some z) :
    y ≠ 0 ∧ (x / y).toNat = z := by
  have hy : y ≠ 0 := by
    rintro rfl
    unfold chkDiv at h
    split at h
    · cases h
    · rename_i h0; exact h0 rfl
  exact ⟨hy, Option.some.inj ((vyChkDiv hy).symm.trans h)⟩

/-! ## The inversion step tactic -/

set_option hygiene false in
open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- **One inversion step** of a cut-run walk over the hypothesis `run`: peel the next node
(`ric_next`) and invert its instruction by the matching `ri_*` lemma (`PUSH`, `DUP`/`SWAP` by
`rfl`, `SLOAD` with the covered-fork hypothesis in context, every other register instruction
by `ri_<name>`), substituting the successor state.  The instruction is read off the node, so
no unification against a mismatched lemma is attempted. -/
elab "istep" : tactic => do
  let run : Ident := mkIdent `run
  let s1 : Ident := mkIdent `s1
  evalTactic (← `(tactic| (have hnext := ric_next $run; clear $run; obtain ⟨_, $s1, $run⟩ := hnext)))
  withMainContext do
    let ldecl ← getLocalDeclFromUserName `s1
    let ty ← instantiateMVars ldecl.type
    let args := ty.getAppArgs
    let n ← whnfR (← instantiateMVars args[args.size - 2]!)
    let some c := n.getAppFn.constName? | throwError "istep: no instruction in {n}"
    let cs := c.componentsRev.head!.toString
    let tac ← if cs == "push" then `(tactic| obtain ⟨_, rfl⟩ := Blanc.Lift.ri_push $s1)
      else if cs == "reg" then do
        let r ← whnfR n.appArg!
        let some rc := r.getAppFn.constName? | throwError "istep: no register op in {r}"
        match rc.componentsRev.head!.toString with
        | "dup" => `(tactic| obtain ⟨_, rfl⟩ := Blanc.Lift.ri_dup rfl $s1)
        | "swap" => `(tactic| obtain ⟨_, rfl⟩ := Blanc.Lift.ri_swap rfl $s1)
        | "sload" => `(tactic| obtain ⟨_, rfl⟩ := Blanc.Lift.ri_sload (by assumption) $s1)
        | "keccak256" => `(tactic| obtain ⟨_, rfl⟩ := Blanc.Lift.ri_keccak $s1)
        | o => do
          let id := mkIdent (`Blanc.Lift ++ Name.mkSimple ("ri_" ++ o))
          `(tactic| obtain ⟨_, rfl⟩ := $id $s1)
      else throwError "istep: unsupported node {n}"
    evalTactic tac
    evalTactic (← `(tactic| clear $s1))

/-- Membership of a carried word in a literal list. -/
macro "wmem" : tactic =>
  `(tactic| (repeat' (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)))

set_option hygiene false in
/-- `MLOAD` of the carried word at `o`, over the tracked memory `hT`. -/
macro "imload' " o:term : tactic => `(tactic|
  (have hstep := ric_mloadT (o := $o) hT run (by wmem) (by decide)
   clear hT run; obtain ⟨_, _, hT, run⟩ := hstep))

set_option hygiene false in
/-- `PUSH o; MLOAD` of the carried word at `o`. -/
macro "imload " o:term : tactic => `(tactic| (istep; imload' $o))

set_option hygiene false in
/-- `MSTORE` into the tracked window (a literal predicate) at `o`, over the tracked memory `hT`. -/
macro "imstore' " o:term : tactic => `(tactic|
  (have hstep := ric_mstoreT (o := $o) hT run (by decide)
     rfl rfl
   clear hT run; obtain ⟨_, _, hT, run⟩ := hstep))

set_option hygiene false in
/-- `PUSH o; MSTORE` into the callee window at `o`. -/
macro "imstore " o:term : tactic => `(tactic| (istep; imstore' $o))

set_option hygiene false in
/-- `MSTORE` overwriting at `o` (carried words it hits are dropped; the list is normalized). -/
macro "imstoreO' " o:term : tactic => `(tactic|
  (have hstep := ric_mstoreO (o := $o) hT run (by decide)
     rfl
   clear hT run; obtain ⟨_, _, hT, run⟩ := hstep
   simp only [wordsOff, List.filter_cons, List.filter_nil, Nat.reduceAdd, Nat.reduceLeDiff,
     decide_true, decide_false, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
     ite_true, ite_false, Bool.false_eq_true, ↓reduceIte] at hT))

set_option hygiene false in
/-- `PUSH o; MSTORE` overwriting at `o`. -/
macro "imstoreO " o:term : tactic => `(tactic| (istep; imstoreO' $o))

set_option hygiene false in
/-- `KECCAK256` of the carried word at `o`. -/
macro "ikeccak " o:term : tactic => `(tactic|
  (have hstep := ric_keccakT (o := $o) hT run (by wmem) (by decide) (by decide)
   clear hT run; obtain ⟨_, _, hT, run⟩ := hstep))

set_option hygiene false in
/-- A `JUMPI` whose fall-through reverts: keep the taken arm and its condition. -/
macro "iassert " h:ident : tactic => `(tactic|
  (have hbr := ric_branch run; clear run
   rcases hbr with ⟨-, _, run⟩ | ⟨$h, _, run⟩
   · exact (run.false_of_noOk rfl).elim
   have hd := ric_dest run; clear run; obtain ⟨_, run⟩ := hd))

/-! ## The forward step tactics

A forward walk proves `∃ M', SFunc.RunExactCut … (R M') ∧ Q M'` (or a plain exact cut run)
with, in context, the tracked memory `hT`, its size `hS : M.size = n`, `hn : n % 32 = 0`, the
cover `htop`, the stack room `hroom` and the covered fork. -/

set_option hygiene false in
open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- **One forward step**: read the next node of the goal's tree and apply the matching
`rxc_*` lemma (lifted through the `∃ M'` goal by `xlift`).  Gas is matched by `Nat` offsets. -/
elab "xstep" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let isEx := goal.getAppFn.constName? == some ``Exists
  let run := if isEx then (goal.appArg!.bindingBody!.getAppArgs[0]!) else goal
  let args := run.getAppArgs
  let f ← whnf args[4]!
  let some c := f.getAppFn.constName? | throwError "xstep: no node in {f}"
  let cs := c.componentsRev.head!.toString
  let room ← `(term| (by first | omega | (simp only [List.length_cons]; omega)))
  let lem ← if cs == "dest" then `(term| Blanc.Lift.rxc_dest)
    else if cs == "next" then do
      let n ← whnf f.getAppArgs[0]!
      let some nc := n.getAppFn.constName? | throwError "xstep: no instruction in {n}"
      if nc.componentsRev.head!.toString == "push" then `(term| Blanc.Lift.rxc_push rfl $room)
      else do
        let r ← whnf n.appArg!
        let some rc := r.getAppFn.constName? | throwError "xstep: no register op in {r}"
        match rc.componentsRev.head!.toString with
        | "dup" => `(term| Blanc.Lift.rxc_dup rfl $room)
        | "swap" => do
          let i ← whnf r.appArg!
          let iv ← whnf (← mkAppM ``Fin.val #[i])
          match iv.rawNatLit? with
          | some 0 => `(term| Blanc.Lift.rxc_swap0)
          | some 1 => `(term| Blanc.Lift.rxc_swap1)
          | _ => throwError "xstep: unsupported swap {i}"
        | "pop" => `(term| Blanc.Lift.rxc_pop)
        | "add" => `(term| Blanc.Lift.rxc_add $room)
        | "sub" => `(term| Blanc.Lift.rxc_sub' rfl $room)
        | "sload" => `(term| Blanc.Lift.rxc_sload_sel (by assumption) $room)
        | "timestamp" => `(term| Blanc.Lift.rxc_timestamp $room)
        | o => do
          let id := mkIdent (`Blanc.Lift ++ Name.mkSimple ("rxc_" ++ o))
          `(term| $id rfl $room)
    else throwError "xstep: unsupported node {f}"
  if isEx then
    evalTactic (← `(tactic| refine Blanc.Lift.xlift (fun _ k => $lem k) ?_))
  else
    evalTactic (← `(tactic| refine $lem ?_))

set_option hygiene false in
/-- Forward `MLOAD` of the carried word at `o`. -/
macro "xmload' " o:term : tactic => `(tactic|
  refine Blanc.Lift.xlift (fun _ k => Blanc.Lift.rxc_mloadT (o := $o) hT hS hn (by wmem)
    (by decide) (by first | omega | (simp only [List.length_cons]; omega)) k) ?_)

set_option hygiene false in
/-- Forward `PUSH o; MLOAD`. -/
macro "xmload " o:term : tactic => `(tactic| (xstep; xmload' $o))

set_option hygiene false in
/-- Forward `MSTORE` at `o` (overwriting), renewing `hT` and `hS`. -/
macro "xmstore' " o:term : tactic => `(tactic|
  (refine Blanc.Lift.rxc_mstoreT (o := $o) hT hS hn (by decide) (by omega) rfl ?_
   intro hT hS
   simp only [wordsOff, List.filter_cons, List.filter_nil, Nat.reduceAdd, Nat.reduceLeDiff,
     decide_true, decide_false, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
     ite_true, ite_false, Bool.false_eq_true, ↓reduceIte] at hT))

set_option hygiene false in
/-- Forward `PUSH o; MSTORE`. -/
macro "xmstore " o:term : tactic => `(tactic| (xstep; xmstore' $o))

set_option hygiene false in
/-- Forward `KECCAK256` of the carried word at `o`. -/
macro "xkeccak " o:term : tactic => `(tactic|
  refine Blanc.Lift.xlift (fun _ k => Blanc.Lift.rxc_keccakT (o := $o) hT hS hn (by wmem)
    (by decide) (by decide) (by first | omega | (simp only [List.length_cons]; omega)) k) ?_)

set_option hygiene false in
/-- Forward `JUMPI` taken (`h : w ≠ 0`) into its in-tree target, then its `JUMPDEST`. -/
macro "xassert " h:term:max : tactic => `(tactic|
  (refine Blanc.Lift.xlift (fun _ k => Blanc.Lift.rxc_branch_succ $h k) ?_; xstep))

set_option hygiene false in
/-- Forward `JUMPI` not taken (`h : w = 0`). -/
macro "xzero " h:term:max : tactic => `(tactic|
  refine Blanc.Lift.xlift (fun _ k => Blanc.Lift.rxc_branch_zeroOf $h k) ?_)

set_option hygiene false in
/-- Forward `JUMP` into entry `k` (`hk : fs[k]? = some g`). -/
macro "xjump " hk:term:max : tactic => `(tactic|
  refine Blanc.Lift.xlift (fun _ kk => Blanc.Lift.rxc_jump $hk List.not_mem_nil kk) ?_)

set_option hygiene false in
/-- Forward conditional goto taken (`h : w ≠ 0`) into entry `k`. -/
macro "xgoto " h:term:max hk:term:max : tactic => `(tactic|
  refine Blanc.Lift.xlift (fun _ kk => Blanc.Lift.rxc_branchTo_succ $h $hk List.not_mem_nil kk) ?_)

set_option hygiene false in
/-- The callee's forward return. -/
macro "xret" : tactic => `(tactic| exact Blanc.Lift.rxc_retT hT hS)

end Blanc.Lift
