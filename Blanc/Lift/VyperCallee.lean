import Blanc.Lift.VyperFrameLoop
import Blanc.Lift.WalkSteps
import Blanc.Lift.StableSwapNewton.Defs
import Blanc.ForwardStorageAccess

/-!
# Walking Vyper 0.2.x internal callees: memory windows and checked arithmetic

A Vyper 0.2.x internal function keeps its frame in a fixed memory window (and the scratch words
at `0` and `0xc0`), and checks its `uint256` arithmetic with fixed instruction patterns.  This
module gives a callee walk the vocabulary to state and prove its value contract without tracking
concrete memory terms:

* `Mem.KeepsOff μ μ' P`: `μ'` is at least as large as `μ` and keeps every byte below `μ`'s size
  at which `P` fails (`P` describes the windows the callee writes).  It refines
  `Mem.AgreeOutside` (`Mem.KeepsOff.agreeOutside`) and preserves every carried word outside the
  windows (`Words.keepsOff`).
* `MemTrack M₀ M P L`: the walk's memory `M` keeps `M₀` off `P` and carries the words `L`.
  `ric_mloadT` / `ric_mstoreT` step it through `MLOAD`/`MSTORE` of carried or fresh words.
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

/-! ## Memory windows -/

/-- `μ'` is at least as large as `μ` and keeps every byte of `μ` (below its size) off `P`. -/
def Mem.KeepsOff (μ μ' : Mem) (P : Nat → Prop) : Prop :=
  μ.size ≤ μ'.size ∧ ∀ i, i < μ.size → ¬ P i → μ'.data.getD i 0 = μ.data.getD i 0

namespace Mem.KeepsOff

variable {μ μ' μ'' : Mem} {P Q : Nat → Prop}

theorem refl (μ : Mem) (P : Nat → Prop) : Mem.KeepsOff μ μ P :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

theorem trans (h1 : Mem.KeepsOff μ μ' P) (h2 : Mem.KeepsOff μ' μ'' P) : Mem.KeepsOff μ μ'' P :=
  ⟨le_trans h1.1 h2.1, fun i hi hp => by rw [h2.2 i (lt_of_lt_of_le hi h1.1) hp, h1.2 i hi hp]⟩

theorem mono (h : Mem.KeepsOff μ μ' P) (hPQ : ∀ i, P i → Q i) : Mem.KeepsOff μ μ' Q :=
  ⟨h.1, fun i hi hq => h.2 i hi (fun hp => hq (hPQ i hp))⟩

theorem of_agreeOutside {lo hi : Nat} (h : Mem.AgreeOutside μ μ' lo hi) :
    Mem.KeepsOff μ μ' (fun i => lo ≤ i ∧ i < hi) :=
  ⟨h.1, fun i hi' hp => h.2 i hi' (by omega)⟩

/-- A window containing every written byte gives `Mem.AgreeOutside`. -/
theorem agreeOutside {lo hi : Nat} (h : Mem.KeepsOff μ μ' P)
    (hP : ∀ i, P i → lo ≤ i ∧ i < hi) : Mem.AgreeOutside μ μ' lo hi :=
  ⟨h.1, fun i hi' hout => h.2 i hi' (fun hp => by have := hP i hp; omega)⟩

/-- Every byte of `[lo, hi)` below `μ`'s size is kept when no byte there is written. -/
theorem getD {lo hi : Nat} (h : Mem.KeepsOff μ μ' P) (hP : ∀ i, P i → i < lo ∨ hi ≤ i)
    {i : Nat} (h1 : lo ≤ i) (h2 : i < hi) (hs : i < μ.size) :
    μ'.data.getD i 0 = μ.data.getD i 0 :=
  h.2 i hs (fun hp => by have := hP i hp; omega)

theorem extend (μ : Mem) (i n : Nat) (P : Nat → Prop) : Mem.KeepsOff μ (μ.extend i n) P :=
  ⟨memExtSize_ge _ _ _, fun _ _ _ => rfl⟩

theorem write_word (μ : Mem) (o : Nat) (v : B256) {P : Nat → Prop}
    (hP : ∀ j, o ≤ j → j < o + 32 → P j) : Mem.KeepsOff μ (μ.write o v.toBytes) P := by
  have h := Mem.write_agree μ o v.toBytes
  rw [B256.length_toBytes] at h
  exact (of_agreeOutside h).mono fun i hi => hP i hi.1 hi.2

end Mem.KeepsOff

/-- Carried words outside the written windows survive. -/
theorem Words.keepsOff {M M' : Mem} {L : List (Nat × B256)} {P : Nat → Prop} (h : Words M L)
    (hk : Mem.KeepsOff M M' P)
    (hout : ∀ o v, (o, v) ∈ L → ∀ j, o ≤ j → j < o + 32 → ¬ P j) : Words M' L := by
  intro o v hm
  obtain ⟨hs, hv⟩ := h o v hm
  refine ⟨le_trans hs hk.1, ?_⟩
  rw [memWord_congr (μ := M) (fun j hj => hk.2 _ (by omega) (hout o v hm _ (by omega) (by omega)))]
  exact hv

/-- **The callee walk's memory**: it keeps the entry memory `M₀` off the windows `P`, carries
the words `L`, and is well formed when `M₀` is. -/
structure MemTrack (M₀ M : Mem) (P : Nat → Prop) (L : List (Nat × B256)) : Prop where
  keeps : Mem.KeepsOff M₀ M P
  words : Words M L
  wf : Mem.Wf M₀ → Mem.Wf M

theorem MemTrack.init (M₀ : Mem) (P : Nat → Prop) : MemTrack M₀ M₀ P [] :=
  ⟨Mem.KeepsOff.refl M₀ P, Words.nil M₀, id⟩

theorem MemTrack.sub {M₀ M : Mem} {P : Nat → Prop} {L L' : List (Nat × B256)}
    (h : MemTrack M₀ M P L) (hs : L' ⊆ L) : MemTrack M₀ M P L' :=
  ⟨h.keeps, h.words.sub hs, h.wf⟩

theorem MemTrack.mem_size {M₀ M : Mem} {P : Nat → Prop} {L : List (Nat × B256)}
    (h : MemTrack M₀ M P L) {o : Nat} {v : B256} (hm : (o, v) ∈ L) : o + 32 ≤ M.size :=
  (h.words o v hm).1

section Steps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M M₀ : Mem}
  {G : Nat} {f : SFunc} {r : Seg} {P : Nat → Prop} {L : List (Nat × B256)}

/-- `MLOAD` of a carried word, inverted over a tracked memory. -/
theorem ric_mloadT {i v : B256} {o : Nat} (hT : MemTrack M₀ M P L)
    (run : SFunc.RunCut fs sevm C (St b (i :: S) M G) (.next (.reg .mload) f) r)
    (hm : (o, v) ∈ L) (hi : i.toNat = o) :
    ∃ M' G', MemTrack M₀ M' P L ∧ SFunc.RunCut fs sevm C (St b (v :: S) M' G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G1, rfl⟩ := ri_mload s1
  rw [hi] at run
  have hk := Mem.KeepsOff.extend M o 32 P
  refine ⟨_, G1, ⟨hT.keeps.trans hk, ?_, fun h => (hT.wf h).extend _ _⟩, ?_⟩
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
    (hi : i.toNat = o) (hP : ∀ j, o ≤ j → j < o + 32 → P j)
    (hout : (L.map Prod.fst).all (fun p => decide (p + 32 ≤ o) || decide (o + 32 ≤ p)) = true) :
    ∃ M' G', MemTrack M₀ M' P ((o, v) :: L) ∧ SFunc.RunCut fs sevm C (St b S M' G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G1, rfl⟩ := ri_mstore s1
  rw [hi] at run
  refine ⟨_, G1, ⟨hT.keeps.trans (Mem.KeepsOff.write_word M o v hP), ?_,
    fun h => (hT.wf h).write _ _⟩, run⟩
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
    (hi : i.toNat = o) (hP : ∀ j, o ≤ j → j < o + 32 → P j) :
    ∃ M' G', MemTrack M₀ M' P ((o, v) :: wordsOff o L) ∧
      SFunc.RunCut fs sevm C (St b S M' G') f r := by
  have hT' := hT.sub (L' := wordsOff o L) (List.filter_subset' _)
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
  refine ⟨_, G1, ⟨hT.keeps.trans hk, ?_, fun h => (hT.wf h).extend _ _⟩, ?_⟩
  · intro o' v' hm'
    obtain ⟨hs, hv⟩ := hT.words o' v' hm'
    exact ⟨le_trans hs hk.1, hv⟩
  · have hv : Bytes.toB256 (M.read o 32).1 = w := hT.words.memWord hm
    have hlen : (M.read o 32).1.length = 32 := by
      simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
    rw [← Bytes.toBytes_toB256_of_length hlen, hv] at run
    exact run

end Steps

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
     (fun j h1 h2 => by beta_reduce; omega) rfl
   clear hT run; obtain ⟨_, _, hT, run⟩ := hstep))

set_option hygiene false in
/-- `PUSH o; MSTORE` into the callee window at `o`. -/
macro "imstore " o:term : tactic => `(tactic| (istep; imstore' $o))

set_option hygiene false in
/-- `MSTORE` overwriting at `o` (carried words it hits are dropped; the list is normalized). -/
macro "imstoreO' " o:term : tactic => `(tactic|
  (have hstep := ric_mstoreO (o := $o) hT run (by decide)
     (fun j h1 h2 => by beta_reduce; omega)
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

end Blanc.Lift
