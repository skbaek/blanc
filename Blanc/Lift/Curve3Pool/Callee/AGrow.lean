import Blanc.Lift.Curve3Pool.Callee.A

/-!
# `_A` over a memory one word short of its frame

`a_exact` runs `_A` over a memory covering `[0, 0x200)`. `_calc_withdraw_one_coin` calls it
with the memory at `0x1e0`: outside a ramp `_A` writes below `0x1a0` only, during a ramp its
store at `0x1e0` grows the memory by one word (`3` gas more). `a_exact_1e0` is that run: the
returned memory is `0x1e0` (no ramp, `e = 0`) or `0x200` (ramp, `e = 3`).

`rxc_mstoreT_grow` is the tracked `MSTORE` one word past the end.
-/

namespace Blanc.Lift

open Jaune

/-- A word store past an aligned end grows the memory to the word's end. -/
theorem Mem.size_write_word_end {N : Mem} {w : B256} (h : N.size % 32 = 0) :
    (N.write N.size w.toBytes).size = N.size + 32 := by
  have hc : ceil32 (N.size + 32) = N.size + 32 := by
    unfold ceil32; rw [show (N.size + 32) % 32 = 0 by omega]
  rcases hb : w.toBytes with _ | ⟨b, bs⟩
  · exact absurd (hb ▸ B256.length_toBytes w) (by simp only [List.length_nil,
      OfNat.zero_ne_ofNat, not_false_eq_true])
  · have hlen : (b :: bs).length = 32 := hb ▸ B256.length_toBytes w
    simp only [Mem.write, hlen]
    split_ifs with h1
    all_goals dsimp only
    all_goals first | omega | exact hc

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M M₀ : Mem}
  {G n : Nat} {f : SFunc} {W : List (Nat × Nat)} {L : List (Nat × B256)}

/-- A tracked `MSTORE` at the end of an aligned memory, growing it by one word. -/
theorem rxc_mstoreT_grow {i v : B256} {o c : Nat} {R : Mem → Seg} {Q : Mem → Prop}
    (hT : MemTrack M₀ M W L) (hS : M.size = n)
    (hc : 3 + (calculateMemoryGasCost (n + 32) - calculateMemoryGasCost n) = c)
    (hn : n % 32 = 0) (hi : i.toNat = o) (ho : o = n) (hW : coversWord W o = true)
    (k : MemTrack M₀ (M.write o v.toBytes) W ((o, v) :: wordsOff o L) →
      (M.write o v.toBytes).size = n + 32 →
      ∃ M', SFunc.RunExactCut fs sevm C (St b S (M.write o v.toBytes) G) f (R M') ∧ Q M') :
    ∃ M', SFunc.RunExactCut fs sevm C
      (St b (i :: v :: S) M (G + c)) (.next (.reg .mstore) f) (R M') ∧ Q M' := by
  subst hi ho hc
  have hsz : (M.write i.toNat v.toBytes).size = i.toNat + 32 := by
    have e := Mem.size_write_word_end (N := M) (w := v) (by rw [hS]; exact hn)
    rw [hS] at e
    exact e
  obtain ⟨M', run, hq⟩ := k (hT.writeO v hW) hsz
  refine ⟨M', rxc_mstore ?_ rfl run, hq⟩
  rw [St.extCost_eq hS, show memExtSize i.toNat i.toNat 32 = i.toNat + 32 from by
    unfold memExtSize ceilDiv; simp only [Nat.max_def]; split_ifs <;> first | contradiction | omega]
  rfl

end Fwd

end Blanc.Lift

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift
open Blanc.StableSwapNewton

set_option hygiene false in
/-- `PUSH o; MSTORE` growing the tracked memory by one word at `o = n`, at cost `c`. -/
macro "xmstoreG " o:term "," c:term : tactic => `(tactic|
  (xstep
   refine rxc_mstoreT_grow (o := $o) (c := $c) hT hS (by decide) hn rfl rfl (by decide) ?_
   intro hT hS
   simp only [wordsOff, List.filter_cons, List.filter_nil, Nat.reduceAdd, Nat.reduceLeDiff,
     decide_true, decide_false, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
     ite_true, ite_false, Bool.false_eq_true, ↓reduceIte] at hT))

/-- `_A`'s extra gas over a `0x1e0` memory: the ramp's store at `0x1e0` grows it. -/
def aE (sevm : Sevm) (b : Devm) : Nat :=
  if sevm.benvStat.time.toNat < (b.getStorVal sevm.currentTarget futureATimeSlot).toNat then 3
  else 0

/-- The memory size `_A` leaves from `0x1e0`. -/
def aSz (sevm : Sevm) (b : Devm) : Nat :=
  if sevm.benvStat.time.toNat < (b.getStorVal sevm.currentTarget futureATimeSlot).toNat then
    0x200 else 0x1e0

theorem aSz_mod (sevm : Sevm) (b : Devm) : aSz sevm b % 32 = 0 := by
  unfold aSz; split <;> decide

theorem aSz_ext (sevm : Sevm) (b : Devm) : memExtSize (aSz sevm b) 0x1e0 32 = 0x200 := by
  unfold aSz; split <;> decide

/-- The extra gas and the growing store at `0x1e0` after it cost `6` together. -/
theorem aE_store (sevm : Sevm) (b : Devm) :
    aE sevm b + (3 + (calculateMemoryGasCost 0x200 - calculateMemoryGasCost (aSz sevm b))) = 6 := by
  unfold aE aSz; split <;> decide

theorem aE_le (sevm : Sevm) (b : Devm) : aE sevm b ≤ 3 := by
  unfold aE; split <;> decide

-- SEGMENT: aExact1e0
/-- **`_A`, forward, over a memory of `0x1e0`**: as `a_exact`, at `aE` more gas (the ramp's store
at `0x1e0` grows the memory), leaving a memory of `aSz`. -/
theorem a_exact_1e0 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G v : Nat} {ret : B256}
    {s : State} (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hA : aChk s sevm.benvStat.time.toNat = some v) (hwf : Mem.Wf M) (hS : M.size = 0x1e0)
    (hroom : S.length + 16 < 1024) :
    ∃ w, (∃ M', SFunc.RunExact prog sevm (St b (ret :: S) M (G + aE sevm b + aGas sevm b))
      t_00a9_c27 (.returned (St (aBase sevm b) (w :: S) M' G)) ∧
      (Mem.KeepsOff M M' aWin ∧ Mem.Wf M' ∧ M'.size = aSz sevm b)) ∧ w.toNat = v := by
  have hT := MemTrack.init hwf aWin
  have hn : (0x1e0 : Nat) % 32 = 0 := by decide
  have e1 := ha.futureATime
  have e2 := ha.futureA
  have e3 := ha.initialA
  have e4 := ha.initialATime
  rw [aChk_eq, ← e1, ← e2, ← e3, ← e4] at hA
  simp only [← getStorVal_eq_getStor] at hA
  unfold aGas aBase aE aSz
  by_cases ht : sevm.benvStat.time.toNat <
      (b.getStorVal sevm.currentTarget futureATimeSlot).toNat
  · simp only [ht, ↓reduceIte] at hA ⊢
    by_cases hup : (b.getStorVal sevm.currentTarget futureASlot).toNat >
        (b.getStorVal sevm.currentTarget initialASlot).toNat
    · simp only [hup, ↓reduceIte] at hA ⊢
      simp only [SFunc.runExact_iff_runExactCut_nil]
      simp only [← slot_09, ← slot_07, ← slot_06, ← slot_08] at ht hup hA ⊢
      refine ⟨?w1, ?run1, ?val1⟩
      case run1 =>
        rw [show ∀ x1 x2 x3 x4 : Nat, G + 3 + (458 + x1 + x2 + x3 + x4) =
          G + 397 + x4 + 9 + x3 + 36 + x2 + 9 + x1 + 10 from fun _ _ _ _ => by omega]
        xstep; xmstore 0x140; xstep; xstep; xmstore 0x160; xstep; xstep; xmstore 0x180
        xmload 0x160; xstep; xstep; xstep; xstep
        xzero (ltCheck_iszero_of_lt ht)
        xstep; xstep; xmstore 0x1c0; xstep; xstep; xmstoreG 0x1e0, 6
        rw [show (0x1e0 + 32 : Nat) = 0x200 from rfl] at hS
        have hn : (0x200 : Nat) % 32 = 0 := by decide
        xmload 0x1c0; xmload 0x180; xstep; xstep; xstep
        xzero (by simp only [afterSload_getStorVal]; exact gtCheck_iszero_of_lt hup)
        exact (a_up_exact hT hS hn (by decide) hroom
          (by simpa only [afterSload_getStorVal] using hA)).1
      case val1 => exact aUpW_toNat (by simpa only [afterSload_getStorVal] using hA)
    · simp only [hup, ↓reduceIte] at hA ⊢
      simp only [SFunc.runExact_iff_runExactCut_nil]
      simp only [← slot_09, ← slot_07, ← slot_06, ← slot_08] at ht hup hA ⊢
      refine ⟨?w2, ?run2, ?val2⟩
      case run2 =>
        rw [show ∀ x1 x2 x3 x4 : Nat, G + 3 + (453 + x1 + x2 + x3 + x4) =
          G + 392 + x4 + 9 + x3 + 36 + x2 + 9 + x1 + 10 from fun _ _ _ _ => by omega]
        xstep; xmstore 0x140; xstep; xstep; xmstore 0x160; xstep; xstep; xmstore 0x180
        xmload 0x160; xstep; xstep; xstep; xstep
        xzero (ltCheck_iszero_of_lt ht)
        xstep; xstep; xmstore 0x1c0; xstep; xstep; xmstoreG 0x1e0, 6
        rw [show (0x1e0 + 32 : Nat) = 0x200 from rfl] at hS
        have hn : (0x200 : Nat) % 32 = 0 := by decide
        xmload 0x1c0; xmload 0x180; xstep; xstep; xstep
        refine Blanc.Lift.xlift (fun _ k => rxc_branch_succ
          (by simp only [afterSload_getStorVal]; exact gtCheck_iszero_of_not_lt hup) k) ?_
        exact (a_down_exact hT hS hn (by decide) hroom
          (by simpa only [afterSload_getStorVal] using hA)).1
      case val2 => exact aDownW_toNat (by simpa only [afterSload_getStorVal] using hA)
  · simp only [ht, ↓reduceIte] at hA ⊢
    simp only [SFunc.runExact_iff_runExactCut_nil]
    simp only [← slot_09, ← slot_07] at ht hA ⊢
    refine ⟨?w3, ?run3, ?val3⟩
    case run3 =>
      rw [show ∀ x1 x2 : Nat, G + 0 + (85 + x1 + x2) = G + 66 + x2 + 9 + x1 + 10 from
        fun _ _ => by omega]
      xstep; xmstore 0x140; xstep; xstep; xmstore 0x160; xstep; xstep; xmstore 0x180
      xmload 0x160; xstep; xstep; xstep; xstep
      xassert (ltCheck_iszero_of_not_lt ht)
      xmload 0x180; xmstore 0x0; xmload 0x0; xmload 0x140
      xret
    case val3 =>
      simp only [afterSload_getStorVal]
      exact (Option.some.inj hA)

end Blanc.Lift.Curve3Pool
