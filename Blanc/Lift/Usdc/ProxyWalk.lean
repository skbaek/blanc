import Blanc.Lift.Usdc.Proxy.Check
import Blanc.Lift.Usdc.Constants
import Blanc.Lift.ReachWalk
import Blanc.Lift.InvWalkOps
import Blanc.Lift.WalkSteps
import Blanc.Lift.ExactLeaf
import Blanc.Lift.RunPWalk
import Blanc.AddressSlotProofs

/-!
# Walking the proxy certificate (C2b)

The prefix and big-step walks over the generated proxy certificate (`Proxy.cert`) that the proxy
frame theorems (`ProxyForward.lean`) use.  Certificate-driven: every step is the inversion of the
checked tree's node (`rr_*` over a prefix reach, `rpw_*` over a big-step run, `ri_*` for the
instruction), never an unfolding of the bytes.

* The step kit (`ri_address`, `ri_dup_any`, `rr_branchTo`, the big-step node inversions `rpw_*`,
  `St.self'`) is the generic `Blanc/Lift/RunPWalk.lean`.
* The internal getters: `_admin()` (entry 8) returns the admin word, `_implementation()`
  (entry 14) the implementation word; `_willFallback()` (entry 22) returns only for a caller
  other than the admin word (`willFallback_ret`).
-/

namespace Blanc.Lift

open Jaune Blanc

end Blanc.Lift

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- The proxy program. -/
abbrev prog : List SFunc := cert.prog

theorem adminSlot_word : Bytes.toB256 [0x01] * Bytes.toB256 [0x10, 0xd6, 0xa5, 0x4a, 0x47, 0x54,
    0xc8, 0x86, 0x9d, 0x68, 0x86, 0xb5, 0xf5, 0xd7, 0xfb, 0xfa, 0x5b, 0x45, 0x22, 0x23, 0x7e, 0xa5,
    0xc6, 0x0d, 0x11, 0xbc, 0x4e, 0x7a, 0x1f, 0xf9, 0x39, 0x0b] = adminSlot := by
  decide +kernel

theorem implSlot_word : Bytes.toB256 [0x01] * Bytes.toB256 [0x70, 0x50, 0xc9, 0xe0, 0xf4, 0xca,
    0x76, 0x9c, 0x69, 0xbd, 0x3a, 0x8e, 0xf7, 0x40, 0xbc, 0x37, 0x93, 0x4f, 0x8e, 0x2c, 0x03, 0x6e,
    0x5a, 0x72, 0x3f, 0xd8, 0xee, 0x04, 0x8e, 0xd3, 0xf8, 0xc3] = implSlot := by
  decide +kernel

theorem iszero_ne {x : B256} (h : B256.eqCheck x 0 ≠ 0) : x = 0 := by
  unfold B256.eqCheck at h
  split at h
  · assumption
  · exact (h rfl).elim

theorem ne_of_eqCheck_eq_zero {x y : B256} (h : B256.eqCheck x y = 0) : x ≠ y := by
  intro hxy
  unfold B256.eqCheck at h
  split at h
  · exact absurd h (by decide)
  · contradiction

theorem eqCheck_ne_zero {x y : B256} (h : B256.eqCheck x y ≠ 0) : x = y := by
  unfold B256.eqCheck at h
  split at h
  · assumption
  · exact (h rfl).elim

theorem iszero_eq_zero {x : B256} (h : B256.eqCheck x 0 = 0) : x ≠ 0 := ne_of_eqCheck_eq_zero h

theorem ff20_caller (a : Adr) :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& a.toB256 = a.toB256 := by
  rw [ff20_and_word, toAdr_toB256]

/-- The masked comparison of the caller with a word decides the caller's equality with the word's
address. -/
theorem masked_eq_iff (a : Adr) (v : B256) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& a.toB256 =
     Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& v) ↔ a = v.toAdr := by
  rw [ff20_caller, ff20_and_word]
  constructor
  · intro h
    have := congrArg B256.toAdr h
    rwa [toAdr_toB256, toAdr_toB256] at this
  · intro h
    rw [h]

section Getters

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

include hP

/-- `_admin()`: the admin word, after one storage read. -/
theorem admin_ret (hfork : CoveredFork sevm.benvStat.fork) {r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (r :: S) M G) t_06a8_c8 (.returned D)) :
    ∃ G', D = St (afterSload sevm b adminSlot)
      (b.getStorVal sevm.currentTarget adminSlot :: S) M G' := by
  unfold t_06a8_c8 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_mul (hP s)
  rw [adminSlot_word] at run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_sload hfork (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  exact rpw_ret run

/-- `_implementation()`: the implementation word, after one storage read. -/
theorem impl_ret (hfork : CoveredFork sevm.benvStat.fork) {r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (r :: S) M G) t_0651_c14 (.returned D)) :
    ∃ G', D = St (afterSload sevm b implSlot)
      (b.getStorVal sevm.currentTarget implSlot :: S) M G' := by
  unfold t_0651_c14 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_mul (hP s)
  rw [implSlot_word] at run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_sload hfork (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  exact rpw_ret run

/-- `_willFallback()` returns only for a caller other than the admin word. -/
theorem willFallback_ret (hfork : CoveredFork sevm.benvStat.fork) {r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (r :: S) M G) t_0576_c22 (.returned D)) :
    sevm.caller ≠ (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      ∃ G', D = St (afterSload sevm b adminSlot) S M G' := by
  unfold t_0576_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D1, callee, run⟩ := rpw_callRet (k := 8) rfl run
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
  unfold t_057e_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨hc, _, run⟩
  · exact (SFunc.RunP.not_returned_of_haltsOnly run (by decide)).elim
  refine ⟨fun h => ne_of_eqCheck_eq_zero (iszero_ne (iszero_eq_zero (iszero_ne hc))) ((masked_eq_iff _ _).mpr h), ?_⟩
  unfold t_0647_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D2, callee, run⟩ := rpw_callRet (k := 31) rfl run
  unfold t_0777_c31 at callee
  obtain ⟨_, callee⟩ := rpw_dest callee
  obtain ⟨_, rfl⟩ := rpw_ret callee
  unfold t_064f_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  exact rpw_ret run

end Getters

end Blanc.Lift.Usdc.Proxy

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- The `_fallback()` body, one copy per caller context: `_willFallback()`, then
`_delegate(_implementation())`, entered at the delegate copy `d`. -/
def fbTree (d : Nat) : SFunc :=
  .dest (.next (.push [0x02, 0x01] (by decide)) (.next (.push [0x05, 0x76] (by decide))
    (.callNext 22 (.dest (.next (.push [0x02, 0x11] (by decide)) (.next (.push [0x02, 0x0c] (by decide))
      (.next (.push [0x06, 0x51] (by decide)) (.callNext 14 (.dest (.next (.push [0x06, 0x82] (by decide))
        (.jump d)))))))))))

/-- The getters and `_willFallback()` make no external call. -/
def getterEntries : List Nat := [8, 14, 22, 31]

theorem getters_execFree : ExecFreeSet prog getterEntries = true := by decide

section Fallback

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}

include hP

/-- **The fallback reaches only its `DELEGATECALL`.**  A prefix reach from a `_fallback()` copy to
an external instruction passes `_willFallback()` (so the caller is not the admin word) and stops at
the `DELEGATECALL` of `_delegate`, whose operands are the remaining gas, the implementation word,
and the input window `[0, calldatasize)` that `CALLDATACOPY` has just filled with the calldata. -/
theorem fallback_reach (hfork : CoveredFork sevm.benvStat.fork) {d : Nat}
    (hd : prog[d]? = some t_0682_c23)
    (run : Reach P prog sevm ⟨St b S M G, fbTree d, K⟩ T) (hT : AtExec T) :
    sevm.caller ≠ (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      ∃ (g : B256) (rest : SFunc) (G' : Nat), T = ⟨St (afterSload sevm (afterSload sevm b adminSlot) implSlot)
        (g :: b.getStorVal sevm.currentTarget implSlot :: 0 :: sevm.data.length.toB256 :: 0 :: 0 ::
          b.getStorVal sevm.currentTarget implSlot :: Bytes.toB256 [0x02, 0x11] :: S)
        (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G',
        .next (.exec .delegatecall) rest, K⟩ := by
  unfold fbTree at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 22) rfl (by decide) run hT
  obtain ⟨notAdmin, _, rfl⟩ := willFallback_ret hP hfork callee
  refine ⟨notAdmin, ?_⟩
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 14) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := impl_ret hP hfork callee
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rr_jump run hT
  rw [hd] at hg
  cases hg
  unfold t_0682_c23 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatacopy (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨w, _, rfl⟩ := ri_gas (hP s)
  rcases Reach.exec run with rfl | ⟨_, -, run⟩
  · exact ⟨w, _, _, by rw [getStorVal_afterSload]; rfl⟩
  · obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    rcases Reach.branch run hT with ⟨_, _, -, run⟩ | ⟨_, _, _, -, -, run⟩
    · unfold t_069f_c23 at run
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      exact (Reach.not_last run hT).elim
    · unfold t_06a3_c23 at run
      obtain ⟨_, -, run⟩ := Reach.dest run hT
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      exact (Reach.not_last run hT).elim

end Fallback

end Blanc.Lift.Usdc.Proxy
