import Blanc.Lift.Curve3Pool.KitCheck
import Blanc.Lift.Curve3Pool.Layout
import Blanc.Lift.VyperCallee
import Blanc.Lift.ReachWalk

/-!
# The callee `_A` (pc `0xa9`, entry 27)

`_A()` (source lines 147–166) is called with its return address on the stack, keeps it at
`0x140`, reads `future_A_time` (slot 9) and `future_A` (slot 7) into `0x160`/`0x180`, and, while
the ramp is still running (`TIMESTAMP < future_A_time`), `initial_A` (slot 6) and
`initial_A_time` (slot 8) into `0x1c0`/`0x1e0`; it returns the interpolated amplification through
the scratch word `0`.

* `aWin`: the bytes it writes, `[0, 0x20) ∪ [0x140, 0x200)`;
* `aBase sevm b`: the base it leaves (the selected storage loads of its path);
* `ALands sevm s b S M d`: **the value contract** — `d` is the base `aBase sevm b` with the
  caller's stack `S` under the returned word `v`, `aChk s t = some v` at the frame's timestamp
  `t`, and the memory keeps the entry memory off `aWin`;
* `a_spec`: every return of a run of entry 27 from `St b (ret :: S) M G` lands as `ALands`,
  given the storage abstraction `Abstracts (b.getStor sevm.currentTarget) s`.

The walk is split at the ramp test: `a_up` (rising ramp, `t_00e3_c27`) and `a_down` (falling
ramp, `t_018a_c27`) hold the two interpolation arms.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-! ## The value contract -/

/-- The bytes `_A` writes: the scratch word `0` and its frame `[0x140, 0x200)`. -/
local notation "aWin" => fun i : Nat => i < 0x20 ∨ (0x140 ≤ i ∧ i < 0x200)

/-- The base `_A` leaves: `future_A_time` and `future_A` loaded, and while the ramp runs
`initial_A` and `initial_A_time` too. -/
def aBase (sevm : Sevm) (b : Devm) : Devm :=
  if sevm.benvStat.time.toNat < (b.getStorVal sevm.currentTarget futureATimeSlot).toNat then
    afterSload sevm (afterSload sevm (afterSload sevm (afterSload sevm b futureATimeSlot)
      futureASlot) initialASlot) initialATimeSlot
  else afterSload sevm (afterSload sevm b futureATimeSlot) futureASlot

/-- **What `_A` leaves**: the amplification `aChk s t` at the frame's timestamp on top of the
caller's stack, over `aBase`, with the entry memory kept off `aWin`. -/
def ALands (sevm : Sevm) (s : State) (b : Devm) (S : List B256) (M : Mem) (d : Devm) : Prop :=
  ∃ v M' G', d = St (aBase sevm b) (v :: S) M' G' ∧
    aChk s sevm.benvStat.time.toNat = some v.toNat ∧ Mem.KeepsOff M M' aWin ∧
    (Mem.Wf M → Mem.Wf M')

/-- The rising arm of `aChk` (lines 160–161). -/
def aUp (a0 a1 t0 t1 t : Nat) : Option Nat := do
  let d ← chkDiv (← chkMul (← chkSub a1 a0) (← chkSub t t0)) (← chkSub t1 t0)
  chkAdd a0 d

/-- The falling arm of `aChk` (line 163). -/
def aDown (a0 a1 t0 t1 t : Nat) : Option Nat := do
  let d ← chkDiv (← chkMul (← chkSub a0 a1) (← chkSub t t0)) (← chkSub t1 t0)
  chkSub a0 d

theorem aChk_eq (s : State) (t : Nat) :
    aChk s t = if t < s.futureATime then
      if s.futureA > s.initialA then aUp s.initialA s.futureA s.initialATime s.futureATime t
      else aDown s.initialA s.futureA s.initialATime s.futureATime t
    else some s.futureA := rfl

/-! ## Walk tactics -/

/-! ## The two ramp arms -/

section Arms

variable {sevm : Sevm} {B : Devm} {S : List B256} {M₀ M : Mem} {G : Nat} {r : Seg}
  {ret ft fa ia it : B256}

/-- The words `_A` carries at the ramp test. -/
abbrev aWords (ret ft fa ia it : B256) : List (Nat × B256) :=
  [(0x1e0, it), (0x1c0, ia), (0x180, fa), (0x160, ft), (0x140, ret)]

-- SEGMENT: aUp
/-- **The rising ramp** (`t_00e3_c27`, lines 160–161). -/
theorem a_up (hT : MemTrack M₀ M aWin (aWords ret ft fa ia it))
    (run : SFunc.RunCut prog sevm [] (St B S M G) t_00e3_c27 r) :
    ∃ v M' G', r = .done (.returned (St B (v :: S) M' G')) ∧
      aUp ia.toNat fa.toNat it.toNat ft.toNat sevm.benvStat.time.toNat = some v.toNat ∧
      Mem.KeepsOff M₀ M' aWin ∧ (Mem.Wf M₀ → Mem.Wf M') := by
  unfold t_00e3_c27 at run
  imload 0x1c0; imload 0x180; imload 0x1c0; istep; istep; istep; istep; istep
  iassert h1
  istep; istep; istep; istep; istep; istep; istep; istep
  imload 0x1e0; istep; istep; istep; istep; istep
  iassert h2
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  istep; istep; istep; istep; istep; istep; istep
  iassert h3
  istep; istep; istep; istep; istep; istep; istep
  imload 0x160; imload 0x1e0; istep; istep; istep; istep; istep
  iassert h4
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  iassert h5
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  iassert h6
  istep; istep; istep; istep; istep; istep; istep
  imstore 0x0; imload 0x0; imload 0x140
  obtain ⟨G', rfl⟩ := ric_ret run
  refine ⟨_, _, G', rfl, ?_, hT.keeps, hT.wf⟩
  simp only [aUp, vyChkSub h1, vyChkSub h2, vyChkMul h3, vyChkSub h4, vyChkDiv h5, vyChkAdd h6,
    Option.bind_eq_bind, Option.bind_some]

-- SEGMENT: aDown
/-- **The falling ramp** (`t_018a_c27`, line 163). -/
theorem a_down (hT : MemTrack M₀ M aWin (aWords ret ft fa ia it))
    (run : SFunc.RunCut prog sevm [] (St B S M G) t_018a_c27 r) :
    ∃ v M' G', r = .done (.returned (St B (v :: S) M' G')) ∧
      aDown ia.toNat fa.toNat it.toNat ft.toNat sevm.benvStat.time.toNat = some v.toNat ∧
      Mem.KeepsOff M₀ M' aWin ∧ (Mem.Wf M₀ → Mem.Wf M') := by
  obtain ⟨_, run⟩ := ric_dest run
  imload 0x1c0; imload 0x1c0; imload 0x180; istep; istep; istep; istep; istep
  iassert h1
  istep; istep; istep; istep; istep; istep; istep; istep
  imload 0x1e0; istep; istep; istep; istep; istep
  iassert h2
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  istep; istep; istep; istep; istep; istep; istep
  iassert h3
  istep; istep; istep; istep; istep; istep; istep
  imload 0x160; imload 0x1e0; istep; istep; istep; istep; istep
  iassert h4
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  iassert h5
  istep; istep; istep; istep; istep; istep; istep; istep; istep; istep; istep
  iassert h6
  istep; istep; istep; istep; istep; istep; istep
  imstore 0x0; imload 0x0; imload 0x140
  obtain ⟨G', rfl⟩ := ric_ret run
  refine ⟨_, _, G', rfl, ?_, hT.keeps, hT.wf⟩
  simp only [aDown, vyChkSub h1, vyChkSub h2, vyChkMul h3, vyChkSub h4, vyChkDiv h5,
    vyChkSub h6, Option.bind_eq_bind, Option.bind_some]

end Arms

/-! ## The contract -/

theorem slot_06 : Bytes.toB256 [0x06] = initialASlot := by decide
theorem slot_07 : Bytes.toB256 [0x07] = futureASlot := by decide
theorem slot_08 : Bytes.toB256 [0x08] = initialATimeSlot := by decide
theorem slot_09 : Bytes.toB256 [0x09] = futureATimeSlot := by decide

-- SEGMENT: aSpec
/-- **`_A`'s contract**: every run of entry 27 from its return address over the caller's stack
returns (it never halts the frame), and lands as `ALands`: `aChk s t` on top of `S`, over the
loads of `aBase`, the memory kept off `aWin`. -/
theorem a_spec {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {ret : B256}
    {s : State} {o : Outcome} (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (run : SFunc.Run prog sevm (St b (ret :: S) M G) t_00a9_c27 o) :
    ∃ d, o = .returned d ∧ ALands sevm s b S M d := by
  have run := run.cut
  have hT := MemTrack.init M aWin
  obtain ⟨_, run⟩ := ric_dest run
  imstore 0x140; istep; istep; imstore 0x160; istep; istep; imstore 0x180
  imload 0x160; istep; istep; istep; istep
  have e1 := ha.futureATime
  have e2 := ha.futureA
  have e3 := ha.initialA
  have e4 := ha.initialATime
  rw [← slot_09] at e1
  rw [← slot_07] at e2
  rw [← slot_06] at e3
  rw [← slot_08] at e4
  rcases ric_branch run with ⟨hw, _, run⟩ | ⟨hw, _, run⟩
  · have ht := ltCheck_iszero_eq hw
    istep; istep; imstore 0x1c0; istep; istep; imstore 0x1e0
    imload 0x1c0; imload 0x180; istep; istep; istep
    simp only [getStorVal_eq_getStor, afterSload_getStor] at ht hT run ⊢
    have hb : aBase sevm b = afterSload sevm (afterSload sevm (afterSload sevm (afterSload sevm b
        (Bytes.toB256 [0x09])) (Bytes.toB256 [0x07])) (Bytes.toB256 [0x06]))
        (Bytes.toB256 [0x08]) := by
      unfold aBase
      rw [← slot_09, ← slot_07, ← slot_06, ← slot_08, getStorVal_eq_getStor, ite_eq_left ht]
    rcases ric_branch run with ⟨hw2, _, run⟩ | ⟨hw2, _, run⟩
    · have hup := gtCheck_iszero_eq hw2
      obtain ⟨v, M', G', hr, hv, hk, hwf⟩ := a_up hT run
      cases hr
      refine ⟨_, rfl, v, M', G', by rw [hb], ?_, hk, hwf⟩
      rw [aChk_eq, ← e1, ← e2, ← e3, ← e4, ite_eq_left ht, ite_eq_left (gt_iff_lt.mpr hup)]
      exact hv
    · have hdn := gtCheck_iszero_ne hw2
      obtain ⟨v, M', G', hr, hv, hk, hwf⟩ := a_down hT run
      cases hr
      refine ⟨_, rfl, v, M', G', by rw [hb], ?_, hk, hwf⟩
      rw [aChk_eq, ← e1, ← e2, ← e3, ← e4, ite_eq_left ht, ite_eq_right (fun h => hdn (gt_iff_lt.mp h))]
      exact hv
  · have ht := ltCheck_iszero_ne hw
    obtain ⟨_, run⟩ := ric_dest run
    imload 0x180; imstore 0x0; imload 0x0; imload 0x140
    obtain ⟨G', hr⟩ := ric_ret run
    cases hr
    simp only [getStorVal_eq_getStor] at ht ⊢
    have hb : aBase sevm b = afterSload sevm (afterSload sevm b (Bytes.toB256 [0x09]))
        (Bytes.toB256 [0x07]) := by
      unfold aBase
      rw [← slot_09, ← slot_07, getStorVal_eq_getStor, ite_eq_right ht]
    exact ⟨_, rfl, _, _, G', by rw [hb], by rw [aChk_eq, ← e1, ← e2, ite_eq_right ht, afterSload_getStor],
      hT.keeps, hT.wf⟩

/-- `_A` changes the world only by warming its storage keys. -/
theorem aBase_sloadsOnly (sevm : Sevm) (b : Devm) : SloadsOnly sevm b (aBase sevm b) := by
  unfold aBase
  split
  · exact ((((SloadsOnly.refl).sload _).sload _).sload _).sload _
  · exact ((SloadsOnly.refl).sload _).sload _

/-! ## Kernel facts over the entry closure -/

theorem prog_27 : prog[27]? = some t_00a9_c27 := by decide +kernel

/-- Entry 27 references no other entry; it is state-silent. -/
theorem a_silentSet : SilentSet prog [27] = true := by decide +kernel

/-- It makes no external call. -/
theorem a_execFreeSet : ExecFreeSet prog [27] = true := by decide +kernel

/-- It never halts the frame (for `ric_pcCall` at its call sites). -/
theorem a_neverHalts : calleeNeverHalts prog 27 8 = true := by decide +kernel

end Blanc.Lift.Curve3Pool
