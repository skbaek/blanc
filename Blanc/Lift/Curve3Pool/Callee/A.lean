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
abbrev aWin : List (Nat × Nat) := [(0, 0x20), (0x140, 0x200)]

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
    Mem.Wf M'

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
      Mem.KeepsOff M₀ M' aWin ∧ Mem.Wf M' := by
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
      Mem.KeepsOff M₀ M' aWin ∧ Mem.Wf M' := by
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

/-! ## Forward twins -/

/-- The word the rising arm returns. -/
def aUpW (a0 a1 t0 t1 t : B256) : B256 := a0 + (a1 - a0) * (t - t0) / (t1 - t0)

/-- The word the falling arm returns. -/
def aDownW (a0 a1 t0 t1 t : B256) : B256 := a0 - (a0 - a1) * (t - t0) / (t1 - t0)

theorem aUp_some {a0 a1 t0 t1 t v : Nat} (h : aUp a0 a1 t0 t1 t = some v) :
    ∃ d e p q r, chkSub a1 a0 = some d ∧ chkSub t t0 = some e ∧ chkMul d e = some p ∧
      chkSub t1 t0 = some q ∧ chkDiv p q = some r ∧ chkAdd a0 r = some v := by
  simp only [aUp, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d, hd, e, he, p, hp, q, hq, r, hr, hv⟩ := h
  exact ⟨d, e, p, q, r, hd, he, hp, hq, hr, hv⟩

theorem aDown_some {a0 a1 t0 t1 t v : Nat} (h : aDown a0 a1 t0 t1 t = some v) :
    ∃ d e p q r, chkSub a0 a1 = some d ∧ chkSub t t0 = some e ∧ chkMul d e = some p ∧
      chkSub t1 t0 = some q ∧ chkDiv p q = some r ∧ chkSub a0 r = some v := by
  simp only [aDown, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d, hd, e, he, p, hp, q, hq, r, hr, hv⟩ := h
  exact ⟨d, e, p, q, r, hd, he, hp, hq, hr, hv⟩

theorem aUpW_toNat {ia fa it ft t : B256} {v : Nat}
    (hv : aUp ia.toNat fa.toNat it.toNat ft.toNat t.toNat = some v) :
    (aUpW ia fa it ft t).toNat = v := by
  obtain ⟨d, e, p, q, r, hd, he, hp, hq, hr, hvv⟩ := aUp_some hv
  obtain ⟨-, rfl⟩ := fwdChkSub hd
  obtain ⟨-, rfl⟩ := fwdChkSub he
  obtain ⟨-, rfl⟩ := fwdChkMul hp
  obtain ⟨-, rfl⟩ := fwdChkSub hq
  obtain ⟨-, rfl⟩ := fwdChkDiv hr
  obtain ⟨-, rfl⟩ := fwdChkAdd hvv
  rfl

theorem aDownW_toNat {ia fa it ft t : B256} {v : Nat}
    (hv : aDown ia.toNat fa.toNat it.toNat ft.toNat t.toNat = some v) :
    (aDownW ia fa it ft t).toNat = v := by
  obtain ⟨d, e, p, q, r, hd, he, hp, hq, hr, hvv⟩ := aDown_some hv
  obtain ⟨-, rfl⟩ := fwdChkSub hd
  obtain ⟨-, rfl⟩ := fwdChkSub he
  obtain ⟨-, rfl⟩ := fwdChkMul hp
  obtain ⟨-, rfl⟩ := fwdChkSub hq
  obtain ⟨-, rfl⟩ := fwdChkDiv hr
  obtain ⟨-, rfl⟩ := fwdChkSub hvv
  rfl

section ArmsFwd

variable {sevm : Sevm} {B : Devm} {S : List B256} {M₀ M : Mem} {G n v : Nat}
  {ret ft fa ia it : B256}

-- SEGMENT: aUpExact
/-- **The rising ramp, forward** (`357` gas over a covered memory). -/
theorem a_up_exact (hT : MemTrack M₀ M aWin (aWords ret ft fa ia it)) (hS : M.size = n)
    (hn : n % 32 = 0) (htop : 0x200 ≤ n) (hroom : S.length + 16 < 1024)
    (hv : aUp ia.toNat fa.toNat it.toNat ft.toNat sevm.benvStat.time.toNat = some v) :
    (∃ M', SFunc.RunExactCut prog sevm [] (St B S M (G + 357)) t_00e3_c27
      (.done (.returned (St B (aUpW ia fa it ft sevm.benvStat.time :: S) M' G))) ∧
      (Mem.KeepsOff M₀ M' aWin ∧ Mem.Wf M' ∧ M'.size = n)) ∧
      (aUpW ia fa it ft sevm.benvStat.time).toNat = v := by
  obtain ⟨d, e, p, q, r, hd, he, hp, hq, hr, hvv⟩ := aUp_some hv
  obtain ⟨g1, rfl⟩ := fwdChkSub hd
  obtain ⟨g2, rfl⟩ := fwdChkSub he
  obtain ⟨g3, rfl⟩ := fwdChkMul hp
  obtain ⟨g4, rfl⟩ := fwdChkSub hq
  obtain ⟨g5, rfl⟩ := fwdChkDiv hr
  obtain ⟨g6, rfl⟩ := fwdChkAdd hvv
  refine ⟨?_, rfl⟩
  xmload 0x1c0; xmload 0x180; xmload 0x1c0; xstep; xstep; xstep; xstep; xstep
  xassert g1
  xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xmload 0x1e0; xstep; xstep; xstep; xstep; xstep
  xassert g2
  xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xassert g3
  xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xmload 0x160; xmload 0x1e0; xstep; xstep; xstep; xstep; xstep
  xassert g4
  xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xassert g5
  xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xassert g6
  xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xmstore 0x0; xmload 0x0; xmload 0x140
  xret

-- SEGMENT: aDownExact
/-- **The falling ramp, forward** (`352` gas over a covered memory). -/
theorem a_down_exact (hT : MemTrack M₀ M aWin (aWords ret ft fa ia it)) (hS : M.size = n)
    (hn : n % 32 = 0) (htop : 0x200 ≤ n) (hroom : S.length + 16 < 1024)
    (hv : aDown ia.toNat fa.toNat it.toNat ft.toNat sevm.benvStat.time.toNat = some v) :
    (∃ M', SFunc.RunExactCut prog sevm [] (St B S M (G + 352)) t_018a_c27
      (.done (.returned (St B (aDownW ia fa it ft sevm.benvStat.time :: S) M' G))) ∧
      (Mem.KeepsOff M₀ M' aWin ∧ Mem.Wf M' ∧ M'.size = n)) ∧
      (aDownW ia fa it ft sevm.benvStat.time).toNat = v := by
  obtain ⟨d, e, p, q, r, hd, he, hp, hq, hr, hvv⟩ := aDown_some hv
  obtain ⟨g1, rfl⟩ := fwdChkSub hd
  obtain ⟨g2, rfl⟩ := fwdChkSub he
  obtain ⟨g3, rfl⟩ := fwdChkMul hp
  obtain ⟨g4, rfl⟩ := fwdChkSub hq
  obtain ⟨g5, rfl⟩ := fwdChkDiv hr
  obtain ⟨g6, rfl⟩ := fwdChkSub hvv
  refine ⟨?_, rfl⟩
  xstep
  xmload 0x1c0; xmload 0x1c0; xmload 0x180; xstep; xstep; xstep; xstep; xstep
  xassert g1
  xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xmload 0x1e0; xstep; xstep; xstep; xstep; xstep
  xassert g2
  xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xassert g3
  xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xmload 0x160; xmload 0x1e0; xstep; xstep; xstep; xstep; xstep
  xassert g4
  xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xassert g5
  xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xassert g6
  xstep; xstep; xstep; xstep; xstep; xstep; xstep
  xmstore 0x0; xmload 0x0; xmload 0x140
  xret

end ArmsFwd

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
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hwf : Mem.Wf M)
    (run : SFunc.Run prog sevm (St b (ret :: S) M G) t_00a9_c27 o) :
    ∃ d, o = .returned d ∧ ALands sevm s b S M d := by
  have run := run.cut
  have hT := MemTrack.init hwf aWin
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

/-! ## The forward contract -/

/-- **`_A`'s gas**: the instruction charges of its path (`85` outside a ramp, `458` rising,
`453` falling) and its storage loads, warm or cold. -/
def aGas (sevm : Sevm) (b : Devm) : Nat :=
  if sevm.benvStat.time.toNat < (b.getStorVal sevm.currentTarget futureATimeSlot).toNat then
    (if (b.getStorVal sevm.currentTarget futureASlot).toNat >
        (b.getStorVal sevm.currentTarget initialASlot).toNat then 458 else 453) +
      sloadCost sevm b futureATimeSlot +
      sloadCost sevm (afterSload sevm b futureATimeSlot) futureASlot +
      sloadCost sevm (afterSload sevm (afterSload sevm b futureATimeSlot) futureASlot)
        initialASlot +
      sloadCost sevm (afterSload sevm (afterSload sevm (afterSload sevm b futureATimeSlot)
        futureASlot) initialASlot) initialATimeSlot
  else 85 + sloadCost sevm b futureATimeSlot +
    sloadCost sevm (afterSload sevm b futureATimeSlot) futureASlot

-- SEGMENT: aExact
/-- **`_A`, forward**: when `aChk s t = some v`, entry 27 runs from its return address over a
memory covering its frame (`0x200 ≤ M.size`, word aligned) and returns a word reading `v` over
`aBase`, at gas `aGas`, the memory kept off `aWin` with its size. -/
theorem a_exact {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G n v : Nat} {ret : B256}
    {s : State} (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hA : aChk s sevm.benvStat.time.toNat = some v) (hwf : Mem.Wf M) (hS : M.size = n)
    (hn : n % 32 = 0) (htop : 0x200 ≤ n) (hroom : S.length + 16 < 1024) :
    ∃ w, (∃ M', SFunc.RunExact prog sevm (St b (ret :: S) M (G + aGas sevm b)) t_00a9_c27
      (.returned (St (aBase sevm b) (w :: S) M' G)) ∧
      (Mem.KeepsOff M M' aWin ∧ Mem.Wf M' ∧ M'.size = n)) ∧ w.toNat = v := by
  have hT := MemTrack.init hwf aWin
  have e1 := ha.futureATime
  have e2 := ha.futureA
  have e3 := ha.initialA
  have e4 := ha.initialATime
  rw [aChk_eq, ← e1, ← e2, ← e3, ← e4] at hA
  simp only [← getStorVal_eq_getStor] at hA
  unfold aGas aBase
  by_cases ht : sevm.benvStat.time.toNat <
      (b.getStorVal sevm.currentTarget futureATimeSlot).toNat
  · simp only [ht, ↓reduceIte] at hA ⊢
    by_cases hup : (b.getStorVal sevm.currentTarget futureASlot).toNat >
        (b.getStorVal sevm.currentTarget initialASlot).toNat
    · simp only [hup, ↓reduceIte] at hA ⊢
      rw [show ∀ x1 x2 x3 x4 : Nat, G + (458 + x1 + x2 + x3 + x4) =
        G + 394 + x4 + 9 + x3 + 36 + x2 + 9 + x1 + 10 from fun _ _ _ _ => by omega]
      simp only [SFunc.runExact_iff_runExactCut_nil]
      simp only [← slot_09, ← slot_07, ← slot_06, ← slot_08] at ht hup hA ⊢
      refine ⟨?w1, ?run1, ?val1⟩
      case run1 =>
        xstep; xmstore 0x140; xstep; xstep; xmstore 0x160; xstep; xstep; xmstore 0x180
        xmload 0x160; xstep; xstep; xstep; xstep
        xzero (ltCheck_iszero_of_lt ht)
        xstep; xstep; xmstore 0x1c0; xstep; xstep; xmstore 0x1e0
        xmload 0x1c0; xmload 0x180; xstep; xstep; xstep
        xzero (by simp only [afterSload_getStorVal]; exact gtCheck_iszero_of_lt hup)
        exact (a_up_exact hT hS hn htop hroom (by simpa only [afterSload_getStorVal] using hA)).1
      case val1 => exact aUpW_toNat (by simpa only [afterSload_getStorVal] using hA)
    · simp only [hup, ↓reduceIte] at hA ⊢
      rw [show ∀ x1 x2 x3 x4 : Nat, G + (453 + x1 + x2 + x3 + x4) =
        G + 389 + x4 + 9 + x3 + 36 + x2 + 9 + x1 + 10 from fun _ _ _ _ => by omega]
      simp only [SFunc.runExact_iff_runExactCut_nil]
      simp only [← slot_09, ← slot_07, ← slot_06, ← slot_08] at ht hup hA ⊢
      refine ⟨?w2, ?run2, ?val2⟩
      case run2 =>
        xstep; xmstore 0x140; xstep; xstep; xmstore 0x160; xstep; xstep; xmstore 0x180
        xmload 0x160; xstep; xstep; xstep; xstep
        xzero (ltCheck_iszero_of_lt ht)
        xstep; xstep; xmstore 0x1c0; xstep; xstep; xmstore 0x1e0
        xmload 0x1c0; xmload 0x180; xstep; xstep; xstep
        refine Blanc.Lift.xlift (fun _ k => rxc_branch_succ
          (by simp only [afterSload_getStorVal]; exact gtCheck_iszero_of_not_lt hup) k) ?_
        exact (a_down_exact hT hS hn htop hroom (by simpa only [afterSload_getStorVal] using hA)).1
      case val2 => exact aDownW_toNat (by simpa only [afterSload_getStorVal] using hA)
  · simp only [ht, ↓reduceIte] at hA ⊢
    rw [show ∀ x1 x2 : Nat, G + (85 + x1 + x2) = G + 66 + x2 + 9 + x1 + 10 from
      fun _ _ => by omega]
    simp only [SFunc.runExact_iff_runExactCut_nil]
    simp only [← slot_09, ← slot_07] at ht hA ⊢
    refine ⟨?w3, ?run3, ?val3⟩
    case run3 =>
      xstep; xmstore 0x140; xstep; xstep; xmstore 0x160; xstep; xstep; xmstore 0x180
      xmload 0x160; xstep; xstep; xstep; xstep
      xassert (ltCheck_iszero_of_not_lt ht)
      xmload 0x180; xmstore 0x0; xmload 0x0; xmload 0x140
      xret
    case val3 =>
      simp only [afterSload_getStorVal]
      exact (Option.some.inj hA)

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

/-- It never halts the frame (for `ric_pcCall` at its call sites). -/
theorem a_neverHalts : calleeNeverHalts prog 27 8 = true := by decide +kernel

end Blanc.Lift.Curve3Pool
