-- DripMachine.lean : DRIP's shared fresh-index machine, inverted.
--
-- All five endpoints stage their operands into contract-owned scratch words
-- and tail-call one machine: guard the stored index and clock, compute the
-- elapsed exponent, run the Maker-shaped square-and-multiply loop with its
-- exact inline overflow checks, floor-compose the factor onto the stored
-- index, and return through the route dispatcher.  This module inverts a
-- *successful* run of that machine into the guards it must have crossed and
-- the exact word it must have produced.
--
-- Everything here is source-level `Func.Run`.  The deployed-byte lift is
-- `Blanc.correct`, consumed once in `Blanc/DripFunctional.lean`; there is no
-- second compiled walk of the same body.

import Blanc.Drip
import Blanc.FuncMainPrefix
import Blanc.Ladder
import Blanc.MachineDataFacts
import Blanc.RunPrefix
import Jaune.RPow

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Drip

/-! ## The scratch image

DRIP's machine keeps its whole working state in fixed 32-byte scratch words
rather than on the EVM stack, so the walk's invariant is a byte image plus
`Mem.Wf`.  These two definitions and their read-over-write laws are the only
memory vocabulary the rest of the module needs. -/

/-- The word DRIP's machine reads back from scratch slot `w`. -/
def scratch (image : Bytes) (w : B256) : B256 :=
  Bytes.toB256 (image.sliceD (w * 32).toNat 32 0)

/-- The image after DRIP's machine writes `v` into scratch slot `w`. -/
def setScratch (image : Bytes) (w v : B256) : Bytes :=
  Bytes.writeAt image (w * 32).toNat v.toBytes

/-- Two scratch slots are disjoint exactly when their 32-byte windows are.
Every DRIP slot is a distinct small multiple of 32, so each instance is a
closed decision. -/
def SlotsDisjoint (w w' : B256) : Prop :=
  (w * 32).toNat + 32 ≤ (w' * 32).toNat ∨ (w' * 32).toNat + 32 ≤ (w * 32).toNat

instance decidableSlotsDisjoint (w w' : B256) :
    Decidable (SlotsDisjoint w w') :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem SlotsDisjoint.symm {w w' : B256} (h : SlotsDisjoint w w') :
    SlotsDisjoint w' w := Or.symm h

@[simp] theorem scratch_setScratch_self (image : Bytes) (w v : B256) :
    scratch (setScratch image w v) w = v :=
  Bytes.readWord_writeAt_self image (w * 32).toNat v

theorem scratch_setScratch_of_disjoint (image : Bytes) {w w' : B256}
    (v : B256) (h : SlotsDisjoint w w') :
    scratch (setScratch image w' v) w = scratch image w := by
  unfold scratch setScratch
  rw [Bytes.readWord_writeAt_of_disjoint image (w * 32).toNat (w' * 32).toNat v h]

/-! ## The machine frame

`Frame image base s` is what every step of the walk carries: `s`'s memory is
well-formed and reads as `image`, and `s` agrees with the machine's entry
state `base` on everything the machine may not disturb before it commits. -/

structure Frame (image : Bytes) (base s : Devm) : Prop where
  wf : Mem.Wf s.memory
  reads : Mem.Reads s.memory image
  state : base.state = s.state
  logs : base.logs = s.logs

theorem Frame.line {image : Bytes} {base s t : Devm} {e : Sevm} {l : Line}
    (frame : Frame image base s)
    (hstate : Line.Inv Devm.state l) (hmemory : Line.Inv Devm.memory l)
    (hlogs : Line.Inv Devm.logs l)
    (run : Line.Run e s l t) : Frame image base t where
  wf := by rw [← Line.of_inv Devm.memory hmemory run]; exact frame.wf
  reads := by rw [← Line.of_inv Devm.memory hmemory run]; exact frame.reads
  state := frame.state.trans (Line.of_inv Devm.state hstate run)
  logs := frame.logs.trans (Line.of_inv Devm.logs hlogs run)

theorem Frame.of_popBurn {image : Bytes} {base s t : Devm} {xs : List B256}
    (frame : Frame image base s) (pop : Devm.PopBurn xs s t) :
    Frame image base t where
  wf := by rw [← pop.memory]; exact frame.wf
  reads := by rw [← pop.memory]; exact frame.reads
  state := frame.state.trans pop.state
  logs := frame.logs.trans pop.logs

theorem Frame.of_burn {image : Bytes} {base s t : Devm}
    (frame : Frame image base s) (burn : Devm.Burn s t) :
    Frame image base t where
  wf := by rw [← burn.memory]; exact frame.wf
  reads := by rw [← burn.memory]; exact frame.reads
  state := frame.state.trans burn.state
  logs := frame.logs.trans burn.logs

/-- One `loadWord` step pushes the addressed scratch word and preserves the
frame. -/
theorem Frame.loadWord {image : Bytes} {base s t : Devm} {e : Sevm}
    {w : B256} {tail : Stack}
    (frame : Frame image base s) (hp : tail <<+ s.stack)
    (run : Line.Run e s (Drip.loadWord w) t) :
    (scratch image w :: tail <<+ t.stack) ∧ Frame image base t := by
  obtain ⟨hstack, hwf, hreads, hstate⟩ :=
    of_run_loadWordAt_image (word := w) (value := scratch image w) hp
      frame.wf frame.reads rfl run
  exact ⟨hstack,
    ⟨hwf, hreads, frame.state.trans hstate,
      frame.logs.trans (of_run_loadWordAt_logs run)⟩⟩

/-- One `mstoreAt` step consumes the stack top into the scratch image. -/
theorem Frame.mstoreAt {image : Bytes} {base s t : Devm} {e : Sevm}
    {w v : B256} {tail : Stack}
    (frame : Frame image base s) (hp : v :: tail <<+ s.stack)
    (run : Line.Run e s (mstoreAt w) t) :
    (tail <<+ t.stack) ∧ Frame (setScratch image w v) base t := by
  obtain ⟨hstack, hwf, hreads, hstate⟩ :=
    of_run_mstoreAt_image hp frame.wf frame.reads run
  exact ⟨hstack,
    ⟨hwf, hreads, frame.state.trans hstate,
      frame.logs.trans (Line.of_inv Devm.logs (by line_inv) run)⟩⟩

/-- Every `loadWord` line is gas-free: `push` plus `mload`. -/
theorem gasFree_loadWord (w : B256) : Line.gasFree (loadWord w) = true := by
  simp only [loadWord, Line.gasFree, Ninst.pushB256, Ninst.gasFree,
    Rinst.gasFree, Bool.true_and]

/-- Every `mstoreAt` line is gas-free: `push` plus `mstore`. -/
theorem gasFree_mstoreAt (w : B256) : Line.gasFree (mstoreAt w) = true := by
  simp only [mstoreAt, Line.gasFree, Ninst.pushB256, Ninst.gasFree,
    Rinst.gasFree, Bool.true_and]

/-! ## The guard shape

Every DRIP check computes one flag and takes `.revert <?> continuation`.  A
successful run therefore forces the flag to zero — the rejecting arm is the
inline `Func.revert`, which has no successful run at all — and continues in
the fall-through with the flag popped. -/

theorem of_run_guard_prefix {fs : List Func} {e : Sevm} {s r : Devm}
    {flag : B256} {tail : Stack} {cont : Func} {path : Prog.SourcePath}
    (hp : flag :: tail <<+ s.stack)
    (run : Func.Run fs e s (.revert <?> cont) r) :
    flag = 0 ∧ ∃ t target, (tail <<+ t.stack) ∧ Devm.PopBurn [0] s t ∧
      Func.RunPrefix fs e path s (.revert <?> cont) target t cont ∧
      Func.Run fs e t cont r := by
  rcases run_prefix_branch run with
    ⟨t, mid, hpop, hcont, hpre⟩ | ⟨w, t, u, mid, hnz, hpop, hburn, hrev⟩
  · rcases popBurn_pref hpop hp with ⟨hflag, htail⟩
    exact ⟨hflag.symm, t, mid, htail, hpop, hpre, hcont⟩
  · exact absurd hrev.1 not_run_revert

theorem of_run_guard {fs : List Func} {e : Sevm} {s r : Devm}
    {flag : B256} {tail : Stack} {cont : Func}
    (hp : flag :: tail <<+ s.stack)
    (run : Func.Run fs e s (.revert <?> cont) r) :
    flag = 0 ∧ ∃ t, (tail <<+ t.stack) ∧ Devm.PopBurn [0] s t ∧
      Func.Run fs e t cont r := by
  obtain ⟨hflag, t, _, htail, hpop, _, hcont⟩ :=
    of_run_guard_prefix (path := ⟨0, []⟩) hp run
  exact ⟨hflag, t, htail, hpop, hcont⟩

/-- `TIMESTAMP` is a push-item instruction; the shared observation-invariance
instances do not currently reach its memory column, so the frame step is
built from the push directly. -/
theorem Frame.timestamp {image : Bytes} {base s t : Devm} {e : Sevm}
    (frame : Frame image base s) (run : Ninst.Run e s Ninst.timestamp t) :
    Frame image base t := by
  change Ninst.Run e s (.reg .timestamp) t at run
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  have hpb := Devm.pushBurn_of_pushItem hrun
  exact ⟨by rw [← hpb.memory]; exact frame.wf,
    by rw [← hpb.memory]; exact frame.reads,
    frame.state.trans hpb.state, frame.logs.trans hpb.logs⟩

/-! ## Reading a zero flag

Each DRIP guard's fall-through says its flag word is zero.  The following comparison adapter turns
that word back into the equality it stands for; unsigned-order flags use
`B256.not_lt_of_ltCheck_eq_zero` from the common library. -/

private theorem eq_of_iszero_eqCheck_eq_zero {x y : B256}
    (h : ((x =? y) =? 0) = 0) : x = y := by
  by_contra hne
  simp only [B256.eqCheck, if_neg hne] at h
  exact absurd h (by decide +kernel)

private theorem nofm_right_zero (x : B256) : B256.Nofm x 0 := by
  unfold B256.Nofm
  rw [B256.toNat_zero, Nat.mul_zero]
  positivity

/-! ## The guarded rounded multiply

`guardedRoundedMul L R O next` is the Maker-shaped rounded multiplication with
its two inline overflow checks: the division-recovery check that the product
did not truncate, and the `sum < addend` check that adding the half-up offset
did not wrap.  A successful run therefore *proves* Jaune's two word-level
premises rather than assuming them, and leaves exactly `B256.mulr` in the
output slot. -/

private theorem of_run_roundedMulRecovery_prefix {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    {leftWord rightWord : B256} {next : Func} {path : Prog.SourcePath}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (roundedMulRecovery leftWord rightWord +++ next) r) :
    ∃ t target, Frame image entry t ∧
      (((scratch image leftWord =?
        ((scratch image rightWord * scratch image leftWord) / scratch image rightWord)) =? 0) ::
        scratch image rightWord * scratch image leftWord :: tail <<+ t.stack) ∧
      Func.RunPrefix fs e path s (roundedMulRecovery leftWord rightWord +++ next)
        target t next ∧
      Func.Run fs e t next r := by
  by_cases same : leftWord = rightWord
  · subst rightWord
    simp only [roundedMulRecovery] at run ⊢
    rcases run_prefix_prepend (l := loadWord leftWord) (path := path)
      (gasFree_loadWord leftWord) run with
      ⟨s1, mid1, hline1, run, hpre1⟩
    obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
    rcases run_prefix_prepend
      (l := [dup 0, dup 0, mul, dup 0, dup 2, swap 0, div, swap 0, swap 1, eq,
        iszero]) (path := mid1)
      (by decide : Line.gasFree [dup 0, dup 0, mul, dup 0, dup 2, swap 0, div,
        swap 0, swap 1, eq, iszero] = true) run with
      ⟨s2, mid2, hline2, run, hpre2⟩
    have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
    let x := scratch image leftWord
    let p := x * x
    have hp2 : ((x =? (p / x)) =? 0) :: p :: tail <<+ s2.stack := by
      rcases Line.of_run_cons hline2 with ⟨t1, hd1, rest⟩
      rcases Line.of_run_cons rest with ⟨t2, hd2, rest⟩
      rcases Line.of_run_cons rest with ⟨t3, hm, rest⟩
      rcases Line.of_run_cons rest with ⟨t4, hd3, rest⟩
      rcases Line.of_run_cons rest with ⟨t5, hd4, rest⟩
      rcases Line.of_run_cons rest with ⟨t6, hs1, rest⟩
      rcases Line.of_run_cons rest with ⟨t7, hv, rest⟩
      rcases Line.of_run_cons rest with ⟨t8, hs2, rest⟩
      rcases Line.of_run_cons rest with ⟨t9, hs3, rest⟩
      rcases Line.of_run_cons rest with ⟨t10, he, rest⟩
      rcases Line.of_run_cons rest with ⟨t11, hz, hnil⟩
      cases hnil
      have h1 : x :: x :: tail <<+ t1.stack := prefix_of_dup_val hd1 (by show_nth) hp1
      have h2 : x :: x :: x :: tail <<+ t2.stack := prefix_of_dup_val hd2 (by show_nth) h1
      have h3 : p :: x :: tail <<+ t3.stack := prefix_of_mul hm h2
      have h4 : p :: p :: x :: tail <<+ t4.stack := prefix_of_dup_val hd3 (by show_nth) h3
      have h5 : x :: p :: p :: x :: tail <<+ t5.stack := prefix_of_dup_val hd4 (by show_nth) h4
      have h6 : p :: x :: p :: x :: tail <<+ t6.stack :=
        Stack.prefix_of_swap (show Stack.Swap 0
          (x :: p :: p :: x :: tail) (p :: x :: p :: x :: tail)
          from Stack.swapCore_zero) (of_run_swap hs1) h5
      have h7 : (p / x) :: p :: x :: tail <<+ t7.stack := prefix_of_div hv h6
      have h8 : p :: (p / x) :: x :: tail <<+ t8.stack :=
        Stack.prefix_of_swap (show Stack.Swap 0
          ((p / x) :: p :: x :: tail) (p :: (p / x) :: x :: tail)
          from Stack.swapCore_zero) (of_run_swap hs2) h7
      have h9 : x :: (p / x) :: p :: tail <<+ t9.stack :=
        Stack.prefix_of_swap (show Stack.Swap 1
          (p :: (p / x) :: x :: tail) (x :: (p / x) :: p :: tail)
          from Stack.swapCore_succ Stack.swapCore_zero) (of_run_swap hs3) h8
      exact prefix_of_iszero hz (prefix_of_eq he h9)
    exact ⟨s2, mid2, frame2, hp2, Func.RunPrefix.trans hpre1 hpre2, run⟩
  · simp only [roundedMulRecovery, if_neg same] at run ⊢
    rcases run_prefix_prepend (l := loadWord leftWord) (path := path)
      (gasFree_loadWord leftWord) run with
      ⟨s1, mid1, hline1, run, hpre1⟩
    obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
    rcases run_prefix_prepend (l := loadWord rightWord) (path := mid1)
      (gasFree_loadWord rightWord) run with
      ⟨s2, mid2, hline2, run, hpre2⟩
    obtain ⟨hp2, frame2⟩ := frame1.loadWord hp1 hline2
    rcases run_prefix_prepend (l := [mul, dup 0]) (path := mid2)
      (by decide : Line.gasFree [mul, dup 0] = true) run with
      ⟨s3, mid3, hline3, run, hpre3⟩
    have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
    have hp3 : scratch image rightWord * scratch image leftWord ::
        scratch image rightWord * scratch image leftWord :: tail <<+ s3.stack := by
      rcases Line.of_run_cons hline3 with ⟨u, hmul, hrest⟩
      rcases Line.of_run_cons hrest with ⟨v, hdup, hnil⟩
      cases hnil
      exact prefix_of_dup_val hdup (by show_nth) (prefix_of_mul hmul hp2)
    rcases run_prefix_prepend (l := loadWord rightWord) (path := mid3)
      (gasFree_loadWord rightWord) run with
      ⟨s4, mid4, hline4, run, hpre4⟩
    obtain ⟨hp4, frame4⟩ := frame3.loadWord hp3 hline4
    rcases run_prefix_prepend (l := [swap 0, div]) (path := mid4)
      (by decide : Line.gasFree [swap 0, div] = true) run with
      ⟨s5, mid5, hline5, run, hpre5⟩
    have frame5 := frame4.line (by line_inv) (by line_inv) (by line_inv) hline5
    have hp5 : (scratch image rightWord * scratch image leftWord) /
          scratch image rightWord ::
        scratch image rightWord * scratch image leftWord :: tail <<+ s5.stack := by
      rcases Line.of_run_cons hline5 with ⟨u, hswap, hrest⟩
      rcases Line.of_run_cons hrest with ⟨v, hdiv, hnil⟩
      cases hnil
      have hswapped :
          scratch image rightWord * scratch image leftWord ::
            scratch image rightWord ::
              scratch image rightWord * scratch image leftWord :: tail <<+
            u.stack :=
        Stack.prefix_of_swap
          (show Stack.Swap 0
              (scratch image rightWord ::
                scratch image rightWord * scratch image leftWord ::
                  scratch image rightWord * scratch image leftWord :: tail)
              (scratch image rightWord * scratch image leftWord ::
                scratch image rightWord ::
                  scratch image rightWord * scratch image leftWord :: tail)
            from Stack.swapCore_zero)
          (of_run_swap hswap) hp4
      exact prefix_of_div hdiv hswapped
    rcases run_prefix_prepend (l := loadWord leftWord) (path := mid5)
      (gasFree_loadWord leftWord) run with
      ⟨s6, mid6, hline6, run, hpre6⟩
    obtain ⟨hp6, frame6⟩ := frame5.loadWord hp5 hline6
    rcases run_prefix_prepend (l := [eq, iszero]) (path := mid6)
      (by decide : Line.gasFree [eq, iszero] = true) run with
      ⟨s7, mid7, hline7, run, hpre7⟩
    have frame7 := frame6.line (by line_inv) (by line_inv) (by line_inv) hline7
    have hp7 : ((scratch image leftWord =?
          ((scratch image rightWord * scratch image leftWord) /
            scratch image rightWord)) =? 0) ::
        scratch image rightWord * scratch image leftWord :: tail <<+ s7.stack := by
      rcases Line.of_run_cons hline7 with ⟨u, heq, hrest⟩
      rcases Line.of_run_cons hrest with ⟨v, hiszero, hnil⟩
      cases hnil
      exact prefix_of_iszero hiszero (prefix_of_eq heq hp6)
    exact ⟨s7, mid7, frame7, hp7,
      Func.RunPrefix.trans hpre1 (Func.RunPrefix.trans hpre2
        (Func.RunPrefix.trans hpre3 (Func.RunPrefix.trans hpre4
          (Func.RunPrefix.trans hpre5 (Func.RunPrefix.trans hpre6 hpre7))))),
      run⟩

private theorem of_run_roundedMulRecovery {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    {leftWord rightWord : B256} {next : Func}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (roundedMulRecovery leftWord rightWord +++ next) r) :
    ∃ t, Frame image entry t ∧
      (((scratch image leftWord =?
        ((scratch image rightWord * scratch image leftWord) / scratch image rightWord)) =? 0) ::
        scratch image rightWord * scratch image leftWord :: tail <<+ t.stack) ∧
      Func.Run fs e t next r := by
  obtain ⟨t, _, frt, hpt, _, run⟩ :=
    of_run_roundedMulRecovery_prefix (path := ⟨0, []⟩) frame hp run
  exact ⟨t, frt, hpt, run⟩

theorem of_run_guardedRoundedMul_prefix {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    {leftWord rightWord outputWord : B256} {next : Func}
    {path : Prog.SourcePath}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s
      (guardedRoundedMul leftWord rightWord outputWord next) r) :
    ∃ t target,
      B256.Nofm (scratch image leftWord) (scratch image rightWord) ∧
      B256.Nof (scratch image rightWord * scratch image leftWord) half ∧
      (tail <<+ t.stack) ∧
      Frame
        (setScratch image outputWord
          ((half + scratch image rightWord * scratch image leftWord) / scale))
        entry t ∧
      Func.RunPrefix fs e path s
        (guardedRoundedMul leftWord rightWord outputWord next) target t next ∧
      Func.Run fs e t next r := by
  unfold guardedRoundedMul at run
  obtain ⟨s7, mid7, frame7, hp7, hpre7, run⟩ :=
    of_run_roundedMulRecovery_prefix (path := path) frame hp run
  obtain ⟨hflag1, s8, mid8, hp8, hpop8, hpre8, run⟩ :=
    of_run_guard_prefix (path := mid7) hp7 run
  have frame8 := frame7.of_popBurn hpop8
  have hrecover := eq_of_iszero_eqCheck_eq_zero hflag1
  have hnofm : B256.Nofm (scratch image leftWord) (scratch image rightWord) := by
    by_cases hzero : scratch image rightWord = 0
    · rw [hzero]
      exact nofm_right_zero _
    · refine (B256.mul_div_eq_iff_nofm hzero).1 ?_
      rw [B256.mul_comm (scratch image leftWord)]
      exact hrecover.symm
  rcases run_prefix_prepend (l := [dup 0, pushB256 half, add, dup 0]) (path := mid8)
    (by decide : Line.gasFree [dup 0, pushB256 half, add, dup 0] = true) run with
    ⟨s9, mid9, hline9, run, hpre9⟩
  have frame9 := frame8.line (by line_inv) (by line_inv) (by line_inv) hline9
  have hp9 : (half + scratch image rightWord * scratch image leftWord) ::
      (half + scratch image rightWord * scratch image leftWord) ::
      (scratch image rightWord * scratch image leftWord) :: tail <<+ s9.stack := by
    rcases Line.of_run_cons hline9 with ⟨u1, hdup1, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hadd, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u4, hdup2, hnil⟩
    cases hnil
    have h1 := prefix_of_dup_val hdup1 (by show_nth) hp8
    have h2 := prefix_of_push (of_run_pushB256 hpush) h1
    have h3 := prefix_of_add hadd h2
    exact prefix_of_dup_val hdup2 (by show_nth) h3
  -- Keep the rounded sum beneath the overflow flag without a scratch write.
  rcases run_prefix_prepend (l := [swap 1, swap 0]) (path := mid9)
    (by decide : Line.gasFree [swap 1, swap 0] = true) run with
    ⟨s10, mid10, hline10, run, hpre10⟩
  have frame10 := frame9.line (by line_inv) (by line_inv) (by line_inv) hline10
  have hp10 : (half + scratch image rightWord * scratch image leftWord) ::
      (scratch image rightWord * scratch image leftWord) ::
      (half + scratch image rightWord * scratch image leftWord) :: tail <<+
      s10.stack := by
    rcases Line.of_run_cons hline10 with ⟨u, hswap1, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hswap0, hnil⟩
    cases hnil
    have h1 : (scratch image rightWord * scratch image leftWord) ::
        (half + scratch image rightWord * scratch image leftWord) ::
        (half + scratch image rightWord * scratch image leftWord) :: tail <<+
        u.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 1
          ((half + scratch image rightWord * scratch image leftWord) ::
            (half + scratch image rightWord * scratch image leftWord) ::
            (scratch image rightWord * scratch image leftWord) :: tail)
          ((scratch image rightWord * scratch image leftWord) ::
            (half + scratch image rightWord * scratch image leftWord) ::
            (half + scratch image rightWord * scratch image leftWord) :: tail)
          from Stack.swapCore_succ Stack.swapCore_zero)
        (of_run_swap hswap1) hp9
    exact Stack.prefix_of_swap
      (show Stack.Swap 0
        ((scratch image rightWord * scratch image leftWord) ::
          (half + scratch image rightWord * scratch image leftWord) ::
          (half + scratch image rightWord * scratch image leftWord) :: tail)
        ((half + scratch image rightWord * scratch image leftWord) ::
          (scratch image rightWord * scratch image leftWord) ::
          (half + scratch image rightWord * scratch image leftWord) :: tail)
        from Stack.swapCore_zero)
      (of_run_swap hswap0) h1
  rcases run_prefix_prepend (l := [lt]) (path := mid10)
    (by decide : Line.gasFree [lt] = true) run with
    ⟨s11, mid11, hline11, run, hpre11⟩
  have frame11 := frame10.line (by line_inv) (by line_inv) (by line_inv) hline11
  have hp11 : ((half + scratch image rightWord * scratch image leftWord) <?
      (scratch image rightWord * scratch image leftWord)) ::
      (half + scratch image rightWord * scratch image leftWord) :: tail <<+ s11.stack :=
    prefix_of_lt (of_run_singleton hline11) hp10
  obtain ⟨hflag2, s12, mid12, hp12, hpop12, hpre12, run⟩ :=
    of_run_guard_prefix (path := mid11) hp11 run
  have frame12 := frame11.of_popBurn hpop12
  have hnof : B256.Nof (scratch image rightWord * scratch image leftWord) half := by
    by_contra hcontra
    exact B256.not_lt_of_ltCheck_eq_zero hflag2
      (by rw [B256.add_comm]; exact (B256.add_lt_iff_not_nof _ _).2 hcontra)
  rcases run_prefix_prepend (l := [pushB256 scale, swap 0, div]) (path := mid12)
    (by decide : Line.gasFree [pushB256 scale, swap 0, div] = true) run with
    ⟨s14, mid14, hline14, run, hpre14⟩
  have frame14 := frame12.line (by line_inv) (by line_inv) (by line_inv) hline14
  have hp14 : (((half + scratch image rightWord * scratch image leftWord) /
      scale)) :: tail <<+ s14.stack := by
    rcases Line.of_run_cons hline14 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdiv, hnil⟩
    cases hnil
    have h1 := prefix_of_push (of_run_pushB256 hpush) hp12
    have h2 : (half + scratch image rightWord * scratch image leftWord) ::
        scale :: tail <<+ u2.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scale :: (half + scratch image rightWord * scratch image leftWord) ::
              tail)
            ((half + scratch image rightWord * scratch image leftWord) ::
              scale :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) h1
    exact prefix_of_div hdiv h2
  rcases run_prefix_prepend (l := (mstoreAt outputWord)) (path := mid14)
    (gasFree_mstoreAt outputWord) run with
    ⟨s15, mid15, hline15, run, hpre15⟩
  obtain ⟨hp15, frame15⟩ := frame14.mstoreAt hp14 hline15
  exact ⟨s15, mid15, hnofm, hnof, hp15, frame15,
    Func.RunPrefix.trans hpre7 (Func.RunPrefix.trans hpre8
      (Func.RunPrefix.trans hpre9 (Func.RunPrefix.trans hpre10
        (Func.RunPrefix.trans hpre11 (Func.RunPrefix.trans hpre12
          (Func.RunPrefix.trans hpre14 hpre15)))))),
    run⟩

theorem of_run_guardedRoundedMul {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    {leftWord rightWord outputWord : B256} {next : Func}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s
      (guardedRoundedMul leftWord rightWord outputWord next) r) :
    ∃ t,
      B256.Nofm (scratch image leftWord) (scratch image rightWord) ∧
      B256.Nof (scratch image rightWord * scratch image leftWord) half ∧
      (tail <<+ t.stack) ∧
      Frame
        (setScratch image outputWord
          ((half + scratch image rightWord * scratch image leftWord) / scale))
        entry t ∧
      Func.Run fs e t next r := by
  obtain ⟨t, _, hnofm, hnof, hpt, frt, _, run⟩ :=
    of_run_guardedRoundedMul_prefix (path := ⟨0, []⟩) frame hp run
  exact ⟨t, hnofm, hnof, hpt, frt, run⟩

/-! ## The auxiliary table and its slots

The machine is five mutually tail-calling auxiliaries.  `AuxLookup` is the
lookup contract their `Func.call` indices need, discharged once for the
deployed program. -/

structure AuxLookup (fs : List Func) : Prop where
  freshStart : fs[freshStartSlot]? = some Drip.freshStart
  rpowLoop : fs[rpowLoopSlot]? = some Drip.rpowLoop
  rpowAfterSquare : fs[rpowAfterSquareSlot]? = some Drip.rpowAfterSquare
  rpowAdvance : fs[rpowAdvanceSlot]? = some Drip.rpowAdvance
  composeFresh : fs[composeFreshSlot]? = some Drip.composeFresh
  freshRoute : fs[freshRouteSlot]? = some Drip.freshRoute

theorem auxLookup_runtime : AuxLookup (runtime.main :: runtime.aux) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `of_run_call_of_lookup` twin exposing the one-step call prefix. -/
private theorem of_run_call_of_lookup_prefix {fs : List Func} {e : Sevm}
    {s r : Devm} {k : Nat} {f : Func} {path : Prog.SourcePath}
    (hlookup : fs[k]? = some f)
    (run : Func.Run fs e s (.call k) r) :
    ∃ t, Devm.Burn s t ∧
      Func.RunPrefix fs e path s (.call k) ⟨k, []⟩ t f ∧
      Func.Run fs e t f r := by
  cases run with
  | call hget hburn hbody =>
      rename_i t _
      rw [hlookup] at hget
      cases Option.some.inj hget
      exact ⟨t, hburn,
        Func.RunPrefix.call hlookup hburn Func.RunPrefix.refl, hbody⟩

private theorem of_run_call_of_lookup {fs : List Func} {e : Sevm} {s r : Devm}
    {k : Nat} {f : Func} (hlookup : fs[k]? = some f)
    (run : Func.Run fs e s (.call k) r) :
    ∃ t, Devm.Burn s t ∧ Func.Run fs e t f r := by
  obtain ⟨t, hburn, _, hrun⟩ :=
    of_run_call_of_lookup_prefix (path := ⟨k, []⟩) hlookup run
  exact ⟨t, hburn, hrun⟩

/-! ## What the loop may touch

The rpow loop writes only its exponent, base, accumulator and rounding
scratch words.  Every other DRIP slot — the stored index, the timestamp, the
route tag and the endpoint operands — reads through it unchanged, which is
what lets `composeFresh` and the route dispatcher still see what the entry
bodies staged. -/

def LoopOnly (image image' : Bytes) : Prop :=
  ∀ w, SlotsDisjoint w exponentWord → SlotsDisjoint w baseWord →
    SlotsDisjoint w accumulatorWord → SlotsDisjoint w roundedWord →
    scratch image' w = scratch image w

theorem LoopOnly.rfl' (image : Bytes) : LoopOnly image image :=
  fun _ _ _ _ _ => Eq.refl _

theorem LoopOnly.trans {a b c : Bytes} (hab : LoopOnly a b) (hbc : LoopOnly b c) :
    LoopOnly a c :=
  fun w h1 h2 h3 h4 => (hbc w h1 h2 h3 h4).trans (hab w h1 h2 h3 h4)

theorem LoopOnly.exponent (image : Bytes) (v : B256) :
    LoopOnly image (setScratch image exponentWord v) :=
  fun _ h _ _ _ => scratch_setScratch_of_disjoint image v h

theorem LoopOnly.base (image : Bytes) (v : B256) :
    LoopOnly image (setScratch image baseWord v) :=
  fun _ _ h _ _ => scratch_setScratch_of_disjoint image v h

theorem LoopOnly.accumulator (image : Bytes) (v : B256) :
    LoopOnly image (setScratch image accumulatorWord v) :=
  fun _ _ _ h _ => scratch_setScratch_of_disjoint image v h

theorem LoopOnly.rounded (image : Bytes) (v : B256) :
    LoopOnly image (setScratch image roundedWord v) :=
  fun _ _ _ _ h => scratch_setScratch_of_disjoint image v h

/-! ## The frozen slot separations the loop consumes -/

theorem exponent_base : SlotsDisjoint exponentWord baseWord := by decide +kernel
theorem exponent_accumulator : SlotsDisjoint exponentWord accumulatorWord := by
  decide +kernel
theorem exponent_rounded : SlotsDisjoint exponentWord roundedWord := by
  decide +kernel
theorem base_accumulator : SlotsDisjoint baseWord accumulatorWord := by
  decide +kernel
theorem base_rounded : SlotsDisjoint baseWord roundedWord := by decide +kernel
theorem accumulator_rounded : SlotsDisjoint accumulatorWord roundedWord := by
  decide +kernel
theorem storedChi_now : SlotsDisjoint storedChiWord nowWord := by decide +kernel
theorem storedChi_exponent : SlotsDisjoint storedChiWord exponentWord := by
  decide +kernel
theorem storedChi_base : SlotsDisjoint storedChiWord baseWord := by
  decide +kernel
theorem storedChi_accumulator : SlotsDisjoint storedChiWord accumulatorWord := by
  decide +kernel
theorem accumulator_exponent : SlotsDisjoint accumulatorWord exponentWord := by
  decide +kernel
theorem base_exponent : SlotsDisjoint baseWord exponentWord := by decide +kernel
theorem accumulator_base : SlotsDisjoint accumulatorWord baseWord := by
  decide +kernel
theorem now_exponent : SlotsDisjoint nowWord exponentWord := by decide +kernel
theorem now_base : SlotsDisjoint nowWord baseWord := by decide +kernel
theorem now_accumulator : SlotsDisjoint nowWord accumulatorWord := by
  decide +kernel
theorem now_freshChi : SlotsDisjoint nowWord freshChiWord := by decide +kernel
theorem argument_route : SlotsDisjoint argumentWord routeWord := by
  decide +kernel
theorem row_result : SlotsDisjoint rowWord resultWord := by decide +kernel
theorem total_result : SlotsDisjoint totalWord resultWord := by decide +kernel
theorem total_newRow : SlotsDisjoint totalWord newRowWord := by decide +kernel
theorem result_newRow : SlotsDisjoint resultWord newRowWord := by decide +kernel
theorem freshChi_newTotal : SlotsDisjoint freshChiWord newTotalWord := by
  decide +kernel
theorem now_newTotal : SlotsDisjoint nowWord newTotalWord := by decide +kernel
theorem newRow_newTotal : SlotsDisjoint newRowWord newTotalWord := by
  decide +kernel
theorem result_newTotal : SlotsDisjoint resultWord newTotalWord := by
  decide +kernel
theorem freshChi_newRow : SlotsDisjoint freshChiWord newRowWord := by
  decide +kernel
theorem freshChi_result : SlotsDisjoint freshChiWord resultWord := by
  decide +kernel
theorem now_newRow : SlotsDisjoint nowWord newRowWord := by decide +kernel
theorem now_result : SlotsDisjoint nowWord resultWord := by decide +kernel
theorem argument_row : SlotsDisjoint argumentWord rowWord := by decide +kernel
theorem argument_total : SlotsDisjoint argumentWord totalWord := by
  decide +kernel
theorem row_route : SlotsDisjoint rowWord routeWord := by decide +kernel
theorem row_total : SlotsDisjoint rowWord totalWord := by decide +kernel
theorem total_route : SlotsDisjoint totalWord routeWord := by decide +kernel
theorem argument_result : SlotsDisjoint argumentWord resultWord := by
  decide +kernel

/-! ## What the whole machine may touch

The machine owns the stored index, the timestamp, the loop's three working
words, the rounding scratch word and the fresh index.  The route tag and the
three endpoint operand words the entry bodies staged read through it
unchanged, which is what lets the route dispatcher and the endpoint tails
still see them. -/

def MachineOnly (image image' : Bytes) : Prop :=
  scratch image' routeWord = scratch image routeWord ∧
    scratch image' argumentWord = scratch image argumentWord ∧
    scratch image' rowWord = scratch image rowWord ∧
    scratch image' totalWord = scratch image totalWord

theorem MachineOnly.rfl' (image : Bytes) : MachineOnly image image :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩

theorem MachineOnly.trans {a b c : Bytes} (hab : MachineOnly a b)
    (hbc : MachineOnly b c) : MachineOnly a c :=
  ⟨hbc.1.trans hab.1, hbc.2.1.trans hab.2.1, hbc.2.2.1.trans hab.2.2.1,
    hbc.2.2.2.trans hab.2.2.2⟩

/-- Writing any machine-owned slot preserves the staged operands. -/
theorem MachineOnly.setScratch (image : Bytes) (w v : B256)
    (hroute : SlotsDisjoint routeWord w) (harg : SlotsDisjoint argumentWord w)
    (hrow : SlotsDisjoint rowWord w) (htotal : SlotsDisjoint totalWord w) :
    MachineOnly image (setScratch image w v) :=
  ⟨scratch_setScratch_of_disjoint image v hroute,
    scratch_setScratch_of_disjoint image v harg,
    scratch_setScratch_of_disjoint image v hrow,
    scratch_setScratch_of_disjoint image v htotal⟩

theorem MachineOnly.storedChi (image : Bytes) (v : B256) :
    MachineOnly image (Drip.setScratch image storedChiWord v) :=
  MachineOnly.setScratch image storedChiWord v (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem MachineOnly.now (image : Bytes) (v : B256) :
    MachineOnly image (Drip.setScratch image nowWord v) :=
  MachineOnly.setScratch image nowWord v (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem MachineOnly.exponent (image : Bytes) (v : B256) :
    MachineOnly image (Drip.setScratch image exponentWord v) :=
  MachineOnly.setScratch image exponentWord v (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem MachineOnly.base (image : Bytes) (v : B256) :
    MachineOnly image (Drip.setScratch image baseWord v) :=
  MachineOnly.setScratch image baseWord v (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem MachineOnly.accumulator (image : Bytes) (v : B256) :
    MachineOnly image (Drip.setScratch image accumulatorWord v) :=
  MachineOnly.setScratch image accumulatorWord v (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem MachineOnly.freshChi (image : Bytes) (v : B256) :
    MachineOnly image (Drip.setScratch image freshChiWord v) :=
  MachineOnly.setScratch image freshChiWord v (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem LoopOnly.toMachineOnly {a b : Bytes} (h : LoopOnly a b) :
    MachineOnly a b :=
  ⟨h routeWord (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    h argumentWord (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    h rowWord (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    h totalWord (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)⟩

/-- The stored index and the timestamp read through the loop unchanged. -/
theorem LoopOnly.storedChi {a b : Bytes} (h : LoopOnly a b) :
    scratch b storedChiWord = scratch a storedChiWord :=
  h storedChiWord (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem LoopOnly.now {a b : Bytes} (h : LoopOnly a b) :
    scratch b nowWord = scratch a nowWord :=
  h nowWord (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The runtime's low-bit parity test is exactly `Nat` parity of the exponent
word. -/
private theorem toNat_one_and (x : B256) :
    ((1 : B256) &&& x).toNat = x.toNat % 2 := by
  rw [B256.toNat_and, show (1 : B256).toNat = 1 by decide +kernel]
  exact Nat.one_and_eq_mod_two x.toNat

/-- The runtime's low-bit branch flag is zero exactly when the exponent is
even. -/
private theorem one_and_eq_zero_iff (x : B256) :
    ((1 : B256) &&& x) = 0 ↔ x.toNat % 2 ≠ 1 := by
  constructor
  · intro hzero hodd
    have hbit := toNat_one_and x
    rw [hzero, B256.toNat_zero, hodd] at hbit
    exact absurd hbit.symm (by decide)
  · intro heven
    apply B256.toNat_inj
    rw [toNat_one_and, B256.toNat_zero]
    omega

/-! ## Halving the exponent, and the conditional multiply

`rpowAdvance` divides the exponent word by two and re-enters the loop;
`rpowAfterSquare` multiplies the accumulator by the freshly squared base
exactly when the exponent's low bit is set, and then advances.  Both are
stated over an abstract scratch image so the loop induction never has to carry
a concrete one. -/

private theorem of_run_rpowAdvance_prefix {fs : List Func}
    (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    {path : Prog.SourcePath}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call rpowAdvanceSlot) r) :
    ∃ t target, (tail <<+ t.stack) ∧
      Frame (setScratch image exponentWord (scratch image exponentWord / 2))
        entry t ∧
      Func.RunPrefix fs e path s (.call rpowAdvanceSlot) target t
        (.call rpowLoopSlot) ∧
      Func.Run fs e t (.call rpowLoopSlot) r := by
  obtain ⟨s0, hburn0, hpre0, run⟩ :=
    of_run_call_of_lookup_prefix (path := path) hlookup.rpowAdvance run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.rpowAdvance at run
  rcases run_prefix_prepend (path := ⟨rpowAdvanceSlot, []⟩)
    (by decide : Line.gasFree (loadWord exponentWord) = true) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  rcases run_prefix_prepend (path := mid1)
    (by decide : Line.gasFree [pushB256 2, swap 0, div] = true) run with
    ⟨s2, mid2, hline2, run, hpre2⟩
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : (scratch image exponentWord / 2) :: tail <<+ s2.stack := by
    rcases Line.of_run_cons hline2 with ⟨v1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v2, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v3, hdiv, hnil⟩
    cases hnil
    have h1 := prefix_of_push (of_run_pushB256 hpush) hp1
    have h2 : scratch image exponentWord :: (2 : B256) :: tail <<+ v2.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0 ((2 : B256) :: scratch image exponentWord :: tail)
            (scratch image exponentWord :: (2 : B256) :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) h1
    exact prefix_of_div hdiv h2
  rcases run_prefix_prepend (path := mid2)
    (by decide : Line.gasFree (mstoreAt exponentWord) = true) run with
    ⟨s3, mid3, hline3, run, hpre3⟩
  obtain ⟨hp3, frame3⟩ := frame2.mstoreAt hp2 hline3
  exact ⟨s3, mid3, hp3, frame3,
    Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
      (Func.RunPrefix.trans hpre2 hpre3)), run⟩

private theorem of_run_rpowAdvance {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call rpowAdvanceSlot) r) :
    ∃ t, (tail <<+ t.stack) ∧
      Frame (setScratch image exponentWord (scratch image exponentWord / 2))
        entry t ∧
      Func.Run fs e t (.call rpowLoopSlot) r := by
  obtain ⟨t, _, hpt, frt, _, run⟩ :=
    of_run_rpowAdvance_prefix (path := ⟨rpowAdvanceSlot, []⟩) hlookup frame hp
      run
  exact ⟨t, hpt, frt, run⟩

private theorem of_run_rpowAfterSquare_prefix {fs : List Func}
    (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    {path : Prog.SourcePath}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call rpowAfterSquareSlot) r) :
    ∃ t image' target,
      (if (scratch image exponentWord).toNat % 2 = 1 then
          B256.Nofm (scratch image accumulatorWord) (scratch image baseWord) ∧
          B256.Nof (scratch image baseWord * scratch image accumulatorWord) half
        else True) ∧
      scratch image' accumulatorWord =
        (if (scratch image exponentWord).toNat % 2 = 1 then
            B256.mulr scale half (scratch image accumulatorWord)
              (scratch image baseWord)
          else scratch image accumulatorWord) ∧
      scratch image' baseWord = scratch image baseWord ∧
      scratch image' exponentWord = scratch image exponentWord / 2 ∧
      LoopOnly image image' ∧
      Frame image' entry t ∧ (tail <<+ t.stack) ∧
      Func.RunPrefix fs e path s (.call rpowAfterSquareSlot) target t
        (.call rpowLoopSlot) ∧
      Func.Run fs e t (.call rpowLoopSlot) r := by
  obtain ⟨s0, hburn0, hpre0, run⟩ :=
    of_run_call_of_lookup_prefix (path := path) hlookup.rpowAfterSquare run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.rpowAfterSquare at run
  rcases run_prefix_prepend (l := loadWord exponentWord)
    (path := ⟨rpowAfterSquareSlot, []⟩) (gasFree_loadWord exponentWord) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  rcases run_prefix_prepend (l := [pushB256 1, and]) (path := mid1)
    (by decide : Line.gasFree [pushB256 1, and] = true) run with
    ⟨s2, mid2, hline2, run, hpre2⟩
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : ((1 : B256) &&& scratch image exponentWord) :: tail <<+ s2.stack := by
    rcases Line.of_run_cons hline2 with ⟨v1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v2, hand, hnil⟩
    cases hnil
    exact prefix_of_and hand (prefix_of_push (of_run_pushB256 hpush) hp1)
  have hparity := one_and_eq_zero_iff (scratch image exponentWord)
  rcases run_prefix_branch (path := mid2) run with
    ⟨v, midV, hpop, run, hpreB⟩ | ⟨w, v, v', midV, hnz, hpop, hburn, run, hpreB⟩
  · -- low bit clear: skip the multiply
    have hflag : ((1 : B256) &&& scratch image exponentWord) = 0 :=
      (popBurn_pref hpop hp2).1.symm
    have heven : (scratch image exponentWord).toNat % 2 ≠ 1 := hparity.1 hflag
    have frameV := frame2.of_popBurn hpop
    have hpV : tail <<+ v.stack := (popBurn_pref hpop hp2).2
    obtain ⟨t, midT, hpt, framet, hpreA, run⟩ :=
      of_run_rpowAdvance_prefix (path := midV) hlookup frameV hpV run
    refine ⟨t, setScratch image exponentWord (scratch image exponentWord / 2),
      midT, by rw [if_neg heven]; trivial, ?_, ?_, ?_, ?_, framet, hpt,
      Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
        (Func.RunPrefix.trans hpre2 (Func.RunPrefix.trans hpreB hpreA))),
      run⟩
    · rw [if_neg heven]
      exact scratch_setScratch_of_disjoint image _ exponent_accumulator.symm
    · exact scratch_setScratch_of_disjoint image _ exponent_base.symm
    · exact scratch_setScratch_self image exponentWord _
    · exact LoopOnly.exponent image _
  · -- low bit set: multiply the accumulator by the squared base
    have hflag : ((1 : B256) &&& scratch image exponentWord) ≠ 0 := by
      rw [← (popBurn_pref hpop hp2).1]
      exact hnz
    have hodd : (scratch image exponentWord).toNat % 2 = 1 := by
      by_contra heven
      exact hflag (hparity.2 heven)
    have frameV := (frame2.of_popBurn hpop).of_burn hburn
    have hpV : tail <<+ v'.stack := by
      rw [← hburn.stack]
      exact (popBurn_pref hpop hp2).2
    obtain ⟨v1, midV1, hnofm, hnof, hpV1, frameV1, hpreM, run⟩ :=
      of_run_guardedRoundedMul_prefix (path := midV) frameV hpV run
    obtain ⟨t, midT, hpt, framet, hpreA, run⟩ :=
      of_run_rpowAdvance_prefix (path := midV1) hlookup frameV1 hpV1 run
    refine ⟨t, _, midT, by rw [if_pos hodd]; exact ⟨hnofm, hnof⟩, ?_, ?_, ?_,
      ?_, framet, hpt,
      Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
        (Func.RunPrefix.trans hpre2 (Func.RunPrefix.trans hpreB
          (Func.RunPrefix.trans hpreM hpreA)))),
      run⟩
    · rw [if_pos hodd,
        scratch_setScratch_of_disjoint _ _ exponent_accumulator.symm,
        scratch_setScratch_self]
      unfold B256.mulr
      rw [@B256.add_comm half
          (scratch image baseWord * scratch image accumulatorWord),
        B256.mul_comm (scratch image baseWord)]
    · rw [scratch_setScratch_of_disjoint _ _ exponent_base.symm,
        scratch_setScratch_of_disjoint _ _ base_accumulator]
    · rw [scratch_setScratch_self,
        scratch_setScratch_of_disjoint _ _ exponent_accumulator]
    · exact (LoopOnly.accumulator image _).trans (LoopOnly.exponent _ _)

private theorem of_run_rpowAfterSquare {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call rpowAfterSquareSlot) r) :
    ∃ t image',
      (if (scratch image exponentWord).toNat % 2 = 1 then
          B256.Nofm (scratch image accumulatorWord) (scratch image baseWord) ∧
          B256.Nof (scratch image baseWord * scratch image accumulatorWord) half
        else True) ∧
      scratch image' accumulatorWord =
        (if (scratch image exponentWord).toNat % 2 = 1 then
            B256.mulr scale half (scratch image accumulatorWord)
              (scratch image baseWord)
          else scratch image accumulatorWord) ∧
      scratch image' baseWord = scratch image baseWord ∧
      scratch image' exponentWord = scratch image exponentWord / 2 ∧
      LoopOnly image image' ∧
      Frame image' entry t ∧ (tail <<+ t.stack) ∧
      Func.Run fs e t (.call rpowLoopSlot) r := by
  obtain ⟨t, image', _, hcond, hacc, hbase, hexp, hloop, frt, hpt, _, run⟩ :=
    of_run_rpowAfterSquare_prefix (path := ⟨rpowAfterSquareSlot, []⟩) hlookup
      frame hp run
  exact ⟨t, image', hcond, hacc, hbase, hexp, hloop, frt, hpt, run⟩

/-! ## The square-and-multiply loop

A successful run of the machine's loop slot is exactly Jaune's guarded word
loop: it establishes `B256.RPowLoopGuards` from the checks the runtime
actually crossed, leaves `B256.rpowLoop` in the accumulator slot, and reaches
the index-composition slot.  The induction is on the exponent's `Nat` image,
which the runtime halves once per iteration. -/

theorem of_run_rpowLoop_prefix {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry r : Devm} :
    ∀ (n : Nat) {s : Devm} {image : Bytes} {tail : Stack}
      {path : Prog.SourcePath},
      (scratch image exponentWord).toNat = n →
      Frame image entry s → (tail <<+ s.stack) →
      Func.Run fs e s (.call rpowLoopSlot) r →
      ∃ t image' target,
        B256.RPowLoopGuards scale half (scratch image accumulatorWord)
          (scratch image baseWord) n ∧
        scratch image' accumulatorWord =
          B256.rpowLoop scale half (scratch image accumulatorWord)
            (scratch image baseWord) n ∧
        LoopOnly image image' ∧
        Frame image' entry t ∧ (tail <<+ t.stack) ∧
        Func.RunPrefix fs e path s (.call rpowLoopSlot) target t
          (.call composeFreshSlot) ∧
        Func.Run fs e t (.call composeFreshSlot) r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s image tail path hexp frame hp run
  obtain ⟨s0, hburn0, hpre0, run⟩ :=
    of_run_call_of_lookup_prefix (path := path) hlookup.rpowLoop run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.rpowLoop at run
  rcases run_prefix_prepend (l := loadWord exponentWord)
    (path := ⟨rpowLoopSlot, []⟩) (gasFree_loadWord exponentWord) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  rcases run_prefix_prepend (l := [iszero]) (path := mid1)
    (by decide : Line.gasFree [iszero] = true) run with
    ⟨s2, mid2, hline2, run, hpre2⟩
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : ((scratch image exponentWord) =? 0) :: tail <<+ s2.stack :=
    prefix_of_iszero (of_run_singleton hline2) hp1
  by_cases hn : n = 0
  · -- exponent zero: the loop is the identity and jumps straight to composition
    have hE : scratch image exponentWord = 0 :=
      B256.toNat_inj _ 0 (by rw [hexp, hn, B256.toNat_zero])
    rw [hE, B256.eqCheck, if_pos rfl] at hp2
    rcases run_prefix_branch (path := mid2) run with
      ⟨u, midU, hpop, hsquare, hpreB⟩
      | ⟨w, u, v, midV, hnz, hpop, hburn, hcompose, hpreB⟩
    · exact absurd (popBurn_pref hpop hp2).1 (by decide +kernel)
    · refine ⟨v, image, midV, ?_, ?_, LoopOnly.rfl' image,
        (frame2.of_popBurn hpop).of_burn hburn, ?_,
        Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
          (Func.RunPrefix.trans hpre2 hpreB)),
        hcompose⟩
      · rw [B256.RPowLoopGuards, dif_pos hn]
        trivial
      · rw [B256.rpowLoop, dif_pos hn]
      · rw [← hburn.stack]
        exact (popBurn_pref hpop hp2).2
  · -- exponent nonzero: square, conditionally multiply, halve, recurse
    have hE : scratch image exponentWord ≠ 0 := by
      intro hzero
      exact hn (by rw [← hexp, hzero, B256.toNat_zero])
    rw [B256.eqCheck, if_neg hE] at hp2
    rcases run_prefix_branch (path := mid2) run with
      ⟨u, midU, hpop, hsquare, hpreB⟩
      | ⟨w, u, v, midV, hnz, hpop, hburn, hcompose, hpreB⟩
    swap
    · exact absurd (popBurn_pref hpop hp2).1 hnz
    have frameU := frame2.of_popBurn hpop
    have hpU : tail <<+ u.stack := (popBurn_pref hpop hp2).2
    obtain ⟨u1, midU1, hnofmSquare, hnofSquare, hpU1, frameU1, hpreM,
      run⟩ :=
      of_run_guardedRoundedMul_prefix (path := midU) frameU hpU hsquare
    obtain ⟨t1, image2, midT1, hcond, hacc2, hbase2, hexp2, hloop12,
      framet1, hpt1, hpreA, run⟩ :=
      of_run_rpowAfterSquare_prefix (path := midU1) hlookup frameU1 hpU1 run
    rw [scratch_setScratch_self] at hcond hacc2 hbase2
    rw [scratch_setScratch_of_disjoint _ _ exponent_base] at hcond hacc2 hexp2
    rw [scratch_setScratch_of_disjoint _ _ base_accumulator.symm] at hcond hacc2
    have hxx : (half + scratch image baseWord * scratch image baseWord) / scale =
        B256.mulr scale half (scratch image baseWord)
          (scratch image baseWord) := by
      unfold B256.mulr
      rw [@B256.add_comm half
        (scratch image baseWord * scratch image baseWord)]
    rw [hxx, hexp] at hcond hacc2
    rw [hxx] at hbase2
    have hexpNat : (scratch image2 exponentWord).toNat = n / 2 := by
      rw [hexp2, B256.toNat_div (by decide +kernel : (2 : B256) ≠ 0),
        show (2 : B256).toNat = 2 by decide +kernel, hexp]
    obtain ⟨t2, image3, midT, hguards2, hacc3, hloop23, framet2, hpt2,
      hpreIH, run⟩ :=
      ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
        (path := midT1) hexpNat framet1 hpt1 run
    rw [hacc2, hbase2] at hguards2 hacc3
    refine ⟨t2, image3, midT, ?_, ?_, ?_, framet2, hpt2,
      Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
        (Func.RunPrefix.trans hpre2 (Func.RunPrefix.trans hpreB
          (Func.RunPrefix.trans hpreM (Func.RunPrefix.trans hpreA hpreIH))))),
      run⟩
    · rw [B256.RPowLoopGuards, dif_neg hn]
      refine ⟨hnofmSquare, hnofSquare, ?_, hguards2⟩
      by_cases hpar : n % 2 = 1
      · rw [if_pos hpar] at hcond ⊢
        exact ⟨hcond.1, by rw [B256.mul_comm]; exact hcond.2⟩
      · rw [if_neg hpar]
        trivial
    · rw [B256.rpowLoop, dif_neg hn]
      exact hacc3
    · exact ((LoopOnly.base image _).trans hloop12).trans hloop23

theorem of_run_rpowLoop {fs : List Func} (hlookup : AuxLookup fs) {e : Sevm}
    {entry r : Devm} :
    ∀ (n : Nat) {s : Devm} {image : Bytes} {tail : Stack},
      (scratch image exponentWord).toNat = n →
      Frame image entry s → (tail <<+ s.stack) →
      Func.Run fs e s (.call rpowLoopSlot) r →
      ∃ t image',
        B256.RPowLoopGuards scale half (scratch image accumulatorWord)
          (scratch image baseWord) n ∧
        scratch image' accumulatorWord =
          B256.rpowLoop scale half (scratch image accumulatorWord)
            (scratch image baseWord) n ∧
        LoopOnly image image' ∧
        Frame image' entry t ∧ (tail <<+ t.stack) ∧
        Func.Run fs e t (.call composeFreshSlot) r := by
  intro n s image tail hexp frame hp run
  obtain ⟨t, image', _, hguards, hacc, hloop, frt, hpt, _, run⟩ :=
    of_run_rpowLoop_prefix hlookup n (path := ⟨rpowLoopSlot, []⟩) hexp frame hp
      run
  exact ⟨t, image', hguards, hacc, hloop, frt, hpt, run⟩

/-! ## Floor composition onto the stored index

`composeFresh` multiplies the stored index by the realized factor under the
same exact division-recovery check, floors the product by the scale — with no
half-up offset, which is the frozen memo's rule that the loop's rounding and
the outer composition play different roles — and rejects any result above the
frozen index cap. -/

theorem of_run_composeFresh_prefix {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    {path : Prog.SourcePath}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call composeFreshSlot) r) :
    ∃ t target,
      B256.Nofm (scratch image storedChiWord) (scratch image accumulatorWord) ∧
      ¬ maxChi <
        (scratch image accumulatorWord * scratch image storedChiWord) / scale ∧
      (((scratch image accumulatorWord * scratch image storedChiWord) / scale) ::
        tail <<+ t.stack) ∧
      Frame image entry t ∧
      Func.RunPrefix fs e path s (.call composeFreshSlot) target t
        (.call freshRouteSlot) ∧
      Func.Run fs e t (.call freshRouteSlot) r := by
  obtain ⟨s0, hburn0, hpre0, run⟩ :=
    of_run_call_of_lookup_prefix (path := path) hlookup.composeFresh run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.composeFresh at run
  rcases run_prefix_prepend (l := (loadWord storedChiWord)) (path := ⟨composeFreshSlot, []⟩)
    (gasFree_loadWord storedChiWord) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  rcases run_prefix_prepend (l := (loadWord accumulatorWord)) (path := mid1)
    (gasFree_loadWord accumulatorWord) run with
    ⟨s2, mid2, hline2, run, hpre2⟩
  obtain ⟨hp2, frame2⟩ := frame1.loadWord hp1 hline2
  rcases run_prefix_prepend (l := [mul, dup 0]) (path := mid2)
    (by decide : Line.gasFree [mul, dup 0] = true) run with
    ⟨s3, mid3, hline3, run, hpre3⟩
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : (scratch image accumulatorWord * scratch image storedChiWord) ::
      (scratch image accumulatorWord * scratch image storedChiWord) ::
      tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u, hmul, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_mul hmul hp2)
  rcases run_prefix_prepend (l := (loadWord accumulatorWord)) (path := mid3)
    (gasFree_loadWord accumulatorWord) run with
    ⟨s4, mid4, hline4, run, hpre4⟩
  obtain ⟨hp4, frame4⟩ := frame3.loadWord hp3 hline4
  rcases run_prefix_prepend (l := [swap 0, div]) (path := mid4)
    (by decide : Line.gasFree [swap 0, div] = true) run with
    ⟨s5, mid5, hline5, run, hpre5⟩
  have frame5 := frame4.line (by line_inv) (by line_inv) (by line_inv) hline5
  have hp5 : ((scratch image accumulatorWord * scratch image storedChiWord) /
        scratch image accumulatorWord) ::
      (scratch image accumulatorWord * scratch image storedChiWord) ::
      tail <<+ s5.stack := by
    rcases Line.of_run_cons hline5 with ⟨u, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hdiv, hnil⟩
    cases hnil
    have hswapped :
        (scratch image accumulatorWord * scratch image storedChiWord) ::
          scratch image accumulatorWord ::
          (scratch image accumulatorWord * scratch image storedChiWord) ::
          tail <<+ u.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scratch image accumulatorWord ::
              (scratch image accumulatorWord * scratch image storedChiWord) ::
              (scratch image accumulatorWord * scratch image storedChiWord) ::
              tail)
            ((scratch image accumulatorWord * scratch image storedChiWord) ::
              scratch image accumulatorWord ::
              (scratch image accumulatorWord * scratch image storedChiWord) ::
              tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) hp4
    exact prefix_of_div hdiv hswapped
  rcases run_prefix_prepend (l := (loadWord storedChiWord)) (path := mid5)
    (gasFree_loadWord storedChiWord) run with
    ⟨s6, mid6, hline6, run, hpre6⟩
  obtain ⟨hp6, frame6⟩ := frame5.loadWord hp5 hline6
  rcases run_prefix_prepend (l := [eq, iszero]) (path := mid6)
    (by decide : Line.gasFree [eq, iszero] = true) run with
    ⟨s7, mid7, hline7, run, hpre7⟩
  have frame7 := frame6.line (by line_inv) (by line_inv) (by line_inv) hline7
  have hp7 : ((scratch image storedChiWord =?
        ((scratch image accumulatorWord * scratch image storedChiWord) /
          scratch image accumulatorWord)) =? 0) ::
      (scratch image accumulatorWord * scratch image storedChiWord) ::
      tail <<+ s7.stack := by
    rcases Line.of_run_cons hline7 with ⟨u, heq, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hiszero, hnil⟩
    cases hnil
    exact prefix_of_iszero hiszero (prefix_of_eq heq hp6)
  obtain ⟨hflag1, s8, mid8, hp8, hpop8, hpre8, run⟩ :=
    of_run_guard_prefix (path := mid7) hp7 run
  have frame8 := frame7.of_popBurn hpop8
  have hrecover := eq_of_iszero_eqCheck_eq_zero hflag1
  have hnofm : B256.Nofm (scratch image storedChiWord)
      (scratch image accumulatorWord) := by
    by_cases hzero : scratch image accumulatorWord = 0
    · rw [hzero]
      exact nofm_right_zero _
    · refine (B256.mul_div_eq_iff_nofm hzero).1 ?_
      rw [B256.mul_comm (scratch image storedChiWord)]
      exact hrecover.symm
  rcases run_prefix_prepend (l := [pushB256 scale, swap 0, div, dup 0]) (path := mid8)
    (by decide : Line.gasFree [pushB256 scale, swap 0, div, dup 0] = true) run with
    ⟨s9, mid9, hline9, run, hpre9⟩
  have frame9 := frame8.line (by line_inv) (by line_inv) (by line_inv) hline9
  have hp9 : ((scratch image accumulatorWord * scratch image storedChiWord) /
        scale) ::
      ((scratch image accumulatorWord * scratch image storedChiWord) / scale) ::
      tail <<+ s9.stack := by
    rcases Line.of_run_cons hline9 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdiv, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u4, hdup, hnil⟩
    cases hnil
    have h1 := prefix_of_push (of_run_pushB256 hpush) hp8
    have h2 :
        (scratch image accumulatorWord * scratch image storedChiWord) ::
          scale :: tail <<+ u2.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scale ::
              (scratch image accumulatorWord * scratch image storedChiWord) ::
              tail)
            ((scratch image accumulatorWord * scratch image storedChiWord) ::
              scale :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) h1
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_div hdiv h2)
  rcases run_prefix_prepend (l := [pushB256 maxChi, lt]) (path := mid9)
    (by decide : Line.gasFree [pushB256 maxChi, lt] = true) run with
    ⟨s11, mid11, hline11, run, hpre11⟩
  have frame11 := frame9.line (by line_inv) (by line_inv) (by line_inv) hline11
  have hp11 : (maxChi <?
      ((scratch image accumulatorWord * scratch image storedChiWord) / scale))
      :: ((scratch image accumulatorWord * scratch image storedChiWord) / scale) ::
      tail <<+ s11.stack := by
    rcases Line.of_run_cons hline11 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp9)
  obtain ⟨hflag2, s12, mid12, hp12, hpop12, hpre12, run⟩ :=
    of_run_guard_prefix (path := mid11) hp11 run
  have frame12 := frame11.of_popBurn hpop12
  exact ⟨s12, mid12, hnofm, B256.not_lt_of_ltCheck_eq_zero hflag2, hp12,
    frame12,
    Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
      (Func.RunPrefix.trans hpre2 (Func.RunPrefix.trans hpre3
        (Func.RunPrefix.trans hpre4 (Func.RunPrefix.trans hpre5
          (Func.RunPrefix.trans hpre6 (Func.RunPrefix.trans hpre7
            (Func.RunPrefix.trans hpre8 (Func.RunPrefix.trans hpre9
              (Func.RunPrefix.trans hpre11 hpre12)))))))))),
    run⟩

theorem of_run_composeFresh {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call composeFreshSlot) r) :
    ∃ t,
      B256.Nofm (scratch image storedChiWord) (scratch image accumulatorWord) ∧
      ¬ maxChi <
        (scratch image accumulatorWord * scratch image storedChiWord) / scale ∧
      (((scratch image accumulatorWord * scratch image storedChiWord) / scale) ::
        tail <<+ t.stack) ∧
      Frame image entry t ∧
      Func.Run fs e t (.call freshRouteSlot) r := by
  obtain ⟨t, _, hnofm, hcap, hpt, frt, _, run⟩ :=
    of_run_composeFresh_prefix (path := ⟨composeFreshSlot, []⟩) hlookup frame
      hp run
  exact ⟨t, hnofm, hcap, hpt, frt, run⟩

/-- The exponent-halving tail shared by both initialization arms: halve the
staged exponent, run the loop, and arrive at index composition with the
realized factor in the accumulator slot. -/
private theorem of_run_halveExponent_prefix {fs : List Func}
    (hlookup : AuxLookup fs)
    {e : Sevm} {entry s' r : Devm} {image img : Bytes} {tail : Stack}
    {acc k chi now : B256} {path : Prog.SourcePath}
    (hkNat : k.toNat ≠ 0)
    (hacc : acc = (if k.toNat % 2 = 1 then rate else scale))
    (hexpImg : scratch img exponentWord = k)
    (haccImg : scratch img accumulatorWord = acc)
    (hbaseImg : scratch img baseWord = rate)
    (hchiImg : scratch img storedChiWord = chi)
    (hnowImg : scratch img nowWord = now)
    (hmachineImg : MachineOnly image img)
    (frameImg : Frame img entry s') (hpImg : tail <<+ s'.stack)
    (run : Func.Run fs e s'
      (loadWord exponentWord +++ pushB256 2 ::: swap 0 ::: div :::
        mstoreAt exponentWord +++ Func.call rpowLoopSlot) r) :
    ∃ tm imageM target,
      B256.RPowGuards scale half rate k.toNat ∧
      scratch imageM accumulatorWord = B256.rpow scale half rate k.toNat ∧
      scratch imageM storedChiWord = chi ∧
      scratch imageM nowWord = now ∧
      MachineOnly image imageM ∧
      Frame imageM entry tm ∧ (tail <<+ tm.stack) ∧
      Func.RunPrefix fs e path s'
        (loadWord exponentWord +++ pushB256 2 ::: swap 0 ::: div :::
          mstoreAt exponentWord +++ Func.call rpowLoopSlot) target tm
        (.call composeFreshSlot) ∧
      Func.Run fs e tm (.call composeFreshSlot) r := by
  have hrateNe : rate ≠ 0 := by decide +kernel
  rcases run_prefix_prepend (l := loadWord exponentWord) (path := path)
    (gasFree_loadWord exponentWord) run with
    ⟨u1, mid1, hl1, run, hpre1⟩
  obtain ⟨hpu1, frameu1⟩ := frameImg.loadWord hpImg hl1
  rw [hexpImg] at hpu1
  rcases run_prefix_prepend (l := [pushB256 2, swap 0, div]) (path := mid1)
    (by decide : Line.gasFree [pushB256 2, swap 0, div] = true) run with
    ⟨u2, mid2, hl2, run, hpre2⟩
  have frameu2 := frameu1.line (by line_inv) (by line_inv) (by line_inv) hl2
  have hpu2 : (k / 2) :: tail <<+ u2.stack := by
    rcases Line.of_run_cons hl2 with ⟨v1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v2, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v3, hdiv, hnil⟩
    cases hnil
    have h1 := prefix_of_push (of_run_pushB256 hpush) hpu1
    have h2 : k :: (2 : B256) :: tail <<+ v2.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0 ((2 : B256) :: k :: tail) (k :: (2 : B256) :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) h1
    exact prefix_of_div hdiv h2
  rcases run_prefix_prepend (l := mstoreAt exponentWord) (path := mid2)
    (gasFree_mstoreAt exponentWord) run with
    ⟨u3, mid3, hl3, run, hpre3⟩
  obtain ⟨hpu3, frameu3⟩ := frameu2.mstoreAt hpu2 hl3
  have hexpNat :
      (scratch (setScratch img exponentWord (k / 2)) exponentWord).toNat =
        k.toNat / 2 := by
    rw [scratch_setScratch_self,
      B256.toNat_div (by decide +kernel : (2 : B256) ≠ 0),
      show (2 : B256).toNat = 2 by decide +kernel]
  obtain ⟨t2, imageF, midT, hguardsL, haccF, hloopF, frameF, hpF, hpreL,
    run⟩ :=
    of_run_rpowLoop_prefix hlookup _ (path := mid3) hexpNat frameu3 hpu3 run
  rw [scratch_setScratch_of_disjoint _ _ accumulator_exponent, haccImg,
      scratch_setScratch_of_disjoint _ _ base_exponent, hbaseImg]
    at hguardsL haccF
  refine ⟨t2, imageF, midT, ?_, ?_, ?_, ?_, ?_, frameF, hpF,
    Func.RunPrefix.trans hpre1 (Func.RunPrefix.trans hpre2
      (Func.RunPrefix.trans hpre3 hpreL)),
    run⟩
  · rw [B256.RPowGuards, if_neg hrateNe, if_neg hkNat, ← hacc]
    exact hguardsL
  · rw [haccF, B256.rpow, if_neg hrateNe, if_neg hkNat, ← hacc]
  · rw [hloopF.storedChi,
      scratch_setScratch_of_disjoint _ _ storedChi_exponent, hchiImg]
  · rw [hloopF.now, scratch_setScratch_of_disjoint _ _ now_exponent, hnowImg]
  · exact hmachineImg.trans
      ((MachineOnly.exponent img _).trans hloopF.toMachineOnly)

private theorem of_run_halveExponent {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s' r : Devm} {image img : Bytes} {tail : Stack}
    {acc k chi now : B256}
    (hkNat : k.toNat ≠ 0)
    (hacc : acc = (if k.toNat % 2 = 1 then rate else scale))
    (hexpImg : scratch img exponentWord = k)
    (haccImg : scratch img accumulatorWord = acc)
    (hbaseImg : scratch img baseWord = rate)
    (hchiImg : scratch img storedChiWord = chi)
    (hnowImg : scratch img nowWord = now)
    (hmachineImg : MachineOnly image img)
    (frameImg : Frame img entry s') (hpImg : tail <<+ s'.stack)
    (run : Func.Run fs e s'
      (loadWord exponentWord +++ pushB256 2 ::: swap 0 ::: div :::
        mstoreAt exponentWord +++ Func.call rpowLoopSlot) r) :
    ∃ tm imageM,
      B256.RPowGuards scale half rate k.toNat ∧
      scratch imageM accumulatorWord = B256.rpow scale half rate k.toNat ∧
      scratch imageM storedChiWord = chi ∧
      scratch imageM nowWord = now ∧
      MachineOnly image imageM ∧
      Frame imageM entry tm ∧ (tail <<+ tm.stack) ∧
      Func.Run fs e tm (.call composeFreshSlot) r := by
  obtain ⟨tm, imageM, _, hguards, haccF, hchi, hnow, hmachine, frt, hpt,
    _, run⟩ :=
    of_run_halveExponent_prefix hlookup (path := ⟨freshStartSlot, []⟩) hkNat hacc
      hexpImg haccImg hbaseImg hchiImg hnowImg hmachineImg frameImg hpImg run
  exact ⟨tm, imageM, hguards, haccF, hchi, hnow, hmachine, frt, hpt, run⟩

/-! ## The machine's entry: guards, initialization, loop, composition

A successful run of the machine's start slot crosses four checks in order —
the stored index is in range, the clock has not gone backwards, and the
elapsed interval is within the frozen four-byte ceiling — then runs the loop
at the elapsed exponent and floor-composes the realized factor onto the stored
index.  Every one of those is a *conclusion* here, established from the
branches the run actually took. -/

theorem of_run_freshStart_prefix {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    {path : Prog.SourcePath}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call freshStartSlot) r) :
    ∃ t image' target,
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      B256.Nofm (Devm.getStorVal entry e.currentTarget chiSlot)
        (B256.rpow scale half rate
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat) ∧
      ¬ maxChi <
        (B256.rpow scale half rate
              (e.benvStat.time -
                Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
      scratch image' accumulatorWord =
        B256.rpow scale half rate
          (e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      scratch image' nowWord = e.benvStat.time ∧
      MachineOnly image image' ∧
      Frame image' entry t ∧
      (((B256.rpow scale half rate
          (e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
          Devm.getStorVal entry e.currentTarget chiSlot) / scale) :: tail <<+ t.stack) ∧
      Func.RunPrefix fs e path s (.call freshStartSlot) target t
        (.call freshRouteSlot) ∧
      Func.Run fs e t (.call freshRouteSlot) r := by
  obtain ⟨s0, hburn0, hpre0, run⟩ :=
    of_run_call_of_lookup_prefix (path := path) hlookup.freshStart run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.freshStart at run
  -- SLOAD the stored index and stage it
  rcases run_prefix_prepend (l := [pushB256 chiSlot, sload]) (path := ⟨freshStartSlot, []⟩)
    (by decide : Line.gasFree [pushB256 chiSlot, sload] = true) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  have frame1 := frame0.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : Devm.getStorVal entry e.currentTarget chiSlot :: tail <<+
      s1.stack := by
    rcases Line.of_run_cons hline1 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hsload, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) hp0)
    rw [hyval,
      Devm.getStorVal_of_state
        (frame0.state.trans (of_run_pushB256 hpush).state).symm] at hy
    simpa using hy
  rcases run_prefix_prepend (l := (mstoreAt storedChiWord)) (path := mid1)
    (gasFree_mstoreAt storedChiWord) run with
    ⟨s2, mid2, hline2, run, hpre2⟩
  obtain ⟨hp2, frame2⟩ := frame1.mstoreAt hp1 hline2
  -- the stored index is at least the scale
  rcases run_prefix_prepend (l := [pushB256 scale]) (path := mid2)
    (by decide : Line.gasFree [pushB256 scale] = true) run with
    ⟨s3, mid3, hline3, run, hpre3⟩
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : scale :: tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp2
  rcases run_prefix_prepend (l := (loadWord storedChiWord)) (path := mid3)
    (gasFree_loadWord storedChiWord) run with
    ⟨s4, mid4, hline4, run, hpre4⟩
  obtain ⟨hp4, frame4⟩ := frame3.loadWord hp3 hline4
  rw [scratch_setScratch_self] at hp4
  rcases run_prefix_prepend (l := [lt]) (path := mid4)
    (by decide : Line.gasFree [lt] = true) run with
    ⟨s5, mid5, hline5, run, hpre5⟩
  have frame5 := frame4.line (by line_inv) (by line_inv) (by line_inv) hline5
  have hp5 : ((Devm.getStorVal entry e.currentTarget chiSlot) <? scale) ::
      tail <<+ s5.stack := prefix_of_lt (of_run_singleton hline5) hp4
  obtain ⟨hflagLower, s6, mid6, hp6, hpop6, hpre6, run⟩ :=
    of_run_guard_prefix (path := mid5) hp5 run
  have frame6 := frame5.of_popBurn hpop6
  have hlower := B256.not_lt_of_ltCheck_eq_zero hflagLower
  -- the stored index is within the frozen cap
  rcases run_prefix_prepend (l := (loadWord storedChiWord)) (path := mid6)
    (gasFree_loadWord storedChiWord) run with
    ⟨s7, mid7, hline7, run, hpre7⟩
  obtain ⟨hp7, frame7⟩ := frame6.loadWord hp6 hline7
  rw [scratch_setScratch_self] at hp7
  rcases run_prefix_prepend (l := [pushB256 maxChi, lt]) (path := mid7)
    (by decide : Line.gasFree [pushB256 maxChi, lt] = true) run with
    ⟨s8, mid8, hline8, run, hpre8⟩
  have frame8 := frame7.line (by line_inv) (by line_inv) (by line_inv) hline8
  have hp8 : (maxChi <? Devm.getStorVal entry e.currentTarget chiSlot) ::
      tail <<+ s8.stack := by
    rcases Line.of_run_cons hline8 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp7)
  obtain ⟨hflagUpper, s9, mid9, hp9, hpop9, hpre9, run⟩ :=
    of_run_guard_prefix (path := mid8) hp8 run
  have frame9 := frame8.of_popBurn hpop9
  have hupper := B256.not_lt_of_ltCheck_eq_zero hflagUpper
  -- stage the block timestamp
  rcases run_prefix_prepend (l := [timestamp]) (path := mid9)
    (by decide : Line.gasFree [timestamp] = true) run with
    ⟨s10, mid10, hline10, run, hpre10⟩
  have frame10 := frame9.timestamp (of_run_singleton hline10)
  have hp10 : e.benvStat.time :: tail <<+ s10.stack :=
    prefix_of_timestamp hp9 (of_run_singleton hline10)
  rcases run_prefix_prepend (l := (mstoreAt nowWord)) (path := mid10)
    (gasFree_mstoreAt nowWord) run with
    ⟨s11, mid11, hline11, run, hpre11⟩
  obtain ⟨hp11, frame11⟩ := frame10.mstoreAt hp10 hline11
  -- the clock has not gone backwards
  rcases run_prefix_prepend (l := [pushB256 rhoSlot, sload]) (path := mid11)
    (by decide : Line.gasFree [pushB256 rhoSlot, sload] = true) run with
    ⟨s12, mid12, hline12, run, hpre12⟩
  have frame12 := frame11.line (by line_inv) (by line_inv) (by line_inv) hline12
  have hp12 : Devm.getStorVal entry e.currentTarget rhoSlot :: tail <<+
      s12.stack := by
    rcases Line.of_run_cons hline12 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hsload, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) hp11)
    rw [hyval,
      Devm.getStorVal_of_state
        (frame11.state.trans (of_run_pushB256 hpush).state).symm] at hy
    simpa using hy
  -- retain rho across the comparison for the subsequent subtraction
  rcases run_prefix_prepend (l := [dup 0]) (path := mid12)
    (by decide : Line.gasFree [dup 0] = true) run with
    ⟨s12dup, mid12dup, hline12dup, run, hpre12dup⟩
  have frame12dup := frame12.line (by line_inv) (by line_inv) (by line_inv) hline12dup
  have hp12dup : Devm.getStorVal entry e.currentTarget rhoSlot ::
      Devm.getStorVal entry e.currentTarget rhoSlot :: tail <<+ s12dup.stack :=
    prefix_of_dup_val (of_run_singleton hline12dup) (by show_nth) hp12
  rcases run_prefix_prepend (l := (loadWord nowWord)) (path := mid12dup)
    (gasFree_loadWord nowWord) run with
    ⟨s13, mid13, hline13, run, hpre13⟩
  obtain ⟨hp13, frame13⟩ := frame12dup.loadWord hp12dup hline13
  rw [scratch_setScratch_self] at hp13
  rcases run_prefix_prepend (l := [lt]) (path := mid13)
    (by decide : Line.gasFree [lt] = true) run with
    ⟨s14, mid14, hline14, run, hpre14⟩
  have frame14 := frame13.line (by line_inv) (by line_inv) (by line_inv) hline14
  have hp14 : (e.benvStat.time <?
      Devm.getStorVal entry e.currentTarget rhoSlot) ::
      Devm.getStorVal entry e.currentTarget rhoSlot :: tail <<+ s14.stack :=
    prefix_of_lt (of_run_singleton hline14) hp13
  obtain ⟨hflagClock, s15, mid15, hp15, hpop15, hpre15, run⟩ :=
    of_run_guard_prefix (path := mid14) hp14 run
  have frame15 := frame14.of_popBurn hpop15
  have hclock := B256.not_lt_of_ltCheck_eq_zero hflagClock
  -- stage the elapsed interval using the retained rho
  rcases run_prefix_prepend (l := (loadWord nowWord)) (path := mid15)
    (gasFree_loadWord nowWord) run with
    ⟨s17, mid17, hline17, run, hpre17⟩
  obtain ⟨hp17, frame17⟩ := frame15.loadWord hp15 hline17
  rw [scratch_setScratch_self] at hp17
  rcases run_prefix_prepend (l := [sub]) (path := mid17)
    (by decide : Line.gasFree [sub] = true) run with
    ⟨s18, mid18, hline18, run, hpre18⟩
  have frame18 := frame17.line (by line_inv) (by line_inv) (by line_inv) hline18
  have hp18 : (e.benvStat.time -
      Devm.getStorVal entry e.currentTarget rhoSlot) :: tail <<+ s18.stack :=
    prefix_of_sub (of_run_singleton hline18) hp17
  rcases run_prefix_prepend (l := (mstoreAt exponentWord)) (path := mid18)
    (gasFree_mstoreAt exponentWord) run with
    ⟨s19, mid19, hline19, run, hpre19⟩
  obtain ⟨hp19, frame19⟩ := frame18.mstoreAt hp18 hline19
  -- the elapsed interval is within the frozen four-byte ceiling
  rcases run_prefix_prepend (l := (loadWord exponentWord)) (path := mid19)
    (gasFree_loadWord exponentWord) run with
    ⟨s20, mid20, hline20, run, hpre20⟩
  obtain ⟨hp20, frame20⟩ := frame19.loadWord hp19 hline20
  rw [scratch_setScratch_self] at hp20
  rcases run_prefix_prepend (l := [pushB256 maxElapsed, lt]) (path := mid20)
    (by decide : Line.gasFree [pushB256 maxElapsed, lt] = true) run with
    ⟨s21, mid21, hline21, run, hpre21⟩
  have frame21 := frame20.line (by line_inv) (by line_inv) (by line_inv) hline21
  have hp21 : (maxElapsed <? (e.benvStat.time -
      Devm.getStorVal entry e.currentTarget rhoSlot)) :: tail <<+ s21.stack := by
    rcases Line.of_run_cons hline21 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp20)
  obtain ⟨hflagElapsed, s22, mid22, hp22, hpop22, hpre22, run⟩ :=
    of_run_guard_prefix (path := mid21) hp21 run
  have frame22 := frame21.of_popBurn hpop22
  have helapsed := B256.not_lt_of_ltCheck_eq_zero hflagElapsed
  -- initialize the loop's base; the zero-base arm is unreachable at DRIP's rate
  have hrateNe : rate ≠ 0 := by decide +kernel
  rcases run_prefix_prepend (l := [pushB256 rate, dup 0]) (path := mid22)
    (by decide : Line.gasFree [pushB256 rate, dup 0] = true) run with
    ⟨s23, mid23, hline23, run, hpre23⟩
  have frame23 := frame22.line (by line_inv) (by line_inv) (by line_inv) hline23
  have hp23 : rate :: rate :: tail <<+ s23.stack := by
    rcases Line.of_run_cons hline23 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth)
      (prefix_of_push (of_run_pushB256 hpush) hp22)
  rcases run_prefix_prepend (l := (mstoreAt baseWord)) (path := mid23)
    (gasFree_mstoreAt baseWord) run with
    ⟨s24, mid24, hline24, run, hpre24⟩
  obtain ⟨hp24, frame24⟩ := frame23.mstoreAt hp23 hline24
  rcases run_prefix_prepend (l := [iszero]) (path := mid24)
    (by decide : Line.gasFree [iszero] = true) run with
    ⟨s25, mid25, hline25, run, hpre25⟩
  have frame25 := frame24.line (by line_inv) (by line_inv) (by line_inv) hline25
  have hp25 : (rate =? 0) :: tail <<+ s25.stack :=
    prefix_of_iszero (of_run_singleton hline25) hp24
  rw [B256.eqCheck, if_neg hrateNe] at hp25
  rcases run_prefix_branch (path := mid25) run with
    ⟨s26, mid26, hpop26, run, hpreB⟩
    | ⟨w, s26, s26', mid26x, hnz, hpop26, hburn26, run, hpreB⟩
  swap
  · exact absurd (popBurn_pref hpop26 hp25).1 hnz
  have frame26 := frame25.of_popBurn hpop26
  have hp26 : tail <<+ s26.stack := (popBurn_pref hpop26 hp25).2
  rcases run_prefix_prepend (l := (loadWord exponentWord)) (path := mid26)
    (gasFree_loadWord exponentWord) run with
    ⟨s27, mid27, hline27, run, hpre27⟩
  obtain ⟨hp27, frame27⟩ := frame26.loadWord hp26 hline27
  rw [scratch_setScratch_of_disjoint _ _ exponent_base,
    scratch_setScratch_self] at hp27
  rcases run_prefix_prepend (l := [iszero]) (path := mid27)
    (by decide : Line.gasFree [iszero] = true) run with
    ⟨s28, mid28, hline28, run, hpre28⟩
  have frame28 := frame27.line (by line_inv) (by line_inv) (by line_inv) hline28
  have hp28 : ((e.benvStat.time -
      Devm.getStorVal entry e.currentTarget rhoSlot) =? 0) :: tail <<+
      s28.stack := prefix_of_iszero (of_run_singleton hline28) hp27
  -- both initialization arms converge on the index-composition slot; the
  -- shared tail below runs index composition and the final assembly once,
  -- with each leaf supplying its own full walk prefix.
  have converge : ∀ {tm : Devm} {imageM : Bytes} {midK : Prog.SourcePath},
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat →
      scratch imageM accumulatorWord =
        B256.rpow scale half rate
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat →
      scratch imageM storedChiWord =
        Devm.getStorVal entry e.currentTarget chiSlot →
      scratch imageM nowWord = e.benvStat.time →
      MachineOnly image imageM →
      Frame imageM entry tm → (tail <<+ tm.stack) →
      Func.RunPrefix fs e path s (.call freshStartSlot) midK tm
        (.call composeFreshSlot) →
      Func.Run fs e tm (.call composeFreshSlot) r →
      ∃ t image' target,
        ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
        ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
        ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
        ¬ maxElapsed <
          e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
        B256.RPowGuards scale half rate
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
        B256.Nofm (Devm.getStorVal entry e.currentTarget chiSlot)
          (B256.rpow scale half rate
            (e.benvStat.time -
              Devm.getStorVal entry e.currentTarget rhoSlot).toNat) ∧
        ¬ maxChi <
          (B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
        scratch image' accumulatorWord =
          B256.rpow scale half rate
            (e.benvStat.time -
              Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
        scratch image' nowWord = e.benvStat.time ∧
        MachineOnly image image' ∧
        Frame image' entry t ∧
        (((B256.rpow scale half rate
            (e.benvStat.time -
              Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale) ::
          tail <<+ t.stack) ∧
        Func.RunPrefix fs e path s (.call freshStartSlot) target t
          (.call freshRouteSlot) ∧
        Func.Run fs e t (.call freshRouteSlot) r := by
    intro tm imageM midK hguards haccM hchiM hnowM hmachineM frameM hpM hpreFull
      run
    obtain ⟨t, midC, hnofm, hcap, hpt, framet, hpreC, run⟩ :=
      of_run_composeFresh_prefix (path := midK) hlookup frameM hpM run
    rw [haccM, hchiM] at hnofm hcap hpt
    exact ⟨t, imageM, midC, hlower, hupper, hclock, helapsed, hguards,
      hnofm, hcap, haccM, hnowM, hmachineM, framet, hpt,
      Func.RunPrefix.trans hpreFull hpreC, run⟩
  rcases run_prefix_branch (path := mid28) run with
    ⟨s29, mid29, hpop29, run, hpreB29⟩
    | ⟨w', s29, s29', mid29z, hnz', hpop29, hburn29, run, hpreB29z⟩
  · -- the exponent is nonzero: seed the accumulator by parity and loop
    have hflag :
        ((e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot) =? 0) = 0 :=
      (popBurn_pref hpop29 hp28).1.symm
    have hk : (e.benvStat.time -
        Devm.getStorVal entry e.currentTarget rhoSlot) ≠ 0 := by
      intro hzero
      rw [hzero, B256.eqCheck, if_pos rfl] at hflag
      exact absurd hflag (by decide +kernel)
    have hkNat : (e.benvStat.time -
        Devm.getStorVal entry e.currentTarget rhoSlot).toNat ≠ 0 := by
      intro hzeroNat
      exact hk (B256.toNat_inj _ 0 (by rw [hzeroNat, B256.toNat_zero]))
    have frame29 := frame28.of_popBurn hpop29
    have hp29 : tail <<+ s29.stack := (popBurn_pref hpop29 hp28).2
    rcases run_prefix_prepend (l := loadWord exponentWord) (path := mid29)
      (gasFree_loadWord exponentWord) run with
      ⟨s30, mid30, hline30, run, hpre30⟩
    obtain ⟨hp30, frame30⟩ := frame29.loadWord hp29 hline30
    rw [scratch_setScratch_of_disjoint _ _ exponent_base,
      scratch_setScratch_self] at hp30
    rcases run_prefix_prepend (l := [pushB256 1, and]) (path := mid30)
      (by decide : Line.gasFree [pushB256 1, and] = true) run with
      ⟨s31, mid31, hline31, run, hpre31⟩
    have frame31 := frame30.line (by line_inv) (by line_inv) (by line_inv) hline31
    have hp31 : ((1 : B256) &&& (e.benvStat.time -
        Devm.getStorVal entry e.currentTarget rhoSlot)) :: tail <<+
        s31.stack := by
      rcases Line.of_run_cons hline31 with ⟨v1, hpush, hrest⟩
      rcases Line.of_run_cons hrest with ⟨v2, hand, hnil⟩
      cases hnil
      exact prefix_of_and hand (prefix_of_push (of_run_pushB256 hpush) hp30)
    have hparity := one_and_eq_zero_iff
      (e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot)
    rcases run_prefix_branch (path := mid31) run with
      ⟨s32, mid32, hpop32, run, hpreB32⟩
      | ⟨w'', s32, s32', mid32o, hnz'', hpop32, hburn32, run, hpreB32⟩
    · -- even exponent: seed the accumulator with the scale
      have heven := hparity.1 (popBurn_pref hpop32 hp31).1.symm
      have frame32 := frame31.of_popBurn hpop32
      have hp32 : tail <<+ s32.stack := (popBurn_pref hpop32 hp31).2
      rcases run_prefix_prepend (l := [pushB256 scale]) (path := mid32)
        (by decide : Line.gasFree [pushB256 scale] = true) run with
        ⟨s33, mid33, hline33, run, hpre33⟩
      have frame33 := frame32.line (by line_inv) (by line_inv) (by line_inv)
        hline33
      have hp33 : scale :: tail <<+ s33.stack := by
        rcases Line.of_run_cons hline33 with ⟨v, hpush, hnil⟩
        cases hnil
        exact prefix_of_push (of_run_pushB256 hpush) hp32
      rcases run_prefix_prepend (l := mstoreAt accumulatorWord)
        (path := mid33) (gasFree_mstoreAt accumulatorWord) run with
        ⟨s34, mid34, hline34, run, hpre34⟩
      obtain ⟨hp34, frame34⟩ := frame33.mstoreAt hp33 hline34
      obtain ⟨tm, imageM, midH, hguards, haccF, hchi, hnow, hmachine,
        frameF, hpF, hpreH, run⟩ :=
        of_run_halveExponent_prefix hlookup (path := mid34) hkNat
          (by rw [if_neg heven]) (by rw [scratch_setScratch_of_disjoint _ _ exponent_accumulator,
          scratch_setScratch_of_disjoint _ _ exponent_base,
          scratch_setScratch_self]) (scratch_setScratch_self _ _ _) (by rw [scratch_setScratch_of_disjoint _ _ base_accumulator,
          scratch_setScratch_self]) (by rw [scratch_setScratch_of_disjoint _ _ storedChi_accumulator,
          scratch_setScratch_of_disjoint _ _ storedChi_base,
          scratch_setScratch_of_disjoint _ _ storedChi_exponent,
          scratch_setScratch_of_disjoint _ _ storedChi_now,
          scratch_setScratch_self]) (by rw [scratch_setScratch_of_disjoint _ _ now_accumulator,
          scratch_setScratch_of_disjoint _ _ now_base,
          scratch_setScratch_of_disjoint _ _ now_exponent,
          scratch_setScratch_self])
          (by exact ((((MachineOnly.storedChi image _).trans
          (MachineOnly.now _ _)).trans (MachineOnly.exponent _ _)).trans
          (MachineOnly.base _ _)).trans (MachineOnly.accumulator _ _)) frame34 hp34 run
      · refine converge (midK := midH) hguards haccF hchi hnow hmachine frameF
          hpF ?_ run
        · exact Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
          (Func.RunPrefix.trans hpre2
            (Func.RunPrefix.trans hpre3
              (Func.RunPrefix.trans hpre4
                (Func.RunPrefix.trans hpre5
                  (Func.RunPrefix.trans hpre6
                    (Func.RunPrefix.trans hpre7
                      (Func.RunPrefix.trans hpre8
                        (Func.RunPrefix.trans hpre9
                          (Func.RunPrefix.trans hpre10
                            (Func.RunPrefix.trans hpre11
                              (Func.RunPrefix.trans hpre12
                                (Func.RunPrefix.trans hpre12dup
                                  (Func.RunPrefix.trans hpre13
                                    (Func.RunPrefix.trans hpre14
                                      (Func.RunPrefix.trans hpre15
                                        (Func.RunPrefix.trans hpre17
                                          (Func.RunPrefix.trans hpre18
                                            (Func.RunPrefix.trans hpre19
                                              (Func.RunPrefix.trans hpre20
                                                (Func.RunPrefix.trans hpre21
                                                  (Func.RunPrefix.trans hpre22
                                                    (Func.RunPrefix.trans hpre23
                                                      (Func.RunPrefix.trans hpre24
                                                        (Func.RunPrefix.trans hpre25
                                                          (Func.RunPrefix.trans hpreB
                                                            (Func.RunPrefix.trans hpre27
                                                              (Func.RunPrefix.trans hpre28
                                                                (Func.RunPrefix.trans hpreB29
                                                                  (Func.RunPrefix.trans hpre30
                                                                    (Func.RunPrefix.trans hpre31
                                                                      (Func.RunPrefix.trans hpreB32
                                                                        (Func.RunPrefix.trans hpre33
                                                                          (Func.RunPrefix.trans hpre34 hpreH))))))))))))))))))))))))))))))))))
    · -- odd exponent: seed the accumulator with the rate
      have hodd : (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat % 2 = 1 := by
        by_contra heven
        exact hnz'' ((popBurn_pref hpop32 hp31).1.trans (hparity.2 heven))
      have frame32 := (frame31.of_popBurn hpop32).of_burn hburn32
      have hp32 : tail <<+ s32'.stack := by
        rw [← hburn32.stack]
        exact (popBurn_pref hpop32 hp31).2
      rcases run_prefix_prepend (l := [pushB256 rate]) (path := mid32o)
        (by decide : Line.gasFree [pushB256 rate] = true) run with
        ⟨s33, mid33, hline33, run, hpre33⟩
      have frame33 := frame32.line (by line_inv) (by line_inv) (by line_inv)
        hline33
      have hp33 : rate :: tail <<+ s33.stack := by
        rcases Line.of_run_cons hline33 with ⟨v, hpush, hnil⟩
        cases hnil
        exact prefix_of_push (of_run_pushB256 hpush) hp32
      rcases run_prefix_prepend (l := mstoreAt accumulatorWord)
        (path := mid33) (gasFree_mstoreAt accumulatorWord) run with
        ⟨s34, mid34, hline34, run, hpre34⟩
      obtain ⟨hp34, frame34⟩ := frame33.mstoreAt hp33 hline34
      obtain ⟨tm, imageM, midH, hguards, haccF, hchi, hnow, hmachine,
        frameF, hpF, hpreH, run⟩ :=
        of_run_halveExponent_prefix hlookup (path := mid34) hkNat
          (by rw [if_pos hodd]) (by rw [scratch_setScratch_of_disjoint _ _ exponent_accumulator,
          scratch_setScratch_of_disjoint _ _ exponent_base,
          scratch_setScratch_self]) (scratch_setScratch_self _ _ _) (by rw [scratch_setScratch_of_disjoint _ _ base_accumulator,
          scratch_setScratch_self]) (by rw [scratch_setScratch_of_disjoint _ _ storedChi_accumulator,
          scratch_setScratch_of_disjoint _ _ storedChi_base,
          scratch_setScratch_of_disjoint _ _ storedChi_exponent,
          scratch_setScratch_of_disjoint _ _ storedChi_now,
          scratch_setScratch_self]) (by rw [scratch_setScratch_of_disjoint _ _ now_accumulator,
          scratch_setScratch_of_disjoint _ _ now_base,
          scratch_setScratch_of_disjoint _ _ now_exponent,
          scratch_setScratch_self])
          (by exact ((((MachineOnly.storedChi image _).trans
          (MachineOnly.now _ _)).trans (MachineOnly.exponent _ _)).trans
          (MachineOnly.base _ _)).trans (MachineOnly.accumulator _ _)) frame34 hp34 run
      · refine converge (midK := midH) hguards haccF hchi hnow hmachine frameF
          hpF ?_ run
        · exact Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
          (Func.RunPrefix.trans hpre2
            (Func.RunPrefix.trans hpre3
              (Func.RunPrefix.trans hpre4
                (Func.RunPrefix.trans hpre5
                  (Func.RunPrefix.trans hpre6
                    (Func.RunPrefix.trans hpre7
                      (Func.RunPrefix.trans hpre8
                        (Func.RunPrefix.trans hpre9
                          (Func.RunPrefix.trans hpre10
                            (Func.RunPrefix.trans hpre11
                              (Func.RunPrefix.trans hpre12
                                (Func.RunPrefix.trans hpre12dup
                                  (Func.RunPrefix.trans hpre13
                                    (Func.RunPrefix.trans hpre14
                                      (Func.RunPrefix.trans hpre15
                                        (Func.RunPrefix.trans hpre17
                                          (Func.RunPrefix.trans hpre18
                                            (Func.RunPrefix.trans hpre19
                                              (Func.RunPrefix.trans hpre20
                                                (Func.RunPrefix.trans hpre21
                                                  (Func.RunPrefix.trans hpre22
                                                    (Func.RunPrefix.trans hpre23
                                                      (Func.RunPrefix.trans hpre24
                                                        (Func.RunPrefix.trans hpre25
                                                          (Func.RunPrefix.trans hpreB
                                                            (Func.RunPrefix.trans hpre27
                                                              (Func.RunPrefix.trans hpre28
                                                                (Func.RunPrefix.trans hpreB29
                                                                  (Func.RunPrefix.trans hpre30
                                                                    (Func.RunPrefix.trans hpre31
                                                                      (Func.RunPrefix.trans hpreB32
                                                                        (Func.RunPrefix.trans hpre33
                                                                          (Func.RunPrefix.trans hpre34 hpreH))))))))))))))))))))))))))))))))))
  · -- the exponent is zero: the factor is the scale itself
    have hk : (e.benvStat.time -
        Devm.getStorVal entry e.currentTarget rhoSlot) = 0 := by
      by_contra hne
      rw [B256.eqCheck, if_neg hne] at hp28
      exact absurd (popBurn_pref hpop29 hp28).1 hnz'
    have hkNat : (e.benvStat.time -
        Devm.getStorVal entry e.currentTarget rhoSlot).toNat = 0 := by
      rw [hk, B256.toNat_zero]
    have frame29 := (frame28.of_popBurn hpop29).of_burn hburn29
    have hp29 : tail <<+ s29'.stack := by
      rw [← hburn29.stack]
      exact (popBurn_pref hpop29 hp28).2
    rcases run_prefix_prepend (l := [pushB256 scale]) (path := mid29z)
      (by decide : Line.gasFree [pushB256 scale] = true) run with
      ⟨s30, mid30, hline30, run, hpre30⟩
    have frame30 := frame29.line (by line_inv) (by line_inv) (by line_inv)
      hline30
    have hp30 : scale :: tail <<+ s30.stack := by
      rcases Line.of_run_cons hline30 with ⟨v, hpush, hnil⟩
      cases hnil
      exact prefix_of_push (of_run_pushB256 hpush) hp29
    rcases run_prefix_prepend (l := mstoreAt accumulatorWord) (path := mid30)
      (gasFree_mstoreAt accumulatorWord) run with
      ⟨s31, mid31, hline31, run, hpre31⟩
    obtain ⟨hp31, frame31⟩ := frame30.mstoreAt hp30 hline31
    refine converge (midK := mid31) ?_ ?_ ?_ ?_ ?_ frame31 hp31 ?_ run
    · rw [hkNat, B256.RPowGuards, if_neg hrateNe, if_pos rfl]
      trivial
    · rw [scratch_setScratch_self, hkNat, B256.rpow, if_neg hrateNe,
        if_pos rfl]
    · rw [scratch_setScratch_of_disjoint _ _ storedChi_accumulator,
        scratch_setScratch_of_disjoint _ _ storedChi_base,
        scratch_setScratch_of_disjoint _ _ storedChi_exponent,
        scratch_setScratch_of_disjoint _ _ storedChi_now,
        scratch_setScratch_self]
    · rw [scratch_setScratch_of_disjoint _ _ now_accumulator,
        scratch_setScratch_of_disjoint _ _ now_base,
        scratch_setScratch_of_disjoint _ _ now_exponent,
        scratch_setScratch_self]
    · exact ((((MachineOnly.storedChi image _).trans
        (MachineOnly.now _ _)).trans (MachineOnly.exponent _ _)).trans
        (MachineOnly.base _ _)).trans (MachineOnly.accumulator _ _)
    · exact Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
      (Func.RunPrefix.trans hpre2
        (Func.RunPrefix.trans hpre3
          (Func.RunPrefix.trans hpre4
            (Func.RunPrefix.trans hpre5
              (Func.RunPrefix.trans hpre6
                (Func.RunPrefix.trans hpre7
                  (Func.RunPrefix.trans hpre8
                    (Func.RunPrefix.trans hpre9
                      (Func.RunPrefix.trans hpre10
                        (Func.RunPrefix.trans hpre11
                          (Func.RunPrefix.trans hpre12
                            (Func.RunPrefix.trans hpre12dup
                              (Func.RunPrefix.trans hpre13
                                (Func.RunPrefix.trans hpre14
                                  (Func.RunPrefix.trans hpre15
                                    (Func.RunPrefix.trans hpre17
                                      (Func.RunPrefix.trans hpre18
                                        (Func.RunPrefix.trans hpre19
                                          (Func.RunPrefix.trans hpre20
                                            (Func.RunPrefix.trans hpre21
                                              (Func.RunPrefix.trans hpre22
                                                (Func.RunPrefix.trans hpre23
                                                  (Func.RunPrefix.trans hpre24
                                                    (Func.RunPrefix.trans hpre25
                                                      (Func.RunPrefix.trans hpreB
                                                        (Func.RunPrefix.trans hpre27
                                                          (Func.RunPrefix.trans hpre28
                                                            (Func.RunPrefix.trans hpreB29z
                                                              (Func.RunPrefix.trans hpre30 hpre31))))))))))))))))))))))))))))))

theorem of_run_freshStart {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call freshStartSlot) r) :
    ∃ t image',
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      B256.Nofm (Devm.getStorVal entry e.currentTarget chiSlot)
        (B256.rpow scale half rate
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat) ∧
      ¬ maxChi <
        (B256.rpow scale half rate
              (e.benvStat.time -
                Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
      scratch image' accumulatorWord =
        B256.rpow scale half rate
          (e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      scratch image' nowWord = e.benvStat.time ∧
      MachineOnly image image' ∧
      Frame image' entry t ∧
      (((B256.rpow scale half rate
          (e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
          Devm.getStorVal entry e.currentTarget chiSlot) / scale) :: tail <<+ t.stack) ∧
      Func.Run fs e t (.call freshRouteSlot) r := by
  obtain ⟨t, image', _, hlower, hupper, hclock, helapsed, hguards, hnofm, hcap,
    haccM, hnowM, hmachineM, framet, hpt, _, run⟩ :=
    of_run_freshStart_prefix (path := ⟨freshStartSlot, []⟩) hlookup frame hp
      run
  exact ⟨t, image', hlower, hupper, hclock, helapsed, hguards, hnofm, hcap,
    haccM, hnowM, hmachineM, framet, hpt, run⟩

/-! ## The route dispatcher

The machine returns through a finite five-way tag test.  A successful run
reaches exactly the endpoint tail its entry body staged; a tag outside the
five has no successful run, because the last test's rejecting arm is the
inline reverter. -/

private theorem of_run_routeTest_prefix {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    {c : B256} {body next : Func} {path : Prog.SourcePath}
    (frame : Frame image entry s)
    (hp : scratch image routeWord :: tail <<+ s.stack)
    (run : Func.Run fs e s
      (dup 0 ::: pushB256 c ::: eq ::: ((pop ::: body) <?> next)) r) :
    (scratch image routeWord = c ∧ ∃ t target, Frame image entry t ∧
        (tail <<+ t.stack) ∧
        Func.RunPrefix fs e path s
          (dup 0 ::: pushB256 c ::: eq ::: ((pop ::: body) <?> next)) target t
          body ∧
        Func.Run fs e t body r) ∨
      (∃ t target, Frame image entry t ∧
        (scratch image routeWord :: tail <<+ t.stack) ∧
        Func.RunPrefix fs e path s
          (dup 0 ::: pushB256 c ::: eq ::: ((pop ::: body) <?> next)) target t
          next ∧
        Func.Run fs e t next r) := by
  rcases run_prefix_prepend (l := [dup 0, pushB256 c, eq]) (path := path)
    (by simp only [Line.gasFree, Ninst.pushB256, Ninst.gasFree, Rinst.gasFree,
      Bool.true_and] : Line.gasFree [dup 0, pushB256 c, eq] = true) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : (c =? scratch image routeWord) :: scratch image routeWord ::
      tail <<+ s1.stack := by
    rcases Line.of_run_cons hline1 with ⟨u1, hdup, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, heq, hnil⟩
    cases hnil
    have hdupPrefix : scratch image routeWord :: scratch image routeWord ::
        tail <<+ u1.stack := prefix_of_dup_val hdup (by show_nth) hp
    exact prefix_of_eq heq
      (prefix_of_push (of_run_pushB256 hpush) hdupPrefix)
  rcases run_prefix_branch (path := mid1) run with
    ⟨s2, mid2, hpop, run, hpreB⟩
    | ⟨w, s2, s3, mid3, hnz, hpop, hburn, run, hpreB⟩
  · refine Or.inr ⟨s2, mid2, frame1.of_popBurn hpop, ?_,
      Func.RunPrefix.trans hpre1 hpreB, run⟩
    exact (popBurn_pref hpop hp1).2
  · have htag : scratch image routeWord = c := by
      by_contra hne
      rw [B256.eqCheck, if_neg (fun h => hne h.symm)] at hp1
      exact absurd (popBurn_pref hpop hp1).1 hnz
    refine Or.inl ⟨htag, ?_⟩
    have frame3 := (frame1.of_popBurn hpop).of_burn hburn
    have hp3 : scratch image routeWord :: tail <<+ s3.stack := by
      rw [← hburn.stack]
      exact (popBurn_pref hpop hp1).2
    rcases run_prefix_prepend (l := [pop]) (path := mid3)
      (by decide : Line.gasFree [pop] = true) run with
      ⟨s4, mid4, hline4, run, hpre4⟩
    have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
    exact ⟨s4, mid4, frame4,
      prefix_of_pop (of_run_pop (of_run_singleton hline4)) hp3,
      Func.RunPrefix.trans hpre1 (Func.RunPrefix.trans hpreB hpre4), run⟩

private theorem of_run_routeTest {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    {c : B256} {body next : Func}
    (frame : Frame image entry s)
    (hp : scratch image routeWord :: tail <<+ s.stack)
    (run : Func.Run fs e s
      (dup 0 ::: pushB256 c ::: eq ::: ((pop ::: body) <?> next)) r) :
    (scratch image routeWord = c ∧ ∃ t, Frame image entry t ∧
        (tail <<+ t.stack) ∧ Func.Run fs e t body r) ∨
      (∃ t, Frame image entry t ∧
        (scratch image routeWord :: tail <<+ t.stack) ∧
        Func.Run fs e t next r) := by
  rcases of_run_routeTest_prefix (path := ⟨freshRouteSlot, []⟩) frame hp run with
    ⟨htag, t, _, frt, hpt, _, run⟩ | ⟨t, _, frt, hpt, _, run⟩
  · exact Or.inl ⟨htag, t, frt, hpt, run⟩
  · exact Or.inr ⟨t, frt, hpt, run⟩

theorem of_run_freshRoute_prefix {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    {path : Prog.SourcePath}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call freshRouteSlot) r) :
    ∃ t target, Frame image entry t ∧ (tail <<+ t.stack) ∧
      ((scratch image routeWord = routeConvertToAssets ∧
          Func.RunPrefix fs e path s (.call freshRouteSlot) target t
            afterConvertToAssets ∧
          Func.Run fs e t afterConvertToAssets r) ∨
        (scratch image routeWord = routeExit ∧
          Func.RunPrefix fs e path s (.call freshRouteSlot) target t
            afterExit ∧
          Func.Run fs e t afterExit r) ∨
        (scratch image routeWord = routeConvertToUnits ∧
          Func.RunPrefix fs e path s (.call freshRouteSlot) target t
            afterConvertToUnits ∧
          Func.Run fs e t afterConvertToUnits r) ∨
        (scratch image routeWord = routeDrip ∧
          Func.RunPrefix fs e path s (.call freshRouteSlot) target t
            afterDrip ∧
          Func.Run fs e t afterDrip r) ∨
        (scratch image routeWord = routeJoin ∧
          Func.RunPrefix fs e path s (.call freshRouteSlot) target t
            afterJoin ∧
          Func.Run fs e t afterJoin r)) := by
  obtain ⟨s0, hburn0, hpre0, run⟩ :=
    of_run_call_of_lookup_prefix (path := path) hlookup.freshRoute run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.freshRoute at run
  rcases run_prefix_prepend (l := loadWord routeWord)
    (path := ⟨freshRouteSlot, []⟩) (gasFree_loadWord routeWord) run with
    ⟨s1, mid1, hline1, run, hpre1⟩
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  rcases of_run_routeTest_prefix (path := mid1) frame1 hp1 run with
    ⟨htag, t, midT, framet, hpt, hpreT, run⟩
    | ⟨s2, mid2, frame2, hp2, hpreT1, run⟩
  · refine ⟨t, midT, framet, hpt, Or.inl ⟨htag, ?_, run⟩⟩
    exact Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1 hpreT)
  rcases of_run_routeTest_prefix (path := mid2) frame2 hp2 run with
    ⟨htag, t, midT, framet, hpt, hpreT, run⟩
    | ⟨s3, mid3, frame3, hp3, hpreT2, run⟩
  · refine ⟨t, midT, framet, hpt, Or.inr (Or.inl ⟨htag, ?_, run⟩)⟩
    exact Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
      (Func.RunPrefix.trans hpreT1 hpreT))
  rcases of_run_routeTest_prefix (path := mid3) frame3 hp3 run with
    ⟨htag, t, midT, framet, hpt, hpreT, run⟩
    | ⟨s4, mid4, frame4, hp4, hpreT3, run⟩
  · refine ⟨t, midT, framet, hpt, Or.inr (Or.inr (Or.inl ⟨htag, ?_, run⟩))⟩
    exact Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
      (Func.RunPrefix.trans hpreT1 (Func.RunPrefix.trans hpreT2 hpreT)))
  rcases of_run_routeTest_prefix (path := mid4) frame4 hp4 run with
    ⟨htag, t, midT, framet, hpt, hpreT, run⟩
    | ⟨s5, mid5, frame5, hp5, hpreT4, run⟩
  · refine ⟨t, midT, framet, hpt,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨htag, ?_, run⟩)))⟩
    exact Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
      (Func.RunPrefix.trans hpreT1 (Func.RunPrefix.trans hpreT2
        (Func.RunPrefix.trans hpreT3 hpreT))))
  -- the last test has no `pop`: the tag word is consumed by the comparison
  rcases run_prefix_prepend (l := [pushB256 routeJoin, eq]) (path := mid5)
    (by decide : Line.gasFree [pushB256 routeJoin, eq] = true) run with
    ⟨s6, mid6, hline6, run, hpre6⟩
  have frame6 := frame5.line (by line_inv) (by line_inv) (by line_inv) hline6
  have hp6 : (routeJoin =? scratch image routeWord) :: tail <<+ s6.stack := by
    rcases Line.of_run_cons hline6 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, heq, hnil⟩
    cases hnil
    exact prefix_of_eq heq (prefix_of_push (of_run_pushB256 hpush) hp5)
  rcases run_prefix_branch (path := mid6) run with
    ⟨s7, mid7, hpop, run, hpreB⟩
    | ⟨w, s7, s8, mid8, hnz, hpop, hburn, run, hpreB⟩
  · exact absurd run not_run_revert
  · have htag : scratch image routeWord = routeJoin := by
      by_contra hne
      rw [B256.eqCheck, if_neg (fun h => hne h.symm)] at hp6
      exact absurd (popBurn_pref hpop hp6).1 hnz
    refine ⟨s8, mid8, (frame6.of_popBurn hpop).of_burn hburn, ?_,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨htag, ?_, run⟩)))⟩
    · rw [← hburn.stack]
      exact (popBurn_pref hpop hp6).2
    · exact Func.RunPrefix.trans hpre0 (Func.RunPrefix.trans hpre1
        (Func.RunPrefix.trans hpreT1 (Func.RunPrefix.trans hpreT2
          (Func.RunPrefix.trans hpreT3 (Func.RunPrefix.trans hpreT4
            (Func.RunPrefix.trans hpre6 hpreB))))))

theorem of_run_freshRoute {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call freshRouteSlot) r) :
    ∃ t, Frame image entry t ∧ (tail <<+ t.stack) ∧
      ((scratch image routeWord = routeConvertToAssets ∧
          Func.Run fs e t afterConvertToAssets r) ∨
        (scratch image routeWord = routeExit ∧
          Func.Run fs e t afterExit r) ∨
        (scratch image routeWord = routeConvertToUnits ∧
          Func.Run fs e t afterConvertToUnits r) ∨
        (scratch image routeWord = routeDrip ∧
          Func.Run fs e t afterDrip r) ∨
        (scratch image routeWord = routeJoin ∧
          Func.Run fs e t afterJoin r)) := by
  rcases of_run_freshRoute_prefix (path := ⟨freshRouteSlot, []⟩) hlookup frame
    hp run with
    ⟨t, _, frt, hpt, hdisj⟩
  refine ⟨t, frt, hpt, ?_⟩
  rcases hdisj with ⟨htag, _, run⟩ | ⟨htag, _, run⟩ | ⟨htag, _, run⟩
    | ⟨htag, _, run⟩ | ⟨htag, _, run⟩
  · exact Or.inl ⟨htag, run⟩
  · exact Or.inr (Or.inl ⟨htag, run⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htag, run⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨htag, run⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨htag, run⟩)))

end Drip

end Blanc
