-- DripFresh.lean : DRIP's shared fresh-index machine, inverted.
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
import Blanc.Ladder
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

/-! ## The guard shape

Every DRIP check computes one flag and takes `.revert <?> continuation`.  A
successful run therefore forces the flag to zero — the rejecting arm is the
inline `Func.revert`, which has no successful run at all — and continues in
the fall-through with the flag popped. -/

theorem of_run_guard {fs : List Func} {e : Sevm} {s r : Devm}
    {flag : B256} {tail : Stack} {cont : Func}
    (hp : flag :: tail <<+ s.stack)
    (run : Func.Run fs e s (.revert <?> cont) r) :
    flag = 0 ∧ ∃ t, (tail <<+ t.stack) ∧ Devm.PopBurn [0] s t ∧
      Func.Run fs e t cont r := by
  rcases of_run_branch run with
    ⟨t, hpop, hcont⟩ | ⟨w, t, u, hnz, hpop, hburn, hrev⟩
  · rcases popBurn_pref hpop hp with ⟨hflag, htail⟩
    exact ⟨hflag.symm, t, htail, hpop, hcont⟩
  · exact absurd hrev not_run_revert

private theorem of_run_single {e : Sevm} {s t : Devm} {i : Ninst}
    (run : Line.Run e s [i] t) : Ninst.Run e s i t := by
  rcases Line.of_run_cons run with ⟨u, hi, hnil⟩
  cases hnil
  exact hi

/-! ## Reading a zero flag

Each DRIP guard's fall-through says its flag word is zero.  These three turn
that word back into the comparison it stands for. -/

private theorem eq_of_iszero_eqCheck_eq_zero {x y : B256}
    (h : ((x =? y) =? 0) = 0) : x = y := by
  by_contra hne
  simp only [B256.eqCheck, if_neg hne] at h
  exact absurd h (by decide +kernel)

private theorem not_lt_of_ltCheck_eq_zero {x y : B256} (h : (x <? y) = 0) :
    ¬ x < y := by
  intro hlt
  rw [B256.ltCheck, if_pos hlt] at h
  exact absurd h (by decide +kernel)

/-- Word multiplication commutes.  Jaune states `B256.add_comm` but not this;
it is a contract-neutral shape and belongs beside `B256.and_comm` and
`B256.xor_comm` in the common library.  It is proved here only because the
hoist needs a build slot this host is currently refusing, and is recorded as
an outstanding common-library-first action in the goal's state brief. -/
private theorem b256_mul_comm (x y : B256) : x * y = y * x := by
  apply B256.toNat_inj
  rw [B256.toNat_mul, B256.toNat_mul, Nat.mul_comm]

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
        (setScratch
          (setScratch image roundedWord
            (half + scratch image rightWord * scratch image leftWord))
          outputWord
          ((half + scratch image rightWord * scratch image leftWord) / scale))
        entry t ∧
      Func.Run fs e t next r := by
  unfold guardedRoundedMul at run
  refine run_prepend_elim _ (loadWord leftWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
  refine run_prepend_elim _ (loadWord rightWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.loadWord hp1 hline2
  refine run_prepend_elim _ [mul, dup 0] ?_ run
  intro s3 hline3 run
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : scratch image rightWord * scratch image leftWord ::
      scratch image rightWord * scratch image leftWord :: tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u, hmul, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_mul hmul hp2)
  refine run_prepend_elim _ (loadWord rightWord) ?_ run
  intro s4 hline4 run
  obtain ⟨hp4, frame4⟩ := frame3.loadWord hp3 hline4
  refine run_prepend_elim _ [swap 0, div] ?_ run
  intro s5 hline5 run
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
  refine run_prepend_elim _ (loadWord leftWord) ?_ run
  intro s6 hline6 run
  obtain ⟨hp6, frame6⟩ := frame5.loadWord hp5 hline6
  refine run_prepend_elim _ [eq, iszero] ?_ run
  intro s7 hline7 run
  have frame7 := frame6.line (by line_inv) (by line_inv) (by line_inv) hline7
  have hp7 : ((scratch image leftWord =?
        ((scratch image rightWord * scratch image leftWord) /
          scratch image rightWord)) =? 0) ::
      scratch image rightWord * scratch image leftWord :: tail <<+ s7.stack := by
    rcases Line.of_run_cons hline7 with ⟨u, heq, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hiszero, hnil⟩
    cases hnil
    exact prefix_of_iszero hiszero (prefix_of_eq heq hp6)
  obtain ⟨hflag1, s8, hp8, hpop8, run⟩ := of_run_guard hp7 run
  have frame8 := frame7.of_popBurn hpop8
  have hrecover := eq_of_iszero_eqCheck_eq_zero hflag1
  have hnofm : B256.Nofm (scratch image leftWord) (scratch image rightWord) := by
    by_cases hzero : scratch image rightWord = 0
    · rw [hzero]
      exact nofm_right_zero _
    · refine (B256.mul_div_eq_iff_nofm hzero).1 ?_
      rw [b256_mul_comm (scratch image leftWord)]
      exact hrecover.symm
  refine run_prepend_elim _ [dup 0, pushB256 half, add, dup 0] ?_ run
  intro s9 hline9 run
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
  refine run_prepend_elim _ (mstoreAt roundedWord) ?_ run
  intro s10 hline10 run
  obtain ⟨hp10, frame10⟩ := frame9.mstoreAt hp9 hline10
  refine run_prepend_elim _ [lt] ?_ run
  intro s11 hline11 run
  have frame11 := frame10.line (by line_inv) (by line_inv) (by line_inv) hline11
  have hp11 : ((half + scratch image rightWord * scratch image leftWord) <?
      (scratch image rightWord * scratch image leftWord)) :: tail <<+ s11.stack :=
    prefix_of_lt (of_run_single hline11) hp10
  obtain ⟨hflag2, s12, hp12, hpop12, run⟩ := of_run_guard hp11 run
  have frame12 := frame11.of_popBurn hpop12
  have hnof : B256.Nof (scratch image rightWord * scratch image leftWord) half := by
    by_contra hcontra
    exact not_lt_of_ltCheck_eq_zero hflag2
      (by rw [B256.add_comm]; exact (B256.add_lt_iff_not_nof _ _).2 hcontra)
  refine run_prepend_elim _ (loadWord roundedWord) ?_ run
  intro s13 hline13 run
  obtain ⟨hp13, frame13⟩ := frame12.loadWord hp12 hline13
  rw [scratch_setScratch_self] at hp13
  refine run_prepend_elim _ [pushB256 scale, swap 0, div] ?_ run
  intro s14 hline14 run
  have frame14 := frame13.line (by line_inv) (by line_inv) (by line_inv) hline14
  have hp14 : (((half + scratch image rightWord * scratch image leftWord) /
      scale)) :: tail <<+ s14.stack := by
    rcases Line.of_run_cons hline14 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdiv, hnil⟩
    cases hnil
    have h1 := prefix_of_push (of_run_pushB256 hpush) hp13
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
  refine run_prepend_elim _ (mstoreAt outputWord) ?_ run
  intro s15 hline15 run
  obtain ⟨hp15, frame15⟩ := frame14.mstoreAt hp14 hline15
  exact ⟨s15, hnofm, hnof, hp15, frame15, run⟩

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

private theorem of_run_call_of_lookup {fs : List Func} {e : Sevm} {s r : Devm}
    {k : Nat} {f : Func} (hlookup : fs[k]? = some f)
    (run : Func.Run fs e s (.call k) r) :
    ∃ t, Devm.Burn s t ∧ Func.Run fs e t f r := by
  cases run with
  | call hget hburn hbody =>
      rename_i t _
      rw [hlookup] at hget
      cases Option.some.inj hget
      exact ⟨t, hburn, hbody⟩

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

theorem exponent_base : SlotsDisjoint exponentWord baseWord :=
  Or.inl (by decide +kernel)
theorem exponent_accumulator : SlotsDisjoint exponentWord accumulatorWord :=
  Or.inl (by decide +kernel)
theorem exponent_rounded : SlotsDisjoint exponentWord roundedWord :=
  Or.inl (by decide +kernel)
theorem base_accumulator : SlotsDisjoint baseWord accumulatorWord :=
  Or.inl (by decide +kernel)
theorem base_rounded : SlotsDisjoint baseWord roundedWord :=
  Or.inl (by decide +kernel)
theorem accumulator_rounded : SlotsDisjoint accumulatorWord roundedWord :=
  Or.inl (by decide +kernel)

/-- The runtime's low-bit parity test is exactly `Nat` parity of the exponent
word. -/
private theorem toNat_one_and (x : B256) :
    ((1 : B256) &&& x).toNat = x.toNat % 2 := by
  rw [B256.toNat_and, show (1 : B256).toNat = 1 by decide +kernel]
  exact Nat.one_and_eq_mod_two x.toNat

/-! ## Halving the exponent, and the conditional multiply

`rpowAdvance` divides the exponent word by two and re-enters the loop;
`rpowAfterSquare` multiplies the accumulator by the freshly squared base
exactly when the exponent's low bit is set, and then advances.  Both are
stated over an abstract scratch image so the loop induction never has to carry
a concrete one. -/

private theorem of_run_rpowAdvance {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call rpowAdvanceSlot) r) :
    ∃ t, (tail <<+ t.stack) ∧
      Frame (setScratch image exponentWord (scratch image exponentWord / 2))
        entry t ∧
      Func.Run fs e t (.call rpowLoopSlot) r := by
  obtain ⟨s0, hburn0, run⟩ := of_run_call_of_lookup hlookup.rpowAdvance run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.rpowAdvance at run
  refine run_prepend_elim _ (loadWord exponentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  refine run_prepend_elim _ [pushB256 2, swap 0, div] ?_ run
  intro s2 hline2 run
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
  refine run_prepend_elim _ (mstoreAt exponentWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.mstoreAt hp2 hline3
  exact ⟨s3, hp3, frame3, run⟩

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
  obtain ⟨s0, hburn0, run⟩ := of_run_call_of_lookup hlookup.rpowAfterSquare run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.rpowAfterSquare at run
  refine run_prepend_elim _ (loadWord exponentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  refine run_prepend_elim _ [pushB256 1, and] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : ((1 : B256) &&& scratch image exponentWord) :: tail <<+ s2.stack := by
    rcases Line.of_run_cons hline2 with ⟨v1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v2, hand, hnil⟩
    cases hnil
    exact prefix_of_and hand (prefix_of_push (of_run_pushB256 hpush) hp1)
  have hparity : ((1 : B256) &&& scratch image exponentWord) = 0 ↔
      (scratch image exponentWord).toNat % 2 ≠ 1 := by
    constructor
    · intro hzero hodd
      have := toNat_one_and (scratch image exponentWord)
      rw [hzero, B256.toNat_zero, hodd] at this
      exact absurd this.symm (by decide)
    · intro heven
      apply B256.toNat_inj
      rw [toNat_one_and, B256.toNat_zero]
      omega
  rcases of_run_branch run with
    ⟨v, hpop, run⟩ | ⟨w, v, v', hnz, hpop, hburn, run⟩
  · -- low bit clear: skip the multiply
    have hflag : ((1 : B256) &&& scratch image exponentWord) = 0 :=
      (popBurn_pref hpop hp2).1.symm
    have heven : (scratch image exponentWord).toNat % 2 ≠ 1 := hparity.1 hflag
    have frameV := frame2.of_popBurn hpop
    have hpV : tail <<+ v.stack := (popBurn_pref hpop hp2).2
    obtain ⟨t, hpt, framet, run⟩ := of_run_rpowAdvance hlookup frameV hpV run
    refine ⟨t, setScratch image exponentWord (scratch image exponentWord / 2),
      by rw [if_neg heven]; trivial, ?_, ?_, ?_, ?_, framet, hpt, run⟩
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
    obtain ⟨v1, hnofm, hnof, hpV1, frameV1, run⟩ :=
      of_run_guardedRoundedMul frameV hpV run
    obtain ⟨t, hpt, framet, run⟩ := of_run_rpowAdvance hlookup frameV1 hpV1 run
    refine ⟨t, _, by rw [if_pos hodd]; exact ⟨hnofm, hnof⟩, ?_, ?_, ?_, ?_,
      framet, hpt, run⟩
    · rw [if_pos hodd,
        scratch_setScratch_of_disjoint _ _ exponent_accumulator.symm,
        scratch_setScratch_self]
      unfold B256.mulr
      rw [@B256.add_comm half
          (scratch image baseWord * scratch image accumulatorWord),
        b256_mul_comm (scratch image baseWord)]
    · rw [scratch_setScratch_of_disjoint _ _ exponent_base.symm,
        scratch_setScratch_of_disjoint _ _ base_accumulator,
        scratch_setScratch_of_disjoint _ _ base_rounded]
    · rw [scratch_setScratch_self,
        scratch_setScratch_of_disjoint _ _ exponent_accumulator,
        scratch_setScratch_of_disjoint _ _ exponent_rounded]
    · exact ((LoopOnly.rounded image _).trans
        (LoopOnly.accumulator _ _)).trans (LoopOnly.exponent _ _)

/-! ## The square-and-multiply loop

A successful run of the machine's loop slot is exactly Jaune's guarded word
loop: it establishes `B256.RPowLoopGuards` from the checks the runtime
actually crossed, leaves `B256.rpowLoop` in the accumulator slot, and reaches
the index-composition slot.  The induction is on the exponent's `Nat` image,
which the runtime halves once per iteration. -/

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
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s image tail hexp frame hp run
  obtain ⟨s0, hburn0, run⟩ := of_run_call_of_lookup hlookup.rpowLoop run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.rpowLoop at run
  refine run_prepend_elim _ (loadWord exponentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  refine run_prepend_elim _ [iszero] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : ((scratch image exponentWord) =? 0) :: tail <<+ s2.stack :=
    prefix_of_iszero (of_run_single hline2) hp1
  by_cases hn : n = 0
  · -- exponent zero: the loop is the identity and jumps straight to composition
    have hE : scratch image exponentWord = 0 :=
      B256.toNat_inj _ 0 (by rw [hexp, hn, B256.toNat_zero])
    rw [hE, B256.eqCheck, if_pos rfl] at hp2
    rcases of_run_branch run with
      ⟨u, hpop, hsquare⟩ | ⟨w, u, v, hnz, hpop, hburn, hcompose⟩
    · exact absurd (popBurn_pref hpop hp2).1 (by decide +kernel)
    · refine ⟨v, image, ?_, ?_, LoopOnly.rfl' image,
        (frame2.of_popBurn hpop).of_burn hburn, ?_, hcompose⟩
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
    rcases of_run_branch run with
      ⟨u, hpop, hsquare⟩ | ⟨w, u, v, hnz, hpop, hburn, hcompose⟩
    swap
    · exact absurd (popBurn_pref hpop hp2).1 hnz
    have frameU := frame2.of_popBurn hpop
    have hpU : tail <<+ u.stack := (popBurn_pref hpop hp2).2
    obtain ⟨u1, hnofmSquare, hnofSquare, hpU1, frameU1, run⟩ :=
      of_run_guardedRoundedMul frameU hpU hsquare
    obtain ⟨t1, image2, hcond, hacc2, hbase2, hexp2, hloop12, framet1, hpt1,
      run⟩ := of_run_rpowAfterSquare hlookup frameU1 hpU1 run
    rw [scratch_setScratch_self] at hcond hacc2 hbase2
    rw [scratch_setScratch_of_disjoint _ _ exponent_base,
      scratch_setScratch_of_disjoint _ _ exponent_rounded] at hcond hacc2 hexp2
    rw [scratch_setScratch_of_disjoint _ _ base_accumulator.symm,
      scratch_setScratch_of_disjoint _ _ accumulator_rounded] at hcond hacc2
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
    obtain ⟨t2, image3, hguards2, hacc3, hloop23, framet2, hpt2, run⟩ :=
      ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
        hexpNat framet1 hpt1 run
    rw [hacc2, hbase2] at hguards2 hacc3
    refine ⟨t2, image3, ?_, ?_, ?_, framet2, hpt2, run⟩
    · rw [B256.RPowLoopGuards, dif_neg hn]
      refine ⟨hnofmSquare, hnofSquare, ?_, hguards2⟩
      by_cases hpar : n % 2 = 1
      · rw [if_pos hpar] at hcond ⊢
        exact ⟨hcond.1, by rw [b256_mul_comm]; exact hcond.2⟩
      · rw [if_neg hpar]
        trivial
    · rw [B256.rpowLoop, dif_neg hn]
      exact hacc3
    · exact (((LoopOnly.rounded image _).trans
        (LoopOnly.base _ _)).trans hloop12).trans hloop23

end Drip

end Blanc
