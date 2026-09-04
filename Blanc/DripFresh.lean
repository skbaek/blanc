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
  have hparity := one_and_eq_zero_iff (scratch image exponentWord)
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

/-! ## Floor composition onto the stored index

`composeFresh` multiplies the stored index by the realized factor under the
same exact division-recovery check, floors the product by the scale — with no
half-up offset, which is the frozen memo's rule that the loop's rounding and
the outer composition play different roles — and rejects any result above the
frozen index cap. -/

theorem of_run_composeFresh {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s (.call composeFreshSlot) r) :
    ∃ t,
      B256.Nofm (scratch image storedChiWord) (scratch image accumulatorWord) ∧
      ¬ maxChi <
        (scratch image accumulatorWord * scratch image storedChiWord) / scale ∧
      (tail <<+ t.stack) ∧
      Frame
        (setScratch image freshChiWord
          ((scratch image accumulatorWord * scratch image storedChiWord) / scale))
        entry t ∧
      Func.Run fs e t (.call freshRouteSlot) r := by
  obtain ⟨s0, hburn0, run⟩ := of_run_call_of_lookup hlookup.composeFresh run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.composeFresh at run
  refine run_prepend_elim _ (loadWord storedChiWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  refine run_prepend_elim _ (loadWord accumulatorWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.loadWord hp1 hline2
  refine run_prepend_elim _ [mul, dup 0] ?_ run
  intro s3 hline3 run
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : (scratch image accumulatorWord * scratch image storedChiWord) ::
      (scratch image accumulatorWord * scratch image storedChiWord) ::
      tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u, hmul, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_mul hmul hp2)
  refine run_prepend_elim _ (loadWord accumulatorWord) ?_ run
  intro s4 hline4 run
  obtain ⟨hp4, frame4⟩ := frame3.loadWord hp3 hline4
  refine run_prepend_elim _ [swap 0, div] ?_ run
  intro s5 hline5 run
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
  refine run_prepend_elim _ (loadWord storedChiWord) ?_ run
  intro s6 hline6 run
  obtain ⟨hp6, frame6⟩ := frame5.loadWord hp5 hline6
  refine run_prepend_elim _ [eq, iszero] ?_ run
  intro s7 hline7 run
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
  obtain ⟨hflag1, s8, hp8, hpop8, run⟩ := of_run_guard hp7 run
  have frame8 := frame7.of_popBurn hpop8
  have hrecover := eq_of_iszero_eqCheck_eq_zero hflag1
  have hnofm : B256.Nofm (scratch image storedChiWord)
      (scratch image accumulatorWord) := by
    by_cases hzero : scratch image accumulatorWord = 0
    · rw [hzero]
      exact nofm_right_zero _
    · refine (B256.mul_div_eq_iff_nofm hzero).1 ?_
      rw [b256_mul_comm (scratch image storedChiWord)]
      exact hrecover.symm
  refine run_prepend_elim _ [pushB256 scale, swap 0, div, dup 0] ?_ run
  intro s9 hline9 run
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
  refine run_prepend_elim _ (mstoreAt freshChiWord) ?_ run
  intro s10 hline10 run
  obtain ⟨hp10, frame10⟩ := frame9.mstoreAt hp9 hline10
  refine run_prepend_elim _ [pushB256 maxChi, lt] ?_ run
  intro s11 hline11 run
  have frame11 := frame10.line (by line_inv) (by line_inv) (by line_inv) hline11
  have hp11 : (maxChi <?
      ((scratch image accumulatorWord * scratch image storedChiWord) / scale))
      :: tail <<+ s11.stack := by
    rcases Line.of_run_cons hline11 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp10)
  obtain ⟨hflag2, s12, hp12, hpop12, run⟩ := of_run_guard hp11 run
  have frame12 := frame11.of_popBurn hpop12
  exact ⟨s12, hnofm, not_lt_of_ltCheck_eq_zero hflag2, hp12, frame12, run⟩

/-- The exponent-halving tail shared by both initialization arms: halve the
staged exponent, run the loop, and arrive at index composition with the
realized factor in the accumulator slot. -/
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
  have hrateNe : rate ≠ 0 := by decide +kernel
  refine run_prepend_elim _ (loadWord exponentWord) ?_ run
  intro u1 hl1 run
  obtain ⟨hpu1, frameu1⟩ := frameImg.loadWord hpImg hl1
  rw [hexpImg] at hpu1
  refine run_prepend_elim _ [pushB256 2, swap 0, div] ?_ run
  intro u2 hl2 run
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
  refine run_prepend_elim _ (mstoreAt exponentWord) ?_ run
  intro u3 hl3 run
  obtain ⟨hpu3, frameu3⟩ := frameu2.mstoreAt hpu2 hl3
  have hexpNat :
      (scratch (setScratch img exponentWord (k / 2)) exponentWord).toNat =
        k.toNat / 2 := by
    rw [scratch_setScratch_self,
      B256.toNat_div (by decide +kernel : (2 : B256) ≠ 0),
      show (2 : B256).toNat = 2 by decide +kernel]
  obtain ⟨t2, imageF, hguardsL, haccF, hloopF, frameF, hpF, run⟩ :=
    of_run_rpowLoop hlookup _ hexpNat frameu3 hpu3 run
  rw [scratch_setScratch_of_disjoint _ _ accumulator_exponent, haccImg,
      scratch_setScratch_of_disjoint _ _ base_exponent, hbaseImg]
    at hguardsL haccF
  refine ⟨t2, imageF, ?_, ?_, ?_, ?_, ?_, frameF, hpF, run⟩
  · rw [B256.RPowGuards, if_neg hrateNe, if_neg hkNat, ← hacc]
    exact hguardsL
  · rw [haccF, B256.rpow, if_neg hrateNe, if_neg hkNat, ← hacc]
  · rw [hloopF.storedChi,
      scratch_setScratch_of_disjoint _ _ storedChi_exponent, hchiImg]
  · rw [hloopF.now, scratch_setScratch_of_disjoint _ _ now_exponent, hnowImg]
  · exact hmachineImg.trans
      ((MachineOnly.exponent img _).trans hloopF.toMachineOnly)

/-! ## The machine's entry: guards, initialization, loop, composition

A successful run of the machine's start slot crosses four checks in order —
the stored index is in range, the clock has not gone backwards, and the
elapsed interval is within the frozen four-byte ceiling — then runs the loop
at the elapsed exponent and floor-composes the realized factor onto the stored
index.  Every one of those is a *conclusion* here, established from the
branches the run actually took. -/

private theorem getStorVal_of_state {s t : Devm} (h : s.state = t.state)
    (a : Adr) (k : B256) :
    Devm.getStorVal s a k = Devm.getStorVal t a k := by
  unfold Devm.getStorVal Devm.getAcct
  rw [h]

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
      scratch image' freshChiWord =
        (B256.rpow scale half rate
              (e.benvStat.time -
                Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
      scratch image' nowWord = e.benvStat.time ∧
      MachineOnly image image' ∧
      Frame image' entry t ∧ (tail <<+ t.stack) ∧
      Func.Run fs e t (.call freshRouteSlot) r := by
  obtain ⟨s0, hburn0, run⟩ := of_run_call_of_lookup hlookup.freshStart run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.freshStart at run
  -- SLOAD the stored index and stage it
  refine run_prepend_elim _ [pushB256 chiSlot, sload] ?_ run
  intro s1 hline1 run
  have frame1 := frame0.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : Devm.getStorVal entry e.currentTarget chiSlot :: tail <<+
      s1.stack := by
    rcases Line.of_run_cons hline1 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hsload, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) hp0)
    rw [hyval,
      getStorVal_of_state
        (frame0.state.trans (of_run_pushB256 hpush).state).symm] at hy
    simpa using hy
  refine run_prepend_elim _ (mstoreAt storedChiWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.mstoreAt hp1 hline2
  -- the stored index is at least the scale
  refine run_prepend_elim _ [pushB256 scale] ?_ run
  intro s3 hline3 run
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : scale :: tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp2
  refine run_prepend_elim _ (loadWord storedChiWord) ?_ run
  intro s4 hline4 run
  obtain ⟨hp4, frame4⟩ := frame3.loadWord hp3 hline4
  rw [scratch_setScratch_self] at hp4
  refine run_prepend_elim _ [lt] ?_ run
  intro s5 hline5 run
  have frame5 := frame4.line (by line_inv) (by line_inv) (by line_inv) hline5
  have hp5 : ((Devm.getStorVal entry e.currentTarget chiSlot) <? scale) ::
      tail <<+ s5.stack := prefix_of_lt (of_run_single hline5) hp4
  obtain ⟨hflagLower, s6, hp6, hpop6, run⟩ := of_run_guard hp5 run
  have frame6 := frame5.of_popBurn hpop6
  have hlower := not_lt_of_ltCheck_eq_zero hflagLower
  -- the stored index is within the frozen cap
  refine run_prepend_elim _ (loadWord storedChiWord) ?_ run
  intro s7 hline7 run
  obtain ⟨hp7, frame7⟩ := frame6.loadWord hp6 hline7
  rw [scratch_setScratch_self] at hp7
  refine run_prepend_elim _ [pushB256 maxChi, lt] ?_ run
  intro s8 hline8 run
  have frame8 := frame7.line (by line_inv) (by line_inv) (by line_inv) hline8
  have hp8 : (maxChi <? Devm.getStorVal entry e.currentTarget chiSlot) ::
      tail <<+ s8.stack := by
    rcases Line.of_run_cons hline8 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp7)
  obtain ⟨hflagUpper, s9, hp9, hpop9, run⟩ := of_run_guard hp8 run
  have frame9 := frame8.of_popBurn hpop9
  have hupper := not_lt_of_ltCheck_eq_zero hflagUpper
  -- stage the block timestamp
  refine run_prepend_elim _ [timestamp] ?_ run
  intro s10 hline10 run
  have frame10 := frame9.timestamp (of_run_single hline10)
  have hp10 : e.benvStat.time :: tail <<+ s10.stack :=
    prefix_of_timestamp hp9 (of_run_single hline10)
  refine run_prepend_elim _ (mstoreAt nowWord) ?_ run
  intro s11 hline11 run
  obtain ⟨hp11, frame11⟩ := frame10.mstoreAt hp10 hline11
  -- the clock has not gone backwards
  refine run_prepend_elim _ [pushB256 rhoSlot, sload] ?_ run
  intro s12 hline12 run
  have frame12 := frame11.line (by line_inv) (by line_inv) (by line_inv) hline12
  have hp12 : Devm.getStorVal entry e.currentTarget rhoSlot :: tail <<+
      s12.stack := by
    rcases Line.of_run_cons hline12 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hsload, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) hp11)
    rw [hyval,
      getStorVal_of_state
        (frame11.state.trans (of_run_pushB256 hpush).state).symm] at hy
    simpa using hy
  refine run_prepend_elim _ (loadWord nowWord) ?_ run
  intro s13 hline13 run
  obtain ⟨hp13, frame13⟩ := frame12.loadWord hp12 hline13
  rw [scratch_setScratch_self] at hp13
  refine run_prepend_elim _ [lt] ?_ run
  intro s14 hline14 run
  have frame14 := frame13.line (by line_inv) (by line_inv) (by line_inv) hline14
  have hp14 : (e.benvStat.time <?
      Devm.getStorVal entry e.currentTarget rhoSlot) :: tail <<+ s14.stack :=
    prefix_of_lt (of_run_single hline14) hp13
  obtain ⟨hflagClock, s15, hp15, hpop15, run⟩ := of_run_guard hp14 run
  have frame15 := frame14.of_popBurn hpop15
  have hclock := not_lt_of_ltCheck_eq_zero hflagClock
  -- stage the elapsed interval
  refine run_prepend_elim _ [pushB256 rhoSlot, sload] ?_ run
  intro s16 hline16 run
  have frame16 := frame15.line (by line_inv) (by line_inv) (by line_inv) hline16
  have hp16 : Devm.getStorVal entry e.currentTarget rhoSlot :: tail <<+
      s16.stack := by
    rcases Line.of_run_cons hline16 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hsload, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) hp15)
    rw [hyval,
      getStorVal_of_state
        (frame15.state.trans (of_run_pushB256 hpush).state).symm] at hy
    simpa using hy
  refine run_prepend_elim _ (loadWord nowWord) ?_ run
  intro s17 hline17 run
  obtain ⟨hp17, frame17⟩ := frame16.loadWord hp16 hline17
  rw [scratch_setScratch_self] at hp17
  refine run_prepend_elim _ [sub] ?_ run
  intro s18 hline18 run
  have frame18 := frame17.line (by line_inv) (by line_inv) (by line_inv) hline18
  have hp18 : (e.benvStat.time -
      Devm.getStorVal entry e.currentTarget rhoSlot) :: tail <<+ s18.stack :=
    prefix_of_sub (of_run_single hline18) hp17
  refine run_prepend_elim _ (mstoreAt exponentWord) ?_ run
  intro s19 hline19 run
  obtain ⟨hp19, frame19⟩ := frame18.mstoreAt hp18 hline19
  -- the elapsed interval is within the frozen four-byte ceiling
  refine run_prepend_elim _ (loadWord exponentWord) ?_ run
  intro s20 hline20 run
  obtain ⟨hp20, frame20⟩ := frame19.loadWord hp19 hline20
  rw [scratch_setScratch_self] at hp20
  refine run_prepend_elim _ [pushB256 maxElapsed, lt] ?_ run
  intro s21 hline21 run
  have frame21 := frame20.line (by line_inv) (by line_inv) (by line_inv) hline21
  have hp21 : (maxElapsed <? (e.benvStat.time -
      Devm.getStorVal entry e.currentTarget rhoSlot)) :: tail <<+ s21.stack := by
    rcases Line.of_run_cons hline21 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp20)
  obtain ⟨hflagElapsed, s22, hp22, hpop22, run⟩ := of_run_guard hp21 run
  have frame22 := frame21.of_popBurn hpop22
  have helapsed := not_lt_of_ltCheck_eq_zero hflagElapsed
  -- initialize the loop's base; the zero-base arm is unreachable at DRIP's rate
  have hrateNe : rate ≠ 0 := by decide +kernel
  refine run_prepend_elim _ [pushB256 rate, dup 0] ?_ run
  intro s23 hline23 run
  have frame23 := frame22.line (by line_inv) (by line_inv) (by line_inv) hline23
  have hp23 : rate :: rate :: tail <<+ s23.stack := by
    rcases Line.of_run_cons hline23 with ⟨u, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨v, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth)
      (prefix_of_push (of_run_pushB256 hpush) hp22)
  refine run_prepend_elim _ (mstoreAt baseWord) ?_ run
  intro s24 hline24 run
  obtain ⟨hp24, frame24⟩ := frame23.mstoreAt hp23 hline24
  refine run_prepend_elim _ [iszero] ?_ run
  intro s25 hline25 run
  have frame25 := frame24.line (by line_inv) (by line_inv) (by line_inv) hline25
  have hp25 : (rate =? 0) :: tail <<+ s25.stack :=
    prefix_of_iszero (of_run_single hline25) hp24
  rw [B256.eqCheck, if_neg hrateNe] at hp25
  rcases of_run_branch run with
    ⟨s26, hpop26, run⟩ | ⟨w, s26, s26', hnz, hpop26, hburn26, run⟩
  swap
  · exact absurd (popBurn_pref hpop26 hp25).1 hnz
  have frame26 := frame25.of_popBurn hpop26
  have hp26 : tail <<+ s26.stack := (popBurn_pref hpop26 hp25).2
  refine run_prepend_elim _ (loadWord exponentWord) ?_ run
  intro s27 hline27 run
  obtain ⟨hp27, frame27⟩ := frame26.loadWord hp26 hline27
  rw [scratch_setScratch_of_disjoint _ _ exponent_base,
    scratch_setScratch_self] at hp27
  refine run_prepend_elim _ [iszero] ?_ run
  intro s28 hline28 run
  have frame28 := frame27.line (by line_inv) (by line_inv) (by line_inv) hline28
  have hp28 : ((e.benvStat.time -
      Devm.getStorVal entry e.currentTarget rhoSlot) =? 0) :: tail <<+
      s28.stack := prefix_of_iszero (of_run_single hline28) hp27
  -- both initialization arms converge on the index-composition slot
  have key : ∃ tm imageM,
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      scratch imageM accumulatorWord =
        B256.rpow scale half rate
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      scratch imageM storedChiWord =
        Devm.getStorVal entry e.currentTarget chiSlot ∧
      scratch imageM nowWord = e.benvStat.time ∧
      MachineOnly image imageM ∧
      Frame imageM entry tm ∧ (tail <<+ tm.stack) ∧
      Func.Run fs e tm (.call composeFreshSlot) r := by
    rcases of_run_branch run with
      ⟨s29, hpop29, run⟩ | ⟨w', s29, s29', hnz', hpop29, hburn29, run⟩
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
      refine run_prepend_elim _ (loadWord exponentWord) ?_ run
      intro s30 hline30 run
      obtain ⟨hp30, frame30⟩ := frame29.loadWord hp29 hline30
      rw [scratch_setScratch_of_disjoint _ _ exponent_base,
        scratch_setScratch_self] at hp30
      refine run_prepend_elim _ [pushB256 1, and] ?_ run
      intro s31 hline31 run
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
      rcases of_run_branch run with
        ⟨s32, hpop32, run⟩ | ⟨w'', s32, s32', hnz'', hpop32, hburn32, run⟩
      · -- even exponent: seed the accumulator with the scale
        have heven := hparity.1 (popBurn_pref hpop32 hp31).1.symm
        have frame32 := frame31.of_popBurn hpop32
        have hp32 : tail <<+ s32.stack := (popBurn_pref hpop32 hp31).2
        refine run_prepend_elim _ [pushB256 scale] ?_ run
        intro s33 hline33 run
        have frame33 := frame32.line (by line_inv) (by line_inv) (by line_inv)
          hline33
        have hp33 : scale :: tail <<+ s33.stack := by
          rcases Line.of_run_cons hline33 with ⟨v, hpush, hnil⟩
          cases hnil
          exact prefix_of_push (of_run_pushB256 hpush) hp32
        refine run_prepend_elim _ (mstoreAt accumulatorWord) ?_ run
        intro s34 hline34 run
        obtain ⟨hp34, frame34⟩ := frame33.mstoreAt hp33 hline34
        refine of_run_halveExponent hlookup hkNat (by rw [if_neg heven]) ?_
          (scratch_setScratch_self _ _ _) ?_ ?_ ?_ ?_ frame34 hp34 run
        · rw [scratch_setScratch_of_disjoint _ _ exponent_accumulator,
            scratch_setScratch_of_disjoint _ _ exponent_base,
            scratch_setScratch_self]
        · rw [scratch_setScratch_of_disjoint _ _ base_accumulator,
            scratch_setScratch_self]
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
      · -- odd exponent: seed the accumulator with the rate
        have hodd : (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat % 2 = 1 := by
          by_contra heven
          exact hnz'' ((popBurn_pref hpop32 hp31).1.trans (hparity.2 heven))
        have frame32 := (frame31.of_popBurn hpop32).of_burn hburn32
        have hp32 : tail <<+ s32'.stack := by
          rw [← hburn32.stack]
          exact (popBurn_pref hpop32 hp31).2
        refine run_prepend_elim _ [pushB256 rate] ?_ run
        intro s33 hline33 run
        have frame33 := frame32.line (by line_inv) (by line_inv) (by line_inv)
          hline33
        have hp33 : rate :: tail <<+ s33.stack := by
          rcases Line.of_run_cons hline33 with ⟨v, hpush, hnil⟩
          cases hnil
          exact prefix_of_push (of_run_pushB256 hpush) hp32
        refine run_prepend_elim _ (mstoreAt accumulatorWord) ?_ run
        intro s34 hline34 run
        obtain ⟨hp34, frame34⟩ := frame33.mstoreAt hp33 hline34
        refine of_run_halveExponent hlookup hkNat (by rw [if_pos hodd]) ?_
          (scratch_setScratch_self _ _ _) ?_ ?_ ?_ ?_ frame34 hp34 run
        · rw [scratch_setScratch_of_disjoint _ _ exponent_accumulator,
            scratch_setScratch_of_disjoint _ _ exponent_base,
            scratch_setScratch_self]
        · rw [scratch_setScratch_of_disjoint _ _ base_accumulator,
            scratch_setScratch_self]
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
      refine run_prepend_elim _ [pushB256 scale] ?_ run
      intro s30 hline30 run
      have frame30 := frame29.line (by line_inv) (by line_inv) (by line_inv)
        hline30
      have hp30 : scale :: tail <<+ s30.stack := by
        rcases Line.of_run_cons hline30 with ⟨v, hpush, hnil⟩
        cases hnil
        exact prefix_of_push (of_run_pushB256 hpush) hp29
      refine run_prepend_elim _ (mstoreAt accumulatorWord) ?_ run
      intro s31 hline31 run
      obtain ⟨hp31, frame31⟩ := frame30.mstoreAt hp30 hline31
      refine ⟨s31, _, ?_, ?_, ?_, ?_, ?_, frame31, hp31, run⟩
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
  obtain ⟨tm, imageM, hguards, haccM, hchiM, hnowM, hmachineM, frameM, hpM,
    run⟩ := key
  obtain ⟨t, hnofm, hcap, hpt, framet, run⟩ :=
    of_run_composeFresh hlookup frameM hpM run
  rw [haccM, hchiM] at hnofm hcap framet
  refine ⟨t, _, hlower, hupper, hclock, helapsed, hguards, hnofm, hcap,
    scratch_setScratch_self _ _ _, ?_,
    hmachineM.trans (MachineOnly.freshChi imageM _), framet, hpt, run⟩
  rw [scratch_setScratch_of_disjoint _ _ now_freshChi, hnowM]

/-! ## The route dispatcher

The machine returns through a finite five-way tag test.  A successful run
reaches exactly the endpoint tail its entry body staged; a tag outside the
five has no successful run, because the last test's rejecting arm is the
inline reverter. -/

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
  refine run_prepend_elim _ [dup 0, pushB256 c, eq] ?_ run
  intro s1 hline1 run
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
  rcases of_run_branch run with
    ⟨s2, hpop, run⟩ | ⟨w, s2, s3, hnz, hpop, hburn, run⟩
  · refine Or.inr ⟨s2, frame1.of_popBurn hpop, ?_, run⟩
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
    refine run_prepend_elim _ [pop] ?_ run
    intro s4 hline4 run
    have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
    exact ⟨s4, frame4, prefix_of_pop (of_run_pop (of_run_single hline4)) hp3,
      run⟩

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
  obtain ⟨s0, hburn0, run⟩ := of_run_call_of_lookup hlookup.freshRoute run
  have frame0 := frame.of_burn hburn0
  have hp0 : tail <<+ s0.stack := hburn0.stack ▸ hp
  unfold Drip.freshRoute at run
  refine run_prepend_elim _ (loadWord routeWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame0.loadWord hp0 hline1
  rcases of_run_routeTest frame1 hp1 run with
    ⟨htag, t, framet, hpt, run⟩ | ⟨s2, frame2, hp2, run⟩
  · exact ⟨t, framet, hpt, Or.inl ⟨htag, run⟩⟩
  rcases of_run_routeTest frame2 hp2 run with
    ⟨htag, t, framet, hpt, run⟩ | ⟨s3, frame3, hp3, run⟩
  · exact ⟨t, framet, hpt, Or.inr (Or.inl ⟨htag, run⟩)⟩
  rcases of_run_routeTest frame3 hp3 run with
    ⟨htag, t, framet, hpt, run⟩ | ⟨s4, frame4, hp4, run⟩
  · exact ⟨t, framet, hpt, Or.inr (Or.inr (Or.inl ⟨htag, run⟩))⟩
  rcases of_run_routeTest frame4 hp4 run with
    ⟨htag, t, framet, hpt, run⟩ | ⟨s5, frame5, hp5, run⟩
  · exact ⟨t, framet, hpt, Or.inr (Or.inr (Or.inr (Or.inl ⟨htag, run⟩)))⟩
  -- the last test has no `pop`: the tag word is consumed by the comparison
  refine run_prepend_elim _ [pushB256 routeJoin, eq] ?_ run
  intro s6 hline6 run
  have frame6 := frame5.line (by line_inv) (by line_inv) (by line_inv) hline6
  have hp6 : (routeJoin =? scratch image routeWord) :: tail <<+ s6.stack := by
    rcases Line.of_run_cons hline6 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, heq, hnil⟩
    cases hnil
    exact prefix_of_eq heq (prefix_of_push (of_run_pushB256 hpush) hp5)
  rcases of_run_branch run with
    ⟨s7, hpop, run⟩ | ⟨w, s7, s8, hnz, hpop, hburn, run⟩
  · exact absurd run not_run_revert
  · have htag : scratch image routeWord = routeJoin := by
      by_contra hne
      rw [B256.eqCheck, if_neg (fun h => hne h.symm)] at hp6
      exact absurd (popBurn_pref hpop hp6).1 hnz
    refine ⟨s8, (frame6.of_popBurn hpop).of_burn hburn, ?_,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨htag, run⟩)))⟩
    rw [← hburn.stack]
    exact (popBurn_pref hpop hp6).2

/-! ## The `drip()` tail

`afterDrip` is the smallest of the five endpoint tails and the one that makes
the machine's output visible: commit the fresh index and the timestamp to
their frozen scalar slots, in that order, and return the new index. -/

private theorem getStor_of_state {s t : Devm} (h : s.state = t.state) :
    Devm.getStor s = Devm.getStor t := by
  funext a
  unfold Devm.getStor Devm.getAcct
  rw [h]

theorem of_run_afterDrip {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterDrip r) :
    Devm.getStor r e.currentTarget =
        ((Devm.getStor entry e.currentTarget).set chiSlot
          (scratch image freshChiWord)).set rhoSlot (scratch image nowWord) ∧
      ReturnsWord (scratch image freshChiWord) r := by
  unfold Drip.afterDrip Drip.commitFresh at run
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, hwf1, hreads1, hst1⟩ :=
    of_run_loadWordAt_image (word := freshChiWord)
      (value := scratch image freshChiWord) hp frame.wf frame.reads rfl hline1
  refine run_prepend_elim _ [pushB256 chiSlot, sstore] ?_ run
  intro s2 hline2 run
  rcases Line.of_run_cons hline2 with ⟨u1, hpush1, hrest⟩
  rcases Line.of_run_cons hrest with ⟨u2, hstore1, hnil⟩
  cases hnil
  have hpu1 : chiSlot :: scratch image freshChiWord :: tail <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp1
  have hstor2 : Devm.getStor s2 e.currentTarget =
      (Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord) := by
    rw [sstore_getStor_set hstore1 hpu1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush1).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst1) e.currentTarget,
      ← congrFun (getStor_of_state frame.state) e.currentTarget]
  have hp2 : tail <<+ s2.stack := prefix_of_sstore hstore1 hpu1
  have hmem2 : s1.memory = s2.memory :=
    Line.of_inv Devm.memory (by line_inv) hline2
  have hwf2 : Mem.Wf s2.memory := by rw [← hmem2]; exact hwf1
  have hreads2 : Mem.Reads s2.memory image := by rw [← hmem2]; exact hreads1
  refine run_prepend_elim _ (loadWord nowWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, hwf3, hreads3, hst3⟩ :=
    of_run_loadWordAt_image (word := nowWord)
      (value := scratch image nowWord) hp2 hwf2 hreads2 rfl hline3
  refine run_prepend_elim _ [pushB256 rhoSlot, sstore] ?_ run
  intro s4 hline4 run
  rcases Line.of_run_cons hline4 with ⟨v1, hpush2, hrest⟩
  rcases Line.of_run_cons hrest with ⟨v2, hstore2, hnil⟩
  cases hnil
  have hpv1 : rhoSlot :: scratch image nowWord :: tail <<+ v1.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp3
  have hstor4 : Devm.getStor s4 e.currentTarget =
      ((Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord)).set rhoSlot (scratch image nowWord) := by
    rw [sstore_getStor_set hstore2 hpv1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush2).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst3) e.currentTarget, hstor2]
  have hp4 : tail <<+ s4.stack := prefix_of_sstore hstore2 hpv1
  have hmem4 : s3.memory = s4.memory :=
    Line.of_inv Devm.memory (by line_inv) hline4
  have hwf4 : Mem.Wf s4.memory := by rw [← hmem4]; exact hwf3
  have hreads4 : Mem.Reads s4.memory image := by rw [← hmem4]; exact hreads3
  -- the return tail leaves storage alone and returns the fresh index
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, hwf5, hreads5, hst5⟩ :=
    of_run_loadWordAt_image (word := freshChiWord)
      (value := scratch image freshChiWord) hp4 hwf4 hreads4 rfl hline5
  refine ⟨?_, (returnsWord_of_storeReturn hp5 run).1⟩
  rw [← congrFun
      (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run) e.currentTarget,
    ← congrFun (getStor_of_state hst5) e.currentTarget, hstor4]

/-! ## `drip()`, end to end at source level

The first complete DRIP endpoint: a successful permissionless `drip()` crosses
the four frozen guards, computes the exact Jaune-certified factor under
Jaune's own word-safety bundle, writes the composed index and the block
timestamp to their frozen scalar slots in that order, and returns the new
index. -/

theorem of_run_drip {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.drip r) :
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
      Devm.getStor r e.currentTarget =
        ((Devm.getStor entry e.currentTarget).set chiSlot
            ((B256.rpow scale half rate
                  (e.benvStat.time -
                    Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
                Devm.getStorVal entry e.currentTarget chiSlot) / scale)).set
          rhoSlot e.benvStat.time ∧
      ReturnsWord
        ((B256.rpow scale half rate
              (e.benvStat.time -
                Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale) r := by
  unfold Drip.drip Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 routeDrip] ?_ run
  intro s1 hline1 run
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : routeDrip :: tail <<+ s1.stack := by
    rcases Line.of_run_cons hline1 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.mstoreAt hp1 hline2
  obtain ⟨t3, image3, hlower, hupper, hclock, helapsed, hguards, hnofm, hcap,
    hfresh, hnow, hmachine, frame3, hp3, run⟩ :=
    of_run_freshStart hlookup frame2 hp2 run
  have htag : scratch image3 routeWord = routeDrip := by
    rw [hmachine.1, scratch_setScratch_self]
  obtain ⟨t4, frame4, hp4, hroute⟩ := of_run_freshRoute hlookup frame3 hp3 run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact absurd (htag.symm.trans htagA) (by decide +kernel)
  · exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · exact absurd (htag.symm.trans htagU) (by decide +kernel)
  · obtain ⟨hstor, hret⟩ := of_run_afterDrip frame4 hp4 run
    rw [hfresh, hnow] at hstor
    rw [hfresh] at hret
    exact ⟨hlower, hupper, hclock, helapsed, hguards, hnofm, hcap, hstor, hret⟩
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

/-! ## The two conversion views

Both views are arithmetic-only previews at the same realized index a mutation
would use.  They perform the machine's whole guard route and then one exact
surface floor; neither writes storage, so a successful view leaves the
contract's rows exactly as it found them. -/

theorem of_run_afterConvertToAssets {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterConvertToAssets r) :
    Devm.getStor s = Devm.getStor r ∧
      ReturnsWord
        ((scratch image freshChiWord * scratch image argumentWord) / scale) r := by
  refine ⟨Func.of_inv Devm.getStor Devm.getStor (by func_inv) run, ?_⟩
  unfold Drip.afterConvertToAssets at run
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.loadWord hp1 hline2
  refine run_prepend_elim _ [mul, pushB256 scale, swap 0, div] ?_ run
  intro s3 hline3 run
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : ((scratch image freshChiWord * scratch image argumentWord) /
      scale) :: tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u1, hmul, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u4, hdiv, hnil⟩
    cases hnil
    have h1 := prefix_of_mul hmul hp2
    have h2 := prefix_of_push (of_run_pushB256 hpush) h1
    have h3 : (scratch image freshChiWord * scratch image argumentWord) ::
        scale :: tail <<+ u3.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scale :: (scratch image freshChiWord *
              scratch image argumentWord) :: tail)
            ((scratch image freshChiWord * scratch image argumentWord) ::
              scale :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) h2
    exact prefix_of_div hdiv h3
  refine run_prepend_elim _ (mstoreAt resultWord) ?_ run
  intro s4 hline4 run
  obtain ⟨hp4, frame4⟩ := frame3.mstoreAt hp3 hline4
  refine run_prepend_elim _ (loadWord resultWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, frame5⟩ := frame4.loadWord hp4 hline5
  rw [scratch_setScratch_self] at hp5
  exact (returnsWord_of_storeReturn hp5 run).1

theorem of_run_afterConvertToUnits {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterConvertToUnits r) :
    Devm.getStor s = Devm.getStor r ∧
      ReturnsWord
        ((scale * scratch image argumentWord) /
          scratch image freshChiWord) r := by
  refine ⟨Func.of_inv Devm.getStor Devm.getStor (by func_inv) run, ?_⟩
  unfold Drip.afterConvertToUnits at run
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
  refine run_prepend_elim _ [pushB256 scale, mul] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : (scale * scratch image argumentWord) :: tail <<+ s2.stack := by
    rcases Line.of_run_cons hline2 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hmul, hnil⟩
    cases hnil
    exact prefix_of_mul hmul (prefix_of_push (of_run_pushB256 hpush) hp1)
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.loadWord hp2 hline3
  refine run_prepend_elim _ [swap 0, div] ?_ run
  intro s4 hline4 run
  have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
  have hp4 : ((scale * scratch image argumentWord) /
      scratch image freshChiWord) :: tail <<+ s4.stack := by
    rcases Line.of_run_cons hline4 with ⟨u1, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdiv, hnil⟩
    cases hnil
    have h1 : (scale * scratch image argumentWord) ::
        scratch image freshChiWord :: tail <<+ u1.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scratch image freshChiWord ::
              (scale * scratch image argumentWord) :: tail)
            ((scale * scratch image argumentWord) ::
              scratch image freshChiWord :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) hp3
    exact prefix_of_div hdiv h1
  refine run_prepend_elim _ (mstoreAt resultWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, frame5⟩ := frame4.mstoreAt hp4 hline5
  refine run_prepend_elim _ (loadWord resultWord) ?_ run
  intro s6 hline6 run
  obtain ⟨hp6, frame6⟩ := frame5.loadWord hp5 hline6
  rw [scratch_setScratch_self] at hp6
  exact (returnsWord_of_storeReturn hp6 run).1

/-! ## The two views, end to end at source level -/

private theorem of_run_viewEntry {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    {cap route : B256}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s
      (arg 0 +++ dup 0 ::: mstoreAt argumentWord +++ pushB256 cap ::: lt :::
        (.revert <?> (stageRoute route +++ Func.call freshStartSlot))) r) :
    ∃ t image',
      ¬ cap < Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      scratch image' routeWord = route ∧
      scratch image' argumentWord = Sevm.dataWord e (32 * 0 + 4) ∧
      scratch image' freshChiWord =
        (B256.rpow scale half rate
              (e.benvStat.time -
                Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
      Frame image' entry t ∧ (tail <<+ t.stack) ∧
      Func.Run fs e t (.call freshRouteSlot) r := by
  refine run_prepend_elim _ (arg 0) ?_ run
  intro s1 hline1 run
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : Sevm.dataWord e (32 * 0 + 4) :: tail <<+ s1.stack :=
    prefix_of_cdl_val hp hline1
  refine run_prepend_elim _ [dup 0] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : Sevm.dataWord e (32 * 0 + 4) :: Sevm.dataWord e (32 * 0 + 4) ::
      tail <<+ s2.stack :=
    prefix_of_dup_val (of_run_single hline2) (by show_nth) hp1
  refine run_prepend_elim _ (mstoreAt argumentWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.mstoreAt hp2 hline3
  refine run_prepend_elim _ [pushB256 cap, lt] ?_ run
  intro s4 hline4 run
  have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
  have hp4 : (cap <? Sevm.dataWord e (32 * 0 + 4)) :: tail <<+ s4.stack := by
    rcases Line.of_run_cons hline4 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp3)
  obtain ⟨hflagCap, s5, hp5, hpop5, run⟩ := of_run_guard hp4 run
  have frame5 := frame4.of_popBurn hpop5
  have hcap := not_lt_of_ltCheck_eq_zero hflagCap
  unfold Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 route] ?_ run
  intro s6 hline6 run
  have frame6 := frame5.line (by line_inv) (by line_inv) (by line_inv) hline6
  have hp6 : route :: tail <<+ s6.stack := by
    rcases Line.of_run_cons hline6 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp5
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s7 hline7 run
  obtain ⟨hp7, frame7⟩ := frame6.mstoreAt hp6 hline7
  obtain ⟨t8, image8, hlower, hupper, hclock, helapsed, hguards, hnofm, hcapChi,
    hfresh, hnow, hmachine, frame8, hp8, run⟩ :=
    of_run_freshStart hlookup frame7 hp7 run
  refine ⟨t8, image8, hcap, hlower, hupper, hclock, helapsed, hguards, ?_, ?_,
    hfresh, frame8, hp8, run⟩
  · rw [hmachine.1, scratch_setScratch_self]
  · rw [hmachine.2.1,
      scratch_setScratch_of_disjoint _ _ argument_route,
      scratch_setScratch_self]

theorem of_run_convertToAssets {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.convertToAssets r) :
    ¬ maxUnits < Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      Devm.getStor entry = Devm.getStor r ∧
      ReturnsWord
        (((B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale) *
          Sevm.dataWord e (32 * 0 + 4) / scale) r := by
  unfold Drip.convertToAssets at run
  obtain ⟨t, image', hcap, hlower, hupper, hclock, helapsed, hguards, htag,
    harg, hfresh, framet, hpt, run⟩ := of_run_viewEntry hlookup frame hp run
  obtain ⟨t2, frame2, hp2, hroute⟩ := of_run_freshRoute hlookup framet hpt run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · obtain ⟨hstor, hret⟩ := of_run_afterConvertToAssets frame2 hp2 run
    rw [hfresh, harg] at hret
    exact ⟨hcap, hlower, hupper, hclock, helapsed, hguards,
      (getStor_of_state frame2.state).trans hstor, hret⟩
  · exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · exact absurd (htag.symm.trans htagU) (by decide +kernel)
  · exact absurd (htag.symm.trans htagD) (by decide +kernel)
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

theorem of_run_convertToUnits {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.convertToUnits r) :
    ¬ maxAsset < Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      Devm.getStor entry = Devm.getStor r ∧
      ReturnsWord
        (scale * Sevm.dataWord e (32 * 0 + 4) /
          ((B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale)) r := by
  unfold Drip.convertToUnits at run
  obtain ⟨t, image', hcap, hlower, hupper, hclock, helapsed, hguards, htag,
    harg, hfresh, framet, hpt, run⟩ := of_run_viewEntry hlookup frame hp run
  obtain ⟨t2, frame2, hp2, hroute⟩ := of_run_freshRoute hlookup framet hpt run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact absurd (htag.symm.trans htagA) (by decide +kernel)
  · exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · obtain ⟨hstor, hret⟩ := of_run_afterConvertToUnits frame2 hp2 run
    rw [hfresh, harg] at hret
    exact ⟨hcap, hlower, hupper, hclock, helapsed, hguards,
      (getStor_of_state frame2.state).trans hstor, hret⟩
  · exact absurd (htag.symm.trans htagD) (by decide +kernel)
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

/-! ## The `join()` tail

`afterJoin` credits `⌊a·S / chi⁺⌋` normalized units, checks the caller row and
the total against their frozen caps *before* any persistent write, and then
writes in the frozen order: the fresh index, the timestamp, the caller's row,
and the total.  The caller's row is keyed by the raw address word, which
`Blanc/DripCore.lean` separately proves cannot alias a scalar slot. -/

theorem of_run_afterJoin {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterJoin r) :
    ¬ maxUnits < scratch image rowWord +
        (scale * scratch image argumentWord / scratch image freshChiWord) ∧
      ¬ maxPie <
        (scale * scratch image argumentWord / scratch image freshChiWord) +
          scratch image totalWord ∧
      Devm.getStor r e.currentTarget =
        ((((Devm.getStor entry e.currentTarget).set chiSlot
              (scratch image freshChiWord)).set rhoSlot
            (scratch image nowWord)).set e.caller.toB256
            (scratch image rowWord +
              (scale * scratch image argumentWord /
                scratch image freshChiWord))).set totalUnitsSlot
          ((scale * scratch image argumentWord / scratch image freshChiWord) +
            scratch image totalWord) ∧
      ReturnsWord
        (scale * scratch image argumentWord / scratch image freshChiWord) r := by
  unfold Drip.afterJoin at run
  -- the credited unit count
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
  refine run_prepend_elim _ [pushB256 scale, mul] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : (scale * scratch image argumentWord) :: tail <<+ s2.stack := by
    rcases Line.of_run_cons hline2 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hmul, hnil⟩
    cases hnil
    exact prefix_of_mul hmul (prefix_of_push (of_run_pushB256 hpush) hp1)
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.loadWord hp2 hline3
  refine run_prepend_elim _ [swap 0, div, dup 0] ?_ run
  intro s4 hline4 run
  have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
  have hp4 : (scale * scratch image argumentWord /
        scratch image freshChiWord) ::
      (scale * scratch image argumentWord / scratch image freshChiWord) ::
      tail <<+ s4.stack := by
    rcases Line.of_run_cons hline4 with ⟨u1, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdiv, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    have h1 : (scale * scratch image argumentWord) ::
        scratch image freshChiWord :: tail <<+ u1.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scratch image freshChiWord ::
              (scale * scratch image argumentWord) :: tail)
            ((scale * scratch image argumentWord) ::
              scratch image freshChiWord :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) hp3
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_div hdiv h1)
  refine run_prepend_elim _ (mstoreAt resultWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, frame5⟩ := frame4.mstoreAt hp4 hline5
  -- the caller row cap
  refine run_prepend_elim _ (loadWord rowWord) ?_ run
  intro s6 hline6 run
  obtain ⟨hp6, frame6⟩ := frame5.loadWord hp5 hline6
  rw [scratch_setScratch_of_disjoint _ _ row_result] at hp6
  refine run_prepend_elim _ [add, dup 0] ?_ run
  intro s7 hline7 run
  have frame7 := frame6.line (by line_inv) (by line_inv) (by line_inv) hline7
  have hp7 : (scratch image rowWord +
        (scale * scratch image argumentWord / scratch image freshChiWord)) ::
      (scratch image rowWord +
        (scale * scratch image argumentWord / scratch image freshChiWord)) ::
      tail <<+ s7.stack := by
    rcases Line.of_run_cons hline7 with ⟨u1, hadd, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_add hadd hp6)
  refine run_prepend_elim _ (mstoreAt newRowWord) ?_ run
  intro s8 hline8 run
  obtain ⟨hp8, frame8⟩ := frame7.mstoreAt hp7 hline8
  refine run_prepend_elim _ [pushB256 maxUnits, lt] ?_ run
  intro s9 hline9 run
  have frame9 := frame8.line (by line_inv) (by line_inv) (by line_inv) hline9
  have hp9 : (maxUnits <? (scratch image rowWord +
      (scale * scratch image argumentWord / scratch image freshChiWord))) ::
      tail <<+ s9.stack := by
    rcases Line.of_run_cons hline9 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp8)
  obtain ⟨hflagRow, s10, hp10, hpop10, run⟩ := of_run_guard hp9 run
  have frame10 := frame9.of_popBurn hpop10
  have hrowCap := not_lt_of_ltCheck_eq_zero hflagRow
  -- the total cap
  refine run_prepend_elim _ (loadWord totalWord) ?_ run
  intro s11 hline11 run
  obtain ⟨hp11, frame11⟩ := frame10.loadWord hp10 hline11
  rw [scratch_setScratch_of_disjoint _ _ total_newRow,
    scratch_setScratch_of_disjoint _ _ total_result] at hp11
  refine run_prepend_elim _ (loadWord resultWord) ?_ run
  intro s12 hline12 run
  obtain ⟨hp12, frame12⟩ := frame11.loadWord hp11 hline12
  rw [scratch_setScratch_of_disjoint _ _ result_newRow,
    scratch_setScratch_self] at hp12
  refine run_prepend_elim _ [add, dup 0] ?_ run
  intro s13 hline13 run
  have frame13 := frame12.line (by line_inv) (by line_inv) (by line_inv) hline13
  have hp13 : ((scale * scratch image argumentWord /
        scratch image freshChiWord) + scratch image totalWord) ::
      ((scale * scratch image argumentWord / scratch image freshChiWord) +
        scratch image totalWord) :: tail <<+ s13.stack := by
    rcases Line.of_run_cons hline13 with ⟨u1, hadd, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_add hadd hp12)
  refine run_prepend_elim _ (mstoreAt newTotalWord) ?_ run
  intro s14 hline14 run
  obtain ⟨hp14, frame14⟩ := frame13.mstoreAt hp13 hline14
  refine run_prepend_elim _ [pushB256 maxPie, lt] ?_ run
  intro s15 hline15 run
  have frame15 := frame14.line (by line_inv) (by line_inv) (by line_inv) hline15
  have hp15 : (maxPie <? ((scale * scratch image argumentWord /
      scratch image freshChiWord) + scratch image totalWord)) ::
      tail <<+ s15.stack := by
    rcases Line.of_run_cons hline15 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp14)
  obtain ⟨hflagTotal, s16, hp16, hpop16, run⟩ := of_run_guard hp15 run
  have frame16 := frame15.of_popBurn hpop16
  have htotalCap := not_lt_of_ltCheck_eq_zero hflagTotal
  -- the frozen write order: index, clock, caller row, total
  unfold Drip.commitFresh at run
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s17 hline17 run
  obtain ⟨hp17, hwf17, hreads17, hst17⟩ :=
    of_run_loadWordAt_image (word := freshChiWord)
      (value := scratch image freshChiWord) hp16 frame16.wf frame16.reads
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ freshChi_newTotal,
            scratch_setScratch_of_disjoint _ _ freshChi_newRow,
            scratch_setScratch_of_disjoint _ _ freshChi_result]) hline17
  refine run_prepend_elim _ [pushB256 chiSlot, sstore] ?_ run
  intro s18 hline18 run
  rcases Line.of_run_cons hline18 with ⟨u1, hpush1, hrest⟩
  rcases Line.of_run_cons hrest with ⟨u2, hstore1, hnil⟩
  cases hnil
  have hpu1 : chiSlot :: scratch image freshChiWord :: tail <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp17
  have hstor18 : Devm.getStor s18 e.currentTarget =
      (Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord) := by
    rw [sstore_getStor_set hstore1 hpu1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush1).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst17) e.currentTarget,
      ← congrFun (getStor_of_state frame16.state) e.currentTarget]
  have hp18 : tail <<+ s18.stack := prefix_of_sstore hstore1 hpu1
  have hmem18 : s17.memory = s18.memory :=
    Line.of_inv Devm.memory (by line_inv) hline18
  refine run_prepend_elim _ (loadWord nowWord) ?_ run
  intro s19 hline19 run
  obtain ⟨hp19, hwf19, hreads19, hst19⟩ :=
    of_run_loadWordAt_image (word := nowWord)
      (value := scratch image nowWord) hp18 (hmem18 ▸ hwf17) (hmem18 ▸ hreads17)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ now_newTotal,
            scratch_setScratch_of_disjoint _ _ now_newRow,
            scratch_setScratch_of_disjoint _ _ now_result]) hline19
  refine run_prepend_elim _ [pushB256 rhoSlot, sstore] ?_ run
  intro s20 hline20 run
  rcases Line.of_run_cons hline20 with ⟨v1, hpush2, hrest⟩
  rcases Line.of_run_cons hrest with ⟨v2, hstore2, hnil⟩
  cases hnil
  have hpv1 : rhoSlot :: scratch image nowWord :: tail <<+ v1.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp19
  have hstor20 : Devm.getStor s20 e.currentTarget =
      ((Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord)).set rhoSlot (scratch image nowWord) := by
    rw [sstore_getStor_set hstore2 hpv1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush2).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst19) e.currentTarget, hstor18]
  have hp20 : tail <<+ s20.stack := prefix_of_sstore hstore2 hpv1
  have hmem20 : s19.memory = s20.memory :=
    Line.of_inv Devm.memory (by line_inv) hline20
  refine run_prepend_elim _ (loadWord newRowWord) ?_ run
  intro s21 hline21 run
  obtain ⟨hp21, hwf21, hreads21, hst21⟩ :=
    of_run_loadWordAt_image (word := newRowWord)
      (value := scratch image rowWord +
        (scale * scratch image argumentWord / scratch image freshChiWord))
      hp20 (hmem20 ▸ hwf19) (hmem20 ▸ hreads19)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ newRow_newTotal,
            scratch_setScratch_self]) hline21
  refine run_prepend_elim _ [caller, sstore] ?_ run
  intro s22 hline22 run
  rcases Line.of_run_cons hline22 with ⟨w1, hcaller, hrest⟩
  rcases Line.of_run_cons hrest with ⟨w2, hstore3, hnil⟩
  cases hnil
  have hpw1 : e.caller.toB256 :: (scratch image rowWord +
      (scale * scratch image argumentWord / scratch image freshChiWord)) ::
      tail <<+ w1.stack := prefix_of_push (of_run_caller hcaller) hp21
  have hstor22 : Devm.getStor s22 e.currentTarget =
      (((Devm.getStor entry e.currentTarget).set chiSlot
          (scratch image freshChiWord)).set rhoSlot
        (scratch image nowWord)).set e.caller.toB256
        (scratch image rowWord +
          (scale * scratch image argumentWord /
            scratch image freshChiWord)) := by
    rw [sstore_getStor_set hstore3 hpw1,
      ← congrFun (getStor_of_state (of_run_caller hcaller).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst21) e.currentTarget, hstor20]
  have hp22 : tail <<+ s22.stack := prefix_of_sstore hstore3 hpw1
  have hmem22 : s21.memory = s22.memory :=
    Line.of_inv Devm.memory (by line_inv) hline22
  refine run_prepend_elim _ (loadWord newTotalWord) ?_ run
  intro s23 hline23 run
  obtain ⟨hp23, hwf23, hreads23, hst23⟩ :=
    of_run_loadWordAt_image (word := newTotalWord)
      (value := (scale * scratch image argumentWord /
        scratch image freshChiWord) + scratch image totalWord)
      hp22 (hmem22 ▸ hwf21) (hmem22 ▸ hreads21)
      (by show scratch _ _ = _
          rw [scratch_setScratch_self]) hline23
  refine run_prepend_elim _ [pushB256 totalUnitsSlot, sstore] ?_ run
  intro s24 hline24 run
  rcases Line.of_run_cons hline24 with ⟨x1, hpush4, hrest⟩
  rcases Line.of_run_cons hrest with ⟨x2, hstore4, hnil⟩
  cases hnil
  have hpx1 : totalUnitsSlot :: ((scale * scratch image argumentWord /
      scratch image freshChiWord) + scratch image totalWord) :: tail <<+
      x1.stack := prefix_of_push (of_run_pushB256 hpush4) hp23
  have hstor24 : Devm.getStor s24 e.currentTarget =
      ((((Devm.getStor entry e.currentTarget).set chiSlot
            (scratch image freshChiWord)).set rhoSlot
          (scratch image nowWord)).set e.caller.toB256
          (scratch image rowWord +
            (scale * scratch image argumentWord /
              scratch image freshChiWord))).set totalUnitsSlot
        ((scale * scratch image argumentWord / scratch image freshChiWord) +
          scratch image totalWord) := by
    rw [sstore_getStor_set hstore4 hpx1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush4).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst23) e.currentTarget, hstor22]
  have hp24 : tail <<+ s24.stack := prefix_of_sstore hstore4 hpx1
  have hmem24 : s23.memory = s24.memory :=
    Line.of_inv Devm.memory (by line_inv) hline24
  refine run_prepend_elim _ (loadWord resultWord) ?_ run
  intro s25 hline25 run
  obtain ⟨hp25, hwf25, hreads25, hst25⟩ :=
    of_run_loadWordAt_image (word := resultWord)
      (value := scale * scratch image argumentWord / scratch image freshChiWord)
      hp24 (hmem24 ▸ hwf23) (hmem24 ▸ hreads23)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ result_newTotal,
            scratch_setScratch_of_disjoint _ _ result_newRow,
            scratch_setScratch_self]) hline25
  refine ⟨hrowCap, htotalCap, ?_, (returnsWord_of_storeReturn hp25 run).1⟩
  rw [← congrFun
      (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run) e.currentTarget,
    ← congrFun (getStor_of_state hst25) e.currentTarget, hstor24]

/-! ## `join()`, end to end at source level -/

theorem of_run_join {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.join r) :
    ¬ maxAsset < e.value ∧
      ¬ maxUnits < Devm.getStorVal entry e.currentTarget e.caller.toB256 ∧
      ¬ maxPie < Devm.getStorVal entry e.currentTarget totalUnitsSlot ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      ∃ freshChi units,
        freshChi =
          (B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
        units = scale * e.value / freshChi ∧
        ¬ maxUnits <
          Devm.getStorVal entry e.currentTarget e.caller.toB256 + units ∧
        ¬ maxPie <
          units + Devm.getStorVal entry e.currentTarget totalUnitsSlot ∧
        Devm.getStor r e.currentTarget =
          ((((Devm.getStor entry e.currentTarget).set chiSlot freshChi).set
              rhoSlot e.benvStat.time).set e.caller.toB256
              (Devm.getStorVal entry e.currentTarget e.caller.toB256 +
                units)).set totalUnitsSlot
            (units + Devm.getStorVal entry e.currentTarget totalUnitsSlot) ∧
        ReturnsWord units r := by
  unfold Drip.join at run
  -- the call value's surface cap
  refine run_prepend_elim _ [callvalue, dup 0] ?_ run
  intro s1 hline1 run
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : e.value :: e.value :: tail <<+ s1.stack := by
    rcases Line.of_run_cons hline1 with ⟨u1, hcv, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth)
      (prefix_of_push (of_run_callvalue hcv) hp)
  refine run_prepend_elim _ (mstoreAt argumentWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.mstoreAt hp1 hline2
  refine run_prepend_elim _ [pushB256 maxAsset, lt] ?_ run
  intro s3 hline3 run
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : (maxAsset <? e.value) :: tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp2)
  obtain ⟨hflagAsset, s4, hp4, hpop4, run⟩ := of_run_guard hp3 run
  have frame4 := frame3.of_popBurn hpop4
  have hassetCap := not_lt_of_ltCheck_eq_zero hflagAsset
  -- the caller row's surface cap
  refine run_prepend_elim _ [caller, sload, dup 0] ?_ run
  intro s5 hline5 run
  have frame5 := frame4.line (by line_inv) (by line_inv) (by line_inv) hline5
  have hp5 : Devm.getStorVal entry e.currentTarget e.caller.toB256 ::
      Devm.getStorVal entry e.currentTarget e.caller.toB256 ::
      tail <<+ s5.stack := by
    rcases Line.of_run_cons hline5 with ⟨u1, hcaller, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_caller hcaller) hp4)
    rw [hyval,
      getStorVal_of_state
        (frame4.state.trans (of_run_caller hcaller).state).symm] at hy
    exact prefix_of_dup_val hdup (by show_nth) hy
  refine run_prepend_elim _ (mstoreAt rowWord) ?_ run
  intro s6 hline6 run
  obtain ⟨hp6, frame6⟩ := frame5.mstoreAt hp5 hline6
  refine run_prepend_elim _ [pushB256 maxUnits, lt] ?_ run
  intro s7 hline7 run
  have frame7 := frame6.line (by line_inv) (by line_inv) (by line_inv) hline7
  have hp7 : (maxUnits <?
      Devm.getStorVal entry e.currentTarget e.caller.toB256) ::
      tail <<+ s7.stack := by
    rcases Line.of_run_cons hline7 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp6)
  obtain ⟨hflagRow, s8, hp8, hpop8, run⟩ := of_run_guard hp7 run
  have frame8 := frame7.of_popBurn hpop8
  have hrowCapPre := not_lt_of_ltCheck_eq_zero hflagRow
  -- the total's surface cap
  refine run_prepend_elim _ [pushB256 totalUnitsSlot, sload, dup 0] ?_ run
  intro s9 hline9 run
  have frame9 := frame8.line (by line_inv) (by line_inv) (by line_inv) hline9
  have hp9 : Devm.getStorVal entry e.currentTarget totalUnitsSlot ::
      Devm.getStorVal entry e.currentTarget totalUnitsSlot ::
      tail <<+ s9.stack := by
    rcases Line.of_run_cons hline9 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) hp8)
    rw [hyval,
      getStorVal_of_state
        (frame8.state.trans (of_run_pushB256 hpush).state).symm] at hy
    exact prefix_of_dup_val hdup (by show_nth) hy
  refine run_prepend_elim _ (mstoreAt totalWord) ?_ run
  intro s10 hline10 run
  obtain ⟨hp10, frame10⟩ := frame9.mstoreAt hp9 hline10
  refine run_prepend_elim _ [pushB256 maxPie, lt] ?_ run
  intro s11 hline11 run
  have frame11 := frame10.line (by line_inv) (by line_inv) (by line_inv) hline11
  have hp11 : (maxPie <?
      Devm.getStorVal entry e.currentTarget totalUnitsSlot) ::
      tail <<+ s11.stack := by
    rcases Line.of_run_cons hline11 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp10)
  obtain ⟨hflagTotal, s12, hp12, hpop12, run⟩ := of_run_guard hp11 run
  have frame12 := frame11.of_popBurn hpop12
  have htotalCapPre := not_lt_of_ltCheck_eq_zero hflagTotal
  -- stage the route and enter the machine
  unfold Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 routeJoin] ?_ run
  intro s13 hline13 run
  have frame13 := frame12.line (by line_inv) (by line_inv) (by line_inv) hline13
  have hp13 : routeJoin :: tail <<+ s13.stack := by
    rcases Line.of_run_cons hline13 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp12
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s14 hline14 run
  obtain ⟨hp14, frame14⟩ := frame13.mstoreAt hp13 hline14
  obtain ⟨t15, image15, hlower, hupper, hclock, helapsed, hguards, hnofm,
    hcapChi, hfresh, hnow, hmachine, frame15, hp15, run⟩ :=
    of_run_freshStart hlookup frame14 hp14 run
  have htag : scratch image15 routeWord = routeJoin := by
    rw [hmachine.1, scratch_setScratch_self]
  have harg : scratch image15 argumentWord = e.value := by
    rw [hmachine.2.1,
      scratch_setScratch_of_disjoint _ _ argument_route,
      scratch_setScratch_of_disjoint _ _ argument_total,
      scratch_setScratch_of_disjoint _ _ argument_row,
      scratch_setScratch_self]
  have hrow : scratch image15 rowWord =
      Devm.getStorVal entry e.currentTarget e.caller.toB256 := by
    rw [hmachine.2.2.1,
      scratch_setScratch_of_disjoint _ _ row_route,
      scratch_setScratch_of_disjoint _ _ row_total,
      scratch_setScratch_self]
  have htotal : scratch image15 totalWord =
      Devm.getStorVal entry e.currentTarget totalUnitsSlot := by
    rw [hmachine.2.2.2,
      scratch_setScratch_of_disjoint _ _ total_route,
      scratch_setScratch_self]
  obtain ⟨t16, frame16, hp16, hroute⟩ := of_run_freshRoute hlookup frame15 hp15 run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact absurd (htag.symm.trans htagA) (by decide +kernel)
  · exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · exact absurd (htag.symm.trans htagU) (by decide +kernel)
  · exact absurd (htag.symm.trans htagD) (by decide +kernel)
  · obtain ⟨hrowCap, htotalCap, hstor, hret⟩ :=
      of_run_afterJoin frame16 hp16 run
    simp only [harg, hrow, htotal, hfresh, hnow] at hrowCap htotalCap hstor hret
    refine ⟨hassetCap, hrowCapPre, htotalCapPre, hlower, hupper, hclock,
      helapsed, hguards, _, _, rfl, rfl, hrowCap, htotalCap, hstor, hret⟩

/-! ## `exit`'s checks-effects-interactions boundary

Every successful `exit` has *already* committed all four ledger writes — the
fresh index, the clock, the caller's debited row and the debited total — before
it reaches the outbound `CALL`.  That is the frozen memo's
checks-effects-interactions requirement, stated as a property of the walk
rather than assumed of the code. -/

theorem of_run_afterExit_settles {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterExit r) :
    ∃ t,
      Devm.getStor t e.currentTarget =
        ((((Devm.getStor entry e.currentTarget).set chiSlot
              (scratch image freshChiWord)).set rhoSlot
            (scratch image nowWord)).set e.caller.toB256
            (scratch image rowWord - scratch image argumentWord)).set
          totalUnitsSlot
          (scratch image totalWord - scratch image argumentWord) ∧
      (tail <<+ t.stack) ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (setScratch image resultWord
          ((scratch image freshChiWord * scratch image argumentWord) /
            scale)) ∧
      Func.Run fs e t
        (loadWord resultWord +++ sendToCaller +++
          (returnScratch resultWord <?> Func.revert)) r := by
  unfold Drip.afterExit Drip.commitFresh at run
  -- the payout
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.loadWord hp1 hline2
  refine run_prepend_elim _ [mul, pushB256 scale, swap 0, div] ?_ run
  intro s3 hline3 run
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : ((scratch image freshChiWord * scratch image argumentWord) /
      scale) :: tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u1, hmul, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u4, hdiv, hnil⟩
    cases hnil
    have h1 := prefix_of_mul hmul hp2
    have h2 := prefix_of_push (of_run_pushB256 hpush) h1
    have h3 : (scratch image freshChiWord * scratch image argumentWord) ::
        scale :: tail <<+ u3.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scale :: (scratch image freshChiWord *
              scratch image argumentWord) :: tail)
            ((scratch image freshChiWord * scratch image argumentWord) ::
              scale :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) h2
    exact prefix_of_div hdiv h3
  refine run_prepend_elim _ (mstoreAt resultWord) ?_ run
  intro s4 hline4 run
  obtain ⟨hp4, frame4⟩ := frame3.mstoreAt hp3 hline4
  -- the four ordered writes
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, hwf5, hreads5, hst5⟩ :=
    of_run_loadWordAt_image (word := freshChiWord)
      (value := scratch image freshChiWord) hp4 frame4.wf frame4.reads
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ freshChi_result]) hline5
  refine run_prepend_elim _ [pushB256 chiSlot, sstore] ?_ run
  intro s6 hline6 run
  rcases Line.of_run_cons hline6 with ⟨u1, hpush1, hrest⟩
  rcases Line.of_run_cons hrest with ⟨u2, hstore1, hnil⟩
  cases hnil
  have hpu1 : chiSlot :: scratch image freshChiWord :: tail <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp5
  have hstor6 : Devm.getStor s6 e.currentTarget =
      (Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord) := by
    rw [sstore_getStor_set hstore1 hpu1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush1).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst5) e.currentTarget,
      ← congrFun (getStor_of_state frame4.state) e.currentTarget]
  have hp6 : tail <<+ s6.stack := prefix_of_sstore hstore1 hpu1
  have hmem6 : s5.memory = s6.memory :=
    Line.of_inv Devm.memory (by line_inv) hline6
  refine run_prepend_elim _ (loadWord nowWord) ?_ run
  intro s7 hline7 run
  obtain ⟨hp7, hwf7, hreads7, hst7⟩ :=
    of_run_loadWordAt_image (word := nowWord)
      (value := scratch image nowWord) hp6 (hmem6 ▸ hwf5) (hmem6 ▸ hreads5)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ now_result]) hline7
  refine run_prepend_elim _ [pushB256 rhoSlot, sstore] ?_ run
  intro s8 hline8 run
  rcases Line.of_run_cons hline8 with ⟨v1, hpush2, hrest⟩
  rcases Line.of_run_cons hrest with ⟨v2, hstore2, hnil⟩
  cases hnil
  have hpv1 : rhoSlot :: scratch image nowWord :: tail <<+ v1.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp7
  have hstor8 : Devm.getStor s8 e.currentTarget =
      ((Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord)).set rhoSlot (scratch image nowWord) := by
    rw [sstore_getStor_set hstore2 hpv1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush2).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst7) e.currentTarget, hstor6]
  have hp8 : tail <<+ s8.stack := prefix_of_sstore hstore2 hpv1
  have hmem8 : s7.memory = s8.memory :=
    Line.of_inv Devm.memory (by line_inv) hline8
  -- debit the caller's row
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s9 hline9 run
  obtain ⟨hp9, hwf9, hreads9, hst9⟩ :=
    of_run_loadWordAt_image (word := argumentWord)
      (value := scratch image argumentWord) hp8 (hmem8 ▸ hwf7) (hmem8 ▸ hreads7)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ argument_result]) hline9
  refine run_prepend_elim _ (loadWord rowWord) ?_ run
  intro s10 hline10 run
  obtain ⟨hp10, hwf10, hreads10, hst10⟩ :=
    of_run_loadWordAt_image (word := rowWord)
      (value := scratch image rowWord) hp9 hwf9 hreads9
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ row_result]) hline10
  refine run_prepend_elim _ [sub, caller, sstore] ?_ run
  intro s11 hline11 run
  rcases Line.of_run_cons hline11 with ⟨w1, hsub, hrest⟩
  rcases Line.of_run_cons hrest with ⟨w2, hcaller, hrest⟩
  rcases Line.of_run_cons hrest with ⟨w3, hstore3, hnil⟩
  cases hnil
  have hpw2 : e.caller.toB256 ::
      (scratch image rowWord - scratch image argumentWord) :: tail <<+
      w2.stack :=
    prefix_of_push (of_run_caller hcaller) (prefix_of_sub hsub hp10)
  have hstor11 : Devm.getStor s11 e.currentTarget =
      (((Devm.getStor entry e.currentTarget).set chiSlot
          (scratch image freshChiWord)).set rhoSlot
        (scratch image nowWord)).set e.caller.toB256
        (scratch image rowWord - scratch image argumentWord) := by
    rw [sstore_getStor_set hstore3 hpw2,
      ← congrFun (getStor_of_state (of_run_caller hcaller).state)
        e.currentTarget,
      ← congrFun (getStor_of_state
        (Line.of_inv Devm.state (by line_inv)
          (Line.Run.cons hsub Line.Run.nil))) e.currentTarget,
      ← congrFun (getStor_of_state hst10) e.currentTarget,
      ← congrFun (getStor_of_state hst9) e.currentTarget, hstor8]
  have hp11 : tail <<+ s11.stack := prefix_of_sstore hstore3 hpw2
  have hmem11 : s10.memory = s11.memory :=
    Line.of_inv Devm.memory (by line_inv) hline11
  -- debit the total
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s12 hline12 run
  obtain ⟨hp12, hwf12, hreads12, hst12⟩ :=
    of_run_loadWordAt_image (word := argumentWord)
      (value := scratch image argumentWord) hp11 (hmem11 ▸ hwf10)
      (hmem11 ▸ hreads10)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ argument_result]) hline12
  refine run_prepend_elim _ (loadWord totalWord) ?_ run
  intro s13 hline13 run
  obtain ⟨hp13, hwf13, hreads13, hst13⟩ :=
    of_run_loadWordAt_image (word := totalWord)
      (value := scratch image totalWord) hp12 hwf12 hreads12
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ total_result]) hline13
  refine run_prepend_elim _ [sub, pushB256 totalUnitsSlot, sstore] ?_ run
  intro s14 hline14 run
  rcases Line.of_run_cons hline14 with ⟨x1, hsub2, hrest⟩
  rcases Line.of_run_cons hrest with ⟨x2, hpush4, hrest⟩
  rcases Line.of_run_cons hrest with ⟨x3, hstore4, hnil⟩
  cases hnil
  have hpx2 : totalUnitsSlot ::
      (scratch image totalWord - scratch image argumentWord) :: tail <<+
      x2.stack :=
    prefix_of_push (of_run_pushB256 hpush4) (prefix_of_sub hsub2 hp13)
  have hstor14 : Devm.getStor s14 e.currentTarget =
      ((((Devm.getStor entry e.currentTarget).set chiSlot
            (scratch image freshChiWord)).set rhoSlot
          (scratch image nowWord)).set e.caller.toB256
          (scratch image rowWord - scratch image argumentWord)).set
        totalUnitsSlot
        (scratch image totalWord - scratch image argumentWord) := by
    rw [sstore_getStor_set hstore4 hpx2,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush4).state)
        e.currentTarget,
      ← congrFun (getStor_of_state
        (Line.of_inv Devm.state (by line_inv)
          (Line.Run.cons hsub2 Line.Run.nil))) e.currentTarget,
      ← congrFun (getStor_of_state hst13) e.currentTarget,
      ← congrFun (getStor_of_state hst12) e.currentTarget, hstor11]
  have hp14 : tail <<+ s14.stack := prefix_of_sstore hstore4 hpx2
  have hmem14 : s13.memory = s14.memory :=
    Line.of_inv Devm.memory (by line_inv) hline14
  exact ⟨s14, hstor14, hp14, hmem14 ▸ hwf13, hmem14 ▸ hreads13, run⟩

/-! ## `exit(units)`, end to end at source level up to the outbound call

Every successful `exit` checks its caps *and* that the caller and the total
actually hold the units, computes the payout at the freshly accrued index, and
commits all four ledger writes before the outbound `CALL` is reached.  The
child crossing and the whole-frame rollback on a failed child are the one
remaining piece of the endpoint. -/

theorem of_run_exit_settles {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.exit r) :
    ¬ maxUnits < Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ maxUnits < Devm.getStorVal entry e.currentTarget e.caller.toB256 ∧
      ¬ maxPie < Devm.getStorVal entry e.currentTarget totalUnitsSlot ∧
      ¬ Devm.getStorVal entry e.currentTarget e.caller.toB256 <
        Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget totalUnitsSlot <
        Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      ∃ t freshChi settledImage,
        freshChi =
          (B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
        scratch settledImage resultWord =
          (freshChi * Sevm.dataWord e (32 * 0 + 4)) / scale ∧
        tail <<+ t.stack ∧
        Mem.Wf t.memory ∧
        Mem.Reads t.memory settledImage ∧
        Devm.getStor t e.currentTarget =
          ((((Devm.getStor entry e.currentTarget).set chiSlot freshChi).set
              rhoSlot e.benvStat.time).set e.caller.toB256
              (Devm.getStorVal entry e.currentTarget e.caller.toB256 -
                Sevm.dataWord e (32 * 0 + 4))).set totalUnitsSlot
            (Devm.getStorVal entry e.currentTarget totalUnitsSlot -
              Sevm.dataWord e (32 * 0 + 4)) ∧
        Func.Run fs e t
          (loadWord resultWord +++ sendToCaller +++
            (returnScratch resultWord <?> Func.revert)) r := by
  unfold Drip.exit at run
  -- the argument's surface cap
  refine run_prepend_elim _ (arg 0) ?_ run
  intro s1 hline1 run
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : Sevm.dataWord e (32 * 0 + 4) :: tail <<+ s1.stack :=
    prefix_of_cdl_val hp hline1
  refine run_prepend_elim _ [dup 0] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : Sevm.dataWord e (32 * 0 + 4) :: Sevm.dataWord e (32 * 0 + 4) ::
      tail <<+ s2.stack :=
    prefix_of_dup_val (of_run_single hline2) (by show_nth) hp1
  refine run_prepend_elim _ (mstoreAt argumentWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.mstoreAt hp2 hline3
  refine run_prepend_elim _ [pushB256 maxUnits, lt] ?_ run
  intro s4 hline4 run
  have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
  have hp4 : (maxUnits <? Sevm.dataWord e (32 * 0 + 4)) :: tail <<+ s4.stack := by
    rcases Line.of_run_cons hline4 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp3)
  obtain ⟨hflagArg, s5, hp5, hpop5, run⟩ := of_run_guard hp4 run
  have frame5 := frame4.of_popBurn hpop5
  have hargCap := not_lt_of_ltCheck_eq_zero hflagArg
  -- the caller row's surface cap
  refine run_prepend_elim _ [caller, sload, dup 0] ?_ run
  intro s6 hline6 run
  have frame6 := frame5.line (by line_inv) (by line_inv) (by line_inv) hline6
  have hp6 : Devm.getStorVal entry e.currentTarget e.caller.toB256 ::
      Devm.getStorVal entry e.currentTarget e.caller.toB256 ::
      tail <<+ s6.stack := by
    rcases Line.of_run_cons hline6 with ⟨u1, hcaller, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_caller hcaller) hp5)
    rw [hyval,
      getStorVal_of_state
        (frame5.state.trans (of_run_caller hcaller).state).symm] at hy
    exact prefix_of_dup_val hdup (by show_nth) hy
  refine run_prepend_elim _ (mstoreAt rowWord) ?_ run
  intro s7 hline7 run
  obtain ⟨hp7, frame7⟩ := frame6.mstoreAt hp6 hline7
  refine run_prepend_elim _ [pushB256 maxUnits, lt] ?_ run
  intro s8 hline8 run
  have frame8 := frame7.line (by line_inv) (by line_inv) (by line_inv) hline8
  have hp8 : (maxUnits <?
      Devm.getStorVal entry e.currentTarget e.caller.toB256) ::
      tail <<+ s8.stack := by
    rcases Line.of_run_cons hline8 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp7)
  obtain ⟨hflagRow, s9, hp9, hpop9, run⟩ := of_run_guard hp8 run
  have frame9 := frame8.of_popBurn hpop9
  have hrowCap := not_lt_of_ltCheck_eq_zero hflagRow
  -- the total's surface cap
  refine run_prepend_elim _ [pushB256 totalUnitsSlot, sload, dup 0] ?_ run
  intro s10 hline10 run
  have frame10 := frame9.line (by line_inv) (by line_inv) (by line_inv) hline10
  have hp10 : Devm.getStorVal entry e.currentTarget totalUnitsSlot ::
      Devm.getStorVal entry e.currentTarget totalUnitsSlot ::
      tail <<+ s10.stack := by
    rcases Line.of_run_cons hline10 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) hp9)
    rw [hyval,
      getStorVal_of_state
        (frame9.state.trans (of_run_pushB256 hpush).state).symm] at hy
    exact prefix_of_dup_val hdup (by show_nth) hy
  refine run_prepend_elim _ (mstoreAt totalWord) ?_ run
  intro s11 hline11 run
  obtain ⟨hp11, frame11⟩ := frame10.mstoreAt hp10 hline11
  refine run_prepend_elim _ [pushB256 maxPie, lt] ?_ run
  intro s12 hline12 run
  have frame12 := frame11.line (by line_inv) (by line_inv) (by line_inv) hline12
  have hp12 : (maxPie <?
      Devm.getStorVal entry e.currentTarget totalUnitsSlot) ::
      tail <<+ s12.stack := by
    rcases Line.of_run_cons hline12 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp11)
  obtain ⟨hflagTotal, s13, hp13, hpop13, run⟩ := of_run_guard hp12 run
  have frame13 := frame12.of_popBurn hpop13
  have htotalCap := not_lt_of_ltCheck_eq_zero hflagTotal
  -- the caller actually holds the units
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s14 hline14 run
  obtain ⟨hp14, frame14⟩ := frame13.loadWord hp13 hline14
  rw [scratch_setScratch_of_disjoint _ _ argument_total,
    scratch_setScratch_of_disjoint _ _ argument_row,
    scratch_setScratch_self] at hp14
  refine run_prepend_elim _ (loadWord rowWord) ?_ run
  intro s15 hline15 run
  obtain ⟨hp15, frame15⟩ := frame14.loadWord hp14 hline15
  rw [scratch_setScratch_of_disjoint _ _ row_total,
    scratch_setScratch_self] at hp15
  refine run_prepend_elim _ [lt] ?_ run
  intro s16 hline16 run
  have frame16 := frame15.line (by line_inv) (by line_inv) (by line_inv) hline16
  have hp16 : (Devm.getStorVal entry e.currentTarget e.caller.toB256 <?
      Sevm.dataWord e (32 * 0 + 4)) :: tail <<+ s16.stack :=
    prefix_of_lt (of_run_single hline16) hp15
  obtain ⟨hflagOwn, s17, hp17, hpop17, run⟩ := of_run_guard hp16 run
  have frame17 := frame16.of_popBurn hpop17
  have hown := not_lt_of_ltCheck_eq_zero hflagOwn
  -- the total actually holds the units
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s18 hline18 run
  obtain ⟨hp18, frame18⟩ := frame17.loadWord hp17 hline18
  rw [scratch_setScratch_of_disjoint _ _ argument_total,
    scratch_setScratch_of_disjoint _ _ argument_row,
    scratch_setScratch_self] at hp18
  refine run_prepend_elim _ (loadWord totalWord) ?_ run
  intro s19 hline19 run
  obtain ⟨hp19, frame19⟩ := frame18.loadWord hp18 hline19
  rw [scratch_setScratch_self] at hp19
  refine run_prepend_elim _ [lt] ?_ run
  intro s20 hline20 run
  have frame20 := frame19.line (by line_inv) (by line_inv) (by line_inv) hline20
  have hp20 : (Devm.getStorVal entry e.currentTarget totalUnitsSlot <?
      Sevm.dataWord e (32 * 0 + 4)) :: tail <<+ s20.stack :=
    prefix_of_lt (of_run_single hline20) hp19
  obtain ⟨hflagFund, s21, hp21, hpop21, run⟩ := of_run_guard hp20 run
  have frame21 := frame20.of_popBurn hpop21
  have hfund := not_lt_of_ltCheck_eq_zero hflagFund
  -- stage the route and enter the machine
  unfold Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 routeExit] ?_ run
  intro s22 hline22 run
  have frame22 := frame21.line (by line_inv) (by line_inv) (by line_inv) hline22
  have hp22 : routeExit :: tail <<+ s22.stack := by
    rcases Line.of_run_cons hline22 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp21
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s23 hline23 run
  obtain ⟨hp23, frame23⟩ := frame22.mstoreAt hp22 hline23
  obtain ⟨t24, image24, hlower, hupper, hclock, helapsed, hguards, hnofm,
    hcapChi, hfresh, hnow, hmachine, frame24, hp24, run⟩ :=
    of_run_freshStart hlookup frame23 hp23 run
  have htag : scratch image24 routeWord = routeExit := by
    rw [hmachine.1, scratch_setScratch_self]
  have harg : scratch image24 argumentWord = Sevm.dataWord e (32 * 0 + 4) := by
    rw [hmachine.2.1,
      scratch_setScratch_of_disjoint _ _ argument_route,
      scratch_setScratch_of_disjoint _ _ argument_total,
      scratch_setScratch_of_disjoint _ _ argument_row,
      scratch_setScratch_self]
  have hrow : scratch image24 rowWord =
      Devm.getStorVal entry e.currentTarget e.caller.toB256 := by
    rw [hmachine.2.2.1,
      scratch_setScratch_of_disjoint _ _ row_route,
      scratch_setScratch_of_disjoint _ _ row_total,
      scratch_setScratch_self]
  have htotal : scratch image24 totalWord =
      Devm.getStorVal entry e.currentTarget totalUnitsSlot := by
    rw [hmachine.2.2.2,
      scratch_setScratch_of_disjoint _ _ total_route,
      scratch_setScratch_self]
  obtain ⟨t25, frame25, hp25, hroute⟩ :=
    of_run_freshRoute hlookup frame24 hp24 run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact absurd (htag.symm.trans htagA) (by decide +kernel)
  · obtain ⟨t26, hstor, hp26, hwf26, hreads26, run⟩ :=
      of_run_afterExit_settles frame25 hp25 run
    simp only [harg, hrow, htotal, hfresh, hnow] at hstor hreads26
    exact ⟨hargCap, hrowCap, htotalCap, hown, hfund, hlower, hupper, hclock,
      helapsed, hguards, t26, _,
      setScratch image24 resultWord
        (((B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale *
            Sevm.dataWord e (32 * 0 + 4)) / scale),
      rfl, scratch_setScratch_self _ _ _, hp26, hwf26, hreads26, hstor, run⟩
  · exact absurd (htag.symm.trans htagU) (by decide +kernel)
  · exact absurd (htag.symm.trans htagD) (by decide +kernel)
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

/-! ## `exit`'s entered child and exact return

The settlement theorem above stops just before the payout word is loaded for
the outbound call.  The remaining walk matters: the call uses the recipient,
value and two empty memory windows frozen by the statement memo; a zero status
word selects `Func.revert`; and only an entered, clean child can reach the
one-word return.  The raw parent/child equalities below retain the whole-frame
rollback boundary supplied by `of_run_call_val_with_depth_frame` instead of
summarizing the call as an unexplained success flag. -/

private theorem exit_sendToCaller_frame
    {sevm : Sevm} {pre callPost : Devm} {p : B256} {xs : Stack}
    (hp : p :: xs <<+ pre.stack)
    (run : Line.Run sevm pre sendToCaller callPost) :
    ∃ callPre gasWord,
      gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs <<+
        callPre.stack ∧
      Ninst.Run sevm callPre call callPost ∧
      Devm.getStor callPre = Devm.getStor pre ∧
      Devm.getBal callPre = Devm.getBal pre ∧
      Devm.getCode callPre = Devm.getCode pre ∧
      callPre.logs = pre.logs ∧
      callPre.output = pre.output ∧
      callPre.memory = pre.memory := by
  unfold sendToCaller at run
  let callPrefix : Line := pushList [0, 0, 0, 0] ++ [swap 3, caller, gas]
  rcases of_run_append callPrefix run with ⟨callPre, hprefix, hcall⟩
  have hstorPrefix : Devm.getStor pre = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by unfold callPrefix; line_inv) hprefix
  have hbalPrefix : Devm.getBal pre = Devm.getBal callPre :=
    Line.of_inv Devm.getBal (by unfold callPrefix; line_inv) hprefix
  have hcodePrefix : Devm.getCode pre = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by unfold callPrefix; line_inv) hprefix
  have hlogsPrefix : pre.logs = callPre.logs :=
    Line.of_inv Devm.logs (by unfold callPrefix; line_inv) hprefix
  have houtPrefix : pre.output = callPre.output :=
    Line.of_inv Devm.output (by unfold callPrefix; line_inv) hprefix
  have hmemPrefix : pre.memory = callPre.memory :=
    Line.of_inv Devm.memory (by unfold callPrefix; line_inv) hprefix
  rcases Line.of_run_cons hcall with ⟨callPost', qcall, hnil⟩
  cases hnil
  unfold callPrefix pushList at hprefix
  simp only [List.map] at hprefix
  rcases Line.of_run_cons hprefix with ⟨s1, q1, hprefix⟩
  have p1 : (0 : B256) :: p :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons hprefix with ⟨s2, q2, hprefix⟩
  have p2 : (0 : B256) :: 0 :: p :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 q2) p1
  rcases Line.of_run_cons hprefix with ⟨s3, q3, hprefix⟩
  have p3 : (0 : B256) :: 0 :: 0 :: p :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 q3) p2
  rcases Line.of_run_cons hprefix with ⟨s4, q4, hprefix⟩
  have p4 : (0 : B256) :: 0 :: 0 :: 0 :: p :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 q4) p3
  rcases Line.of_run_cons hprefix with ⟨s5, qswap, hprefix⟩
  have hswap : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: p :: xs)
      (p :: 0 :: 0 :: 0 :: 0 :: xs) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have p5 : p :: 0 :: 0 :: 0 :: 0 :: xs <<+ s5.stack :=
    Stack.prefix_of_swap hswap (of_run_swap qswap) p4
  rcases Line.of_run_cons hprefix with ⟨s6, qcaller, hprefix⟩
  have p6 : sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs <<+
      s6.stack :=
    prefix_of_push (of_run_caller qcaller) p5
  rcases Line.of_run_cons hprefix with ⟨s7, qgas, hnil⟩
  cases hnil
  rcases of_run_gas qgas with ⟨gasWord, hgas⟩
  refine ⟨callPre, gasWord, ?_, qcall,
    hstorPrefix.symm, hbalPrefix.symm, hcodePrefix.symm, hlogsPrefix.symm,
    houtPrefix.symm, hmemPrefix.symm⟩
  simpa only [List.cons_append, List.nil_append] using prefix_of_push hgas p6

/-- An `exit` payout whose status word is consumed by the success guard.  The
carrier retains the exact EIP-150 child message, delegation choice, empty
calldata/output windows, successful child settlement and caller resumption.
The first disjunct of `of_run_call_val_with_depth_frame` is absent precisely
because its zero flag selects the outer `Func.revert`; that inversion still
supplies `Devm.WorldEq` for the rejected child-failure arm. -/
def AcceptedPayout (sevm : Sevm) (p : B256)
    (callPre callPost guardPost returnPre : Devm) : Prop :=
  ∃ (gasWord : B256) (xs : Stack) (parent child : Devm) (xl : Xlot)
    (delegated : Bool) (nextAddress : Adr) (code : ByteArray) (avail pc : Nat),
    (gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs) <<+
      callPre.stack ∧
    Ninst.Run sevm callPre call callPost ∧
    Devm.PopBurn [1] callPost guardPost ∧
    Devm.Burn guardPost returnPre ∧
    Ninst.StepRun pc sevm callPre call xl (.ok callPost) ∧
    0 < sevm.depth ∧
    callPre.stack = gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 ::
      parent.stack ∧
    parent.state = callPre.state ∧
    parent.memory = callPre.memory.extends [(0, 0), (0, 0)] ∧
    parent.logs = callPre.logs ∧
    parent.output = callPre.output ∧
    ((getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) =
          none ∧
        nextAddress = sevm.caller.toB256.toAdr ∧
        code = callPre.getCode sevm.caller.toB256.toAdr ∧
        delegated = false) ∨
      (∃ d,
        getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) =
            some d ∧
          nextAddress = d ∧ code = callPre.getCode d ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg sevm parent
        (min gasWord.toNat (except64th avail) +
          (if p.toNat = 0 then 0 else gCallStipend))
        p sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
        ((callPre.memory.read 0 0).1) code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    (Resume.call parent 0 0).run (.ok child) = .ok callPost ∧
    callPost.state = child.state ∧
    callPost.returnData = child.output ∧
    callPost.memory = parent.memory.write 0 (child.output.take 0) ∧
    callPost.stack = (1 : B256) :: parent.stack

/-- The complete successful source-level `exit`: all guards hold, the four
ledger writes are already present at the call boundary, the exact value call
entered and settled cleanly, and the outer frame returns the payout word.
Callback-final storage and balance are related to the resumed child rather
than falsely summarized as a callback-free delta. -/
def ExitPaysExactly (sevm : Sevm) (entry post : Devm) : Prop :=
  let units := Sevm.dataWord sevm (32 * 0 + 4)
  let oldRow := Devm.getStorVal entry sevm.currentTarget sevm.caller.toB256
  let oldTotal := Devm.getStorVal entry sevm.currentTarget totalUnitsSlot
  let oldChi := Devm.getStorVal entry sevm.currentTarget chiSlot
  let oldRho := Devm.getStorVal entry sevm.currentTarget rhoSlot
  let elapsed := sevm.benvStat.time - oldRho
  let freshChi :=
    (B256.rpow scale half rate elapsed.toNat * oldChi) / scale
  let payout := (freshChi * units) / scale
  ¬ maxUnits < units ∧
    ¬ maxUnits < oldRow ∧
    ¬ maxPie < oldTotal ∧
    ¬ oldRow < units ∧
    ¬ oldTotal < units ∧
    ¬ oldChi < scale ∧
    ¬ maxChi < oldChi ∧
    ¬ sevm.benvStat.time < oldRho ∧
    ¬ maxElapsed < elapsed ∧
    B256.RPowGuards scale half rate elapsed.toNat ∧
    ∃ callPre callPost guardPost returnPre,
      Devm.getStor callPre sevm.currentTarget =
        ((((Devm.getStor entry sevm.currentTarget).set chiSlot freshChi).set
              rhoSlot sevm.benvStat.time).set sevm.caller.toB256
              (oldRow - units)).set totalUnitsSlot (oldTotal - units) ∧
      AcceptedPayout sevm payout callPre callPost guardPost returnPre ∧
      Devm.getStor post = Devm.getStor callPost ∧
      Devm.getBal post = Devm.getBal callPost ∧
      ReturnsWord payout post

theorem exit_pays_exactly {fs : List Func} (hlookup : AuxLookup fs)
    {sevm : Sevm} {entry s post : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs sevm s Drip.exit post) :
    ExitPaysExactly sevm entry post := by
  unfold ExitPaysExactly
  dsimp only
  rcases of_run_exit_settles hlookup frame hp run with
    ⟨hargCap, hrowCap, htotalCap, hown, hfund, hlower, hupper, hclock,
      helapsed, hguards, callStart, freshChi, settledImage, hfresh,
      hresult, hpStart, hwfStart, hreadsStart, hstorStart, suffix⟩
  subst freshChi
  refine ⟨hargCap, hrowCap, htotalCap, hown, hfund, hlower, hupper,
    hclock, helapsed, hguards, ?_⟩
  rcases of_run_prepend (loadWord resultWord) _ suffix with
    ⟨sendPre, hload, suffix⟩
  obtain ⟨hpSend, hwfSend, hreadsSend, hstateSend⟩ :=
    of_run_loadWordAt_image (word := resultWord)
      (value :=
        ((B256.rpow scale half rate
              (sevm.benvStat.time -
                Devm.getStorVal entry sevm.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry sevm.currentTarget chiSlot) / scale *
          Sevm.dataWord sevm (32 * 0 + 4)) / scale)
      hpStart hwfStart hreadsStart hresult hload
  rcases of_run_prepend sendToCaller _ suffix with
    ⟨callPost, hsend, hbranch⟩
  rcases exit_sendToCaller_frame hpSend hsend with
    ⟨callPre, gasWord, hstack, hcall, hstorSend, hbalSend, hcodeSend,
      hlogsSend, houtSend, hmemSend⟩
  have hstorTail : Devm.getStor callPost = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hbranch
  have hbalTail : Devm.getBal callPost = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hbranch
  rcases of_run_branch hbranch with
    ⟨_, hzero, hrev⟩ |
      ⟨w, guardPost, returnPre, hw, hpop, hburn, hreturn⟩
  · exact (not_run_revert hrev).elim
  rcases of_run_call_val_with_depth_frame hstack hcall with
      hfailed | hentered
  · exact (hw (popBurn_pref hpop hfailed.1).1).elim
  rcases hentered with
    ⟨parent, child, xl, delegated, nextAddress, code, avail, pc, hstep,
      hdepth, hstackEq, hparentState, hparentMemory, hparentLogs,
      hparentOutput, hdelegated, hfilled, hmessage, hclean, hresume,
      hpostState, hpostReturnData, hpostMemory, hpostStack⟩
  have hpostPrefix : (1 : B256) :: tail <<+ callPost.stack := by
    rw [hpostStack]
    apply pref_cons
    rw [hstackEq] at hstack
    exact cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
      (cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
        (cons_pref_cons_inv hstack))))))
  have hpop1 : Devm.PopBurn [1] callPost guardPost := by
    have hwone : w = 1 := (popBurn_pref hpop hpostPrefix).1
    subst w
    exact hpop
  have hguardPrefix : tail <<+ guardPost.stack :=
    (popBurn_pref hpop1 hpostPrefix).2
  have hreturnPrefix : tail <<+ returnPre.stack := by
    rw [← hburn.stack]
    exact hguardPrefix
  have hstorCallPre :
      Devm.getStor callPre sevm.currentTarget =
        ((((Devm.getStor entry sevm.currentTarget).set chiSlot
                ((B256.rpow scale half rate
                      (sevm.benvStat.time -
                        Devm.getStorVal entry sevm.currentTarget rhoSlot).toNat *
                    Devm.getStorVal entry sevm.currentTarget chiSlot) /
                  scale)).set rhoSlot sevm.benvStat.time).set
            sevm.caller.toB256
            (Devm.getStorVal entry sevm.currentTarget sevm.caller.toB256 -
              Sevm.dataWord sevm (32 * 0 + 4))).set totalUnitsSlot
          (Devm.getStorVal entry sevm.currentTarget totalUnitsSlot -
            Sevm.dataWord sevm (32 * 0 + 4)) := by
    rw [hstorSend,
      ← congrFun (getStor_of_state hstateSend) sevm.currentTarget,
      hstorStart]
  refine ⟨callPre, callPost, guardPost, returnPre, hstorCallPre, ?_,
    hstorTail.symm, hbalTail.symm, ?_⟩
  · unfold AcceptedPayout
    exact ⟨gasWord, tail, parent, child, xl, delegated, nextAddress, code,
      avail, pc, hstack, hcall, hpop1, hburn, hstep, hdepth, hstackEq,
      hparentState, hparentMemory, hparentLogs, hparentOutput, hdelegated,
      hfilled, hmessage, hclean, hresume, hpostState, hpostReturnData,
      hpostMemory, hpostStack⟩
  · have hcallMemory : callPost.memory = callPre.memory := by
      rw [hpostMemory, hparentMemory]
      rfl
    have hwfCallPre : Mem.Wf callPre.memory := by
      rw [hmemSend]
      exact hwfSend
    have hreadsCallPre : Mem.Reads callPre.memory settledImage := by
      rw [hmemSend]
      exact hreadsSend
    have hwfCallPost : Mem.Wf callPost.memory := by
      rw [hcallMemory]
      exact hwfCallPre
    have hreadsCallPost : Mem.Reads callPost.memory settledImage := by
      rw [hcallMemory]
      exact hreadsCallPre
    have hmemoryReturn : callPost.memory = returnPre.memory :=
      hpop1.memory.trans hburn.memory
    have hwfReturn : Mem.Wf returnPre.memory := by
      rw [← hmemoryReturn]
      exact hwfCallPost
    have hreadsReturn : Mem.Reads returnPre.memory settledImage := by
      rw [← hmemoryReturn]
      exact hreadsCallPost
    unfold returnScratch at hreturn
    rcases of_run_prepend (loadWord resultWord) _ hreturn with
      ⟨returnWordPre, hloadReturn, hstoreReturn⟩
    obtain ⟨hpReturn, _, _, _⟩ :=
      of_run_loadWordAt_image (word := resultWord)
        (value :=
          ((B256.rpow scale half rate
                (sevm.benvStat.time -
                  Devm.getStorVal entry sevm.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry sevm.currentTarget chiSlot) / scale *
            Sevm.dataWord sevm (32 * 0 + 4)) / scale)
        hreturnPrefix hwfReturn hreadsReturn hresult hloadReturn
    exact (returnsWord_of_storeReturn hpReturn hstoreReturn).1

end Drip

end Blanc
