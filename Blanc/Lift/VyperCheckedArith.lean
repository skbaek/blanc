import Blanc.Lift.Vyper
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.ExactWalkCut
import Blanc.Lift.VyperFrameLoop
import Blanc.Lift.MemGlue
import Blanc.Lift.VyperCallee
import Blanc.Lift.StableSwapNewton.Defs
import Blanc.Lift.WalkInvKit

/-!
# Vyper 0.2.x checked `uint256` arithmetic and word-slot frames

Vyper 0.2.x compiles each checked `uint256` operation on the two stack words `[y, x]` (`y` on
top) to a fixed idiom: a guard over the operands, `PUSH2 ok JUMPI` past a reverting
fall-through, and a clean-up that leaves the result alone.  The trees here are those idioms
with the guard's tag, the reverting arm and the continuation as parameters:

* `vyMulT` computes `x * y`, guarded by `x = 0 ∨ (x * y) / x = y` (no wrap);
* `vyAddT` computes `x + y`, guarded by `¬ (x + y < x)` (no wrap);
* `vySubT` computes `x - y`, guarded by `¬ (x < y)` (no underflow);
* `vyDivT` computes `x / y`, guarded by `y ≠ 0`.

`ric_vyChk*` invert them (the guard holds, as a `Nat` fact, and the continuation runs from the
result); `rxc_vyChk*` run them forward at constant cost.

**Word-slot frames.**  A Vyper internal function keeps its variables in a fixed memory window
of words.  `WordFrame M0 M lo ws` says that `M` holds the words `ws` at `lo, lo + 32, …`,
inside the logical size, has `M0`'s size and agrees with `M0` outside the window.  The steps
`ric_mloadF`/`ric_mstoreF` (and their `PUSH2` forms) read and write a slot by index.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The idiom trees -/

/-! ## Guard facts -/

/-! ## Guards read as the checked operations on naturals -/

section Checked

open Blanc.StableSwapNewton

end Checked

/-! ## Comparison flags as branch conditions -/

/-! ## Signed range checks

Vyper 0.2 checks an `int128` index `0 ≤ i < n` with two `SLT`s. -/

/-! ## Inverted -/

section Inv

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg} {h l : UInt8} {fail k : SFunc}

/-- `SLT`, inverted, with its value. -/
theorem ri_sltV {x y : B256} {d : Devm}
    (hr : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .slt) d) :
    ∃ G', d = St b (B256.sltCheck x y :: S) M G' := by
  rcases of_run_reg hr with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := B256.sltCheck) (Devm.diffBurn_of_applyBinary run)

end Inv

/-! ## Word-slot frames -/

/-- `M` holds the words `ws` at `lo, lo + 32, …` inside `M0`'s (word-aligned) size, has
`M0`'s size and agrees with `M0` outside `[lo, lo + 32 * ws.length)`. -/
structure WordFrame (M0 M : Mem) (lo : Nat) (ws : List B256) : Prop where
  size : M.size = M0.size
  aligned : M0.size % 32 = 0
  cover : lo + 32 * ws.length ≤ M0.size
  word : ∀ j (hj : j < ws.length), memWord M (lo + 32 * j) = ws[j]
  agree : Mem.AgreeOutside M0 M lo (lo + 32 * ws.length)
  wf : Mem.Wf M0 → Mem.Wf M

theorem WordFrame.init {M0 : Mem} {lo n : Nat} (hsz : M0.size % 32 = 0)
    (hc : lo + 32 * n ≤ M0.size) : WordFrame M0 M0 lo (frameWords M0 lo n) where
  size := rfl
  aligned := hsz
  cover := by rw [length_frameWords]; exact hc
  word j hj := by simp only [frameWords, List.getElem_map, List.getElem_range]
  agree := Mem.AgreeOutside.refl _ _ _
  wf h := h

section FrameSteps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem}
  {G : Nat} {r : Seg} {f : SFunc} {lo : Nat} {ws : List B256}

end FrameSteps

/-! ## Forward -/

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg} {h l : UInt8} {fail k : SFunc}

end Fwd

/-! ## Checked operations read back as guards (for the forward walks) -/

section CheckedInv

open Blanc.StableSwapNewton

end CheckedInv

/-! ## `JUMPI` into a goto entry, forward -/

section FwdBranchTo

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg} {f g : SFunc} {j : Nat}

end FwdBranchTo

/-! ## Small word facts for the walks -/

/-- Stack room, whatever the shape of the stack's known prefix. -/
macro "vy_room" : tactic => `(tactic| first | omega | (simp only [List.length_cons]; omega))

/-! ## Tracked memory through frame save and restore chains -/

/-! ## From a word frame to a tracked memory -/


/-- `MLOAD` of an untracked word, inverted over a tracked memory: some word, the memory grown
to cover it. -/
theorem ric_mloadU {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256}
    {M M₀ : Mem} {G : Nat} {f : SFunc} {r : Seg} {P : List (Nat × Nat)} {L : List (Nat × B256)}
    {i : B256} {o : Nat} (hT : MemTrack M₀ M P L)
    (run : SFunc.RunCut fs sevm C (St b (i :: S) M G) (.next (.reg .mload) f) r)
    (hi : i.toNat = o) :
    ∃ v M' G', MemTrack M₀ M' P L ∧ SFunc.RunCut fs sevm C (St b (v :: S) M' G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G1, rfl⟩ := ri_mload s1
  rw [hi] at run
  have hk := Mem.KeepsOff.extend M o 32 P
  refine ⟨_, _, G1, ⟨hT.keeps.trans hk, ?_, hT.wf.extend _ _,
    fun h => Mem.size_extend_mod _ _ (hT.aligned h)⟩, run⟩
  intro o' v' hm'
  obtain ⟨hs, hv⟩ := hT.words o' v' hm'
  exact ⟨le_trans hs hk.1, hv⟩

set_option hygiene false in
/-- `PUSH o; MLOAD` of an untracked word. -/
macro "imloadU " o:term : tactic => `(tactic|
  (istep
   have hstep := ric_mloadU (o := $o) hT run (by decide)
   clear hT run; obtain ⟨_, _, _, hT, run⟩ := hstep))

set_option hygiene false in
/-- `SLT`, inverted to its value. -/
macro "isltV" : tactic => `(tactic|
  (have hnext := ric_next run; clear run; obtain ⟨_, s1, run⟩ := hnext
   obtain ⟨_, rfl⟩ := ri_sltV s1; clear s1))

set_option hygiene false in
open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- **Name the tracked memory** of a forward walk: generalize the memory term of `hT` (a
`MemTrack _ M _ _`) to the fresh name given, in `hT`, `hS` and the goal. -/
elab "xname " n:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? `hT | throwError "xname: no hT"
  let ty ← instantiateMVars ld.type
  let args := ty.getAppArgs
  unless args.size == 4 do throwError "xname: hT is not a MemTrack: {ty}"
  let stx ← Term.exprToSyntax args[1]!
  evalTactic (← `(tactic| generalize $stx:term = $n:ident at hT hS ⊢))

set_option hygiene false in
open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- `xname` keeping the equation: generalize the tracked memory term to `n`, with `h : term = n`. -/
elab "xnameE " n:ident h:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? `hT | throwError "xnameE: no hT"
  let ty ← instantiateMVars ld.type
  let args := ty.getAppArgs
  unless args.size == 4 do throwError "xnameE: hT is not a MemTrack: {ty}"
  let stx ← Term.exprToSyntax args[1]!
  evalTactic (← `(tactic| generalize $h:ident : $stx:term = $n:ident at hT hS ⊢))

end Blanc.Lift
