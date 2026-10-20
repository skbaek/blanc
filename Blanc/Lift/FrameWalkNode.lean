import Blanc.Lift.FrameWalk
import Blanc.Lift.SoundSpan

/-!
# Crossing a certified callee from a walked frame state

A frame walk on the actual derivation (`XAt`, `Blanc/Lift/FrameWalk.lean`) reaches the entry of
a certified tree; the lifting recursion (`node_soundM`) relates the rest of the derivation to the
tree's synthetic run.  This module joins the two:

* `Exec.Deriv.Prec.gasMeasure_lt`, `Exec.Deriv.lt.gasMeasure_lt`,
  `Exec.Deriv.ParentPrefix.gasMeasure_le`: gas only falls down a derivation, so a walked state's
  word-sized gas bound survives;
* `xa_node`: at a checked node, the walk either ends in the tree's halting run, or the tree
  returns to `ρ` and the walk continues there in the actual returned state (exact gas), with
  some remaining children;
* `xa_node_span`: for an exec-free tree (`ExecFreeSet`, `SFunc.execFreeIn`), the walk keeps its
  remaining children `L` across the return, and a halting run leaves none (`L = []`).

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## Gas only falls down a derivation -/

/-- An immediate sub-derivation starts with strictly less gas. -/
theorem Exec.Deriv.Prec.gasMeasure_lt {q p : Exec.Deriv} (h : q ≺ p) :
    q.devm.gasMeasure < p.devm.gasMeasure := by
  cases h with
  | cont hstep _ => exact gas_cont hstep
  | doneOk hstep henter hr _ => exact gas_done hstep henter hr
  | runOkCont hstep henter excChild hr _ => exact gas_run hstep henter excChild hr
  | @runErrChild pc sevm devm f rsm _ cevm _ _ hstep henter _ _ =>
    have b := Evm.step_gasBound ⟨pc, sevm, devm⟩
    rw [hstep] at b
    change f.inner.gas + rsm.parentGas < devm.gasMeasure ∧ _ at b
    change cevm.dyna.gasMeasure < devm.gasMeasure
    rw [Frame.enter_run_gasMeasure henter]
    omega
  | @runOkChild pc sevm devm f rsm _ cevm _ _ _ hstep henter _ _ _ =>
    have b := Evm.step_gasBound ⟨pc, sevm, devm⟩
    rw [hstep] at b
    change f.inner.gas + rsm.parentGas < devm.gasMeasure ∧ _ at b
    change cevm.dyna.gasMeasure < devm.gasMeasure
    rw [Frame.enter_run_gasMeasure henter]
    omega

theorem Exec.Deriv.le.gasMeasure_le {q p : Exec.Deriv} (h : Exec.Deriv.le q p) :
    q.devm.gasMeasure ≤ p.devm.gasMeasure := by
  induction h with
  | refl => exact le_rfl
  | step _ prec ih => exact le_of_lt (lt_of_le_of_lt ih (Exec.Deriv.Prec.gasMeasure_lt prec))

theorem Exec.Deriv.lt.gasMeasure_lt {q p : Exec.Deriv} (h : Exec.Deriv.lt q p) :
    q.devm.gasMeasure < p.devm.gasMeasure := by
  obtain ⟨q', hle, prec⟩ := h
  exact lt_of_le_of_lt (Exec.Deriv.le.gasMeasure_le hle) (Exec.Deriv.Prec.gasMeasure_lt prec)

theorem Exec.Deriv.ParentPrefix.gasMeasure_le {p q : Exec.Deriv}
    (h : Exec.Deriv.ParentPrefix p q) : q.devm.gasMeasure ≤ p.devm.gasMeasure := by
  induction h with
  | refl => exact le_rfl
  | step head _ ih => exact le_of_lt (lt_of_le_of_lt ih (Exec.Deriv.Prec.gasMeasure_lt head.prec))

/-! ## B1: any checked node -/

section Node

variable {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool}
  {sevm : Sevm} {post d : Devm} {pc m : Nat} {a : List AVal} {f : SFunc} {ρ : B256}
  {S base : List B256} {μ : MemMap} {L : List Exec.Frame}

/-- **A checked node crossed from a walked state.**  The tree's run halts with the frame's
result, or returns to `ρ`: the walk continues at `ρ` in the actual returned state, whose stack
holds exactly `m` words above the untouched `base`. -/
theorem xa_node (hc : Cert.CheckedM code c ms b) (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hcheck : checkNodeM code c.entries ms b m pc a μ f = true)
    (hstack : d.stack = S ++ base) (hframe : FrameMatches ρ a S)
    (hmem : MemMatches ρ μ d.memory) (h : XAt sevm post pc d L) :
    SFunc.Run c.prog sevm d f (.halted post) ∨
      ∃ (d' : Devm) (S' : List B256) (L' : List Exec.Frame),
        SFunc.Run c.prog sevm d f (.returned d') ∧ XAt sevm post ρ.toNat d' L' ∧
        d'.stack = S' ++ base ∧ S'.length = m := by
  obtain ⟨exc, -, hg⟩ := h
  rcases node_soundM hc ⟨pc, sevm, d, .ok post, exc⟩ ⟨pc, sevm, d, .ok post, exc⟩
      (fun _ hr => List.mem_cons_of_mem _ hr) post rfl hcode hfork m a f ρ S base μ hcheck
      hstack hframe hmem with
    run | ⟨-, d', S', exc', hlt, run, hst, hlen⟩
  · exact .inl (run.mono StepIn.toRun)
  · exact .inr ⟨d', S', _, run.mono StepIn.toRun,
      XAt.of_exec exc' (lt_trans (Exec.Deriv.lt.gasMeasure_lt hlt) hg), hst, hlen⟩

/-! ## B2: exec-free trees keep the remaining children -/

/-- **An exec-free checked node crossed from a walked state.**  As `xa_node`, and the tree
spawns no frame: a halting run leaves no remaining child, and the walk continues at `ρ` with
the same remaining children `L`. -/
theorem xa_node_span {E : List Nat} (hc : Cert.CheckedM code c ms b)
    (hE : ExecFreeSet c.prog E = true) (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hcheck : checkNodeM code c.entries ms b m pc a μ f = true) (hfree : f.execFreeIn E = true)
    (hstack : d.stack = S ++ base) (hframe : FrameMatches ρ a S)
    (hmem : MemMatches ρ μ d.memory) (h : XAt sevm post pc d L) :
    (SFunc.Run c.prog sevm d f (.halted post) ∧ L = []) ∨
      ∃ (d' : Devm) (S' : List B256),
        SFunc.Run c.prog sevm d f (.returned d') ∧ XAt sevm post ρ.toNat d' L ∧
        d'.stack = S' ++ base ∧ S'.length = m := by
  obtain ⟨exc, rfl, hg⟩ := h
  rcases node_span_childFrames hc hE exc hcode hfork hcheck hfree hstack hframe hmem with
    ⟨run, hnil⟩ | ⟨d', exc', S', run, hch, pp, hst, hlen⟩
  · exact .inl ⟨run, hnil⟩
  · exact .inr ⟨d', S', run,
      ⟨exc', hch, lt_of_le_of_lt (Exec.Deriv.ParentPrefix.gasMeasure_le pp) hg⟩, hst, hlen⟩

end Node

end Blanc.Lift
