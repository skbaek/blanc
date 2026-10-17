import Blanc.Composition.Weth9TokenCore
import Blanc.Lift.Token.Along

/-!
# WETH9's ledger across an arbitrary derivation: a holder nobody acts for keeps its balance

Over any committed derivation entered in WETH9's footprint precondition and admitted at WETH9 (HASH-T
over the keys its WETH9 frames touch), the footprint ledger after the run is the WETH9 book run over the
derivation's committed entry frames (`Exec.coreAccounting` with WETH9's model carrier), and every ledger
along that run is good (positional accounting plus the per-frame `FrameOk`).  So a holder `h` with no
allowance, none of whose WETH9 entries in the run is its own (`BookLaws.run_holder`), keeps its balance
from below and its zero allowances (`run_weth_holder`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9XLeg

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay Blanc.Composition.Weth9Token Blanc.Composition.Weth9TokenFrames

variable {ca : Adr} {U : Key → Prop}

/-- WETH9's whole-run model accounting, at every admitted derivation. -/
theorem weth9_core (ca : Adr) (inj : KeyInj U) :
    Exec.Fa (Exec.WknSem ca weth9Sem (fun pc s d e _ =>
      Exec.CoreAccounting ca weth9Sem (footEntry U) (wethCarrier ca U) (wethObservation ca U)
        pc s d e)) :=
  Exec.coreAccounting ca weth9Sem (footEntry U) (wethCarrier ca U) (wethObservation ca U)
    LedgerReplay.append (fun _ _ => ()) (fun _ _ _ => rfl)
    (fun _ hf => committedFrameInvocations_foreign hf)
    (fun hrun target deeper => Exec.CoreAccounting.spawnReplayTarget (fun _ _ => rfl)
      (fun {_ _} h => ledger_congr_get h) (fun _ hf => committedFrameInvocations_static hf)
      LedgerReplay.append (weth9_spawnKinds ca) (weth9_spawnReplay ca inj) hrun target deeper)

/-- WETH9's positional model accounting, at every admitted derivation. -/
theorem weth9_positional (ca : Adr) (inj : KeyInj U) :
    Exec.Fa (Exec.WknSem ca weth9Sem (fun pc s d e _ =>
      Exec.PositionalAccounting ca weth9Sem (footEntry U) (wethCarrier ca U)
        (wethObservation ca U) (fun _ => False) pc s d e)) :=
  Exec.positionalAccounting (Opaque := fun _ => False) (fun _ _ => rfl)
    (fun {_ _} h => ledger_congr_get h) (fun _ hf => committedFrameInvocations_foreign hf)
    LedgerReplay.append (fun _ op => op.elim) (weth9_core ca inj)
    (fun hrun target deeper => Exec.PositionalAccounting.modelTarget (fun _ _ => rfl)
      (fun {_ _} h => ledger_congr_get h) LedgerReplay.append (weth9_spawnKinds ca)
      (weth9_spawnReplay ca inj) (weth9_core ca inj) hrun target deeper)

open Classical in
/-- **The WETH9 holder segment below a derivation.**  Over a committed derivation on a covered fork,
entered with WETH9's code bookkeeping (`weth9Sem.At`), the footprint precondition and WETH9's own code
address, admitted by `footEntry U` over injective slots and under the ether-supply bound: if no
committed non-static frame at WETH9 is called by `h` and `h` has no allowance in the entry ledger,
then `h`'s booked balance does not drop across the run and `h` still has no allowance. -/
theorem run_weth_holder (inj : KeyInj U) {h : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (fork : CoveredFork sevm.benvStat.fork) (installed : weth9Sem.At ca pc sevm pre)
    (admitted : Exec.FrameAdmitted ca (footEntry U) run) (bound : sum pre.state.bal < 2 ^ 256)
    (hpre : (footSpec U).PreWf ca sevm pre)
    (rootCA : sevm.currentTarget = ca → sevm.codeAddress = some ca)
    (noOwn : ∀ f ∈ Exec.committedFrames run, f.sevm.currentTarget = ca →
      f.sevm.isStatic = false → f.sevm.caller ≠ h)
    (zero : ∀ g, weth9Book.allow (ledger U (pre.state.getStor ca)) h g = 0) :
    weth9Book.bal (ledger U (pre.state.getStor ca)) h ≤
        weth9Book.bal (ledger U ((Execution.committedPost out committed).state.getStor ca)) h ∧
      ∀ g, weth9Book.allow (ledger U ((Execution.committedPost out committed).state.getStor ca))
        h g = 0 := by
  have framesOk : ∀ f ∈ Exec.committedFrames run, FrameOk ca U f := by
    intro f member
    rw [Exec.committedFrames, dite_eq_left committed] at member
    rcases List.mem_cons.mp member with rfl | deeper
    · exact ⟨hpre, installed, rootCA, fork⟩
    · exact weth9_framesOk ca inj _ _ _ _ run installed run committed fork installed admitted hpre
        rootCA f deeper
  have entries : ∀ f ∈ Exec.committedFrames run, f.sevm.currentTarget = ca →
      f.sevm.codeAddress = some ca := fun f member => (framesOk f member).codeAddress
  have toBook : ∀ {frames : List Exec.Frame} {a b : Weth9.Ledger},
      (∀ f ∈ frames, f.sevm.currentTarget = ca → f.sevm.codeAddress = some ca) →
      LedgerReplay a (frames.flatMap (committedFrameInvocations ca)) b →
      weth9Book.run a (entryAsks ca frames) = some b := by
    intro frames a b hca replay
    refine (weth9Book_run_eq _ _).trans ?_
    rw [entryAsks_calls frames hca]
    exact replay
  obtain ⟨-, replayOf⟩ := weth9_core ca inj pc sevm pre out run installed run committed fork
    installed admitted
  obtain ⟨steps, replay, observed⟩ := replayOf bound
  change LedgerReplay (ledger U (pre.state.getStor ca)) steps
    (ledger U ((Execution.committedPost out committed).state.getStor ca)) at replay
  change steps = (Exec.committedFrames run).flatMap (committedFrameInvocations ca) at observed
  subst observed
  have bookRun := toBook entries replay
  have along : ∀ n p, n < (entryAsks ca (Exec.committedFrames run)).length →
      weth9Book.run (ledger U (pre.state.getStor ca))
        ((entryAsks ca (Exec.committedFrames run)).take n) = some p → weth9Book.Good p := by
    intro n p hn prefixRun
    obtain ⟨b1, g, b2, eq, asks⟩ := entryAsks_take ca (Exec.committedFrames run) n hn
    obtain ⟨steps', replay', observed'⟩ := weth9_positional ca inj pc sevm pre out run installed
      run committed fork installed admitted bound b1 g b2 eq (fun _ _ _ op => op)
    change LedgerReplay (ledger U (pre.state.getStor ca)) steps'
      (ledger U (g.pre.state.getStor ca)) at replay'
    change steps' = b1.flatMap (committedFrameInvocations ca) at observed'
    subst observed'
    have b1Run := toBook (fun f hf => entries f (by rw [eq]; exact List.mem_append_left _ hf))
      replay'
    rw [asks, prefixRun] at b1Run
    cases Option.some.inj b1Run
    exact good_of_pre (framesOk g (by rw [eq]; exact List.mem_append_right _ List.mem_cons_self)).pre.pre
  have safe : ∀ a ∈ entryAsks ca (Exec.committedFrames run), a.caller = h →
      (weth9Book.op a).HolderSafe := by
    intro a member own
    unfold entryAsks at member
    obtain ⟨f, fMem, rfl⟩ := List.mem_map.mp member
    obtain ⟨fIn, sel⟩ := List.mem_filter.mp fMem
    have sel' := of_decide_eq_true sel
    exact absurd own (noOwn f fIn sel'.1.1 sel'.2)
  have none : (entryAsks ca (Exec.committedFrames run)).filter (fun a => decide (a.caller = h)) =
      [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a member
    unfold entryAsks at member
    obtain ⟨f, fMem, rfl⟩ := List.mem_map.mp member
    obtain ⟨fIn, sel⟩ := List.mem_filter.mp fMem
    have sel' := of_decide_eq_true sel
    simpa only [decide_eq_true_eq] using noOwn f fIn sel'.1.1 sel'.2
  obtain ⟨balLe, allowZero⟩ := weth9Book_laws.run_holder bookRun along zero safe
  rw [none, List.map_nil, List.sum_nil, Nat.add_zero] at balLe
  exact ⟨balLe, allowZero⟩

end Blanc.Composition.UniswapV2PairWeth9XLeg
