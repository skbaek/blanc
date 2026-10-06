import Blanc.Lift.Weth9.CommittedHistory
import Blanc.Lift.CallChildren

/-!
# Every settled non-static WETH9 frame runs WETH9 and calls only as itself

Over a configured history in which the WETH9 runtime is installed at `ca` (the premises of
`weth9_history_committed`), the generic entry ladder (`ConfiguredHistoryTrace.entryGood_settled`, with
the trivial carried invariant) puts every settlement-committed non-static frame at `ca` at pc `0`, on a
covered fork, running the WETH9 bytes with the code installed (`weth9_history_settled_runsCode`).  The certificate cursor says
such a frame executes no external instruction but `CALL`/`STATICCALL` (`weth9_spawnKinds`), and both hand
the current target to the child as caller, so every direct child of such a frame is called by `ca`
itself (`weth9_history_settled_children_caller`).  Static frames are not claimed: the ladder only
observes non-static frames.
-/

namespace Blanc.Composition.Weth9SettledCallers

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- **Every settled non-static frame at the WETH9 address runs the WETH9 runtime from its entry.**  From
the premises of `weth9_history_committed`, every settlement-committed non-static frame at `ca` starts at
pc `0`, runs the deployed WETH9 bytes, is on a covered fork, and finds the WETH9 code installed at `ca`
(`CodeSem.At`). -/
theorem weth9_history_settled_runsCode {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace)) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = ca → G.sevm.isStatic = false →
      G.pc = 0 ∧ G.sevm.code = code ∧ CoveredFork G.sevm.benvStat.fork ∧
        weth9Sem.At ca 0 G.sevm G.pre := by
  let U := historyKeyUniverse ca trace K₀
  have extended : FootInv U (checkpoint.state.getStor ca) (checkpoint.state.bal ca) :=
    initial.extend fresh
  have admitted : trace.FrameAdmitted ca (footEntry U) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have start : (footSpec U).StateInv ca checkpoint.state :=
    footSpec_stateInv_iff.mpr ⟨installed, sumNof, extended.support, extended.backed⟩
  obtain ⟨-, good⟩ := trace.entryGood_settled (I := fun _ => True) admitted start trivial
    (footSpec_preservesAdmitted ca extended.inj) (fun _ _ _ _ _ _ _ _ => trivial)
    (weth9_spawnKinds ca) (fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
  intro G member target static
  obtain ⟨pcZero, fork, at₀, -, -⟩ := good G member target static
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
  dsimp only at pcZero fork at₀ target ⊢
  subst pcZero
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post => exact ⟨rfl, (weth9Sem.correct run (at₀.2 target).1).1, fork, at₀⟩

/-- **Every direct child of a settled non-static WETH9 frame is called by WETH9 itself.**  From the
premises of `weth9_history_committed`, every direct child of a settlement-committed non-static frame at
`ca` has caller `ca`: the frame runs the WETH9 bytes from pc `0` (`weth9_history_settled_runsCode`),
whose certificate executes no external instruction but `CALL`/`STATICCALL` (`weth9_spawnKinds`). -/
theorem weth9_history_settled_children_caller {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace)) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = ca → G.sevm.isStatic = false →
      ∀ c ∈ Exec.childFrames G.run, c.sevm.caller = ca := by
  intro G member target static
  obtain ⟨pcZero, -, fork, at₀⟩ :=
    weth9_history_settled_runsCode trace installed sumNof initial fresh G member target static
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
  dsimp only at pcZero fork at₀ target ⊢
  subst pcZero
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      have image : some sevm.code.toList = weth9Sem.image := (at₀.2 target).1
      rw [← target]
      exact Exec.childFrames_caller_of_callKinds
        (root := ⟨0, sevm, pre, .ok post, run⟩)
        (fun chain instruction =>
          weth9_spawnKinds ca run (weth9Sem.correct run image) target fork at₀ _ chain _ instruction)
        run (.refl _)

end Blanc.Composition.Weth9SettledCallers
