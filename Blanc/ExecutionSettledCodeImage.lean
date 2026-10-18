import Blanc.ExecutionSettledOwnCode

/-!
# An installed code image at every settled frame, whatever spawns

`ConfiguredHistoryTrace.settled_codeImage`: if the checkpoint holds a certified code image `sem` at
`a`, every settled frame of a configured history finds that image at `a` when it starts.  Unlike
`ConfiguredHistoryTrace.settled_ownCode` this needs no spawn restriction (`OwnSpawns`): it says
nothing about which code a frame runs, only that nonempty code is never replaced (same-frame steps
and child entries preserve it, `Exec.Deriv.ParentPrefix.balSum_le_getCode`,
`Evm.step_spawn_child`).

Contract-neutral; carried by the storage-trivial specification of `sem`.
-/

namespace Blanc

open Jaune

/-- **Code image below a frame.**  Along the chain of a frame `R` whose world holds the image of
`sem` at `a`, every committed descendant frame starts with that image at `a`. -/
theorem Exec.descendantFrames_codeImage {a : Adr} {sem : CodeSem} :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
      {R : Exec.Deriv}, Exec.Deriv.ParentPrefix R ⟨pc, sevm, pre, out, run⟩ →
      some (R.devm.getCode a).toList = sem.image →
      ∀ f ∈ Exec.descendantFrames run, some (f.pre.getCode a).toList = sem.image := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ _ _ f member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro R chain code
      simpa only [Exec.descendantFrames] using ih (chain.snoc (.cont step next)) code
  | doneErr _ _ _ =>
      intro _ _ _ f member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro R chain code
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.doneOk step enter resume next)) code
  | runErr _ _ _ _ =>
      intro _ _ _ f member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro R chain code f member
      have nonempty : (R.devm.getCode a).toList ≠ [] := fun empty =>
        sem.ne_nil (code.symm.trans (congrArg some empty)) rfl
      have nodeCode : nodePre.getCode a = R.devm.getCode a :=
        (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 a nonempty
      have childCode : some (cevm.dyna.getCode a).toList = sem.image := by
        rw [(Evm.step_spawn_child hstep henter).2.1 a, nodeCode]
        exact code
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume next
          settles] at member
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with (rfl | inChild) | inNext
        · exact childCode
        · exact childIh (R := ⟨_, _, _, _, child⟩) (.refl _) childCode f inChild
        · exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) code f inNext
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child hresume next
          settles] at member
        exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) code f member

namespace ExecutionTrace

open ExecutionAccountingReplay in
/-- The ladder observing every settled frame with the image of `sem` at `a`. -/
private def codeImageLadder (a : Adr) (sem : CodeSem) :
    AccountingLadderAdmitted (ContractSpecSem.ofStorageOnly sem (fun _ => True)) a
      (fun _ _ => True) where
  carrier :=
    { Snap := Unit
      Step := Exec.Frame
      Tag := Unit
      Replay := fun _ steps _ => ∀ f ∈ steps, some (f.pre.getCode a).toList = sem.image
      ofState := fun _ => ()
      frameEntry := fun _ _ => ()
      nil := fun _ f member => (List.not_mem_nil member).elim
      readsStorage := false
      silent := fun _ _ => rfl
      credit := by
        intros
        exact ⟨[], fun f member => (List.not_mem_nil member).elim⟩
      entry_eq_ofState := fun _ _ _ _ => rfl }
  append := fun left right f member => (List.mem_append.mp member).elim (left f) (right f)
  tag := fun _ _ => ()
  preserves := by
    intro sevm pre post fork run admitted image wf inv
    exact ⟨trivial, trivial⟩
  view :=
    { O := Exec.Frame
      obs := id
      obs_nil := rfl
      obs_append := fun _ _ => rfl
      frameObs := fun f => [f]
      credit := by
        intros
        exact ⟨[], fun f member => (List.not_mem_nil member).elim, rfl⟩ }
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed _ ready _ fork bound
    obtain ⟨installed, -⟩ := Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    refine ⟨Exec.committedFrames run, ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    intro f member
    rw [Exec.committedFrames, dite_eq_left committed] at member
    rcases List.mem_cons.mp member with rfl | deeper
    · exact installed.1
    · exact Exec.descendantFrames_codeImage run (R := ⟨pc, sevm, pre, out, run⟩) (.refl _)
        installed.1 f deeper

/-- **A certified code image stays installed at every settled frame.**  If the checkpoint holds
the image of `sem` at `a`, every settled frame of the history finds it at `a` when it starts. -/
theorem ConfiguredHistoryTrace.settled_codeImage (sem : CodeSem) (a : Adr)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode a).toList = sem.image) :
    ∀ f ∈ trace.settledFrames, some (f.pre.getCode a).toList = sem.image := by
  have admitted : trace.FrameAdmitted a (fun _ _ => True) :=
    (trace.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial
  obtain ⟨steps, replay, observed⟩ :=
    (codeImageLadder a sem).configuredHistory trace admitted ⟨installed, trivial, trivial⟩
  change steps = trace.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  intro f member
  exact replay f (observed ▸ member)

end ExecutionTrace

end Blanc
