import Blanc.DripRealizedHistory
import Blanc.PrefixTransport
import Blanc.ExecutionPathLocator

/-!
DRIP exit payout identity at the actual compiled `CALL` node.

The source results expose the pre-callback state only as a loose witness. This
leaf threads the loose gas-free walk prefix from the runtime entry to the head
of `gas ::: call ::: …`, replays it onto the actual execution with
`Exec.Deriv.SourceCursor.ofRunPrefix`, crosses `gas` with the actual step, and
reads the payout fields off the actual node. The `gas` word is the actual
node's own; it is never claimed equal to a loose one.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Drip

/-- The suffix of `exit` that starts at the only gas-reading instruction. -/
def exitCallSuffix : Func :=
  gas ::: call ::: ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> Func.revert)

/-- The loose gas-free prefix from the runtime entry to the `gas` head of the
exit payout, with the settled ledger facts restated against the execution's
own entry state. -/
theorem exit_gasHead_prefix {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = exitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    let units := Sevm.dataWord sevm (32 * 0 + 4)
    let freshChi := (B256.rpow scale half rate
      (sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
      Devm.getStorVal pre sevm.currentTarget chiSlot) / scale
    let payout := (freshChi * units) / scale
    ∃ (entry t : Devm) (target : Prog.SourcePath),
      Devm.Burn pre entry ∧
      Devm.getCode t = Devm.getCode pre ∧
      (sevm.caller.toB256 :: payout :: 0 :: 0 :: 0 :: 0 :: payout :: [] <<+
        t.stack) ∧
      Mem.Wf t.memory ∧
      Devm.getStor t sevm.currentTarget =
        ((((Devm.getStor pre sevm.currentTarget).set chiSlot freshChi).set
            rhoSlot sevm.benvStat.time).set sevm.caller.toB256
            (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 - units)).set
          totalUnitsSlot
            (Devm.getStorVal pre sevm.currentTarget totalUnitsSlot - units) ∧
      Func.RunPrefix (runtime.main :: runtime.aux) sevm ⟨0, []⟩ entry main
        target t exitCallSuffix ∧
      Func.Run (runtime.main :: runtime.aux) sevm t exitCallSuffix post := by
  dsimp only
  have hrun : Prog.Run sevm pre runtime post :=
    correct sevm pre runtime post exc (installed_compile hcode)
  dsimp only [Prog.Run] at hrun
  cases hrun
  rename (_ = _) => heq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => entry
  cases heq
  rcases dispatch_entry_of_run_main_prefix (path := ⟨0, []⟩) run hnonempty with
    ⟨s2, path2, hst2, hmm2, -, -, hpfx, hpre2, hdispatch⟩
  rw [hsel] at hpfx
  have hmem : (exitSelector, nonpayable (exactCalldata 36 exit)) ∈ funcs := by
    simp [funcs]
  rcases reach_of_dispatch_logs (path := path2) funcs_sorted hmem hpfx
      hdispatch with
    ⟨s3, path3, -, hst3, hmm3, -, -, hpre3, hwrapped⟩
  rcases of_run_nonpayable_exactCalldata_prefix (path := path3) hwrapped with
    ⟨s4, path4, -, -, hst4, hmm4, -, -, hpre4, hbody⟩
  have hst : pre.state = s4.state :=
    burn.state.trans (hst2.trans (hst3.trans hst4))
  have hmm : pre.memory = s4.memory :=
    burn.memory.trans (hmm2.trans (hmm3.trans hmm4))
  have hmem4 : s4.memory = Mem.empty := by rw [← hmm, hcanon]
  have hframe : Frame [] s4 s4 :=
    ⟨by rw [hmem4]; exact Mem.wf_empty,
      by rw [hmem4]; exact Mem.reads_empty, rfl, rfl⟩
  rcases of_run_exit_settles_full_prefix (path := path4) auxLookup_runtime
      hframe nil_pref hbody with
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, t, freshChi, settledImage, target,
      hfresh, hcodeT, hpT, hwfT, -, hstorT, hpre5, suffix⟩
  subst freshChi
  have hgv : ∀ k, Devm.getStorVal s4 sevm.currentTarget k =
      Devm.getStorVal pre sevm.currentTarget k :=
    fun k => Devm.getStorVal_of_state hst.symm sevm.currentTarget k
  have hg : Devm.getStor s4 sevm.currentTarget =
      Devm.getStor pre sevm.currentTarget :=
    getStor_eq_of_state_eq hst.symm sevm.currentTarget
  have hc : Devm.getCode s4 = Devm.getCode pre :=
    congrArg State.getCode hst.symm
  simp only [hgv, hg, hc] at hcodeT hpT hstorT
  exact ⟨entry, t, target, burn, hcodeT, hpT, hwfT, hstorT,
    (hpre2.trans hpre3).trans (hpre4.trans hpre5), suffix⟩

/-- Recognizer for the value-transferring `CALL` source instruction. -/
def isCallInstruction : Ninst → Bool
  | .exec .call => true
  | _ => false

/-- Compiled counter of the exit payout `CALL`, the runtime's only source
`call` site. -/
def exitCallSitePc : Nat := 1720

private theorem runtime_call_sites_checked :
    (runtime.sourceSites.all fun site =>
      !isCallInstruction site.instruction || site.pc == exitCallSitePc) =
        true := by
  decide +kernel

/-- Every source `call` site of the compiled runtime sits at one counter: the
exit payout is the runtime's only `CALL`. -/
theorem runtime_call_site_pc {site : Prog.SourceSite}
    (member : site ∈ runtime.sourceSites)
    (isCall : site.instruction = call) : site.pc = exitCallSitePc := by
  have checked := List.all_eq_true.mp runtime_call_sites_checked site member
  rw [isCall] at checked
  simpa [isCallInstruction] using checked

/-- **Exit payout identity.** A successful `exit` of the installed runtime has
an actual same-frame `CALL` node whose storage, code, payout stack words and
memory well-formedness are the settled ones. The `gas` word is existential and
is the actual node's own. -/
theorem exit_callNode_identity_of_exec {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = exitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    let units := Sevm.dataWord sevm (32 * 0 + 4)
    let freshChi := (B256.rpow scale half rate
      (sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
      Devm.getStorVal pre sevm.currentTarget chiSlot) / scale
    let payout := (freshChi * units) / scale
    ∃ (node : Exec.NinstOccurrence ⟨0, sevm, pre, .ok post, exc⟩)
      (gasWord : B256),
      node.instruction = call ∧
      node.node.pc = exitCallSitePc ∧
      Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, exc⟩ node.node ∧
      Devm.getStor node.node.devm sevm.currentTarget =
        ((((Devm.getStor pre sevm.currentTarget).set chiSlot freshChi).set
            rhoSlot sevm.benvStat.time).set sevm.caller.toB256
            (Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 - units)).set
          totalUnitsSlot
            (Devm.getStorVal pre sevm.currentTarget totalUnitsSlot - units) ∧
      Devm.getCode node.node.devm = Devm.getCode pre ∧
      (gasWord :: sevm.caller.toB256 :: payout :: 0 :: 0 :: 0 :: 0 :: payout ::
        [] <<+ node.node.devm.stack) ∧
      Mem.Wf node.node.devm.memory ∧
      ∃ callPost guardPost returnPre, node.stepResult = .ok callPost ∧
        AcceptedPayout sevm payout node.node.devm callPost guardPost
          returnPre := by
  dsimp only
  rcases exit_gasHead_prefix exc hcode hsel hnonempty hcanon with
    ⟨entry, t, target, burn, hcodeT, hpT, hwfT, hstorT, walk, -⟩
  have compiled : some sevm.code.toList = runtime.compile :=
    installed_compile hcode
  rcases Exec.Deriv.SourceCursor.mainForward
      (root := ⟨0, sevm, pre, .ok post, exc⟩) (program := runtime)
      rfl compiled rfl with
    ⟨mainCursor, mainReached, actualBurn⟩
  have seed : Devm.EqModGas entry mainCursor.pre :=
    (Devm.EqModGas.refl pre).of_burn burn actualBurn
  rcases mainCursor.ofRunPrefix compiled rfl walk seed with
    ⟨gasCursor, agree, gasReached⟩
  unfold exitCallSuffix at gasCursor
  rcases gasCursor.nextForward rfl with ⟨callCursor, gasEdge, gasRun⟩
  rcases of_run_gas gasRun with ⟨gasWord, gasPush⟩
  rcases callCursor.nextForward rfl with ⟨afterCursor, callEdge, callRun⟩
  have restRun : Func.Run (runtime.main :: runtime.aux) sevm afterCursor.pre
      ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> Func.revert) post :=
    correct_core runtime.main runtime.aux afterCursor.node _ compiled
      afterCursor.codeSlice
  have callRun' := callRun
  rcases callRun with ⟨slot, filled, anyPc, stepRun⟩
  have stepRun' := Ninst.stepRun_pc_irrel (n := call) rfl
    (pc' := callCursor.pc) stepRun
  have sameFrame : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, exc⟩
      callCursor.node :=
    (mainReached.trans gasReached).snoc gasEdge
  have reached : callCursor.node ∈ Exec.rawNodes exc :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix exc _).mpr
      ⟨_, Exec.mem_rawFrameRoots_self exc, sameFrame⟩
  have sitePc : callCursor.pc = exitCallSitePc :=
    runtime_call_site_pc
      (callCursor.sourceIncluded
        (site := ⟨⟨target.functionIndex, target.steps ++ [.rest]⟩,
          callCursor.pc, call⟩)
        (by simp [Func.sourceSites])) rfl
  have stateT : t.state = gasCursor.pre.state := agree.state
  have stackT : t.stack = gasCursor.pre.stack := agree.stack
  have memoryT : t.memory = gasCursor.pre.memory := agree.memory
  have stateCall : t.state = callCursor.pre.state :=
    stateT.trans gasPush.state
  have memoryCall : t.memory = callCursor.pre.memory :=
    memoryT.trans gasPush.memory
  rw [stackT] at hpT
  have hstack := prefix_of_push gasPush hpT
  rcases of_run_branch restRun with
    ⟨_, -, hrev⟩ | ⟨w, guardPost, returnPre, hw, hpop, hburn, -⟩
  · exact (not_run_revert hrev).elim
  rcases of_run_call_val_with_depth_frame hstack callRun' with
    hfailed | hentered
  · exact (hw (popBurn_pref hpop hfailed.1).1).elim
  rcases hentered with
    ⟨parent, child, xl, delegated, nextAddress, childCode, avail, pc, hstep,
      hdepth, hstackEq, hparentState, hparentMemory, hparentLogs,
      hparentOutput, hdelegated, hfilled, hmessage, hclean, hresume,
      hpostState, hpostReturnData, hpostMemory, hpostStack⟩
  have hpop1 : Devm.PopBurn [1] afterCursor.pre guardPost := by
    have hpostPrefix : (1 : B256) :: [] <<+ afterCursor.pre.stack := by
      rw [hpostStack]
      exact pref_cons nil_pref
    have hwone : w = 1 := (popBurn_pref hpop hpostPrefix).1
    subst w
    exact hpop
  refine ⟨⟨callCursor.node, call, slot, .ok afterCursor.pre, reached,
    callCursor.ninstAt, filled, stepRun'⟩, gasWord, rfl, sitePc, sameFrame,
    ?_, ?_, hstack, ?_, afterCursor.pre, guardPost, returnPre, rfl, ?_⟩
  · exact (getStor_eq_of_state_eq stateCall.symm sevm.currentTarget).trans
      hstorT
  · exact (congrArg State.getCode stateCall.symm).trans hcodeT
  · change Mem.Wf callCursor.pre.memory
    rw [← memoryCall]
    exact hwfT
  · exact ⟨gasWord, _, parent, child, xl, delegated, nextAddress, childCode,
      avail, pc, hstack, callRun', hpop1, hburn, hstep, hdepth, hstackEq,
      hparentState, hparentMemory, hparentLogs, hparentOutput, hdelegated,
      hfilled, hmessage, hclean, hresume, hpostState, hpostReturnData,
      hpostMemory, hpostStack⟩

/-- The selected body's compiled exit has an actual same-frame `CALL` node in
its own retained execution, carrying the settled ledger, the exact payout
words, and the accepted payout stated at that node's state. Unlike
`exit_preCallback`, the pre-callback state here is the node's, not a witness. -/
theorem BodyExecutionOccurrence.exit_callNode_identity
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {body : ExecutionTrace.AppliedBodyTrace benv txs wds state bout}
    (occurrence : BodyExecutionOccurrence body)
    (codeEq : occurrence.execution.sevm.code.toList = code)
    (selector : Sevm.selector occurrence.execution.sevm = exitSelector)
    (nonempty : occurrence.execution.sevm.data.length.toB256 ≠ 0)
    (canonicalEntry : occurrence.execution.entryState.memory = Mem.empty) :
    let sevm := occurrence.execution.sevm
    let initial := occurrence.execution.entryState
    let units := Sevm.dataWord sevm (32 * 0 + 4)
    let freshChi := (B256.rpow scale half rate
      (sevm.benvStat.time - Devm.getStorVal initial sevm.currentTarget rhoSlot).toNat *
      Devm.getStorVal initial sevm.currentTarget chiSlot) / scale
    let payout := (freshChi * units) / scale
    ∃ (node : Exec.NinstOccurrence
        ⟨0, sevm, initial, .ok occurrence.execution.postState,
          occurrence.execution.run⟩)
      (gasWord : B256),
      node.instruction = call ∧
      node.node.pc = exitCallSitePc ∧
      Exec.Deriv.ParentPrefix
        ⟨0, sevm, initial, .ok occurrence.execution.postState,
          occurrence.execution.run⟩ node.node ∧
      Devm.getStor node.node.devm sevm.currentTarget =
        ((((Devm.getStor initial sevm.currentTarget).set chiSlot freshChi).set
            rhoSlot sevm.benvStat.time).set sevm.caller.toB256
            (Devm.getStorVal initial sevm.currentTarget sevm.caller.toB256 - units)).set
          totalUnitsSlot
            (Devm.getStorVal initial sevm.currentTarget totalUnitsSlot - units) ∧
      Devm.getCode node.node.devm = Devm.getCode initial ∧
      (gasWord :: sevm.caller.toB256 :: payout :: 0 :: 0 :: 0 :: 0 :: payout ::
        [] <<+ node.node.devm.stack) ∧
      Mem.Wf node.node.devm.memory ∧
      ∃ callPost guardPost returnPre, node.stepResult = .ok callPost ∧
        AcceptedPayout sevm payout node.node.devm callPost guardPost
          returnPre :=
  exit_callNode_identity_of_exec occurrence.execution.run codeEq selector
    nonempty canonicalEntry

end Drip

end Blanc
