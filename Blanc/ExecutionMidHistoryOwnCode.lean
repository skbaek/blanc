import Blanc.ExecutionInOwnCode
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.ExecutionMidHistoryInFacts
import Blanc.ExecutionInRootOwnCode
import Blanc.ExecutionHistoryCommittedCuts

/-!
# Own code at retained frames of a mid-block history

The historical descendant theorem already follows each actual spawn. This
module carries that observation through the existing mid-history accounting
runner, starting at the exact post-transaction boundary.
-/

namespace Blanc.ExecutionTrace

open Jaune ExecutionAccountingReplay

/-- Own code and its address at the actual roots after a transaction cut.
The initial suffix retains its requests; later blocks retain all system stages.
No installed-world or storage-preservation premise is required. -/
theorem MidHistoryTraceIn.settledRoots_rootOwnEntry
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  induction trace with
  | tail block cut =>
    intro R member
    rcases List.mem_append.mp member with transactions | requests
    · exact cut.after.settledRoots_rootOwnEntry R transactions
    · exact block.bodyTrace.requests.settledRoots_rootOwnEntry R requests
  | step prior block ih =>
    intro R member
    rcases List.mem_append.mp member with earlier | later
    · exact ih R earlier
    · exact block.settledRoots_rootOwnEntry R later

/-- The original prefix before a selected transaction has the same root-entry
provenance, including its beacon and history system stages. -/
theorem ConfiguredBlockTraceIn.rootsBeforeTxSplit_rootOwnEntry
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    ∀ R ∈ block.rootsBeforeTxSplit cut, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  intro R member
  simp only [ConfiguredBlockTraceIn.rootsBeforeTxSplit, List.mem_append] at member
  rcases member with (beacon | history) | transactions
  · exact block.bodyTrace.beacon.settledRoots_rootOwnEntry R beacon
  · exact block.bodyTrace.history.settledRoots_rootOwnEntry R history
  · exact cut.before.settledRoots_rootOwnEntry R transactions

/-- An observation-only historical ladder for installed and executed code.
It reuses the actual descendant proof and the caller's existing preservation law. -/
def ownCodeLadderIn {F : Fork → Prop} {c : ContractSpecSem} {ca : Adr}
    {entry : Sevm → Devm → Prop} {C : ByteArray}
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hsgF : ∀ {f}, F f → f.ruleSet.stateGas = none)
    (image : c.sem.image = some C.toList)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C) : AccountingLadderAdmittedIn F c ca entry where
  carrier :=
    { Snap := Unit
      Step := Exec.Frame
      Tag := Unit
      Replay := fun _ steps _ => ∀ f ∈ steps, OwnCodeAtIn F ca C f
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
  preserves := preserves
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
    have pcZero : pc = 0 := by
      have same := congrArg Evm.pc evmEq
      simpa only [initEvm] using same
    have code : pre.getCode ca = C := bytes_eq_of_image (installed.1.trans image)
    have own : sevm.currentTarget = ca → sevm.code = C := fun target =>
      bytes_eq_of_image ((installed.2 target).1.trans image)
    refine ⟨Exec.committedFrames run, ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    intro f member
    rw [Exec.committedFrames, dite_eq_left committed] at member
    rcases List.mem_cons.mp member with rfl | deeper
    · exact ⟨code, pcZero, fork, hsgF fork, own⟩
    · exact Exec.descendantFrames_ownCodeIn nonempty nondelegating spawns run
        (R := ⟨pc, sevm, pre, out, run⟩) (.refl _) pcZero fork (hsgF fork) code own f deeper

/-- Installed code and execution identity at every retained frame from the actual cut.
The fork, balance, installation and admission requirements are the existing runner's. -/
theorem MidHistoryTraceIn.settled_ownCodeIn {F : Fork → Prop} {c : ContractSpecSem}
    {ca : Adr} {entry : Sevm → Devm → Prop} {C : ByteArray}
    {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (hsgF : ∀ {f}, F f → f.ruleSet.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry) (rewards : trace.RewardCreditsFunded)
    (inv : c.StateInv ca start.state) (K : InstalledCert C)
    (image : c.sem.image = some C.toList)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  obtain ⟨steps, replay, observed⟩ :=
    (ownCodeLadderIn preserves hsgF image nonempty nondelegating spawns).midHistoryIn
      trace admitted capabilities rewards inv K image
  change steps = trace.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  intro f member
  exact replay f (observed ▸ member)

/-- Code-only specialization: installation suffices when no storage property is requested. -/
theorem MidHistoryTraceIn.settled_ownCode_of_imageIn (sem : CodeSem) (ca : Adr)
    {F : Fork → Prop} {C : ByteArray} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F)
    (installed : some (start.state.getCode ca).toList = sem.image)
    (K : InstalledCert C) (image : sem.image = some C.toList)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  have admitted : trace.FrameAdmitted ca (fun _ _ => True) :=
    (trace.frameAdmitted_iff_rawFrames ca _).2 fun _ _ _ => trivial
  have preserves :
      (ContractSpecSem.ofStorageOnly sem (fun _ => True)).PreservesAdmittedIn
        F ca (fun _ _ => True) :=
    fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩
  exact trace.settled_ownCodeIn preserves capabilities capabilities.stateGas_none admitted
    (trace.rewardCreditsFunded capabilities) ⟨installed, trivial, trivial⟩ K image
    nonempty nondelegating spawns

end Blanc.ExecutionTrace
