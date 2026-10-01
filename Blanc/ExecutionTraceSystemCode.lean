import Blanc.SystemContracts
import Blanc.ExecutionTraceSystem
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionTraceCodeKeep

/-!
# System frames that run canonical code enter no other frame

`Blanc/ExecutionTraceSystem.lean` confines the frames of a system message to the message's own
target when the code of *every* frame it enters is `SpawnFree`.  That premise names all the frames
and is offset-blind (false of the canonical EIP-7002 code).  This module states the message-level
fact in terms of the one code the system message actually starts from, and with the
reachability-aware `SpawnFreeReach`.
-/

namespace Blanc

open Jaune

theorem Exec.rawFrameRoots_of_reach {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out)
    (hb : noPushBefore sevm.code pc 32 = true) (h : SpawnFreeReach sevm.code) :
    ∀ root ∈ Exec.rawFrameRoots run, root.sevm = sevm := by
  intro root member
  simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants_eq_nil_of_reach run hb h,
    List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  rfl

namespace ExecutionTrace

/-- If the code a retained frame starts from is spawn-free at reachable positions, every frame the
slot entered runs on that frame's static machine, in particular targets that frame's target. -/
theorem RetainedXlot.rawFrames_target_of_reach {slot : Xlot} (retained : RetainedXlot slot)
    {t : Adr} {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (hrun : RunFrame frame slot out) (hcode : SpawnFreeReach frame.inner.code)
    (ht : frame.inner.currentTarget = t) :
    ∀ root ∈ retained.rawFrames, root.sevm.currentTarget = t := by
  cases retained with
  | none => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hpc : pc = 0 := Frame.enter_run_pc henter
      have hsevm : sevm.code = frame.inner.code := Frame.enter_run_code henter
      intro root member
      have := Exec.rawFrameRoots_of_reach run (by rw [hpc]; exact noPushBefore_zero _ _)
        (by rw [hsevm]; exact hcode) root member
      rw [this, Frame.enter_run_currentTarget henter]
      exact ht

/-- A settled call whose executed message runs spawn-free code enters only frames at the
message's target. -/
theorem MessageCallTrace.rawFrames_target_of_reach
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (htarget : msg.target.isNone = false)
    (hcode : ∀ delegated refund, messageCallDelegation msg = .ok ⟨delegated, refund⟩ →
      SpawnFreeReach (messageCallExecutionMessage delegated).code) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = msg.currentTarget := by
  cases trace with
  | createCollision => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | createRun target => simp only [htarget, Bool.false_eq_true] at target
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      subst execMsgEq
      refine RetainedXlot.rawFrames_target_of_reach coreTrace.retained coreTrace.run
        (hcode delegated refund delegation) ?_
      show (messageCallExecutionMessage delegated).currentTarget = msg.currentTarget
      rw [messageCallExecutionMessage_currentTarget]
      exact messageCallDelegation_currentTarget_eq delegation

/-- **A system message whose target holds spawn-free code enters no frame but its own.** -/
theorem SystemMessageTrace.rawFrames_target_of_code
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hreach : SpawnFreeReach (benv.state.getCode target))
    (hnd : ¬ isValidDelegation (benv.state.getCode target)) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = target := by
  have htarget : (systemTransactionMessage benv target data).target.isNone = false := by
    simp only [systemTransactionMessage, processSystemTransactionMsg, Option.isNone_some]
  refine trace.message.rawFrames_target_of_reach htarget ?_
  intro delegated refund hdel
  have hauths : (systemTransactionMessage benv target data).tenv.stat.auths.isEmpty = true := by
    simp only [systemTransactionMessage, processSystemTransactionMsg, processSystemTransactionTenv,
      Std.TreeMap.empty_eq_emptyc, List.isEmpty_nil]
  have hdelegated : delegated = systemTransactionMessage benv target data := by
    unfold messageCallDelegation at hdel
    simp only [hauths, ↓reduceIte] at hdel
    exact (Prod.mk.inj (Except.ok.inj hdel)).1.symm
  have hcode : (systemTransactionMessage benv target data).code = benv.state.getCode target := rfl
  have hnone : getDelegatedCodeAddress (systemTransactionMessage benv target data).code = none := by
    rw [hcode]
    have h : ¬ isValidDelegation (benv.state.getCode target) := hnd
    simp only [getDelegatedCodeAddress, h, ↓reduceIte]
  subst hdelegated
  unfold messageCallExecutionMessage
  rw [hnone]
  simpa only [hcode] using hreach

/-! ### The canonical code stays installed and its frames stay put -/

/-- The canonical code is installed in the state a system message runs in: the message enters no
frame but its own. -/
theorem SystemMessageTrace.rawFrames_target_of_installed
    {benv : Benv} {target : Adr} {c : ByteArray} {data : Bytes} {state : State}
    {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out)
    (hmem : (target, c) ∈ systemContracts) (installed : SystemCodeInstalled benv.state) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = target := by
  obtain ⟨hreach, hnd, -⟩ := systemContracts_facts _ hmem
  have hc : benv.state.getCode target = c := installed _ hmem
  refine trace.rawFrames_target_of_code ?_ ?_
  · rw [hc]; exact hreach
  · rw [hc]; exact hnd

/-- A system message keeps the canonical code installed when none of the frames it enters is a
CREATE at a system address. -/
theorem SystemMessageTrace.installed_keep
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    SystemCodeInstalled state := by
  intro p hp
  obtain ⟨hpost, -⟩ := trace.codeAt hfork (a := p.1) (avoid p hp)
  rw [hpost]
  exact installed p hp

/-- The requests keep the canonical code installed, and both request messages enter no frame but
their own. -/
theorem RequestsTrace.systemFrames_of_installed
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    (∀ root ∈ trace.rawFrames, root.sevm.currentTarget ∈ systemTargets) ∧
      SystemCodeInstalled state := by
  have avoidW : ∀ p ∈ systemContracts, ∀ root ∈ trace.withdrawal.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [RequestsTrace.rawFrames, List.mem_append]
      exact Or.inl member)
  have avoidC : ∀ p ∈ systemContracts, ∀ root ∈ trace.consolidation.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [RequestsTrace.rawFrames, List.mem_append]
      exact Or.inr member)
  have hW := trace.withdrawal.rawFrames_target_of_installed
    (c := withdrawalRequestCode) (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false, true_or, or_true]) installed
  have installedW := trace.withdrawal.installed_keep hfork installed avoidW
  have hC := trace.consolidation.rawFrames_target_of_installed
    (c := consolidationRequestCode) (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false, or_true]) installedW
  have installedC := trace.consolidation.installed_keep
    (benv := benv.withState trace.withdrawalState) hfork installedW avoidC
  refine ⟨?_, ?_⟩
  · intro root member
    simp only [RequestsTrace.rawFrames, List.mem_append] at member
    simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false]
    rcases member with member | member
    · exact Or.inr (Or.inr (Or.inl (hW root member)))
    · exact Or.inr (Or.inr (Or.inr (hC root member)))
  · rw [trace.state_eq_consolidationState]
    exact installedC

/-- **A block body that starts with the canonical system code installed ends with it, and every
frame of its system messages targets a system address**, when no frame it enters is a CREATE at a
system address, no authorization of its transactions recovers to one, and none was created in the
block. -/
theorem AppliedBodyTrace.systemFrames_of_installed
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (notCreated : ∀ p ∈ systemContracts, p.1 ∉ benv.createdAccounts)
    (hauth : ∀ p ∈ systemContracts, ∀ q ∈ trace.decodedTxs.putIndex, ∀ auth ∈ q.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ p.1)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    (∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ∈ systemTargets) ∧
      SystemCodeInstalled state := by
  have avoidBeacon : ∀ p ∈ systemContracts, ∀ root ∈ trace.beacon.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [AppliedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inl member)))
  have avoidHistory : ∀ p ∈ systemContracts, ∀ root ∈ trace.history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [AppliedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inr member)))
  have avoidTx : ∀ p ∈ systemContracts, ∀ root ∈ trace.transactions.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [AppliedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inr member))
  have avoidRequests : ∀ p ∈ systemContracts, ∀ root ∈ trace.requests.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [AppliedBodyTrace.rawFrames, List.mem_append]
      exact Or.inr member)
  -- the beacon-roots message, then the history-storage message
  have hBeacon := trace.beacon.rawFrames_target_of_installed
    (c := beaconRootsCode) (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false, true_or]) installed
  have installedBeacon := trace.beacon.installed_keep hfork installed avoidBeacon
  have hHistory := trace.history.rawFrames_target_of_installed
    (benv := benv.withState trace.beaconState) (c := historyStorageCode)
    (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
      true_or, or_true]) installedBeacon
  have installedHistory := trace.history.installed_keep
    (benv := benv.withState trace.beaconState) hfork installedBeacon avoidHistory
  -- the transactions
  have installedTx : SystemCodeInstalled trace.transactionBenv.state := by
    intro p hp
    obtain ⟨-, hnd, hne⟩ := systemContracts_facts p hp
    have hcode : ((benv.withState trace.beaconState).withState trace.historyState).state.getCode
        p.1 = p.2 := installedHistory p hp
    have := trace.transactions.codeAt_keep
      (benv := (benv.withState trace.beaconState).withState trace.historyState) hfork
      (hauth p hp) (avoidTx p hp) (by rw [hcode]; exact hne) (by rw [hcode]; exact hnd)
      (notCreated p hp)
    rw [this]
    exact hcode
  have hfork' : CoveredFork
      (trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds)).stat.fork := by
    change CoveredFork trace.transactionBenv.stat.fork
    rw [trace.transactions.stat_eq]
    exact hfork
  have installedWithdrawals : SystemCodeInstalled
      (trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds)).state := by
    intro p hp
    change (processWithdrawalsState trace.transactionBenv.state wds).getCode p.1 = p.2
    rw [processWithdrawalsState_getCode]
    exact installedTx p hp
  obtain ⟨hRequests, installedRequests⟩ :=
    trace.requests.systemFrames_of_installed hfork' installedWithdrawals avoidRequests
  refine ⟨?_, ?_⟩
  · intro root member
    simp only [AppliedBodyTrace.systemRawFrames, List.mem_append] at member
    rcases member with (member | member) | member
    · simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl (hBeacon root member)
    · simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inl (hHistory root member))
    · exact hRequests root member
  · rw [← trace.requestState_eq]
    exact installedRequests

theorem ConfiguredBlockTrace.systemFrames_of_installed
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) (installed : SystemCodeInstalled pre.state)
    (hauth : ∀ p ∈ systemContracts, ∀ q ∈ trace.bodyTrace.decodedTxs.putIndex,
      ∀ auth ∈ q.2.auths, ∀ authority, recoverAuthority auth = .ok authority →
        authority ≠ p.1)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    (∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ∈ systemTargets) ∧
      SystemCodeInstalled post.state := by
  obtain ⟨hframes, hstate⟩ := trace.bodyTrace.systemFrames_of_installed
    (by change CoveredFork trace.fork; exact trace.covered) installed
    (fun p _ => trace.not_mem_openingCreatedAccounts p.1) hauth avoid
  refine ⟨hframes, ?_⟩
  intro p hp
  rw [trace.postState]
  exact hstate p hp

/-- **A configured history that starts with the canonical system code installed ends with it, and
every frame of every system message it runs targets a system address**, when no frame it enters is
a CREATE at a system address and no authorization of its transactions recovers to one.  Both
premises are trace-local. -/
theorem ConfiguredHistoryTrace.systemFrames_of_installed
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : SystemCodeInstalled checkpoint.state)
    (hauth : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    (∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ∈ systemTargets) ∧
      SystemCodeInstalled future.state := by
  induction trace with
  | refl =>
      exact ⟨fun root member => by simp only [systemRawFrames, List.not_mem_nil] at member,
        installed⟩
  | step prior block ih =>
      obtain ⟨hprior, hpriorState⟩ := ih (fun p hp => (hauth p hp).1)
        (fun p hp root member => avoid p hp root (by
          simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append]
          exact Or.inl member))
      obtain ⟨hblock, hblockState⟩ := block.systemFrames_of_installed hpriorState
        (fun p hp => (hauth p hp).2)
        (fun p hp root member => avoid p hp root (by
          simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append]
          exact Or.inr member))
      refine ⟨fun root member => ?_, hblockState⟩
      simp only [ConfiguredHistoryTrace.systemRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hprior root member
      · exact hblock root member

end ExecutionTrace

end Blanc
