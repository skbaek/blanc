import Blanc.ExecutionTraceWarmth

/-!
# Frames entered by code that never spawns

A frame whose code contains no CALL-family or CREATE-family instruction enters no child.  The
system contracts (EIP-4788 beacon roots, EIP-2935 history storage, EIP-7002 withdrawal requests,
EIP-7251 consolidation requests) are such code, so the only frame a system message enters is its
own: the one targeting the system address.  This module states that as an execution fact.
-/

namespace Blanc

open Jaune

/-- The code has no instruction that could spawn a child frame. -/
def SpawnFree (code : ByteArray) : Prop := ∀ pc x, ¬ Xinst.At code pc x

/-- A run of spawn-free code enters no descendant frame. -/
theorem Exec.rawFrameDescendants_eq_nil {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (h : SpawnFree sevm.code) :
    Exec.rawFrameDescendants run = [] := by
  induction run with
  | halt hstep => simp [Exec.rawFrameDescendants]
  | cont hstep next ih => simpa [Exec.rawFrameDescendants] using ih h
  | doneErr hstep henter hresume =>
      obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
      exact absurd hx (h _ x)
  | doneOk hstep henter hresume next ih =>
      obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
      exact absurd hx (h _ x)
  | runErr hstep henter child hresume ih =>
      obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
      exact absurd hx (h _ x)
  | runOk hstep henter child hresume next ihChild ihNext =>
      obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
      exact absurd hx (h _ x)

/-- The frames of a run of spawn-free code are the run's own root. -/
theorem Exec.rawFrameRoots_of_spawnFree {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) (h : SpawnFree sevm.code) :
    ∀ root ∈ Exec.rawFrameRoots run, root.sevm = sevm := by
  intro root member
  simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants_eq_nil run h, List.mem_cons,
    List.not_mem_nil, or_false] at member
  subst member
  rfl

namespace ExecutionTrace

/-- If the first frame a retained slot entered runs spawn-free code, every frame the slot entered
runs on that frame's static machine, in particular targets that frame's target. -/
theorem RetainedXlot.rawFrames_sevm_of_spawnFree {slot : Xlot} (retained : RetainedXlot slot)
    (h : ∀ root ∈ retained.rawFrames, SpawnFree root.sevm.code) {t : Adr}
    {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (hrun : RunFrame frame slot out) (ht : frame.inner.currentTarget = t) :
    ∀ root ∈ retained.rawFrames, root.sevm.currentTarget = t := by
  cases retained with
  | none => intro root member; simp [RetainedXlot.rawFrames] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hself : SpawnFree sevm.code :=
        h ⟨pc, sevm, pre, execution, run⟩ (by simp [RetainedXlot.rawFrames, Exec.rawFrameRoots])
      intro root member
      have := Exec.rawFrameRoots_of_spawnFree run hself root member
      rw [this, Frame.enter_run_currentTarget henter]
      exact ht

theorem messageCallExecutionMessage_currentTarget (msg : Msg) :
    (messageCallExecutionMessage msg).currentTarget = msg.currentTarget := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- A settled call whose entered frames run spawn-free code enters only frames at the message's
target. -/
theorem MessageCallTrace.rawFrames_target_of_spawnFree
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (htarget : msg.target.isNone = false)
    (h : ∀ root ∈ trace.rawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = msg.currentTarget := by
  cases trace with
  | createCollision => intro root member; simp [MessageCallTrace.rawFrames] at member
  | createRun target => simp [htarget] at target
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      subst execMsgEq
      refine RetainedXlot.rawFrames_sevm_of_spawnFree coreTrace.retained h coreTrace.run ?_
      show (messageCallExecutionMessage delegated).currentTarget = msg.currentTarget
      rw [messageCallExecutionMessage_currentTarget]
      exact messageCallDelegation_currentTarget_eq delegation

theorem SystemMessageTrace.rawFrames_target_of_spawnFree
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (h : ∀ root ∈ trace.rawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = target := by
  have htarget : (systemTransactionMessage benv target data).target.isNone = false := by
    simp [systemTransactionMessage, processSystemTransactionMsg]
  exact trace.message.rawFrames_target_of_spawnFree htarget h

/-- The four system-message targets of a block body. -/
def systemTargets : List Adr :=
  [beaconRootsAddress, historyStorageAddress, withdrawalRequestPredeployAddress,
    consolidationRequestPredeployAddress]

theorem AppliedBodyTrace.systemRawFrames_target_of_spawnFree
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (h : ∀ root ∈ trace.systemRawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ∈ systemTargets := by
  intro root member
  have hbeacon := trace.beacon.rawFrames_target_of_spawnFree
    (fun r m => h r (by simp only [AppliedBodyTrace.systemRawFrames, List.mem_append]; tauto))
  have hhistory := trace.history.rawFrames_target_of_spawnFree
    (fun r m => h r (by simp only [AppliedBodyTrace.systemRawFrames, List.mem_append]; tauto))
  have hwithdrawal := trace.requests.withdrawal.rawFrames_target_of_spawnFree
    (fun r m => h r (by
      simp only [AppliedBodyTrace.systemRawFrames, RequestsTrace.rawFrames, List.mem_append]
      tauto))
  have hconsolidation := trace.requests.consolidation.rawFrames_target_of_spawnFree
    (fun r m => h r (by
      simp only [AppliedBodyTrace.systemRawFrames, RequestsTrace.rawFrames, List.mem_append]
      tauto))
  simp only [AppliedBodyTrace.systemRawFrames, RequestsTrace.rawFrames, List.mem_append] at member
  simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false]
  rcases member with (member | member) | member | member
  · exact Or.inl (hbeacon root member)
  · exact Or.inr (Or.inl (hhistory root member))
  · exact Or.inr (Or.inr (Or.inl (hwithdrawal root member)))
  · exact Or.inr (Or.inr (Or.inr (hconsolidation root member)))

theorem ConfiguredHistoryTrace.systemRawFrames_target_of_spawnFree
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (h : ∀ root ∈ trace.systemRawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ∈ systemTargets := by
  induction trace with
  | refl => intro root member; simp [ConfiguredHistoryTrace.systemRawFrames] at member
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTrace.systemRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih (fun r m => h r (by
          simp only [ConfiguredHistoryTrace.systemRawFrames, List.mem_append]
          exact Or.inl m)) root member
      · exact block.bodyTrace.systemRawFrames_target_of_spawnFree
          (fun r m => h r (by
            simp only [ConfiguredHistoryTrace.systemRawFrames, List.mem_append]
            exact Or.inr m)) root member

end ExecutionTrace

end Blanc
