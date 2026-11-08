import Blanc.ExecutionWarmth
import Blanc.ExecutionTraceAdmission
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionTraceFrames

/-!
# Warmth of the frames a transaction enters

Every transaction pre-warms every precompile of the active rules (EIP-2929), and the accessed set
of a frame only grows (`Blanc/ExecutionWarmth.lean`).  So every frame entered by a transaction's
message, including those of subtrees that later revert, starts with every precompile warm.  A
system message starts with an empty set (`processSystemTransactionMsg`, on the covered forks that
have no state gas), so nothing is claimed of its frames.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- A retained slot whose frame's message carries `a` in its accessed set enters only frames that
start with `a` warm. -/
theorem RetainedXlot.rawFrames_warm
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (hsg : frame.inner.benv.stat.rules.stateGas = Option.none)
    (ha : a ∈ frame.inner.accessedAddresses) :
    ∀ root ∈ retained.rawFrames, a ∈ root.devm.accessedAddresses := by
  cases retained with
  | none => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      obtain ⟨benv, _, hevm⟩ := Frame.enter_run_inv henter
      have hstat := Frame.enter_run_benvStat henter
      have hpre : a ∈ pre.accessedAddresses := by
        have h : (⟨pc, sevm, pre⟩ : Evm) = initEvm (frame.inner.withBenv benv) := by
          simpa only using hevm
        cases h
        exact ha
      exact Exec.rawFrameRoots_warm a run (by rw [hstat]; exact hsg) hpre

theorem ProcessMessageTrace.rawFrames_warm
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (trace : ProcessMessageTrace msg out)
    (hsg : msg.benv.stat.rules.stateGas = Option.none) (ha : a ∈ msg.accessedAddresses) :
    ∀ root ∈ trace.rawFrames, a ∈ root.devm.accessedAddresses :=
  RetainedXlot.rawFrames_warm trace.retained trace.run hsg ha

theorem ProcessCreateMessageTrace.rawFrames_warm
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (trace : ProcessCreateMessageTrace msg out)
    (hsg : msg.benv.stat.rules.stateGas = Option.none) (ha : a ∈ msg.accessedAddresses) :
    ∀ root ∈ trace.rawFrames, a ∈ root.devm.accessedAddresses :=
  RetainedXlot.rawFrames_warm trace.retained trace.run hsg ha

/-! ### The message wrappers -/

private theorem setDelegationStep_accessed
    {auth : Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationStep auth msg refund = .ok ⟨msg', refund'⟩) :
    ∀ a, a ∈ msg.accessedAddresses → a ∈ msg'.accessedAddresses := by
  unfold setDelegationStep at run
  dsimp only at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, _⟩
    exact fun _ h => h
  · split at run
    · simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, _⟩
      exact fun _ h => h
    · split at run
      · simp only [Except.ok.injEq, Prod.mk.injEq] at run
        rcases run with ⟨rfl, _⟩
        exact fun _ h => h
      · cases run
      · split at run
        · simp only [Except.ok.injEq, Prod.mk.injEq] at run
          rcases run with ⟨rfl, _⟩
          exact fun _ h => Std.HashSet.mem_insert.2 (Or.inr h)
        · split at run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            exact fun _ h => Std.HashSet.mem_insert.2 (Or.inr h)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            exact fun _ h => Std.HashSet.mem_insert.2 (Or.inr h)

private theorem setDelegationLoop_accessed
    {auths : List Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationLoop auths msg refund = .ok ⟨msg', refund'⟩) :
    ∀ a, a ∈ msg.accessedAddresses → a ∈ msg'.accessedAddresses := by
  induction auths generalizing msg refund with
  | nil =>
      unfold setDelegationLoop at run
      simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, _⟩
      exact fun _ h => h
  | cons auth auths ih =>
      unfold setDelegationLoop at run
      simp only [bind, Except.bind] at run
      split at run
      · cases run
      · rename_i pair step
        obtain ⟨stepMsg, stepRefund⟩ := pair
        exact fun a h => ih run a (setDelegationStep_accessed step a h)

private theorem setDelegation_accessed
    {msg delegated : Msg} {refund : B256}
    (run : setDelegation msg = .ok ⟨delegated, refund⟩) :
    ∀ a, a ∈ msg.accessedAddresses → a ∈ delegated.accessedAddresses := by
  unfold setDelegation at run
  rcases Except.bind_eq_ok run with
    ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩
  have grow := setDelegationLoop_accessed loop
  cases codeAddress : loopMsg.codeAddress with
  | none => simp only [codeAddress, Except.bind_error, reduceCtorEq] at rest
  | some address =>
      simp only [codeAddress, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at rest
      rcases rest with ⟨rfl, rfl⟩
      exact grow

/-- The EIP-7702 delegation prefix only warms addresses. -/
theorem messageCallDelegation_accessed
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    ∀ a, a ∈ msg.accessedAddresses → a ∈ delegated.accessedAddresses := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact fun _ h => h
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, delegatedRun, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact setDelegation_accessed delegatedRun

/-- Resolving delegated code only warms the delegate. -/
theorem messageCallExecutionMessage_accessed (msg : Msg) :
    ∀ a, a ∈ msg.accessedAddresses → a ∈ (messageCallExecutionMessage msg).accessedAddresses := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  split
  · exact fun _ h => h
  · exact fun _ h => Std.HashSet.mem_insert.2 (Or.inr h)

/-- **Every frame a settled message call enters starts with `a` warm**, whenever the message
itself carries `a` in its accessed set. -/
theorem MessageCallTrace.rawFrames_warm
    {msg : Msg} {state : State} {out : MsgCallOutput} {a : Adr}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = Option.none) (ha : a ∈ msg.accessedAddresses) :
    ∀ root ∈ trace.rawFrames, a ∈ root.devm.accessedAddresses := by
  cases trace with
  | createCollision => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | createRun target collision evm core coreTrace result =>
      exact coreTrace.rawFrames_warm hsg ha
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      subst execMsgEq
      refine coreTrace.rawFrames_warm ?_
        (messageCallExecutionMessage_accessed delegated a
          (messageCallDelegation_accessed delegation a ha))
      rw [messageCallExecutionMessage_benv_stat delegated,
        messageCallDelegation_benv_stat delegation]
      exact hsg

/-! ### Transactions -/

/-- EIP-2929: a prepared transaction message has every active precompile warm. -/
theorem prepareMessage_precompile_accessed {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h : prepareMessage benv tenv tx = .ok msg) {a : Adr}
    (ha : a ∈ benv.stat.rules.precompiles) : a ∈ msg.accessedAddresses := by
  unfold prepareMessage at h
  split at h
  all_goals
    dsimp only at h
    obtain rfl := Except.ok.inj h
    exact Std.HashSet.mem_insertMany_list.2
      (Or.inr (List.contains_iff_mem.2 (List.mem_append_left _ ha)))

/-! ### Bodies and histories -/

/-- The frames entered by a block's system messages, which start cold on the covered forks. -/
def AppliedBodyTrace.systemRawFrames
    (trace : AppliedBodyTrace benv txs ommers wds state bout) : List Exec.Deriv :=
  trace.beacon.rawFrames ++ trace.history.rawFrames ++ trace.requests.rawFrames

def ConfiguredBlockTrace.systemRawFrames
    (trace : ConfiguredBlockTrace cfg pre post) : List Exec.Deriv :=
  trace.bodyTrace.systemRawFrames

def ConfiguredHistoryTrace.systemRawFrames :
    ConfiguredHistoryTrace cfg checkpoint future → List Exec.Deriv
  | .refl _ _ _ => []
  | .step prior block => prior.systemRawFrames ++ block.systemRawFrames

/-- The frames of the transactions of a configured history. -/
def ConfiguredHistoryTrace.txRawFrames :
    ConfiguredHistoryTrace cfg checkpoint future → List Exec.Deriv
  | .refl _ _ _ => []
  | .step prior block => prior.txRawFrames ++ block.bodyTrace.transactions.rawFrames

end ExecutionTrace

end Blanc
