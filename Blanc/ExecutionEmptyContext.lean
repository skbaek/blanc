import Blanc.ExecutionNonceCode
import Blanc.ExecutionHistoryInCodeAt
import Blanc.ExecutionDeletionProvenance
import Blanc.ExecutionInRawNodeOrigin

/-!
# Frames in an empty-code storage context run empty code

If an account `a` holds empty code and no CREATE frame of an execution targets `a`, then every
reached node whose storage context is `a` runs empty code: a CALL into `a` loads `a`'s (empty,
hence non-designator) code, a CALLCODE or DELEGATECALL keeps its parent's context only from a
parent that is itself running code, and CREATE is excluded. Such a node decodes only
STOP, in particular no SELFDESTRUCT, so `a` is never scheduled for deletion.

This is the code-free counterpart of the nonempty-code invariants (`Devm.NoDel`,
`Exec.rawNodes_context_protected_noStateGas`): it applies to externally owned accounts and
to the SYSTEM address, whose code is empty.
-/

namespace Blanc

open Jaune

/-- The empty byte array is no EIP-7702 delegation designator. -/
theorem not_isValidDelegation_empty : ¬ isValidDelegation ByteArray.empty := by
  decide

/-- Empty code decodes only STOP, never SELFDESTRUCT. -/
theorem Linst.not_at_selfdestruct_of_size_zero {code : ByteArray} (empty : code.size = 0)
    (pc : Nat) : ¬ Linst.At code pc .selfdestruct := by
  simp only [Linst.At, ByteArray.getInst, empty, Nat.not_lt_zero, ↓reduceDIte,
    Option.some.injEq, Inst.last.injEq]
  decide

/-- An entered child whose storage context is `a` runs empty code, when its spawning node's
context `a` would run empty code, the child is no CREATE at `a`, and `a`'s code is empty at
the child's entry. -/
private theorem Evm.step_spawn_emptyContext_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume} {child : Evm} {a : Adr}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child)
    (parent : sevm.currentTarget = a → sevm.code.size = 0)
    (avoid : child.sta.codeAddress = none → child.sta.currentTarget ≠ a)
    (empty : child.dyna.getCode a = ByteArray.empty) :
    child.sta.currentTarget = a → child.sta.code.size = 0 := by
  intro target
  have parentCode : sevm.code.size ≠ 0 := by
    intro zero
    obtain ⟨x, atX, _, _⟩ := Evm.step_spawn_inv step
    simp only [Xinst.At, ByteArray.getInst, zero, Nat.not_lt_zero, ↓reduceDIte] at atX
    cases atX
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  have codeAddress : child.sta.codeAddress = frame.inner.codeAddress := by
    obtain ⟨benv, -, h⟩ := Frame.enter_run_inv enter
    rw [h]
    rfl
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, _⟩ |
    ⟨d, endowment, address, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, callTarget, callCodeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, hprefix₀, _, source, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · exact (avoid (codeAddress.trans (genericCreate.step_spawn_codeAddress spawn)) target).elim
  · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    have targetEq : child.sta.currentTarget = callTarget := Frame.enter_run_currentTarget enter
    rcases source with same | source
    · exact (parentCode (parent (same ▸ targetEq ▸ target))).elim
    · have entryCode : d₀.getCode a = ByteArray.empty := by
        rw [← empty, (Evm.step_spawn_child step enter).2.1 a]
        exact (hprefix₀.getCode a).symm
      rw [← targetEq, target] at source
      rw [Frame.enter_run_code enter, source (by rw [entryCode]; exact not_isValidDelegation_empty),
        entryCode]
      rfl

/-- Every reached node of an execution whose storage context is `a` runs empty code, when the
entry node does, and every entered child root avoids CREATE at `a` and sees empty code at
`a`. -/
private theorem Exec.rawNodes_emptyContext_of_descendants
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (roots : ∀ root ∈ Exec.rawFrameDescendants run,
      (root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) ∧
        root.devm.getCode a = ByteArray.empty)
    (entry : sevm.currentTarget = a → sevm.code.size = 0) :
    ∀ n ∈ Exec.rawNodes run, n.sevm.currentTarget = a → n.sevm.code.size = 0 := by
  induction run with
  | halt step =>
    intro n member
    simp only [Exec.rawNodes, List.mem_singleton] at member
    subst n
    exact entry
  | cont step next ih =>
    intro n member
    simp only [Exec.rawNodes, List.mem_cons] at member
    rcases member with rfl | member
    · exact entry
    · exact ih hsg (by simpa only [Exec.rawFrameDescendants] using roots) entry n member
  | doneErr step enter resumed =>
    intro n member
    simp only [Exec.rawNodes, List.mem_singleton] at member
    subst n
    exact entry
  | doneOk step enter resumed next ih =>
    intro n member
    simp only [Exec.rawNodes, List.mem_cons] at member
    rcases member with rfl | member
    · exact entry
    · exact ih hsg (by simpa only [Exec.rawFrameDescendants] using roots) entry n member
  | @runErr pc sevm pre frame resume pc' childEvm raw error step enter child resumed ih =>
    intro n member
    simp only [Exec.rawNodes, List.mem_cons] at member
    rcases member with rfl | member
    · exact entry
    · have self := roots ⟨childEvm.pc, childEvm.sta, childEvm.dyna, raw, child⟩
        (by simp only [Exec.rawFrameDescendants, List.mem_cons, true_or])
      exact ih (by rw [Evm.step_spawn_child_benvStat step enter]; exact hsg)
        (fun root inner => roots root (by
          simp only [Exec.rawFrameDescendants, List.mem_cons]
          exact Or.inr inner))
        (Evm.step_spawn_emptyContext_noStateGas hsg step enter entry self.1 self.2) n member
  | @runOk pc sevm pre frame resume pc' childEvm raw post out
      step enter child resumed next childIH nextIH =>
    intro n member
    simp only [Exec.rawNodes, List.mem_cons, List.mem_append] at member
    rcases member with rfl | inChild | inNext
    · exact entry
    · have self := roots ⟨childEvm.pc, childEvm.sta, childEvm.dyna, raw, child⟩
        (by simp only [Exec.rawFrameDescendants, List.mem_cons, true_or])
      exact childIH (by rw [Evm.step_spawn_child_benvStat step enter]; exact hsg)
        (fun root inner => roots root (by
          simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl inner)))
        (Evm.step_spawn_emptyContext_noStateGas hsg step enter entry self.1 self.2) n inChild
    · exact nextIH hsg
        (fun root inner => roots root (by
          simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr inner)))
        entry n inNext

/-- **Empty-code context nodes run empty code.** If `a` holds empty code at the entry of an
execution, no frame it enters is a CREATE at `a`, and the entry frame runs empty code when
its context is `a`, then every reached node in context `a` runs empty code. -/
theorem Exec.rawNodes_emptyContext_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (avoid : ∀ root ∈ Exec.rawFrameRoots run,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (empty : pre.getCode a = ByteArray.empty)
    (entry : sevm.currentTarget = a → sevm.code.size = 0) :
    ∀ n ∈ Exec.rawNodes run, n.sevm.currentTarget = a → n.sevm.code.size = 0 := by
  obtain ⟨-, codes⟩ := ExecutionTrace.Exec.codeAt_avoid_noStateGas run hsg avoid
  refine Exec.rawNodes_emptyContext_of_descendants run hsg (fun root member => ?_) entry
  have inRoots : root ∈ Exec.rawFrameRoots run := List.mem_cons_of_mem _ member
  exact ⟨avoid root inRoots, (codes root inRoots).trans empty⟩

/-- Consequently no reached node in context `a` executes SELFDESTRUCT. -/
theorem Exec.rawNodes_no_selfdestruct_of_emptyContext
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (avoid : ∀ root ∈ Exec.rawFrameRoots run,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (empty : pre.getCode a = ByteArray.empty)
    (entry : sevm.currentTarget = a → sevm.code.size = 0) :
    ∀ n ∈ Exec.rawNodes run,
      n.sevm.currentTarget = a → ¬ Linst.At n.sevm.code n.pc .selfdestruct :=
  fun n member target =>
    Linst.not_at_selfdestruct_of_size_zero
      (Exec.rawNodes_emptyContext_noStateGas run hsg avoid empty entry n member target) _

namespace ExecutionTrace

/-- A message that, in storage context `a` and with a code address, runs `a`'s code when that
code is empty. CREATE messages have no code address and are excluded by CREATE avoidance. -/
def MsgEmptyEntry (a : Adr) (msg : Msg) : Prop :=
  msg.currentTarget = a → msg.codeAddress ≠ Option.none →
    msg.benv.state.getCode a = ByteArray.empty → msg.code.size = 0

/-- A retained slot's committed root executes no SELFDESTRUCT in context `a`, at any retained
node, when `a`'s code is empty at message entry and no entered frame is a CREATE at `a`. -/
theorem RetainedXlot.settledRoots_no_selfdestruct_of_emptyContext
    {slot : Xlot} (retained : RetainedXlot slot)
    {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (process : RunFrame frame slot out)
    (hsg : frame.inner.benv.stat.rules.stateGas = Option.none)
    (avoid : ∀ root ∈ retained.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : frame.inner.benv.state.getCode a = ByteArray.empty)
    (entry : MsgEmptyEntry a frame.inner) :
    ∀ R ∈ retained.settledRoots, ∀ node ∈ Exec.retainedNodes R.run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
  cases retained with
  | none => intro R member; cases member
  | @some pc sevm pre execution run =>
    intro R member
    simp only [RetainedXlot.settledRoots] at member
    split at member
    · rw [List.mem_singleton] at member
      subst R
      have henter := (RunFrame.some_inv process).1
      have hroots : ∀ root ∈ Exec.rawFrameRoots run, root.sevm.codeAddress = Option.none →
          root.sevm.currentTarget ≠ a := avoid
      intro node retainedNode
      refine Exec.rawNodes_no_selfdestruct_of_emptyContext run
        (by rw [Frame.enter_run_benvStat henter]; exact hsg) hroots
        ((Frame.enter_run_getCode henter a).trans empty) ?_ node
        ((Exec.retainedNodes_sublist_rawNodes run).subset retainedNode)
      intro target
      by_cases address : sevm.codeAddress = Option.none
      · exact (hroots _ List.mem_cons_self address target).elim
      · rw [Frame.enter_run_code henter]
        apply entry ((Frame.enter_run_currentTarget henter).symm.trans target)
          (by rw [← Frame.enter_run_codeAddress henter]; exact address)
        exact empty
    · cases member

/-- A call message's committed root executes no SELFDESTRUCT in context `a`. -/
theorem ProcessMessageTrace.settledRoots_no_selfdestruct_of_emptyContext {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (trace : ProcessMessageTrace msg out) (hsg : msg.benv.stat.rules.stateGas = Option.none)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : msg.benv.state.getCode a = ByteArray.empty) (entry : MsgEmptyEntry a msg) :
    ∀ R ∈ trace.settledRoots, ∀ node ∈ Exec.retainedNodes R.run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
  rcases trace with ⟨slot, retained, process⟩
  have safe := retained.settledRoots_no_selfdestruct_of_emptyContext process hsg avoid empty entry
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · exact safe R member
    · cases member

/-- A create message's committed root executes no SELFDESTRUCT in context `a`. -/
theorem ProcessCreateMessageTrace.settledRoots_no_selfdestruct_of_emptyContext {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (trace : ProcessCreateMessageTrace msg out) (hsg : msg.benv.stat.rules.stateGas = Option.none)
    (hca : msg.codeAddress = Option.none)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : msg.benv.state.getCode a = ByteArray.empty) :
    ∀ R ∈ trace.settledRoots, ∀ node ∈ Exec.retainedNodes R.run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
  rcases trace with ⟨slot, retained, process⟩
  have safe := retained.settledRoots_no_selfdestruct_of_emptyContext process
    ((congrArg (fun stat : BenvStat => stat.rules.stateGas)
      (processCreateMessage.msg_benvStat msg)).trans hsg) avoid
    ((processCreateMessage.msg_getCode msg a).trans empty)
    (fun _ address => (address hca).elim)
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    · exact safe R member
    · cases member

/-- Code-delegation resolution of a message running its own target's code runs empty code at
a target whose code is empty. -/
theorem messageCallExecutionMessage_emptyEntry {msg : Msg} {a : Adr}
    (own : msg.code = msg.benv.state.getCode msg.currentTarget) :
    MsgEmptyEntry a (messageCallExecutionMessage msg) := by
  intro target _ empty
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation at target empty ⊢
  split
  · rename_i hnone
    rw [hnone] at target empty
    rw [own, target, empty]
    rfl
  · rename_i address hsome
    rw [hsome] at target empty
    exfalso
    apply not_isValidDelegation_empty
    rw [← empty, ← target, ← own]
    unfold ForkRules.delegatedCodeAddress at hsome
    split at hsome
    · unfold getDelegatedCodeAddress at hsome
      split at hsome
      · assumption
      · cases hsome
    · cases hsome

/-- **A message call never schedules the deletion of an empty-code account it never creates.**
If `a` holds empty code at message entry, no entered frame is a CREATE at `a`, and either
delegation is disabled or no authorization recovers to `a`, then no retained node in context
`a` executes SELFDESTRUCT. -/
theorem MessageCallTrace.settledRoots_no_selfdestruct_of_emptyContext {msg : Msg}
    {state : State} {out : MsgCallOutput} {a : Adr}
    (trace : MessageCallTrace msg state out) (hsg : msg.benv.stat.rules.stateGas = Option.none)
    (hca : msg.target.isNone = true → msg.codeAddress = Option.none) (own : MsgOwn msg)
    (hauth : msg.benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ msg.tenv.stat.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : msg.benv.state.getCode a = ByteArray.empty) :
    ∀ R ∈ trace.settledRoots, ∀ node ∈ Exec.retainedNodes R.run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
  cases trace with
  | createCollision => intro R member; cases member
  | createRun target collision evm core inner result =>
    exact inner.settledRoots_no_selfdestruct_of_emptyContext hsg (hca target) avoid empty
  | callRun target delegated refund delegation execMsg execEq evm core inner result =>
    have hsgExec : execMsg.benv.stat.rules.stateGas = Option.none := by
      rw [execEq, messageCallExecutionMessage_benv_stat,
        messageCallDelegation_benv_stat delegation]
      exact hsg
    have hcode : execMsg.benv.state.getCode a = msg.benv.state.getCode a := by
      rcases hauth with hdis | hauth
      · have hleg : messageCallDelegation msg = .ok ⟨msg, 0⟩ :=
          processMessageCall.legacyAuthorization_disabled msg hdis
        have hdel : delegated = msg :=
          (Prod.mk.inj (Except.ok.inj (hleg.symm.trans delegation))).1.symm
        rw [execEq, hdel]
        exact messageCallExecutionMessage_getCode msg a
      · rw [execEq, messageCallExecutionMessage_getCode]
        exact messageCallDelegation_getCode hauth delegation
    subst execEq
    exact inner.settledRoots_no_selfdestruct_of_emptyContext hsgExec avoid (hcode.trans empty)
      (messageCallExecutionMessage_emptyEntry (messageCallDelegation_own delegation target own))

/-- **A transaction never deletes an empty-code account it never creates.** If `a` holds
empty code at the transaction's start, no frame it enters is a CREATE at `a`, and either
delegation is disabled or none of its authorizations recovers to `a`, then `a` is not in the
transaction's deletion set. -/
theorem TransactionTrace.not_deleted_of_emptyContext
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = Option.none) {a : Adr}
    (hauth : benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
        authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a)
    (empty : benv.state.getCode a = ByteArray.empty) :
    a ∉ trace.messageOut.accountsToDelete := by
  have hbenv := prepareMessage_benv trace.prepared
  obtain ⟨htenv, hca⟩ := prepareMessage_fields trace.prepared
  have hmsgState : trace.msg.benv.state.getCode a = ByteArray.empty := by
    rw [hbenv]
    have h1 := State.subBal_getCode trace.debit (a := a)
    change trace.debitState.getCode a = _
    rw [h1]
    unfold State.getCode
    rw [State.incrNonce_get_code]
    exact empty
  have hmsgAuth : trace.msg.benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ trace.msg.tenv.stat.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a := by
    rcases hauth with hdis | hauth
    · exact Or.inl (by rw [hbenv]; exact hdis)
    · exact Or.inr (by
        rw [htenv]
        simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using hauth)
  exact trace.not_deleted_of_retained_terminals hsg
    (trace.message.settledRoots_no_selfdestruct_of_emptyContext (by rw [hbenv]; exact hsg) hca
      (prepareMessage_own_entry trace.prepared) hmsgAuth avoid hmsgState)

end ExecutionTrace

end Blanc
