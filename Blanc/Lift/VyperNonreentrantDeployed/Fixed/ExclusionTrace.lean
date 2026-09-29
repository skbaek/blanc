import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exclusion
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionMessageAdmission

/-!
# V+ at transaction and history level

`vplus_exclusion` (`Exclusion.lean`) is stated for one execution
`R : Exec 0 sevm pre out` under the premise `hroot`: if the top frame is owned by `P`, it
runs the code stored at `P`.  Here the top-level executions are the ones the retained trace
carriers actually hold, and that premise is derived from the message that started them.

* **Message level** (`ProcessMessageTrace.vplus`, `ProcessCreateMessageTrace.vplus`): the
  root is `initEvm` of the message with its entry benv, so its target and code are the
  message's, and the entry state has the message's codes (a value transfer moves balances
  only).  A well-formed call message (`msg.code` is the code stored at its target) satisfies
  `hroot`; a CREATE root never runs at a `P` that holds code (collision check).
* **Transaction level** (`TransactionTrace.vplus`): `prepareMessage` sets `currentTarget`
  and `code := getCode target` of the debited state, so `hroot` holds of every prepared
  message; the world premises are about the transaction's opening state.  The EIP-7702
  delegation path is an explicit excluded case (`tx.auths = []`): a delegation rewrites the
  authorities' code before execution.
* **History level** (`ConfiguredHistoryTrace.vplus`): every raw frame root retained by a
  configured history is an execution `Exec 0 …` on a covered fork (derived from the trace),
  so `vplus_exclusion` applies to each one.  The world premises, the root's code identity
  and `HashAvoidIn` are per retained execution: none is derivable from the trace, since they
  constrain the world and the hashes an attacker chooses.

The conclusion is `VplusExcludes P R`, the conclusion of `vplus_exclusion` for the
execution `R`: no frame at or below a child spawned by a frame active between lock set and
release is a `P`-owned comparator frame reaching a guarded body.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed

open Jaune Blanc.LockExclusion
open Blanc.ExecutionTrace
open Jaune.Exec.Deriv (ParentPrefix)

/-- The conclusion of `vplus_exclusion` for the execution `R`: for every raw frame root `F`
active (`ActiveRel`) at a node `h` that spawns a child `c`, every raw frame root `G` at or
below `c` is not a `P`-owned comparator frame that reaches a guarded body start. -/
def VplusExcludes (P : Adr) {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec pc sevm pre out) : Prop :=
  ∀ F h c : Exec.Deriv, F ∈ Exec.rawFrameRoots R → ActiveRel P F h → Spawns h c →
    ∀ G : Exec.Deriv, G ∈ Exec.rawFrameRoots c.exc → ¬ lockL.Enters P G

/-- `vplus_exclusion` in the `VplusExcludes` form. -/
theorem vplus_excludes {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork) {P : Adr}
    (hP : pre.getCode P = forwarderCode curvePlainImpl847e ∨ pre.getCode P = code)
    (hI : pre.getCode curvePlainImpl847e = code)
    (hroot : sevm.currentTarget = P → sevm.code = pre.getCode P)
    (hash : lockL.HashAvoidIn P R) : VplusExcludes P R :=
  fun _ _ _ hF active spawn _ hG => vplus_exclusion R hfork hP hI hroot hash hF active spawn hG

/-! ## The retained interpreter execution of a message -/

/-- The exclusion for the interpreter execution a retained slot holds (nothing to say of an
empty slot: a precompile or an entry failure runs no frame). -/
def _root_.Blanc.ExecutionTrace.RetainedXlot.Vplus (P : Adr) :
    {slot : Xlot} → RetainedXlot slot → Prop
  | _, .none => True
  | _, .some run => lockL.HashAvoidIn P run → VplusExcludes P run

/-- **V+ for a call message's retained execution.**  `hroot` is the message's own
well-formedness (`msg.code` is the code stored at its target); the world premises are about
the message's opening state. -/
theorem _root_.Blanc.ExecutionTrace.ProcessMessageTrace.vplus {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (hfork : CoveredFork msg.benv.stat.fork) {P : Adr}
    (hP : msg.benv.state.getCode P = forwarderCode curvePlainImpl847e ∨
      msg.benv.state.getCode P = code)
    (hI : msg.benv.state.getCode curvePlainImpl847e = code)
    (hroot : msg.currentTarget = P → msg.code = msg.benv.state.getCode P) :
    trace.retained.Vplus P := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => trivial
  | @some pc sevm pre out run =>
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      simp only [Frame.ofCall] at transfer evmEq
      have same := benvAfterTransfer_ok_getCode transfer
      obtain ⟨rfl, rfl, rfl⟩ : pc = 0 ∧ sevm = initSevm (msg.withBenv entry) ∧
          pre = initDevm (msg.withBenv entry) := by
        have h := evmEq
        injection h with h1 h2 h3
        exact ⟨h1, h2, h3⟩
      have code_eq : ∀ a, (initDevm (msg.withBenv entry)).getCode a = msg.benv.state.getCode a :=
        fun a => same a
      intro hash
      refine vplus_excludes run ?_ ?_ ?_ (fun h => ?_) hash
      · rw [initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat transfer]
        exact hfork
      · rw [code_eq]; exact hP
      · rw [code_eq]; exact hI
      · rw [code_eq]; exact hroot h

/-- Both codes `P` may hold (the comparator, or the forwarder to it) are nonempty. -/
theorem holds_code_ne_nil {s : State} {P : Adr}
    (hP : s.getCode P = forwarderCode curvePlainImpl847e ∨ s.getCode P = code) :
    (s.getCode P).toList ≠ [] := by
  intro empty
  have size : (s.getCode P).size = 0 := by
    rw [ByteArray.size_eq_length_toList, empty]; rfl
  rcases hP with h | h <;> rw [h] at size
  · simp [forwarderCode, ByteArray.size] at size
  · rw [code_size] at size
    exact absurd size (by decide)

/-- **V+ for a CREATE message's retained execution.**  The message found no code or nonce at
its target (`hcollision`), so its root does not run at a `P` that holds code; the world
premises are about the message's opening state. -/
theorem _root_.Blanc.ExecutionTrace.ProcessCreateMessageTrace.vplus {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) (hfork : CoveredFork msg.benv.stat.fork)
    (hcollision : messageCreateCollision msg = false) {P : Adr}
    (hP : msg.benv.state.getCode P = forwarderCode curvePlainImpl847e ∨
      msg.benv.state.getCode P = code)
    (hI : msg.benv.state.getCode curvePlainImpl847e = code) :
    trace.retained.Vplus P := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => trivial
  | @some pc sevm pre out run =>
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
      simp only [Frame.ofCreate] at transfer evmEq
      have same := benvAfterTransfer_ok_getCode transfer
      have targetNe : msg.currentTarget ≠ P := by
        unfold messageCreateCollision at hcollision
        rw [Bool.or_eq_false_iff] at hcollision
        exact ne_wa_of_not_hasCodeOrNonce (holds_code_ne_nil hP) hcollision.1
      obtain ⟨rfl, rfl, rfl⟩ : pc = 0 ∧
          sevm = initSevm ((processCreateMessage.msg msg).withBenv entry) ∧
          pre = initDevm ((processCreateMessage.msg msg).withBenv entry) := by
        have h := evmEq
        injection h with h1 h2 h3
        exact ⟨h1, h2, h3⟩
      have code_eq : ∀ a, (initDevm ((processCreateMessage.msg msg).withBenv entry)).getCode a =
          msg.benv.state.getCode a := fun a =>
        (same a).trans (processCreateMessage.msg_getCode msg a)
      intro hash
      refine vplus_excludes run ?_ ?_ ?_ (fun h => ?_) hash
      · rw [initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat transfer,
          processCreateMessage.msg_benvStat]
        exact hfork
      · rw [code_eq]; exact hP
      · rw [code_eq]; exact hI
      · exact (targetNe h).elim

/-! ## A settled message call, and a transaction -/

/-- The exclusion for the interpreter core, if any, a settled message call retained. -/
def _root_.Blanc.ExecutionTrace.MessageCallTrace.Vplus (P : Adr) {msg : Msg} {state : State}
    {out : MsgCallOutput} : MessageCallTrace msg state out → Prop
  | .createCollision .. => True
  | .createRun _ _ _ _ core _ => core.retained.Vplus P
  | .callRun _ _ _ _ _ _ _ _ core _ => core.retained.Vplus P

/-- Neither code `P` may hold is an EIP-7702 delegation designator. -/
theorem holds_not_delegation {s : State} {P : Adr}
    (hP : s.getCode P = forwarderCode curvePlainImpl847e ∨ s.getCode P = code) :
    getDelegatedCodeAddress (s.getCode P) = none := by
  have notDelegation : ¬ isValidDelegation (s.getCode P) := by
    rintro ⟨size, -⟩
    rcases hP with h | h <;> rw [h] at size
    · simp [forwarderCode, ByteArray.size, eoaDelegatedCodeLength] at size
    · rw [code_size] at size
      simp [eoaDelegatedCodeLength] at size
  simp [getDelegatedCodeAddress, notDelegation]

/-- **V+ for a settled message call's retained execution.**  Without an EIP-7702
authorization list (`noAuths`; a delegation rewrites the authorities' code before the
frame runs, so that path is excluded here), the executed message is the call itself, and
its root is well formed (`hroot`: a call message's code is the code stored at its target,
at `P`). -/
theorem _root_.Blanc.ExecutionTrace.MessageCallTrace.vplus {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (hfork : CoveredFork msg.benv.stat.fork)
    {P : Adr}
    (hP : msg.benv.state.getCode P = forwarderCode curvePlainImpl847e ∨
      msg.benv.state.getCode P = code)
    (hI : msg.benv.state.getCode curvePlainImpl847e = code)
    (hroot : msg.target.isNone = false → msg.currentTarget = P →
      msg.code = msg.benv.state.getCode P)
    (noAuths : msg.tenv.stat.auths.isEmpty = true) :
    trace.Vplus P := by
  cases trace with
  | createCollision => trivial
  | createRun target collision evm core coreTrace result =>
      exact coreTrace.vplus hfork collision hP hI
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      have delegatedEq : delegated = msg := by
        unfold messageCallDelegation at delegation
        simp only [noAuths, ↓reduceIte] at delegation
        exact (congrArg Prod.fst (Except.ok.inj delegation)).symm
      subst delegatedEq
      subst execMsgEq
      have benvEq : (messageCallExecutionMessage delegated).benv = delegated.benv := by
        unfold messageCallExecutionMessage; split <;> rfl
      have targetEq : (messageCallExecutionMessage delegated).currentTarget =
          delegated.currentTarget := by
        unfold messageCallExecutionMessage; split <;> rfl
      refine coreTrace.vplus ?_ ?_ ?_ ?_
      · rw [benvEq]; exact hfork
      · rw [benvEq]; exact hP
      · rw [benvEq]; exact hI
      · intro h
        rw [targetEq] at h
        have code_eq := hroot target h
        have none_eq : getDelegatedCodeAddress delegated.code = none := by
          rw [code_eq]; exact holds_not_delegation hP
        have exec_eq : messageCallExecutionMessage delegated = delegated := by
          unfold messageCallExecutionMessage; rw [none_eq]
        rw [exec_eq]; exact code_eq

/-- The prepared message of a transaction: it keeps the transaction's authorization list, its
benv is the debited world, and a call's code is the code stored at its target in that world. -/
theorem _root_.Blanc.ExecutionTrace.TransactionTrace.prepared_facts {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    trace.msg.tenv.stat.auths = tx.auths ∧
      trace.msg.benv = { benv.beginTransaction with state := trace.debitState } ∧
      (trace.msg.target.isNone = false → trace.msg.code =
        trace.msg.benv.state.getCode trace.msg.currentTarget) := by
  have prepared := trace.prepared
  refine ⟨?_, prepareMessage_benv prepared, ?_⟩
  · unfold prepareMessage at prepared
    cases hrecv : tx.type.receiver? <;> simp [hrecv] at prepared <;> rw [← prepared] <;> rfl
  · unfold prepareMessage at prepared
    cases hrecv : tx.type.receiver? with
    | none => simp [hrecv] at prepared; rw [← prepared]; simp
    | some target =>
        simp [hrecv] at prepared
        rw [← prepared]
        intro _
        rfl

/-- **V+ for a transaction's top-level execution.**  The well-formed-root premise of
`vplus_exclusion` is not assumed: `prepareMessage` builds the message with
`currentTarget := target` and `code := getCode target` of the debited world, and the debit
(nonce bump, balance) leaves every code alone, so `hroot` holds of the retained root.  The
world premises are about the transaction's opening state; `HashAvoidIn` is stated of the
retained execution (`RetainedXlot.Vplus`).  A contract-creating transaction has no `P`-owned
root (its target is codeless), and the EIP-7702 path is excluded (`tx.auths = []`). -/
theorem _root_.Blanc.ExecutionTrace.TransactionTrace.vplus {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork) {P : Adr}
    (hP : benv.state.getCode P = forwarderCode curvePlainImpl847e ∨
      benv.state.getCode P = code)
    (hI : benv.state.getCode curvePlainImpl847e = code)
    (noAuths : tx.auths = []) :
    trace.message.Vplus P := by
  obtain ⟨auths, benvEq, rootCode⟩ := trace.prepared_facts
  have debit : ∀ a, trace.msg.benv.state.getCode a = benv.state.getCode a := by
    intro a
    rw [benvEq]
    exact (State.subBal_getCode trace.debit).trans State.incrNonce_get_code
  refine trace.message.vplus ?_ ?_ ?_ ?_ ?_
  · rw [benvEq]; simpa [Benv.beginTransaction] using hfork
  · rw [debit]; exact hP
  · rw [debit]; exact hI
  · intro isCall target
    rw [← target]
    exact rootCode isCall
  · rw [auths, noAuths]; rfl

/-! ## A configured history -/

/-- **V+ for every execution a configured history retains.**  Each raw frame root `R` of the
history (a message's top-level frame, or any frame entered below one, whatever its outcome or
settlement) is an execution `Exec 0 …` on a covered fork, both derived from the trace
(`ConfiguredHistoryTrace.rootEntry`).  Four things are stated per retained execution `R`
and cannot be derived from the trace: the world premises `hP`, `hI` (what code the storage
owner `P` and the implementation hold), the code identity of `R`'s own root `hroot`, and
`HashAvoidIn` of `R` (the hashes an attacker chooses).  The conclusion is
`vplus_exclusion`'s, for `R`. -/
theorem _root_.Blanc.ExecutionTrace.ConfiguredHistoryTrace.vplus {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {P : Adr}
    (R : Exec.Deriv) (member : R ∈ trace.rawFrames)
    (hP : R.devm.getCode P = forwarderCode curvePlainImpl847e ∨ R.devm.getCode P = code)
    (hI : R.devm.getCode curvePlainImpl847e = code)
    (hroot : R.sevm.currentTarget = P → R.sevm.code = R.devm.getCode P)
    (hash : lockL.HashAvoidIn P R.exc) : VplusExcludes P R.exc := by
  obtain ⟨pcZero, fork⟩ := trace.rootEntry R member
  obtain ⟨pc, sevm, pre, out, run⟩ := R
  dsimp only at pcZero fork hP hI hroot hash ⊢
  subst pcZero
  exact vplus_excludes run fork hP hI hroot hash

end Blanc.Lift.VyperNonreentrantDeployed.Fixed
