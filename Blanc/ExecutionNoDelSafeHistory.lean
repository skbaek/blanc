import Blanc.ExecutionNoDelProducer
import Blanc.ExecutionTraceCodeKeep
import Blanc.ExecutionHistoryInStateTrace
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionStagedFrames

/-!
# Safe-parametric no-deletion and code survival across configured In-histories

`Blanc/ExecutionNoDelTransaction.lean` and `Blanc/ExecutionNoDelHistory.lean`
prove no-deletion and code survival from an installed checked runtime
(`InstalledCert C`: certificate check, `callOnly`, `noSelfdestruct`, no
EIP-7702 designator, nonempty). A proxy runtime that `DELEGATECALL`s cannot
meet `callOnly`, so this module restates the same chain with the certificate
replaced by what the proofs actually consume:

* a raw safety premise over the retained raw runs of each trace, stated with
  the trace's own raw-frame enumeration (`RetainedXlot.rawFrames`,
  `MessageCallTrace.rawFrames`, …, `StagedBodyTrace.rawFrames`,
  `ConfiguredBlockTraceIn.rawFrames`, `ConfiguredHistoryTraceIn.rawFrames`)
  and `Exec.rawNodes`: `ExecutionTrace.SafeRawFrames wa trace.rawFrames`
  says every node of every listed frame's own execution excludes decoded
  `SELFDESTRUCT` in the executing storage context `wa`;
* the code facts the proofs actually use on the code `C` at `wa`
  (`C.toList ≠ []`, `¬ isValidDelegation C`), with `C` still the code proved
  to survive (`getCode wa = C` at every endpoint), not a fixed global image.

The leaf bridge `Exec.safeNodes_of_installedCert` turns the installed-cert
producer `Exec.safe_of_installedCert` into per-frame safety: every node of a
listed frame's execution is a node of the whole run
(`Exec.rawNodes_of_mem_rawFrameRoots`), so top-run safety covers it. Each
`…_of_installedCert` theorem is a wrapper over the matching `…_of_safe`
theorem via its trace's `safeRawFrames_of_installedCert` bridge.
-/

namespace Blanc

open Jaune

/-- Raw terminal safety of one execution: every reached node in the executing
storage context `wa` excludes decoded `SELFDESTRUCT`. This is the `safe`
premise of `Exec.inv_noDel_of_raw_terminal_safe`, named for reuse. -/
def Exec.SafeNodes (wa : Adr) {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : Prop :=
  ∀ node ∈ Exec.rawNodes run,
    node.sevm.currentTarget = wa →
    ¬ Linst.At node.sevm.code node.pc .selfdestruct

/-- Every node of a listed frame's own execution is a node of the whole run.
Induction over the driver tree: the listed root is the run itself, a child
root's nodes sit in the child's chronology segment, and deeper descendants
are covered by the induction hypotheses. -/
theorem Exec.rawNodes_of_mem_rawFrameRoots
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (R : Exec.Deriv)
    (hR : R ∈ Exec.rawFrameRoots run) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ Exec.rawNodes run := by
  revert R hR node hn
  induction run with
  | halt hstep =>
      intro R hR node hn
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at hR
      subst hR
      exact hn
  | cont hstep next ih =>
      intro R hR node hn
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at hR
      rcases hR with rfl | hR
      · exact hn
      · have hR' : R ∈ Exec.rawFrameRoots next := List.mem_cons_of_mem _ hR
        have hmem := ih R hR' node hn
        simp only [Exec.rawNodes]
        exact List.mem_cons_of_mem _ hmem
  | doneErr hstep henter hresume =>
      intro R hR node hn
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at hR
      subst hR
      exact hn
  | doneOk hstep henter hresume next ih =>
      intro R hR node hn
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at hR
      rcases hR with rfl | hR
      · exact hn
      · have hR' : R ∈ Exec.rawFrameRoots next := List.mem_cons_of_mem _ hR
        have hmem := ih R hR' node hn
        simp only [Exec.rawNodes]
        exact List.mem_cons_of_mem _ hmem
  | runErr hstep henter child hresume ih =>
      intro R hR node hn
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at hR
      rcases hR with rfl | hR
      · exact hn
      · rcases hR with rfl | hR
        · simp only [Exec.rawNodes]
          exact List.mem_cons_of_mem _ hn
        · have hR' : R ∈ Exec.rawFrameRoots child := List.mem_cons_of_mem _ hR
          have hmem := ih R hR' node hn
          simp only [Exec.rawNodes]
          exact List.mem_cons_of_mem _ hmem
  | runOk hstep henter child hresume next ihc ihn =>
      intro R hR node hn
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at hR
      rcases hR with rfl | hR
      · exact hn
      · rcases hR with rfl | hR
        · simp only [Exec.rawNodes]
          exact List.mem_cons_of_mem _ (List.mem_append_left _ hn)
        · rcases hR with hR | hR
          · have hR' : R ∈ Exec.rawFrameRoots child := List.mem_cons_of_mem _ hR
            have hmem := ihc R hR' node hn
            simp only [Exec.rawNodes]
            exact List.mem_cons_of_mem _ (List.mem_append_left _ hmem)
          · have hR' : R ∈ Exec.rawFrameRoots next := List.mem_cons_of_mem _ hR
            have hmem := ihn R hR' node hn
            simp only [Exec.rawNodes]
            exact List.mem_cons_of_mem _ (List.mem_append_right _ hmem)

/-- **Per-frame safety from an installed checked runtime.** Top-run safety
(`Exec.safe_of_installedCert`) covers every node of every listed frame's own
execution, since those nodes are nodes of the whole run. This is the leaf
bridge used by every trace-level `safeRawFrames_of_installedCert`. -/
theorem Exec.safeNodes_of_installedCert {wa : Adr} {C : ByteArray} {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (installed : pre.getCode wa = C) (hCne : C.toList ≠ [])
    (root : sevm.currentTarget = wa → pc = 0 ∧ sevm.code = C) :
    ∀ R ∈ Exec.rawFrameRoots run, Exec.SafeNodes wa R.exc := by
  intro R hR node hn htgt
  exact Exec.safe_of_installedCert hc callOnly noSelfdestruct hCdel run hsg installed
    hCne root node (Exec.rawNodes_of_mem_rawFrameRoots run R hR node hn) htgt

/-- Proof-of-work rewards only credit balances. -/
theorem payRewards_getCode (pow : PowRules) (number : Nat) (coinbase : Adr)
    (ommers : List Header) (st : State) (a : Adr) :
    (payRewards pow number coinbase ommers st).getCode a = st.getCode a := by
  unfold payRewards
  suffices h : ∀ (os : List Header) (s : State),
      (os.foldl (fun acc ommer => acc.addBal ommer.coinbase
        ((8 + ommer.number - number) * pow.blockReward / 8).toB256) s).getCode a = s.getCode a by
    rw [h, State.addBal_getCode]
  intro os
  induction os with
  | nil => intro s; rfl
  | cons o os ih =>
      intro s
      rw [List.foldl_cons, ih, State.addBal_getCode]

/-- A filled slot keeps every nonempty code (fork-free). -/
theorem Xlot.invGetCode_of_filled {xl : Xlot} (filled : xl.Filled) : Xlot.InvGetCode xl := by
  apply Xlot.invGetCode_of_rel
  rcases xl with _ | ⟨evm, raw⟩
  · trivial
  · obtain ⟨exc⟩ := filled
    exact Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
      Ninst.codePreserve_effectRec Jinst.codePreserve_effect Linst.codePreserve_effect exc

/-- Removing touched empty accounts never removes an account with nonempty code. -/
theorem sweepTouchedAccounts_getCode_of_nonempty (rules : ForkRules) (addresses : List Adr)
    {state : State} {a : Adr} (h : (state.getCode a).toList ≠ []) :
    (sweepTouchedAccounts rules addresses state).getCode a = state.getCode a := by
  unfold sweepTouchedAccounts
  split
  · induction addresses generalizing state with
    | nil => rfl
    | cons x xs ih =>
      rw [List.foldl_cons]
      split
      · rename_i hempty
        have hne : x ≠ a := by
          rintro rfl
          apply h
          have hsize : (state.getCode x).size = 0 := hempty.2.1
          rw [ByteArray.size_eq_length_toList] at hsize
          exact List.eq_nil_of_length_eq_zero hsize
        have hcode := ExecutionTrace.destroyAccount_getCode_ne (w := state) hne
        rw [ih (by rw [hcode]; exact h), hcode]
      · exact ih h
  · rfl

/-! ## Raw message cores -/

/-- A filled frame slot meets its no-deletion obligation from raw safety of an
explicitly given retained run (with its slot equation). The installed code
facts are not needed here: only `stateGas = none` reaches the core. -/
theorem RunFrame.invNoDel_of_safe {wa : Adr}
    {f : Frame} {xl : Xlot} {r : Except (EvmError × State × AdrSet × Tra) Devm}
    {evm : Evm} {exn : Execution} (e : xl = .some ⟨evm, exn⟩)
    (exc : Exec evm.pc evm.sta evm.dyna exn)
    (run : RunFrame f xl r)
    (hsg : f.inner.benv.stat.rules.stateGas = none)
    (safe : Exec.SafeNodes wa exc) :
    Xlot.InvNoDel wa xl := by
  subst e
  obtain ⟨henter, -⟩ := RunFrame.some_inv run
  intro hnd
  exact Exec.inv_noDel_of_raw_terminal_safe exc
    (by rw [Frame.enter_run_benvStat henter]; exact hsg)
    safe hnd

/-- **Raw call-message no-deletion from explicit raw safety**, every outcome
(including error payloads and the rollback snapshot). -/
theorem ProcessMessage.inv_noDel_of_safe {wa : Adr}
    {msg : Msg} {xl : Xlot} {ex : Except (EvmError × State × AdrSet × Tra) Devm}
    {evm : Evm} {exn : Execution} (e : xl = .some ⟨evm, exn⟩)
    (exc : Exec evm.pc evm.sta evm.dyna exn)
    (run : ProcessMessage msg xl ex)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions)
    (safe : Exec.SafeNodes wa exc) :
    MsgResult.NoDel wa ex :=
  ProcessMessage.inv_noDel
    (RunFrame.invNoDel_of_safe e exc run hsg safe)
    run h h_inherited

/-- **Raw create-message no-deletion from explicit raw safety**, every outcome,
for a create not targeting `wa`. -/
theorem ProcessCreateMessage.inv_noDel_of_safe {wa : Adr}
    {msg : Msg} {xl : Xlot} {ex : Except (EvmError × State × AdrSet × Tra) Devm}
    {evm : Evm} {exn : Execution} (e : xl = .some ⟨evm, exn⟩)
    (exc : Exec evm.pc evm.sta evm.dyna exn)
    (run : ProcessCreateMessage msg xl ex)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions)
    (safe : Exec.SafeNodes wa exc) :
    MsgResult.NoDel wa ex :=
  ProcessCreateMessage.inv_noDel
    (RunFrame.invNoDel_of_safe e exc run
      (by rw [show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
        processCreateMessage.msg_benvStat]; exact hsg)
      safe)
    run h_ct h h_inherited

namespace ExecutionTrace

/-- Raw safety over a trace's own raw-frame enumeration: every node of every
listed frame's own execution excludes decoded `SELFDESTRUCT` in the executing
storage context `wa`. This is the safety premise replacing `InstalledCert`
at every level of the chain below. -/
def SafeRawFrames (wa : Adr) (roots : List Exec.Deriv) : Prop :=
  ∀ R ∈ roots, Exec.SafeNodes wa R.exc

theorem SafeRawFrames.nil (wa : Adr) : SafeRawFrames wa [] := by
  intro R hR
  exact False.elim (List.not_mem_nil hR)

theorem SafeRawFrames.append {wa : Adr} {l₁ l₂ : List Exec.Deriv}
    (h₁ : SafeRawFrames wa l₁) (h₂ : SafeRawFrames wa l₂) :
    SafeRawFrames wa (l₁ ++ l₂) := by
  intro R hR
  rcases List.mem_append.mp hR with h | h
  · exact h₁ R h
  · exact h₂ R h

theorem SafeRawFrames.of_append_left {wa : Adr} {l₁ l₂ : List Exec.Deriv}
    (h : SafeRawFrames wa (l₁ ++ l₂)) : SafeRawFrames wa l₁ :=
  fun R hR => h R (List.mem_append.mpr (Or.inl hR))

theorem SafeRawFrames.of_append_right {wa : Adr} {l₁ l₂ : List Exec.Deriv}
    (h : SafeRawFrames wa (l₁ ++ l₂)) : SafeRawFrames wa l₂ :=
  fun R hR => h R (List.mem_append.mpr (Or.inr hR))

/-- No retained transaction of the list schedules `wa` for deletion. -/
def ApplyTransactionsTrace.NoDelScheduled (wa : Adr) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → Prop
  | _, _, _, _, _, .nil _ _ => True
  | _, _, _, _, _, .cons head tail =>
      wa ∉ head.messageOut.accountsToDelete ∧ tail.NoDelScheduled wa

/-- No selected transaction of a retained block schedules `wa` for deletion. -/
def ConfiguredBlockTraceIn.NoDelScheduled {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post) (wa : Adr) : Prop :=
  trace.bodyTrace.transactions.NoDelScheduled wa

/-- No selected transaction of any block of a retained history schedules `wa` for deletion. -/
def ConfiguredHistoryTraceIn.NoDelScheduled {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} (wa : Adr) :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.NoDelScheduled wa ∧ block.NoDelScheduled wa

/-- The create arm settles at the core state and schedules the core's deletions only on
success. -/
private theorem processMessageCall_createRun_noDel {wa : Adr}
    {msg : Msg} {evm : Devm} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = false)
    (core : processCreateMessage msg = .ok evm)
    (result : processMessageCall msg = .ok ⟨state, out⟩)
    (hnd : wa ∉ evm.accountsToDelete) :
    state = evm.state ∧ wa ∉ out.accountsToDelete := by
  unfold processMessageCall at result
  simp only [target, ↓reduceIte] at result
  unfold processMessageCall.create at result
  rw [hsg] at result
  unfold messageCreateCollision at collision
  simp only [collision, bind, Except.bind] at result
  rcases Except.bind_eq_ok result with ⟨actual, actualMap, tail⟩
  have actualEq : actual = evm := Except.ok.inj
    ((Except.bimap_id_eq_ok actualMap).symm.trans core)
  subst actual
  split at tail
  · rcases Except.bind_eq_ok tail with ⟨_, _, output⟩
    have hout := Prod.mk.inj (Except.ok.inj output)
    refine ⟨hout.1.symm, ?_⟩
    rw [← hout.2]
    exact hnd
  · have hout := Prod.mk.inj (Except.ok.inj tail)
    refine ⟨hout.1.symm, ?_⟩
    rw [← hout.2]
    exact AdrSet.not_mem_empty

/-- The call arm settles at the core state and schedules the core's deletions only on success. -/
private theorem processMessageCall_callRun_noDel {wa : Adr}
    {msg delegated execMsg : Msg} {refund : Nat}
    {evm : Devm} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (target : msg.target.isNone = false)
    (delegation : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (execMsgEq : execMsg = messageCallExecutionMessage delegated)
    (core : processMessage execMsg = .ok evm)
    (result : processMessageCall msg = .ok ⟨state, out⟩)
    (hnd : wa ∉ evm.accountsToDelete) :
    state = evm.state ∧ wa ∉ out.accountsToDelete := by
  unfold processMessageCall at result
  simp only [target, Bool.false_eq_true, ↓reduceIte] at result
  unfold processMessageCall.call at result
  simp only [hsg] at result
  rw [show processMessageCall.legacyAuthorization msg = .ok ⟨delegated, refund⟩ from delegation]
    at result
  simp only [Except.bind_ok] at result
  have coreExec : processMessage (messageCallExecutionMessage delegated) = .ok evm :=
    (congrArg processMessage execMsgEq).symm.trans core
  rcases Except.bind_eq_ok result with ⟨actual, actualMap, tail⟩
  have actualEq : actual = evm := Except.ok.inj
    ((Except.bimap_id_eq_ok actualMap).symm.trans coreExec)
  subst actual
  split at tail
  · rcases Except.bind_eq_ok tail with ⟨_, _, output⟩
    have hout := Prod.mk.inj (Except.ok.inj output)
    refine ⟨hout.1.symm, ?_⟩
    rw [← hout.2]
    exact hnd
  · have hout := Prod.mk.inj (Except.ok.inj tail)
    refine ⟨hout.1.symm, ?_⟩
    rw [← hout.2]
    exact AdrSet.not_mem_empty

/-- The EIP-7702 authorization prefix keeps `wa`'s undesignated nonempty code, its creation and
inherited-deletion exclusions, and the executing message's own-code relation. -/
private theorem messageCallDelegation_installed {wa : Adr} {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (h : Msg.NoDel wa msg) (hnd : ¬ isValidDelegation (msg.benv.state.getCode wa))
    (h_inherited : wa ∉ msg.inheritedDeletions)
    (address : msg.codeAddress = some msg.currentTarget)
    (own : msg.code = msg.benv.state.getCode msg.currentTarget) :
    Msg.NoDel wa delegated ∧
      delegated.benv.state.getCode wa = msg.benv.state.getCode wa ∧
      wa ∉ delegated.inheritedDeletions ∧
      delegated.code = delegated.benv.state.getCode delegated.currentTarget := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, -⟩
    exact ⟨h, rfl, h_inherited, own⟩
  · obtain ⟨⟨middle, counter⟩, hdel, rest⟩ := Except.bind_eq_ok run
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, -⟩
    refine ⟨setDelegation_msg_noDel hdel h hnd, (setDelegation_benv_equiv hdel).2 wa h.code hnd,
      (setDelegation_inheritedDeletions hdel) ▸ h_inherited, ?_⟩
    unfold setDelegation at hdel
    obtain ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩ := Except.bind_eq_ok hdel
    have fields := setDelegationLoop_fields loop
    have loopAddress : loopMsg.codeAddress = some loopMsg.currentTarget := by
      rw [fields.2.2.2.2.2, address, fields.2.2.1]
    simp only [loopAddress, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, _⟩
    rfl

/-- Code-delegation resolution keeps the installed undesignated code at a message to `wa`. -/
private theorem messageCallExecutionMessage_code_installed {wa : Adr} {C : ByteArray} {m : Msg}
    (own : m.code = m.benv.state.getCode m.currentTarget)
    (installed : m.benv.state.getCode wa = C) (hCdel : ¬ isValidDelegation C) :
    (messageCallExecutionMessage m).currentTarget = wa →
      (messageCallExecutionMessage m).code = C := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  split
  · intro htgt
    rw [own, htgt, installed]
  · rename_i address resolved
    intro htgt
    have code : m.code = C := by rw [own, htgt, installed]
    have none : getDelegatedCodeAddress C = Option.none := by
      simp only [getDelegatedCodeAddress, hCdel, ↓reduceIte]
    simp only [ForkRules.delegatedCodeAddress, code, none, ite_self, reduceCtorEq] at resolved

/-- A transaction's top-level message runs its call target's own code. -/
private theorem prepareMessage_own {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h : prepareMessage benv tenv tx = .ok msg) :
    msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget := by
  intro htarget
  unfold prepareMessage at h
  rcases hr : tx.type.receiver? with _ | target
  · simp only [hr] at h
    obtain rfl := Except.ok.inj h
    simp only [Option.isNone_none, Bool.true_eq_false] at htarget
  · simp only [hr] at h
    obtain rfl := Except.ok.inj h
    exact ⟨rfl, rfl⟩

/-! ## Retained message traces -/

/-- **Retained call-message no-deletion from trace safety**, every outcome. An
empty retention needs no safety; a retained run carries it via its frame
roots. -/
theorem ProcessMessageTrace.inv_noDel_of_safe {wa : Adr}
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions)
    (safe : SafeRawFrames wa trace.rawFrames) :
    MsgResult.NoDel wa out := by
  rcases trace with ⟨slot, retained, run⟩
  cases retained with
  | none =>
      have obl : Xlot.InvNoDel wa .none := by trivial
      exact ProcessMessage.inv_noDel obl run h h_inherited
  | @some pc sevm pre raw run' =>
      have safeTop : Exec.SafeNodes wa run' :=
        fun node hn htgt =>
          safe _ (Exec.mem_rawFrameRoots_self run') node hn htgt
      exact ProcessMessage.inv_noDel
        (RunFrame.invNoDel_of_safe (e := rfl) run' run hsg safeTop)
        run h h_inherited

/-- **Retained create-message no-deletion from trace safety**, every outcome,
for a create not targeting `wa`. -/
theorem ProcessCreateMessageTrace.inv_noDel_of_safe {wa : Adr}
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions)
    (safe : SafeRawFrames wa trace.rawFrames) :
    MsgResult.NoDel wa out := by
  rcases trace with ⟨slot, retained, run⟩
  cases retained with
  | none =>
      have obl : Xlot.InvNoDel wa .none := by trivial
      exact ProcessCreateMessage.inv_noDel obl run h_ct h h_inherited
  | @some pc sevm pre raw run' =>
      have safeTop : Exec.SafeNodes wa run' :=
        fun node hn htgt =>
          safe _ (Exec.mem_rawFrameRoots_self run') node hn htgt
      have hsg' : (Frame.ofCreate msg).inner.benv.stat.rules.stateGas = none := by
        rw [show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
          processCreateMessage.msg_benvStat]
        exact hsg
      exact ProcessCreateMessage.inv_noDel
        (RunFrame.invNoDel_of_safe (e := rfl) run' run hsg' safeTop)
        run h_ct h h_inherited

/-! ## The settled message-call wrapper -/

/-- **Settled message-call no-deletion and code survival** for a protected
account whose code `C` at `wa` is nonempty and undesignated, under
`stateGas = none` with no fork premise. Covers the collision arm, the create
arm (a create cannot target `wa`) and the call arm (authorizations and
code-delegation resolution keep `wa`'s code). Raw safety comes from the
trace's own raw frames. -/
theorem MessageCallTrace.noDel_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (installed : msg.benv.state.getCode wa = C)
    (own : msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions)
    (safe : SafeRawFrames wa trace.rawFrames) :
    wa ∉ out.accountsToDelete ∧ state.getCode wa = C := by
  have hCne : C.toList ≠ [] := installed ▸ h.code
  cases trace with
  | createCollision target collision result =>
      unfold processMessageCall at result
      simp only [target, ↓reduceIte] at result
      unfold processMessageCall.create at result
      rw [hsg] at result
      unfold messageCreateCollision at collision
      simp only [collision, ↓reduceIte, pure] at result
      have hout := Prod.mk.inj (Except.ok.inj result)
      refine ⟨by rw [← hout.2]; exact AdrSet.not_mem_empty, by rw [← hout.1]; exact installed⟩
  | createRun target collision evm core coreTrace result =>
      have h_ct : msg.currentTarget ≠ wa := ne_wa_of_not_hasCodeOrNonce h.code
        (by simpa only [messageCreateCollision] using collision)
      have hevm := coreTrace.inv_noDel_of_safe hsg h_ct h h_inherited safe
      obtain ⟨hstate, hdel⟩ :=
        processMessageCall_createRun_noDel hsg target collision core result hevm.atd
      refine ⟨hdel, ?_⟩
      have keep := ProcessCreateMessage.codePreserve
        (Xlot.invGetCode_of_filled coreTrace.retained.toFilled) coreTrace.run wa
        (Ne.symm h_ct) (by rw [installed]; exact hCne)
      rw [hstate, ← installed]
      exact keep
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      obtain ⟨address, ownCode⟩ := own target
      obtain ⟨hdNoDel, hdCode, hdInherited, hdOwn⟩ := messageCallDelegation_installed
        delegation h (by rw [installed]; exact hCdel) h_inherited address ownCode
      have execState : execMsg.benv.state.getCode wa = C := by
        rw [execMsgEq, messageCallExecutionMessage_getCode, hdCode, installed]
      have execSg : execMsg.benv.stat.rules.stateGas = none := by
        rw [execMsgEq, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hsg
      have execNoDel : Msg.NoDel wa execMsg := by
        rw [execMsgEq]
        unfold messageCallExecutionMessage Msg.resolveCodeDelegation
        split <;> exact ⟨hdNoDel.ca, hdNoDel.code⟩
      have execInherited : wa ∉ execMsg.inheritedDeletions := by
        rw [execMsgEq]
        unfold messageCallExecutionMessage Msg.resolveCodeDelegation
        split <;> exact hdInherited
      have execCode : execMsg.currentTarget = wa → execMsg.code = C := by
        rw [execMsgEq]
        exact messageCallExecutionMessage_code_installed hdOwn (hdCode.trans installed) hCdel
      have hevm := coreTrace.inv_noDel_of_safe execSg execNoDel execInherited safe
      obtain ⟨hstate, hdel⟩ := processMessageCall_callRun_noDel hsg target delegation execMsgEq
        core result hevm.atd
      refine ⟨hdel, ?_⟩
      have keep := ProcessMessage.codePreserve
        (Xlot.invGetCode_of_filled coreTrace.retained.toFilled) coreTrace.run wa
        (by rw [execState]; exact hCne)
      rw [hstate, ← execState]
      exact keep

/-! ## One selected transaction -/

/-- **Protected-account survival across one selected transaction**, under `stateGas = none`
with no fork premise. If the code `C` at `wa` is nonempty and undesignated and `wa` was
not created in the block, then the transaction never schedules `wa` for deletion, and `wa` holds
`C` after the message and in the final state: the deletion fold and the touched sweep keep it.
Raw safety comes from the trace's own raw frames. -/
theorem TransactionTrace.noDel_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    wa ∉ trace.messageOut.accountsToDelete ∧ trace.messageState.getCode wa = C ∧
      state.getCode wa = C := by
  have hbenv := prepareMessage_benv trace.prepared
  have hdebit : trace.debitState.getCode wa = benv.state.getCode wa := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode wa = C := by
    rw [hbenv]
    exact hdebit.trans installed
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]
    exact hsg
  have hnodel : Msg.NoDel wa trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using notCreated
    · rw [hmsgState]
      exact hCne
  obtain ⟨hnot, hmsg⟩ := trace.message.noDel_of_safe hCdel
    hmsgSg hmsgState (prepareMessage_own trace.prepared) hnodel
    (trace.not_mem_msg_inheritedDeletions wa) safe
  refine ⟨hnot, hmsg, ?_⟩
  obtain ⟨refundCounter, -, hfinal⟩ := trace.exists_selectedFinalStateForm hsg
  have hnotList : ∀ x ∈ trace.messageOut.accountsToDelete.toList, x ≠ wa :=
    fun x hx heq => hnot (heq ▸ Std.HashSet.mem_toList.mp hx)
  rw [hfinal, sweepTouchedAccounts_getCode_of_nonempty, foldl_destroyAccount_getCode_ne _ hnotList,
    State.addBal_getCode, State.addBal_getCode, hmsg]
  rw [foldl_destroyAccount_getCode_ne _ hnotList, State.addBal_getCode, State.addBal_getCode, hmsg]
  exact hCne

/-! ## System messages, requests, and staged bodies -/

/-- **A system message keeps a protected code and never schedules `wa` for
deletion**, under `stateGas = none`, from trace safety and the code facts.
A system message is an ordinary message call to its target with empty
inherited deletions; no premise that `wa` differs from the target is needed. -/
theorem SystemMessageTrace.noDel_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    wa ∉ out.accountsToDelete ∧ state.getCode wa = C := by
  exact trace.message.noDel_of_safe hCdel hsg installed (fun _ => ⟨rfl, rfl⟩)
    ⟨notCreated, show (benv.state.getCode wa).toList ≠ [] by rw [installed]; exact hCne⟩
    AdrSet.not_mem_empty safe

/-- The two checked request calls keep a protected code. -/
theorem RequestsTrace.noDel_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    wa ∉ trace.withdrawalOut.accountsToDelete ∧
      wa ∉ trace.consolidationOut.accountsToDelete ∧ state.getCode wa = C := by
  obtain ⟨hw, hwCode⟩ := trace.withdrawal.noDel_of_safe hCdel hCne hsg installed notCreated
    (SafeRawFrames.of_append_left safe)
  obtain ⟨hc, hcCode⟩ := trace.consolidation.noDel_of_safe
    (benv := benv.withState trace.withdrawalState) hCdel hCne hsg hwCode notCreated
    (SafeRawFrames.of_append_right safe)
  exact ⟨hw, hc, by rw [trace.state_eq_consolidationState]; exact hcCode⟩

/-- **A selected transaction list keeps a protected code** and schedules no
deletion of `wa`, under `stateGas = none`, when `wa` is not block-created. -/
theorem ApplyTransactionsTrace.noDel_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    trace.NoDelScheduled wa ∧ finalBenv.state.getCode wa = C := by
  induction trace with
  | nil => exact ⟨trivial, installed⟩
  | cons head tail ih =>
      have safeHead : SafeRawFrames wa head.rawFrames :=
        SafeRawFrames.of_append_left safe
      have safeTail : SafeRawFrames wa tail.rawFrames :=
        SafeRawFrames.of_append_right safe
      obtain ⟨hnot, -, hstate⟩ := head.noDel_of_safe hCdel hCne hsg installed notCreated
        safeHead
      obtain ⟨htail, hfinal⟩ := ih hsg hstate notCreated safeTail
      exact ⟨⟨hnot, htail⟩, hfinal⟩

/-- The beacon stage keeps a protected code. -/
theorem BeaconStageTrace.code_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    state.getCode wa = C := by
  cases trace with
  | skipped => exact installed
  | called _ _ message _ _ =>
      exact (message.noDel_of_safe hCdel hCne hsg installed notCreated safe).2

/-- The history-storage stage keeps a protected code. -/
theorem HistoryStageTrace.code_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    state.getCode wa = C := by
  cases trace with
  | skipped => exact installed
  | called _ _ _ _ message _ _ =>
      exact (message.noDel_of_safe hCdel hCne hsg installed notCreated safe).2

/-- The request stage keeps a protected code. -/
theorem RequestStageTrace.code_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    state.getCode wa = C := by
  cases trace with
  | skipped => exact installed
  | called _ requests _ =>
      exact (requests.noDel_of_safe hCdel hCne hsg installed notCreated safe).2.2

/-- **A staged body keeps a protected code**, stage by stage in `applyBody` order,
and no selected transaction of it schedules `wa` for deletion. -/
theorem StagedBodyTrace.noDel_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    trace.transactions.NoDelScheduled wa ∧ state.getCode wa = C := by
  have rawEq : trace.rawFrames =
      trace.beacon.rawFrames ++ trace.history.rawFrames ++
        trace.transactions.rawFrames ++ trace.requests.rawFrames := rfl
  -- Split the unfolded enumeration. `List.append` chains nest to the left
  -- here (`((b ++ h) ++ t) ++ r`), so each fragment reaches the full chain by
  -- climbing from its own position with fully explicit sides.
  have safeBeacon : SafeRawFrames wa trace.beacon.rawFrames := by
    intro R hR
    exact (rawEq ▸ safe) R (List.mem_append_left trace.requests.rawFrames
      (List.mem_append_left trace.transactions.rawFrames
        (List.mem_append_left trace.history.rawFrames hR)))
  have safeHistory : SafeRawFrames wa trace.history.rawFrames := by
    intro R hR
    exact (rawEq ▸ safe) R (List.mem_append_left trace.requests.rawFrames
      (List.mem_append_left trace.transactions.rawFrames
        (List.mem_append_right trace.beacon.rawFrames hR)))
  have safeTx : SafeRawFrames wa trace.transactions.rawFrames := by
    intro R hR
    exact (rawEq ▸ safe) R (List.mem_append_left trace.requests.rawFrames
      (List.mem_append_right
        (trace.beacon.rawFrames ++ trace.history.rawFrames) hR))
  have safeReq : SafeRawFrames wa trace.requests.rawFrames := by
    intro R hR
    exact (rawEq ▸ safe) R (List.mem_append_right
      (trace.beacon.rawFrames ++ trace.history.rawFrames ++ trace.transactions.rawFrames)
      hR)
  have hbeacon := trace.beacon.code_of_safe hCdel hCne hsg installed notCreated safeBeacon
  have hhistory := trace.history.code_of_safe (benv := benv.withState trace.beaconState)
    hCdel hCne hsg hbeacon notCreated safeHistory
  obtain ⟨hsched, htx⟩ := trace.transactions.noDel_of_safe
    (benv := (benv.withState trace.beaconState).withState trace.historyState)
    hCdel hCne hsg hhistory notCreated safeTx
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have txCreated : trace.transactionBenv.createdAccounts = benv.createdAccounts :=
    trace.transactions.createdAccounts_eq
  have hwithdrawal : trace.withdrawalState.getCode wa = C := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact htx
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
        exact htx
  have hrequest := trace.requests.code_of_safe
    (benv := trace.transactionBenv.withState trace.withdrawalState) hCdel hCne
    (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    hwithdrawal
    (by change wa ∉ trace.transactionBenv.createdAccounts; rw [txCreated]; exact notCreated)
    safeReq
  refine ⟨hsched, ?_⟩
  rw [trace.finalState_eq, trace.rewardState_eq]
  split
  · exact hrequest
  · rw [payRewards_getCode]
    exact hrequest

/-! ## Configured In-blocks and In-histories -/

/-- **A configured block keeps a protected code**, with per-block
`stateGas = none` from the history's own capability evidence. -/
theorem ConfiguredBlockTraceIn.noDel_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (installed : pre.state.getCode wa = C)
    (safe : SafeRawFrames wa trace.rawFrames) :
    trace.NoDelScheduled wa ∧ post.state.getCode wa = C := by
  obtain ⟨hsched, hstate⟩ := trace.bodyTrace.noDel_of_safe hCdel hCne
    (capabilities.stateGas_none trace.forkIn) installed AdrSet.not_mem_empty safe
  refine ⟨hsched, ?_⟩
  rw [trace.postEq]
  exact hstate

/-- **Code survival and no-deletion along a configured history**, from trace
safety and the code facts. If the checkpoint holds a nonempty, undesignated
code `C` at `wa`, the endpoint state of a retained In-history holds `C` at
`wa` (by induction, so does every checkpoint of its spine), and no selected
transaction along it schedules `wa` for deletion. No `CoveredFork`;
per-block `stateGas = none` from `BodyStageCapabilities F`; no premise that
`wa` is never targeted. -/
theorem ConfiguredHistoryTraceIn.noDel_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode wa = C)
    (safe : SafeRawFrames wa history.rawFrames) :
    history.NoDelScheduled wa ∧ future.state.getCode wa = C := by
  induction history with
  | refl => exact ⟨trivial, installed⟩
  | step prior block ih =>
      have safePrior : SafeRawFrames wa prior.rawFrames :=
        SafeRawFrames.of_append_left safe
      have safeBlock : SafeRawFrames wa block.rawFrames :=
        SafeRawFrames.of_append_right safe
      obtain ⟨hprior, hcurrent⟩ := ih safePrior
      obtain ⟨hblock, hpost⟩ := block.noDel_of_safe hCdel hCne capabilities hcurrent
        safeBlock
      exact ⟨⟨hprior, hblock⟩, hpost⟩

/-! ## Installed-certificate bridges -/

/-- **Per-frame safety of a retained call message from an installed checked
runtime.** Top-run safety covers every listed frame's execution. -/
theorem ProcessMessageTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (installed : msg.benv.state.getCode wa = C)
    (hcode : msg.currentTarget = wa → msg.code = C)
    (h : Msg.NoDel wa msg) :
    SafeRawFrames wa trace.rawFrames := by
  have hCne : C.toList ≠ [] := installed ▸ h.code
  rcases trace with ⟨slot, retained, run⟩
  cases retained with
  | none => exact SafeRawFrames.nil wa
  | @some pc sevm pre raw run' =>
      obtain ⟨henter, -⟩ := RunFrame.some_inv run
      exact Exec.safeNodes_of_installedCert hc callOnly noSelfdestruct hCdel run'
        (by rw [Frame.enter_run_benvStat henter]; exact hsg)
        (by rw [Frame.enter_run_getCode henter]; exact installed)
        hCne
        (fun htgt => ⟨Frame.enter_run_pc henter, by
          rw [Frame.enter_run_code henter]
          exact hcode (show (Frame.ofCall msg).inner.currentTarget = wa from by
            rw [← Frame.enter_run_currentTarget henter]; exact htgt)⟩)

/-- **Per-frame safety of a retained create message from an installed checked
runtime**, for a create not targeting `wa`. -/
theorem ProcessCreateMessageTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (installed : msg.benv.state.getCode wa = C)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) :
    SafeRawFrames wa trace.rawFrames := by
  have hCne : C.toList ≠ [] := installed ▸ h.code
  rcases trace with ⟨slot, retained, run⟩
  cases retained with
  | none => exact SafeRawFrames.nil wa
  | @some pc sevm pre raw run' =>
      obtain ⟨henter, -⟩ := RunFrame.some_inv run
      exact Exec.safeNodes_of_installedCert hc callOnly noSelfdestruct hCdel run'
        (by rw [Frame.enter_run_benvStat henter,
          show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
          processCreateMessage.msg_benvStat]; exact hsg)
        (by rw [Frame.enter_run_getCode henter,
          show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
          processCreateMessage.msg_getCode]; exact installed)
        hCne
        (fun htgt => absurd (show msg.currentTarget = wa from by
          have hinner : (Frame.ofCreate msg).inner.currentTarget = wa := by
            rw [← Frame.enter_run_currentTarget henter]; exact htgt
          exact hinner) h_ct)

/-- **Per-frame safety of a settled message call from an installed checked
runtime.** The collision arm retains nothing; the create/call arms delegate
to the retained core (EIP-7702 authorization and code resolution keep `wa`'s
code for the call arm). -/
theorem MessageCallTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (installed : msg.benv.state.getCode wa = C)
    (own : msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions) :
    SafeRawFrames wa trace.rawFrames := by
  have hCne : C.toList ≠ [] := installed ▸ h.code
  cases trace with
  | createCollision target collision result => exact SafeRawFrames.nil wa
  | createRun target collision evm core coreTrace result =>
      have h_ct : msg.currentTarget ≠ wa := ne_wa_of_not_hasCodeOrNonce h.code
        (by simpa only [messageCreateCollision] using collision)
      exact coreTrace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel
        hsg installed h_ct h
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      obtain ⟨address, ownCode⟩ := own target
      obtain ⟨hdNoDel, hdCode, hdInherited, hdOwn⟩ := messageCallDelegation_installed
        delegation h (by rw [installed]; exact hCdel) h_inherited address ownCode
      have execState : execMsg.benv.state.getCode wa = C := by
        rw [execMsgEq, messageCallExecutionMessage_getCode, hdCode, installed]
      have execSg : execMsg.benv.stat.rules.stateGas = none := by
        rw [execMsgEq, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hsg
      have execNoDel : Msg.NoDel wa execMsg := by
        rw [execMsgEq]
        unfold messageCallExecutionMessage Msg.resolveCodeDelegation
        split <;> exact ⟨hdNoDel.ca, hdNoDel.code⟩
      have execInherited : wa ∉ execMsg.inheritedDeletions := by
        rw [execMsgEq]
        unfold messageCallExecutionMessage Msg.resolveCodeDelegation
        split <;> exact hdInherited
      have execCode : execMsg.currentTarget = wa → execMsg.code = C := by
        rw [execMsgEq]
        exact messageCallExecutionMessage_code_installed hdOwn (hdCode.trans installed) hCdel
      exact coreTrace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel
        execSg execState execCode execNoDel

/-- **Per-frame safety of one selected transaction from an installed checked
runtime.** -/
theorem TransactionTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    SafeRawFrames wa trace.rawFrames := by
  have hbenv := prepareMessage_benv trace.prepared
  have hmsgState : trace.msg.benv.state.getCode wa = C := by
    have hdebit : trace.debitState.getCode wa = benv.state.getCode wa := by
      rw [State.subBal_getCode trace.debit]
      unfold State.getCode
      rw [State.incrNonce_get_code]
    rw [hbenv]
    exact hdebit.trans installed
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]
    exact hsg
  have hnodel : Msg.NoDel wa trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using notCreated
    · rw [hmsgState]
      exact hCne
  exact trace.message.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel
    hmsgSg hmsgState (prepareMessage_own trace.prepared) hnodel
    (trace.not_mem_msg_inheritedDeletions wa)

/-- **Per-frame safety of a system message from an installed checked runtime.** -/
theorem SystemMessageTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    SafeRawFrames wa trace.rawFrames := by
  exact trace.message.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel
    hsg installed (fun _ => ⟨rfl, rfl⟩)
    ⟨notCreated, show (benv.state.getCode wa).toList ≠ [] by rw [installed]; exact hCne⟩
    AdrSet.not_mem_empty

/-- **Per-frame safety of the two checked request calls from an installed
checked runtime.** The consolidation code fact comes back out of the
withdrawal's safe chain. -/
theorem RequestsTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    SafeRawFrames wa trace.rawFrames := by
  have hsW := trace.withdrawal.safeRawFrames_of_installedCert hc callOnly noSelfdestruct
    hCdel hCne hsg installed notCreated
  have hwCode : trace.withdrawalState.getCode wa = C :=
    (trace.withdrawal.noDel_of_safe hCdel hCne hsg installed notCreated hsW).2
  have hsC := trace.consolidation.safeRawFrames_of_installedCert
    (benv := benv.withState trace.withdrawalState) hc callOnly noSelfdestruct hCdel hCne
    hsg hwCode notCreated
  have rawEq : trace.rawFrames =
      trace.withdrawal.rawFrames ++ trace.consolidation.rawFrames := rfl
  intro R hR
  rw [rawEq] at hR
  rcases List.mem_append.mp hR with h | h
  · exact hsW R h
  · exact hsC R h

/-- **Per-frame safety of a selected transaction list from an installed checked
runtime.** The next code fact comes back out of the head's safe chain. -/
theorem ApplyTransactionsTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    SafeRawFrames wa trace.rawFrames := by
  induction trace with
  | nil => exact SafeRawFrames.nil wa
  | cons head tail ih =>
      have hsHead : SafeRawFrames wa head.rawFrames :=
        head.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel hCne hsg
          installed notCreated
      have hstate : _ :=
        (head.noDel_of_safe hCdel hCne hsg installed notCreated hsHead).2.2
      have hsTail : SafeRawFrames wa tail.rawFrames := ih hsg hstate notCreated
      intro R hR
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at hR
      rcases hR with h | h
      · exact hsHead R h
      · exact hsTail R h

/-- The beacon stage retains per-frame safety. -/
theorem BeaconStageTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    SafeRawFrames wa trace.rawFrames := by
  cases trace with
  | skipped => exact SafeRawFrames.nil wa
  | called _ _ message _ _ =>
      exact message.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel hCne
        hsg installed notCreated

/-- The history-storage stage retains per-frame safety. -/
theorem HistoryStageTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    SafeRawFrames wa trace.rawFrames := by
  cases trace with
  | skipped => exact SafeRawFrames.nil wa
  | called _ _ _ _ message _ _ =>
      exact message.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel hCne
        hsg installed notCreated

/-- The request stage retains per-frame safety. -/
theorem RequestStageTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    SafeRawFrames wa trace.rawFrames := by
  cases trace with
  | skipped => exact SafeRawFrames.nil wa
  | called _ requests _ =>
      exact requests.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel hCne
        hsg installed notCreated

/-- **Per-frame safety of a staged body from an installed checked runtime.**
Stage code facts come back out of each stage's safe chain, in `applyBody`
order. -/
theorem StagedBodyTrace.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    SafeRawFrames wa trace.rawFrames := by
  have hsBeacon := trace.beacon.safeRawFrames_of_installedCert hc callOnly noSelfdestruct
    hCdel hCne hsg installed notCreated
  have hbeacon : trace.beaconState.getCode wa = C :=
    trace.beacon.code_of_safe hCdel hCne hsg installed notCreated hsBeacon
  have hsHistory := trace.history.safeRawFrames_of_installedCert
    (benv := benv.withState trace.beaconState) hc callOnly noSelfdestruct hCdel hCne hsg
    hbeacon notCreated
  have hhistory : trace.historyState.getCode wa = C :=
    trace.history.code_of_safe (benv := benv.withState trace.beaconState) hCdel hCne hsg
      hbeacon notCreated hsHistory
  have hsTx := trace.transactions.safeRawFrames_of_installedCert
    (benv := (benv.withState trace.beaconState).withState trace.historyState) hc callOnly
    noSelfdestruct hCdel hCne hsg hhistory notCreated
  have htx : trace.transactionBenv.state.getCode wa = C :=
    (trace.transactions.noDel_of_safe
      (benv := (benv.withState trace.beaconState).withState trace.historyState) hCdel hCne
      hsg hhistory notCreated hsTx).2
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have txCreated : trace.transactionBenv.createdAccounts = benv.createdAccounts :=
    trace.transactions.createdAccounts_eq
  have hwithdrawal : trace.withdrawalState.getCode wa = C := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact htx
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
        exact htx
  have hsReq := trace.requests.safeRawFrames_of_installedCert
    (benv := trace.transactionBenv.withState trace.withdrawalState) hc callOnly
    noSelfdestruct hCdel hCne
    (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    hwithdrawal
    (by change wa ∉ trace.transactionBenv.createdAccounts; rw [txCreated]; exact notCreated)
  -- Recombine left-nested, mirroring the enumeration's own nesting.
  have hab := SafeRawFrames.append hsBeacon hsHistory
  have habt := SafeRawFrames.append hab hsTx
  exact SafeRawFrames.append habt hsReq

/-- **Per-frame safety of a configured block from an installed checked
runtime.** -/
theorem ConfiguredBlockTraceIn.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (installed : pre.state.getCode wa = C) :
    SafeRawFrames wa trace.rawFrames := by
  exact trace.bodyTrace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel
    hCne (capabilities.stateGas_none trace.forkIn) installed AdrSet.not_mem_empty

/-- **Per-frame safety along a configured history from an installed checked
runtime**, by refl/step induction; each checkpoint code fact comes back out
of the prior spine's safe chain. -/
theorem ConfiguredHistoryTraceIn.safeRawFrames_of_installedCert {wa : Adr} {C : ByteArray}
    {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode wa = C) :
    SafeRawFrames wa history.rawFrames := by
  induction history with
  | refl => exact SafeRawFrames.nil wa
  | step prior block ih =>
      have hsPrior : SafeRawFrames wa prior.rawFrames := ih
      have hcurrent : _ :=
        (prior.noDel_of_safe hCdel hCne capabilities installed hsPrior).2
      have hsBlock : SafeRawFrames wa block.rawFrames :=
        block.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel hCne
          capabilities hcurrent
      intro R hR
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append] at hR
      rcases hR with h | h
      · exact hsPrior R h
      · exact hsBlock R h

end ExecutionTrace

end Blanc
