import Blanc.ExecutionInCodeImage
import Blanc.ExecutionSettledOwnCode
import Blanc.ExecutionAccountingCore
import Blanc.ExecutionMessageAdmission
import Blanc.ExecutionTransactionAdmission
import Blanc.ExecutionBodyAdmission
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionImmutableCode
import Blanc.StorageOnlySpec

/-!
# Own code at settled frames (and historical roots) of In-carrier histories

In-carrier analogue of `ConfiguredHistoryTrace.settled_ownCode`
(`Blanc/ExecutionSettledOwnCode.lean`), on the same pattern as
`ConfiguredHistoryTraceIn.settled_codeImageIn`: the storage-only
specification preserves itself trivially, admission comes from
`frameAdmitted_iff_rawFrames`, and the invariant threads through the In
rungs (`*.stateInv_admitted_semIn`, `*.benvInv_admitted_semIn`).

The non-`In` proof closes through the accounting ladder
(`ownLadder.configuredHistory`), which has no In runner. Here each level
unpacks its own message roots instead: entry evidence comes straight from
the retained `ProcessMessage` record (`RunFrame.some_inv`,
`Frame.enter_run_inv`), the per-message invariant from `msgInv_sem` /
`systemTransactionMessage_msgInv_sem`, and the per-message bound from
`msg_sum_nof` and the rung `sum_le` facts. Collision-only CREATEs settle
nothing.

The chain concludes `OwnCodeAtIn`: installed code and pc `0` as in
`OwnCodeAt`, but the selected fork-domain fact `F` and `stateGas = none` in
place of coverage (`CoveredFork`, membership in
`[.prague, .osaka, .bpo1, .bpo2]`, which no historical Muir Glacier or
Byzantium root satisfies), both riding the entry `benvStat` equations. Roots
need no spawn classification, so the roots chain threads no `cover` and no
`OwnSpawns` premise; each root splits from its committed descendants via
`Exec.descendantFrames_ownCodeIn` (child `F` and gas absence by
`Evm.step_spawn_child_benvStat`), classified by the fork-free contract
`OwnSpawnsIn`, ending in `ConfiguredHistoryTraceIn.settled_ownCodeIn`.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

open ContractSpecSem

variable {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop} {C : ByteArray}

/-! ## Historical own code at settled roots

`CoveredFork` is membership in `[.prague, .osaka, .bpo1, .bpo2]`, which no
historical (Muir Glacier, Byzantium, ...) root can satisfy.  The chain below
concludes `OwnCodeAtIn` instead: installed code and pc `0` as before, but the
selected fork-domain fact `F` and `stateGas = none` (both transported along
`Evm.step_spawn_child_benvStat`, the child's `benvStat` equals the parent's)
in place of coverage.  Roots need no spawn classification at all: entry
evidence plus the image equation already put installed code under them, so
the roots chain threads only the invariant, the sums, `F` and state-gas
absence, with no `cover` premise and no `OwnSpawns` premise.

The descendant induction (`Exec.descendantFrames_ownCodeIn`) is further below:
spawn classification goes through the fork-free contract `OwnSpawnsIn`
(state-gas absence in place of the `CoveredFork` premise; consumers produce
it as they produce `OwnSpawns`, swapping `cursor_of_parentPrefix` for
`cursor_of_parentPrefix_noStateGas`), and the create2-unprotected arm splits
on the actual `op.create2` rules fact. -/

/-- Own code at a settled root on a historical fork: `C` installed at `ca`
when the frame starts, entry at pc `0` under the selected domain `F` with no
state gas, and running `C` whenever at `ca`.  Both `F` and state-gas absence
transport across spawns by `Evm.step_spawn_child_benvStat`. -/
def OwnCodeAtIn (F : Fork → Prop) (ca : Adr) (C : ByteArray) (f : Exec.Frame) : Prop :=
  f.pre.getCode ca = C ∧ f.pc = 0 ∧ F f.sevm.benvStat.fork ∧
    f.sevm.benvStat.rules.stateGas = none ∧
    (f.sevm.currentTarget = ca → f.sevm.code = C)

/-- Historical own code at the settled root of a retained call message: the
entry evidence feeds `messageRoot_facts` as before; `F` and state-gas absence
ride the entry `benvStat` equations (`initSevm_benvStat`, `Msg.withBenv_benvStat`,
`benvAfterTransfer_stat`) instead of coverage. -/
theorem ProcessMessageTrace.settledRoots_ownCodeIn {msg : Msg} {post : Devm}
    {F : Fork → Prop}
    (trace : ProcessMessageTrace msg (.ok post))
    (ready : c.MessageRunReady ca msg)
    (bound : sum msg.benv.state.bal < 2 ^ 256)
    (hF : F msg.benv.stat.fork) (hsg : msg.benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  rcases trace with ⟨slot, retained, process⟩
  -- Name the triple: casing `retained` substitutes the slot index away.
  set T : ProcessMessageTrace msg (.ok post) := ⟨slot, retained, process⟩ with hTdef
  cases retained with
  | none =>
      intro R member
      simp only [hTdef, ProcessMessageTrace.settledRoots] at member
      cases member
  | @some pc sevm pre raw run =>
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entryBenv, transfer, evmEq⟩
      simp only [Frame.ofCall] at evmEq
      obtain ⟨installed, -⟩ :=
        Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
      have pcZero : pc = 0 := by
        have hpc := congrArg Evm.pc evmEq
        simpa only [initEvm] using hpc
      have code : pre.getCode ca = C :=
        ExecutionTrace.bytes_eq_of_image (installed.1.trans image)
      have own : sevm.currentTarget = ca → sevm.code = C := fun target =>
        ExecutionTrace.bytes_eq_of_image ((installed.2 target).1.trans image)
      have rootF : F sevm.benvStat.fork := by
        have sevmEq : sevm = initSevm (msg.withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact hF
      have rootGas : sevm.benvStat.rules.stateGas = none := by
        have sevmEq : sevm = initSevm (msg.withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact hsg
      by_cases hc : Frame.settlementCommits (Frame.ofCall msg) raw = true
      · have hcomm : Execution.commits raw = true :=
          Frame.raw_commits_of_settlementCommits hc
        have rootEq : T.settledRoots = [Exec.Frame.ofRun run hcomm] := by
          rw [hTdef]
          simp only [ProcessMessageTrace.settledRoots, hc, ite_true,
            RetainedXlot.settledRoots]
          rw [dite_eq_left hcomm]
        have rootMem : Exec.Frame.ofRun run hcomm ∈ T.settledRoots := by
          rw [rootEq]
          exact List.mem_singleton.mpr rfl
        intro R member
        rw [rootEq, List.mem_singleton] at member
        subst member
        exact ⟨code, pcZero, rootF, rootGas, own⟩
      · intro R member
        simp only [hTdef, ProcessMessageTrace.settledRoots, hc] at member
        exact False.elim (List.not_mem_nil member)

/-- Historical own code at the settled root of a retained create message: the
create frame enters its prepared inner message. -/
theorem ProcessCreateMessageTrace.settledRoots_ownCodeIn {msg : Msg} {post : Devm}
    {F : Fork → Prop}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (msgInv : c.MsgInv ca msg)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (bound : sum msg.benv.state.bal < 2 ^ 256)
    (hF : F msg.benv.stat.fork) (hsg : msg.benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  rcases trace with ⟨slot, retained, process⟩
  -- Name the triple: casing `retained` substitutes the slot index away.
  set T : ProcessCreateMessageTrace msg (.ok post) := ⟨slot, retained, process⟩ with hTdef
  cases retained with
  | none =>
      intro R member
      simp only [hTdef, ProcessCreateMessageTrace.settledRoots] at member
      cases member
  | @some pc sevm pre raw run =>
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entryBenv, transfer, evmEq⟩
      simp only [Frame.ofCreate] at evmEq
      have preparedInv : c.MsgInv ca (processCreateMessage.msg msg) :=
        msgInv.processCreateMessage_msg targetNone targetNe
      have preparedTargetNe :
          (processCreateMessage.msg msg).currentTarget ≠ ca := by
        intro target
        exact targetNe (by
          simpa only [processCreateMessage.msg, Msg.withBenv] using target)
      have innerReady := preparedInv.runReady_of_foreign preparedTargetNe
      have innerBound :
          sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
        rw [Jaune.processCreateMessage_msg_bal_eq]
        exact bound
      have preparedF : F (processCreateMessage.msg msg).benv.stat.fork := by
        rw [processCreateMessage.msg_benvStat]
        exact hF
      have preparedGas :
          (processCreateMessage.msg msg).benv.stat.rules.stateGas = none := by
        rw [processCreateMessage.msg_benvStat]
        exact hsg
      obtain ⟨installed, -⟩ :=
        Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq innerReady
          innerBound
      have pcZero : pc = 0 := by
        have hpc := congrArg Evm.pc evmEq
        simpa only [initEvm] using hpc
      have code : pre.getCode ca = C :=
        ExecutionTrace.bytes_eq_of_image (installed.1.trans image)
      have own : sevm.currentTarget = ca → sevm.code = C := fun target =>
        ExecutionTrace.bytes_eq_of_image ((installed.2 target).1.trans image)
      have rootF : F sevm.benvStat.fork := by
        have sevmEq : sevm =
            initSevm ((processCreateMessage.msg msg).withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact preparedF
      have rootGas : sevm.benvStat.rules.stateGas = none := by
        have sevmEq : sevm =
            initSevm ((processCreateMessage.msg msg).withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact preparedGas
      by_cases hc : Frame.settlementCommits (Frame.ofCreate msg) raw = true
      · have hcomm : Execution.commits raw = true :=
          Frame.raw_commits_of_settlementCommits hc
        have rootEq : T.settledRoots = [Exec.Frame.ofRun run hcomm] := by
          rw [hTdef]
          simp only [ProcessCreateMessageTrace.settledRoots, hc, ite_true,
            RetainedXlot.settledRoots]
          rw [dite_eq_left hcomm]
        have rootMem : Exec.Frame.ofRun run hcomm ∈ T.settledRoots := by
          rw [rootEq]
          exact List.mem_singleton.mpr rfl
        intro R member
        rw [rootEq, List.mem_singleton] at member
        subst member
        exact ⟨code, pcZero, rootF, rootGas, own⟩
      · intro R member
        simp only [hTdef, ProcessCreateMessageTrace.settledRoots, hc] at member
        exact False.elim (List.not_mem_nil member)

/-- Historical own code at the settled roots of a message call: collision
settles nothing; a create runs the prepared inner message; a call runs the
delegated execution message.  The invariant (not a readiness certificate)
suffices: each arm builds its own readiness. -/
theorem MessageCallTrace.settledRoots_ownCodeIn {msg : Msg} {state : State}
    {out : MsgCallOutput} {F : Fork → Prop}
    (trace : MessageCallTrace msg state out)
    (msgInv : c.MsgInv ca msg)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (hF : F msg.benv.stat.fork) (hsg : msg.benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  cases trace with
  | createCollision _ _ _ =>
      intro R member
      simp only [MessageCallTrace.settledRoots] at member
      exact False.elim (List.not_mem_nil member)
  | createRun h_target h_collision _ _ coreTrace _ =>
      have targetNe : msg.currentTarget ≠ ca :=
        StateInv.ne_of_messageCreateCollision_false msgInv.state h_collision
      intro R member
      exact coreTrace.settledRoots_ownCodeIn msgInv h_target targetNe sumNof
        hF hsg image R member
  | callRun h_target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      subst execMsgEq
      have delegatedInv := msgInv.of_messageCallDelegation delegation
      have execReady :
          c.MessageRunReady ca (messageCallExecutionMessage delegated) := by
        refine ⟨delegatedInv.messageCallExecutionMessage, Or.inl ?_⟩
        rw [messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq delegation]
        exact h_target
      have execSum :
          sum (messageCallExecutionMessage delegated).benv.state.bal < 2 ^ 256 := by
        have balEq : (messageCallExecutionMessage delegated).benv.state.bal =
            msg.benv.state.bal := by
          rw [messageCallExecutionMessage_bal_eq,
            messageCallDelegation_bal_eq delegation]
        rw [balEq]
        exact sumNof
      have execF : F (messageCallExecutionMessage delegated).benv.stat.fork := by
        rw [messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hF
      have execGas :
          (messageCallExecutionMessage delegated).benv.stat.rules.stateGas =
            none := by
        rw [messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hsg
      intro R member
      exact coreTrace.settledRoots_ownCodeIn execReady execSum execF execGas
        image R member

/-- Historical own code at the settled roots of one transaction: the prepared
message supplies the invariant; `F` and state-gas absence ride
`prepareMessage_benv` and `Benv.beginTransaction`. -/
theorem TransactionTrace.settledRoots_ownCodeIn
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {F : Fork → Prop}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  have msgInv := trace.msgInv_sem inv.state inv.ca
  have msgSum := trace.msg_sum_nof sumNof
  have msgF : F trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hF
  have msgGas : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact hsg
  intro R member
  exact trace.message.settledRoots_ownCodeIn msgInv msgSum msgF msgGas image R
    member

/-- Historical own code at the settled roots of a transaction list: the head
runs from the entry invariant, the tail from the rung invariant and sum. -/
theorem ApplyTransactionsTrace.settledRoots_ownCodeIn {F : Fork → Prop}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  induction trace with
  | nil =>
      intro R member
      simp only [ApplyTransactionsTrace.settledRoots,
        List.not_mem_nil] at member
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      have headInv : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted_semIn preserves hF hsg admitted.1 sumNof inv K
          image
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hsg)
          sumNof
      intro R member
      simp only [ApplyTransactionsTrace.settledRoots, List.mem_append] at member
      rcases member with member | member
      · exact head.settledRoots_ownCodeIn inv sumNof hF hsg image R member
      · exact ih (by simpa only [Benv.withState] using hF)
          (by simpa only [Benv.withState] using hsg) admitted.2 headInv
          nextSum R member

/-- Historical own code at the settled root of a system message: the
constructed message invariant runs the single retained call. -/
theorem SystemMessageTrace.settledRoots_ownCodeIn
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput} {F : Fork → Prop}
    (trace : SystemMessageTrace benv target data state out)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  have msgInv : c.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv_sem inv.state inv.ca
  have msgSum :
      sum (systemTransactionMessage benv target data).benv.state.bal < 2 ^ 256 := by
    rw [systemTransactionMessage_benv_state]
    exact sumNof
  have msgF : F (systemTransactionMessage benv target data).benv.stat.fork := by
    simpa only [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hF
  have msgGas :
      (systemTransactionMessage benv target data).benv.stat.rules.stateGas =
        none :=
    hsg
  intro R member
  exact trace.message.settledRoots_ownCodeIn msgInv msgSum msgF msgGas image R
    member

/-- Historical own code at the settled roots of the two request calls:
withdrawal, then consolidation from the rung invariant and sum. -/
theorem RequestsTrace.settledRoots_ownCodeIn {F : Fork → Prop}
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  have withdrawal := trace.withdrawal.stateInv_and_sum_le_admitted_semIn
    preserves hF hsg admitted.withdrawal inv K image
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    ⟨withdrawal.1, by simpa only [Benv.withState] using inv.ca⟩
  have withdrawalSum :
      sum (benv.withState trace.withdrawalState).state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (by simpa only [Benv.withState] using withdrawal.2) sumNof
  have hFwd : F (benv.withState trace.withdrawalState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsgwd : (benv.withState trace.withdrawalState).stat.rules.stateGas = none := by
    simpa only [Benv.withState] using hsg
  intro R member
  simp only [RequestsTrace.settledRoots, List.mem_append] at member
  rcases member with member | member
  · exact trace.withdrawal.settledRoots_ownCodeIn inv sumNof hF hsg image R
      member
  · exact trace.consolidation.settledRoots_ownCodeIn withdrawalInv withdrawalSum
      hFwd hsgwd image R member

/-- Historical own code at the settled roots of a beacon stage: skipped stages
settle nothing, a called stage is one system message. -/
theorem BeaconStageTrace.settledRoots_ownCodeIn
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    {F : Fork → Prop}
    (trace : BeaconStageTrace rules benv state bal)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  cases trace with
  | skipped =>
      intro R member
      simp only [BeaconStageTrace.settledRoots] at member
      exact False.elim (List.not_mem_nil member)
  | called _ _ message _ _ =>
      intro R member
      exact message.settledRoots_ownCodeIn inv sumNof hF hsg image R member

/-- Historical own code at the settled roots of a history-storage stage. -/
theorem HistoryStageTrace.settledRoots_ownCodeIn
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder} {F : Fork → Prop}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  cases trace with
  | skipped =>
      intro R member
      simp only [HistoryStageTrace.settledRoots] at member
      exact False.elim (List.not_mem_nil member)
  | called _ _ _ _ message _ _ =>
      intro R member
      exact message.settledRoots_ownCodeIn inv sumNof hF hsg image R member

/-- Historical own code at the settled roots of a request stage. -/
theorem RequestStageTrace.settledRoots_ownCodeIn {F : Fork → Prop}
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  cases trace with
  | skipped =>
      intro R member
      simp only [RequestStageTrace.settledRoots] at member
      exact False.elim (List.not_mem_nil member)
  | called _ requests _ =>
      intro R member
      exact requests.settledRoots_ownCodeIn preserves hF hsg admitted inv
        sumNof K image R member

/-- Historical own code at the settled roots of a staged body, in D1 stage
order.  Stage invariants come back out of the In-rungs; the request entry sum
comes from the withdrawal pass bound. -/
theorem StagedBodyTrace.settledRoots_ownCodeIn {F : Fork → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  have openSum : sum benv.state.bal < 2 ^ 256 := by omega
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_semIn
    preserves hF hsg admitted.beacon inv K image
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, by simpa only [Benv.withState] using inv.ca⟩
  have beaconSum : sum (benv.withState trace.beaconState).state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (by simpa only [Benv.withState] using beacon.2) openSum
  have hFbeacon : F (benv.withState trace.beaconState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsgbeacon :
      (benv.withState trace.beaconState).stat.rules.stateGas = none := by
    simpa only [Benv.withState] using hsg
  have history := trace.history.stateInv_and_sum_le_admitted_semIn
    preserves hFbeacon hsgbeacon admitted.history beaconInv K image
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historyLe : sum trace.historyState.bal ≤ sum benv.state.bal :=
    le_trans (by simpa only [Benv.withState] using history.2) beacon.2
  have historySum : sum trace.historyState.bal < 2 ^ 256 := by omega
  have hFtx :
      F ((benv.withState trace.beaconState).withState trace.historyState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsgtx :
      ((benv.withState trace.beaconState).withState trace.historyState).stat.rules.stateGas =
        none := by
    simpa only [Benv.withState] using hsg
  have transactionsInv : c.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv_admitted_semIn preserves hFtx hsgtx
      admitted.transactions historySum historyInv K image
  have transactionLe : sum trace.transactionBenv.state.bal ≤ sum benv.state.bal :=
    le_trans (trace.transactions.sum_le_noStateGas (by simpa only [Benv.withState] using hsg))
      historyLe
  have txSum : sum trace.transactionBenv.state.bal < 2 ^ 256 := by omega
  have txWdBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    omega
  have txStat : trace.transactionBenv.stat = benv.stat :=
    trace.transactions.stat_eq
  have withdrawalInv : c.BenvInv ca
      (trace.transactionBenv.withState trace.withdrawalState) := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact ⟨transactionsInv.state, by simpa only [Benv.withState] using
          transactionsInv.ca⟩
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1]
        exact benvInv_processWithdrawalsState_sem transactionsInv (by omega)
  have requestSum :
      sum (trace.transactionBenv.withState trace.withdrawalState).state.bal <
        2 ^ 256 := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        simpa only [Benv.withState] using txSum
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        have wseq : trace.withdrawalState =
            processWithdrawalsState trace.transactionBenv.state wds :=
          (Prod.mk.inj run).1.symm
        rw [wseq]
        simpa only [Benv.withState] using
          processWithdrawalsState_sum_nof txWdBound
  have hFreq : F trace.transactionBenv.stat.fork := by
    rw [txStat]; exact hF
  have hsgreq : trace.transactionBenv.stat.rules.stateGas = none := by
    rw [txStat]; exact hsg
  have hFreqWs : F (trace.transactionBenv.withState
      trace.withdrawalState).stat.fork := by
    simpa only [Benv.withState] using hFreq
  have hsgreqWs : (trace.transactionBenv.withState
      trace.withdrawalState).stat.rules.stateGas = none := by
    simpa only [Benv.withState] using hsgreq
  intro R member
  simp only [StagedBodyTrace.settledRoots, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact trace.beacon.settledRoots_ownCodeIn inv openSum hF hsg image R
      member
  · exact trace.history.settledRoots_ownCodeIn beaconInv beaconSum hFbeacon
      hsgbeacon image R member
  · exact trace.transactions.settledRoots_ownCodeIn preserves hFtx hsgtx
      admitted.transactions historyInv historySum K image R member
  · exact trace.requests.settledRoots_ownCodeIn preserves hFreqWs hsgreqWs
      admitted.requests withdrawalInv requestSum K image R member

/-- Historical own code at the settled roots of a configured In-block: the
block entry invariant plus empty block-level creation, with `F` and state-gas
absence from the block's own selection. -/
theorem ConfiguredBlockTraceIn.settledRoots_ownCodeIn {F : Fork → Prop}
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca pre.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ R ∈ trace.settledRoots, OwnCodeAtIn F ca C R := by
  intro R member
  exact trace.bodyTrace.settledRoots_ownCodeIn preserves trace.forkIn
    (capabilities.stateGas_none trace.forkIn) admitted trace.withdrawalsBound
    ⟨inv, AdrSet.not_mem_empty⟩ K image R member

/-- **Installed code at every settled root of an In-history.** If `C` is
installed at `a` at the checkpoint, then every settled root of the history
finds `C` at `a` when it starts, enters at pc `0` under the selected domain
with no state gas and, if it runs at `a`, runs `C`.  The storage-only
specification preserves itself trivially; no coverage premise is needed
because roots need no spawn classification.  Descendants need
`Exec.descendantFrames_ownCodeIn` (not in this module: historical spawn
classification is a consumer-facing contract beyond this unit). -/
theorem ConfiguredHistoryTraceIn.settledRoots_ownCodeIn (sem : CodeSem) (a : Adr)
    {F : Fork → Prop} {C : ByteArray}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (rewards : history.RewardCreditsFunded)
    (installed : some (checkpoint.state.getCode a).toList = sem.image)
    (K : InstalledCert C) (image : sem.image = some C.toList) :
    ∀ R ∈ history.settledRoots, OwnCodeAtIn F a C R := by
  have admitted : history.FrameAdmitted a (fun _ _ => True) :=
    (history.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial
  have preserves :
      (ContractSpecSem.ofStorageOnly sem (fun _ => True)).PreservesAdmittedIn
        F a (fun _ _ => True) :=
    fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩
  have inv : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).StateInv
      a checkpoint.state :=
    ⟨installed, trivial, trivial⟩
  induction history with
  | refl =>
      intro R member
      simp only [ConfiguredHistoryTraceIn.settledRoots,
        List.not_mem_nil] at member
  | step prior block ih =>
      intro R member
      simp only [ConfiguredHistoryTraceIn.settledRoots, List.mem_append] at member
      rcases member with member | member
      · exact ih rewards.1 admitted.1 R member
      · exact block.settledRoots_ownCodeIn preserves capabilities admitted.2
          (prior.stateInv_admitted_semIn preserves capabilities admitted.1
            rewards.1 inv K image) K image R member

/-! ## Historical descendant induction

`OwnSpawnsIn` is the fork-free spawn contract: like `OwnSpawns`, but the
state-gas absence (which the no-state-gas cursor needs) in place of the
`CoveredFork` premise. Consumers produce it exactly as they produce
`OwnSpawns` (`own_spawns`), swapping `cursor_of_parentPrefix` for
`cursor_of_parentPrefix_noStateGas` and keeping `CursorOK.exec_spawn_undelegated`.
`Exec.descendantFrames_ownCodeIn` is the `descendantFrames_ownCode` induction
with the child-fork step replaced by `Evm.step_spawn_child_benvStat` (the
child's `benvStat` equals the parent's, so `F` and state-gas absence
transport) and the create2-unprotected arm split on the actual
`op.create2` rules fact: enabled mirrors the covered unfolding with explicit
rules facts; disabled contradicts the spawn against the error arm. -/

/-- The spawn kinds of frames running `C` at `ca` on a historical fork: every
external instruction decoded along their chain is `CALL`, `STATICCALL` or
`CREATE2`, under state-gas absence instead of fork coverage. -/
def OwnSpawnsIn (ca : Adr) (C : ByteArray) : Prop :=
  ∀ {R N : Exec.Deriv} {x : Xinst}, R.pc = 0 → R.sevm.code = C → R.sevm.currentTarget = ca →
    R.sevm.benvStat.rules.stateGas = none →
    Exec.Deriv.ParentPrefix R N →
    Ninst.At N.sevm.code N.pc (.exec x) → x = .call ∨ x = .staticcall ∨ x = .create2

/-- **Own code below a frame on a historical fork.** Along the chain of a
frame `R` that starts at pc `0` with `C` installed at `ca` (and runs `C` if
it runs at `ca`), every committed descendant frame satisfies `OwnCodeAtIn`
under the selected domain, provided frames running `C` at `ca` spawn only by
`CALL`, `STATICCALL` or `CREATE2` (`OwnSpawnsIn`). -/
theorem Exec.descendantFrames_ownCodeIn {ca : Adr} {C : ByteArray} {F : Fork → Prop}
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
      {R : Exec.Deriv}, Exec.Deriv.ParentPrefix R ⟨pc, sevm, pre, out, run⟩ → R.pc = 0 →
      F R.sevm.benvStat.fork → R.sevm.benvStat.rules.stateGas = none →
      R.devm.getCode ca = C →
      (R.sevm.currentTarget = ca → R.sevm.code = C) →
      ∀ f ∈ Exec.descendantFrames run, OwnCodeAtIn F ca C f := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ _ _ _ _ _ _ f member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro R chain pcZero hF hsg code own
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.cont step next)) pcZero hF hsg code own
  | doneErr _ _ _ =>
      intro _ _ _ _ _ _ _ f member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro R chain pcZero hF hsg code own
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.doneOk step enter resume next)) pcZero hF hsg code own
  | runErr _ _ _ _ =>
      intro _ _ _ _ _ _ _ f member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro R chain pcZero hF hsg code own f member
      have sevmEq : nodeSevm = R.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
      have codeNe : C ≠ .empty := fun empty => nonempty (by rw [empty]; simp only [ByteArray.toList_empty])
      have nodeCode : nodePre.getCode ca = C := by
        have keep := (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 ca
          (by rw [code]; exact nonempty)
        exact keep.trans code
      have nodeF : F nodeSevm.benvStat.fork := by rw [sevmEq]; exact hF
      have nodeGas : nodeSevm.benvStat.rules.stateGas = none := by rw [sevmEq]; exact hsg
      obtain ⟨pcZero', getCode, codeSource⟩ := Evm.step_spawn_child hstep henter
      have hbenv : cevm.sta.benvStat = nodeSevm.benvStat :=
        Evm.step_spawn_child_benvStat hstep henter
      have childF : F cevm.sta.benvStat.fork := by rw [hbenv]; exact nodeF
      have childGas : cevm.sta.benvStat.rules.stateGas = none := by rw [hbenv]; exact nodeGas
      have childCode : cevm.dyna.getCode ca = C := (getCode ca).trans nodeCode
      have childOwn : cevm.sta.currentTarget = ca → cevm.sta.code = C := by
        intro target
        by_cases same : nodeSevm.currentTarget = ca
        · obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv hstep
          have kind := spawns (N := ⟨nodePc, nodeSevm, nodePre, final,
            .runOk hstep henter child hresume next⟩) pcZero (own (sevmEq ▸ same))
            (sevmEq ▸ same) hsg chain hat
          have sameTarget : frame.inner.currentTarget = nodeSevm.currentTarget := by
            rw [← Frame.enter_run_currentTarget henter, target, same]
          have notDel : ¬ isValidDelegation (nodePre.getCode frame.inner.currentTarget) := by
            rw [sameTarget, same, nodeCode]
            exact nondelegating
          rw [Frame.enter_run_code henter]
          rcases kind with rfl | rfl | rfl
          · rw [Xinst.step_call_sameTarget_code spawn sameTarget notDel, sameTarget, same, nodeCode]
          · rw [Xinst.step_staticcall_sameTarget_code spawn sameTarget notDel, sameTarget, same,
              nodeCode]
          · by_cases hcreate2 : nodeSevm.benvStat.rules.op.create2 = true
            · have unprotected : ¬ State.Protected nodePre.state frame.inner.currentTarget := by
                simp only [Xinst.step, nodeGas, hcreate2, ↓reduceIte, Bind.bind,
                  Except.bind] at spawn
                rcases eq1 : Devm.pop nodePre with _ | ⟨v1, s1⟩ <;> simp only [eq1] at spawn
                · simp only [XStep.ofExcept, reduceCtorEq] at spawn
                rcases eq2 : Devm.popToNat s1 with _ | ⟨n2, s2⟩ <;> simp only [eq2] at spawn
                · simp only [XStep.ofExcept, reduceCtorEq] at spawn
                rcases eq3 : Devm.popToNat s2 with _ | ⟨n3, s3⟩ <;> simp only [eq3] at spawn
                · simp only [XStep.ofExcept, reduceCtorEq] at spawn
                rcases eq4 : Devm.pop s3 with _ | ⟨v4, s4⟩ <;> simp only [eq4] at spawn
                · simp only [XStep.ofExcept, reduceCtorEq] at spawn
                split at spawn
                · simp only [XStep.ofExcept, reduceCtorEq] at spawn
                rename_i s5 eq5
                simp only [XStep.ofExcept, pure, Except.pure] at spawn
                have state : (s5.memExtends [(n2, n3)]).state = nodePre.state := by
                  obtain ⟨x2, f2, -⟩ := Devm.pop_of_popToNat_val eq2
                  obtain ⟨x3, f3, -⟩ := Devm.pop_of_popToNat_val eq3
                  rw [show (s5.memExtends [(n2, n3)]).state = s5.state from rfl,
                    ← (Devm.burn_of_chargeGas eq5).state, ← (Devm.pop_of_pop eq4).state, ← f3.state,
                    ← f2.state, ← (Devm.pop_of_pop eq1).state]
                rw [← state, (genericCreate_step_spawn_exact spawn).1]
                exact genericCreate_step_spawn_target_unprotected spawn
              rw [sameTarget, same] at unprotected
              exact (unprotected (State.Protected.of_code_ne_nil (by
                change (nodePre.getCode ca).toList ≠ []
                rw [nodeCode]
                exact nonempty))).elim
            · simp only [Xinst.step, hcreate2, Bool.false_eq_true, ↓reduceIte,
                XStep.ofExcept, reduceCtorEq] at spawn
        · rw [codeSource (by rw [target]; exact same) (by rw [target, nodeCode]; exact codeNe)
            (by rw [target, nodeCode]; exact nondelegating), target, nodeCode]
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume next
          settles] at member
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with (rfl | inChild) | inNext
        · exact ⟨childCode, pcZero', childF, childGas, childOwn⟩
        · exact childIh (R := ⟨_, _, _, _, child⟩) (.refl _) pcZero' childF childGas childCode childOwn
            f inChild
        · exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) pcZero hF hsg code own
            f inNext
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child hresume next
          settles] at member
        exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) pcZero hF hsg code own
          f member

/-! ## Historical own code at all settled frames

With `descendantFrames_ownCodeIn` in hand, each retained core splits its
committed frames into the root (the corresponding `…settledRoots_ownCodeIn`
worker) and its committed descendants (the induction). The levels above
thread the invariant, the sums, `F`, state-gas absence and `OwnSpawnsIn`
exactly as the roots chain threads its premises, ending in
`ConfiguredHistoryTraceIn.settled_ownCodeIn` with no cover premise. -/

/-- Historical own code at every settled frame of a retained call message:
the root goes through the roots worker, deeper frames through the
descendant induction. -/
theorem ProcessMessageTrace.settledFrames_ownCodeIn {msg : Msg} {post : Devm}
    {F : Fork → Prop}
    (trace : ProcessMessageTrace msg (.ok post))
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (ready : c.MessageRunReady ca msg)
    (bound : sum msg.benv.state.bal < 2 ^ 256)
    (hF : F msg.benv.stat.fork) (hsg : msg.benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  rcases trace with ⟨slot, retained, process⟩
  -- Name the triple: casing `retained` substitutes the slot index away.
  set T : ProcessMessageTrace msg (.ok post) := ⟨slot, retained, process⟩ with hTdef
  cases retained with
  | none =>
      intro f member
      simp only [hTdef, ProcessMessageTrace.settledFrames] at member
      cases member
  | @some pc sevm pre raw run =>
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entryBenv, transfer, evmEq⟩
      simp only [Frame.ofCall] at evmEq
      obtain ⟨installed, -⟩ :=
        Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
      have pcZero : pc = 0 := by
        have hpc := congrArg Evm.pc evmEq
        simpa only [initEvm] using hpc
      have code : pre.getCode ca = C :=
        ExecutionTrace.bytes_eq_of_image (installed.1.trans image)
      have own : sevm.currentTarget = ca → sevm.code = C := fun target =>
        ExecutionTrace.bytes_eq_of_image ((installed.2 target).1.trans image)
      have rootF : F sevm.benvStat.fork := by
        have sevmEq : sevm = initSevm (msg.withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact hF
      have rootGas : sevm.benvStat.rules.stateGas = none := by
        have sevmEq : sevm = initSevm (msg.withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact hsg
      by_cases hc : Frame.settlementCommits (Frame.ofCall msg) raw = true
      · have hcomm : Execution.commits raw = true :=
          Frame.raw_commits_of_settlementCommits hc
        have rootEq : T.settledRoots = [Exec.Frame.ofRun run hcomm] := by
          rw [hTdef]
          simp only [ProcessMessageTrace.settledRoots, hc, ite_true,
            RetainedXlot.settledRoots]
          rw [dite_eq_left hcomm]
        have rootMem : Exec.Frame.ofRun run hcomm ∈ T.settledRoots := by
          rw [rootEq]
          exact List.mem_singleton.mpr rfl
        have frameEq : T.settledFrames = Exec.committedFrames run := by
          rw [hTdef]
          simp only [ProcessMessageTrace.settledFrames, hc, ite_true]
        intro f member
        rw [frameEq, Exec.committedFrames, dite_eq_left hcomm] at member
        rcases List.mem_cons.mp member with rfl | deeper
        · exact ProcessMessageTrace.settledRoots_ownCodeIn T ready bound hF hsg
            image _ rootMem
        · exact Exec.descendantFrames_ownCodeIn nonempty nondelegating spawns run
            (R := ⟨pc, sevm, pre, raw, run⟩) (.refl _) pcZero rootF rootGas code
            own f deeper
      · intro f member
        simp only [hTdef, ProcessMessageTrace.settledFrames, hc] at member
        exact False.elim (List.not_mem_nil member)

/-- Historical own code at every settled frame of a retained create message. -/
theorem ProcessCreateMessageTrace.settledFrames_ownCodeIn {msg : Msg} {post : Devm}
    {F : Fork → Prop}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (msgInv : c.MsgInv ca msg)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (bound : sum msg.benv.state.bal < 2 ^ 256)
    (hF : F msg.benv.stat.fork) (hsg : msg.benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  rcases trace with ⟨slot, retained, process⟩
  -- Name the triple: casing `retained` substitutes the slot index away.
  set T : ProcessCreateMessageTrace msg (.ok post) := ⟨slot, retained, process⟩ with hTdef
  cases retained with
  | none =>
      intro f member
      simp only [hTdef, ProcessCreateMessageTrace.settledFrames] at member
      cases member
  | @some pc sevm pre raw run =>
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with ⟨entryBenv, transfer, evmEq⟩
      simp only [Frame.ofCreate] at evmEq
      have preparedInv : c.MsgInv ca (processCreateMessage.msg msg) :=
        msgInv.processCreateMessage_msg targetNone targetNe
      have preparedTargetNe :
          (processCreateMessage.msg msg).currentTarget ≠ ca := by
        intro target
        exact targetNe (by
          simpa only [processCreateMessage.msg, Msg.withBenv] using target)
      have innerReady := preparedInv.runReady_of_foreign preparedTargetNe
      have innerBound :
          sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
        rw [Jaune.processCreateMessage_msg_bal_eq]
        exact bound
      have preparedF : F (processCreateMessage.msg msg).benv.stat.fork := by
        rw [processCreateMessage.msg_benvStat]
        exact hF
      have preparedGas :
          (processCreateMessage.msg msg).benv.stat.rules.stateGas = none := by
        rw [processCreateMessage.msg_benvStat]
        exact hsg
      obtain ⟨installed, -⟩ :=
        Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq innerReady
          innerBound
      have pcZero : pc = 0 := by
        have hpc := congrArg Evm.pc evmEq
        simpa only [initEvm] using hpc
      have code : pre.getCode ca = C :=
        ExecutionTrace.bytes_eq_of_image (installed.1.trans image)
      have own : sevm.currentTarget = ca → sevm.code = C := fun target =>
        ExecutionTrace.bytes_eq_of_image ((installed.2 target).1.trans image)
      have rootF : F sevm.benvStat.fork := by
        have sevmEq : sevm =
            initSevm ((processCreateMessage.msg msg).withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact preparedF
      have rootGas : sevm.benvStat.rules.stateGas = none := by
        have sevmEq : sevm =
            initSevm ((processCreateMessage.msg msg).withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        rw [sevmEq, initSevm_benvStat, Msg.withBenv_benvStat,
          benvAfterTransfer_stat transfer]
        exact preparedGas
      by_cases hc : Frame.settlementCommits (Frame.ofCreate msg) raw = true
      · have hcomm : Execution.commits raw = true :=
          Frame.raw_commits_of_settlementCommits hc
        have rootEq : T.settledRoots = [Exec.Frame.ofRun run hcomm] := by
          rw [hTdef]
          simp only [ProcessCreateMessageTrace.settledRoots, hc, ite_true,
            RetainedXlot.settledRoots]
          rw [dite_eq_left hcomm]
        have rootMem : Exec.Frame.ofRun run hcomm ∈ T.settledRoots := by
          rw [rootEq]
          exact List.mem_singleton.mpr rfl
        have frameEq : T.settledFrames = Exec.committedFrames run := by
          rw [hTdef]
          simp only [ProcessCreateMessageTrace.settledFrames, hc, ite_true]
        intro f member
        rw [frameEq, Exec.committedFrames, dite_eq_left hcomm] at member
        rcases List.mem_cons.mp member with rfl | deeper
        · exact ProcessCreateMessageTrace.settledRoots_ownCodeIn T msgInv
            targetNone targetNe bound hF hsg image _ rootMem
        · exact Exec.descendantFrames_ownCodeIn nonempty nondelegating spawns run
            (R := ⟨pc, sevm, pre, raw, run⟩) (.refl _) pcZero rootF rootGas code
            own f deeper
      · intro f member
        simp only [hTdef, ProcessCreateMessageTrace.settledFrames, hc] at member
        exact False.elim (List.not_mem_nil member)

/-- Historical own code at every settled frame of a message call. -/
theorem MessageCallTrace.settledFrames_ownCodeIn {msg : Msg} {state : State}
    {out : MsgCallOutput} {F : Fork → Prop}
    (trace : MessageCallTrace msg state out)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (msgInv : c.MsgInv ca msg)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (hF : F msg.benv.stat.fork) (hsg : msg.benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  cases trace with
  | createCollision _ _ _ =>
      intro f member
      simp only [MessageCallTrace.settledFrames] at member
      exact False.elim (List.not_mem_nil member)
  | createRun h_target h_collision _ _ coreTrace _ =>
      have targetNe : msg.currentTarget ≠ ca :=
        StateInv.ne_of_messageCreateCollision_false msgInv.state h_collision
      intro f member
      exact coreTrace.settledFrames_ownCodeIn nonempty nondelegating spawns
        msgInv h_target targetNe sumNof hF hsg image f member
  | callRun h_target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      subst execMsgEq
      have delegatedInv := msgInv.of_messageCallDelegation delegation
      have execReady :
          c.MessageRunReady ca (messageCallExecutionMessage delegated) := by
        refine ⟨delegatedInv.messageCallExecutionMessage, Or.inl ?_⟩
        rw [messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq delegation]
        exact h_target
      have execSum :
          sum (messageCallExecutionMessage delegated).benv.state.bal < 2 ^ 256 := by
        have balEq : (messageCallExecutionMessage delegated).benv.state.bal =
            msg.benv.state.bal := by
          rw [messageCallExecutionMessage_bal_eq,
            messageCallDelegation_bal_eq delegation]
        rw [balEq]
        exact sumNof
      have execF : F (messageCallExecutionMessage delegated).benv.stat.fork := by
        rw [messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hF
      have execGas :
          (messageCallExecutionMessage delegated).benv.stat.rules.stateGas =
            none := by
        rw [messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hsg
      intro f member
      exact coreTrace.settledFrames_ownCodeIn nonempty nondelegating spawns
        execReady execSum execF execGas image f member

/-- Historical own code at every settled frame of one transaction. -/
theorem TransactionTrace.settledFrames_ownCodeIn
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {F : Fork → Prop}
    (trace : TransactionTrace benv bout tx index state bout')
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  have msgInv := trace.msgInv_sem inv.state inv.ca
  have msgSum := trace.msg_sum_nof sumNof
  have msgF : F trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hF
  have msgGas : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact hsg
  intro f member
  exact trace.message.settledFrames_ownCodeIn nonempty nondelegating spawns
    msgInv msgSum msgF msgGas image f member

/-- Historical own code at every settled frame of a transaction list. -/
theorem ApplyTransactionsTrace.settledFrames_ownCodeIn {F : Fork → Prop}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  induction trace with
  | nil =>
      intro f member
      simp only [ApplyTransactionsTrace.settledFrames,
        List.not_mem_nil] at member
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      have headInv : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted_semIn preserves hF hsg admitted.1 sumNof inv K
          image
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hsg)
          sumNof
      intro f member
      simp only [ApplyTransactionsTrace.settledFrames, List.mem_append] at member
      rcases member with member | member
      · exact head.settledFrames_ownCodeIn nonempty nondelegating spawns inv
          sumNof hF hsg image f member
      · exact ih (by simpa only [Benv.withState] using hF)
          (by simpa only [Benv.withState] using hsg) admitted.2 headInv
          nextSum f member

/-- Historical own code at every settled frame of a system message. -/
theorem SystemMessageTrace.settledFrames_ownCodeIn
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput} {F : Fork → Prop}
    (trace : SystemMessageTrace benv target data state out)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  have msgInv : c.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv_sem inv.state inv.ca
  have msgSum :
      sum (systemTransactionMessage benv target data).benv.state.bal < 2 ^ 256 := by
    rw [systemTransactionMessage_benv_state]
    exact sumNof
  have msgF : F (systemTransactionMessage benv target data).benv.stat.fork :=
    hF
  have msgGas :
      (systemTransactionMessage benv target data).benv.stat.rules.stateGas =
        none :=
    hsg
  intro f member
  exact trace.message.settledFrames_ownCodeIn nonempty nondelegating spawns
    msgInv msgSum msgF msgGas image f member

/-- Historical own code at every settled frame of the two request calls. -/
theorem RequestsTrace.settledFrames_ownCodeIn {F : Fork → Prop}
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  have withdrawal := trace.withdrawal.stateInv_and_sum_le_admitted_semIn
    preserves hF hsg admitted.withdrawal inv K image
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    ⟨withdrawal.1, by simpa only [Benv.withState] using inv.ca⟩
  have withdrawalSum :
      sum (benv.withState trace.withdrawalState).state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (by simpa only [Benv.withState] using withdrawal.2) sumNof
  have hFwd : F (benv.withState trace.withdrawalState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsgwd : (benv.withState trace.withdrawalState).stat.rules.stateGas = none := by
    simpa only [Benv.withState] using hsg
  intro f member
  simp only [RequestsTrace.settledFrames, List.mem_append] at member
  rcases member with member | member
  · exact trace.withdrawal.settledFrames_ownCodeIn nonempty nondelegating
      spawns inv sumNof hF hsg image f member
  · exact trace.consolidation.settledFrames_ownCodeIn nonempty nondelegating
      spawns withdrawalInv withdrawalSum hFwd hsgwd image f member

/-- Historical own code at every settled frame of a beacon stage. -/
theorem BeaconStageTrace.settledFrames_ownCodeIn
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    {F : Fork → Prop}
    (trace : BeaconStageTrace rules benv state bal)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  cases trace with
  | skipped =>
      intro f member
      simp only [BeaconStageTrace.settledFrames] at member
      exact False.elim (List.not_mem_nil member)
  | called _ _ message _ _ =>
      intro f member
      exact message.settledFrames_ownCodeIn nonempty nondelegating spawns inv
        sumNof hF hsg image f member

/-- Historical own code at every settled frame of a history-storage stage. -/
theorem HistoryStageTrace.settledFrames_ownCodeIn
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder} {F : Fork → Prop}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  cases trace with
  | skipped =>
      intro f member
      simp only [HistoryStageTrace.settledFrames] at member
      exact False.elim (List.not_mem_nil member)
  | called _ _ _ _ message _ _ =>
      intro f member
      exact message.settledFrames_ownCodeIn nonempty nondelegating spawns inv
        sumNof hF hsg image f member

/-- Historical own code at every settled frame of a request stage. -/
theorem RequestStageTrace.settledFrames_ownCodeIn {F : Fork → Prop}
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  cases trace with
  | skipped =>
      intro f member
      simp only [RequestStageTrace.settledFrames] at member
      exact False.elim (List.not_mem_nil member)
  | called _ requests _ =>
      intro f member
      exact requests.settledFrames_ownCodeIn nonempty nondelegating spawns
        preserves hF hsg admitted inv sumNof K image f member

/-- Historical own code at every settled frame of a staged body. -/
theorem StagedBodyTrace.settledFrames_ownCodeIn {F : Fork → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  have openSum : sum benv.state.bal < 2 ^ 256 := by omega
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_semIn
    preserves hF hsg admitted.beacon inv K image
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, by simpa only [Benv.withState] using inv.ca⟩
  have beaconSum : sum (benv.withState trace.beaconState).state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (by simpa only [Benv.withState] using beacon.2) openSum
  have hFbeacon : F (benv.withState trace.beaconState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsgbeacon :
      (benv.withState trace.beaconState).stat.rules.stateGas = none := by
    simpa only [Benv.withState] using hsg
  have history := trace.history.stateInv_and_sum_le_admitted_semIn
    preserves hFbeacon hsgbeacon admitted.history beaconInv K image
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historyLe : sum trace.historyState.bal ≤ sum benv.state.bal :=
    le_trans (by simpa only [Benv.withState] using history.2) beacon.2
  have historySum : sum trace.historyState.bal < 2 ^ 256 := by omega
  have hFtx :
      F ((benv.withState trace.beaconState).withState trace.historyState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsgtx :
      ((benv.withState trace.beaconState).withState trace.historyState).stat.rules.stateGas =
        none := by
    simpa only [Benv.withState] using hsg
  have transactionsInv : c.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv_admitted_semIn preserves hFtx hsgtx
      admitted.transactions historySum historyInv K image
  have transactionLe : sum trace.transactionBenv.state.bal ≤ sum benv.state.bal :=
    le_trans (trace.transactions.sum_le_noStateGas (by simpa only [Benv.withState] using hsg))
      historyLe
  have txSum : sum trace.transactionBenv.state.bal < 2 ^ 256 := by omega
  have txWdBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    omega
  have txStat : trace.transactionBenv.stat = benv.stat :=
    trace.transactions.stat_eq
  have withdrawalInv : c.BenvInv ca
      (trace.transactionBenv.withState trace.withdrawalState) := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact ⟨transactionsInv.state, by simpa only [Benv.withState] using
          transactionsInv.ca⟩
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1]
        exact benvInv_processWithdrawalsState_sem transactionsInv (by omega)
  have requestSum :
      sum (trace.transactionBenv.withState trace.withdrawalState).state.bal <
        2 ^ 256 := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        simpa only [Benv.withState] using txSum
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        have wseq : trace.withdrawalState =
            processWithdrawalsState trace.transactionBenv.state wds :=
          (Prod.mk.inj run).1.symm
        rw [wseq]
        simpa only [Benv.withState] using
          processWithdrawalsState_sum_nof txWdBound
  have hFreq : F trace.transactionBenv.stat.fork := by
    rw [txStat]; exact hF
  have hsgreq : trace.transactionBenv.stat.rules.stateGas = none := by
    rw [txStat]; exact hsg
  have hFreqWs : F (trace.transactionBenv.withState
      trace.withdrawalState).stat.fork := by
    simpa only [Benv.withState] using hFreq
  have hsgreqWs : (trace.transactionBenv.withState
      trace.withdrawalState).stat.rules.stateGas = none := by
    simpa only [Benv.withState] using hsgreq
  intro f member
  simp only [StagedBodyTrace.settledFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact trace.beacon.settledFrames_ownCodeIn nonempty nondelegating spawns
      inv openSum hF hsg image f member
  · exact trace.history.settledFrames_ownCodeIn nonempty nondelegating spawns
      beaconInv beaconSum hFbeacon hsgbeacon image f member
  · exact trace.transactions.settledFrames_ownCodeIn nonempty nondelegating
      spawns preserves hFtx hsgtx admitted.transactions historyInv historySum
      K image f member
  · exact trace.requests.settledFrames_ownCodeIn nonempty nondelegating spawns
      preserves hFreqWs hsgreqWs admitted.requests withdrawalInv requestSum
      K image f member

/-- Historical own code at every settled frame of a configured In-block. -/
theorem ConfiguredBlockTraceIn.settledFrames_ownCodeIn {F : Fork → Prop}
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn ca C)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca pre.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F ca C f := by
  intro f member
  exact trace.bodyTrace.settledFrames_ownCodeIn nonempty nondelegating spawns
    preserves trace.forkIn (capabilities.stateGas_none trace.forkIn) admitted
    trace.withdrawalsBound ⟨inv, AdrSet.not_mem_empty⟩ K image f member

/-- **Installed code at every settled frame of an In-history on a historical
fork.** If `C` is installed at `a` at the checkpoint, is nonempty and is no
designator, selected-domain frames running `C` at `a` spawn only by `CALL`,
`STATICCALL` or `CREATE2` (`OwnSpawnsIn`), then every settled frame of the
history finds `C` at `a` when it starts, enters at pc `0` under the selected
domain with no state gas and, if it runs at `a`, runs `C`. The storage-only
specification preserves itself trivially; no coverage premise is needed. -/
theorem ConfiguredHistoryTraceIn.settled_ownCodeIn (sem : CodeSem) (a : Adr)
    {F : Fork → Prop} {C : ByteArray}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (spawns : OwnSpawnsIn a C)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (rewards : history.RewardCreditsFunded)
    (installed : some (checkpoint.state.getCode a).toList = sem.image)
    (K : InstalledCert C) (image : sem.image = some C.toList) :
    ∀ f ∈ history.settledFrames, OwnCodeAtIn F a C f := by
  have admitted : history.FrameAdmitted a (fun _ _ => True) :=
    (history.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial
  have preserves :
      (ContractSpecSem.ofStorageOnly sem (fun _ => True)).PreservesAdmittedIn
        F a (fun _ _ => True) :=
    fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩
  have inv : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).StateInv
      a checkpoint.state :=
    ⟨installed, trivial, trivial⟩
  induction history with
  | refl =>
      intro f member
      simp only [ConfiguredHistoryTraceIn.settledFrames,
        List.not_mem_nil] at member
  | step prior block ih =>
      intro f member
      simp only [ConfiguredHistoryTraceIn.settledFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih rewards.1 admitted.1 f member
      · exact block.settledFrames_ownCodeIn nonempty nondelegating spawns
          preserves capabilities admitted.2
          (prior.stateInv_admitted_semIn preserves capabilities admitted.1
            rewards.1 inv K image) K image f member

end ExecutionTrace

end Blanc
