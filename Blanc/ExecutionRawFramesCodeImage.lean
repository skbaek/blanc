import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionBodyPrefixAdmission
import Blanc.ExecutionTraceCodeAt
import Blanc.LockExclusion
import Blanc.StorageOnlySpec

/-!
# A certified code image at every raw frame of a history (contract-neutral)

`ConfiguredHistoryTrace.rawFrames_codeImage`: if the checkpoint holds the image of `c.sem` at `ca`
and `c` is preserved under an admission the history meets, every raw frame of the history (rolled
back or not) starts with that image at `ca`.

The state invariant `c.StateInv` (which carries the image) reaches every message entry along the
admitted rungs (`*.stateInv_admitted_sem`, `MsgInv`); inside one message, an entered frame keeps
every nonempty code of its entry at each raw root (`Exec.rawFrameRoots_codePreserve`).
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

open ContractSpecSem

variable {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}

/-- The raw roots of a retained slot keep a code image of the frame's entry world. -/
theorem RetainedXlot.rawFrames_codeImage {sem : CodeSem} {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} (retained : RetainedXlot slot)
    (hrun : RunFrame frame slot out)
    (image : Option.some (frame.inner.benv.state.getCode ca).toList = sem.image) :
    ∀ root ∈ retained.rawFrames, Option.some (root.devm.getCode ca).toList = sem.image := by
  cases retained with
  | none => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hcode : pre.getCode ca = frame.inner.benv.state.getCode ca :=
        Frame.enter_run_getCode henter ca
      have nonempty : (pre.getCode ca).toList ≠ [] := fun empty =>
        sem.ne_nil (image.symm.trans (by rw [← hcode, empty])) rfl
      intro root member
      rw [Exec.rawFrameRoots_codePreserve run ca nonempty root member, hcode]
      exact image

theorem MessageCallTrace.rawFrames_codeImage {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (ready : c.MsgInv ca msg) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  cases trace with
  | createCollision target collision result =>
      intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | createRun target collision evm core coreTrace result =>
      intro root member
      refine RetainedXlot.rawFrames_codeImage coreTrace.retained coreTrace.run ?_ root member
      change some ((processCreateMessage.msg msg).benv.state.getCode ca).toList = _
      rw [processCreateMessage.msg_getCode]
      exact ready.state.code
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      have execReady : c.MsgInv ca execMsg := by
        rw [execMsgEq]
        exact (ready.of_messageCallDelegation delegation).messageCallExecutionMessage
      intro root member
      exact RetainedXlot.rawFrames_codeImage coreTrace.retained coreTrace.run execReady.state.code
        root member

theorem TransactionTrace.rawFrames_codeImage {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') (inv : c.BenvInv ca benv) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image :=
  trace.message.rawFrames_codeImage (trace.msgInv_sem inv.state inv.ca)

theorem ApplyTransactionsTrace.rawFrames_codeImage {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (preserves : c.PreservesAdmitted ca entry) (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry) (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  induction trace with
  | nil => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      have headInv : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted_sem preserves hfork admitted.1 sumNof inv
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hfork.rules_stateGas_none)
          sumNof
      intro root member
      simp only [rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact head.rawFrames_codeImage inv root member
      · exact ih hfork admitted.2 nextSum headInv root member

theorem SystemMessageTrace.rawFrames_codeImage {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out)
    (inv : c.BenvInv ca benv) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image :=
  trace.message.rawFrames_codeImage (systemTransactionMessage_msgInv_sem inv.state inv.ca)

theorem RequestsTrace.rawFrames_codeImage {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout')
    (preserves : c.PreservesAdmitted ca entry) (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry) (inv : c.BenvInv ca benv) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  have withdrawal := trace.withdrawal.stateInv_and_sum_le_admitted_sem
    preserves hfork admitted.withdrawal inv
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    ⟨withdrawal.1, by simpa only [Benv.withState] using inv.ca⟩
  intro root member
  simp only [rawFrames, List.mem_append] at member
  rcases member with member | member
  · exact trace.withdrawal.rawFrames_codeImage inv root member
  · exact trace.consolidation.rawFrames_codeImage withdrawalInv root member

theorem AppliedBodyTrace.rawFrames_codeImage {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) (preserves : c.PreservesAdmitted ca entry)
    (hfork : CoveredFork benv.stat.fork) (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) (inv : c.BenvInv ca benv) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_sem
    preserves hfork admitted.beacon inv
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, by simpa only [Benv.withState] using inv.ca⟩
  have history := trace.history.stateInv_and_sum_le_admitted_sem
    preserves (by simpa only [Benv.withState] using hfork) admitted.history beaconInv
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historySum : sum trace.historyState.bal < 2 ^ 256 := by
    have : sum trace.historyState.bal ≤ sum benv.state.bal :=
      le_trans (by simpa only [Benv.withState] using history.2) beacon.2
    omega
  have requestInv : c.BenvInv ca trace.requestBenv :=
    trace.requestBenvInv_admitted_sem preserves hfork admitted bound inv
  intro root member
  simp only [rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact trace.beacon.rawFrames_codeImage inv root member
  · exact trace.history.rawFrames_codeImage beaconInv root member
  · exact trace.transactions.rawFrames_codeImage preserves
      (by simpa only [Benv.withState] using hfork) admitted.transactions historySum historyInv
      root member
  · exact trace.requests.rawFrames_codeImage preserves (trace.requestBenv_covered hfork)
      admitted.requests requestInv root member

theorem ConfiguredBlockTrace.rawFrames_codeImage {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry) (inv : c.StateInv ca pre.state) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image :=
  trace.bodyTrace.rawFrames_codeImage preserves trace.covered admitted trace.openingBound
    ⟨inv, trace.not_mem_openingCreatedAccounts ca⟩

/-- **A certified code image at every raw frame of a history.** -/
theorem ConfiguredHistoryTrace.rawFrames_codeImage {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (preserves : c.PreservesAdmitted ca entry) (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca checkpoint.state) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  induction trace with
  | refl => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro root member
      simp only [rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih admitted.1 root member
      · exact block.rawFrames_codeImage preserves admitted.2
          (prior.stateInv_admitted_sem preserves admitted.1 inv) root member

/-- **A certified code image installed at the checkpoint is at every raw frame** of the history,
rolled-back frames included. -/
theorem ConfiguredHistoryTrace.rawFrames_codeImage_of_installed (sem : CodeSem) (a : Adr)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode a).toList = sem.image) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode a).toList = sem.image :=
  trace.rawFrames_codeImage (c := ContractSpecSem.ofStorageOnly sem (fun _ => True)) (ca := a)
    (entry := fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)
    ((trace.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial) ⟨installed, trivial, trivial⟩

end ExecutionTrace

end Blanc
