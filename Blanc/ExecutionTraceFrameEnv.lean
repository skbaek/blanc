import Blanc.ExecutionMessageGas
import Blanc.ExecutionTraceCalldata
import Blanc.ExecutionTransactionGas
import Blanc.ExecutionTraceSystemCode
import Blanc.ExecutionCodeAt
import Blanc.Lift.CallerProvenance
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionTraceCodeAt

/-!
# Generic environment discharge for per-frame walk premises

Frame walks and contract frame theorems take premises about the frame's entry that a configured
history determines without any per-frame assumption, or with only trace-local ones.  This module
discharges three of them once, for every contract:

* **Entry gas fits a word** (`ConfiguredHistoryTrace.gas_bound`,
  `ConfiguredHistoryTrace.frameAdmitted_gas`).  Frame walks start from `pre.gasMeasure < 2 ^ 256`.
  Inside one execution no entered frame starts with more gas than the execution's root
  (`Exec.rawFrameRoots_gas_le`: a spawn passes `frame.inner.gas < pre.gasMeasure`,
  `Evm.step_gasBound`; the child starts with exactly that, `Frame.enter_run_gasMeasure`; the parent
  resumes with no more than it had).  A message's root frame starts with the message grant
  (delegation and code resolution keep it); a transaction's grant is below `tx.gas`, which
  `checkTransaction` keeps below the block gas limit, which header validation keeps below `2 ^ 63`
  (`ConfiguredBlockTrace.header_gasLimit_lt`); a system message's grant is `systemTransactionGas`.
  So every raw frame of a configured history starts with `gasMeasure < 2 ^ 64`.
* **Children keep the code at an address no CREATE frame targets**
  (`Exec.childFrames_codeAt_keep`), from `Exec.codeAt_avoid` on each committed direct child.
* **System frames never target a contract whose code differs in size from every canonical
  system code** (`not_mem_systemTargets_of_size`, `ConfiguredHistoryTrace.system_ne_of_size`),
  hoisted from the Beacon deposit contract.
-/

namespace Blanc

open Jaune

/-! ## Direct children keep the code at an address no CREATE frame targets -/

/-- **Every committed direct child of an execution keeps the code at `a`**, when the execution
enters no CREATE frame targeting `a` (`Exec.codeAt_avoid` on each child). -/
theorem Exec.childFrames_codeAt_keep {a : Adr} :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      CoveredFork sevm.benvStat.fork →
      (∀ root ∈ Exec.rawFrameRoots run,
        root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) →
      ∀ c ∈ Exec.childFrames run, c.post.getCode a = c.pre.getCode a := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
    intro _ _ c member
    simp only [Exec.childFrames, List.not_mem_nil] at member
  | @cont pc sevm devm pc' devm' ex step next ih =>
    intro hfork avoid
    have hself := avoid _ (List.mem_cons_self ..)
    refine ih hfork ?_
    intro root member
    simp only [Exec.rawFrameRoots, List.mem_cons] at member
    rcases member with rfl | member
    · exact hself
    · exact avoid root (by
        simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons, member, or_true])
  | doneErr _ _ _ =>
    intro _ _ c member
    simp only [Exec.childFrames, List.not_mem_nil] at member
  | @doneOk pc sevm devm frame resume pc' result devm' ex step enter resumed next ih =>
    intro hfork avoid
    have hself := avoid _ (List.mem_cons_self ..)
    refine ih hfork ?_
    intro root member
    simp only [Exec.rawFrameRoots, List.mem_cons] at member
    rcases member with rfl | member
    · exact hself
    · exact avoid root (by
        simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons, member, or_true])
  | runErr _ _ _ _ =>
    intro _ _ c member
    simp only [Exec.childFrames, List.not_mem_nil] at member
  | @runOk pc sevm devm frame resume pc' cevm raw devm' ex step enter child resumed next
      childIh nextIh =>
    intro hfork avoid c member
    have hself := avoid _ (List.mem_cons_self ..)
    simp only [Exec.childFrames, List.mem_append] at member
    rcases member with here | later
    · split at here
      · rename_i committed
        rw [List.mem_singleton] at here
        subst here
        have forkc := (ExecutionTrace.Evm.step_spawn_child_data hfork step enter).2
        have keep := (Exec.codeAt_avoid child forkc (by
          intro root member
          exact avoid root (by
            simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
              List.mem_append] at member ⊢
            rcases member with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))))).1
        cases raw with
        | error _ =>
          have raw := Frame.raw_commits_of_settlementCommits committed
          simp only [Execution.commits, Bool.false_eq_true] at raw
        | ok childPost => exact keep
      · simp only [List.not_mem_nil] at here
    · refine nextIh hfork ?_ c later
      intro root member
      simp only [Exec.rawFrameRoots, List.mem_cons] at member
      rcases member with rfl | member
      · exact hself
      · exact avoid root (by
          simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
            List.mem_append, member, or_true])

/-- No entered frame of an execution starts with more gas than the execution's own root. -/
theorem Exec.rawFrameRoots_gas_le {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    ∀ root ∈ Exec.rawFrameRoots run, root.devm.gasMeasure ≤ pre.gasMeasure := by
  induction run with
  | halt hstep =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
      List.not_mem_nil, or_false] at member
    subst member
    exact Nat.le_refl _
  | @cont pc sevm pre pc' inter out step next ih =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
    have bound := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at bound
    change inter.gasMeasure < pre.gasMeasure at bound
    rcases member with rfl | member
    · exact Nat.le_refl _
    · have tail := ih root (by simp only [Exec.rawFrameRoots, List.mem_cons, member, or_true])
      omega
  | doneErr hstep henter hresume =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
      List.not_mem_nil, or_false] at member
    subst member
    exact Nat.le_refl _
  | @doneOk pc sevm pre frame resume pc' result inter out step enter resumed next ih =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
    have spawn := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at spawn
    change frame.inner.gas + resume.parentGas < pre.gasMeasure ∧ _ at spawn
    have resumedGas := Resume.run_gasLe (rsm := resume) (m := frame.inner.gas)
      (fun d hd => Frame.enter_done_gasLe enter hd)
    rw [resumed, Execution.gasMeasure_ok] at resumedGas
    rcases member with rfl | member
    · exact Nat.le_refl _
    · have tail := ih root (by simp only [Exec.rawFrameRoots, List.mem_cons, member, or_true])
      omega
  | @runErr pc sevm pre frame resume pc' childEvm raw error step enter child resumed ih =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
    have spawn := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at spawn
    change frame.inner.gas + resume.parentGas < pre.gasMeasure ∧ _ at spawn
    have childRoot := Frame.enter_run_gasMeasure enter
    rcases member with rfl | rfl | member
    · exact Nat.le_refl _
    · change childEvm.dyna.gasMeasure ≤ pre.gasMeasure
      omega
    · have tail := ih root (by simp only [Exec.rawFrameRoots, List.mem_cons, member, or_true])
      omega
  | @runOk pc sevm pre frame resume pc' childEvm raw inter out
      step enter child resumed next childIH nextIH =>
    intro root member
    simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
      List.mem_append] at member
    have spawn := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at spawn
    change frame.inner.gas + resume.parentGas < pre.gasMeasure ∧ _ at spawn
    have childRoot := Frame.enter_run_gasMeasure enter
    rcases member with rfl | rfl | member | member
    · exact Nat.le_refl _
    · change childEvm.dyna.gasMeasure ≤ pre.gasMeasure
      omega
    · have tail := childIH root
        (by simp only [Exec.rawFrameRoots, List.mem_cons, member, or_true])
      omega
    · have childGas : raw.SettledGasLe frame.inner.gas := by
        intro sg d hd
        have budget := Exec.descendantFrames_settledGas child sg d hd
        rw [childRoot] at budget
        omega
      have resumedGas := Resume.run_gasLe (rsm := resume) (r := frame.settle raw)
        (m := frame.inner.gas) (fun d hd => Frame.settle_gasLe childGas hd)
      rw [resumed, Execution.gasMeasure_ok] at resumedGas
      have tail := nextIH root
        (by simp only [Exec.rawFrameRoots, List.mem_cons, member, or_true])
      omega

namespace ExecutionTrace

/-! ## From retained slots to whole histories -/

/-- A retained slot enters only frames with at most its frame's grant. -/
theorem RetainedXlot.rawFrames_gas_le {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out) :
    ∀ root ∈ retained.rawFrames, root.devm.gasMeasure ≤ frame.inner.gas := by
  cases retained with
  | none => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
    obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
    have hroot := Frame.enter_run_gasMeasure henter
    dsimp only at hroot
    intro root member
    have bound := Exec.rawFrameRoots_gas_le run root member
    omega

theorem ProcessMessageTrace.rawFrames_gas_le {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ msg.gas :=
  RetainedXlot.rawFrames_gas_le trace.retained trace.run

theorem ProcessCreateMessageTrace.rawFrames_gas_le {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ msg.gas := by
  intro root member
  have bound := RetainedXlot.rawFrames_gas_le trace.retained trace.run root member
  have gas : (Frame.ofCreate msg).inner.gas = msg.gas := processCreateMessage.msg_gas msg
  rw [gas] at bound
  exact bound

/-- A settled message call enters only frames with at most the message grant. -/
theorem MessageCallTrace.rawFrames_gas_le {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ msg.gas := by
  cases trace with
  | createCollision _ _ _ =>
    intro root hmem
    simp only [rawFrames, List.not_mem_nil] at hmem
  | createRun _ _ _ _ core _ =>
    intro root hmem
    simp only [MessageCallTrace.rawFrames] at hmem
    exact core.rawFrames_gas_le root hmem
  | callRun _ delegated refund hdel execMsg hexec _ _ core _ =>
    intro root hmem
    simp only [MessageCallTrace.rawFrames] at hmem
    have bound := core.rawFrames_gas_le root hmem
    rw [hexec, messageCallExecutionMessage_gas, messageCallDelegation_gas hdel] at bound
    exact bound

/-- A transaction enters only frames with gas below the block gas limit. -/
theorem TransactionTrace.rawFrames_gas_lt {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < benv.stat.blockGasLimit := by
  have grant := trace.msg_gas_succ_le hfork
  have room := trace.gas_le_remaining hfork
  intro root hmem
  simp only [TransactionTrace.rawFrames] at hmem
  have bound := trace.message.rawFrames_gas_le root hmem
  change tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed at room
  omega

theorem SystemMessageTrace.rawFrames_gas_le {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ systemTransactionGas := by
  intro root hmem
  simp only [SystemMessageTrace.rawFrames] at hmem
  exact trace.message.rawFrames_gas_le root hmem

theorem ApplyTransactionsTrace.rawFrames_gas_lt
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < benv.stat.blockGasLimit := by
  induction trace with
  | nil => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | cons head tail ih =>
    intro root member
    simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
    rcases member with member | member
    · exact head.rawFrames_gas_lt hfork root member
    · exact ih hfork root member

/-- A block body enters only frames with gas below the larger of the block gas limit and the
system-message grant. -/
theorem AppliedBodyTrace.rawFrames_gas_lt {benv : Benv}
    {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames,
      root.devm.gasMeasure < benv.stat.blockGasLimit + systemTransactionGas + 1 := by
  intro root hmem
  simp only [AppliedBodyTrace.rawFrames, List.mem_append, RequestsTrace.rawFrames] at hmem
  rcases hmem with ((hmem | hmem) | hmem) | hmem | hmem
  · have bound := trace.beacon.rawFrames_gas_le root hmem
    omega
  · have bound := trace.history.rawFrames_gas_le root hmem
    omega
  · have bound := trace.transactions.rawFrames_gas_lt hfork root hmem
    change root.devm.gasMeasure < benv.stat.blockGasLimit at bound
    omega
  · have bound := trace.requests.withdrawal.rawFrames_gas_le root hmem
    omega
  · have bound := trace.requests.consolidation.rawFrames_gas_le root hmem
    omega

/-- Every raw frame of a configured block starts with `gasMeasure < 2 ^ 64`. -/
theorem ConfiguredBlockTrace.rawFrames_gas_lt {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTrace cfg pre post) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < 2 ^ 64 := by
  have hlim := trace.header_gasLimit_lt
  intro root hmem
  simp only [ConfiguredBlockTrace.rawFrames] at hmem
  have bound := trace.bodyTrace.rawFrames_gas_lt trace.covered root hmem
  change root.devm.gasMeasure <
    trace.block.header.gasLimit + systemTransactionGas + 1 at bound
  simp only [systemTransactionGas] at bound
  omega

/-- **Every raw frame of a configured history starts with `gasMeasure < 2 ^ 64`**, with no
per-frame premise. -/
theorem ConfiguredHistoryTrace.gas_bound {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < 2 ^ 64 := by
  induction trace with
  | refl _ _ _ => intro root hmem; simp only [rawFrames, List.not_mem_nil] at hmem
  | step prior block ih =>
    intro root hmem
    simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact ih root hmem
    · exact block.rawFrames_gas_lt root hmem

/-- Admission corollary: the per-frame word-gas premise of frame walks follows from the trace. -/
theorem ConfiguredHistoryTrace.frameAdmitted_gas {cfg : ChainConfig}
    {checkpoint future : BlockChain} {ca : Adr}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    trace.FrameAdmitted ca (fun _ pre => pre.gasMeasure < 2 ^ 256) := by
  rw [ConfiguredHistoryTrace.frameAdmitted_iff_rawFrames]
  intro root member _
  have bound := trace.gas_bound root member
  omega

/-- An address whose installed code has a size no canonical system code has is not a system
address. -/
theorem not_mem_systemTargets_of_size {w : State} {ca : Adr} {c : ByteArray}
    (installed : w.getCode ca = c) (system : SystemCodeInstalled w)
    (size : ∀ p ∈ systemContracts, p.2.size ≠ c.size) :
    ca ∉ systemTargets := by
  intro hmem
  have hsize : ∀ p ∈ systemContracts, p.1 = ca → False := by
    intro p hp hca
    have h := system p hp
    rw [hca, installed] at h
    exact size p hp (congrArg ByteArray.size h).symm
  simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hsize (beaconRootsAddress, beaconRootsCode) (by simp only [systemContracts,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, true_or]) rfl
  · exact hsize (historyStorageAddress, historyStorageCode) (by simp only [systemContracts,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, true_or, or_true]) rfl
  · exact hsize (withdrawalRequestPredeployAddress, withdrawalRequestCode)
      (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
        true_or, or_true]) rfl
  · exact hsize (consolidationRequestPredeployAddress, consolidationRequestCode)
      (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
        or_true]) rfl

/-- **No system frame targets a contract whose installed code differs in size from every
canonical system code**, under the canonical system code installed at the checkpoint and the
trace-local system exclusions. -/
theorem ConfiguredHistoryTrace.system_ne_of_size {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {ca : Adr} {c : ByteArray}
    (systemInstalled : SystemCodeInstalled checkpoint.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (systemNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1)
    (installed : checkpoint.state.getCode ca = c)
    (size : ∀ p ∈ systemContracts, p.2.size ≠ c.size) :
    ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ ca := by
  intro root member h
  obtain ⟨hframes, -⟩ := trace.systemFrames_of_installed systemInstalled systemNoAuthority
    systemNoFrame
  exact not_mem_systemTargets_of_size installed systemInstalled size (h ▸ hframes root member)

/-! ## The raw frames of a history are closed under descent

Every frame a raw frame enters is itself a raw frame of the history.  So a trace-local premise over
`trace.rawFrames` (such as "no CREATE frame targets `a`") covers every frame below a given raw
frame, which is what per-frame consumers like `Exec.childFrames_codeAt_keep` need. -/

/-- A list of raw frames closed under descent: each member's own raw frame roots are members. -/
def RawFramesClosed (frames : List Exec.Deriv) : Prop :=
  ∀ d ∈ frames, ∀ e ∈ Exec.rawFrameRoots d.exc, e ∈ frames

theorem RawFramesClosed.nil : RawFramesClosed [] := by
  intro d member
  simp only [List.not_mem_nil] at member

theorem RawFramesClosed.append {left right : List Exec.Deriv} (hl : RawFramesClosed left)
    (hr : RawFramesClosed right) : RawFramesClosed (left ++ right) := by
  intro d member e he
  rcases List.mem_append.mp member with h | h
  · exact List.mem_append_left _ (hl d h e he)
  · exact List.mem_append_right _ (hr d h e he)

theorem RawFramesClosed.roots {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : RawFramesClosed (Exec.rawFrameRoots run) :=
  fun _ hd _ he => Exec.rawFrameRoots_trans hd he

theorem RetainedXlot.rawFrames_closed {slot : Xlot} (retained : RetainedXlot slot) :
    RawFramesClosed retained.rawFrames := by
  cases retained with
  | none => exact RawFramesClosed.nil
  | some run => exact RawFramesClosed.roots run

theorem MessageCallTrace.rawFrames_closed {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) : RawFramesClosed trace.rawFrames := by
  cases trace with
  | createCollision => exact RawFramesClosed.nil
  | createRun _ _ _ _ core _ => exact core.retained.rawFrames_closed
  | callRun _ _ _ _ _ _ _ _ core _ => exact core.retained.rawFrames_closed

theorem ApplyTransactionsTrace.rawFrames_closed
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    RawFramesClosed trace.rawFrames := by
  induction trace with
  | nil => exact RawFramesClosed.nil
  | cons head tail ih => exact RawFramesClosed.append head.message.rawFrames_closed ih

theorem AppliedBodyTrace.rawFrames_closed {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) : RawFramesClosed trace.rawFrames :=
  RawFramesClosed.append (RawFramesClosed.append (RawFramesClosed.append
    trace.beacon.message.rawFrames_closed trace.history.message.rawFrames_closed)
    trace.transactions.rawFrames_closed)
    (RawFramesClosed.append trace.requests.withdrawal.message.rawFrames_closed
      trace.requests.consolidation.message.rawFrames_closed)

/-- **The raw frames of a configured history are closed under descent.** -/
theorem ConfiguredHistoryTrace.rawFrames_closed {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    RawFramesClosed trace.rawFrames := by
  induction trace with
  | refl => exact RawFramesClosed.nil
  | step prior block ih => exact RawFramesClosed.append ih block.bodyTrace.rawFrames_closed

/-- **Children keep the code at an address no CREATE frame of the history targets**: every
committed direct child of every raw frame of the history leaves the code at `a` as it found it. -/
theorem ConfiguredHistoryTrace.childFrames_codeAt_keep {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    {a : Adr}
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    ∀ root ∈ trace.rawFrames, ∀ c ∈ Exec.childFrames root.exc,
      c.post.getCode a = c.pre.getCode a := by
  intro root member
  exact Exec.childFrames_codeAt_keep root.exc (trace.rootEntry root member).2
    (fun d hd => noFrame d (trace.rawFrames_closed root member d hd))

/-- **A precompile is ready at every transaction frame**: warm (the transaction pre-warm) and
without an EIP-7702 delegation designator (empty code, from empty code at the checkpoint, no
authorization recovering to it and no CREATE frame targeting it). -/
theorem ConfiguredHistoryTrace.precompileReady {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    {a : Adr} (precompile : ∀ f, CoveredFork f → a ∈ (Fork.ruleSet f).precompiles)
    (checkpointEmpty : checkpoint.state.getCode a = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt a)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    ∀ root ∈ trace.txRawFrames, getDelegatedCodeAddress (root.devm.getCode a) = none ∧
      a ∈ root.devm.accessedAddresses := by
  intro root member
  obtain ⟨hcode, -⟩ := trace.codeAt_empty noAuthority noFrame checkpointEmpty
  refine ⟨?_, trace.txRawFrames_warm precompile root member⟩
  have hnot : ¬ isValidDelegation ByteArray.empty := fun h => absurd h.1 (by decide)
  rw [hcode root member]
  simp only [getDelegatedCodeAddress, hnot, ↓reduceIte]

end ExecutionTrace

end Blanc
