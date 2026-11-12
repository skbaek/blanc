import Blanc.ExecutionKeptFresh
import Blanc.Lift.TargetLogEvents
import Blanc.ExecutionSettledReceiptLogs
import Blanc.RlpReceiptKeys
import Blanc.TransactionHistoricalForward

/-! # Log sequence compatibility of the existing kept and committed projections -/

namespace Blanc

open Jaune

open private Frame_enter_run_logs_noStateGas from Blanc.Lift.CommittedLogs

/-- A frame's added logs are the existing committed boundary ledger, at any original path. -/
theorem Exec.addedLogs_eq_ownLogs
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none) (path : List Nat) (counter : Nat) :
    (Execution.committedPost out committed).logs.drop pre.logs.length =
      (Exec.stateBoundariesOfCommits path counter run committed).flatMap
        Exec.boundaryOwnLogs := by
  rw [Exec.committed_logs_at_noStateGas run committed hsg rfl rfl path counter,
    List.drop_length_append' rfl]

private theorem Exec.logAt_filter_of_foreign
    {a : Adr} {keep : Log → Bool}
    (address : ∀ log, keep log = true → log.address = a)
    {pc : Nat} {sevm : Sevm} {pre : Devm} (foreign : sevm.currentTarget ≠ a) :
    (Exec.logAt? pc sevm pre).toList.filter keep = [] := by
  unfold Exec.logAt?
  split <;> try rfl
  rename_i n decoded
  split <;> try rfl
  rename_i mi sz rest stackEq
  have skipped : keep ⟨sevm.currentTarget, rest.take n.val,
      (pre.memory.read mi.toNat sz.toNat).1⟩ = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    exact foreign (address _ selected)
  simp only [Option.toList_some, List.filter_cons, skipped, Bool.false_eq_true,
    ↓reduceIte, List.filter_nil]

/-- Filtering the original committed ledger by an address selects precisely the added
logs of the existing kept traversal, in order. Foreign LOGs disappear by their actual
emitter address; discarded settlements disappear in the existing ledger. -/
theorem Exec.keptAt_ownLogs
    {a : Adr} {keep : Log → Bool}
    (address : ∀ log, keep log = true → log.address = a)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none) (foreign : sevm.currentTarget ≠ a)
    (path : List Nat) (counter : Nat) :
    ((Exec.stateBoundariesOfCommits path counter run committed).flatMap
      Exec.boundaryOwnLogs).filter keep =
      (Exec.keptAt a run).flatMap
        (fun frame => (frame.post.logs.drop frame.pre.logs.length).filter keep) := by
  induction run generalizing path counter with
  | halt step =>
      simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, List.flatMap_nil,
        Exec.boundaryOwnLogs, Exec.stateBoundary, List.nil_append, List.filter_nil,
        Exec.keptAt]
  | cont step next ih =>
      simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons,
        Exec.boundaryOwnLogs, Exec.stateBoundary, Exec.Frame.rootDeriv, Exec.Frame.ofRun,
        Exec.Deriv.successfulLog?, List.filter_append, Exec.keptAt]
      rw [Exec.logAt_filter_of_foreign address foreign, List.nil_append]
      exact ih committed hsg foreign path counter
  | doneErr step enter resumed =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resumed next ih =>
      simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, Exec.boundaryOwnLogs,
        Exec.stateBoundary, List.nil_append, Exec.keptAt]
      exact ih committed hsg foreign path (counter + 1)
  | runErr step enter child resumed ih =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre callee resume pc' childEvm raw inter out step enter child resumed next
      childIH nextIH =>
      simp only [Exec.stateBoundariesOfCommits, Exec.keptAt]
      by_cases settles : Frame.settlementCommits callee raw = true
      · rw [dite_eq_left settles, dite_eq_left settles]
        simp only [List.flatMap_cons, List.flatMap_append, Exec.boundaryOwnLogs,
          Exec.stateBoundary, List.nil_append, List.filter_append]
        rw [nextIH committed hsg foreign path (counter + 1)]
        have childSg : childEvm.sta.benvStat.rules.stateGas = none := by
          rw [Evm.step_spawn_child_benvStat step enter]
          exact hsg
        by_cases target : childEvm.sta.currentTarget = a
        · rw [ite_eq_left target]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
            Exec.Frame.post, Exec.Frame.ofRun]
          rw [Exec.addedLogs_eq_ownLogs child
            (Frame.raw_commits_of_settlementCommits settles) childSg (path ++ [counter]) 0]
        · rw [ite_eq_right target,
            childIH (Frame.raw_commits_of_settlementCommits settles) childSg target
              (path ++ [counter]) 0]
      · rw [dite_eq_right settles, dite_eq_right settles]
        simp only [List.flatMap_cons, Exec.boundaryOwnLogs, Exec.stateBoundary,
          List.nil_append]
        exact nextIH committed hsg foreign path (counter + 1)

/-- Root selection folds precisely that root's committed added logs. -/
theorem Root.keptAt_logs {a : Adr} {keep : Log → Bool}
    (address : ∀ log, keep log = true → log.address = a) (root : Root)
    (hsg : root.evm.sta.benvStat.rules.stateGas = none) :
    (root.keptAt a).flatMap
        (fun frame => (frame.post.logs.drop frame.pre.logs.length).filter keep) =
      if committed : Frame.settlementCommits root.frame root.raw = true then
        ((Execution.committedPost root.raw
          (Frame.raw_commits_of_settlementCommits committed)).logs.drop
            root.evm.dyna.logs.length).filter keep
      else [] := by
  unfold Root.keptAt
  split
  next committed =>
    by_cases target : root.evm.sta.currentTarget = a
    · rw [ite_eq_left target]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        Exec.Frame.post, Exec.Frame.ofRun]
    · rw [ite_eq_right target, Exec.addedLogs_eq_ownLogs root.run
        (Frame.raw_commits_of_settlementCommits committed) hsg [] 0]
      exact (Exec.keptAt_ownLogs address root.run
        (Frame.raw_commits_of_settlementCommits committed) hsg target [] 0).symm
  next rolled => rfl

private theorem Exec.keptAt_filter_descendantFrames_of_leaves
    {a : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (leaves : ∀ fr ∈ Exec.descendantFrames run, fr.sevm.currentTarget = a →
      Exec.descendantFrames fr.run = []) :
    Exec.keptAt a run = (Exec.descendantFrames run).filter
      (fun fr => decide (fr.sevm.currentTarget = a)) := by
  induction run with
  | halt _ => simp only [Exec.keptAt, Exec.descendantFrames, List.filter_nil]
  | cont _ next ih =>
    simp only [Exec.keptAt, Exec.descendantFrames] at leaves ⊢
    exact ih leaves
  | doneErr _ _ _ => simp only [Exec.keptAt, Exec.descendantFrames, List.filter_nil]
  | doneOk _ _ _ next ih =>
    simp only [Exec.keptAt, Exec.descendantFrames] at leaves ⊢
    exact ih leaves
  | runErr _ _ _ _ => simp only [Exec.keptAt, Exec.descendantFrames, List.filter_nil]
  | @runOk pc sevm pre frame resume pcNext childEvm raw inter out step enter child resumed next
      childIH nextIH =>
    by_cases settles : Frame.settlementCommits frame raw = true
    · simp only [Exec.keptAt, Exec.descendantFrames, dite_eq_left settles] at leaves ⊢
      have childLeaves : ∀ fr ∈ Exec.descendantFrames child, fr.sevm.currentTarget = a →
          Exec.descendantFrames fr.run = [] := fun fr member target =>
        leaves fr (List.mem_cons_of_mem _ (List.mem_append_left _ member)) target
      have nextLeaves : ∀ fr ∈ Exec.descendantFrames next, fr.sevm.currentTarget = a →
          Exec.descendantFrames fr.run = [] := fun fr member target =>
        leaves fr (List.mem_cons_of_mem _ (List.mem_append_right _ member)) target
      rw [List.filter_append, List.filter_cons, nextIH nextLeaves]
      by_cases target : childEvm.sta.currentTarget = a
      · have empty : Exec.descendantFrames child = [] := leaves _ List.mem_cons_self target
        rw [ite_eq_left target, empty, List.filter_nil]
        have selected : decide ((Exec.Frame.ofRun child
            (Frame.raw_commits_of_settlementCommits settles)).sevm.currentTarget = a) = true :=
          decide_eq_true target
        simp only [selected, ↓reduceIte]
      · rw [ite_eq_right target, childIH childLeaves]
        have selected : decide ((Exec.Frame.ofRun child
            (Frame.raw_commits_of_settlementCommits settles)).sevm.currentTarget = a) = false :=
          decide_eq_false target
        simp only [selected, Bool.false_eq_true, ↓reduceIte]
    · simp only [Exec.keptAt, Exec.descendantFrames, dite_eq_right settles,
        List.nil_append] at leaves ⊢
      exact nextIH leaves

/-- On a selected address whose retained frames are leaves, pruning at that address
selects exactly the address-filtered committed frame list. -/
private theorem Root.keptAt_filter_frames_of_leaves {a : Adr} (root : Root)
    (leaves : ∀ fr ∈ root.frames, fr.sevm.currentTarget = a →
      Exec.descendantFrames fr.run = []) :
    root.keptAt a = root.frames.filter (fun fr => decide (fr.sevm.currentTarget = a)) := by
  by_cases settles : Frame.settlementCommits root.frame root.raw = true
  · have committed := Frame.raw_commits_of_settlementCommits settles
    simp only [Root.keptAt, Root.frames, dite_eq_left settles, ite_eq_left settles,
      Exec.committedFrames, dite_eq_left committed] at leaves ⊢
    by_cases target : root.evm.sta.currentTarget = a
    · have empty : Exec.descendantFrames root.run = [] := leaves _ List.mem_cons_self target
      rw [ite_eq_left target, empty]
      simp only [Exec.Frame.ofRun, List.filter_cons, decide_eq_true target, ↓reduceIte,
        List.filter_nil]
    · rw [ite_eq_right target]
      rw [Exec.keptAt_filter_descendantFrames_of_leaves root.run
        (fun fr member selected => leaves fr (List.mem_cons_of_mem _ member) selected)]
      simp only [Exec.Frame.ofRun, List.filter_cons, decide_eq_false target,
        Bool.false_eq_true, ↓reduceIte]
  · simp only [Root.keptAt, Root.frames, dite_eq_right settles, ite_eq_right settles,
      List.filter_nil]

private theorem roots_keptAt_filter_frames_of_leaves {a : Adr} (rs : List Root)
    (leaves : ∀ fr ∈ rs.flatMap Root.frames, fr.sevm.currentTarget = a →
      Exec.descendantFrames fr.run = []) :
    rs.flatMap (Root.keptAt a) =
      (rs.flatMap Root.frames).filter (fun fr => decide (fr.sevm.currentTarget = a)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons] at leaves
    simp only [List.flatMap_cons, List.filter_append]
    rw [Root.keptAt_filter_frames_of_leaves r
        (fun fr hfr => leaves fr (List.mem_append_left _ hfr)),
      ih (fun fr hfr => leaves fr (List.mem_append_right _ hfr))]

namespace ExecutionTrace

private def RetainedXlot.rootList (frame : Frame) {slot : Xlot} :
    RetainedXlot slot → List Root
  | .none => []
  | @RetainedXlot.some pc sevm pre raw run => [⟨frame, ⟨pc, sevm, pre⟩, raw, run⟩]

private theorem RetainedXlot.rootList_entry {frame : Frame} {slot : Xlot}
    {result : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (run : RunFrame frame slot result) :
    (retained.rootList frame).map (fun root => (root.frame, root.evm)) =
      (enteredFrame frame).toList := by
  cases retained with
  | none =>
      cases enter : frame.enter with
      | done result => rw [enteredFrame, enter]; rfl
      | run evm => simp only [RunFrame, enter, reduceCtorEq, false_and, exists_false] at run
  | some body =>
      rw [enteredFrame, (RunFrame.some_inv run).1]
      rfl

private def MessageCallTrace.rootList {msg : Msg} {state : State} {out : MsgCallOutput} :
    MessageCallTrace msg state out → List Root
  | .createCollision .. => []
  | .createRun _ _ _ _ trace _ => trace.retained.rootList (Frame.ofCreate msg)
  | .callRun _ _ _ _ execMsg _ _ _ trace _ => trace.retained.rootList (Frame.ofCall execMsg)

private theorem MessageCallTrace.rootList_roots {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (hsg : msg.benv.stat.rules.stateGas = none) :
    MessageRoots msg state out trace.rootList := by
  refine ⟨trace.result, ?_⟩
  cases trace with
  | createCollision target collision result =>
      simp only [MessageCallTrace.rootList, List.map_nil, messageEntry, hsg, legacyEntry,
        target, collision, ↓reduceIte, Option.toList_none]
  | createRun target collision evm core trace result =>
      simp only [MessageCallTrace.rootList, messageEntry, hsg, legacyEntry, target,
        collision, ↓reduceIte]
      exact trace.retained.rootList_entry trace.run
  | callRun target delegated refund delegation execMsg execEq evm core trace result =>
      subst execMsg
      simp only [MessageCallTrace.rootList, messageEntry, hsg, legacyEntry, target,
        Bool.false_eq_true, ↓reduceIte, delegation]
      exact trace.retained.rootList_entry trace.run

private theorem RetainedXlot.rootList_keptLogs {a : Adr} {keep : Log → Bool}
    (address : ∀ log, keep log = true → log.address = a)
    {frame : Frame} {slot : Xlot} {result : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (run : RunFrame frame slot result)
    (hsg : frame.inner.benv.stat.rules.stateGas = Option.none) :
    ((retained.rootList frame).flatMap (Root.keptAt a)).flatMap
        (fun fr => (fr.post.logs.drop fr.pre.logs.length).filter keep) =
      (match retained with
        | .none => ([] : List Exec.Frame)
        | @RetainedXlot.some _ _ _ raw body =>
          if Frame.settlementCommits frame raw = true then
            (RetainedXlot.some body).settledRoots else []).flatMap
              (fun fr : Exec.Frame => fr.post.logs.filter keep) := by
  cases retained with
  | none => rfl
  | @some pc sevm pre raw body =>
      have enter := (RunFrame.some_inv run).1
      have stat : sevm.benvStat.rules.stateGas = Option.none := by
        rw [Frame.enter_run_benvStat enter]
        exact hsg
      have logs : pre.logs = [] := Frame_enter_run_logs_noStateGas hsg enter
      simp only [RetainedXlot.rootList, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [Root.keptAt_logs address _ stat]
      by_cases settles : Frame.settlementCommits frame raw = true
      · have committed := Frame.raw_commits_of_settlementCommits settles
        simp only [settles, ↓reduceDIte, ↓reduceIte, RetainedXlot.settledRoots, committed,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, Exec.Frame.post,
          Exec.Frame.ofRun, logs, List.length_nil, List.drop_zero]
      · simp only [settles, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, List.flatMap_nil]

private theorem MessageCallTrace.rootList_keptLogs {a : Adr} {keep : Log → Bool}
    (address : ∀ log, keep log = true → log.address = a)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (hsg : msg.benv.stat.rules.stateGas = none) :
    (trace.rootList.flatMap (Root.keptAt a)).flatMap
        (fun fr => (fr.post.logs.drop fr.pre.logs.length).filter keep) =
      trace.settledRoots.flatMap (fun fr => fr.post.logs.filter keep) := by
  cases trace with
  | createCollision target collision result => rfl
  | createRun target collision evm core trace result =>
      rcases trace with ⟨slot, retained, process⟩
      cases retained with
      | none => rfl
      | some body =>
          exact (RetainedXlot.some body).rootList_keptLogs address process hsg
  | callRun target delegated refund delegation execMsg execEq evm core trace result =>
      have stat : execMsg.benv.stat = msg.benv.stat := by
        subst execMsg
        rw [messageCallExecutionMessage_benv_stat, messageCallDelegation_benv_stat delegation]
      have innerSg : (Frame.ofCall execMsg).inner.benv.stat.rules.stateGas = none := by
        change execMsg.benv.stat.rules.stateGas = none
        rw [stat]; exact hsg
      rcases trace with ⟨slot, retained, process⟩
      cases retained with
      | none => rfl
      | some body =>
          exact (RetainedXlot.some body).rootList_keptLogs address process innerSg

/-- Actual message logs filtered at an address are exactly its original kept frames'
added logs, in chronological order. No receipt or attribution assumption is supplied. -/
theorem _root_.Blanc.MessageRoots.keptAt_logs {a : Adr} {keep : Log → Bool}
    (address : ∀ log, keep log = true → log.address = a)
    {msg : Msg} {state : State} {out : MsgCallOutput} {roots : List Root}
    (run : MessageRoots msg state out roots) (hsg : msg.benv.stat.rules.stateGas = none) :
    out.logs.filter keep = (roots.flatMap (Root.keptAt a)).flatMap
      (fun fr => (fr.post.logs.drop fr.pre.logs.length).filter keep) := by
  obtain ⟨trace⟩ := exists_messageCallTrace_of_stateGas_none run.1 hsg
  have same := run.unique (trace.rootList_roots hsg)
  rw [same, trace.rootList_keptLogs address hsg, trace.logs_eq_settledRoots hsg,
    List.filter_flatMap]

private theorem TransactionTrace.transactionMessage_eq
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    transactionMessage benv bout tx index = .ok (trace.sender, trace.msg) := by
  have valid : validateTransaction benv.stat.rules tx 0 =
      .ok (trace.intrinsicGas, trace.calldataFloorGasCost) := by
    rw [validateTransaction_sender_congr_none (s1 := 0) (s2 := trace.validationSender) hsg]
    exact trace.validation
  unfold transactionMessage
  dsimp only
  rw [recoverValidationSender_of_stateGas_none (benv := benv.beginTransaction) tx hsg]
  have checked := trace.checked
  have debit := trace.debit
  have prepared := trace.prepared
  simp only [BenvStat.rules, Benv.beginTransaction, transactionBlobGasFee,
    transactionTenvAt, transactionTenv, allocateEvmGas, Except.mapError]
    at valid checked debit prepared hsg ⊢
  simp only [bind, Except.bind, valid, checked, debit, Option.toExcept, hsg, prepared]

/-- The ordered receipt-key append is a projection of the original selected settlement. -/
theorem TransactionTrace.receiptKeys_eq
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none) :
    bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] := by
  obtain ⟨refund, refundEq, _⟩ := trace.exists_selectedFinalStateForm hsg
  have valid : validateTransaction benv.stat.rules tx 0 =
      .ok (trace.intrinsicGas, trace.calldataFloorGasCost) := by
    rw [validateTransaction_sender_congr_none (s1 := 0) (s2 := trace.validationSender) hsg]
    exact trace.validation
  obtain ⟨actualBout, result, _, _, keys, _⟩ :=
    processTransaction_of_stages_selected_receipts hsg hbal valid trace.checked
      trace.debit trace.prepared trace.message.result refundEq
  have same := Prod.mk.inj (Except.ok.inj (trace.result.symm.trans result))
  rw [← same.2] at keys
  exact keys

private theorem TransactionTrace.receipt_keptAt_logs {a : Adr} {keep : Log → Bool}
    (address : ∀ log, keep log = true → log.address = a)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {sender : Adr} {roots : List Root}
    (trace : TransactionTrace benv bout tx index state bout')
    (run : TransactionRoots benv bout tx index state bout' sender roots)
    (hsg : benv.stat.rules.stateGas = none) :
    (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
      trace.messageOut.logs).2.logs.filter keep =
      (roots.flatMap (Root.keptAt a)).flatMap
        (fun fr => (fr.post.logs.drop fr.pre.logs.length).filter keep) := by
  obtain ⟨msg, messageState, messageOut, prepared, message⟩ := run.2
  have same := Prod.mk.inj (Except.ok.inj (prepared.symm.trans
    (trace.transactionMessage_eq hsg)))
  have msgEq := same.2
  subst msg
  have outcome := Prod.mk.inj (Except.ok.inj (message.1.symm.trans trace.message.result))
  obtain ⟨rfl, rfl⟩ := outcome
  exact message.keptAt_logs address (by rw [prepareMessage_benv trace.prepared]; exact hsg)

private theorem MessageCallTrace.rootList_frames {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    trace.rootList.flatMap Root.frames = trace.settledFrames := by
  cases trace with
  | createCollision target collision result => rfl
  | createRun target collision evm core trace result =>
    rcases trace with ⟨slot, retained, process⟩
    cases retained with
    | none => rfl
    | some body =>
      simp only [MessageCallTrace.rootList, RetainedXlot.rootList, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Root.frames, MessageCallTrace.settledFrames,
        ProcessCreateMessageTrace.settledFrames]
  | callRun target delegated refund delegation execMsg execEq evm core trace result =>
    rcases trace with ⟨slot, retained, process⟩
    cases retained with
    | none => rfl
    | some body =>
      simp only [MessageCallTrace.rootList, RetainedXlot.rootList, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Root.frames, MessageCallTrace.settledFrames,
        ProcessMessageTrace.settledFrames]

private theorem TransactionTrace.roots_frames
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout2 : BlockOutput} {sender : Adr} {roots : List Root}
    (trace : TransactionTrace benv bout tx index state bout2)
    (run : TransactionRoots benv bout tx index state bout2 sender roots)
    (hsg : benv.stat.rules.stateGas = none) :
    roots.flatMap Root.frames = trace.settledFrames := by
  obtain ⟨msg, messageState, messageOut, prepared, message⟩ := run.2
  have same := Prod.mk.inj (Except.ok.inj (prepared.symm.trans
    (trace.transactionMessage_eq hsg)))
  have msgEq := same.2
  subst msg
  have messageSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact hsg
  rw [message.unique (trace.message.rootList_roots messageSg),
    trace.message.rootList_frames]
  rfl

private theorem ApplyTransactionsTrace.roots_frames
    {txs : List (Nat × Tx)} {benv finalBenv finalBenv2 : Benv} {bout finalBout finalBout2 : BlockOutput}
    {senders : List (Adr × Tx)} {roots : List Root}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (run : TransactionsRoots txs benv bout finalBenv2 finalBout2 senders roots)
    (hsg : benv.stat.rules.stateGas = none) :
    (finalBenv2 = finalBenv ∧ finalBout2 = finalBout) ∧
      roots.flatMap Root.frames = trace.settledFrames := by
  induction trace generalizing senders roots with
  | nil =>
    cases run
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  | cons head tail ih =>
    cases run with
    | cons first later =>
      have same := Prod.mk.inj (Except.ok.inj (first.1.symm.trans head.result))
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨heq, hframes⟩ := ih later hsg
      exact ⟨heq, by simp only [List.flatMap_append, ApplyTransactionsTrace.settledFrames,
        head.roots_frames first hsg, hframes]⟩

private theorem RequestsTrace.requestPass_frames
    {benv : Benv} {bout boutPass : BlockOutput} {state : State} {bout2 : BlockOutput}
    {actualState : State} {actualOut : BlockOutput} {steps : List RequestStep}
    (trace : RequestsTrace benv bout state bout2)
    (run : RequestPass benv boutPass actualState actualOut steps)
    (hsg : benv.stat.rules.stateGas = none)
    (enabled : benv.stat.rules.header.requestsHash = true) :
    (requestRootsOf steps).flatMap Root.frames = trace.settledFrames := by
  rw [RequestPass, ite_eq_left enabled] at run
  obtain ⟨deposits, acc, bal, parsed, roots, output⟩ := run
  rw [trace.requestShape] at roots
  cases roots with
  | cons withdrawalRun withdrawalRoots later =>
    have same := Prod.mk.inj (Except.ok.inj (withdrawalRun.symm.trans trace.withdrawalRun))
    obtain ⟨rfl, rfl⟩ := same
    cases later with
    | cons consolidationRun consolidationRoots tail =>
      have same := Prod.mk.inj
        (Except.ok.inj (consolidationRun.symm.trans trace.consolidationRun))
      obtain ⟨rfl, rfl⟩ := same
      cases tail
      have withdrawalSg : (systemTransactionMessage benv
          withdrawalRequestPredeployAddress []).benv.stat.rules.stateGas = none := hsg
      have consolidationSg : (systemTransactionMessage (benv.withState trace.withdrawalState)
          consolidationRequestPredeployAddress []).benv.stat.rules.stateGas = none := hsg
      simp only [requestRootsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.flatMap_append, RequestsTrace.settledFrames, SystemMessageTrace.settledFrames]
      rw [withdrawalRoots.unique (trace.withdrawal.message.rootList_roots withdrawalSg),
        consolidationRoots.unique (trace.consolidation.message.rootList_roots consolidationSg),
        trace.withdrawal.message.rootList_frames,
        trace.consolidation.message.rootList_frames]

private theorem AppliedBodyTrace.preRoots_frames
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state2 : State} {bout2 : BlockOutput} {preState : State} {preBal : BalBuilder}
    {preRoots : List Root}
    (trace : AppliedBodyTrace benv txs ommers wds state2 bout2)
    (pre : PreRoots benv preState preBal preRoots)
    (fork : CoveredFork benv.stat.fork) :
    preState = trace.historyState ∧
      ({BlockOutput.init with bal := preBal} : BlockOutput) = .init ∧
      preRoots.flatMap Root.frames =
        trace.beacon.settledFrames ++ trace.history.settledFrames := by
  have hbal : benv.stat.rules.bal = none := fork.rules_bal_none
  have hsg : benv.stat.rules.stateGas = none := fork.rules_stateGas_none
  have hbeacon : benv.stat.rules.sys.beaconRoots = true :=
    fork.cases (motive := fun f => f.ruleSet.sys.beaconRoots = true) rfl rfl rfl rfl
  have hhistory : benv.stat.rules.sys.historyStorage = true :=
    fork.cases (motive := fun f => f.ruleSet.sys.historyStorage = true) rfl rfl rfl rfl
  obtain ⟨beacon, beaconBal, beaconRoots, historyRoots, hb, cb, hh, ch, rfl⟩ := pre
  simp only [beaconRootsCall, hbeacon, ↓reduceIte, BalBuilder.incorporateSystem, hbal] at hb
  obtain ⟨⟨st, out⟩, hrun, hb⟩ := Except.bind_eq_ok hb
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [Except.mapError_eq_ok_iff] at hrun
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj (hrun.symm.trans trace.beacon.run))
  simp only [historyStorageCall, hhistory, ↓reduceIte, BalBuilder.incorporateSystem, hbal] at hh
  obtain ⟨lastHash, hlast, hh⟩ := Except.bind_eq_ok hh
  obtain ⟨⟨st2, out2⟩, hrun2, hh⟩ := Except.bind_eq_ok hh
  simp only [Except.ok.injEq, Prod.mk.injEq] at hh
  obtain ⟨hpre, hpreBal⟩ := hh
  obtain rfl := Except.ok.inj (hlast.symm.trans trace.lastHashRun)
  rw [Except.mapError_eq_ok_iff] at hrun2
  obtain ⟨hst2, -⟩ := Prod.mk.inj (Except.ok.inj (hrun2.symm.trans trace.history.run))
  have hstateEq : preState = trace.historyState := hpre.symm.trans hst2
  subst hstateEq
  rw [PreCall, ite_eq_left hbeacon] at cb
  obtain ⟨_, bMsgRoots⟩ := cb
  have hdata : historyData benv = trace.lastHash.toBytes := by
    unfold historyData
    have hsome : benv.stat.blockHashes.getLast? = some trace.lastHash :=
      Option.toExcept_eq_ok trace.lastHashRun
    rw [hsome]
  rw [PreCall, ite_eq_left hhistory, hdata] at ch
  obtain ⟨_, hMsgRoots⟩ := ch
  have bSg : (systemTransactionMessage benv beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes).benv.stat.rules.stateGas = none := hsg
  have hSg : (systemTransactionMessage (benv.withState trace.beaconState) historyStorageAddress
      trace.lastHash.toBytes).benv.stat.rules.stateGas = none := hsg
  refine ⟨rfl, by rw [← hpreBal]; rfl, ?_⟩
  rw [List.flatMap_append,
    bMsgRoots.unique (trace.beacon.message.rootList_roots bSg),
    hMsgRoots.unique (trace.history.message.rootList_roots hSg),
    trace.beacon.message.rootList_frames,
    trace.history.message.rootList_frames]
  rfl

private theorem AppliedBodyTrace.bodyRoots_frames
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state state2 : State} {bout bout2 : BlockOutput} {run : BodyRun}
    (trace : AppliedBodyTrace benv txs ommers wds state2 bout2)
    (body : BodyRoots benv txs ommers wds state bout run)
    (fork : CoveredFork benv.stat.fork) :
    run.preRoots.flatMap Root.frames =
      trace.beacon.settledFrames ++ trace.history.settledFrames ∧
    run.txRoots.flatMap Root.frames = trace.transactions.settledFrames ∧
    (requestRootsOf run.requests).flatMap Root.frames = trace.requests.settledFrames ∧
    run.roots.flatMap Root.frames = trace.settledFrames := by
  have hsg : benv.stat.rules.stateGas = none := fork.rules_stateGas_none
  have hwds : benv.stat.rules.header.withdrawalsRoot = true :=
    fork.cases (motive := fun f => f.ruleSet.header.withdrawalsRoot = true) rfl rfl rfl rfl
  have hreq : benv.stat.rules.header.requestsHash = true :=
    fork.cases (motive := fun f => f.ruleSet.header.requestsHash = true) rfl rfl rfl rfl
  obtain ⟨hpreState, hpreBal, hpreFrames⟩ := trace.preRoots_frames body.pre fork
  obtain ⟨decoded, hd, txRoots⟩ := body.transactions
  obtain rfl : decoded = trace.decodedTxs := Except.ok.inj (hd.symm.trans trace.decodeRun)
  rw [hpreState, hpreBal] at txRoots
  obtain ⟨⟨htxEnv, htxOut⟩, htxFrames⟩ := trace.transactions.roots_frames txRoots hsg
  obtain ⟨reqSt, reqOut, reqPass⟩ := body.requests
  rw [htxEnv, htxOut] at reqPass
  simp only [withdrawalsPass, hwds, ↓reduceIte, processWithdrawals] at reqPass
  have hsgReq : (trace.transactionBenv.withState
      (processWithdrawalsState trace.transactionBenv.state wds)).stat.rules.stateGas = none := by
    change trace.transactionBenv.stat.rules.stateGas = none
    rw [trace.transactions.stat_eq]
    exact hsg
  have hreqOn : (trace.transactionBenv.withState
      (processWithdrawalsState trace.transactionBenv.state wds)).stat.rules.header.requestsHash =
      true := by
    change trace.transactionBenv.stat.rules.header.requestsHash = true
    rw [trace.transactions.stat_eq]
    exact hreq
  have hreqFrames := trace.requests.requestPass_frames reqPass hsgReq hreqOn
  refine ⟨hpreFrames, htxFrames, hreqFrames, ?_⟩
  simp only [BodyRun.roots, List.flatMap_append, hpreFrames, htxFrames, hreqFrames,
    AppliedBodyTrace.settledFrames, List.append_assoc]

/-- The frames of a configured block's kept roots are its settled frames. -/
theorem ConfiguredBlockTrace.kept_roots_frames {cfg : ChainConfig} {pre post : BlockChain}
    (t : ConfiguredBlockTrace cfg pre post) :
    t.kept.run.roots.flatMap Root.frames = t.settledFrames :=
  (t.bodyTrace.bodyRoots_frames t.keptStep.body t.covered).2.2.2

/-- The frames of a configured block's system pre-call and post-call request roots are its
settled system frames. -/
theorem ConfiguredBlockTrace.kept_systemRoots_frames {cfg : ChainConfig} {pre post : BlockChain}
    (t : ConfiguredBlockTrace cfg pre post) :
    (t.kept.run.preRoots ++ requestRootsOf t.kept.run.requests).flatMap Root.frames =
      t.bodyTrace.beacon.settledFrames ++ t.bodyTrace.history.settledFrames ++
        t.bodyTrace.requests.settledFrames := by
  obtain ⟨hpre, _, hreq, _⟩ := t.bodyTrace.bodyRoots_frames t.keptStep.body t.covered
  simp only [List.flatMap_append, hpre, hreq, List.append_assoc]

/-- On an address whose settled frames in a configured block are leaves, the kept traversal
selects precisely the address-filtered settled frames. -/
theorem ConfiguredBlockTrace.keptAt_eq_filter_settledFrames_of_leaves
    {cfg : ChainConfig} {pre post : BlockChain}
    (t : ConfiguredBlockTrace cfg pre post) (a : Adr)
    (leaves : ∀ fr ∈ t.settledFrames, fr.sevm.currentTarget = a →
      Exec.descendantFrames fr.run = []) :
    t.kept.keptAt a = t.settledFrames.filter (fun fr => decide (fr.sevm.currentTarget = a)) := by
  unfold KeptBlock.keptAt
  rw [roots_keptAt_filter_frames_of_leaves t.kept.run.roots
      (by rw [t.kept_roots_frames]; exact leaves),
    t.kept_roots_frames]

/-- When no settled system frame targets `a`, the block's system roots keep no frames at `a`. -/
theorem ConfiguredBlockTrace.kept_systemRoots_keptAt_nil
    {cfg : ChainConfig} {pre post : BlockChain}
    (t : ConfiguredBlockTrace cfg pre post) (a : Adr)
    (noTarget : ∀ fr ∈ t.bodyTrace.beacon.settledFrames ++ t.bodyTrace.history.settledFrames ++
      t.bodyTrace.requests.settledFrames, fr.sevm.currentTarget ≠ a) :
    (t.kept.run.preRoots ++ requestRootsOf t.kept.run.requests).flatMap (Root.keptAt a) = [] := by
  have sub : ∀ fr ∈ (t.kept.run.preRoots ++ requestRootsOf t.kept.run.requests).flatMap Root.frames,
      fr.sevm.currentTarget = a → Exec.descendantFrames fr.run = [] := by
    rw [t.kept_systemRoots_frames]
    intro fr hfr htarget
    exact False.elim (noTarget fr hfr htarget)
  rw [roots_keptAt_filter_frames_of_leaves _ sub, t.kept_systemRoots_frames]
  apply List.filter_eq_nil_iff.mpr
  intro fr hfr
  simp only [decide_eq_true_eq]
  exact noTarget fr hfr

/-- On an address whose settled frames along a configured history are leaves, the kept blocks'
frames at `a` are precisely the address-filtered settled frames. -/
theorem ConfiguredHistoryTrace.keptAt_eq_filter_settledFrames_of_leaves
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (t : ConfiguredHistoryTrace cfg checkpoint future) (a : Adr)
    (leaves : ∀ fr ∈ t.settledFrames, fr.sevm.currentTarget = a →
      Exec.descendantFrames fr.run = []) :
    t.kept.flatMap (KeptBlock.keptAt a) =
      t.settledFrames.filter (fun fr => decide (fr.sevm.currentTarget = a)) := by
  induction t with
  | refl => rfl
  | step prior block ih =>
    simp only [ConfiguredHistoryTrace.settledFrames] at leaves
    simp only [ConfiguredHistoryTrace.kept, ConfiguredHistoryTrace.settledFrames,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.filter_append]
    rw [ih (fun fr hfr => leaves fr (List.mem_append_left _ hfr)),
      block.keptAt_eq_filter_settledFrames_of_leaves a
        (fun fr hfr => leaves fr (List.mem_append_right _ hfr))]

end ExecutionTrace

/-- Receipts of the original indexed transactions are complete and ordered. Their
selected values survive the actual suffix, and their address-filtered logs are exactly
the original kept-frame added logs. Index separation is the original list's strict order. -/
theorem TransactionsRoots.receipt_keptAt_logs {a : Adr} {keep : Log → Bool}
    (address : ∀ log, keep log = true → log.address = a)
    {txis : List (Nat × Tx)} {benv final : Benv} {bout out : BlockOutput}
    {senders : List (Adr × Tx)} {roots : List Root}
    (run : TransactionsRoots txis benv bout final out senders roots)
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none)
    (ordered : txis.Pairwise (fun left right => left.1 < right.1)) :
    ∃ receipts : List (Fin 5 × Receipt),
      out.receiptKeys = bout.receiptKeys ++
        txis.map (fun item => BLT.toBytes (.bytes item.1.toBytes)) ∧
      List.Forall₂ (fun key receipt => out.receiptsTrie[key]? = some receipt)
        (txis.map (fun item => BLT.toBytes (.bytes item.1.toBytes))) receipts ∧
      receipts.flatMap (fun receipt => receipt.2.logs.filter keep) =
        (roots.flatMap (Root.keptAt a)).flatMap
          (fun fr => (fr.post.logs.drop fr.pre.logs.length).filter keep) := by
  induction run with
  | nil => exact ⟨[], (List.append_nil _).symm, .nil, rfl⟩
  | @cons index tx rest benv final bout bout' out state sender first later senders head tail ih =>
      have order := List.pairwise_cons.mp ordered
      obtain ⟨trace⟩ := ExecutionTrace.exists_transactionTrace_of_stateGas_none head.1 hsg
      obtain ⟨suffix⟩ := ExecutionTrace.exists_applyTransactionsTrace_of_stateGas_none tail.run hsg
      have different : ∀ item ∈ rest, BLT.toBytes (.bytes item.1.toBytes) ≠
          BLT.toBytes (.bytes index.toBytes) := by
        intro item member
        apply RlpConcrete.receipt_key_ne
        have bound := order.1 item member
        omega
      have lookup := (suffix.receipt_preserved_of_keys_ne different).trans
        (trace.receipt_of_selected_settlement hsg)
      obtain ⟨receipts, keys, lookups, logs⟩ := ih hsg hbal order.2
      refine ⟨makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        trace.messageOut.logs :: receipts, ?_, .cons lookup lookups, ?_⟩
      · rw [keys, trace.receiptKeys_eq hsg hbal, List.map_cons, List.append_assoc]
        rfl
      · simp only [List.flatMap_cons, List.flatMap_append]
        rw [trace.receipt_keptAt_logs address head hsg, logs]

private theorem putIndex_aux_lower {α : Type} (xs : List α) (offset : Nat) :
    ∀ item ∈ Jaune.List.putIndex.aux offset xs, offset ≤ item.1 := by
  induction xs generalizing offset with
  | nil => intro item member; cases member
  | cons x xs ih =>
      intro item member
      change item ∈ (offset, x) :: Jaune.List.putIndex.aux (offset + 1) xs at member
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_refl _
      · have bound := ih (offset + 1) item later
        omega

/-- The source transaction occurrences receive strictly increasing natural indices. -/
theorem putIndex_pairwise {α : Type} (xs : List α) :
    xs.putIndex.Pairwise (fun left right => left.1 < right.1) := by
  suffices ∀ offset, (Jaune.List.putIndex.aux offset xs).Pairwise
      (fun left right => left.1 < right.1) from this 0
  induction xs with
  | nil => exact fun _ => .nil
  | cons x xs ih =>
      intro offset
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih (offset + 1)⟩
      intro item member
      have bound := putIndex_aux_lower xs (offset + 1) item member
      omega

end Blanc
