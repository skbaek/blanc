import Blanc.ExecutionKeptFresh
import Blanc.ExecutionNoDelProducer
import Blanc.ExecutionDeletionProvenance

open private TransactionRoots.spine PreparedTx PreparedTx.routed PreparedTx.deletions
  PreparedTx.stat PreparedTx.debit debit_getCode settleSelfdestructs_get
  from Blanc.ExecutionKeptChain

/-! # Installed runtime transport on the original kept transaction carrier -/

namespace Blanc

open Jaune

private theorem MessageRoots.root_runtime
    {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (run : MessageRoots msg state out rs) (routed : RoutedMessage msg)
    {a : Adr} {C : ByteArray} (installed : msg.benv.state.getCode a = C)
    (nonempty : C.toList ≠ []) (nondesignator : ¬ isValidDelegation C)
    {root : Root} (member : root ∈ rs) (here : root.evm.sta.currentTarget = a) :
    root.evm.pc = 0 ∧ root.evm.sta.code = C := by
  have same : msg.currentTarget = a := (run.entry_routing member).2.1.symm.trans here
  have code : msg.benv.state.getCode msg.currentTarget = C := by
    rw [same]; exact installed
  cases call : msg.target.isNone with
  | false =>
      obtain ⟨address, image⟩ := routed.1 call
      refine ⟨(run.entry_machine member).1, ?_⟩
      exact ((run.entry_call_code member call address image).1
        (by rw [code]; exact nonempty) (by rw [code]; exact nondesignator)).trans code
  | true =>
      exact (run.create_ne member (by rw [installed]; exact nonempty)
        (by rw [installed]; exact nondesignator) call same).elim

/-- Actual runtime terminal safety excludes output deletion, even for an earlier-created account. -/
theorem MessageRoots.not_deleted_of_runtimeSafety
    {C : ByteArray} (K : InstalledRuntimeSafety C)
    {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (run : MessageRoots msg state out rs) (routed : RoutedMessage msg)
    (hsg : msg.benv.stat.rules.stateGas = none) {a : Adr}
    (installed : msg.benv.state.getCode a = C)
    (inherited : a ∉ msg.inheritedDeletions) : a ∉ out.accountsToDelete := by
  intro deleted
  rcases run.deletions deleted with old | ⟨root, member, settles, deleted⟩
  · exact inherited old
  · have hc : (msg.benv.state.getCode a).toList ≠ [] := by
      rw [installed]; exact K.nonempty
    have hd : ¬ isValidDelegation (msg.benv.state.getCode a) := by
      rw [installed]; exact K.notDelegation
    have rootGas : root.evm.sta.benvStat.rules.stateGas = none := by
      rw [(run.entry_routing member).2.2.1]; exact hsg
    have safe := K.safe root.run rootGas
      ((run.entry_kept member hc hd).1.trans installed)
      (run.root_runtime routed installed K.nonempty K.notDelegation member)
    exact Exec.not_mem_atd_of_retained_terminal_safe root.run
      (Frame.raw_commits_of_settlementCommits settles) rootGas
      (by rw [(run.entry_sets member).1]; exact inherited)
      (fun node kept => safe node ((Exec.retainedNodes_sublist_rawNodes root.run).subset kept))
      deleted

/-- Original kept frames run the installed image from pc zero on their actual fresh machine. -/
theorem MessageRoots.runtime_entry
    {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (run : MessageRoots msg state out rs) (routed : RoutedMessage msg)
    {a : Adr} {C : ByteArray} (installed : msg.benv.state.getCode a = C)
    (nonempty : C.toList ≠ []) (nondesignator : ¬ isValidDelegation C) :
    ∀ frame ∈ rs.flatMap (Root.keptAt a),
      frame.pc = 0 ∧ frame.sevm.currentTarget = a ∧ frame.sevm.code = C ∧
        frame.sevm.benvStat = msg.benv.stat ∧ Exec.FreshEntry frame.sevm frame.pre := by
  intro frame member
  obtain ⟨root, rootMember, kept⟩ := List.mem_flatMap.mp member
  have machine := run.entry_machine rootMember
  have fresh := Root.keptAt_fresh ⟨machine.2.1, machine.2.2.1⟩ a kept
  have stat := (run.entry_routing rootMember).2.2.1
  by_cases settles : Frame.settlementCommits root.frame root.raw = true
  · rw [Root.keptAt, dite_eq_left settles] at kept
    by_cases here : root.evm.sta.currentTarget = a
    · rw [ite_eq_left here, List.mem_singleton] at kept
      subst frame
      have own := run.root_runtime routed installed nonempty nondesignator rootMember here
      exact ⟨own.1, here, own.2, stat, fresh⟩
    · rw [ite_eq_right here] at kept
      have entry := Exec.keptAt_entry root.run
        (Frame.raw_commits_of_settlementCommits settles) here
        ((run.entry_kept rootMember (by rw [installed]; exact nonempty)
          (by rw [installed]; exact nondesignator)).1.trans installed)
        nonempty nondesignator frame kept
      exact ⟨entry.pc, entry.target, entry.code, entry.benvStat.trans stat, fresh⟩
  · rw [Root.keptAt, dite_eq_right settles] at kept
    cases kept

/-- Actual transaction settlement preserves installed code and the original kept-frame entries.
The target may already belong to the block's created-account set. -/
theorem TransactionRoots.runtime_of_runtimeSafety
    {C : ByteArray} (K : InstalledRuntimeSafety C)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {sender : Adr} {rs : List Root}
    (run : TransactionRoots benv bout tx index state bout' sender rs)
    (hsg : benv.stat.rules.stateGas = none)
    (noSweep : benv.stat.rules.settle.touchedSweep = false) {a : Adr}
    (installed : benv.state.getCode a = C) :
    state.getCode a = C ∧
      ∀ frame ∈ rs.flatMap (Root.keptAt a),
        frame.pc = 0 ∧ frame.sevm.currentTarget = a ∧ frame.sevm.code = C ∧
          frame.sevm.benvStat.fork = benv.stat.fork ∧ Exec.FreshEntry frame.sevm frame.pre := by
  obtain ⟨msg, messageState, messageOut, refund, tip, facts, roots, final, -⟩ :=
    TransactionRoots.spine run
  obtain ⟨value, debit⟩ := PreparedTx.debit facts
  have inputCode := (debit_getCode debit a).trans installed
  have hc : (msg.benv.state.getCode a).toList ≠ [] := by
    rw [inputCode]; exact K.nonempty
  have hd : ¬ isValidDelegation (msg.benv.state.getCode a) := by
    rw [inputCode]; exact K.notDelegation
  have rootGas : msg.benv.stat.rules.stateGas = none := by
    rw [PreparedTx.stat facts]; exact hsg
  have messageCode := (roots.chain hc hd).2
  have notDeleted := roots.not_deleted_of_runtimeSafety K (PreparedTx.routed facts) rootGas inputCode
    (by rw [PreparedTx.deletions facts]; exact AdrSet.not_mem_empty)
  have notList : ∀ x ∈ messageOut.accountsToDelete.toList, x ≠ a :=
    fun x member same => notDeleted (same ▸ Std.HashSet.mem_toList.mp member)
  rw [sweepTouchedAccounts_of_not_touchedSweep noSweep] at final
  have targetCell := settleSelfdestructs_get notList benv.stat.rules
    ((messageState.addBal sender refund).addBal benv.stat.coinbase tip)
  have finalCode : state.getCode a = messageState.getCode a := by
    rw [final]
    unfold State.getCode
    rw [targetCell]
    change ((messageState.addBal sender refund).addBal benv.stat.coinbase tip).getCode a = _
    rw [State.addBal_getCode, State.addBal_getCode]
    rfl
  refine ⟨finalCode.trans (messageCode.trans inputCode), ?_⟩
  intro frame member
  obtain ⟨pc, target, code, stat, fresh⟩ :=
    roots.runtime_entry (PreparedTx.routed facts) inputCode K.nonempty K.notDelegation frame member
  refine ⟨pc, target, code, ?_, fresh⟩
  rw [stat, PreparedTx.stat facts]
  rfl

/-- The original indexed transaction fold transports the installed runtime to every kept
target frame, without a calldata bound or an exclusion from created accounts. -/
theorem TransactionsRoots.runtime_of_runtimeSafety
    {C : ByteArray} (K : InstalledRuntimeSafety C)
    {txis : List (Nat × Tx)} {benv final : Benv} {bout out : BlockOutput}
    {senders : List (Adr × Tx)} {roots : List Root}
    (run : TransactionsRoots txis benv bout final out senders roots)
    (hsg : benv.stat.rules.stateGas = none)
    (noSweep : benv.stat.rules.settle.touchedSweep = false) {a : Adr}
    (installed : benv.state.getCode a = C) :
    final.state.getCode a = C ∧
      ∀ frame ∈ roots.flatMap (Root.keptAt a),
        frame.pc = 0 ∧ frame.sevm.currentTarget = a ∧ frame.sevm.code = C ∧
          frame.sevm.benvStat.fork = benv.stat.fork ∧ Exec.FreshEntry frame.sevm frame.pre := by
  induction run with
  | nil =>
      refine ⟨installed, ?_⟩
      intro frame member
      cases member
  | cons head tail ih =>
      obtain ⟨headCode, headEntries⟩ := head.runtime_of_runtimeSafety K hsg noSweep installed
      obtain ⟨finalCode, laterEntries⟩ := ih hsg noSweep headCode
      refine ⟨finalCode, ?_⟩
      intro frame member
      rw [List.flatMap_append] at member
      rcases List.mem_append.mp member with first | later
      · exact headEntries frame first
      · exact laterEntries frame later

end Blanc
