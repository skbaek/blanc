import Blanc.TransactionForward
import Blanc.ForwardStorageAccess
import Blanc.SystemContracts

/-!
# The forward direction of a successful system call

Jaune's `processSystemTransaction` wraps the SYSTEM caller's message to a system
contract in `processMessageCall`.  For a canonical system contract on a covered fork
(no state-gas dimension, target not a precompile, code not a delegation), the wrapper
returns exactly the frame's post state whenever the raw frame `exec` succeeds without
error and with a non-negative refund counter.  The unchecked and checked block-level
entry points follow once the canonical code is installed.

A contract's system-path walk therefore only supplies its own `exec` result; the
envelope is shared.
-/

namespace Blanc

open Jaune

/-- The SYSTEM caller's message to `target` running `code` on `data`, as
`processSystemTransaction` builds it. -/
def systemCallMsg (benv : Benv) (target : Adr) (code : ByteArray) (data : Bytes) : Msg :=
  processSystemTransactionMsg benv.beginTransaction
    (processSystemTransactionTenv benv.beginTransaction) target data code

/-- The call output of a clean system frame. -/
def systemCallOutput (post : Devm) : MsgCallOutput :=
  { gasLeft := post.gasLeft
    refundCounter := post.refundCounter
    logs := post.logs
    accountsToDelete := post.accountsToDelete
    error := none
    returnData := post.output }

/-- No canonical system contract sits at a precompile address on a covered fork. -/
theorem systemContracts_not_precompile {p : Adr × ByteArray} (member : p ∈ systemContracts)
    {fork : Fork} (covered : CoveredFork fork) : ¬ (Fork.ruleSet fork).isPrecomp p.1 := by
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact covered.beaconRoots_not_precompile
  · exact covered.historyStorage_not_precompile
  · exact covered.cases (motive := fun f =>
      ¬ (Fork.ruleSet f).isPrecomp withdrawalRequestPredeployAddress)
      (by decide) (by decide) (by decide) (by decide)
  · exact covered.cases (motive := fun f =>
      ¬ (Fork.ruleSet f).isPrecomp consolidationRequestPredeployAddress)
      (by decide) (by decide) (by decide) (by decide)

/-- Canonical system code is not an EIP-7702 delegation designator. -/
theorem systemContracts_nondelegated {p : Adr × ByteArray} (member : p ∈ systemContracts) :
    getDelegatedCodeAddress p.2 = none := by
  have ordinary := (systemContracts_facts p member).2.1
  simp only [getDelegatedCodeAddress, ordinary, ite_false]

/-- Canonical system code is nonempty. -/
theorem systemContracts_nonempty {p : Adr × ByteArray} (member : p ∈ systemContracts) :
    p.2.isEmpty = false := by
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide +kernel

/-- **The system-call wrapper over a successful raw frame.** -/
theorem processSystemTransaction_of_exec {benv : Benv} {p : Adr × ByteArray}
    (member : p ∈ systemContracts) {data : Bytes} {post : Devm}
    (fork : CoveredFork benv.stat.fork)
    (run : exec (initEvm (systemCallMsg benv p.1 p.2 data)) = .ok post)
    (clean : post.error = none) (nonneg : 0 ≤ post.refundCounter) :
    processSystemTransaction benv p.1 p.2 data = .ok (post.state, systemCallOutput post) := by
  have entry : (systemCallMsg benv p.1 p.2 data).benvAfterTransfer =
      .ok benv.beginTransaction := rfl
  have codeEntry : executeCode.enter
      ((systemCallMsg benv p.1 p.2 data).withBenv benv.beginTransaction) =
      .inl (initEvm ((systemCallMsg benv p.1 p.2 data).withBenv benv.beginTransaction)) := by
    have notPrecompile : ¬ benv.stat.rules.isPrecomp p.1 :=
      systemContracts_not_precompile member fork
    change (if (!false && (benv.stat.rules.isPrecomp p.1)) then _ else _) = _
    simp only [Bool.not_false, Bool.true_and, notPrecompile, decide_false,
      Bool.false_eq_true, ite_false]
  have self : (systemCallMsg benv p.1 p.2 data).withBenv benv.beginTransaction =
      systemCallMsg benv p.1 p.2 data := rfl
  have message : processMessage (systemCallMsg benv p.1 p.2 data) = .ok post :=
    MessageExecution.processMessage_clean_of_exec_afterTransfer_of_codeEntry
      _ _ _ entry codeEntry (by rw [self]; exact run) clean
  have call := processMessageCall_call_of_message
    (msg := systemCallMsg benv p.1 p.2 data) (post := post)
    (fork.rules_stateGas_none (s := benv.beginTransaction.stat)) rfl rfl
    (systemContracts_nondelegated member) message clean
    (Int.toNat?_eq_some_of_nonneg nonneg)
  simp only [Nat.zero_add, Int.toNat_of_nonneg nonneg] at call
  exact call

/-- The unchecked block-level system call over installed canonical code. -/
theorem processUncheckedSystemTransaction_of_exec {benv : Benv} {p : Adr × ByteArray}
    (member : p ∈ systemContracts) {data : Bytes} {post : Devm}
    (fork : CoveredFork benv.stat.fork) (installed : benv.state.getCode p.1 = p.2)
    (run : exec (initEvm (systemCallMsg benv p.1 p.2 data)) = .ok post)
    (clean : post.error = none) (nonneg : 0 ≤ post.refundCounter) :
    processUncheckedSystemTransaction benv p.1 data =
      .ok (post.state, systemCallOutput post) := by
  unfold processUncheckedSystemTransaction
  simp only [installed]
  exact processSystemTransaction_of_exec member fork run clean nonneg

/-- The checked block-level system call over installed canonical code: neither
checked error arm is reachable. -/
theorem processCheckedSystemTransaction_of_exec {benv : Benv} {p : Adr × ByteArray}
    (member : p ∈ systemContracts) {data : Bytes} {post : Devm}
    (fork : CoveredFork benv.stat.fork) (installed : benv.state.getCode p.1 = p.2)
    (run : exec (initEvm (systemCallMsg benv p.1 p.2 data)) = .ok post)
    (clean : post.error = none) (nonneg : 0 ≤ post.refundCounter) :
    processCheckedSystemTransaction benv p.1 data =
      .ok (post.state, systemCallOutput post) := by
  unfold processCheckedSystemTransaction
  simp only [installed, systemContracts_nonempty member, Bool.false_eq_true, ite_false]
  rw [processSystemTransaction_of_exec member fork run clean nonneg]
  rfl

/-- A selected `SSTORE` writes the world state exactly at the executing account. -/
theorem afterSstore_state (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).state =
      base.state.setStorVal sevm.currentTarget key value := by
  unfold afterSstore
  split <;> rfl

/-- A storage write leaves every other account untouched. -/
theorem State.get_setStorVal_ne (w : State) {owner a : Adr} (key value : B256)
    (different : owner ≠ a) : (w.setStorVal owner key value).get a = w.get a := by
  unfold State.setStorVal
  exact State.get_set_ne w different _

end Blanc
