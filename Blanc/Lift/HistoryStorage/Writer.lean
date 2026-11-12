import Blanc.Lift.SystemWordWriter
import Blanc.Lift.SystemExecution.HistoryStorage.SystemWalk

/-! Actual canonical H execution inside the shared privileged word writer.
This module supplies the child law, not a closed kept-history witness. -/

namespace Blanc.Lift.HistoryStorage.Writer

open Jaune Blanc.Lift
open SystemExecution.HistoryStorage

def key (s : Sevm) : B256 := (s.benvStat.number.toB256 - 1) % 8191
def frameCost (s : Sevm) (b : Devm) : Nat := 43 + sstoreCost s b (key s) (Sevm.dataWord s 0)
def framePost (s : Sevm) (b : Devm) (gas : Nat) : Devm :=
  St (afterSstore s b (key s) (Sevm.dataWord s 0)) [] .empty (gas - frameCost s b)

/-- The SYSTEM arm of the actual 83-byte runtime at its supplied child gas. -/
theorem frame_exec {msg : Msg}
    (fork : CoveredFork (initSevm msg).benvStat.fork)
    (runtime : (initSevm msg).code = historyStorageCode)
    (caller : (initSevm msg).caller = systemAddress)
    (dynamic : (initSevm msg).isStatic = false) (enough : 47000 ≤ msg.gas) :
    exec (initEvm msg) = .ok (framePost (initSevm msg) (initDevm msg) msg.gas) := by
  let s := initSevm msg
  let b := initDevm msg
  let G := msg.gas - frameCost s b
  have cost := sstoreCost_le s b (key s) (Sevm.dataWord s 0)
  simp only [gasColdSload, gasStorageSet] at cost
  have balance : G + 21 + 22 + sstoreCost s b (key s) (Sevm.dataWord s 0) = msg.gas := by
    dsimp only [G, frameCost]
    omega
  have run := root_run (fs := prog) (sevm := s) (b := b) (M := .empty) (G := G)
    fork dynamic caller (by change 2300 < _; dsimp only [G, frameCost]; omega)
  change SFunc.RunExact prog s
    (St b [] .empty (G + 21 + 22 + sstoreCost s b (key s) (Sevm.dataWord s 0)))
    t_0000_c0 (.halted (framePost s b msg.gas)) at run
  rw [balance] at run
  have raw : Nonempty (Exec 0 s (St b [] .empty msg.gas) (.ok (framePost s b msg.gas))) := by
    apply lift_exact cert_check jumps_ok runtime fork.shanghaiOnwards
    exact ⟨t_0000_c0, prog_root, run⟩
  change Nonempty (Exec 0 s b (.ok (framePost s b msg.gas))) at raw
  exact (exec_iff_exec_eq _ _ _ _).mp raw

def writerChild (s : Sevm) (b : Devm) (word : B256) (gas : Nat) : Devm :=
  let m := SystemWordWriter.childMsg s b historyStorageAddress word gas historyStorageCode
  framePost (initSevm m) (initDevm m) m.gas

theorem child_error (msg : Msg) : (framePost (initSevm msg) (initDevm msg) msg.gas).error = none := by
  rw [framePost, St_error, afterSstore_error]
  rfl

theorem child_output (msg : Msg) : (framePost (initSevm msg) (initDevm msg) msg.gas).output = [] := by
  rw [framePost, show ∀ b S M G, (St b S M G).output = b.output from fun _ _ _ _ => rfl,
    afterSstore_output]
  rfl

/-- The child's success is derived from the real canonical runtime. -/
theorem writerChild_exec {s : Sevm} {b : Devm} {word : B256} {gas : Nat}
    (fork : CoveredFork s.benvStat.fork) (dynamic : s.isStatic = false)
    (system : s.currentTarget = systemAddress) (enough : 52000 ≤ gas) :
    exec (initEvm (SystemWordWriter.childMsg s b historyStorageAddress word gas historyStorageCode)) =
      .ok (writerChild s b word gas) := by
  apply frame_exec (msg := SystemWordWriter.childMsg s b historyStorageAddress word gas historyStorageCode) fork rfl system
  · change (false || s.isStatic) = false
    rw [dynamic]
    rfl
  · change 47000 ≤ SystemWordWriter.forwardedGas b historyStorageAddress gas
    have access : accessCost historyStorageAddress b.accessedAddresses ≤ 2600 := by
      unfold accessCost
      split <;> decide
    unfold SystemWordWriter.forwardedGas except64th
    omega

/-- Exact child storage, including arbitrary previous slot content. -/
theorem writerChild_state (s : Sevm) (b : Devm) (word : B256) (gas : Nat) :
    (writerChild s b word gas).state = b.state.setStorVal historyStorageAddress (key s) word := by
  let m := SystemWordWriter.childMsg s b historyStorageAddress word gas historyStorageCode
  have data : Sevm.dataWord (initSevm m) 0 = word := by
    apply dataWord_of_append (pre := []) (post := []) rfl
    exact SystemWordWriter.childMsg_data s b historyStorageAddress word gas historyStorageCode
  change (framePost (initSevm m) (initDevm m) m.gas).state = _
  rw [framePost, St_state, afterSstore_state, data]
  rfl

/-- At transaction entry the snapshot equals the current storage, so the actual
single SSTORE cannot introduce a negative refund. -/
theorem writerChild_refund (s : Sevm) (b : Devm) (word : B256) (gas : Nat)
    (origin : ∀ k, getOrigStorVal s historyStorageAddress k = b.getStorVal historyStorageAddress k) :
    0 ≤ (writerChild s b word gas).refundCounter := by
  let m := SystemWordWriter.childMsg s b historyStorageAddress word gas historyStorageCode
  let cs := initSevm m
  let cb := initDevm m
  have safe : RefundSafe (cb.getOrigStorVal cs cs.currentTarget (key cs))
      (cb.getStorVal cs.currentTarget (key cs)) := refundSafe_of_snapshot_eq cs cb (key cs) (origin _)
  exact afterSstore_refundCounter_ge_of_safe cs cb (key cs) (Sevm.dataWord cs 0) safe

theorem writerChild_noDelete (s : Sevm) (b : Devm) (word : B256) (gas : Nat)
    (fork : CoveredFork s.benvStat.fork) :
    (writerChild s b word gas).accountsToDelete.isEmpty = true := by
  let m := SystemWordWriter.childMsg s b historyStorageAddress word gas historyStorageCode
  have empty := callChildMsg_initDevm_accountsToDelete_isEmpty
    (sevm := s) (p := SystemWordWriter.parent b historyStorageAddress word gas)
    (mcs := SystemWordWriter.forwardedGas b historyStorageAddress gas) (value := 0)
    (callee := historyStorageAddress) (dadr := historyStorageAddress) (ii := 0) (is := 32)
    (code := historyStorageCode) (dp := false) (stmid := b.state) fork.shanghaiOnwards
  change (framePost (initSevm m) (initDevm m) m.gas).accountsToDelete.isEmpty = true
  rw [framePost, show ∀ b S M G, (St b S M G).accountsToDelete = b.accountsToDelete
    from fun _ _ _ _ => rfl, afterSstore_accountsToDelete]
  exact empty

/-- Settled parent effects used by original transaction receipt forwarding. -/
theorem writer_post_facts (s : Sevm) (b : Devm) (word : B256) (gas : Nat)
    (fork : CoveredFork s.benvStat.fork)
    (origin : ∀ k, getOrigStorVal s historyStorageAddress k = b.getStorVal historyStorageAddress k) :
    let p := SystemWordWriter.post b historyStorageAddress word gas (writerChild s b word gas)
    p.error = b.error ∧ p.output = b.output ∧ p.logs = b.logs ∧
    (∀ a, p.getCode a = b.getCode a) ∧
    p.accountsToDelete.isEmpty = b.accountsToDelete.isEmpty ∧ b.refundCounter ≤ p.refundCounter ∧
    p.state = b.state.setStorVal historyStorageAddress (key s) word := by
  let m := SystemWordWriter.childMsg s b historyStorageAddress word gas historyStorageCode
  have settled := SystemWordWriter.post_facts b (writerChild s b word gas)
    historyStorageAddress word gas (child_output m)
  refine ⟨settled.2.2.2.1, settled.2.2.2.2.1, ?_, ?_, ?_, ?_, settled.1.trans (writerChild_state s b word gas)⟩
  · have logs : (writerChild s b word gas).logs = [] := by
      change (framePost (initSevm m) (initDevm m) m.gas).logs = []
      rw [framePost, show ∀ b S M G, (St b S M G).logs = b.logs from fun _ _ _ _ => rfl,
        afterSstore_logs]
      change (match s.benvStat.rules.stateGas with | none => [] | some _ => _) = []
      rw [fork.rules_stateGas_none]
    rw [settled.2.1, logs, List.append_nil]
  · intro a
    change (framePost (initSevm m) (initDevm m) m.gas).getCode a = b.getCode a
    rw [framePost, St_getCode, afterSstore_getCode]
    rfl
  · rw [settled.2.2.2.2.2.1]
    exact adrSet_union_isEmpty _ _ (writerChild_noDelete s b word gas fork)
  · rw [settled.2.2.1]
    have refund := writerChild_refund s b word gas origin
    omega

/-- Exact original message execution through the real writer prefix and CALL. -/
theorem message_exec {msg : Msg} {word : B256}
    (fork : CoveredFork msg.benv.stat.fork) (depth : msg.depth ≠ 0)
    (dynamic : msg.isStatic = false) (system : msg.currentTarget = systemAddress)
    (gasLt : msg.gas < 2 ^ 256) (enough : 52027 ≤ msg.gas)
    (installed : msg.benv.state.getCode historyStorageAddress = historyStorageCode)
    (runtime : msg.code = SystemWordWriter.code historyStorageAddress word) :
    exec (initEvm msg) = .ok
      (SystemWordWriter.post (initDevm msg) historyStorageAddress word (msg.gas - 27)
        (writerChild (initSevm msg) (initDevm msg) word (msg.gas - 27))) := by
  have run := SystemWordWriter.exec (sevm := initSevm msg) (base := initDevm msg)
    (word := word) (gas := msg.gas - 27) fork depth (by omega) ?_ installed (by rfl) ?_
    runtime (writerChild_exec fork dynamic system (by omega)) (child_error _)
  · rw [Nat.sub_add_cancel (by omega : 27 ≤ msg.gas)] at run
    exact run
  · have access : accessCost historyStorageAddress (initDevm msg).accessedAddresses ≤ 2600 := by
      unfold accessCost
      split <;> decide
    omega
  · exact propext (iff_of_false fork.historyStorage_not_precompile (by decide))

end Blanc.Lift.HistoryStorage.Writer
