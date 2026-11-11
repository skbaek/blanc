import Blanc.Lift.SystemWordWriter
import Blanc.Lift.SystemExecution.BeaconRoots.SystemWalk

/-! The exact privileged word writer, with its actual child law discharged by
the canonical beacon-roots bytecode walk. This is a local execution building block,
not a closed kept-history control. -/

namespace Blanc.Lift.BeaconRoots.Writer

open Jaune Blanc.Lift
open SystemExecution.BeaconRoots

def tagKey (sevm : Sevm) : B256 := sevm.benvStat.time % (0x1fff : B256)
def valueKey (sevm : Sevm) : B256 := (0x1fff : B256) + tagKey sevm
def firstStore (sevm : Sevm) (base : Devm) : Devm :=
  afterSstore sevm base (tagKey sevm) sevm.benvStat.time
def frameCost (sevm : Sevm) (base : Devm) : Nat :=
  52 + sstoreCost sevm base (tagKey sevm) sevm.benvStat.time +
    sstoreCost sevm (firstStore sevm base) (valueKey sevm) (Sevm.dataWord sevm 0)
def framePost (sevm : Sevm) (base : Devm) (gas : Nat) : Devm :=
  St (afterSstore sevm (firstStore sevm base) (valueKey sevm) (Sevm.dataWord sevm 0))
    [] .empty (gas - frameCost sevm base + 1)

/-- The canonical SYSTEM arm at an arbitrary real child-message gas allocation. -/
theorem frame_exec {msg : Msg}
    (fork : CoveredFork (initSevm msg).benvStat.fork)
    (runtime : (initSevm msg).code = beaconRootsCode)
    (caller : (initSevm msg).caller = systemAddress)
    (dynamic : (initSevm msg).isStatic = false)
    (gas : 47000 ≤ msg.gas) :
    exec (initEvm msg) = .ok (framePost (initSevm msg) (initDevm msg) msg.gas) := by
  let sevm := initSevm msg
  let base := initDevm msg
  let cost := frameCost sevm base
  let G := msg.gas - cost
  have c₁ := sstoreCost_le sevm base (tagKey sevm) sevm.benvStat.time
  have c₂ := sstoreCost_le sevm (firstStore sevm base) (valueKey sevm) (Sevm.dataWord sevm 0)
  simp only [gasColdSload, gasStorageSet] at c₁ c₂
  have enough : 2300 < G := by
    dsimp only [G, cost, frameCost]
    omega
  have run := root_run (fs := prog) (sevm := sevm) (b := base) (M := .empty)
    (G := G) fork dynamic caller (by change 2300 < _; omega) (by change 2300 < _; omega)
  have sum : G + 21 + 31 +
      sstoreCost sevm base (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time +
      sstoreCost sevm
        (afterSstore sevm base (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time)
        ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256))
        (Sevm.dataWord sevm 0) = msg.gas := by
    dsimp only [G, cost, frameCost, firstStore, valueKey, tagKey]
    dsimp only [firstStore, valueKey, tagKey] at c₁ c₂
    omega
  rw [sum] at run
  have run : SFunc.RunExact prog sevm (St base [] .empty msg.gas) t_0000_c0
      (.halted (framePost sevm base msg.gas)) := run
  have raw : Nonempty (Exec 0 sevm (St base [] .empty msg.gas)
      (.ok (framePost sevm base msg.gas))) := by
    apply lift_exact cert_check jumps_ok runtime fork.shanghaiOnwards
    exact ⟨t_0000_c0, prog_root, run⟩
  change Nonempty (Exec 0 sevm base (.ok (framePost sevm base msg.gas))) at raw
  exact (exec_iff_exec_eq _ _ _ _).mp raw

theorem framePost_error (msg : Msg) :
    (framePost (initSevm msg) (initDevm msg) msg.gas).error = none := by
  rw [framePost, St_error, afterSstore_error, firstStore, afterSstore_error]
  rfl

theorem framePost_output (msg : Msg) :
    (framePost (initSevm msg) (initDevm msg) msg.gas).output = [] := by
  rw [framePost, show ∀ b S M G, (St b S M G).output = b.output from fun _ _ _ _ => rfl,
    afterSstore_output, firstStore, afterSstore_output]
  rfl

def writerChild (sevm : Sevm) (base : Devm) (word : B256) (gas : Nat) : Devm :=
  let msg := SystemWordWriter.childMsg sevm base beaconRootsAddress word gas beaconRootsCode
  framePost (initSevm msg) (initDevm msg) msg.gas

/-- The supplied child law is discharged by the real canonical R bytecode, at the
gas actually forwarded by the writer. -/
theorem writerChild_exec {sevm : Sevm} {base : Devm} {word : B256} {gas : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (system : sevm.currentTarget = systemAddress)
    (enough : 52000 ≤ gas) :
    exec (initEvm (SystemWordWriter.childMsg sevm base beaconRootsAddress word gas beaconRootsCode)) =
      .ok (writerChild sevm base word gas) := by
  apply frame_exec
    (msg := SystemWordWriter.childMsg sevm base beaconRootsAddress word gas beaconRootsCode)
    fork rfl system
  · change (false || sevm.isStatic) = false
    rw [dynamic]
    rfl
  · change 47000 ≤ SystemWordWriter.forwardedGas base beaconRootsAddress gas
    have access : accessCost beaconRootsAddress base.accessedAddresses ≤ 2600 := by
      unfold accessCost
      split <;> decide
    unfold SystemWordWriter.forwardedGas except64th
    omega

theorem writer_exec {sevm : Sevm} {base : Devm} {word : B256} {gas : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false) (system : sevm.currentTarget = systemAddress)
    (gasLt : gas < 2 ^ 256) (enough : 52000 ≤ gas)
    (installed : base.getCode beaconRootsAddress = beaconRootsCode)
    (runtime : sevm.code = SystemWordWriter.code beaconRootsAddress word) :
    exec ⟨0, sevm, base.setMach ⟨[], .empty, gas + 27, base.stateGas⟩⟩ =
      .ok (SystemWordWriter.post base beaconRootsAddress word gas (writerChild sevm base word gas)) := by
  apply SystemWordWriter.exec fork depth gasLt ?_ installed (by rfl) ?_
    runtime (writerChild_exec fork dynamic system enough) (framePost_error _)
  · have access : accessCost beaconRootsAddress base.accessedAddresses ≤ 2600 := by
      unfold accessCost
      split <;> decide
    omega
  · exact propext (iff_of_false fork.beaconRoots_not_precompile (by decide))

/-- A real message entry, with enough gas for the fixed prefix and the actual R child. -/
theorem message_exec {msg : Msg} {word : B256}
    (fork : CoveredFork msg.benv.stat.fork) (depth : msg.depth ≠ 0)
    (dynamic : msg.isStatic = false) (system : msg.currentTarget = systemAddress)
    (gasLt : msg.gas < 2 ^ 256) (enough : 52027 ≤ msg.gas)
    (installed : msg.benv.state.getCode beaconRootsAddress = beaconRootsCode)
    (runtime : msg.code = SystemWordWriter.code beaconRootsAddress word) :
    exec (initEvm msg) = .ok
      (SystemWordWriter.post (initDevm msg) beaconRootsAddress word (msg.gas - 27)
        (writerChild (initSevm msg) (initDevm msg) word (msg.gas - 27))) := by
  have run := writer_exec (sevm := initSevm msg) (base := initDevm msg)
    (word := word) (gas := msg.gas - 27) fork depth dynamic system
    (by omega) (by omega) installed runtime
  rw [Nat.sub_add_cancel (by omega : 27 ≤ msg.gas)] at run
  exact run

theorem writerChild_facts (sevm : Sevm) (base : Devm) (word : B256) (gas : Nat)
    (fork : CoveredFork sevm.benvStat.fork) :
    (writerChild sevm base word gas).error = none ∧
    (writerChild sevm base word gas).output = [] ∧
    (writerChild sevm base word gas).logs = [] ∧
    (∀ a, (writerChild sevm base word gas).getCode a = base.getCode a) ∧
    (writerChild sevm base word gas).state =
      (base.state.setStorVal beaconRootsAddress (tagKey sevm) sevm.benvStat.time).setStorVal
        beaconRootsAddress (valueKey sevm) word := by
  let msg := SystemWordWriter.childMsg sevm base beaconRootsAddress word gas beaconRootsCode
  have value : Sevm.dataWord (initSevm msg) 0 = word := by
    apply dataWord_of_append (pre := []) (post := []) rfl
    simp only [List.nil_append, List.append_nil]
    exact SystemWordWriter.childMsg_data sevm base beaconRootsAddress word gas beaconRootsCode
  refine ⟨framePost_error msg, framePost_output msg, ?_, ?_, ?_⟩
  · change (afterSstore (initSevm msg) (firstStore (initSevm msg) (initDevm msg))
      (valueKey (initSevm msg)) (Sevm.dataWord (initSevm msg) 0)).logs = []
    rw [afterSstore_logs, firstStore, afterSstore_logs]
    change (match sevm.benvStat.rules.stateGas with | none => [] | some _ => _) = []
    rw [fork.rules_stateGas_none]
  · intro a
    change (framePost (initSevm msg) (initDevm msg) msg.gas).getCode a = _
    rw [framePost, St_getCode, afterSstore_getCode, firstStore, afterSstore_getCode]
    rfl
  · change (framePost (initSevm msg) (initDevm msg) msg.gas).state = _
    rw [framePost, St_state, afterSstore_state, firstStore, afterSstore_state, value]
    rfl

theorem writerChild_noDelete (sevm : Sevm) (base : Devm) (word : B256) (gas : Nat)
    (fork : CoveredFork sevm.benvStat.fork) :
    (writerChild sevm base word gas).accountsToDelete.isEmpty = true := by
  let msg := SystemWordWriter.childMsg sevm base beaconRootsAddress word gas beaconRootsCode
  have empty := callChildMsg_initDevm_accountsToDelete_isEmpty
    (sevm := sevm) (p := SystemWordWriter.parent base beaconRootsAddress word gas)
    (mcs := SystemWordWriter.forwardedGas base beaconRootsAddress gas) (value := 0)
    (callee := beaconRootsAddress) (dadr := beaconRootsAddress) (ii := 0) (is := 32)
    (code := beaconRootsCode) (dp := false) (stmid := base.state) fork.shanghaiOnwards
  change (framePost (initSevm msg) (initDevm msg) msg.gas).accountsToDelete.isEmpty = true
  rw [framePost, show ∀ b S M G, (St b S M G).accountsToDelete = b.accountsToDelete
    from fun _ _ _ _ => rfl, afterSstore_accountsToDelete, firstStore, afterSstore_accountsToDelete]
  exact empty

/-- A transaction-start snapshot equal to the current R storage supplies the
original-value safety needed for nonnegative refunds. -/
theorem writerChild_refund (sevm : Sevm) (base : Devm) (word : B256) (gas : Nat)
    (origin : ∀ k, getOrigStorVal sevm beaconRootsAddress k = base.getStorVal beaconRootsAddress k) :
    0 ≤ (writerChild sevm base word gas).refundCounter := by
  let msg := SystemWordWriter.childMsg sevm base beaconRootsAddress word gas beaconRootsCode
  let csevm := initSevm msg
  let child := initDevm msg
  have safe₁ : RefundSafe (child.getOrigStorVal csevm csevm.currentTarget (tagKey csevm))
      (child.getStorVal csevm.currentTarget (tagKey csevm)) :=
    refundSafe_of_snapshot_eq csevm child (tagKey csevm) (origin _)
  have first : 0 ≤ (firstStore csevm child).refundCounter :=
    afterSstore_refundCounter_ge_of_safe csevm child (tagKey csevm) csevm.benvStat.time safe₁
  have safe₂ : RefundSafe ((firstStore csevm child).getOrigStorVal csevm csevm.currentTarget (valueKey csevm))
      ((firstStore csevm child).getStorVal csevm.currentTarget (valueKey csevm)) := by
    apply refundSafe_of_snapshot_eq
    rw [getStorVal_eq_getStor, firstStore, afterSstore_getStor_self,
      Stor.get_set_ne _ (show tagKey csevm ≠ valueKey csevm from systemKey_ne msg.benv)]
    exact origin _
  have second := afterSstore_refundCounter_ge_of_safe csevm (firstStore csevm child)
    (valueKey csevm) (Sevm.dataWord csevm 0) safe₂
  exact first.trans second

/-- Full settled writer effects, ready for the ordinary transaction receipt wrapper.
The snapshot premise is local to refund safety; the real child run is already proved. -/
theorem writer_post_facts (sevm : Sevm) (base : Devm) (word : B256) (gas : Nat)
    (fork : CoveredFork sevm.benvStat.fork)
    (origin : ∀ k, getOrigStorVal sevm beaconRootsAddress k = base.getStorVal beaconRootsAddress k) :
    let p := SystemWordWriter.post base beaconRootsAddress word gas (writerChild sevm base word gas)
    p.error = base.error ∧ p.output = base.output ∧ p.logs = base.logs ∧
    (∀ a, p.getCode a = base.getCode a) ∧
    p.accountsToDelete.isEmpty = base.accountsToDelete.isEmpty ∧
    base.refundCounter ≤ p.refundCounter ∧
    p.state = (base.state.setStorVal beaconRootsAddress (tagKey sevm) sevm.benvStat.time).setStorVal
      beaconRootsAddress (valueKey sevm) word := by
  have child := writerChild_facts sevm base word gas fork
  have settled := SystemWordWriter.post_facts base (writerChild sevm base word gas)
    beaconRootsAddress word gas child.2.1
  refine ⟨settled.2.2.2.1, settled.2.2.2.2.1, ?_, ?_, ?_, ?_, settled.1.trans child.2.2.2.2⟩
  · rw [settled.2.1, child.2.2.1, List.append_nil]
  · intro a
    exact (SystemWordWriter.post_code _ _ _ _ _ _).trans (child.2.2.2.1 a)
  · rw [settled.2.2.2.2.2.1]
    exact adrSet_union_isEmpty _ _ (writerChild_noDelete sevm base word gas fork)
  · rw [settled.2.2.1]
    have nonnegative := writerChild_refund sevm base word gas origin
    omega

end Blanc.Lift.BeaconRoots.Writer
