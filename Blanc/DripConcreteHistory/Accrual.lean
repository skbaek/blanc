import Blanc.DripConcreteHistory.Join
import Blanc.TransactionForward

namespace Blanc
open Jaune
namespace Drip

theorem concreteDripChecked :
    checkTransaction (initBenv .prague concreteJoined concreteDripExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteDripTx 0) concreteDripTx =
      .ok (concreteCreateSender, 2, [], 0) := by
  have hgas : checkTransactionGasLimits
      (initBenv .prague concreteJoined concreteDripExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteDripTx 0) concreteDripTx = .ok 0 := by decide +kernel
  have hchain : checkTransactionChainId
      (initBenv .prague concreteJoined concreteDripExecutionHeader).beginTransaction
      concreteDripTx = .ok () := by decide +kernel
  have hfee : checkTransactionGasFee
      (initBenv .prague concreteJoined concreteDripExecutionHeader).beginTransaction
      concreteDripTx = .ok (2, 4000000) := by decide +kernel
  have hblob : checkTransactionBlobData
      (initBenv .prague concreteJoined concreteDripExecutionHeader).beginTransaction
      concreteDripTx 4000000 = .ok (4000000, []) := by rfl
  have hreceiver : checkTransactionReceiver concreteDripTx = .ok () := by rfl
  have hauth : checkTransactionAuthorizationList concreteDripTx = .ok () := by rfl
  exact checkTransaction_ok_of_parts hgas hchain concreteDripRecoveredSender hfee
    hblob hreceiver hauth concreteDripSenderChecked

noncomputable def concreteDripTxInput : Benv :=
  initBenv .prague concreteJoined concreteDripExecutionHeader

noncomputable def concreteDripDebit : State :=
  let nonceState := concreteJoined.state.incrNonce concreteCreateSender
  nonceState.setBal concreteCreateSender (nonceState.bal concreteCreateSender - 1000000)

theorem concreteDripDebit_run :
    (concreteDripTxInput.beginTransaction.state.incrNonce concreteCreateSender).subBal
      concreteCreateSender 1000000 = some concreteDripDebit := by
  have hb : (concreteJoined.state.incrNonce concreteCreateSender).bal concreteCreateSender =
      999999999998887794 := by
    unfold State.bal
    rw [State.incrNonce_get_bal]
    exact concreteJoinedSenderBalance
  change (concreteJoined.state.incrNonce concreteCreateSender).subBal concreteCreateSender
    1000000 = _
  unfold State.subBal
  rw [hb, ite_eq_right (by decide +kernel)]
  unfold concreteDripDebit
  dsimp only
  rw [hb]

noncomputable def concreteDripTenv : Tenv :=
  deploymentTenv concreteDripTxInput concreteDripTx concreteCreateSender 0

noncomputable def concreteDripMessage : Msg := {
  benv := { concreteDripTxInput.beginTransaction with state := concreteDripDebit }
  tenv := concreteDripTenv
  caller := concreteCreateSender
  target := some concreteCreateTarget
  currentTarget := concreteCreateTarget
  gas := concreteDripTenv.stat.gas
  value := 0
  data := concreteDripTx.data
  code := concreteDripDebit.getCode concreteCreateTarget
  codeAddress := some concreteCreateTarget
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := concreteDripTenv.stat.accessListAddresses.insertMany
    (pragueRules.precompiles ++ [concreteCreateSender, concreteCreateTarget])
  accessedStorageKeys := concreteDripTenv.stat.accessListStorageKeys
  disablePrecompiles := false }

theorem concreteDripMessage_prepared :
    prepareMessage { concreteDripTxInput.beginTransaction with state := concreteDripDebit }
      concreteDripTenv concreteDripTx = .ok concreteDripMessage := rfl

theorem concreteDripMessage_code : concreteDripMessage.code.toList = code := by
  change (concreteDripDebit.getCode concreteCreateTarget).toList = code
  unfold concreteDripDebit
  rw [State.setBal_getCode]
  change ((concreteJoined.state.incrNonce concreteCreateSender).get concreteCreateTarget).code.toList = code
  rw [State.incrNonce_get_code]
  change (concreteJoined.state.getCode concreteCreateTarget).toList = code
  rw [concreteJoinedCode, concreteDeploymentRoot.installed]
  simp only [ByteArray.toList_eq_toList_data]

theorem concreteDripDebit_balance :
    concreteDripDebit.bal concreteCreateSender = 999999999997887794 := by
  unfold concreteDripDebit
  change ((concreteJoined.state.incrNonce concreteCreateSender).setBal concreteCreateSender
    ((concreteJoined.state.incrNonce concreteCreateSender).bal concreteCreateSender - 1000000)).bal _ = _
  unfold State.bal
  rw [State.setBal_get_self, Acct.clearIfEmpty_bal, State.incrNonce_get_bal]
  change concreteJoined.state.bal concreteCreateSender - 1000000 = _
  rw [concreteJoinedSenderBalance]
  decide +kernel

private theorem concreteDripDebit_sender_nonce :
    (concreteDripDebit.get concreteCreateSender).nonce = 3 := by
  unfold concreteDripDebit
  rw [State.setBal_get_nonce]
  unfold State.incrNonce
  rw [State.setAccount_get_self, Acct.clearIfEmpty_nonce]
  change concreteJoined.state.getNonce concreteCreateSender + 1 = 3
  rw [concreteJoinedSenderNonce]
  rfl

private theorem concreteDripDebit_sender_protected :
    State.Protected concreteDripDebit concreteCreateSender := by
  left
  rw [concreteDripDebit_sender_nonce]
  decide

private theorem concreteDripDebit_target_protected :
    State.Protected concreteDripDebit concreteCreateTarget := by
  right
  have hlen : code.length = 1762 := codeSize_exact
  change (concreteDripDebit.getCode concreteCreateTarget).size ≠ 0
  have image : (concreteDripDebit.getCode concreteCreateTarget).toList = code := concreteDripMessage_code
  rw [ByteArray.size_eq_length_toList, image]
  omega

private theorem concreteDripDebit_storage (address : Adr) :
    (concreteDripDebit.get address).stor = (concreteJoined.state.get address).stor := by
  have bumped : ((concreteJoined.state.incrNonce concreteCreateSender).get concreteCreateSender).nonce = 3 := by
    rw [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce]
    change concreteJoined.state.getNonce concreteCreateSender + 1 = 3
    rw [concreteJoinedSenderNonce]
    rfl
  unfold concreteDripDebit
  rw [State.setBal_get_stor, ite_eq_right]
  · rw [State.incrNonce_get_stor, ite_eq_right]
    rintro ⟨_, empty⟩
    have nonzero : concreteJoined.state.getNonce concreteCreateSender + 1 ≠ 0 := by
      rw [concreteJoinedSenderNonce]
      decide
    exact nonzero empty.2.1
  · rintro ⟨_, empty⟩
    have nonzero : ((concreteJoined.state.incrNonce concreteCreateSender).get concreteCreateSender).nonce ≠ 0 := by
      rw [bumped]
      decide
    exact nonzero empty.2.1

/-- The synthetic zero debit and zero credit are the identity on the actual debited world. -/
theorem concreteDripEntryState_eq :
    (concreteDripDebit.setBal concreteCreateSender
      (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0 =
        concreteDripDebit := by
  rw [B256.sub_zero, State.setBal_current_of_protected concreteDripDebit_sender_protected,
    State.addBal_zero_of_protected concreteDripDebit_target_protected]

noncomputable def concreteDripEntry : Benv :=
  concreteDripMessage.benv.withState
    ((concreteDripDebit.setBal concreteCreateSender
      (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0)

theorem concreteDripEntry_run :
    concreteDripMessage.benvAfterTransfer = .ok concreteDripEntry := by
  rw [Msg.benvAfterTransfer_of_value_zero rfl]
  unfold concreteDripEntry
  rw [concreteDripEntryState_eq]
  rfl

theorem concreteDripEntry_storage (address : Adr) :
    (concreteDripEntry.state.get address).stor = (concreteJoined.state.get address).stor := by
  change (((concreteDripDebit.setBal _ _).addBal _ _).get address).stor = _
  rw [concreteDripEntryState_eq]
  exact concreteDripDebit_storage address


noncomputable def concreteDripSevm : Sevm := initSevm (concreteDripMessage.withBenv concreteDripEntry)
noncomputable def concreteDripDevm : Devm := initDevm (concreteDripMessage.withBenv concreteDripEntry)

theorem concreteDripDevm_chi : concreteDripDevm.getStorVal concreteCreateTarget chiSlot = rate := by
  change (concreteDripEntry.state.get concreteCreateTarget).stor.get chiSlot = rate
  rw [concreteDripEntry_storage]
  exact concreteJoined_values.1

theorem concreteDripDevm_rho : concreteDripDevm.getStorVal concreteCreateTarget rhoSlot = 2 := by
  change (concreteDripEntry.state.get concreteCreateTarget).stor.get rhoSlot = 2
  rw [concreteDripEntry_storage]
  exact concreteJoined_values.2.1

theorem concreteDripDevm_cold (k : B256) :
    (concreteCreateTarget, k) ∉ concreteDripDevm.accessedStorageKeys := by
  change (concreteCreateTarget, k) ∉ (∅ : Std.HashSet (Adr × B256))
  simp only [Std.HashSet.not_mem_empty, not_false_eq_true]

def concreteDripStagingMemory : Mem := Mem.empty.write 32 (4 : B256).toBytes

private theorem concreteDrip_readChi (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat) (next : Func)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hchi : base.getStorVal sevm.currentTarget chiSlot = rate)
    (hcold : (sevm.currentTarget, chiSlot) ∉ base.accessedStorageKeys)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((addAccessedStorageKey base sevm.currentTarget chiSlot).setMach ⟨[rate], M, G, base.stateGas⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 2103, base.stateGas⟩)
      (Ninst.pushB256 chiSlot ::: Ninst.sload ::: next) post := by
  func_run (2)
  change Func.RunCompiled _ sevm
    ((addAccessedStorageKey base sevm.currentTarget chiSlot).setMach
      ⟨[base.getStorVal sevm.currentTarget chiSlot], M, G + 2103 - 2103, base.stateGas⟩) next post
  simpa only [hchi, Nat.add_sub_cancel] using htail


private theorem concreteDrip_stageClock (sevm : Sevm) (base post : Devm) (M C : Mem)
    (G : Nat) (next : Func) (htime : sevm.benvStat.time = 5)
    (hsize : M.size = 64)
    (hstore : M.write (storedChiWord * 32).toNat rate.toBytes = C)
    (hcsize : C.size = 192)
    (hread : Bytes.toB256 (C.read (storedChiWord * 32).toNat 32).1 = rate)
    (hmem : (C.read (storedChiWord * 32).toNat 32).2 = C)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], C.write 192 (5 : B256).toBytes, G, base.stateGas⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[rate], M, G + 79, base.stateGas⟩)
      (mstoreAt storedChiWord +++
        (Ninst.pushB256 scale ::: loadWord storedChiWord +++ Ninst.lt :::
          (.revert <?>
            (loadWord storedChiWord +++ Ninst.pushB256 maxChi ::: Ninst.lt :::
              (.revert <?> (Ninst.timestamp ::: mstoreAt nowWord +++ next)))))) post := by
  func_run (2) [12]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (3) [0]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [htime]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], C.write 192 (5 : B256).toBytes, G + 79 - 79, base.stateGas⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteDrip_stageElapsed (sevm : Sevm) (base post : Devm) (M E : Mem)
    (G : Nat) (next : Func)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hrho : base.getStorVal sevm.currentTarget rhoSlot = 2)
    (hcold : (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hsize : M.size = 224)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 5)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hstore : M.write (exponentWord * 32).toNat (3 : B256).toBytes = E)
    (hesize : E.size = 224)
    (hexp : Bytes.toB256 (E.read (exponentWord * 32).toNat 32).1 = 3)
    (hemem : (E.read (exponentWord * 32).toNat 32).2 = E)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((addAccessedStorageKey base sevm.currentTarget rhoSlot).setMach ⟨[], E, G, base.stateGas⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 2166, base.stateGas⟩)
      (Ninst.pushB256 rhoSlot ::: Ninst.sload ::: Ninst.dup 0 :::
        loadWord nowWord +++ Ninst.lt :::
          (.revert <?> (loadWord nowWord +++ Ninst.sub :::
            mstoreAt exponentWord +++ loadWord exponentWord +++
            Ninst.pushB256 maxElapsed ::: Ninst.lt ::: (.revert <?> next)))) post := by
  func_run (2)
  change Func.RunCompiled _ sevm
    ((addAccessedStorageKey base sevm.currentTarget rhoSlot).setMach
      ⟨[base.getStorVal sevm.currentTarget rhoSlot], M, G + 2166 - 2103, base.stateGas⟩) _ post
  rw [hrho]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (3) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hesize]
    decide +kernel
  rw [hexp, hemem]
  func_run (3) [0]
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteDrip_initializeRpow (sevm : Sevm) (base post : Devm) (M B A Z : Mem)
    (G : Nat) (zeroBase zeroExponent evenExponent : Func)
    (hsize : M.size = 224)
    (hbase : M.write (baseWord * 32).toNat rate.toBytes = B)
    (hbsize : B.size = 256)
    (hbexp : Bytes.toB256 (B.read (exponentWord * 32).toNat 32).1 = 3)
    (hbmem : (B.read (exponentWord * 32).toNat 32).2 = B)
    (hacc : B.write (accumulatorWord * 32).toNat rate.toBytes = A)
    (hasize : A.size = 288)
    (haexp : Bytes.toB256 (A.read (exponentWord * 32).toNat 32).1 = 3)
    (hamem : (A.read (exponentWord * 32).toNat 32).2 = A)
    (hzero : A.write (exponentWord * 32).toNat (1 : B256).toBytes = Z)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Z, G, base.stateGas⟩) rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 122, base.stateGas⟩)
      (Ninst.pushB256 rate ::: Ninst.dup 0 ::: mstoreAt baseWord +++ Ninst.iszero :::
        (zeroBase <?> (loadWord exponentWord +++ Ninst.iszero :::
          (zeroExponent <?> (loadWord exponentWord +++ Ninst.pushB256 1 ::: Ninst.and :::
            ((Ninst.pushB256 rate ::: mstoreAt accumulatorWord +++ loadWord exponentWord +++
              Ninst.pushB256 2 ::: Ninst.swap 0 ::: Ninst.div ::: mstoreAt exponentWord +++
              .call rpowLoopSlot) <?> evenExponent)))))) post := by
  func_run (4) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hbase]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (3) [1]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hacc]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [haexp, hamem]
  func_run (5) [1, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [hzero]
  apply Func.runCompiled_call' (f := rpowLoop) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach, Devm.stateGas_setMach] using hloop


def concreteDripClockMemory : Mem :=
  (concreteDripStagingMemory.write 160 rate.toBytes).write 192 (5 : B256).toBytes
def concreteDripExponentMemory : Mem := concreteDripClockMemory.write 0 (3 : B256).toBytes
def concreteDripBaseMemory : Mem := concreteDripExponentMemory.write 224 rate.toBytes
def concreteDripAccumulatorMemory : Mem := concreteDripBaseMemory.write 256 rate.toBytes
def concreteDripLoopMemory : Mem := concreteDripAccumulatorMemory.write 0 (1 : B256).toBytes

def concreteDripFreshBase (sevm : Sevm) (base : Devm) : Devm :=
  addAccessedStorageKey (addAccessedStorageKey base sevm.currentTarget chiSlot) sevm.currentTarget rhoSlot

private theorem concreteDrip_stagingSize : concreteDripStagingMemory.size = 64 := by decide +kernel

private theorem concreteDrip_chiMemoryFacts :
    (concreteDripStagingMemory.write 160 rate.toBytes).size = 192 ∧
    Bytes.toB256 ((concreteDripStagingMemory.write 160 rate.toBytes).read 160 32).1 = rate ∧
    ((concreteDripStagingMemory.write 160 rate.toBytes).read 160 32).2 =
      concreteDripStagingMemory.write 160 rate.toBytes := by
  have hsize : (concreteDripStagingMemory.write 160 rate.toBytes).size = 192 :=
    Mem.size_write_of_size (i := 160) concreteDrip_stagingSize
      (by decide) (B256.length_toBytes rate)
  have hreads : Mem.Reads (concreteDripStagingMemory.write 160 rate.toBytes)
      (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes) 160 rate.toBytes) := by
    unfold concreteDripStagingMemory
    repeat' first | apply Mem.Reads.write | apply Mem.Wf.write |
      exact Mem.wf_empty | exact Mem.reads_empty
  refine ⟨hsize, ?_, Mem.read_snd_eq_self ?_⟩
  · rw [hreads.read]
    exact Bytes.readWord_writeAt_self _ _ _
  · rw [hsize]
    decide

private theorem concreteDrip_clockMemoryFacts : concreteDripClockMemory.size = 224 ∧
    Bytes.toB256 (concreteDripClockMemory.read 192 32).1 = 5 ∧
    (concreteDripClockMemory.read 192 32).2 = concreteDripClockMemory := by
  have hsize : concreteDripClockMemory.size = 224 :=
    Mem.size_write_of_size (i := 192) concreteDrip_chiMemoryFacts.1
      (by decide) (B256.length_toBytes (5 : B256))
  have hreads : Mem.Reads concreteDripClockMemory
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes)
        160 rate.toBytes) 192 (5 : B256).toBytes) := by
    unfold concreteDripClockMemory concreteDripStagingMemory
    repeat' first | apply Mem.Reads.write | apply Mem.Wf.write |
      exact Mem.wf_empty | exact Mem.reads_empty
  refine ⟨hsize, ?_, Mem.read_snd_eq_self ?_⟩
  · rw [hreads.read]
    exact Bytes.readWord_writeAt_self _ _ _
  · rw [hsize]
    decide

private theorem concreteDrip_exponentMemoryFacts : concreteDripExponentMemory.size = 224 ∧
    Bytes.toB256 (concreteDripExponentMemory.read 0 32).1 = 3 ∧
    (concreteDripExponentMemory.read 0 32).2 = concreteDripExponentMemory := by
  have hsize : concreteDripExponentMemory.size = 224 :=
    Mem.size_write_of_size (i := 0) concreteDrip_clockMemoryFacts.1
      (by decide) (B256.length_toBytes (3 : B256))
  refine ⟨hsize, ?_, Mem.read_snd_eq_self ?_⟩
  · change Bytes.toB256 ((concreteDripClockMemory.write 0 (3 : B256).toBytes).read 0 32).1 = 3
    simpa only [B256.length_toBytes, B256.toB256_toBytes] using
      congrArg Bytes.toB256 (Mem.read_write_zero concreteDripClockMemory
        (ys := (3 : B256).toBytes) (by decide))
  · rw [hsize]
    decide

private theorem concreteDrip_baseMemoryFacts : concreteDripBaseMemory.size = 256 ∧
    Bytes.toB256 (concreteDripBaseMemory.read 0 32).1 = 3 ∧
    (concreteDripBaseMemory.read 0 32).2 = concreteDripBaseMemory := by
  have hsize : concreteDripBaseMemory.size = 256 :=
    Mem.size_write_of_size (i := 224) concreteDrip_exponentMemoryFacts.1
      (by decide) (B256.length_toBytes rate)
  have hreads : Mem.Reads concreteDripBaseMemory
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt []
        32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes)
        0 (3 : B256).toBytes) 224 rate.toBytes) := by
    unfold concreteDripBaseMemory concreteDripExponentMemory
      concreteDripClockMemory concreteDripStagingMemory
    repeat' first | apply Mem.Reads.write | apply Mem.Wf.write |
      exact Mem.wf_empty | exact Mem.reads_empty
  refine ⟨hsize, ?_, Mem.read_snd_eq_self ?_⟩
  · rw [hreads.read,
      Bytes.readWord_writeAt_of_disjoint _ 0 224 _ (by decide)]
    exact Bytes.readWord_writeAt_self _ _ _
  · rw [hsize]
    decide

private theorem concreteDrip_accumulatorMemoryFacts : concreteDripAccumulatorMemory.size = 288 ∧
    Bytes.toB256 (concreteDripAccumulatorMemory.read 0 32).1 = 3 ∧
    (concreteDripAccumulatorMemory.read 0 32).2 = concreteDripAccumulatorMemory := by
  have hsize : concreteDripAccumulatorMemory.size = 288 :=
    Mem.size_write_of_size (i := 256) concreteDrip_baseMemoryFacts.1
      (by decide) (B256.length_toBytes rate)
  have hreads : Mem.Reads concreteDripAccumulatorMemory
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt []
        32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes)
        0 (3 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) := by
    unfold concreteDripAccumulatorMemory concreteDripBaseMemory
      concreteDripExponentMemory concreteDripClockMemory concreteDripStagingMemory
    repeat' first | apply Mem.Reads.write | apply Mem.Wf.write |
      exact Mem.wf_empty | exact Mem.reads_empty
  refine ⟨hsize, ?_, Mem.read_snd_eq_self ?_⟩
  · rw [hreads.read,
      Bytes.readWord_writeAt_of_disjoint _ 0 256 _ (by decide),
      Bytes.readWord_writeAt_of_disjoint _ 0 224 _ (by decide)]
    exact Bytes.readWord_writeAt_self _ _ _
  · rw [hsize]
    decide

theorem concreteDrip_freshStart (sevm : Sevm) (base post : Devm) (G : Nat)
    (htime : sevm.benvStat.time = 5)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hchi : base.getStorVal sevm.currentTarget chiSlot = rate)
    (hrho : base.getStorVal sevm.currentTarget rhoSlot = 2)
    (hcoldChi : (sevm.currentTarget, chiSlot) ∉ base.accessedStorageKeys)
    (hcoldRho : (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((concreteDripFreshBase sevm base).setMach ⟨[], concreteDripLoopMemory, G, (concreteDripFreshBase sevm base).stateGas⟩)
      rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteDripStagingMemory, G + 122 + 2166 + 79 + 2103, base.stateGas⟩)
      freshStart post := by
  apply concreteDrip_readChi sevm _ _ _ _ _ hsg hchi hcoldChi
  apply concreteDrip_stageClock (sevm := sevm) (C := concreteDripStagingMemory.write 160 rate.toBytes)
  · exact htime
  · exact concreteDrip_stagingSize
  · rfl
  · exact concreteDrip_chiMemoryFacts.1
  · exact concreteDrip_chiMemoryFacts.2.1
  · exact concreteDrip_chiMemoryFacts.2.2
  apply concreteDrip_stageElapsed (E := concreteDripExponentMemory) (hsg := hsg)
  · exact hrho
  · change (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys.insert
      (sevm.currentTarget, chiSlot)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by simp only [beq_iff_eq, Prod.mk.injEq, true_and]; decide +kernel, hcoldRho⟩
  · exact concreteDrip_clockMemoryFacts.1
  · exact concreteDrip_clockMemoryFacts.2.1
  · exact concreteDrip_clockMemoryFacts.2.2
  · rfl
  · exact concreteDrip_exponentMemoryFacts.1
  · exact concreteDrip_exponentMemoryFacts.2.1
  · exact concreteDrip_exponentMemoryFacts.2.2
  apply concreteDrip_initializeRpow (B := concreteDripBaseMemory)
    (A := concreteDripAccumulatorMemory) (Z := concreteDripLoopMemory)
  · exact concreteDrip_exponentMemoryFacts.1
  · rfl
  · exact concreteDrip_baseMemoryFacts.1
  · exact concreteDrip_baseMemoryFacts.2.1
  · exact concreteDrip_baseMemoryFacts.2.2
  · rfl
  · exact concreteDrip_accumulatorMemoryFacts.1
  · exact concreteDrip_accumulatorMemoryFacts.2.1
  · exact concreteDrip_accumulatorMemoryFacts.2.2
  · rfl
  exact hloop


def concreteDripSquare : B256 := 1000000003094251918120023625
def concreteDripFactor : B256 := 1000000004641377880770433536
def concreteDripChi : B256 := 1000000006188503845814442183

end Drip
end Blanc
