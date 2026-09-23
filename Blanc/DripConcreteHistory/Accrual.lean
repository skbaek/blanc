import Blanc.DripConcreteHistory.Join

namespace Blanc
open Jaune
namespace Drip

theorem concreteDripValidated :
    validateTransaction pragueRules concreteDripTx 0 =
      .ok (calculateIntrinsicCost pragueRules concreteDripTx 0) := by
  decide +kernel

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
  rw [checkTransaction, hgas]
  simp only [Except.mapError, bind, Except.bind]
  rw [hchain]
  change (do
    let sender ← Except.mapError TransitionError.senderRecovery (recoverSender 1 concreteDripTx)
    let (effective, maxFee) ← Except.mapError TransitionError.transaction
      (checkTransactionGasFee (initBenv .prague concreteJoined concreteDripExecutionHeader).beginTransaction concreteDripTx)
    let (maxFee, hashes) ← Except.mapError TransitionError.transaction
      (checkTransactionBlobData (initBenv .prague concreteJoined concreteDripExecutionHeader).beginTransaction concreteDripTx maxFee)
    Except.mapError TransitionError.transaction (checkTransactionReceiver concreteDripTx)
    Except.mapError TransitionError.transaction (checkTransactionAuthorizationList concreteDripTx)
    Except.mapError TransitionError.transaction (checkTransactionSenderAccount (concreteJoined.state.get sender) concreteDripTx maxFee)
    pure (sender, effective, hashes, 0)) = _
  rw [concreteDripRecoveredSender, hfee]
  change (do
    Except.mapError TransitionError.transaction
      (checkTransactionSenderAccount (concreteJoined.state.get concreteCreateSender) concreteDripTx 4000000)
    pure (concreteCreateSender, 2, [], 0)) = _
  rw [concreteDripSenderChecked]
  rfl

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
  rw [hb, if_neg (by decide +kernel)]
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
  simp [ByteArray.toList_eq_toList_data]

theorem concreteDripDebit_balance :
    concreteDripDebit.bal concreteCreateSender = 999999999997887794 := by
  unfold concreteDripDebit
  change ((concreteJoined.state.incrNonce concreteCreateSender).setBal concreteCreateSender
    ((concreteJoined.state.incrNonce concreteCreateSender).bal concreteCreateSender - 1000000)).bal _ = _
  unfold State.bal
  rw [State.setBal_get_self, State.incrNonce_get_bal]
  change concreteJoined.state.bal concreteCreateSender - 1000000 = _
  rw [concreteJoinedSenderBalance]
  decide +kernel

noncomputable def concreteDripEntry : Benv :=
  concreteDripMessage.benv.withState
    ((concreteDripDebit.setBal concreteCreateSender
      (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0)

theorem concreteDripEntry_run :
    concreteDripMessage.benvAfterTransfer = .ok concreteDripEntry := by
  unfold concreteDripEntry concreteDripMessage
  generalize concreteDripDebit = debit
  generalize concreteDripTxInput.beginTransaction = begun
  generalize concreteDripTenv = tenv
  have hnot : ¬ debit.bal concreteCreateSender < (0 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero]
    omega
  simp only [Msg.benvAfterTransfer, if_true, Benv.subBal, State.subBal, hnot, if_false,
    bind, Option.bind, Option.toExcept, Except.bind, Benv.addBal, Benv.withState]

theorem concreteDripEntry_storage (address : Adr) :
    (concreteDripEntry.state.get address).stor = (concreteJoined.state.get address).stor := by
  change (((concreteDripDebit.setBal _ _).addBal _ _).get address).stor = _
  unfold State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteDripDebit
  dsimp only
  rw [State.setBal_get_stor, State.incrNonce_get_stor]


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
  simp

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
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteDrip_clockMemoryFacts : concreteDripClockMemory.size = 224 ∧
    Bytes.toB256 (concreteDripClockMemory.read 192 32).1 = 5 ∧
    (concreteDripClockMemory.read 192 32).2 = concreteDripClockMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteDrip_exponentMemoryFacts : concreteDripExponentMemory.size = 224 ∧
    Bytes.toB256 (concreteDripExponentMemory.read 0 32).1 = 3 ∧
    (concreteDripExponentMemory.read 0 32).2 = concreteDripExponentMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteDrip_baseMemoryFacts : concreteDripBaseMemory.size = 256 ∧
    Bytes.toB256 (concreteDripBaseMemory.read 0 32).1 = 3 ∧
    (concreteDripBaseMemory.read 0 32).2 = concreteDripBaseMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteDrip_accumulatorMemoryFacts : concreteDripAccumulatorMemory.size = 288 ∧
    Bytes.toB256 (concreteDripAccumulatorMemory.read 0 32).1 = 3 ∧
    (concreteDripAccumulatorMemory.read 0 32).2 = concreteDripAccumulatorMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

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
