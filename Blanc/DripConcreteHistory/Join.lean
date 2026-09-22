import Blanc.DripConcreteHistory.Deployment

namespace Blanc
open Jaune
namespace Drip

theorem concreteJoinValidated :
    validateTransaction pragueRules concreteJoinTx 0 =
      .ok (calculateIntrinsicCost pragueRules concreteJoinTx 0) := by
  decide +kernel

theorem concreteJoinChecked :
    checkTransaction (initBenv .prague concreteDeployed concreteJoinExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteJoinTx 0) concreteJoinTx =
      .ok (concreteCreateSender, 2, [], 0) := by
  have hgas : checkTransactionGasLimits
      (initBenv .prague concreteDeployed concreteJoinExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteJoinTx 0) concreteJoinTx = .ok 0 := by decide +kernel
  have hchain : checkTransactionChainId
      (initBenv .prague concreteDeployed concreteJoinExecutionHeader).beginTransaction
      concreteJoinTx = .ok () := by decide +kernel
  have hfee : checkTransactionGasFee
      (initBenv .prague concreteDeployed concreteJoinExecutionHeader).beginTransaction
      concreteJoinTx = .ok (2, 4000000) := by decide +kernel
  rw [checkTransaction, hgas]
  simp only [Except.mapError, bind, Except.bind]
  rw [hchain]
  change (do
    let sender ← Except.mapError TransitionError.senderRecovery (recoverSender 1 concreteJoinTx)
    let (effective, maxFee) ← Except.mapError TransitionError.transaction
      (checkTransactionGasFee (initBenv .prague concreteDeployed concreteJoinExecutionHeader).beginTransaction concreteJoinTx)
    let (maxFee, hashes) ← Except.mapError TransitionError.transaction
      (checkTransactionBlobData (initBenv .prague concreteDeployed concreteJoinExecutionHeader).beginTransaction concreteJoinTx maxFee)
    Except.mapError TransitionError.transaction (checkTransactionReceiver concreteJoinTx)
    Except.mapError TransitionError.transaction (checkTransactionAuthorizationList concreteJoinTx)
    Except.mapError TransitionError.transaction (checkTransactionSenderAccount (concreteDeployed.state.get sender) concreteJoinTx maxFee)
    pure (sender, effective, hashes, 0)) = _
  rw [concreteJoinRecoveredSender, hfee]
  change (do
    Except.mapError TransitionError.transaction
      (checkTransactionSenderAccount (concreteDeployed.state.get concreteCreateSender) concreteJoinTx 4000000)
    pure (concreteCreateSender, 2, [], 0)) = _
  rw [concreteJoinSenderChecked]
  rfl

noncomputable def concreteJoinTxInput : Benv :=
  initBenv .prague concreteDeployed concreteJoinExecutionHeader

noncomputable def concreteJoinDebit : State :=
  let nonceState := concreteDeployed.state.incrNonce concreteCreateSender
  nonceState.setBal concreteCreateSender (nonceState.bal concreteCreateSender - 1000000)

theorem concreteJoinDebit_run :
    (concreteJoinTxInput.beginTransaction.state.incrNonce concreteCreateSender).subBal
      concreteCreateSender 1000000 = some concreteJoinDebit := by
  have hb : (concreteDeployed.state.incrNonce concreteCreateSender).bal concreteCreateSender =
      999999999999040182 := by
    unfold State.bal
    rw [State.incrNonce_get_bal]
    exact concreteDeployedSenderBalance
  change (concreteDeployed.state.incrNonce concreteCreateSender).subBal concreteCreateSender
    1000000 = _
  unfold State.subBal
  rw [hb, if_neg (by decide +kernel)]
  unfold concreteJoinDebit
  dsimp only
  rw [hb]

noncomputable def concreteJoinTenv : Tenv :=
  deploymentTenv concreteJoinTxInput concreteJoinTx concreteCreateSender 0

noncomputable def concreteJoinMessage : Msg := {
  benv := { concreteJoinTxInput.beginTransaction with state := concreteJoinDebit }
  tenv := concreteJoinTenv
  caller := concreteCreateSender
  target := some concreteCreateTarget
  currentTarget := concreteCreateTarget
  gas := concreteJoinTenv.stat.gas
  value := 100
  data := concreteJoinTx.data
  code := concreteJoinDebit.getCode concreteCreateTarget
  codeAddress := some concreteCreateTarget
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := concreteJoinTenv.stat.accessListAddresses.insertMany
    (pragueRules.precompiles ++ [concreteCreateSender, concreteCreateTarget])
  accessedStorageKeys := concreteJoinTenv.stat.accessListStorageKeys
  disablePrecompiles := false }

theorem concreteJoinMessage_prepared :
    prepareMessage { concreteJoinTxInput.beginTransaction with state := concreteJoinDebit }
      concreteJoinTenv concreteJoinTx = .ok concreteJoinMessage := rfl

theorem concreteJoinMessage_code : concreteJoinMessage.code.toList = code := by
  change (concreteJoinDebit.getCode concreteCreateTarget).toList = code
  unfold concreteJoinDebit
  rw [State.setBal_getCode]
  change ((concreteDeployed.state.incrNonce concreteCreateSender).get concreteCreateTarget).code.toList = code
  rw [State.incrNonce_get_code]
  change (concreteDeployed.state.getCode concreteCreateTarget).toList = code
  rw [concreteDeploymentRoot.installed]
  simp [ByteArray.toList_eq_toList_data]

theorem concreteJoinDebit_balance :
    concreteJoinDebit.bal concreteCreateSender = 999999999998040182 := by
  unfold concreteJoinDebit
  change ((concreteDeployed.state.incrNonce concreteCreateSender).setBal concreteCreateSender
    ((concreteDeployed.state.incrNonce concreteCreateSender).bal concreteCreateSender - 1000000)).bal _ = _
  unfold State.bal
  rw [State.setBal_get_self, State.incrNonce_get_bal]
  change concreteDeployed.state.bal concreteCreateSender - 1000000 = _
  rw [concreteDeployedSenderBalance]
  decide +kernel

noncomputable def concreteJoinEntry : Benv :=
  concreteJoinMessage.benv.withState
    ((concreteJoinDebit.setBal concreteCreateSender
      (concreteJoinDebit.bal concreteCreateSender - 100)).addBal concreteCreateTarget 100)

theorem concreteJoinEntry_run :
    concreteJoinMessage.benvAfterTransfer = .ok concreteJoinEntry := by
  have hs : concreteJoinDebit.subBal concreteCreateSender 100 =
      some (concreteJoinDebit.setBal concreteCreateSender
        (concreteJoinDebit.bal concreteCreateSender - 100)) := by
    unfold State.subBal
    rw [concreteJoinDebit_balance, if_neg (by decide +kernel)]
  change (do
    let b ← (concreteJoinMessage.benv.subBal concreteCreateSender 100).toExcept _
    pure (b.addBal concreteCreateTarget 100)) = _
  unfold Benv.subBal
  change (do
    let b ← (do
      let st ← concreteJoinDebit.subBal concreteCreateSender 100
      some (concreteJoinMessage.benv.withState st)).toExcept _
    pure (b.addBal concreteCreateTarget 100)) = _
  rw [hs]
  rfl

theorem concreteJoinEntry_storage (address : Adr) :
    (concreteJoinEntry.state.get address).stor = (concreteDeployed.state.get address).stor := by
  change (((concreteJoinDebit.setBal _ _).addBal _ _).get address).stor = _
  unfold State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteJoinDebit
  dsimp only
  rw [State.setBal_get_stor, State.incrNonce_get_stor]

private theorem concreteJoin_dispatch (sevm : Sevm) (base post : Devm) (G : Nat)
    (hdata : sevm.data = concreteJoinTx.data)
    (hjoin : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩) join post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
    (base.setMach ⟨[], Mem.empty, G + 113, base.stateGas⟩) main post := by
  have hd : dripSelector = (0x9f678cca : B256) := by decide +kernel
  have hj : joinSelector = (0xb688a363 : B256) := by decide +kernel
  have hshift : Sevm.dataWord sevm 0 >>> B256.toNat 224 = joinSelector := by
    simp only [Sevm.dataWord, hdata, concreteJoinTx]
    decide +kernel
  func_run (1)
  simp only [hdata, concreteJoinTx]
  func_run (5) [joinSelector]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[joinSelector], Mem.empty, G + 113 - 27, base.stateGas⟩) (dispatch tree) post
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[joinSelector], Mem.empty, G + 113 - 27, base.stateGas⟩)
    (Ninst.dup 0 ::: Ninst.pushB256 dripSelector ::: Ninst.gt :::
      (dispatch (.fork (.fork (.leaf convertToAssetsSelector (nonpayable (exactCalldata 36 convertToAssets)))
          (.leaf exitSelector (nonpayable (exactCalldata 36 exit))))
        (.leaf convertToUnitsSelector (nonpayable (exactCalldata 36 convertToUnits)))) <?>
       dispatch (.fork (.leaf dripSelector (nonpayable (exactCalldata 4 drip)))
         (.leaf joinSelector (exactCalldata 4 join))))) post
  simp only [hd, hj]
  func_run (4) [0]
  func_run (11) [0, 1, 1]
  all_goals first
    | exact hjoin
    | (simp only [hdata, concreteJoinTx]; decide +kernel)

noncomputable def concreteJoinSevm : Sevm :=
  initSevm (concreteJoinMessage.withBenv concreteJoinEntry)

private theorem concreteJoin_stateGas_none : concreteJoinSevm.benvStat.rules.stateGas = none := by
  exact CoveredFork.prague.rules_stateGas_none

def concreteJoinStagingMemory : Mem :=
  (((Mem.empty.write 64 (100 : B256).toBytes).write 96 (0 : B256).toBytes).write
    128 (0 : B256).toBytes).write 32 (5 : B256).toBytes

def concreteJoinStagingBase (base : Devm) : Devm :=
  addAccessedStorageKey (addAccessedStorageKey base concreteCreateTarget
    concreteCreateSender.toB256) concreteCreateTarget totalUnitsSlot

private theorem concreteJoin_stage (base post : Devm) (G : Nat)
    (hrow : base.getStorVal concreteCreateTarget concreteCreateSender.toB256 = 0)
    (htotal : base.getStorVal concreteCreateTarget totalUnitsSlot = 0)
    (hcoldRow : (concreteCreateTarget, concreteCreateSender.toB256) ∉ base.accessedStorageKeys)
    (hcoldTotal : (concreteCreateTarget, totalUnitsSlot) ∉ base.accessedStorageKeys)
    (hfresh : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      ((concreteJoinStagingBase base).setMach
        ⟨[], concreteJoinStagingMemory, G, (concreteJoinStagingBase base).stateGas⟩)
      freshStart post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], Mem.empty, G + 4327, base.stateGas⟩) join post := by
  func_run (8) [9, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  func_run (1)
  · exact concreteJoin_stateGas_none
  change Func.RunCompiled _ concreteJoinSevm
    ((addAccessedStorageKey _ concreteCreateTarget concreteCreateSender.toB256).setMach
      ⟨[base.getStorVal concreteCreateTarget concreteCreateSender.toB256],
        Mem.empty.write 64 (100 : B256).toBytes, G + 4327 - 2141, base.stateGas⟩) _ post
  rw [hrow]
  func_run (7) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteJoinSevm
    ((addAccessedStorageKey base concreteCreateTarget concreteCreateSender.toB256).setMach
      ⟨[totalUnitsSlot], (Mem.empty.write 64 (100 : B256).toBytes).write 96 (0 : B256).toBytes,
        G + 4327 - 2175, base.stateGas⟩) _ post
  func_run (1)
  · exact concreteJoin_stateGas_none
  · change (concreteCreateTarget, totalUnitsSlot) ∉
      base.accessedStorageKeys.insert (concreteCreateTarget, concreteCreateSender.toB256)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by decide +kernel, hcoldTotal⟩
  change Func.RunCompiled _ concreteJoinSevm
    ((concreteJoinStagingBase base).setMach
      ⟨[base.getStorVal concreteCreateTarget totalUnitsSlot],
        (Mem.empty.write 64 (100 : B256).toBytes).write 96 (0 : B256).toBytes,
        G + 4327 - 4275, (concreteJoinStagingBase base).stateGas⟩) _ post
  rw [htotal]
  func_run (6) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  func_run (3) [0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteJoinSevm
    ((concreteJoinStagingBase base).setMach
      ⟨[], concreteJoinStagingMemory, G + 4327 - 4315, (concreteJoinStagingBase base).stateGas⟩)
    (.call freshStartSlot) post
  apply Func.runCompiled_call' (f := freshStart) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
      Devm.stateGas_setMach] using hfresh

theorem concreteDeployedRho : (concreteDeployed.state.getStor concreteCreateTarget).get rhoSlot = 1 := by
  rw [concreteDeployed_state]
  unfold concreteDeploymentState deploymentFinalState
  change (((((constructorInstalledState concreteConstructorEntry concreteCreateTarget 1).addBal _ _).addBal _ _).get
    concreteCreateTarget).stor).get rhoSlot = 1
  simp only [State.addBal, State.setBal_get_stor, constructorInstalledState,
    State.setCode_get_stor, constructorStoredState, State.setStorVal,
    State.get_set_self]
  exact Stor.get_set_self _ _ _

noncomputable def concreteJoinDevm : Devm :=
  initDevm (concreteJoinMessage.withBenv concreteJoinEntry)

theorem concreteJoinDevm_chi : concreteJoinDevm.getStorVal concreteCreateTarget chiSlot = scale := by
  change (concreteJoinEntry.state.get concreteCreateTarget).stor.get chiSlot = scale
  rw [concreteJoinEntry_storage]
  exact concreteDeploymentRoot.chi

theorem concreteJoinDevm_rho : concreteJoinDevm.getStorVal concreteCreateTarget rhoSlot = 1 := by
  change (concreteJoinEntry.state.get concreteCreateTarget).stor.get rhoSlot = 1
  rw [concreteJoinEntry_storage]
  exact concreteDeployedRho

theorem concreteJoinDevm_pie (k : B256) (hc : k ≠ chiSlot) (hr : k ≠ rhoSlot) :
    concreteJoinDevm.getStorVal concreteCreateTarget k = 0 := by
  change (concreteJoinEntry.state.get concreteCreateTarget).stor.get k = 0
  rw [concreteJoinEntry_storage]
  exact concreteDeploymentRoot.pie k hc hr

theorem concreteJoinDevm_cold (k : B256) :
    (concreteCreateTarget, k) ∉ concreteJoinDevm.accessedStorageKeys := by
  change (concreteCreateTarget, k) ∉ (∅ : Std.HashSet (Adr × B256))
  simp

theorem concreteJoin_factor_one : B256.rpow scale half rate 1 = rate := by
  rw [drip_word_rpow_unfold_nonzero (by decide : (1 : Nat) ≠ 0)]
  decide +kernel

/-- The exponent-one initialization leaves exponent zero at the loop entry. -/
private theorem concreteJoin_rpowZero (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hread : Bytes.toB256 (M.read 0 32).1 = 0)
    (hmem : (M.read 0 32).2 = M)
    (hcompose : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G, base.stateGas⟩) composeFresh post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G + 34, base.stateGas⟩) rpowLoop post := by
  func_run (1)
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mload_of (v := 0) (M := M) (c := 3) (G := G + 29)
      (s := []) rfl ?_ hread hmem ?_ (by decide)) ?_
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  simp only [Devm.setMach_setMach]
  func_run (2) [1]
  apply Func.runCompiled_call' (f := composeFresh) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
      Devm.stateGas_setMach] using hcompose

private theorem concreteJoin_readChi (base post : Devm) (M : Mem) (G : Nat) (next : Func)
    (hchi : base.getStorVal concreteCreateTarget chiSlot = scale)
    (hcold : (concreteCreateTarget, chiSlot) ∉ base.accessedStorageKeys)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      ((addAccessedStorageKey base concreteCreateTarget chiSlot).setMach
        ⟨[scale], M, G, base.stateGas⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G + 2103, base.stateGas⟩)
      (Ninst.pushB256 chiSlot ::: Ninst.sload ::: next) post := by
  func_run (2)
  · exact concreteJoin_stateGas_none
  change Func.RunCompiled _ concreteJoinSevm
    ((addAccessedStorageKey base concreteCreateTarget chiSlot).setMach
      ⟨[base.getStorVal concreteCreateTarget chiSlot], M, G + 2103 - 2103, base.stateGas⟩) next post
  simpa only [hchi, Nat.add_sub_cancel] using htail

def concreteJoinClockMemory : Mem :=
  (concreteJoinStagingMemory.write 160 scale.toBytes).write 192 (2 : B256).toBytes

private theorem concreteJoin_stageClock (base post : Devm) (M C : Mem)
    (G : Nat) (next : Func)
    (hsize : M.size = 160)
    (hstore : M.write (storedChiWord * 32).toNat scale.toBytes = C)
    (hcsize : C.size = 192)
    (hread : Bytes.toB256 (C.read (storedChiWord * 32).toNat 32).1 = scale)
    (hmem : (C.read (storedChiWord * 32).toNat 32).2 = C)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], C.write 192 (2 : B256).toBytes, G, base.stateGas⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[scale], M, G + 70, base.stateGas⟩)
      (mstoreAt storedChiWord +++
        (Ninst.pushB256 scale ::: loadWord storedChiWord +++ Ninst.lt :::
          (.revert <?>
            (loadWord storedChiWord +++ Ninst.pushB256 maxChi ::: Ninst.lt :::
              (.revert <?> (Ninst.timestamp ::: mstoreAt nowWord +++ next)))))) post := by
  func_run (2) [3]
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
  change Func.RunCompiled _ concreteJoinSevm
    (base.setMach ⟨[], C.write 192 (2 : B256).toBytes, G + 70 - 70, base.stateGas⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteJoin_stageElapsed (base post : Devm) (M E : Mem)
    (G : Nat) (next : Func)
    (hrho : base.getStorVal concreteCreateTarget rhoSlot = 1)
    (hcold : (concreteCreateTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hsize : M.size = 224)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 2)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hstore : M.write (exponentWord * 32).toNat (1 : B256).toBytes = E)
    (hesize : E.size = 224)
    (hexp : Bytes.toB256 (E.read (exponentWord * 32).toNat 32).1 = 1)
    (hemem : (E.read (exponentWord * 32).toNat 32).2 = E)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      ((addAccessedStorageKey base concreteCreateTarget rhoSlot).setMach
        ⟨[], E, G, base.stateGas⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G + 2166, base.stateGas⟩)
      (Ninst.pushB256 rhoSlot ::: Ninst.sload ::: Ninst.dup 0 :::
        loadWord nowWord +++ Ninst.lt :::
          (.revert <?> (loadWord nowWord +++ Ninst.sub :::
            mstoreAt exponentWord +++ loadWord exponentWord +++
            Ninst.pushB256 maxElapsed ::: Ninst.lt ::: (.revert <?> next)))) post := by
  func_run (2)
  · exact concreteJoin_stateGas_none
  change Func.RunCompiled _ concreteJoinSevm
    ((addAccessedStorageKey base concreteCreateTarget rhoSlot).setMach
      ⟨[base.getStorVal concreteCreateTarget rhoSlot], M, G + 2166 - 2103, base.stateGas⟩) _ post
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
  func_run (3) [1, 0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hesize]
    decide +kernel
  rw [hexp, hemem]
  func_run (3) [0]
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteJoin_initializeRpow (base post : Devm) (M B A Z : Mem)
    (G : Nat) (zeroBase zeroExponent evenExponent : Func)
    (hsize : M.size = 224)
    (hbase : M.write (baseWord * 32).toNat rate.toBytes = B)
    (hbsize : B.size = 256)
    (hbexp : Bytes.toB256 (B.read (exponentWord * 32).toNat 32).1 = 1)
    (hbmem : (B.read (exponentWord * 32).toNat 32).2 = B)
    (hacc : B.write (accumulatorWord * 32).toNat rate.toBytes = A)
    (hasize : A.size = 288)
    (haexp : Bytes.toB256 (A.read (exponentWord * 32).toNat 32).1 = 1)
    (hamem : (A.read (exponentWord * 32).toNat 32).2 = A)
    (hzero : A.write (exponentWord * 32).toNat (0 : B256).toBytes = Z)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], Z, G, base.stateGas⟩) rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
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
  func_run (5) [0, 0]
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
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
      Devm.stateGas_setMach] using hloop

def concreteJoinExponentMemory : Mem := concreteJoinClockMemory.write 0 (1 : B256).toBytes
def concreteJoinBaseMemory : Mem := concreteJoinExponentMemory.write 224 rate.toBytes
def concreteJoinAccumulatorMemory : Mem := concreteJoinBaseMemory.write 256 rate.toBytes
def concreteJoinRpowMemory : Mem := concreteJoinAccumulatorMemory.write 0 (0 : B256).toBytes

def concreteJoinFreshBase (base : Devm) : Devm :=
  addAccessedStorageKey (addAccessedStorageKey base concreteCreateTarget chiSlot)
    concreteCreateTarget rhoSlot

private theorem concreteJoin_stagingSize : concreteJoinStagingMemory.size = 160 := by decide +kernel

private theorem concreteJoin_chiMemoryFacts :
    (concreteJoinStagingMemory.write 160 scale.toBytes).size = 192 ∧
    Bytes.toB256 ((concreteJoinStagingMemory.write 160 scale.toBytes).read 160 32).1 = scale ∧
    ((concreteJoinStagingMemory.write 160 scale.toBytes).read 160 32).2 =
      concreteJoinStagingMemory.write 160 scale.toBytes := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_clockMemoryFacts : concreteJoinClockMemory.size = 224 ∧
    Bytes.toB256 (concreteJoinClockMemory.read 192 32).1 = 2 ∧
    (concreteJoinClockMemory.read 192 32).2 = concreteJoinClockMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_exponentMemoryFacts : concreteJoinExponentMemory.size = 224 ∧
    Bytes.toB256 (concreteJoinExponentMemory.read 0 32).1 = 1 ∧
    (concreteJoinExponentMemory.read 0 32).2 = concreteJoinExponentMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_baseMemoryFacts : concreteJoinBaseMemory.size = 256 ∧
    Bytes.toB256 (concreteJoinBaseMemory.read 0 32).1 = 1 ∧
    (concreteJoinBaseMemory.read 0 32).2 = concreteJoinBaseMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_accumulatorMemoryFacts : concreteJoinAccumulatorMemory.size = 288 ∧
    Bytes.toB256 (concreteJoinAccumulatorMemory.read 0 32).1 = 1 ∧
    (concreteJoinAccumulatorMemory.read 0 32).2 = concreteJoinAccumulatorMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_rpowMemorySize : concreteJoinRpowMemory.size = 288 := by
  decide +kernel

private theorem concreteJoin_rpowMemoryRead : Bytes.toB256 (concreteJoinRpowMemory.read 0 32).1 = 0 := by
  decide +kernel

private theorem concreteJoin_rpowMemoryUnchanged :
    (concreteJoinRpowMemory.read 0 32).2 = concreteJoinRpowMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteJoin_rpowMemorySize]
  decide +kernel

theorem concreteJoin_freshStart (base post : Devm) (G : Nat)
    (hchi : base.getStorVal concreteCreateTarget chiSlot = scale)
    (hrho : base.getStorVal concreteCreateTarget rhoSlot = 1)
    (hcoldChi : (concreteCreateTarget, chiSlot) ∉ base.accessedStorageKeys)
    (hcoldRho : (concreteCreateTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hcompose : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      ((concreteJoinFreshBase base).setMach
        ⟨[], concreteJoinRpowMemory, G, (concreteJoinFreshBase base).stateGas⟩)
      composeFresh post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], concreteJoinStagingMemory, G + 34 + 122 + 2166 + 70 + 2103,
        base.stateGas⟩)
      freshStart post := by
  apply concreteJoin_readChi _ _ _ _ _ hchi hcoldChi
  apply concreteJoin_stageClock (C := concreteJoinStagingMemory.write 160 scale.toBytes)
  · exact concreteJoin_stagingSize
  · rfl
  · exact concreteJoin_chiMemoryFacts.1
  · exact concreteJoin_chiMemoryFacts.2.1
  · exact concreteJoin_chiMemoryFacts.2.2
  apply concreteJoin_stageElapsed (E := concreteJoinExponentMemory)
  · exact hrho
  · change (concreteCreateTarget, rhoSlot) ∉ base.accessedStorageKeys.insert
      (concreteCreateTarget, chiSlot)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by decide +kernel, hcoldRho⟩
  · exact concreteJoin_clockMemoryFacts.1
  · exact concreteJoin_clockMemoryFacts.2.1
  · exact concreteJoin_clockMemoryFacts.2.2
  · rfl
  · exact concreteJoin_exponentMemoryFacts.1
  · exact concreteJoin_exponentMemoryFacts.2.1
  · exact concreteJoin_exponentMemoryFacts.2.2
  apply concreteJoin_initializeRpow (B := concreteJoinBaseMemory)
    (A := concreteJoinAccumulatorMemory) (Z := concreteJoinRpowMemory)
  · exact concreteJoin_exponentMemoryFacts.1
  · rfl
  · exact concreteJoin_baseMemoryFacts.1
  · exact concreteJoin_baseMemoryFacts.2.1
  · exact concreteJoin_baseMemoryFacts.2.2
  · rfl
  · exact concreteJoin_accumulatorMemoryFacts.1
  · exact concreteJoin_accumulatorMemoryFacts.2.1
  · exact concreteJoin_accumulatorMemoryFacts.2.2
  · rfl
  exact concreteJoin_rpowZero _ _ _ _ concreteJoin_rpowMemorySize
    concreteJoin_rpowMemoryRead concreteJoin_rpowMemoryUnchanged hcompose

private theorem concreteJoin_composeFresh (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hchi : Bytes.toB256 (M.read (storedChiWord * 32).toNat 32).1 = scale)
    (hchiMem : (M.read (storedChiWord * 32).toNat 32).2 = M)
    (hfactor : Bytes.toB256 (M.read (accumulatorWord * 32).toNat 32).1 = rate)
    (hfactorMem : (M.read (accumulatorWord * 32).toNat 32).2 = M)
    (hroute : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate], M, G, base.stateGas⟩) freshRoute post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G + 104, base.stateGas⟩) composeFresh post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [scale * rate, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [scale, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (3) [1, 0]
  func_run (7) [rate, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  apply Func.runCompiled_call' (f := freshRoute) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach,
      Devm.stateGas_setMach] using hroute

private theorem concreteJoin_freshRoute (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hroute : Bytes.toB256 (M.read (routeWord * 32).toNat 32).1 = routeJoin)
    (hmem : (M.read (routeWord * 32).toNat 32).2 = M)
    (hjoin : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate], M, G, base.stateGas⟩) afterJoin post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate], M, G + 114, base.stateGas⟩) freshRoute post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hroute, hmem]
  func_run (19) [0, 0, 0, 0, 1]
  simpa only [Nat.add_sub_cancel] using hjoin

def concreteJoinCommit : Func :=
  commitFresh +++ Ninst.caller ::: Ninst.sstore ::: Ninst.swap 0 :::
    Ninst.pushB256 totalUnitsSlot ::: Ninst.sstore :::
    mstoreAt 0 +++ returnMemoryRange 0 32

private theorem concreteJoin_afterJoin (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (harg : Bytes.toB256 (M.read (argumentWord * 32).toNat 32).1 = 100)
    (hargMem : (M.read (argumentWord * 32).toNat 32).2 = M)
    (hrow : Bytes.toB256 (M.read (rowWord * 32).toNat 32).1 = 0)
    (hrowMem : (M.read (rowWord * 32).toNat 32).2 = M)
    (htotal : Bytes.toB256 (M.read (totalWord * 32).toNat 32).1 = 0)
    (htotalMem : (M.read (totalWord * 32).toNat 32).2 = M)
    (hcommit : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate, 99, 99, 99], M, G, base.stateGas⟩) concreteJoinCommit post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate], M, G + 96, base.stateGas⟩) afterJoin post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [harg, hargMem]
  func_run (8) [100 * scale, 99, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hrow, hrowMem]
  func_run (5) [99, 0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [htotal, htotalMem]
  func_run (7) [99, 0]
  simpa only [Nat.add_sub_cancel, concreteJoinCommit] using hcommit

private theorem concreteJoin_commitFresh (base C R post : Devm) (M : Mem) (G : Nat)
    (next : Func)
    (hsize : M.size = 288)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 2)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hchiCost : sstoreCost concreteJoinSevm base chiSlot rate = 2900)
    (hchi : afterSstore concreteJoinSevm base chiSlot rate = C)
    (hrhoCost : sstoreCost concreteJoinSevm C rhoSlot 2 = 2900)
    (hrho : afterSstore concreteJoinSevm C rhoSlot 2 = R)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (R.setMach ⟨[99, 99, 99], M, G, R.stateGas⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate, 99, 99, 99], M, G + 5812, base.stateGas⟩)
      (commitFresh +++ next) post := by
  have hfork : CoveredFork concreteJoinSevm.benvStat.fork := by
    exact CoveredFork.prague
  have hCStateGas : C.stateGas = base.stateGas := by
    rw [← hchi]
    unfold afterSstore
    split <;> rfl
  have hRStateGas : R.stateGas = C.stateGas := by
    rw [← hrho]
    unfold afterSstore
    split <;> rfl
  func_run (1)
  rw [show G + 5812 - 3 = (G + 2909) + 2900 by omega]
  refine Func.RunCompiled.next
    (devm' := C.setMach ⟨[99, 99, 99], M, G + 2909, base.stateGas⟩) ?_ ?_
  · simpa only [hchiCost, hchi] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := concreteJoinSevm)
        (base := base) (key := chiSlot) (value := rate)
        (stack := [99, 99, 99]) (memory := M) (G := G + 2909) hfork
        (by rw [hchiCost]; simp only [gCallStipend]; omega) rfl)
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (1)
  rw [← hCStateGas]
  rw [show G + 2909 - 9 = G + 2900 by omega]
  refine Func.RunCompiled.next (devm' := R.setMach ⟨[99, 99, 99], M, G, C.stateGas⟩) ?_ ?_
  · simpa only [hrhoCost, hrho] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := concreteJoinSevm)
        (base := C) (key := rhoSlot) (value := 2)
        (stack := [99, 99, 99]) (memory := M) (G := G) hfork
        (by rw [hrhoCost]; simp only [gCallStipend]; omega) rfl)
  simpa only [hRStateGas, Blanc.prepend] using htail

private def concreteJoinRpowImage : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt [] 64 (100 : B256).toBytes)
        96 (0 : B256).toBytes) 128 (0 : B256).toBytes) 32 (5 : B256).toBytes)
      160 scale.toBytes) 192 (2 : B256).toBytes) 0 (1 : B256).toBytes)
    224 rate.toBytes) 256 rate.toBytes) 0 (0 : B256).toBytes

private theorem concreteJoin_rpowReads : Mem.Reads concreteJoinRpowMemory concreteJoinRpowImage := by
  unfold concreteJoinRpowMemory concreteJoinAccumulatorMemory concreteJoinBaseMemory
    concreteJoinExponentMemory concreteJoinClockMemory concreteJoinStagingMemory concreteJoinRpowImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteJoin_originalStorage (key : B256) :
    getOrigStorVal concreteJoinSevm concreteCreateTarget key =
      (concreteDeployed.state.getStor concreteCreateTarget).get key := by
  rfl


private theorem concreteJoin_rpowRead_chi :
    Bytes.toB256 (concreteJoinRpowMemory.read 160 32).1 = scale := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 192 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_factor :
    Bytes.toB256 (concreteJoinRpowMemory.read 256 32).1 = rate := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_route :
    Bytes.toB256 (concreteJoinRpowMemory.read 32 32).1 = routeJoin := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 160 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_argument :
    Bytes.toB256 (concreteJoinRpowMemory.read 64 32).1 = 100 := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 32 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 128 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 96 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_row :
    Bytes.toB256 (concreteJoinRpowMemory.read 96 32).1 = 0 := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 32 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 128 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_total :
    Bytes.toB256 (concreteJoinRpowMemory.read 128 32).1 = 0 := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 32 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_now :
    Bytes.toB256 (concreteJoinRpowMemory.read 192 32).1 = 2 := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

noncomputable def concreteJoinStorageBase : Devm :=
  concreteJoinFreshBase (concreteJoinStagingBase concreteJoinDevm)

private theorem concreteJoinStorageBase_storage (a : Adr) (k : B256) :
    concreteJoinStorageBase.getStorVal a k = concreteJoinDevm.getStorVal a k := rfl

private theorem concreteJoinStorageBase_warm (k : B256)
    (hk : k = chiSlot ∨ k = rhoSlot ∨ k = concreteCreateSender.toB256 ∨ k = totalUnitsSlot) :
    (concreteCreateTarget, k) ∈ concreteJoinStorageBase.accessedStorageKeys := by
  change (concreteCreateTarget, k) ∈
    (((concreteJoinDevm.accessedStorageKeys.insert
      (concreteCreateTarget, concreteCreateSender.toB256)).insert
      (concreteCreateTarget, totalUnitsSlot)).insert
      (concreteCreateTarget, chiSlot)).insert (concreteCreateTarget, rhoSlot)
  rcases hk with h | h | h | h <;> subst k <;> simp

noncomputable def concreteJoinChiBase : Devm :=
  (concreteJoinStorageBase.withRefundCounter 0).setStorVal concreteCreateTarget chiSlot rate

private theorem concreteJoin_chiStore :
    sstoreCost concreteJoinSevm concreteJoinStorageBase chiSlot rate = 2900 ∧
    afterSstore concreteJoinSevm concreteJoinStorageBase chiSlot rate = concreteJoinChiBase := by
  have ht : concreteJoinSevm.currentTarget = concreteCreateTarget := rfl
  have hw := concreteJoinStorageBase_warm chiSlot (Or.inl rfl)
  have hr : concreteJoinStorageBase.refundCounter = 0 := rfl
  have hc : sstoreValueCost scale scale rate = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteJoinSevm.benvStat.rules.gas rate scale scale 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteJoin_originalStorage,
      concreteDeploymentRoot.chi, concreteJoinStorageBase_storage, concreteJoinDevm_chi, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteJoin_originalStorage,
      concreteDeploymentRoot.chi, concreteJoinStorageBase_storage, concreteJoinDevm_chi, hr, hf]
    rfl

private theorem concreteJoinChiBase_storage (k : B256) (h : chiSlot ≠ k) :
    concreteJoinChiBase.getStorVal concreteCreateTarget k =
      concreteJoinStorageBase.getStorVal concreteCreateTarget k := by
  change (Devm.getStor ((concreteJoinStorageBase.withRefundCounter 0).setStorVal
    concreteCreateTarget chiSlot rate) concreteCreateTarget).get k = _
  rw [setStorVal_getStor_self, Stor.get_set_ne _ h, Devm.withRefundCounter_getStor]
  rfl

noncomputable def concreteJoinRhoBase : Devm :=
  (concreteJoinChiBase.withRefundCounter 0).setStorVal concreteCreateTarget rhoSlot 2

private theorem concreteJoin_rhoStore :
    sstoreCost concreteJoinSevm concreteJoinChiBase rhoSlot 2 = 2900 ∧
    afterSstore concreteJoinSevm concreteJoinChiBase rhoSlot 2 = concreteJoinRhoBase := by
  have ht : concreteJoinSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, rhoSlot) ∈ concreteJoinChiBase.accessedStorageKeys := by
    rw [concreteJoinChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteJoinStorageBase_warm rhoSlot (Or.inr (Or.inl rfl))
  have hr : concreteJoinChiBase.refundCounter = 0 := rfl
  have hv : concreteJoinChiBase.getStorVal concreteCreateTarget rhoSlot = 1 := by
    rw [concreteJoinChiBase_storage _ (by decide +kernel), concreteJoinStorageBase_storage]
    exact concreteJoinDevm_rho
  have hc : sstoreValueCost 1 1 2 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteJoinSevm.benvStat.rules.gas 2 1 1 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteJoin_originalStorage,
      concreteDeployedRho, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteJoin_originalStorage,
      concreteDeployedRho, hv, hr, hf]
    rfl

private theorem concreteJoinRhoBase_storage (k : B256) (hc : chiSlot ≠ k) (hr : rhoSlot ≠ k) :
    concreteJoinRhoBase.getStorVal concreteCreateTarget k = 0 := by
  change (Devm.getStor ((concreteJoinChiBase.withRefundCounter 0).setStorVal
    concreteCreateTarget rhoSlot 2) concreteCreateTarget).get k = _
  rw [setStorVal_getStor_self, Stor.get_set_ne _ hr, Devm.withRefundCounter_getStor]
  change concreteJoinChiBase.getStorVal concreteCreateTarget k = 0
  rw [concreteJoinChiBase_storage _ hc, concreteJoinStorageBase_storage]
  exact concreteJoinDevm_pie _ (Ne.symm hc) (Ne.symm hr)

noncomputable def concreteJoinRowBase : Devm :=
  (concreteJoinRhoBase.withRefundCounter 0).setStorVal
    concreteCreateTarget concreteCreateSender.toB256 99

private theorem concreteJoin_rowStore :
    sstoreCost concreteJoinSevm concreteJoinRhoBase concreteCreateSender.toB256 99 = 20000 ∧
    afterSstore concreteJoinSevm concreteJoinRhoBase concreteCreateSender.toB256 99 =
      concreteJoinRowBase := by
  have ht : concreteJoinSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, concreteCreateSender.toB256) ∈
      concreteJoinRhoBase.accessedStorageKeys := by
    rw [concreteJoinRhoBase, Devm.sstoreWarmBase_accessedStorageKeys,
      concreteJoinChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteJoinStorageBase_warm _ (Or.inr (Or.inr (Or.inl rfl)))
  have hr : concreteJoinRhoBase.refundCounter = 0 := rfl
  have ho : (concreteDeployed.state.getStor concreteCreateTarget).get
      concreteCreateSender.toB256 = 0 :=
    concreteDeploymentRoot.pie _ (by decide +kernel) (by decide +kernel)
  have hv := concreteJoinRhoBase_storage concreteCreateSender.toB256
    (by decide +kernel) (by decide +kernel)
  have hc : sstoreValueCost 0 0 99 = 20000 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteJoinSevm.benvStat.rules.gas 99 0 0 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteJoin_originalStorage, ho, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteJoin_originalStorage, ho, hv, hr, hf]
    rfl

noncomputable def concreteJoinTotalBase : Devm :=
  (concreteJoinRowBase.withRefundCounter 0).setStorVal concreteCreateTarget totalUnitsSlot 99

private theorem concreteJoin_totalStore :
    sstoreCost concreteJoinSevm concreteJoinRowBase totalUnitsSlot 99 = 20000 ∧
    afterSstore concreteJoinSevm concreteJoinRowBase totalUnitsSlot 99 = concreteJoinTotalBase := by
  have ht : concreteJoinSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, totalUnitsSlot) ∈ concreteJoinRowBase.accessedStorageKeys := by
    rw [concreteJoinRowBase, Devm.sstoreWarmBase_accessedStorageKeys,
      concreteJoinRhoBase, Devm.sstoreWarmBase_accessedStorageKeys,
      concreteJoinChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteJoinStorageBase_warm _ (Or.inr (Or.inr (Or.inr rfl)))
  have hr : concreteJoinRowBase.refundCounter = 0 := rfl
  have ho : (concreteDeployed.state.getStor concreteCreateTarget).get totalUnitsSlot = 0 :=
    concreteDeploymentRoot.pie _ (by decide +kernel) (by decide +kernel)
  have hv : concreteJoinRowBase.getStorVal concreteCreateTarget totalUnitsSlot = 0 := by
    change (Devm.getStor ((concreteJoinRhoBase.withRefundCounter 0).setStorVal
      concreteCreateTarget concreteCreateSender.toB256 99) concreteCreateTarget).get totalUnitsSlot = _
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel :
      concreteCreateSender.toB256 ≠ totalUnitsSlot), Devm.withRefundCounter_getStor]
    exact concreteJoinRhoBase_storage _ (by decide +kernel) (by decide +kernel)
  have hc : sstoreValueCost 0 0 99 = 20000 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteJoinSevm.benvStat.rules.gas 99 0 0 0 = 0 := by
    decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteJoin_originalStorage, ho, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteJoin_originalStorage, ho, hv, hr, hf]
    rfl

private theorem concreteJoin_commitUnits (base P T : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hrowCost : sstoreCost concreteJoinSevm base concreteCreateSender.toB256 99 = 20000)
    (hrow : afterSstore concreteJoinSevm base concreteCreateSender.toB256 99 = P)
    (htotalCost : sstoreCost concreteJoinSevm P totalUnitsSlot 99 = 20000)
    (htotal : afterSstore concreteJoinSevm P totalUnitsSlot 99 = T) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[99, 99, 99], M, G + 40018, base.stateGas⟩)
      (Ninst.caller ::: Ninst.sstore ::: Ninst.swap 0 :::
        Ninst.pushB256 totalUnitsSlot ::: Ninst.sstore :::
        mstoreAt 0 +++ returnMemoryRange 0 32)
      ((T.setMach ⟨[], M.write 0 (99 : B256).toBytes, G, P.stateGas⟩).withOutput
        (99 : B256).toBytes) := by
  have hcaller : concreteJoinSevm.caller = concreteCreateSender := rfl
  have hfork : CoveredFork concreteJoinSevm.benvStat.fork := by
    exact CoveredFork.prague
  have hPStateGas : P.stateGas = base.stateGas := by
    rw [← hrow]
    unfold afterSstore
    split <;> rfl
  func_run (1)
  rw [hcaller]
  rw [show G + 40018 - 2 = (G + 20016) + 20000 by omega]
  refine Func.RunCompiled.next
    (devm' := P.setMach ⟨[99, 99], M, G + 20016, base.stateGas⟩) ?_ ?_
  · simpa only [hrowCost, hrow] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := concreteJoinSevm)
        (base := base) (key := concreteCreateSender.toB256) (value := 99)
        (stack := [99, 99]) (memory := M) (G := G + 20016) hfork
        (by rw [hrowCost]; simp only [gCallStipend]; omega) rfl)
  func_run (2)
  rw [← hPStateGas]
  rw [show G + 20016 - 6 = (G + 10) + 20000 by omega]
  refine Func.RunCompiled.next (devm' := T.setMach ⟨[99], M, G + 10, P.stateGas⟩) ?_ ?_
  · simpa only [htotalCost, htotal] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := concreteJoinSevm)
        (base := P) (key := totalUnitsSlot) (value := 99)
        (stack := [99]) (memory := M) (G := G + 10) hfork
        (by rw [htotalCost]; simp only [gCallStipend]; omega) rfl)
  func_run (4) [0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  have hnsize : (M.write 0 (99 : B256).toBytes).size = 288 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsize]; decide)]
    exact hsize
  have hnread : ((M.write 0 (99 : B256).toBytes).read 0 32).1 = (99 : B256).toBytes := by
    simpa only [B256.length_toBytes] using
      (Mem.read_write_zero M (ys := (99 : B256).toBytes) (by decide +kernel))
  have hnmem : ((M.write 0 (99 : B256).toBytes).read 0 32).2 = M.write 0 (99 : B256).toBytes := by
    apply Mem.read_snd_eq_self
    rw [hnsize]
    decide +kernel
  apply Func.runCompiled_return_of (G := G) (e := 0)
  · rfl
  · change calculateMemoryGasCost (memExtsSize (M.write 0 (99 : B256).toBytes).size [(0, 32)]) -
      calculateMemoryGasCost (M.write 0 (99 : B256).toBytes).size = 0
    rw [hnsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  · change (((M.write 0 (99 : B256).toBytes).read 0 32).1,
      T.setMach ⟨[], ((M.write 0 (99 : B256).toBytes).read 0 32).2, G, P.stateGas⟩) = _
    rw [hnread, hnmem]

private theorem concreteJoin_rpowMemoryUnchangedAt (i : Nat) (h : i + 32 ≤ 288) :
    (concreteJoinRpowMemory.read i 32).2 = concreteJoinRpowMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteJoin_rpowMemorySize]
  exact memExtSize_of_le (by decide) h

noncomputable def concreteJoinRuntimePost (G : Nat) : Devm :=
  (concreteJoinTotalBase.setMach
    ⟨[], concreteJoinRpowMemory.write 0 (99 : B256).toBytes, G,
      concreteJoinTotalBase.stateGas⟩).withOutput (99 : B256).toBytes

theorem concreteJoin_composedRun (G : Nat) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (concreteJoinStorageBase.setMach ⟨[], concreteJoinRpowMemory,
        G + 45830 + 96 + 114 + 104, concreteJoinStorageBase.stateGas⟩)
      composeFresh (concreteJoinRuntimePost G) := by
  apply concreteJoin_composeFresh
  · exact concreteJoin_rpowMemorySize
  · exact concreteJoin_rpowRead_chi
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  · exact concreteJoin_rpowRead_factor
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  apply concreteJoin_freshRoute
  · exact concreteJoin_rpowMemorySize
  · exact concreteJoin_rpowRead_route
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  apply concreteJoin_afterJoin
  · exact concreteJoin_rpowMemorySize
  · exact concreteJoin_rpowRead_argument
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  · exact concreteJoin_rpowRead_row
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  · exact concreteJoin_rpowRead_total
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  unfold concreteJoinCommit
  rw [show G + 45830 = (G + 40018) + 5812 by omega]
  apply concreteJoin_commitFresh (C := concreteJoinChiBase) (R := concreteJoinRhoBase)
  · exact concreteJoin_rpowMemorySize
  · exact concreteJoin_rpowRead_now
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  · exact concreteJoin_chiStore.1
  · exact concreteJoin_chiStore.2
  · exact concreteJoin_rhoStore.1
  · exact concreteJoin_rhoStore.2
  have hTotalStateGas : concreteJoinTotalBase.stateGas = concreteJoinRowBase.stateGas := by
    have hkeep : ∀ (a : Devm) (r : Nat) (t : Adr) (k v : B256),
        ((a.withRefundCounter r).setStorVal t k v).stateGas = a.stateGas :=
      fun _ _ _ _ _ => rfl
    exact hkeep _ _ _ _ _
  unfold concreteJoinRuntimePost
  rw [hTotalStateGas]
  exact concreteJoin_commitUnits _ concreteJoinRowBase concreteJoinTotalBase _ G
    concreteJoin_rpowMemorySize concreteJoin_rowStore.1 concreteJoin_rowStore.2
    concreteJoin_totalStore.1 concreteJoin_totalStore.2

theorem concreteJoin_runtime (G : Nat) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (concreteJoinDevm.setMach ⟨[], Mem.empty, G + 55079, concreteJoinDevm.stateGas⟩)
      main (concreteJoinRuntimePost G) := by
  rw [show G + 55079 = G + 45830 + 96 + 114 + 104 + 34 + 122 + 2166 + 70 + 2103 + 4327 + 113 by omega]
  apply concreteJoin_dispatch
    (G := G + 45830 + 96 + 114 + 104 + 34 + 122 + 2166 + 70 + 2103 + 4327)
  · rfl
  apply concreteJoin_stage
    (G := G + 45830 + 96 + 114 + 104 + 34 + 122 + 2166 + 70 + 2103)
  · exact concreteJoinDevm_pie _ (by decide +kernel) (by decide +kernel)
  · exact concreteJoinDevm_pie _ (by decide +kernel) (by decide +kernel)
  · exact concreteJoinDevm_cold _
  · exact concreteJoinDevm_cold _
  apply concreteJoin_freshStart (G := G + 45830 + 96 + 114 + 104)
  · exact concreteJoinDevm_chi
  · exact concreteJoinDevm_rho
  · change (concreteCreateTarget, chiSlot) ∉
      (concreteJoinDevm.accessedStorageKeys.insert
        (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)
    simp only [Std.HashSet.mem_insert, concreteJoinDevm_cold, or_false, not_or]
    exact ⟨by decide +kernel, by decide +kernel⟩
  · change (concreteCreateTarget, rhoSlot) ∉
      (concreteJoinDevm.accessedStorageKeys.insert
        (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)
    simp only [Std.HashSet.mem_insert, concreteJoinDevm_cold, or_false, not_or]
    exact ⟨by decide +kernel, by decide +kernel⟩
  exact concreteJoin_composedRun G

theorem concreteJoinDevm_gas : concreteJoinDevm.gasLeft = 478936 := by
  change 500000 - deploymentIntrinsicGas concreteJoinTxInput concreteJoinTx concreteCreateSender = 478936
  decide +kernel

theorem concreteJoin_program :
    Prog.RunCompiled concreteJoinSevm concreteJoinDevm runtime (concreteJoinRuntimePost 423856) := by
  apply Prog.runCompiled_intro (G := 423856 + 55079)
    (mid := concreteJoinDevm.setMach ⟨[], Mem.empty, 423856 + 55079,
      concreteJoinDevm.stateGas⟩)
  · rw [concreteJoinDevm_gas]
    decide
  · rfl
  exact concreteJoin_runtime 423856

theorem concreteJoin_compiled : some concreteJoinSevm.code.toList = Prog.compile runtime := by
  change some concreteJoinMessage.code.toList = _
  rw [concreteJoinMessage_code, code_compile]

theorem concreteJoin_exec :
    exec (initEvm (concreteJoinMessage.withBenv concreteJoinEntry)) =
      .ok (concreteJoinRuntimePost 423856) :=
  Prog.exec_of_runCompiled concreteJoin_program concreteJoin_compiled

theorem concreteJoin_frameEntry :
    (Frame.ofCall concreteJoinMessage).enter =
      .run (initEvm (concreteJoinMessage.withBenv concreteJoinEntry)) := by
  have hnp : ¬ pragueRules.isPrecomp concreteCreateTarget :=
    concreteDeploymentBase.target_not_precompile (ChainConfig.pragueOnly_rulesAt 1 2)
  have he : executeCode.enter (concreteJoinMessage.withBenv concreteJoinEntry) =
      .inl (initEvm (concreteJoinMessage.withBenv concreteJoinEntry)) := by
    unfold executeCode.enter
    change (if !false && pragueRules.isPrecomp concreteCreateTarget then _ else _) = _
    simp only [Bool.not_false, Bool.true_and, hnp]
    rfl
  unfold Frame.enter Frame.ofCall
  rw [concreteJoinEntry_run]
  dsimp only
  rw [he]

private theorem concreteJoin_postError : (concreteJoinRuntimePost 423856).error = none := rfl

theorem concreteJoin_processMessage :
    processMessage concreteJoinMessage = .ok (concreteJoinRuntimePost 423856) := by
  unfold processMessage runFrame
  rw [concreteJoin_frameEntry]
  simp [Frame.settle_eq_settleMsg_handleErrorWith, Frame.settleMsg, concreteJoin_exec,
    executeCode.handleErrorWith_ok, Frame.ofCall, processMessage.settle, concreteJoin_postError]

noncomputable def concreteJoinMessageState : State := (concreteJoinRuntimePost 423856).state

def concreteJoinMessageOutput : MsgCallOutput := {
  gasLeft := 423856
  refundCounter := 0
  logs := []
  accountsToDelete := .emptyWithCapacity
  error := none
  returnData := (99 : B256).toBytes }

theorem concreteJoin_messageCall :
    processMessageCall concreteJoinMessage = .ok (concreteJoinMessageState, concreteJoinMessageOutput) := by
  have htarget : concreteJoinMessage.target.isNone = false := rfl
  have hauths : concreteJoinMessage.tenv.stat.auths = [] := rfl
  have hcode : some concreteJoinMessage.code.toList = Prog.compile runtime := concreteJoin_compiled
  have hdelegation : getDelegatedCodeAddress concreteJoinMessage.code = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg (not_delegation_of_compile hcode)]
  have hrefund : (concreteJoinRuntimePost 423856).refundCounter = 0 := rfl
  unfold processMessageCall
  rw [htarget]
  unfold processMessageCall.call
  simp only [hauths, List.isEmpty, if_true, bind, Except.bind, hdelegation,
    concreteJoin_processMessage, Except.bimap, id_eq, concreteJoin_postError,
    Option.isNone, hrefund]
  rfl

noncomputable def concreteJoinTransactionState : State :=
  deploymentFinalState concreteJoinTxInput concreteJoinTx concreteCreateSender
    concreteJoinMessageState 76144

def concreteJoinTransactionBout : BlockOutput :=
  deploymentFinalBout .init concreteJoinTx 0 concreteJoinMessageOutput 76144

theorem concreteJoin_transaction :
    processTransaction concreteJoinTxInput .init concreteJoinTx 0 =
      .ok (concreteJoinTransactionState, concreteJoinTransactionBout) := by
  have hchecked := concreteJoinChecked
  change checkTransaction concreteJoinTxInput.beginTransaction
    (deploymentTxPreludeBout .init concreteJoinTx 0) concreteJoinTx =
      .ok (concreteCreateSender, 2, [], 0) at hchecked
  have hdebit := concreteJoinDebit_run
  simp only [Benv.beginTransaction] at hdebit
  have hprepareRun :
      Except.bind
        (prepareMessage
          { concreteJoinTxInput.beginTransaction with state := concreteJoinDebit }
          concreteJoinTenv concreteJoinTx)
        (fun msg => Except.mapError TransitionError.vm (processMessageCall msg)) =
        .ok (concreteJoinMessageState, concreteJoinMessageOutput) := by
    rw [concreteJoinMessage_prepared]
    simp only [Except.bind, concreteJoin_messageCall, Except.mapError]
  have hvalidationStateGas :
      concreteJoinTxInput.beginTransaction.stat.rules.stateGas = none := by
    change concreteJoinTxInput.stat.rules.stateGas = none
    exact CoveredFork.prague.rules_stateGas_none
  have hforkStateGas : pragueRules.stateGas = none := pragueRules_stateGas
  have hrules : concreteJoinTxInput.beginTransaction.stat.rules = pragueRules := rfl
  have htypeThree : concreteJoinTx.isTypeThree = false := rfl
  have haccessList : concreteJoinTx.accessList = [] := rfl
  have hauths : concreteJoinTx.auths = [] := rfl
  unfold processTransaction
  simp only [bind, Except.bind]
  change (do
    let validationSender ←
      ((match concreteJoinTxInput.beginTransaction.stat.rules.stateGas with
        | none => Except.ok 0
        | some _ => do
          Except.mapError TransitionError.transaction
            (checkTransactionChainId concreteJoinTxInput.beginTransaction concreteJoinTx)
          Except.mapError (fun e => TransitionError.senderRecovery e)
            (recoverSender concreteJoinTxInput.beginTransaction.stat.chainId concreteJoinTx)) :
        Except TransitionError Adr)
    (fun _ => _) validationSender) =
      .ok (concreteJoinTransactionState, concreteJoinTransactionBout) <;>
  rw [hvalidationStateGas]
  simp only [bind, Except.bind]
  rw [hrules]
  simp only [Except.mapError]
  simp only [deploymentTxPreludeBout, ExecutionTrace.transactionPreludeBout] at hchecked
  rw [hchecked]
  simp only [htypeThree, haccessList, hauths, Bool.false_eq_true, if_false,
    Nat.add_zero, Benv.beginTransaction]
  have htxGas : concreteJoinTx.gas = 500000 := rfl
  rw [htxGas, show Nat.toB256 (500000 * 2) = 1000000 by decide +kernel, hdebit]
  simp only [Option.toExcept]
  change (Except.bind
    (Except.bind
      (prepareMessage
        {concreteJoinTxInput.beginTransaction with state := concreteJoinDebit}
        concreteJoinTenv concreteJoinTx)
      (fun msg => Except.mapError TransitionError.vm (processMessageCall msg)))
    (fun v => _)) = _
  rw [hprepareRun]
  simp only [Except.bind]
  have hprice : min 1 (8 - concreteJoinTxInput.stat.baseFeePerGas) +
      concreteJoinTxInput.stat.baseFeePerGas = 2 := by rfl
  have hgas : max (500000 - 423856 - min ((500000 - 423856) / 5) 0)
      (calculateIntrinsicCost pragueRules concreteJoinTx concreteCreateSender).2 = 76144 := by decide +kernel
  unfold concreteJoinMessageOutput
  rw [show Int.toNat? 0 = some 0 by rfl]
  simp only [hgas]
  unfold concreteJoinTransactionState concreteJoinTransactionBout deploymentFinalState deploymentFinalBout
  simp only [deploymentEffectiveGasPrice, concreteJoinTx, concreteJoinMessageOutput, hprice]
  have hdelete : (Std.HashSet.emptyWithCapacity : AdrSet).toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    rfl
  rw [hdelete]
  rfl

theorem concreteJoinTransactionCode (a : Adr) :
    concreteJoinTransactionState.getCode a = concreteDeployed.state.getCode a := by
  unfold concreteJoinTransactionState deploymentFinalState
  rw [State.addBal_getCode, State.addBal_getCode]
  unfold concreteJoinMessageState concreteJoinRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  change concreteJoinTotalBase.getCode a = _
  unfold concreteJoinTotalBase
  rw [Devm.setStorVal_getCode]
  change concreteJoinRowBase.getCode a = _
  unfold concreteJoinRowBase
  rw [Devm.setStorVal_getCode]
  change concreteJoinRhoBase.getCode a = _
  unfold concreteJoinRhoBase
  rw [Devm.setStorVal_getCode]
  change concreteJoinChiBase.getCode a = _
  unfold concreteJoinChiBase
  rw [Devm.setStorVal_getCode]
  change concreteJoinEntry.state.getCode a = _
  change ((concreteJoinDebit.setBal _ _).addBal _ _).getCode a = _
  rw [State.addBal_getCode, State.setBal_getCode]
  unfold concreteJoinDebit
  rw [State.setBal_getCode]
  change ((concreteDeployed.state.incrNonce concreteCreateSender).get a).code = _
  rw [State.incrNonce_get_code]
  rfl

theorem concreteJoin_receiptEntry :
    concreteJoinTransactionBout.receiptsTrie[deploymentReceiptKey 0]? =
      some (makeReceipt concreteJoinTx none 76144 []) := by
  change (BlockOutput.init.receiptsTrie.insert (deploymentReceiptKey 0)
    (makeReceipt concreteJoinTx none 76144 []))[deploymentReceiptKey 0]? = _
  rw [Std.TreeMap.getElem?_insert_self]

theorem concreteJoin_requestSuffix :
    processGeneralPurposeRequests (concreteJoinTxInput.withState concreteJoinTransactionState)
      concreteJoinTransactionBout = .ok (concreteJoinTransactionState, concreteJoinTransactionBout) := by
  have hcode (a : Adr) (ha : a ∈ [beaconRootsAddress, historyStorageAddress,
      withdrawalRequestPredeployAddress, consolidationRequestPredeployAddress]) :
      some (concreteJoinTransactionState.getCode a).toList = Prog.compile deploymentSystemProgram := by
    rw [concreteJoinTransactionCode]
    exact concreteDeployedSystemCode a ha
  obtain ⟨withdrawalOut, hw, _, _, _, _, hwr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (concreteJoinTxInput.withState concreteJoinTransactionState) withdrawalRequestPredeployAddress []
      (hcode _ (by simp)) (by change ¬ pragueRules.isPrecomp withdrawalRequestPredeployAddress; decide)
      CoveredFork.prague
  obtain ⟨consolidationOut, hc, _, _, _, _, hcr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((concreteJoinTxInput.withState concreteJoinTransactionState).withState concreteJoinTransactionState)
      consolidationRequestPredeployAddress [] (hcode _ (by simp))
      (by change ¬ pragueRules.isPrecomp consolidationRequestPredeployAddress; decide) CoveredFork.prague
  have hrequests :
      (concreteJoinTxInput.withState concreteJoinTransactionState).stat.rules.requests =
        [(1, withdrawalRequestPredeployAddress),
         (2, consolidationRequestPredeployAddress)] := by
    change pragueRules.requests = _
    exact pragueRules_requests
  have hw' : processCheckedSystemTransaction
      (concreteJoinTxInput.withState concreteJoinTransactionState)
      withdrawalRequestPredeployAddress [] =
      .ok (concreteJoinTransactionState, withdrawalOut) := by
    simpa [Benv.withState] using hw
  have hbalNone :
      (concreteJoinTxInput.withState concreteJoinTransactionState).stat.rules.bal = none := by
    change pragueRules.bal = none
    rfl
  have hbaseBalNone : concreteJoinTxInput.stat.rules.bal = none := by
    change pragueRules.bal = none
    rfl
  have hd : parseDepositRequests concreteJoinTransactionBout = .ok [] := by
    unfold parseDepositRequests
    have hk : concreteJoinTransactionBout.receiptKeys = [deploymentReceiptKey 0] := rfl
    rw [hk]
    simp
    rw [concreteJoin_receiptEntry]
    unfold makeReceipt
    rfl
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt
  rw [hd, hrequests]
  simp [runRequestContracts, hw', hc, hwr, hcr, hbalNone, hbaseBalNone]
  rfl

theorem concreteJoin_body :
    applyBody concreteJoinTxInput [.inl concreteJoinTxRlp] [] =
      .ok (concreteJoinTransactionState, concreteJoinTransactionBout) := by
  obtain ⟨beaconOut, hb, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    concreteJoinTxInput beaconRootsAddress concreteJoinTxInput.stat.parentBeaconBlockRoot.toBytes
    (concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp beaconRootsAddress; decide) CoveredFork.prague
  obtain ⟨historyOut, hh, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (concreteJoinTxInput.withState concreteDeployed.state) historyStorageAddress
    concreteDeploymentEnvelope.block.header.hash.toBytes
    (concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp historyStorageAddress; decide) CoveredFork.prague
  have hl : (concreteJoinTxInput.withState concreteDeployed.state).stat.blockHashes.getLast? =
      some concreteDeploymentEnvelope.block.header.hash := by rfl
  have hi : (concreteJoinTxInput.withState concreteDeployed.state).withState concreteDeployed.state =
      concreteJoinTxInput := rfl
  have hstate : concreteJoinTxInput.state = concreteDeployed.state := rfl
  have hh' : processUncheckedSystemTransaction
      (concreteJoinTxInput.withState concreteJoinTxInput.state) historyStorageAddress
      concreteDeploymentEnvelope.block.header.hash.toBytes =
      .ok ((concreteJoinTxInput.withState concreteJoinTxInput.state).state, historyOut) := by
    simpa only [hstate] using hh
  have hl' : (concreteJoinTxInput.withState concreteJoinTxInput.state).stat.blockHashes.getLast? =
      some concreteDeploymentEnvelope.block.header.hash := by
    simpa only [hstate] using hl
  have hi' : (concreteJoinTxInput.withState concreteJoinTxInput.state).withState
      concreteJoinTxInput.state = concreteJoinTxInput := by
    simpa only [hstate] using hi
  have hbalNone : concreteJoinTxInput.stat.rules.bal = none := by
    change pragueRules.bal = none
    rfl
  unfold applyBody
  simp only [BalBuilder.incorporateSystem, hbalNone, checkBlockAccessListGasLimit]
  rw [hb]
  simp only [Except.mapError, bind, Except.bind]
  rw [hl']
  simp only [Option.toExcept, hh', Except.mapError, bind, Except.bind]
  rw [show (concreteJoinTxInput.withState concreteJoinTxInput.state).state =
    concreteJoinTxInput.state from rfl, hi']
  have htransaction := concreteJoin_transaction
  unfold BlockOutput.init at htransaction
  simp only [BlockOutput.init, List.mapM_cons, List.mapM_nil, concreteJoinDecode, pure, Except.pure, bind, Except.bind, List.putIndex, List.putIndex.aux,
    applyTransactions, htransaction]
  have hwithdrawals : processWithdrawals
      (concreteJoinTxInput.withState concreteJoinTransactionState)
      concreteJoinTransactionBout [] =
      (concreteJoinTransactionState, concreteJoinTransactionBout) := by
    unfold processWithdrawals processWithdrawalsState processWithdrawalsTrie
      BlockOutput.withWithdrawalsTrie
    rfl
  rw [hwithdrawals]
  simp only [Prod.fst, Prod.snd]
  rw [show (concreteJoinTxInput.withState concreteJoinTransactionState).withState
    concreteJoinTransactionState = concreteJoinTxInput.withState concreteJoinTransactionState from rfl]
  rw [concreteJoin_requestSuffix]
  rfl

noncomputable def concreteJoinHeader (sr tr rr wr rh : B256) : Header :=
  { concreteJoinExecutionHeader with
    gasUsed := 76144
    stateRoot := sr
    txsRoot := tr
    receiptRoot := rr
    withdrawalsRoot := wr
    requestsHash := some rh }

theorem concreteJoinHeader_benv (sr tr rr wr rh : B256) :
    initBenv .prague concreteDeployed (concreteJoinHeader sr tr rr wr rh) = concreteJoinTxInput := rfl

theorem concreteJoinHeader_valid (sr tr rr wr rh : B256) :
    validateHeader pragueRules concreteDeployed (concreteJoinHeader sr tr rr wr rh) = .ok () := by
  have hlast : concreteDeployed.blocks.getLast? = some concreteDeploymentEnvelope.block :=
    appendBlock_getLast? concreteBase.blocks concreteDeploymentEnvelope.block
  have hparent : concreteDeploymentEnvelope.block.header =
      concreteDeploymentHeader concreteDeploymentBody.1.root
        (getTransactionsRoot concreteDeploymentBody.2) (getReceiptRoot concreteDeploymentBody.2)
        (getWithdrawalsRoot concreteDeploymentBody.2)
        (computeRequestsHash concreteDeploymentBody.2.requests) := rfl
  have hparentGasLimit : concreteDeploymentEnvelope.block.header.gasLimit = 10000000 := by
    rw [hparent]
    rfl
  have hparentGasUsed : concreteDeploymentEnvelope.block.header.gasUsed = 479909 := by
    rw [hparent]
    rfl
  have hparentBaseFee : concreteDeploymentEnvelope.block.header.baseFeePerGas = 1 := by
    rw [hparent]
    rfl
  have hparentTimestamp : concreteDeploymentEnvelope.block.header.timestamp = 1 := by
    rw [hparent]
    rfl
  have hparentNumber : concreteDeploymentEnvelope.block.header.number = 1 := by
    rw [hparent]
    rfl
  have hparentBlobGas : concreteDeploymentEnvelope.block.header.blobGasUsed = 0 := by
    rw [hparent]
    rfl
  have hparentExcessBlobGas : concreteDeploymentEnvelope.block.header.excessBlobGas = 0 := by
    rw [hparent]
    rfl
  have hparentExtraData : concreteDeploymentEnvelope.block.header.extraData = [] := by
    rw [hparent]
    rfl
  have hparentDifficulty : concreteDeploymentEnvelope.block.header.difficulty = 0 := by
    rw [hparent]
    rfl
  have hparentNonce : concreteDeploymentEnvelope.block.header.nonce = 0 := by
    rw [hparent]
    rfl
  have hparentOmmers : concreteDeploymentEnvelope.block.header.ommersHash = emptyOmmerHash := by
    rw [hparent]
    rfl
  have hparentBal : concreteDeploymentEnvelope.block.header.blockAccessListHash = none := by
    rw [hparent]
    rfl
  have hparentSlot : concreteDeploymentEnvelope.block.header.slotNumber = none := by
    rw [hparent]
    rfl
  have hbase : calculateBaseFeePerGas 10000000 10000000 479909 1 = .ok 1 := by
    decide +kernel
  have hexcess : calculateExcessBlobGas pragueRules.blob concreteDeploymentEnvelope.block.header = 0 := by
    unfold calculateExcessBlobGas
    rw [hparentExcessBlobGas, hparentBlobGas]
    decide +kernel
  simp only [validateHeader, hlast, Option.toExcept, bind, Except.bind,
    concreteJoinHeader, concreteJoinExecutionHeader, Header.hash, hparentGasLimit,
    hparentGasUsed, hparentBaseFee, hparentTimestamp, hparentNumber, hparentBlobGas,
    hparentExcessBlobGas, hparentExtraData, hparentDifficulty, hparentNonce, hparentOmmers,
    hparentBal, hparentSlot, hbase, hexcess, ne_eq, not_true_eq_false, ite_false]
  simp only [Except.mapError]
  rfl

noncomputable def concreteJoinBlock : Block := {
  header := concreteJoinHeader concreteJoinTransactionState.root
    (getTransactionsRoot concreteJoinTransactionBout) (getReceiptRoot concreteJoinTransactionBout)
    (getWithdrawalsRoot concreteJoinTransactionBout) (computeRequestsHash concreteJoinTransactionBout.requests)
  txs := [.inl concreteJoinTxRlp]
  ommers := []
  wds := [] }

noncomputable def concreteJoined : BlockChain :=
  ⟨appendBlock concreteDeployed.blocks concreteJoinBlock, concreteJoinTransactionState, concreteDeployed.chainId⟩

theorem concreteJoin_checks :
    stateTransitionChecks concreteJoinTransactionBout concreteJoinBlock.header
      (getTransactionsRoot concreteJoinTransactionBout) concreteJoinTransactionState.root
      (getReceiptRoot concreteJoinTransactionBout) (logsBloom concreteJoinTransactionBout.blockLogs)
      (getWithdrawalsRoot concreteJoinTransactionBout)
      (computeRequestsHash concreteJoinTransactionBout.requests) = .ok () := by
  have hg : concreteJoinTransactionBout.blockGasUsed = 76144 := rfl
  have hl : concreteJoinTransactionBout.blockLogs = [] := rfl
  have hb : concreteJoinTransactionBout.blobGasUsed = 0 := rfl
  simp only [stateTransitionChecks, hg, hl, hb, concreteJoinBlock, concreteJoinHeader,
    concreteJoinExecutionHeader, concreteDeploymentEnvelope, concreteCanonicalBlock,
    CanonicalBlock.ofDecode, concreteDeploymentBlock, concreteDeploymentHeader,
    concreteExecutionHeader, concreteGenesisHeader, logsBloom, List.foldl_nil,
    ne_eq, not_true_eq_false, ite_false, pure, Bind.bind, Except.bind]
  rfl

theorem concreteJoin_step :
    stateTransitionUsing concreteConfig concreteDeployed concreteJoinBlock = .ok concreteJoined := by
  rw [stateTransitionUsing_eq_of_chainId_eq concreteDeploymentRoot.deployed_chainId]
  rw [show concreteConfig.forkAt concreteJoinBlock.header.timestamp = .ok .prague from
    ChainConfig.pragueOnly_forkAt 1 _]
  change stateTransitionAt .prague concreteDeployed concreteJoinBlock = _
  rw [stateTransitionAt_eq_ok_iff, stateTransitionE]
  have hh : validateHeader Fork.prague.ruleSet concreteDeployed concreteJoinBlock.header = .ok () := by
    change validateHeader pragueRules concreteDeployed concreteJoinBlock.header = .ok ()
    exact concreteJoinHeader_valid _ _ _ _ _
  rw [hh]
  change (do
    let output ← applyBody (initBenv .prague concreteDeployed concreteJoinBlock.header)
      concreteJoinBlock.txs concreteJoinBlock.wds
    Except.mapError TransitionError.block (stateTransitionChecks output.2
      concreteJoinBlock.header (getTransactionsRoot output.2) output.1.root
      (getReceiptRoot output.2) (logsBloom output.2.blockLogs)
      (getWithdrawalsRoot output.2) (computeRequestsHash output.2.requests))
    .ok (⟨appendBlock concreteDeployed.blocks concreteJoinBlock, output.1,
      concreteDeployed.chainId⟩ : BlockChain)) = .ok concreteJoined
  have hbody : applyBody (initBenv .prague concreteDeployed concreteJoinBlock.header)
      concreteJoinBlock.txs concreteJoinBlock.wds =
      .ok (concreteJoinTransactionState, concreteJoinTransactionBout) := by
    change applyBody (initBenv .prague concreteDeployed (concreteJoinHeader _ _ _ _ _))
      [.inl concreteJoinTxRlp] [] = _
    rw [concreteJoinHeader_benv]
    exact concreteJoin_body
  rw [hbody]
  simp only [Bind.bind, Except.bind, concreteJoin_checks, Except.mapError]
  rfl

theorem concreteJoined_storage : concreteJoined.state.getStor concreteCreateTarget =
    ((((concreteDeployed.state.getStor concreteCreateTarget).set chiSlot rate).set rhoSlot 2).set
      concreteCreateSender.toB256 99).set totalUnitsSlot 99 := by
  change concreteJoinTransactionState.getStor concreteCreateTarget = _
  unfold concreteJoinTransactionState deploymentFinalState State.getStor State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteJoinMessageState concreteJoinRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  change Devm.getStor concreteJoinTotalBase concreteCreateTarget = _
  unfold concreteJoinTotalBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteJoinRowBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteJoinRhoBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteJoinChiBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  have hs : Devm.getStor concreteJoinStorageBase concreteCreateTarget =
      (concreteDeployed.state.get concreteCreateTarget).stor := by
    change (concreteJoinEntry.state.get concreteCreateTarget).stor = _
    exact concreteJoinEntry_storage _
  rw [hs]

theorem concreteJoined_values :
    (concreteJoined.state.getStor concreteCreateTarget).get chiSlot = rate ∧
    (concreteJoined.state.getStor concreteCreateTarget).get rhoSlot = 2 ∧
    (concreteJoined.state.getStor concreteCreateTarget).get concreteCreateSender.toB256 = 99 ∧
    (concreteJoined.state.getStor concreteCreateTarget).get totalUnitsSlot = 99 := by
  rw [concreteJoined_storage]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel),
      Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  · exact Stor.get_set_self _ _ _

theorem concreteJoin_receiptSucceeded :
    (concreteJoinTransactionBout.receiptsTrie[deploymentReceiptKey 0]?).map
      (fun entry => entry.2.succeeded) = some true := by
  rw [concreteJoin_receiptEntry]
  rfl

private theorem concreteJoinMessageState_sender :
    concreteJoinMessageState.get concreteCreateSender = concreteJoinEntry.state.get concreteCreateSender := by
  unfold concreteJoinMessageState concreteJoinRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  change (((((concreteJoinEntry.state.setStorVal concreteCreateTarget chiSlot rate).setStorVal
    concreteCreateTarget rhoSlot 2).setStorVal concreteCreateTarget concreteCreateSender.toB256 99).setStorVal
    concreteCreateTarget totalUnitsSlot 99).get concreteCreateSender) = _
  simp only [State.setStorVal, State.get_set_ne _ ht]

theorem concreteJoinedSenderNonce : concreteJoined.state.getNonce concreteCreateSender = 2 := by
  change (concreteJoinTransactionState.get concreteCreateSender).nonce = _
  unfold concreteJoinTransactionState deploymentFinalState
  change (((concreteJoinMessageState.addBal concreteCreateSender 847712).addBal 0 76144).get
    concreteCreateSender).nonce = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  rw [concreteJoinMessageState_sender]
  change ((((concreteJoinDebit.setBal concreteCreateSender
    (concreteJoinDebit.bal concreteCreateSender - 100)).addBal concreteCreateTarget 100).get
    concreteCreateSender).nonce) = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  unfold concreteJoinDebit
  simp only [State.setBal_get_self, State.incrNonce, State.get_set_self]
  change (concreteDeployed.state.getNonce concreteCreateSender) + 1 = 2
  rw [concreteDeployedSenderNonce]
  rfl

theorem concreteJoinedSenderBalance : concreteJoined.state.bal concreteCreateSender = 999999999998887794 := by
  change (concreteJoinTransactionState.get concreteCreateSender).bal = _
  unfold concreteJoinTransactionState deploymentFinalState
  change (((concreteJoinMessageState.addBal concreteCreateSender 847712).addBal 0 76144).get
    concreteCreateSender).bal = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  change (concreteJoinMessageState.get concreteCreateSender).bal + 847712 = _
  rw [concreteJoinMessageState_sender]
  change ((((concreteJoinDebit.setBal concreteCreateSender
    (concreteJoinDebit.bal concreteCreateSender - 100)).addBal concreteCreateTarget 100).get
    concreteCreateSender).bal) + 847712 = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  change (concreteJoinDebit.bal concreteCreateSender - 100) + 847712 = _
  rw [concreteJoinDebit_balance]
  decide +kernel

theorem concreteJoinedCode (a : Adr) :
    concreteJoined.state.getCode a = concreteDeployed.state.getCode a := concreteJoinTransactionCode a

def concreteDripTx : Tx := {
  nonce := 2
  gas := 500000
  value := 0
  data := [0x9f, 0x67, 0x8c, 0xca]
  v := 1
  r := (0x54bbe7f6c75d559928c649a8d39736a680bb4e569d274ed61fc2e20098435621 : B256).toBytes
  s := (0x4e3417937e13aa8105714ddc0ab4591dc8359cb0a950cceeaa56ada642129272 : B256).toBytes
  type := .two 1 1 8 (some concreteCreateTarget) [] }

def concreteDripSigningPayload : Bytes :=
  [0x02, 0xe4, 1, 2, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++
  concreteCreateTarget.toBytes ++ [0x80, 0x84, 0x9f, 0x67, 0x8c, 0xca, 0xc0]

theorem concreteDripSigningEncoded :
    concreteDripTx.signingHash = some concreteDripSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 2).sig = [2] := by decide +kernel
  have ht : (BLT.bytes concreteCreateTarget.toBytes).toBytes =
      0x94 :: concreteCreateTarget.toBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by decide +kernel)]
    rfl
  have hlen : concreteCreateTarget.toBytes.length = 20 := rfl
  simp only [Tx.signingHash, concreteDripTx, hc, hn, AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  change 2 :: (BLT.list [.bytes [1], .bytes [2], .bytes (Nat.toBytes 1),
    .bytes (Nat.toBytes 8), .bytes (Nat.toBytes 500000), .bytes concreteCreateTarget.toBytes,
    .bytes (Nat.toBytes 0), .bytes [0x9f, 0x67, 0x8c, 0xca], .list []]).toBytes = _
  simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, ht, hlen,
    Nat.toBytes, Nat.toBytes.aux, concreteDripSigningPayload]

theorem concreteDripSigningHash :
    concreteDripTx.signingHash =
      some (0x1570eb57cef628e0a7446f140edbacc6972f0f656ad8f176b2ebadfd37f517bc : B256) := by
  rw [concreteDripSigningEncoded]
  decide +kernel

theorem concreteDripRecoveredSender :
    recoverSender 1 concreteDripTx = .ok concreteCreateSender := by
  rw [recoverSender, concreteDripSigningHash]
  decide +kernel

def concreteDripFields : List BLT :=
  [.bytes [1], .bytes [2], .bytes [1], .bytes [8], .bytes [7, 0xa1, 0x20],
   .bytes concreteCreateTarget.toBytes, .bytes [], .bytes [0x9f, 0x67, 0x8c, 0xca],
   .list [], .bytes [1], .bytes concreteDripTx.r, .bytes concreteDripTx.s]

def concreteDripPayload : Bytes :=
  [1, 2, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++ concreteCreateTarget.toBytes ++
  [0x80, 0x84, 0x9f, 0x67, 0x8c, 0xca, 0xc0, 1, 0xa0] ++ concreteDripTx.r ++
  [0xa0] ++ concreteDripTx.s

def concreteDripTxRlp : Bytes := [2, 0xf8, 0x67] ++ concreteDripPayload

theorem concreteDripBLT : concreteDripTx.toBLT = .list concreteDripFields := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 2).sig = [2] := by decide +kernel
  have hr : trimZero concreteDripTx.r = concreteDripTx.r := by decide +kernel
  have hs : trimZero concreteDripTx.s = concreteDripTx.s := by decide +kernel
  simp only [Tx.toBLT, concreteDripTx, hc, AccessList.toBLT, List.map_nil]
  simp [concreteDripFields, concreteDripTx, Nat.toBytes, Nat.toBytes.aux]
  exact ⟨hr, hs⟩

theorem concreteDripPayloadParse (k : Nat) :
    Bytes.toBLTs? (k + 12) concreteDripPayload = some concreteDripFields := by
  unfold concreteDripPayload concreteDripFields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 2 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 8 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [7, 0xa1, 0x20] _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 _ _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 [0x9f, 0x67, 0x8c, 0xca] _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_list _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 _ _ _ rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil] using RlpConcrete.decode_bytes_32 k concreteDripTx.s [] rfl
  rw [Bytes.toBLTs?]

theorem concreteDripPayload_length : concreteDripPayload.length = 103 := by
  simp only [concreteDripPayload, List.length_append, List.length_cons, List.length_nil]
  rfl

theorem concreteDripEnvelopeParse :
    Bytes.toBLT? (0xf8 :: 0x67 :: concreteDripPayload) = some (.list concreteDripFields) := by
  have hsplit : Jaune.List.splitAt? 103 concreteDripPayload = some (concreteDripPayload, []) := by
    simpa only [concreteDripPayload_length, List.append_nil] using
      RlpConcrete.splitAt_append concreteDripPayload ([] : Bytes)
  have hp : Bytes.toBLTDiff? 105 (0xf8 :: 0x67 :: concreteDripPayload) =
      some (.list concreteDripFields, []) := by
    rw [Bytes.toBLTDiff?]
    change (do
      let p ← Jaune.List.splitAt? 1 ([0x67] ++ concreteDripPayload)
      let q ← Jaune.List.splitAt? (Bytes.toNat p.1) p.2
      let rs ← Bytes.toBLTs? 104 q.1
      pure (BLT.list rs, q.2)) = _
    rw [show Jaune.List.splitAt? 1 ([0x67] ++ concreteDripPayload) =
      some ([0x67], concreteDripPayload) from
        RlpConcrete.splitAt_append [0x67] concreteDripPayload]
    change (do
      let q ← Jaune.List.splitAt? 103 concreteDripPayload
      let rs ← Bytes.toBLTs? 104 q.1
      pure (BLT.list rs, q.2)) = _
    rw [hsplit]
    change (do let rs ← Bytes.toBLTs? 104 concreteDripPayload; pure (BLT.list rs, [])) = _
    rw [concreteDripPayloadParse 92]
    rfl
  unfold Bytes.toBLT?
  simp only [List.length_cons, concreteDripPayload_length]
  rw [hp]

theorem concreteDripDecode : decodeTx (.inl concreteDripTxRlp) = .ok concreteDripTx := by
  simp only [decodeTx, concreteDripTxRlp, List.cons_append, List.nil_append,
    Bytes.toExTx, concreteDripEnvelopeParse, concreteDripFields]
  rfl


noncomputable def concreteDripExecutionHeader : Header :=
  { concreteJoinBlock.header with
    parentHash := concreteJoinBlock.header.hash
    number := 3
    gasUsed := 0
    timestamp := 5 }

theorem concreteJoinedSenderCode : concreteJoined.state.getCode concreteCreateSender = ByteArray.empty := by
  rw [concreteJoinedCode]
  exact concreteDeployedSenderCode

theorem concreteDripSenderChecked :
    checkTransactionSenderAccount (concreteJoined.state.get concreteCreateSender)
      concreteDripTx 4000000 = .ok () := by
  have hn : (concreteJoined.state.get concreteCreateSender).nonce = 2 := concreteJoinedSenderNonce
  have hb : (concreteJoined.state.get concreteCreateSender).bal = 999999999998887794 :=
    concreteJoinedSenderBalance
  have hc : (concreteJoined.state.get concreteCreateSender).code = ByteArray.empty :=
    concreteJoinedSenderCode
  simp only [checkTransactionSenderAccount, hn, hb, checkTransactionSenderCode, hc]
  decide +kernel


end Drip
end Blanc
