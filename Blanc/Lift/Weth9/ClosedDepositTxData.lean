import Blanc.Lift.Weth9.ClosedSigning

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.Lift

/-- Concrete admission and initial slot facts; execution remains to be proved. -/
structure DepositTxContext (benv : Benv) : Prop where
  fork : benv.stat.fork = .bpo2
  chain : benv.stat.chainId = 1
  baseFee : benv.stat.baseFeePerGas = 1
  coinbase : benv.stat.coinbase = 0
  room : 50000 ≤ benv.stat.blockGasLimit
  nonce : (benv.state.get senderE).nonce = 0
  balance : benv.state.bal senderE = 1000000
  noCode : (benv.state.getCode senderE).size = 0
  code : benv.state.getCode contractAddress = Weth9.code
  slot : (benv.state.getStor contractAddress).get (balSlot senderE) = 0
  ether : benv.state.bal contractAddress = 0

def depositDebitState (st : Jaune.State) : Jaune.State :=
  (st.incrNonce senderE).setBal senderE 900000

def depositTransferState (st : Jaune.State) : Jaune.State :=
  ((depositDebitState st).setBal senderE 899999).addBal contractAddress 1

def depositFrameState (st : Jaune.State) : Jaune.State :=
  (depositTransferState st).setStorVal contractAddress (balSlot senderE) 1

def depositSettledState (st : Jaune.State) : Jaune.State :=
  ((depositFrameState st).addBal senderE 9924).addBal 0 45038

theorem deposit_intrinsic {rules : ForkRules}
    (hsg : rules.stateGas = none) (hbase : rules.gas.txBase = 21000)
    (hfloor : rules.gas.floorTokenCost = 10) :
    calculateIntrinsicCost rules depositTx senderE = (21064, 21160) := by
  rw [calculateIntrinsicCost_two_call hsg (by rfl)]
  simp only [depositTx, dpSel_eq, hbase, hfloor]
  decide +kernel

theorem deposit_frame_gas {sevm : Sevm} {pre : Devm}
    (hvalue : sevm.value = 1)
    (hcur : pre.getStorVal sevm.currentTarget (balSlot sevm.caller) = 0)
    (horig : getOrigStorVal sevm sevm.currentTarget (balSlot sevm.caller) = 0)
    (hcold : (sevm.currentTarget, balSlot sevm.caller) ∉ pre.accessedStorageKeys) :
    depositGas sevm pre = 23974 ∧ depositStore sevm pre = 20000 := by
  have warm := mem_afterSload_accessedStorageKeys sevm pre (balSlot sevm.caller)
  have load : depositLoad sevm pre = 2100 := by
    unfold depositLoad sloadCost
    simp only [hcold, ite_false]
    rfl
  have store : depositStore sevm pre = 20000 := by
    have sum : (0 : B256) + 1 = 1 := by decide +kernel
    unfold depositStore sstoreCost
    simp only [warm, ite_true, getStorVal_afterSload, hcur, horig, hvalue, sum]
    decide +kernel
  exact ⟨by rw [depositGas, load, store], store⟩

/-- The exact positive deposit frame, before transaction settlement. -/
theorem deposit_frame_success {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code = Weth9.code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcaller : sevm.caller = senderE) (htarget : sevm.currentTarget = contractAddress)
    (hstatic : sevm.isStatic = false) (hdata : sevm.data = depositTx.data)
    (hvalue : sevm.value = 1)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hgas : pre.gasLeft = 28936)
    (hcur : pre.getStorVal contractAddress (balSlot senderE) = 0)
    (horig : getOrigStorVal sevm contractAddress (balSlot senderE) = 0)
    (hcold : (contractAddress, balSlot senderE) ∉ pre.accessedStorageKeys)
    (herror : pre.error = none) (hrefund : pre.refundCounter = 0)
    (hlogs : pre.logs = []) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      DepositFramePost sevm pre post ∧ post.gasLeft = 4962 ∧
      post.error = none ∧ post.refundCounter = 0 ∧
      post.accountsToDelete = pre.accountsToDelete ∧
      post.state = pre.state.setStorVal contractAddress (balSlot senderE) 1 ∧
      ∃ event : Log, event.address = contractAddress ∧ post.logs = [event] := by
  have current : pre.getStorVal sevm.currentTarget (balSlot sevm.caller) = 0 := by
    rw [hcaller, htarget]
    exact hcur
  have original : getOrigStorVal sevm sevm.currentTarget (balSlot sevm.caller) = 0 := by
    rw [hcaller, htarget]
    exact horig
  have cold : (sevm.currentTarget, balSlot sevm.caller) ∉ pre.accessedStorageKeys := by
    rw [hcaller, htarget]
    exact hcold
  obtain ⟨frameGas, storeGas⟩ := deposit_frame_gas hvalue current original cold
  have sum : (0 : B256) + 1 = 1 := by decide +kernel
  have selector : Sevm.selector sevm = dpSel := by
    simp only [Sevm.selector, Sevm.dataWord, hdata, depositTx, dpSel_eq]
    decide +kernel
  have length : sevm.data.length = 4 := by
    simp only [hdata, depositTx, dpSel_eq]
    decide +kernel
  obtain ⟨post, run, gas, output, facts⟩ := weth9_deposit_runExact_framed
    (G := 4962) hfork hstatic selector (by omega) (by omega) hstack hmem
    (by rw [hgas, frameGas]) (by rw [storeGas]; decide +kernel)
  refine ⟨post, (exec_iff_exec_eq 0 sevm pre (.ok post)).mp
    (exec_of_runExact hcode hfork run), facts, gas, facts.error.trans herror, ?_,
    facts.accountsToDelete, ?_, ?_⟩
  · rw [facts.refund, current, original, hvalue, sum, hrefund]
    rfl
  · rw [facts.state, hcaller, htarget, hcur, hvalue, sum]
  · obtain ⟨event, address, logs⟩ := facts.logs
    exact ⟨event, address.trans htarget, by rw [logs, hlogs, List.nil_append]⟩

end Blanc.Lift.Weth9.ClosedInstance
