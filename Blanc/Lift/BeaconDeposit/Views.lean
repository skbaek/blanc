import Blanc.Lift.BeaconDeposit.Jumps
import Blanc.Lift.BeaconDeposit.CountView
import Blanc.Lift.BeaconDeposit.Erc165
import Blanc.Lift.BeaconDeposit.RootView

/-!
# The deployed contract's views, as real executions (parity row P4)

The gas-exact synthetic runs of `get_deposit_count` (`CountView.lean`) and `supportsInterface`
(`Erc165.lean`) composed with the kernel-checked converse bridge `exec_of_runExact`: each is a real
Jaune execution of the deployed runtime.  The post states differ from the pre state only in the
machine (stack, memory, gas), the output, and for the cold count read the accessed-storage set: no
storage, balance, code or log changes.  Counterparts of the port's
`getDepositCount_warm_runCompiled_noRawSstore` and `supportsInterface_runCompiled_noRawSstore`.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

theorem get_deposit_count_warm_exec (sevm : Sevm) (base : Devm) (word : B256) (G : Nat)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositCountSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hwarm : (⟨sevm.currentTarget, countSlot⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hstorage : base.getStorVal sevm.currentTarget countSlot = word) :
    ∃ Mf, Mem.Wf Mf ∧ Mem.Reads Mf (countImg word) ∧ Mf.size = 288 ∧
      Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + countGasWarm, base.stateGas⟩)
        (.ok ((base.setMach ⟨[Sevm.selector sevm], Mf, G, base.stateGas⟩).withOutput
          (Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 word.toNat))))) := by
  obtain ⟨Mf, hwf, hreads, hsize, hrun⟩ := get_deposit_count_warm_runExact sevm base word G
    hdataLength hdataBound hvalue hselector hfork hwarm hstorage
  exact ⟨Mf, hwf, hreads, hsize, exec_of_runExact hcode hfork hrun⟩

theorem get_deposit_count_cold_exec (sevm : Sevm) (base : Devm) (word : B256) (G : Nat)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositCountSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hcold : (⟨sevm.currentTarget, countSlot⟩ : Adr × B256) ∉ base.accessedStorageKeys)
    (hstorage : base.getStorVal sevm.currentTarget countSlot = word) :
    ∃ Mf, Mem.Wf Mf ∧ Mem.Reads Mf (countImg word) ∧ Mf.size = 288 ∧
      Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + countGasCold, base.stateGas⟩)
        (.ok (((addAccessedStorageKey base sevm.currentTarget countSlot).setMach
          ⟨[Sevm.selector sevm], Mf, G, base.stateGas⟩).withOutput
          (Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 word.toNat))))) := by
  obtain ⟨Mf, hwf, hreads, hsize, hrun⟩ := get_deposit_count_cold_runExact sevm base word G
    hdataLength hdataBound hvalue hselector hfork hcold hstorage
  exact ⟨Mf, hwf, hreads, hsize, exec_of_runExact hcode hfork hrun⟩

theorem supportsInterface_exec {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = Blanc.BeaconDeposit.supportsInterfaceSelector)
    (h_len : 36 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : erc165Gas sevm ≤ pre.gasLeft) :
    ∃ post, Nonempty (Exec 0 sevm pre (.ok post)) ∧
      post.gasLeft + erc165Gas sevm = pre.gasLeft ∧
      post.output = Blanc.BeaconDeposit.abiBoolReturn (decide
        (Sevm.argWord sevm 0 >>> 224 = Blanc.BeaconDeposit.erc165InterfaceId ∨
          Sevm.argWord sevm 0 >>> 224 = Blanc.BeaconDeposit.depositInterfaceId)) ∧
      post.state = pre.state ∧ post.logs = pre.logs := by
  obtain ⟨post, hrun, hgas, hout, hstate, hlogs⟩ := supportsInterface_runExact hfork h_value h_sel
    h_len h_len' h_stack h_mem h_gas
  exact ⟨post, exec_of_runExact hcode hfork hrun, hgas, hout, hstate, hlogs⟩

theorem get_deposit_root_exec (sevm : Sevm) (base : Devm) (stor : Stor) (count G : Nat)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositRootSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue : stor.get solCountSlot = Nat.toB256 count)
    (hcount : count < 2 ^ 32)
    (hzero : SolZeroHashesCorrect stor)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : G + rootViewGas sevm base count + 6000 < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + rootViewGas sevm base count, base.stateGas⟩) (.ok post)) ∧
      post.gasLeft = G ∧
      post.output = (Blanc.BeaconDeposit.Acc.root Bytes.sha256 (solAcc stor)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.logs = base.logs := by
  obtain ⟨post, hrun, _, hgas, hout, hst, hcd, _, _, hlogs, _⟩ := get_deposit_root_runExact sevm base
    stor count G hdataLength hdataBound hvalue hselector hfork hstor hcountValue hcount hzero hnodeleg
    hwarm hpre hdepth hbound
  exact ⟨post, exec_of_runExact hcode hfork hrun, hgas, hout, hst, hcd, hlogs⟩

/-- The count word of a storage satisfying the abstraction is the history length. -/
theorem solCount_eq_of_solInv {stor : Stor} {history : List B256} (hinv : SolInv stor history) :
    stor.get solCountSlot = Nat.toB256 history.length ∧ history.length < 2 ^ 32 := by
  obtain ⟨_, hc, hlt, _⟩ := hinv
  refine ⟨B256.toNat_inj _ _ ?_, hlt⟩
  rw [B256.toNat_toB256, Nat.lo_eq_of_lt (by omega)]
  exact hc

/-- **B3 for the root view.**  From a storage satisfying the abstraction for a leaf history, the
deployed `get_deposit_root()` returns the model's reference mixed root of that history. -/
theorem get_deposit_root_exec_mixedRoot (sevm : Sevm) (base : Devm) (stor : Stor)
    (history : List B256) (G : Nat)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositRootSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hinv : SolInv stor history)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : G + rootViewGas sevm base history.length + 6000 < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + rootViewGas sevm base history.length, base.stateGas⟩)
        (.ok post)) ∧
      post.gasLeft = G ∧
      post.output = (Blanc.BeaconDeposit.mixedRootOf Bytes.sha256 history).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      post.logs = base.logs := by
  obtain ⟨hcv, hlt⟩ := solCount_eq_of_solInv hinv
  obtain ⟨post, hexec, hgas, hout, hst, _, hlogs⟩ := get_deposit_root_exec sevm base stor
    history.length G hcode hdataLength hdataBound hvalue hselector hfork hstor hcv hlt hinv.1 hnodeleg
    hwarm hpre hdepth hbound
  refine ⟨post, hexec, hgas, ?_, hst, hlogs⟩
  rw [hout, Blanc.BeaconDeposit.root_correct _ _ _ hinv.2]

/-- **B3 for the count view.**  From a storage satisfying the abstraction, the deployed
`get_deposit_count()` returns the little-endian history length. -/
theorem get_deposit_count_warm_exec_history (sevm : Sevm) (base : Devm) (stor : Stor)
    (history : List B256) (G : Nat)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = Blanc.BeaconDeposit.getDepositCountSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hwarm : (⟨sevm.currentTarget, countSlot⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hinv : SolInv stor history) :
    ∃ Mf, Nonempty (Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + countGasWarm, base.stateGas⟩)
        (.ok ((base.setMach ⟨[Sevm.selector sevm], Mf, G, base.stateGas⟩).withOutput
          (Blanc.BeaconDeposit.abiDynamicBytesReturn (Blanc.BeaconDeposit.le64 history.length))))) := by
  obtain ⟨hcv, hlt⟩ := solCount_eq_of_solInv hinv
  have hword : base.getStorVal sevm.currentTarget countSlot = Nat.toB256 history.length := by
    rw [← hcv, ← hstor]; rfl
  obtain ⟨Mf, _, _, _, hexec⟩ := get_deposit_count_warm_exec sevm base (Nat.toB256 history.length) G
    hcode hdataLength hdataBound hvalue hselector hfork hwarm hword
  refine ⟨Mf, ?_⟩
  rwa [B256.toNat_toB256, Nat.lo_eq_of_lt (by omega)] at hexec

end Blanc.Lift.BeaconDeposit
