import Blanc.Lift.BeaconDeposit.Jumps
import Blanc.Lift.BeaconDeposit.CountView
import Blanc.Lift.BeaconDeposit.Erc165

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

end Blanc.Lift.BeaconDeposit
