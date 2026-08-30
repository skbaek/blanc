import Blanc.BeaconDepositRootEffects

/-!
# Beacon deposit public root-view effects

Thin public composition of the root endpoint, zero-value wrapper, and selector
route.  Keeping this layer separate prevents the endpoint proof term from being
re-expanded while the public carrier is elaborated.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- The exact compiled public root query at zero value. -/
theorem getDepositRoot_zero_runCompiled
    (sevm : Sevm) (base : Devm) (stor : Stor) (count G : Nat)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 count)
    (hcount : count < 2 ^ 32)
    (hzero : ZeroHashesCorrect stor)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      G + 416 +
          rootLoopGas sevm.currentTarget stor 32
            (rootInitialLoopState
              (afterSload sevm base depositCountSlot)
              (Nat.toB256 count)) <
        2 ^ 256)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach
          ⟨[], Mem.empty,
            G + getDepositRootRuntimeGas sevm base stor count⟩)
        runtime post ∧
      post.stack = [] ∧
      post.gasLeft = G ∧
      post.output =
        (Acc.root Bytes.sha256 (accOfStor stor)).toBytes ∧
      Bytes.toB256 post.output =
        Acc.root Bytes.sha256 (accOfStor stor) ∧
      post.returnData =
        (Acc.root Bytes.sha256 (accOfStor stor)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys =
        (rootLoopIter sevm.currentTarget stor 32
          (rootInitialLoopState
            (afterSload sevm base depositCountSlot)
            (Nat.toB256 count))).keys ∧
      post.logs = base.logs ∧
      post.error = base.error ∧
      some sevm.code.toList = Prog.compile runtime := by
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  obtain ⟨post, hendpoint, hstack, hgas, houtput, houtputWord,
      hreturnData, hpostStor, hpostCode, hpostAddresses,
      hpostKeys, hpostLogs, hpostError⟩ :=
    getDepositRootEndpoint_runCompiled
      (fs := runtime.main :: runtime.aux)
      (sevm := sevm) (base := base) (stor := stor)
      (count := count) (G := G)
      hstor hcountValue hcount hzero hnodeleg hwarm hpre hdepth hbound
      (by rfl) (by rfl)
  let endpointGas :=
    416 +
      rootLoopGas sevm.currentTarget stor 32
        (rootInitialLoopState
          (afterSload sevm base depositCountSlot)
          (Nat.toB256 count)) +
      getDepositRootPrefixGas sevm base
  have hendpoint' :
      Func.RunCompiled (runtime.main :: runtime.aux) sevm
        (routeBase.setMach
          ⟨routeBase.stack, routeBase.memory, G + endpointGas⟩)
        getDepositRootEndpoint post := by
    have hgasEntry :
        G + endpointGas =
          G + 416 +
              rootLoopGas sevm.currentTarget stor 32
                (rootInitialLoopState
                  (afterSload sevm base depositCountSlot)
                  (Nat.toB256 count)) +
            getDepositRootPrefixGas sevm base := by
      dsimp only [endpointGas]
      omega
    rw [hgasEntry]
    change Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], Mem.empty,
          G + 416 +
              rootLoopGas sevm.currentTarget stor 32
                (rootInitialLoopState
                  (afterSload sevm base depositCountSlot)
                  (Nat.toB256 count)) +
            getDepositRootPrefixGas sevm base⟩)
      getDepositRootEndpoint post
    exact hendpoint
  have hwrapped :=
    nonpayableEndpoint_zero_runCompiled
      (fs := runtime.main :: runtime.aux) (sevm := sevm)
      (base := routeBase) (post := post) (G := G + endpointGas)
      (body := getDepositRootEndpoint) hvalue
      (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
      hendpoint'
  have hlengthWordNe : sevm.data.length.toB256 ≠ 0 := by
    intro hzeroWord
    have hnat := congrArg B256.toNat hzeroWord
    rw [B256.toNat_toB256_of_lt hdataBound] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  have hroute0 :=
    getDepositRoot_route_runCompiled
      (base := base)
      (K := G + endpointGas + nonpayableEndpointZeroGas)
      hlengthWordNe hselector
      (by
        simpa only [routeBase, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using hwrapped)
  have hboundary :
      G + endpointGas + nonpayableEndpointZeroGas +
          getDepositRootRouteGas =
        G + getDepositRootRuntimeGas sevm base stor count := by
    simp only [endpointGas, getDepositRootRuntimeGas]
    omega
  have hroute : Prog.RunCompiled sevm
      (base.setMach
        ⟨[], Mem.empty,
          G + getDepositRootRuntimeGas sevm base stor count⟩)
      runtime post := by
    simpa only [hboundary] using hroute0
  have hcountWord : stor.get depositCountSlot = Nat.toB256 count := by
    change (Devm.getStor base sevm.currentTarget).get depositCountSlot =
      Nat.toB256 count at hcountValue
    rw [hstor] at hcountValue
    exact hcountValue
  have haccCount : (accOfStor stor).count = count := by
    rw [accOfStor_count, hcountWord,
      B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
  refine ⟨post, hroute, hstack, hgas, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simpa only [Acc.root, haccCount] using houtput
  · simpa only [Acc.root, haccCount] using houtputWord
  · simpa only [Acc.root, haccCount] using hreturnData
  · exact hpostStor
  · exact hpostCode
  · exact hpostAddresses
  · exact hpostKeys
  · exact hpostLogs
  · exact hpostError
  · rw [hcode, code_compile]

/-- The exact zero-value public root query traverses no raw SSTORE, retains no
storage write/effect, and returns the same model root as the compiled-view
theorem above. -/
theorem getDepositRoot_zero_runCompiled_noRawSstore
    (sevm : Sevm) (base : Devm) (stor : Stor) (count G : Nat)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 count)
    (hcount : count < 2 ^ 32)
    (hzero : ZeroHashesCorrect stor)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      G + 416 +
          rootLoopGas sevm.currentTarget stor 32
            (rootInitialLoopState
              (afterSload sevm base depositCountSlot)
              (Nat.toB256 count)) <
        2 ^ 256)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      ∃ execution : Exec 0 sevm
          (base.setMach
            ⟨[], Mem.empty,
              G + getDepositRootRuntimeGas sevm base stor count⟩)
          (.ok post),
        Prog.RunCompiledTo sevm
            (base.setMach
              ⟨[], Mem.empty,
                G + getDepositRootRuntimeGas sevm base stor count⟩)
            runtime (.ok post) ∧
        post.stack = [] ∧
        post.gasLeft = G ∧
        post.output =
          (Acc.root Bytes.sha256 (accOfStor stor)).toBytes ∧
        Bytes.toB256 post.output =
          Acc.root Bytes.sha256 (accOfStor stor) ∧
        post.returnData =
          (Acc.root Bytes.sha256 (accOfStor stor)).toBytes ∧
        (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
        (∀ a, post.getCode a = base.getCode a) ∧
        post.accessedAddresses = base.accessedAddresses ∧
        post.accessedStorageKeys =
          (rootLoopIter sevm.currentTarget stor 32
            (rootInitialLoopState
              (afterSload sevm base depositCountSlot)
              (Nat.toB256 count))).keys ∧
        post.logs = base.logs ∧
        post.error = base.error ∧
        Exec.NoRawSstore execution ∧
        Exec.retainedStorageWrites execution = [] ∧
        Exec.retainedStorageEffectTriples execution = [] ∧
        some sevm.code.toList = Prog.compile runtime := by
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  obtain ⟨post, hendpoint, hstack, hgas, houtput, houtputWord,
      hreturnData, hpostStor, hpostCode, hpostAddresses,
      hpostKeys, hpostLogs, hpostError⟩ :=
    getDepositRootEndpoint_storageEffectRun
      (sevm := sevm) (base := base) (stor := stor)
      (count := count) (G := G)
      hstor hcountValue hcount hzero hnodeleg hwarm hpre hdepth hbound
  let endpointGas :=
    416 +
      rootLoopGas sevm.currentTarget stor 32
        (rootInitialLoopState
          (afterSload sevm base depositCountSlot)
          (Nat.toB256 count)) +
      getDepositRootPrefixGas sevm base
  have hendpoint' : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (routeBase.setMach
        ⟨routeBase.stack, routeBase.memory, G + endpointGas⟩)
      getDepositRootEndpoint (.ok post) [] := by
    have hgasEntry :
        G + endpointGas =
          G + 416 +
              rootLoopGas sevm.currentTarget stor 32
                (rootInitialLoopState
                  (afterSload sevm base depositCountSlot)
                  (Nat.toB256 count)) +
            getDepositRootPrefixGas sevm base := by
      dsimp only [endpointGas]
      omega
    rw [hgasEntry]
    change Func.StorageEffectRun (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], Mem.empty,
          G + 416 +
              rootLoopGas sevm.currentTarget stor 32
                (rootInitialLoopState
                  (afterSload sevm base depositCountSlot)
                  (Nat.toB256 count)) +
            getDepositRootPrefixGas sevm base⟩)
      getDepositRootEndpoint (.ok post) []
    exact hendpoint
  have hwrapped :=
    getDepositRootEndpoint_nonpayable_zero_storageEffectRun
      (fs := runtime.main :: runtime.aux) (sevm := sevm)
      (base := routeBase) (G := G + endpointGas)
      hvalue
      (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
      hendpoint'
  have hlengthWordNe : sevm.data.length.toB256 ≠ 0 := by
    intro hzeroWord
    have hnat := congrArg B256.toNat hzeroWord
    rw [B256.toNat_toB256_of_lt hdataBound] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  obtain ⟨execution, hroute, executionSafe, hwrites, htriples,
      hcompiled⟩ :=
    getDepositRoot_route_noRawSstore
      (base := base)
      (K := G + endpointGas + nonpayableEndpointZeroGas)
      hlengthWordNe hselector hcode (by
        simpa only [routeBase, Devm.setMach_setMach,
            Devm.stack_setMach, Devm.memory_setMach] using hwrapped)
  have hboundary :
      G + endpointGas + nonpayableEndpointZeroGas +
          getDepositRootRouteGas =
        G + getDepositRootRuntimeGas sevm base stor count := by
    simp only [endpointGas, getDepositRootRuntimeGas]
    omega
  have hcountWord : stor.get depositCountSlot = Nat.toB256 count := by
    change (Devm.getStor base sevm.currentTarget).get depositCountSlot =
      Nat.toB256 count at hcountValue
    rw [hstor] at hcountValue
    exact hcountValue
  have haccCount : (accOfStor stor).count = count := by
    rw [accOfStor_count, hcountWord,
      B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
  rw [← hboundary]
  refine ⟨post, execution, hroute, hstack, hgas, ?_, ?_, ?_,
    hpostStor, hpostCode, hpostAddresses, hpostKeys, hpostLogs, hpostError,
    executionSafe, hwrites, htriples, hcompiled⟩
  · simpa only [Acc.root, haccCount] using houtput
  · simpa only [Acc.root, haccCount] using houtputWord
  · simpa only [Acc.root, haccCount] using hreturnData

end Blanc.BeaconDeposit
