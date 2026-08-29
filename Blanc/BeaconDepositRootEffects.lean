import Blanc.BeaconDepositRootFold
import Blanc.BeaconDepositCountEffects

/-!
# Beacon deposit root-view effects

Exact selector-tree routing and compiled effects for `get_deposit_root()`.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- Exact successful internal execution of `get_deposit_root`. -/
theorem getDepositRootEndpoint_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {stor : Stor} {count G : Nat}
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
    (hrootContinuation :
      fs[rootContinuationSlot]? = some rootContinuation)
    (hrootLoop : fs[rootLoopSlot]? = some rootLoop) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach
          ⟨[], Mem.empty,
            G + 416 +
                rootLoopGas sevm.currentTarget stor 32
                  (rootInitialLoopState
                    (afterSload sevm base depositCountSlot)
                    (Nat.toB256 count)) +
              getDepositRootPrefixGas sevm base⟩)
        getDepositRootEndpoint post ∧
      post.stack = [] ∧
      post.gasLeft = G ∧
      post.output =
        (mixIn Bytes.sha256
          (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
          count).toBytes ∧
      Bytes.toB256 post.output =
        mixIn Bytes.sha256
          (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
          count ∧
      post.returnData =
        (mixIn Bytes.sha256
          (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
          count).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys =
        (rootLoopIter sevm.currentTarget stor 32
          (rootInitialLoopState
            (afterSload sevm base depositCountSlot)
            (Nat.toB256 count))).keys ∧
      post.logs = base.logs ∧
      post.error = base.error := by
  let loaded := afterSload sevm base depositCountSlot
  let initial := rootInitialLoopState loaded (Nat.toB256 count)
  let final := rootLoopIter sevm.currentTarget stor 32 initial
  let node :=
    climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0
  let Good : Devm → Prop := fun post =>
    post.stack = [] ∧
    post.gasLeft = G ∧
    post.output = (mixIn Bytes.sha256 node count).toBytes ∧
    Bytes.toB256 post.output = mixIn Bytes.sha256 node count ∧
    post.returnData = (mixIn Bytes.sha256 node count).toBytes ∧
    (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
    (∀ a, post.getCode a = base.getCode a) ∧
    post.accessedAddresses = base.accessedAddresses ∧
    post.accessedStorageKeys = final.keys ∧
    post.logs = base.logs ∧
    post.error = base.error
  let P : Execution → Prop := fun ex =>
    ∃ post, ex = .ok post ∧ Good post
  have hloadedStor :
      Devm.getStor loaded sevm.currentTarget = stor := by
    simpa only [loaded, rootAfterSload_getStor] using hstor
  have hloadedNodeleg :
      getDelegatedCodeAddress (loaded.getCode 2) = none := by
    simpa only [loaded, rootAfterSload_getCode] using hnodeleg
  have hloadedWarm : (2 : Adr) ∈ loaded.accessedAddresses := by
    simpa only [loaded, rootAfterSload_accessedAddresses] using hwarm
  have hactive : RootLoopActive sevm.currentTarget stor 32 initial := by
    simpa only [initial] using
      rootLoopActive_32_initial sevm.currentTarget stor loaded count
        hcount hzero
  have htrace :=
    rootLoopIter_32_initial_eq_climb
      sevm.currentTarget stor loaded count hcount hzero
  have hfinalSize : final.size = 0 := by
    dsimp only [final, initial]
    rw [htrace]
    rfl
  have hfinalNode : final.node = node := by
    dsimp only [final, initial, node]
    rw [htrace]
    rfl
  have hfinalHeight : final.height = (32 : B256) := by
    dsimp only [final, initial]
    rw [htrace]
    rfl
  have hfinishBound : G + 237 < 2 ^ 256 := by
    omega
  obtain ⟨ex, hGood, hloop⟩ :=
    rootLoop_iterations_exists_runCompiledTo
      (P := P)
      (rootInitialLoopCarrier loaded (Nat.toB256 count))
      hloadedStor hactive hloadedNodeleg hloadedWarm hpre hdepth
      (by simpa only [initial] using hbound)
      hrootContinuation hrootLoop
      (by
        intro base' memory' carrier
        have hmem :
            RootMemoryCarrier memory' (Nat.toB256 count) 0 node := by
          have hm := carrier.mem
          change RootMemoryCarrier memory' (Nat.toB256 count)
            final.size final.node at hm
          rw [hfinalSize, hfinalNode] at hm
          exact hm
        have hnodeleg' :
            getDelegatedCodeAddress (base'.getCode 2) = none := by
          rw [carrier.code]
          exact hloadedNodeleg
        have hwarm' : (2 : Adr) ∈ base'.accessedAddresses := by
          rw [carrier.addresses]
          exact hloadedWarm
        obtain ⟨post, hfinish, hstack, hgas, houtput, houtputWord,
            hreturnData, hpostStor, hpostCode, hpostAddresses,
            hpostKeys, hpostLogs, hpostError⟩ :=
          rootFinish_runCompiled
            (fs := fs) (sevm := sevm) (base := base')
            (memory := memory') (oldCount := Nat.toB256 count)
            (shiftedSize := 0) (node := node) (height := (32 : B256))
            (G := G) hmem hnodeleg' hwarm' hpre hdepth hfinishBound
        have hterminal :
            Func.RunCompiledTo fs sevm
              (base'.setMach
                ⟨[(32 : B256)], memory', G + 416⟩)
              rootLoop (.ok post) := by
          apply rootLoopFinish32_dispatch_runCompiledTo
            (stack := []) (K := G + 391) hmem
            (by simp only [List.length_nil]; omega)
          simpa only [show G + 391 + 25 = G + 416 by omega] using
            Func.RunCompiledTo.of_runCompiled hfinish
        refine ⟨.ok post, ?_, ?_⟩
        · refine ⟨post, rfl, ?_⟩
          dsimp only [Good]
          refine ⟨hstack, hgas, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [
              B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
              using houtput
          · simpa only [
              B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
              using houtputWord
          · simpa only [
              B256.toNat_toB256_of_lt (by omega : count < 2 ^ 256)]
              using hreturnData
          · intro a
            rw [hpostStor, carrier.stor]
            simp only [loaded, rootAfterSload_getStor]
          · intro a
            rw [hpostCode, carrier.code]
            simp only [loaded, rootAfterSload_getCode]
          · rw [hpostAddresses, carrier.addresses]
            simp only [loaded, rootAfterSload_accessedAddresses]
          · rw [hpostKeys, carrier.keys]
          · rw [hpostLogs, carrier.logs]
            simp only [loaded, rootAfterSload_logs]
          · rw [hpostError, carrier.error]
            simp only [loaded, rootAfterSload_error]
        · change Func.RunCompiledTo fs sevm
            (base'.setMach ⟨[final.height], memory', G + 416⟩)
            rootLoop (.ok post)
          simpa only [hfinalHeight] using hterminal)
  have hloop' : Func.RunCompiledTo fs sevm
      (loaded.setMach
        ⟨[0], rootInitialMemory (Nat.toB256 count),
          G + 416 + rootLoopGas sevm.currentTarget stor 32 initial⟩)
      rootLoop ex := by
    simpa only [initial, rootInitialLoopState] using hloop
  have hendpoint :=
    getDepositRootEndpoint_prefix_runCompiledTo
      (K := G + 416 + rootLoopGas sevm.currentTarget stor 32 initial)
      hcountValue hrootLoop hloop'
  dsimp only [P] at hGood
  rcases hGood with ⟨post, rfl, hpost⟩
  refine ⟨post, Func.RunCompiled.of_runCompiledTo_ok ?_, ?_⟩
  · simpa only [loaded, initial] using hendpoint
  · simpa only [Good, node, final, initial, loaded] using hpost

private def getDepositRootLeafRoute : Func :=
  pushB256 getDepositRootSelector ::: eq :::
    ((nonpayableEndpoint getDepositRootEndpoint) <?> Func.rev)

private def getDepositRootInnerRoute : Func :=
  dup 0 ::: pushB256 getDepositRootSelector ::: gt :::
    ((pushB256 getDepositCountSelector ::: eq :::
        ((nonpayableEndpoint getDepositCountEndpoint) <?> Func.rev)) <?>
      getDepositRootLeafRoute)

private def getDepositRootMiddleRoute : Func :=
  dup 0 ::: pushB256 getDepositCountSelector ::: gt :::
    (dispatch (.leaf depositSelector depositEndpoint) <?>
      getDepositRootInnerRoute)

private def getDepositRootRootRoute : Func :=
  dup 0 ::: pushB256 depositSelector ::: gt :::
    (dispatch
      (.leaf supportsInterfaceSelector
        (nonpayableEndpoint supportsInterfaceEndpoint)) <?>
      getDepositRootMiddleRoute)

private def getDepositRootMainRoute : Func :=
  fsig +++ getDepositRootRootRoute

private theorem getDepositRootMainRoute_eq :
    Func.main tree = getDepositRootMainRoute := by
  rfl

private theorem getDepositRootLeafRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayableEndpoint getDepositRootEndpoint) out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩)
      getDepositRootLeafRoute out := by
  unfold getDepositRootLeafRoute
  have hpushCost :
      pushCost getDepositRootSelector.toBytes.sig = gVerylow := by
    rw [getDepositRootSelector_eq]
    decide +kernel
  have hpushGas :
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩).gasLeft =
          G + 17 + gVerylow := by
    simp only [Devm.gasLeft_setMach, gVerylow]
  have hpushRoom :
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩).stack.length <
          1024 := by
    simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 hpushCost hpushGas hpushRoom) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .eq) (f := B256.eqCheck)
      (cost := gVerylow) (G := G + 14) (v := 1)
      (by rintro ⟨⟩) rfl rfl (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_succ
    (w := (1 : B256)) (s := []) (G := G)
    (by decide) rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    hbody

private theorem getDepositRootInnerRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hleaf : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 20⟩)
      getDepositRootLeafRoute out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 42⟩)
      getDepositRootInnerRoute out := by
  unfold getDepositRootInnerRoute
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositRootSelector) (G := G + 39) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost :
      pushCost getDepositRootSelector.toBytes.sig = gVerylow := by
    rw [getDepositRootSelector_eq]
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 36) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 33) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_zero
    (s := [getDepositRootSelector]) (G := G + 20)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hleaf)

private theorem getDepositRootMiddleRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hinner : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 42⟩)
      getDepositRootInnerRoute out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 64⟩)
      getDepositRootMiddleRoute out := by
  unfold getDepositRootMiddleRoute
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositRootSelector) (G := G + 61) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost :
      pushCost getDepositCountSelector.toBytes.sig = gVerylow := by
    rw [getDepositCountSelector_eq]
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 58) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 55) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [getDepositCountSelector_eq, getDepositRootSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_zero
    (s := [getDepositRootSelector]) (G := G + 42)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hinner)

private theorem getDepositRootRootRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hmiddle : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 64⟩)
      getDepositRootMiddleRoute out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 86⟩)
      getDepositRootRootRoute out := by
  unfold getDepositRootRootRoute
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositRootSelector) (G := G + 83) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost : pushCost depositSelector.toBytes.sig = gVerylow := by
    rw [depositSelector_eq]
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 80) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 77) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [depositSelector_eq, getDepositRootSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_zero
    (s := [getDepositRootSelector]) (G := G + 64)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hmiddle)

private theorem getDepositRootMainRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hroot : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositRootSelector], Mem.empty, G + 86⟩)
      getDepositRootRootRoute out) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 97⟩)
      (Func.main tree) out := by
  rw [getDepositRootMainRoute_eq]
  unfold getDepositRootMainRoute fsig shiftRight cdl
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (c := gBase) (G := G + 95)
      pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_calldataload
      (v := Sevm.dataWord sevm 0) (G := G + 92) rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  have hpush224 : pushCost (224 : B256).toBytes.sig = gVerylow := by
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 89) hpush224
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have h224 : (224 : B256).toNat = 224 := by
    decide +kernel
  have hselector' :
      Sevm.dataWord sevm 0 >>> (224 : B256).toNat =
        getDepositRootSelector := by
    rw [h224]
    exact hselector
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .shr)
      (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := G + 86)
      (v := getDepositRootSelector)
      (by rintro ⟨⟩) rfl rfl hselector'
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach]
  simpa only [Devm.memory_setMach, prepend] using hroot

def getDepositRootRouteGas : Nat := 114

/-- Exact compiled selector-tree cost through the root nonpayable wrapper. -/
theorem getDepositRoot_route_runCompiledTo
    {sevm : Sevm} {base : Devm} {out : Execution} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hbody : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩)
      (nonpayableEndpoint getDepositRootEndpoint) out) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, K + getDepositRootRouteGas⟩)
      runtime out := by
  have hleaf :=
    getDepositRootLeafRoute_runCompiledTo (G := K) hbody
  have hinner :=
    getDepositRootInnerRoute_runCompiledTo (G := K) hleaf
  have hmiddle :=
    getDepositRootMiddleRoute_runCompiledTo (G := K) hinner
  have hroot :=
    getDepositRootRootRoute_runCompiledTo (G := K) hmiddle
  have hmain :=
    getDepositRootMainRoute_runCompiledTo (G := K) hselector hroot
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, K + 113⟩)
    (G := K + 113) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, getDepositRootRouteGas,
      gJumpdest]
  · unfold runtime
    func_run (1) []
    exact Func.runCompiledTo_branch_succ
      (w := sevm.data.length.toB256) (s := []) (G := K + 97)
      hnonempty rfl
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)
      (by
        simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest]
        omega)
      (by
        simpa only [runtime, Devm.setMach_setMach, Devm.memory_setMach]
          using hmain)

/-- Successful specialization of the exact public root route. -/
theorem getDepositRoot_route_runCompiled
    {sevm : Sevm} {base post : Devm} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hbody : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩)
      (nonpayableEndpoint getDepositRootEndpoint) post) :
    Prog.RunCompiled sevm
      (base.setMach ⟨[], Mem.empty, K + getDepositRootRouteGas⟩)
      runtime post := by
  rcases getDepositRoot_route_runCompiledTo hnonempty hselector
      (Func.RunCompiledTo.of_runCompiled hbody) with
    ⟨mid, hburn, hmain⟩
  exact ⟨mid, hburn, Func.RunCompiled.of_runCompiledTo_ok hmain⟩

def getDepositRootRuntimeGas
    (sevm : Sevm) (base : Devm) (stor : Stor) (count : Nat) : Nat :=
  416 +
    rootLoopGas sevm.currentTarget stor 32
      (rootInitialLoopState
        (afterSload sevm base depositCountSlot)
        (Nat.toB256 count)) +
    getDepositRootPrefixGas sevm base +
    nonpayableEndpointZeroGas +
    getDepositRootRouteGas

def getDepositRootNonzeroValueRuntimeGas : Nat := 134

/-- A value-carrying root query is rejected before the endpoint reads the
count slot or invokes SHA-256. -/
theorem getDepositRoot_nonzero_value_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hvalue : sevm.value ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hcode : sevm.code.toList = code) :
    Prog.RunCompiledTo sevm
      (base.setMach
        ⟨[], Mem.empty, G + getDepositRootNonzeroValueRuntimeGas⟩)
      runtime
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
    some sevm.code.toList = Prog.compile runtime := by
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  have hbody := nonpayableEndpoint_nonzero_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := routeBase) (G := G)
    (body := getDepositRootEndpoint) hvalue
    (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
  have hroute := getDepositRoot_route_runCompiledTo
    (base := base) (K := G + nonpayableEndpointRevertGas)
    hnonempty hselector (by
      simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using hbody)
  constructor
  · have hboundary :
        G + nonpayableEndpointRevertGas + getDepositRootRouteGas =
          G + getDepositRootNonzeroValueRuntimeGas := by
      simp only [nonpayableEndpointRevertGas, getDepositRootRouteGas,
        getDepositRootNonzeroValueRuntimeGas]
    simpa only [hboundary] using hroute
  · rw [hcode, code_compile]

end Blanc.BeaconDeposit
