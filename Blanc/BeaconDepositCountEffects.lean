import Blanc.BeaconDepositEffects
import Blanc.BeaconDepositMemory

/-!
# Beacon deposit count effects

Exact memory, endpoint, selector-route, and public compiled semantics for
`get_deposit_count()`.  Kept separate from the other effect families so each
compiled walk remains an independently measurable proof unit.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst
/-! ## Exact deposit-count endpoint -/

def getDepositCountEndpointWarmGas : Nat := 253
def getDepositCountEndpointColdGas : Nat := 2253

private lemma count_addAccessedStorageKey_setMach_setMach
    {base : Devm} {target : Adr} {key : B256} {mach mach' : Mach} :
    (addAccessedStorageKey (base.setMach mach) target key).setMach mach' =
      (addAccessedStorageKey base target key).setMach mach' := rfl

/-- A warm count read returns the canonical ABI dynamic-`bytes` image. -/
theorem getDepositCountEndpoint_warm_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (word : B256) (G : Nat)
    (hwarm :
      ⟨sevm.currentTarget, depositCountSlot⟩ ∈ base.accessedStorageKeys)
    (hvalue :
      base.getStorVal sevm.currentTarget depositCountSlot = word) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], Mem.empty, G + getDepositCountEndpointWarmGas⟩)
      getDepositCountEndpoint
      ((base.setMach
        ⟨[], getDepositCountResultMemory word, G⟩).withOutput
          (abiDynamicBytesReturn (le64 word.toNat))) := by
  have hreturn := getDepositCountReturn_runCompiled
    (fs := fs) (sevm := sevm) (base := base) word G
  have hstore := storeLe64At64_runCompiled
    (fs := fs) (sevm := sevm) (base := base)
    (word := word) (G := G + 5) hreturn
  have hsuffix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], getDepositCountHeaderMemory, G + 219⟩)
      (pushB256 depositCountSlot ::: sload :::
        storeLe64At 64 +++ returnMemoryRange 0 96)
      ((base.setMach
        ⟨[], getDepositCountResultMemory word, G⟩).withOutput
          (abiDynamicBytesReturn (le64 word.toNat))) := by
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_pushB256
        (w := depositCountSlot) (c := gVerylow) (G := G + 216)
        (by decide +kernel)
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [Devm.stack_setMach, List.length_nil]; omega)
    · simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.RunCompiled.next
      · exact Ninst.runCompiled_sload_warm
          (k := depositCountSlot) (v := word) (s := [])
          (G := G + 116) rfl hwarm hvalue
          (by simp only [Devm.gasLeft_setMach, gasWarmAccess])
          (by simp only [List.length_nil]; omega)
      · simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hstore
  unfold getDepositCountEndpoint getDepositCountEndpointWarmGas
  exact getDepositCountHeader_runCompiled hsuffix

/-- A cold count read adds exactly its storage key to the accessed set and
returns the same canonical image. -/
theorem getDepositCountEndpoint_cold_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (word : B256) (G : Nat)
    (hcold :
      ⟨sevm.currentTarget, depositCountSlot⟩ ∉ base.accessedStorageKeys)
    (hvalue :
      base.getStorVal sevm.currentTarget depositCountSlot = word) :
    let moved :=
      addAccessedStorageKey base sevm.currentTarget depositCountSlot
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], Mem.empty, G + getDepositCountEndpointColdGas⟩)
      getDepositCountEndpoint
      ((moved.setMach
        ⟨[], getDepositCountResultMemory word, G⟩).withOutput
          (abiDynamicBytesReturn (le64 word.toNat))) := by
  let moved :=
    addAccessedStorageKey base sevm.currentTarget depositCountSlot
  have hreturn := getDepositCountReturn_runCompiled
    (fs := fs) (sevm := sevm) (base := moved) word G
  have hstore := storeLe64At64_runCompiled
    (fs := fs) (sevm := sevm) (base := moved)
    (word := word) (G := G + 5) hreturn
  have hsuffix : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], getDepositCountHeaderMemory, G + 2219⟩)
      (pushB256 depositCountSlot ::: sload :::
        storeLe64At 64 +++ returnMemoryRange 0 96)
      ((moved.setMach
        ⟨[], getDepositCountResultMemory word, G⟩).withOutput
          (abiDynamicBytesReturn (le64 word.toNat))) := by
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_pushB256
        (w := depositCountSlot) (c := gVerylow) (G := G + 2216)
        (by decide +kernel)
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [Devm.stack_setMach, List.length_nil]; omega)
    · simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.RunCompiled.next
      · exact Ninst.runCompiled_sload_cold
          (k := depositCountSlot) (v := word) (s := [])
          (G := G + 116) rfl hcold hvalue
          (by simp only [Devm.gasLeft_setMach, gasColdSload])
          (by simp only [List.length_nil]; omega)
      · simpa only [moved,
          count_addAccessedStorageKey_setMach_setMach,
          Devm.setMach_setMach, Devm.memory_setMach] using hstore
  unfold getDepositCountEndpoint getDepositCountEndpointColdGas
  exact getDepositCountHeader_runCompiled hsuffix

/-! ## Exact deposit-count selector route -/

private def getDepositCountLeafRoute : Func :=
  pushB256 getDepositCountSelector ::: eq :::
    ((nonpayableEndpoint getDepositCountEndpoint) <?> Func.rev)

private def getDepositCountInnerDispatch : Func :=
  dup 0 ::: pushB256 getDepositRootSelector ::: gt :::
    (getDepositCountLeafRoute <?>
      dispatch
        (.leaf getDepositRootSelector
          (nonpayableEndpoint getDepositRootEndpoint)))

private def getDepositCountMiddleDispatch : Func :=
  dup 0 ::: pushB256 getDepositCountSelector ::: gt :::
    (dispatch (.leaf depositSelector depositEndpoint) <?>
      getDepositCountInnerDispatch)

private def getDepositCountRootDispatch : Func :=
  dup 0 ::: pushB256 depositSelector ::: gt :::
    (dispatch
      (.leaf supportsInterfaceSelector
        (nonpayableEndpoint supportsInterfaceEndpoint)) <?>
      getDepositCountMiddleDispatch)

private def getDepositCountMainRoute : Func :=
  fsig +++ getDepositCountRootDispatch

private theorem getDepositCountMainRoute_eq :
    Func.main tree = getDepositCountMainRoute := by
  rfl

private theorem getDepositCountLeafRoute_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hbody : Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayableEndpoint getDepositCountEndpoint) post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 20⟩)
      getDepositCountLeafRoute post := by
  unfold getDepositCountLeafRoute
  have hpushCost :
      pushCost getDepositCountSelector.toBytes.sig = gVerylow := by
    rw [getDepositCountSelector_eq]
    decide +kernel
  have hpushGas :
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 20⟩).gasLeft =
          G + 17 + gVerylow := by
    simp only [Devm.gasLeft_setMach, gVerylow]
  have hpushRoom :
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 20⟩).stack.length <
          1024 := by
    simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 hpushCost hpushGas hpushRoom) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have heqGas : G + 17 = G + 14 + gVerylow := by
    simp only [gVerylow]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_binary (r := .eq) (f := B256.eqCheck)
      (cost := gVerylow) (G := G + 14) (v := 1)
      (by rintro ⟨⟩) rfl rfl (by decide +kernel) heqGas
      (by decide)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiled_branch_succ
    (w := (1 : B256)) (s := []) (G := G)
    (by decide) rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    hbody

private theorem getDepositCountInnerDispatch_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hleaf : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 20⟩)
      getDepositCountLeafRoute post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 43⟩)
      getDepositCountInnerDispatch post := by
  unfold getDepositCountInnerDispatch
  refine Func.RunCompiled.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositCountSelector) (G := G + 40) rfl
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
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (G := G + 37) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 34) (v := 1)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [getDepositCountSelector_eq, getDepositRootSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiled_branch_succ
    (w := (1 : B256)) (s := [getDepositCountSelector])
    (G := G + 20)
    (by decide) rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hleaf)

private theorem getDepositCountMiddleDispatch_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hinner : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 43⟩)
      getDepositCountInnerDispatch post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 65⟩)
      getDepositCountMiddleDispatch post := by
  unfold getDepositCountMiddleDispatch
  refine Func.RunCompiled.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositCountSelector) (G := G + 62) rfl
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
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (G := G + 59) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 56) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [getDepositCountSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiled_branch_zero
    (s := [getDepositCountSelector]) (G := G + 43)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hinner)

private theorem getDepositCountRootDispatch_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hmiddle : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 65⟩)
      getDepositCountMiddleDispatch post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 87⟩)
      getDepositCountRootDispatch post := by
  unfold getDepositCountRootDispatch
  refine Func.RunCompiled.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositCountSelector) (G := G + 84) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost : pushCost depositSelector.toBytes.sig = gVerylow := by
    rw [depositSelector_eq]
    decide +kernel
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (G := G + 81) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 78) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [getDepositCountSelector_eq, depositSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiled_branch_zero
    (s := [getDepositCountSelector]) (G := G + 65)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hmiddle)

private theorem getDepositCountMainRoute_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hselector : Sevm.selector sevm = getDepositCountSelector)
    (hroot : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 87⟩)
      getDepositCountRootDispatch post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + 98⟩)
      (Func.main tree) post := by
  rw [getDepositCountMainRoute_eq]
  unfold getDepositCountMainRoute fsig shiftRight cdl
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (c := gBase) (G := G + 96)
      pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_calldataload
      (v := Sevm.dataWord sevm 0) (G := G + 93) rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  have hpush224 : pushCost (224 : B256).toBytes.sig = gVerylow := by
    decide +kernel
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (G := G + 90) hpush224
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
        getDepositCountSelector := by
    rw [h224]
    exact hselector
  refine Func.RunCompiled.next
    (Ninst.runCompiled_binary (r := .shr)
      (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := G + 87)
      (v := getDepositCountSelector)
      (by rintro ⟨⟩) rfl rfl hselector'
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach]
  simpa only [Devm.memory_setMach, prepend] using hroot

private theorem getDepositCountLeafRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayableEndpoint getDepositCountEndpoint) out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 20⟩)
      getDepositCountLeafRoute out := by
  unfold getDepositCountLeafRoute
  have hpushCost :
      pushCost getDepositCountSelector.toBytes.sig = gVerylow := by
    rw [getDepositCountSelector_eq]
    decide +kernel
  have hpushGas :
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 20⟩).gasLeft =
          G + 17 + gVerylow := by
    simp only [Devm.gasLeft_setMach, gVerylow]
  have hpushRoom :
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 20⟩).stack.length <
          1024 := by
    simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 hpushCost hpushGas hpushRoom) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have heqGas : G + 17 = G + 14 + gVerylow := by
    simp only [gVerylow]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .eq) (f := B256.eqCheck)
      (cost := gVerylow) (G := G + 14) (v := 1)
      (by rintro ⟨⟩) rfl rfl (by decide +kernel) heqGas
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

private theorem getDepositCountInnerDispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hleaf : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 20⟩)
      getDepositCountLeafRoute out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 43⟩)
      getDepositCountInnerDispatch out := by
  unfold getDepositCountInnerDispatch
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositCountSelector) (G := G + 40) rfl
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
    (Ninst.runCompiled_pushB256 (G := G + 37) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 34) (v := 1)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [getDepositCountSelector_eq, getDepositRootSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_succ
    (w := (1 : B256)) (s := [getDepositCountSelector])
    (G := G + 20)
    (by decide) rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hleaf)

private theorem getDepositCountMiddleDispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hinner : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 43⟩)
      getDepositCountInnerDispatch out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 65⟩)
      getDepositCountMiddleDispatch out := by
  unfold getDepositCountMiddleDispatch
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositCountSelector) (G := G + 62) rfl
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
    (Ninst.runCompiled_pushB256 (G := G + 59) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 56) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [getDepositCountSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_zero
    (s := [getDepositCountSelector]) (G := G + 43)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hinner)

private theorem getDepositCountRootDispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hmiddle : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 65⟩)
      getDepositCountMiddleDispatch out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 87⟩)
      getDepositCountRootDispatch out := by
  unfold getDepositCountRootDispatch
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := getDepositCountSelector) (G := G + 84) rfl
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
    (Ninst.runCompiled_pushB256 (G := G + 81) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 78) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [getDepositCountSelector_eq, depositSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_zero
    (s := [getDepositCountSelector]) (G := G + 65)
    rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hmiddle)

private theorem getDepositCountMainRoute_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hselector : Sevm.selector sevm = getDepositCountSelector)
    (hroot : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[getDepositCountSelector], Mem.empty, G + 87⟩)
      getDepositCountRootDispatch out) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 98⟩)
      (Func.main tree) out := by
  rw [getDepositCountMainRoute_eq]
  unfold getDepositCountMainRoute fsig shiftRight cdl
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (c := gBase) (G := G + 96)
      pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_calldataload
      (v := Sevm.dataWord sevm 0) (G := G + 93) rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  have hpush224 : pushCost (224 : B256).toBytes.sig = gVerylow := by
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 90) hpush224
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
        getDepositCountSelector := by
    rw [h224]
    exact hselector
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .shr)
      (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := G + 87)
      (v := getDepositCountSelector)
      (by rintro ⟨⟩) rfl rfl hselector'
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach]
  simpa only [Devm.memory_setMach, prepend] using hroot

def getDepositCountRouteGas : Nat := 115

theorem getDepositCount_route_runCompiled
    {sevm : Sevm} {base post : Devm} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = getDepositCountSelector)
    (hbody : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩)
      (nonpayableEndpoint getDepositCountEndpoint) post) :
    Prog.RunCompiled sevm
      (base.setMach ⟨[], Mem.empty, K + getDepositCountRouteGas⟩)
      runtime post := by
  have hleaf :=
    getDepositCountLeafRoute_runCompiled (G := K) hbody
  have hinner :=
    getDepositCountInnerDispatch_runCompiled (G := K) hleaf
  have hmiddle :=
    getDepositCountMiddleDispatch_runCompiled (G := K) hinner
  have hroot :=
    getDepositCountRootDispatch_runCompiled (G := K) hmiddle
  have hmain :=
    getDepositCountMainRoute_runCompiled (G := K) hselector hroot
  refine Prog.runCompiled_intro
    (mid := base.setMach ⟨[], Mem.empty, K + 114⟩)
    (G := K + 114) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, getDepositCountRouteGas,
      gJumpdest]
  · unfold runtime
    func_run (1) []
    exact Func.runCompiled_branch_succ
      (w := sevm.data.length.toB256) (s := []) (G := K + 98)
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

theorem getDepositCount_route_runCompiledTo
    {sevm : Sevm} {base : Devm} {out : Execution} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = getDepositCountSelector)
    (hbody : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩)
      (nonpayableEndpoint getDepositCountEndpoint) out) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, K + getDepositCountRouteGas⟩)
      runtime out := by
  have hleaf :=
    getDepositCountLeafRoute_runCompiledTo (G := K) hbody
  have hinner :=
    getDepositCountInnerDispatch_runCompiledTo (G := K) hleaf
  have hmiddle :=
    getDepositCountMiddleDispatch_runCompiledTo (G := K) hinner
  have hroot :=
    getDepositCountRootDispatch_runCompiledTo (G := K) hmiddle
  have hmain :=
    getDepositCountMainRoute_runCompiledTo (G := K) hselector hroot
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, K + 114⟩)
    (G := K + 114) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, getDepositCountRouteGas,
      gJumpdest]
  · unfold runtime
    func_run (1) []
    exact Func.runCompiledTo_branch_succ
      (w := sevm.data.length.toB256) (s := []) (G := K + 98)
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

def getDepositCountWarmRuntimeGas : Nat := 383
def getDepositCountColdRuntimeGas : Nat := 2383

/-- The exact compiled public count route when the count slot is warm. -/
theorem getDepositCount_warm_runCompiled
    (sevm : Sevm) (base : Devm) (word : B256) (G : Nat)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = getDepositCountSelector)
    (hwarm :
      ⟨sevm.currentTarget, depositCountSlot⟩ ∈ base.accessedStorageKeys)
    (hstorage :
      base.getStorVal sevm.currentTarget depositCountSlot = word)
    (hcode : sevm.code.toList = code) :
    Prog.RunCompiled sevm
      (base.setMach
        ⟨[], Mem.empty, G + getDepositCountWarmRuntimeGas⟩)
      runtime
      ((base.setMach
        ⟨[], getDepositCountResultMemory word, G⟩).withOutput
          (abiDynamicBytesReturn (le64 word.toNat))) ∧
    some sevm.code.toList = Prog.compile runtime := by
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  have hendpoint := getDepositCountEndpoint_warm_runCompiled
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := routeBase) word G
    (by
      change ⟨sevm.currentTarget, depositCountSlot⟩ ∈
        base.accessedStorageKeys
      exact hwarm)
    (by simpa only [routeBase, Devm.getStorVal_setMach] using hstorage)
  have hwrapped :
      Func.RunCompiled (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 268⟩)
        (nonpayableEndpoint getDepositCountEndpoint)
        ((base.setMach
          ⟨[], getDepositCountResultMemory word, G⟩).withOutput
            (abiDynamicBytesReturn (le64 word.toNat))) := by
    have hrun := nonpayableEndpoint_zero_runCompiled
      (fs := runtime.main :: runtime.aux) (sevm := sevm)
      (base := routeBase)
      (post :=
        (base.setMach
          ⟨[], getDepositCountResultMemory word, G⟩).withOutput
            (abiDynamicBytesReturn (le64 word.toNat)))
      (G := G + getDepositCountEndpointWarmGas)
      (body := getDepositCountEndpoint) hvalue
      (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
      (by
        simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hendpoint)
    have hboundary :
        G + getDepositCountEndpointWarmGas + nonpayableEndpointZeroGas =
          G + 268 := by
      simp only [getDepositCountEndpointWarmGas,
        nonpayableEndpointZeroGas]
    simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach, hboundary] using hrun
  have hlengthWordNe : sevm.data.length.toB256 ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hdataBound] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  constructor
  · have hroute := getDepositCount_route_runCompiled
      (base := base) (K := G + 268)
      hlengthWordNe hselector hwrapped
    have hboundary :
        G + 268 + getDepositCountRouteGas =
          G + getDepositCountWarmRuntimeGas := by
      simp only [getDepositCountRouteGas, getDepositCountWarmRuntimeGas]
    simpa only [hboundary] using hroute
  · rw [hcode, code_compile]

/-- The exact compiled public count route when the count slot is cold. -/
theorem getDepositCount_cold_runCompiled
    (sevm : Sevm) (base : Devm) (word : B256) (G : Nat)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = getDepositCountSelector)
    (hcold :
      ⟨sevm.currentTarget, depositCountSlot⟩ ∉ base.accessedStorageKeys)
    (hstorage :
      base.getStorVal sevm.currentTarget depositCountSlot = word)
    (hcode : sevm.code.toList = code) :
    let moved :=
      addAccessedStorageKey base sevm.currentTarget depositCountSlot
    Prog.RunCompiled sevm
      (base.setMach
        ⟨[], Mem.empty, G + getDepositCountColdRuntimeGas⟩)
      runtime
      ((moved.setMach
        ⟨[], getDepositCountResultMemory word, G⟩).withOutput
          (abiDynamicBytesReturn (le64 word.toNat))) ∧
    some sevm.code.toList = Prog.compile runtime := by
  let moved :=
    addAccessedStorageKey base sevm.currentTarget depositCountSlot
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  have hendpoint := getDepositCountEndpoint_cold_runCompiled
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := routeBase) word G
    (by
      change ⟨sevm.currentTarget, depositCountSlot⟩ ∉
        base.accessedStorageKeys
      exact hcold)
    (by simpa only [routeBase, Devm.getStorVal_setMach] using hstorage)
  have hwrapped :
      Func.RunCompiled (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 2268⟩)
        (nonpayableEndpoint getDepositCountEndpoint)
        ((moved.setMach
          ⟨[], getDepositCountResultMemory word, G⟩).withOutput
            (abiDynamicBytesReturn (le64 word.toNat))) := by
    have hrun := nonpayableEndpoint_zero_runCompiled
      (fs := runtime.main :: runtime.aux) (sevm := sevm)
      (base := routeBase)
      (post :=
        (moved.setMach
          ⟨[], getDepositCountResultMemory word, G⟩).withOutput
            (abiDynamicBytesReturn (le64 word.toNat)))
      (G := G + getDepositCountEndpointColdGas)
      (body := getDepositCountEndpoint) hvalue
      (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
      (by
        simpa only [routeBase, moved,
          count_addAccessedStorageKey_setMach_setMach,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hendpoint)
    have hboundary :
        G + getDepositCountEndpointColdGas + nonpayableEndpointZeroGas =
          G + 2268 := by
      simp only [getDepositCountEndpointColdGas,
        nonpayableEndpointZeroGas]
    simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach, hboundary] using hrun
  have hlengthWordNe : sevm.data.length.toB256 ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hdataBound] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  constructor
  · have hroute := getDepositCount_route_runCompiled
      (base := base) (K := G + 2268)
      hlengthWordNe hselector hwrapped
    have hboundary :
        G + 2268 + getDepositCountRouteGas =
          G + getDepositCountColdRuntimeGas := by
      simp only [getDepositCountRouteGas, getDepositCountColdRuntimeGas]
    simpa only [hboundary] using hroute
  · rw [hcode, code_compile]

def getDepositCountNonzeroValueRuntimeGas : Nat := 135

/-- A value-carrying count query is rejected before the endpoint reads the
count slot. -/
theorem getDepositCount_nonzero_value_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hvalue : sevm.value ≠ 0)
    (hselector : Sevm.selector sevm = getDepositCountSelector)
    (hcode : sevm.code.toList = code) :
    Prog.RunCompiledTo sevm
      (base.setMach
        ⟨[], Mem.empty, G + getDepositCountNonzeroValueRuntimeGas⟩)
      runtime
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
    some sevm.code.toList = Prog.compile runtime := by
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  have hbody := nonpayableEndpoint_nonzero_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := routeBase) (G := G)
    (body := getDepositCountEndpoint) hvalue
    (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
  have hroute := getDepositCount_route_runCompiledTo
    (base := base) (K := G + nonpayableEndpointRevertGas)
    hnonempty hselector (by
      simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using hbody)
  constructor
  · have hboundary :
        G + nonpayableEndpointRevertGas + getDepositCountRouteGas =
          G + getDepositCountNonzeroValueRuntimeGas := by
      simp only [nonpayableEndpointRevertGas, getDepositCountRouteGas,
        getDepositCountNonzeroValueRuntimeGas]
    simpa only [hboundary] using hroute
  · rw [hcode, code_compile]

end Blanc.BeaconDeposit
