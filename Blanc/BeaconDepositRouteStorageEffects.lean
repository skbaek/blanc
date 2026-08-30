import Blanc.BeaconDepositEffects
import Blanc.ForwardStorageEffects

/-! # Exact retained effects along the Beacon deposit selector route -/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

private theorem exactDepositLeafRoute_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩) depositEndpoint out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[depositSelector], Mem.empty, G + 20⟩)
      depositLeafRoute out effects := by
  unfold depositLeafRoute
  have hpushCost : pushCost depositSelector.toBytes.sig = gVerylow := by
    rw [depositSelector_eq]
    decide +kernel
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 17) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary (r := .eq) (f := B256.eqCheck)
      (cost := gVerylow) (G := G + 14) (v := 1)
      (by rintro ⟨⟩) rfl rfl (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach]
  exact Func.StorageEffectRun.succ
    (word := (1 : B256)) (by decide)
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using
        Devm.popBurnBy_setMach
          (devm := base.setMach ⟨[(1 : B256)], Mem.empty, G + 14⟩)
          (G := G) rfl
          (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh,
            gJumpdest]))
    hbody

private theorem exactDepositMiddleDispatch_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hleaf : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[depositSelector], Mem.empty, G + 20⟩)
      depositLeafRoute out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[depositSelector], Mem.empty, G + 43⟩)
      depositMiddleDispatch out effects := by
  unfold depositMiddleDispatch
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_dup
      (n := 0) (w := depositSelector) (G := G + 40) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost :
      pushCost getDepositCountSelector.toBytes.sig = gVerylow := by
    rw [getDepositCountSelector_eq]
    decide +kernel
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 37) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 34) (v := 1)
      (by rintro ⟨⟩) rfl rfl
      (by
        rw [depositSelector_eq, getDepositCountSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach]
  exact Func.StorageEffectRun.succ
    (word := (1 : B256)) (by decide)
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using
        Devm.popBurnBy_setMach
          (devm := base.setMach
            ⟨[(1 : B256), depositSelector], Mem.empty, G + 34⟩)
          (G := G + 20) rfl
          (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh,
            gJumpdest]))
    (by simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hleaf)

private theorem exactDepositRootDispatch_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hmiddle : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[depositSelector], Mem.empty, G + 43⟩)
      depositMiddleDispatch out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[depositSelector], Mem.empty, G + 65⟩)
      depositRootDispatch out effects := by
  unfold depositRootDispatch
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_dup
      (n := 0) (w := depositSelector) (G := G + 62) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hpushCost : pushCost depositSelector.toBytes.sig = gVerylow := by
    rw [depositSelector_eq]
    decide +kernel
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 59) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 56) (v := 0)
      (by rintro ⟨⟩) rfl rfl (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
  simp only [Devm.setMach_setMach]
  exact Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using
        Devm.popBurnBy_setMach
          (devm := base.setMach
            ⟨[(0 : B256), depositSelector], Mem.empty, G + 56⟩)
          (G := G + 43) rfl
          (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
    (by simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hmiddle)

private theorem exactDepositMainRoute_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {effects : List (Adr × B256 × B256)} {G : Nat}
    (hselector : Sevm.selector sevm = depositSelector)
    (hroot : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[depositSelector], Mem.empty, G + 65⟩)
      depositRootDispatch out effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], Mem.empty, G + 76⟩)
      (Func.main tree) out effects := by
  rw [depositMainRoute_eq]
  unfold depositMainRoute fsig shiftRight cdl
  have h224 : (224 : B256).toNat = 224 := by
    decide +kernel
  have hselector' :
      Sevm.dataWord sevm 0 >>> (224 : B256).toNat = depositSelector := by
    rw [h224]
    exact hselector
  storage_effect_run (4) [depositSelector]
  simpa only [Devm.setMach_setMach, Devm.memory_setMach, prepend,
      show G + 76 - 11 = G + 65 by omega] using hroot

/-- Exact-effect analogue of `deposit_route_runCompiledTo`.  The selector
prefix is childless and storage-neutral, so it preserves the endpoint's
retained effect list exactly while exposing the runtime entry burn needed by
the execution bridge. -/
theorem deposit_route_storageEffectRun
    {sevm : Sevm} {base : Devm} {out : Execution}
    {effects : List (Adr × B256 × B256)} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = depositSelector)
    (hbody : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩) depositEndpoint out effects) :
    ∃ mid : Devm,
      Devm.BurnBy gJumpdest
        (base.setMach ⟨[], Mem.empty, K + depositRouteGas⟩) mid ∧
      Func.StorageEffectRun (runtime.main :: runtime.aux)
        sevm mid runtime.main out effects := by
  have hleaf :=
    exactDepositLeafRoute_storageEffectRun (G := K) hbody
  have hmiddle :=
    exactDepositMiddleDispatch_storageEffectRun (G := K) hleaf
  have hroot :=
    exactDepositRootDispatch_storageEffectRun (G := K) hmiddle
  have hmain :=
    exactDepositMainRoute_storageEffectRun (G := K) hselector hroot
  let pre := base.setMach ⟨[], Mem.empty, K + depositRouteGas⟩
  let mid := base.setMach ⟨[], Mem.empty, K + 92⟩
  let afterSize := base.setMach
    ⟨[sevm.data.length.toB256], Mem.empty, K + 90⟩
  let afterBranch := base.setMach ⟨[], Mem.empty, K + 76⟩
  have hsize : Ninst.RunCompiled sevm mid calldatasize afterSize := by
    simpa only [mid, afterSize, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm) (devm := mid)
        (r := .calldatasize) (x := Nat.toB256 sevm.data.length)
        (cost := gBase) (G := K + 90) (by rintro ⟨⟩) rfl
        (by simp only [mid, Devm.gasLeft_setMach, gBase])
        (by simp only [mid, Devm.stack_setMach, List.length_nil]; omega))
  have hroom : afterSize.stack.length < 1024 := by
    simp only [afterSize, Devm.stack_setMach, List.length_cons,
      List.length_nil]
    omega
  have hpop : Devm.PopBurnBy [sevm.data.length.toB256]
      (gVerylow + gHigh + gJumpdest) afterSize afterBranch := by
    simpa only [afterSize, afterBranch, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := afterSize) (G := K + 76)
        (by simp only [afterSize, Devm.stack_setMach])
        (by simp only [afterSize, Devm.gasLeft_setMach,
          gVerylow, gHigh, gJumpdest])
  have hbranch : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm afterSize
      (Func.main tree <?> Func.rev) out effects :=
    .succ hnonempty hroom hpop (by
      simpa only [afterBranch] using hmain)
  have hmainEffects : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm mid runtime.main out effects := by
    unfold runtime
    exact Func.StorageEffectRun.next_effectNeutral hsize
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      hbranch
  have hentry : Devm.BurnBy gJumpdest pre mid := by
    simpa only [pre, mid, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, depositRouteGas, gJumpdest] using
      Devm.burnBy_setMach_gas
        (devm := pre) (G := K + 92)
        (by simp only [pre, Devm.gasLeft_setMach, depositRouteGas])
  exact ⟨mid, hentry, hmainEffects⟩

/-- Translate an exact-effect deposit endpoint walk through the public selector
route to an actual bytecode execution with the same retained chronology. -/
theorem deposit_route_retainedStorageEffectTriples
    {sevm : Sevm} {base : Devm} {out : Execution}
    {effects : List (Adr × B256 × B256)} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = depositSelector)
    (hbody : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩) depositEndpoint out effects)
    (hcommits : Execution.commits out = true)
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, K + depositRouteGas⟩) out,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, K + depositRouteGas⟩) runtime out ∧
      Exec.retainedStorageEffectTriples execution = effects ∧
      some sevm.code.toList = Prog.compile runtime := by
  obtain ⟨mid, hentry, hmain⟩ :=
    deposit_route_storageEffectRun hnonempty hselector hbody
  have hprogram : Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, K + depositRouteGas⟩) runtime out :=
    ⟨mid, hentry, hmain.run⟩
  have hcompiled : some sevm.code.toList = Prog.compile runtime := by
    rw [hcode, code_compile]
  obtain ⟨execution, heffects⟩ :=
    Prog.exists_exec_retainedStorageEffectTriples
      hentry hmain.path hcommits hcompiled
  exact ⟨execution, hprogram, heffects, hcompiled⟩

end Blanc.BeaconDeposit
