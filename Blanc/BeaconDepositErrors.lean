import Blanc.BeaconDepositAbi
import Blanc.BeaconDepositEffects
import Blanc.BeaconDepositErrorModel
import Blanc.ForwardNoRawSstore

/-!
# Beacon deposit compiled error routes

Exact public-route witnesses for malformed ABI input, selector misses, and the
eight reachable source-model errors.  Every public revert theorem in this file
is paired with raw-chronology `SSTORE` freedom; rollback and an empty retained
write list are consequences, never substitutes for that path certificate.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-! ## Empty calldata -/

/-- Exact public gas for the runtime's empty-calldata fallback. -/
def emptyCalldataRuntimeGas : Nat := 20

/-- Empty calldata selects the runtime's top-level `Func.rev` before selector
extraction.  The exhibited execution is raw-chronology `SSTORE`-free, hence
also has no retained storage writes. -/
theorem empty_calldata_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hdata : sevm.data = [])
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + emptyCalldataRuntimeGas⟩)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + emptyCalldataRuntimeGas⟩)
        runtime
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      some sevm.code.toList = Prog.compile runtime := by
  let pre :=
    base.setMach ⟨[], Mem.empty, G + emptyCalldataRuntimeGas⟩
  let mid := base.setMach ⟨[], Mem.empty, G + 19⟩
  let afterSize := base.setMach ⟨[(0 : B256)], Mem.empty, G + 17⟩
  let afterBranch := base.setMach ⟨[], Mem.empty, G + 4⟩
  let out : Execution :=
    .error (.revert,
      (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])
  have hrev : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      afterBranch Func.rev out := by
    simpa only [afterBranch, out, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Func.runCompiledTo_rev_func
        (fs := runtime.main :: runtime.aux) (sevm := sevm)
        (devm := afterBranch) (G := G)
        (by simp only [afterBranch, Devm.gasLeft_setMach, gBase])
        (by simp only [afterBranch, Devm.stack_setMach,
          List.length_nil]; omega))
  have hrevSafe : Func.RunCompiledTo.NoRawSstorePath hrev := by
    exact Func.RunCompiledTo.NoRawSstorePath.of_execFree hrev
      (by simp [Func.rev, Ninst.pushB256, funcExecFree])
      (by simp [Func.rev, Ninst.pushB256, Func.LocalSstoreFree])
  have hbranch : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm afterSize
      (Func.main tree <?> Func.rev) out := by
    exact Func.runCompiledTo_branch_zero
      (devm := afterSize) (f := Func.rev) (g := Func.main tree)
      (s := []) (G := G + 4)
      (by simp only [afterSize, Devm.stack_setMach])
      (by simp only [afterSize, Devm.stack_setMach,
        List.length_cons, List.length_nil]; omega)
      (by simp only [afterSize, Devm.gasLeft_setMach,
        gVerylow, gHigh])
      (by simpa only [afterSize, afterBranch, Devm.setMach_setMach,
          Devm.memory_setMach] using hrev)
  have hbranchSafe : Func.RunCompiledTo.NoRawSstorePath hbranch := by
    have hroom : afterSize.stack.length < 1024 := by
      simp only [afterSize, Devm.stack_setMach, List.length_cons,
        List.length_nil]
      omega
    have hpop : Devm.PopBurnBy [0] (gVerylow + gHigh)
        afterSize afterBranch := by
      simpa only [afterSize, afterBranch, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using
        Devm.popBurnBy_setMach
          (devm := afterSize) (G := G + 4)
          (by simp only [afterSize, Devm.stack_setMach])
          (by simp only [afterSize, Devm.gasLeft_setMach,
            gVerylow, gHigh])
    exact .zero (room := hroom) (pop := hpop) (by
      simpa only [afterSize, afterBranch, Devm.setMach_setMach,
          Devm.memory_setMach] using hrevSafe)
  have hsize : Ninst.RunCompiled sevm mid calldatasize afterSize := by
    simpa only [hdata, mid, afterSize, List.length_nil,
        show Nat.toB256 0 = (0 : B256) by decide,
        Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm) (devm := mid)
        (r := .calldatasize) (x := Nat.toB256 sevm.data.length)
        (cost := gBase) (G := G + 17) (by rintro ⟨⟩) rfl
        (by simp only [mid, Devm.gasLeft_setMach, gBase])
        (by simp only [mid, Devm.stack_setMach, List.length_nil]; omega))
  have hmain : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      mid runtime.main out := by
    unfold runtime
    exact Func.RunCompiledTo.next hsize hbranch
  have hmainSafe : Func.RunCompiledTo.NoRawSstorePath hmain := by
    unfold runtime at hmain ⊢
    exact Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
      (instructionRun := hsize) (tail := hbranch)
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      hbranchSafe
  have hentryGas : pre.gasLeft = (G + 19) + gJumpdest := by
    simp only [pre, emptyCalldataRuntimeGas, Devm.gasLeft_setMach,
      gJumpdest]
  have hentry : Devm.BurnBy gJumpdest pre mid := by
    simpa only [pre, mid, Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Devm.burnBy_setMach_gas hentryGas
  have hprogram : Prog.RunCompiledTo sevm pre runtime out :=
    ⟨mid, hentry, hmain⟩
  have hcompiled : some sevm.code.toList = Prog.compile runtime := by
    rw [hcode, code_compile]
  obtain ⟨execution, executionSafe⟩ :=
    Prog.exists_exec_noRawSstore hentry hmain hmainSafe hcompiled
  refine ⟨execution, ?_, executionSafe,
    executionSafe.retainedStorageWrites_eq_nil, hcompiled⟩
  simpa only [pre, out] using hprogram

/-! ## Selector miss -/

/-- A stable selector outside the four-entry Beacon deposit ABI surface. -/
def noMatchSelector : B256 := 0xffffffff

/-- Exact public gas for the selected rightmost dispatcher miss. -/
def noMatchSelectorRuntimeGas : Nat := 117

theorem noMatchSelectorRuntimeGas_eq : noMatchSelectorRuntimeGas = 117 := by
  rfl

/-- The rightmost leaf rejects `noMatchSelector` and enters its inline empty
revert.  The paired certificate is indexed by the identical compiled walk. -/
private theorem noMatchLeaf_runCompiledTo_with_path
    {sevm : Sevm} {base : Devm} {G : Nat} :
    ∃ run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[noMatchSelector], Mem.empty, G + 23⟩)
        (dispatch (.leaf getDepositRootSelector
          (nonpayableEndpoint getDepositRootEndpoint)))
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Func.RunCompiledTo.NoRawSstorePath run := by
  let revPre := base.setMach ⟨[], Mem.empty, G + 4⟩
  let out : Execution :=
    .error (.revert,
      (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])
  have hrev : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      revPre Func.rev out := by
    simpa only [revPre, out, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      (Func.runCompiledTo_rev_func
        (fs := runtime.main :: runtime.aux) (sevm := sevm)
        (devm := revPre) (G := G)
        (by simp only [revPre, Devm.gasLeft_setMach, gBase])
        (by simp only [revPre, Devm.stack_setMach,
          List.length_nil]; omega))
  have hrevSafe : Func.RunCompiledTo.NoRawSstorePath hrev :=
    Func.RunCompiledTo.NoRawSstorePath.of_execFree hrev
      (by simp [Func.rev, Ninst.pushB256, funcExecFree])
      (by simp [Func.rev, Ninst.pushB256, Func.LocalSstoreFree])
  let branchPre :=
    base.setMach ⟨[(0 : B256)], Mem.empty, G + 17⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons,
      List.length_nil]
    omega
  have hbranchPop : Devm.PopBurnBy [0] (gVerylow + gHigh)
      branchPre revPre := by
    simpa only [branchPre, revPre, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := branchPre) (G := G + 4)
        (by simp only [branchPre, Devm.stack_setMach])
        (by simp only [branchPre, Devm.gasLeft_setMach,
          gVerylow, gHigh])
  let hbranch : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm branchPre
      (nonpayableEndpoint getDepositRootEndpoint <?> Func.rev) out :=
    .zero hbranchRoom hbranchPop hrev
  have hbranchSafe : Func.RunCompiledTo.NoRawSstorePath hbranch := by
    dsimp only [hbranch]
    exact .zero (room := hbranchRoom) (pop := hbranchPop) hrevSafe
  let afterPush := base.setMach
    ⟨[getDepositRootSelector, noMatchSelector], Mem.empty, G + 20⟩
  have hpushCost :
      pushCost getDepositRootSelector.toBytes.sig = gVerylow := by
    rw [getDepositRootSelector_eq]
    decide +kernel
  have hpush : Ninst.RunCompiled sevm
      (base.setMach ⟨[noMatchSelector], Mem.empty, G + 23⟩)
      (pushB256 getDepositRootSelector) afterPush := by
    simpa only [afterPush, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256
        (devm := base.setMach
          ⟨[noMatchSelector], Mem.empty, G + 23⟩)
        (w := getDepositRootSelector) (G := G + 20) hpushCost
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  have heq : Ninst.RunCompiled sevm afterPush eq branchPre := by
    exact Ninst.runCompiled_binary
      (r := .eq) (f := B256.eqCheck) (cost := gVerylow)
      (G := G + 17) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by rw [noMatchSelector, getDepositRootSelector_eq]; decide +kernel)
      (by simp only [afterPush, Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega)
  let run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[noMatchSelector], Mem.empty, G + 23⟩)
      (dispatch (.leaf getDepositRootSelector
        (nonpayableEndpoint getDepositRootEndpoint))) out := by
    unfold dispatch
    exact .next hpush (.next heq hbranch)
  refine ⟨run, ?_⟩
  exact Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
    (instructionRun := hpush)
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
    (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
      (instructionRun := heq)
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      hbranchSafe)

/-- The maximum selector falls through the count/root fork to the rightmost
leaf, preserving the leaf's raw-SSTORE certificate. -/
private theorem noMatchInnerDispatch_runCompiledTo_with_path
    {sevm : Sevm} {base : Devm} {G : Nat} :
    ∃ run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[noMatchSelector], Mem.empty, G + 45⟩)
        (dispatch
          (.fork
            (.leaf getDepositCountSelector
              (nonpayableEndpoint getDepositCountEndpoint))
            (.leaf getDepositRootSelector
              (nonpayableEndpoint getDepositRootEndpoint))))
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Func.RunCompiledTo.NoRawSstorePath run := by
  obtain ⟨hleaf, hleafSafe⟩ :=
    noMatchLeaf_runCompiledTo_with_path (sevm := sevm)
      (base := base) (G := G)
  let branchPre :=
    base.setMach ⟨[(0 : B256), noMatchSelector], Mem.empty, G + 36⟩
  let leafPre :=
    base.setMach ⟨[noMatchSelector], Mem.empty, G + 23⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons,
      List.length_nil]
    omega
  have hbranchPop : Devm.PopBurnBy [0] (gVerylow + gHigh)
      branchPre leafPre := by
    simpa only [branchPre, leafPre, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := branchPre) (G := G + 23)
        (by simp only [branchPre, Devm.stack_setMach])
        (by simp only [branchPre, Devm.gasLeft_setMach,
          gVerylow, gHigh])
  let hbranch : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm branchPre
      (dispatch
          (.leaf getDepositCountSelector
            (nonpayableEndpoint getDepositCountEndpoint)) <?>
        dispatch
          (.leaf getDepositRootSelector
            (nonpayableEndpoint getDepositRootEndpoint)))
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) :=
    .zero hbranchRoom hbranchPop (by
      simpa only [leafPre] using hleaf)
  have hbranchSafe : Func.RunCompiledTo.NoRawSstorePath hbranch := by
    dsimp only [hbranch]
    exact .zero (room := hbranchRoom) (pop := hbranchPop) (by
      simpa only [leafPre] using hleafSafe)
  let afterDup := base.setMach
    ⟨[noMatchSelector, noMatchSelector], Mem.empty, G + 42⟩
  have hdup : Ninst.RunCompiled sevm
      (base.setMach ⟨[noMatchSelector], Mem.empty, G + 45⟩)
      (dup 0) afterDup := by
    simpa only [afterDup, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      (Ninst.runCompiled_dup
        (devm := base.setMach
          ⟨[noMatchSelector], Mem.empty, G + 45⟩)
        (n := 0) (w := noMatchSelector) (G := G + 42) rfl
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  let afterPush := base.setMach
    ⟨[getDepositRootSelector, noMatchSelector, noMatchSelector],
      Mem.empty, G + 39⟩
  have hpushCost :
      pushCost getDepositRootSelector.toBytes.sig = gVerylow := by
    rw [getDepositRootSelector_eq]
    decide +kernel
  have hpush : Ninst.RunCompiled sevm afterDup
      (pushB256 getDepositRootSelector) afterPush := by
    simpa only [afterDup, afterPush, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (devm := afterDup)
        (w := getDepositRootSelector) (G := G + 39) hpushCost
        (by simp only [afterDup, Devm.gasLeft_setMach, gVerylow])
        (by simp only [afterDup, Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  have hgt : Ninst.RunCompiled sevm afterPush gt branchPre := by
    exact Ninst.runCompiled_binary
      (r := .gt) (f := B256.gtCheck) (cost := gVerylow)
      (G := G + 36) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by rw [noMatchSelector, getDepositRootSelector_eq]; decide +kernel)
      (by simp only [afterPush, Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega)
  let run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[noMatchSelector], Mem.empty, G + 45⟩)
      (dispatch
        (.fork
          (.leaf getDepositCountSelector
            (nonpayableEndpoint getDepositCountEndpoint))
          (.leaf getDepositRootSelector
            (nonpayableEndpoint getDepositRootEndpoint))))
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) := by
    unfold dispatch
    exact .next hdup (.next hpush (.next hgt hbranch))
  refine ⟨run, ?_⟩
  exact Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
    (instructionRun := hdup)
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
    (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
      (instructionRun := hpush)
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
        (instructionRun := hgt)
        (by intro impossible; cases impossible)
        (by intro operation impossible; cases impossible)
        hbranchSafe))

/-- The maximum selector also falls through the deposit/count pivot into the
right-hand count/root dispatcher. -/
private theorem noMatchMiddleDispatch_runCompiledTo_with_path
    {sevm : Sevm} {base : Devm} {G : Nat} :
    ∃ run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[noMatchSelector], Mem.empty, G + 67⟩)
        (dispatch
          (.fork
            (.leaf depositSelector depositEndpoint)
            (.fork
              (.leaf getDepositCountSelector
                (nonpayableEndpoint getDepositCountEndpoint))
              (.leaf getDepositRootSelector
                (nonpayableEndpoint getDepositRootEndpoint)))))
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Func.RunCompiledTo.NoRawSstorePath run := by
  obtain ⟨hinner, hinnerSafe⟩ :=
    noMatchInnerDispatch_runCompiledTo_with_path (sevm := sevm)
      (base := base) (G := G)
  let branchPre :=
    base.setMach ⟨[(0 : B256), noMatchSelector], Mem.empty, G + 58⟩
  let innerPre :=
    base.setMach ⟨[noMatchSelector], Mem.empty, G + 45⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons,
      List.length_nil]
    omega
  have hbranchPop : Devm.PopBurnBy [0] (gVerylow + gHigh)
      branchPre innerPre := by
    simpa only [branchPre, innerPre, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := branchPre) (G := G + 45)
        (by simp only [branchPre, Devm.stack_setMach])
        (by simp only [branchPre, Devm.gasLeft_setMach,
          gVerylow, gHigh])
  let hbranch : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm branchPre
      (dispatch (.leaf depositSelector depositEndpoint) <?>
        dispatch
          (.fork
            (.leaf getDepositCountSelector
              (nonpayableEndpoint getDepositCountEndpoint))
            (.leaf getDepositRootSelector
              (nonpayableEndpoint getDepositRootEndpoint))))
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) :=
    .zero hbranchRoom hbranchPop (by
      simpa only [innerPre] using hinner)
  have hbranchSafe : Func.RunCompiledTo.NoRawSstorePath hbranch := by
    dsimp only [hbranch]
    exact .zero (room := hbranchRoom) (pop := hbranchPop) (by
      simpa only [innerPre] using hinnerSafe)
  let afterDup := base.setMach
    ⟨[noMatchSelector, noMatchSelector], Mem.empty, G + 64⟩
  have hdup : Ninst.RunCompiled sevm
      (base.setMach ⟨[noMatchSelector], Mem.empty, G + 67⟩)
      (dup 0) afterDup := by
    simpa only [afterDup, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      (Ninst.runCompiled_dup
        (devm := base.setMach
          ⟨[noMatchSelector], Mem.empty, G + 67⟩)
        (n := 0) (w := noMatchSelector) (G := G + 64) rfl
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  let afterPush := base.setMach
    ⟨[getDepositCountSelector, noMatchSelector, noMatchSelector],
      Mem.empty, G + 61⟩
  have hpushCost :
      pushCost getDepositCountSelector.toBytes.sig = gVerylow := by
    rw [getDepositCountSelector_eq]
    decide +kernel
  have hpush : Ninst.RunCompiled sevm afterDup
      (pushB256 getDepositCountSelector) afterPush := by
    simpa only [afterDup, afterPush, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (devm := afterDup)
        (w := getDepositCountSelector) (G := G + 61) hpushCost
        (by simp only [afterDup, Devm.gasLeft_setMach, gVerylow])
        (by simp only [afterDup, Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  have hgt : Ninst.RunCompiled sevm afterPush gt branchPre := by
    exact Ninst.runCompiled_binary
      (r := .gt) (f := B256.gtCheck) (cost := gVerylow)
      (G := G + 58) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by rw [noMatchSelector, getDepositCountSelector_eq]; decide +kernel)
      (by simp only [afterPush, Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega)
  let run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[noMatchSelector], Mem.empty, G + 67⟩)
      (dispatch
        (.fork
          (.leaf depositSelector depositEndpoint)
          (.fork
            (.leaf getDepositCountSelector
              (nonpayableEndpoint getDepositCountEndpoint))
            (.leaf getDepositRootSelector
              (nonpayableEndpoint getDepositRootEndpoint)))))
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) := by
    unfold dispatch
    exact .next hdup (.next hpush (.next hgt hbranch))
  refine ⟨run, ?_⟩
  exact Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
    (instructionRun := hdup)
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
    (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
      (instructionRun := hpush)
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
        (instructionRun := hgt)
        (by intro impossible; cases impossible)
        (by intro operation impossible; cases impossible)
        hbranchSafe))

/-- The root selector fork also falls right, reaching the already-certified
middle dispatcher. -/
private theorem noMatchRootDispatch_runCompiledTo_with_path
    {sevm : Sevm} {base : Devm} {G : Nat} :
    ∃ run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[noMatchSelector], Mem.empty, G + 89⟩)
        (dispatch tree)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Func.RunCompiledTo.NoRawSstorePath run := by
  obtain ⟨hmiddle, hmiddleSafe⟩ :=
    noMatchMiddleDispatch_runCompiledTo_with_path (sevm := sevm)
      (base := base) (G := G)
  let branchPre :=
    base.setMach ⟨[(0 : B256), noMatchSelector], Mem.empty, G + 80⟩
  let middlePre :=
    base.setMach ⟨[noMatchSelector], Mem.empty, G + 67⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons,
      List.length_nil]
    omega
  have hbranchPop : Devm.PopBurnBy [0] (gVerylow + gHigh)
      branchPre middlePre := by
    simpa only [branchPre, middlePre, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := branchPre) (G := G + 67)
        (by simp only [branchPre, Devm.stack_setMach])
        (by simp only [branchPre, Devm.gasLeft_setMach,
          gVerylow, gHigh])
  let hbranch : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm branchPre
      (dispatch
          (.leaf supportsInterfaceSelector
            (nonpayableEndpoint supportsInterfaceEndpoint)) <?>
        dispatch
          (.fork
            (.leaf depositSelector depositEndpoint)
            (.fork
              (.leaf getDepositCountSelector
                (nonpayableEndpoint getDepositCountEndpoint))
              (.leaf getDepositRootSelector
                (nonpayableEndpoint getDepositRootEndpoint)))))
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) :=
    .zero hbranchRoom hbranchPop (by
      simpa only [middlePre] using hmiddle)
  have hbranchSafe : Func.RunCompiledTo.NoRawSstorePath hbranch := by
    dsimp only [hbranch]
    exact .zero (room := hbranchRoom) (pop := hbranchPop) (by
      simpa only [middlePre] using hmiddleSafe)
  let afterDup := base.setMach
    ⟨[noMatchSelector, noMatchSelector], Mem.empty, G + 86⟩
  have hdup : Ninst.RunCompiled sevm
      (base.setMach ⟨[noMatchSelector], Mem.empty, G + 89⟩)
      (dup 0) afterDup := by
    simpa only [afterDup, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      (Ninst.runCompiled_dup
        (devm := base.setMach
          ⟨[noMatchSelector], Mem.empty, G + 89⟩)
        (n := 0) (w := noMatchSelector) (G := G + 86) rfl
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  let afterPush := base.setMach
    ⟨[depositSelector, noMatchSelector, noMatchSelector],
      Mem.empty, G + 83⟩
  have hpushCost :
      pushCost depositSelector.toBytes.sig = gVerylow := by
    rw [depositSelector_eq]
    decide +kernel
  have hpush : Ninst.RunCompiled sevm afterDup
      (pushB256 depositSelector) afterPush := by
    simpa only [afterDup, afterPush, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (devm := afterDup)
        (w := depositSelector) (G := G + 83) hpushCost
        (by simp only [afterDup, Devm.gasLeft_setMach, gVerylow])
        (by simp only [afterDup, Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  have hgt : Ninst.RunCompiled sevm afterPush gt branchPre := by
    exact Ninst.runCompiled_binary
      (r := .gt) (f := B256.gtCheck) (cost := gVerylow)
      (G := G + 80) (v := 0)
      (by rintro ⟨⟩) rfl rfl
      (by rw [noMatchSelector, depositSelector_eq]; decide +kernel)
      (by simp only [afterPush, Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega)
  let run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[noMatchSelector], Mem.empty, G + 89⟩)
      (dispatch tree)
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) := by
    unfold tree dispatch
    exact .next hdup (.next hpush (.next hgt hbranch))
  refine ⟨run, ?_⟩
  exact Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
    (instructionRun := hdup)
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
    (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
      (instructionRun := hpush)
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
        (instructionRun := hgt)
        (by intro impossible; cases impossible)
        (by intro operation impossible; cases impossible)
        hbranchSafe))

/-- Selector extraction is instruction-only, so the root dispatch certificate
extends to the exact `Func.main tree` walk. -/
private theorem noMatchMain_runCompiledTo_with_path
    {sevm : Sevm} {base : Devm} {G : Nat}
    (hselector : Sevm.selector sevm = noMatchSelector) :
    ∃ run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 100⟩)
        (Func.main tree)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Func.RunCompiledTo.NoRawSstorePath run := by
  obtain ⟨hroot, hrootSafe⟩ :=
    noMatchRootDispatch_runCompiledTo_with_path (sevm := sevm)
      (base := base) (G := G)
  let afterPushZero :=
    base.setMach ⟨[(0 : B256)], Mem.empty, G + 98⟩
  have hpushZero : Ninst.RunCompiled sevm
      (base.setMach ⟨[], Mem.empty, G + 100⟩)
      (pushB256 0) afterPushZero := by
    simpa only [afterPushZero, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm)
        (devm := base.setMach ⟨[], Mem.empty, G + 100⟩)
        (w := (0 : B256)) (c := gBase) (G := G + 98) pushCost_zero
        (by simp only [Devm.gasLeft_setMach, gBase])
        (by simp only [Devm.stack_setMach, List.length_nil]; omega))
  let afterLoad := base.setMach
    ⟨[Sevm.dataWord sevm 0], Mem.empty, G + 95⟩
  have hload : Ninst.RunCompiled sevm afterPushZero
      calldataload afterLoad := by
    simpa only [afterPushZero, afterLoad, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_calldataload (sevm := sevm)
        (devm := afterPushZero) (v := Sevm.dataWord sevm 0)
        (G := G + 95) rfl rfl
        (by simp only [afterPushZero, Devm.gasLeft_setMach, gVerylow])
        (by decide))
  let afterPush224 := base.setMach
    ⟨[(224 : B256), Sevm.dataWord sevm 0], Mem.empty, G + 92⟩
  have hpush224Cost : pushCost (224 : B256).toBytes.sig = gVerylow := by
    decide +kernel
  have hpush224 : Ninst.RunCompiled sevm afterLoad
      (pushB256 224) afterPush224 := by
    simpa only [afterLoad, afterPush224, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm) (devm := afterLoad)
        (w := (224 : B256)) (G := G + 92) hpush224Cost
        (by simp only [afterLoad, Devm.gasLeft_setMach, gVerylow])
        (by simp only [afterLoad, Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  let afterShr :=
    base.setMach ⟨[noMatchSelector], Mem.empty, G + 89⟩
  have h224 : (224 : B256).toNat = 224 := by decide +kernel
  have hselector' :
      Sevm.dataWord sevm 0 >>> (224 : B256).toNat = noMatchSelector := by
    rw [h224]
    exact hselector
  have hshr : Ninst.RunCompiled sevm afterPush224 shr afterShr := by
    exact Ninst.runCompiled_binary
      (r := .shr) (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := G + 89) (v := noMatchSelector)
      (by rintro ⟨⟩) rfl rfl hselector'
      (by simp only [afterPush224, Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega)
  let run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 100⟩)
      (Func.main tree)
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) := by
    unfold Func.main fsig shiftRight cdl
    exact .next hpushZero (.next hload (.next hpush224 (.next hshr (by
      simpa only [afterShr, prepend] using hroot))))
  refine ⟨run, ?_⟩
  change Func.RunCompiledTo.NoRawSstorePath
    (.next hpushZero (.next hload (.next hpush224 (.next hshr hroot))))
  exact Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
    (instructionRun := hpushZero)
    (by intro impossible; cases impossible)
    (by intro operation impossible; cases impossible)
    (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
      (instructionRun := hload)
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
        (instructionRun := hpush224)
        (by intro impossible; cases impossible)
        (by intro operation impossible; cases impossible)
        (Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
          (instructionRun := hshr)
          (by intro impossible; cases impossible)
          (by intro operation impossible; cases impossible)
          (by simpa only [afterShr, prepend] using hrootSafe))))

/-- The concrete selector miss reaches the inline empty revert without ever
executing raw `SSTORE`.  Empty retained writes are derived from that same
execution witness. -/
theorem noMatchSelector_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = noMatchSelector)
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + noMatchSelectorRuntimeGas⟩)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + noMatchSelectorRuntimeGas⟩)
        runtime
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      some sevm.code.toList = Prog.compile runtime := by
  let pre :=
    base.setMach ⟨[], Mem.empty, G + noMatchSelectorRuntimeGas⟩
  let mid := base.setMach ⟨[], Mem.empty, G + 116⟩
  let afterSize := base.setMach
    ⟨[sevm.data.length.toB256], Mem.empty, G + 114⟩
  let afterBranch := base.setMach ⟨[], Mem.empty, G + 100⟩
  let out : Execution :=
    .error (.revert,
      (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])
  obtain ⟨hmain, hmainSafe⟩ :=
    noMatchMain_runCompiledTo_with_path (sevm := sevm)
      (base := base) (G := G) hselector
  have hbranchRoom : afterSize.stack.length < 1024 := by
    simp only [afterSize, Devm.stack_setMach, List.length_cons,
      List.length_nil]
    omega
  have hbranchPop : Devm.PopBurnBy [sevm.data.length.toB256]
      (gVerylow + gHigh + gJumpdest) afterSize afterBranch := by
    simpa only [afterSize, afterBranch, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := afterSize) (G := G + 100)
        (by simp only [afterSize, Devm.stack_setMach])
        (by simp only [afterSize, Devm.gasLeft_setMach,
          gVerylow, gHigh, gJumpdest])
  let hbranch : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm afterSize
      (Func.main tree <?> Func.rev) out :=
    .succ hnonempty hbranchRoom hbranchPop (by
      simpa only [afterBranch, out] using hmain)
  have hbranchSafe : Func.RunCompiledTo.NoRawSstorePath hbranch := by
    dsimp only [hbranch]
    exact .succ (nonzero := hnonempty) (room := hbranchRoom)
      (pop := hbranchPop) (by
        simpa only [afterBranch, out] using hmainSafe)
  have hsize : Ninst.RunCompiled sevm mid calldatasize afterSize := by
    simpa only [mid, afterSize, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm) (devm := mid)
        (r := .calldatasize) (x := Nat.toB256 sevm.data.length)
        (cost := gBase) (G := G + 114) (by rintro ⟨⟩) rfl
        (by simp only [mid, Devm.gasLeft_setMach, gBase])
        (by simp only [mid, Devm.stack_setMach, List.length_nil]; omega))
  have hmainRun : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm mid runtime.main out := by
    unfold runtime
    exact .next hsize hbranch
  have hmainRunSafe : Func.RunCompiledTo.NoRawSstorePath hmainRun := by
    unfold runtime at hmainRun ⊢
    exact Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
      (instructionRun := hsize)
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      hbranchSafe
  have hentryGas : pre.gasLeft = (G + 116) + gJumpdest := by
    simp only [pre, noMatchSelectorRuntimeGas, Devm.gasLeft_setMach,
      gJumpdest]
  have hentry : Devm.BurnBy gJumpdest pre mid := by
    simpa only [pre, mid, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using Devm.burnBy_setMach_gas hentryGas
  have hprogram : Prog.RunCompiledTo sevm pre runtime out :=
    ⟨mid, hentry, hmainRun⟩
  have hcompiled : some sevm.code.toList = Prog.compile runtime := by
    rw [hcode, code_compile]
  obtain ⟨execution, executionSafe⟩ :=
    Prog.exists_exec_noRawSstore hentry hmainRun hmainRunSafe hcompiled
  refine ⟨execution, ?_, executionSafe,
    executionSafe.retainedStorageWrites_eq_nil, hcompiled⟩
  simpa only [pre, out] using hprogram

/-! ## Malformed deposit ABI -/

/-- Exact public gas for one of the thirteen malformed deposit-ABI rows. -/
def depositMalformedRuntimeGas (failure : DepositAbiFailure) : Nat :=
  failure.endpointGas + depositRouteGas

/-- One selected malformed-ABI row reaches its exact empty-revert state through
the payable deposit selector route. -/
theorem deposit_malformed_row_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat) (failure : DepositAbiFailure)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hselector : Sevm.selector sevm = depositSelector)
    (hfailure : DepositAbiFailure.Holds sevm.data failure)
    (hcode : sevm.code.toList = code) :
    Prog.RunCompiledTo sevm
      (base.setMach
        ⟨[], Mem.empty, G + depositMalformedRuntimeGas failure⟩)
      runtime
      (.error (.revert,
        (base.setMach
          ⟨failure.finalStack sevm.data,
            failure.finalMemory sevm.data, G⟩).withOutput [])) ∧
    some sevm.code.toList = Prog.compile runtime := by
  have hendpoint := validateDepositAbi_failure_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm) (base := base)
    (G := G) (body := depositBody) failure (by rfl) hdataBound hfailure
  have hroute := deposit_route_runCompiledTo
    (K := G + failure.endpointGas) hnonempty hselector hendpoint
  constructor
  · have hgas :
        G + failure.endpointGas + depositRouteGas =
          G + depositMalformedRuntimeGas failure := by
      simp only [depositMalformedRuntimeGas]
      omega
    simpa only [hgas] using hroute
  · rw [hcode, code_compile]

/-- Structural ABI invalidity selects one of the thirteen exact public revert
rows.  The witness records the source-order first failing guard. -/
theorem deposit_malformed_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hselector : Sevm.selector sevm = depositSelector)
    (hbad : ¬ DepositAbiStructureDecodable sevm.data)
    (hcode : sevm.code.toList = code) :
    ∃ failure : DepositAbiFailure,
      DepositAbiFailure.Holds sevm.data failure ∧
      Prog.RunCompiledTo sevm
        (base.setMach
          ⟨[], Mem.empty, G + depositMalformedRuntimeGas failure⟩)
        runtime
        (.error (.revert,
          (base.setMach
            ⟨failure.finalStack sevm.data,
              failure.finalMemory sevm.data, G⟩).withOutput [])) ∧
      some sevm.code.toList = Prog.compile runtime := by
  obtain ⟨failure, hfailure⟩ := exists_depositAbiFailure hbad
  obtain ⟨hrun, hcompiled⟩ := deposit_malformed_row_runCompiledTo
    sevm base G failure hnonempty hdataBound hselector hfailure hcode
  exact ⟨failure, hfailure, hrun, hcompiled⟩

end Blanc.BeaconDeposit
