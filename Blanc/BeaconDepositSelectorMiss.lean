import Blanc.BeaconDepositEffects
import Blanc.ForwardDispatchMiss

/-!
# Universal Beacon selector misses

Every nonempty selector-dispatch input outside the four-entry ABI census
reaches the inline empty revert.  The top-level empty-calldata branch is proved
separately by `empty_calldata_runCompiledTo`.  The exact gas depends on the
binary-search path; the identical compiled proof carries raw-SSTORE freedom
and both empty retained chronologies.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

theorem tree_hasSelector_iff (selector : B256) :
    tree.HasSelector selector ↔ selector ∈ beaconSelectors := by
  constructor
  · rintro ⟨body, member⟩
    rcases member with member | member
    · have pairEq : (selector, body) =
          (supportsInterfaceSelector,
            nonpayableEndpoint supportsInterfaceEndpoint) := member
      simp only [beaconSelectors, List.mem_cons]
      exact .inl (congrArg Prod.fst pairEq)
    · rcases member with member | member
      · have pairEq : (selector, body) =
            (depositSelector, depositEndpoint) := member
        simp only [beaconSelectors, List.mem_cons]
        exact .inr (.inl (congrArg Prod.fst pairEq))
      · rcases member with member | member
        · have pairEq : (selector, body) =
              (getDepositCountSelector,
                nonpayableEndpoint getDepositCountEndpoint) := member
          simp only [beaconSelectors, List.mem_cons]
          exact .inr (.inr (.inl (congrArg Prod.fst pairEq)))
        · have pairEq : (selector, body) =
              (getDepositRootSelector,
                nonpayableEndpoint getDepositRootEndpoint) := member
          simp only [beaconSelectors, List.mem_cons]
          exact .inr (.inr (.inr (.inl (congrArg Prod.fst pairEq))))
  · intro member
    simp only [beaconSelectors, List.mem_cons] at member
    rcases member with member | member | member | member | member
    · subst selector
      exact ⟨nonpayableEndpoint supportsInterfaceEndpoint, .inl rfl⟩
    · subst selector
      exact ⟨depositEndpoint, .inr (.inl rfl)⟩
    · subst selector
      exact ⟨nonpayableEndpoint getDepositCountEndpoint,
        .inr (.inr (.inl rfl))⟩
    · subst selector
      exact ⟨nonpayableEndpoint getDepositRootEndpoint,
        .inr (.inr (.inr rfl))⟩
    · contradiction

/-- Exact public gas of a selector-dependent dispatcher miss. -/
def unmatchedSelectorRuntimeGas (selector : B256) : Nat :=
  tree.dispatchMissGas selector + 28

private theorem unmatchedSelectorMain_runCompiledTo_with_path
    {sevm : Sevm} {base : Devm} {G : Nat} {selector : B256}
    (hselector : Sevm.selector sevm = selector)
    (hmiss : selector ∉ beaconSelectors) :
    ∃ run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
        (base.setMach
          ⟨[], Mem.empty, G + tree.dispatchMissGas selector + 11⟩)
        (Func.main tree)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Func.RunCompiledTo.NoRawSstorePath run := by
  have htreeMiss : ¬ tree.HasSelector selector := by
    intro member
    exact hmiss ((tree_hasSelector_iff selector).1 member)
  obtain ⟨hdispatch, hdispatchSafe⟩ :=
    tree.dispatchMiss_runCompiledTo_with_path selector
      (program := runtime) (sevm := sevm) (base := base) G htreeMiss
  let D := tree.dispatchMissGas selector
  let afterPushZero :=
    base.setMach ⟨[(0 : B256)], Mem.empty, G + D + 9⟩
  have hpushZero : Ninst.RunCompiled sevm
      (base.setMach ⟨[], Mem.empty, G + D + 11⟩)
      (pushB256 0) afterPushZero := by
    simpa only [afterPushZero, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm)
        (devm := base.setMach ⟨[], Mem.empty, G + D + 11⟩)
        (w := (0 : B256)) (c := gBase) (G := G + D + 9)
        pushCost_zero
        (by simp only [Devm.gasLeft_setMach, gBase])
        (by simp only [Devm.stack_setMach, List.length_nil]; omega))
  let afterLoad := base.setMach
    ⟨[Sevm.dataWord sevm 0], Mem.empty, G + D + 6⟩
  have hload : Ninst.RunCompiled sevm afterPushZero
      calldataload afterLoad := by
    simpa only [afterPushZero, afterLoad, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_calldataload (sevm := sevm)
        (devm := afterPushZero) (v := Sevm.dataWord sevm 0)
        (G := G + D + 6) rfl rfl
        (by simp only [afterPushZero, Devm.gasLeft_setMach,
          gVerylow])
        (by decide))
  let afterPush224 := base.setMach
    ⟨[(224 : B256), Sevm.dataWord sevm 0], Mem.empty, G + D + 3⟩
  have hpush224Cost : pushCost (224 : B256).toBytes.sig = gVerylow := by
    decide +kernel
  have hpush224 : Ninst.RunCompiled sevm afterLoad
      (pushB256 224) afterPush224 := by
    simpa only [afterLoad, afterPush224, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm) (devm := afterLoad)
        (w := (224 : B256)) (G := G + D + 3) hpush224Cost
        (by simp only [afterLoad, Devm.gasLeft_setMach,
          gVerylow])
        (by simp only [afterLoad, Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  let afterShr := base.setMach ⟨[selector], Mem.empty, G + D⟩
  have h224 : (224 : B256).toNat = 224 := by decide +kernel
  have hselector' :
      Sevm.dataWord sevm 0 >>> (224 : B256).toNat = selector := by
    rw [h224]
    exact hselector
  have hshr : Ninst.RunCompiled sevm afterPush224 shr afterShr := by
    exact Ninst.runCompiled_binary
      (r := .shr) (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := G + D) (v := selector)
      (by rintro ⟨⟩) rfl rfl hselector'
      (by simp only [afterPush224, Devm.gasLeft_setMach,
        gVerylow])
      (by simp only [List.length_nil]; omega)
  let run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G + D + 11⟩)
      (Func.main tree)
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) := by
    unfold Func.main fsig shiftRight cdl
    exact .next hpushZero (.next hload (.next hpush224 (.next hshr (by
      simpa only [afterShr, D, prepend] using hdispatch))))
  have runSafe : Func.RunCompiledTo.NoRawSstorePath run := by
    change Func.RunCompiledTo.NoRawSstorePath
      (.next hpushZero (.next hload (.next hpush224
        (.next hshr hdispatch))))
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
            (by simpa only [afterShr, D, prepend] using hdispatchSafe))))
  simpa only [D, Nat.add_assoc] using ⟨run, runSafe⟩

/-- Every nonempty selector-dispatch input outside the four-entry ABI surface
reaches the inline empty revert without a raw SSTORE.  The empty-calldata
branch is the separate `empty_calldata_runCompiledTo` theorem.  Gas is recorded
by the selected tree walk. -/
theorem unmatched_selector_noRawSstore
    (sevm : Sevm) (base : Devm) (G : Nat) (selector : B256)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = selector)
    (hmiss : selector ∉ beaconSelectors)
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach
          ⟨[], Mem.empty, G + unmatchedSelectorRuntimeGas selector⟩)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Prog.RunCompiledTo sevm
        (base.setMach
          ⟨[], Mem.empty, G + unmatchedSelectorRuntimeGas selector⟩)
        runtime
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      Exec.retainedStorageEffectTriples execution = [] ∧
      some sevm.code.toList = Prog.compile runtime := by
  let D := tree.dispatchMissGas selector
  let pre := base.setMach ⟨[], Mem.empty, G + D + 28⟩
  let mid := base.setMach ⟨[], Mem.empty, G + D + 27⟩
  let afterSize := base.setMach
    ⟨[sevm.data.length.toB256], Mem.empty, G + D + 25⟩
  let afterBranch := base.setMach ⟨[], Mem.empty, G + D + 11⟩
  let out : Execution :=
    .error (.revert,
      (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])
  obtain ⟨hmain, hmainSafe⟩ :=
    unmatchedSelectorMain_runCompiledTo_with_path
      (sevm := sevm) (base := base) (G := G) hselector hmiss
  have hroom : afterSize.stack.length < 1024 := by
    simp only [afterSize, Devm.stack_setMach, List.length_cons,
      List.length_nil]
    omega
  have hpop : Devm.PopBurnBy [sevm.data.length.toB256]
      (gVerylow + gHigh + gJumpdest) afterSize afterBranch := by
    simpa only [afterSize, afterBranch, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := afterSize) (G := G + D + 11)
        (by simp only [afterSize, Devm.stack_setMach])
        (by simp only [afterSize, Devm.gasLeft_setMach,
          gVerylow, gHigh, gJumpdest])
  have mainPack :
      ∃ run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
          afterBranch (Func.main tree) out,
        Func.RunCompiledTo.NoRawSstorePath run := by
    simpa only [afterBranch, out, D, Nat.add_assoc] using
      (⟨hmain, hmainSafe⟩ :
        ∃ run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
            (base.setMach ⟨[], Mem.empty,
              G + tree.dispatchMissGas selector + 11⟩)
            (Func.main tree)
            (.error (.revert,
              (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
          Func.RunCompiledTo.NoRawSstorePath run)
  obtain ⟨hmain', hmainSafe'⟩ := mainPack
  let hbranch : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm afterSize
      (Func.main tree <?> Func.rev) out :=
    .succ hnonempty hroom hpop hmain'
  have hbranchSafe : Func.RunCompiledTo.NoRawSstorePath hbranch := by
    dsimp only [hbranch]
    exact .succ (nonzero := hnonempty) (room := hroom) (pop := hpop)
      hmainSafe'
  have hsize : Ninst.RunCompiled sevm mid calldatasize afterSize := by
    simpa only [mid, afterSize, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm) (devm := mid)
        (r := .calldatasize) (x := Nat.toB256 sevm.data.length)
        (cost := gBase) (G := G + D + 25) (by rintro ⟨⟩) rfl
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
  have hentry : Devm.BurnBy gJumpdest pre mid := by
    simpa only [pre, mid, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, gJumpdest] using
      Devm.burnBy_setMach_gas (devm := pre) (G := G + D + 27)
        (by simp only [pre, Devm.gasLeft_setMach])
  have hprogram : Prog.RunCompiledTo sevm pre runtime out :=
    ⟨mid, hentry, hmainRun⟩
  have hcompiled : some sevm.code.toList = Prog.compile runtime := by
    rw [hcode, code_compile]
  obtain ⟨execution, executionSafe⟩ :=
    Prog.exists_exec_noRawSstore hentry hmainRun hmainRunSafe hcompiled
  refine ⟨execution, ?_, executionSafe,
    executionSafe.retainedStorageWrites_eq_nil,
    executionSafe.retainedStorageEffectTriples_eq_nil, hcompiled⟩
  simpa only [pre, out, D, unmatchedSelectorRuntimeGas,
    Nat.add_assoc] using hprogram

end Blanc.BeaconDeposit
