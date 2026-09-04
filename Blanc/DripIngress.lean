-- DripIngress.lean : the two DRIP ingress dispositions that never reach an
-- endpoint body.
--
-- Empty calldata is the payable receive: it reaches the runtime's top-level
-- `STOP` before selector extraction, so no ledger row, index, clock, or log
-- moves.  Every nonempty input whose selector is outside the frozen
-- five-entry census reaches the dispatcher's inline empty revert.  Both
-- witnesses carry raw-chronology `SSTORE` freedom on the exact execution, so
-- neither disposition can hide a rolled-back write.

import Blanc.DripCode
import Blanc.ForwardDispatchMiss
import Blanc.ForwardNoRawSstore

namespace Blanc.Drip

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## The selector census

`funcs` is the frozen five-entry list and `tree` is its balanced dispatcher.
This is the one fact that turns "not one of DRIP's five selectors" into
"the dispatcher has no leaf for it". -/

theorem tree_hasSelector_iff (sel : B256) :
    tree.HasSelector sel ↔ sel ∈ selectors := by
  constructor
  · rintro ⟨body, member⟩
    simp only [selectors, List.mem_cons, List.not_mem_nil, or_false]
    rcases member with member | member
    · rcases member with member | member
      · rcases member with member | member
        · exact .inl (congrArg Prod.fst
            (member : (sel, body) =
              (convertToAssetsSelector,
                nonpayable (exactCalldata 36 convertToAssets))))
        · exact .inr (.inl (congrArg Prod.fst
            (member : (sel, body) =
              (exitSelector, nonpayable (exactCalldata 36 exit)))))
      · exact .inr (.inr (.inl (congrArg Prod.fst
          (member : (sel, body) =
            (convertToUnitsSelector,
              nonpayable (exactCalldata 36 convertToUnits))))))
    · rcases member with member | member
      · exact .inr (.inr (.inr (.inl (congrArg Prod.fst
          (member : (sel, body) =
            (dripSelector, nonpayable (exactCalldata 4 drip)))))))
      · exact .inr (.inr (.inr (.inr (congrArg Prod.fst
          (member : (sel, body) =
            (joinSelector, exactCalldata 4 join))))))
  · intro member
    simp only [selectors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with member | member | member | member | member
    · subst sel
      exact ⟨nonpayable (exactCalldata 36 convertToAssets),
        .inl (.inl (.inl rfl))⟩
    · subst sel
      exact ⟨nonpayable (exactCalldata 36 exit), .inl (.inl (.inr rfl))⟩
    · subst sel
      exact ⟨nonpayable (exactCalldata 36 convertToUnits), .inl (.inr rfl)⟩
    · subst sel
      exact ⟨nonpayable (exactCalldata 4 drip), .inr (.inl rfl)⟩
    · subst sel
      exact ⟨exactCalldata 4 join, .inr (.inr rfl)⟩

/-! ## Empty calldata: the payable receive -/

/-- Exact public gas of the runtime's empty-calldata receive. -/
def receiveRuntimeGas : Nat := 16

/-- Empty calldata reaches the runtime's top-level `STOP` before selector
extraction.  The exhibited execution ends `.ok` at the entry world state, so
storage, balances, code, logs and output are literally unchanged, and it is
raw-chronology `SSTORE`-free. -/
theorem receive_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hdata : sevm.data = [])
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, G + receiveRuntimeGas⟩)
        (.ok (base.setMach ⟨[], Mem.empty, G⟩)),
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + receiveRuntimeGas⟩)
        runtime
        (.ok (base.setMach ⟨[], Mem.empty, G⟩)) ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      Exec.retainedStorageEffectTriples execution = [] ∧
      some sevm.code.toList = Prog.compile runtime := by
  let pre := base.setMach ⟨[], Mem.empty, G + receiveRuntimeGas⟩
  let mid := base.setMach ⟨[], Mem.empty, G + 15⟩
  let afterSize := base.setMach ⟨[(0 : B256)], Mem.empty, G + 13⟩
  let afterBranch := base.setMach ⟨[], Mem.empty, G⟩
  let out : Execution := .ok afterBranch
  have hstop : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      afterBranch Func.stop out :=
    .last (show Linst.Run sevm afterBranch .stop out from rfl)
  have hstopSafe : Func.RunCompiledTo.NoRawSstorePath hstop :=
    Func.RunCompiledTo.NoRawSstorePath.of_execFree hstop
      (by simp [Func.stop, funcExecFree])
      (by simp [Func.stop, Func.LocalSstoreFree])
  have hroom : afterSize.stack.length < 1024 := by
    simp only [afterSize, Devm.stack_setMach, List.length_cons,
      List.length_nil]
    omega
  have hpop : Devm.PopBurnBy [0] (gVerylow + gHigh) afterSize afterBranch := by
    simpa only [afterSize, afterBranch, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm := afterSize) (G := G)
        (by simp only [afterSize, Devm.stack_setMach])
        (by simp only [afterSize, Devm.gasLeft_setMach, gVerylow, gHigh])
  have hbranch : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm afterSize
      (Func.main tree <?> Func.stop) out :=
    .zero hroom hpop hstop
  have hbranchSafe : Func.RunCompiledTo.NoRawSstorePath hbranch :=
    .zero (room := hroom) (pop := hpop) hstopSafe
  have hsize : Ninst.RunCompiled sevm mid calldatasize afterSize := by
    simpa only [hdata, mid, afterSize, List.length_nil,
        show Nat.toB256 0 = (0 : B256) by decide,
        Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm) (devm := mid)
        (r := .calldatasize) (x := Nat.toB256 sevm.data.length)
        (cost := gBase) (G := G + 13) (by rintro ⟨⟩) rfl
        (by simp only [mid, Devm.gasLeft_setMach, gBase])
        (by simp only [mid, Devm.stack_setMach, List.length_nil]; omega))
  have hmain : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      mid runtime.main out := by
    unfold runtime main
    exact .next hsize hbranch
  have hmainSafe : Func.RunCompiledTo.NoRawSstorePath hmain := by
    unfold runtime main at hmain ⊢
    exact Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
      (instructionRun := hsize) (tail := hbranch)
      (by intro impossible; cases impossible)
      (by intro operation impossible; cases impossible)
      hbranchSafe
  have hentry : Devm.BurnBy gJumpdest pre mid := by
    simpa only [pre, mid, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using
      Devm.burnBy_setMach_gas (devm := pre) (G := G + 15)
        (by simp only [pre, receiveRuntimeGas, Devm.gasLeft_setMach,
          gJumpdest])
  have hprogram : Prog.RunCompiledTo sevm pre runtime out :=
    ⟨mid, hentry, hmain⟩
  have hcompiled : some sevm.code.toList = Prog.compile runtime := by
    rw [hcode, code_compile]
  obtain ⟨execution, executionSafe⟩ :=
    Prog.exists_exec_noRawSstore hentry hmain hmainSafe hcompiled
  exact ⟨execution, hprogram, executionSafe,
    executionSafe.retainedStorageWrites_eq_nil,
    executionSafe.retainedStorageEffectTriples_eq_nil, hcompiled⟩

/-! ## Nonempty calldata outside the census -/

/-- Exact public gas of a selector-dependent dispatcher miss. -/
def unmatchedSelectorRuntimeGas (sel : B256) : Nat :=
  tree.dispatchMissGas sel + 28

private theorem unmatchedSelectorMain_runCompiledTo_with_path
    {sevm : Sevm} {base : Devm} {G : Nat} {sel : B256}
    (hselector : Sevm.selector sevm = sel)
    (hmiss : sel ∉ selectors) :
    ∃ run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
        (base.setMach
          ⟨[], Mem.empty, G + tree.dispatchMissGas sel + 11⟩)
        (Func.main tree)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Func.RunCompiledTo.NoRawSstorePath run := by
  have htreeMiss : ¬ tree.HasSelector sel := by
    intro member
    exact hmiss ((tree_hasSelector_iff sel).1 member)
  obtain ⟨hdispatch, hdispatchSafe⟩ :=
    tree.dispatchMiss_runCompiledTo_with_path sel
      (program := runtime) (sevm := sevm) (base := base) G htreeMiss
  let D := tree.dispatchMissGas sel
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
        (by simp only [afterPushZero, Devm.gasLeft_setMach, gVerylow])
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
        (by simp only [afterLoad, Devm.gasLeft_setMach, gVerylow])
        (by simp only [afterLoad, Devm.stack_setMach, List.length_cons,
          List.length_nil]; omega))
  let afterShr := base.setMach ⟨[sel], Mem.empty, G + D⟩
  have h224 : (224 : B256).toNat = 224 := by decide +kernel
  have hselector' :
      Sevm.dataWord sevm 0 >>> (224 : B256).toNat = sel := by
    rw [h224]
    exact hselector
  have hshr : Ninst.RunCompiled sevm afterPush224 shr afterShr :=
    Ninst.runCompiled_binary
      (r := .shr) (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := G + D) (v := sel)
      (by rintro ⟨⟩) rfl rfl hselector'
      (by simp only [afterPush224, Devm.gasLeft_setMach, gVerylow])
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

/-- Every nonempty input whose selector is outside DRIP's frozen five-entry
census reaches the dispatcher's inline empty revert without a raw `SSTORE`.
The empty-calldata receive is the separate `receive_runCompiledTo`. -/
theorem unmatched_selector_noRawSstore
    (sevm : Sevm) (base : Devm) (G : Nat) (sel : B256)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = sel)
    (hmiss : sel ∉ selectors)
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach
          ⟨[], Mem.empty, G + unmatchedSelectorRuntimeGas sel⟩)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Prog.RunCompiledTo sevm
        (base.setMach
          ⟨[], Mem.empty, G + unmatchedSelectorRuntimeGas sel⟩)
        runtime
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      Exec.retainedStorageEffectTriples execution = [] ∧
      some sevm.code.toList = Prog.compile runtime := by
  let D := tree.dispatchMissGas sel
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
              G + tree.dispatchMissGas sel + 11⟩)
            (Func.main tree)
            (.error (.revert,
              (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
          Func.RunCompiledTo.NoRawSstorePath run)
  obtain ⟨hmain', hmainSafe'⟩ := mainPack
  let hbranch : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm afterSize
      (Func.main tree <?> Func.stop) out :=
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
    unfold runtime main
    exact .next hsize hbranch
  have hmainRunSafe : Func.RunCompiledTo.NoRawSstorePath hmainRun := by
    unfold runtime main at hmainRun ⊢
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

end Blanc.Drip
