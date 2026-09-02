import Blanc.ForwardNoRawSstore

/-!
# Exact raw-write-free dispatcher misses

Selector-dependent construction for a failed binary-search dispatcher walk.
Only the selected subtree is traversed, so an unmatched selector remains
raw-SSTORE-free even when an unselected sibling contains a write or external
instruction.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- A selector occurs at one of a dispatch tree's leaves. -/
def DispatchTree.HasSelector (tree : DispatchTree) (selector : B256) : Prop :=
  ∃ body, (selector, body) ∈ tree

/-- Exact gas used by `dispatch tree` when `selector` misses every leaf.
The branch cost is selector-dependent and the pushed pivot may use `PUSH0`. -/
def DispatchTree.dispatchMissGas : DispatchTree → B256 → Nat
  | .leaf leafSelector _, _ => pushCost leafSelector.toBytes.sig + 20
  | .fork left right, selector =>
      let pivot := leftmostFsig right
      if pivot > selector then
        left.dispatchMissGas selector + pushCost pivot.toBytes.sig + 20
      else
        right.dispatchMissGas selector + pushCost pivot.toBytes.sig + 19

private theorem DispatchTree.hasSelector_leaf_iff
    (leafSelector selector : B256) (body : Func) :
    (DispatchTree.leaf leafSelector body).HasSelector selector ↔
      selector = leafSelector := by
  constructor
  · rintro ⟨found, member⟩
    change (selector, found) = (leafSelector, body) at member
    exact congrArg Prod.fst member
  · intro selectorEq
    subst selectorEq
    exact ⟨body, rfl⟩

private theorem DispatchTree.hasSelector_fork_iff
    (left right : DispatchTree) (selector : B256) :
    (DispatchTree.fork left right).HasSelector selector ↔
      left.HasSelector selector ∨ right.HasSelector selector := by
  constructor
  · rintro ⟨body, member⟩
    change (selector, body) ∈ left ∨ (selector, body) ∈ right at member
    rcases member with member | member
    · exact .inl ⟨body, member⟩
    · exact .inr ⟨body, member⟩
  · rintro (⟨body, member⟩ | ⟨body, member⟩)
    · exact ⟨body, .inl member⟩
    · exact ⟨body, .inr member⟩

/-- An exact failed dispatcher walk paired with raw-SSTORE freedom for the
identical selected proof.  No property of an unselected leaf body is needed. -/
theorem DispatchTree.dispatchMiss_runCompiledTo_with_path
    (tree : DispatchTree) (selector : B256)
    {program : Prog} {sevm : Sevm} {base : Devm} (G : Nat)
    (hmiss : ¬ tree.HasSelector selector) :
    ∃ run : Func.RunCompiledTo (program.main :: program.aux) sevm
        (base.setMach
          ⟨[selector], Mem.empty, G + tree.dispatchMissGas selector⟩)
        (dispatch tree)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
      Func.RunCompiledTo.NoRawSstorePath run := by
  induction tree with
  | leaf leafSelector body =>
      have hne : leafSelector ≠ selector := by
        intro heq
        apply hmiss
        exact (DispatchTree.hasSelector_leaf_iff
          leafSelector selector body).2 heq.symm
      let revertPre := base.setMach ⟨[], Mem.empty, G + 4⟩
      let out : Execution :=
        .error (.revert,
          (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])
      have hrev : Func.RunCompiledTo (program.main :: program.aux) sevm
          revertPre Func.revert out := by
        simpa only [revertPre, out, Devm.setMach_setMach,
            Devm.stack_setMach, Devm.memory_setMach] using
          (Func.runCompiledTo_revert_func
            (fs := program.main :: program.aux) (sevm := sevm)
            (devm := revertPre) (G := G)
            (by simp only [revertPre, Devm.gasLeft_setMach, gBase])
            (by simp only [revertPre, Devm.stack_setMach,
              List.length_nil]; omega))
      have hrevSafe : Func.RunCompiledTo.NoRawSstorePath hrev :=
        Func.RunCompiledTo.NoRawSstorePath.of_execFree hrev
          (by simp [Func.revert, Ninst.pushB256, funcExecFree])
          (by simp [Func.revert, Ninst.pushB256,
            Func.LocalSstoreFree])
      let branchPre := base.setMach ⟨[(0 : B256)], Mem.empty, G + 17⟩
      have hroom : branchPre.stack.length < 1024 := by
        simp only [branchPre, Devm.stack_setMach, List.length_cons,
          List.length_nil]
        omega
      have hpop : Devm.PopBurnBy [0] (gVerylow + gHigh)
          branchPre revertPre := by
        simpa only [branchPre, revertPre, Devm.setMach_setMach,
            Devm.stack_setMach, Devm.memory_setMach] using
          Devm.popBurnBy_setMach (devm := branchPre) (G := G + 4)
            (by simp only [branchPre, Devm.stack_setMach])
            (by simp only [branchPre, Devm.gasLeft_setMach,
              gVerylow, gHigh])
      let hbranch : Func.RunCompiledTo (program.main :: program.aux) sevm
          branchPre (body <?> Func.revert) out :=
        .zero hroom hpop hrev
      let afterPush := base.setMach
        ⟨[leafSelector, selector], Mem.empty, G + 20⟩
      have hpush : Ninst.RunCompiled sevm
          (base.setMach
            ⟨[selector], Mem.empty,
              G + (DispatchTree.leaf leafSelector body).dispatchMissGas
                selector⟩)
          (pushB256 leafSelector) afterPush := by
        simpa only [DispatchTree.dispatchMissGas, afterPush,
            Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach, Nat.add_assoc] using
          (Ninst.runCompiled_pushB256
            (devm := base.setMach
              ⟨[selector], Mem.empty,
                G + pushCost leafSelector.toBytes.sig + 20⟩)
            (w := leafSelector) (G := G + 20) rfl
            (by simp only [Devm.gasLeft_setMach]; omega)
            (by simp only [Devm.stack_setMach, List.length_cons,
              List.length_nil]; omega))
      have heq : Ninst.RunCompiled sevm afterPush eq branchPre := by
        exact Ninst.runCompiled_binary
          (r := .eq) (f := B256.eqCheck) (cost := gVerylow)
          (G := G + 17) (v := 0)
          (by rintro ⟨⟩) rfl rfl
          (by simp [B256.eqCheck, hne])
          (by simp only [afterPush, Devm.gasLeft_setMach, gVerylow])
          (by simp only [List.length_nil]; omega)
      let run : Func.RunCompiledTo (program.main :: program.aux) sevm
          (base.setMach
            ⟨[selector], Mem.empty,
              G + (DispatchTree.leaf leafSelector body).dispatchMissGas
                selector⟩)
          (dispatch (.leaf leafSelector body)) out := by
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
          (by
            dsimp only [hbranch]
            exact .zero (room := hroom) (pop := hpop) hrevSafe))
  | fork left right ihLeft ihRight =>
      have hleft : ¬ left.HasSelector selector := by
        intro member
        exact hmiss ((DispatchTree.hasSelector_fork_iff
          left right selector).2 (.inl member))
      have hright : ¬ right.HasSelector selector := by
        intro member
        exact hmiss ((DispatchTree.hasSelector_fork_iff
          left right selector).2 (.inr member))
      let pivot := leftmostFsig right
      by_cases hpivot : pivot > selector
      · obtain ⟨hchild, hchildSafe⟩ :=
          ihLeft hleft
        let childGas := left.dispatchMissGas selector
        let childPre := base.setMach
          ⟨[selector], Mem.empty, G + childGas⟩
        let branchPre := base.setMach
          ⟨[(1 : B256), selector], Mem.empty, G + childGas + 14⟩
        have hroom : branchPre.stack.length < 1024 := by
          simp only [branchPre, Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
        have hpop : Devm.PopBurnBy [(1 : B256)]
            (gVerylow + gHigh + gJumpdest) branchPre childPre := by
          simpa only [branchPre, childPre, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using
            Devm.popBurnBy_setMach (devm := branchPre)
              (G := G + childGas)
              (by simp only [branchPre, Devm.stack_setMach])
              (by simp only [branchPre, Devm.gasLeft_setMach,
                gVerylow, gHigh, gJumpdest])
        let hbranch : Func.RunCompiledTo
            (program.main :: program.aux) sevm branchPre
            (dispatch left <?> dispatch right)
            (.error (.revert,
              (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) :=
          .succ (by decide) hroom hpop (by
            simpa only [childPre, childGas] using hchild)
        let afterDup := base.setMach
          ⟨[selector, selector], Mem.empty,
            G + childGas + pushCost pivot.toBytes.sig + 17⟩
        have hdup : Ninst.RunCompiled sevm
            (base.setMach
              ⟨[selector], Mem.empty,
                G + left.dispatchMissGas selector +
                  pushCost pivot.toBytes.sig + 20⟩)
            (dup 0) afterDup := by
          simpa only [afterDup, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach, gVerylow]
            using
              (Ninst.runCompiled_dup
                (devm := base.setMach
                  ⟨[selector], Mem.empty,
                    G + left.dispatchMissGas selector +
                      pushCost pivot.toBytes.sig + 20⟩)
                (n := 0) (w := selector)
                (G := G + childGas + pushCost pivot.toBytes.sig + 17)
                rfl (by
                  simp only [Devm.gasLeft_setMach, gVerylow]
                  omega)
                (by simp only [Devm.stack_setMach, List.length_cons,
                  List.length_nil]; omega))
        let afterPush := base.setMach
          ⟨[pivot, selector, selector], Mem.empty,
            G + childGas + 17⟩
        have hpush : Ninst.RunCompiled sevm afterDup
            (pushB256 pivot) afterPush := by
          simpa only [afterDup, afterPush, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using
            (Ninst.runCompiled_pushB256 (devm := afterDup)
              (w := pivot) (G := G + childGas + 17) rfl
              (by simp only [afterDup, Devm.gasLeft_setMach]; omega)
              (by simp only [afterDup, Devm.stack_setMach,
                List.length_cons, List.length_nil]; omega))
        have hgt : Ninst.RunCompiled sevm afterPush gt branchPre := by
          exact Ninst.runCompiled_binary
            (r := .gt) (f := B256.gtCheck) (cost := gVerylow)
            (G := G + childGas + 14) (v := 1)
            (by rintro ⟨⟩) rfl rfl
            (by simp [B256.gtCheck, hpivot])
            (by simp only [afterPush, Devm.gasLeft_setMach, gVerylow])
            (by simp only [List.length_cons, List.length_nil]; omega)
        let run0 : Func.RunCompiledTo (program.main :: program.aux) sevm
            (base.setMach ⟨[selector], Mem.empty,
              G + left.dispatchMissGas selector +
                pushCost pivot.toBytes.sig + 20⟩)
            (dispatch (.fork left right))
            (.error (.revert,
              (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) := by
          unfold dispatch
          exact .next hdup (.next hpush (.next hgt hbranch))
        have hbranchSafe :
            Func.RunCompiledTo.NoRawSstorePath hbranch := by
          dsimp only [hbranch]
          exact .succ (nonzero := by decide) (room := hroom)
            (pop := hpop) (by
              simpa only [childPre, childGas] using hchildSafe)
        have run0Safe : Func.RunCompiledTo.NoRawSstorePath run0 :=
          Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
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
        have packaged :
            ∃ run : Func.RunCompiledTo (program.main :: program.aux) sevm
                (base.setMach ⟨[selector], Mem.empty,
                  G + left.dispatchMissGas selector +
                    pushCost pivot.toBytes.sig + 20⟩)
                (dispatch (.fork left right))
                (.error (.revert,
                  (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
              Func.RunCompiledTo.NoRawSstorePath run :=
          ⟨run0, run0Safe⟩
        simpa [DispatchTree.dispatchMissGas, pivot, hpivot,
          Nat.add_assoc] using packaged
      · obtain ⟨hchild, hchildSafe⟩ :=
          ihRight hright
        let childGas := right.dispatchMissGas selector
        let childPre := base.setMach
          ⟨[selector], Mem.empty, G + childGas⟩
        let branchPre := base.setMach
          ⟨[(0 : B256), selector], Mem.empty, G + childGas + 13⟩
        have hroom : branchPre.stack.length < 1024 := by
          simp only [branchPre, Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
        have hpop : Devm.PopBurnBy [0] (gVerylow + gHigh)
            branchPre childPre := by
          simpa only [branchPre, childPre, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using
            Devm.popBurnBy_setMach (devm := branchPre)
              (G := G + childGas)
              (by simp only [branchPre, Devm.stack_setMach])
              (by simp only [branchPre, Devm.gasLeft_setMach,
                gVerylow, gHigh])
        let hbranch : Func.RunCompiledTo
            (program.main :: program.aux) sevm branchPre
            (dispatch left <?> dispatch right)
            (.error (.revert,
              (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) :=
          .zero hroom hpop (by
            simpa only [childPre, childGas] using hchild)
        let afterDup := base.setMach
          ⟨[selector, selector], Mem.empty,
            G + childGas + pushCost pivot.toBytes.sig + 16⟩
        have hdup : Ninst.RunCompiled sevm
            (base.setMach
              ⟨[selector], Mem.empty,
                G + right.dispatchMissGas selector +
                  pushCost pivot.toBytes.sig + 19⟩)
            (dup 0) afterDup := by
          simpa only [afterDup, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach, gVerylow]
            using
              (Ninst.runCompiled_dup
                (devm := base.setMach
                  ⟨[selector], Mem.empty,
                    G + right.dispatchMissGas selector +
                      pushCost pivot.toBytes.sig + 19⟩)
                (n := 0) (w := selector)
                (G := G + childGas + pushCost pivot.toBytes.sig + 16)
                rfl (by
                  simp only [Devm.gasLeft_setMach, gVerylow]
                  omega)
                (by simp only [Devm.stack_setMach, List.length_cons,
                  List.length_nil]; omega))
        let afterPush := base.setMach
          ⟨[pivot, selector, selector], Mem.empty,
            G + childGas + 16⟩
        have hpush : Ninst.RunCompiled sevm afterDup
            (pushB256 pivot) afterPush := by
          simpa only [afterDup, afterPush, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using
            (Ninst.runCompiled_pushB256 (devm := afterDup)
              (w := pivot) (G := G + childGas + 16) rfl
              (by simp only [afterDup, Devm.gasLeft_setMach]; omega)
              (by simp only [afterDup, Devm.stack_setMach,
                List.length_cons, List.length_nil]; omega))
        have hgt : Ninst.RunCompiled sevm afterPush gt branchPre := by
          exact Ninst.runCompiled_binary
            (r := .gt) (f := B256.gtCheck) (cost := gVerylow)
            (G := G + childGas + 13) (v := 0)
            (by rintro ⟨⟩) rfl rfl
            (by simp [B256.gtCheck, hpivot])
            (by simp only [afterPush, Devm.gasLeft_setMach, gVerylow])
            (by simp only [List.length_cons, List.length_nil]; omega)
        let run0 : Func.RunCompiledTo (program.main :: program.aux) sevm
            (base.setMach ⟨[selector], Mem.empty,
              G + right.dispatchMissGas selector +
                pushCost pivot.toBytes.sig + 19⟩)
            (dispatch (.fork left right))
            (.error (.revert,
              (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) := by
          unfold dispatch
          exact .next hdup (.next hpush (.next hgt hbranch))
        have hbranchSafe :
            Func.RunCompiledTo.NoRawSstorePath hbranch := by
          dsimp only [hbranch]
          exact .zero (room := hroom) (pop := hpop) (by
            simpa only [childPre, childGas] using hchildSafe)
        have run0Safe : Func.RunCompiledTo.NoRawSstorePath run0 :=
          Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
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
        have packaged :
            ∃ run : Func.RunCompiledTo (program.main :: program.aux) sevm
                (base.setMach ⟨[selector], Mem.empty,
                  G + right.dispatchMissGas selector +
                    pushCost pivot.toBytes.sig + 19⟩)
                (dispatch (.fork left right))
                (.error (.revert,
                  (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])),
              Func.RunCompiledTo.NoRawSstorePath run :=
          ⟨run0, run0Safe⟩
        simpa [DispatchTree.dispatchMissGas, pivot, hpivot,
          Nat.add_assoc] using packaged

end Blanc
