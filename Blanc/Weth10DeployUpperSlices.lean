-- Weth10DeployUpperSlices.lean : exact upper parameter-span locality for WETH10.
--
-- These shape-indexed byte-reader lemmas isolate the generated runtime spans
-- affected by deployment parameters without expanding off-span dispatcher arms.

import Blanc.Weth10Code
import Blanc.Forward
import Mathlib.Tactic.IntervalCases

namespace Blanc

open Jaune

namespace Weth10

private def prefixByteSize : Line → Nat
  | [] => 0
  | inst :: rest => inst.size + prefixByteSize rest

private theorem byteAt_prepend_eq_prefix
    (locations : List Nat) (n : Nat) (l : Line) (p0 p : Func)
    (i : Nat) (d : UInt8) (hi : i < prefixByteSize l) :
    Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p) i d =
      Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p0) i d := by
  induction l generalizing n i with
  | nil => simp [prefixByteSize] at hi
  | cons inst rest ih =>
      change
        Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p)) i d =
          Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p0)) i d
      by_cases hinst : i < inst.size
      · conv_lhs => rw [Func.byteAtByShape, if_pos hinst]
        conv_rhs => rw [Func.byteAtByShape, if_pos hinst]
      · conv_lhs => rw [Func.byteAtByShape, if_neg hinst]
        conv_rhs => rw [Func.byteAtByShape, if_neg hinst]
        apply ih
        simp only [prefixByteSize] at hi
        omega

private theorem byteAt_prepend_to_tail
    (locations : List Nat) (n : Nat) (l : Line) (p0 p : Func)
    (i : Nat) (d : UInt8) (hlo : prefixByteSize l ≤ i) :
    Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p) i d =
      Func.byteAtByShape locations (n + prefixByteSize l) p0.compileShape
        p (i - prefixByteSize l) d := by
  induction l generalizing n i with
  | nil => simp [prefixByteSize, prepend]
  | cons inst rest ih =>
      have hinst : inst.size ≤ i := by
        simp only [prefixByteSize] at hlo
        omega
      change
        Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p)) i d = _
      conv_lhs => rw [Func.byteAtByShape, if_neg (Nat.not_lt_of_ge hinst)]
      rw [ih (n := n + inst.size) (i := i - inst.size) (by
        simp only [prefixByteSize] at hlo
        omega)]
      simp only [prefixByteSize, Nat.add_assoc, Nat.sub_sub]

private theorem byteAt_next_to_tail
    (locations : List Nat) (n : Nat) (inst0 inst : Ninst) (p0 p : Func)
    (i : Nat) (d : UInt8) (hlo : inst0.size ≤ i) :
    Func.byteAtByShape locations n (inst0 ::: p0).compileShape
        (inst ::: p) i d =
      Func.byteAtByShape locations (n + inst0.size) p0.compileShape
        p (i - inst0.size) d := by
  rw [Func.compileShape, Func.byteAtByShape, if_neg (Nat.not_lt_of_ge hlo)]

private theorem byteAt_branch_eq_header
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (i : Nat) (d : UInt8)
    (hi : i < 4) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) i d =
      Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left0 right0) i d := by
  conv_lhs => rw [Func.byteAtByShape, if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using hi)]
  conv_rhs => rw [Func.byteAtByShape, if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using hi)]

private theorem byteAt_branch_to_left
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (i : Nat) (d : UInt8)
    (hlo : 4 ≤ i) (hinside : i - 4 < left0.compileShape.byteSize) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) i d =
      Func.byteAtByShape locations (n + 4) left0.compileShape left
        (i - 4) d := by
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
      hinside)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]

private lemma byteAt_branch_jumpdest
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (d : UInt8) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) (4 + left0.compileShape.byteSize) d =
      Jinst.jumpdest.toUInt8 := by
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_pos (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  have hi0 :
      4 + left0.compileShape.byteSize - 4 -
        left0.compileShape.byteSize = 0 := by
    omega
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [hi0]
  rfl

private theorem byteAt_branch_eq_before_right
    (locations : List Nat) (n : Nat)
    (left0 right0 right : Func) (i : Nat) (d : UInt8)
    (hi : i < 5 + left0.compileShape.byteSize) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left0 right) i d =
      Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left0 right0) i d := by
  by_cases hheader : i < 4
  · exact byteAt_branch_eq_header locations n left0 right0 left0 right
      i d hheader
  · by_cases hleft : i - 4 < left0.compileShape.byteSize
    · rw [byteAt_branch_to_left locations n left0 right0 left0 right i d
          (by omega) hleft,
        byteAt_branch_to_left locations n left0 right0 left0 right0 i d
          (by omega) hleft]
    · have hjump : i = 4 + left0.compileShape.byteSize := by omega
      subst i
      rw [byteAt_branch_jumpdest locations n left0 right0 left0 right,
        byteAt_branch_jumpdest locations n left0 right0 left0 right0]

private theorem byteAt_branch_to_right
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (i : Nat) (d : UInt8)
    (hlo : 5 + left0.compileShape.byteSize ≤ i) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) i d =
      Func.byteAtByShape locations
        (n + 5 + left0.compileShape.byteSize) right0.compileShape right
        (i - (5 + left0.compileShape.byteSize)) d := by
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  congr 1 <;> omega

private theorem pushDeployWord_opcode_eq
    (locations : List Nat) (n : Nat) (p0 p : Func) (w : B256) :
    Func.byteAtByShape locations n (pushDeployWord 0 ::: p0).compileShape
        (pushDeployWord w ::: p) 0 0 =
      Func.byteAtByShape locations n (pushDeployWord 0 ::: p0).compileShape
        (pushDeployWord 0 ::: p0) 0 0 := by
  simp [Func.byteAtByShape, Func.compileShape, pushDeployWord,
    Ninst.toBytes, Ninst.size, pushToB8L, pushToB8, B256.length_toBytes]

private theorem byteAt_pushDeployWord_data
    (locations : List Nat) (n : Nat) (p0 p : Func) (w : B256)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n (pushDeployWord 0 ::: p0).compileShape
        (pushDeployWord w ::: p) (j + 1) 0 =
      w.toBytes.getD j 0 := by
  rw [Func.compileShape, Func.byteAtByShape]
  rw [if_pos (by
    simp only [pushDeployWord, Ninst.size, B256.length_toBytes]
    omega)]
  rw [List.getD_takeD]
  rw [if_pos (by
    simp only [pushDeployWord, Ninst.size, B256.length_toBytes]
    omega)]
  simp only [pushDeployWord, Ninst.toBytes, pushToB8L,
    List.getD_cons_succ]

private def permitCorePrefix : Line :=
  [Ninst.chainid] ++ addressArg 0 ++ [Ninst.dup 0] ++ tagNonceKey ++
  [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ mstoreAt 4 ++
  [Ninst.pushB256 1, Ninst.add, Ninst.swap 0, Ninst.sstore, Ninst.pop,
    Ninst.pushB256 PERMIT_TYPEHASH] ++ mstoreAt 0 ++
  argCopy 1 0 3 ++ arg 3 ++ mstoreAt 5 ++
  pushList [192, 0] ++ [Ninst.kec, Ninst.dup 1]

private def permitDynamicPath : Func :=
  Ninst.swap 0 ::: calculateDomainSeparator +++ .call permitRecoverSlot

private def permitCachedPath (dp : DeployParams) : Func :=
  Ninst.swap 0 ::: Ninst.pop :::
    pushDeployWord dp.cachedDomainSeparator ::: .call permitRecoverSlot

private def permitCoreTail (dp : DeployParams) : Func :=
  pushDeployWord dp.deploymentChainId ::: Ninst.eq :::
    Func.branch permitDynamicPath (permitCachedPath dp)

private def permitCoreX (dp : DeployParams) : Func :=
  permitCorePrefix +++ permitCoreTail dp

private def permitGuardPrefix : Line :=
  arg 3 ++ [Ninst.timestamp, Ninst.gt]

private def permitFactored (dp : DeployParams) : Func :=
  permitGuardPrefix +++
    Func.branch (permitCoreX dp) (.call expiredPermitErrorSlot)

private theorem permit_eq_factored (dp : DeployParams) :
    permit dp = permitFactored dp := by
  unfold permit permitFactored permitCoreX permitCoreTail
  simp only [permitGuardPrefix, permitCorePrefix, permitDynamicPath,
    permitCachedPath, prepend_append, List.cons_append, List.nil_append,
    prepend]

private def permitCachedPrefix : Line :=
  [Ninst.swap 0, Ninst.pop]

private theorem permitCachedPath_eq (dp : DeployParams) :
    permitCachedPath dp =
      permitCachedPrefix +++
        (pushDeployWord dp.cachedDomainSeparator :::
          .call permitRecoverSlot) := by
  rfl

/- Permit-path sizes, decided once here and shared by every walk lemma
below instead of re-deciding the same kernel walk per site. -/

private theorem permit_size :
    (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 326 := by
  decide +kernel

private theorem permitDynamicPath_size :
    permitDynamicPath.compileShape.byteSize = 123 := by
  decide +kernel

private theorem permitCoreTail_size :
    (permitCoreTail (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      201 := by
  decide +kernel

private theorem permitCoreX_size :
    (permitCoreX (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 312 := by
  decide +kernel

private theorem permitCachedPathByteAt_eq_zero_0_3
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 3) :
    Func.byteAtByShape locations n
        (permitCachedPath (⟨0, 0⟩ : DeployParams)).compileShape
        (permitCachedPath dp) i 0 =
      Func.byteAtByShape locations n
        (permitCachedPath (⟨0, 0⟩ : DeployParams)).compileShape
        (permitCachedPath (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [permitCachedPath_eq dp,
    permitCachedPath_eq (⟨0, 0⟩ : DeployParams)]
  have hprefix : prefixByteSize permitCachedPrefix = 2 := by
    decide +kernel
  by_cases hpre : i < 2
  · apply byteAt_prepend_eq_prefix
    simpa only [hprefix] using hpre
  · have hiEq : i = 2 := by omega
    subst i
    conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitCachedPrefix)
      (p0 := pushDeployWord 0 ::: .call permitRecoverSlot)
      (p := pushDeployWord dp.cachedDomainSeparator :::
        .call permitRecoverSlot)
      (i := 2) (d := 0) (by rw [hprefix])]
    conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitCachedPrefix)
      (p0 := pushDeployWord 0 ::: .call permitRecoverSlot)
      (p := pushDeployWord 0 ::: .call permitRecoverSlot)
      (i := 2) (d := 0) (by rw [hprefix])]
    simp only [hprefix, Nat.reduceSub]
    exact pushDeployWord_opcode_eq _ _ _ _ _

private theorem permitByteAt_to_coreTail
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 120 ≤ i)
    (hinside : i - 120 <
      (permitCoreTail (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) i d =
      Func.byteAtByShape locations (n + 120)
        (permitCoreTail (⟨0, 0⟩ : DeployParams)).compileShape
        (permitCoreTail dp) (i - 120) d := by
  rw [permit_eq_factored dp,
    permit_eq_factored (⟨0, 0⟩ : DeployParams)]
  unfold permitFactored
  have hguard : prefixByteSize permitGuardPrefix = 5 := by
    decide +kernel
  have hcore : prefixByteSize permitCorePrefix = 111 := by
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitGuardPrefix)
      (p0 := Func.branch
        (permitCoreX (⟨0, 0⟩ : DeployParams))
        (.call expiredPermitErrorSlot))
      (p := Func.branch (permitCoreX dp)
        (.call expiredPermitErrorSlot))
      (i := i) (d := d) (by rw [hguard]; omega)]
  simp only [hguard]
  change
    Func.byteAtByShape locations (n + 5)
        (.branch
          (permitCoreX (⟨0, 0⟩ : DeployParams)).compileShape
          (Func.call expiredPermitErrorSlot).compileShape)
        (.branch (permitCoreX dp) (.call expiredPermitErrorSlot))
        (i - 5) d = _
  conv_lhs => rw [byteAt_branch_to_left
      (locations := locations) (n := n + 5)
      (left0 := permitCoreX (⟨0, 0⟩ : DeployParams))
      (right0 := .call expiredPermitErrorSlot)
      (left := permitCoreX dp)
      (right := .call expiredPermitErrorSlot)
      (i := i - 5) (d := d) (by omega) (by
        have hcoreSize :
            (permitCoreX
              (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 312 :=
        permitCoreX_size
        rw [hcoreSize]
        have htailSize :
            (permitCoreTail
              (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 201 :=
        permitCoreTail_size
        rw [htailSize] at hinside
        omega)]
  unfold permitCoreX
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n + 5 + 4)
      (l := permitCorePrefix)
      (p0 := permitCoreTail (⟨0, 0⟩ : DeployParams))
      (p := permitCoreTail dp) (i := i - 5 - 4) (d := d)
      (by rw [hcore]; omega)]
  simp only [hcore]
  congr 1

private theorem permitCoreTailByteAt_eq_zero_33_165
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 33 ≤ i) (hi : i < 165) :
    Func.byteAtByShape locations n
        (permitCoreTail (⟨0, 0⟩ : DeployParams)).compileShape
        (permitCoreTail dp) i 0 =
      Func.byteAtByShape locations n
        (permitCoreTail (⟨0, 0⟩ : DeployParams)).compileShape
        (permitCoreTail (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold permitCoreTail
  have hpush : (pushDeployWord 0).size = 33 := by decide +kernel
  conv_lhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n)
      (inst0 := pushDeployWord 0)
      (inst := pushDeployWord dp.deploymentChainId)
      (p0 := Ninst.eq :::
        Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (p := Ninst.eq :::
        Func.branch permitDynamicPath (permitCachedPath dp))
      (i := i) (d := 0) (by rw [hpush]; omega)]
  conv_rhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n)
      (inst0 := pushDeployWord 0) (inst := pushDeployWord 0)
      (p0 := Ninst.eq :::
        Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (p := Ninst.eq :::
        Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (i := i) (d := 0) (by rw [hpush]; omega)]
  simp only [hpush]
  have heqSize : Ninst.eq.size = 1 := by decide +kernel
  by_cases heq : i - 33 < 1
  · conv_lhs => rw [Func.compileShape, Func.byteAtByShape,
        if_pos (by rw [heqSize]; exact heq)]
    conv_rhs => rw [Func.compileShape, Func.byteAtByShape,
        if_pos (by rw [heqSize]; exact heq)]
  · conv_lhs => rw [byteAt_next_to_tail
        (locations := locations) (n := n + 33)
        (inst0 := Ninst.eq) (inst := Ninst.eq)
        (p0 := Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
        (p := Func.branch permitDynamicPath (permitCachedPath dp))
        (i := i - 33) (d := 0) (by rw [heqSize]; omega)]
    conv_rhs => rw [byteAt_next_to_tail
        (locations := locations) (n := n + 33)
        (inst0 := Ninst.eq) (inst := Ninst.eq)
        (p0 := Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
        (p := Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
        (i := i - 33) (d := 0) (by rw [heqSize]; omega)]
    simp only [heqSize]
    have hdynamic :
        permitDynamicPath.compileShape.byteSize = 123 :=
        permitDynamicPath_size
    change
      Func.byteAtByShape locations (n + 33 + 1)
          (.branch permitDynamicPath.compileShape
            (permitCachedPath
              (⟨0, 0⟩ : DeployParams)).compileShape)
          (.branch permitDynamicPath (permitCachedPath dp))
          (i - 33 - 1) 0 =
        Func.byteAtByShape locations (n + 33 + 1)
          (.branch permitDynamicPath.compileShape
            (permitCachedPath
              (⟨0, 0⟩ : DeployParams)).compileShape)
          (.branch permitDynamicPath
            (permitCachedPath (⟨0, 0⟩ : DeployParams)))
          (i - 33 - 1) 0
    by_cases hbefore : i - 33 - 1 < 128
    · apply byteAt_branch_eq_before_right
      simpa only [hdynamic, Nat.reduceAdd] using hbefore
    · conv_lhs => rw [byteAt_branch_to_right
          (locations := locations) (n := n + 33 + 1)
          (left0 := permitDynamicPath)
          (right0 := permitCachedPath
            (⟨0, 0⟩ : DeployParams))
          (left := permitDynamicPath) (right := permitCachedPath dp)
          (i := i - 33 - 1) (d := 0)
          (by rw [hdynamic]; omega)]
      conv_rhs => rw [byteAt_branch_to_right
          (locations := locations) (n := n + 33 + 1)
          (left0 := permitDynamicPath)
          (right0 := permitCachedPath
            (⟨0, 0⟩ : DeployParams))
          (left := permitDynamicPath)
          (right := permitCachedPath
            (⟨0, 0⟩ : DeployParams))
          (i := i - 33 - 1) (d := 0)
          (by rw [hdynamic]; omega)]
      simp only [hdynamic, Nat.reduceAdd]
      apply permitCachedPathByteAt_eq_zero_0_3
      omega

private theorem permitByteAt_eq_zero_153_285
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 153 ≤ i) (hi : i < 285) :
    Func.byteAtByShape locations n
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) i 0 =
      Func.byteAtByShape locations n
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit (⟨0, 0⟩ : DeployParams)) i 0 := by
  have htailSize :
      (permitCoreTail
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 201 :=
        permitCoreTail_size
  rw [permitByteAt_to_coreTail locations n dp i 0 (by omega) (by
        rw [htailSize]
        omega),
    permitByteAt_to_coreTail locations n
      (⟨0, 0⟩ : DeployParams) i 0 (by omega) (by
        rw [htailSize]
        omega)]
  apply permitCoreTailByteAt_eq_zero_33_165
  · omega
  · omega

private theorem noncesSel_eq :
    selector "nonces" [.address] = (0x7ecebe00 : B256) := by
  decide +kernel

private theorem approveAndCallSel_eq :
    selector "approveAndCall" [.address, .uint256, .dynBytes] =
      (0xcae9ca51 : B256) := by
  decide +kernel

private theorem permitSel_eq :
    selector "permit"
        [.address, .address, .uint256, .uint256, .uint 8, .bytes 32,
          .bytes 32] = (0xd505accf : B256) := by
  decide +kernel

private theorem flashFeeSel_eq :
    selector "flashFee" [.address, .uint256] = (0xd9d98ce4 : B256) := by
  decide +kernel

private theorem allowanceSel_eq :
    selector "allowance" [.address, .address] = (0xdd62ed3e : B256) := by
  decide +kernel

private def treeSlice (dp : DeployParams) (fuel lo len : Nat) : DispatchTree :=
  DispatchTree.build fuel ((weth10Funcs dp).drop lo |>.take len)

private def dispatch26_0_14 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 26 0 14)

private def dispatch25_14_7 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 25 14 7)

private def dispatch24_21_3 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 24 21 3)

private def dispatch23_26_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 23 26 1)

private def dispatch22_24_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 22 24 1)

private def dispatchNode (selector : B256) (offPath onPath : Func) : Func :=
  Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
    (offPath <?> onPath)

private lemma dispatchNodeByteAt_to_onPath
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func) (i : Nat) (d : UInt8)
    (hpush : (Ninst.pushB256 selector).size = 5)
    (hlo : 11 ≤ i)
    (hinside : i - 11 < on0.compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) i d =
      Func.byteAtByShape locations (n + 11) on0.compileShape on
        (i - 11) d := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  have hiEq : i - 1 - 5 - 1 - 4 = i - 11 := by omega
  change
    Func.byteAtByShape locations n
      (.next (Ninst.dup 0).size
        (.next (Ninst.pushB256 selector).size
          (.next Ninst.gt.size
            (.branch on0.compileShape off0.compileShape))))
      (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
        (off <?> on)) i d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_pos (by
    simpa only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd, hiEq] using hinside)]
  simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
    Nat.reduceAdd, hiEq]

private lemma dispatchNodeByteAt_to_offPath
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func) (i : Nat) (d : UInt8)
    (hpush : (Ninst.pushB256 selector).size = 5)
    (hlo : 12 + on0.compileShape.byteSize ≤ i) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) i d =
      Func.byteAtByShape locations
        (n + 12 + on0.compileShape.byteSize) off0.compileShape off
        (i - (12 + on0.compileShape.byteSize)) d := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  change
    Func.byteAtByShape locations n
      (.next (Ninst.dup 0).size
        (.next (Ninst.pushB256 selector).size
          (.next Ninst.gt.size
            (.branch on0.compileShape off0.compileShape))))
      (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
        (off <?> on)) i d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
    Nat.reduceAdd]
  congr 1 <;> omega

private def flashFeeLeaf : Func :=
  Ninst.pushB256 (0xd9d98ce4 : B256) ::: Ninst.eq :::
    ((nonpayable flashFee) <?> .call fallbackSlot)

private def dispatchD9 (dp : DeployParams) : Func :=
  dispatchNode 0xd9d98ce4 (dispatch22_24_1 dp) flashFeeLeaf

private def dispatchDd (dp : DeployParams) : Func :=
  dispatchNode 0xdd62ed3e (dispatchD9 dp) (dispatch23_26_1 dp)

private def dispatchD505 (dp : DeployParams) : Func :=
  dispatchNode 0xd505accf (dispatch24_21_3 dp) (dispatchDd dp)

private def dispatchCae9 (dp : DeployParams) : Func :=
  dispatchNode 0xcae9ca51 (dispatch25_14_7 dp) (dispatchD505 dp)

private def flashFeeDispatch (dp : DeployParams) : Func :=
  dispatchNode 0x7ecebe00 (dispatch26_0_14 dp) (dispatchCae9 dp)

private theorem flashFeeDispatch_eq (dp : DeployParams) :
    dispatchWith fallbackSlot (weth10Tree dp) = flashFeeDispatch dp := by
  simp [weth10Tree, DispatchTree.ofSorted, weth10Funcs, DispatchTree.build,
    treeSlice, dispatch26_0_14, dispatch25_14_7, dispatch24_21_3,
    dispatch23_26_1, dispatch22_24_1, flashFeeDispatch, dispatchCae9,
    dispatchD505, dispatchDd, dispatchD9, flashFeeLeaf, dispatchNode,
    dispatchWith,
    leftmostFsig, noncesSel_eq, approveAndCallSel_eq, permitSel_eq,
    flashFeeSel_eq, allowanceSel_eq]

private theorem dispatch22_24_1_eq_permit (dp : DeployParams) :
    dispatch22_24_1 dp =
      Ninst.pushB256 (0xd505accf : B256) ::: Ninst.eq :::
        ((nonpayable (permit dp)) <?> .call fallbackSlot) := by
  simp [dispatch22_24_1, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith, permitSel_eq]

private def permitLeafPrefix : Line :=
  [Ninst.pushB256 (0xd505accf : B256), Ninst.eq]

private def nonpayablePrefix : Line :=
  [Ninst.callvalue, Ninst.iszero]

/- Dispatch-chain sizes: one small decide per leaf subtree, every internal
node composed through `dispatchNode_size`. -/

private theorem dispatchNode_size (s : B256) (off on : Func)
    (hpush : (Ninst.pushB256 s).size = 5) :
    (dispatchNode s off on).compileShape.byteSize =
      12 + on.compileShape.byteSize + off.compileShape.byteSize := by
  have hpushBytes : (Ninst.toBytes (Ninst.pushB256 s)).length = 5 := by
    rw [← Ninst.size_eq_length_toBytes]
    exact hpush
  have hdup : (Ninst.toBytes (Ninst.dup 0)).length = 1 := rfl
  have hgt : (Ninst.toBytes Ninst.gt).length = 1 := rfl
  simp only [Func.CompileShape.byteSize_compileShape, dispatchNode, compsize,
    hpushBytes, hdup, hgt]
  omega

private theorem flashFeeLeaf_size :
    flashFeeLeaf.compileShape.byteSize = 47 := by
  decide +kernel

private theorem dispatch23_26_1_size :
    (dispatch23_26_1 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      110 := by
  decide +kernel

private theorem dispatch22_24_1_size :
    (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      351 := by
  decide +kernel

private theorem dispatch25_14_7_size :
    (dispatch25_14_7 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      822 := by
  decide +kernel

private theorem dispatch24_21_3_size :
    (dispatch24_21_3 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      391 := by
  decide +kernel

private theorem dispatchD9_size :
    (dispatchD9 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 410 := by
  unfold dispatchD9
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    flashFeeLeaf_size, dispatch22_24_1_size]

private theorem dispatchDd_size :
    (dispatchDd (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 532 := by
  unfold dispatchDd
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    dispatch23_26_1_size, dispatchD9_size]

private theorem dispatchD505_size :
    (dispatchD505 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 935 := by
  unfold dispatchD505
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    dispatchDd_size, dispatch24_21_3_size]

private theorem dispatchCae9_size :
    (dispatchCae9 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 1769 := by
  unfold dispatchCae9
  rw [dispatchNode_size _ _ _ (by decide +kernel),
    dispatchD505_size, dispatch25_14_7_size]

private theorem dispatch22_24_1ByteAt_to_permit
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 25 ≤ i)
    (_hinside : i - 25 <
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatch22_24_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_24_1 dp) i d =
      Func.byteAtByShape locations (n + 25)
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) (i - 25) d := by
  rw [dispatch22_24_1_eq_permit dp,
    dispatch22_24_1_eq_permit (⟨0, 0⟩ : DeployParams)]
  change
    Func.byteAtByShape locations n
        (permitLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable
              (permit (⟨0, 0⟩ : DeployParams)))).compileShape
        (permitLeafPrefix +++
          Func.branch (.call fallbackSlot) (nonpayable (permit dp)))
        i d = _
  have hleafPrefix : prefixByteSize permitLeafPrefix = 6 := by
    decide +kernel
  have hcall : (Func.call fallbackSlot).compileShape.byteSize = 4 := by
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitLeafPrefix)
      (p0 := Func.branch (.call fallbackSlot)
        (nonpayable (permit (⟨0, 0⟩ : DeployParams))))
      (p := Func.branch (.call fallbackSlot) (nonpayable (permit dp)))
      (i := i) (d := d) (by rw [hleafPrefix]; omega)]
  simp only [hleafPrefix]
  change
    Func.byteAtByShape locations (n + 6)
        (.branch (Func.call fallbackSlot).compileShape
          (nonpayable
            (permit (⟨0, 0⟩ : DeployParams))).compileShape)
        (.branch (.call fallbackSlot) (nonpayable (permit dp)))
        (i - 6) d = _
  conv_lhs => rw [byteAt_branch_to_right
      (locations := locations) (n := n + 6)
      (left0 := .call fallbackSlot)
      (right0 := nonpayable
        (permit (⟨0, 0⟩ : DeployParams)))
      (left := .call fallbackSlot)
      (right := nonpayable (permit dp))
      (i := i - 6) (d := d) (by rw [hcall]; omega)]
  simp only [hcall]
  have hiNonpayable : i - 6 - (5 + 4) = i - 15 := by omega
  rw [hiNonpayable]
  change
    Func.byteAtByShape locations (n + 6 + 5 + 4)
        (nonpayablePrefix +++
          Func.branch Func.rev
            (permit (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++
          Func.branch Func.rev (permit dp)) (i - 15) d = _
  have hnonpayablePrefix : prefixByteSize nonpayablePrefix = 2 := by
    decide +kernel
  have hrev : Func.rev.compileShape.byteSize = 3 := by
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n + 6 + 5 + 4)
      (l := nonpayablePrefix)
      (p0 := Func.branch Func.rev
        (permit (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch Func.rev (permit dp))
      (i := i - 15) (d := d) (by
        rw [hnonpayablePrefix]
        omega)]
  simp only [hnonpayablePrefix]
  change
    Func.byteAtByShape locations (n + 6 + 5 + 4 + 2)
        (.branch Func.rev.compileShape
          (permit (⟨0, 0⟩ : DeployParams)).compileShape)
        (.branch Func.rev (permit dp)) (i - 15 - 2) d = _
  conv_lhs => rw [byteAt_branch_to_right
      (locations := locations) (n := n + 6 + 5 + 4 + 2)
      (left0 := Func.rev)
      (right0 := permit (⟨0, 0⟩ : DeployParams))
      (left := Func.rev) (right := permit dp)
      (i := i - 15 - 2) (d := d) (by rw [hrev]; omega)]
  simp only [hrev]
  congr 1

private theorem dispatchD9ByteAt_to_permit
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 84 ≤ i)
    (hinside : i - 84 <
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatchD9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD9 dp) i d =
      Func.byteAtByShape locations (n + 84)
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) (i - 84) d := by
  unfold dispatchD9
  have hpush : (Ninst.pushB256 (0xd9d98ce4 : B256)).size = 5 := by
    decide +kernel
  have honSize : flashFeeLeaf.compileShape.byteSize = 47 :=
        flashFeeLeaf_size
  rw [dispatchNodeByteAt_to_offPath
      (locations := locations) (n := n) (selector := 0xd9d98ce4)
      (off0 := dispatch22_24_1 (⟨0, 0⟩ : DeployParams))
      (on0 := flashFeeLeaf) (off := dispatch22_24_1 dp)
      (on := flashFeeLeaf) (i := i) (d := d) hpush (by
        rw [honSize]
        omega)]
  simp only [honSize, Nat.reduceAdd]
  simpa only [Nat.sub_sub, Nat.reduceAdd, Nat.add_assoc] using
    dispatch22_24_1ByteAt_to_permit locations (n + 59) dp
      (i - 59) d (by omega) (by
        simpa only [Nat.sub_sub, Nat.reduceAdd] using hinside)

private theorem dispatchDdByteAt_to_permit
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 206 ≤ i)
    (hinside : i - 206 <
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatchDd (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchDd dp) i d =
      Func.byteAtByShape locations (n + 206)
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) (i - 206) d := by
  unfold dispatchDd
  have hpush : (Ninst.pushB256 (0xdd62ed3e : B256)).size = 5 := by
    decide +kernel
  have honSize :
      (dispatch23_26_1
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 110 :=
        dispatch23_26_1_size
  rw [dispatchNodeByteAt_to_offPath
      (locations := locations) (n := n) (selector := 0xdd62ed3e)
      (off0 := dispatchD9 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatch23_26_1 (⟨0, 0⟩ : DeployParams))
      (off := dispatchD9 dp) (on := dispatch23_26_1 dp)
      (i := i) (d := d) hpush (by rw [honSize]; omega)]
  simp only [honSize, Nat.reduceAdd]
  simpa only [Nat.sub_sub, Nat.reduceAdd, Nat.add_assoc] using
    dispatchD9ByteAt_to_permit locations (n + 122) dp
      (i - 122) d (by omega) (by
        simpa only [Nat.sub_sub, Nat.reduceAdd] using hinside)

private theorem dispatchD505ByteAt_to_permit
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 217 ≤ i)
    (hinside : i - 217 <
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatchD505 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchD505 dp) i d =
      Func.byteAtByShape locations (n + 217)
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) (i - 217) d := by
  unfold dispatchD505
  have hpush : (Ninst.pushB256 (0xd505accf : B256)).size = 5 := by
    decide +kernel
  have honSize :
      (dispatchDd
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 532 :=
        dispatchDd_size
  have hpermitSize :
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 326 :=
        permit_size
  rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n) (selector := 0xd505accf)
      (off0 := dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchDd (⟨0, 0⟩ : DeployParams))
      (off := dispatch24_21_3 dp) (on := dispatchDd dp)
      (i := i) (d := d) hpush (by omega) (by
        rw [honSize]
        rw [hpermitSize] at hinside
        omega)]
  simpa only [Nat.sub_sub, Nat.reduceAdd, Nat.add_assoc] using
    dispatchDdByteAt_to_permit locations (n + 11) dp
      (i - 11) d (by omega) (by
        simpa only [Nat.sub_sub, Nat.reduceAdd] using hinside)

private theorem dispatchCae9ByteAt_to_permit
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 228 ≤ i)
    (hinside : i - 228 <
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatchCae9 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatchCae9 dp) i d =
      Func.byteAtByShape locations (n + 228)
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) (i - 228) d := by
  unfold dispatchCae9
  have hpush : (Ninst.pushB256 (0xcae9ca51 : B256)).size = 5 := by
    decide +kernel
  have honSize :
      (dispatchD505
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 935 :=
        dispatchD505_size
  have hpermitSize :
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 326 :=
        permit_size
  rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n) (selector := 0xcae9ca51)
      (off0 := dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchD505 (⟨0, 0⟩ : DeployParams))
      (off := dispatch25_14_7 dp) (on := dispatchD505 dp)
      (i := i) (d := d) hpush (by omega) (by
        rw [honSize]
        rw [hpermitSize] at hinside
        omega)]
  simpa only [Nat.sub_sub, Nat.reduceAdd, Nat.add_assoc] using
    dispatchD505ByteAt_to_permit locations (n + 11) dp
      (i - 11) d (by omega) (by
        simpa only [Nat.sub_sub, Nat.reduceAdd] using hinside)

private theorem flashFeeDispatchByteAt_to_permit
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 239 ≤ i)
    (hinside : i - 239 <
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (flashFeeDispatch (⟨0, 0⟩ : DeployParams)).compileShape
        (flashFeeDispatch dp) i d =
      Func.byteAtByShape locations (n + 239)
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) (i - 239) d := by
  unfold flashFeeDispatch
  have hpush : (Ninst.pushB256 (0x7ecebe00 : B256)).size = 5 := by
    decide +kernel
  have honSize :
      (dispatchCae9
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 1769 :=
        dispatchCae9_size
  have hpermitSize :
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 326 :=
        permit_size
  rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n) (selector := 0x7ecebe00)
      (off0 := dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchCae9 (⟨0, 0⟩ : DeployParams))
      (off := dispatch26_0_14 dp) (on := dispatchCae9 dp)
      (i := i) (d := d) hpush (by omega) (by
        rw [honSize]
        rw [hpermitSize] at hinside
        omega)]
  simpa only [Nat.sub_sub, Nat.reduceAdd, Nat.add_assoc] using
    dispatchCae9ByteAt_to_permit locations (n + 11) dp
      (i - 11) d (by omega) (by
        simpa only [Nat.sub_sub, Nat.reduceAdd] using hinside)

private theorem weth10DispatchByteAt_to_permit
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 239 ≤ i)
    (hinside : i - 239 <
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i d =
      Func.byteAtByShape locations (n + 239)
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) (i - 239) d := by
  rw [flashFeeDispatch_eq dp,
    flashFeeDispatch_eq (⟨0, 0⟩ : DeployParams)]
  exact flashFeeDispatchByteAt_to_permit
    locations n dp i d hlo hinside

theorem weth10DispatchByteAt_eq_zero_392_524
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 392 ≤ i) (hi : i < 524) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  have hpermit :
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 326 :=
        permit_size
  rw [weth10DispatchByteAt_to_permit locations n dp i 0
        (by omega) (by rw [hpermit]; omega),
    weth10DispatchByteAt_to_permit locations n
      (⟨0, 0⟩ : DeployParams) i 0
        (by omega) (by rw [hpermit]; omega)]
  apply permitByteAt_eq_zero_153_285 <;> omega

private theorem permitCachedPathByteAt_cachedWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (permitCachedPath (⟨0, 0⟩ : DeployParams)).compileShape
        (permitCachedPath dp) (3 + j) 0 =
      dp.cachedDomainSeparator.toBytes.getD j 0 := by
  rw [permitCachedPath_eq dp,
    permitCachedPath_eq (⟨0, 0⟩ : DeployParams)]
  have hprefix : prefixByteSize permitCachedPrefix = 2 := by
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := permitCachedPrefix)
      (p0 := pushDeployWord 0 ::: .call permitRecoverSlot)
      (p := pushDeployWord dp.cachedDomainSeparator :::
        .call permitRecoverSlot)
      (i := 3 + j) (d := 0) (by rw [hprefix]; omega)]
  simp only [hprefix]
  have hi : 3 + j - 2 = j + 1 := by omega
  rw [hi]
  exact byteAt_pushDeployWord_data locations (n + 2)
    _ _ dp.cachedDomainSeparator j hj

private theorem permitCoreTailByteAt_cachedWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (permitCoreTail (⟨0, 0⟩ : DeployParams)).compileShape
        (permitCoreTail dp) (165 + j) 0 =
      dp.cachedDomainSeparator.toBytes.getD j 0 := by
  unfold permitCoreTail
  have hpush : (pushDeployWord 0).size = 33 := by decide +kernel
  conv_lhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n)
      (inst0 := pushDeployWord 0)
      (inst := pushDeployWord dp.deploymentChainId)
      (p0 := Ninst.eq :::
        Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (p := Ninst.eq :::
        Func.branch permitDynamicPath (permitCachedPath dp))
      (i := 165 + j) (d := 0) (by rw [hpush]; omega)]
  simp only [hpush]
  have heqSize : Ninst.eq.size = 1 := by decide +kernel
  conv_lhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n + 33)
      (inst0 := Ninst.eq) (inst := Ninst.eq)
      (p0 := Func.branch permitDynamicPath
        (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch permitDynamicPath (permitCachedPath dp))
      (i := 165 + j - 33) (d := 0) (by rw [heqSize]; omega)]
  simp only [heqSize]
  change
    Func.byteAtByShape locations (n + 33 + 1)
        (.branch permitDynamicPath.compileShape
          (permitCachedPath
            (⟨0, 0⟩ : DeployParams)).compileShape)
        (.branch permitDynamicPath (permitCachedPath dp))
        (165 + j - 33 - 1) 0 = _
  have hdynamic : permitDynamicPath.compileShape.byteSize = 123 :=
        permitDynamicPath_size
  conv_lhs => rw [byteAt_branch_to_right
      (locations := locations) (n := n + 33 + 1)
      (left0 := permitDynamicPath)
      (right0 := permitCachedPath
        (⟨0, 0⟩ : DeployParams))
      (left := permitDynamicPath) (right := permitCachedPath dp)
      (i := 165 + j - 33 - 1) (d := 0) (by
        rw [hdynamic]
        omega)]
  simp only [hdynamic, Nat.reduceAdd]
  have hi : 165 + j - 33 - 1 - 128 = 3 + j := by omega
  rw [hi]
  exact permitCachedPathByteAt_cachedWord
    locations (n + 33 + 1 + 128) dp j hj

private theorem permitByteAt_cachedWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) (285 + j) 0 =
      dp.cachedDomainSeparator.toBytes.getD j 0 := by
  have htailSize :
      (permitCoreTail
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 201 :=
        permitCoreTail_size
  rw [permitByteAt_to_coreTail locations n dp (285 + j) 0
      (by omega) (by rw [htailSize]; omega)]
  have hi : 285 + j - 120 = 165 + j := by omega
  rw [hi]
  exact permitCoreTailByteAt_cachedWord
    locations (n + 120) dp j hj

theorem weth10DispatchByteAt_cachedWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) (524 + j) 0 =
      dp.cachedDomainSeparator.toBytes.getD j 0 := by
  have hpermit :
      (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 326 :=
        permit_size
  rw [weth10DispatchByteAt_to_permit locations n dp (524 + j) 0
      (by omega) (by rw [hpermit]; omega)]
  have hi : 524 + j - 239 = 285 + j := by omega
  rw [hi]
  exact permitByteAt_cachedWord locations (n + 239) dp j hj

private theorem permitCoreTailByteAt_eq_zero_197_201
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 197 ≤ i) (hi : i < 201) :
    Func.byteAtByShape locations n
        (permitCoreTail (⟨0, 0⟩ : DeployParams)).compileShape
        (permitCoreTail dp) i 0 =
      Func.byteAtByShape locations n
        (permitCoreTail (⟨0, 0⟩ : DeployParams)).compileShape
        (permitCoreTail (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold permitCoreTail
  have hpush : (pushDeployWord 0).size = 33 := by decide +kernel
  conv_lhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n)
      (inst0 := pushDeployWord 0)
      (inst := pushDeployWord dp.deploymentChainId)
      (p0 := Ninst.eq :::
        Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (p := Ninst.eq :::
        Func.branch permitDynamicPath (permitCachedPath dp))
      (i := i) (d := 0) (by rw [hpush]; omega)]
  conv_rhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n)
      (inst0 := pushDeployWord 0) (inst := pushDeployWord 0)
      (p0 := Ninst.eq :::
        Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (p := Ninst.eq :::
        Func.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (i := i) (d := 0) (by rw [hpush]; omega)]
  simp only [hpush]
  have heqSize : Ninst.eq.size = 1 := by decide +kernel
  conv_lhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n + 33)
      (inst0 := Ninst.eq) (inst := Ninst.eq)
      (p0 := Func.branch permitDynamicPath
        (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch permitDynamicPath (permitCachedPath dp))
      (i := i - 33) (d := 0) (by rw [heqSize]; omega)]
  conv_rhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n + 33)
      (inst0 := Ninst.eq) (inst := Ninst.eq)
      (p0 := Func.branch permitDynamicPath
        (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch permitDynamicPath
        (permitCachedPath (⟨0, 0⟩ : DeployParams)))
      (i := i - 33) (d := 0) (by rw [heqSize]; omega)]
  simp only [heqSize]
  change
    Func.byteAtByShape locations (n + 33 + 1)
        (.branch permitDynamicPath.compileShape
          (permitCachedPath
            (⟨0, 0⟩ : DeployParams)).compileShape)
        (.branch permitDynamicPath (permitCachedPath dp))
        (i - 33 - 1) 0 =
      Func.byteAtByShape locations (n + 33 + 1)
        (.branch permitDynamicPath.compileShape
          (permitCachedPath
            (⟨0, 0⟩ : DeployParams)).compileShape)
        (.branch permitDynamicPath
          (permitCachedPath (⟨0, 0⟩ : DeployParams)))
        (i - 33 - 1) 0
  have hdynamic : permitDynamicPath.compileShape.byteSize = 123 :=
        permitDynamicPath_size
  conv_lhs => rw [byteAt_branch_to_right
      (locations := locations) (n := n + 33 + 1)
      (left0 := permitDynamicPath)
      (right0 := permitCachedPath
        (⟨0, 0⟩ : DeployParams))
      (left := permitDynamicPath) (right := permitCachedPath dp)
      (i := i - 33 - 1) (d := 0) (by rw [hdynamic]; omega)]
  conv_rhs => rw [byteAt_branch_to_right
      (locations := locations) (n := n + 33 + 1)
      (left0 := permitDynamicPath)
      (right0 := permitCachedPath
        (⟨0, 0⟩ : DeployParams))
      (left := permitDynamicPath)
      (right := permitCachedPath
        (⟨0, 0⟩ : DeployParams))
      (i := i - 33 - 1) (d := 0) (by rw [hdynamic]; omega)]
  simp only [hdynamic, Nat.reduceAdd]
  rw [permitCachedPath_eq dp,
    permitCachedPath_eq (⟨0, 0⟩ : DeployParams)]
  have hprefix : prefixByteSize permitCachedPrefix = 2 := by
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n + 33 + 1 + 128)
      (l := permitCachedPrefix)
      (p0 := pushDeployWord 0 ::: .call permitRecoverSlot)
      (p := pushDeployWord dp.cachedDomainSeparator :::
        .call permitRecoverSlot)
      (i := i - 33 - 1 - 128) (d := 0) (by
        rw [hprefix]
        omega)]
  conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n + 33 + 1 + 128)
      (l := permitCachedPrefix)
      (p0 := pushDeployWord 0 ::: .call permitRecoverSlot)
      (p := pushDeployWord 0 ::: .call permitRecoverSlot)
      (i := i - 33 - 1 - 128) (d := 0) (by
        rw [hprefix]
        omega)]
  simp only [hprefix]
  conv_lhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n + 33 + 1 + 128 + 2)
      (inst0 := pushDeployWord 0)
      (inst := pushDeployWord dp.cachedDomainSeparator)
      (p0 := .call permitRecoverSlot) (p := .call permitRecoverSlot)
      (i := i - 33 - 1 - 128 - 2) (d := 0) (by
        rw [hpush]
        omega)]
  conv_rhs => rw [byteAt_next_to_tail
      (locations := locations) (n := n + 33 + 1 + 128 + 2)
      (inst0 := pushDeployWord 0) (inst := pushDeployWord 0)
      (p0 := .call permitRecoverSlot) (p := .call permitRecoverSlot)
      (i := i - 33 - 1 - 128 - 2) (d := 0) (by
        rw [hpush]
        omega)]

private theorem permitByteAt_eq_zero_317_326
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 317 ≤ i) (hi : i < 326) :
    Func.byteAtByShape locations n
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit dp) i 0 =
      Func.byteAtByShape locations n
        (permit (⟨0, 0⟩ : DeployParams)).compileShape
        (permit (⟨0, 0⟩ : DeployParams)) i 0 := by
  by_cases hcore : i < 321
  · have htailSize :
        (permitCoreTail
          (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 201 :=
        permitCoreTail_size
    rw [permitByteAt_to_coreTail locations n dp i 0
          (by omega) (by rw [htailSize]; omega),
      permitByteAt_to_coreTail locations n
        (⟨0, 0⟩ : DeployParams) i 0
          (by omega) (by rw [htailSize]; omega)]
    apply permitCoreTailByteAt_eq_zero_197_201 <;> omega
  · rw [permit_eq_factored dp,
      permit_eq_factored (⟨0, 0⟩ : DeployParams)]
    unfold permitFactored
    have hguard : prefixByteSize permitGuardPrefix = 5 := by
      decide +kernel
    conv_lhs => rw [byteAt_prepend_to_tail
        (locations := locations) (n := n) (l := permitGuardPrefix)
        (p0 := Func.branch
          (permitCoreX (⟨0, 0⟩ : DeployParams))
          (.call expiredPermitErrorSlot))
        (p := Func.branch (permitCoreX dp)
          (.call expiredPermitErrorSlot))
        (i := i) (d := 0) (by rw [hguard]; omega)]
    conv_rhs => rw [byteAt_prepend_to_tail
        (locations := locations) (n := n) (l := permitGuardPrefix)
        (p0 := Func.branch
          (permitCoreX (⟨0, 0⟩ : DeployParams))
          (.call expiredPermitErrorSlot))
        (p := Func.branch
          (permitCoreX (⟨0, 0⟩ : DeployParams))
          (.call expiredPermitErrorSlot))
        (i := i) (d := 0) (by rw [hguard]; omega)]
    simp only [hguard]
    change
      Func.byteAtByShape locations (n + 5)
          (.branch
            (permitCoreX (⟨0, 0⟩ : DeployParams)).compileShape
            (Func.call expiredPermitErrorSlot).compileShape)
          (.branch (permitCoreX dp) (.call expiredPermitErrorSlot))
          (i - 5) 0 =
        Func.byteAtByShape locations (n + 5)
          (.branch
            (permitCoreX (⟨0, 0⟩ : DeployParams)).compileShape
            (Func.call expiredPermitErrorSlot).compileShape)
          (.branch (permitCoreX (⟨0, 0⟩ : DeployParams))
            (.call expiredPermitErrorSlot)) (i - 5) 0
    have hcoreSize :
        (permitCoreX
          (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 312 :=
        permitCoreX_size
    by_cases hjump : i = 321
    · have hiEq : i - 5 = 4 +
          (permitCoreX
            (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
        rw [hcoreSize]
        omega
      rw [hiEq]
      rw [byteAt_branch_jumpdest locations (n + 5)
          (permitCoreX (⟨0, 0⟩ : DeployParams))
          (.call expiredPermitErrorSlot)
          (permitCoreX dp) (.call expiredPermitErrorSlot),
        byteAt_branch_jumpdest locations (n + 5)
          (permitCoreX (⟨0, 0⟩ : DeployParams))
          (.call expiredPermitErrorSlot)
          (permitCoreX (⟨0, 0⟩ : DeployParams))
          (.call expiredPermitErrorSlot)]
    · rw [byteAt_branch_to_right locations (n + 5)
          (permitCoreX (⟨0, 0⟩ : DeployParams))
          (.call expiredPermitErrorSlot)
          (permitCoreX dp) (.call expiredPermitErrorSlot)
          (i - 5) 0 (by rw [hcoreSize]; omega),
        byteAt_branch_to_right locations (n + 5)
          (permitCoreX (⟨0, 0⟩ : DeployParams))
          (.call expiredPermitErrorSlot)
          (permitCoreX (⟨0, 0⟩ : DeployParams))
          (.call expiredPermitErrorSlot)
          (i - 5) 0 (by rw [hcoreSize]; omega)]

private theorem dispatchNodeByteAt_eq_prefix
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func)
    (hpush : (Ninst.pushB256 selector).size = 5)
    (i : Nat) (hi : i < 11) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) i 0 =
      Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off0 on0) i 0 := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  interval_cases i <;>
    simp [dispatchNode, Func.byteAtByShape, Func.compileShape,
      hdup, hgt, hpush]

private lemma dispatchNodeByteAt_jumpdest
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func)
    (hpush : (Ninst.pushB256 selector).size = 5) (d : UInt8) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) (11 + on0.compileShape.byteSize) d =
      Jinst.jumpdest.toUInt8 := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  change
    Func.byteAtByShape locations n
      (.next (Ninst.dup 0).size
        (.next (Ninst.pushB256 selector).size
          (.next Ninst.gt.size
            (.branch on0.compileShape off0.compileShape))))
      (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
        (off <?> on)) (11 + on0.compileShape.byteSize) d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [hdup]
    omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [hdup, hpush]
    omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [hdup, hpush, hgt]
    omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_pos (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  have hi0 :
      11 + on0.compileShape.byteSize - 1 - 5 - 1 - 4 -
        on0.compileShape.byteSize = 0 := by
    omega
  simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
    Nat.reduceAdd]
  rw [hi0]
  rfl

private theorem dispatchNodeByteAt_eq_jumpdest
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func)
    (hpush : (Ninst.pushB256 selector).size = 5) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) (11 + on0.compileShape.byteSize) 0 =
      Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off0 on0)
        (11 + on0.compileShape.byteSize) 0 := by
  rw [dispatchNodeByteAt_jumpdest locations n selector off0 on0 off on hpush,
    dispatchNodeByteAt_jumpdest locations n selector off0 on0 off0 on0 hpush]

private theorem deploymentChainIdSel_eq :
    selector "deploymentChainId" [] = (0xcd0d0096 : B256) := by
  decide +kernel

private theorem depositSel_eq :
    selector "deposit" [] = (0xd0e30db0 : B256) := by
  decide +kernel

private def dispatchLeaf (selector : B256) (body : Func) : Func :=
  Ninst.pushB256 selector ::: Ninst.eq :::
    (body <?> .call fallbackSlot)

private def dispatch24Factored (dp : DeployParams) : Func :=
  dispatchNode 0xd0e30db0
    (dispatchNode 0xcd0d0096
      (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
      (dispatchLeaf 0xcd0d0096
        (nonpayable (deploymentChainId dp))))
    (dispatchLeaf 0xd0e30db0 deposit)

private theorem dispatch24_21_3_eq_factored (dp : DeployParams) :
    dispatch24_21_3 dp = dispatch24Factored dp := by
  simp [dispatch24_21_3, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith, dispatch24Factored, dispatchNode, dispatchLeaf,
    leftmostFsig, approveAndCallSel_eq, deploymentChainIdSel_eq,
    depositSel_eq]

private def dispatchLeafPrefix (selector : B256) : Line :=
  [Ninst.pushB256 selector, Ninst.eq]

private theorem dispatchLeaf_eq (selector : B256) (body : Func) :
    dispatchLeaf selector body =
      dispatchLeafPrefix selector +++
        Func.branch (.call fallbackSlot) body := by
  rfl

private theorem depositDispatchLeaf_size :
    (dispatchLeaf 0xd0e30db0 deposit).compileShape.byteSize = 64 := by
  decide +kernel

private theorem deploymentChainIdDispatchLeaf_size :
    (dispatchLeaf 0xcd0d0096 (nonpayable (deploymentChainId
      (⟨0, 0⟩ : DeployParams)))).compileShape.byteSize = 64 := by
  decide +kernel

private theorem dispatchLeafByteAt_eq_before_body
    (locations : List Nat) (n : Nat) (selector : B256)
    (body0 body : Func) (i : Nat) (d : UInt8)
    (hpush : (Ninst.pushB256 selector).size = 5) (hi : i < 15) :
    Func.byteAtByShape locations n (dispatchLeaf selector body0).compileShape
        (dispatchLeaf selector body) i d =
      Func.byteAtByShape locations n (dispatchLeaf selector body0).compileShape
        (dispatchLeaf selector body0) i d := by
  rw [dispatchLeaf_eq selector body, dispatchLeaf_eq selector body0]
  have heq : Ninst.eq.size = 1 := by decide +kernel
  have hprefix : prefixByteSize (dispatchLeafPrefix selector) = 6 := by
    simp [dispatchLeafPrefix, prefixByteSize, hpush, heq]
  by_cases hpre : i < 6
  · apply byteAt_prepend_eq_prefix
    simpa only [hprefix] using hpre
  · conv_lhs => rw [byteAt_prepend_to_tail
        (locations := locations) (n := n)
        (l := dispatchLeafPrefix selector)
        (p0 := Func.branch (.call fallbackSlot) body0)
        (p := Func.branch (.call fallbackSlot) body)
        (i := i) (d := d) (by rw [hprefix]; omega)]
    conv_rhs => rw [byteAt_prepend_to_tail
        (locations := locations) (n := n)
        (l := dispatchLeafPrefix selector)
        (p0 := Func.branch (.call fallbackSlot) body0)
        (p := Func.branch (.call fallbackSlot) body0)
        (i := i) (d := d) (by rw [hprefix]; omega)]
    simp only [hprefix]
    have hcall :
        (Func.call fallbackSlot).compileShape.byteSize = 4 := by
      decide +kernel
    apply byteAt_branch_eq_before_right
    rw [hcall]
    omega

private theorem dispatchLeafByteAt_to_body
    (locations : List Nat) (n : Nat) (selector : B256)
    (body0 body : Func) (i : Nat) (d : UInt8)
    (hpush : (Ninst.pushB256 selector).size = 5) (hlo : 15 ≤ i) :
    Func.byteAtByShape locations n (dispatchLeaf selector body0).compileShape
        (dispatchLeaf selector body) i d =
      Func.byteAtByShape locations (n + 15) body0.compileShape body
        (i - 15) d := by
  rw [dispatchLeaf_eq selector body, dispatchLeaf_eq selector body0]
  have heq : Ninst.eq.size = 1 := by decide +kernel
  have hprefix : prefixByteSize (dispatchLeafPrefix selector) = 6 := by
    simp [dispatchLeafPrefix, prefixByteSize, hpush, heq]
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n)
      (l := dispatchLeafPrefix selector)
      (p0 := Func.branch (.call fallbackSlot) body0)
      (p := Func.branch (.call fallbackSlot) body)
      (i := i) (d := d) (by rw [hprefix]; omega)]
  simp only [hprefix]
  have hcall : (Func.call fallbackSlot).compileShape.byteSize = 4 := by
    decide +kernel
  change
    Func.byteAtByShape locations (n + 6)
        (.branch (Func.call fallbackSlot).compileShape body0.compileShape)
        (.branch (.call fallbackSlot) body) (i - 6) d = _
  rw [byteAt_branch_to_right locations (n + 6)
      (.call fallbackSlot) body0 (.call fallbackSlot) body
      (i - 6) d (by rw [hcall]; omega)]
  simp only [hcall]
  congr 1

private theorem nonpayableByteAt_eq_before_body
    (locations : List Nat) (n : Nat) (body0 body : Func)
    (i : Nat) (d : UInt8) (hi : i < 10) :
    Func.byteAtByShape locations n (nonpayable body0).compileShape
        (nonpayable body) i d =
      Func.byteAtByShape locations n (nonpayable body0).compileShape
        (nonpayable body0) i d := by
  change
    Func.byteAtByShape locations n
        (nonpayablePrefix +++ Func.branch Func.rev body0).compileShape
        (nonpayablePrefix +++ Func.branch Func.rev body) i d =
      Func.byteAtByShape locations n
        (nonpayablePrefix +++ Func.branch Func.rev body0).compileShape
        (nonpayablePrefix +++ Func.branch Func.rev body0) i d
  have hprefix : prefixByteSize nonpayablePrefix = 2 := by decide +kernel
  by_cases hpre : i < 2
  · apply byteAt_prepend_eq_prefix
    simpa only [hprefix] using hpre
  · conv_lhs => rw [byteAt_prepend_to_tail
        (locations := locations) (n := n) (l := nonpayablePrefix)
        (p0 := Func.branch Func.rev body0)
        (p := Func.branch Func.rev body)
        (i := i) (d := d) (by rw [hprefix]; omega)]
    conv_rhs => rw [byteAt_prepend_to_tail
        (locations := locations) (n := n) (l := nonpayablePrefix)
        (p0 := Func.branch Func.rev body0)
        (p := Func.branch Func.rev body0)
        (i := i) (d := d) (by rw [hprefix]; omega)]
    simp only [hprefix]
    have hrev : Func.rev.compileShape.byteSize = 3 := by decide +kernel
    apply byteAt_branch_eq_before_right
    rw [hrev]
    omega

private theorem nonpayableByteAt_to_body
    (locations : List Nat) (n : Nat) (body0 body : Func)
    (i : Nat) (d : UInt8) (hlo : 10 ≤ i) :
    Func.byteAtByShape locations n (nonpayable body0).compileShape
        (nonpayable body) i d =
      Func.byteAtByShape locations (n + 10) body0.compileShape body
        (i - 10) d := by
  change
    Func.byteAtByShape locations n
        (nonpayablePrefix +++ Func.branch Func.rev body0).compileShape
        (nonpayablePrefix +++ Func.branch Func.rev body) i d = _
  have hprefix : prefixByteSize nonpayablePrefix = 2 := by decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := nonpayablePrefix)
      (p0 := Func.branch Func.rev body0)
      (p := Func.branch Func.rev body)
      (i := i) (d := d) (by rw [hprefix]; omega)]
  simp only [hprefix]
  have hrev : Func.rev.compileShape.byteSize = 3 := by decide +kernel
  change
    Func.byteAtByShape locations (n + 2)
        (.branch Func.rev.compileShape body0.compileShape)
        (.branch Func.rev body) (i - 2) d = _
  rw [byteAt_branch_to_right locations (n + 2)
      Func.rev body0 Func.rev body (i - 2) d (by rw [hrev]; omega)]
  simp only [hrev]
  congr 1

private theorem deploymentChainIdByteAt_eq_zero_opcode
    (locations : List Nat) (n : Nat) (dp : DeployParams) :
    Func.byteAtByShape locations n
        (deploymentChainId (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentChainId dp) 0 0 =
      Func.byteAtByShape locations n
        (deploymentChainId (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentChainId (⟨0, 0⟩ : DeployParams)) 0 0 := by
  unfold deploymentChainId returnDeployWord
  exact pushDeployWord_opcode_eq _ _ _ _ _

private theorem deploymentChainIdByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (deploymentChainId (⟨0, 0⟩ : DeployParams)).compileShape
        (deploymentChainId dp) (j + 1) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  unfold deploymentChainId returnDeployWord
  exact byteAt_pushDeployWord_data
    locations n _ _ dp.deploymentChainId j hj

private theorem deploymentLeafByteAt_eq_zero_0_26
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 26) :
    Func.byteAtByShape locations n
        (dispatchLeaf 0xcd0d0096
          (nonpayable
            (deploymentChainId
              (⟨0, 0⟩ : DeployParams)))).compileShape
        (dispatchLeaf 0xcd0d0096
          (nonpayable (deploymentChainId dp))) i 0 =
      Func.byteAtByShape locations n
        (dispatchLeaf 0xcd0d0096
          (nonpayable
            (deploymentChainId
              (⟨0, 0⟩ : DeployParams)))).compileShape
        (dispatchLeaf 0xcd0d0096
          (nonpayable
            (deploymentChainId
              (⟨0, 0⟩ : DeployParams)))) i 0 := by
  have hpush : (Ninst.pushB256 (0xcd0d0096 : B256)).size = 5 := by
    decide +kernel
  by_cases hleaf : i < 15
  · exact dispatchLeafByteAt_eq_before_body locations n 0xcd0d0096
      (nonpayable
        (deploymentChainId (⟨0, 0⟩ : DeployParams)))
      (nonpayable (deploymentChainId dp)) i 0 hpush hleaf
  · rw [dispatchLeafByteAt_to_body locations n 0xcd0d0096
        (nonpayable
          (deploymentChainId (⟨0, 0⟩ : DeployParams)))
        (nonpayable (deploymentChainId dp)) i 0 hpush (by omega),
      dispatchLeafByteAt_to_body locations n 0xcd0d0096
        (nonpayable
          (deploymentChainId (⟨0, 0⟩ : DeployParams)))
        (nonpayable
          (deploymentChainId (⟨0, 0⟩ : DeployParams)))
        i 0 hpush (by omega)]
    by_cases hnonpayable : i - 15 < 10
    · exact nonpayableByteAt_eq_before_body locations (n + 15)
        (deploymentChainId (⟨0, 0⟩ : DeployParams))
        (deploymentChainId dp) (i - 15) 0 hnonpayable
    · rw [nonpayableByteAt_to_body locations (n + 15)
          (deploymentChainId (⟨0, 0⟩ : DeployParams))
          (deploymentChainId dp) (i - 15) 0 (by omega),
        nonpayableByteAt_to_body locations (n + 15)
          (deploymentChainId (⟨0, 0⟩ : DeployParams))
          (deploymentChainId (⟨0, 0⟩ : DeployParams))
          (i - 15) 0 (by omega)]
      have hiEq : i - 15 - 10 = 0 := by omega
      rw [hiEq]
      exact deploymentChainIdByteAt_eq_zero_opcode
        locations (n + 15 + 10) dp

private theorem deploymentLeafByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchLeaf 0xcd0d0096
          (nonpayable
            (deploymentChainId
              (⟨0, 0⟩ : DeployParams)))).compileShape
        (dispatchLeaf 0xcd0d0096
          (nonpayable (deploymentChainId dp))) (26 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  have hpush : (Ninst.pushB256 (0xcd0d0096 : B256)).size = 5 := by
    decide +kernel
  rw [dispatchLeafByteAt_to_body locations n 0xcd0d0096
      (nonpayable
        (deploymentChainId (⟨0, 0⟩ : DeployParams)))
      (nonpayable (deploymentChainId dp)) (26 + j) 0 hpush (by omega)]
  have hiLeaf : 26 + j - 15 = 11 + j := by omega
  rw [hiLeaf]
  rw [nonpayableByteAt_to_body locations (n + 15)
      (deploymentChainId (⟨0, 0⟩ : DeployParams))
      (deploymentChainId dp) (11 + j) 0 (by omega)]
  have hiBody : 11 + j - 10 = j + 1 := by omega
  rw [hiBody]
  exact deploymentChainIdByteAt_chainWord
    locations (n + 15 + 10) dp j hj

private theorem dispatch24_21_3ByteAt_eq_zero_0_113
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 113) :
    Func.byteAtByShape locations n
        (dispatch24_21_3 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_21_3 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch24_21_3 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_21_3 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch24_21_3_eq_factored dp,
    dispatch24_21_3_eq_factored (⟨0, 0⟩ : DeployParams)]
  unfold dispatch24Factored
  have hdepositPush :
      (Ninst.pushB256 (0xd0e30db0 : B256)).size = 5 := by
    decide +kernel
  have hdeploymentPush :
      (Ninst.pushB256 (0xcd0d0096 : B256)).size = 5 := by
    decide +kernel
  have hdepositLeaf :
      (dispatchLeaf 0xd0e30db0 deposit).compileShape.byteSize = 64 :=
        depositDispatchLeaf_size
  by_cases hroot : i < 11
  · exact dispatchNodeByteAt_eq_prefix locations n 0xd0e30db0
      (dispatchNode 0xcd0d0096
        (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
        (dispatchLeaf 0xcd0d0096
          (nonpayable
            (deploymentChainId (⟨0, 0⟩ : DeployParams)))))
      (dispatchLeaf 0xd0e30db0 deposit)
      (dispatchNode 0xcd0d0096
        (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
        (dispatchLeaf 0xcd0d0096
          (nonpayable (deploymentChainId dp))))
      (dispatchLeaf 0xd0e30db0 deposit) hdepositPush i hroot
  · by_cases hon : i - 11 < 64
    · rw [dispatchNodeByteAt_to_onPath
          (locations := locations) (n := n) (selector := 0xd0e30db0)
          (off0 := dispatchNode 0xcd0d0096
            (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
            (dispatchLeaf 0xcd0d0096
              (nonpayable
                (deploymentChainId
                  (⟨0, 0⟩ : DeployParams)))))
          (on0 := dispatchLeaf 0xd0e30db0 deposit)
          (off := dispatchNode 0xcd0d0096
            (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
            (dispatchLeaf 0xcd0d0096
              (nonpayable (deploymentChainId dp))))
          (on := dispatchLeaf 0xd0e30db0 deposit)
          (i := i) (d := 0) hdepositPush (by omega)
          (by simpa only [hdepositLeaf] using hon),
        dispatchNodeByteAt_to_onPath
          (locations := locations) (n := n) (selector := 0xd0e30db0)
          (off0 := dispatchNode 0xcd0d0096
            (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
            (dispatchLeaf 0xcd0d0096
              (nonpayable
                (deploymentChainId
                  (⟨0, 0⟩ : DeployParams)))))
          (on0 := dispatchLeaf 0xd0e30db0 deposit)
          (off := dispatchNode 0xcd0d0096
            (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
            (dispatchLeaf 0xcd0d0096
              (nonpayable
                (deploymentChainId
                  (⟨0, 0⟩ : DeployParams)))))
          (on := dispatchLeaf 0xd0e30db0 deposit)
          (i := i) (d := 0) hdepositPush (by omega)
          (by simpa only [hdepositLeaf] using hon)]
    · by_cases hjump : i = 75
      · have hiEq : i = 11 +
            (dispatchLeaf 0xd0e30db0 deposit).compileShape.byteSize := by
          rw [hdepositLeaf]
          omega
        rw [hiEq]
        exact dispatchNodeByteAt_eq_jumpdest locations n 0xd0e30db0
          (dispatchNode 0xcd0d0096
            (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
            (dispatchLeaf 0xcd0d0096
              (nonpayable
                (deploymentChainId
                  (⟨0, 0⟩ : DeployParams)))))
          (dispatchLeaf 0xd0e30db0 deposit)
          (dispatchNode 0xcd0d0096
            (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
            (dispatchLeaf 0xcd0d0096
              (nonpayable (deploymentChainId dp))))
          (dispatchLeaf 0xd0e30db0 deposit) hdepositPush
      · rw [dispatchNodeByteAt_to_offPath
            (locations := locations) (n := n) (selector := 0xd0e30db0)
            (off0 := dispatchNode 0xcd0d0096
              (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
              (dispatchLeaf 0xcd0d0096
                (nonpayable
                  (deploymentChainId
                    (⟨0, 0⟩ : DeployParams)))))
            (on0 := dispatchLeaf 0xd0e30db0 deposit)
            (off := dispatchNode 0xcd0d0096
              (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
              (dispatchLeaf 0xcd0d0096
                (nonpayable (deploymentChainId dp))))
            (on := dispatchLeaf 0xd0e30db0 deposit)
            (i := i) (d := 0) hdepositPush (by
              rw [hdepositLeaf]
              omega),
          dispatchNodeByteAt_to_offPath
            (locations := locations) (n := n) (selector := 0xd0e30db0)
            (off0 := dispatchNode 0xcd0d0096
              (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
              (dispatchLeaf 0xcd0d0096
                (nonpayable
                  (deploymentChainId
                    (⟨0, 0⟩ : DeployParams)))))
            (on0 := dispatchLeaf 0xd0e30db0 deposit)
            (off := dispatchNode 0xcd0d0096
              (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
              (dispatchLeaf 0xcd0d0096
                (nonpayable
                  (deploymentChainId
                    (⟨0, 0⟩ : DeployParams)))))
            (on := dispatchLeaf 0xd0e30db0 deposit)
            (i := i) (d := 0) hdepositPush (by
              rw [hdepositLeaf]
              omega)]
        simp only [hdepositLeaf, Nat.reduceAdd]
        by_cases hinner : i - 76 < 11
        · exact dispatchNodeByteAt_eq_prefix locations (n + 76)
            0xcd0d0096
            (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
            (dispatchLeaf 0xcd0d0096
              (nonpayable
                (deploymentChainId
                  (⟨0, 0⟩ : DeployParams))))
            (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
            (dispatchLeaf 0xcd0d0096
              (nonpayable (deploymentChainId dp)))
            hdeploymentPush (i - 76) hinner
        · have hdeploymentLeaf :
              (dispatchLeaf 0xcd0d0096
                (nonpayable
                  (deploymentChainId
                    (⟨0, 0⟩ : DeployParams)))).compileShape.byteSize =
                64 := by
            decide +kernel
          rw [dispatchNodeByteAt_to_onPath
                (locations := locations) (n := n + 76)
                (selector := 0xcd0d0096)
                (off0 := dispatchLeaf 0xcae9ca51
                  (nonpayable approveAndCall))
                (on0 := dispatchLeaf 0xcd0d0096
                  (nonpayable
                    (deploymentChainId
                      (⟨0, 0⟩ : DeployParams))))
                (off := dispatchLeaf 0xcae9ca51
                  (nonpayable approveAndCall))
                (on := dispatchLeaf 0xcd0d0096
                  (nonpayable (deploymentChainId dp)))
                (i := i - 76) (d := 0) hdeploymentPush (by omega)
                (by rw [hdeploymentLeaf]; omega),
              dispatchNodeByteAt_to_onPath
                (locations := locations) (n := n + 76)
                (selector := 0xcd0d0096)
                (off0 := dispatchLeaf 0xcae9ca51
                  (nonpayable approveAndCall))
                (on0 := dispatchLeaf 0xcd0d0096
                  (nonpayable
                    (deploymentChainId
                      (⟨0, 0⟩ : DeployParams))))
                (off := dispatchLeaf 0xcae9ca51
                  (nonpayable approveAndCall))
                (on := dispatchLeaf 0xcd0d0096
                  (nonpayable
                    (deploymentChainId
                      (⟨0, 0⟩ : DeployParams))))
                (i := i - 76) (d := 0) hdeploymentPush (by omega)
                (by rw [hdeploymentLeaf]; omega)]
          apply deploymentLeafByteAt_eq_zero_0_26
          omega

private theorem dispatch24_21_3ByteAt_chainWord
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatch24_21_3 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_21_3 dp) (113 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  rw [dispatch24_21_3_eq_factored dp,
    dispatch24_21_3_eq_factored (⟨0, 0⟩ : DeployParams)]
  unfold dispatch24Factored
  have hdepositPush :
      (Ninst.pushB256 (0xd0e30db0 : B256)).size = 5 := by
    decide +kernel
  have hdeploymentPush :
      (Ninst.pushB256 (0xcd0d0096 : B256)).size = 5 := by
    decide +kernel
  have hdepositLeaf :
      (dispatchLeaf 0xd0e30db0 deposit).compileShape.byteSize = 64 :=
        depositDispatchLeaf_size
  rw [dispatchNodeByteAt_to_offPath
      (locations := locations) (n := n) (selector := 0xd0e30db0)
      (off0 := dispatchNode 0xcd0d0096
        (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
        (dispatchLeaf 0xcd0d0096
          (nonpayable
            (deploymentChainId (⟨0, 0⟩ : DeployParams)))))
      (on0 := dispatchLeaf 0xd0e30db0 deposit)
      (off := dispatchNode 0xcd0d0096
        (dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
        (dispatchLeaf 0xcd0d0096
          (nonpayable (deploymentChainId dp))))
      (on := dispatchLeaf 0xd0e30db0 deposit)
      (i := 113 + j) (d := 0) hdepositPush (by
        rw [hdepositLeaf]
        omega)]
  simp only [hdepositLeaf, Nat.reduceAdd]
  have hdeploymentLeaf :
      (dispatchLeaf 0xcd0d0096
        (nonpayable
          (deploymentChainId
            (⟨0, 0⟩ : DeployParams)))).compileShape.byteSize = 64 :=
        deploymentChainIdDispatchLeaf_size
  rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n + 76)
      (selector := 0xcd0d0096)
      (off0 := dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
      (on0 := dispatchLeaf 0xcd0d0096
        (nonpayable
          (deploymentChainId (⟨0, 0⟩ : DeployParams))))
      (off := dispatchLeaf 0xcae9ca51 (nonpayable approveAndCall))
      (on := dispatchLeaf 0xcd0d0096
        (nonpayable (deploymentChainId dp)))
      (i := 113 + j - 76) (d := 0) hdeploymentPush (by omega)
      (by rw [hdeploymentLeaf]; omega)]
  have hi : 113 + j - 76 - 11 = 26 + j := by omega
  rw [hi]
  exact deploymentLeafByteAt_chainWord
    locations (n + 76 + 11) dp j hj

private theorem flashFeeDispatchByteAt_to_dispatch24_21_3
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 566 ≤ i)
    (hinside : i - 566 <
      (dispatch24_21_3
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (flashFeeDispatch (⟨0, 0⟩ : DeployParams)).compileShape
        (flashFeeDispatch dp) i d =
      Func.byteAtByShape locations (n + 566)
        (dispatch24_21_3
          (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_21_3 dp) (i - 566) d := by
  unfold flashFeeDispatch
  have hrootPush :
      (Ninst.pushB256 (0x7ecebe00 : B256)).size = 5 := by
    decide +kernel
  have hcae9Size :
      (dispatchCae9
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 1769 :=
        dispatchCae9_size
  have hdispatch24Size :
      (dispatch24_21_3
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 391 :=
        dispatch24_21_3_size
  conv_lhs => rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n) (selector := 0x7ecebe00)
      (off0 := dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchCae9 (⟨0, 0⟩ : DeployParams))
      (off := dispatch26_0_14 dp) (on := dispatchCae9 dp)
      (i := i) (d := d) hrootPush (by omega) (by
        rw [hcae9Size]
        rw [hdispatch24Size] at hinside
        omega)]
  unfold dispatchCae9
  have hcae9Push :
      (Ninst.pushB256 (0xcae9ca51 : B256)).size = 5 := by
    decide +kernel
  have hd505Size :
      (dispatchD505
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 935 :=
        dispatchD505_size
  conv_lhs => rw [dispatchNodeByteAt_to_onPath
      (locations := locations) (n := n + 11)
      (selector := 0xcae9ca51)
      (off0 := dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchD505 (⟨0, 0⟩ : DeployParams))
      (off := dispatch25_14_7 dp) (on := dispatchD505 dp)
      (i := i - 11) (d := d) hcae9Push (by omega) (by
        rw [hd505Size]
        rw [hdispatch24Size] at hinside
        omega)]
  unfold dispatchD505
  have hd505Push :
      (Ninst.pushB256 (0xd505accf : B256)).size = 5 := by
    decide +kernel
  have hddSize :
      (dispatchDd
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 532 :=
        dispatchDd_size
  conv_lhs => rw [dispatchNodeByteAt_to_offPath
      (locations := locations) (n := n + 11 + 11)
      (selector := 0xd505accf)
      (off0 := dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
      (on0 := dispatchDd (⟨0, 0⟩ : DeployParams))
      (off := dispatch24_21_3 dp) (on := dispatchDd dp)
      (i := i - 11 - 11) (d := d) hd505Push (by
        rw [hddSize]
        omega)]
  simp only [hddSize, Nat.reduceAdd]
  have hn : n + 11 + 11 + 12 + 532 = n + 566 := by omega
  have hi : i - 11 - 11 - (12 + 532) = i - 566 := by omega
  rw [hn, hi]

private theorem weth10DispatchByteAt_to_dispatch24_21_3
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (d : UInt8) (hlo : 566 ≤ i)
    (hinside : i - 566 <
      (dispatch24_21_3
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i d =
      Func.byteAtByShape locations (n + 566)
        (dispatch24_21_3
          (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_21_3 dp) (i - 566) d := by
  rw [flashFeeDispatch_eq dp,
    flashFeeDispatch_eq (⟨0, 0⟩ : DeployParams)]
  exact flashFeeDispatchByteAt_to_dispatch24_21_3
    locations n dp i d hlo hinside

private theorem weth10DispatchByteAt_eq_zero_565
    (locations : List Nat) (n : Nat) (dp : DeployParams) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) 565 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) 565 0 := by
  rw [flashFeeDispatch_eq dp,
    flashFeeDispatch_eq (⟨0, 0⟩ : DeployParams)]
  unfold flashFeeDispatch
  have hrootPush :
      (Ninst.pushB256 (0x7ecebe00 : B256)).size = 5 := by
    decide +kernel
  have hcae9Size :
      (dispatchCae9
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 1769 :=
        dispatchCae9_size
  rw [dispatchNodeByteAt_to_onPath
        (locations := locations) (n := n) (selector := 0x7ecebe00)
        (off0 := dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
        (on0 := dispatchCae9 (⟨0, 0⟩ : DeployParams))
        (off := dispatch26_0_14 dp) (on := dispatchCae9 dp)
        (i := 565) (d := 0) hrootPush (by omega) (by
          rw [hcae9Size]
          omega),
      dispatchNodeByteAt_to_onPath
        (locations := locations) (n := n) (selector := 0x7ecebe00)
        (off0 := dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
        (on0 := dispatchCae9 (⟨0, 0⟩ : DeployParams))
        (off := dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
        (on := dispatchCae9 (⟨0, 0⟩ : DeployParams))
        (i := 565) (d := 0) hrootPush (by omega) (by
          rw [hcae9Size]
          omega)]
  unfold dispatchCae9
  have hcae9Push :
      (Ninst.pushB256 (0xcae9ca51 : B256)).size = 5 := by
    decide +kernel
  have hd505Size :
      (dispatchD505
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 935 :=
        dispatchD505_size
  rw [dispatchNodeByteAt_to_onPath
        (locations := locations) (n := n + 11)
        (selector := 0xcae9ca51)
        (off0 := dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
        (on0 := dispatchD505 (⟨0, 0⟩ : DeployParams))
        (off := dispatch25_14_7 dp) (on := dispatchD505 dp)
        (i := 565 - 11) (d := 0) hcae9Push (by omega) (by
          rw [hd505Size]
          omega),
      dispatchNodeByteAt_to_onPath
        (locations := locations) (n := n + 11)
        (selector := 0xcae9ca51)
        (off0 := dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
        (on0 := dispatchD505 (⟨0, 0⟩ : DeployParams))
        (off := dispatch25_14_7 (⟨0, 0⟩ : DeployParams))
        (on := dispatchD505 (⟨0, 0⟩ : DeployParams))
        (i := 565 - 11) (d := 0) hcae9Push (by omega) (by
          rw [hd505Size]
          omega)]
  unfold dispatchD505
  have hd505Push :
      (Ninst.pushB256 (0xd505accf : B256)).size = 5 := by
    decide +kernel
  have hddSize :
      (dispatchDd
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 532 :=
        dispatchDd_size
  have hi : 565 - 11 - 11 = 11 +
      (dispatchDd
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize := by
    rw [hddSize]
  rw [hi]
  exact dispatchNodeByteAt_eq_jumpdest locations (n + 11 + 11)
    0xd505accf
    (dispatch24_21_3 (⟨0, 0⟩ : DeployParams))
    (dispatchDd (⟨0, 0⟩ : DeployParams))
    (dispatch24_21_3 dp) (dispatchDd dp) hd505Push

theorem weth10DispatchByteAt_eq_zero_556_679
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 556 ≤ i) (hi : i < 679) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  by_cases hpermit : i < 565
  · have hpermitSize :
        (permit (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 326 :=
        permit_size
    have hloPermit : 239 ≤ i := by omega
    have hinsidePermit : i - 239 < 326 := by omega
    rw [weth10DispatchByteAt_to_permit locations n dp i 0
          hloPermit (by simpa only [hpermitSize] using hinsidePermit),
      weth10DispatchByteAt_to_permit locations n
        (⟨0, 0⟩ : DeployParams) i 0
          hloPermit (by simpa only [hpermitSize] using hinsidePermit)]
    apply permitByteAt_eq_zero_317_326
    · omega
    · omega
  · by_cases hjump : i = 565
    · subst i
      exact weth10DispatchByteAt_eq_zero_565 locations n dp
    · have hdispatch24Size :
        (dispatch24_21_3
          (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 391 :=
        dispatch24_21_3_size
      rw [weth10DispatchByteAt_to_dispatch24_21_3 locations n dp i 0
            (by omega) (by rw [hdispatch24Size]; omega),
        weth10DispatchByteAt_to_dispatch24_21_3 locations n
          (⟨0, 0⟩ : DeployParams) i 0
            (by omega) (by rw [hdispatch24Size]; omega)]
      apply dispatch24_21_3ByteAt_eq_zero_0_113
      omega

theorem weth10DispatchByteAt_chainWord_691
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) (679 + j) 0 =
      dp.deploymentChainId.toBytes.getD j 0 := by
  have hdispatch24Size :
      (dispatch24_21_3
        (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 391 :=
        dispatch24_21_3_size
  rw [weth10DispatchByteAt_to_dispatch24_21_3
      locations n dp (679 + j) 0 (by omega) (by
        rw [hdispatch24Size]
        omega)]
  have hi : 679 + j - 566 = 113 + j := by omega
  rw [hi]
  exact dispatch24_21_3ByteAt_chainWord
    locations (n + 566) dp j hj

end Weth10

end Blanc


