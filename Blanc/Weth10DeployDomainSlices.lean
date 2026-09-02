import Blanc.Weth10Code
import Blanc.Forward

namespace Blanc

open Jaune

namespace Weth10

/-! Shape-indexed byte classification for the parameterized lower dispatcher.
The proofs isolate the two generated deployment words while keeping all
off-path subtrees opaque. -/

private def lineByteSize : Line → Nat
  | [] => 0
  | inst :: rest => inst.size + lineByteSize rest

private theorem byteAt_prepend_eq_prefix
    (locations : List Nat) (n : Nat) (l : Line) (p0 p : Func)
    (i : Nat) (d : UInt8) (hi : i < lineByteSize l) :
    Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p) i d =
      Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p0) i d := by
  induction l generalizing n i with
  | nil => simp [lineByteSize] at hi
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
        simp only [lineByteSize] at hi
        omega

private theorem byteAt_prepend_to_tail
    (locations : List Nat) (n : Nat) (l : Line) (p0 p : Func)
    (i : Nat) (d : UInt8) (hlo : lineByteSize l ≤ i) :
    Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p) i d =
      Func.byteAtByShape locations (n + lineByteSize l) p0.compileShape
        p (i - lineByteSize l) d := by
  induction l generalizing n i with
  | nil => simp [lineByteSize, prepend]
  | cons inst rest ih =>
      have hinst : inst.size ≤ i := by
        simp only [lineByteSize] at hlo
        omega
      change
        Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p)) i d = _
      conv_lhs => rw [Func.byteAtByShape, if_neg (Nat.not_lt_of_ge hinst)]
      rw [ih (n := n + inst.size) (i := i - inst.size) (by
        simp only [lineByteSize] at hlo
        omega)]
      simp only [lineByteSize, Nat.add_assoc, Nat.sub_sub]

private theorem byteAt_next_to_tail
    (locations : List Nat) (n : Nat) (inst0 inst : Ninst)
    (p0 p : Func) (i : Nat) (d : UInt8)
    (_hsize : inst.size = inst0.size) (hlo : inst0.size ≤ i) :
    Func.byteAtByShape locations n (inst0 ::: p0).compileShape
        (inst ::: p) i d =
      Func.byteAtByShape locations (n + inst0.size) p0.compileShape
        p (i - inst0.size) d := by
  change
    Func.byteAtByShape locations n (.next inst0.size p0.compileShape)
        (inst ::: p) i d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (Nat.not_lt_of_ge hlo)]

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
      simp [Func.byteAtByShape]

private theorem pushDeployWord_opcode_eq
    (locations : List Nat) (n : Nat) (p0 p : Func) (w : B256) :
    Func.byteAtByShape locations n (pushDeployWord 0 ::: p0).compileShape
        (pushDeployWord w ::: p) 0 0 =
      Func.byteAtByShape locations n (pushDeployWord 0 ::: p0).compileShape
        (pushDeployWord 0 ::: p0) 0 0 := by
  simp [Func.byteAtByShape, Func.compileShape, pushDeployWord,
    Ninst.toBytes, Ninst.size, pushToB8L, pushToB8,
    B256.length_toBytes]

private theorem pushDeployWord_word_byte
    (locations : List Nat) (n : Nat) (p0 p : Func) (w : B256)
    (j : Nat) (hj : j < 32) (d : UInt8) :
    Func.byteAtByShape locations n (pushDeployWord 0 ::: p0).compileShape
        (pushDeployWord w ::: p) (j + 1) d =
      w.toBytes.getD j d := by
  have hsize0 : (pushDeployWord 0).size = 33 := by
    simp [pushDeployWord, Ninst.size, B256.length_toBytes]
  change
    Func.byteAtByShape locations n
      (.next (pushDeployWord 0).size p0.compileShape)
      (pushDeployWord w ::: p) (j + 1) d = _
  rw [Func.byteAtByShape, if_pos (by
    simpa only [hsize0] using Nat.add_lt_add_right hj 1)]
  rw [hsize0]
  simp only [pushDeployWord, Ninst.toBytes, pushToB8L, pushToB8,
    B256.length_toBytes]
  rw [List.takeD_eq_self 0 (by
    simp only [B256.length_toBytes, List.length_cons])]
  simp

private def domainHead : Line := [Ninst.chainid, Ninst.dup 0]

private def domainCalculatePath : Func :=
  calculateDomainSeparator +++ mstoreAt 0 +++ returnMemoryRange 0 32

private def domainReturnTail : Func :=
  mstoreAt 0 +++ returnMemoryRange 0 32

private def domainCachedPath (dp : DeployParams) : Func :=
  Ninst.pop ::: pushDeployWord dp.cachedDomainSeparator ::: domainReturnTail

private def domainAfterChain (dp : DeployParams) : Func :=
  Ninst.eq ::: Func.branch domainCalculatePath (domainCachedPath dp)

private def domainFactored (dp : DeployParams) : Func :=
  domainHead +++
    (pushDeployWord dp.deploymentChainId ::: domainAfterChain dp)

private theorem domainSeparator_eq_factored (dp : DeployParams) :
    domainSeparator dp = domainFactored dp := by
  rfl

private theorem domainCachedPathByteAt_eq_zero_0_2
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 2) :
    Func.byteAtByShape locations n
        (domainCachedPath (⟨0, 0⟩ : DeployParams)).compileShape
        (domainCachedPath dp) i 0 =
      Func.byteAtByShape locations n
        (domainCachedPath (⟨0, 0⟩ : DeployParams)).compileShape
        (domainCachedPath (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold domainCachedPath
  change
    Func.byteAtByShape locations n
        (.next Ninst.pop.size
          (pushDeployWord 0 ::: domainReturnTail).compileShape)
        (Ninst.pop :::
          pushDeployWord dp.cachedDomainSeparator ::: domainReturnTail) i 0 =
      Func.byteAtByShape locations n
        (.next Ninst.pop.size
          (pushDeployWord 0 ::: domainReturnTail).compileShape)
        (Ninst.pop ::: pushDeployWord 0 ::: domainReturnTail) i 0
  by_cases hpop : i < 1
  · conv_lhs => rw [Func.byteAtByShape, if_pos (by
      simpa only [Ninst.size] using hpop)]
    conv_rhs => rw [Func.byteAtByShape, if_pos (by
      simpa only [Ninst.size] using hpop)]
  · have hi1 : i = 1 := by omega
    subst i
    conv_lhs => rw [Func.byteAtByShape, if_neg (by
      simp only [Ninst.size]
      omega)]
    conv_rhs => rw [Func.byteAtByShape, if_neg (by
      simp only [Ninst.size]
      omega)]
    simp only [Ninst.size, Nat.reduceSub]
    exact pushDeployWord_opcode_eq _ _ _ _ _

private theorem domainCachedPathByteAt_word
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 2 ≤ i) (hi : i < 34) :
      Func.byteAtByShape locations n
        (domainCachedPath (⟨0, 0⟩ : DeployParams)).compileShape
        (domainCachedPath dp) i 0 =
      dp.cachedDomainSeparator.toBytes.getD (i - 2) 0 := by
  unfold domainCachedPath
  change
    Func.byteAtByShape locations n
        (.next Ninst.pop.size
          (pushDeployWord 0 ::: domainReturnTail).compileShape)
        (Ninst.pop :::
          pushDeployWord dp.cachedDomainSeparator ::: domainReturnTail) i 0 = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [Ninst.size]
    omega)]
  simp only [Ninst.size]
  have hj : i - 2 < 32 := by omega
  have hidx : i - 1 = (i - 2) + 1 := by omega
  rw [hidx]
  exact pushDeployWord_word_byte locations (n + 1) domainReturnTail
    domainReturnTail dp.cachedDomainSeparator (i - 2) hj 0

private theorem domainCachedPathByteAt_eq_zero_34_40
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 34 ≤ i) (hi : i < 40) :
    Func.byteAtByShape locations n
        (domainCachedPath (⟨0, 0⟩ : DeployParams)).compileShape
        (domainCachedPath dp) i 0 =
      Func.byteAtByShape locations n
        (domainCachedPath (⟨0, 0⟩ : DeployParams)).compileShape
        (domainCachedPath (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold domainCachedPath
  change
    Func.byteAtByShape locations n
        (.next Ninst.pop.size
          (pushDeployWord 0 ::: domainReturnTail).compileShape)
        (Ninst.pop :::
          pushDeployWord dp.cachedDomainSeparator ::: domainReturnTail) i 0 =
      Func.byteAtByShape locations n
        (.next Ninst.pop.size
          (pushDeployWord 0 ::: domainReturnTail).compileShape)
        (Ninst.pop ::: pushDeployWord 0 ::: domainReturnTail) i 0
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [Ninst.size]
    omega)]
  conv_rhs => rw [Func.byteAtByShape, if_neg (by
    simp only [Ninst.size]
    omega)]
  simp only [Ninst.size]
  have hsize : (pushDeployWord dp.cachedDomainSeparator).size =
      (pushDeployWord 0).size := by
    simp [pushDeployWord, Ninst.size, B256.length_toBytes]
  rw [byteAt_next_to_tail locations (n + 1)
      (pushDeployWord 0) (pushDeployWord dp.cachedDomainSeparator)
      domainReturnTail domainReturnTail (i - 1) 0 hsize (by
        simp [pushDeployWord, Ninst.size, B256.length_toBytes]
        omega),
    byteAt_next_to_tail locations (n + 1)
      (pushDeployWord 0) (pushDeployWord 0)
      domainReturnTail domainReturnTail (i - 1) 0 rfl (by
        simp [pushDeployWord, Ninst.size, B256.length_toBytes]
        omega)]

private theorem domainAfterChainByteAt_eq_zero_0_132
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 132) :
    Func.byteAtByShape locations n
        (domainAfterChain (⟨0, 0⟩ : DeployParams)).compileShape
        (domainAfterChain dp) i 0 =
      Func.byteAtByShape locations n
        (domainAfterChain (⟨0, 0⟩ : DeployParams)).compileShape
        (domainAfterChain (⟨0, 0⟩ : DeployParams)) i 0 := by
  unfold domainAfterChain
  change
    Func.byteAtByShape locations n
        (.next Ninst.eq.size
          (.branch domainCalculatePath.compileShape
            (domainCachedPath (⟨0, 0⟩ : DeployParams)).compileShape))
        (Ninst.eq :::
          Func.branch domainCalculatePath (domainCachedPath dp)) i 0 =
      Func.byteAtByShape locations n
        (.next Ninst.eq.size
          (.branch domainCalculatePath.compileShape
            (domainCachedPath (⟨0, 0⟩ : DeployParams)).compileShape))
        (Ninst.eq ::: Func.branch domainCalculatePath
          (domainCachedPath (⟨0, 0⟩ : DeployParams))) i 0
  by_cases heq : i < 1
  · conv_lhs => rw [Func.byteAtByShape, if_pos (by
      simpa only [Ninst.size] using heq)]
    conv_rhs => rw [Func.byteAtByShape, if_pos (by
      simpa only [Ninst.size] using heq)]
  · conv_lhs => rw [Func.byteAtByShape, if_neg (by
      simpa only [Ninst.size] using heq)]
    conv_rhs => rw [Func.byteAtByShape, if_neg (by
      simpa only [Ninst.size] using heq)]
    simp only [Ninst.size]
    have hcalc : domainCalculatePath.compileShape.byteSize = 124 := by
      decide +kernel
    by_cases hbefore : i - 1 < 129
    · apply byteAt_branch_eq_before_right
      simpa only [hcalc, Nat.reduceAdd] using hbefore
    · rw [byteAt_branch_to_right locations (n + 1) domainCalculatePath
          (domainCachedPath (⟨0, 0⟩ : DeployParams)) domainCalculatePath
          (domainCachedPath dp) (i - 1) 0 (by
            simp only [hcalc, Nat.reduceAdd]
            omega),
        byteAt_branch_to_right locations (n + 1) domainCalculatePath
          (domainCachedPath (⟨0, 0⟩ : DeployParams)) domainCalculatePath
          (domainCachedPath (⟨0, 0⟩ : DeployParams)) (i - 1) 0 (by
            simp only [hcalc, Nat.reduceAdd]
            omega)]
      simp only [hcalc, Nat.reduceAdd]
      apply domainCachedPathByteAt_eq_zero_0_2
      omega

private theorem domainAfterChainByteAt_to_cachedPath
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 130 ≤ i) :
    Func.byteAtByShape locations n
        (domainAfterChain (⟨0, 0⟩ : DeployParams)).compileShape
        (domainAfterChain dp) i 0 =
      Func.byteAtByShape locations (n + 130)
        (domainCachedPath (⟨0, 0⟩ : DeployParams)).compileShape
        (domainCachedPath dp) (i - 130) 0 := by
  unfold domainAfterChain
  change
    Func.byteAtByShape locations n
        (.next Ninst.eq.size
          (.branch domainCalculatePath.compileShape
            (domainCachedPath (⟨0, 0⟩ : DeployParams)).compileShape))
        (Ninst.eq :::
          Func.branch domainCalculatePath (domainCachedPath dp)) i 0 = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [Ninst.size]
    omega)]
  simp only [Ninst.size]
  have hcalc : domainCalculatePath.compileShape.byteSize = 124 := by
    decide +kernel
  rw [byteAt_branch_to_right locations (n + 1) domainCalculatePath
      (domainCachedPath (⟨0, 0⟩ : DeployParams)) domainCalculatePath
      (domainCachedPath dp) (i - 1) 0 (by
        simp only [hcalc, Nat.reduceAdd]
        omega)]
  simp only [hcalc, Nat.reduceAdd]
  congr 1

private theorem domainByteAt_to_afterChain
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 35 ≤ i) :
    Func.byteAtByShape locations n
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator dp) i 0 =
      Func.byteAtByShape locations (n + 35)
        (domainAfterChain (⟨0, 0⟩ : DeployParams)).compileShape
        (domainAfterChain dp) (i - 35) 0 := by
  rw [domainSeparator_eq_factored dp,
    domainSeparator_eq_factored (⟨0, 0⟩ : DeployParams)]
  unfold domainFactored
  have hhead : lineByteSize domainHead = 2 := by decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
    (locations := locations) (n := n) (l := domainHead)
    (p0 := pushDeployWord 0 ::: domainAfterChain (⟨0, 0⟩ : DeployParams))
    (p := pushDeployWord dp.deploymentChainId ::: domainAfterChain dp)
    (i := i) (d := 0) (by simpa only [hhead] using (show 2 ≤ i by omega))]
  simp only [hhead]
  have hsize : (pushDeployWord dp.deploymentChainId).size =
      (pushDeployWord 0).size := by
    simp [pushDeployWord, Ninst.size, B256.length_toBytes]
  rw [byteAt_next_to_tail locations (n + 2)
      (pushDeployWord 0) (pushDeployWord dp.deploymentChainId)
      (domainAfterChain (⟨0, 0⟩ : DeployParams)) (domainAfterChain dp)
      (i - 2) 0 hsize (by
        simp [pushDeployWord, Ninst.size, B256.length_toBytes]
        omega)]
  simp [pushDeployWord, Ninst.size, B256.length_toBytes]
  congr 1

private theorem domainSeparatorByteAt_eq_zero_0_3
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 3) :
    Func.byteAtByShape locations n
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator dp) i 0 =
      Func.byteAtByShape locations n
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [domainSeparator_eq_factored dp,
    domainSeparator_eq_factored (⟨0, 0⟩ : DeployParams)]
  unfold domainFactored
  have hhead : lineByteSize domainHead = 2 := by decide +kernel
  by_cases hpre : i < 2
  · apply byteAt_prepend_eq_prefix
    simpa only [hhead] using hpre
  · have hi2 : i = 2 := by omega
    subst i
    conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := domainHead)
      (p0 := pushDeployWord 0 ::: domainAfterChain (⟨0, 0⟩ : DeployParams))
      (p := pushDeployWord dp.deploymentChainId ::: domainAfterChain dp)
      (i := 2) (d := 0) (by omega)]
    conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := domainHead)
      (p0 := pushDeployWord 0 ::: domainAfterChain (⟨0, 0⟩ : DeployParams))
      (p := pushDeployWord 0 ::: domainAfterChain (⟨0, 0⟩ : DeployParams))
      (i := 2) (d := 0) (by omega)]
    simp only [hhead, Nat.reduceSub]
    exact pushDeployWord_opcode_eq _ _ _ _ _

private theorem domainSeparatorByteAt_deploymentWord_3_35
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 3 ≤ i) (hi : i < 35) :
    Func.byteAtByShape locations n
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator dp) i 0 =
      dp.deploymentChainId.toBytes.getD (i - 3) 0 := by
  rw [domainSeparator_eq_factored dp,
    domainSeparator_eq_factored (⟨0, 0⟩ : DeployParams)]
  unfold domainFactored
  have hhead : lineByteSize domainHead = 2 := by decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
    (locations := locations) (n := n) (l := domainHead)
    (p0 := pushDeployWord 0 ::: domainAfterChain (⟨0, 0⟩ : DeployParams))
    (p := pushDeployWord dp.deploymentChainId ::: domainAfterChain dp)
    (i := i) (d := 0) (by simpa only [hhead] using (show 2 ≤ i by omega))]
  simp only [hhead]
  have hj : i - 3 < 32 := by omega
  have hidx : i - 2 = (i - 3) + 1 := by omega
  rw [hidx]
  exact pushDeployWord_word_byte locations (n + 2)
    (domainAfterChain (⟨0, 0⟩ : DeployParams)) (domainAfterChain dp)
    dp.deploymentChainId (i - 3) hj 0

private theorem domainSeparatorByteAt_eq_zero_35_167
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 35 ≤ i) (hi : i < 167) :
    Func.byteAtByShape locations n
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator dp) i 0 =
      Func.byteAtByShape locations n
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [domainByteAt_to_afterChain locations n dp i hlo,
    domainByteAt_to_afterChain locations n
      (⟨0, 0⟩ : DeployParams) i hlo]
  apply domainAfterChainByteAt_eq_zero_0_132
  omega

private theorem domainSeparatorByteAt_cachedWord_167_199
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 167 ≤ i) (hi : i < 199) :
    Func.byteAtByShape locations n
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator dp) i 0 =
      dp.cachedDomainSeparator.toBytes.getD (i - 167) 0 := by
  rw [domainByteAt_to_afterChain locations n dp i (by omega),
    domainAfterChainByteAt_to_cachedPath locations (n + 35) dp
      (i - 35) (by omega)]
  have hn : n + 35 + 130 = n + 165 := by omega
  have hread : i - 35 - 130 = i - 165 := by omega
  rw [hn, hread]
  have hword := domainCachedPathByteAt_word locations (n + 165) dp
    (i - 165) (by omega) (by omega)
  have hout : i - 165 - 2 = i - 167 := by omega
  rw [hout] at hword
  exact hword

private theorem domainSeparatorByteAt_eq_zero_199_205
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 199 ≤ i) (hi : i < 205) :
    Func.byteAtByShape locations n
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator dp) i 0 =
      Func.byteAtByShape locations n
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [domainByteAt_to_afterChain locations n dp i (by omega),
    domainByteAt_to_afterChain locations n
      (⟨0, 0⟩ : DeployParams) i (by omega),
    domainAfterChainByteAt_to_cachedPath locations (n + 35) dp
      (i - 35) (by omega),
    domainAfterChainByteAt_to_cachedPath locations (n + 35)
      (⟨0, 0⟩ : DeployParams) (i - 35) (by omega)]
  apply domainCachedPathByteAt_eq_zero_34_40
  · omega
  · omega

private theorem domainSeparator_size :
    (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape.byteSize = 205 := by
  decide +kernel

/-! ## DOMAIN_SEPARATOR leaf and balanced low-dispatch path -/

private def treeSlice (dp : DeployParams) (fuel lo len : Nat) : DispatchTree :=
  DispatchTree.build fuel ((weth10Funcs dp).drop lo |>.take len)

private def dispatch26_0_14 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 26 0 14)

private def dispatch26_14_13 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 26 14 13)

private def dispatch25_0_7 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 25 0 7)

private def dispatch25_7_7 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 25 7 7)

private def dispatch24_7_4 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 24 7 4)

private def dispatch24_11_3 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 24 11 3)

private def dispatch23_7_2 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 23 7 2)

private def dispatch23_9_2 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 23 9 2)

private def dispatch22_7_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 22 7 1)

private def dispatch22_8_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 22 8 1)

private def dispatchNode (selector : B256) (offPath onPath : Func) : Func :=
  Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
    (offPath <?> onPath)

private theorem dispatch26_0_14_eq_node (dp : DeployParams) :
    dispatch26_0_14 dp =
      dispatchNode (selector "decimals" [])
        (dispatch25_0_7 dp) (dispatch25_7_7 dp) := by
  simp [dispatch26_0_14, dispatch25_0_7, dispatch25_7_7, treeSlice,
    weth10Funcs, DispatchTree.build, dispatchNode, dispatchWith,
    leftmostFsig]

private theorem dispatch25_7_7_eq_node (dp : DeployParams) :
    dispatch25_7_7 dp =
      dispatchNode (selector "depositToAndCall" [.address, .dynBytes])
        (dispatch24_7_4 dp) (dispatch24_11_3 dp) := by
  simp [dispatch25_7_7, dispatch24_7_4, dispatch24_11_3, treeSlice,
    weth10Funcs, DispatchTree.build, dispatchNode, dispatchWith,
    leftmostFsig]

private theorem dispatch24_7_4_eq_node (dp : DeployParams) :
    dispatch24_7_4 dp =
      dispatchNode
        (selector "transferAndCall" [.address, .uint256, .dynBytes])
        (dispatch23_7_2 dp) (dispatch23_9_2 dp) := by
  simp [dispatch24_7_4, dispatch23_7_2, dispatch23_9_2, treeSlice,
    weth10Funcs, DispatchTree.build, dispatchNode, dispatchWith,
    leftmostFsig]

private theorem dispatch23_7_2_eq_node (dp : DeployParams) :
    dispatch23_7_2 dp =
      dispatchNode (selector "DOMAIN_SEPARATOR" [])
        (dispatch22_7_1 dp) (dispatch22_8_1 dp) := by
  simp [dispatch23_7_2, dispatch22_7_1, dispatch22_8_1, treeSlice,
    weth10Funcs, DispatchTree.build, dispatchNode, dispatchWith,
    leftmostFsig]

private theorem dispatch22_8_1_eq_leaf (dp : DeployParams) :
    dispatch22_8_1 dp =
      Ninst.pushB256 (selector "DOMAIN_SEPARATOR" []) ::: Ninst.eq :::
        ((nonpayable (domainSeparator dp)) <?> .call fallbackSlot) := by
  simp [dispatch22_8_1, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith]

private theorem fullDispatch_eq_root (dp : DeployParams) :
    dispatchWith fallbackSlot (weth10Tree dp) =
      dispatchNode (selector "nonces" [.address])
        (dispatch26_0_14 dp) (dispatch26_14_13 dp) := by
  simp [weth10Tree, DispatchTree.ofSorted, dispatch26_0_14,
    dispatch26_14_13, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchNode, dispatchWith, leftmostFsig]

/- Subtree sizes are composed bottom-up through `dispatchNode_size` from a
few leaf-level `decide`s: kernel-evaluating `byteSize` over a subtree
re-walks every leaf below it, so deciding each level independently repeated
the same traversal per lemma.  The block is ordered children-first; every
statement is unchanged. -/

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

private theorem dispatch22_7_1_size :
    (dispatch22_7_1 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      33 := by
  decide +kernel

private theorem dispatch22_8_1_size :
    (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      230 := by
  decide +kernel

private theorem dispatch23_9_2_size :
    (dispatch23_9_2 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      713 := by
  decide +kernel

private theorem dispatch24_11_3_size :
    (dispatch24_11_3 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      295 := by
  decide +kernel

private theorem dispatch25_0_7_size :
    (dispatch25_0_7 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      839 := by
  decide +kernel

private theorem dispatch26_14_13_size :
    (dispatch26_14_13 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      1769 := by
  decide +kernel

private theorem dispatch23_7_2_size :
    (dispatch23_7_2 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      275 := by
  rw [dispatch23_7_2_eq_node]
  rw [dispatchNode_size _ _ _ (by decide +kernel)]
  rw [dispatch22_8_1_size, dispatch22_7_1_size]

private theorem dispatch24_7_4_size :
    (dispatch24_7_4 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      1000 := by
  rw [dispatch24_7_4_eq_node]
  rw [dispatchNode_size _ _ _ (by decide +kernel)]
  rw [dispatch23_9_2_size, dispatch23_7_2_size]

private theorem dispatch25_7_7_size :
    (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      1307 := by
  rw [dispatch25_7_7_eq_node]
  rw [dispatchNode_size _ _ _ (by decide +kernel)]
  rw [dispatch24_11_3_size, dispatch24_7_4_size]

private theorem dispatch26_0_14_size :
    (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape.byteSize =
      2158 := by
  rw [dispatch26_0_14_eq_node]
  rw [dispatchNode_size _ _ _ (by decide +kernel)]
  rw [dispatch25_7_7_size, dispatch25_0_7_size]

theorem fullDispatch_size :
    (dispatchWith fallbackSlot
      (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape.byteSize = 3939 := by
  rw [fullDispatch_eq_root]
  rw [dispatchNode_size _ _ _ (by decide +kernel)]
  rw [dispatch26_14_13_size, dispatch26_0_14_size]

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

private def domainLeafPrefix : Line :=
  [Ninst.pushB256 (selector "DOMAIN_SEPARATOR" []), Ninst.eq]

private theorem domainLeafByteAt_to_nonpayable
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 15 ≤ i) :
    Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) i 0 =
      Func.byteAtByShape locations (n + 15)
        (nonpayable
          (domainSeparator (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayable (domainSeparator dp)) (i - 15) 0 := by
  rw [dispatch22_8_1_eq_leaf dp,
    dispatch22_8_1_eq_leaf (⟨0, 0⟩ : DeployParams)]
  change
    Func.byteAtByShape locations n
        (domainLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable
              (domainSeparator (⟨0, 0⟩ : DeployParams)))).compileShape
        (domainLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable (domainSeparator dp))) i 0 = _
  have hprefix : lineByteSize domainLeafPrefix = 6 := by decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
    (locations := locations) (n := n) (l := domainLeafPrefix)
    (p0 := Func.branch (.call fallbackSlot)
      (nonpayable (domainSeparator (⟨0, 0⟩ : DeployParams))))
    (p := Func.branch (.call fallbackSlot)
      (nonpayable (domainSeparator dp)))
    (i := i) (d := 0) (by simpa only [hprefix] using (show 6 ≤ i by omega))]
  simp only [hprefix]
  have hcall : (Func.call fallbackSlot).compileShape.byteSize = 4 := by
    decide +kernel
  change
    Func.byteAtByShape locations (n + 6)
        (.branch (Func.call fallbackSlot).compileShape
          (nonpayable
            (domainSeparator (⟨0, 0⟩ : DeployParams))).compileShape)
        (.branch (.call fallbackSlot)
          (nonpayable (domainSeparator dp))) (i - 6) 0 = _
  rw [byteAt_branch_to_right locations (n + 6) (.call fallbackSlot)
      (nonpayable (domainSeparator (⟨0, 0⟩ : DeployParams)))
      (.call fallbackSlot) (nonpayable (domainSeparator dp))
      (i - 6) 0 (by simp only [hcall, Nat.reduceAdd]; omega)]
  simp only [hcall, Nat.reduceAdd]
  congr 1

private def nonpayablePrefix : Line :=
  [Ninst.callvalue, Ninst.iszero]

private theorem nonpayableDomainByteAt_to_raw
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 10 ≤ i) :
    Func.byteAtByShape locations n
        (nonpayable
          (domainSeparator (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayable (domainSeparator dp)) i 0 =
      Func.byteAtByShape locations (n + 10)
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator dp) (i - 10) 0 := by
  change
    Func.byteAtByShape locations n
        (nonpayablePrefix +++
          Func.branch Func.revert
            (domainSeparator (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++
          Func.branch Func.revert (domainSeparator dp)) i 0 = _
  have hprefix : lineByteSize nonpayablePrefix = 2 := by decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
    (locations := locations) (n := n) (l := nonpayablePrefix)
    (p0 := Func.branch Func.revert
      (domainSeparator (⟨0, 0⟩ : DeployParams)))
    (p := Func.branch Func.revert (domainSeparator dp))
    (i := i) (d := 0) (by simpa only [hprefix] using (show 2 ≤ i by omega))]
  simp only [hprefix]
  have hrev : Func.revert.compileShape.byteSize = 3 := by decide +kernel
  change
    Func.byteAtByShape locations (n + 2)
        (.branch Func.revert.compileShape
          (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape)
        (.branch Func.revert (domainSeparator dp)) (i - 2) 0 = _
  rw [byteAt_branch_to_right locations (n + 2) Func.revert
      (domainSeparator (⟨0, 0⟩ : DeployParams)) Func.revert
      (domainSeparator dp) (i - 2) 0
      (by simp only [hrev, Nat.reduceAdd]; omega)]
  simp only [hrev, Nat.reduceAdd]
  congr 1

private theorem domainLeafByteAt_to_raw
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 25 ≤ i) :
    Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) i 0 =
      Func.byteAtByShape locations (n + 25)
        (domainSeparator (⟨0, 0⟩ : DeployParams)).compileShape
        (domainSeparator dp) (i - 25) 0 := by
  rw [domainLeafByteAt_to_nonpayable locations n dp i (by omega),
    nonpayableDomainByteAt_to_raw locations (n + 15) dp
      (i - 15) (by omega)]
  congr 1

private theorem domainLeafByteAt_eq_zero_0_15
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 15) :
    Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch22_8_1_eq_leaf dp,
    dispatch22_8_1_eq_leaf (⟨0, 0⟩ : DeployParams)]
  change
    Func.byteAtByShape locations n
        (domainLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable
              (domainSeparator (⟨0, 0⟩ : DeployParams)))).compileShape
        (domainLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable (domainSeparator dp))) i 0 =
      Func.byteAtByShape locations n
        (domainLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable
              (domainSeparator (⟨0, 0⟩ : DeployParams)))).compileShape
        (domainLeafPrefix +++
          Func.branch (.call fallbackSlot)
            (nonpayable
              (domainSeparator (⟨0, 0⟩ : DeployParams)))) i 0
  have hprefix : lineByteSize domainLeafPrefix = 6 := by decide +kernel
  by_cases hpre : i < 6
  · apply byteAt_prepend_eq_prefix
    simpa only [hprefix] using hpre
  · conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := domainLeafPrefix)
      (p0 := Func.branch (.call fallbackSlot)
        (nonpayable (domainSeparator (⟨0, 0⟩ : DeployParams))))
      (p := Func.branch (.call fallbackSlot)
        (nonpayable (domainSeparator dp)))
      (i := i) (d := 0) (by simpa only [hprefix] using (show 6 ≤ i by omega))]
    conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := domainLeafPrefix)
      (p0 := Func.branch (.call fallbackSlot)
        (nonpayable (domainSeparator (⟨0, 0⟩ : DeployParams))))
      (p := Func.branch (.call fallbackSlot)
        (nonpayable (domainSeparator (⟨0, 0⟩ : DeployParams))))
      (i := i) (d := 0) (by simpa only [hprefix] using (show 6 ≤ i by omega))]
    simp only [hprefix]
    have hcall : (Func.call fallbackSlot).compileShape.byteSize = 4 := by
      decide +kernel
    apply byteAt_branch_eq_before_right
    simpa only [hcall, Nat.reduceAdd] using
      (show i - 6 < 9 by omega)

private theorem nonpayableDomainByteAt_eq_zero_0_10
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 10) :
    Func.byteAtByShape locations n
        (nonpayable
          (domainSeparator (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayable (domainSeparator dp)) i 0 =
      Func.byteAtByShape locations n
        (nonpayable
          (domainSeparator (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayable
          (domainSeparator (⟨0, 0⟩ : DeployParams))) i 0 := by
  change
    Func.byteAtByShape locations n
        (nonpayablePrefix +++
          Func.branch Func.revert
            (domainSeparator (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++
          Func.branch Func.revert (domainSeparator dp)) i 0 =
      Func.byteAtByShape locations n
        (nonpayablePrefix +++
          Func.branch Func.revert
            (domainSeparator (⟨0, 0⟩ : DeployParams))).compileShape
        (nonpayablePrefix +++
          Func.branch Func.revert
            (domainSeparator (⟨0, 0⟩ : DeployParams))) i 0
  have hprefix : lineByteSize nonpayablePrefix = 2 := by decide +kernel
  by_cases hpre : i < 2
  · apply byteAt_prepend_eq_prefix
    simpa only [hprefix] using hpre
  · conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := nonpayablePrefix)
      (p0 := Func.branch Func.revert
        (domainSeparator (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch Func.revert (domainSeparator dp))
      (i := i) (d := 0) (by simpa only [hprefix] using (show 2 ≤ i by omega))]
    conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n) (l := nonpayablePrefix)
      (p0 := Func.branch Func.revert
        (domainSeparator (⟨0, 0⟩ : DeployParams)))
      (p := Func.branch Func.revert
        (domainSeparator (⟨0, 0⟩ : DeployParams)))
      (i := i) (d := 0) (by simpa only [hprefix] using (show 2 ≤ i by omega))]
    simp only [hprefix]
    have hrev : Func.revert.compileShape.byteSize = 3 := by decide +kernel
    apply byteAt_branch_eq_before_right
    simpa only [hrev, Nat.reduceAdd] using
      (show i - 2 < 8 by omega)

private theorem domainLeafByteAt_eq_zero_0_28
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 28) :
    Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)) i 0 := by
  by_cases hleaf : i < 15
  · exact domainLeafByteAt_eq_zero_0_15 locations n dp i hleaf
  · rw [domainLeafByteAt_to_nonpayable locations n dp i (by omega),
      domainLeafByteAt_to_nonpayable locations n
        (⟨0, 0⟩ : DeployParams) i (by omega)]
    by_cases hguard : i - 15 < 10
    · exact nonpayableDomainByteAt_eq_zero_0_10 locations (n + 15) dp
        (i - 15) hguard
    · rw [nonpayableDomainByteAt_to_raw locations (n + 15) dp
          (i - 15) (by omega),
        nonpayableDomainByteAt_to_raw locations (n + 15)
          (⟨0, 0⟩ : DeployParams) (i - 15) (by omega)]
      apply domainSeparatorByteAt_eq_zero_0_3
      omega

private theorem domainLeafByteAt_deploymentWord_28_60
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 28 ≤ i) (hi : i < 60) :
    Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) i 0 =
      dp.deploymentChainId.toBytes.getD (i - 28) 0 := by
  rw [domainLeafByteAt_to_raw locations n dp i (by omega)]
  have hword := domainSeparatorByteAt_deploymentWord_3_35
    locations (n + 25) dp (i - 25) (by omega) (by omega)
  have hout : i - 25 - 3 = i - 28 := by omega
  rw [hout] at hword
  exact hword

private theorem domainLeafByteAt_eq_zero_60_192
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 60 ≤ i) (hi : i < 192) :
    Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [domainLeafByteAt_to_raw locations n dp i (by omega),
    domainLeafByteAt_to_raw locations n
      (⟨0, 0⟩ : DeployParams) i (by omega)]
  apply domainSeparatorByteAt_eq_zero_35_167 <;> omega

private theorem domainLeafByteAt_cachedWord_192_224
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 192 ≤ i) (hi : i < 224) :
    Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) i 0 =
      dp.cachedDomainSeparator.toBytes.getD (i - 192) 0 := by
  rw [domainLeafByteAt_to_raw locations n dp i (by omega)]
  have hword := domainSeparatorByteAt_cachedWord_167_199
    locations (n + 25) dp (i - 25) (by omega) (by omega)
  have hout : i - 25 - 167 = i - 192 := by omega
  rw [hout] at hword
  exact hword

private theorem domainLeafByteAt_eq_zero_224_230
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 224 ≤ i) (hi : i < 230) :
    Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [domainLeafByteAt_to_raw locations n dp i (by omega),
    domainLeafByteAt_to_raw locations n
      (⟨0, 0⟩ : DeployParams) i (by omega)]
  apply domainSeparatorByteAt_eq_zero_199_205 <;> omega

private theorem dispatch26ByteAt_to_domainLeaf
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1054 ≤ i) (hi : i < 1284) :
    Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 dp) i 0 =
      Func.byteAtByShape locations (n + 1054)
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) (i - 1054) 0 := by
  rw [dispatch26_0_14_eq_node dp,
    dispatch26_0_14_eq_node (⟨0, 0⟩ : DeployParams)]
  have hdec : (Ninst.pushB256 (selector "decimals" [])).size = 5 := by
    decide +kernel
  rw [dispatchNodeByteAt_to_onPath locations n
      (selector "decimals" [])
      (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
      (dispatch25_7_7 (⟨0, 0⟩ : DeployParams))
      (dispatch25_0_7 dp) (dispatch25_7_7 dp) i 0 hdec
      (by omega) (by rw [dispatch25_7_7_size]; omega)]
  rw [dispatch25_7_7_eq_node dp,
    dispatch25_7_7_eq_node (⟨0, 0⟩ : DeployParams)]
  have hdeposit :
      (Ninst.pushB256
        (selector "depositToAndCall" [.address, .dynBytes])).size = 5 := by
    decide +kernel
  rw [dispatchNodeByteAt_to_offPath locations (n + 11)
      (selector "depositToAndCall" [.address, .dynBytes])
      (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
      (dispatch24_11_3 (⟨0, 0⟩ : DeployParams))
      (dispatch24_7_4 dp) (dispatch24_11_3 dp) (i - 11) 0 hdeposit
      (by rw [dispatch24_11_3_size]; omega)]
  rw [dispatch24_11_3_size]
  rw [dispatch24_7_4_eq_node dp,
    dispatch24_7_4_eq_node (⟨0, 0⟩ : DeployParams)]
  have htransfer :
      (Ninst.pushB256
        (selector "transferAndCall" [.address, .uint256, .dynBytes])).size =
        5 := by
    decide +kernel
  rw [dispatchNodeByteAt_to_offPath locations (n + 11 + 12 + 295)
      (selector "transferAndCall" [.address, .uint256, .dynBytes])
      (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
      (dispatch23_9_2 (⟨0, 0⟩ : DeployParams))
      (dispatch23_7_2 dp) (dispatch23_9_2 dp)
      (i - 11 - (12 + 295)) 0 htransfer
      (by rw [dispatch23_9_2_size]; omega)]
  rw [dispatch23_9_2_size]
  rw [dispatch23_7_2_eq_node dp,
    dispatch23_7_2_eq_node (⟨0, 0⟩ : DeployParams)]
  have hdomain :
      (Ninst.pushB256 (selector "DOMAIN_SEPARATOR" [])).size = 5 := by
    decide +kernel
  rw [dispatchNodeByteAt_to_onPath locations
      (n + 11 + 12 + 295 + 12 + 713)
      (selector "DOMAIN_SEPARATOR" [])
      (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
      (dispatch22_8_1 (⟨0, 0⟩ : DeployParams))
      (dispatch22_7_1 dp) (dispatch22_8_1 dp)
      (i - 11 - (12 + 295) - (12 + 713)) 0 hdomain
      (by omega) (by rw [dispatch22_8_1_size]; omega)]
  have hn : n + 11 + 12 + 295 + 12 + 713 + 11 = n + 1054 := by
    omega
  have hindex : i - 11 - (12 + 295) - (12 + 713) - 11 =
      i - 1054 := by
    omega
  rw [hn, hindex]

private theorem dispatch26ByteAt_eq_zero_1054_1082
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1054 ≤ i) (hi : i < 1082) :
    Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch26ByteAt_to_domainLeaf locations n dp i hlo (by omega),
    dispatch26ByteAt_to_domainLeaf locations n
      (⟨0, 0⟩ : DeployParams) i hlo (by omega)]
  apply domainLeafByteAt_eq_zero_0_28
  omega

private theorem dispatch26ByteAt_deploymentWord_1082_1114
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1082 ≤ i) (hi : i < 1114) :
    Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 dp) i 0 =
      dp.deploymentChainId.toBytes.getD (i - 1082) 0 := by
  rw [dispatch26ByteAt_to_domainLeaf locations n dp i (by omega) (by omega)]
  have hword := domainLeafByteAt_deploymentWord_28_60
    locations (n + 1054) dp (i - 1054) (by omega) (by omega)
  have hout : i - 1054 - 28 = i - 1082 := by omega
  rw [hout] at hword
  exact hword

private theorem dispatch26ByteAt_eq_zero_1114_1246
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1114 ≤ i) (hi : i < 1246) :
    Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch26ByteAt_to_domainLeaf locations n dp i (by omega) (by omega),
    dispatch26ByteAt_to_domainLeaf locations n
      (⟨0, 0⟩ : DeployParams) i (by omega) (by omega)]
  apply domainLeafByteAt_eq_zero_60_192 <;> omega

private theorem dispatch26ByteAt_cachedWord_1246_1278
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1246 ≤ i) (hi : i < 1278) :
    Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 dp) i 0 =
      dp.cachedDomainSeparator.toBytes.getD (i - 1246) 0 := by
  rw [dispatch26ByteAt_to_domainLeaf locations n dp i (by omega) (by omega)]
  have hword := domainLeafByteAt_cachedWord_192_224
    locations (n + 1054) dp (i - 1054) (by omega) (by omega)
  have hout : i - 1054 - 192 = i - 1246 := by omega
  rw [hout] at hword
  exact hword

private theorem dispatch26ByteAt_eq_zero_1278_1284
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1278 ≤ i) (hi : i < 1284) :
    Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch26ByteAt_to_domainLeaf locations n dp i (by omega) (by omega),
    dispatch26ByteAt_to_domainLeaf locations n
      (⟨0, 0⟩ : DeployParams) i (by omega) (by omega)]
  apply domainLeafByteAt_eq_zero_224_230 <;> omega

private theorem fullDispatchByteAt_to_low
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1781 ≤ i) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations (n + 1781)
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 dp) (i - 1781) 0 := by
  rw [fullDispatch_eq_root dp,
    fullDispatch_eq_root (⟨0, 0⟩ : DeployParams)]
  have hnonces :
      (Ninst.pushB256 (selector "nonces" [.address])).size = 5 := by
    decide +kernel
  rw [dispatchNodeByteAt_to_offPath locations n
      (selector "nonces" [.address])
      (dispatch26_0_14 (⟨0, 0⟩ : DeployParams))
      (dispatch26_14_13 (⟨0, 0⟩ : DeployParams))
      (dispatch26_0_14 dp) (dispatch26_14_13 dp) i 0 hnonces
      (by rw [dispatch26_14_13_size]; omega)]
  rw [dispatch26_14_13_size]

private theorem fullDispatchByteAt_to_domainLeaf
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 2835 ≤ i) (hi : i < 3065) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations (n + 2835)
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch22_8_1 dp) (i - 2835) 0 := by
  rw [fullDispatchByteAt_to_low locations n dp i (by omega),
    dispatch26ByteAt_to_domainLeaf locations (n + 1781) dp
      (i - 1781) (by omega) (by omega)]
  have hn : n + 1781 + 1054 = n + 2835 := by omega
  have hindex : i - 1781 - 1054 = i - 2835 := by omega
  rw [hn, hindex]

private theorem fullDispatchByteAt_eq_zero_2835_2863
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 2835 ≤ i) (hi : i < 2863) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  rw [fullDispatchByteAt_to_domainLeaf locations n dp i hlo (by omega),
    fullDispatchByteAt_to_domainLeaf locations n
      (⟨0, 0⟩ : DeployParams) i hlo (by omega)]
  apply domainLeafByteAt_eq_zero_0_28
  omega

theorem fullDispatchByteAt_deploymentWord_2863_2895
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 2863 ≤ i) (hi : i < 2895) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      dp.deploymentChainId.toBytes.getD (i - 2863) 0 := by
  rw [fullDispatchByteAt_to_domainLeaf locations n dp i (by omega) (by omega)]
  have hword := domainLeafByteAt_deploymentWord_28_60
    locations (n + 2835) dp (i - 2835) (by omega) (by omega)
  have hout : i - 2835 - 28 = i - 2863 := by omega
  rw [hout] at hword
  exact hword

theorem fullDispatchByteAt_eq_zero_2895_3027
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 2895 ≤ i) (hi : i < 3027) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  rw [fullDispatchByteAt_to_domainLeaf locations n dp i (by omega) (by omega),
    fullDispatchByteAt_to_domainLeaf locations n
      (⟨0, 0⟩ : DeployParams) i (by omega) (by omega)]
  apply domainLeafByteAt_eq_zero_60_192 <;> omega

theorem fullDispatchByteAt_cachedWord_3027_3059
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 3027 ≤ i) (hi : i < 3059) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      dp.cachedDomainSeparator.toBytes.getD (i - 3027) 0 := by
  rw [fullDispatchByteAt_to_domainLeaf locations n dp i (by omega) (by omega)]
  have hword := domainLeafByteAt_cachedWord_192_224
    locations (n + 2835) dp (i - 2835) (by omega) (by omega)
  have hout : i - 2835 - 192 = i - 3027 := by omega
  rw [hout] at hword
  exact hword

private theorem fullDispatchByteAt_eq_zero_3059_3065
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 3059 ≤ i) (hi : i < 3065) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  rw [fullDispatchByteAt_to_domainLeaf locations n dp i (by omega) (by omega),
    fullDispatchByteAt_to_domainLeaf locations n
      (⟨0, 0⟩ : DeployParams) i (by omega) (by omega)]
  apply domainLeafByteAt_eq_zero_224_230 <;> omega

/-! ## Equality before and after the parameterized DOMAIN leaf -/

private def dispatchHeaderPrefix (selector : B256) : Line :=
  [Ninst.dup 0, Ninst.pushB256 selector, Ninst.gt]

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
  unfold dispatchNode
  change
    Func.byteAtByShape locations n
        (dispatchHeaderPrefix selector +++
          Func.branch on0 off0).compileShape
        (dispatchHeaderPrefix selector +++ Func.branch on off) i 0 =
      Func.byteAtByShape locations n
        (dispatchHeaderPrefix selector +++
          Func.branch on0 off0).compileShape
        (dispatchHeaderPrefix selector +++ Func.branch on0 off0) i 0
  have hprefix : lineByteSize (dispatchHeaderPrefix selector) = 7 := by
    change (Ninst.dup 0).size +
      ((Ninst.pushB256 selector).size + (Ninst.gt.size + 0)) = 7
    rw [hpush]
    decide +kernel
  by_cases hline : i < 7
  · apply byteAt_prepend_eq_prefix
    simpa only [hprefix] using hline
  · conv_lhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n)
      (l := dispatchHeaderPrefix selector)
      (p0 := Func.branch on0 off0) (p := Func.branch on off)
      (i := i) (d := 0)
      (by simpa only [hprefix] using (show 7 ≤ i by omega))]
    conv_rhs => rw [byteAt_prepend_to_tail
      (locations := locations) (n := n)
      (l := dispatchHeaderPrefix selector)
      (p0 := Func.branch on0 off0) (p := Func.branch on0 off0)
      (i := i) (d := 0)
      (by simpa only [hprefix] using (show 7 ≤ i by omega))]
    simp only [hprefix]
    apply byteAt_branch_eq_header
    omega

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
  unfold dispatchNode
  change
    Func.byteAtByShape locations n
        (dispatchHeaderPrefix selector +++ Func.branch on0 off0).compileShape
        (dispatchHeaderPrefix selector +++ Func.branch on off)
          (11 + on0.compileShape.byteSize) 0 =
      Func.byteAtByShape locations n
        (dispatchHeaderPrefix selector +++ Func.branch on0 off0).compileShape
        (dispatchHeaderPrefix selector +++ Func.branch on0 off0)
          (11 + on0.compileShape.byteSize) 0
  have hprefix : lineByteSize (dispatchHeaderPrefix selector) = 7 := by
    change (Ninst.dup 0).size +
      ((Ninst.pushB256 selector).size + (Ninst.gt.size + 0)) = 7
    rw [hpush]
    decide +kernel
  conv_lhs => rw [byteAt_prepend_to_tail
    (locations := locations) (n := n) (l := dispatchHeaderPrefix selector)
    (p0 := Func.branch on0 off0) (p := Func.branch on off)
    (i := 11 + on0.compileShape.byteSize) (d := 0)
    (by rw [hprefix]; omega)]
  conv_rhs => rw [byteAt_prepend_to_tail
    (locations := locations) (n := n) (l := dispatchHeaderPrefix selector)
    (p0 := Func.branch on0 off0) (p := Func.branch on0 off0)
    (i := 11 + on0.compileShape.byteSize) (d := 0)
    (by rw [hprefix]; omega)]
  simp only [hprefix]
  have hindex : 11 + on0.compileShape.byteSize - 7 =
      4 + on0.compileShape.byteSize := by omega
  rw [hindex]
  change
    Func.byteAtByShape locations (n + 7)
        (.branch on0.compileShape off0.compileShape)
        (.branch on off) (4 + on0.compileShape.byteSize) 0 =
      Func.byteAtByShape locations (n + 7)
        (.branch on0.compileShape off0.compileShape)
        (.branch on0 off0) (4 + on0.compileShape.byteSize) 0
  rw [byteAt_branch_jumpdest, byteAt_branch_jumpdest]

private theorem dispatch25_0_7_eq_zero (dp : DeployParams) :
    dispatch25_0_7 dp =
      dispatch25_0_7 (⟨0, 0⟩ : DeployParams) := by
  simp [dispatch25_0_7, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith]

private theorem dispatch24_11_3_eq_zero (dp : DeployParams) :
    dispatch24_11_3 dp =
      dispatch24_11_3 (⟨0, 0⟩ : DeployParams) := by
  simp [dispatch24_11_3, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith]

private theorem dispatch23_9_2_eq_zero (dp : DeployParams) :
    dispatch23_9_2 dp =
      dispatch23_9_2 (⟨0, 0⟩ : DeployParams) := by
  simp [dispatch23_9_2, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith]

private theorem dispatch22_7_1_eq_zero (dp : DeployParams) :
    dispatch22_7_1 dp =
      dispatch22_7_1 (⟨0, 0⟩ : DeployParams) := by
  simp [dispatch22_7_1, treeSlice, weth10Funcs, DispatchTree.build,
    dispatchWith]

private theorem dispatch23_7_2ByteAt_eq_zero_0_39
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 39) :
    Func.byteAtByShape locations n
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch23_7_2 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch23_7_2_eq_node dp,
    dispatch23_7_2_eq_node (⟨0, 0⟩ : DeployParams)]
  have hpush :
      (Ninst.pushB256 (selector "DOMAIN_SEPARATOR" [])).size = 5 := by
    decide +kernel
  by_cases hheader : i < 11
  · exact dispatchNodeByteAt_eq_prefix locations n
      (selector "DOMAIN_SEPARATOR" [])
      (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
      (dispatch22_8_1 (⟨0, 0⟩ : DeployParams))
      (dispatch22_7_1 dp) (dispatch22_8_1 dp) hpush i hheader
  · rw [dispatchNodeByteAt_to_onPath locations n
        (selector "DOMAIN_SEPARATOR" [])
        (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_7_1 dp) (dispatch22_8_1 dp) i 0 hpush
        (by omega) (by rw [dispatch22_8_1_size]; omega),
      dispatchNodeByteAt_to_onPath locations n
        (selector "DOMAIN_SEPARATOR" [])
        (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)) i 0 hpush
        (by omega) (by rw [dispatch22_8_1_size]; omega)]
    apply domainLeafByteAt_eq_zero_0_28
    omega

private theorem dispatch24_7_4ByteAt_eq_zero_0_764
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 764) :
    Func.byteAtByShape locations n
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_7_4 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch24_7_4_eq_node dp,
    dispatch24_7_4_eq_node (⟨0, 0⟩ : DeployParams)]
  have hpush :
      (Ninst.pushB256
        (selector "transferAndCall" [.address, .uint256, .dynBytes])).size =
        5 := by
    decide +kernel
  by_cases hoff : i < 725
  · by_cases hheader : i < 11
    · exact dispatchNodeByteAt_eq_prefix locations n
        (selector "transferAndCall" [.address, .uint256, .dynBytes])
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_9_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_7_2 dp) (dispatch23_9_2 dp) hpush i hheader
    · by_cases hon : i - 11 < 713
      · rw [dispatchNodeByteAt_to_onPath locations n
            (selector "transferAndCall" [.address, .uint256, .dynBytes])
            (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
            (dispatch23_9_2 (⟨0, 0⟩ : DeployParams))
            (dispatch23_7_2 dp) (dispatch23_9_2 dp) i 0 hpush
            (by omega) (by simpa only [dispatch23_9_2_size] using hon),
          dispatchNodeByteAt_to_onPath locations n
            (selector "transferAndCall" [.address, .uint256, .dynBytes])
            (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
            (dispatch23_9_2 (⟨0, 0⟩ : DeployParams))
            (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
            (dispatch23_9_2 (⟨0, 0⟩ : DeployParams)) i 0 hpush
            (by omega) (by simpa only [dispatch23_9_2_size] using hon)]
        rw [dispatch23_9_2_eq_zero dp]
      · have hjump : i = 724 := by omega
        subst i
        simpa only [dispatch23_9_2_size, Nat.reduceAdd] using
          dispatchNodeByteAt_eq_jumpdest locations n
            (selector "transferAndCall" [.address, .uint256, .dynBytes])
            (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
            (dispatch23_9_2 (⟨0, 0⟩ : DeployParams))
            (dispatch23_7_2 dp) (dispatch23_9_2 dp) hpush
  · rw [dispatchNodeByteAt_to_offPath locations n
        (selector "transferAndCall" [.address, .uint256, .dynBytes])
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_9_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_7_2 dp) (dispatch23_9_2 dp) i 0 hpush
        (by rw [dispatch23_9_2_size]; omega),
      dispatchNodeByteAt_to_offPath locations n
        (selector "transferAndCall" [.address, .uint256, .dynBytes])
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_9_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_9_2 (⟨0, 0⟩ : DeployParams)) i 0 hpush
        (by rw [dispatch23_9_2_size]; omega)]
    rw [dispatch23_9_2_size]
    apply dispatch23_7_2ByteAt_eq_zero_0_39
    omega

private theorem dispatch25_7_7ByteAt_eq_zero_0_1071
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 1071) :
    Func.byteAtByShape locations n
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch25_7_7 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch25_7_7_eq_node dp,
    dispatch25_7_7_eq_node (⟨0, 0⟩ : DeployParams)]
  have hpush :
      (Ninst.pushB256
        (selector "depositToAndCall" [.address, .dynBytes])).size = 5 := by
    decide +kernel
  by_cases hoff : i < 307
  · by_cases hheader : i < 11
    · exact dispatchNodeByteAt_eq_prefix locations n
        (selector "depositToAndCall" [.address, .dynBytes])
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
        (dispatch24_11_3 (⟨0, 0⟩ : DeployParams))
        (dispatch24_7_4 dp) (dispatch24_11_3 dp) hpush i hheader
    · by_cases hon : i - 11 < 295
      · rw [dispatchNodeByteAt_to_onPath locations n
            (selector "depositToAndCall" [.address, .dynBytes])
            (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
            (dispatch24_11_3 (⟨0, 0⟩ : DeployParams))
            (dispatch24_7_4 dp) (dispatch24_11_3 dp) i 0 hpush
            (by omega) (by simpa only [dispatch24_11_3_size] using hon),
          dispatchNodeByteAt_to_onPath locations n
            (selector "depositToAndCall" [.address, .dynBytes])
            (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
            (dispatch24_11_3 (⟨0, 0⟩ : DeployParams))
            (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
            (dispatch24_11_3 (⟨0, 0⟩ : DeployParams)) i 0 hpush
            (by omega) (by simpa only [dispatch24_11_3_size] using hon)]
        rw [dispatch24_11_3_eq_zero dp]
      · have hjump : i = 306 := by omega
        subst i
        simpa only [dispatch24_11_3_size, Nat.reduceAdd] using
          dispatchNodeByteAt_eq_jumpdest locations n
            (selector "depositToAndCall" [.address, .dynBytes])
            (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
            (dispatch24_11_3 (⟨0, 0⟩ : DeployParams))
            (dispatch24_7_4 dp) (dispatch24_11_3 dp) hpush
  · rw [dispatchNodeByteAt_to_offPath locations n
        (selector "depositToAndCall" [.address, .dynBytes])
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
        (dispatch24_11_3 (⟨0, 0⟩ : DeployParams))
        (dispatch24_7_4 dp) (dispatch24_11_3 dp) i 0 hpush
        (by rw [dispatch24_11_3_size]; omega),
      dispatchNodeByteAt_to_offPath locations n
        (selector "depositToAndCall" [.address, .dynBytes])
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
        (dispatch24_11_3 (⟨0, 0⟩ : DeployParams))
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
        (dispatch24_11_3 (⟨0, 0⟩ : DeployParams)) i 0 hpush
        (by rw [dispatch24_11_3_size]; omega)]
    rw [dispatch24_11_3_size]
    apply dispatch24_7_4ByteAt_eq_zero_0_764
    omega

private theorem dispatch26ByteAt_eq_zero_0_1082
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hi : i < 1082) :
    Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch26_0_14_eq_node dp,
    dispatch26_0_14_eq_node (⟨0, 0⟩ : DeployParams)]
  have hpush : (Ninst.pushB256 (selector "decimals" [])).size = 5 := by
    decide +kernel
  by_cases hheader : i < 11
  · exact dispatchNodeByteAt_eq_prefix locations n
      (selector "decimals" [])
      (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
      (dispatch25_7_7 (⟨0, 0⟩ : DeployParams))
      (dispatch25_0_7 dp) (dispatch25_7_7 dp) hpush i hheader
  · rw [dispatchNodeByteAt_to_onPath locations n
        (selector "decimals" [])
        (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_0_7 dp) (dispatch25_7_7 dp) i 0 hpush
        (by omega) (by rw [dispatch25_7_7_size]; omega),
      dispatchNodeByteAt_to_onPath locations n
        (selector "decimals" [])
        (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)) i 0 hpush
        (by omega) (by rw [dispatch25_7_7_size]; omega)]
    apply dispatch25_7_7ByteAt_eq_zero_0_1071
    omega

private theorem dispatch23_7_2ByteAt_eq_zero_235_275
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 235 ≤ i) (hi : i < 275) :
    Func.byteAtByShape locations n
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch23_7_2 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch23_7_2_eq_node dp,
    dispatch23_7_2_eq_node (⟨0, 0⟩ : DeployParams)]
  have hpush :
      (Ninst.pushB256 (selector "DOMAIN_SEPARATOR" [])).size = 5 := by
    decide +kernel
  by_cases hon : i < 241
  · rw [dispatchNodeByteAt_to_onPath locations n
        (selector "DOMAIN_SEPARATOR" [])
        (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_7_1 dp) (dispatch22_8_1 dp) i 0 hpush
        (by omega) (by rw [dispatch22_8_1_size]; omega),
      dispatchNodeByteAt_to_onPath locations n
        (selector "DOMAIN_SEPARATOR" [])
        (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
        (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)) i 0 hpush
        (by omega) (by rw [dispatch22_8_1_size]; omega)]
    apply domainLeafByteAt_eq_zero_224_230 <;> omega
  · by_cases hjump : i = 241
    · subst i
      simpa only [dispatch22_8_1_size, Nat.reduceAdd] using
        dispatchNodeByteAt_eq_jumpdest locations n
          (selector "DOMAIN_SEPARATOR" [])
          (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
          (dispatch22_8_1 (⟨0, 0⟩ : DeployParams))
          (dispatch22_7_1 dp) (dispatch22_8_1 dp) hpush
    · rw [dispatchNodeByteAt_to_offPath locations n
          (selector "DOMAIN_SEPARATOR" [])
          (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
          (dispatch22_8_1 (⟨0, 0⟩ : DeployParams))
          (dispatch22_7_1 dp) (dispatch22_8_1 dp) i 0 hpush
          (by rw [dispatch22_8_1_size]; omega),
        dispatchNodeByteAt_to_offPath locations n
          (selector "DOMAIN_SEPARATOR" [])
          (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
          (dispatch22_8_1 (⟨0, 0⟩ : DeployParams))
          (dispatch22_7_1 (⟨0, 0⟩ : DeployParams))
          (dispatch22_8_1 (⟨0, 0⟩ : DeployParams)) i 0 hpush
          (by rw [dispatch22_8_1_size]; omega)]
      rw [dispatch22_7_1_eq_zero dp]

private theorem dispatch24_7_4ByteAt_eq_zero_960_1000
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 960 ≤ i) (hi : i < 1000) :
    Func.byteAtByShape locations n
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_7_4 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch24_7_4_eq_node dp,
    dispatch24_7_4_eq_node (⟨0, 0⟩ : DeployParams)]
  have hpush :
      (Ninst.pushB256
        (selector "transferAndCall" [.address, .uint256, .dynBytes])).size =
        5 := by
    decide +kernel
  rw [dispatchNodeByteAt_to_offPath locations n
        (selector "transferAndCall" [.address, .uint256, .dynBytes])
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_9_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_7_2 dp) (dispatch23_9_2 dp) i 0 hpush
        (by rw [dispatch23_9_2_size]; omega),
      dispatchNodeByteAt_to_offPath locations n
        (selector "transferAndCall" [.address, .uint256, .dynBytes])
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_9_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_7_2 (⟨0, 0⟩ : DeployParams))
        (dispatch23_9_2 (⟨0, 0⟩ : DeployParams)) i 0 hpush
        (by rw [dispatch23_9_2_size]; omega)]
  rw [dispatch23_9_2_size]
  apply dispatch23_7_2ByteAt_eq_zero_235_275 <;> omega

private theorem dispatch25_7_7ByteAt_eq_zero_1267_1307
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1267 ≤ i) (hi : i < 1307) :
    Func.byteAtByShape locations n
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch25_7_7 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch25_7_7_eq_node dp,
    dispatch25_7_7_eq_node (⟨0, 0⟩ : DeployParams)]
  have hpush :
      (Ninst.pushB256
        (selector "depositToAndCall" [.address, .dynBytes])).size = 5 := by
    decide +kernel
  rw [dispatchNodeByteAt_to_offPath locations n
        (selector "depositToAndCall" [.address, .dynBytes])
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
        (dispatch24_11_3 (⟨0, 0⟩ : DeployParams))
        (dispatch24_7_4 dp) (dispatch24_11_3 dp) i 0 hpush
        (by rw [dispatch24_11_3_size]; omega),
      dispatchNodeByteAt_to_offPath locations n
        (selector "depositToAndCall" [.address, .dynBytes])
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
        (dispatch24_11_3 (⟨0, 0⟩ : DeployParams))
        (dispatch24_7_4 (⟨0, 0⟩ : DeployParams))
        (dispatch24_11_3 (⟨0, 0⟩ : DeployParams)) i 0 hpush
        (by rw [dispatch24_11_3_size]; omega)]
  rw [dispatch24_11_3_size]
  apply dispatch24_7_4ByteAt_eq_zero_960_1000 <;> omega

private theorem dispatch26ByteAt_eq_zero_1278_2158
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1278 ≤ i) (hi : i < 2158) :
    Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 dp) i 0 =
      Func.byteAtByShape locations n
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)).compileShape
        (dispatch26_0_14 (⟨0, 0⟩ : DeployParams)) i 0 := by
  rw [dispatch26_0_14_eq_node dp,
    dispatch26_0_14_eq_node (⟨0, 0⟩ : DeployParams)]
  have hpush : (Ninst.pushB256 (selector "decimals" [])).size = 5 := by
    decide +kernel
  by_cases hon : i < 1318
  · rw [dispatchNodeByteAt_to_onPath locations n
        (selector "decimals" [])
        (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_0_7 dp) (dispatch25_7_7 dp) i 0 hpush
        (by omega) (by rw [dispatch25_7_7_size]; omega),
      dispatchNodeByteAt_to_onPath locations n
        (selector "decimals" [])
        (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
        (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)) i 0 hpush
        (by omega) (by rw [dispatch25_7_7_size]; omega)]
    apply dispatch25_7_7ByteAt_eq_zero_1267_1307 <;> omega
  · by_cases hjump : i = 1318
    · subst i
      simpa only [dispatch25_7_7_size, Nat.reduceAdd] using
        dispatchNodeByteAt_eq_jumpdest locations n
          (selector "decimals" [])
          (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
          (dispatch25_7_7 (⟨0, 0⟩ : DeployParams))
          (dispatch25_0_7 dp) (dispatch25_7_7 dp) hpush
    · rw [dispatchNodeByteAt_to_offPath locations n
          (selector "decimals" [])
          (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
          (dispatch25_7_7 (⟨0, 0⟩ : DeployParams))
          (dispatch25_0_7 dp) (dispatch25_7_7 dp) i 0 hpush
          (by rw [dispatch25_7_7_size]; omega),
        dispatchNodeByteAt_to_offPath locations n
          (selector "decimals" [])
          (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
          (dispatch25_7_7 (⟨0, 0⟩ : DeployParams))
          (dispatch25_0_7 (⟨0, 0⟩ : DeployParams))
          (dispatch25_7_7 (⟨0, 0⟩ : DeployParams)) i 0 hpush
          (by rw [dispatch25_7_7_size]; omega)]
      rw [dispatch25_0_7_eq_zero dp]

theorem fullDispatchByteAt_eq_zero_1781_2863
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 1781 ≤ i) (hi : i < 2863) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  rw [fullDispatchByteAt_to_low locations n dp i hlo,
    fullDispatchByteAt_to_low locations n
      (⟨0, 0⟩ : DeployParams) i hlo]
  apply dispatch26ByteAt_eq_zero_0_1082
  omega

theorem fullDispatchByteAt_eq_zero_3059_3939
    (locations : List Nat) (n : Nat) (dp : DeployParams)
    (i : Nat) (hlo : 3059 ≤ i) (hi : i < 3939) :
    Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot (weth10Tree dp)) i 0 =
      Func.byteAtByShape locations n
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))).compileShape
        (dispatchWith fallbackSlot
          (weth10Tree (⟨0, 0⟩ : DeployParams))) i 0 := by
  rw [fullDispatchByteAt_to_low locations n dp i (by omega),
    fullDispatchByteAt_to_low locations n
      (⟨0, 0⟩ : DeployParams) i (by omega)]
  apply dispatch26ByteAt_eq_zero_1278_2158 <;> omega

end Weth10

end Blanc
