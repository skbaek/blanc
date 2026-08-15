import Blanc.LidoCircuitBreakerRegistry
import Blanc.ForwardCall

/-!
Concrete positive and semantic-mutant controls for the Lido CircuitBreaker
Registry proof.  Every mutant below changes an executable logical storage
transition; none is an expected-text or diagnostic-string mutation.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Ninst

set_option maxHeartbeats 800000
set_option maxRecDepth 16384

private theorem canonicalSmall (n : Nat) (hn : n < 2 ^ 160) :
    canonicalAddress (Nat.toB256 n) := by
  unfold canonicalAddress
  rw [B256.toNat_toB256_of_lt (by omega)]
  exact hn

private theorem nonzeroCanonicalSmall (n : Nat) (hpos : 0 < n)
    (hn : n < 2 ^ 160) :
    nonzeroCanonicalAddress (Nat.toB256 n) := by
  refine ⟨?_, canonicalSmall n hn⟩
  intro hzero
  have hnat := congrArg B256.toNat hzero
  rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_zero] at hnat
  omega

private theorem emptyStorWitness :
    RegistryWitness (logicalStorageOfStor Stor.empty) [] := by
  have hread (key : B256) : Stor.empty.get key = 0 := by
    rw [Stor.get_eq_getD_find?, Stor.find?_empty]
    rfl
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro entry hmem; simp at hmem
  · intro entry hmem; simp at hmem
  · change Stor.empty.get arrayLengthSlot = 0
    exact hread arrayLengthSlot
  · intro index hindex; simp at hindex
  · intro target htarget
    simpa [logicalStorageOfStor, assignmentAt] using hread (assignmentSlot target)
  · intro target htarget
    change Stor.empty.get (indexSlot target) = 0
    exact hread (indexSlot target)
  · intro pauser hpauser
    change Stor.empty.get (countSlot pauser) = 0
    exact hread (countSlot pauser)
  · simpa [logicalStorageOfStor] using hread (countSlot 0)

namespace RegistryMutants

def oneStor : Stor :=
  applyRegistryWrites Stor.empty
    [(assignmentSlot 7, 9),
     (arrayEntrySlot (Nat.toB256 1), 7),
     (indexSlot 7, Nat.toB256 1),
     (arrayLengthSlot, Nat.toB256 1),
     (countSlot 9, Nat.toB256 1)]

def twoStor : Stor :=
  applyRegistryWrites oneStor
    [(assignmentSlot 8, 10),
     (arrayEntrySlot (Nat.toB256 2), 8),
     (indexSlot 8, Nat.toB256 2),
     (arrayLengthSlot, Nat.toB256 2),
     (countSlot 10, Nat.toB256 1)]

def threeStor : Stor :=
  applyRegistryWrites twoStor
    [(assignmentSlot 11, 12),
     (arrayEntrySlot (Nat.toB256 3), 11),
     (indexSlot 11, Nat.toB256 3),
     (arrayLengthSlot, Nat.toB256 3),
     (countSlot 12, Nat.toB256 1)]

theorem oneEntry_pre_witness :
    RegistryWitness (logicalStorageOfStor oneStor) [(7, 9)] := by
  exact emptyStorWitness.applyFreshWrites
    (nonzeroCanonicalSmall 7 (by omega) (by norm_num))
    (nonzeroCanonicalSmall 9 (by omega) (by norm_num))
    (by decide)

theorem twoEntry_pre_witness :
    RegistryWitness (logicalStorageOfStor twoStor)
      [(7, 9), (8, 10)] := by
  exact oneEntry_pre_witness.applyFreshWrites
    (nonzeroCanonicalSmall 8 (by omega) (by norm_num))
    (nonzeroCanonicalSmall 10 (by omega) (by norm_num))
    (by decide)

theorem threeEntry_pre_witness :
    RegistryWitness (logicalStorageOfStor threeStor)
      [(7, 9), (8, 10), (11, 12)] := by
  exact twoEntry_pre_witness.applyFreshWrites
    (nonzeroCanonicalSmall 11 (by omega) (by norm_num))
    (nonzeroCanonicalSmall 12 (by omega) (by norm_num))
    (by decide)

/-! ### Assignment/membership mutant -/

def assignmentOmittedStor : Stor :=
  applyRegistryWrites Stor.empty
    [(arrayEntrySlot (Nat.toB256 1), 7),
     (indexSlot 7, Nat.toB256 1),
     (arrayLengthSlot, Nat.toB256 1),
     (countSlot 9, Nat.toB256 1)]

theorem assignmentOmitted_rejected :
    ¬ RegistryWitness
      (logicalStorageOfStor assignmentOmittedStor) [(7, 9)] := by
  intro hw
  have h := hw.assignments 7 (canonicalSmall 7 (by norm_num))
  have hactual : assignmentOmittedStor.get (assignmentSlot 7) = 0 := by
    decide
  have hexpected : assignmentAt [(7, 9)] 7 = 9 := by decide
  change assignmentOmittedStor.get (assignmentSlot 7) =
    assignmentAt [(7, 9)] 7 at h
  rw [hactual, hexpected] at h
  exact (by decide : (0 : B256) ≠ 9) h

/-! ### Distinct-pauser old-count mutant -/

def oldCountOmittedStor : Stor :=
  applyRegistryWrites oneStor
    [(assignmentSlot 7, 11),
     (countSlot 11, Nat.toB256 1)]

theorem distinctOldCountOmitted_rejected :
    ¬ RegistryWitness
      (logicalStorageOfStor oldCountOmittedStor) [(7, 11)] := by
  intro hw
  have h := hw.counts 9 (canonicalSmall 9 (by norm_num))
  have hactual : oldCountOmittedStor.get (countSlot 9) = 1 := by decide
  have hexpected : assignmentCount [(7, 11)] 9 = 0 := by decide
  change oldCountOmittedStor.get (countSlot 9) =
    Nat.toB256 (assignmentCount [(7, 11)] 9) at h
  rw [hactual, hexpected] at h
  exact (by decide : (1 : B256) ≠ Nat.toB256 0) h

/-! ### Distinct-pauser new-count mutant -/

def newCountOmittedStor : Stor :=
  applyRegistryWrites oneStor
    [(assignmentSlot 7, 11),
     (countSlot 9, Nat.toB256 0)]

theorem distinctNewCountOmitted_rejected :
    ¬ RegistryWitness
      (logicalStorageOfStor newCountOmittedStor) [(7, 11)] := by
  intro hw
  have h := hw.counts 11 (canonicalSmall 11 (by norm_num))
  have hactual : newCountOmittedStor.get (countSlot 11) = 0 := by decide
  have hexpected : assignmentCount [(7, 11)] 11 = 1 := by decide
  change newCountOmittedStor.get (countSlot 11) =
    Nat.toB256 (assignmentCount [(7, 11)] 11) at h
  rw [hactual, hexpected] at h
  exact (by decide : (0 : B256) ≠ Nat.toB256 1) h

/-! ### Fresh append zero-based index/length mutant -/

def zeroBasedFreshStor : Stor :=
  applyRegistryWrites Stor.empty
    [(assignmentSlot 7, 9),
     (arrayEntrySlot 0, 7),
     (indexSlot 7, 0),
     (arrayLengthSlot, 0),
     (countSlot 9, Nat.toB256 1)]

theorem freshZeroBasedIndexLength_rejected :
    ¬ RegistryWitness
      (logicalStorageOfStor zeroBasedFreshStor) [(7, 9)] := by
  intro hw
  have h := hw.lengthWord
  have hactual : zeroBasedFreshStor.get arrayLengthSlot = 0 := by decide
  change zeroBasedFreshStor.get arrayLengthSlot = Nat.toB256 1 at h
  rw [hactual] at h
  exact (by decide : (0 : B256) ≠ Nat.toB256 1) h

/-! ### Middle-removal hole and dead-tail mutant -/

def middleHoleTailOmittedStor : Stor :=
  applyRegistryWrites threeStor
    [(assignmentSlot 8, 0),
     (countSlot 10, 0),
     (indexSlot 11, Nat.toB256 2),
     (arrayLengthSlot, Nat.toB256 2),
     (indexSlot 8, 0)]

theorem middleRemovalHoleTailOmitted_rejected :
    (¬ RegistryWitness
      (logicalStorageOfStor middleHoleTailOmittedStor)
      [(7, 9), (11, 12)]) ∧
    middleHoleTailOmittedStor.get
      (arrayEntrySlot (Nat.toB256 3)) = 11 := by
  constructor
  · intro hw
    have h := hw.arrayWords 1 (by decide)
    have hactual : middleHoleTailOmittedStor.get
        (arrayEntrySlot (Nat.toB256 2)) = 8 := by decide
    have hexpected : targetAt [(7, 9), (11, 12)] 1 = 11 := by decide
    change middleHoleTailOmittedStor.get
      (arrayEntrySlot (Nat.toB256 2)) =
        targetAt [(7, 9), (11, 12)] 1 at h
    rw [hactual, hexpected] at h
    exact (by decide : (8 : B256) ≠ 11) h
  · decide

/-! ### Moved-target reverse-index repair mutant -/

def movedIndexOmittedStor : Stor :=
  applyRegistryWrites threeStor
    [(assignmentSlot 8, 0),
     (countSlot 10, 0),
     (arrayEntrySlot (Nat.toB256 2), 11),
     (arrayEntrySlot (Nat.toB256 3), 0),
     (arrayLengthSlot, Nat.toB256 2),
     (indexSlot 8, 0)]

theorem movedIndexOmitted_rejected :
    ¬ RegistryWitness
      (logicalStorageOfStor movedIndexOmittedStor)
      [(7, 9), (11, 12)] := by
  intro hw
  have h := hw.indices 11 (canonicalSmall 11 (by norm_num))
  have hactual : movedIndexOmittedStor.get (indexSlot 11) = 3 := by decide
  have hexpected : oneBasedIndexAt [(7, 9), (11, 12)] 11 = 2 := by decide
  change movedIndexOmittedStor.get (indexSlot 11) =
    Nat.toB256 (oneBasedIndexAt [(7, 9), (11, 12)] 11) at h
  rw [hactual, hexpected] at h
  exact (by decide : (3 : B256) ≠ Nat.toB256 2) h

/-! ### Removed-target reverse-index clear mutant -/

def removedIndexClearOmittedStor : Stor :=
  applyRegistryWrites threeStor
    [(assignmentSlot 8, 0),
     (countSlot 10, 0),
     (arrayEntrySlot (Nat.toB256 2), 11),
     (indexSlot 11, Nat.toB256 2),
     (arrayEntrySlot (Nat.toB256 3), 0),
     (arrayLengthSlot, Nat.toB256 2)]

theorem removedTargetIndexClearOmitted_rejected :
    ¬ RegistryWitness
      (logicalStorageOfStor removedIndexClearOmittedStor)
      [(7, 9), (11, 12)] := by
  intro hw
  have h := hw.indices 8 (canonicalSmall 8 (by norm_num))
  have hactual : removedIndexClearOmittedStor.get (indexSlot 8) = 2 := by
    decide
  have hexpected : oneBasedIndexAt [(7, 9), (11, 12)] 8 = 0 := by decide
  change removedIndexClearOmittedStor.get (indexSlot 8) =
    Nat.toB256 (oneBasedIndexAt [(7, 9), (11, 12)] 8) at h
  rw [hactual, hexpected] at h
  exact (by decide : (2 : B256) ≠ Nat.toB256 0) h

/-! ### Target-zero guard-order semantic mutant -/

/-- A proof-only executable mutant which performs the Registry assignment
write before checking whether the target is zero. -/
def targetZeroGuardAfterAssignment : Func :=
  Blanc.Ninst.pushB256 9 :::
  Blanc.Ninst.pushB256 (assignmentSlot 0) :::
  Blanc.Ninst.sstore :::
  Blanc.Ninst.pushB256 0 :::
  Blanc.Ninst.iszero :::
  (Func.stop <?> Func.stop)

private def targetZeroGuardAfterAssignmentProg : Prog :=
  ⟨targetZeroGuardAfterAssignment, []⟩

private def targetZeroGuardAfterAssignmentCode : ByteArray :=
  ByteArray.mk targetZeroGuardAfterAssignmentProg.emitUnchecked.toArray

private theorem mutantByteArray_toList (bs : Bytes) :
    (ByteArray.mk bs.toArray).toList = bs := by
  rw [ByteArray.toList_eq_toList_data]

private theorem targetZeroGuardAfterAssignment_compile :
    some targetZeroGuardAfterAssignmentCode.toList =
      targetZeroGuardAfterAssignmentProg.compile := by
  rw [targetZeroGuardAfterAssignmentCode, mutantByteArray_toList]
  rfl

private def targetZeroMutantOwner : Adr := Nat.toAdr 100

private def targetZeroMutantSevm : Sevm :=
  { (default : Sevm) with
    currentTarget := targetZeroMutantOwner
    codeAddress := some targetZeroMutantOwner
    code := targetZeroGuardAfterAssignmentCode
    isStatic := false }

private def targetZeroMutantBase : Devm :=
  addAccessedStorageKey (default : Devm)
    targetZeroMutantOwner (assignmentSlot 0)

private def targetZeroMutantPre : Devm :=
  targetZeroMutantBase.setMach
    ⟨[], targetZeroMutantBase.memory, 50001⟩

private def targetZeroMutantD0 : Devm :=
  targetZeroMutantBase.setMach
    ⟨[], targetZeroMutantBase.memory, 50000⟩

private def targetZeroMutantD1 : Devm :=
  targetZeroMutantD0.setMach
    ⟨[9], targetZeroMutantD0.memory, 49997⟩

private def targetZeroMutantD2 : Devm :=
  targetZeroMutantD0.setMach
    ⟨[assignmentSlot 0, 9], targetZeroMutantD0.memory, 49994⟩

private def targetZeroMutantD3 : Devm :=
  ((targetZeroMutantD0.withRefundCounter 0).setStorVal
    targetZeroMutantOwner (assignmentSlot 0) 9).setMach
      ⟨[], targetZeroMutantD0.memory, 29994⟩

private def targetZeroMutantPost : Devm :=
  ((targetZeroMutantD0.withRefundCounter 0).setStorVal
    targetZeroMutantOwner (assignmentSlot 0) 9).setMach
      ⟨[], targetZeroMutantD0.memory, 29975⟩

private theorem targetZeroMutant_push9 :
    Ninst.RunCompiled targetZeroMutantSevm targetZeroMutantD0
      (Blanc.Ninst.pushB256 9) targetZeroMutantD1 := by
  apply Ninst.runCompiled_pushB256 (c := 3) (G := 49997)
  · decide
  · rfl
  · decide

private theorem targetZeroMutant_pushKey :
    Ninst.RunCompiled targetZeroMutantSevm targetZeroMutantD1
      (Blanc.Ninst.pushB256 (assignmentSlot 0))
      targetZeroMutantD2 := by
  apply Ninst.runCompiled_pushB256 (c := 3) (G := 49994)
  · decide
  · rfl
  · decide

private theorem targetZeroMutant_store :
    Ninst.RunCompiled targetZeroMutantSevm targetZeroMutantD2
      Blanc.Ninst.sstore targetZeroMutantD3 := by
  apply Ninst.runCompiled_sstore_warm
      (c := gasStorageSet) (G := 29994)
  · rfl
  · change (targetZeroMutantOwner, assignmentSlot 0) ∈
      (default : Devm).accessedStorageKeys.insert
        (targetZeroMutantOwner, assignmentSlot 0)
    exact Std.HashSet.mem_insert_self
  · decide
  · rfl
  · decide
  · decide
  · rfl

private theorem targetZeroMutant_funcRun :
    Func.RunCompiled [targetZeroGuardAfterAssignment]
      targetZeroMutantSevm targetZeroMutantD0
      targetZeroGuardAfterAssignment targetZeroMutantPost := by
  exact Func.RunCompiled.next targetZeroMutant_push9
    (Func.RunCompiled.next targetZeroMutant_pushKey
      (Func.RunCompiled.next targetZeroMutant_store (by
        func_run [1]
        all_goals try simp [targetZeroMutantD3,
          targetZeroMutantPost, targetZeroMutantD0,
          targetZeroMutantBase, targetZeroMutantSevm,
          targetZeroMutantOwner, targetZeroGuardAfterAssignment,
          gVerylow, gHigh, gJumpdest]
        case h_arm =>
          apply Func.RunCompiled.last
          rfl)))

private theorem targetZeroMutant_progRun :
    Prog.RunCompiled targetZeroMutantSevm targetZeroMutantPre
      targetZeroGuardAfterAssignmentProg targetZeroMutantPost := by
  refine ⟨targetZeroMutantD0, ?_, targetZeroMutant_funcRun⟩
  exact Devm.burnBy_setMach_gas rfl

private theorem targetZeroMutant_preValue :
    targetZeroMutantPre.getStorVal targetZeroMutantOwner
      (assignmentSlot 0) = 0 := by
  rfl

private theorem targetZeroMutant_postValue :
    targetZeroMutantPost.getStorVal targetZeroMutantOwner
      (assignmentSlot 0) = 9 := by
  change ((Devm.getStor
    (targetZeroMutantD0.setStorVal targetZeroMutantOwner
      (assignmentSlot 0) 9) targetZeroMutantOwner).get
        (assignmentSlot 0)) = 9
  rw [setStorVal_getStor_self, Stor.get_set_self]

private theorem targetZeroMutant_exec :
    Nonempty (Exec 0 targetZeroMutantSevm targetZeroMutantPre
      (.ok targetZeroMutantPost)) := by
  have hexec :
      exec ⟨0, targetZeroMutantSevm, targetZeroMutantPre⟩ =
        .ok targetZeroMutantPost :=
    Prog.exec_of_runCompiled targetZeroMutant_progRun
      targetZeroGuardAfterAssignment_compile
  exact (exec_iff_exec_eq _ _ _ _).2 hexec

private theorem targetZeroMutant_write
    (execution : Exec 0 targetZeroMutantSevm targetZeroMutantPre
      (.ok targetZeroMutantPost)) :
    ∃ write : Exec.SuccessfulSstoreOccurrence
        (⟨0, targetZeroMutantSevm, targetZeroMutantPre,
          .ok targetZeroMutantPost, execution⟩ : Exec.Deriv),
      write.Retained ∧
      write.storageOwner = targetZeroMutantOwner ∧
      write.key = assignmentSlot 0 ∧
      write.value = 9 := by
  have hchanged :
      targetZeroMutantPre.getStorVal targetZeroMutantOwner
          (assignmentSlot 0) ≠
        targetZeroMutantPost.getStorVal targetZeroMutantOwner
          (assignmentSlot 0) := by
    rw [targetZeroMutant_preValue, targetZeroMutant_postValue]
    decide
  rcases Exec.exists_lastRetainedSstore_of_getStor_ne execution rfl hchanged with
    ⟨write, hretained, howner, hkey, hvalue, _⟩
  refine ⟨write, hretained, howner, hkey, hvalue.trans ?_⟩
  simpa only [Execution.committedPost, Devm.getStor, Devm.getStorVal] using
    targetZeroMutant_postValue

/-- The executable guard-order mutant reaches a successful Registry assignment
SSTORE at target zero.  Its actual compiled execution therefore falsifies the
production target-zero theorem's universal non-SSTORE conclusion. -/
theorem targetZeroGuardAfterAssignment_compiled_rejected :
    ∃ (program : Prog) (code : ByteArray) (sevm : Sevm)
      (pre post : Devm)
      (_run : Prog.RunCompiled sevm pre program post)
      (execution : Exec 0 sevm pre (.ok post)),
      program = ⟨targetZeroGuardAfterAssignment, []⟩ ∧
      code = ByteArray.mk program.emitUnchecked.toArray ∧
      some code.toList = program.compile ∧
      sevm.code = code ∧
      sevm.currentTarget = Nat.toAdr 100 ∧
      sevm.isStatic = false ∧
      ((Nat.toAdr 100, assignmentSlot 0) : Adr × B256) ∈
        pre.accessedStorageKeys ∧
      pre.getStorVal (Nat.toAdr 100) (assignmentSlot 0) = 0 ∧
      post.getStorVal (Nat.toAdr 100) (assignmentSlot 0) = 9 ∧
      ∃ write : Exec.SuccessfulSstoreOccurrence
          (⟨0, sevm, pre, .ok post, execution⟩ : Exec.Deriv),
        write.Retained ∧
        write.storageOwner = Nat.toAdr 100 ∧
        write.key = assignmentSlot 0 ∧
        write.value = 9 ∧
        ¬(∀ occurrence : Exec.NinstOccurrence
            (⟨0, sevm, pre, .ok post, execution⟩ : Exec.Deriv),
          occurrence.instruction ≠ .reg .sstore) := by
  rcases targetZeroMutant_exec with ⟨execution⟩
  rcases targetZeroMutant_write execution with
    ⟨write, hretained, howner, hkey, hvalue⟩
  refine ⟨targetZeroGuardAfterAssignmentProg,
    targetZeroGuardAfterAssignmentCode, targetZeroMutantSevm,
    targetZeroMutantPre, targetZeroMutantPost,
    targetZeroMutant_progRun, execution, rfl, rfl,
    targetZeroGuardAfterAssignment_compile, rfl, rfl, rfl, ?_,
    ?_, ?_, write, hretained, ?_, hkey, hvalue, ?_⟩
  · change (targetZeroMutantOwner, assignmentSlot 0) ∈
      (default : Devm).accessedStorageKeys.insert
        (targetZeroMutantOwner, assignmentSlot 0)
    exact Std.HashSet.mem_insert_self
  · simpa only [targetZeroMutantOwner] using targetZeroMutant_preValue
  · simpa only [targetZeroMutantOwner] using targetZeroMutant_postValue
  · simpa only [targetZeroMutantOwner] using howner
  intro hall
  exact hall write.occurrence write.instruction_eq

end RegistryMutants

end Blanc.LidoCircuitBreaker
