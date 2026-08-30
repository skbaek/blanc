import Blanc.BeaconDepositDeploy
import Blanc.BeaconDepositCorrectness
import Blanc.DeploymentOccurrence

/-!
# Beacon deposit SSTORE source attribution

Occurrence-facing closure of the compiler-owned persistent-write population.
The runtime has exactly the main-body count store and the insertion-loop branch
store.  The constructor has one recursive source store in its compiled prefix;
the theorem applies even though the runtime bytes are appended to creation
code.

These statements classify source instruction sites.  Dynamic keys, write
values, chronology, retention, and settlement are proved by downstream C5
effect modules rather than inferred from program counters.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-! ## Exact effect vocabularies -/

/-- The successful deposit's complete retained write chronology: count first,
then the unique first-live branch cell. -/
def depositStorageEffectTriples
    (owner : Adr) (stor : Stor) (height : Nat)
    (depositDataRoot : B256) : List (Adr × B256 × B256) :=
  [(owner, depositCountSlot,
      Nat.toB256 (accOfStor stor).count + 1),
    (owner, branchSlot height,
      accumulatedNode Bytes.sha256 (accOfStor stor).branch
        0 height depositDataRoot)]

/-- The constructor's complete retained write chronology: zero-hash slots one
through thirty-one in increasing order, with the matching model digest. -/
def constructorStorageEffectTriples
    (owner : Adr) : List (Adr × B256 × B256) :=
  (List.range 31).map fun index =>
    let height := index + 1
    (owner, zeroHashSlot height, zeroHash Bytes.sha256 height)

/-- Constructor chronology for `remaining` iterations, beginning immediately
above `height`.  This recursion-facing form is extensionally the public
source-order list at height zero. -/
def constructorStorageEffectTriplesFrom
    (owner : Adr) : Nat → Nat → List (Adr × B256 × B256)
  | _, 0 => []
  | height, remaining + 1 =>
      (owner, zeroHashSlot (height + 1),
          zeroHash Bytes.sha256 (height + 1)) ::
        constructorStorageEffectTriplesFrom owner (height + 1) remaining

@[simp] theorem constructorStorageEffectTriplesFrom_zero
    (owner : Adr) (height : Nat) :
    constructorStorageEffectTriplesFrom owner height 0 = [] :=
  rfl

@[simp] theorem constructorStorageEffectTriplesFrom_succ
    (owner : Adr) (height remaining : Nat) :
    constructorStorageEffectTriplesFrom owner height (remaining + 1) =
      (owner, zeroHashSlot (height + 1),
          zeroHash Bytes.sha256 (height + 1)) ::
        constructorStorageEffectTriplesFrom owner (height + 1) remaining :=
  rfl

theorem constructorStorageEffectTriplesFrom_eq_range
    (owner : Adr) (height remaining : Nat) :
    constructorStorageEffectTriplesFrom owner height remaining =
      (List.range remaining).map fun index =>
        (owner, zeroHashSlot (height + index + 1),
          zeroHash Bytes.sha256 (height + index + 1)) := by
  induction remaining generalizing height with
  | zero => rfl
  | succ remaining ih =>
      rw [constructorStorageEffectTriplesFrom_succ,
        List.range_succ_eq_map, List.map_cons, ih]
      apply congrArg₂ List.cons
      · rw [show height + 0 + 1 = height + 1 by omega]
      · rw [List.map_map]
        apply List.map_congr_left
        intro index _
        simp only [Function.comp_apply]
        rw [show height + 1 + index + 1 =
          height + Nat.succ index + 1 by omega]

/-- The recursion-facing chronology at the constructor's initial height is the
same thirty-one-element vocabulary exported by `constructorStorageEffectTriples`. -/
theorem constructorStorageEffectTriplesFrom_initial (owner : Adr) :
    constructorStorageEffectTriplesFrom owner 0 31 =
      constructorStorageEffectTriples owner := by
  rw [constructorStorageEffectTriplesFrom_eq_range]
  unfold constructorStorageEffectTriples
  apply List.map_congr_left
  intro index _
  rw [show 0 + index + 1 = index + 1 by omega]

theorem depositStorageEffectTriples_length
    (owner : Adr) (stor : Stor) (height : Nat) (depositDataRoot : B256) :
    (depositStorageEffectTriples owner stor height depositDataRoot).length = 2 :=
  rfl

theorem constructorStorageEffectTriples_length (owner : Adr) :
    (constructorStorageEffectTriples owner).length = 31 := by
  simp [constructorStorageEffectTriples]

/-- The compiler and creation-byte witnesses package the constructor as an
exact compiled prefix of the full creation code. -/
theorem Exec.Deriv.beaconConstructor_exactProgramPrefix
    {root : Exec.Deriv}
    (entryPc : root.pc = 0)
    (codeIdentity : root.sevm.code.toList = creationCode) :
    root.exactProgramPrefix
      constructorProgram constructorInitPrefix code := by
  refine ⟨entryPc, ?_⟩
  exact ⟨constructorInitPrefix_compile.symm, by
    simpa only [creationCode] using codeIdentity⟩

/-- Every same-frame raw runtime SSTORE belongs to one of the compiler's two
exact persistent-write source sites. -/
theorem Exec.Deriv.beaconRuntime_sstore_pc
    {root target : Exec.Deriv}
    {storageTarget codeAddress : Adr}
    (invocation : root.exactInvocation runtime storageTarget codeAddress)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
      target.pc = 1070 ∨ target.pc = 2869 := by
  rcases root.sstore_sourceSite invocation sameFrame storeAt with
    ⟨site, sourceMember, sitePc, siteInstruction⟩
  have inventoryMember : site ∈ runtimeSstoreSourceSites :=
    mem_runtimeSstoreSourceSites_iff.mpr
      ⟨sourceMember, siteInstruction⟩
  rcases runtimeSstoreSourceSite_pc inventoryMember with countPc | branchPc
  · left
    rw [← sitePc]
    exact countPc
  · right
    rw [← sitePc]
    exact branchPc

/-- Role-preserving source coordinate classification.  Function-table entry
zero is the inlined main/deposit count write; entry thirteen is the insertion
loop's first-live branch write. -/
theorem Exec.Deriv.beaconRuntime_sstore_coordinate
    {root target : Exec.Deriv}
    {storageTarget codeAddress : Adr}
    (invocation : root.exactInvocation runtime storageTarget codeAddress)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ site : Prog.SourceSite,
      site ∈ runtimeSstoreSourceSites ∧
      site.pc = target.pc ∧
      ((site.path.functionIndex = 0 ∧ site.pc = 1070) ∨
        (site.path.functionIndex = 13 ∧ site.pc = 2869)) := by
  rcases root.sstore_sourceSite invocation sameFrame storeAt with
    ⟨site, sourceMember, sitePc, siteInstruction⟩
  have inventoryMember : site ∈ runtimeSstoreSourceSites :=
    mem_runtimeSstoreSourceSites_iff.mpr
      ⟨sourceMember, siteInstruction⟩
  exact ⟨site, inventoryMember, sitePc,
    runtimeSstoreSourceSite_coordinate inventoryMember⟩

/-- Global-occurrence form: once an actual raw frame root is identified as an
exact Beacon runtime invocation, every SSTORE it owns has one of the two
compiler-owned runtime PCs. -/
theorem Exec.NinstOccurrence.beaconRuntime_sstore_pc_of_rawFrameRoot
    {globalRoot frameRoot : Exec.Deriv}
    {storageTarget codeAddress : Adr}
    (occurrence : Exec.NinstOccurrence globalRoot)
    (instructionEq : occurrence.instruction = .reg .sstore)
    (selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)
    (invocation : frameRoot.exactInvocation
      runtime storageTarget codeAddress)
    (sameFrame : Exec.Deriv.ParentPrefix frameRoot occurrence.node) :
    occurrence.node.pc = 1070 ∨ occurrence.node.pc = 2869 := by
  rcases occurrence.sourceSite_of_rawFrameRoot instructionEq selected
      invocation sameFrame with
    ⟨site, sourceMember, sitePc, siteInstruction⟩
  have inventoryMember : site ∈ runtimeSstoreSourceSites :=
    mem_runtimeSstoreSourceSites_iff.mpr
      ⟨sourceMember, siteInstruction⟩
  rcases runtimeSstoreSourceSite_pc inventoryMember with countPc | branchPc
  · left
    rw [← sitePc]
    exact countPc
  · right
    rw [← sitePc]
    exact branchPc

/-- Successful-step specialization of the complete same-frame runtime source
classification.  The enclosing runtime may still revert later. -/
theorem Exec.Deriv.beaconRuntime_successfulSstore_pc
    {root : Exec.Deriv} {storageTarget codeAddress : Adr}
    (invocation : root.exactInvocation runtime storageTarget codeAddress)
    (write : Exec.SuccessfulSstoreOccurrence root)
    (sameFrame : Exec.Deriv.ParentPrefix root write.occurrence.node) :
    write.occurrence.node.pc = 1070 ∨
      write.occurrence.node.pc = 2869 := by
  have storeAt : Ninst.At write.occurrence.node.sevm.code
      write.occurrence.node.pc (.reg .sstore) := by
    rw [← write.instruction_eq]
    exact write.occurrence.decoded
  exact Exec.Deriv.beaconRuntime_sstore_pc invocation sameFrame storeAt

/-- Every same-frame raw constructor SSTORE belongs to the unique recursive
zero-hash write site in the compiled creation prefix. -/
theorem Exec.Deriv.beaconConstructor_sstore_pc
    {root target : Exec.Deriv}
    (identity : root.exactProgramPrefix
      constructorProgram constructorInitPrefix code)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    target.pc = 137 := by
  rcases root.sstore_sourceSite_appended identity sameFrame storeAt with
    ⟨site, sourceMember, sitePc, siteInstruction⟩
  have inventoryMember : site ∈ constructorSstoreSourceSites :=
    mem_constructorSstoreSourceSites_iff.mpr
      ⟨sourceMember, siteInstruction⟩
  rw [← sitePc]
  exact constructorSstoreSourceSite_pc inventoryMember

/-- The constructor write role is uniquely the zero-hash continuation at
function-table entry four and prefix PC 137. -/
theorem Exec.Deriv.beaconConstructor_sstore_coordinate
    {root target : Exec.Deriv}
    (identity : root.exactProgramPrefix
      constructorProgram constructorInitPrefix code)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ site : Prog.SourceSite,
      site ∈ constructorSstoreSourceSites ∧
      site.pc = target.pc ∧
      site.path.functionIndex = 4 ∧ site.pc = 137 := by
  rcases root.sstore_sourceSite_appended identity sameFrame storeAt with
    ⟨site, sourceMember, sitePc, siteInstruction⟩
  have inventoryMember : site ∈ constructorSstoreSourceSites :=
    mem_constructorSstoreSourceSites_iff.mpr
      ⟨sourceMember, siteInstruction⟩
  exact ⟨site, inventoryMember, sitePc,
    constructorSstoreSourceSite_coordinate inventoryMember⟩

/-- Successful-step specialization of the exact appended-constructor source
classification.  The one source site may execute once per loop iteration. -/
theorem Exec.Deriv.beaconConstructor_successfulSstore_pc
    {root : Exec.Deriv}
    (identity : root.exactProgramPrefix
      constructorProgram constructorInitPrefix code)
    (write : Exec.SuccessfulSstoreOccurrence root)
    (sameFrame : Exec.Deriv.ParentPrefix root write.occurrence.node) :
    write.occurrence.node.pc = 137 := by
  have storeAt : Ninst.At write.occurrence.node.sevm.code
      write.occurrence.node.pc (.reg .sstore) := by
    rw [← write.instruction_eq]
    exact write.occurrence.decoded
  exact Exec.Deriv.beaconConstructor_sstore_pc identity sameFrame storeAt

end Blanc.BeaconDeposit
