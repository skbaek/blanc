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

theorem constructorStorageEffectTriplesFrom_zero
    (owner : Adr) (height : Nat) :
    constructorStorageEffectTriplesFrom owner height 0 = [] :=
  rfl

theorem constructorStorageEffectTriplesFrom_succ
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

/-- Every same-frame raw runtime SSTORE belongs to one of the compiler's two
exact persistent-write source sites. -/
theorem Exec.Deriv.beaconRuntime_sstore_pc
    {root target : Exec.Deriv}
    {storageTarget codeAddress : Adr}
    (invocation : (Blanc.Exec.Deriv.exactInvocation runtime storageTarget codeAddress root))
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
      target.pc = 1070 ∨ target.pc = 2869 := by
  rcases (Blanc.Exec.Deriv.sstore_sourceSite (root := root)) invocation sameFrame storeAt with
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

/-- Global-occurrence form: once an actual raw frame root is identified as an
exact Beacon runtime invocation, every SSTORE it owns has one of the two
compiler-owned runtime PCs. -/
theorem Exec.NinstOccurrence.beaconRuntime_sstore_pc_of_rawFrameRoot
    {globalRoot frameRoot : Exec.Deriv}
    {storageTarget codeAddress : Adr}
    (occurrence : Exec.NinstOccurrence globalRoot)
    (instructionEq : occurrence.instruction = .reg .sstore)
    (selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)
    (invocation : (Blanc.Exec.Deriv.exactInvocation
      runtime storageTarget codeAddress frameRoot))
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

/-- Every same-frame raw constructor SSTORE belongs to the unique recursive
zero-hash write site in the compiled creation prefix. -/
theorem Exec.Deriv.beaconConstructor_sstore_pc
    {root target : Exec.Deriv}
    (identity : (Blanc.Exec.Deriv.exactProgramPrefix
      constructorProgram constructorInitPrefix code root))
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    target.pc = 137 := by
  rcases (Blanc.Exec.Deriv.sstore_sourceSite_appended (root := root)) identity sameFrame storeAt with
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
    (identity : (Blanc.Exec.Deriv.exactProgramPrefix
      constructorProgram constructorInitPrefix code root))
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ site : Prog.SourceSite,
      site ∈ constructorSstoreSourceSites ∧
      site.pc = target.pc ∧
      site.path.functionIndex = 4 ∧ site.pc = 137 := by
  rcases (Blanc.Exec.Deriv.sstore_sourceSite_appended (root := root)) identity sameFrame storeAt with
    ⟨site, sourceMember, sitePc, siteInstruction⟩
  have inventoryMember : site ∈ constructorSstoreSourceSites :=
    mem_constructorSstoreSourceSites_iff.mpr
      ⟨sourceMember, siteInstruction⟩
  exact ⟨site, inventoryMember, sitePc,
    constructorSstoreSourceSite_coordinate inventoryMember⟩

end Blanc.BeaconDeposit
