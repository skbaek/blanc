import Blanc.BeaconDepositCode

/-!
# Beacon deposit constructor and creation artifact

The constructor materializes `zero_hashes[1..31]` through one tail-recursive
SHA-256 site, then returns the appended compiled runtime.  Every current
constructor coordinate and length fits in a fixed-width `PUSH2`; the exact
full-width fallback keeps future growth non-truncating.  Both branches have a
layout-independent width, so the provisional and final compiler passes retain
the same shape even though the runtime offset changes.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Independent constructor coordinates -/

def constructorEmptyRevertSlot : Nat := 1
def constructorBubbleRevertSlot : Nat := 2
def constructorZeroHashLoopSlot : Nat := 3
def constructorZeroHashContinuationSlot : Nat := 4

/-- Constructor scratch-memory word that carries the current zero-hash node. -/
def constructorNodeWord : B256 := 2

/-- Use fixed-width `PUSH2` for current constructor coordinates without ever
truncating a future value that outgrows two bytes. -/
def constructorPushWord (word : B256) : Ninst :=
  let value := word.toNat
  if value < 2 ^ 16 then
    Ninst.push [(value >>> 8).toUInt8, value.toUInt8] (by simp)
  else
    Ninst.push word.toBytes (by rw [B256.length_toBytes])

/-- Fixed-width constructor pushes for a source-order word list. -/
def constructorPushWords : List B256 → Line :=
  List.map constructorPushWord

/-- Exact compiled semantics of the constructor's fixed-width form, including
the full-width fallback when a future coordinate no longer fits in `PUSH2`. -/
theorem Ninst.runCompiled_constructorPushWord
    {sevm : Sevm} {devm : Devm} {word : B256} {G : Nat}
    (gas : devm.gasLeft = G + gVerylow)
    (room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (constructorPushWord word)
      (devm.setMach ⟨word :: devm.stack, devm.memory, G⟩) := by
  by_cases fit : word.toNat < 2 ^ 16
  · let bytes : Bytes :=
      [(word.toNat >>> 8).toUInt8, word.toNat.toUInt8]
    have cost : pushCost bytes = gVerylow := by
      simp [bytes, pushCost]
    have pushed : Bytes.toB256 bytes = word := by
      change Bytes.toB256
        [(word.toNat >>> 8).toUInt8, word.toNat.toUInt8] = word
      rw [List.toB256_pair word.toNat fit, Jaune.toB256_toNat]
    have run := Ninst.runCompiled_pushBytes
      (sevm := sevm) (devm := devm) (xs := bytes)
      (le := by simp [bytes]) (c := gVerylow) (G := G)
      cost gas room
    rw [constructorPushWord, if_pos fit]
    simpa only [bytes, pushed] using run
  · have run := Ninst.runCompiled_pushBytes
      (sevm := sevm) (devm := devm) (xs := word.toBytes)
      (le := by rw [B256.length_toBytes])
      (c := gVerylow) (G := G)
      (by
        have hne : word.toBytes ≠ [] := by
          intro empty
          have lengths := congrArg List.length empty
          simp only [B256.length_toBytes, List.length_nil] at lengths
          omega
        simp [pushCost, hne]) gas room
    rw [constructorPushWord, if_neg fit]
    simpa only [B256.toB256_toBytes] using run

/-- Load one constructor scratch word. -/
def constructorLoadWord (word : B256) : Line :=
  [constructorPushWord (word * 32), mload]

/-- Store one constructor scratch word. -/
def constructorStoreWord (word : B256) : Line :=
  [constructorPushWord (word * 32), mstore]

/-- Constructor-local returndata length comparison. -/
def constructorRetdataShorterThan (size : B256) : Line :=
  [constructorPushWord size, retdatasize, lt]

/-! ## Zero-hash materialization -/

/-- Constructor-local fixed-width SHA-256 wrapper. -/
def constructorSha64
    (inputWord outputWord : B256) (success : Func) : Func :=
  constructorPushWords [32, outputWord * 32, 64, inputWord * 32, 2] +++
  gas ::: statcall ::: iszero :::
  ((.call constructorBubbleRevertSlot) <?>
    (constructorRetdataShorterThan 32 +++
      ((.call constructorEmptyRevertSlot) <?> success)))

/-- Copy and return the appended runtime from creation code. -/
def constructorFinish
    (runtimeOffset runtimeLength : Nat) : Func :=
  constructorPushWords
      [Nat.toB256 runtimeLength, Nat.toB256 runtimeOffset, 0] +++
    codecopy :::
    constructorPushWords [Nat.toB256 runtimeLength, 0] +++
    Func.ret

/-- Store the newly computed zero hash and advance the loop height. -/
def constructorZeroHashContinuation : Func :=
  constructorLoadWord constructorNodeWord +++
  dup 1 ::: constructorPushWord (zeroHashBase + 1) ::: add ::: sstore :::
  constructorPushWord 1 ::: add ::: .call constructorZeroHashLoopSlot

/-- Tail-recursive constructor loop that materializes zero hashes 1 through 31. -/
def constructorZeroHashLoop
    (runtimeOffset runtimeLength : Nat) : Func :=
  dup 0 ::: constructorPushWord 31 ::: swap 0 ::: lt :::
  (((constructorLoadWord constructorNodeWord ++ constructorStoreWord 0 ++
      constructorLoadWord constructorNodeWord ++ constructorStoreWord 1) +++
      constructorSha64 0 constructorNodeWord
        (.call constructorZeroHashContinuationSlot)) <?>
    constructorFinish runtimeOffset runtimeLength)

/-- Initialize constructor scratch memory and enter the zero-hash loop. -/
def constructorStart : Func :=
  ([constructorPushWord 0] ++ constructorStoreWord constructorNodeWord ++
    [constructorPushWord 0]) +++
  .call constructorZeroHashLoopSlot

/-- Constructor program parameterized by its appended-runtime coordinates. -/
def constructorProgramAt
    (runtimeOffset runtimeLength : Nat) : Prog :=
  { main := nonpayable constructorStart
    aux := [Func.rev, Func.revReturnData,
      constructorZeroHashLoop runtimeOffset runtimeLength,
      constructorZeroHashContinuation] }

/-! ## Two-pass compiled creation artifact -/

private def provisionalConstructorProgram : Prog :=
  constructorProgramAt 0 codeSize

private def provisionalConstructorPrefix : Bytes :=
  (Prog.compile provisionalConstructorProgram).getD []

def constructorRuntimeOffset : Nat :=
  provisionalConstructorPrefix.length

/-- The exact constructor program compiled into the creation prefix. -/
def constructorProgram : Prog :=
  constructorProgramAt constructorRuntimeOffset codeSize

def constructorInitPrefix : Bytes :=
  (Prog.compile constructorProgram).getD []

def creationCode : Bytes :=
  constructorInitPrefix ++ code

def constructorCreationCode : Bytes :=
  creationCode

def eip3860InitcodeLimit : Nat :=
  pragueCodeLimits.maxInitCodeSize

/-! ## Compiler and layout witnesses -/

private theorem provisionalConstructorProgram_compiles :
    Prog.compiles provisionalConstructorProgram = true := by
  decide +kernel

private theorem provisionalConstructorPrefix_compile :
    Prog.compile provisionalConstructorProgram =
      some provisionalConstructorPrefix := by
  unfold provisionalConstructorPrefix
  exact Prog.compile_eq_some_getD_of_compiles _
    provisionalConstructorProgram_compiles

theorem constructorProgram_compiles :
    Prog.compiles constructorProgram = true := by
  decide +kernel

theorem constructorInitPrefix_compile :
    Prog.compile constructorProgram = some constructorInitPrefix := by
  unfold constructorInitPrefix
  exact Prog.compile_eq_some_getD_of_compiles _ constructorProgram_compiles

private theorem provisionalConstructorPrefix_length :
    provisionalConstructorPrefix.length = 146 := by
  decide +kernel

theorem constructorRuntimeOffset_exact :
    constructorRuntimeOffset = 146 := by
  simpa [constructorRuntimeOffset] using provisionalConstructorPrefix_length

/-- Fixed-width immediates make the final prefix exactly as long as the
provisional offset embedded into it. -/
theorem constructorInitPrefix_length_eq_provisionalOffset :
    constructorInitPrefix.length = constructorRuntimeOffset := by
  decide +kernel

theorem constructorInitPrefix_length_exact :
    constructorInitPrefix.length = 146 := by
  rw [constructorInitPrefix_length_eq_provisionalOffset,
    constructorRuntimeOffset_exact]

theorem constructorAppendedRuntime_length_exact :
    code.length = 2891 := by
  simpa [codeSize] using codeSize_exact

theorem creationCode_eq_prefix_append_runtime :
    creationCode = constructorInitPrefix ++ code := by
  rfl

theorem constructorCreationCode_eq_creationCode :
    constructorCreationCode = creationCode := by
  rfl

theorem creationCode_length_exact :
    creationCode.length = 3037 := by
  simp [creationCode, constructorInitPrefix_length_exact,
    constructorAppendedRuntime_length_exact]

theorem eip3860InitcodeLimit_exact :
    eip3860InitcodeLimit = 49152 := by
  rfl

theorem creationCode_eip3860 :
    creationCode.length <= eip3860InitcodeLimit := by
  rw [creationCode_length_exact, eip3860InitcodeLimit_exact]
  decide

theorem creationCode_drop_prefix :
    creationCode.drop constructorInitPrefix.length = code := by
  simp [creationCode]

theorem creationCode_drop_runtimeOffset :
    creationCode.drop constructorRuntimeOffset = code := by
  rw [← constructorInitPrefix_length_eq_provisionalOffset]
  exact creationCode_drop_prefix

/-- The constructor's CODECOPY window is exactly the appended runtime. -/
theorem creationCode_slice_runtime :
    creationCode.sliceD constructorRuntimeOffset codeSize 0 = code := by
  rw [← constructorInitPrefix_length_eq_provisionalOffset]
  unfold creationCode List.sliceD
  rw [List.drop_length_append' rfl]
  apply Bytes.sliceD_zero_length
  change code.length = codeSize
  exact constructorAppendedRuntime_length_exact.trans codeSize_exact.symm

/-! ## Exact constructor source-site inventory -/

private def constructorIsSstore : Ninst → Bool
  | .reg .sstore => true
  | _ => false

private def constructorIsStaticcall : Ninst → Bool
  | .exec .statcall => true
  | _ => false

private def constructorIsCodecopy : Ninst → Bool
  | .reg .codecopy => true
  | _ => false

private def constructorIsExternalExecution : Ninst → Bool
  | .exec _ => true
  | _ => false

private def constructorSourceSitesMatching
    (predicate : Ninst → Bool) : List Prog.SourceSite :=
  constructorProgram.sourceSites.filter fun site => predicate site.instruction

def constructorSstoreSourceSites : List Prog.SourceSite :=
  constructorSourceSitesMatching constructorIsSstore

def constructorStaticcallSourceSites : List Prog.SourceSite :=
  constructorSourceSitesMatching constructorIsStaticcall

def constructorCodecopySourceSites : List Prog.SourceSite :=
  constructorSourceSitesMatching constructorIsCodecopy

def constructorExternalExecutionSourceSites : List Prog.SourceSite :=
  constructorSourceSitesMatching constructorIsExternalExecution

/-- Membership in the constructor SSTORE inventory is exactly membership in
the constructor source map at its recursive source-level SSTORE. -/
theorem mem_constructorSstoreSourceSites_iff
    {site : Prog.SourceSite} :
    site ∈ constructorSstoreSourceSites ↔
      site ∈ constructorProgram.sourceSites ∧
        site.instruction = .reg .sstore := by
  rcases site with ⟨path, pc, instruction⟩
  cases instruction <;>
    simp [constructorSstoreSourceSites, constructorSourceSitesMatching,
      constructorIsSstore]
  rename_i regular
  cases regular <;>
    simp

def runtimeAndConstructorStaticcallSourceSites : List Prog.SourceSite :=
  runtimeStaticcallSourceSites ++ constructorStaticcallSourceSites

private theorem constructorSourceSiteFacts :
    constructorSstoreSourceSites.length = 1 ∧
    Prog.SourceSite.pcs constructorSstoreSourceSites = [137] ∧
    constructorStaticcallSourceSites.length = 1 ∧
    Prog.SourceSite.pcs constructorStaticcallSourceSites = [98] ∧
    constructorCodecopySourceSites.length = 1 ∧
    Prog.SourceSite.pcs constructorCodecopySourceSites = [57] ∧
    (constructorExternalExecutionSourceSites.all fun site =>
      match site.instruction with
      | .exec .statcall => true
      | _ => false) = true ∧
    constructorExternalExecutionSourceSites.length = 1 ∧
    Prog.SourceSite.pcs constructorExternalExecutionSourceSites = [98] := by
  decide +kernel

theorem constructorSstoreSourceSites_length :
    constructorSstoreSourceSites.length = 1 :=
  constructorSourceSiteFacts.1

theorem constructorSstoreSourceSites_pcs :
    Prog.SourceSite.pcs constructorSstoreSourceSites = [137] :=
  constructorSourceSiteFacts.2.1

theorem constructorSstoreSourceSites_coordinates :
    Prog.SourceSite.coordinates constructorSstoreSourceSites = [(4, 137)] := by
  decide +kernel

/-- Every constructor source-level SSTORE is the unique recursive zero-hash
write site at compiled prefix PC 137. -/
theorem constructorSstoreSourceSite_pc
    {site : Prog.SourceSite}
    (member : site ∈ constructorSstoreSourceSites) :
    site.pc = 137 := by
  have pcMember : site.pc ∈ Prog.SourceSite.pcs constructorSstoreSourceSites :=
    List.mem_map_of_mem member
  rw [constructorSstoreSourceSites_pcs] at pcMember
  simpa using pcMember

theorem constructorSstoreSourceSite_coordinate
    {site : Prog.SourceSite}
    (member : site ∈ constructorSstoreSourceSites) :
    site.path.functionIndex = 4 ∧ site.pc = 137 := by
  have coordinateMember :
      (site.path.functionIndex, site.pc) ∈
        Prog.SourceSite.coordinates constructorSstoreSourceSites :=
    List.mem_map_of_mem member
  rw [constructorSstoreSourceSites_coordinates] at coordinateMember
  simpa using coordinateMember

theorem constructorStaticcallSourceSites_length :
    constructorStaticcallSourceSites.length = 1 :=
  constructorSourceSiteFacts.2.2.1

theorem constructorStaticcallSourceSites_pcs :
    Prog.SourceSite.pcs constructorStaticcallSourceSites = [98] :=
  constructorSourceSiteFacts.2.2.2.1

theorem constructorCodecopySourceSites_length :
    constructorCodecopySourceSites.length = 1 :=
  constructorSourceSiteFacts.2.2.2.2.1

theorem constructorCodecopySourceSites_pcs :
    Prog.SourceSite.pcs constructorCodecopySourceSites = [57] :=
  constructorSourceSiteFacts.2.2.2.2.2.1

theorem constructorExternalExecutionSourceSites_all_staticcall :
    (constructorExternalExecutionSourceSites.all fun site =>
      match site.instruction with
      | .exec .statcall => true
      | _ => false) = true :=
  constructorSourceSiteFacts.2.2.2.2.2.2.1

theorem constructorExternalExecutionSourceSites_length :
    constructorExternalExecutionSourceSites.length = 1 :=
  constructorSourceSiteFacts.2.2.2.2.2.2.2.1

theorem constructorExternalExecutionSourceSites_pcs :
    Prog.SourceSite.pcs constructorExternalExecutionSourceSites = [98] :=
  constructorSourceSiteFacts.2.2.2.2.2.2.2.2

theorem runtimeAndConstructorStaticcallSourceSites_length :
    runtimeAndConstructorStaticcallSourceSites.length = 12 := by
  simp [runtimeAndConstructorStaticcallSourceSites,
    runtimeStaticcallSourceSites_length,
    constructorStaticcallSourceSites_length]

end Blanc.BeaconDeposit
