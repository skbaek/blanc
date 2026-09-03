-- DripDeploy.lean : no-argument DRIP constructor and creation artifact.

import Blanc.CreationArtifact
import Blanc.DripCode

/-!
# DRIP deployment source

The nonpayable constructor accepts no appended argument bytes, initializes
`chi` before `rho`, and returns the exact compiler-generated DRIP runtime.
Full-width creation coordinates make the provisional and final compiler passes
shape-identical without truncating a future artifact that outgrows PUSH2.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Drip

/-- Full-width creation coordinates keep both compiler passes shape-identical. -/
def pushCreationCoordinate (value : Nat) : Ninst :=
  Ninst.push (Nat.toB256 value).toBytes (by rw [B256.length_toBytes])

/-- Strict no-argument body: initialize the two scalar words in frozen order,
copy the appended runtime, and return precisely that memory window. -/
def constructorBody
    (runtimeOffset argsOffset runtimeLength : Nat) : Func :=
  pushCreationCoordinate argsOffset ::: codesize ::: eq :::
  ((pushB256 scale ::: pushB256 chiSlot ::: sstore :::
      timestamp ::: pushB256 rhoSlot ::: sstore :::
      pushCreationCoordinate runtimeLength :::
      pushCreationCoordinate runtimeOffset :::
      pushB256 0 ::: codecopy :::
      pushCreationCoordinate runtimeLength :::
      pushB256 0 ::: Func.return_) <?>
    Func.revert)

/-- Layout-parametric constructor used for the provisional and final passes. -/
def constructorProgramAt
    (runtimeOffset argsOffset runtimeLength : Nat) : Prog :=
  { main := nonpayable
      (constructorBody runtimeOffset argsOffset runtimeLength)
    aux := [] }

private def provisionalConstructorPrefix : Bytes :=
  (Prog.compile (constructorProgramAt 0 0 code.length)).getD []

/-- Compiler-derived byte offset of the appended runtime. -/
def constructorRuntimeOffset : Nat :=
  provisionalConstructorPrefix.length

/-- Exact constructor source closed over the compiler-derived layout. -/
def constructorProgram : Prog :=
  CreationArtifact.finalizedConstructorProgram constructorProgramAt
    provisionalConstructorPrefix code

/-- Exact compiled constructor prefix. -/
def constructorInitPrefix : Bytes :=
  (Prog.compile constructorProgram).getD []

/-- Exact DRIP creation bytes: compiled prefix followed by the runtime literal. -/
def creationCode : Bytes :=
  constructorInitPrefix ++ code

def constructorCreationCode : Bytes := creationCode

def creationCodeSize : Nat := creationCode.length

def eip3860InitcodeLimit : Nat := pragueCodeLimits.maxInitCodeSize

def creationCodeHeadroom : Nat := eip3860InitcodeLimit - creationCodeSize

theorem constructorProgram_eq :
    constructorProgram =
      constructorProgramAt constructorRuntimeOffset
        (constructorRuntimeOffset + code.length) code.length := by
  simp only [constructorProgram,
    CreationArtifact.finalizedConstructorProgram, constructorRuntimeOffset]

theorem constructorProgram_compiles :
    Prog.compiles constructorProgram = true := by
  decide +kernel

theorem constructorInitPrefix_compile :
    Prog.compile constructorProgram = some constructorInitPrefix := by
  unfold constructorInitPrefix
  exact Prog.compile_eq_some_getD_of_compiles _ constructorProgram_compiles

/-- Fixed-width layout operands make the second-pass prefix a true fixed point. -/
theorem constructorInitPrefix_length_eq_runtimeOffset :
    constructorInitPrefix.length = constructorRuntimeOffset := by
  decide +kernel

theorem constructorRuntimeOffset_exact : constructorRuntimeOffset = 239 := by
  decide +kernel

theorem creationCode_eq_prefix_append_runtime :
    creationCode = constructorInitPrefix ++ code := by
  rfl

theorem constructorCreationCode_eq_creationCode :
    constructorCreationCode = creationCode := by
  rfl

theorem creationCode_drop_prefix :
    creationCode.drop constructorInitPrefix.length = code := by
  simp [creationCode]

theorem creationCode_drop_runtimeOffset :
    creationCode.drop constructorRuntimeOffset = code := by
  rw [← constructorInitPrefix_length_eq_runtimeOffset]
  exact creationCode_drop_prefix

/-- The constructor's CODECOPY window is exactly the appended runtime. -/
theorem creationCode_slice_runtime :
    creationCode.sliceD constructorRuntimeOffset codeSize 0 = code := by
  rw [← constructorInitPrefix_length_eq_runtimeOffset]
  unfold creationCode List.sliceD
  rw [List.drop_length_append' rfl]
  change List.takeD code.length code 0 = code
  rw [List.takeD_eq_take _ (by simp)]
  exact List.take_length

theorem eip3860InitcodeLimit_exact : eip3860InitcodeLimit = 49152 := by
  rfl

theorem creationCodeSize_exact : creationCodeSize = 2156 := by
  decide +kernel

theorem creationCode_eip3860 :
    creationCodeSize <= eip3860InitcodeLimit := by
  rw [creationCodeSize_exact, eip3860InitcodeLimit_exact]
  decide

theorem creationCodeHeadroom_exact : creationCodeHeadroom = 46996 := by
  unfold creationCodeHeadroom
  rw [eip3860InitcodeLimit_exact, creationCodeSize_exact]

end Drip
end Blanc
