import Blanc.CommonCore

/-!
Contract-neutral executable vocabulary for compiler-derived creation artifacts.

Runtime families commonly expose deployment parameters through one or more
fixed-width words while retaining the same compiler shape.  This module owns
the byte-difference, word-span validation, and patching operations used to turn
one parameter-neutral compiled member into a creation template.  Contract
families remain responsible for choosing marker worlds and interpreting each
generated word span.
-/

namespace Blanc

open Jaune

namespace CreationArtifact

/-- Byte indices at which two artifacts differ.  Unequal lengths are handled
fail-closed by also returning every unmatched tail index. -/
@[simp] def differingByteOffsets : Nat → Bytes → Bytes → List Nat
  | _, [], [] => []
  | i, [], _ :: ys => i :: differingByteOffsets (i + 1) [] ys
  | i, _ :: xs, [] => i :: differingByteOffsets (i + 1) xs []
  | i, x :: xs, y :: ys =>
      (if x = y then [] else [i]) ++ differingByteOffsets (i + 1) xs ys

/-- First index of every contiguous run in an ordered offset list. -/
def contiguousRunStarts (offsets : List Nat) : List Nat :=
  offsets.filter fun i => i = 0 || !(offsets.contains (i - 1))

/-- Expand word-start metadata to the byte indices it claims are mutable. -/
def wordByteOffsets (starts : List Nat) : List Nat :=
  starts.flatMap fun start => (List.range 32).map (start + ·)

/-- Compiler-derived starts of fixed-width words that differ between a
parameter-neutral template and a one-field marker artifact. -/
def immutableWordOffsets (template marker : Bytes) : List Nat :=
  contiguousRunStarts (differingByteOffsets 0 template marker)

/-- Fail-closed validation for generated immutable-word metadata: compiler
length must stay fixed and every changed byte must belong to one complete,
nonempty 32-byte word span. -/
def immutableWordOffsetsValid (template marker : Bytes) : Bool :=
  marker.length = template.length &&
    !(immutableWordOffsets template marker).isEmpty &&
    differingByteOffsets 0 template marker =
      wordByteOffsets (immutableWordOffsets template marker)

/-- Replace one 32-byte word beginning at `offset`.  Callers validate offsets
against compiler-derived metadata before treating the result as an artifact
identity. -/
def patchWord (code : Bytes) (offset : Nat) (value : B256) : Bytes :=
  code.take offset ++ value.toBytes ++ code.drop (offset + 32)

/-- Close a layout-parametric constructor program over the compiled
provisional prefix and the parameter-neutral runtime template.  Contract
families own the constructor body and artifacts; this helper owns only the
shared coordinate calculation. -/
def finalizedConstructorProgram
    (constructorProgram : Nat → Nat → Nat → Prog)
    (provisionalPrefix runtimeTemplate : Bytes) : Prog :=
  let prefixLength := provisionalPrefix.length
  constructorProgram prefixLength
    (prefixLength + runtimeTemplate.length) runtimeTemplate.length

end CreationArtifact
end Blanc
