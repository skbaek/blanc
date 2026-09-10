import Blanc.Forward

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

/-- Encode one exact EVM word with a fixed two-byte immediate when it fits,
falling back to the complete 32-byte immediate otherwise.  Unlike
`Ninst.pushB256`, the small branch retains leading zeroes and therefore has a
stable three-byte instruction width. -/
def pushB256AsPush2OrPush32 (word : B256) : Ninst :=
  let value := word.toNat
  if value < 2 ^ 16 then
    Ninst.push [(value >>> 8).toUInt8, value.toUInt8] (by simp)
  else
    Ninst.push word.toBytes (by rw [B256.length_toBytes])

end CreationArtifact

/-- Exact compiled semantics of the bounded constructor-word encoder.  Both
immediate widths cost `gVerylow`; the instruction preserves memory and pushes
the complete input word under the ordinary stack-room premise. -/
theorem Ninst.runCompiled_pushB256AsPush2OrPush32
    {sevm : Sevm} {devm : Devm} {word : B256} {G : Nat}
    (gas : devm.gasLeft = G + gVerylow)
    (room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm
      (CreationArtifact.pushB256AsPush2OrPush32 word)
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
    rw [CreationArtifact.pushB256AsPush2OrPush32, if_pos fit]
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
    rw [CreationArtifact.pushB256AsPush2OrPush32, if_neg fit]
    simpa only [B256.toB256_toBytes] using run

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

/-- Certificate witnessing that a layout-parametric constructor program achieves
a verified fixed point for its creation coordinates. -/
structure CreationCoordinatesCertificate
    (constructorProgram : Nat → Nat → Nat → Prog)
    (runtimeLength : Nat) where
  prefixLength : Nat
  provisionalBytes : Bytes
  finalBytes : Bytes
  provisional_compile : Prog.compile (constructorProgram 0 0 runtimeLength) = some provisionalBytes
  prefixLength_eq : prefixLength = provisionalBytes.length
  final_compile : Prog.compile (constructorProgram prefixLength (prefixLength + runtimeLength) runtimeLength) = some finalBytes
  fixed_point : finalBytes.length = prefixLength

namespace CreationCoordinatesCertificate

variable {constructorProgram : Nat → Nat → Nat → Prog} {runtimeLength : Nat}

/-- Final constructor program closed over the certified creation coordinates. -/
def finalProgram (cert : CreationCoordinatesCertificate constructorProgram runtimeLength) : Prog :=
  constructorProgram cert.prefixLength (cert.prefixLength + runtimeLength) runtimeLength

theorem finalProgram_compile (cert : CreationCoordinatesCertificate constructorProgram runtimeLength) :
    Prog.compile cert.finalProgram = some cert.finalBytes :=
  cert.final_compile

end CreationCoordinatesCertificate

/-- Checked adapter for two-pass constructor layout coordinates.
Compiles provisional `C 0 0 runtimeLength` to `b0`, sets `n = b0.length`,
compiles final `C n (n + runtimeLength) runtimeLength` to `b1`, and accepts
only when `b1.length = n`. Rejects compilation failure and coordinate width discrepancies. -/
def checkCreationCoordinates
    (constructorProgram : Nat → Nat → Nat → Prog)
    (runtimeLength : Nat) :
    Option (CreationCoordinatesCertificate constructorProgram runtimeLength) :=
  match h0 : Prog.compile (constructorProgram 0 0 runtimeLength) with
  | none => none
  | some b0 =>
    let n := b0.length
    match h1 : Prog.compile (constructorProgram n (n + runtimeLength) runtimeLength) with
    | none => none
    | some b1 =>
      if hfp : b1.length = n then
        some {
          prefixLength := n
          provisionalBytes := b0
          finalBytes := b1
          provisional_compile := h0
          prefixLength_eq := rfl
          final_compile := h1
          fixed_point := hfp
        }
      else
        none

/-- The executable adapter accepts whatever a certificate witnesses.

`checkCreationCoordinates` runs both compiler passes itself, and a
`CreationCoordinatesCertificate` records exactly that those two passes succeed
with the stated bytes and that the second has the provisional length.  Feeding
a certificate back in therefore shows the adapter reaches its accepting branch
on the same program.  This is the direction a contract family needs in order to
exercise the checker on a real constructor: the family already owns the two
compiler theorems, and this lemma turns them into a statement about the
executable checker without putting `Prog.compile` of a production-sized
constructor under a decision procedure. -/
theorem checkCreationCoordinates_isSome_of_cert
    {constructorProgram : Nat → Nat → Nat → Prog} {runtimeLength : Nat}
    (cert : CreationCoordinatesCertificate constructorProgram runtimeLength) :
    (checkCreationCoordinates constructorProgram runtimeLength).isSome = true := by
  have hlen : cert.provisionalBytes.length = cert.prefixLength :=
    cert.prefixLength_eq.symm
  unfold checkCreationCoordinates
  split
  · rename_i h0
    rw [cert.provisional_compile] at h0
    exact absurd h0 (by simp)
  · rename_i b0 h0
    rw [cert.provisional_compile] at h0
    have hb0 : b0 = cert.provisionalBytes := by
      injection h0 with h0; exact h0.symm
    subst hb0
    -- Zeta-reduce the checker's `let n := b0.length` so `split` can see the
    -- second match; `split` refuses to descend through the binder.
    simp only []
    split
    · rename_i h1
      rw [hlen, cert.final_compile] at h1
      exact absurd h1 (by simp)
    · rename_i b1 h1
      rw [hlen, cert.final_compile] at h1
      have hb1 : b1 = cert.finalBytes := by
        injection h1 with h1; exact h1.symm
      subst hb1
      split
      · rfl
      · rename_i hne
        exact absurd (cert.fixed_point.trans cert.prefixLength_eq) hne

/-! ## Negative controls for creation coordinates checking -/

/-- Negative control constructor: program fails compilation. -/
def failingCompileConstructorProgram (_r _a _l : Nat) : Prog :=
  ⟨.call 999, []⟩

/-- Negative control: compilation failure at provisional pass returns `none`. -/
theorem checkCreationCoordinates_failingCompile (l : Nat) :
    checkCreationCoordinates failingCompileConstructorProgram l = none :=
  rfl

/-- Negative control constructor: second pass changes instruction length. -/
def mismatchedLengthConstructorProgram : Nat → Nat → Nat → Prog
  | 0, _, _ => ⟨.last .stop, []⟩
  | _ + 1, _, _ => ⟨.next (Ninst.reg .pop) (.last .stop), []⟩

/-- Negative control: coordinate width discrepancy between passes returns `none`. -/
theorem checkCreationCoordinates_mismatchedLength (l : Nat) :
    checkCreationCoordinates mismatchedLengthConstructorProgram l = none :=
  rfl

end CreationArtifact

/-- Public alias for the creation coordinates certificate. -/
abbrev CreationCoordinatesCertificate := CreationArtifact.CreationCoordinatesCertificate

/-- Public alias for the creation coordinates checker. -/
abbrev checkCreationCoordinates := CreationArtifact.checkCreationCoordinates

/-- Public alias for the certificate-to-checker direction. -/
abbrev checkCreationCoordinates_isSome_of_cert :=
  @CreationArtifact.checkCreationCoordinates_isSome_of_cert

end Blanc
