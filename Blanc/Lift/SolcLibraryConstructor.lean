import Blanc.Lift.Deploy
import Blanc.BytesWrite

/-! Source effects of Solidity's library constructor: copy a runtime template,
patch its call-protection address, and return the patched byte window. -/

namespace Blanc.Lift

open Jaune

/-- The address patch and terminal return used by Solidity library constructors. -/
def solcLibraryReturn : SFunc :=
  .dest (.next (.reg .address) (.next (.push [0x00] (by decide))
    (.next (.reg .mstore) (.next (.push [0x73] (by decide))
      (.next (.reg (.dup 1)) (.next (.reg .mstore8)
        (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.last .return_)))))))))

/-- The copied template is checked for a PUSH20 before the address patch. -/
def solcLibraryConstructor (sizeBytes offsetBytes : Bytes)
    (sizeBound : sizeBytes.length ≤ 32) (offsetBound : offsetBytes.length ≤ 32) : SFunc :=
  .next (.push sizeBytes sizeBound) (.next (.push offsetBytes offsetBound)
    (.next (.push [0x0b] (by decide)) (.next (.reg (.dup 2))
      (.next (.reg (.dup 2)) (.next (.reg (.dup 2)) (.next (.reg .codecopy)
        (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.push [0x00] (by decide))
          (.next (.reg .byte) (.next (.push [0x73] (by decide)) (.next (.reg .eq)
            (.next (.push [0x00, 0x19] (by decide))
              (.branch .undefined solcLibraryReturn))))))))))))))

/-- The return patch represented as ordered writes to an abstract byte image. -/
def solcLibraryPatchedImage (image : Bytes) (target : Adr) : Bytes :=
  Bytes.writeAt (Bytes.writeAt image 0 target.toB256.toBytes) 11 [0x73]

/-- A successful patch/return preserves storage and returns the patched image. -/
theorem solcLibraryReturn_effects
    {fs : List SFunc} {sevm : Sevm} {b post : Devm} {S : List B256}
    {M : Mem} {G : Nat} {size offset : B256} {image : Bytes}
    (wf : Mem.Wf M) (reads : Mem.Reads M image)
    (run : SFunc.Run fs sevm (St b (11 :: offset :: size :: S) M G)
      solcLibraryReturn (.halted post)) :
    post.getStor = b.getStor ∧
      post.output = (solcLibraryPatchedImage image sevm.currentTarget).sliceD 11 size.toNat 0 := by
  have run := run.cut
  unfold solcLibraryReturn at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_address step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mstore step
  have patched := reads.write wf 0 sevm.currentTarget.toB256.toBytes
  have patchedWf := wf.write 0 sevm.currentTarget.toB256.toBytes
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mstore8 step
  have finalReads := patched.write patchedWf 11 [0x73]
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 2) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
  cases run with
  | last terminal =>
      have effect := ri_return terminal
      exact ⟨funext effect.2.1, effect.1.trans (finalReads.read 11 size.toNat)⟩

/-- A successful complete library constructor returns the copied template with
its address patch. Initial memory stays symbolic throughout the proof. -/
theorem solcLibraryConstructor_effects
    {fs : List SFunc} {sevm : Sevm} {b post : Devm} {S : List B256}
    {M : Mem} {G : Nat} {image : Bytes}
    {sizeBytes offsetBytes : Bytes} {sizeBound : sizeBytes.length ≤ 32}
    {offsetBound : offsetBytes.length ≤ 32} {size offset : B256}
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (wf : Mem.Wf M) (reads : Mem.Reads M image)
    (run : SFunc.Run fs sevm (St b S M G)
      (solcLibraryConstructor sizeBytes offsetBytes sizeBound offsetBound) (.halted post)) :
    post.getStor = b.getStor ∧
      post.output = (solcLibraryPatchedImage
        (Bytes.writeAt image 11 (sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop)))
        sevm.currentTarget).sliceD 11 size.toNat 0 := by
  have run := run.cut
  unfold solcLibraryConstructor at run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, equal⟩ := ri_push step
  rw [sizeWord] at equal
  subst equal
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, equal⟩ := ri_push step
  rw [offsetWord] at equal
  subst equal
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 2) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 2) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 2) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_codecopy step
  let window := sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop)
  have copied := reads.write wf 11 window
  have copiedWf := wf.write 11 window
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mload step
  have loaded := copied.extend 11 32
  have loadedWf := copiedWf.extend 11 32
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_byte step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  rcases ric_branch run with ⟨_, _, impossible⟩ | ⟨_, _, returned⟩
  · cases impossible
  · exact solcLibraryReturn_effects loadedWf loaded returned.uncut

/-- The overlapping writes expose the PUSH20, twenty address bytes, and the
unchanged template tail. This equation never evaluates a concrete machine. -/
theorem solcLibraryPatchedImage_window (image template : Bytes) (target : Adr) (size : Nat)
    (minimum : 21 ≤ size) (fits : size ≤ template.length) :
    (solcLibraryPatchedImage (Bytes.writeAt image 11 template) target).sliceD 11 size 0 =
      [0x73] ++ target.toB256.toBytes.sliceD 12 20 0 ++ template.sliceD 21 (size - 21) 0 := by
  let patched := solcLibraryPatchedImage (Bytes.writeAt image 11 template) target
  have head : patched.sliceD 11 1 0 = [0x73] :=
    Bytes.sliceD_writeAt _ [0x73] 11
  have address : patched.sliceD 12 20 0 = target.toB256.toBytes.sliceD 12 20 0 := by
    dsimp only [patched, solcLibraryPatchedImage]
    rw [Bytes.sliceD_writeAt_after _ _ 12 20 11 (by decide),
      Bytes.sliceD_writeAt_inside _ _ 0 12 20 (by omega)
        (by rw [B256.length_toBytes])]
  have tail : patched.sliceD 32 (size - 21) 0 = template.sliceD 21 (size - 21) 0 := by
    dsimp only [patched, solcLibraryPatchedImage]
    rw [Bytes.sliceD_writeAt_after _ _ 32 (size - 21) 11 (by decide),
      Bytes.sliceD_writeAt_after _ _ 32 (size - 21) 0 (by rw [B256.length_toBytes]),
      Bytes.sliceD_writeAt_inside _ _ 11 32 (size - 21) (by omega) (by omega)]
  change patched.sliceD 11 size 0 = _
  calc
    patched.sliceD 11 size 0 = patched.sliceD 11 (21 + (size - 21)) 0 := by
      congr 1
      omega
    _ = patched.sliceD 11 21 0 ++ patched.sliceD 32 (size - 21) 0 :=
      List.sliceD_add patched 0 21 11 (size - 21)
    _ = (patched.sliceD 11 1 0 ++ patched.sliceD 12 20 0) ++
        patched.sliceD 32 (size - 21) 0 := by
      rw [List.sliceD_add patched 0 1 11 20]
    _ = _ := by rw [head, address, tail]

end Blanc.Lift
