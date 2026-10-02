import Blanc.Lift.UniswapV2Pair.UpdateWalk
import Blanc.ConcreteRun

/-! Affordable execution of the certified uint112 overflow failure. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def overflowSelector : B256 := (0x08c379a0 * 2 ^ 224 : Nat).toB256
def overflowText : B256 := (0x556e697377617056323a204f564552464c4f57 * 2 ^ 104 : Nat).toB256

def overflowMemory (M : Mem) : Mem :=
  (((M.write 128 overflowSelector.toBytes).write 132 (32 : B256).toBytes).write
    164 (19 : B256).toBytes).write 196 overflowText.toBytes

def overflowPayload : Bytes :=
  [0x08, 0xc3, 0x79, 0xa0] ++ (32 : B256).toBytes ++ (19 : B256).toBytes ++
    overflowText.toBytes

theorem overflowMemory_ptr {M : Mem} (mem : PtrMem 128 256 M) :
    PtrMem 128 256 (overflowMemory M) := by
  exact (((mem.write 128 overflowSelector (Or.inr (by decide))).write 132 32
    (Or.inr (by decide))).write 164 19 (Or.inr (by decide))).write
      196 overflowText (Or.inr (by decide))

def overflowFailureBody : Func := (.next (.push [0x40] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.push [0x08, 0xc3, 0x79, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.push [0x04] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .mstore) (.next (.push [0x13] (by decide)) (.next (.push [0x24] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .mstore) (.next (.push [0x55, 0x6e, 0x69, 0x73, 0x77, 0x61, 0x70, 0x56, 0x32, 0x3a, 0x20, 0x4f, 0x56, 0x45, 0x52, 0x46, 0x4c, 0x4f, 0x57, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.push [0x44] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .mstore) (.next (.reg (.swap 0)) (.next (.reg .mload) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg (.swap 0)) (.next (.reg .sub) (.next (.push [0x64] (by decide)) (.next (.reg .add) (.next (.reg (.swap 0)) (.last .revert)))))))))))))))))))))))))))))))





theorem overflowFailureBody_subcode :
    subcode code.toList 0x2311 (Func.compile [] 0x2311 overflowFailureBody) := by
  change List.Slice code.toList 0x2311 _
  refine ⟨102, ?_⟩
  kernel_rfl

theorem overflowFailureBody_noCalls : overflowFailureBody.NoCalls := by
  repeat constructor

theorem overflowFailureBody_run {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G : Nat} {out : Bytes} {failed : Devm}
    (mem : PtrMem 128 256 M) (room : S.length ≤ 1019)
    (read : (St b S (overflowMemory M) G).memRead 128 100 = (out, failed)) :
    Func.RunCompiledTo [] sevm (St b S M (G + 90)) overflowFailureBody
      (.error (.revert, failed.withOutput out)) := by
  let M1 := M.write 128 overflowSelector.toBytes
  let M2 := M1.write 132 (32 : B256).toBytes
  let M3 := M2.write 164 (19 : B256).toBytes
  let M4 := M3.write 196 overflowText.toBytes
  have m1 : PtrMem 128 256 M1 := mem.write 128 overflowSelector (Or.inr (by decide))
  have m2 : PtrMem 128 256 M2 := m1.write 132 32 (Or.inr (by decide))
  have m3 : PtrMem 128 256 M3 := m2.write 164 19 (Or.inr (by decide))
  have m4 : PtrMem 128 256 M4 := m3.write 196 overflowText (Or.inr (by decide))
  unfold overflowFailureBody
  refine .next (Ninst.runCompiled_pushBytes (G := G + 87) rfl rfl (by change S.length + 0 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (64 :: S) M (G + 87)) _ _
  refine .next (Ninst.runCompiled_dup (G := G + 84) rfl rfl (by change S.length + 1 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (64 :: 64 :: S) M (G + 84)) _ _
  refine .next (Ninst.runCompiled_mload_of (G := G + 81) (c := 3) (v := 128) (M := M) rfl ?_ mem.word (mem.read_self (by decide)) rfl (by change S.length + 1 < 1024; omega)) ?_
  · change 3 + (St b (64 :: 64 :: S) M (G + 84)).extCost [(64, 32)] = 3
    rw [St.extCost_eq mem.size]; rfl
  change Func.RunCompiledTo [] sevm (St b (128 :: 64 :: S) M (G + 81)) _ _
  refine .next (Ninst.runCompiled_pushBytes (G := G + 78) rfl rfl (by change S.length + 2 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (overflowSelector :: 128 :: 64 :: S) M (G + 78)) _ _
  refine .next (Ninst.runCompiled_dup (G := G + 75) rfl rfl (by change S.length + 3 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (128 :: overflowSelector :: 128 :: 64 :: S) M (G + 75)) _ _
  refine .next (Ninst.runCompiled_mstore_of (G := G + 72) (e := 0) (M := M1) rfl ?_ rfl rfl) ?_
  · change (St b (128 :: overflowSelector :: 128 :: 64 :: S) M (G + 75)).extCost [(128, 32)] = 0
    rw [St.extCost_eq mem.size]; rfl
  change Func.RunCompiledTo [] sevm (St b (128 :: 64 :: S) M1 (G + 72)) _ _
  refine .next (Ninst.runCompiled_pushBytes (G := G + 69) rfl rfl (by change S.length + 2 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (32 :: 128 :: 64 :: S) M1 (G + 69)) _ _
  refine .next (Ninst.runCompiled_pushBytes (G := G + 66) rfl rfl (by change S.length + 3 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (4 :: 32 :: 128 :: 64 :: S) M1 (G + 66)) _ _
  refine .next (Ninst.runCompiled_dup (G := G + 63) rfl rfl (by change S.length + 4 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (128 :: 4 :: 32 :: 128 :: 64 :: S) M1 (G + 63)) _ _
  refine .next (Ninst.runCompiled_binary (G := G + 60) (v := 132) (by rintro ⟨⟩) rfl rfl (by decide) rfl (by change S.length + 3 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (132 :: 32 :: 128 :: 64 :: S) M1 (G + 60)) _ _
  refine .next (Ninst.runCompiled_mstore_of (G := G + 57) (e := 0) (M := M2) rfl ?_ rfl rfl) ?_
  · change (St b (132 :: 32 :: 128 :: 64 :: S) M1 (G + 60)).extCost [(132, 32)] = 0
    rw [St.extCost_eq m1.size]; rfl
  change Func.RunCompiledTo [] sevm (St b (128 :: 64 :: S) M2 (G + 57)) _ _
  refine .next (Ninst.runCompiled_pushBytes (G := G + 54) rfl rfl (by change S.length + 2 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (19 :: 128 :: 64 :: S) M2 (G + 54)) _ _
  refine .next (Ninst.runCompiled_pushBytes (G := G + 51) rfl rfl (by change S.length + 3 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (36 :: 19 :: 128 :: 64 :: S) M2 (G + 51)) _ _
  refine .next (Ninst.runCompiled_dup (G := G + 48) rfl rfl (by change S.length + 4 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (128 :: 36 :: 19 :: 128 :: 64 :: S) M2 (G + 48)) _ _
  refine .next (Ninst.runCompiled_binary (G := G + 45) (v := 164) (by rintro ⟨⟩) rfl rfl (by decide) rfl (by change S.length + 3 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (164 :: 19 :: 128 :: 64 :: S) M2 (G + 45)) _ _
  refine .next (Ninst.runCompiled_mstore_of (G := G + 42) (e := 0) (M := M3) rfl ?_ rfl rfl) ?_
  · change (St b (164 :: 19 :: 128 :: 64 :: S) M2 (G + 45)).extCost [(164, 32)] = 0
    rw [St.extCost_eq m2.size]; rfl
  change Func.RunCompiledTo [] sevm (St b (128 :: 64 :: S) M3 (G + 42)) _ _
  refine .next (Ninst.runCompiled_pushBytes (G := G + 39) rfl rfl (by change S.length + 2 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (overflowText :: 128 :: 64 :: S) M3 (G + 39)) _ _
  refine .next (Ninst.runCompiled_pushBytes (G := G + 36) rfl rfl (by change S.length + 3 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (68 :: overflowText :: 128 :: 64 :: S) M3 (G + 36)) _ _
  refine .next (Ninst.runCompiled_dup (G := G + 33) rfl rfl (by change S.length + 4 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (128 :: 68 :: overflowText :: 128 :: 64 :: S) M3 (G + 33)) _ _
  refine .next (Ninst.runCompiled_binary (G := G + 30) (v := 196) (by rintro ⟨⟩) rfl rfl (by decide) rfl (by change S.length + 3 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (196 :: overflowText :: 128 :: 64 :: S) M3 (G + 30)) _ _
  refine .next (Ninst.runCompiled_mstore_of (G := G + 27) (e := 0) (M := M4) rfl ?_ rfl rfl) ?_
  · change (St b (196 :: overflowText :: 128 :: 64 :: S) M3 (G + 30)).extCost [(196, 32)] = 0
    rw [St.extCost_eq m3.size]; rfl
  change Func.RunCompiledTo [] sevm (St b (128 :: 64 :: S) M4 (G + 27)) _ _
  refine .next (Ninst.runCompiled_swap (G := G + 24) rfl rfl) ?_
  change Func.RunCompiledTo [] sevm (St b (64 :: 128 :: S) M4 (G + 24)) _ _
  refine .next (Ninst.runCompiled_mload_of (G := G + 21) (c := 3) (v := 128) (M := M4) rfl ?_ m4.word (m4.read_self (by decide)) rfl (by change S.length + 1 < 1024; omega)) ?_
  · change 3 + (St b (64 :: 128 :: S) M4 (G + 24)).extCost [(64, 32)] = 3
    rw [St.extCost_eq m4.size]; rfl
  change Func.RunCompiledTo [] sevm (St b (128 :: 128 :: S) M4 (G + 21)) _ _
  refine .next (Ninst.runCompiled_swap (G := G + 18) rfl rfl) ?_
  change Func.RunCompiledTo [] sevm (St b (128 :: 128 :: S) M4 (G + 18)) _ _
  refine .next (Ninst.runCompiled_dup (G := G + 15) rfl rfl (by change S.length + 2 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (128 :: 128 :: 128 :: S) M4 (G + 15)) _ _
  refine .next (Ninst.runCompiled_swap (G := G + 12) rfl rfl) ?_
  change Func.RunCompiledTo [] sevm (St b (128 :: 128 :: 128 :: S) M4 (G + 12)) _ _
  refine .next (Ninst.runCompiled_binary (G := G + 9) (v := 0) (by rintro ⟨⟩) rfl rfl (by decide) rfl (by change S.length + 1 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (0 :: 128 :: S) M4 (G + 9)) _ _
  refine .next (Ninst.runCompiled_pushBytes (G := G + 6) rfl rfl (by change S.length + 2 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (100 :: 0 :: 128 :: S) M4 (G + 6)) _ _
  refine .next (Ninst.runCompiled_binary (G := G + 3) (v := 100) (by rintro ⟨⟩) rfl rfl (by decide) rfl (by change S.length + 1 < 1024; omega)) ?_
  change Func.RunCompiledTo [] sevm (St b (100 :: 128 :: S) M4 (G + 3)) _ _
  refine .next (Ninst.runCompiled_swap (G := G) rfl rfl) ?_
  change Func.RunCompiledTo [] sevm (St b (128 :: 100 :: S) M4 (G + 0)) _ _
  refine Func.runCompiledTo_revert_of (i := 128) (sz := 100) (G := G) (e := 0)
    rfl ?_ rfl read
  rw [St.extCost_eq m4.size]; rfl


def overflowImage (M : Mem) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt M.data.toList
    128 overflowSelector.toBytes) 132 (32 : B256).toBytes) 164 (19 : B256).toBytes)
      196 overflowText.toBytes

theorem overflowImage_read (M : Mem) :
    (overflowImage M).sliceD 128 100 0 = overflowPayload := by
  have selector : (overflowImage M).sliceD 128 4 0 = [8, 195, 121, 160] := by
    unfold overflowImage
    rw [Bytes.sliceD_writeAt_before _ _ 128 4 196 (by decide),
      Bytes.sliceD_writeAt_before _ _ 128 4 164 (by decide),
      Bytes.sliceD_writeAt_before _ _ 128 4 132 (by decide),
      Bytes.sliceD_writeAt_inside _ _ 128 128 4 (by decide)
        (by rw [B256.length_toBytes]; decide)]
    decide +kernel
  have offset : (overflowImage M).sliceD 132 32 0 = (32 : B256).toBytes := by
    unfold overflowImage
    rw [Bytes.sliceD_writeAt_before _ _ 132 32 196 (by decide),
      Bytes.sliceD_writeAt_before _ _ 132 32 164 (by decide),
      ← B256.length_toBytes (32 : B256), Bytes.sliceD_writeAt]
  have length : (overflowImage M).sliceD 164 32 0 = (19 : B256).toBytes := by
    unfold overflowImage
    rw [Bytes.sliceD_writeAt_before _ _ 164 32 196 (by decide),
      ← B256.length_toBytes (19 : B256), Bytes.sliceD_writeAt]
  have text : (overflowImage M).sliceD 196 32 0 = overflowText.toBytes := by
    unfold overflowImage
    rw [← B256.length_toBytes overflowText, Bytes.sliceD_writeAt]
  rw [show (100 : Nat) = 4 + (32 + (32 + 32)) from rfl, List.sliceD_split,
    List.sliceD_split, List.sliceD_split, selector, offset, length, text]
  rfl

theorem overflowMemory_read {M : Mem} (wf : Mem.Wf M) :
    ((overflowMemory M).read 128 100).1 = overflowPayload := by
  have first := Mem.Reads.write wf (Mem.reads_data M) 128 overflowSelector.toBytes
  have second := Mem.Reads.write (wf.write 128 overflowSelector.toBytes) first
    132 (32 : B256).toBytes
  have third := Mem.Reads.write ((wf.write 128 overflowSelector.toBytes).write
    132 (32 : B256).toBytes) second 164 (19 : B256).toBytes
  have fourth := Mem.Reads.write (((wf.write 128 overflowSelector.toBytes).write
    132 (32 : B256).toBytes).write 164 (19 : B256).toBytes) third 196 overflowText.toBytes
  change Mem.Reads (overflowMemory M) (overflowImage M) at fourth
  rw [fourth.read]
  exact overflowImage_read M

theorem overflowRead {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (mem : PtrMem 128 256 M) :
    (St b S (overflowMemory M) G).memRead 128 100 =
      (overflowPayload, St b S (overflowMemory M) G) := by
  have kept := (overflowMemory_ptr mem).read_self (i := 128) (sz := 100) (by decide)
  have bytes := overflowMemory_read mem.wf
  unfold Devm.memRead
  rw [show (St b S (overflowMemory M) G).memory = overflowMemory M from rfl]
  have readEq : (overflowMemory M).read 128 100 = (overflowPayload, overflowMemory M) :=
    Prod.ext bytes kept
  rw [readEq]
  rfl

theorem overflowFailureBody_boundary : noPushBefore code 0x2311 32 = true := by
  kernel_rfl

theorem overflowFailure_exec {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G : Nat} (codeEq : sevm.code = code)
    (mem : PtrMem 128 256 M) (room : S.length ≤ 1019) :
    Nonempty (Exec 0x2311 sevm (St b S M (G + 90))
      (.error (.revert, (St b S (overflowMemory M) G).withOutput overflowPayload))) := by
  exact Func.exec_of_runCompiledTo_subcode
    (overflowFailureBody_run mem room (overflowRead mem)) overflowFailureBody_noCalls
    0x2311 (by rw [codeEq]; exact overflowFailureBody_subcode)
      (by rw [codeEq]; exact overflowFailureBody_boundary)


private theorem overflowGuardFact0 : Jinst.At code 0x22e0 .jumpdest := by
  unfold Jinst.At
  kernel_rfl

private theorem overflowGuardFact1 : Ninst.At code 0x22e1 (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) := by
  unfold Ninst.At
  kernel_rfl

private theorem overflowGuardFact2 : Ninst.At code 0x22f0 (.reg (.dup 4)) := by
  unfold Ninst.At
  kernel_rfl

private theorem overflowGuardFact3 : Ninst.At code 0x22f1 (.reg .gt) := by
  unfold Ninst.At
  kernel_rfl

private theorem overflowGuardFact4 : Ninst.At code 0x22f2 (.reg (.dup 0)) := by
  unfold Ninst.At
  kernel_rfl

private theorem overflowGuardFact5 : Ninst.At code 0x22f3 (.reg .iszero) := by
  unfold Ninst.At
  kernel_rfl

private theorem overflowGuardFact6 : Ninst.At code 0x22f4 (.reg (.swap 0)) := by
  unfold Ninst.At
  kernel_rfl

private theorem overflowGuardFact7 : Ninst.At code 0x22f5 (.push [0x23, 0x0c] (by decide)) := by
  unfold Ninst.At
  kernel_rfl

private theorem overflowGuardFact8 : Jinst.At code 0x22f8 .jumpi := by
  unfold Jinst.At
  kernel_rfl

private theorem overflowGuardFact9 : Jinst.At code 0x230c .jumpdest := by
  unfold Jinst.At
  kernel_rfl

private theorem overflowGuardFact10 : Ninst.At code 0x230d (.push [0x23, 0x77] (by decide)) := by
  unfold Ninst.At
  kernel_rfl

private theorem overflowGuardFact11 : Jinst.At code 0x2310 .jumpi := by
  unfold Jinst.At
  kernel_rfl

private theorem overflowGuardFact12 : jumpable code 0x230c = true := by
  kernel_rfl


/-- The intended uint112 guard rejects the mathematical input 2^112,
with an affordable operational failure and its exact ABI error message. -/
theorem update_overflow_exec {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {r0 r1 balance1 tag : B256} (codeEq : sevm.code = code)
    (mem : PtrMem 128 256 M) (room : R.length ≤ 1014) :
    Nonempty (Exec 0x22e0 sevm
      (St b (r1 :: r0 :: balance1 :: (2 ^ 112 : Nat).toB256 :: tag :: R) M (G + 136))
      (.error (.revert,
        (St b (r1 :: r0 :: balance1 :: (2 ^ 112 : Nat).toB256 :: tag :: R)
          (overflowMemory M) G).withOutput overflowPayload))) := by
  let S := r1 :: r0 :: balance1 :: (2 ^ 112 : Nat).toB256 :: tag :: R
  have a0 := overflowGuardFact0
  have a1 := overflowGuardFact1
  have a2 := overflowGuardFact2
  have a3 := overflowGuardFact3
  have a4 := overflowGuardFact4
  have a5 := overflowGuardFact5
  have a6 := overflowGuardFact6
  have a7 := overflowGuardFact7
  have a8 := overflowGuardFact8
  have a9 := overflowGuardFact9
  have a10 := overflowGuardFact10
  have a11 := overflowGuardFact11
  have jp := overflowGuardFact12
  rw [← codeEq] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 jp
  have d0 : Evm.step ⟨0x22e0, sevm, St b S M (G + 136)⟩ =
      .cont 0x22e1 (St b S M (G + 135)) :=
    Evm.jumpdest_cont a0 (Devm.burnBy_setMach_gas rfl)
  have n1 : Ninst.RunCompiled sevm (St b (S) M (G + 135))
      (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (St b (reserveMask112 :: S) M (G + 132)) := by
    exact Ninst.runCompiled_pushBytes (G := G + 132) rfl rfl
      (by change R.length + 5 < 1024; omega)
  have n2 : Ninst.RunCompiled sevm (St b (reserveMask112 :: S) M (G + 132))
      (.reg (.dup 4)) (St b ((2 ^ 112 : Nat).toB256 :: reserveMask112 :: S) M (G + 129)) := by
    exact Ninst.runCompiled_dup (G := G + 129) rfl rfl
      (by change R.length + 6 < 1024; omega)
  have n3 : Ninst.RunCompiled sevm (St b ((2 ^ 112 : Nat).toB256 :: reserveMask112 :: S) M (G + 129))
      (.reg .gt) (St b (1 :: S) M (G + 126)) := by
    exact Ninst.runCompiled_binary (G := G + 126) (v := 1)
      (by rintro ⟨⟩) rfl rfl (by decide) rfl
      (by change R.length + 5 < 1024; omega)
  have n4 : Ninst.RunCompiled sevm (St b (1 :: S) M (G + 126))
      (.reg (.dup 0)) (St b (1 :: 1 :: S) M (G + 123)) := by
    exact Ninst.runCompiled_dup (G := G + 123) rfl rfl
      (by change R.length + 6 < 1024; omega)
  have n5 : Ninst.RunCompiled sevm (St b (1 :: 1 :: S) M (G + 123))
      (.reg .iszero) (St b (0 :: 1 :: S) M (G + 120)) := by
    exact Ninst.runCompiled_unary (G := G + 120) (v := 0)
      (by rintro ⟨⟩) rfl rfl (by decide) rfl
      (by change R.length + 6 < 1024; omega)
  have n6 : Ninst.RunCompiled sevm (St b (0 :: 1 :: S) M (G + 120))
      (.reg (.swap 0)) (St b (1 :: 0 :: S) M (G + 117)) := by
    exact Ninst.runCompiled_swap (G := G + 117) rfl rfl
  have n7 : Ninst.RunCompiled sevm (St b (1 :: 0 :: S) M (G + 117))
      (.push [0x23, 0x0c] (by decide)) (St b (0x230c :: 1 :: 0 :: S) M (G + 114)) := by
    exact Ninst.runCompiled_pushBytes (G := G + 114) rfl rfl
      (by change R.length + 7 < 1024; omega)
  have j1 := Evm.jumpi_cont_jump (devm := St b (0x230c :: 1 :: 0 :: S) M (G + 114))
    a8 rfl (by decide : (1 : B256) ≠ 0) (by change 10 ≤ G + 114; omega) jp
  change Evm.step ⟨0x22f8, sevm, St b (0x230c :: 1 :: 0 :: S) M (G + 114)⟩ =
    .cont 0x230c (St b (0 :: S) M (G + 114 - 10)) at j1
  rw [show G + 114 - 10 = G + 104 from by omega] at j1
  have d1 : Evm.step ⟨0x230c, sevm, St b (0 :: S) M (G + 104)⟩ =
      .cont 0x230d (St b (0 :: S) M (G + 103)) :=
    Evm.jumpdest_cont a9 (Devm.burnBy_setMach_gas rfl)
  have n8 : Ninst.RunCompiled sevm (St b (0 :: S) M (G + 103))
      (.push [0x23, 0x77] (by decide))
        (St b (0x2377 :: 0 :: S) M (G + 100)) :=
    Ninst.runCompiled_pushBytes rfl rfl (by change R.length + 6 < 1024; omega)
  have j2 := Evm.jumpi_cont_zero (devm := St b (0x2377 :: 0 :: S) M (G + 100))
    a11 rfl (by change 10 ≤ G + 100; omega)
  change Evm.step ⟨0x2310, sevm, St b (0x2377 :: 0 :: S) M (G + 100)⟩ =
    .cont 0x2311 (St b S M (G + 100 - 10)) at j2
  rw [show G + 100 - 10 = G + 90 from by omega] at j2
  have rest := overflowFailure_exec (b := b) (S := S) (G := G) codeEq mem
    (by change R.length + 5 ≤ 1019; omega)
  have e11 : Nonempty (Exec 0x2310 sevm (St b (0x2377 :: 0 :: S) M (G + 100))
      (.error (.revert, (St b S (overflowMemory M) G).withOutput overflowPayload))) :=
    rest.elim (fun e => ⟨Exec.cont j2 e⟩)
  rcases n8 with ⟨xl8, hf8, hn8⟩
  have e10 := Ninst.exec_of_stepRun a10 hf8 (hn8 0x230d) e11
  have e9 := Nonempty.map (Exec.cont d1) e10
  have e8 := Nonempty.map (Exec.cont j1) e9
  rcases n7 with ⟨xl7, hf7, hn7⟩
  have e7 := Ninst.exec_of_stepRun a7 hf7 (hn7 0x22f5) e8
  rcases n6 with ⟨xl6, hf6, hn6⟩
  have e6 := Ninst.exec_of_stepRun a6 hf6 (hn6 0x22f4) e7
  rcases n5 with ⟨xl5, hf5, hn5⟩
  have e5 := Ninst.exec_of_stepRun a5 hf5 (hn5 0x22f3) e6
  rcases n4 with ⟨xl4, hf4, hn4⟩
  have e4 := Ninst.exec_of_stepRun a4 hf4 (hn4 0x22f2) e5
  rcases n3 with ⟨xl3, hf3, hn3⟩
  have e3 := Ninst.exec_of_stepRun a3 hf3 (hn3 0x22f1) e4
  rcases n2 with ⟨xl2, hf2, hn2⟩
  have e2 := Ninst.exec_of_stepRun a2 hf2 (hn2 0x22f0) e3
  rcases n1 with ⟨xl1, hf1, hn1⟩
  have e1 := Ninst.exec_of_stepRun a1 hf1 (hn1 0x22e1) e2
  exact e1.elim (fun e => ⟨Exec.cont d0 e⟩)


def overflowControlMemory : Mem :=
  (Mem.empty.write 64 (128 : B256).toBytes).write 224 (0 : B256).toBytes

theorem overflowControlMemory_ptr : PtrMem 128 256 overflowControlMemory := by
  exact (PtrMem.init 128).write 224 0 (Or.inr (by decide))

def overflowControlSevm : Sevm := { (default : Sevm) with code := code }

def overflowControlStack : List B256 := [0, 0, 0, (2 ^ 112 : Nat).toB256, 0]

def overflowControlBefore : Devm := St default overflowControlStack overflowControlMemory 136

def overflowControlFailed : Devm :=
  (St default overflowControlStack (overflowMemory overflowControlMemory) 0).withOutput
    overflowPayload


private theorem overflowControlMemoryEq :
    overflowControlFailed.memory = overflowMemory overflowControlMemory := by
  kernel_rfl

private theorem overflowControlLogsEq :
    overflowControlFailed.logs = overflowControlBefore.logs := by
  kernel_rfl

private theorem overflowControlAcctEq :
    overflowControlFailed.getAcct = overflowControlBefore.getAcct := by
  kernel_rfl

private theorem overflowControlStorageEq :
    Devm.getStor overflowControlFailed = Devm.getStor overflowControlBefore := by
  kernel_rfl

/-- A bounded kernel-checked statement control, consumed from the symbolic
operational theorem rather than from a finite interpreter comparison. -/
theorem update_overflow_uint112_kernel_control :
    Nonempty (Exec 0x22e0 overflowControlSevm overflowControlBefore
      (.error (.revert, overflowControlFailed))) ∧
    (2 ^ 112 : Nat).toB256.toNat = 2 ^ 112 ∧
    ¬ (2 ^ 112 : Nat).toB256.toNat < 2 ^ 112 ∧
    overflowControlBefore.gasLeft = 136 ∧
    overflowControlFailed.gasLeft = 0 ∧
    overflowControlFailed.stack = overflowControlStack ∧
    overflowControlFailed.memory = overflowMemory overflowControlMemory ∧
    overflowControlFailed.output = overflowPayload ∧
    overflowControlFailed.logs = overflowControlBefore.logs ∧
    (∀ a, overflowControlFailed.getAcct a = overflowControlBefore.getAcct a) ∧
    (∀ a, Devm.getStor overflowControlFailed a = Devm.getStor overflowControlBefore a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact update_overflow_exec (sevm := overflowControlSevm) (b := default) (R := []) (G := 0)
      (r0 := 0) (r1 := 0) (balance1 := 0) (tag := 0) rfl overflowControlMemory_ptr (by decide)
  · decide
  · decide
  · rfl
  · rfl
  · rfl
  · exact overflowControlMemoryEq
  · rfl
  · exact overflowControlLogsEq
  · intro a; exact congrFun overflowControlAcctEq a
  · intro a; exact congrFun overflowControlStorageEq a

end Blanc.Lift.UniswapV2Pair
