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

end Blanc.Lift.UniswapV2Pair
