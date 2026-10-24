import Blanc.AddressSlotProofs
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorOccurrence
import Blanc.Lift.CursorQuietReturn
import Blanc.Lift.Ecrecover
import Blanc.Lift.InvWalkGas
import Blanc.Lift.InvWalkOps
import Blanc.Lift.WordImage
import Blanc.Lift.WalkSteps
import Blanc.Lift.RunPWalk

import Blanc.Lift.CursorBalanceReply
import Blanc.Lift.HistCursorReturn
import Blanc.Lift.HistEcrecover
import Blanc.Lift.CursorReturnToward
import Blanc.Lift.CursorCutsToward

/-! One actual recovery request and return-consumption engine for checked source layouts. -/

namespace Blanc.Lift.EcrecoverCall

open Jaune Blanc Blanc.Lift

/-- The two branch literals and rejected source subtrees of this calling convention. -/
structure ReturnLayout where
  answerDestination : Bytes
  answerLe : answerDestination.length ≤ 32
  nonzeroDestination : Bytes
  nonzeroLe : nonzeroDestination.length ≤ 32
  failure : SFunc
  zeroFailure : SFunc

private def cleanup : SFunc := (.dest (.next (.reg (.swap 4)) (.next (.reg (.swap 3)) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) .ret)))))))

private def finish : SFunc := (.dest (.next (.reg (.swap 0)) (.next (.reg .pop) cleanup)))

private def readback (layout : ReturnLayout) : SFunc := (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xe0] (by decide)) (.next (.reg .add) (.next (.reg .mload) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .and) (.next (.push layout.nonzeroDestination layout.nonzeroLe) (.branch layout.zeroFailure finish))))))))))))))))

private def tail (layout : ReturnLayout) : SFunc :=
  (callFlagGuardLine layout.answerDestination layout.answerLe).foldr SFunc.next
    (.branch layout.failure (readback layout))

/-- Closed structural checks, independent of any machine execution or answer. -/
structure ReturnChecks (layout : ReturnLayout) : Prop where
  failureHalts : layout.failure.haltsOnly = true
  zeroHalts : layout.zeroFailure.haltsOnly = true
  bodyFree : (tail layout).execFreeIn [] = true
  bodyNoHalt : (tail layout).noHalt = true

private def recoveryPrefix : List Ninst :=
  [ .push [0x00] (by decide),
    .push [0x01] (by decide),
    .reg (.dup 6),
    .reg (.dup 6),
    .reg (.dup 6),
    .reg (.dup 6),
    .push [0x40] (by decide),
    .reg .mload,
    .push [0x00] (by decide),
    .reg (.dup 1),
    .reg .mstore,
    .push [0x20] (by decide),
    .reg .add,
    .push [0x40] (by decide),
    .reg .mstore,
    .push [0x40] (by decide),
    .reg .mload,
    .reg (.dup 0),
    .reg (.dup 5),
    .reg (.dup 1),
    .reg .mstore,
    .push [0x20] (by decide),
    .reg .add,
    .reg (.dup 4),
    .push [0xff] (by decide),
    .reg .and,
    .reg (.dup 1),
    .reg .mstore,
    .push [0x20] (by decide),
    .reg .add,
    .reg (.dup 3),
    .reg (.dup 1),
    .reg .mstore,
    .push [0x20] (by decide),
    .reg .add,
    .reg (.dup 2),
    .reg (.dup 1),
    .reg .mstore,
    .push [0x20] (by decide),
    .reg .add,
    .reg (.swap 4),
    .reg .pop,
    .reg .pop,
    .reg .pop,
    .reg .pop,
    .reg .pop,
    .push [0x20] (by decide),
    .push [0x40] (by decide),
    .reg .mload,
    .push [0x20] (by decide),
    .reg (.dup 1),
    .reg .sub,
    .reg (.swap 0),
    .reg (.dup 0),
    .reg (.dup 4),
    .reg .sub,
    .reg (.swap 0),
    .reg (.dup 5),
    .reg .gas ]

/-- This exact request prefix followed by the layout's checked return source. -/
def entry (layout : ReturnLayout) : SFunc :=
  .dest (recoveryPrefix.foldr SFunc.next (.next (.exec .staticcall) (tail layout)))

variable {code : ByteArray} {c : Cert} {layout : ReturnLayout}

private theorem recovery_prefix_size :
    (recoveryPrefix.map Ninst.size).sum = 74 := by
  rfl

private theorem recovery_prefix_free (n : Ninst) (member : n ∈ recoveryPrefix)
    (x : Xinst) : n ≠ .exec x := by
  have checked : recoveryPrefix.all
      (fun n => match n with | .exec _ => false | _ => true) = true := by rfl
  have good := List.all_eq_true.mp checked n member
  intro same
  rw [same] at good
  cases good

private theorem recovery_allocate_line
    {sevm : Sevm} {b d : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest ret : B256} {S : List B256}
    (ptr : PtrMem p n M)
    (run : Line.Run sevm
      (St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
      (recoveryPrefix.take 15) d) :
    ∃ G', d = St b
      (s :: r :: v :: digest :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S)
      ((M.write p.toNat (0 : B256).toBytes).write 64 (32 + p).toBytes) G' := by
  have read : (M.read 64 32).2 = M := ptr.read_self (by have := ptr.ge; omega)
  have word : Bytes.toB256 (M.read 64 32).1 = p := ptr.word
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, read, word] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  cases run
  exact ⟨_, rfl⟩

private theorem recovery_encode_line
    {sevm : Sevm} {b d : Devm} {M : Mem} {G n : Nat}
    {q placeholder s r v digest ret : B256} {S : List B256}
    (ptr : PtrMem q n M)
    (run : Line.Run sevm
      (St b (s :: r :: v :: digest :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S) M G)
      ((recoveryPrefix.drop 15).take 31) d) :
    ∃ G', d = St b
      ((32 + (32 + (32 + (32 + q)))) :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S)
      ((((M.write q.toNat digest.toBytes).write (32 + q).toNat (255 &&& v).toBytes).write
        (32 + (32 + q)).toNat r.toBytes).write (32 + (32 + (32 + q))).toNat s.toBytes) G' := by
  have read : (M.read 64 32).2 = M := ptr.read_self (by have := ptr.ge; omega)
  have word : Bytes.toB256 (M.read 64 32).1 = q := ptr.word
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, read, word] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  cases run
  exact ⟨_, rfl⟩

private theorem recovery_operands_line
    {sevm : Sevm} {b d : Devm} {M : Mem} {G n : Nat}
    {q lastPtr placeholder s r v digest ret : B256} {S : List B256}
    (ptr : PtrMem q n M)
    (run : Line.Run sevm
      (St b (lastPtr :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S) M G)
      (recoveryPrefix.drop 46) d) :
    ∃ G', d = St b
      (G'.toB256 :: 1 :: q :: (lastPtr - q) :: (q - 32) :: 32 ::
        lastPtr :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S) M G' := by
  have read : (M.read 64 32).2 = M := ptr.read_self (by have := ptr.ge; omega)
  have word : Bytes.toB256 (M.read 64 32).1 = q := ptr.word
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, read, word] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_gas_remaining step
  cases run
  exact ⟨_, rfl⟩

private def recoveryMemory (M : Mem) (p digest v r s : B256) : Mem :=
  ((((((M.write p.toNat (0 : B256).toBytes).write 64 (32 + p).toBytes).write
    (32 + p).toNat digest.toBytes).write
    (32 + (32 + p)).toNat (255 &&& v).toBytes).write
    (32 + (32 + (32 + p))).toNat r.toBytes).write
    (32 + (32 + (32 + (32 + p)))).toNat s.toBytes)

private theorem recovery_memory_input {M : Mem} {n : Nat} {p digest v r s : B256}
    (ptr : PtrMem p n M) (space : p.toNat + 160 < 2 ^ 256) :
    ((recoveryMemory M p digest v r s).read (32 + p).toNat 128).1 =
      digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes := by
  have qnat : (32 + p).toNat = p.toNat + 32 := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have rnat : (32 + (32 + p)).toNat = p.toNat + 32 + 32 := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, qnat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have snat : (32 + (32 + (32 + p))).toNat = p.toNat + 32 + 64 := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, rnat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have tnat : (32 + (32 + (32 + (32 + p)))).toNat = p.toNat + 32 + 96 := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, snat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have image := (Mem.reads_data M).write ptr.wf p.toNat (0 : B256).toBytes
  have wf := ptr.wf.write p.toNat (0 : B256).toBytes
  have image := image.write wf 64 (32 + p).toBytes
  have wf := wf.write 64 (32 + p).toBytes
  have image := image.write wf (32 + p).toNat digest.toBytes
  have wf := wf.write (32 + p).toNat digest.toBytes
  have image := image.write wf (32 + (32 + p)).toNat (255 &&& v).toBytes
  have wf := wf.write (32 + (32 + p)).toNat (255 &&& v).toBytes
  have image := image.write wf (32 + (32 + (32 + p))).toNat r.toBytes
  have wf := wf.write (32 + (32 + (32 + p))).toNat r.toBytes
  have image := image.write wf (32 + (32 + (32 + (32 + p)))).toNat s.toBytes
  unfold recoveryMemory
  rw [Mem.Reads.read image]
  rw [qnat, rnat, snat, tnat]
  rw [Bytes.sliceD_writeAt_word_last _ (p.toNat + 32) 96 _ 128 s (by omega) (by rfl),
    Bytes.sliceD_writeAt_word_last _ (p.toNat + 32) 64 _ 96 r (by omega) (by rfl),
    Bytes.sliceD_writeAt_word_last _ (p.toNat + 32) 32 _ 64 (255 &&& v) (by omega) (by rfl),
    sliceD_word_same]

private theorem recovery_memory_zero {M : Mem} {n : Nat} {p digest v r s : B256}
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat)
    (space : p.toNat + 160 < 2 ^ 256) :
    memWord (recoveryMemory M p digest v r s) p.toNat = 0 := by
  have qnat : (32 + p).toNat = p.toNat + 32 := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have rnat : (32 + (32 + p)).toNat = p.toNat + 32 + 32 := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, qnat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have snat : (32 + (32 + (32 + p))).toNat = p.toNat + 32 + 64 := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, rnat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have tnat : (32 + (32 + (32 + (32 + p)))).toNat = p.toNat + 32 + 96 := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, snat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have image := (Mem.reads_data M).write ptr.wf p.toNat (0 : B256).toBytes
  have wf := ptr.wf.write p.toNat (0 : B256).toBytes
  have image := image.write wf 64 (32 + p).toBytes
  have wf := wf.write 64 (32 + p).toBytes
  have image := image.write wf (32 + p).toNat digest.toBytes
  have wf := wf.write (32 + p).toNat digest.toBytes
  have image := image.write wf (32 + (32 + p)).toNat (255 &&& v).toBytes
  have wf := wf.write (32 + (32 + p)).toNat (255 &&& v).toBytes
  have image := image.write wf (32 + (32 + (32 + p))).toNat r.toBytes
  have wf := wf.write (32 + (32 + (32 + p))).toNat r.toBytes
  have image := image.write wf (32 + (32 + (32 + (32 + p)))).toNat s.toBytes
  unfold memWord recoveryMemory
  rw [Mem.Reads.read image, qnat, rnat, snat, tnat]
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ s (.inl (by omega)),
    Bytes.readWord_writeAt_of_disjoint _ _ _ r (.inl (by omega)),
    Bytes.readWord_writeAt_of_disjoint _ _ _ (255 &&& v) (.inl (by omega)),
    Bytes.readWord_writeAt_of_disjoint _ _ _ digest (.inl (by omega)),
    Bytes.readWord_writeAt_of_disjoint _ _ _ (32 + p) (.inr (by omega)),
    Bytes.readWord_writeAt_self]

private theorem recovery_prefix_line
    {sevm : Sevm} {b d : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest ret : B256} {S : List B256}
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat)
    (space : p.toNat + 160 < 2 ^ 256)
    (run : Line.Run sevm
      (St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
      recoveryPrefix d) :
    ∃ G' n',
      d = St b
        (G'.toB256 :: 1 :: (32 + p) ::
          ((32 + (32 + (32 + (32 + (32 + p))))) - (32 + p)) ::
          ((32 + p) - 32) :: 32 ::
          (32 + (32 + (32 + (32 + (32 + p))))) ::
          1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S)
        ((((((M.write p.toNat (0 : B256).toBytes).write 64 (32 + p).toBytes).write
          (32 + p).toNat digest.toBytes).write
          (32 + (32 + p)).toNat (255 &&& v).toBytes).write
          (32 + (32 + (32 + p))).toNat r.toBytes).write
          (32 + (32 + (32 + (32 + p)))).toNat s.toBytes) G' ∧
      PtrMem (32 + p) n'
        ((((((M.write p.toNat (0 : B256).toBytes).write 64 (32 + p).toBytes).write
          (32 + p).toNat digest.toBytes).write
          (32 + (32 + p)).toNat (255 &&& v).toBytes).write
          (32 + (32 + (32 + p))).toNat r.toBytes).write
          (32 + (32 + (32 + (32 + p)))).toNat s.toBytes) := by
  have qnat : (32 + p).toNat = 32 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have rnat : (32 + (32 + p)).toNat = 64 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, qnat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have snat : (32 + (32 + (32 + p))).toNat = 96 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, rnat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have tnat : (32 + (32 + (32 + (32 + p)))).toNat = 128 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, snat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have ptr1 := (ptr.write p.toNat 0 (.inr lower)).set (q := 32 + p)
  have ptr2 := (((ptr1.write (32 + p).toNat digest (.inr (by omega))).write
    (32 + (32 + p)).toNat (255 &&& v) (.inr (by omega))).write
    (32 + (32 + (32 + p))).toNat r (.inr (by omega))).write
    (32 + (32 + (32 + (32 + p)))).toNat s (.inr (by omega))
  rw [← List.take_append_drop 15 recoveryPrefix] at run
  obtain ⟨mid, first, rest⟩ := of_run_append _ run
  obtain ⟨_, rfl⟩ := recovery_allocate_line ptr first
  rw [← List.take_append_drop 31 (recoveryPrefix.drop 15)] at rest
  obtain ⟨mid, second, last⟩ := of_run_append _ rest
  obtain ⟨_, rfl⟩ := recovery_encode_line ptr1 second
  change Line.Run _ _ (recoveryPrefix.drop 46) _ at last
  obtain ⟨_, rfl⟩ := recovery_operands_line ptr2 last
  exact ⟨_, _, rfl, ptr2⟩

private theorem recovery_prefix_request
    {sevm : Sevm} {b d : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest ret : B256} {S : List B256}
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat)
    (space : p.toNat + 160 < 2 ^ 256)
    (run : Line.Run sevm
      (St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
      recoveryPrefix d) :
    ∃ G' n', d = St b
      (G'.toB256 :: 1 :: (32 + p) :: 128 :: p :: 32 ::
        (32 + (32 + (32 + (32 + (32 + p))))) ::
        1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S)
      (recoveryMemory M p digest v r s) G' ∧
      PtrMem (32 + p) n' (recoveryMemory M p digest v r s) := by
  have qnat : (32 + p).toNat = 32 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have rnat : (32 + (32 + p)).toNat = 64 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, qnat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have snat : (32 + (32 + (32 + p))).toNat = 96 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, rnat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have tnat : (32 + (32 + (32 + (32 + p)))).toNat = 128 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, snat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have enat : (32 + (32 + (32 + (32 + (32 + p))))).toNat = 160 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, tnat,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have length : (32 + (32 + (32 + (32 + (32 + p))))) - (32 + p) = (128 : B256) := by
    apply B256.toNat_inj
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, enat, qnat]; omega),
      enat, qnat]
    change _ = 128
    omega
  have output : (32 + p) - 32 = p := by
    apply B256.toNat_inj
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, qnat]; change 32 ≤ _; omega), qnat]
    change 32 + p.toNat - 32 = p.toNat
    omega
  obtain ⟨G', n', state, ptr'⟩ := recovery_prefix_line ptr lower space run
  rw [length, output] at state
  exact ⟨G', n', state, ptr'⟩

private theorem recovery_call_cut
    (checked : Cert.check code c = true)
    {F : Exec.Deriv} {κ : Cursor} {post b : Devm} {M : Mem} {G : Nat}
    {placeholder s r v digest ret : B256} {S : List B256}
    (ok : CursorOK code c F κ)
    (tree : κ.f = entry layout)
    (state : F.devm = St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep F .staticcall) (next : Cursor),
      step.occurrence.node.pc = F.pc + 75 ∧
      Exec.Deriv.ExecFreeUntil F step.occurrence.node ∧
      step.occurrence.node.sevm = F.sevm ∧
      step.occurrence.node.exn = F.exn ∧
      (∃ G', Line.Run F.sevm
        (St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G')
        recoveryPrefix step.occurrence.node.devm) ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node)
        step.occurrence.node.sevm step.occurrence.node.devm
        (.exec .staticcall) step.returned.devm ∧
      CursorOK code c step.returned next ∧
      next.f = (tail layout) ∧ next.K = κ.K := by
  change κ.f = .dest (recoveryPrefix.foldr SFunc.next
    (.next (.exec .staticcall) (tail layout))) at tree
  have decoded := ok.jumpdestAt_of_dest tree
  obtain ⟨D, kd, edge, jumped, synthetic, _, placed⟩ :=
    cursor_jinst_forwardH checked ok decoded success fork.stateGas
  obtain ⟨dpc, burn⟩ := of_jumpdest_run jumped
  have shape : kd.f = recoveryPrefix.foldr SFunc.next
      (.next (.exec .staticcall) (tail layout)) ∧ kd.K = κ.K := by
    rcases κ with ⟨f, pc, a, m, K⟩
    dsimp only at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  have dsevm := Cursor.parentStep_sevm edge
  have dexn : D.exn = F.exn := by cases edge <;> rfl
  obtain ⟨C, kc, path, cpc, csevm, cexn, callPlaced, callTree, line, sameK, free⟩ :=
    cursor_nexts_line_cont_free_forwardH checked placed
      recoveryPrefix (.next (.exec .staticcall) (tail layout)) shape.1
      (dexn.trans success) (by rw [dsevm]; exact fork.stateGas)
  have span := (Exec.Deriv.ExecFreeUntil.ofStep edge
    (Blanc.Jinst.At.not_exec decoded)).trans (free recovery_prefix_free)
  obtain ⟨step, next, node, _, primitive, crossed, _, returnedPlaced⟩ :=
    cursor_next_call_occurrence_forwardH checked span.1
      callPlaced callTree ((cexn.trans dexn).trans success)
      (by rw [csevm, dsevm]; exact fork.stateGas)
  have nextShape : next.f = (tail layout) ∧ next.K = kc.K := by
    rcases kc with ⟨f, pc, a, m, K⟩
    dsimp only at callTree
    subst f
    cases crossed
    exact ⟨rfl, rfl⟩
  refine ⟨step, next, ?_, ?_, ?_, ?_, ?_, ?_, returnedPlaced,
    nextShape.1, nextShape.2.trans (sameK.trans shape.2)⟩
  · rw [node, cpc, recovery_prefix_size, dpc]
  · rw [node]; exact span
  · rw [node]; exact csevm.trans dsevm
  · rw [node]; exact cexn.trans dexn
  · rw [node]
    rw [state] at burn
    rw [dsevm, St.of_burn burn] at line
    exact ⟨_, line⟩
  · rw [node]; exact primitive

private theorem recovery_call_cut_toward_sstore
    (checked : Cert.check code c = true)
    {F target : Exec.Deriv} {κ : Cursor} {b : Devm} {M : Mem} {G : Nat}
    {placeholder s r v digest ret : B256} {S : List B256}
    (ok : CursorOK code c F κ) (tree : κ.f = entry layout)
    (state : F.devm = St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (step : CallOccurrenceStep F .staticcall) (next : Cursor),
      step.occurrence.node.pc = F.pc + 75 ∧
      Exec.Deriv.ExecFreeUntil F step.occurrence.node ∧
      Exec.Deriv.ParentPrefix step.returned target ∧
      step.occurrence.node.sevm = F.sevm ∧
      (∃ G', Line.Run F.sevm
        (St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G')
        recoveryPrefix step.occurrence.node.devm) ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node)
        step.occurrence.node.sevm step.occurrence.node.devm
        (.exec .staticcall) step.returned.devm ∧
      CursorOK code c step.returned next ∧
      next.f = tail layout ∧ next.K = κ.K := by
  change κ.f = .dest (recoveryPrefix.foldr SFunc.next
    (.next (.exec .staticcall) (tail layout))) at tree
  have decoded := ok.jumpdestAt_of_dest tree
  obtain ⟨D, kd, edge, later, synthetic, _, placed⟩ :=
    cursor_step_toward_sstore_noStateGas checked ok path store
      (by intro f same; rw [tree] at same; cases same) hsg
  obtain ⟨dpc, burn⟩ := of_jumpdest_run (Cursor.parentStep_jinst edge decoded)
  have shape : kd.f = recoveryPrefix.foldr SFunc.next
      (.next (.exec .staticcall) (tail layout)) ∧ kd.K = κ.K := by
    rcases κ with ⟨f, pc, a, m, K⟩
    dsimp only at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  have dsevm := Cursor.parentStep_sevm edge
  have prefixFree : ∀ n ∈ recoveryPrefix, n ≠ .reg .sstore := by
    intro n member same
    have checked : recoveryPrefix.all
        (fun n => match n with | .reg .sstore => false | _ => true) = true := by rfl
    have good := List.all_eq_true.mp checked n member
    rw [same] at good
    cases good
  obtain ⟨C, kc, spanD, laterC, cpc, csevm, _, callPlaced, callTree, sameK, line, free⟩ :=
    cursor_line_toward_sstore_noStateGas checked placed later store recoveryPrefix
      (.next (.exec .staticcall) (tail layout)) shape.1 prefixFree (dsevm ▸ hsg)
  have span := (Exec.Deriv.ExecFreeUntil.ofStep edge
    (Blanc.Jinst.At.not_exec decoded)).trans (free recovery_prefix_free)
  obtain ⟨step, next, node, returnedPath, _, primitive, crossed, _, returnedPlaced⟩ :=
    cursor_call_occurrence_toward_sstore_noStateGas checked span.1 callPlaced callTree
      laterC store (by rw [csevm, dsevm]; exact hsg)
  have nextShape : next.f = tail layout ∧ next.K = kc.K := by
    rcases kc with ⟨f, pc, a, m, K⟩
    dsimp only at callTree
    subst f
    cases crossed
    exact ⟨rfl, rfl⟩
  refine ⟨step, next, ?_, ?_, returnedPath, ?_, ?_, ?_, returnedPlaced,
    nextShape.1, nextShape.2.trans (sameK.trans shape.2)⟩
  · rw [node, cpc, recovery_prefix_size, dpc]
  · rw [node]; exact span
  · rw [node]; exact csevm.trans dsevm
  · rw [node]
    rw [state] at burn
    rw [dsevm, St.of_burn burn] at line
    exact ⟨_, line⟩
  · rw [node]; exact primitive

private theorem recovery_tail_success
    (checks : ReturnChecks layout)
    {sevm : Sevm} {b D : Devm} {M : Mem} {G : Nat} {flag : B256} {S : List B256}
    (flags : flag = 0 ∨ flag = 1)
    (run : SFunc.Run c.prog sevm (St b (flag :: S) M G)
      (tail layout) (.returned D)) :
    flag = 1 ∧ ∃ G', SFunc.Run c.prog sevm
      (St b (0 :: S) M G') (readback layout) (.returned D) := by
  unfold tail callFlagGuardLine at run
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push step
  rcases rpw_branch run with ⟨_, _, rejected⟩ | ⟨taken, G', accepted⟩
  · exact (rejected.not_returned_of_haltsOnly checks.failureHalts).elim
  · rcases flags with h | h
    · subst flag
      exact (taken rfl).elim
    · subst flag
      exact ⟨rfl, G', accepted⟩

private theorem recovery_readback_return
    (checks : ReturnChecks layout)
    {sevm : Sevm} {b D : Devm} {M : Mem} {G : Nat}
    {p w lastPtr placeholder s r v digest ret : B256} {S : List B256}
    (space : p.toNat + 160 < 2 ^ 256)
    (word : memWord M 64 = 32 + p) (answer : memWord M p.toNat = w)
    (run : SFunc.Run c.prog sevm
      (St b (0 :: lastPtr :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S) M G)
      (readback layout) (.returned D)) :
    (w &&& (0xffffffffffffffffffffffffffffffffffffffff : B256)) ≠ 0 ∧
      ∃ M' G', D = St b (w :: S) M' G' := by
  have qnat : (32 + p).toNat = 32 + p.toNat := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have back : (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0 : B256) +
      (32 + p) = p := by
    apply B256.toNat_inj
    rw [B256.toNat_add, qnat,
      show (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0 : B256).toNat =
        2 ^ 256 - 32 from rfl,
      show 2 ^ 256 - 32 + (32 + p.toNat) = 2 ^ 256 + p.toNat by omega,
      Nat.lo, Nat.add_mod_left, Nat.mod_eq_of_lt (B256.toNat_lt p)]
  unfold readback at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, state⟩ := ri_mload step
  change memWord M 64 = _ at word
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, ← memWord, word] at state
  subst state
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, state⟩ := ri_add step
  change _ = St b (((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0 : B256) + (32 + p)) :: _) _ _ at state
  rw [back] at state
  subst state
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, state⟩ := ri_mload step
  have actual : Bytes.toB256 (((M.read 64 32).2).read p.toNat 32).1 = w := answer
  rw [actual] at state
  subst state
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push step
  rcases rpw_branch run with ⟨_, _, rejected⟩ | ⟨nonzero, _, accepted⟩
  · exact (rejected.not_returned_of_haltsOnly checks.zeroHalts).elim
  · refine ⟨nonzero, ?_⟩
    unfold finish at accepted
    obtain ⟨_, accepted⟩ := rpw_dest accepted
    obtain ⟨_, step, accepted⟩ := rpw_next accepted
    obtain ⟨_, rfl⟩ := ri_swap rfl step
    obtain ⟨_, step, accepted⟩ := rpw_next accepted
    obtain ⟨_, rfl⟩ := ri_pop step
    unfold cleanup at accepted
    obtain ⟨_, accepted⟩ := rpw_dest accepted
    obtain ⟨_, step, accepted⟩ := rpw_next accepted
    obtain ⟨_, rfl⟩ := ri_swap rfl step
    obtain ⟨_, step, accepted⟩ := rpw_next accepted
    obtain ⟨_, rfl⟩ := ri_swap rfl step
    obtain ⟨_, step, accepted⟩ := rpw_next accepted
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, accepted⟩ := rpw_next accepted
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, accepted⟩ := rpw_next accepted
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, accepted⟩ := rpw_next accepted
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, state⟩ := rpw_ret accepted
    exact ⟨_, _, state⟩

private theorem recovery_answer_of_return
    (checks : ReturnChecks layout)
    {F : Exec.Deriv} (call : CallOccurrenceStep F .staticcall)
    {b D : Devm} {M : Mem} {G n : Nat}
    {p lastPtr placeholder s r v digest ret : B256} {S : List B256}
    (state : call.occurrence.node.devm = St b
      (G.toB256 :: 1 :: (32 + p) :: 128 :: p :: 32 ::
        lastPtr :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S) M G)
    (ptr : PtrMem (32 + p) n M) (zero : memWord M p.toNat = 0)
    (lower : 96 ≤ p.toNat) (space : p.toNat + 160 < 2 ^ 256)
    (ready : call.occurrence.node.sevm.benvStat.rules.delegatedCodeAddress (b.getCode 1) = none)
    (fork : NeutralFork call.occurrence.node.sevm.benvStat.fork)
    (primitive : Ninst.RunWith (Cursor.DescOf call.occurrence.node)
      call.occurrence.node.sevm call.occurrence.node.devm
      (.exec .staticcall) call.returned.devm)
    (returned : SFunc.Run c.prog call.occurrence.node.sevm call.returned.devm
      (tail layout) (.returned D)) :
    ∃ adr : Adr, adr ≠ 0 ∧
      ecrecoverOutput (M.read (32 + p).toNat 128).1 = adr.toB256.toBytes ∧
      call.returned.devm.returnData = adr.toB256.toBytes ∧
      call.returned.devm.stack = 1 :: lastPtr :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S ∧
      StaticAnsweredH call.occurrence.node.sevm b 1
        (M.read (32 + p).toNat 128).1 adr.toB256.toBytes ∧ D.stack = adr.toB256 :: S := by
  have run := primitive.toRun
  rw [state] at run
  obtain ⟨flag, out, hpost, answered⟩ := ri_staticcallH fork.stateGas run
  have tailRun := returned
  rw [hpost.eq_St] at tailRun
  obtain ⟨flagOne, G', accepted⟩ := recovery_tail_success checks hpost.flag tailRun
  rw [← hpost.memory] at accepted
  have answered := answered flagOne
  change StaticAnsweredH _ _ 1 _ _ at answered
  obtain ⟨parent, child, xl, dp, na, code, gas, sameState, delegation, filled,
    process, clean, childOutput⟩ := answered
  have direct : na = 1 ∧ code = b.getCode 1 ∧ dp = false :=
    CallCodeH.direct_of_effective ready delegation
  obtain ⟨rfl, rfl, rfl⟩ := direct
  obtain ⟨paid, actualOutput⟩ := ecrecover_output_of_processMessage_cleanH
    (ecrecover_activeH _) process clean fork.stateGas
  have outEq : out = ecrecoverOutput (M.read (32 + p).toNat 128).1 :=
    childOutput.symm.trans actualOutput
  have response : out = [] ∨ ∃ adr : Adr, out = adr.toB256.toBytes := by
    rw [outEq]; exact ecrecoverOutput_spectrum _
  have freeword : memWord call.returned.devm.memory 64 = 32 + p := by
    rw [hpost.memory]
    unfold memWord
    have image := ((Mem.reads_data M).extends
      [((32 + p).toNat, (128 : B256).toNat), (p.toNat, (32 : B256).toNat)]).write
        (ptr.wf.extends _) p.toNat (out.take (32 : B256).toNat)
    rw [Mem.Reads.read image,
      Bytes.sliceD_writeAt_before _ _ 64 32 p.toNat (by omega),
      ← (Mem.reads_data M).read]
    exact ptr.word
  rcases response with empty | ⟨adr, address⟩
  · have readZero : memWord call.returned.devm.memory p.toNat = 0 := by
      rw [hpost.memory, empty]
      exact zero
    have bad := (recovery_readback_return checks space freeword readZero accepted).1
    exact (bad (by rfl)).elim
  · have readAddress : memWord call.returned.devm.memory p.toNat = adr.toB256 := by
      rw [hpost.memory, address,
        show (32 : B256).toNat = 32 from rfl,
        ← B256.length_toBytes adr.toB256, List.take_length]
      exact (Mem.memWord_write_word _ _ _).1
    obtain ⟨nonzero, M', G', endState⟩ :=
      recovery_readback_return checks space freeword readAddress accepted
    refine ⟨adr, ?_, outEq.symm.trans address,
      hpost.returnData.trans address, (by rw [hpost.stack, flagOne]), ?_, ?_⟩
    · intro vanished
      subst adr
      exact nonzero (by rfl)
    · exact ⟨parent, child, xl, false, 1, b.getCode 1, gas, sameState,
        CallCodeH.of_effective ready, filled, process, clean, childOutput.trans address⟩
    · rw [endState, St.stack]

private theorem recovery_answer_consumer
    (checked : Cert.check code c = true) (checks : ReturnChecks layout)
    {F : Exec.Deriv} (call : CallOccurrenceStep F .staticcall) {cursor : Cursor}
    {post b : Devm} {M : Mem} {G n : Nat}
    {p lastPtr placeholder s r v digest ret : B256} {S : List B256}
    {caller : SFunc} {K : List SFunc}
    (state : call.occurrence.node.devm = St b
      (G.toB256 :: 1 :: (32 + p) :: 128 :: p :: 32 ::
        lastPtr :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S) M G)
    (ptr : PtrMem (32 + p) n M) (zero : memWord M p.toNat = 0)
    (lower : 96 ≤ p.toNat) (space : p.toNat + 160 < 2 ^ 256)
    (ready : call.occurrence.node.sevm.benvStat.rules.delegatedCodeAddress (b.getCode 1) = none)
    (placed : CursorOK code c call.returned cursor)
    (tree : cursor.f = (tail layout))
    (continuations : cursor.K.map Cont.f = caller :: K)
    (success : call.returned.exn = .ok post)
    (fork : NeutralFork call.occurrence.node.sevm.benvStat.fork)
    (primitive : Ninst.RunWith (Cursor.DescOf call.occurrence.node)
      call.occurrence.node.sevm call.occurrence.node.devm
      (.exec .staticcall) call.returned.devm) :
    ∃ (adr : Adr) (N : Exec.Deriv) (next : Cursor),
      adr ≠ 0 ∧
      ecrecoverOutput (M.read (32 + p).toNat 128).1 = adr.toB256.toBytes ∧
      call.returned.devm.returnData = adr.toB256.toBytes ∧
      call.returned.devm.stack = 1 :: lastPtr :: 1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S ∧
      StaticAnsweredH call.occurrence.node.sevm b 1
        (M.read (32 + p).toNat 128).1 adr.toB256.toBytes ∧
      Exec.Deriv.ExecFreeUntil call.returned N ∧
      N.exn = call.returned.exn ∧ N.sevm = call.returned.sevm ∧
      CursorOK code c N next ∧
      next.f = caller ∧ next.K.map Cont.f = K ∧ N.devm.stack = adr.toB256 :: S := by
  have sameEnv := Cursor.parentStep_sevm call.edge
  have returnedFork : NeutralFork call.returned.sevm.benvStat.fork := by rw [sameEnv]; exact fork
  obtain ⟨N, next, span, suffixEnv, suffixExn, finalPlaced, callerTree, callerK, returned⟩ :=
    placed.quietReturnH checked success returnedFork.stateGas
      (E := []) (by rfl) (by rfl) (by rw [tree]; exact checks.bodyFree) (by rw [tree]; exact checks.bodyNoHalt) continuations
  rw [tree, sameEnv] at returned
  obtain ⟨adr, nonzero, output, returnData, returnedStack, answered, callerStack⟩ :=
    recovery_answer_of_return checks call state ptr zero lower space ready fork primitive returned
  exact ⟨adr, N, next, nonzero, output, returnData, returnedStack, answered, span,
    suffixExn, suffixEnv, finalPlaced, callerTree, callerK, callerStack⟩

private theorem actual_native_answer
    {F : Exec.Deriv} (call : CallOccurrenceStep F .staticcall)
    {g ii is oi os : B256} {xs : Stack} {input : Bytes} {adr : Adr}
    (operands : (g :: 1 :: ii :: is :: oi :: os :: xs) <<+ call.occurrence.node.devm.stack)
    (hsg : call.occurrence.node.sevm.benvStat.rules.stateGas = none)
    (ready : call.occurrence.node.sevm.benvStat.rules.delegatedCodeAddress
      (call.occurrence.node.devm.getCode 1) = none)
    (flag : ∃ rest, call.returned.devm.stack = 1 :: rest)
    (inputEq : (call.occurrence.node.devm.memory.read ii.toNat is.toNat).1 = input)
    (answer : ecrecoverOutput input = adr.toB256.toBytes) :
    ∃ (parent child : Devm) (gas : Nat),
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      Ninst.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm, call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent oi.toNat os.toNat) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧ call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done
        ((Frame.ofCall msg).settle (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧ child.output = adr.toB256.toBytes := by
  have exactStep := call.occurrence.stepRun
  rw [call.instruction, call.result] at exactStep
  rcases of_step_staticcall_val_with_depth_frame_causeH operands call.occurrence.filled
      exactStep hsg with failed | entered
  · obtain ⟨rest, stack⟩ := flag
    rw [stack] at failed
    have impossible : (0 : B256) = 1 := pref_head_unique failed.1 (pref_append [1] _)
    exact (show (0 : B256) ≠ 1 by decide) impossible |>.elim
  · obtain ⟨parent, child, dp, na, code, avail, depth, parentStack, parentState,
      parentMemory, parentLogs, parentOutput, delegation, filled, process, clean,
      resumed, childState, childReturn, childMemory, childStack, spawned⟩ := entered
    have direct : na = 1 ∧ code = call.occurrence.node.devm.getCode 1 ∧ dp = false :=
      CallCodeH.direct_of_effective (t := 1) ready delegation
    obtain ⟨rfl, rfl, rfl⟩ := direct
    rw [show (1 : B256).toAdr = 1 from rfl, inputEq] at process spawned
    obtain ⟨paid, childOutput⟩ := ecrecover_output_of_processMessage_cleanH
      (ecrecover_activeH _) process clean hsg
    let msg := callMsg call.occurrence.node.sevm parent
      (min g.toNat (except64th avail)) 0 call.occurrence.node.sevm.currentTarget
      1 1 true true input (call.occurrence.node.devm.getCode 1) false
    have native : (Frame.ofCall msg).enter = .done
        ((Frame.ofCall msg).settle (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) := by
      apply Frame.enter_eq_done_executePrecomp
        (Msg.benvAfterTransfer_of_value_zero (by rfl)) (by rfl)
      change decide (call.occurrence.node.sevm.benvStat.rules.isPrecomp 1) = true
      exact ecrecover_activeH _
    have emptySlot : call.occurrence.slot = .none := by
      change RunFrame (Frame.ofCall msg) call.occurrence.slot (.ok child) at process
      unfold RunFrame at process
      rw [native] at process
      exact process.1
    exact ⟨parent, child, min g.toNat (except64th avail), spawned, process,
      emptySlot, native, paid, clean, childOutput.trans answer⟩

/-- A successful actual checked recovery return consumes the answer to its own
address-1 invocation. The concrete entry registers, free pointer, effective readiness
and checked caller are local producer obligations; they are not final history
or environmental hypotheses. This theorem does not enumerate flag-zero calls. -/
theorem consumes_effective
    (checked : Cert.check code c = true) (layout : ReturnLayout) (checks : ReturnChecks layout)
    {F : Exec.Deriv} {κ : Cursor} {post b : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest ret : B256} {S : List B256}
    {caller : SFunc} {K : List SFunc}
    (ok : CursorOK code c F κ)
    (tree : κ.f = entry layout)
    (state : F.devm = St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat)
    (space : p.toNat + 160 < 2 ^ 256)
    (ready : F.sevm.benvStat.rules.delegatedCodeAddress (b.getCode 1) = none)
    (continuations : κ.K.map Cont.f = caller :: K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (call : CallOccurrenceStep F .staticcall) (parent child : Devm)
      (gas : Nat) (adr : Adr) (N : Exec.Deriv) (next : Cursor),
      let input := digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      call.occurrence.node.pc = F.pc + 75 ∧
      Exec.Deriv.ExecFreeUntil F call.occurrence.node ∧
      Ninst.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm, call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent p.toNat 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧
      call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done
        ((Frame.ofCall msg).settle (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧
      child.output = adr.toB256.toBytes ∧
      ecrecoverOutput input = adr.toB256.toBytes ∧ adr ≠ 0 ∧
      call.returned.devm.returnData = adr.toB256.toBytes ∧
      Exec.Deriv.ExecFreeUntil call.returned N ∧
      N.exn = F.exn ∧ N.sevm = F.sevm ∧
      CursorOK code c N next ∧
      next.f = caller ∧ next.K.map Cont.f = K ∧ N.devm.stack = adr.toB256 :: S := by
  obtain ⟨call, cursor, callPc, span, sameEnv, sameExn, ⟨G0, line⟩,
    primitive, placed, tailTree, sameK⟩ :=
    recovery_call_cut checked ok tree state success fork
  obtain ⟨Gc, nc, callState, callPtr⟩ := recovery_prefix_request ptr lower space line
  have callFork : NeutralFork call.occurrence.node.sevm.benvStat.fork := by rw [sameEnv]; exact fork
  have callReady : call.occurrence.node.sevm.benvStat.rules.delegatedCodeAddress
      (b.getCode 1) = none := by
    rw [sameEnv]
    exact ready
  have returnedOutcome : call.returned.exn = call.occurrence.node.exn := by
    have edge := call.edge
    generalize call.returned = R at edge ⊢
    generalize call.occurrence.node = C at edge ⊢
    cases edge <;> rfl
  obtain ⟨adr, N, next, nonzero, output, returnData, returnedStack, answered,
    suffix, suffixExn, suffixEnv, finalPlaced, callerTree, callerK, callerStack⟩ :=
    recovery_answer_consumer checked checks call callState callPtr (recovery_memory_zero ptr lower space)
      lower space callReady placed tailTree (by rw [sameK]; exact continuations)
      ((returnedOutcome.trans sameExn).trans success) callFork primitive
  have inputEq : (call.occurrence.node.devm.memory.read (32 + p).toNat 128).1 =
      digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes := by
    rw [callState, St.memory]
    exact recovery_memory_input ptr space
  have operands : (Gc.toB256 :: 1 :: (32 + p) :: 128 :: p :: 32 ::
      (32 + (32 + (32 + (32 + (32 + p))))) ::
      1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S) <<+
      call.occurrence.node.devm.stack := by
    rw [callState, St.stack]
    simpa only [List.append_nil] using pref_append _ []
  have localReady : call.occurrence.node.sevm.benvStat.rules.delegatedCodeAddress
      (call.occurrence.node.devm.getCode 1) = none := by
    rw [callState]
    exact callReady
  have outputEq : ecrecoverOutput
      (digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes) = adr.toB256.toBytes := by
    rw [← recovery_memory_input ptr space]
    exact output
  obtain ⟨parent, child, gas, spawned, process, emptySlot, native, paid, clean, childOutput⟩ :=
    actual_native_answer call operands callFork.stateGas localReady ⟨_, returnedStack⟩ inputEq outputEq
  exact ⟨call, parent, child, gas, adr, N, next, callPc, span, spawned, process,
    emptySlot, native, paid, clean, childOutput, outputEq, nonzero, returnData, suffix,
    (suffixExn.trans returnedOutcome).trans sameExn,
    (suffixEnv.trans (Cursor.parentStep_sevm call.edge)).trans sameEnv,
    finalPlaced, callerTree, callerK, callerStack⟩

/-- Pure nondelegation projects to effective readiness under the actual rules.
The original successful consumer retains its public interface. -/
theorem consumes
    (checked : Cert.check code c = true) (layout : ReturnLayout) (checks : ReturnChecks layout)
    {F : Exec.Deriv} {κ : Cursor} {post b : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest ret : B256} {S : List B256}
    {caller : SFunc} {K : List SFunc}
    (ok : CursorOK code c F κ)
    (tree : κ.f = entry layout)
    (state : F.devm = St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat)
    (space : p.toNat + 160 < 2 ^ 256)
    (nodeleg : getDelegatedCodeAddress (b.getCode 1) = none)
    (continuations : κ.K.map Cont.f = caller :: K)
    (success : F.exn = .ok post) (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (call : CallOccurrenceStep F .staticcall) (parent child : Devm)
      (gas : Nat) (adr : Adr) (N : Exec.Deriv) (next : Cursor),
      let input := digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      call.occurrence.node.pc = F.pc + 75 ∧
      Exec.Deriv.ExecFreeUntil F call.occurrence.node ∧
      Ninst.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm, call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent p.toNat 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧
      call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done
        ((Frame.ofCall msg).settle (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧
      child.output = adr.toB256.toBytes ∧
      ecrecoverOutput input = adr.toB256.toBytes ∧ adr ≠ 0 ∧
      call.returned.devm.returnData = adr.toB256.toBytes ∧
      Exec.Deriv.ExecFreeUntil call.returned N ∧
      N.exn = F.exn ∧ N.sevm = F.sevm ∧
      CursorOK code c N next ∧
      next.f = caller ∧ next.K.map Cont.f = K ∧ N.devm.stack = adr.toB256 :: S := by
  have ready : F.sevm.benvStat.rules.delegatedCodeAddress (b.getCode 1) = none := by
    simp only [ForkRules.delegatedCodeAddress, nodeleg, ite_self]
  exact consumes_effective checked layout checks ok tree state ptr lower space ready
    continuations success fork

/-- An actual checked recovery helper before a later SSTORE returns a native
answer into its original caller continuation. The final frame outcome is
arbitrary. The structural SSTORE-freedom check concerns the helper source,
including its rejected branches; it asserts no authentication fact. -/
theorem consumes_toward_sstore
    (checked : Cert.check code c = true) (checks : ReturnChecks layout)
    {F target : Exec.Deriv} {κ : Cursor} {b : Devm} {M : Mem} {G n : Nat}
    {p placeholder s r v digest ret : B256} {S : List B256}
    {caller : SFunc} {K : List SFunc}
    (ok : CursorOK code c F κ) (tree : κ.f = entry layout)
    (state : F.devm = St b (placeholder :: s :: r :: v :: digest :: ret :: S) M G)
    (ptr : PtrMem p n M) (lower : 96 ≤ p.toNat) (space : p.toNat + 160 < 2 ^ 256)
    (nodeleg : getDelegatedCodeAddress (b.getCode 1) = none)
    (continuations : κ.K.map Cont.f = caller :: K)
    (free : (entry layout).sstoreFreeIn [] = true)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (fork : NeutralFork F.sevm.benvStat.fork) :
    ∃ (call : CallOccurrenceStep F .staticcall) (parent child : Devm)
      (gas : Nat) (adr : Adr) (N : Exec.Deriv) (next : Cursor),
      let input := digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes
      let msg := callMsg call.occurrence.node.sevm parent gas 0
        call.occurrence.node.sevm.currentTarget 1 1 true true input
        (call.occurrence.node.devm.getCode 1) false
      call.occurrence.node.pc = F.pc + 75 ∧
      Exec.Deriv.ExecFreeUntil F call.occurrence.node ∧
      Exec.Deriv.ParentPrefix call.returned N ∧ Exec.Deriv.ParentPrefix N target ∧
      Ninst.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm, call.occurrence.node.devm⟩
        (.exec .staticcall) = .spawn (Frame.ofCall msg)
          (Resume.call parent p.toNat 32) (call.occurrence.node.pc + 1) ∧
      ProcessMessage msg call.occurrence.slot (.ok child) ∧ call.occurrence.slot = .none ∧
      (Frame.ofCall msg).enter = .done
        ((Frame.ofCall msg).settle (executePrecomp (initEvm (msg.withBenv msg.benv)) 1)) ∧
      gasEcrecover ≤ gas ∧ child.error.isSome = false ∧ child.output = adr.toB256.toBytes ∧
      ecrecoverOutput input = adr.toB256.toBytes ∧ adr ≠ 0 ∧
      call.returned.devm.returnData = adr.toB256.toBytes ∧
      CursorOK code c N next ∧ next.f = caller ∧ next.K.map Cont.f = K ∧
      N.devm.stack = adr.toB256 :: S := by
  obtain ⟨call, cursor, callPc, span, callLater, sameEnv, ⟨G0, line⟩,
      primitive, placed, tailTree, sameK⟩ :=
    recovery_call_cut_toward_sstore checked ok tree state path store fork.stateGas
  obtain ⟨Gc, nc, callState, callPtr⟩ := recovery_prefix_request ptr lower space line
  have callFork : NeutralFork call.occurrence.node.sevm.benvStat.fork := by
    rw [sameEnv]
    exact fork
  have callReady : call.occurrence.node.sevm.benvStat.rules.delegatedCodeAddress
      (b.getCode 1) = none := by
    simp only [ForkRules.delegatedCodeAddress, nodeleg, ite_self]
  have returnedSg : call.returned.sevm.benvStat.rules.stateGas = none := by
    rw [Cursor.parentStep_sevm call.edge]
    exact callFork.stateGas
  have tailFree : (tail layout).sstoreFreeIn [] = true := by
    have same : (entry layout).sstoreFreeIn [] = (tail layout).sstoreFreeIn [] := by rfl
    rw [same] at free
    exact free
  obtain ⟨N, next, returnSpan, later, finalPlaced, callerTree, callerK, returned⟩ :=
    placed.returnBeforeSstore_noStateGas checked (E := []) rfl callLater store returnedSg
      (by rw [tailTree]; exact tailFree) (by rw [sameK]; exact continuations)
  rw [tailTree, Cursor.parentStep_sevm call.edge] at returned
  obtain ⟨adr, nonzero, output, returnData, returnedStack, answered, callerStack⟩ :=
    recovery_answer_of_return checks call callState callPtr (recovery_memory_zero ptr lower space)
      lower space callReady callFork primitive returned
  have inputEq : (call.occurrence.node.devm.memory.read (32 + p).toNat 128).1 =
      digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes := by
    rw [callState, St.memory]
    exact recovery_memory_input ptr space
  have operands : (Gc.toB256 :: 1 :: (32 + p) :: 128 :: p :: 32 ::
      (32 + (32 + (32 + (32 + (32 + p))))) ::
      1 :: 0 :: placeholder :: s :: r :: v :: digest :: ret :: S) <<+
      call.occurrence.node.devm.stack := by
    rw [callState, St.stack]
    simpa only [List.append_nil] using pref_append _ []
  have localReady : call.occurrence.node.sevm.benvStat.rules.delegatedCodeAddress
      (call.occurrence.node.devm.getCode 1) = none := by
    rw [callState]
    exact callReady
  have outputEq : ecrecoverOutput
      (digest.toBytes ++ (255 &&& v).toBytes ++ r.toBytes ++ s.toBytes) = adr.toB256.toBytes := by
    rw [← recovery_memory_input ptr space]
    exact output
  obtain ⟨parent, child, gas, spawned, process, emptySlot, native, paid, clean, childOutput⟩ :=
    actual_native_answer call operands callFork.stateGas localReady ⟨_, returnedStack⟩ inputEq outputEq
  exact ⟨call, parent, child, gas, adr, N, next, callPc, span, returnSpan, later,
    spawned, process, emptySlot, native, paid, clean, childOutput, outputEq,
    nonzero, returnData, finalPlaced, callerTree, callerK, callerStack⟩

end Blanc.Lift.EcrecoverCall
