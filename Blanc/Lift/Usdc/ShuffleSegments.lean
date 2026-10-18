import Blanc.Lift.ShuffleSkip
import Blanc.Lift.CallSiteChildren
import Blanc.Lift.Usdc.Impl.Cert

/-!
# USDC's in-frame shuffle segments (route C, theorem C3)

The signed entry points of the USDC implementation (FiatTokenV2_2) spend most of their
instructions on hashing and ABI encoding inside the current function.  Each segment below is
crossed by one kernel decision of the shuffle checker (`Blanc/Lift/ShuffleSkip.lean`), stated as
`seg_*_check`, and read back as a walk step `ric_seg_*`: a cut run of the segment's first tree from
`St b (x₀ :: … :: R) M G` reaches its last node from a state with `b`'s world state and the stack
the statement names.  Input words are `xᵢ`; computed words are fresh variables `uⱼ`; `R` is
untouched.

* the inline EIP-712 struct digests of entries 90, 95 and 89, up to the call of
  `_requireValidSignature` (entry 111);
* permit (entries 8, 80 and 9): the permit digest up to entry 79, the calldata encoding up to the
  signature-bytes copy loop, the loop's exit up to the `DELEGATECALL`, and from the
  `DELEGATECALL`'s result up to `_approve` (entry 81).  The copy loop itself and the
  `DELEGATECALL` are not shuffle segments.

Every `REVERT` arm inside a segment is pruned by the checker.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc.Lift Impl

/-- The shuffle check of entry 90 (`transferWithAuthorization` body): the inline EIP-712 struct
digest, from the return of `_requireValidAuthorization` (entry 112) to the call of
`_requireValidSignature` (entry 111). -/
theorem seg_e90_check : shuffle cert.prog cert.entries [] (.callNext 111 t_467d_c90) 0x4be6 1000
    0x4b55
    (argFrame 7) (t_4b55_c90) = some (some [.lit (Nat.toB256 0x4e88), .arg 0, .unk, .arg 6, .lit
        (Nat.toB256 0x467d), .arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6]) := by
  decide +kernel

/-- **Walk step over entry 90 (`transferWithAuthorization` body): the inline EIP-712 struct digest,
from the return of `_requireValidAuthorization` (entry 112) to the call of `_requireValidSignature`
(entry 111).** -/
theorem ric_seg_e90 {sevm : Sevm} {C : List Nat} {r : Seg}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 x3 x4 x5 x6 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) M G)
        (t_4b55_c90) r) :
    ∃ b' u0 M' G', b'.state = b.state ∧
      SFunc.RunCutP P cert.prog sevm C (St b' (Nat.toB256 0x4e88 :: x0 :: u0 :: x6 :: Nat.toB256 0x467d
        :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) M' G') (.callNext 111 t_467d_c90) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle hP (X := [x0, x1, x2, x3, x4, x5, x6]) fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_e90_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

/-- The shuffle check of entry 95 (`receiveWithAuthorization` body): the inline struct digest, from
the return of entry 112 to the call of entry 111. -/
theorem seg_e95_check : shuffle cert.prog cert.entries [] (.callNext 111 t_467d_c95) 0x467c 1000
    0x45eb
    (argFrame 7) (t_45eb_c95) = some (some [.lit (Nat.toB256 0x4e88), .arg 0, .unk, .arg 6, .lit
        (Nat.toB256 0x467d), .arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6]) := by
  decide +kernel

/-- **Walk step over entry 95 (`receiveWithAuthorization` body): the inline struct digest, from the
return of entry 112 to the call of entry 111.** -/
theorem ric_seg_e95 {sevm : Sevm} {C : List Nat} {r : Seg}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 x3 x4 x5 x6 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) M G)
        (t_45eb_c95) r) :
    ∃ b' u0 M' G', b'.state = b.state ∧
      SFunc.RunCutP P cert.prog sevm C (St b' (Nat.toB256 0x4e88 :: x0 :: u0 :: x6 :: Nat.toB256 0x467d
        :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) M' G') (.callNext 111 t_467d_c95) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle hP (X := [x0, x1, x2, x3, x4, x5, x6]) fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_e95_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

/-- The shuffle check of entry 89 (`cancelAuthorization` body): the inline struct digest, from the
return of `abi.encodePacked(r, s, v)` (entry 110) to the call of entry 111. -/
theorem seg_e89_check : shuffle cert.prog cert.entries [] (.callNext 111 t_4ac3_c89) 0x4ac2 1000
    0x4a49
    (argFrame 3) (t_4a49_c89) = some (some [.lit (Nat.toB256 0x4e88), .arg 0, .unk, .arg 2, .lit
        (Nat.toB256 0x4ac3), .arg 0, .arg 1, .arg 2]) := by
  decide +kernel

/-- **Walk step over entry 89 (`cancelAuthorization` body): the inline struct digest, from the
return of `abi.encodePacked(r, s, v)` (entry 110) to the call of entry 111.** -/
theorem ric_seg_e89 {sevm : Sevm} {C : List Nat} {r : Seg}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P cert.prog sevm C (St b (x0 :: x1 :: x2 :: R) M G) (t_4a49_c89) r) :
    ∃ b' u0 M' G', b'.state = b.state ∧
      SFunc.RunCutP P cert.prog sevm C (St b' (Nat.toB256 0x4e88 :: x0 :: u0 :: x2 :: Nat.toB256 0x4ac3
        :: x0 :: x1 :: x2 :: R) M' G') (.callNext 111 t_4ac3_c89) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle hP (X := [x0, x1, x2]) fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_e89_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

/-- The shuffle check of entry 8 (`_permit`): the permit struct digest, from just after the nonce
store to the call of entry 79 (the typed-data hash). -/
theorem seg_e8digest_check : shuffle cert.prog cert.entries [] (.callNext 79 t_47d3_c8) 0x47d2 1000
    0x476c
    (argFrame 12) (SFunc.lineDrop 27 t_4738_c8) = some (some [.lit (Nat.toB256 0x508b), .unk, .arg
        5, .arg 6, .arg 7, .arg 8, .arg 9, .arg 10, .arg 11]) := by
  decide +kernel

/-- **Walk step over entry 8 (`_permit`): the permit struct digest, from just after the nonce store
to the call of entry 79 (the typed-data hash).** -/
theorem ric_seg_e8digest {sevm : Sevm} {C : List Nat} {r : Seg}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : B256} {R : List
        B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8
        :: x9 :: x10 :: x11 :: R) M G) (SFunc.lineDrop 27 t_4738_c8) r) :
    ∃ b' u0 M' G', b'.state = b.state ∧
      SFunc.RunCutP P cert.prog sevm C (St b' (Nat.toB256 0x508b :: u0 :: x5 :: x6 :: x7 :: x8 :: x9 ::
        x10 :: x11 :: R) M' G') (.callNext 79 t_47d3_c8) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle hP (X := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9,
      x10, x11]) fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_e8digest_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

/-- The shuffle check of entry 8: the ABI encoding of the signature check's calldata, from the
return of entry 79 to the head of the signature-bytes copy loop. -/
theorem seg_e8encode_check : shuffle cert.prog cert.entries [] (t_4848_c8) 0x4848 1000 0x47d3
    (argFrame 7) (t_47d3_c8) = some (some [.lit (Nat.toB256 0), .unk, .unk, .unk, .unk, .unk, .unk,
        .unk, .unk, .arg 2, .arg 0, .arg 6, .lit (Nat.toB256 0x6ccea652), .lit (Nat.toB256
        0x800c32eaa2a6c93cf4cb51794450ed77fbfbb172), .arg 0, .arg 2, .arg 3, .arg 4, .arg 5, .arg
        6]) := by
  decide +kernel

/-- **Walk step over entry 8: the ABI encoding of the signature check's calldata, from the return of
entry 79 to the head of the signature-bytes copy loop.** -/
theorem ric_seg_e8encode {sevm : Sevm} {C : List Nat} {r : Seg}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 x3 x4 x5 x6 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) M G)
        (t_47d3_c8) r) :
    ∃ b' u0 u1 u2 u3 u4 u5 u6 u7 M' G', b'.state = b.state ∧
      SFunc.RunCutP P cert.prog sevm C (St b' (Nat.toB256 0 :: u0 :: u1 :: u2 :: u3 :: u4 :: u5 :: u6
        :: u7 :: x2 :: x0 :: x6 :: Nat.toB256 0x6ccea652 :: Nat.toB256
        0x800c32eaa2a6c93cf4cb51794450ed77fbfbb172 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) M' G')
        (t_4848_c8) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle hP (X := [x0, x1, x2, x3, x4, x5, x6]) fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_e8encode_check rfl run
  carried_out hY h
  exact ⟨b', _, _, _, _, _, _, _, _, M', G', hs, h⟩

/-- The shuffle check of entry 8: from the copy loop's exit, both when the loop never iterates
(entry 8's own tree) and through the partial-word tail or the goto into entry 9, past the code-size
check, to the `DELEGATECALL`. -/
theorem seg_e8exit_check : shuffle cert.prog cert.entries [9] (SFunc.lineDrop 3 t_48ac_c9) 0x48af
    1000 0x4860
    (argFrame 14) (t_4860_c8) = some (some [.unk, .arg 13, .unk, .unk, .unk, .lit (Nat.toB256 0x20),
        .unk, .arg 12, .arg 13]) := by
  decide +kernel

/-- **Walk step over entry 8: from the copy loop's exit, both when the loop never iterates (entry
8's own tree) and through the partial-word tail or the goto into entry 9, past the code-size check,
to the `DELEGATECALL`.** -/
theorem ric_seg_e8exit {sevm : Sevm} {C : List Nat} {r : Seg}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (fork : CoveredFork sevm.benvStat.fork) (hC : 9 ∉ C) {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
        x13 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8
        :: x9 :: x10 :: x11 :: x12 :: x13 :: R) M G) (t_4860_c8) r) :
    ∃ b' u0 u1 u2 u3 u4 M' G', b'.state = b.state ∧
      SFunc.RunCutP P cert.prog sevm C (St b' (u0 :: x13 :: u1 :: u2 :: u3 :: Nat.toB256 0x20 :: u4 ::
        x12 :: x13 :: R) M' G') (SFunc.lineDrop 3 t_48ac_c9) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle hP (X := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9,
      x10, x11, x12, x13]) fork
    (fun k hk => by rw [List.mem_singleton] at hk; subst hk; exact hC) seg_e8exit_check rfl run
  carried_out hY h
  exact ⟨b', _, _, _, _, _, M', G', hs, h⟩

/-- The shuffle check of entry 80 (the copy loop): the same span from the loop's exit after one or
more iterations. -/
theorem seg_e80exit_check : shuffle cert.prog cert.entries [9] (SFunc.lineDrop 3 t_48ac_c9) 0x48af
    1000 0x4860
    (argFrame 14) (t_4860_c80) = some (some [.unk, .arg 13, .unk, .unk, .unk, .lit (Nat.toB256
        0x20), .unk, .arg 12, .arg 13]) := by
  decide +kernel

/-- **Walk step over entry 80 (the copy loop): the same span from the loop's exit after one or more
iterations.** -/
theorem ric_seg_e80exit {sevm : Sevm} {C : List Nat} {r : Seg}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (fork : CoveredFork sevm.benvStat.fork) (hC : 9 ∉ C) {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
        x13 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8
        :: x9 :: x10 :: x11 :: x12 :: x13 :: R) M G) (t_4860_c80) r) :
    ∃ b' u0 u1 u2 u3 u4 M' G', b'.state = b.state ∧
      SFunc.RunCutP P cert.prog sevm C (St b' (u0 :: x13 :: u1 :: u2 :: u3 :: Nat.toB256 0x20 :: u4 ::
        x12 :: x13 :: R) M' G') (SFunc.lineDrop 3 t_48ac_c9) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle hP (X := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9,
      x10, x11, x12, x13]) fork
    (fun k hk => by rw [List.mem_singleton] at hk; subst hk; exact hC) seg_e80exit_check rfl run
  carried_out hY h
  exact ⟨b', _, _, _, _, _, M', G', hs, h⟩

/-- The shuffle check of entry 9: from just after the `DELEGATECALL`, past its success check, the
return-size check and the signature-validity check (each failing arm reverts), to the call of
`_approve` (entry 81). -/
theorem seg_e9call_check : shuffle cert.prog cert.entries [] (.callNext 81 t_494e_c9) 0x494d 1000
    0x48b0
    (argFrame 10) (SFunc.lineDrop 4 t_48ac_c9) = some (some [.lit (Nat.toB256 0x3e18), .arg 7, .arg
        8, .arg 9, .lit (Nat.toB256 0x494e), .arg 4, .arg 5, .arg 6, .arg 7, .arg 8, .arg 9]) := by
  decide +kernel

/-- **Walk step over entry 9: from just after the `DELEGATECALL`, past its success check, the
return-size check and the signature-validity check (each failing arm reverts), to the call of
`_approve` (entry 81).** -/
theorem ric_seg_e9call {sevm : Sevm} {C : List Nat} {r : Seg}
    {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') (fork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : B256} {R : List B256}
    {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8
        :: x9 :: R) M G) (SFunc.lineDrop 4 t_48ac_c9) r) :
    ∃ b' M' G', b'.state = b.state ∧
      SFunc.RunCutP P cert.prog sevm C (St b' (Nat.toB256 0x3e18 :: x7 :: x8 :: x9 :: Nat.toB256 0x494e
        :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) M' G') (.callNext 81 t_494e_c9) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle hP (X := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9])
      fork
    (fun _ hk => absurd hk List.not_mem_nil) seg_e9call_check rfl run
  carried_out hY h
  exact ⟨b', M', G', hs, h⟩

end Blanc.Lift.Usdc
