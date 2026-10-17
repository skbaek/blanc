import Blanc.Lift.Usdc.RefineSignedPermitCore
import Blanc.Lift.Usdc.RefineTransferDispatch

/-!
# The frames of `permit` and `cancelAuthorization` (U6e4)

From the implementation's pc-0 tree on a known selector: the dispatcher, the wrapper's ABI decoding
(the `bytes` decodings by two new shuffle segments, `seg_w149_check` and `seg_w136_check`) and the
body (`RefineSignedPermitCore.lean`): the guards a successful frame passed and the storage it leaves
at its owner (`permitStor`, `cancelStor`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The shuffle check of `permit(…, bytes)`'s wrapper (entry 149): the `bytes` argument's ABI decoding,
from its head check to the call of the body (entry 41). -/
theorem seg_w149_check : shuffle cert.prog cert.entries [] (.callNext 41 t_0489_c149) 0xc59 1000 0xbe5
    (argFrame 10) t_0be5_c149 = some (some [.lit (Nat.toB256 0x2e53), .unk, .arg 4, .arg 5, .arg 6,
      .arg 7, .arg 8, .arg 9]) := by
  decide +kernel

theorem ric_seg_w149 {C : List Nat} {r : Seg} (fork : CoveredFork sevm.benvStat.fork)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : B256} {R : List B256}
    (run : SFunc.RunCut cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 ::
      x9 :: R) M G) t_0be5_c149 r) :
    ∃ b' u0 M' G', b'.state = b.state ∧ SFunc.RunCut cert.prog sevm C
      (St b' (Nat.toB256 0x2e53 :: u0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) M' G')
      (.callNext 41 t_0489_c149) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle (X := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9])
    fork (fun _ hk => absurd hk List.not_mem_nil) seg_w149_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

/-- The shuffle check of `cancelAuthorization(…, bytes)`'s wrapper (entry 136): the `bytes` argument's
ABI decoding, from its head check to the call of the body (entry 28). -/
theorem seg_w136_check : shuffle cert.prog cert.entries [] (.callNext 28 t_0489_c136) 0xe77 1000 0xe03
    (argFrame 8) t_0e03_c136 = some (some [.lit (Nat.toB256 0x3498), .unk, .arg 4, .arg 5, .arg 6,
      .arg 7]) := by
  decide +kernel

/-- A successful `STOP` halt keeps the base's storage. -/
theorem ric_stop_getStor {fs : List SFunc} {C : List Nat} {post : Devm}
    (run : SFunc.RunCut fs sevm C (St b S M G) (.last .stop) (.done (.halted post))) :
    Devm.getStor post = Devm.getStor b := by
  cases run with
  | last hl =>
      cases hl
      rfl

theorem lit4_32 : Bytes.toB256 [4] + Bytes.toB256 [32] = 36 := by decide
theorem lit4_64 : Bytes.toB256 [4] + Bytes.toB256 [64] = 68 := by decide
theorem lit4 : Bytes.toB256 [4] = 4 := by decide

/-- The storage a committed permit leaves: the owner's nonce bumped, the allowance written. -/
def permitStor (σ : Stor) (o s : Adr) (v : B256) : Stor :=
  (σ.set (nonceSlot o) (σ.get (nonceSlot o) + 1)).set (allowSlot o s) v

/-- **The frame of `permit(owner, spender, value, deadline, v, r, s)`** at its pc-0 tree. -/
theorem frame_permitVrs {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode usdcLib = Lib.code) (sel : Sevm.selector sevm = 0xd505accf)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      (Sevm.dataWord sevm 4).toAdr ≠ 0 ∧ (Sevm.dataWord sevm 36).toAdr ≠ 0 ∧
      Devm.getStor post sevm.currentTarget = permitStor (Devm.getStor b sevm.currentTarget)
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  iterate 4 istep h
  rw [selector_word, sel] at h
  repeat idisp h
  repeat istep h
  ibranch h c3
  repeat istep h
  icallP h hc 24 t_36a2_c24
  obtain ⟨p0, d1, d2, b1, M1, G1, e, s1⟩ := e24_inv fork hcode hc
  cases e
  clear hc
  repeat istep h
  have sp := congrFun (ric_stop_getStor h) sevm.currentTarget
  clear h
  simp only [lit4_32, lit4_64] at d1 d2 s1
  simp only [lit4, ff20_word, toAdr_toB256] at d1 d2 s1
  exact ⟨p0, d1, d2, by rw [sp, s1]; rfl⟩

/-- **The frame of `permit(owner, spender, value, deadline, signature)`** at its pc-0 tree. -/
theorem frame_permitBytes {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode usdcLib = Lib.code) (sel : Sevm.selector sevm = 0x9fd5a6cf)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      (Sevm.dataWord sevm 4).toAdr ≠ 0 ∧ (Sevm.dataWord sevm 36).toAdr ≠ 0 ∧
      Devm.getStor post sevm.currentTarget = permitStor (Devm.getStor b sevm.currentTarget)
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  iterate 4 istep h
  rw [selector_word, sel] at h
  repeat idisp h
  repeat istepX h
  ibranch h c3
  repeat istepX h
  ibranch h c4
  obtain ⟨b1, u0, M1, G1, hs1, h⟩ := ric_seg_w149 fork h
  icallP h hc 41 t_2e53_c41
  obtain ⟨p0, d1, d2, b2, M2, G2, e, s2⟩ :=
    e41_inv fork (by rw [getCode_of_state hs1]; exact hcode) hc
  cases e
  clear hc
  repeat istep h
  have sp := congrFun (ric_stop_getStor h) sevm.currentTarget
  clear h
  rw [congrFun (getStor_of_state hs1)] at p0 s2
  simp only [lit4_32, lit4_64] at d1 d2 s2
  simp only [lit4, ff20_word, toAdr_toB256] at d1 d2 s2
  exact ⟨p0, d1, d2, by rw [sp, s2]; rfl⟩

theorem ric_seg_w136 {C : List Nat} {r : Seg} (fork : CoveredFork sevm.benvStat.fork)
    {x0 x1 x2 x3 x4 x5 x6 x7 : B256} {R : List B256}
    (run : SFunc.RunCut cert.prog sevm C (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) M G)
      t_0e03_c136 r) :
    ∃ b' u0 M' G', b'.state = b.state ∧ SFunc.RunCut cert.prog sevm C
      (St b' (Nat.toB256 0x3498 :: u0 :: x4 :: x5 :: x6 :: x7 :: R) M' G')
      (.callNext 28 t_0489_c136) r := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := ric_shuffle (X := [x0, x1, x2, x3, x4, x5, x6, x7])
    fork (fun _ hk => absurd hk List.not_mem_nil) seg_w136_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

/-- The storage a committed cancellation leaves: the authorization marked used. -/
def cancelStor (σ : Stor) (a : Adr) (n : B256) : Stor :=
  σ.set (authSlot a n) (authMark (σ.get (authSlot a n)))

/-- **The frame of `cancelAuthorization(authorizer, nonce, v, r, s)`** at its pc-0 tree. -/
theorem frame_cancelVrs {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode usdcLib = Lib.code) (sel : Sevm.selector sevm = 0x5a049a70)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      boolBit ((Devm.getStor b sevm.currentTarget).get
        (authSlot (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36))) = false ∧
      Devm.getStor post sevm.currentTarget = cancelStor (Devm.getStor b sevm.currentTarget)
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  iterate 4 istep h
  rw [selector_word, sel] at h
  repeat idisp h
  repeat istep h
  ibranch h c3
  repeat istep h
  icallC h hc 52 t_2a20_c52
  obtain ⟨p0, d1, b1, M1, G1, e, s1⟩ := e52_inv fork hcode hc
  cases e
  clear hc
  repeat istep h
  have sp := congrFun (ric_stop_getStor h) sevm.currentTarget
  clear h
  simp only [lit4_32] at d1 s1
  simp only [lit4, word_ff20, toAdr_toB256] at d1 s1
  exact ⟨p0, d1, by rw [sp, s1]; rfl⟩

/-- **The frame of `cancelAuthorization(authorizer, nonce, signature)`** at its pc-0 tree. -/
theorem frame_cancelBytes {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode usdcLib = Lib.code) (sel : Sevm.selector sevm = 0xb7b72899)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      boolBit ((Devm.getStor b sevm.currentTarget).get
        (authSlot (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36))) = false ∧
      Devm.getStor post sevm.currentTarget = cancelStor (Devm.getStor b sevm.currentTarget)
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  iterate 4 istep h
  rw [selector_word, sel] at h
  repeat idisp h
  repeat istep h
  ibranch h c3
  repeat istep h
  ibranch h c4
  obtain ⟨b1, u0, M1, G1, hs1, h⟩ := ric_seg_w136 fork h
  icallC h hc 28 t_3498_c28
  obtain ⟨p0, d1, b2, M2, G2, e, s2⟩ :=
    e28_inv fork (by rw [getCode_of_state hs1]; exact hcode) hc
  cases e
  clear hc
  repeat istep h
  have sp := congrFun (ric_stop_getStor h) sevm.currentTarget
  clear h
  rw [congrFun (getStor_of_state hs1)] at p0 d1 s2
  simp only [lit4_32] at d1 s2
  simp only [lit4, word_ff20, toAdr_toB256] at d1 s2
  exact ⟨p0, d1, by rw [sp, s2]; rfl⟩

end Blanc.Lift.Usdc
