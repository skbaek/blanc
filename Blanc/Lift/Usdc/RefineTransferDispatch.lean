import Blanc.Lift.Usdc.RefineTransferCallees
import Blanc.Lift.InvWalkDispatch

/-!
# USDC's dispatcher and the selector wrappers of the transfer and allowance family
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

theorem RunCut.ite_left {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
    {C : List Nat} {d : Devm} {r : Seg} {c : Prop} [Decidable c] {f g : SFunc} (hc : c)
    (h : SFunc.RunCutP P fs sevm C d (if c then f else g) r) : SFunc.RunCutP P fs sevm C d f r := by
  rwa [ite_eq_left hc] at h

theorem RunCut.ite_right {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
    {C : List Nat} {d : Devm} {r : Seg} {c : Prop} [Decidable c] {f g : SFunc} (hc : ¬ c)
    (h : SFunc.RunCutP P fs sevm C d (if c then f else g) r) : SFunc.RunCutP P fs sevm C d g r := by
  rwa [ite_eq_right hc] at h

/-- One comparison of the dispatcher's binary search on a known selector. -/
macro "idisp " h:ident : tactic => `(tactic| first
  | (have h' := ric_cmp_gt $h; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (replace $h:ident := RunCut.ite_left (by decide) $h)
     | (replace $h:ident := RunCut.ite_right (by decide) $h))
  | (have h' := ric_cmp_eq List.not_mem_nil rfl $h; clear $h; obtain ⟨_, $h:ident⟩ := h'
     first
     | (replace $h:ident := RunCut.ite_left (by decide) $h)
     | (replace $h:ident := RunCut.ite_right (by decide) $h))
  | (have h' := ric_dest $h; clear $h; obtain ⟨_, $h:ident⟩ := h'))

theorem selector_word (sevm : Sevm) :
    Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat = Sevm.selector sevm :=
  rfl

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

theorem lit36 : Bytes.toB256 [32] + Bytes.toB256 [4] = 36 := by decide

/-- **The frame of `transfer(to, value)`** at its pc-0 tree: the guards it passed and the
storage it leaves at its owner. -/
theorem frame_transfer {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm = 0xa9059cbb)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get
        (balSlot (Sevm.dataWord sevm 4).toAdr)) = false ∧
      sevm.caller ≠ 0 ∧ (Sevm.dataWord sevm 4).toAdr ≠ 0 ∧
      (Sevm.dataWord sevm 36).toNat ≤
        balanceBits ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)) ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)) = false ∧
      frozenBit ((debitStor (Devm.getStor b sevm.currentTarget) sevm.caller
        (Sevm.dataWord sevm 36).toNat).get (balSlot (Sevm.dataWord sevm 4).toAdr)) = false ∧
      balanceBits ((debitStor (Devm.getStor b sevm.currentTarget) sevm.caller
        (Sevm.dataWord sevm 36).toNat).get (balSlot (Sevm.dataWord sevm 4).toAdr)) +
          (Sevm.dataWord sevm 36).toNat ≤ 2 ^ 255 - 1 ∧
      Devm.getStor post sevm.currentTarget =
        creditStor (debitStor (Devm.getStor b sevm.currentTarget) sevm.caller
          (Sevm.dataWord sevm 36).toNat) (Sevm.dataWord sevm 4).toAdr
          (Sevm.dataWord sevm 36).toNat := by
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
  icall h hc 37 t_2fa6_c37
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, b1, M1, G1, e, s1⟩ := e37_inv fork hc
  cases e
  clear hc
  repeat istep h
  have sp := congrFun (ric_return_getStor h) sevm.currentTarget
  clear h
  have l4 : Bytes.toB256 [4] = 4 := by decide
  simp only [lit36] at d5 d7 d8 s1
  simp only [l4, word_ff20, toAdr_toB256] at d2 d4 d5 d7 d8 s1
  exact ⟨d1, d2, d3, d4, d5, d6, d7, d8, by rw [sp, s1]⟩

/-- **The frame of `approve(spender, value)`** at its pc-0 tree. -/
theorem frame_approve {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm = 0x095ea7b3)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧ sevm.caller ≠ 0 ∧
      (Sevm.dataWord sevm 4).toAdr ≠ 0 ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
          (Sevm.dataWord sevm 36) := by
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
  icall h hc 71 t_12d3_c71
  obtain ⟨d1, d2, d3, b1, M1, G1, e, s1⟩ := e71_inv fork hc
  cases e
  clear hc
  repeat istep h
  have sp := congrFun (ric_return_getStor h) sevm.currentTarget
  clear h
  have l4 : Bytes.toB256 [4] = 4 := by decide
  simp only [lit36] at *
  simp only [l4, word_ff20, toAdr_toB256] at *
  exact ⟨d1, d2, d3, by rw [sp, s1]⟩

/-- **The frame of `increaseAllowance(spender, increment)`** at its pc-0 tree. -/
theorem frame_increaseAllowance {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm = 0x39509351)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧ sevm.caller ≠ 0 ∧
      (Sevm.dataWord sevm 4).toAdr ≠ 0 ∧
      ((Devm.getStor b sevm.currentTarget).get
        (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)).toNat +
          (Sevm.dataWord sevm 36).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
          (Nat.toB256 (((Devm.getStor b sevm.currentTarget).get
            (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)).toNat +
              (Sevm.dataWord sevm 36).toNat)) := by
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
  icall h hc 58 t_1d6a_c58
  obtain ⟨d1, d2, d3, d4, b1, M1, G1, e, s1⟩ := e58_inv fork hc
  cases e
  clear hc
  repeat istep h
  have sp := congrFun (ric_return_getStor h) sevm.currentTarget
  clear h
  have l4 : Bytes.toB256 [4] = 4 := by decide
  simp only [lit36] at *
  simp only [l4, word_ff20, toAdr_toB256] at *
  exact ⟨d1, d2, d3, d4, by rw [sp, s1]⟩

/-- **The frame of `decreaseAllowance(spender, decrement)`** at its pc-0 tree. -/
theorem frame_decreaseAllowance {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm = 0xa457c2d7)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧ sevm.caller ≠ 0 ∧
      (Sevm.dataWord sevm 4).toAdr ≠ 0 ∧
      (Sevm.dataWord sevm 36).toNat ≤ ((Devm.getStor b sevm.currentTarget).get
        (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
          (Nat.toB256 (((Devm.getStor b sevm.currentTarget).get
            (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)).toNat -
              (Sevm.dataWord sevm 36).toNat)) := by
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
  icall h hc 36 t_2f0e_c36
  obtain ⟨d1, d2, d3, d4, b1, M1, G1, e, s1⟩ := e36_inv fork hc
  cases e
  clear hc
  repeat istep h
  have sp := congrFun (ric_return_getStor h) sevm.currentTarget
  clear h
  have l4 : Bytes.toB256 [4] = 4 := by decide
  simp only [lit36] at *
  simp only [l4, word_ff20, toAdr_toB256] at *
  exact ⟨d1, d2, d3, d4, by rw [sp, s1]⟩

/-- **The frame of `transferFrom(from, to, value)`** at its pc-0 tree. -/
theorem frame_transferFrom {post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm = 0x23b872dd)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get
        (balSlot (Sevm.dataWord sevm 4).toAdr)) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get
        (balSlot (Sevm.dataWord sevm 36).toAdr)) = false ∧
      (Sevm.dataWord sevm 68).toNat ≤ ((Devm.getStor b sevm.currentTarget).get
        (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller)).toNat ∧
      (Sevm.dataWord sevm 4).toAdr ≠ 0 ∧ (Sevm.dataWord sevm 36).toAdr ≠ 0 ∧
      (Sevm.dataWord sevm 68).toNat ≤ balanceBits ((Devm.getStor b sevm.currentTarget).get
        (balSlot (Sevm.dataWord sevm 4).toAdr)) ∧
      frozenBit ((debitStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 68).toNat).get (balSlot (Sevm.dataWord sevm 36).toAdr)) = false ∧
      balanceBits ((debitStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 68).toNat).get (balSlot (Sevm.dataWord sevm 36).toAdr)) +
          (Sevm.dataWord sevm 68).toNat ≤ 2 ^ 255 - 1 ∧
      (Sevm.dataWord sevm 68).toNat ≤ ((creditStor (debitStor (Devm.getStor b sevm.currentTarget)
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 68).toNat) (Sevm.dataWord sevm 36).toAdr
        (Sevm.dataWord sevm 68).toNat).get (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller)).toNat ∧
      Devm.getStor post sevm.currentTarget =
        (creditStor (debitStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr
          (Sevm.dataWord sevm 68).toNat) (Sevm.dataWord sevm 36).toAdr
          (Sevm.dataWord sevm 68).toNat).set (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller)
          (Nat.toB256 (((creditStor (debitStor (Devm.getStor b sevm.currentTarget)
            (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 68).toNat) (Sevm.dataWord sevm 36).toAdr
            (Sevm.dataWord sevm 68).toNat).get
            (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller)).toNat -
              (Sevm.dataWord sevm 68).toNat)) := by
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
  icall h hc 68 t_1437_c68
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, b1, M1, G1, e, s1⟩ := e68_inv fork hc
  cases e
  clear hc
  repeat istep h
  have sp := congrFun (ric_return_getStor h) sevm.currentTarget
  clear h
  have l68 : Bytes.toB256 [64] + Bytes.toB256 [4] = 68 := by decide
  have l36 : Bytes.toB256 [4] + Bytes.toB256 [32] = 36 := by decide
  have l4 : Bytes.toB256 [4] = 4 := by decide
  simp only [l68, l36] at d3 d4 d5 d6 d7 d8 d9 d10 d11 s1
  simp only [l4, ff20_and_word, toAdr_toB256] at d3 d4 d5 d6 d7 d8 d9 d10 d11 s1
  exact ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, by rw [sp, s1]⟩

end Blanc.Lift.Usdc
