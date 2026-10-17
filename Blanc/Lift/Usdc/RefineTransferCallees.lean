import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.InvWalkStep
import Blanc.Lift.Usdc.FootprintLedger

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

theorem lit10 : Bytes.toB256 [10] = 10 := by decide

theorem ff20_word (x : B256) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& x) = x.toAdr.toB256 :=
  ff20_and_word x

theorem lit9 : Bytes.toB256 [9] = 9 := by decide
theorem lit1 : Bytes.toB256 [1] = 1 := by decide
theorem lit255 : (Bytes.toB256 [255]).toNat = 255 := by decide

/-- The callees of the transfer and allowance family: none halts the frame. -/
def familyCallees : List Nat := [7, 12, 13, 36, 37, 58, 68, 71, 81, 83, 92, 93, 96, 98, 99, 100,
  102, 115, 119]

theorem familyCallees_noHalt : NoHaltSet cert.prog familyCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `familyCallees` from a cut run `h`; the callee run is
`hc`, the continuation `h`. -/
macro "icall " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry familyCallees_noHalt
      (by decide : $k ∈ familyCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

theorem litMask255 : Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = Nat.toB256 (2 ^ 255 - 1) := by decide

/-- `require(!_isBlacklisted(a))`, as its flag reaches the branch. -/
theorem frozen_false_of_check {w : B256}
    (h : B256.eqCheck (B256.eqCheck 1 (w >>> 255)) 0 ≠ 0) : frozenBit w = false :=
  by
  unfold frozenBit
  rw [decide_eq_false_iff_not, Nat.not_le]
  exact toNat_lt_of_shr_ne_one (ne_of_eqCheck_eq_zero (eq_zero_of_iszero_ne_zero h)).symm

/-- `whenNotPaused`'s test of the byte at offset 20 of slot 1. -/
theorem flag20_false_of_check {w : B256}
    (h : B256.eqCheck (Bytes.toB256 [255] &&&
      w / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) 0 ≠ 0) :
    flag20 w = false := by
  have e := congrArg B256.toNat (eq_zero_of_iszero_ne_zero h)
  have d0 : Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≠ 0 := by
    decide
  have dn : (Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toNat =
    2 ^ 160 := by decide
  have fn : (Bytes.toB256 [255]).toNat = 2 ^ 8 - 1 := by decide
  rw [Blanc.B256.toNat_and, B256.toNat_div d0, dn, fn, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, B256.toNat_zero] at e
  unfold flag20
  rw [decide_eq_false_iff_not, not_not]
  exact e

theorem toNat_low255 : (Nat.toB256 (2 ^ 255 - 1)).toNat = 2 ^ 255 - 1 :=
  B256.toNat_toB256_of_lt (by decide)

theorem low255_and_toNat (w : B256) :
    (Nat.toB256 (2 ^ 255 - 1) &&& w).toNat = balanceBits w := by
  rw [Blanc.B256.toNat_and, toNat_low255, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-- `_setBalance(a, _balanceOf(a) - v)`'s storage. -/
def debitStor (σ : Stor) (a : Adr) (v : Nat) : Stor :=
  σ.set (balSlot a) (Nat.toB256 (balanceBits (σ.get (balSlot a)) - v))

/-- `_setBalance(a, _balanceOf(a) + v)`'s storage. -/
def creditStor (σ : Stor) (a : Adr) (v : Nat) : Stor :=
  σ.set (balSlot a) (Nat.toB256 (balanceBits (σ.get (balSlot a)) + v))

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **Entry 83, `_isBlacklisted(a)`**: reads the packed word of `a` and returns its top bit
compared with `1`. -/
theorem e83_inv {a ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_3f6a_c83 o) :
    ∃ b' M' G', o = .returned (St b' (B256.eqCheck 1
        (b.getStorVal sevm.currentTarget (balSlot a.toAdr) >>> 255) :: S) M' G') ∧
      Devm.getStor b' = Devm.getStor b := by
  have h := run.cut
  clear run
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  rw [keccak_scratch, ff20_word, lit9, lit1, lit255] at *
  exact ⟨_, _, _, rfl, funext fun x => afterSload_getStor _ _ _ x⟩

/-- **Entry 96, `_balanceOf(a)`**: the low 255 bits of `a`'s packed word. -/
theorem e96_inv {a ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (a :: ret :: S) M G) t_41da_c96 o) :
    ∃ b' M' G', o = .returned (St b' ((Nat.toB256 (2 ^ 255 - 1) &&&
        b.getStorVal sevm.currentTarget (balSlot a.toAdr)) :: S) M' G') ∧
      Devm.getStor b' = Devm.getStor b := by
  have h := run.cut
  clear run
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  rw [keccak_scratch, ff20_word, lit9, litMask255] at *
  exact ⟨_, _, _, rfl, funext fun x => afterSload_getStor _ _ _ x⟩

/-- **Entry 100, SafeMath `sub`**. -/
theorem e100_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_4163_c100 o) :
    x.toNat ≤ y.toNat ∧ ∃ G', o = .returned (St b ((y - x) :: S) M G') := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact ⟨toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero c), _, rfl⟩

/-- **Entry 98, SafeMath `add`** (its tail is entry 7). -/
theorem e98_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_43b5_c98 o) :
    x.toNat + y.toNat < 2 ^ 256 ∧ ∃ G', o = .returned (St b ((x + y) :: S) M G') := by
  have h := run.cut
  clear run
  repeat istep h
  rcases ric_branchTo (g := t_4429_c7) (List.not_mem_nil) rfl h with ⟨c, _, h⟩ | ⟨c, _, h⟩
  · exact (SFunc.RunCutP.false_of_noOk h (by decide)).elim
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact ⟨(add_nof_of_ltCheck (eq_zero_of_iszero_ne_zero c)).1, _, rfl⟩

/-- **Entry 99, `_setBalance(a, v)`**. -/
theorem e99_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_4430_c99 o) :
    x.toNat ≤ 2 ^ 255 - 1 ∧
      frozenBit (b.getStorVal sevm.currentTarget (balSlot y.toAdr)) = false ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          (Devm.getStor b sevm.currentTarget).set (balSlot y.toAdr) x := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  rcases ric_call (g := t_3f6a_c83) rfl h with ⟨_, ⟨D, hc, h⟩ | ⟨D, hc, _⟩⟩
  · obtain ⟨b', M', G', e, hs⟩ := e83_inv fork hc
    cases e
    clear hc
    repeat istep h
    ibranch h c2
    repeat istep h
    obtain ⟨_, e⟩ := ric_ret h
    cases e
    rw [keccak_scratch, word_ff20, lit9, litMask255] at *
    refine ⟨?_, frozen_false_of_check c2, _, _, _, rfl, ?_⟩
    · have := le_of_gt_check c1
      rwa [toNat_low255] at this
    · rw [afterSstore_getStor_self, hs]
      rfl
  · obtain ⟨_, _, _, e, _⟩ := e83_inv fork hc
    cases e

/-- **Entry 93, `_transfer(from, to, value)`**. -/
theorem e93_inv {x y z ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: z :: ret :: S) M G) t_3f98_c93 o) :
    z.toAdr ≠ 0 ∧ y.toAdr ≠ 0 ∧
      x.toNat ≤ balanceBits ((Devm.getStor b sevm.currentTarget).get (balSlot z.toAdr)) ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot z.toAdr)) = false ∧
      frozenBit ((debitStor (Devm.getStor b sevm.currentTarget) z.toAdr x.toNat).get
        (balSlot y.toAdr)) = false ∧
      balanceBits ((debitStor (Devm.getStor b sevm.currentTarget) z.toAdr x.toNat).get
        (balSlot y.toAdr)) + x.toNat ≤ 2 ^ 255 - 1 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' sevm.currentTarget =
        creditStor (debitStor (Devm.getStor b sevm.currentTarget) z.toAdr x.toNat) y.toAdr
          x.toNat := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  repeat istep h
  icall h hc 96 t_41da_c96
  obtain ⟨b1, M1, G1, e, s1⟩ := e96_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c3
  repeat istep h
  icall h hc 96 t_41da_c96
  obtain ⟨b2, M2, G2, e, s2⟩ := e96_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 100 t_4163_c100
  obtain ⟨c4, G3, e⟩ := e100_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 99 t_4430_c99
  obtain ⟨c5, c6, b4, M4, G4, e, s4⟩ := e99_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 96 t_41da_c96
  obtain ⟨b5, M5, G5, e, s5⟩ := e96_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 98 t_43b5_c98
  obtain ⟨c7, G6, e⟩ := e98_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 99 t_4430_c99
  obtain ⟨c8, c9, b7, M7, G7, e, s7⟩ := e99_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  rw [Devm.addLog_getStor] at sB
  rw [getStorVal_of_getStor s1] at c4 s4 c5
  rw [getStorVal_of_getStor s2, getStorVal_of_getStor s1] at c6
  rw [getStorVal_of_getStor s5] at c9
  simp only [gsv] at c4 c6 c7 c8 c9 s4 s7
  rw [s4, s2, s1] at c7 c8 c9 s7
  rw [low255_and_toNat] at c4
  have dw := sub_word (a := Nat.toB256 (2 ^ 255 - 1) &&&
    (Devm.getStor b sevm.currentTarget).get (balSlot z.toAdr)) (x := x)
    (by rw [low255_and_toNat]; exact c4)
  rw [low255_and_toNat] at dw
  rw [dw] at s4 c7 c8 c9 s7
  rw [s5, s4, s2, s1] at s7
  have aw := add_word c7
  rw [low255_and_toNat] at aw c7
  rw [aw] at s7 c8
  refine ⟨adr_ne_zero_of_mask c1, adr_ne_zero_of_mask c2, ?_, ?_, ?_, ?_, B, MB, GB, eo, ?_⟩
  · exact c4
  · exact c6
  · exact c9
  · rw [B256.toNat_toB256_of_lt (by omega), Nat.add_comm] at c8
    exact c8
  · rw [sB, s7, Nat.add_comm]
    rfl

/-- **Entry 81, `_approve(owner, spender, value)`**. -/
theorem e81_inv {x y z ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: z :: ret :: S) M G) t_3e18_c81 o) :
    z.toAdr ≠ 0 ∧ y.toAdr ≠ 0 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (allowSlot z.toAdr y.toAdr) x := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  rw [Devm.addLog_getStor] at sB
  refine ⟨adr_ne_zero_of_mask c1, adr_ne_zero_of_mask c2, B, MB, GB, eo, ?_⟩
  rw [sB, afterSstore_getStor_self, keccak_scratch, keccak_scratch, word_ff20, word_ff20, lit10]
  rfl

/-- **Entry 102, `_increaseAllowance(owner, spender, increment)`**. -/
theorem e102_inv {x y z ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: z :: ret :: S) M G) t_436b_c102 o) :
    z.toAdr ≠ 0 ∧ y.toAdr ≠ 0 ∧
      ((Devm.getStor b sevm.currentTarget).get (allowSlot z.toAdr y.toAdr)).toNat + x.toNat <
        2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (allowSlot z.toAdr y.toAdr)
          (Nat.toB256 (((Devm.getStor b sevm.currentTarget).get
            (allowSlot z.toAdr y.toAdr)).toNat + x.toNat)) := by
  have h := run.cut
  clear run
  repeat istep h
  icall h hc 98 t_43b5_c98
  obtain ⟨c1, G1, e⟩ := e98_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 81 t_3e18_c81
  obtain ⟨c2, c3, b2, M2, G2, e, s2⟩ := e81_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  rw [keccak_scratch, keccak_scratch, word_ff20, word_ff20, lit10] at c1 s2
  rw [gsv] at c1
  rw [afterSload_getStor, gsv, add_word c1] at s2
  have slot : Blanc.Lift.mapSlot y.toAdr.toB256 (Blanc.Lift.mapSlot z.toAdr.toB256 10) =
    allowSlot z.toAdr y.toAdr := rfl
  rw [slot] at c1 s2
  refine ⟨c2, c3, by omega, B, MB, GB, eo, ?_⟩
  rw [sB, s2, Nat.add_comm]

/-- The error-message copy loop of SafeMath's messaged `sub` (entries 119, 12, 13) only reverts. -/
theorem revertCopy_noExit : NoExitSet cert.prog [12, 13, 119] = true := by decide +kernel

/-- **Entry 115, SafeMath `sub(a, b, message)`**. -/
theorem e115_inv {x y w ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: w :: ret :: S) M G) t_50c5_c115 o) :
    y.toNat ≤ w.toNat ∧ ∃ G', o = .returned (St b ((w - y) :: S) M G') := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c
  · exact (SFunc.RunP.false_of_noExit revertCopy_noExit (by decide) (by decide) h.uncut).elim
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨le_of_gt_check c, _, Seg.done.inj e⟩

/-- **Entry 92, `_decreaseAllowance(owner, spender, decrement)`**. -/
theorem e92_inv {x y z ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: z :: ret :: S) M G) t_4956_c92 o) :
    z.toAdr ≠ 0 ∧ y.toAdr ≠ 0 ∧
      x.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot z.toAdr y.toAdr)).toNat ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (allowSlot z.toAdr y.toAdr)
          (Nat.toB256 (((Devm.getStor b sevm.currentTarget).get
            (allowSlot z.toAdr y.toAdr)).toNat - x.toNat)) := by
  have h := run.cut
  clear run
  repeat istep h
  icall h hc 115 t_50c5_c115
  obtain ⟨c1, G1, e⟩ := e115_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 81 t_3e18_c81
  obtain ⟨c2, c3, b2, M2, G2, e, s2⟩ := e81_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  rw [keccak_scratch, keccak_scratch, word_ff20, word_ff20, lit10] at c1 s2
  have slot : Blanc.Lift.mapSlot y.toAdr.toB256 (Blanc.Lift.mapSlot z.toAdr.toB256 10) =
    allowSlot z.toAdr y.toAdr := rfl
  rw [slot, gsv] at c1 s2
  rw [afterSload_getStor, sub_word c1] at s2
  exact ⟨c2, c3, c1, B, MB, GB, eo, by rw [sB, s2]⟩

/-- **Entry 71, the body of `approve(spender, value)`**. -/
theorem e71_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_12d3_c71 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧ sevm.caller ≠ 0 ∧
      y.toAdr ≠ 0 ∧ ∃ b' M' G', o = .returned (St b' (1 :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          (Devm.getStor b sevm.currentTarget).set (allowSlot sevm.caller y.toAdr) x := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icall h hc 81 t_3e18_c81
  obtain ⟨c2, c3, b2, M2, G2, e, s2⟩ := e81_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  have p := flag20_false_of_check c1
  rw [lit1] at p eo s2
  rw [toAdr_toB256] at c2 s2
  rw [afterSload_getStor] at s2
  exact ⟨p, c2, c3, B, MB, GB, eo, by rw [sB, s2]⟩

/-- **Entry 58, the body of `increaseAllowance(spender, increment)`**. -/
theorem e58_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_1d6a_c58 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧ sevm.caller ≠ 0 ∧
      y.toAdr ≠ 0 ∧
      ((Devm.getStor b sevm.currentTarget).get (allowSlot sevm.caller y.toAdr)).toNat + x.toNat <
        2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' (1 :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          (Devm.getStor b sevm.currentTarget).set (allowSlot sevm.caller y.toAdr)
            (Nat.toB256 (((Devm.getStor b sevm.currentTarget).get
              (allowSlot sevm.caller y.toAdr)).toNat + x.toNat)) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icall h hc 102 t_436b_c102
  obtain ⟨c2, c3, c4, b2, M2, G2, e, s2⟩ := e102_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  have p := flag20_false_of_check c1
  rw [lit1] at p eo s2
  rw [toAdr_toB256] at c2 c4 s2
  rw [afterSload_getStor] at s2 c4
  exact ⟨p, c2, c3, c4, B, MB, GB, eo, by rw [sB, s2]⟩

/-- **Entry 36, the body of `decreaseAllowance(spender, decrement)`**. -/
theorem e36_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_2f0e_c36 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧ sevm.caller ≠ 0 ∧
      y.toAdr ≠ 0 ∧
      x.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot sevm.caller y.toAdr)).toNat ∧
      ∃ b' M' G', o = .returned (St b' (1 :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          (Devm.getStor b sevm.currentTarget).set (allowSlot sevm.caller y.toAdr)
            (Nat.toB256 (((Devm.getStor b sevm.currentTarget).get
              (allowSlot sevm.caller y.toAdr)).toNat - x.toNat)) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icall h hc 92 t_4956_c92
  obtain ⟨c2, c3, c4, b2, M2, G2, e, s2⟩ := e92_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  have p := flag20_false_of_check c1
  rw [lit1] at p eo s2
  rw [toAdr_toB256] at c2 c4 s2
  rw [afterSload_getStor] at s2 c4
  exact ⟨p, c2, c3, c4, B, MB, GB, eo, by rw [sB, s2]⟩

/-- **Entry 37, the body of `transfer(to, value)`**. -/
theorem e37_inv {x y ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_2fa6_c37 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot y.toAdr)) = false ∧
      sevm.caller ≠ 0 ∧ y.toAdr ≠ 0 ∧
      x.toNat ≤ balanceBits ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)) ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)) = false ∧
      frozenBit ((debitStor (Devm.getStor b sevm.currentTarget) sevm.caller x.toNat).get
        (balSlot y.toAdr)) = false ∧
      balanceBits ((debitStor (Devm.getStor b sevm.currentTarget) sevm.caller x.toNat).get
        (balSlot y.toAdr)) + x.toNat ≤ 2 ^ 255 - 1 ∧
      ∃ b' M' G', o = .returned (St b' (1 :: S) M' G') ∧ Devm.getStor b' sevm.currentTarget =
        creditStor (debitStor (Devm.getStor b sevm.currentTarget) sevm.caller x.toNat) y.toAdr
          x.toNat := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icall h hc 83 t_3f6a_c83
  obtain ⟨b1, M1, G1, e, s1⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c2
  repeat istep h
  icall h hc 83 t_3f6a_c83
  obtain ⟨b2, M2, G2, e, s2⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c3
  repeat istep h
  icall h hc 93 t_3f98_c93
  obtain ⟨c4, c5, c6, c7, c8, c9, b3, M3, G3, e, s3⟩ := e93_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  have p := flag20_false_of_check c1
  have f := frozen_false_of_check c3
  rw [lit1] at p eo
  rw [getStorVal_of_getStor s1, gsv, afterSload_getStor] at f
  rw [toAdr_toB256] at c4 c6 c7 c8 c9 s3
  rw [s2, s1, afterSload_getStor] at c6 c7 c8 c9 s3
  exact ⟨p, f, c4, c5, c6, c7, c8, c9, B, MB, GB, eo, by rw [sB, s3]⟩

/-- **Entry 68, the body of `transferFrom(from, to, value)`**. -/
theorem e68_inv {x y z ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: z :: ret :: S) M G) t_1437_c68 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot z.toAdr)) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot y.toAdr)) = false ∧
      x.toNat ≤ ((Devm.getStor b sevm.currentTarget).get (allowSlot z.toAdr sevm.caller)).toNat ∧
      z.toAdr ≠ 0 ∧ y.toAdr ≠ 0 ∧
      x.toNat ≤ balanceBits ((Devm.getStor b sevm.currentTarget).get (balSlot z.toAdr)) ∧
      frozenBit ((debitStor (Devm.getStor b sevm.currentTarget) z.toAdr x.toNat).get
        (balSlot y.toAdr)) = false ∧
      balanceBits ((debitStor (Devm.getStor b sevm.currentTarget) z.toAdr x.toNat).get
        (balSlot y.toAdr)) + x.toNat ≤ 2 ^ 255 - 1 ∧
      x.toNat ≤ ((creditStor (debitStor (Devm.getStor b sevm.currentTarget) z.toAdr x.toNat)
        y.toAdr x.toNat).get (allowSlot z.toAdr sevm.caller)).toNat ∧
      ∃ b' M' G', o = .returned (St b' (1 :: S) M' G') ∧ Devm.getStor b' sevm.currentTarget =
        (creditStor (debitStor (Devm.getStor b sevm.currentTarget) z.toAdr x.toNat) y.toAdr
          x.toNat).set (allowSlot z.toAdr sevm.caller)
          (Nat.toB256 (((creditStor (debitStor (Devm.getStor b sevm.currentTarget) z.toAdr
            x.toNat) y.toAdr x.toNat).get (allowSlot z.toAdr sevm.caller)).toNat - x.toNat)) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icall h hc 83 t_3f6a_c83
  obtain ⟨b1, M1, G1, e, s1⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c2
  repeat istep h
  icall h hc 83 t_3f6a_c83
  obtain ⟨b2, M2, G2, e, s2⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c3
  repeat istep h
  icall h hc 83 t_3f6a_c83
  obtain ⟨b3, M3, G3, e, s3⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c4
  repeat istep h
  ibranch h c5
  repeat istep h
  icall h hc 93 t_3f98_c93
  obtain ⟨d1, d2, d3, d4, d5, d6, b4, M4, G4, e, s4⟩ := e93_inv fork hc
  cases e
  clear hc
  repeat istep h
  icall h hc 100 t_4163_c100
  obtain ⟨d7, G5, e⟩ := e100_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  have p := flag20_false_of_check c1
  have f1 := frozen_false_of_check c2
  have f2 := frozen_false_of_check c3
  have f3 := frozen_false_of_check c4
  have a1 := le_of_gt_check c5
  clear c1 c2 c3 c4 c5
  have slot : Blanc.Lift.mapSlot sevm.caller.toB256 (Blanc.Lift.mapSlot z.toAdr.toB256 10) =
    allowSlot z.toAdr sevm.caller := rfl
  have t1 := congrFun s1 sevm.currentTarget
  have t2 := congrFun s2 sevm.currentTarget
  have t3 := congrFun s3 sevm.currentTarget
  have tB := congrFun sB sevm.currentTarget
  clear s1 s2 s3 sB
  simp only [keccak_scratch, word_ff20, lit10, lit1, gsv, afterSload_getStor, afterSstore_getStor_self,
    toAdr_toB256, slot, t1, t2, t3] at p eo f1 f2 f3 a1 d3 d4 d5 d6 d7 s4 tB
  rw [s4] at d7 tB
  rw [sub_word d7] at tB
  exact ⟨p, f1, f2, f3, a1, d1, d2, d3, d5, d6, d7, B, MB, GB, eo, tB⟩

end Blanc.Lift.Usdc
