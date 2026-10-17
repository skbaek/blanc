import Blanc.Lift.Usdc.RefineTransferCallees

/-!
# Certificate walks of the callees the signed family shares (U6e2)

Inversion walks, in the style of `RefineTransferCallees.lean` and with its kit, over the
implementation certificate's entries that the authorization selectors share:

* entry 110, `_requireUnusedAuthorization(authorizer, nonce)`: the low byte of the
  authorization-state word is clear;
* entry 112, `_requireValidAuthorization(authorizer, nonce, validAfter, validBefore)`: the two
  timestamp checks, then entry 110;
* entry 113, `_markAuthorizationAsUsed(authorizer, nonce)`: the authorization-state write at
  `0x5060` (and its `AuthorizationUsed` log);
* the tail `t_4ac3_c89` of `_cancelAuthorization` after its signature check: the
  authorization-state write at `0x4b1d` (and its `AuthorizationCanceled` log).

Each lemma holds for any stack below the callee's frame and any base, and states the guards a
returned run passed and the storage it leaves at the frame's owner.  The `whenNotPaused` and
`notBlacklisted` modifiers of the signed bodies are the transfer family's (`flag20_false_of_check`,
`frozen_false_of_check`, `e83_inv`).  The word algebra: `boolBit_false_of_check` reads the
unused-authorization guard, and `boolBit_authMark` shows the stored word marks the authorization
used, which is what `ledger_set_auth` asks.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

/-- The callees of the signed family's authorization checks and writes: none halts the frame. -/
def signedCallees : List Nat := [110, 112, 113]

theorem signedCallees_noHalt : NoHaltSet cert.prog signedCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `signedCallees` from a cut run `h`; the callee run is
`hc`, the continuation `h`. -/
macro "icallS " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry signedCallees_noHalt
      (by decide : $k ∈ signedCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- The authorization-state word after a write of `true`: the old word with its low byte set
to `1`. -/
def authMark (w : B256) : B256 :=
  Bytes.toB256 [1] ||| (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0x00] &&& w)

/-- The marked word reads as a used authorization. -/
theorem boolBit_authMark (w : B256) : boolBit (authMark w) = true := by
  unfold boolBit
  rw [decide_eq_true_iff, B256.toNat_eq, B128.toNat_eq (authMark w).2]
  have low : (authMark w).2.2 = 1 ||| ((0xffffffffffffff00 : UInt64) &&& w.2.2) := rfl
  rw [low, UInt64.toNat_or, UInt64.toNat_and]
  have one : (1 : UInt64).toNat = 1 := rfl
  have odd := Nat.testBit_or 1 ((0xffffffffffffff00 : UInt64).toNat &&& w.2.2.toNat) 0
  rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at odd
  rw [one]
  generalize 1 ||| (0xffffffffffffff00 : UInt64).toNat &&& w.2.2.toNat = t at odd ⊢
  intro e
  have m2 := Nat.mod_mod_of_dvd ((authMark w).1.toNat * 2 ^ 128 + ((authMark w).2.1.toNat * 2 ^ 64 +
    t)) (by decide : 2 ∣ 256)
  rw [e, Nat.zero_mod] at m2
  by_cases h : t % 2 = 1
  · omega
  · simp only [h, decide_false, decide_true, Bool.true_or] at odd
    exact absurd odd Bool.false_ne_true

/-- `require(!_authorizationStates[a][n])`, as its flag reaches the branch. -/
theorem boolBit_false_of_check {w : B256}
    (h : B256.eqCheck (Bytes.toB256 [255] &&& w) 0 ≠ 0) : boolBit w = false := by
  have e := congrArg B256.toNat (eq_zero_of_iszero_ne_zero h)
  have fn : (Bytes.toB256 [255]).toNat = 2 ^ 8 - 1 := by decide
  rw [Blanc.B256.toNat_and, fn, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    B256.toNat_zero] at e
  unfold boolBit
  rw [decide_eq_false_iff_not, not_not]
  exact e

theorem lit16 : Bytes.toB256 [16] = 16 := by decide

theorem lt_of_gtCheck_ne_zero {x y : B256} (h : B256.gtCheck x y ≠ 0) : y < x := by
  unfold B256.gtCheck at h
  split at h
  · assumption
  · exact absurd rfl h

theorem lt_of_ltCheck_ne_zero {x y : B256} (h : B256.ltCheck x y ≠ 0) : x < y := by
  unfold B256.ltCheck at h
  split at h
  · assumption
  · exact absurd rfl h

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **Entry 110, `_requireUnusedAuthorization(a, n)`**: reads the authorization-state word of
`(a, n)` and requires its low byte clear. -/
theorem e110_inv {n a ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (n :: a :: ret :: S) M G) t_524e_c110 o) :
    boolBit ((Devm.getStor b sevm.currentTarget).get (authSlot a.toAdr n)) = false ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' = Devm.getStor b := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  rw [keccak_scratch, keccak_scratch, word_ff20, lit16, gsv] at c
  exact ⟨boolBit_false_of_check c, _, _, _, rfl, funext fun x => afterSload_getStor _ _ _ x⟩

/-- **Entry 112, `_requireValidAuthorization(a, n, validAfter, validBefore)`**: the time window,
then entry 110. -/
theorem e112_inv {vb va n a ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (vb :: va :: n :: a :: ret :: S) M G) t_4dc8_c112 o) :
    va < sevm.benvStat.time ∧ sevm.benvStat.time < vb ∧
      boolBit ((Devm.getStor b sevm.currentTarget).get (authSlot a.toAdr n)) = false ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' = Devm.getStor b := by
  have h := run.cut
  clear run
  repeat istep h
  obtain ⟨_, hd, h⟩ := ric_next h
  obtain ⟨_, e⟩ := ri_timestamp hd
  subst e
  clear hd
  repeat istep h
  ibranch h c1
  repeat istep h
  obtain ⟨_, hd, h⟩ := ric_next h
  obtain ⟨_, e⟩ := ri_timestamp hd
  subst e
  clear hd
  repeat istep h
  ibranch h c2
  repeat istep h
  icallS h hc 110 t_524e_c110
  obtain ⟨c3, b1, M1, G1, e, s1⟩ := e110_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  cases e
  exact ⟨lt_of_gtCheck_ne_zero c1, lt_of_ltCheck_ne_zero c2, c3, _, _, _, rfl, s1⟩

/-- **Entry 113, `_markAuthorizationAsUsed(a, n)`**: the authorization-state write at `0x5060`. -/
theorem e113_inv {n a ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (n :: a :: ret :: S) M G) t_5006_c113 o) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set (authSlot a.toAdr n)
        (authMark ((Devm.getStor b sevm.currentTarget).get (authSlot a.toAdr n))) := by
  have h := run.cut
  clear run
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  rw [Devm.addLog_getStor] at sB
  refine ⟨B, MB, GB, eo, ?_⟩
  rw [sB]
  rw [afterSstore_getStor_self, keccak_scratch, keccak_scratch, word_ff20, lit16, afterSload_getStor,
    gsv]
  rfl

/-- **The tail of `_cancelAuthorization`** after its signature check (`t_4ac3_c89`): the
authorization-state write at `0x4b1d`, for any cut and any continuation. -/
theorem k89_cancel_inv {sig n a ret : B256} {C : List Nat} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut cert.prog sevm C (St b (sig :: n :: a :: ret :: S) M G) t_4ac3_c89 r) :
    ∃ b' M' G', r = .done (.returned (St b' S M' G')) ∧ Devm.getStor b' sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set (authSlot a.toAdr n)
        (authMark ((Devm.getStor b sevm.currentTarget).get (authSlot a.toAdr n))) := by
  have h := run
  clear run
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  subst e
  refine ⟨_, _, _, rfl, ?_⟩
  rw [Devm.addLog_getStor]
  rw [afterSstore_getStor_self, keccak_scratch, keccak_scratch, word_ff20, lit16, afterSload_getStor,
    gsv]
  rfl

end Blanc.Lift.Usdc
