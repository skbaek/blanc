import Blanc.Lift.Usdc.RefineSignedAuthChecks
import Blanc.Lift.Usdc.RefineSignedCallees
import Blanc.Lift.SelectorRoute

/-!
# Certificate walks of `transferWithAuthorization` and `receiveWithAuthorization` (U6e3)

Inversion walks over the implementation certificate, with the route-C skips for everything that
writes no storage: the internal functions 90 (`transferWithAuthorization`) and 95
(`receiveWithAuthorization`) — `_requireValidAuthorization` (entry 112), the struct digest
(`ric_seg_e90`/`ric_seg_e95`), `_requireValidSignature` (`skip_sigRet`), then
`_markAuthorizationAsUsed` (entry 113) and `_transfer` (entry 93) — and the `(v, r, s)` adapters
87 and 84 (`ric_seg_e87`/`ric_seg_e84`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

/-- The authorization word of `(a, n)` marked used. -/
def markStor (σ : Stor) (a : Adr) (n : B256) : Stor :=
  σ.set (authSlot a n) (authMark (σ.get (authSlot a n)))

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- What the authorization internals guarantee and write, over the words `from`, `to`, `value`,
`validAfter`, `validBefore`, `nonce`. -/
def AuthPost (sevm : Sevm) (σ : Stor) (fr dst val va vb n : B256) (σ' : Stor) : Prop :=
  va < sevm.benvStat.time ∧ sevm.benvStat.time < vb ∧
    boolBit (σ.get (authSlot fr.toAdr n)) = false ∧
    fr.toAdr ≠ 0 ∧ dst.toAdr ≠ 0 ∧
    val.toNat ≤ balanceBits ((markStor σ fr.toAdr n).get (balSlot fr.toAdr)) ∧
    frozenBit ((markStor σ fr.toAdr n).get (balSlot fr.toAdr)) = false ∧
    frozenBit ((debitStor (markStor σ fr.toAdr n) fr.toAdr val.toNat).get
      (balSlot dst.toAdr)) = false ∧
    balanceBits ((debitStor (markStor σ fr.toAdr n) fr.toAdr val.toNat).get
      (balSlot dst.toAdr)) + val.toNat ≤ 2 ^ 255 - 1 ∧
    σ' = creditStor (debitStor (markStor σ fr.toAdr n) fr.toAdr val.toNat) dst.toAdr val.toNat

/-- **Entry 90, `_transferWithAuthorization(from, to, value, validAfter, validBefore, nonce,
signature)`.** -/
theorem e90_inv {x0 x1 x2 x3 x4 x5 x6 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ret :: S) M G)
      t_4b49_c90 o) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧
      AuthPost sevm (Devm.getStor b sevm.currentTarget) x6 x5 x4 x3 x2 x1
        (Devm.getStor b' sevm.currentTarget) := by
  have h := run.cut
  clear run
  repeat istep h
  icallA h hc 112 t_4dc8_c112
  have st1 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨t1, t2, a0, b1, M1, G1, e, s1⟩ := e112_inv fork hc
  cases e
  clear hc
  obtain ⟨b2, u0, M2, G2, st2, h⟩ := ric_seg_e90 fork h
  have hcode2 : b2.getCode usdcLib = Lib.code := by
    exact (getCode_eq_of_state_eq (st2.trans st1) _).trans hcode
  obtain ⟨b3, M3, G3, s3, -, h⟩ := skip_sigRet fork hcode2 h
  repeat istep h
  icallA h hc 113 t_5006_c113
  obtain ⟨b4, M4, G4, e, s4⟩ := e113_inv fork hc
  cases e
  clear hc
  repeat istep h
  icallA h hc 93 t_3f98_c93
  obtain ⟨c1, c2, c3, c4, c5, c6, b5, M5, G5, e, s5⟩ := e93_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  have hb3 : Devm.getStor b3 sevm.currentTarget = Devm.getStor b sevm.currentTarget :=
    s3.trans ((getStor_eq_of_state_eq st2 _).trans (congrFun s1 _))
  have hb4 : Devm.getStor b4 sevm.currentTarget =
      markStor (Devm.getStor b sevm.currentTarget) x6.toAdr x1 := by
    rw [s4, hb3]
    rfl
  rw [hb4] at c3 c4 c5 c6 s5
  exact ⟨B, MB, GB, eo, t1, t2, a0, c1, c2, c3, c4, c5, c6, by rw [congrFun sB, s5]⟩

/-- **Entry 95, `_receiveWithAuthorization(from, to, value, validAfter, validBefore, nonce,
signature)`.** -/
theorem e95_inv {x0 x1 x2 x3 x4 x5 x6 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ret :: S) M G)
      t_4571_c95 o) :
    sevm.caller = x5.toAdr ∧ ∃ b' M' G', o = .returned (St b' S M' G') ∧
      AuthPost sevm (Devm.getStor b sevm.currentTarget) x6 x5 x4 x3 x2 x1
        (Devm.getStor b' sevm.currentTarget) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c0
  repeat istep h
  icallA h hc 112 t_4dc8_c112
  have st1 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨t1, t2, a0, b1, M1, G1, e, s1⟩ := e112_inv fork hc
  cases e
  clear hc
  obtain ⟨b2, u0, M2, G2, st2, h⟩ := ric_seg_e95 fork h
  have hcode2 : b2.getCode usdcLib = Lib.code := by
    exact (getCode_eq_of_state_eq (st2.trans st1) _).trans hcode
  obtain ⟨b3, M3, G3, s3, -, h⟩ := skip_sigRet fork hcode2 h
  repeat istep h
  icallA h hc 113 t_5006_c113
  obtain ⟨b4, M4, G4, e, s4⟩ := e113_inv fork hc
  cases e
  clear hc
  repeat istep h
  icallA h hc 93 t_3f98_c93
  obtain ⟨c1, c2, c3, c4, c5, c6, b5, M5, G5, e, s5⟩ := e93_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  have hb3 : Devm.getStor b3 sevm.currentTarget = Devm.getStor b sevm.currentTarget :=
    s3.trans ((getStor_eq_of_state_eq st2 _).trans (congrFun s1 _))
  have hb4 : Devm.getStor b4 sevm.currentTarget =
      markStor (Devm.getStor b sevm.currentTarget) x6.toAdr x1 := by
    rw [s4, hb3]
    rfl
  rw [hb4] at c3 c4 c5 c6 s5
  refine ⟨?_, B, MB, GB, eo, t1, t2, a0, c1, c2, c3, c4, c5, c6, by rw [congrFun sB, s5]⟩
  have e := congrArg B256.toAdr (eq_of_eqCheck_ne c0)
  rwa [word_ff20, toAdr_toB256, toAdr_toB256] at e

/-- **Entry 87, `transferWithAuthorization(from, to, value, validAfter, validBefore, nonce, v, r,
s)`'s adapter**: `abi.encodePacked(r, s, v)`, then entry 90. -/
theorem e87_inv {x0 x1 x2 x3 x4 x5 x6 x7 x8 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: ret :: S) M G) t_4c3f_c87 o) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧
      AuthPost sevm (Devm.getStor b sevm.currentTarget) x8 x7 x6 x5 x4 x3
        (Devm.getStor b' sevm.currentTarget) := by
  obtain ⟨b1, u0, M1, G1, st1, h⟩ := ric_seg_e87 fork run.cut
  icallA h hc 90 t_4b49_c90
  obtain ⟨b2, M2, G2, e, post⟩ :=
    e90_inv fork ((getCode_eq_of_state_eq st1 _).trans hcode) hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  rw [getStor_eq_of_state_eq st1] at post
  exact ⟨B, MB, GB, eo, by rw [congrFun sB]; exact post⟩

/-- **Entry 84, `receiveWithAuthorization(from, to, value, validAfter, validBefore, nonce, v, r,
s)`'s adapter**: `abi.encodePacked(r, s, v)`, then entry 95. -/
theorem e84_inv {x0 x1 x2 x3 x4 x5 x6 x7 x8 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: ret :: S) M G) t_4c83_c84 o) :
    sevm.caller = x7.toAdr ∧ ∃ b' M' G', o = .returned (St b' S M' G') ∧
      AuthPost sevm (Devm.getStor b sevm.currentTarget) x8 x7 x6 x5 x4 x3
        (Devm.getStor b' sevm.currentTarget) := by
  obtain ⟨b1, u0, M1, G1, st1, h⟩ := ric_seg_e84 fork run.cut
  icallA h hc 95 t_4571_c95
  obtain ⟨cl, b2, M2, G2, e, post⟩ :=
    e95_inv fork ((getCode_eq_of_state_eq st1 _).trans hcode) hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  rw [getStor_eq_of_state_eq st1] at post
  exact ⟨cl, B, MB, GB, eo, by rw [congrFun sB]; exact post⟩

/-- **Entry 20, the body of `transferWithAuthorization(…, v, r, s)`**: `whenNotPaused`,
`notBlacklisted(from)`, `notBlacklisted(to)`, then entry 87. -/
theorem e20_inv {x0 x1 x2 x3 x4 x5 x6 x7 x8 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: ret :: S) M G) t_3889_c20 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot x8.toAdr)) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot x7.toAdr)) = false ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        AuthPost sevm (Devm.getStor b sevm.currentTarget) x8 x7 x6 x5 x4 x3
          (Devm.getStor b' sevm.currentTarget) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icallA h hc 83 t_3f6a_c83
  have st1 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨b1, M1, G1, e, s1⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c2
  repeat istep h
  icallA h hc 83 t_3f6a_c83
  have st2 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨b2, M2, G2, e, s2⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c3
  repeat istep h
  icallA h hc 87 t_4c3f_c87
  obtain ⟨b3, M3, G3, e, post⟩ := e87_inv fork
    ((getCode_eq_of_state_eq (st2.trans st1) _).trans ((afterSload_getCode _ _ _ _).trans hcode)) hc
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
  rw [gsv, lit1] at p
  rw [gsv, afterSload_getStor] at f1
  rw [gsv, congrFun s1, afterSload_getStor] at f2
  change AuthPost sevm (Devm.getStor b2 sevm.currentTarget) _ _ _ _ _ _ _ at post
  rw [congrFun s2, congrFun s1, afterSload_getStor] at post
  exact ⟨p, f1, f2, B, MB, GB, eo, by rw [congrFun sB]; exact post⟩

/-- **Entry 15, the body of `receiveWithAuthorization(…, v, r, s)`**: `whenNotPaused`,
`notBlacklisted(from)`, `notBlacklisted(to)`, then entry 84. -/
theorem e15_inv {x0 x1 x2 x3 x4 x5 x6 x7 x8 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: ret :: S) M G) t_3aa2_c15 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot x8.toAdr)) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot x7.toAdr)) = false ∧
      sevm.caller = x7.toAdr ∧ ∃ b' M' G', o = .returned (St b' S M' G') ∧
        AuthPost sevm (Devm.getStor b sevm.currentTarget) x8 x7 x6 x5 x4 x3
          (Devm.getStor b' sevm.currentTarget) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icallA h hc 83 t_3f6a_c83
  have st1 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨b1, M1, G1, e, s1⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c2
  repeat istep h
  icallA h hc 83 t_3f6a_c83
  have st2 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨b2, M2, G2, e, s2⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c3
  repeat istep h
  icallA h hc 84 t_4c83_c84
  obtain ⟨cl, b3, M3, G3, e, post⟩ := e84_inv fork
    ((getCode_eq_of_state_eq (st2.trans st1) _).trans ((afterSload_getCode _ _ _ _).trans hcode)) hc
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
  rw [gsv, lit1] at p
  rw [gsv, afterSload_getStor] at f1
  rw [gsv, congrFun s1, afterSload_getStor] at f2
  change AuthPost sevm (Devm.getStor b2 sevm.currentTarget) _ _ _ _ _ _ _ at post
  rw [congrFun s2, congrFun s1, afterSload_getStor] at post
  exact ⟨p, f1, f2, cl, B, MB, GB, eo, by rw [congrFun sB]; exact post⟩

/-- **Entry 30, the body of `transferWithAuthorization(…, signature)`**: `whenNotPaused`,
`notBlacklisted(from)`, `notBlacklisted(to)`, then entry 90. -/
theorem e30_inv {x0 x1 x2 x3 x4 x5 x6 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ret :: S) M G) t_3549_c30 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot x6.toAdr)) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot x5.toAdr)) = false ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧
        AuthPost sevm (Devm.getStor b sevm.currentTarget) x6 x5 x4 x3 x2 x1
          (Devm.getStor b' sevm.currentTarget) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icallA h hc 83 t_3f6a_c83
  have st1 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨b1, M1, G1, e, s1⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c2
  repeat istep h
  icallA h hc 83 t_3f6a_c83
  have st2 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨b2, M2, G2, e, s2⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c3
  repeat istep h
  icallA h hc 90 t_4b49_c90
  obtain ⟨b3, M3, G3, e, post⟩ := e90_inv fork
    ((getCode_eq_of_state_eq (st2.trans st1) _).trans ((afterSload_getCode _ _ _ _).trans hcode)) hc
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
  rw [gsv, lit1] at p
  rw [gsv, afterSload_getStor] at f1
  rw [gsv, congrFun s1, afterSload_getStor] at f2
  change AuthPost sevm (Devm.getStor b2 sevm.currentTarget) _ _ _ _ _ _ _ at post
  rw [congrFun s2, congrFun s1, afterSload_getStor] at post
  exact ⟨p, f1, f2, B, MB, GB, eo, by rw [congrFun sB]; exact post⟩

/-- **Entry 43, the body of `receiveWithAuthorization(…, signature)`**: `whenNotPaused`,
`notBlacklisted(from)`, `notBlacklisted(to)`, then entry 95. -/
theorem e43_inv {x0 x1 x2 x3 x4 x5 x6 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ret :: S) M G) t_2c16_c43 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot x6.toAdr)) = false ∧
      frozenBit ((Devm.getStor b sevm.currentTarget).get (balSlot x5.toAdr)) = false ∧
      sevm.caller = x5.toAdr ∧ ∃ b' M' G', o = .returned (St b' S M' G') ∧
        AuthPost sevm (Devm.getStor b sevm.currentTarget) x6 x5 x4 x3 x2 x1
          (Devm.getStor b' sevm.currentTarget) := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  icallA h hc 83 t_3f6a_c83
  have st1 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨b1, M1, G1, e, s1⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c2
  repeat istep h
  icallA h hc 83 t_3f6a_c83
  have st2 := SFunc.Run.state_of_silent auth_silent (by decide) (by decide) hc
  obtain ⟨b2, M2, G2, e, s2⟩ := e83_inv fork hc
  cases e
  clear hc
  repeat istep h
  ibranch h c3
  repeat istep h
  icallA h hc 95 t_4571_c95
  obtain ⟨cl, b3, M3, G3, e, post⟩ := e95_inv fork
    ((getCode_eq_of_state_eq (st2.trans st1) _).trans ((afterSload_getCode _ _ _ _).trans hcode)) hc
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
  rw [gsv, lit1] at p
  rw [gsv, afterSload_getStor] at f1
  rw [gsv, congrFun s1, afterSload_getStor] at f2
  change AuthPost sevm (Devm.getStor b2 sevm.currentTarget) _ _ _ _ _ _ _ at post
  rw [congrFun s2, congrFun s1, afterSload_getStor] at post
  exact ⟨p, f1, f2, cl, B, MB, GB, eo, by rw [congrFun sB]; exact post⟩

/-- A `STOP` halt keeps the base's storage. -/
theorem ric_stop_getStor {fs : List SFunc} {C : List Nat} {post : Devm}
    (run : SFunc.RunCut fs sevm C (St b S M G) (.last .stop) (.done (.halted post))) :
    Devm.getStor post = Devm.getStor b := by
  cases run with
  | last hl =>
    simp only [Linst.Run, Linst.run, Except.ok.injEq] at hl
    subst hl
    rfl

end Blanc.Lift.Usdc
