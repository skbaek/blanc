import Blanc.Lift.Usdc.SignedSkip
import Blanc.Lift.Usdc.ShuffleSegments
import Blanc.Lift.Usdc.RefineSignedCallees

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- `_domainSeparator`'s closure (entry 78, the `name` loop included). -/
def sil78 : List Nat := [6, 76, 77, 78, 106, 107]

theorem sil78_silent : SilentSet cert.prog sil78 = true := by decide +kernel

theorem sil79_silent : SilentSet cert.prog [79] = true := by decide +kernel

/-- **Crossing `_domainSeparator`** (entry 78, frame `[ret]`, one return word). -/
theorem skip_e78 {C : List Nat} {f : SFunc} {r : Seg} {dd ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut cert.prog sevm C (St b (dd :: ρ :: S) M G) (.callNext 78 f) r) :
    (∃ b' y M' G', b'.state = b.state ∧ SFunc.RunCut cert.prog sevm C (St b' (y :: S) M' G') f r) ∨
      ∃ D, r = .done (.halted D) := by
  rcases ric_call_silent (e := ⟨0x4276, [.ret], 1⟩) (ρ := ρ) (S := ρ :: S) cert_check fork
      (Sk := sil78) sil78_silent (by decide) rfl rfl (List.Forall₂.cons rfl .nil) run with
    ⟨b', Y, M', G', hs, hlen, cont⟩ | ⟨D, -, hr⟩
  · match Y, hlen, cont with
    | [y], _, cont => exact .inl ⟨b', y, M', G', hs, cont⟩
  · exact .inr ⟨D, hr⟩

/-- **Crossing `_hashTypedDataV4`** (entry 79, frame `[_, _, ret]`, one return word). -/
theorem skip_e79 {C : List Nat} {f : SFunc} {r : Seg} {dd x y ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut cert.prog sevm C (St b (dd :: x :: y :: ρ :: S) M G) (.callNext 79 f) r) :
    (∃ b' z M' G', b'.state = b.state ∧ SFunc.RunCut cert.prog sevm C (St b' (z :: S) M' G') f r) ∨
      ∃ D, r = .done (.halted D) := by
  rcases ric_call_silent (e := ⟨0x508b, [.unk, .unk, .ret], 1⟩) (ρ := ρ) (S := x :: y :: ρ :: S)
      cert_check fork (Sk := [79]) sil79_silent (by decide) rfl rfl
      (List.Forall₂.cons trivial (.cons trivial (.cons rfl .nil))) run with
    ⟨b', Y, M', G', hs, hlen, cont⟩ | ⟨D, -, hr⟩
  · match Y, hlen, cont with
    | [z], _, cont => exact .inl ⟨b', z, M', G', hs, cont⟩
  · exact .inr ⟨D, hr⟩

theorem getCode_of_state {b' : Devm} (h : b'.state = b.state) (a : Adr) :
    b'.getCode a = b.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h]

theorem getStor_of_state {b' : Devm} (h : b'.state = b.state) : Devm.getStor b' = Devm.getStor b := by
  funext a
  unfold Devm.getStor Devm.getAcct
  rw [h]

theorem libWord_lit : Nat.toB256 0x800c32eaa2a6c93cf4cb51794450ed77fbfbb172 = usdcLib.toB256 := by
  decide +kernel

/-- **The tail of `_permit`** from its library `DELEGATECALL` (entry 9): the call is skipped, its
result checked, and `_approve(owner, spender, value)` (entry 81) writes the allowance. -/
theorem permit_tail {C : List Nat} {r : Seg} {g ii is oi os y0 y1 y2 y3 y4 y5 y6 y7 y8 ret : B256}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.RunCut cert.prog sevm C (St b (g :: usdcLib.toB256 :: ii :: is :: oi :: os :: y0 ::
      y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: y8 :: ret :: S) M G) (SFunc.lineDrop 3 t_48ac_c9) r) :
    y8.toAdr ≠ 0 ∧ y7.toAdr ≠ 0 ∧ ∃ b' M' G', r = .done (.returned (St b' S M' G')) ∧
      Devm.getStor b' sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (allowSlot y8.toAdr y7.toAdr) y6 := by
  obtain ⟨b1, x, M1, G1, hs1, -, h⟩ := skip_libCall fork hcode run
  clear run
  obtain ⟨b2, M2, G2, hs2, h⟩ := ric_seg_e9call fork h
  icall h hc 81 t_3e18_c81
  obtain ⟨d1, d2, b3, M3, G3, e, s3⟩ := e81_inv fork hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  refine ⟨d1, d2, b3, _, _, e, ?_⟩
  rw [s3, congrFun (getStor_of_state hs2) _, hs1]

/-- **The signature-bytes copy loop** (entry 80, solc's word copy into the call's calldata): every
run of the loop from its head, whose every exit satisfies `Q` (a finished segment), satisfies `Q`.
Each iteration keeps the base machine and the words below the counter. -/
theorem copy80 {a1 a2 a3 : B256} {R0 : List B256} {r : Seg} (Q : Seg → Prop)
    (fork : CoveredFork sevm.benvStat.fork) (hQ : ∀ r, Q r → ∃ o, r = .done o)
    (exit : ∀ i M G r, SFunc.RunCut cert.prog sevm [80] (St b (i :: a1 :: a2 :: a3 :: R0) M G)
      t_4860_c80 r → Q r)
    {i : B256} (run : SFunc.RunCut cert.prog sevm [] (St b (i :: a1 :: a2 :: a3 :: R0) M G)
      t_4848_c80 r) : Q r := by
  refine SFunc.RunCutP.loop (k := 80) rfl (by decide)
    (fun d => ∃ i M G, d = St b (i :: a1 :: a2 :: a3 :: R0) M G) Q ?_ _ r ⟨i, M, G, rfl⟩ run
  rintro d ⟨i, M, G, rfl⟩ r h
  repeat istep h
  ibranch h c
  · repeat istep h
    obtain ⟨_, e⟩ := ric_jumpCut List.mem_cons_self h
    subst e
    simp only [Seg.LoopPost, ↓reduceIte]
    exact ⟨_, _, _, rfl⟩
  · have q := exit _ _ _ _ h
    obtain ⟨o, rfl⟩ := hQ _ q
    exact q

/-- **`_permit`'s body** (entry 8, from its deadline flag): the nonce bump, the digest, the library
check (skipped) and `_approve(owner, spender, value)`. -/
theorem e8_inv {fl x0 x1 x2 x3 x4 ret : B256} {r : Seg} (fork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode usdcLib = Lib.code) (nh : ∀ D, r ≠ .done (.halted D))
    (run : SFunc.RunCut cert.prog sevm [] (St b (fl :: x0 :: x1 :: x2 :: x3 :: x4 :: ret :: S) M G)
      t_46c0_c8 r) :
    x4.toAdr ≠ 0 ∧ x3.toAdr ≠ 0 ∧ ∃ b' M' G', r = .done (.returned (St b' S M' G')) ∧
      Devm.getStor b' sevm.currentTarget =
        ((Devm.getStor b sevm.currentTarget).set (nonceSlot x4.toAdr)
          ((Devm.getStor b sevm.currentTarget).get (nonceSlot x4.toAdr) + 1)).set
          (allowSlot x4.toAdr x3.toAdr) x2 := by
  have h := run
  clear run
  repeat istep h
  ibranch h c1
  repeat istep h
  rcases skip_e78 fork h with ⟨b1, y1, M1, G1, hs1, h⟩ | ⟨D, rfl⟩
  swap
  · exact absurd rfl (nh D)
  iterate 27 istep h
  obtain ⟨b2, u0, M2, G2, hs2, h⟩ := ric_seg_e8digest fork h
  rcases skip_e79 fork h with ⟨b3, z, M3, G3, hs3, h⟩ | ⟨D, rfl⟩
  swap
  · exact absurd rfl (nh D)
  obtain ⟨b4, v0, v1, v2, v3, v4, v5, v6, v7, M4, G4, hs4, h⟩ := ric_seg_e8encode fork h
  rw [libWord_lit] at h
  have code4 : b4.getCode usdcLib = Lib.code := by
    rw [getCode_of_state hs4, getCode_of_state hs3, getCode_of_state hs2, afterSstore_getCode,
      afterSload_getCode, getCode_of_state hs1, hcode]
  have key : x4.toAdr ≠ 0 ∧ x3.toAdr ≠ 0 ∧ ∃ b' M' G', r = .done (.returned (St b' S M' G')) ∧
      Devm.getStor b' sevm.currentTarget =
        (Devm.getStor b4 sevm.currentTarget).set (allowSlot x4.toAdr x3.toAdr) x2 := by
    repeat istep h
    ibranch h c2
    · repeat istep h
      obtain ⟨_, h⟩ := ric_jump (by decide) rfl h
      refine copy80 (fun r => x4.toAdr ≠ 0 ∧ x3.toAdr ≠ 0 ∧ ∃ b' M' G',
          r = .done (.returned (St b' S M' G')) ∧ Devm.getStor b' sevm.currentTarget =
            (Devm.getStor b4 sevm.currentTarget).set (allowSlot x4.toAdr x3.toAdr) x2) fork
        (fun r q => ?_) (fun i M G r h => ?_) h
      · obtain ⟨-, -, b', M', G', e, -⟩ := q
        exact ⟨_, e⟩
      · obtain ⟨b5, w0, w1, w2, w3, w4, M5, G5, hs5, h⟩ := ric_seg_e80exit fork (by decide) h
        obtain ⟨d1, d2, b6, M6, G6, e, s6⟩ := permit_tail fork (by rw [getCode_of_state hs5]; exact code4) h
        exact ⟨d1, d2, b6, M6, G6, e, by rw [s6, getStor_of_state hs5]⟩
    · obtain ⟨b5, w0, w1, w2, w3, w4, M5, G5, hs5, h⟩ := ric_seg_e8exit fork (by decide) h
      obtain ⟨d1, d2, b6, M6, G6, e, s6⟩ := permit_tail fork (by rw [getCode_of_state hs5]; exact code4) h
      exact ⟨d1, d2, b6, M6, G6, e, by rw [s6, getStor_of_state hs5]⟩
  obtain ⟨d1, d2, b', M', G', e, s'⟩ := key
  refine ⟨d1, d2, b', M', G', e, ?_⟩
  rw [s', getStor_of_state hs4, getStor_of_state hs3, getStor_of_state hs2, afterSstore_getStor_self,
    afterSload_getStor, getStor_of_state hs1, keccak_scratch, word_ff20, gsv, getStor_of_state hs1]
  rfl

/-- The callees of the permit paths: none halts the frame. -/
def permitCallees : List Nat := [6, 8, 9, 24, 41, 76, 77, 78, 79, 80, 81, 88, 94, 106, 107]

theorem permitCallees_noHalt : NoHaltSet cert.prog permitCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `permitCallees`. -/
macro "icallP " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry permitCallees_noHalt
      (by decide : $k ∈ permitCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- One `TIMESTAMP` step of a cut run. -/
macro "itime " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_timestamp hd
   subst e; clear hd))

/-- **`_permit(owner, spender, value, deadline, signature)`** (entry 94, with its goto into entry 8):
the nonce bump and the allowance write. -/
theorem e94_inv {x0 x1 x2 x3 x4 ret : B256} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (x0 :: x1 :: x2 :: x3 :: x4 :: ret :: S) M G) t_4692_c94 o) :
    x4.toAdr ≠ 0 ∧ x3.toAdr ≠ 0 ∧ ∃ b' M' G', o = .returned (St b' S M' G') ∧
      Devm.getStor b' sevm.currentTarget =
        ((Devm.getStor b sevm.currentTarget).set (nonceSlot x4.toAdr)
          ((Devm.getStor b sevm.currentTarget).get (nonceSlot x4.toAdr) + 1)).set
          (allowSlot x4.toAdr x3.toAdr) x2 := by
  have nh : ∀ D, Seg.done o ≠ .done (.halted D) := fun D e =>
    SFunc.RunP.not_halted_entry permitCallees_noHalt (k := 94) (by decide) rfl run (Seg.done.inj e)
  have h := run.cut
  clear run
  repeat istep h
  rcases ric_branchTo (by decide) rfl h with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · repeat istep h
    itime h
    iterate 3 istep h
    obtain ⟨d1, d2, b', M', G', e, s'⟩ := e8_inv fork hcode nh h
    exact ⟨d1, d2, b', M', G', Seg.done.inj e, s'⟩
  · obtain ⟨d1, d2, b', M', G', e, s'⟩ := e8_inv fork hcode nh h
    exact ⟨d1, d2, b', M', G', Seg.done.inj e, s'⟩

/-- One straight-line step, also over `SHL`, `MUL`, `CALLDATACOPY` and `TIMESTAMP`. -/
macro "istepX " h:ident : tactic => `(tactic| first
  | istep $h
  | (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     first
     | (obtain ⟨_, e⟩ := ri_shl hd; subst e; clear hd)
     | (obtain ⟨_, e⟩ := ri_mul hd; subst e; clear hd)
     | (obtain ⟨_, e⟩ := ri_calldatacopy hd; subst e; clear hd)
     | (obtain ⟨_, e⟩ := ri_timestamp hd; subst e; clear hd)))

/-- The common conclusion of the permit callees: the owner and spender are nonzero, and the
returned storage bumps the owner's nonce and writes the allowance. -/
def PermitPost (b : Devm) (P : Adr) (owner spender value : B256) (S : List B256) (o : Outcome) :
    Prop :=
  owner.toAdr ≠ 0 ∧ spender.toAdr ≠ 0 ∧ ∃ b' M' G', o = .returned (St b' S M' G') ∧
    Devm.getStor b' P = ((Devm.getStor b P).set (nonceSlot owner.toAdr)
      ((Devm.getStor b P).get (nonceSlot owner.toAdr) + 1)).set
      (allowSlot owner.toAdr spender.toAdr) value

/-- **`_permit(owner, spender, value, deadline, v, r, s)`** (entry 88): `abi.encodePacked(r, s, v)`,
then entry 94. -/
theorem e88_inv {y0 y1 y2 y3 y4 y5 y6 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: ret :: S) M G)
      t_4be7_c88 o) : PermitPost b sevm.currentTarget y6 y5 y4 S o := by
  have h := run.cut
  clear run
  repeat istepX h
  icallP h hc 94 t_4692_c94
  obtain ⟨d1, d2, b1, M1, G1, e, s1⟩ := e94_inv fork hcode hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨d1, d2, b1, _, _, Seg.done.inj e, s1⟩

/-- **`permit(owner, spender, value, deadline, v, r, s)`'s body** (entry 24): `whenNotPaused`, then
entry 88. -/
theorem e24_inv {y0 y1 y2 y3 y4 y5 y6 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: ret :: S) M G)
      t_36a2_c24 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      PermitPost b sevm.currentTarget y6 y5 y4 S o := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c
  repeat istep h
  icallP h hc 88 t_4be7_c88
  obtain ⟨d1, d2, b1, M1, G1, e, s1⟩ := e88_inv fork (by rw [afterSload_getCode]; exact hcode) hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  rw [afterSload_getStor] at s1
  rw [gsv] at c
  exact ⟨flag20_false_of_check c, d1, d2, b1, _, _, Seg.done.inj e, s1⟩

/-- **`permit(owner, spender, value, deadline, signature)`'s body** (entry 41): `whenNotPaused`,
then entry 94. -/
theorem e41_inv {y0 y1 y2 y3 y4 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (y0 :: y1 :: y2 :: y3 :: y4 :: ret :: S) M G)
      t_2e53_c41 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      PermitPost b sevm.currentTarget y4 y3 y2 S o := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c
  repeat istep h
  icallP h hc 94 t_4692_c94
  obtain ⟨d1, d2, b1, M1, G1, e, s1⟩ := e94_inv fork (by rw [afterSload_getCode]; exact hcode) hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  rw [afterSload_getStor] at s1
  rw [gsv] at c
  exact ⟨flag20_false_of_check c, d1, d2, b1, _, _, Seg.done.inj e, s1⟩

/-- The callees of the cancellation paths: none halts the frame. -/
def cancelCallees : List Nat := [4, 6, 11, 28, 52, 76, 77, 78, 79, 89, 97, 106, 107, 110, 111, 117]

theorem cancelCallees_noHalt : NoHaltSet cert.prog cancelCallees = true := by decide +kernel

theorem sil110_silent : SilentSet cert.prog [110] = true := by decide +kernel

/-- The common conclusion of the cancellation callees: the authorization was unused, and the
returned storage marks it used. -/
def CancelPost (b : Devm) (P : Adr) (a n : B256) (S : List B256) (o : Outcome) : Prop :=
  boolBit ((Devm.getStor b P).get (authSlot a.toAdr n)) = false ∧
    ∃ b' M' G', o = .returned (St b' S M' G') ∧ Devm.getStor b' P =
      (Devm.getStor b P).set (authSlot a.toAdr n) (authMark ((Devm.getStor b P).get (authSlot a.toAdr n)))

/-- **`_cancelAuthorization(authorizer, nonce, signature)`** (entry 89): entry 110, the struct digest,
the signature check (skipped) and the authorization-state write. -/
theorem e89_inv {z0 z1 z2 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (z0 :: z1 :: z2 :: ret :: S) M G) t_4a3f_c89 o) :
    CancelPost b sevm.currentTarget z2 z1 S o := by
  have nh : ∀ D, Seg.done o ≠ .done (.halted D) := fun D e =>
    SFunc.RunP.not_halted_entry cancelCallees_noHalt (k := 89) (by decide) rfl run (Seg.done.inj e)
  have h := run.cut
  clear run
  repeat istep h
  icallS h hc 110 t_524e_c110
  have hs1 := SFunc.Run.state_of_silent sil110_silent rfl rfl hc
  obtain ⟨c1, b1, M1, G1, e, -⟩ := e110_inv fork hc
  cases e
  clear hc
  replace hs1 : b1.state = b.state := hs1
  obtain ⟨b2, u0, M2, G2, hs2, h⟩ := ric_seg_e89 fork h
  rcases skip_requireValidSignature fork (by rw [getCode_of_state hs2, getCode_of_state hs1]; exact hcode)
      h with ⟨b3, M3, G3, hs3, -, h⟩ | ⟨D, -, -, e⟩
  · obtain ⟨b4, M4, G4, e, s4⟩ := k89_cancel_inv fork h
    refine ⟨c1, b4, M4, G4, Seg.done.inj e, ?_⟩
    rw [s4, hs3, congrFun (getStor_of_state hs2) _, congrFun (getStor_of_state hs1) _]
  · exact absurd e (nh D)

/-- Enter callee entry `k` (tree `T`) of `cancelCallees`. -/
macro "icallC " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry cancelCallees_noHalt
      (by decide : $k ∈ cancelCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- **`cancelAuthorization(authorizer, nonce, signature)`'s body** (entry 28): `whenNotPaused`, then
entry 89. -/
theorem e28_inv {w0 w1 w2 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (w0 :: w1 :: w2 :: ret :: S) M G) t_3498_c28 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      CancelPost b sevm.currentTarget w2 w1 S o := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c
  repeat istep h
  icallC h hc 89 t_4a3f_c89
  obtain ⟨d1, b1, M1, G1, e, s1⟩ := e89_inv fork (by rw [afterSload_getCode]; exact hcode) hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  rw [afterSload_getStor] at s1 d1
  rw [gsv] at c
  exact ⟨flag20_false_of_check c, d1, b1, _, _, Seg.done.inj e, s1⟩

/-- **`_cancelAuthorization(authorizer, nonce, v, r, s)`** (entry 97): `abi.encodePacked(r, s, v)`, then
entry 89. -/
theorem e97_inv {v0 v1 v2 v3 v4 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (v0 :: v1 :: v2 :: v3 :: v4 :: ret :: S) M G) t_4531_c97 o) :
    CancelPost b sevm.currentTarget v4 v3 S o := by
  have h := run.cut
  clear run
  repeat istepX h
  icallC h hc 89 t_4a3f_c89
  obtain ⟨d1, b1, M1, G1, e, s1⟩ := e89_inv fork hcode hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨d1, b1, _, _, Seg.done.inj e, s1⟩

/-- **`cancelAuthorization(authorizer, nonce, v, r, s)`'s body** (entry 52): `whenNotPaused`, then
entry 97. -/
theorem e52_inv {v0 v1 v2 v3 v4 ret : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (hcode : b.getCode usdcLib = Lib.code)
    (run : SFunc.Run cert.prog sevm (St b (v0 :: v1 :: v2 :: v3 :: v4 :: ret :: S) M G) t_2a20_c52 o) :
    flag20 ((Devm.getStor b sevm.currentTarget).get 1) = false ∧
      CancelPost b sevm.currentTarget v4 v3 S o := by
  have h := run.cut
  clear run
  repeat istep h
  ibranch h c
  repeat istep h
  icallC h hc 97 t_4531_c97
  obtain ⟨d1, b1, M1, G1, e, s1⟩ := e97_inv fork (by rw [afterSload_getCode]; exact hcode) hc
  cases e
  clear hc
  repeat istep h
  obtain ⟨_, e⟩ := ric_ret h
  rw [afterSload_getStor] at s1 d1
  rw [gsv] at c
  exact ⟨flag20_false_of_check c, d1, b1, _, _, Seg.done.inj e, s1⟩

end Blanc.Lift.Usdc
