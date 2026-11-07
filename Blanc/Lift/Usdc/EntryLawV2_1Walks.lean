import Blanc.Lift.Usdc.V2_1Frames
import Blanc.Lift.Usdc.EntryLawV2Walks

/-!
# FiatTokenV2_1: the frames of `mint`, `transferWithAuthorization` and `receiveWithAuthorization`

`EntryLawV2Walks` with V2_1's trees: the code differs by labels and entry numbers, and by a simpler flag check.
`receiveWithAuthorization` adds a caller check before the same body, which the law does not read.
-/

namespace Blanc.Lift.Usdc.ImplV2_1

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The internal callees of these walks: none halts the frame. -/
def entryCallees : List Nat := [6, 7, 10, 15, 46, 67, 69, 73, 75, 76, 82, 83, 84, 86, 87, 89, 91]

theorem entryCallees_noHalt : NoHaltSet cert.prog entryCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `entryCallees` from a cut run `h`. -/
macro "fcall " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry entryCallees_noHalt
      (by decide : $k ∈ entryCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- **Entry 89, `_requireUnusedAuthorization`.** -/
theorem e87_inv {x y ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_4627_c87 o) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
      Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  refine ⟨_, _, _, Seg.done.inj e, by uwf, ?_⟩
  simp only [afterSloadH_getStor]

/-- **Entry 83, `_requireValidAuthorization`.** -/
theorem e82_inv {a c n w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (a :: c :: n :: w :: ret :: S) M G) t_47ff_c82 o) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
      Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget := by
  have h := run.cut
  clear run
  iterate 2 ustep h
  utime h
  iterate 2 ustep h
  ibranch h c1
  iterate 2 ustep h
  utime h
  iterate 2 ustep h
  ibranch h c2
  repeat ustep h
  fcall h hc 87 t_4627_c87
  obtain ⟨B, M1, G1, e, wf1, st⟩ := e87_inv fork wf hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, Seg.done.inj e, by uwf, st⟩

/-- **The tail of `ECRecover.recover`**: its `STATICCALL`, what it recovers left unread. -/
theorem e6_inv {c z x0 x1 x2 x3 ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (h : SFunc.RunCut cert.prog sevm []
      (St b (c :: z :: x0 :: x1 :: x2 :: x3 :: ret :: S) M G) t_49d7_c7 (Seg.done o)) :
    ∃ r b' M' G', o = .returned (St b' (r :: S) M' G') ∧ Mem.Wf M' ∧
      Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget := by
  iterate 3 ustep h
  ibranch h c1
  iterate 20 ustep h
  umemw h wf
  iterate 20 ustep h
  umemw h wf
  iterate 19 ustep h
  ugas h
  have h1 := ric_next h
  clear h
  obtain ⟨_, hd, h⟩ := h1
  obtain ⟨flag, out, hpost, -⟩ := ri_staticcallH fork.stateGas_none hd
  rw [hpost.eq_St] at h
  have st := hpost.stor sevm.currentTarget
  clear hd hpost
  umemx h wf
  ugen h
  iterate 4 ustep h
  ibranch h c2
  repeat ustep h
  ibranch h c3
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e, by uwfx, st⟩

/-- **Entry 91, `ECRecover.recover`.** -/
theorem e89_inv {x0 x1 x2 x3 ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (x0 :: x1 :: x2 :: x3 :: ret :: S) M G) t_4944_c89 o) :
    ∃ r b' M' G', o = .returned (St b' (r :: S) M' G') ∧ Mem.Wf M' ∧
      Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  iterate 10 ustep h
  ubranchTo h c2
  · iterate 7 ustep h
    exact e6_inv fork wf h
  · exact e6_inv fork wf h

/-- **Entry 84, the digest and the recovery.** -/
theorem e83_inv {p x0 x1 x2 x3 ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (p :: x0 :: x1 :: x2 :: x3 :: ret :: S) M G) t_46b5_c83 o) :
    ∃ r b' M' G', o = .returned (St b' (r :: S) M' G') ∧ Mem.Wf M' ∧
      Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget := by
  have h := run.cut
  clear run
  repeat ustep h
  fcall h hc 89 t_4944_c89
  obtain ⟨r, B, M1, G1, e, wf1, st⟩ := e89_inv fork (by uwf) hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e, wf1, st⟩

/-- **Entry 85, `_markAuthorizationUsed`.** -/
theorem e84_inv {n w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (n :: w :: ret :: S) M G) t_48bf_c84 o) :
    ∃ x b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
      Devm.getStor b' sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (ImplV2.authSlot w.toAdr n) x ∧
      AuthLogged sevm b' w.toAdr := by
  have h := run.cut
  clear run
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  refine ⟨?x, _, _, _, Seg.done.inj e, by uwf, ?_, ?_⟩
  rotate_left
  simp only [Devm.addLog_getStor, afterSstoreH_getStor_self, afterSloadH_getStor, keccak_scratch, ff20_and_word,
    word_ff20, toAdr_toB256, ImplV2.lit16, gsv]
  rfl
  refine ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, ?_⟩
  simp only [word_ff20, List.take_succ_cons, List.take_zero]
  exact congrArg₂ List.cons (by decide) rfl

/-- **Entry 67, `_transferWithAuthorization`**: the signature's checks, unread; the flag, then `_transfer`. -/
theorem e69_inv {s r v n before after val t f ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm
      (St b (s :: r :: v :: n :: before :: after :: val :: t :: f :: ret :: S) M G) t_4327_c69 o) :
    ∃ x, let σ := (Devm.getStor b sevm.currentTarget).set (ImplV2.authSlot f.toAdr n) x
      val.toNat ≤ (σ.get (balSlot f.toAdr)).toNat ∧
      val.toNat + ((σ.set (balSlot f.toAdr) (σ.get (balSlot f.toAdr) - val)).get (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
        Devm.getStor b' sevm.currentTarget = moveStor σ f.toAdr t.toAdr val ∧ AuthLogged sevm b' f.toAdr := by
  have h := run.cut
  clear run
  repeat ustep h
  fcall h hc 82 t_47ff_c82
  obtain ⟨B1, M1, G1, e, wf1, st1⟩ := e82_inv fork wf hc
  cases e
  clear hc wf
  repeat ustep h
  fcall h hc 83 t_46b5_c83
  obtain ⟨rr, B2, M2, G2, e, wf2, st2⟩ := e83_inv fork (by uwf) hc
  cases e
  clear hc wf1
  repeat ustep h
  ibranch h c1
  repeat ustep h
  fcall h hc 84 t_48bf_c84
  obtain ⟨x, B3, M3, G3, e, wf3, st3, lg3⟩ := e84_inv fork wf2 hc
  cases e
  clear hc wf2
  repeat ustep h
  fcall h hc 73 t_3b21_c73
  obtain ⟨d1, d2, B4, M4, G4, e, wf4, st4, keep4⟩ := e73_inv fork wf3 hc
  cases e
  clear hc wf3
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  have base : Devm.getStor B3 sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set (ImplV2.authSlot f.toAdr n) x := by
    rw [st3, st2]
    simp only [afterSloadH_getStor, st1]
  rw [base] at d1 d2 st4
  exact ⟨x, d1, d2, _, _, _, Seg.done.inj e, wf4, st4, lg3.mono keep4⟩

/-- **Entry 15, `transferWithAuthorization`'s modifiers.** -/
theorem e15_inv {s r v n before after val t f ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm
      (St b (s :: r :: v :: n :: before :: after :: val :: t :: f :: ret :: S) M G) t_337d_c15 o) :
    ∃ x, let σ := (Devm.getStor b sevm.currentTarget).set (ImplV2.authSlot f.toAdr n) x
      val.toNat ≤ (σ.get (balSlot f.toAdr)).toNat ∧
      val.toNat + ((σ.set (balSlot f.toAdr) (σ.get (balSlot f.toAdr) - val)).get (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
        Devm.getStor b' sevm.currentTarget = moveStor σ f.toAdr t.toAdr val ∧ AuthLogged sevm b' f.toAdr := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  ibranch h c3
  repeat ustep h
  fcall h hc 69 t_4327_c69
  obtain ⟨x, d1, d2, B, M1, G1, e, wf1, st, lg⟩ := e69_inv fork (by uwf) hc
  cases e
  clear hc
  simp only [afterSloadH_getStor] at d1 d2 st
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨x, d1, d2, _, _, _, Seg.done.inj e, wf1, st, lg⟩

/-- **The `transferWithAuthorization` frame of FiatTokenV2**: the flag at `(from, nonce)`, then the move from `from`
to `to`. What the signature recovers is not read; `noSignature` is what speaks for a holder that is `from`.
Its committed frame logs `AuthorizationUsed` with its authorizer, the check a reader of `noSignature` makes. -/
theorem frame_twa_logged {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0xe3ee160e)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    (∃ x, let σ := Stor.set (Devm.getStor b sevm.currentTarget) (ImplV2.authSlot (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)) x
      (Sevm.dataWord sevm 68).toNat ≤ (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      (Sevm.dataWord sevm 68).toNat + ((σ.set (balSlot (Sevm.dataWord sevm 4).toAdr)
        (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr) - Sevm.dataWord sevm 68)).get
          (balSlot (Sevm.dataWord sevm 36).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        moveStor σ (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68)) ∧ AuthLogged sevm post (Sevm.dataWord sevm 4).toAdr := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  fcall h hc 15 t_337d_c15
  obtain ⟨x, d1, d2, B, M1, G1, e, wf1, st, lg⟩ := e15_inv fork (by uwf) hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  clear h
  simp only [show Bytes.toB256 [64] + Bytes.toB256 [4] = 68 by decide, show Bytes.toB256 [32] + Bytes.toB256 [4] = 36 by decide,
    show Bytes.toB256 [160] + Bytes.toB256 [4] = 164 by decide, lit4, ff20_and_word, word_ff20, toAdr_toB256] at d1 d2 st lg
  exact ⟨⟨x, d1, d2, st⟩, lg⟩


/-- The move. -/
theorem frame_twa {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0xe3ee160e)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ x, let σ := Stor.set (Devm.getStor b sevm.currentTarget) (ImplV2.authSlot (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)) x
      (Sevm.dataWord sevm 68).toNat ≤ (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      (Sevm.dataWord sevm 68).toNat + ((σ.set (balSlot (Sevm.dataWord sevm 4).toAdr)
        (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr) - Sevm.dataWord sevm 68)).get
          (balSlot (Sevm.dataWord sevm 36).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        moveStor σ (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) :=
  (frame_twa_logged fork wf sel run).1


/-- **Entry 44, `mint(to, amount)`**: the supply, the credit, the minter's allowance. -/
theorem e46_inv {v t ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: ret :: S) M G) t_1cb9_c46 o) :
    ∃ m, let σ := Stor.set (Devm.getStor b sevm.currentTarget) 11 (v + (Devm.getStor b sevm.currentTarget).get 11)
      v.toNat + (σ.get (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' (Bytes.toB256 [1] :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          (σ.set (balSlot t.toAdr) (v + σ.get (balSlot t.toAdr))).set (ImplV2.minterSlot sevm.caller) m := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  unorm h
  ibranch h c2
  repeat ustep h
  unorm h
  ibranch h c3
  repeat ustep h
  unorm h
  ibranch h c4
  repeat ustep h
  ibranch h c5
  repeat ustep h
  ibranch h c6
  repeat ustep h
  unorm h
  ibranch h c7
  repeat ustep h
  fcall h hc 75 t_3e26_c75
  obtain ⟨-, G1, e⟩ := e75_inv fork hc
  cases e
  clear hc c1 c2 c3 c4 c5 c6 c7
  umemw h wf
  repeat ustep h
  unorm h
  umemw h wf
  fcall h hc 75 t_3e26_c75
  obtain ⟨d, G2, e⟩ := e75_inv fork hc
  cases e
  clear hc
  repeat ustep h
  unorm h
  umemw h wf
  fcall h hc 76 t_3d4c_c76
  obtain ⟨-, M1, G3, e, wf1⟩ := e76_inv fork wf hc
  cases e
  clear hc
  repeat ustep h
  unorm h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  simp only [afterSstoreH_getStor_self, afterSloadH_getStor, keccak_scratch, ff20_and_word, word_ff20,
    toAdr_toB256, lit9, ImplV2.lit11, ImplV2.lit13, gsv] at d
  refine ⟨?m, d, B, MB, GB, eo, ?_⟩
  rotate_left
  rw [sB]
  simp only [Devm.addLog_getStor, afterSstoreH_getStor_self, afterSloadH_getStor, keccak_scratch, ff20_and_word,
    word_ff20, toAdr_toB256, lit9, ImplV2.lit11, ImplV2.lit13, gsv]
  rfl

/-- **The `mint(to, v)` frame of FiatTokenV2.** -/
theorem frame_mint {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0x40c10f19)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ m, let σ := Stor.set (Devm.getStor b sevm.currentTarget) 11 (Sevm.dataWord sevm 36 + (Devm.getStor b sevm.currentTarget).get 11)
      (Sevm.dataWord sevm 36).toNat + (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        (σ.set (balSlot (Sevm.dataWord sevm 4).toAdr)
          (Sevm.dataWord sevm 36 + σ.get (balSlot (Sevm.dataWord sevm 4).toAdr))).set (ImplV2.minterSlot sevm.caller) m := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  fcall h hc 46 t_1cb9_c46
  obtain ⟨m, d, B, MB, GB, e, sB⟩ := e46_inv fork (by uwf) hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_return_getStor h
  clear h
  simp only [lit36] at d sB
  simp only [ff20_and_word, word_ff20, toAdr_toB256, lit4] at d sB
  exact ⟨m, d, by rw [sp, sB]⟩

/-- **Entry 67, `_receiveWithAuthorization`**: the caller check, then as `_transferWithAuthorization`. -/
theorem e67_inv {s r v n before after val t f ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm
      (St b (s :: r :: v :: n :: before :: after :: val :: t :: f :: ret :: S) M G) t_4469_c67 o) :
    ∃ x, let σ := (Devm.getStor b sevm.currentTarget).set (ImplV2.authSlot f.toAdr n) x
      val.toNat ≤ (σ.get (balSlot f.toAdr)).toNat ∧
      val.toNat + ((σ.set (balSlot f.toAdr) (σ.get (balSlot f.toAdr) - val)).get (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
        Devm.getStor b' sevm.currentTarget = moveStor σ f.toAdr t.toAdr val ∧ AuthLogged sevm b' f.toAdr := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c0
  repeat ustep h
  fcall h hc 82 t_47ff_c82
  obtain ⟨B1, M1, G1, e, wf1, st1⟩ := e82_inv fork wf hc
  cases e
  clear hc wf
  repeat ustep h
  fcall h hc 83 t_46b5_c83
  obtain ⟨rr, B2, M2, G2, e, wf2, st2⟩ := e83_inv fork (by uwf) hc
  cases e
  clear hc wf1
  repeat ustep h
  ibranch h c1
  repeat ustep h
  fcall h hc 84 t_48bf_c84
  obtain ⟨x, B3, M3, G3, e, wf3, st3, lg3⟩ := e84_inv fork wf2 hc
  cases e
  clear hc wf2
  repeat ustep h
  fcall h hc 73 t_3b21_c73
  obtain ⟨d1, d2, B4, M4, G4, e, wf4, st4, keep4⟩ := e73_inv fork wf3 hc
  cases e
  clear hc wf3
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  have base : Devm.getStor B3 sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set (ImplV2.authSlot f.toAdr n) x := by
    rw [st3, st2]
    simp only [afterSloadH_getStor, st1]
  rw [base] at d1 d2 st4
  exact ⟨x, d1, d2, _, _, _, Seg.done.inj e, wf4, st4, lg3.mono keep4⟩

/-- **Entry 10, `receiveWithAuthorization`'s modifiers.** -/
theorem e10_inv {s r v n before after val t f ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm
      (St b (s :: r :: v :: n :: before :: after :: val :: t :: f :: ret :: S) M G) t_35d8_c10 o) :
    ∃ x, let σ := (Devm.getStor b sevm.currentTarget).set (ImplV2.authSlot f.toAdr n) x
      val.toNat ≤ (σ.get (balSlot f.toAdr)).toNat ∧
      val.toNat + ((σ.set (balSlot f.toAdr) (σ.get (balSlot f.toAdr) - val)).get (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
        Devm.getStor b' sevm.currentTarget = moveStor σ f.toAdr t.toAdr val ∧ AuthLogged sevm b' f.toAdr := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  ibranch h c3
  repeat ustep h
  fcall h hc 67 t_4469_c67
  obtain ⟨x, d1, d2, B, M1, G1, e, wf1, st, lg⟩ := e67_inv fork (by uwf) hc
  cases e
  clear hc
  simp only [afterSloadH_getStor] at d1 d2 st
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨x, d1, d2, _, _, _, Seg.done.inj e, wf1, st, lg⟩

/-- **The `receiveWithAuthorization` frame of FiatTokenV2_1**: the flag at `(from, nonce)`, then the move from `from`
to `to`. What the signature recovers is not read; `noSignature` is what speaks for a holder that is `from`.
Its committed frame logs `AuthorizationUsed` with its authorizer, the check a reader of `noSignature` makes. -/
theorem frame_rwa_logged {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0xef55bec6)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    (∃ x, let σ := Stor.set (Devm.getStor b sevm.currentTarget) (ImplV2.authSlot (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)) x
      (Sevm.dataWord sevm 68).toNat ≤ (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      (Sevm.dataWord sevm 68).toNat + ((σ.set (balSlot (Sevm.dataWord sevm 4).toAdr)
        (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr) - Sevm.dataWord sevm 68)).get
          (balSlot (Sevm.dataWord sevm 36).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        moveStor σ (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68)) ∧ AuthLogged sevm post (Sevm.dataWord sevm 4).toAdr := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  fcall h hc 10 t_35d8_c10
  obtain ⟨x, d1, d2, B, M1, G1, e, wf1, st, lg⟩ := e10_inv fork (by uwf) hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  clear h
  simp only [show Bytes.toB256 [64] + Bytes.toB256 [4] = 68 by decide, show Bytes.toB256 [32] + Bytes.toB256 [4] = 36 by decide,
    show Bytes.toB256 [160] + Bytes.toB256 [4] = 164 by decide, lit4, ff20_and_word, word_ff20, toAdr_toB256] at d1 d2 st lg
  exact ⟨⟨x, d1, d2, st⟩, lg⟩


/-- The move. -/
theorem frame_rwa {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0xef55bec6)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ x, let σ := Stor.set (Devm.getStor b sevm.currentTarget) (ImplV2.authSlot (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)) x
      (Sevm.dataWord sevm 68).toNat ≤ (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      (Sevm.dataWord sevm 68).toNat + ((σ.set (balSlot (Sevm.dataWord sevm 4).toAdr)
        (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr) - Sevm.dataWord sevm 68)).get
          (balSlot (Sevm.dataWord sevm 36).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        moveStor σ (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) :=
  (frame_rwa_logged fork wf sel run).1


end Blanc.Lift.Usdc.ImplV2_1
