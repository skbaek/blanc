import Blanc.Lift.Usdc.V2Frames
import Blanc.Lift.HistStaticCall

/-!
# FiatTokenV2: the frames of `mint` and `transferWithAuthorization`, inverted

`frame_mint`: the balance credit, with the supply and the minter's allowance. `frame_twa`: through the validity check
and the signature recovery (the `STATICCALL` to `ecrecover`; what it answers is not read), the authorization flag, then
`_transfer`. Anyone can send the signed one, so a credit by it needs this walk, not a premise.
-/

namespace Blanc.Lift.Usdc.ImplV2

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The internal callees of these walks: none halts the frame. -/
def entryCallees : List Nat := [5, 6, 15, 44, 67, 74, 77, 78, 83, 84, 85, 88, 89, 91, 93]

theorem entryCallees_noHalt : NoHaltSet cert.prog entryCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `entryCallees` from a cut run `h`. -/
macro "ecall " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry entryCallees_noHalt
      (by decide : $k ∈ entryCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- `TIMESTAMP`, which `ustep` does not take. -/
macro "utime " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_timestamp hd
   subst e; clear hd))

/-- `uwf`, past a `STATICCALL`'s memory. -/
macro "uwfx" : tactic => `(tactic|
  repeat (first
    | with_reducible apply Mem.Wf.write
    | with_reducible apply Mem.Wf.read_snd
    | with_reducible apply Mem.Wf.extends
    | with_reducible assumption))

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- `umemw`, past a `STATICCALL`'s memory. -/
elab "umemx " h:ident wf:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some st := ty.find? (fun x => x.isAppOfArity ``Blanc.Lift.St 4)
    | throwError "umemx: no walk state"
  let ms ← Term.exprToSyntax (st.getArg! 2)
  let mn := mkIdent (← mkFreshUserName `M)
  let wn := mkIdent (← mkFreshUserName `wfn)
  evalTactic (← `(tactic| (have $wn:ident : Mem.Wf $ms := by uwfx)))
  evalTactic (← `(tactic| clear $wf:ident))
  evalTactic (← `(tactic| generalize $ms = $mn:ident at $h:ident $wn:ident))
  evalTactic (← `(tactic| rename_i $wf:ident))

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- Generalize the stack words of the walk state of cut run `h` that are not variables: a walk past them reads none
of them, and their size is what `whnf` pays for. -/
elab "ugen " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let some st := ty.find? (fun x => x.isAppOfArity ``Blanc.Lift.St 4)
    | throwError "ugen: no walk state"
  let mut stack := st.getArg! 1
  let mut words : Array Expr := #[]
  while stack.isAppOfArity ``List.cons 3 do
    let w := stack.getArg! 1
    unless w.isFVar do words := words.push w
    stack := stack.getArg! 2
  for w in words do
    let wStx ← Term.exprToSyntax w
    let n := mkIdent (← mkFreshUserName `w)
    evalTactic (← `(tactic| try generalize $wStx = $n:ident at $h:ident))

/-- **Entry 89, `_requireUnusedAuthorization`.** -/
theorem e89_inv {x y ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: ret :: S) M G) t_4c93_c89 o) :
    ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
      Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  refine ⟨_, _, _, Seg.done.inj e, by uwf, ?_⟩
  simp only [afterSloadH_getStor]

/-- **Entry 83, `_requireValidAuthorization`.** -/
theorem e83_inv {a c n w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (a :: c :: n :: w :: ret :: S) M G) t_4d9e_c83 o) :
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
  ecall h hc 89 t_4c93_c89
  obtain ⟨B, M1, G1, e, wf1, st⟩ := e89_inv fork wf hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, Seg.done.inj e, by uwf, st⟩

/-- **The tail of `ECRecover.recover`**: its `STATICCALL`, what it recovers left unread. -/
theorem e6_inv {c z x0 x1 x2 x3 ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (h : SFunc.RunCut cert.prog sevm []
      (St b (c :: z :: x0 :: x1 :: x2 :: x3 :: ret :: S) M G) t_504e_c6 (Seg.done o)) :
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
theorem e91_inv {x0 x1 x2 x3 ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (x0 :: x1 :: x2 :: x3 :: ret :: S) M G) t_4fbb_c91 o) :
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
theorem e84_inv {p x0 x1 x2 x3 ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (p :: x0 :: x1 :: x2 :: x3 :: ret :: S) M G) t_4d2c_c84 o) :
    ∃ r b' M' G', o = .returned (St b' (r :: S) M' G') ∧ Mem.Wf M' ∧
      Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget := by
  have h := run.cut
  clear run
  repeat ustep h
  ecall h hc 91 t_4fbb_c91
  obtain ⟨r, B, M1, G1, e, wf1, st⟩ := e91_inv fork (by uwf) hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e, wf1, st⟩

/-- The authorization flag (`_authorizationStates`, slot 16). -/
def authSlot (a : Adr) (n : B256) : B256 := mapSlot n (mapSlot a.toB256 16)

theorem lit16 : Bytes.toB256 [16] = 16 := by decide

/-- **Entry 85, `_markAuthorizationUsed`.** -/
theorem e85_inv {n w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (n :: w :: ret :: S) M G) t_4e5e_c85 o) :
    ∃ x b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
      Devm.getStor b' sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (authSlot w.toAdr n) x := by
  have h := run.cut
  clear run
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  refine ⟨?x, _, _, _, Seg.done.inj e, by uwf, ?_⟩
  rotate_left
  simp only [Devm.addLog_getStor, afterSstoreH_getStor_self, afterSloadH_getStor, keccak_scratch, ff20_and_word,
    word_ff20, toAdr_toB256, lit16, gsv]
  rfl

/-- **Entry 67, `_transferWithAuthorization`**: the signature's checks, unread; the flag, then `_transfer`. -/
theorem e67_inv {s r v n before after val t f ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm
      (St b (s :: r :: v :: n :: before :: after :: val :: t :: f :: ret :: S) M G) t_4aac_c67 o) :
    ∃ x, let σ := (Devm.getStor b sevm.currentTarget).set (authSlot f.toAdr n) x
      val.toNat ≤ (σ.get (balSlot f.toAdr)).toNat ∧
      val.toNat + ((σ.set (balSlot f.toAdr) (σ.get (balSlot f.toAdr) - val)).get (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
        Devm.getStor b' sevm.currentTarget = moveStor σ f.toAdr t.toAdr val := by
  have h := run.cut
  clear run
  repeat ustep h
  ecall h hc 83 t_4d9e_c83
  obtain ⟨B1, M1, G1, e, wf1, st1⟩ := e83_inv fork wf hc
  cases e
  clear hc wf
  repeat ustep h
  ecall h hc 84 t_4d2c_c84
  obtain ⟨rr, B2, M2, G2, e, wf2, st2⟩ := e84_inv fork (by uwf) hc
  cases e
  clear hc wf1
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ecall h hc 85 t_4e5e_c85
  obtain ⟨x, B3, M3, G3, e, wf3, st3⟩ := e85_inv fork wf2 hc
  cases e
  clear hc wf2
  repeat ustep h
  ecall h hc 74 t_3ef8_c74
  obtain ⟨d1, d2, B4, M4, G4, e, wf4, st4⟩ := e74_inv fork wf3 hc
  cases e
  clear hc wf3
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  have base : Devm.getStor B3 sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set (authSlot f.toAdr n) x := by
    rw [st3, st2]
    simp only [afterSloadH_getStor, st1]
  rw [base] at d1 d2 st4
  exact ⟨x, d1, d2, _, _, _, Seg.done.inj e, wf4, st4⟩

/-- **Entry 15, `transferWithAuthorization`'s modifiers.** -/
theorem e15_inv {s r v n before after val t f ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm
      (St b (s :: r :: v :: n :: before :: after :: val :: t :: f :: ret :: S) M G) t_38fe_c15 o) :
    ∃ x, let σ := (Devm.getStor b sevm.currentTarget).set (authSlot f.toAdr n) x
      val.toNat ≤ (σ.get (balSlot f.toAdr)).toNat ∧
      val.toNat + ((σ.set (balSlot f.toAdr) (σ.get (balSlot f.toAdr) - val)).get (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' S M' G') ∧ Mem.Wf M' ∧
        Devm.getStor b' sevm.currentTarget = moveStor σ f.toAdr t.toAdr val := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  ibranch h c3
  repeat ustep h
  ecall h hc 67 t_4aac_c67
  obtain ⟨x, d1, d2, B, M1, G1, e, wf1, st⟩ := e67_inv fork (by uwf) hc
  cases e
  clear hc
  simp only [afterSloadH_getStor] at d1 d2 st
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨x, d1, d2, _, _, _, Seg.done.inj e, wf1, st⟩

/-- **The `transferWithAuthorization` frame of FiatTokenV2**: the flag at `(from, nonce)`, then the move from `from`
to `to`. What the signature recovers is not read; `noSignature` is what speaks for a holder that is `from`. -/
theorem frame_twa {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0xe3ee160e)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ x, let σ := Stor.set (Devm.getStor b sevm.currentTarget) (authSlot (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)) x
      (Sevm.dataWord sevm 68).toNat ≤ (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      (Sevm.dataWord sevm 68).toNat + ((σ.set (balSlot (Sevm.dataWord sevm 4).toAdr)
        (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr) - Sevm.dataWord sevm 68)).get
          (balSlot (Sevm.dataWord sevm 36).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        moveStor σ (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ecall h hc 15 t_38fe_c15
  obtain ⟨x, d1, d2, B, M1, G1, e, wf1, st⟩ := e15_inv fork (by uwf) hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  clear h
  simp only [lit4, lit36, show Bytes.toB256 [4] + Bytes.toB256 [64] = 68 by decide,
    show Bytes.toB256 [4] + Bytes.toB256 [32] = 36 by decide,
    show Bytes.toB256 [32] + Bytes.toB256 [4] = 36 by decide,
    show Bytes.toB256 [64] + Bytes.toB256 [4] = 68 by decide,
    show Bytes.toB256 [160] + Bytes.toB256 [4] = 164 by decide,
    show Bytes.toB256 [4] + Bytes.toB256 [160] = 164 by decide,
    ff20_and_word, word_ff20, toAdr_toB256] at d1 d2 st
  exact ⟨x, d1, d2, st⟩

/-- The minter's allowance (`minterAllowed`, slot 13). -/
def minterSlot (a : Adr) : B256 := mapSlot a.toB256 13

theorem lit13 : Bytes.toB256 [13] = 13 := by decide
theorem lit11 : Bytes.toB256 [11] = 11 := by decide

/-- **Entry 44, `mint(to, amount)`**: the supply, the credit, the minter's allowance. -/
theorem e44_inv {v t ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (run : SFunc.Run cert.prog sevm (St b (v :: t :: ret :: S) M G) t_1d43_c44 o) :
    ∃ m, let σ := Stor.set (Devm.getStor b sevm.currentTarget) 11 (v + (Devm.getStor b sevm.currentTarget).get 11)
      v.toNat + (σ.get (balSlot t.toAdr)).toNat < 2 ^ 256 ∧
      ∃ b' M' G', o = .returned (St b' (Bytes.toB256 [1] :: S) M' G') ∧
        Devm.getStor b' sevm.currentTarget =
          (σ.set (balSlot t.toAdr) (v + σ.get (balSlot t.toAdr))).set (minterSlot sevm.caller) m := by
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
  ucall h hc 77 t_41fd_c77
  obtain ⟨-, G1, e⟩ := e77_inv fork hc
  cases e
  clear hc c1 c2 c3 c4 c5 c6 c7
  umemw h wf
  repeat ustep h
  unorm h
  umemw h wf
  ucall h hc 77 t_41fd_c77
  obtain ⟨d, G2, e⟩ := e77_inv fork hc
  cases e
  clear hc
  repeat ustep h
  unorm h
  umemw h wf
  ucall h hc 78 t_4123_c78
  obtain ⟨-, M1, G3, e, wf1⟩ := e78_inv fork wf hc
  cases e
  clear hc
  repeat ustep h
  unorm h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  obtain ⟨B, MB, GB, eo, sB⟩ := ret_named e
  clear e
  simp only [afterSstoreH_getStor_self, afterSloadH_getStor, keccak_scratch, ff20_and_word, word_ff20,
    toAdr_toB256, lit9, lit11, lit13, gsv] at d
  refine ⟨?m, d, B, MB, GB, eo, ?_⟩
  rotate_left
  rw [sB]
  simp only [Devm.addLog_getStor, afterSstoreH_getStor_self, afterSloadH_getStor, keccak_scratch, ff20_and_word,
    word_ff20, toAdr_toB256, lit9, lit11, lit13, gsv]
  rfl

/-- **The `mint(to, v)` frame of FiatTokenV2.** -/
theorem frame_mint {post : Devm} (fork : HistFork sevm.benvStat.fork) (wf : Mem.Wf M)
    (sel : Blanc.Sevm.selector sevm = 0x40c10f19)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ m, let σ := Stor.set (Devm.getStor b sevm.currentTarget) 11 (Sevm.dataWord sevm 36 + (Devm.getStor b sevm.currentTarget).get 11)
      (Sevm.dataWord sevm 36).toNat + (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        (σ.set (balSlot (Sevm.dataWord sevm 4).toAdr)
          (Sevm.dataWord sevm 36 + σ.get (balSlot (Sevm.dataWord sevm 4).toAdr))).set (minterSlot sevm.caller) m := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ecall h hc 44 t_1d43_c44
  obtain ⟨m, d, B, MB, GB, e, sB⟩ := e44_inv fork (by uwf) hc
  cases e
  clear hc
  repeat ustep h
  have sp := ric_return_getStor h
  clear h
  simp only [lit36] at d sB
  simp only [ff20_and_word, word_ff20, toAdr_toB256, lit4] at d sB
  exact ⟨m, d, by rw [sp, sB]⟩

end Blanc.Lift.Usdc.ImplV2
