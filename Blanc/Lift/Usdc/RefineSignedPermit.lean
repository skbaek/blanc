import Blanc.Lift.Usdc.RefineSignedPermitNodes

/-!
# U6e4: the per-call laws of `permit` and `cancelAuthorization`, and `impl_signed_law`

`implStepLaw_permit` and `implStepLaw_cancel`: `ImplStepLaw` for the calls of each constructor,
both ABI overloads (`(…, v, r, s)` and `(…, bytes signature)`).  A successful implementation frame
decoding the call runs its wrapper (`RefineSignedPermitFrames.lean`, route C: the digests, the
encodings and the library are skipped); read through the footprint ledger its storage at the proxy
is the book's step, and it writes neither of the proxy's two slots.  Its only external instruction
is the library `DELEGATECALL` (`RefineSignedPermitNodes.lean`), reached with the starting storage
(cancellation) or the starting storage with the owner's nonce word written (permit): the node
clause is `libNode_clause`.  `impl_signed_law` assembles these with U6e3's `implStepLaw_twa` and
`implStepLaw_rwa`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.SlotFootprint Impl

theorem decode_permit {e : Sevm} {o s : Adr} {v : Nat} (h : decodeCall e = some (.permit o s v)) :
    (Sevm.selector e = 0x9fd5a6cf ∨ Sevm.selector e = 0xd505accf) ∧
      o = (Sevm.dataWord e 4).toAdr ∧ s = (Sevm.dataWord e 36).toAdr ∧
      v = (Sevm.dataWord e 68).toNat := by
  obtain ⟨-, r, hm, hs, hr⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (cases hr; done) | (cases hr; exact ⟨.inl hs.symm, rfl, rfl, rfl⟩) |
    (cases hr; exact ⟨.inr hs.symm, rfl, rfl, rfl⟩)

theorem decode_cancel {e : Sevm} {a : Adr} {n : B256}
    (h : decodeCall e = some (.cancelAuthorization a n)) :
    (Sevm.selector e = 0xb7b72899 ∨ Sevm.selector e = 0x5a049a70) ∧
      a = (Sevm.dataWord e 4).toAdr ∧ n = Sevm.dataWord e 36 := by
  obtain ⟨-, r, hm, hs, hr⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (cases hr; done) | (cases hr; exact ⟨.inl hs.symm, rfl, rfl⟩) |
    (cases hr; exact ⟨.inr hs.symm, rfl, rfl⟩)

/-- The implementation frame's run from its pc-0 tree. -/
theorem impl_frame_run {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) :
    SFunc.Run cert.prog sevm (St pre pre.stack pre.memory pre.gasLeft) t_0000_c0 (.halted post) := by
  obtain ⟨f, hf, r⟩ := lift_sound cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at hf
  cases hf
  rw [← St.self rfl rfl]
  exact r

theorem nonce_succ_toNat (w : B256) : (w + 1).toNat = (w.toNat + 1) % 2 ^ 256 := by
  rw [B256.toNat_add, Nat.lo, show (1 : B256).toNat = 1 from rfl, Nat.add_comm]

/-- **ImplStepLaw for `permit`** (U6e4), both overloads. -/
theorem implStepLaw_permit : ImplStepLaw (fun c => ∃ o s v, c = .permit o s v) := by
  intro P U sevm pre post run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin c dec
    fam
  obtain ⟨o, s, v, rfl⟩ := fam
  subst tgt
  obtain ⟨sel, rfl, rfl, rfl⟩ := decode_permit dec
  have hcode : pre.getCode usdcLib = Lib.code := lib_code_of_image lib
  have tk : ∀ k ∈ (Call.permit (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
      (Sevm.dataWord sevm 68).toNat).keys sevm.caller, U k :=
    fun k h => keys k (keys_sub_frameKeys dec k h)
  have kn : U (.nonce (Sevm.dataWord sevm 4).toAdr) := tk _ (by
    simp only [Call.keys, List.mem_cons, true_or])
  have ka : U (.allow (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr) := tk _ (by
    simp only [Call.keys, List.mem_cons, List.not_mem_nil, or_false, or_true])
  have na : ¬ sevm.caller = (ledger U (pre.state.getStor sevm.currentTarget)).admin := notAdmin
  have hrun := impl_frame_run run codeEq fork
  obtain ⟨⟨p0, o0, s0, sp⟩, node⟩ :
      (flag20 ((pre.state.getStor sevm.currentTarget).get 1) = false ∧
        (Sevm.dataWord sevm 4).toAdr ≠ 0 ∧ (Sevm.dataWord sevm 36).toAdr ≠ 0 ∧
        post.state.getStor sevm.currentTarget = permitStor (pre.state.getStor sevm.currentTarget)
          (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68)) ∧
      ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall ∧
          ∃ w, N.devm.state.getStor sevm.currentTarget = (pre.state.getStor sevm.currentTarget).set
            (nonceSlot (Sevm.dataWord sevm 4).toAdr) w := by
    rcases sel with sel | sel
    · exact ⟨frame_permitBytes fork hcode sel hrun, permit_node_bytes run codeEq fork sel⟩
    · exact ⟨frame_permitVrs fork hcode sel hrun, permit_node_vrs run codeEq fork sel⟩
  clear hrun
  have hp : (ledger U (pre.state.getStor sevm.currentTarget)).paused = false := p0
  refine ⟨?_, ?_, ?_, fun N hN x hx => ?_⟩
  · simp only [usdcBookS, na, dec, ↓reduceIte, Ledger.step, Ledger.approveOf]
    rw [hp, ite_eq_right (by simp only [Bool.false_eq_true, not_false_eq_true]),
      ite_eq_right (by rintro (h | h); exact o0 h; exact s0 h), sp]
    unfold permitStor
    rw [ledger_set_allow inj apart ka, ledger_set_nonce_bump inj apart kn
      (by rw [nonce_succ_toNat, ledger_nonce kn])]
  · rw [sp]
    unfold permitStor
    rw [get_set_off (y := allowSlot _ _) (x := implSlot) (apart _ ka) (by decide),
      get_set_off (y := nonceSlot _) (x := implSlot) (apart _ kn) (by decide)]
  · rw [sp]
    unfold permitStor
    rw [get_set_off (y := allowSlot _ _) (x := adminSlot) (apart _ ka) (by decide),
      get_set_off (y := nonceSlot _) (x := adminSlot) (apart _ kn) (by decide)]
  · obtain ⟨rfl, w, hw⟩ := node N hN x hx
    exact ⟨rfl, libNode_clause apart (.inr ⟨_, w, kn, hw⟩)⟩

/-- **ImplStepLaw for `cancelAuthorization`** (U6e4), both overloads. -/
theorem implStepLaw_cancel : ImplStepLaw (fun c => ∃ a n, c = .cancelAuthorization a n) := by
  intro P U sevm pre post run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin c dec
    fam
  obtain ⟨a, n, rfl⟩ := fam
  subst tgt
  obtain ⟨sel, rfl, rfl⟩ := decode_cancel dec
  have hcode : pre.getCode usdcLib = Lib.code := lib_code_of_image lib
  have ka : U (.auth (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)) :=
    keys _ (keys_sub_frameKeys dec _ (by simp only [Call.keys, List.mem_cons, true_or]))
  have na : ¬ sevm.caller = (ledger U (pre.state.getStor sevm.currentTarget)).admin := notAdmin
  have hrun := impl_frame_run run codeEq fork
  obtain ⟨⟨p0, a0, sp⟩, node⟩ :
      (flag20 ((pre.state.getStor sevm.currentTarget).get 1) = false ∧
        boolBit ((pre.state.getStor sevm.currentTarget).get
          (authSlot (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36))) = false ∧
        post.state.getStor sevm.currentTarget = cancelStor (pre.state.getStor sevm.currentTarget)
          (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)) ∧
      ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall ∧ N.devm.state = pre.state := by
    rcases sel with sel | sel
    · exact ⟨frame_cancelBytes fork hcode sel hrun,
        cancel_node run codeEq fork sel route_cancel_bytes (by decide)⟩
    · exact ⟨frame_cancelVrs fork hcode sel hrun,
        cancel_node run codeEq fork sel route_cancel_vrs (by decide)⟩
  clear hrun
  have g : ¬ ((ledger U (pre.state.getStor sevm.currentTarget)).paused = true ∨
      (ledger U (pre.state.getStor sevm.currentTarget)).authUsed (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36) = true) := by
    rw [ledger_authUsed ka]
    change ¬ (flag20 _ = true ∨ _)
    rw [p0, a0]
    simp only [Bool.false_eq_true, or_self, not_false_eq_true]
  refine ⟨?_, ?_, ?_, fun N hN x hx => ?_⟩
  · simp only [usdcBookS, na, dec, ↓reduceIte, Ledger.step]
    rw [ite_eq_right g, sp]
    exact congrArg some (ledger_set_auth inj apart ka (boolBit_authMark _)).symm
  · rw [sp, cancelStor, get_set_off (y := authSlot _ _) (x := implSlot) (apart _ ka) (by decide)]
  · rw [sp, cancelStor, get_set_off (y := authSlot _ _) (x := adminSlot) (apart _ ka) (by decide)]
  · obtain ⟨rfl, hst⟩ := node N hN x hx
    exact ⟨rfl, libNode_clause apart (.inl (by rw [hst]))⟩

/-- **The step law of the signed family** (U6e): `permit`, `transferWithAuthorization`,
`receiveWithAuthorization` and `cancelAuthorization`, both overloads of each. -/
theorem impl_signed_law : ImplStepLaw famSigned := by
  intro P U sevm pre post run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin c dec
    fam
  cases c <;> simp only [famSigned] at fam
  · exact implStepLaw_permit run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin _
      dec ⟨_, _, _, rfl⟩
  · exact implStepLaw_twa run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin _ dec
      ⟨_, _, _, _, rfl⟩
  · exact implStepLaw_rwa run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin _ dec
      ⟨_, _, _, _, rfl⟩
  · exact implStepLaw_cancel run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin _
      dec ⟨_, _, rfl⟩

end Blanc.Lift.Usdc
