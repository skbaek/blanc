import Blanc.Lift.Usdc.RefineSignedAuthFrames
import Blanc.Lift.ReachPreExec
import Blanc.Lift.Usdc.RefineTransfer

/-!
# U6e3: the per-call laws of `transferWithAuthorization` and `receiveWithAuthorization`

`implStepLaw_twa` and `implStepLaw_rwa`: `ImplStepLaw` for the calls of each constructor, both
ABI overloads (`(…, v, r, s)` and `(…, bytes signature)`).  A successful implementation frame
decoding the call runs its wrapper (`RefineSignedAuthFrames.lean`): read through the footprint
ledger its storage at the proxy is the book's step (mark the authorization used, then
`Ledger.move`), and it writes neither of the proxy's two slots.  Its only external instruction is
the library `DELEGATECALL` inside `_requireValidSignature`, reached with the frame's starting world
(`Reach.preExec_state` over the certificate's before-phase sets), so the node clause is
`libNode_clause`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.SlotFootprint Impl

theorem decode_twa {e : Sevm} {s d : Adr} {v : Nat} {n : B256}
    (h : decodeCall e = some (.transferWithAuthorization s d v n)) :
    (Sevm.selector e = 0xcf092995 ∨ Sevm.selector e = 0xe3ee160e) ∧
      s = (Sevm.dataWord e 4).toAdr ∧ d = (Sevm.dataWord e 36).toAdr ∧
      v = (Sevm.dataWord e 68).toNat ∧ n = Sevm.dataWord e 164 := by
  obtain ⟨-, r, hm, hs, hr⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (cases hr; done) | (cases hr; exact ⟨.inl hs.symm, rfl, rfl, rfl, rfl⟩) |
    (cases hr; exact ⟨.inr hs.symm, rfl, rfl, rfl, rfl⟩)

theorem decode_rwa {e : Sevm} {s d : Adr} {v : Nat} {n : B256}
    (h : decodeCall e = some (.receiveWithAuthorization s d v n)) :
    (Sevm.selector e = 0x88b7ab63 ∨ Sevm.selector e = 0xef55bec6) ∧
      s = (Sevm.dataWord e 4).toAdr ∧ d = (Sevm.dataWord e 36).toAdr ∧
      v = (Sevm.dataWord e 68).toNat ∧ n = Sevm.dataWord e 164 := by
  obtain ⟨-, r, hm, hs, hr⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (cases hr; done) | (cases hr; exact ⟨.inl hs.symm, rfl, rfl, rfl, rfl⟩) |
    (cases hr; exact ⟨.inr hs.symm, rfl, rfl, rfl, rfl⟩)

/-- **The library call of an authorization frame.**  Every node of a successful implementation
frame routed to one of the authorization wrappers that decodes an external instruction is a
`DELEGATECALL` reached with the frame's starting world. -/
theorem auth_node {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) {σ : B256} {j : Nat}
    (sel : Blanc.Sevm.selector sevm = σ) (route : dispTree.selWalk σ = .inl (σ, j))
    (hj : j ∈ authW) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall ∧ N.devm.state = pre.state := by
  intro N hN x hx
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix Impl.cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl code fork hN
  obtain ⟨g0, hf0, -⟩ := ok.tree_of_exec hx
  have hT : AtExec (κ.conf N.devm) := ⟨x, g0, hf0⟩
  change Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) implProg sevm ⟨pre, Impl.t_0000_c0, []⟩
    (κ.conf N.devm) at reach
  obtain ⟨M, G, dreach⟩ := impl_preamble_reach StepIn.toRun reach hT
  rw [sel] at dreach
  obtain ⟨-, g, G', hg, greach⟩ := Reach.selWalk_inl StepIn.toRun route dreach hT
  obtain ⟨hs, x', f', hf, hx'⟩ := Reach.preExec_state StepIn.toRun auth_execFree auth_silent
    auth_preExec greach hT (.inl ⟨PreExecSet.lookup auth_preExec hj hg,
      fun _ h => absurd h List.not_mem_nil⟩)
  have e : SFunc.next (.exec x) g0 = .next (.exec x') f' := hf0.symm.trans hf
  injection e with e1
  injection e1 with e2
  subst e2
  exact ⟨by simpa only [beq_iff_eq] using hx', hs⟩

section Ledger

variable {U : Key → Prop} {σ : Stor} (inj : Inj Key.slot U) (apart : Apart Key.slot fixedSlots U)
include inj apart

/-- **The authorization frame's storage is the book's step**, and keeps the proxy's two slots.
`rcv` adds `receiveWithAuthorization`'s `to = caller` check. -/
theorem auth_ledger {sevm : Sevm} {σ' : Stor} (rcv : Prop) [Decidable rcv] (hr : ¬ rcv)
    (hs : U (.bal (Sevm.dataWord sevm 4).toAdr)) (hd : U (.bal (Sevm.dataWord sevm 36).toAdr))
    (ha : U (.auth (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)))
    (fr : AuthFrame sevm σ σ') :
    (if (ledger U σ).paused = true ∨ (ledger U σ).frozen (Sevm.dataWord sevm 4).toAdr = true ∨
        (ledger U σ).frozen (Sevm.dataWord sevm 36).toAdr = true ∨ rcv ∨
        (ledger U σ).authUsed (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164) = true
      then none else ((ledger U σ).useAuth (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 164)).move (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68).toNat) = some (ledger U σ') ∧
      σ'.get implSlot = σ.get implSlot ∧ σ'.get adminSlot = σ.get adminSlot := by
  obtain ⟨p0, f1, f2, -, -, a0, s0, d0, hv, fs, fd, hb, rfl⟩ := fr
  have g : ¬ ((ledger U σ).paused = true ∨ (ledger U σ).frozen (Sevm.dataWord sevm 4).toAdr = true ∨
      (ledger U σ).frozen (Sevm.dataWord sevm 36).toAdr = true ∨ rcv ∨
      (ledger U σ).authUsed (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164) = true) := by
    rw [ledger_frozen hs, ledger_frozen hd, ledger_authUsed ha]
    change ¬ (flag20 _ = true ∨ _)
    rw [p0, f1, f2, a0]
    simp only [Bool.false_eq_true, false_or, or_false]
    exact hr
  have mark : (ledger U σ).useAuth (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164) =
      ledger U (markStor σ (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)) :=
    (ledger_set_auth inj apart ha (boolBit_authMark _)).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [ite_eq_right g, mark]
    exact ledger_move inj apart hs hd s0 d0 fs hv fd hb
  · unfold creditStor debitStor markStor
    rw [get_set_off (y := balSlot _) (x := implSlot) (apart _ hd) (by decide),
      get_set_off (y := balSlot _) (x := implSlot) (apart _ hs) (by decide),
      get_set_off (y := authSlot _ _) (x := implSlot) (apart _ ha) (by decide)]
  · unfold creditStor debitStor markStor
    rw [get_set_off (y := balSlot _) (x := adminSlot) (apart _ hd) (by decide),
      get_set_off (y := balSlot _) (x := adminSlot) (apart _ hs) (by decide),
      get_set_off (y := authSlot _ _) (x := adminSlot) (apart _ ha) (by decide)]

end Ledger

/-- **ImplStepLaw for `transferWithAuthorization`** (U6e3), both overloads. -/
theorem implStepLaw_twa :
    ImplStepLaw (fun c => ∃ s d v n, c = .transferWithAuthorization s d v n) := by
  intro P U sevm pre post run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin c dec
    fam
  obtain ⟨s, d, v, n, rfl⟩ := fam
  subst tgt
  obtain ⟨sel, rfl, rfl, rfl, rfl⟩ := decode_twa dec
  have hcode : pre.getCode usdcLib = Lib.code := lib_code_of_image lib
  have tk : ∀ k ∈ (Call.transferWithAuthorization (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68).toNat
      (Sevm.dataWord sevm 164)).keys sevm.caller, U k :=
    fun k h => keys k (keys_sub_frameKeys dec k h)
  have hs : U (.bal (Sevm.dataWord sevm 4).toAdr) := tk _ (by simp only [Call.keys, List.mem_cons, true_or])
  have hd : U (.bal (Sevm.dataWord sevm 36).toAdr) := tk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])
  have ha : U (.auth (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)) := tk _ (by simp only [Call.keys, List.mem_cons, List.not_mem_nil, or_false, or_true])
  have na : ¬ sevm.caller = (ledger U (pre.state.getStor sevm.currentTarget)).admin := notAdmin
  obtain ⟨fr, node⟩ : AuthFrame sevm (pre.state.getStor sevm.currentTarget)
        (post.state.getStor sevm.currentTarget) ∧
      ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall ∧ N.devm.state = pre.state := by
    rcases sel with sel | sel
    · exact ⟨frame_twa_bytes run codeEq fork hcode sel,
        auth_node run codeEq fork sel route_twa_bytes (by decide)⟩
    · exact ⟨frame_twa_vrs run codeEq fork hcode sel,
        auth_node run codeEq fork sel route_twa_vrs (by decide)⟩
  obtain ⟨step, ki, ka⟩ := auth_ledger inj apart False not_false hs hd ha fr
  refine ⟨?_, ki, ka, fun N hN x hx => ?_⟩
  · simp only [usdcBookS, na, dec, ↓reduceIte, Ledger.step]
    simpa only [false_or] using step
  · obtain ⟨rfl, hst⟩ := node N hN x hx
    have h := libNode_clause (N := N.devm.state.getStor sevm.currentTarget) apart
      (.inl (by rw [hst]))
    exact ⟨rfl, h⟩

/-- **ImplStepLaw for `receiveWithAuthorization`** (U6e3), both overloads. -/
theorem implStepLaw_rwa :
    ImplStepLaw (fun c => ∃ s d v n, c = .receiveWithAuthorization s d v n) := by
  intro P U sevm pre post run codeEq tgt codeAddr fork nonstatic inj apart keys lib notAdmin c dec
    fam
  obtain ⟨s, d, v, n, rfl⟩ := fam
  subst tgt
  obtain ⟨sel, rfl, rfl, rfl, rfl⟩ := decode_rwa dec
  have hcode : pre.getCode usdcLib = Lib.code := lib_code_of_image lib
  have tk : ∀ k ∈ (Call.receiveWithAuthorization (Sevm.dataWord sevm 4).toAdr
      (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68).toNat
      (Sevm.dataWord sevm 164)).keys sevm.caller, U k :=
    fun k h => keys k (keys_sub_frameKeys dec k h)
  have hs : U (.bal (Sevm.dataWord sevm 4).toAdr) := tk _ (by simp only [Call.keys, List.mem_cons, true_or])
  have hd : U (.bal (Sevm.dataWord sevm 36).toAdr) := tk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])
  have ha : U (.auth (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)) := tk _ (by simp only [Call.keys, List.mem_cons, List.not_mem_nil, or_false, or_true])
  have na : ¬ sevm.caller = (ledger U (pre.state.getStor sevm.currentTarget)).admin := notAdmin
  obtain ⟨cl, fr, node⟩ : sevm.caller = (Sevm.dataWord sevm 36).toAdr ∧ AuthFrame sevm (pre.state.getStor sevm.currentTarget)
        (post.state.getStor sevm.currentTarget) ∧
      ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall ∧ N.devm.state = pre.state := by
    rcases sel with sel | sel
    · exact ⟨(frame_rwa_bytes run codeEq fork hcode sel).1, (frame_rwa_bytes run codeEq fork hcode sel).2,
        auth_node run codeEq fork sel route_rwa_bytes (by decide)⟩
    · exact ⟨(frame_rwa_vrs run codeEq fork hcode sel).1, (frame_rwa_vrs run codeEq fork hcode sel).2,
        auth_node run codeEq fork sel route_rwa_vrs (by decide)⟩
  obtain ⟨step, ki, ka⟩ := auth_ledger inj apart ((Sevm.dataWord sevm 36).toAdr ≠ sevm.caller)
    (fun h => h cl.symm) hs hd ha fr
  refine ⟨?_, ki, ka, fun N hN x hx => ?_⟩
  · simp only [usdcBookS, na, dec, ↓reduceIte, Ledger.step]
    exact step
  · obtain ⟨rfl, hst⟩ := node N hN x hx
    have h := libNode_clause (N := N.devm.state.getStor sevm.currentTarget) apart
      (.inl (by rw [hst]))
    exact ⟨rfl, h⟩

end Blanc.Lift.Usdc
