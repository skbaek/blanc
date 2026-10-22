import Blanc.Composition.Curve3Pool3CrvCoinExactTransport
import Blanc.Lift.Curve3Pool.ExactLivePremises

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift
open VyperNonreentrantDeployed.Token20 (balSlot allowSlot)

/-- The push's charge, chosen from a normalized input before caller gas is supplied. -/
def token20PushDebit (sevm : Sevm) (t ii oi : B256) (b : Devm) (S : List B256) (M : Mem) : Nat :=
  ccAcc (b.withGasLeft 0) S M 0 t + ccExt (b.withGasLeft 0) S M 0 ii 0x44 oi +
    VyperNonreentrantDeployed.Token20.transferGas
      (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi))
      (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi))

/-- The full push successor at normalized input and final residual gas. -/
def token20PushNext (sevm : Sevm) (t ii oi : B256) (b : Devm) (S : List B256) (M : Mem) : Devm :=
  ccPost (b.withGasLeft 0) S M 0 t ii 0x44 oi
    (VyperNonreentrantDeployed.Token20.transferPost
      (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi))
      (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi)) 0)

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {c : Adr} {U : Nat} {ii oi : B256}

/-- Token20's actual transfer realizes an exact parent-call profile. -/
theorem token20_coinPushExactAt (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hne : c ≠ sevm.currentTarget)
    (hU : 80000 ≤ U) (hii : ii.toNat + 0x44 ≤ 3104) (hoi : oi.toNat + 32 ≤ 3104)
    (hW : ∀ b, W b → b.getCode c = VyperNonreentrantDeployed.Token20.code ∧
      T20MoveFits (b.getStor c) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves c (t20Move (b.getStor c) sevm.currentTarget sevm.caller amt)
      ((getOrigAcct sevm c).stor = b.getStor c ∧ c ∉ b.createdAccounts ∧
        balSlot sevm.currentTarget ≠ balSlot sevm.caller) b d → W' d) :
    Curve3Pool.CoinPushExactAt sevm W W' t amt U ii oi := by
  refine ⟨token20PushDebit sevm t ii oi, token20PushNext sevm t ii oi, ?_⟩
  refine { entry_gas := ?_, congr := ?_, sound := ?_ }
  · intros; rfl
  · intro b b' S M h
    unfold token20PushDebit token20PushNext
    rw [h.withGasLeft_eq 0]
    exact ⟨rfl, .refl _⟩
  · rintro b S M G ⟨hW0, hUG, hG, hin, hS⟩
    obtain ⟨hc, hfits⟩ := hW b hW0
    have hext : ccExt b S M G ii 0x44 oi ≤ 309 :=
      ccExt_le (by decide) (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii) hoi
    have hfwd := ccFwd_ge (t := t) (by omega) hext
    obtain ⟨cpost, used, hcost, hchildpost, hexec, herr, hout, hgas, hused,
        hcode, hstor, hs, hcr, hrf⟩ := push_child_exact hfork hstatic ht hc hin hfits hfwd
    have hnCost : used = VyperNonreentrantDeployed.Token20.transferGas
        (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi))
        (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi)) := by
      rw [hcost]
      unfold ccMsg
      rw [AllGasCall.message_sevm_reframe, AllGasCall.message_devm_reframe]
      exact t20_transferGas_reframe _ _ _
    have hdebit : token20PushDebit sevm t ii oi b S M =
        ccAcc b S M G t + ccExt b S M G ii 0x44 oi + used := by
      unfold token20PushDebit
      rw [← hnCost]
      rfl
    have haccCost := ccAcc_le (b := b) (S := S) (M := M) (G := G) (t := t)
    have hfund : ccFwd b S M G t ii 0x44 oi + ccAcc b S M G t +
        ccExt b S M G ii 0x44 oi ≤ G := by
      have := cc_fwd_le b S M G t ii 0x44 oi
      omega
    have hsum := AllGasCall.resume_debit b S M G t ii 0x44 oi cpost used hfund
      (by change used ≤ ccFwd b S M G t ii 0x44 oi; omega) hgas
    change G = (ccPost b S M G t ii 0x44 oi cpost).gasLeft +
      (ccAcc b S M G t + ccExt b S M G ii 0x44 oi + used) at hsum
    rw [← hdebit] at hsum
    have hp : Devm.EqModGas (ccParent b S M G t ii 0x44 oi)
        (ccParent (b.withGasLeft 0) S M 0 t ii 0x44 oi) := by
      apply Devm.EqModGas.of_normalized_eq
      rfl
    have hcp : Devm.EqModGas cpost
        (VyperNonreentrantDeployed.Token20.transferPost
          (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi))
          (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi)) 0) := by
      rw [hchildpost]
      unfold ccMsg
      rw [AllGasCall.message_sevm_reframe, AllGasCall.message_devm_reframe,
        t20_transferPost_reframe]
      exact t20_transferPost_residual _ _ _
    have hn : Devm.EqModGas (ccPost b S M G t ii 0x44 oi cpost)
        (token20PushNext sevm t ii oi b S M) :=
      hp.callChildPost hcp oi.toNat 32
    obtain ⟨hrun, hpost, hok, hlen, hg1, hg2, hst, hacc⟩ := cc_answer_true hfork
      (by rw [ht, show b.state.getCode c = b.getCode c from rfl, hc]; exact token20_undelegated)
      hdepth (by rw [ht]; exact prec_false hprec) hS hG (by omega) hext hused hexec herr hout hgas
    refine ⟨by rw [hdebit]; omega, _, hrun, hsum, hn, hpost, hok, hlen,
      by rw [getStor_of_state hst, hstor _ (Ne.symm hne)],
      hW' b _ hW0 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      idReady_of_child (by rw [getCode_of_state hst, hcode]) hacc⟩
    · intro a; rw [getCode_of_state hst, hcode]
    · intro a ha; rw [getStor_of_state hst, hstor a ha]
    · rw [getStor_of_state hst, hs]
    · exact ccPost_error ..
    · exact (ccPost_created ..).trans hcr
    · rintro ⟨h1, h2, h3⟩
      rw [ccPost_refund]
      have := hrf h1 h2 h3
      omega

/-- The pull's charge, chosen from a normalized input before caller gas is supplied. -/
def token20PullDebit (sevm : Sevm) (t ii oi : B256) (b : Devm) (S : List B256) (M : Mem) : Nat :=
  ccAcc (b.withGasLeft 0) S M 0 t + ccExt (b.withGasLeft 0) S M 0 ii 0x64 oi +
    VyperNonreentrantDeployed.Token20.transferFromGas
      (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi))
      (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi))

/-- The full pull successor at normalized input and final residual gas. -/
def token20PullNext (sevm : Sevm) (t ii oi : B256) (b : Devm) (S : List B256) (M : Mem) : Devm :=
  ccPost (b.withGasLeft 0) S M 0 t ii 0x64 oi
    (VyperNonreentrantDeployed.Token20.transferFromPost
      (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi))
      (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi)) 0)

/-- Token20's actual transferFrom realizes an exact parent-call profile. -/
theorem token20_coinPullExactAt (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hne : c ≠ sevm.currentTarget)
    (hU : 80000 ≤ U) (hii : ii.toNat + 0x64 ≤ 3104) (hoi : oi.toNat + 32 ≤ 3104)
    (hW : ∀ b, W b → b.getCode c = VyperNonreentrantDeployed.Token20.code ∧
      T20PullFits (b.getStor c) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves c (t20Move (t20Allow (b.getStor c) sevm.caller
        sevm.currentTarget amt) sevm.caller sevm.currentTarget amt)
      ((getOrigAcct sevm c).stor = b.getStor c ∧ c ∉ b.createdAccounts ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.caller ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.currentTarget ∧
        balSlot sevm.caller ≠ balSlot sevm.currentTarget) b d → W' d) :
    Curve3Pool.CoinPullExactAt sevm W W' t amt U ii oi := by
  refine ⟨token20PullDebit sevm t ii oi, token20PullNext sevm t ii oi, ?_⟩
  refine { entry_gas := ?_, congr := ?_, sound := ?_ }
  · intros; rfl
  · intro b b' S M h
    unfold token20PullDebit token20PullNext
    rw [h.withGasLeft_eq 0]
    exact ⟨rfl, .refl _⟩
  · rintro b S M G ⟨hW0, hUG, hG, hin, hS⟩
    obtain ⟨hc, hfits⟩ := hW b hW0
    have hext : ccExt b S M G ii 0x64 oi ≤ 309 :=
      ccExt_le (by decide) (by rw [show (0x64 : B256).toNat = 0x64 from rfl]; exact hii) hoi
    have hfwd := ccFwd_ge (t := t) (by omega) hext
    obtain ⟨cpost, used, hcost, hchildpost, hexec, herr, hout, hgas, hused,
        hcode, hstor, hs, hcr, hrf⟩ := pull_child_exact hfork hstatic ht hc hin hfits hfwd
    have hnCost : used = VyperNonreentrantDeployed.Token20.transferFromGas
        (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi))
        (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi)) := by
      rw [hcost]
      unfold ccMsg
      rw [AllGasCall.message_sevm_reframe, AllGasCall.message_devm_reframe]
      exact t20_transferFromGas_reframe _ _ _
    have hdebit : token20PullDebit sevm t ii oi b S M =
        ccAcc b S M G t + ccExt b S M G ii 0x64 oi + used := by
      unfold token20PullDebit
      rw [← hnCost]
      rfl
    have haccCost := ccAcc_le (b := b) (S := S) (M := M) (G := G) (t := t)
    have hfund : ccFwd b S M G t ii 0x64 oi + ccAcc b S M G t +
        ccExt b S M G ii 0x64 oi ≤ G := by
      have := cc_fwd_le b S M G t ii 0x64 oi
      omega
    have hsum := AllGasCall.resume_debit b S M G t ii 0x64 oi cpost used hfund
      (by change used ≤ ccFwd b S M G t ii 0x64 oi; omega) hgas
    change G = (ccPost b S M G t ii 0x64 oi cpost).gasLeft +
      (ccAcc b S M G t + ccExt b S M G ii 0x64 oi + used) at hsum
    rw [← hdebit] at hsum
    have hp : Devm.EqModGas (ccParent b S M G t ii 0x64 oi)
        (ccParent (b.withGasLeft 0) S M 0 t ii 0x64 oi) := by
      apply Devm.EqModGas.of_normalized_eq
      rfl
    have hcp : Devm.EqModGas cpost
        (VyperNonreentrantDeployed.Token20.transferFromPost
          (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi))
          (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x64 oi)) 0) := by
      rw [hchildpost]
      unfold ccMsg
      rw [AllGasCall.message_sevm_reframe, AllGasCall.message_devm_reframe,
        t20_transferFromPost_reframe]
      exact t20_transferFromPost_residual _ _ _
    have hn : Devm.EqModGas (ccPost b S M G t ii 0x64 oi cpost)
        (token20PullNext sevm t ii oi b S M) :=
      hp.callChildPost hcp oi.toNat 32
    obtain ⟨hrun, hpost, hok, hlen, hg1, hg2, hst, hacc⟩ := cc_answer_true hfork
      (by rw [ht, show b.state.getCode c = b.getCode c from rfl, hc]; exact token20_undelegated)
      hdepth (by rw [ht]; exact prec_false hprec) hS hG (by omega) hext hused hexec herr hout hgas
    refine ⟨by rw [hdebit]; omega, _, hrun, hsum, hn, hpost, hok, hlen,
      by rw [getStor_of_state hst, hstor _ (Ne.symm hne)],
      hW' b _ hW0 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      idReady_of_child (by rw [getCode_of_state hst, hcode]) hacc⟩
    · intro a; rw [getCode_of_state hst, hcode]
    · intro a ha; rw [getStor_of_state hst, hstor a ha]
    · rw [getStor_of_state hst, hs]
    · exact ccPost_error ..
    · exact (ccPost_created ..).trans hcr
    · rintro ⟨h1, h2, h3, h4, h5⟩
      rw [ccPost_refund]
      have := hrf h1 h2 h3 h4 h5
      omega

section Balance

open Curve3PoolCalleeLive VyperNonreentrantDeployed.Token20

/-- Exact balance-call charge from the normalized input, chosen before caller gas. -/
def token20BalanceDebit (sevm : Sevm) (t ii oi : B256) (b : Devm) (S : List B256) (M : Mem) : Nat :=
  ccAcc (b.withGasLeft 0) S M 0 t + ccExt (b.withGasLeft 0) S M 0 ii 0x24 oi +
    balanceOfGas (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi))
      (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi))

/-- Full canonical successor for the balance call, normalized only in execution gas. -/
def token20BalanceNext (sevm : Sevm) (t ii oi : B256) (b : Devm) (S : List B256) (M : Mem) : Devm :=
  ccPost (b.withGasLeft 0) S M 0 t ii 0x24 oi
    (balanceOfPost (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi))
      (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi)) 0)

variable {B : B256}

/-- Token20's actual static balance execution realizes an exact parent-call profile. -/
theorem token20_coinBalExactAt (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode c = VyperNonreentrantDeployed.Token20.code ∧
      (b.getStor c).get (balSlot sevm.currentTarget) = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    Curve3Pool.CoinBalExactAt sevm W W' t B U ii oi := by
  refine ⟨token20BalanceDebit sevm t ii oi, token20BalanceNext sevm t ii oi, ?_⟩
  refine { entry_gas := ?_, congr := ?_, sound := ?_ }
  · intros; rfl
  · intro b b' S M h
    unfold token20BalanceDebit token20BalanceNext
    rw [h.withGasLeft_eq 0]
    exact ⟨rfl, .refl _⟩
  · rintro b S M G ⟨hWb, hUG, hG, hin, hS⟩
    obtain ⟨hcharge, hfwd⟩ := fwd_ge (b := b) (S := S) (M := M) (t := t) (G := G)
      (ii := ii) (is := 0x24) (oi := oi) (os := 0x20)
      (by omega) (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii) hoi
    obtain ⟨hc, hB⟩ := hW b hWb
    obtain ⟨cpost, used, hcost, hchildpost, hdel, hexec, herr, hgas, hused, hout, hst⟩ :=
      balance_child_exact hfork ht hc hin hB hfwd
    have hi : initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20) =
        (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi)).withGasLeft
          (fwd b S M G t ii 0x24 oi 0x20) := rfl
    have hnCost : used = balanceOfGas
        (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi))
        (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi)) := by
      rw [hcost, hi]
      change balanceOfGas
        {initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi) with
          gas := fwd b S M G t ii 0x24 oi 0x20}
        ((initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi)).withGasLeft
          (fwd b S M G t ii 0x24 oi 0x20)) = _
      exact t20_balanceGas_reframe _ _ _
    have hdebit : token20BalanceDebit sevm t ii oi b S M =
        acc b t + ext b S M ii 0x24 oi 0x20 + used := by
      unfold token20BalanceDebit
      rw [← hnCost]
      rfl
    have he := ext_le (b := b) (S := S) (M := M)
      (ii := ii) (is := 0x24) (oi := oi) (os := 0x20)
      (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii) hoi
    have ha := acc_le (b := b) (t := t)
    have hfund := fwd_charge hcharge
    have hsum := AllGasCall.resume_debit b S M G t ii 0x24 oi cpost used hfund
      (by change used ≤ fwd b S M G t ii 0x24 oi 0x20; omega) hgas
    change G = (callChildPost (parent b S M G t ii 0x24 oi 0x20) cpost oi.toNat 32).gasLeft +
      (acc b t + ext b S M ii 0x24 oi 0x20 + used) at hsum
    rw [← hdebit] at hsum
    have hp : Devm.EqModGas (parent b S M G t ii 0x24 oi 0x20)
        (ccParent (b.withGasLeft 0) S M 0 t ii 0x24 oi) := by
      apply Devm.EqModGas.of_normalized_eq
      rfl
    have hcp : Devm.EqModGas cpost
        (balanceOfPost (initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi))
          (initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi)) 0) := by
      rw [hchildpost, hi]
      change Devm.EqModGas (balanceOfPost
        {initSevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi) with
          gas := fwd b S M G t ii 0x24 oi 0x20}
        ((initDevm (ccMsg sevm (b.withGasLeft 0) S M 0 t ii 0x24 oi)).withGasLeft
          (fwd b S M G t ii 0x24 oi 0x20))
        (fwd b S M G t ii 0x24 oi 0x20 - used)) _
      rw [t20_balancePost_reframe]
      exact t20_balancePost_residual _ _ _
    have hn : Devm.EqModGas
        (callChildPost (parent b S M G t ii 0x24 oi 0x20) cpost oi.toNat 32)
        (token20BalanceNext sevm t ii oi b S M) := hp.callChildPost hcp oi.toNat 32
    have hrun := static_cross hfork hdepth (by rw [ht]; exact prec_false hprec)
      hdel hS hG hcharge hexec herr
    obtain ⟨flag, out, hpost, -, -⟩ := ri_staticcall_bounded hfork (Ninst.Run.of_runCompiled hrun)
    have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
      (callChildPost_stack' _ _ _ _))).1
    subst hflag
    have hout' : out = B.toBytes := by
      rw [← hpost.returnData, callChildPost_returnData', hout]
    subst hout'
    refine ⟨by rw [hdebit]; omega, _, hrun, hsum, hn, B.toBytes, hpost, ?_, ?_, ?_, ?_, ?_⟩
    · rw [B256.length_toBytes]
    · rw [B256.length_toBytes]; decide
    · rw [List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes]
    · refine hW' b _ hWb (fun a => ?_) (fun a => ?_)
      · rw [getStor_of_state (callChildPost_state' _ _ _ _), getStor_of_state hst]
      · rw [getCode_of_state (callChildPost_state' _ _ _ _), getCode_of_state hst]
    · intro hid
      refine ⟨?_, ?_, hid.pre, hid.fork⟩
      · show getDelegatedCodeAddress (cpost.getCode 4) = none
        rw [getCode_of_state hst]; exact hid.nodeleg
      · exact callChildPost_mem_warm _ _ _ _ 4
          (parent_mem_warm b S M G t ii 0x24 oi 0x20 4 hid.warm)

end Balance

end Blanc.Composition.Curve3Pool3CrvInstance
