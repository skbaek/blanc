-- ProrataFunctional.lean : storage-key disjointness and the public
-- selector entry route.

import Blanc.ProrataCode
import Blanc.Ladder

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Prorata

/-! ## Storage-key disjointness

The share mapping is keyed by CALLER, so every balance slot is address-shaped;
`supplySlot` is the all-ones word and is not.  Both write paths need exactly
this one fact to keep a balance write off the supply slot, so it is stated once
here rather than in each of them. -/

/-- No CALLER-keyed balance slot is the supply slot. -/
theorem caller_ne_supplySlot (a : Adr) : a.toB256 ≠ supplySlot := by
  intro h
  have hv : ValidAdr supplySlot := h ▸ validAdr_toB256 a
  have hnv : ¬ ValidAdr supplySlot := by
    rw [validAdr_iff]
    decide
  exact hnv hv

private structure EntryFrame (s t : Devm) : Prop where
  stor : Devm.getStor s = Devm.getStor t
  bal : Devm.getBal s = Devm.getBal t
  code : Devm.getCode s = Devm.getCode t
  memory : s.memory = t.memory
  logs : s.logs = t.logs
  output : s.output = t.output

/-- A successful hand-shaped dispatch route reaches one raw body without
changing the persistent state observed by the contract specification. -/
def BodyEntry (fs : List Func) (sevm : Sevm) (pre post : Devm)
    (body : Func) : Prop :=
  ∃ entry,
    Devm.getStor entry = Devm.getStor pre ∧
    Devm.getBal entry = Devm.getBal pre ∧
    Devm.getCode entry = Devm.getCode pre ∧
    Func.Run fs sevm entry body post

/-- The five possible raw bodies of a successful `prorataMain` execution. -/
inductive ProrataMainSuccess (fs : List Func) (sevm : Sevm)
    (pre post : Devm) : Prop where
  | deposit (entry : BodyEntry fs sevm pre post Prorata.deposit)
  | withdraw (entry : BodyEntry fs sevm pre post Prorata.withdraw)
  | convertToShares (entry : BodyEntry fs sevm pre post Prorata.convertToShares)
  | convertToAssets (entry : BodyEntry fs sevm pre post Prorata.convertToAssets)
  | donate (entry : BodyEntry fs sevm pre post Prorata.donate)

/-- The same exhaustive main-route classification, retaining the shared
zero-value ingress fact for the three nonpayable bodies. -/
inductive ProrataMainRoute (fs : List Func) (sevm : Sevm)
    (pre post : Devm) : Prop where
  | deposit (entry : BodyEntry fs sevm pre post Prorata.deposit)
  | withdraw (value_eq_zero : sevm.value = 0)
      (entry : BodyEntry fs sevm pre post Prorata.withdraw)
  | convertToShares (value_eq_zero : sevm.value = 0)
      (entry : BodyEntry fs sevm pre post Prorata.convertToShares)
  | convertToAssets (value_eq_zero : sevm.value = 0)
      (entry : BodyEntry fs sevm pre post Prorata.convertToAssets)
  | donate (entry : BodyEntry fs sevm pre post Prorata.donate)

private lemma EntryFrame.trans {s t u : Devm}
    (h : EntryFrame s t) (k : EntryFrame t u) : EntryFrame s u :=
  ⟨h.stor.trans k.stor, h.bal.trans k.bal, h.code.trans k.code,
    h.memory.trans k.memory, h.logs.trans k.logs, h.output.trans k.output⟩

private lemma EntryFrame.exists_run {fs : List Func} {e : Sevm} {pre entry post : Devm}
    {body : Func} (frame : EntryFrame pre entry) (run : Func.Run fs e entry body post) :
    ∃ s',
      Devm.getStor s' = Devm.getStor pre ∧
      Devm.getBal s' = Devm.getBal pre ∧
      Devm.getCode s' = Devm.getCode pre ∧
      s'.memory = pre.memory ∧ s'.logs = pre.logs ∧ s'.output = pre.output ∧
      Func.Run fs e s' body post :=
  ⟨entry, frame.stor.symm, frame.bal.symm, frame.code.symm, frame.memory.symm,
    frame.logs.symm, frame.output.symm, run⟩

private lemma EntryFrame.bodyEntry {fs : List Func} {e : Sevm}
    {pre entry post : Devm} {body : Func}
    (frame : EntryFrame pre entry) (run : Func.Run fs e entry body post) :
    BodyEntry fs e pre post body :=
  ⟨entry, frame.stor.symm, frame.bal.symm, frame.code.symm, run⟩

private lemma getStor_of_state {s t : Devm} (h : s.state = t.state) :
    Devm.getStor s = Devm.getStor t := by
  funext a
  show (s.state.get a).stor = (t.state.get a).stor
  rw [h]

private lemma getBal_of_state {s t : Devm} (h : s.state = t.state) :
    Devm.getBal s = Devm.getBal t := by
  funext a
  simp [Devm.getBal, Devm.getAcct]
  rw [h]

private lemma getCode_of_state {s t : Devm} (h : s.state = t.state) :
    Devm.getCode s = Devm.getCode t := by
  funext a
  simp [Devm.getCode, Devm.getAcct]
  rw [h]

private lemma entryFrame_line {e : Sevm} {s t : Devm} {l : Line}
    (h_stor : Line.Inv Devm.getStor l)
    (h_bal : Line.Inv Devm.getBal l)
    (h_code : Line.Inv Devm.getCode l)
    (h_memory : Line.Inv Devm.memory l)
    (h_logs : Line.Inv Devm.logs l)
    (h_output : Line.Inv Devm.output l)
    (run : Line.Run e s l t) : EntryFrame s t :=
  ⟨Line.of_inv Devm.getStor h_stor run, Line.of_inv Devm.getBal h_bal run,
    Line.of_inv Devm.getCode h_code run, Line.of_inv Devm.memory h_memory run,
    Line.of_inv Devm.logs h_logs run, Line.of_inv Devm.output h_output run⟩

private lemma entryFrame_fsig {e : Sevm} {s t : Devm}
    (run : Line.Run e s fsig t) : EntryFrame s t :=
  ⟨Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run,
    Line.of_inv Devm.getCode (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run, fsig_logs run, fsig_output run⟩

private lemma entryFrame_pop {s t : Devm} {xs : List B256}
    (pop : Devm.PopBurn xs s t) : EntryFrame s t :=
  ⟨getStor_of_state pop.state, getBal_of_state pop.state,
    getCode_of_state pop.state, pop.memory, pop.logs, pop.output⟩

private lemma entryFrame_burn {s t : Devm}
    (burn : Devm.Burn s t) : EntryFrame s t :=
  ⟨getStor_of_state burn.state, getBal_of_state burn.state,
    getCode_of_state burn.state, burn.memory, burn.logs, burn.output⟩

private lemma entryFrame_callvalue {e : Sevm} {s t : Devm}
    (run : Line.Run e s [callvalue] t) : EntryFrame s t := by
  rcases Line.of_run_cons run with ⟨u, qvalue, hnil⟩
  cases hnil
  have push := of_run_callvalue qvalue
  exact ⟨getStor_of_state push.state, getBal_of_state push.state,
    getCode_of_state push.state, push.memory, push.logs, push.output⟩

private lemma entryFrame_selectorTest {e : Sevm} {s t : Devm} {sig : B256}
    (run : Line.Run e s [dup 0, pushB256 sig, eq] t) : EntryFrame s t :=
  entryFrame_line (by line_inv) (by line_inv) (by line_inv)
    (by line_inv) (by line_inv) (by line_inv) run

private lemma entryFrame_plainSelectorTest {e : Sevm} {s t : Devm} {sig : B256}
    (run : Line.Run e s [pushB256 sig, eq] t) : EntryFrame s t :=
  entryFrame_line (by line_inv) (by line_inv) (by line_inv)
    (by line_inv) (by line_inv) (by line_inv) run

private lemma entryFrame_popLine {e : Sevm} {s t : Devm}
    (run : Line.Run e s [pop] t) : EntryFrame s t :=
  entryFrame_line (by line_inv) (by line_inv) (by line_inv)
    (by line_inv) (by line_inv) (by line_inv) run

private lemma selector_flag {e : Sevm} {s t : Devm} {sig expected : B256}
    (hp : sig :: [] <<+ s.stack)
    (run : Line.Run e s [dup 0, pushB256 expected, eq] t) :
    (sig =? expected) :: sig :: [] <<+ t.stack := by
  rcases Line.of_run_cons run with ⟨s1, hdup, hrest⟩
  rcases Line.of_run_cons hrest with ⟨s2, hpush, hrest⟩
  rcases Line.of_run_cons hrest with ⟨s3, heq, hnil⟩
  cases hnil
  have hp1 : sig :: sig :: [] <<+ s1.stack :=
    prefix_of_dup_val hdup (by show_nth) hp
  have hp2 : expected :: sig :: sig :: [] <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 hpush) hp1
  have hflag : (expected =? sig) :: sig :: [] <<+ t.stack :=
    prefix_of_eq heq hp2
  by_cases h : sig = expected
  · simpa [B256.eqCheck, h] using hflag
  · simpa [B256.eqCheck, h, Ne.symm h] using hflag

private lemma plain_selector_flag {e : Sevm} {s t : Devm} {sig expected : B256}
    (hp : sig :: [] <<+ s.stack)
    (run : Line.Run e s [pushB256 expected, eq] t) :
    (sig =? expected) :: [] <<+ t.stack := by
  rcases Line.of_run_cons run with ⟨s1, hpush, hrest⟩
  rcases Line.of_run_cons hrest with ⟨s2, heq, hnil⟩
  cases hnil
  have hp1 : expected :: sig :: [] <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 hpush) hp
  have hflag : (expected =? sig) :: [] <<+ t.stack :=
    prefix_of_eq heq hp1
  by_cases h : sig = expected
  · simpa [B256.eqCheck, h] using hflag
  · simpa [B256.eqCheck, h, Ne.symm h] using hflag

private lemma not_run_pop_donate {fs : List Func} {e : Sevm} {s r : Devm}
    (h_nonempty : e.data.length.toB256 ≠ 0) :
    ¬ Func.Run fs e s (pop ::: Prorata.donate) r := by
  intro run
  rcases of_run_prepend [pop] Prorata.donate run with ⟨t, _, hdonate⟩
  unfold Prorata.donate at hdonate
  rcases of_run_prepend [calldatasize] _ hdonate with ⟨u, hsize, hbranch⟩
  rcases Line.of_run_cons hsize with ⟨v, qsize, hnil⟩
  cases hnil
  have hp : e.data.length.toB256 :: [] <<+ u.stack :=
    prefix_of_push (of_run_calldatasize qsize) nil_pref
  rcases of_run_branch hbranch with
    ⟨u, hpop, hstop⟩ | ⟨w, u, v, hnz, hpop, hburn, hrev⟩
  · exact h_nonempty (popBurn_pref hpop hp).1.symm
  · exact not_run_rev hrev

private theorem deposit_body_of_prorataMain
    {fs : List Func} {e : Sevm} {s r : Devm}
    (hp : selector "deposit" [] :: [] <<+ s.stack)
    (run : Func.Run fs e s
      (dup 0 ::: pushB256 (selector "deposit" []) ::: eq :::
        ((pop ::: Prorata.deposit) <?>
          callvalue ::: ((pop ::: Prorata.donate) <?> Prorata.zeroValueDispatch))) r) :
    ∃ t, EntryFrame s t ∧ Func.Run fs e t Prorata.deposit r := by
  revert run
  func_execute 3
  intro hbranch
  have hflag := selector_flag hp h₁
  rw [show (selector "deposit" [] =? selector "deposit" []) = 1 from
    by simp [B256.eqCheck]] at hflag
  rcases of_run_branch hbranch with
    ⟨u, hpop, hwrong⟩ | ⟨w, u, v, hnz, hpop, hburn, hbody⟩
  · exact (B256.zero_ne_one (popBurn_pref hpop hflag).1).elim
  · rcases of_run_prepend [pop] Prorata.deposit hbody with ⟨t, hpopLine, hdeposit⟩
    exact ⟨t,
      (entryFrame_line (by line_inv) (by line_inv) (by line_inv) (by line_inv)
        (by line_inv) (by line_inv) h₁).trans ((entryFrame_pop hpop).trans
        ((entryFrame_burn hburn).trans
          (entryFrame_line (by line_inv) (by line_inv) (by line_inv) (by line_inv)
            (by line_inv) (by line_inv) hpopLine))), hdeposit⟩

private theorem withdraw_body_of_prorataMain
    {fs : List Func} {e : Sevm} {s r : Devm}
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (hp : selector "withdraw" [.uint256] :: [] <<+ s.stack)
    (run : Func.Run fs e s
      (dup 0 ::: pushB256 (selector "deposit" []) ::: eq :::
        ((pop ::: Prorata.deposit) <?>
          callvalue ::: ((pop ::: Prorata.donate) <?> Prorata.zeroValueDispatch))) r) :
    ∃ t, EntryFrame s t ∧ Func.Run fs e t Prorata.withdraw r := by
  revert run
  func_execute 3
  intro hdepositBranch
  have hdepositFlag := selector_flag hp h₁
  have hne : selector "withdraw" [.uint256] ≠ selector "deposit" [] := by
    decide +kernel
  rw [B256.eqCheck, if_neg hne] at hdepositFlag
  rcases of_run_branch hdepositBranch with
    ⟨u, hpop, hcontinue⟩ | ⟨w, u, v, hnz, hpop, hburn, hwrong⟩
  · rcases of_run_prepend [callvalue] _ hcontinue with
      ⟨uValue, hvalueLine, hvalueBranch⟩
    have hpAfterDeposit : selector "withdraw" [.uint256] :: [] <<+ u.stack :=
      (popBurn_pref hpop hdepositFlag).2
    rcases Line.of_run_cons hvalueLine with ⟨uValue', qvalue, hnil⟩
    cases hnil
    have hvaluePrefix : e.value :: selector "withdraw" [.uint256] :: [] <<+
        uValue.stack :=
      prefix_of_push (of_run_callvalue qvalue) hpAfterDeposit
    rcases of_run_branch hvalueBranch with
      ⟨x, hpopValue, hzero⟩ | ⟨z, x, y, hnzValue, hpopValue, hburnValue, hdonate⟩
    · rcases of_run_prepend [dup 0, pushB256 (selector "withdraw" [.uint256]), eq] _ hzero with
        ⟨uWithdraw, hwithdrawLine, hwithdrawBranch⟩
      have hpAfterValue : selector "withdraw" [.uint256] :: [] <<+ x.stack :=
        (popBurn_pref hpopValue hvaluePrefix).2
      have hwithdrawFlag := selector_flag hpAfterValue hwithdrawLine
      rw [show (selector "withdraw" [.uint256] =? selector "withdraw" [.uint256]) = 1 from
        by simp [B256.eqCheck]] at hwithdrawFlag
      rcases of_run_branch hwithdrawBranch with
        ⟨a, hpopWithdraw, hwrong⟩ |
        ⟨q, a, b, hnzWithdraw, hpopWithdraw, hburnWithdraw, hbody⟩
      · exact (B256.zero_ne_one (popBurn_pref hpopWithdraw hwithdrawFlag).1).elim
      · rcases of_run_prepend [pop] Prorata.withdraw hbody with
          ⟨t, hpopLine, hwithdraw⟩
        exact ⟨t,
          (entryFrame_line (by line_inv) (by line_inv) (by line_inv) (by line_inv)
            (by line_inv) (by line_inv) h₁).trans ((entryFrame_pop hpop).trans
            ((entryFrame_callvalue hvalueLine).trans ((entryFrame_pop hpopValue).trans
              ((entryFrame_line (by line_inv) (by line_inv) (by line_inv) (by line_inv)
                (by line_inv) (by line_inv) hwithdrawLine).trans ((entryFrame_pop hpopWithdraw).trans
                ((entryFrame_burn hburnWithdraw).trans
                  (entryFrame_line (by line_inv) (by line_inv) (by line_inv) (by line_inv)
                    (by line_inv) (by line_inv) hpopLine))))))), hwithdraw⟩
    · exact (not_run_pop_donate h_nonempty hdonate).elim
  · exact (hnz (popBurn_pref hpop hdepositFlag).1).elim

private theorem convertToShares_body_of_prorataMain
    {fs : List Func} {e : Sevm} {s r : Devm}
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (hp : selector "convertToShares" [.uint256] :: [] <<+ s.stack)
    (run : Func.Run fs e s
      (dup 0 ::: pushB256 (selector "deposit" []) ::: eq :::
        ((pop ::: Prorata.deposit) <?>
          callvalue ::: ((pop ::: Prorata.donate) <?> Prorata.zeroValueDispatch))) r) :
    ∃ t, EntryFrame s t ∧ Func.Run fs e t Prorata.convertToShares r := by
  revert run
  func_execute 3
  intro hdepositBranch
  have hdepositFlag := selector_flag hp h₁
  have hdepositNe : selector "convertToShares" [.uint256] ≠ selector "deposit" [] := by
    decide +kernel
  rw [B256.eqCheck, if_neg hdepositNe] at hdepositFlag
  rcases of_run_branch hdepositBranch with
    ⟨u, hpop, hcontinue⟩ | ⟨w, u, v, hnz, hpop, hburn, hwrong⟩
  · rcases of_run_prepend [callvalue] _ hcontinue with
      ⟨uValue, hvalueLine, hvalueBranch⟩
    have hpAfterDeposit : selector "convertToShares" [.uint256] :: [] <<+ u.stack :=
      (popBurn_pref hpop hdepositFlag).2
    rcases Line.of_run_cons hvalueLine with ⟨uValue', qvalue, hnil⟩
    cases hnil
    have hvaluePrefix : e.value :: selector "convertToShares" [.uint256] :: [] <<+
        uValue.stack :=
      prefix_of_push (of_run_callvalue qvalue) hpAfterDeposit
    rcases of_run_branch hvalueBranch with
      ⟨x, hpopValue, hzero⟩ | ⟨z, x, y, hnzValue, hpopValue, hburnValue, hdonate⟩
    · rcases of_run_prepend [dup 0, pushB256 (selector "withdraw" [.uint256]), eq] _ hzero with
        ⟨uWithdraw, hwithdrawLine, hwithdrawBranch⟩
      have hpAfterValue : selector "convertToShares" [.uint256] :: [] <<+ x.stack :=
        (popBurn_pref hpopValue hvaluePrefix).2
      have hwithdrawFlag := selector_flag hpAfterValue hwithdrawLine
      have hwithdrawNe : selector "convertToShares" [.uint256] ≠
          selector "withdraw" [.uint256] := by
        decide +kernel
      rw [B256.eqCheck, if_neg hwithdrawNe] at hwithdrawFlag
      rcases of_run_branch hwithdrawBranch with
        ⟨a, hpopWithdraw, hcontinueShares⟩ |
        ⟨q, a, b, hnzWithdraw, hpopWithdraw, hburnWithdraw, hwrong⟩
      · rcases of_run_prepend [dup 0, pushB256 (selector "convertToShares" [.uint256]), eq] _
          hcontinueShares with ⟨uShares, hsharesLine, hsharesBranch⟩
        have hpAfterWithdraw : selector "convertToShares" [.uint256] :: [] <<+ a.stack :=
          (popBurn_pref hpopWithdraw hwithdrawFlag).2
        have hsharesFlag := selector_flag hpAfterWithdraw hsharesLine
        rw [show (selector "convertToShares" [.uint256] =?
            selector "convertToShares" [.uint256]) = 1 from by simp [B256.eqCheck]] at hsharesFlag
        rcases of_run_branch hsharesBranch with
          ⟨c, hpopShares, hwrong⟩ |
          ⟨q, c, d, hnzShares, hpopShares, hburnShares, hbody⟩
        · exact (B256.zero_ne_one (popBurn_pref hpopShares hsharesFlag).1).elim
        · rcases of_run_prepend [pop] Prorata.convertToShares hbody with
            ⟨t, hpopLine, hshares⟩
          exact ⟨t,
            (entryFrame_line (by line_inv) (by line_inv) (by line_inv) (by line_inv)
              (by line_inv) (by line_inv) h₁).trans ((entryFrame_pop hpop).trans
              ((entryFrame_callvalue hvalueLine).trans ((entryFrame_pop hpopValue).trans
                ((entryFrame_line (by line_inv) (by line_inv) (by line_inv) (by line_inv)
                  (by line_inv) (by line_inv) hwithdrawLine).trans ((entryFrame_pop hpopWithdraw).trans
                  ((entryFrame_line (by line_inv) (by line_inv) (by line_inv) (by line_inv)
                    (by line_inv) (by line_inv) hsharesLine).trans ((entryFrame_pop hpopShares).trans
                    ((entryFrame_burn hburnShares).trans
                      (entryFrame_line (by line_inv) (by line_inv) (by line_inv) (by line_inv)
                        (by line_inv) (by line_inv) hpopLine))))))))), hshares⟩
      · exact (hnzWithdraw (popBurn_pref hpopWithdraw hwithdrawFlag).1).elim
    · exact (not_run_pop_donate h_nonempty hdonate).elim
  · exact (hnz (popBurn_pref hpop hdepositFlag).1).elim

private theorem convertToAssets_body_of_prorataMain
    {fs : List Func} {e : Sevm} {s r : Devm}
    (h_nonempty : e.data.length.toB256 ≠ 0)
    (hp : selector "convertToAssets" [.uint256] :: [] <<+ s.stack)
    (run : Func.Run fs e s
      (dup 0 ::: pushB256 (selector "deposit" []) ::: eq :::
        ((pop ::: Prorata.deposit) <?>
          callvalue ::: ((pop ::: Prorata.donate) <?> Prorata.zeroValueDispatch))) r) :
    ∃ t, EntryFrame s t ∧ Func.Run fs e t Prorata.convertToAssets r := by
  revert run
  func_execute 3
  intro hdepositBranch
  have hdepositFlag := selector_flag hp h₁
  have hdepositNe : selector "convertToAssets" [.uint256] ≠ selector "deposit" [] := by
    decide +kernel
  rw [B256.eqCheck, if_neg hdepositNe] at hdepositFlag
  rcases of_run_branch hdepositBranch with
    ⟨u, hpop, hcontinue⟩ | ⟨w, u, v, hnz, hpop, hburn, hwrong⟩
  · rcases of_run_prepend [callvalue] _ hcontinue with
      ⟨uValue, hvalueLine, hvalueBranch⟩
    have hpAfterDeposit : selector "convertToAssets" [.uint256] :: [] <<+ u.stack :=
      (popBurn_pref hpop hdepositFlag).2
    rcases Line.of_run_cons hvalueLine with ⟨uValue', qvalue, hnil⟩
    cases hnil
    have hvaluePrefix : e.value :: selector "convertToAssets" [.uint256] :: [] <<+
        uValue.stack :=
      prefix_of_push (of_run_callvalue qvalue) hpAfterDeposit
    rcases of_run_branch hvalueBranch with
      ⟨x, hpopValue, hzero⟩ | ⟨z, x, y, hnzValue, hpopValue, hburnValue, hdonate⟩
    · rcases of_run_prepend [dup 0, pushB256 (selector "withdraw" [.uint256]), eq] _ hzero with
        ⟨uWithdraw, hwithdrawLine, hwithdrawBranch⟩
      have hpAfterValue : selector "convertToAssets" [.uint256] :: [] <<+ x.stack :=
        (popBurn_pref hpopValue hvaluePrefix).2
      have hwithdrawFlag := selector_flag hpAfterValue hwithdrawLine
      have hwithdrawNe : selector "convertToAssets" [.uint256] ≠
          selector "withdraw" [.uint256] := by
        decide +kernel
      rw [B256.eqCheck, if_neg hwithdrawNe] at hwithdrawFlag
      rcases of_run_branch hwithdrawBranch with
        ⟨a, hpopWithdraw, hcontinueShares⟩ |
        ⟨q, a, b, hnzWithdraw, hpopWithdraw, hburnWithdraw, hwrong⟩
      · rcases of_run_prepend [dup 0, pushB256 (selector "convertToShares" [.uint256]), eq] _
          hcontinueShares with ⟨uShares, hsharesLine, hsharesBranch⟩
        have hpAfterWithdraw : selector "convertToAssets" [.uint256] :: [] <<+ a.stack :=
          (popBurn_pref hpopWithdraw hwithdrawFlag).2
        have hsharesFlag := selector_flag hpAfterWithdraw hsharesLine
        have hsharesNe : selector "convertToAssets" [.uint256] ≠
            selector "convertToShares" [.uint256] := by
          decide +kernel
        rw [B256.eqCheck, if_neg hsharesNe] at hsharesFlag
        rcases of_run_branch hsharesBranch with
          ⟨c, hpopShares, hassetEntry⟩ |
          ⟨q, c, d, hnzShares, hpopShares, hburnShares, hwrong⟩
        · rcases of_run_prepend [pushB256 (selector "convertToAssets" [.uint256]), eq] _
            hassetEntry with ⟨uAssets, hassetsLine, hassetsBranch⟩
          have hpAfterShares : selector "convertToAssets" [.uint256] :: [] <<+ c.stack :=
            (popBurn_pref hpopShares hsharesFlag).2
          have hassetsFlag := plain_selector_flag hpAfterShares hassetsLine
          rw [show (selector "convertToAssets" [.uint256] =?
              selector "convertToAssets" [.uint256]) = 1 from by simp [B256.eqCheck]] at hassetsFlag
          rcases of_run_branch hassetsBranch with
            ⟨q, hpopAssets, hwrong⟩ |
            ⟨q, a, b, hnzAssets, hpopAssets, hburnAssets, hassets⟩
          · exact (B256.zero_ne_one (popBurn_pref hpopAssets hassetsFlag).1).elim
          · have f1 := entryFrame_line (by line_inv) (by line_inv) (by line_inv)
              (by line_inv) (by line_inv) (by line_inv) h₁
            have f2 := f1.trans (entryFrame_pop hpop)
            have f3 := f2.trans (entryFrame_callvalue hvalueLine)
            have f4 := f3.trans (entryFrame_pop hpopValue)
            have f5 := f4.trans (entryFrame_line (by line_inv) (by line_inv) (by line_inv)
              (by line_inv) (by line_inv) (by line_inv) hwithdrawLine)
            have f6 := f5.trans (entryFrame_pop hpopWithdraw)
            have f7 := f6.trans (entryFrame_line (by line_inv) (by line_inv) (by line_inv)
              (by line_inv) (by line_inv) (by line_inv) hsharesLine)
            have f8 := f7.trans (entryFrame_pop hpopShares)
            have f9 := f8.trans (entryFrame_line (by line_inv) (by line_inv) (by line_inv)
              (by line_inv) (by line_inv) (by line_inv) hassetsLine)
            have f10 := f9.trans (entryFrame_pop hpopAssets)
            exact ⟨b, f10.trans (entryFrame_burn hburnAssets), hassets⟩
        · exact (hnzShares (popBurn_pref hpopShares hsharesFlag).1).elim
      · exact (hnzWithdraw (popBurn_pref hpopWithdraw hwithdrawFlag).1).elim
    · exact (not_run_pop_donate h_nonempty hdonate).elim
  · exact (hnz (popBurn_pref hpop hdepositFlag).1).elim

/-- Every successful execution of the hand-shaped main reaches exactly one of
the five raw PRORATA bodies through a persistent-state-silent ingress, and the
shared nonpayable split retains zero callvalue for its three guarded routes. -/
theorem classify_prorataMain_route
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre Prorata.prorataMain post) :
    ProrataMainRoute fs sevm pre post := by
  simp only [Prorata.prorataMain] at run
  rcases of_run_prepend fsig _ run with ⟨afterSig, hsig, hmain⟩
  rcases of_run_prepend
      [dup 0, pushB256 (selector "deposit" []), eq] _ hmain with
    ⟨afterDepositTest, hdepositTest, hdepositBranch⟩
  have routeSig : EntryFrame pre afterSig := entryFrame_fsig hsig
  have routeDepositTest : EntryFrame pre afterDepositTest :=
    routeSig.trans (entryFrame_selectorTest hdepositTest)
  rcases of_run_branch hdepositBranch with
    ⟨afterDepositPop, hdepositPop, hvalue⟩ |
    ⟨depositFlag, afterDepositPop, afterDepositBurn, hdepositFlag,
      hdepositPop, hdepositBurn, hdeposit⟩
  · have routeValuePre : EntryFrame pre afterDepositPop :=
      routeDepositTest.trans (entryFrame_pop hdepositPop)
    rcases of_run_prepend [callvalue] _ hvalue with
      ⟨afterValue, hvalueLine, hvalueBranch⟩
    have routeValue : EntryFrame pre afterValue :=
      routeValuePre.trans (entryFrame_callvalue hvalueLine)
    rcases of_run_branch hvalueBranch with
      ⟨afterValuePop, hvaluePop, hzeroDispatch⟩ |
      ⟨valueFlag, afterValuePop, afterValueBurn, hvalueFlag,
        hvaluePop, hvalueBurn, hdonate⟩
    · have hvaluePrefix : sevm.value :: [] <<+ afterValue.stack := by
        rcases Line.of_run_cons hvalueLine with
          ⟨afterCallvalue, hcallvalue, hnil⟩
        cases hnil
        exact prefix_of_push (of_run_callvalue hcallvalue) nil_pref
      have hvalueZero : sevm.value = 0 :=
        (popBurn_pref hvaluePop hvaluePrefix).1.symm
      have routeZero : EntryFrame pre afterValuePop :=
        routeValue.trans (entryFrame_pop hvaluePop)
      simp only [Prorata.zeroValueDispatch] at hzeroDispatch
      rcases of_run_prepend
          [dup 0, pushB256 (selector "withdraw" [.uint256]), eq] _
          hzeroDispatch with
        ⟨afterWithdrawTest, hwithdrawTest, hwithdrawBranch⟩
      have routeWithdrawTest : EntryFrame pre afterWithdrawTest :=
        routeZero.trans (entryFrame_selectorTest hwithdrawTest)
      rcases of_run_branch hwithdrawBranch with
        ⟨afterWithdrawPop, hwithdrawPop, hsharesPath⟩ |
        ⟨withdrawFlag, afterWithdrawPop, afterWithdrawBurn, hwithdrawFlag,
          hwithdrawPop, hwithdrawBurn, hwithdrawPath⟩
      · have routeSharesPre : EntryFrame pre afterWithdrawPop :=
          routeWithdrawTest.trans (entryFrame_pop hwithdrawPop)
        rcases of_run_prepend
            [dup 0, pushB256 (selector "convertToShares" [.uint256]), eq] _
            hsharesPath with
          ⟨afterSharesTest, hsharesTest, hsharesBranch⟩
        have routeSharesTest : EntryFrame pre afterSharesTest :=
          routeSharesPre.trans (entryFrame_selectorTest hsharesTest)
        rcases of_run_branch hsharesBranch with
          ⟨afterSharesPop, hsharesPop, hassetsPath⟩ |
          ⟨sharesFlag, afterSharesPop, afterSharesBurn, hsharesFlag,
            hsharesPop, hsharesBurn, hsharesBody⟩
        · have routeAssetsPre : EntryFrame pre afterSharesPop :=
            routeSharesTest.trans (entryFrame_pop hsharesPop)
          rcases of_run_prepend
              [pushB256 (selector "convertToAssets" [.uint256]), eq] _
              hassetsPath with
            ⟨afterAssetsTest, hassetsTest, hassetsBranch⟩
          have routeAssetsTest : EntryFrame pre afterAssetsTest :=
            routeAssetsPre.trans (entryFrame_plainSelectorTest hassetsTest)
          rcases of_run_branch hassetsBranch with
            ⟨donateEntry, hassetsPop, hdonateBody⟩ |
            ⟨assetsFlag, afterAssetsPop, afterAssetsBurn, hassetsFlag,
              hassetsPop, hassetsBurn, hassetsBodyPath⟩
          · exact .donate
              ((routeAssetsTest.trans (entryFrame_pop hassetsPop)).bodyEntry
                hdonateBody)
          · exact .convertToAssets hvalueZero
              ((routeAssetsTest.trans ((entryFrame_pop hassetsPop).trans
                (entryFrame_burn hassetsBurn))).bodyEntry hassetsBodyPath)
        · rcases of_run_prepend [pop] Prorata.convertToShares hsharesBody with
              ⟨sharesEntry, hsharesBodyPop, hsharesRun⟩
          exact .convertToShares hvalueZero
            ((routeSharesTest.trans ((entryFrame_pop hsharesPop).trans
              ((entryFrame_burn hsharesBurn).trans
                (entryFrame_popLine hsharesBodyPop)))).bodyEntry hsharesRun)
      · rcases of_run_prepend [pop] Prorata.withdraw hwithdrawPath with
            ⟨withdrawEntry, hwithdrawBodyPop, hwithdrawRun⟩
        exact .withdraw hvalueZero
          ((routeWithdrawTest.trans ((entryFrame_pop hwithdrawPop).trans
            ((entryFrame_burn hwithdrawBurn).trans
              (entryFrame_popLine hwithdrawBodyPop)))).bodyEntry hwithdrawRun)
    · rcases of_run_prepend [pop] Prorata.donate hdonate with
          ⟨donateEntry, hdonatePop, hdonateRun⟩
      exact .donate
        ((routeValue.trans ((entryFrame_pop hvaluePop).trans
          ((entryFrame_burn hvalueBurn).trans
            (entryFrame_popLine hdonatePop)))).bodyEntry hdonateRun)
  · rcases of_run_prepend [pop] Prorata.deposit hdeposit with
        ⟨depositEntry, hdepositBodyPop, hdepositRun⟩
    exact .deposit
      ((routeDepositTest.trans ((entryFrame_pop hdepositPop).trans
        ((entryFrame_burn hdepositBurn).trans
          (entryFrame_popLine hdepositBodyPop)))).bodyEntry hdepositRun)

/-- Compatibility projection retaining the original persistent-state route
surface for consumers that do not need the nonpayable value fact. -/
theorem classify_prorataMain_success
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre Prorata.prorataMain post) :
    ProrataMainSuccess fs sevm pre post := by
  cases classify_prorataMain_route run with
  | deposit entry => exact .deposit entry
  | withdraw _ entry => exact .withdraw entry
  | convertToShares _ entry => exact .convertToShares entry
  | convertToAssets _ entry => exact .convertToAssets entry
  | donate entry => exact .donate entry

/-- A successful call on a recognized ABI selector reaches the corresponding
raw PRORATA body with its selector removed.  The nonempty word premise rules
out the receive route used for nonzero-value calls. -/
theorem exec_enters_prorataSelector_logs
    {sevm : Sevm} {pre post : Devm} {sig : B256} {body : Func}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile Prorata.prorata)
    (h_sel : Sevm.selector sevm = sig)
    (h_nonempty : sevm.data.length.toB256 ≠ 0)
    (h_mem : (sig, body) ∈ Prorata.prorataFuncs) :
    ∃ s',
      Devm.getStor s' = Devm.getStor pre ∧
      Devm.getBal s' = Devm.getBal pre ∧
      Devm.getCode s' = Devm.getCode pre ∧
      s'.memory = pre.memory ∧ s'.logs = pre.logs ∧ s'.output = pre.output ∧
      Func.Run (Prorata.prorata.main :: Prorata.prorata.aux) sevm s' body post := by
  have h_run : Prog.Run sevm pre Prorata.prorata post :=
    correct sevm pre Prorata.prorata post exc h_code
  dsimp only [Prog.Run] at h_run
  cases h_run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases h_eq
  have run' : Func.Run (Prorata.prorata.main :: Prorata.prorata.aux) sevm s₀
      (fsig +++
        (dup 0 ::: pushB256 (selector "deposit" []) ::: eq :::
          ((pop ::: Prorata.deposit) <?>
            callvalue ::: ((pop ::: Prorata.donate) <?> Prorata.zeroValueDispatch)))) post := by
    simpa only [Prorata.prorata, Prorata.prorataMain] using run
  refine run_prepend_elim _ fsig ?_ run'
  intro s₁ hfsig hmain
  have hp : sig :: [] <<+ s₁.stack := by
    rw [← h_sel]
    exact prefix_of_fsig nil_pref hfsig
  simp only [Prorata.prorataFuncs, List.mem_cons] at h_mem
  rcases h_mem with hassets | hwithdraw | hshares | hdeposit
  · injection hassets with hsig hbody
    subst sig
    subst body
    rw [hsig] at hp
    rcases convertToAssets_body_of_prorataMain h_nonempty hp hmain with
      ⟨entry, hroute, hbody⟩
    exact (entryFrame_burn burn).trans ((entryFrame_fsig hfsig).trans hroute) |>.exists_run hbody
  · injection hwithdraw with hsig hbody
    subst sig
    subst body
    rw [hsig] at hp
    rcases withdraw_body_of_prorataMain h_nonempty hp hmain with ⟨entry, hroute, hbody⟩
    exact (entryFrame_burn burn).trans ((entryFrame_fsig hfsig).trans hroute) |>.exists_run hbody
  · injection hshares with hsig hbody
    subst sig
    subst body
    rw [hsig] at hp
    rcases convertToShares_body_of_prorataMain h_nonempty hp hmain with
      ⟨entry, hroute, hbody⟩
    exact (entryFrame_burn burn).trans ((entryFrame_fsig hfsig).trans hroute) |>.exists_run hbody
  · rcases hdeposit with hdeposit | hnil
    · injection hdeposit with hsig hbody
      subst sig
      subst body
      rw [hsig] at hp
      rcases deposit_body_of_prorataMain hp hmain with ⟨entry, hroute, hbody⟩
      exact (entryFrame_burn burn).trans ((entryFrame_fsig hfsig).trans hroute) |>.exists_run hbody
    · simp at hnil

end Prorata

end Blanc
