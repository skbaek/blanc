-- CommonProofs/Balance.lean : balance-sum relations, primitive state updates and the `line_execute`/`invariance` tactics.

import Blanc.CommonProofs.Messages
import Blanc.CommonProofs.Hinv
import Blanc.CommonProofs.NoDel

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

/-! ## 4. Balance-sum relations and primitive state updates -/

def State.balSum (st : Jaune.State) : Nat :=
  sum st.bal

def Devm.balSum (d : Devm) : Nat :=
  State.balSum d.state

def State.BalNoninc (pre post : Jaune.State) : Prop :=
  State.balSum post ≤ State.balSum pre

def Devm.BalNoninc (pre post : Devm) : Prop :=
  Devm.balSum post ≤ Devm.balSum pre

def State.BalGrowth (allowance : Nat) (pre post : Jaune.State) : Prop :=
  State.balSum post ≤ State.balSum pre + allowance

lemma balNoninc_refl_trans :
    (ReflexiveRel State.BalNoninc ∧ TransitiveRel State.BalNoninc) ∧
    (ReflexiveRel Devm.BalNoninc ∧ TransitiveRel Devm.BalNoninc) := by
  exact ⟨⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩,
         ⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩⟩

lemma Adr.toNat_lt_size (a : Adr) : a.toNat < 2 ^ 160 := by
  rw [← toAdr_toNat a, Nat.toNat_toAdr, Nat.lo]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

lemma sumBelow_setBal_eq_local (st : Jaune.State) (a : Adr) (v : B256)
    (n : Nat) (hn : n ≤ a.toNat) (hsize : n ≤ 2 ^ 160) :
    sumBelow (fun x => (st.setBal a v).bal x) n =
      sumBelow (fun x => st.bal x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    rw [ih (Nat.le_of_succ_le hn) (Nat.le_of_succ_le hsize)]
    have hnlt : n < a.toNat := Nat.lt_of_succ_le hn
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    have hne : n.toAdr ≠ a := by
      intro heq
      have hnat := congrArg Adr.toNat heq
      rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
      omega
    have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
      State.setAccount_get_ne _ hne.symm _
    have hbal : (st.setBal a v).bal n.toAdr = st.bal n.toAdr := by
      dsimp only [State.setBal, State.bal]
      have hget' : (st.setAccount a ((st.get a).withBal v)).get n.toAdr =
          st.get n.toAdr := by
        simpa only [State.setBal] using hget
      rw [hget']
    rw [hbal]

lemma sumBelow_setBal_add_local (st : Jaune.State) (a : Adr) (v : B256)
    (n : Nat) (hsize : n ≤ 2 ^ 160) (ha : a.toNat < n) :
    sumBelow (fun x => (st.setBal a v).bal x) n + (st.bal a).toNat =
      sumBelow (fun x => st.bal x) n + v.toNat := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq
    · have hih := ih (Nat.le_of_succ_le hsize) ha_lt
      have hne : n.toAdr ≠ a := by
        intro heq
        have hnat := congrArg Adr.toNat heq
        rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
        omega
      have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
        State.setAccount_get_ne _ hne.symm _
      change sumBelow (fun x => (st.setBal a v).bal x) n +
          ((st.setBal a v).get n.toAdr).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get n.toAdr).bal.toNat + v.toNat
      rw [hget]
      omega
    · have hprefix := sumBelow_setBal_eq_local st a v n
        (Nat.le_of_eq ha_eq.symm) (Nat.le_of_succ_le hsize)
      have haddr : n.toAdr = a := by
        rw [← ha_eq]
        exact toAdr_toNat a
      rw [hprefix, haddr]
      change sumBelow (fun x => st.bal x) n +
          ((st.setBal a v).get a).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      dsimp only [State.setBal]
      rw [State.setAccount_get_self, Acct.clearIfEmpty_bal]
      change sumBelow (fun x => st.bal x) n + v.toNat +
          (st.get a).bal.toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      omega

lemma State.balSum_setBal (st : Jaune.State) (a : Adr) (v : B256) :
    State.balSum (st.setBal a v) + (st.bal a).toNat =
      State.balSum st + v.toNat := by
  have hmax : Adr.max.toNat.succ = 2 ^ 160 := by decide
  have ha : a.toNat < Adr.max.toNat.succ := by
    rw [hmax]
    exact Adr.toNat_lt_size a
  simpa only [balSum, sum, succ_eq_add_one] using
    (sumBelow_setBal_add_local st a v Adr.max.toNat.succ (by rw [hmax]) ha)

lemma State.balSum_subBal {st mid : Jaune.State} {a : Adr} {v : B256}
    (h : st.subBal a v = some mid) :
    State.balSum mid + v.toNat = State.balSum st := by
  unfold State.subBal at h
  split at h
  · contradiction
  · injection h with h_mid
    subst h_mid
    have h_set := State.balSum_setBal st a (st.bal a - v)
    rename_i h_not_lt
    have h_le : v ≤ st.bal a := le_of_not_gt h_not_lt
    have h_le2 : v.toNat ≤ (st.bal a).toNat := B256.toNat_le_toNat h_le
    rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_set
    omega

lemma State.addBal_growth (st : Jaune.State) (a : Adr) (v : B256) :
    State.BalGrowth v.toNat st (st.addBal a v) := by
  unfold State.addBal State.BalGrowth
  have h := State.balSum_setBal st a (st.bal a + v)
  rw [B256.toNat_add] at h
  unfold Nat.lo at h
  have h_mod := Nat.mod_le ((st.bal a).toNat + v.toNat) (2^256)
  omega

/- This lemma is the reusable conservation/nonincrease theorem for value transfer,
   including the recipient-overflow case.  -/
lemma State.sub_addBal_noninc {st mid : Jaune.State}
    {src dst : Adr} {v : B256}
    (hsub : st.subBal src v = some mid) :
    State.BalNoninc st (mid.addBal dst v) := by
  dsimp only [BalNoninc]
  have h1 := State.addBal_growth mid dst v
  dsimp only [BalGrowth] at h1
  have h2 := State.balSum_subBal hsub
  omega

lemma State.setBal_zero_noninc (st : Jaune.State) (a : Adr) :
    State.BalNoninc st (st.setBal a 0) := by
  unfold State.BalNoninc
  have h := State.balSum_setBal st a 0
  have hz : ((0 : B256).toNat) = 0 := by decide
  rw [hz, Nat.add_zero] at h
  omega

lemma Devm.balNoninc_of_state {pre post : Devm}
    (h : State.BalNoninc pre.state post.state) : Devm.BalNoninc pre post := by
  exact h

lemma Devm.balNoninc_of_getBal_eq {pre post : Devm}
    (h : post.getBal = pre.getBal) : Devm.BalNoninc pre post := by
  unfold Devm.BalNoninc Devm.balSum State.balSum
  change sum post.getBal ≤ sum pre.getBal
  rw [h]

/-! ## 5. Balance effects of instruction and message semantic units -/

def MessageExecution := Except (EvmError × Jaune.State × AdrSet × Tra) Devm

def MessageExecution.state : MessageExecution → Jaune.State
  | .ok d => d.state
  | .error ⟨_, st, _, _⟩ => st

def MessageExecution.Rel
    (R : Jaune.State → Jaune.State → Prop)
    (pre : Jaune.State) (out : MessageExecution) : Prop :=
  R pre out.state

/-- A successful message settlement either restored the message-entry world or
retained a clean successful message result unchanged at the world-state level. -/
theorem processMessage_settle_ok_state_cases
    {msg : Msg} {result : MessageExecution} {post : Devm}
    (h : processMessage.settle msg result = .ok post) :
    post.state = msg.benv.state ∨
      ∃ raw : Devm, result = .ok raw ∧
        raw.error.isSome = false ∧ post.state = raw.state := by
  cases result with
  | error error =>
      simp only [processMessage.settle, Except.bind_error, reduceCtorEq] at h
  | ok raw =>
      unfold processMessage.settle at h
      simp only [bind, Except.bind] at h
      cases herr : raw.error.isSome with
      | false =>
          rw [ite_eq_right (by simpa only [Bool.not_eq_true, Option.isSome_eq_false_iff,
            Option.isNone_iff_eq_none] using herr)] at h
          exact Or.inr ⟨raw, rfl, herr,
            (congrArg Devm.state (Except.ok.inj h)).symm⟩
      | true =>
          rw [ite_eq_left herr] at h
          have heq := Except.ok.inj h
          exact Or.inl <| calc
            post.state =
                (raw.rollback msg.benv.state
                  msg.tenv.transientStorage).state :=
              (congrArg Devm.state heq).symm
            _ = msg.benv.state := rfl

/-- A no-slot core run is a failed entry or a precompile/empty-code execution.
On a successful wrapper result it either rolled back or retained exactly the
successful message-entry transfer; precompiles cannot alter the world. -/
theorem ProcessMessage.none_ok_state_cases
    {msg : Msg} {post : Devm}
    (hprocess : ProcessMessage msg .none (.ok post)) :
    post.state = msg.benv.state ∨
      ∃ benv, msg.benvAfterTransfer = .ok benv ∧
        post.state = benv.state := by
  rcases RunFrame.decompose hprocess with
    ⟨error, _htransfer, _hslot, hresult⟩ |
    ⟨benv, _result, htransfer, hexecute, hresult⟩
  · simp only [Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
    processMessage.settle, Except.bind_error, reduceCtorEq] at hresult
  · change msg.benvAfterTransfer = .ok benv at htransfer
    change ExecuteCode (msg.withBenv benv) .none _result at hexecute
    change (.ok post) = processMessage.settle msg _result at hresult
    unfold ExecuteCode at hexecute
    cases hentry : executeCode.enter (msg.withBenv benv) with
    | inl evm =>
        rw [hentry] at hexecute
        rcases hexecute with ⟨raw, hslot, _⟩
        cases hslot
    | inr raw =>
        rw [hentry] at hexecute
        rcases executeCode.enter_inr hentry with ⟨address, hraw⟩
        rcases processMessage_settle_ok_state_cases hresult.symm with
          hrollback | ⟨clean, hclean, _hcleanError, hpost⟩
        · exact Or.inl hrollback
        · have hhandled :
              executeCode.handleErrorWith
                (msg.withBenv benv).benv.stat.rules.stateGas
                (executePrecomp (initEvm (msg.withBenv benv)) address) =
                  .ok clean := by
            rw [← hraw, ← hexecute.2, hclean]
          have hcleanState :=
            executeCode.handle_precompile_ok_state hhandled
          exact Or.inr ⟨benv, htransfer, hpost.trans hcleanState⟩

def BenvExecution.state : Except (EvmError × Jaune.State × AdrSet × Tra) Benv →
    Jaune.State
  | .ok benv => benv.state
  | .error ⟨_, st, _, _⟩ => st

/-! Error-side `getBal` frame lemmas, mirroring the generated `*_getCode_err`
family in `Blanc/Common.lean`: every regular-instruction error path leaves
balances unchanged. -/

lemma Rinst.inv_getBal_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Devm.StateWriteFrame.getBal_eq hf a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact congrFun (congrArg (fun s => s.bal) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (hf.getBal a).symm

lemma Rinst.balance_effect (r : Rinst) :
    Rinst.Effect Devm.BalNoninc r := by
  intro pc sevm pre out hrun
  cases out with
  | ok post => exact Devm.balNoninc_of_getBal_eq (Rinst.preserves_bal hrun).symm
  | error err => exact Devm.balNoninc_of_getBal_eq (funext fun a => Rinst.inv_getBal_err hrun a)

lemma Jinst.balance_effect (j : Jinst) :
    Jinst.Effect Devm.BalNoninc j := by
  intro evm out hrun
  have hf := Jinst.run_instructionFrame evm j
  rw [hrun] at hf
  cases out <;> exact Devm.balNoninc_of_getBal_eq
    (funext fun a => (hf.getBal a).symm)

lemma Ninst.push_balance_effectRec {xs : Bytes} {hxs : xs.length ≤ 32} :
    Ninst.EffectRec Devm.BalNoninc (.push xs hxs) := by
  exact Ninst.push_effectRec_of_instructionFrame (R := Devm.BalNoninc)
    (fun _ _ hf =>
      Devm.balNoninc_of_getBal_eq (funext fun a => (hf.getBal a).symm))

lemma Ninst.dupn_balance_effectRec {imm : UInt8} :
    Ninst.EffectRec Devm.BalNoninc (.dupn imm) := by
  exact Ninst.dupn_effectRec_of_instructionFrame (R := Devm.BalNoninc)
    (fun _ _ hf =>
      Devm.balNoninc_of_getBal_eq (funext fun a => (hf.getBal a).symm))

lemma Ninst.swapn_balance_effectRec {imm : UInt8} :
    Ninst.EffectRec Devm.BalNoninc (.swapn imm) := by
  exact Ninst.swapn_effectRec_of_instructionFrame (R := Devm.BalNoninc)
    (fun _ _ hf =>
      Devm.balNoninc_of_getBal_eq (funext fun a => (hf.getBal a).symm))

lemma Ninst.exchange_balance_effectRec {imm : UInt8} :
    Ninst.EffectRec Devm.BalNoninc (.exchange imm) := by
  exact Ninst.exchange_effectRec_of_instructionFrame (R := Devm.BalNoninc)
    (fun _ _ hf =>
      Devm.balNoninc_of_getBal_eq (funext fun a => (hf.getBal a).symm))

/-- An instruction frame is balance-silent, hence transports directly to the
total-balance preorder used by the balance-effect layer. -/
lemma Devm.instructionFrame_refines_balNoninc :
    ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → Devm.BalNoninc d d' := by
  intro pre post h
  apply Devm.balNoninc_of_state
  rw [h.state]
  exact balNoninc_refl_trans.1.1 _

/-- Charging state gas is balance-silent: it refines the instruction frame,
hence transports to the balance preorder on either outcome. -/
lemma Devm.chargeStateGas_balNoninc {amount : Nat} {d : Devm}
    {exn : Execution} (h : chargeStateGas amount d = exn) :
    Execution.Rel Devm.BalNoninc d exn := by
  rw [← h]
  exact Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
    (chargeStateGas_instructionFrame amount d)

lemma Devm.chargeStateGas_balNoninc_of_ok {amount : Nat} {d d' : Devm}
    (h : chargeStateGas amount d = .ok d') :
    Devm.BalNoninc d d' := by
  have hr := Devm.chargeStateGas_balNoninc h
  exact hr

/-- Historical presence-preserving beneficiary credits and ordinary credits
have identical balances, although their account-presence observations differ. -/
lemma Devm.creditBeneficiary_getBal (rules : ForkRules) (donee : Adr)
    (value : B256) (d : Devm) :
    (d.creditBeneficiary rules donee value).getBal = (d.addBal donee value).getBal := by
  unfold Devm.creditBeneficiary
  split
  · rfl
  · funext a
    change ((d.state.setPresent donee
      ((d.state.get donee).withBal (d.state.bal donee + value))).get a).bal =
        ((d.state.addBal donee value).get a).bal
    unfold State.addBal State.setBal
    by_cases h : donee = a
    · subst a
      rw [State.get_setPresent_self, State.setAccount_get_self, Acct.clearIfEmpty_bal]
    · rw [State.get_setPresent_ne _ h, State.setAccount_get_ne _ h]

lemma Linst.selfdestruct_balance_effect :
    Linst.Effect Devm.BalNoninc .selfdestruct := by
  intro sevm pre out run
  dsimp only [Linst.Run, Linst.run, ne_eq, Except.bind_ok, ite_not, Lean.Elab.WF.paramLet,
    Devm.balReadAccount_accessedAddresses, Devm.balReadAccount_getAcct] at run
  revert run
  cases hsg : sevm.benvStat.rules.stateGas
  · -- Covered-fork lane: priced access over balance reads, charge, sweep.
    intro run
    dsimp only [Devm.balReadAccount_accessedAddresses, ite_not, bind, Except.bind] at run
    revert run
    cases h1 : pre.popToAdr <;> dsimp only [Devm.balReadAccount_accessedAddresses, ite_not]
    case error err =>
      intro run
      rw [← run]
      apply Devm.balNoninc_of_getBal_eq
      rw [Devm.popToAdr_err_snd h1]
    case ok res1 =>
      have hpop : res1.2.getBal = pre.getBal := by
        funext a
        exact Devm.popToAdr_getBal_eq h1 a
      have hacc : (match sevm.benvStat.rules.access with | .eip2929 => (if res1.1 ∉ (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).accessedAddresses then (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)) res1.1, gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess) else ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)) | .flat _ => ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)).1.getBal = res1.2.getBal := by
        funext a
        cases haccess : sevm.benvStat.rules.access <;> dsimp only <;>
          (try split) <;>
          exact (Devm.balReadAccount_getBal sevm.benvStat.rules sevm.currentTarget a
            (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).trans
            (Devm.balReadAccount_getBal sevm.benvStat.rules res1.1 a res1.2)
      cases h2 : chargeGas _ _ <;> dsimp only
      case error err =>
        intro run
        rw [← run]
        apply Devm.balNoninc_of_getBal_eq
        rw [chargeGas_err_snd h2]
        exact hacc.trans hpop
      case ok res2 =>
        have hpre : res2.getBal = pre.getBal := by
          funext a
          exact (chargeGas_getBal_eq h2 a).trans
            (congrFun (hacc.trans hpop) a)
        cases h3 : assertDynamic sevm res2
        case error err =>
          intro run
          rw [← run]
          apply Devm.balNoninc_of_getBal_eq
          have herr : err.2 = res2 := by
            dsimp only [assertDynamic] at h3
            exact Except.assert_err_snd h3
          rw [herr]
          exact hpre
        case ok _ =>
          cases h4 : res2.subBal _ _ <;> dsimp only [Option.toExcept]
          case none =>
            intro run
            rw [← run]
            exact Devm.balNoninc_of_getBal_eq hpre
          case some res3 =>
            have hsub : res2.state.subBal sevm.currentTarget
                (res1.2.getAcct sevm.currentTarget).bal = some res3.state := by
              dsimp only [Devm.subBal, Option.bind_eq_bind, Option.bind] at h4
              cases hs : res2.state.subBal sevm.currentTarget
                  (res1.2.getAcct sevm.currentTarget).bal
              · rw [hs] at h4
                contradiction
              · rw [hs] at h4
                injection h4 with heq
                subst heq
                rfl
            have htransfer : State.BalNoninc pre.state
                (res3.addBal res1.1
                  (res1.2.getAcct sevm.currentTarget).bal).state := by
              have ht := State.sub_addBal_noninc (dst := res1.1) hsub
              have hbal : res2.state.bal = pre.state.bal := hpre
              unfold State.BalNoninc State.balSum at ht ⊢
              rw [hbal] at ht
              exact ht
            let credited := res3.creditBeneficiary sevm.benvStat.rules res1.1
              (res1.2.getAcct sevm.currentTarget).bal
            have hcredit : State.BalNoninc pre.state credited.state := by
              have heq : credited.state.bal =
                  (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).state.bal :=
                Devm.creditBeneficiary_getBal _ _ _ _
              unfold State.BalNoninc State.balSum at *
              rw [heq]
              exact htransfer
            change (if sevm.currentTarget ∈ credited.createdAccounts ∨
                sevm.benvStat.rules.settle.selfdestructOnlyCreated = false then
              .ok (creditSelfdestructRefund sevm.benvStat.rules
                (sevm.currentTarget ∈ credited.accountsToDelete)
                (addAccountToDelete (credited.setBal sevm.currentTarget 0)
                  sevm.currentTarget)) else .ok credited) = out → _
            split
            · intro run; rw [← run]
              apply Devm.balNoninc_of_state
              change State.BalNoninc pre.state
                (creditSelfdestructRefund _ _ _).state
              have hstate (d : Devm) :
                  (creditSelfdestructRefund sevm.benvStat.rules
                    (sevm.currentTarget ∈ credited.accountsToDelete) d).state = d.state := by
                unfold creditSelfdestructRefund
                split <;> rfl
              rw [hstate]
              exact balNoninc_refl_trans.1.2 hcredit (State.setBal_zero_noninc _ _)
            · intro run; rw [← run]
              exact Devm.balNoninc_of_state hcredit
  · -- Amsterdam lane: static check, priced access, state charges, logging sweep.
    rename_i state
    intro run
    dsimp only [Devm.balReadAccount_accessedAddresses, ite_not, bind, Except.bind] at run
    revert run
    cases h0 : assertDynamic sevm pre <;> dsimp only [ite_not]
    case error err =>
      intro run; rw [← run]
      apply Devm.balNoninc_of_getBal_eq
      have herr : err.2 = pre := by
        dsimp only [assertDynamic] at h0
        exact Except.assert_err_snd h0
      rw [herr]
    case ok _ =>
      cases h1 : pre.popToAdr <;> dsimp only [ite_not]
      case error err =>
        intro run; rw [← run]
        apply Devm.balNoninc_of_getBal_eq
        rw [Devm.popToAdr_err_snd h1]
      case ok res1 =>
        have hpop : res1.2.getBal = pre.getBal := by
          funext a
          exact Devm.popToAdr_getBal_eq h1 a
        cases hg : Except.assert (gasSelfDestruct + (if res1.1 ∉ res1.2.accessedAddresses then sevm.benvStat.rules.gas.coldAccountAccess else 0) ≤ res1.2.gasLeft) (⟨.halt (.outOfGas .none), res1.2⟩ : EvmError × Devm) <;> dsimp only [ite_not]
        case error err =>
          intro run; rw [← run]
          apply Devm.balNoninc_of_getBal_eq
          have herr : err.2 = res1.2 := Except.assert_err_snd hg
          rw [herr]
          exact hpop
        case ok _ =>
          have hwb : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2))).getBal = res1.2.getBal := by
            funext a
            have e1 : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2))).getBal a = (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2).getBal a :=
              (Devm.balReadAccount_getBal _ _ _ _).trans (Devm.balReadAccount_getBal _ _ _ _)
            have e2 : (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2).getBal a = res1.2.getBal a := by
              split <;> rfl
            exact e1.trans e2
          cases hchg : chargeGas _ _ <;> dsimp only [ite_not]
          case error err =>
            intro run; rw [← run]
            apply Devm.balNoninc_of_getBal_eq
            rw [chargeGas_err_snd hchg]
            exact hwb.trans hpop
          case ok res2 =>
            have hpre2 : res2.getBal = pre.getBal := by
              funext a
              exact (chargeGas_getBal_eq hchg a).trans
                (congrFun (hwb.trans hpop) a)
            cases hstg : chargeStateGas _ _ <;> dsimp only [ite_not]
            case error err =>
              intro run; rw [← run]
              exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
                (Devm.balNoninc_of_getBal_eq hpre2)
                (Devm.chargeStateGas_balNoninc hstg)
            case ok res2b =>
              have hPre : Devm.BalNoninc pre res2b :=
                balNoninc_refl_trans.2.2 (Devm.balNoninc_of_getBal_eq hpre2)
                  (Devm.chargeStateGas_balNoninc_of_ok hstg)
              have hPreState : State.BalNoninc pre.state res2b.state := hPre
              cases h4 : res2b.subBal _ _ <;> dsimp only [Option.toExcept, ite_not]
              case none =>
                intro run; rw [← run]
                exact hPre
              case some res3 =>
                have hsub : res2b.state.subBal sevm.currentTarget (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal = some res3.state := by
                  dsimp only [Devm.subBal, Option.bind_eq_bind, Option.bind] at h4
                  cases hs : res2b.state.subBal sevm.currentTarget (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal
                  · rw [hs] at h4
                    simp only [reduceCtorEq] at h4
                  · rw [hs] at h4
                    injection h4 with heq
                    subst heq
                    rfl
                have htransfer : State.BalNoninc pre.state (res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).state :=
                  balNoninc_refl_trans.1.2 hPreState (State.sub_addBal_noninc (dst := res1.1) hsub)
                by_cases h_if : sevm.currentTarget ∈ ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).createdAccounts
                · simp only [h_if, ite_eq_left]
                  intro run; rw [← run]
                  unfold Execution.Rel Outcome.Rel
                  apply Devm.balNoninc_of_state
                  apply balNoninc_refl_trans.1.2 htransfer
                  rw [(Devm.emitTransferLog_instructionFrame _ _ _ _).state]
                  exact balNoninc_refl_trans.1.1 _
                · simp only [h_if]
                  intro run; rw [← run]
                  unfold Execution.Rel Outcome.Rel
                  apply Devm.balNoninc_of_state
                  apply balNoninc_refl_trans.1.2 htransfer
                  rw [(Devm.emitTransferLog_instructionFrame _ _ _ _).state]
                  exact balNoninc_refl_trans.1.1 _

lemma Linst.balance_effect (l : Linst) :
    Linst.Effect Devm.BalNoninc l := by
  rcases eq_or_ne l .selfdestruct with rfl | h_not_selfdestruct
  · exact Linst.selfdestruct_balance_effect
  · intro sevm pre out run
    have hf := Linst.run_instructionFrame sevm pre l h_not_selfdestruct
    rw [run] at hf
    cases out <;> exact Devm.balNoninc_of_getBal_eq
      (funext fun a => (hf.getBal a).symm)

lemma Msg.benvAfterTransfer_balance_effect {msg : Msg}
    {out : Except (EvmError × Jaune.State × AdrSet × Tra) Benv}
    (h : msg.benvAfterTransfer = out) :
    State.BalNoninc msg.benv.state (BenvExecution.state out) := by
  by_cases h_stv : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · unfold Msg.benvAfterTransfer at h
    rw [ite_eq_left h_stv] at h
    unfold Benv.subBal at h
    rcases h_sub : msg.benv.state.subBal msg.caller msg.value with _ | st_mid
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      exact Nat.le_refl _
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      change State.BalNoninc msg.benv.state (st_mid.addBal msg.currentTarget msg.value)
      exact State.sub_addBal_noninc h_sub
  · unfold Msg.benvAfterTransfer at h
    rw [ite_eq_right h_stv] at h
    rw [← h]
    exact Nat.le_refl _

lemma processCreateMessage.chargeCodeGas_balance_effect
    {rules : ForkRules} {pre : Devm} {out : Execution}
    (h : processCreateMessage.chargeCodeGas rules pre = out) :
    Execution.Rel Devm.BalNoninc pre out := by
  rw [← h]
  exact Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
    (processCreateMessage.chargeCodeGas_instructionFrame rules pre)

lemma executePrecomp_balance_effect {evm : Evm} {a : Adr} {out : Execution}
    (h : executePrecomp evm a = out) :
    Execution.Rel Devm.BalNoninc evm.dyna out := by
  subst out
  unfold executePrecomp applyPrecompResult Execution.Rel Outcome.Rel
    Devm.BalNoninc Devm.balSum State.balSum
  cases precompileRun evm a <;> rfl

/-- `executeCode.handleError` selects between the raw execution result and a
rolled-back state without introducing any balance write of its own, so it
transports a raw `Devm.BalNoninc` frame to a `State.BalNoninc` on the handled
message outcome. -/
lemma executeCode.handleError_balance_effect {pre : Devm} {raw : Execution}
    {handled : MessageExecution} {stateGas : Option StateGasRules}
    (hb : Execution.Rel Devm.BalNoninc pre raw)
    (hh : executeCode.handleErrorWith stateGas raw = handled) :
    State.BalNoninc pre.state (MessageExecution.state handled) := by
  unfold executeCode.handleErrorWith at hh
  split at hh
  · rcases raw with ⟨err, d⟩ | d
    · cases err <;>
        (simp only [executeCode.handleError] at hh; subst handled; exact hb)
    · simp only [executeCode.handleError] at hh
      subst handled
      exact hb
  · rcases raw with ⟨err, d⟩ | d
    · cases err <;>
        (simp only [executeCode.handleErrorAmsterdam] at hh; subst handled; exact hb)
    · simp only [executeCode.handleErrorAmsterdam] at hh
      subst handled
      exact hb

/-- Frame projections of the two child messages, as explicit equations: the
defeq is cheap to state and expensive to re-derive at every use site. -/
lemma callMsg_benv_state
    {sevm : Sevm} {evm1 : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {calldata : Bytes}
    {code : ByteArray} {dp : Bool} :
    ( callMsg sevm evm1 gas value caller target codeAddress stv isSt calldata
        code dp ).benv.state = evm1.state := rfl

lemma createMsg_benv_state
    {sevm : Sevm} {devm : Devm} {createGas : Nat} {endowment : B256}
    {newAddress : Adr} {calldata : Bytes} :
    (createMsg sevm devm createGas endowment newAddress calldata).benv.state
      = devm.state := rfl

lemma callMsgAmsterdam_benv_state
    {sevm : Sevm} {evm1 : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {calldata : Bytes}
    {code : ByteArray} {dp : Bool} {reservoir : Nat} :
    ( { callMsg sevm evm1 gas value caller target codeAddress stv isSt calldata
        code dp with stateGasGrant := reservoir } ).benv.state
      = evm1.state := rfl

lemma createMsgAmsterdam_benv_state
    {sevm : Sevm} {devm : Devm} {createGas : Nat} {endowment : B256}
    {newAddress : Adr} {calldata : Bytes} {reservoir : Nat} :
    ( { createMsg sevm devm createGas endowment newAddress calldata
        with stateGasGrant := reservoir } ).benv.state
      = devm.state := rfl

/-- The create driver is the call driver on the seeded message, followed by the
create-specific settlement. -/
lemma processCreateMessage_eq (msg : Msg) :
    processCreateMessage msg =
      processCreateMessage.settle msg
        (processMessage (processCreateMessage.msg msg)) := by
  unfold processCreateMessage processMessage runFrame Frame.enter Frame.settle
    Frame.settleMsg Frame.ofCreate Frame.ofCall
  rcases (processCreateMessage.msg msg).benvAfterTransfer with e | benv <;>
    simp only [reduceIte]
  · rfl
  · rcases executeCode.enter ((processCreateMessage.msg msg).withBenv benv) with
      evm | raw
    · rfl
    · rfl

lemma processCreateMessage.settle_error {msg : Msg}
    {e : EvmError × Jaune.State × AdrSet × Tra} :
    processCreateMessage.settle msg (.error e) = .error e := rfl

/-- A failed child message aborts the CREATE-family return path. -/
lemma Resume.create_run_error {parent : Devm} {newAddress : Adr}
    {e : EvmError × Jaune.State × AdrSet × Tra} {sf : Devm}
    (h : (Resume.create parent newAddress).run (.error e) = .ok sf) : False := by
  rcases e with ⟨err, st, ac, tra⟩
  unfold Resume.run liftToExecution at h
  cases h

lemma processMessage.settle_error {msg : Msg}
    {e : EvmError × Jaune.State × AdrSet × Tra} :
    processMessage.settle msg (.error e) = .error e := rfl

/-- **Message settlement inverted.**  A frame that settles `.ok` came from an
`.ok` sub-result, and the settled state is either that sub-result rolled back
to the message's entry world, or the sub-result itself — according to whether
it carried an error.

This is the general shape that `processMessage.settle_ok_gasLe` upstream
projects onto gas.  Consumers previously re-derived it inline: dispatch the
`.error` arm through `settle_error`, unfold the settle, and split on
`evm.error.isSome`.  Taking the disjunction directly replaces that walk with a
single `rcases`, and keeps the rollback's world arguments named rather than
re-elaborated at each site. -/
theorem processMessage.settle_ok_cases {msg : Msg}
    {r : Except (EvmError × Jaune.State × AdrSet × Tra) Devm} {post : Devm}
    (hset : processMessage.settle msg r = .ok post) :
    ∃ evm : Devm, r = .ok evm ∧
      (evm.error.isSome = true ∧
          Devm.recordTouch msg.benv.stat.rules
            (msg.currentTarget == ripemd160Address) msg.currentTarget
            ((evm.rollback msg.benv.state msg.tenv.transientStorage).withStorageWrites
              msg.benv.storageWrites) = post
        ∨ ¬ evm.error.isSome = true ∧
          Devm.recordTouch msg.benv.stat.rules true msg.currentTarget evm = post) := by
  cases r with
  | error e => exact absurd hset (by rw [processMessage.settle_error]; simp only [reduceCtorEq,
    not_false_eq_true])
  | ok evm =>
    refine ⟨evm, rfl, ?_⟩
    unfold processMessage.settle at hset
    dsimp only [bind, Except.bind] at hset
    by_cases herr : evm.error.isSome = true
    · rw [ite_eq_left herr] at hset
      exact .inl ⟨herr, Except.ok.inj hset⟩
    · rw [ite_eq_right herr] at hset
      exact .inr ⟨herr, Except.ok.inj hset⟩

/-- Master balance effect for the code-execution layer: running the callee's
code (interpreter, precompile, or the empty-code no-op) never increases the
total balance relative to the freshly-initialised message state. The `Xlot`
witness carries the interpreter's own `Devm.BalNoninc` frame; the precompile
branch supplies its frame directly. -/
lemma ExecuteCode.balance_effect {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (hec : ExecuteCode msg xl ex) :
    State.BalNoninc (initEvm msg).dyna.state (MessageExecution.state ex) := by
  unfold ExecuteCode at hec
  rcases henter : executeCode.enter msg with evm | raw <;> rw [henter] at hec
  · rcases hec with ⟨raw, hxl_eq, hh⟩
    rw [hxl_eq] at hxl
    rw [executeCode.enter_inl henter] at hxl
    exact executeCode.handleError_balance_effect hxl hh.symm
  · obtain ⟨adr, hraw⟩ := executeCode.enter_inr henter
    refine executeCode.handleError_balance_effect ?_ hec.2.symm
    rw [hraw]
    exact executePrecomp_balance_effect rfl

lemma ProcessMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp run
  unfold FrameBody at hbody
  rcases h_benv : msg.benvAfterTransfer with ⟨err, st, ac, tra⟩ | benv <;>
    rw [h_benv] at hbody
  · rw [hbody.2, processMessage.settle_error]
    have ht := Msg.benvAfterTransfer_balance_effect h_benv
    simp only [MessageExecution.Rel, MessageExecution.state,
      BenvExecution.state] at ht ⊢
    exact ht
  · have htransfer := Msg.benvAfterTransfer_balance_effect h_benv
    have hexec : State.BalNoninc benv.state (MessageExecution.state r0) := by
      have h := ExecuteCode.balance_effect hxl hbody
      have hinit : (initEvm (msg.withBenv benv)).dyna.state = benv.state := rfl
      rwa [hinit] at h
    unfold processMessage.settle
    rcases r0 with e' | evm
    · exact Nat.le_trans hexec htransfer
    · dsimp only [bind, Except.bind]
      split
      · exact balNoninc_refl_trans.1.1 _
      · exact Nat.le_trans hexec htransfer

lemma ProcessCreateMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessCreateMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  obtain ⟨ex', run_pm, rfl⟩ := ProcessCreateMessage.iff_processMessage.mp run
  have h_seed : (processCreateMessage.msg msg).benv.state.bal = msg.benv.state.bal := by
    change ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
      msg.currentTarget).bal = msg.benv.state.bal
    rw [State.incrNonce_bal, State.setStor_bal]
  have h_pm := ProcessMessage.balance_effect hxl run_pm
  unfold MessageExecution.Rel State.BalNoninc State.balSum at h_pm
  rw [h_seed] at h_pm
  unfold processCreateMessage.settle
  rcases ex' with e' | evm
  · exact h_pm
  · dsimp only [bind, Except.bind]
    split
    · cases h_cg : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
      | error err =>
        rcases err with ⟨err_msg, err_evm⟩
        have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
        unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum
          State.balSum at h_charge
        dsimp only [id] at h_charge
        dsimp only [MessageExecution.state] at h_pm
        cases err_msg
        case halt =>
          dsimp only
          cases hsg : msg.benv.stat.rules.stateGas
          · exact balNoninc_refl_trans.1.1 _
          · exact balNoninc_refl_trans.1.1 _
        all_goals exact Nat.le_trans h_charge h_pm
      | ok devm_charge =>
        dsimp only []
        have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
        unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum
          State.balSum at h_charge
        dsimp only [id] at h_charge
        dsimp only [MessageExecution.state] at h_pm
        change sum (devm_charge.state.setCode msg.currentTarget
          ⟨⟨devm_charge.output⟩⟩).bal ≤ sum msg.benv.state.bal
        rw [State.setCode_bal]
        exact Nat.le_trans h_charge h_pm
    · exact balNoninc_refl_trans.1.1 _

/-- The create prefix's sender nonce bump is a non-balance world write. -/
lemma Devm.incrNonce_balance_effect (pre : Devm) (a : Adr) :
    Devm.BalNoninc pre (pre.incrNonce a) := by
  unfold Devm.BalNoninc Devm.balSum State.balSum
  change sum (pre.state.incrNonce a).bal ≤ sum pre.state.bal
  rw [State.incrNonce_bal]

/-- Child-error incorporation installs the child's already-accounted world;
the parent fields it retains do not include balances. -/
lemma incorporateChildOnError_balance_effect
    {pre parent child : Devm} {returnData : Bytes}
    (h : State.BalNoninc pre.state child.state) :
    Devm.BalNoninc pre
      (incorporateChildOnError parent child returnData) := by
  apply Devm.balNoninc_of_state
  dsimp only [incorporateChildOnError]
  exact h

/-- Child-success incorporation has the same precise balance projection as
the error form, while differing in the non-balance fields it incorporates. -/
lemma incorporateChildOnSuccess_balance_effect
    {pre parent child : Devm} {returnData : Bytes}
    (h : State.BalNoninc pre.state child.state) :
    Devm.BalNoninc pre
      (incorporateChildOnSuccess parent child returnData) := by
  apply Devm.balNoninc_of_state
  dsimp only [incorporateChildOnSuccess]
  exact h

lemma incorporateChildAmsterdamOnError_balance_effect
    {pre parent child : Devm} {returnData : Bytes}
    (h : State.BalNoninc pre.state child.state) :
    Devm.BalNoninc pre
      (incorporateChildAmsterdamOnError parent child returnData) := by
  apply Devm.balNoninc_of_state
  dsimp only [incorporateChildAmsterdamOnError]
  exact h

lemma incorporateChildAmsterdamOnSuccess_balance_effect
    {pre parent child : Devm} {returnData : Bytes}
    (h : State.BalNoninc pre.state child.state) :
    Devm.BalNoninc pre
      (incorporateChildAmsterdamOnSuccess parent child returnData) := by
  apply Devm.balNoninc_of_state
  dsimp only [incorporateChildAmsterdamOnSuccess]
  exact h

/-- Pushing a status word and writing the returned output to memory are both
frame moves, so they carry a balance bound on the incorporated machine. -/
lemma Devm.pushMemWrite_balance {pre d : Devm} {v : B256} {oi : Nat} {o : Bytes}
    (h : Devm.BalNoninc pre d) :
    Execution.Rel Devm.BalNoninc pre
      (d.push v >>= fun d' => .ok (d'.memWrite oi o)) := by
  refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 h ?_
  refine Execution.Rel.bind balNoninc_refl_trans.2.2
    (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
      (Devm.push_instructionFrame v d)) ?_
  intro d'
  exact Devm.instructionFrame_refines_balNoninc
    (Devm.memWrite_instructionFrame d' oi o)

/-- A status push onto a machine already bounded against `pre` keeps the
bound, on both outcomes. -/
lemma Devm.push_balance_gen {v : B256} {pre d : Devm} {ex : Execution}
    (h : Devm.push v d = ex) (hf : Devm.BalNoninc pre d) :
    Execution.Rel Devm.BalNoninc pre ex := by
  subst h
  exact Execution.Rel.trans_left balNoninc_refl_trans.2.2 hf
    (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
      (Devm.push_instructionFrame v d))

/-- The CREATE-family return path never raises the parent's balance sum: the
child's world is already bounded and the status push is a frame move. -/
lemma Resume.create_balance {parent : Devm} {newAddress : Adr}
    {r : MessageExecution}
    (h : State.BalNoninc parent.state (MessageExecution.state r)) :
    Execution.Rel Devm.BalNoninc parent
      ((Resume.create parent newAddress).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;> dsimp only [bind, Except.bind]
  · simp only [Execution.Rel, Outcome.Rel]
    exact h
  · split
    · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
        (incorporateChildOnError_balance_effect h)
        (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
          (Devm.push_instructionFrame 0 _))
    · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
        (incorporateChildOnSuccess_balance_effect h)
        (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
          (Devm.push_instructionFrame _ _))

/-- The CALL-family return path, likewise: incorporation plus a push and a
memory write. -/
lemma Resume.call_balance {parent : Devm} {oi os : Nat} {r : MessageExecution}
    (h : State.BalNoninc parent.state (MessageExecution.state r)) :
    Execution.Rel Devm.BalNoninc parent ((Resume.call parent oi os).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;> dsimp only [bind, Except.bind]
  · simp only [Execution.Rel, Outcome.Rel]
    exact h
  · split
    · exact Devm.pushMemWrite_balance (incorporateChildOnError_balance_effect h)
    · exact Devm.pushMemWrite_balance (incorporateChildOnSuccess_balance_effect h)

/-- The Amsterdam CREATE-family return path never raises the parent's balance
sum: the guards fail with the child itself, the refund credit touches gas
only, and incorporation plus the status push are bounded as in the legacy
path. -/
lemma Resume.createAmsterdam_balance {state : StateGasRules} {parent : Devm}
    {newAddress : Adr} {nac : Bool} {r : MessageExecution}
    (h : State.BalNoninc parent.state (MessageExecution.state r)) :
    Execution.Rel Devm.BalNoninc parent
      ((Resume.createAmsterdam state parent newAddress nac).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind, Except.assert]
  · simp only [Execution.Rel, Outcome.Rel]
    exact h
  · split
    · by_cases hP : child.AmsterdamFailedChildSettled
      · rw [ite_eq_left hP]
        dsimp only
        by_cases hnac : nac = true
        · rw [ite_eq_left hnac]
          refine Execution.Rel.trans_left balNoninc_refl_trans.2.2
            (balNoninc_refl_trans.2.2
              (incorporateChildAmsterdamOnError_balance_effect h)
              (Devm.instructionFrame_refines_balNoninc
                (Devm.creditStateGasRefund_instructionFrame _ _)))
            (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
              (Devm.push_instructionFrame 0 _))
        · rw [ite_eq_right hnac]
          exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
            (incorporateChildAmsterdamOnError_balance_effect h)
            (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
              (Devm.push_instructionFrame 0 _))
      · rw [ite_eq_right hP]
        simp only [Execution.Rel, Outcome.Rel]
        exact Devm.balNoninc_of_state h
    · by_cases hP : child.AmsterdamChildUncommitted
      · rw [ite_eq_left hP]
        dsimp only
        exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
          (incorporateChildAmsterdamOnSuccess_balance_effect h)
          (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
            (Devm.push_instructionFrame _ _))
      · rw [ite_eq_right hP]
        simp only [Execution.Rel, Outcome.Rel]
        exact Devm.balNoninc_of_state h

/-- The Amsterdam CALL-family return path, likewise: incorporation plus a
push and a memory write, with the guard and credit steps bounded. -/
lemma Resume.callAmsterdam_balance {state : StateGasRules} {parent : Devm}
    {oi os : Nat} {nac : Bool} {r : MessageExecution}
    (h : State.BalNoninc parent.state (MessageExecution.state r)) :
    Execution.Rel Devm.BalNoninc parent
      ((Resume.callAmsterdam state parent oi os nac).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind, Except.assert]
  · simp only [Execution.Rel, Outcome.Rel]
    exact h
  · split
    · by_cases hP : child.AmsterdamFailedChildSettled
      · rw [ite_eq_left hP]
        dsimp only
        by_cases hnac : nac = true
        · rw [ite_eq_left hnac]
          exact Devm.pushMemWrite_balance
            (balNoninc_refl_trans.2.2
              (incorporateChildAmsterdamOnError_balance_effect h)
              (Devm.instructionFrame_refines_balNoninc
                (Devm.creditStateGasRefund_instructionFrame _ _)))
        · rw [ite_eq_right hnac]
          exact Devm.pushMemWrite_balance
            (incorporateChildAmsterdamOnError_balance_effect h)
      · rw [ite_eq_right hP]
        simp only [Execution.Rel, Outcome.Rel]
        exact Devm.balNoninc_of_state h
    · by_cases hP : child.AmsterdamChildUncommitted
      · rw [ite_eq_left hP]
        dsimp only
        exact Devm.pushMemWrite_balance
          (incorporateChildAmsterdamOnSuccess_balance_effect h)
      · rw [ite_eq_right hP]
        simp only [Execution.Rel, Outcome.Rel]
        exact Devm.balNoninc_of_state h

/-- Canonical balance-effect master for generic calls.  The call prefix is
balance-silent; all balance changes are delegated to `ProcessMessage`, and
child incorporation merely installs the child's already-bounded state. -/
lemma GenericCall.balanceEffect
    {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code dp xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  have hret : Devm.BalNoninc pre (pre.withReturnData []) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl)
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl)
  -- depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl)
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 hret ?_
    refine Resume.call_balance ?_
    have h := ProcessMessage.balance_effect hxl hframe
    unfold MessageExecution.Rel at h
    rwa [callMsg_benv_state] at h

lemma GenericCallAmsterdam.balanceEffect
    {sevm : Sevm} {state : StateGasRules} {pre : Devm} {gas reservoir : Nat}
    {value : B256} {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray}
    {dp nac ib : Bool} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCallAmsterdam sevm state pre gas reservoir value caller
      target codeAddress stv istat ii is oi os code dp nac ib xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  have hret : Devm.BalNoninc pre (pre.withReturnData []) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl)
  unfold GenericCallAmsterdam genericCallAmsterdam.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  all_goals first
    | obtain ⟨-, rfl⟩ := run
      rename_i heq
      by_cases hnac : nac = true
      · simp only [hnac] at heq
        refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
        exact Devm.instructionFrame_refines_balNoninc
          (Devm.instructionFrame_trans
            (Devm.restoreChildGas_instructionFrame _ _ _)
            (Devm.creditStateGasRefund_instructionFrame _ _))
      · simp only [hnac] at heq
        refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
        exact Devm.instructionFrame_refines_balNoninc
          (Devm.restoreChildGas_instructionFrame _ _ _)
    | obtain ⟨r, hframe, rfl⟩ := run
      refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 hret ?_
      refine Resume.callAmsterdam_balance ?_
      have h := ProcessMessage.balance_effect hxl hframe
      unfold MessageExecution.Rel at h
      rwa [callMsgAmsterdam_benv_state] at h

/-- Canonical balance-effect master for generic creates.  Unlike calls, its
prefix contains the sender nonce write and its child path performs fresh
account initialisation before installing the child world. -/
lemma GenericCreate.balanceEffect
    {sevm : Sevm} {pre : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCreate sevm pre endowment newAddress mi ms xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  have hgas : Devm.BalNoninc pre
      (pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl)
  have hret : Devm.BalNoninc pre
      ((pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)).withReturnData []) :=
    balNoninc_refl_trans.2.2 hgas
      (Devm.instructionFrame_refines_balNoninc
        (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl))
  have hnonce : Devm.BalNoninc pre
      (addAccessedAddress
        (((pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress) := by
    refine balNoninc_refl_trans.2.2 hret ?_
    refine balNoninc_refl_trans.2.2
      (Devm.incrNonce_balance_effect _ sevm.currentTarget) ?_
    exact Devm.instructionFrame_refines_balNoninc
      (addAccessedAddress_instructionFrame _ newAddress)
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- init-code-size assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    exact balNoninc_refl_trans.2.1 _
  -- static-context assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    exact hgas
  -- balance / max-nonce / depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl)
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl)
  -- address-collision early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    exact Devm.push_balance_gen heq hnonce
  -- address-collision early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    exact Devm.push_balance_gen heq hnonce
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 hnonce ?_
    refine Resume.create_balance ?_
    have h := ProcessCreateMessage.balance_effect hxl hframe
    unfold MessageExecution.Rel at h
    rwa [createMsg_benv_state] at h

lemma GenericCreateAmsterdam.balanceEffect
    {sevm : Sevm} {state : StateGasRules} {pre : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCreateAmsterdam sevm state pre endowment newAddress mi ms
      xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  have hret : Devm.BalNoninc pre (pre.withReturnData []) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl)
  have hD : Devm.BalNoninc pre
      (Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress)) :=
    balNoninc_refl_trans.2.2 hret
      (balNoninc_refl_trans.2.2
        (Devm.instructionFrame_refines_balNoninc
          (Devm.balReadAccount_instructionFrame sevm.benvStat.rules
            sevm.currentTarget _))
        (balNoninc_refl_trans.2.2
          (Devm.instructionFrame_refines_balNoninc
            (addAccessedAddress_instructionFrame _ newAddress))
          (Devm.instructionFrame_refines_balNoninc
            (Devm.balReadAccount_instructionFrame sevm.benvStat.rules
              newAddress _))))
  have hW2 : Devm.BalNoninc
      (Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress))
      ((Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData []))
          newAddress)).withholdCreateGas.2) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.withholdCreateGas_instructionFrame _)
  have hPc : Devm.BalNoninc
      ((Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData []))
          newAddress)).withholdCreateGas.2)
      (((Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData []))
          newAddress)).withholdCreateGas.2).incrNonce sevm.currentTarget) :=
    Devm.incrNonce_balance_effect _ sevm.currentTarget
  have hR2 : Devm.BalNoninc
      ((Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData []))
          newAddress)).withholdCreateGas.2)
      (((Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData []))
          newAddress)).withholdCreateGas.2).drainStateGasReservoir.2) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.drainStateGasReservoir_instructionFrame _)
  have hP2 : Devm.BalNoninc
      (((Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData []))
          newAddress)).withholdCreateGas.2).drainStateGasReservoir.2)
      ((((Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData []))
          newAddress)).withholdCreateGas.2).drainStateGasReservoir.2).incrNonce
        sevm.currentTarget) :=
    Devm.incrNonce_balance_effect _ sevm.currentTarget
  unfold GenericCreateAmsterdam genericCreateAmsterdam.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- preflight abort, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.balReadAccount_instructionFrame _ _ _)
  -- preflight abort, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.balReadAccount_instructionFrame _ _ _)
  -- creation charge failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    exact Execution.Rel.trans_left balNoninc_refl_trans.2.2 hD
      (Devm.chargeStateGas_balNoninc heq)
  -- charged collision, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i v hchg _ _ _ hpush
    have hW : Devm.BalNoninc v v.withholdCreateGas.2 :=
      Devm.instructionFrame_refines_balNoninc
        (Devm.withholdCreateGas_instructionFrame v)
    have hI : Devm.BalNoninc v.withholdCreateGas.2
        (v.withholdCreateGas.2.incrNonce sevm.currentTarget) :=
      Devm.incrNonce_balance_effect _ sevm.currentTarget
    exact Devm.push_balance_gen hpush
      (balNoninc_refl_trans.2.2 hD
        (balNoninc_refl_trans.2.2
          (Devm.chargeStateGas_balNoninc_of_ok hchg)
          (balNoninc_refl_trans.2.2 hW hI)))
  -- charged collision, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i v hchg _ _ _ hpush
    have hW : Devm.BalNoninc v v.withholdCreateGas.2 :=
      Devm.instructionFrame_refines_balNoninc
        (Devm.withholdCreateGas_instructionFrame v)
    have hI : Devm.BalNoninc v.withholdCreateGas.2
        (v.withholdCreateGas.2.incrNonce sevm.currentTarget) :=
      Devm.incrNonce_balance_effect _ sevm.currentTarget
    exact Devm.push_balance_gen hpush
      (balNoninc_refl_trans.2.2 hD
        (balNoninc_refl_trans.2.2
          (Devm.chargeStateGas_balNoninc_of_ok hchg)
          (balNoninc_refl_trans.2.2 hW hI)))
  -- charged spawn
  · obtain ⟨r, hframe, rfl⟩ := run
    rename_i v hchg _
    have hW : Devm.BalNoninc v v.withholdCreateGas.2 :=
      Devm.instructionFrame_refines_balNoninc
        (Devm.withholdCreateGas_instructionFrame v)
    have hR : Devm.BalNoninc v.withholdCreateGas.2
        (v.withholdCreateGas.2.drainStateGasReservoir.2) :=
      Devm.instructionFrame_refines_balNoninc
        (Devm.drainStateGasReservoir_instructionFrame _)
    have hI : Devm.BalNoninc v.withholdCreateGas.2.drainStateGasReservoir.2
        (v.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce
          sevm.currentTarget) :=
      Devm.incrNonce_balance_effect _ sevm.currentTarget
    refine Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (balNoninc_refl_trans.2.2 hD
        (balNoninc_refl_trans.2.2
          (Devm.chargeStateGas_balNoninc_of_ok hchg)
          (balNoninc_refl_trans.2.2 hW
            (balNoninc_refl_trans.2.2 hR hI)))) ?_
    refine Resume.createAmsterdam_balance ?_
    have h := ProcessCreateMessage.balance_effect hxl hframe
    unfold MessageExecution.Rel at h
    rw [createMsgAmsterdam_benv_state] at h
    exact h
  -- uncharged collision, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i hpush
    exact Devm.push_balance_gen hpush
      (balNoninc_refl_trans.2.2 hD
        (balNoninc_refl_trans.2.2 hW2 hPc))
  -- uncharged collision, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i hpush
    exact Devm.push_balance_gen hpush
      (balNoninc_refl_trans.2.2 hD
        (balNoninc_refl_trans.2.2 hW2 hPc))
  -- uncharged spawn
  · obtain ⟨r, hframe, rfl⟩ := run
    refine Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (balNoninc_refl_trans.2.2 hD
        (balNoninc_refl_trans.2.2 hW2
          (balNoninc_refl_trans.2.2 hR2 hP2))) ?_
    refine Resume.createAmsterdam_balance ?_
    have h := ProcessCreateMessage.balance_effect hxl hframe
    unfold MessageExecution.Rel at h
    rw [createMsgAmsterdam_benv_state] at h
    exact h

lemma Xinst.balance_effectRec (x : Xinst) :
    Xinst.EffectRec Devm.BalNoninc x := by
  intro sevm pre xl out hxl run
  unfold Xinst.Run at run
  rcases Xinst.step_shape sevm pre x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ |
    ⟨d, st, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, st, g, r, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      nac, ib, hf, -, -, -, hs⟩ <;> rw [hs] at run
  -- the whole step stayed inside the instruction frame
  · obtain ⟨-, rfl⟩ := run
    exact Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc hframe
  -- dispatched to the CREATE family
  · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (Devm.instructionFrame_refines_balNoninc hf)
      (GenericCreate.balanceEffect hxl run)
  -- dispatched to the CALL family
  · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (Devm.instructionFrame_refines_balNoninc hf)
      (GenericCall.balanceEffect hxl run)
  -- dispatched to the Amsterdam CREATE family
  · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (Devm.instructionFrame_refines_balNoninc hf)
      (GenericCreateAmsterdam.balanceEffect hxl run)
  -- dispatched to the Amsterdam CALL family
  · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (Devm.instructionFrame_refines_balNoninc hf)
      (GenericCallAmsterdam.balanceEffect hxl run)

lemma Ninst.balance_effectRec (n : Ninst) :
    Ninst.EffectRec Devm.BalNoninc n := by
  cases n
  case reg r =>
    apply Ninst.effectRec_reg
    apply Rinst.balance_effect
  case exec x =>
    apply Ninst.effectRec_exec
    apply Xinst.balance_effectRec
  case push xs hxs =>
    apply Ninst.push_balance_effectRec
  case dupn imm =>
    apply Ninst.dupn_balance_effectRec
  case swapn imm =>
    apply Ninst.swapn_balance_effectRec
  case exchange imm =>
    apply Ninst.exchange_balance_effectRec

theorem Exec.balance_effect {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    Execution.Rel Devm.BalNoninc pre out :=
  Exec.effect balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2 Ninst.balance_effectRec Jinst.balance_effect Linst.balance_effect run

lemma Ninst.balance_effect (n : Ninst) : Ninst.Effect Devm.BalNoninc n := by
  apply Ninst.effect_of_effectRec balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2
  · exact Ninst.balance_effectRec
  · exact Jinst.balance_effect
  · exact Linst.balance_effect

theorem Func.balance_effect {fs : List Func} {sevm : Sevm}
    {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : Devm.BalNoninc pre post := by
  apply Func.effect (R := Devm.BalNoninc) (htrans := balNoninc_refl_trans.2.2) _ _ Ninst.balance_effect Linst.balance_effect run
  · intro xs pr po hpop
    apply Devm.balNoninc_of_state
    rw [hpop.state]
    exact balNoninc_refl_trans.1.1 _
  · intro pr po hburn
    apply Devm.balNoninc_of_state
    rw [hburn.state]
    exact balNoninc_refl_trans.1.1 _

/-! ## 6. Executable wrappers and the Solvent.lean endpoint -/

lemma Xlot.balance_rel_of_filled {xl : Xlot}
    (hfill : xl.Filled) :
    Xlot.Rel Devm.BalNoninc xl := by
  rcases xl with _ | ⟨evm, exn⟩
  · constructor
  · rcases hfill with ⟨exc⟩
    exact Exec.balance_effect exc

lemma processMessage_balance_noninc {msg : Msg} {post : Devm}
    (h : processMessage msg = .ok post) :
    State.BalNoninc msg.benv.state post.state := by
  obtain ⟨xl, hfill, hrun⟩ := of_processMessage msg (.ok post) h
  have heff := ProcessMessage.balance_effect (Xlot.balance_rel_of_filled hfill) hrun
  change State.BalNoninc msg.benv.state post.state at heff
  exact heff

lemma processCreateMessage_balance_noninc
    {msg : Msg} {post : Devm}
    (h : processCreateMessage msg = .ok post) :
    State.BalNoninc msg.benv.state post.state := by
  rcases of_processCreateMessage msg (.ok post) h with ⟨xl, hfill, hrun⟩
  have hxl : Xlot.Rel Devm.BalNoninc xl := Xlot.balance_rel_of_filled hfill
  have heff := ProcessCreateMessage.balance_effect hxl hrun
  exact heff

lemma setDelegationStep_bal_eq {auth : Auth} {msg msg' : Msg} {rc rc' : B256}
    (h : setDelegationStep auth msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  unfold setDelegationStep at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩; rfl
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩; rfl
      · cases h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩; rfl
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            show ((msg.benv.state.setCode _ _).incrNonce _).bal =
              msg.benv.state.bal
            rw [State.incrNonce_bal, State.setCode_bal]

lemma setDelegationLoop_bal_eq {auths : List Auth} {msg msg' : Msg}
    {rc rc' : B256}
    (h : setDelegationLoop auths msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  induction auths generalizing msg rc with
  | nil =>
    unfold setDelegationLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | cons auth auths ih =>
    unfold setDelegationLoop at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p h_step
      obtain ⟨msgS, rcS⟩ := p
      exact (ih h).trans (setDelegationStep_bal_eq h_step)

lemma setDelegation_balSum_eq {msg msg' : Msg} {refund : B256}
    (h : setDelegation msg = .ok ⟨msg', refund⟩) :
    State.balSum msg'.benv.state = State.balSum msg.benv.state := by
  unfold setDelegation at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p h_loop
    obtain ⟨msgL, rcL⟩ := p
    have h_bal := setDelegationLoop_bal_eq h_loop
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      unfold State.balSum
      rw [show ({ msgL with
        code := msgL.benv.state.getCode _ } : Msg).benv.state.bal =
          msgL.benv.state.bal from rfl, h_bal]

lemma setDelegationStep_benvStat {auth : Auth} {msg msg' : Msg} {rc rc' : B256}
    (h : setDelegationStep auth msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.stat = msg.benv.stat := by
  unfold setDelegationStep at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩; rfl
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩; rfl
      · cases h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩; rfl
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; rfl

lemma setDelegationLoop_benvStat {auths : List Auth} {msg msg' : Msg}
    {rc rc' : B256}
    (h : setDelegationLoop auths msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.stat = msg.benv.stat := by
  induction auths generalizing msg rc with
  | nil =>
    unfold setDelegationLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | cons auth auths ih =>
    unfold setDelegationLoop at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p h_step
      obtain ⟨msgS, rcS⟩ := p
      exact (ih h).trans (setDelegationStep_benvStat h_step)

lemma setDelegation_benvStat {msg msg' : Msg} {refund : B256}
    (h : setDelegation msg = .ok ⟨msg', refund⟩) :
    msg'.benv.stat = msg.benv.stat := by
  unfold setDelegation at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p h_loop
    obtain ⟨msgL, rcL⟩ := p
    have hst := setDelegationLoop_benvStat h_loop
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact hst

lemma processMessageCall.call_balance_noninc
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (hgas : msg.benv.stat.rules.stateGas = none)
    (h : processMessageCall.call msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.call at h
  simp only [hgas] at h
  rcases Except.bind_eq_ok h with ⟨⟨msgD, refund⟩, hauth, h⟩
  have hsum : State.balSum msgD.benv.state = State.balSum msg.benv.state := by
    unfold processMessageCall.legacyAuthorization at hauth
    split at hauth
    · cases hauth; rfl
    · rcases Except.bind_eq_ok hauth with ⟨⟨delegated, rc⟩, hd, hrest⟩
      cases hrest
      exact setDelegation_balSum_eq hd
  rcases Except.bind_eq_ok h with ⟨evm, hevm, h⟩
  have hbal := processMessage_balance_noninc (Except.bimap_id_eq_ok hevm)
  have hresolve : msgD.resolveCodeDelegation.benv = msgD.benv := by
    unfold Msg.resolveCodeDelegation
    split <;> rfl
  have hpre : State.BalNoninc msg.benv.state evm.state := by
    rw [hresolve] at hbal
    unfold State.BalNoninc at *
    omega
  split at h <;>
    (obtain ⟨rc, _, h⟩ := Except.bind_eq_ok h
     cases h
     exact hpre)

lemma processMessageCall.create_balance_noninc
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (hgas : msg.benv.stat.rules.stateGas = none)
    (h : processMessageCall.create msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.create at h
  simp only [hgas] at h
  split at h
  · -- Address collision: the pre-state is returned unchanged.
    cases h
    exact le_refl _
  · -- No collision: the created message determines the post-state.
    obtain ⟨evm, hevm, h⟩ := Except.bind_eq_ok h
    have hbal := processCreateMessage_balance_noninc (Except.bimap_id_eq_ok hevm)
    split at h <;>
      (obtain ⟨rc, _, h⟩ := Except.bind_eq_ok h
       cases h
       exact hbal)

lemma processMessageCall_balance_noninc
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (hgas : msg.benv.stat.rules.stateGas = none)
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall at h
  split at h
  · exact processMessageCall.create_balance_noninc hgas h
  · exact processMessageCall.call_balance_noninc hgas h

lemma processMessageCall_sum_le
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (hgas : msg.benv.stat.rules.stateGas = none)
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    sum post.bal ≤ sum msg.benv.state.bal := by
  exact processMessageCall_balance_noninc hgas h


/-! ## The shared ERC-20 proof layer

The lemma half of the hoist whose definition half is `Blanc/CommonCore.lean`'s
*The shared ERC-20 surface*. Every declaration below arrived here from
`Blanc/Solvent.lean` byte-identically in statement and proof: each one mentions
no contract-specific constant once the shared definitions moved up, so none was
ever WETH's, and `Blanc/Conserved.lean` -- which may not import a sibling
contract's module -- needs them as much as `Blanc/Solvent.lean` does.

Placement within the shared layer follows what each declaration mentions.
Anything stated in terms of `Increase`/`Decrease`/`Transfer` had to land in
`Blanc/Ladder.lean` instead, since that algebra is defined below this module:
`incrAt_of_incrWbal`, `of_transferFromUpdateSbal` and `transfer_of_transfer`
are there, immediately after `transfer_preserves_sum`. -/

/-! ### Address-shaped words -/

theorem validAdr_toB256 (a : Adr) : ValidAdr a.toB256 := ⟨a, rfl⟩

lemma toB256_toAdr {w : B256} :
    ValidAdr w → w.toAdr.toB256 = w := by
  intro h; rcases h with ⟨a, ha⟩;
  rw [← ha, toAdr_toB256]

lemma pref_cons {α} {x : α} {xs ys : List α}
    (h : xs <<+ ys) : (x :: xs) <<+ (x :: ys) := by
  rcases h with ⟨t, h⟩
  refine ⟨t, ?_⟩
  simp only [Split] at h ⊢
  rw [h]
  rfl

lemma cons_pref_cons_inv {α} {x : α} {xs ys : List α} (h : (x :: xs) <<+ (x :: ys)) : xs <<+ ys := by
  rcases h with ⟨zs, h⟩
  injection h with _ h_tail
  exact ⟨zs, h_tail⟩

/-! ### Line-walking tactics

`line_execute` and `line_execute_with` split a `Line.Run` goal at a chosen
instruction count and name the intermediate state. They lived in
`Blanc/Solvent.lean`, which put them out of reach of any second contract; their
whole supporting cast (`run_append_elim`, `findSubscript`, `Strings.intro`)
is in `Blanc/Tactics.lean`, upstream of here. -/

section

open Lean.Elab.Tactic
open Lean.Parser.Tactic
open Lean.Elab.Term
open Lean
open Qq

def Line.take : Nat → Q(Line) → TacticM Q(Line)
| 0, _ => pure q([] : Line)
| n + 1, l => do
  let l' : Q(Line) ← Lean.Meta.whnf l
  match l' with
  | ~q([]) => failure
  | ~q($i :: $is) =>
    let x ← Line.take n is
    pure q($i :: $x)
  | _ => failure

elab "line_execute" e:num : tactic =>
  withMainContext do
    let n := Lean.TSyntax.getNat e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s $l _ → $c) =>
      let ss ← findSubscript s
      let x ← Line.take n l
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]
    | _ => throwError "unexpected goal for line_execute"

elab "line_execute_with" e:term : tactic =>
  withMainContext do
    let x ← elabTermForApply e
    let g : Q(Prop) ← getMainTarget
    match g with
    | ~q(Line.Run _ $s _ _ → $c) =>
      let ss ← findSubscript s
      Lean.Expr.apply (Lean.mkApp2 q(@run_append_elim) c x)
      Strings.intro ["s" ++ ss, "h" ++ ss]
    | _ => throwError "unexpected goal for line_execute_with"

end

/-! ### The address mask, and what the two address guards yield -/

lemma B128.and_eq_and_prod_and (x y : B128) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

lemma B256.and_eq_and_prod_and (x y : B256) :
    x &&& y = ⟨x.1 &&& y.1, x.2 &&& y.2⟩ := rfl

/-! A bitwise `or` is zero only if both its operands are.

The fact every *composite* guard needs: a guard built as `or` of two clauses
passes exactly when both clauses pass, so the one flag the walk sees on the
stack yields both conjuncts.  `Blanc/Fmint.lean`'s `checkSlotCollides` is the
first such guard; `checkAddress`, being a single clause, never needed this. -/

theorem UInt64.of_or_eq_zero {x y : UInt64} (h : x ||| y = 0) : x = 0 ∧ y = 0 := by
  have hb := congrArg UInt64.toBitVec h
  rw [UInt64.toBitVec_or, UInt64.toBitVec_zero, BitVec.or_eq_zero_iff] at hb
  exact ⟨UInt64.toBitVec_inj.mp (by rw [hb.1]; rfl),
         UInt64.toBitVec_inj.mp (by rw [hb.2]; rfl)⟩

theorem B128.of_or_eq_zero {x y : B128} (h : x ||| y = 0) : x = 0 ∧ y = 0 := by
  have h1 : x.1 ||| y.1 = 0 := congrArg (fun z : B128 => z.1) h
  have h2 : x.2 ||| y.2 = 0 := congrArg (fun z : B128 => z.2) h
  exact ⟨Prod.ext (UInt64.of_or_eq_zero h1).1 (UInt64.of_or_eq_zero h2).1,
         Prod.ext (UInt64.of_or_eq_zero h1).2 (UInt64.of_or_eq_zero h2).2⟩

theorem B256.of_or_eq_zero {x y : B256} (h : x ||| y = 0) : x = 0 ∧ y = 0 := by
  have h1 : x.1 ||| y.1 = 0 := congrArg (fun z : B256 => z.1) h
  have h2 : x.2 ||| y.2 = 0 := congrArg (fun z : B256 => z.2) h
  exact ⟨Prod.ext (B128.of_or_eq_zero h1).1 (B128.of_or_eq_zero h2).1,
         Prod.ext (B128.of_or_eq_zero h1).2 (B128.of_or_eq_zero h2).2⟩

/-! A word and its complement sum to the all-ones value, with no carry at any
bit — so a bound of the form `y ≤ ~~~ x` is exactly a no-overflow guarantee
for `x + y`.  The fact a *complement-shaped* bound check needs: fmint's
`maxFlashLoan = not supply` is the first user, and the reason its
`amount ≤ maxFlashLoan` guard is the entire overflow argument for the mint. -/

lemma UInt64.toNat_add_not (x : UInt64) : x.toNat + (~~~x).toNat = 2 ^ 64 - 1 := by
  rw [UInt64.toNat_not]
  have h := UInt64.toNat_lt x
  simp only [UInt64.size] at *
  omega

/-- `B128.toNat`'s shift-or decomposition, as plain arithmetic: the low word
sits strictly below the shifted high word, so the `|||` is an `+`. -/
lemma B128.toNat_eq (x : B128) : x.toNat = x.1.toNat * 2 ^ 64 + x.2.toNat := by
  simp only [B128.toNat]
  rw [← Nat.add_eq_or (by rw [Nat.shiftLeft_eq]; exact Nat.dvd_mul_left _ _) (UInt64.toNat_lt _),
    Nat.shiftLeft_eq]

lemma B256.toNat_eq (x : B256) : x.toNat = x.1.toNat * 2 ^ 128 + x.2.toNat := by
  simp only [B256.toNat]
  rw [← Nat.add_eq_or (by rw [Nat.shiftLeft_eq]; exact Nat.dvd_mul_left _ _) B128.toNat_lt,
    Nat.shiftLeft_eq]

lemma B128.toNat_add_not (x : B128) : x.toNat + (~~~x).toNat = 2 ^ 128 - 1 := by
  have h1 := UInt64.toNat_add_not x.1
  have h2 := UInt64.toNat_add_not x.2
  have hc : (~~~x) = ⟨~~~x.1, ~~~x.2⟩ := rfl
  rw [B128.toNat_eq, B128.toNat_eq, hc]
  simp only []
  omega

lemma B256.toNat_add_not (x : B256) : x.toNat + (~~~x).toNat = 2 ^ 256 - 1 := by
  have h1 := B128.toNat_add_not x.1
  have h2 := B128.toNat_add_not x.2
  have hc : (~~~x) = ⟨~~~x.1, ~~~x.2⟩ := rfl
  rw [B256.toNat_eq, B256.toNat_eq, hc]
  simp only []
  omega

/-- A word whose complement is zero is the all-ones word — and the converse.

The fact a `[not, iszero]` pair yields: fmint's `isMax`, the infinite-allowance
test, is exactly that pair, so a walk that has read the flag learns whether the
allowance it loaded is `type(uint256).max`.  Proved from `toNat_add_not` rather
than by cases on the four `UInt64` limbs. -/
lemma B256.eq_max_of_not_eq_zero {x : B256} (h : ~~~ x = 0) : x = B256.max := by
  have h1 := B256.toNat_add_not x
  rw [h, show (0 : B256).toNat = 0 from rfl] at h1
  have h2 : x.toNat = B256.max.toNat := by
    rw [show B256.max.toNat = 2 ^ 256 - 1 from rfl]
    omega
  rw [← toB256_toNat x, h2, toB256_toNat]

lemma B256.not_max : (~~~ (B256.max : B256)) = 0 := rfl

/-- Every word is at most `B256.max`.  Small, but it is what makes "the
allowance is below the amount" already say "the allowance is not the infinite
one": the two arms of an `isMax` allowance test cannot both be escaped. -/
lemma B256.le_max (x : B256) : x ≤ B256.max := by
  rcases B256.le_or_gt x B256.max with h | h
  · exact h
  · exfalso
    have h1 := B256.toNat_lt_toNat h
    have h2 := B256.toNat_lt x
    rw [show (B256.max : B256).toNat = 2 ^ 256 - 1 from rfl] at h1
    omega

/-- The whole overflow argument for a complement-bounded add: `y ≤ ~~~ x` says
exactly that `x + y` does not overflow. -/
lemma B256.nof_of_le_not {x y : B256} (h : y ≤ ~~~ x) : B256.Nof x y := by
  have h1 := B256.toNat_add_not x
  have h2 := B256.toNat_le_toNat h
  unfold B256.Nof
  omega

/-- The converse of `B256.nof_of_le_not`: a non-overflowing add is exactly one
whose second operand is within the complement of the first.  Together the two
say that "`x + y` does not overflow" and "`y ≤ 2 ^ 256 - 1 - x`" are the same
statement — which is what lets a contract's `amount ≤ maxFlashLoan` guard be
read off a `B256.Nof` fact and vice versa. -/
lemma B256.le_not_of_nof {x y : B256} (h : B256.Nof x y) : y ≤ ~~~ x := by
  rcases B256.le_or_gt y (~~~ x) with h' | h'
  · exact h'
  · exfalso
    have h1 := B256.toNat_lt_toNat h'
    have h2 := B256.toNat_add_not x
    unfold B256.Nof at h
    omega

lemma B128.zero_and {x : B128} : 0 &&& x = 0 := by
  simp only [and_eq_and_prod_and]
  apply Prod.ext <;> change (0 : UInt64) &&& _ = 0 <;> apply UInt64.zero_and

lemma UInt64.mask_and_eq_zero (x : UInt32) :
    (0xffffffff00000000 : UInt64) &&& x.toUInt64 = 0 := by
  rw [← @UInt32.and_neg_one x, UInt32.toUInt64_and]
  rw [UInt64.and_comm (UInt32.toUInt64 _), ← UInt64.and_assoc]
  apply UInt64.zero_and

lemma UInt64.toUInt32_toUInt64_eq_of_highMask_and_eq_zero {x : UInt64}
    (h : (0xffffffff00000000 : UInt64) &&& x = 0) :
    x.toUInt32.toUInt64 = x := by
  apply UInt64.toBitVec_inj.mp
  simp only [UInt32.toBitVec_toUInt64, UInt64.toBitVec_toUInt32]
  apply BitVec.eq_of_getElem_eq_iff.mpr
  intro i hi
  rw [BitVec.getElem_setWidth]
  by_cases hi32 : i < 32
  · rw [BitVec.getLsbD_eq_getElem hi32, BitVec.getElem_setWidth,
      BitVec.getLsbD_eq_getElem (by omega)]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    have hb := congrArg UInt64.toBitVec h
    rw [UInt64.toBitVec_and, UInt64.toBitVec_zero] at hb
    have hb_i := congrArg (fun v : BitVec 64 => v[i]) hb
    simp only [BitVec.getElem_and hi, BitVec.getElem_zero hi] at hb_i
    have hmask : ((0xffffffff00000000 : UInt64).toBitVec)[i] = true := by
      change (((-1 : UInt64) <<< 32).toBitVec)[i] = true
      rw [UInt64.toBitVec_shiftLeft, BitVec.getElem_shiftLeft' hi]
      simp only [UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceMod, BitVec.toNat_ofNat,
        reducePow, reduceMod, hi32, decide_false, Bool.not_false, UInt64.toBitVec_neg,
        BitVec.reduceNeg, Bool.true_and]
      change (BitVec.allOnes 64)[i - 32] = true
      rw [BitVec.getElem_eq_testBit_toNat _ _ (by omega), BitVec.toNat_allOnes]
      rw [Nat.testBit_two_pow_sub_succ (x := 0) (by norm_num only)]
      have hi64 : i - 32 < 64 := by omega
      simp only [hi64, decide_true, zero_testBit, Bool.not_false, Bool.and_self]
    rw [hmask] at hb_i
    exact hb_i.symm

lemma validAdr_iff {w : B256} :
    ValidAdr w ↔ addressMask &&& w = 0 := by
  constructor <;> intro h
  · rcases h with ⟨⟨a32, a128⟩, ⟨_⟩⟩
    change (B128.and (UInt64.max, 0xffffffff00000000) (0, a32.toUInt64),
      B128.and 0 a128) = (0 : B256)
    have h_high : B128.and (UInt64.max, 0xffffffff00000000) (0, a32.toUInt64) = 0 := by
      change (UInt64.max &&& 0, (0xffffffff00000000 : UInt64) &&& a32.toUInt64) = (0, 0)
      simp only [UInt64.and_zero, UInt64.mask_and_eq_zero]
    have h_low : B128.and 0 a128 = 0 := by exact B128.zero_and
    rw [h_high, h_low]
    change ((0 : B128), (0 : B128)) = ((0 : B128), (0 : B128))
    rfl
  · refine' ⟨w.toAdr, _⟩
    rcases w with ⟨⟨wz, wh⟩, wl⟩
    simp only [addressMask] at h
    have hz := congrArg (fun x : B256 => x.1.1) h
    have hm := congrArg (fun x : B256 => x.1.2) h
    change UInt64.max &&& wz = 0 at hz
    change (0xffffffff00000000 : UInt64) &&& wh = 0 at hm
    have h_wz : wz = 0 := by
      simp only [UInt64.max] at hz
      change (-1 : UInt64) &&& wz = 0 at hz
      simpa only [UInt64.neg_one_and] using hz
    have h_wh : wh.toUInt32.toUInt64 = wh := by
      exact UInt64.toUInt32_toUInt64_eq_of_highMask_and_eq_zero hm
    simp only [B256.toAdr, Adr.toB256, h_wz, h_wh]
    rfl

lemma addressMask_eq_shl :
    addressMask = (~~~ (0 : B256)) <<< (160 : Nat).toB256.toNat := by
  rw [B256.toNat_toB256, Nat.lo_eq_of_lt (by omega)]; rfl

lemma of_push_addressMask {e : Sevm} {s s' : Devm} {xs}
    (h_pfx : xs <<+ s.stack) (h_run : Line.Run e s pushAddressMask s') :
    (addressMask :: xs <<+ s'.stack) := by
  rw [addressMask_eq_shl]
  revert s; simp only [pushAddressMask]; line_prefix

lemma of_check_non_address {e : Sevm} {s s' : Devm} {x xs}
    (h_pfx : x :: xs <<+ s.stack) (h_run : Line.Run e s checkNonAddress s') :
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ValidAdr x) := by
  rename' s' => s''
  rcases of_run_append _ h_run with ⟨sm, h_push, h_and⟩; clear h_run
  have h_pfx' := of_push_addressMask h_pfx h_push; clear h_pfx h_push s
  have h_pfx2 : (addressMask &&& x) :: xs <<+ s''.stack := by
    revert h_and; revert sm; line_prefix
  refine ⟨_, h_pfx2, Iff.symm validAdr_iff⟩

/-- `arg k ++ checkNonAddress`, the composite an address-shaped argument guard
tests: the masked word is zero exactly when the argument's head word is
address-shaped.  Contract-neutral, so it lives here rather than in the first
family that needed it. -/
theorem prefix_of_argCheckNonAddress {e : Sevm} {s s' : Devm} {k : B256}
    {xs : Stack} (hp : xs <<+ s.stack)
    (run : Line.Run e s (arg k ++ checkNonAddress) s') :
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ValidAdr (Sevm.argWord e k)) := by
  rcases of_run_append (arg k) run with ⟨_mid, r1, r2⟩
  exact of_check_non_address (prefix_of_arg hp r1) r2

lemma of_check_address {e : Sevm} {s s' : Devm} {x xs} :
    (x :: xs <<+ s.stack) →
    Line.Run e s checkAddress s' →
    ∃ y, (y :: xs <<+ s'.stack) ∧ (y = 0 ↔ ¬ ValidAdr x) := by
  rename' s' => s''; intros h_pfx h_run
  rcases of_run_append _ h_run with ⟨sm, hs', h_run'⟩; clear h_run
  rcases of_check_non_address h_pfx hs' with ⟨y, h_pfx', h_iff⟩; clear h_pfx hs' s
  have h_pfx2 : ((y =? 0) :: xs <<+ s''.stack) := by
    revert h_run'; revert sm; line_prefix
  refine' ⟨_, h_pfx2, _⟩; rw [← h_iff]
  apply Ne.ite_eq_right_iff <| Ne.symm B256.zero_ne_one

/-! ### `sstore`'s effect on storage -/

/-- Replacing the machine component before an accessed-storage-key update is
irrelevant once the caller supplies the final machine component. -/
theorem Devm.addAccessedStorageKey_setMach_setMach
    {base : Devm} {target : Adr} {key : B256} {mach mach' : Mach} :
    (addAccessedStorageKey (base.setMach mach) target key).setMach mach' =
      (addAccessedStorageKey base target key).setMach mach' := rfl

/-- Persistent storage read-after-write at the same address and key. -/
theorem Devm.getStorVal_setStorVal_self
    (devm : Devm) (adr : Adr) (key val : B256) :
    (devm.setStorVal adr key val).getStorVal adr key = val := by
  show (Devm.getStor (devm.setStorVal adr key val) adr).get key = val
  rw [setStorVal_getStor_self, Stor.get_set_self]

/-! ### Reusable projection cuts for compiled RETURN and SSTORE posts -/

/-- A `setMach`/`memRead`/`withOutput` return post preserves the base world. -/
lemma Devm.returnPost_world (devm : Devm) (stack : List B256)
    (gas index size : Nat) (output : Bytes) :
    ((((devm.setMach ⟨stack, devm.memory, gas, devm.stateGas⟩).memRead index size).2
        ).withOutput output).world = devm.world := rfl

/-- A `setMach`/`memRead`/`withOutput` return post preserves persistent
storage reads. -/
lemma Devm.returnPost_getStorVal (devm : Devm) (stack : List B256)
    (gas index size : Nat) (output : Bytes) (adr : Adr) (key : B256) :
    Devm.getStorVal
        ((((devm.setMach ⟨stack, devm.memory, gas, devm.stateGas⟩).memRead index size).2
          ).withOutput output) adr key =
      devm.getStorVal adr key := by
  unfold Devm.getStorVal Devm.getAcct
  rw [show (((((devm.setMach ⟨stack, devm.memory, gas, devm.stateGas⟩).memRead index size).2
      ).withOutput output).state) = devm.state from
        congrArg World.state
          (Devm.returnPost_world devm stack gas index size output)]

/-- A `setMach`/`memRead`/`withOutput` return post preserves transient
storage. -/
lemma Devm.returnPost_transientStorage (devm : Devm) (stack : List B256)
    (gas index size : Nat) (output : Bytes) :
    ((((devm.setMach ⟨stack, devm.memory, gas, devm.stateGas⟩).memRead index size).2
        ).withOutput output).transientStorage = devm.transientStorage :=
  congrArg World.transientStorage
    (Devm.returnPost_world devm stack gas index size output)

/-- A `setMach`/`memRead`/`withOutput` return post preserves the warmed
storage-key set. -/
lemma Devm.returnPost_accessedStorageKeys (devm : Devm) (stack : List B256)
    (gas index size : Nat) (output : Bytes) :
    ((((devm.setMach ⟨stack, devm.memory, gas, devm.stateGas⟩).memRead index size).2
        ).withOutput output).accessedStorageKeys =
      devm.accessedStorageKeys := by
  rfl

/-- The standard warm/refund/storage-write post has exactly the written
persistent state. -/
lemma Devm.sstoreBase_state (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).state =
        devm.state.setStorVal target key value := rfl

/-- The standard warm/refund/storage-write post preserves the prior error. -/
lemma Devm.sstoreBase_error (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).error = devm.error := rfl

/-- The standard warm/refund/storage-write post preserves transient storage. -/
lemma Devm.sstoreBase_transientStorage
    (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).transientStorage =
        devm.transientStorage := rfl

/-- The standard warm/refund/storage-write post preserves logs. -/
lemma Devm.sstoreBase_logs (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).logs = devm.logs := rfl

/-- The standard warm/refund/storage-write post records exactly the written
storage key in the warmed-key set. -/
lemma Devm.sstoreBase_accessedStorageKeys
    (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    (((addAccessedStorageKey devm target key).withRefundCounter refund
      ).setStorVal target key value).accessedStorageKeys =
        devm.accessedStorageKeys.insert (target, key) := by
  rfl

/-- A warm SSTORE skips the insertion step and therefore preserves the
already-warmed storage-key set across its refund and persistent write. -/
lemma Devm.sstoreWarmBase_accessedStorageKeys
    (devm : Devm) (target : Adr) (key : B256)
    (refund : Int) (value : B256) :
    ((devm.withRefundCounter refund).setStorVal target key value
      ).accessedStorageKeys = devm.accessedStorageKeys := by
  rfl

lemma sstore_getStor_setStorVal {sevm : Sevm} {s s' : Devm} {x xs}
    (h_run : Ninst.Run sevm s Blanc.Ninst.sstore s') (hx : x :: xs <<+ s.stack) :
    ∃ v, Devm.getStor s' sevm.currentTarget = (Devm.getStor s sevm.currentTarget).set x v := by
  rcases of_run_reg h_run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  cases hsg : sevm.benvStat.rules.stateGas
  · -- Legacy gas lane: the regime-selected eight-bind walk.
    simp only [hsg] at run
    split at run
    all_goals
      rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
      rcases Except.bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
      rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
      rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
      rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
      rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
      rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
      rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
      have hkx : x = key :=
        (List.of_cons_pref_of_cons_pref hx (pref_of_split (Devm.pop_of_pop h1).stack)).left
      have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
      have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
      have e4 : Devm.getStor s₂ = Devm.getStor s₃ := by
        repeat' split at h4
        all_goals injection h4 with eq; injection eq with eq _; subst eq; rfl
      have e6 : Devm.getStor s₃ = Devm.getStor s₄ := by
        injection h6 with eq; rw [← eq]; rfl
      have e7 : Devm.getStor s₄ = Devm.getStor s₅ := chargeGas_getStor_eq h7
      have E : Devm.getStor s = Devm.getStor s₅ := e1.trans (e2.trans (e4.trans (e6.trans e7)))
      have E' : Devm.getStor s =
            Devm.getStor (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget s₅) :=
        E.trans rfl
      injection h9 with eq
      refine ⟨val, ?_⟩
      rw [← eq, setStorVal_getStor_self, hkx, E']
  · -- Amsterdam: static check first, state-gas second dimension.
    simp only [hsg] at run
    rcases Except.bind_eq_ok run with ⟨_, h0, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨⟨key, s₁⟩, h1, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨⟨val, s₂⟩, h2, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨_, h3, run₄⟩
    rcases Except.bind_eq_ok run₄ with ⟨s₃, hchg, run₅⟩
    rcases Except.bind_eq_ok run₅ with ⟨s₄, hstg, h9⟩
    have hkx : x = key :=
      (List.of_cons_pref_of_cons_pref hx (pref_of_split (Devm.pop_of_pop h1).stack)).left
    have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
    have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
    have echg : Devm.getStor s₂ = Devm.getStor s₃ := by
      have e1' := chargeGas_getStor_eq hchg
      have e2' : Devm.getStor s₂ = Devm.getStor s₃ := by
        rw [← e1']
        simp only [Devm.creditStateGasRefund, Mach.creditStateGasRefund,
          Devm.withRefundCounter, Devm.balReadStorage]
        try split <;> (try split) <;> rfl
      exact e2'
    have estg : Devm.getStor s₃ = Devm.getStor s₄ :=
      Devm.chargeStateGas_getStor hstg
    have E : Devm.getStor s = Devm.getStor s₄ := e1.trans (e2.trans (echg.trans estg))
    have E' : Devm.getStor s =
        Devm.getStor (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget s₄) :=
      E.trans rfl
    injection h9 with eq
    refine ⟨val, ?_⟩
    rw [← eq, setStorVal_getStor_self, hkx, E']

lemma sstore_preserves_stor_rest {x xs} {sevm : Sevm} {s s' : Devm} :
  ¬ ValidAdr x →
  (x :: xs <<+ s.stack) →
  Ninst.Run sevm s Blanc.Ninst.sstore s' →
  (Stor.rest (Devm.getStor s sevm.currentTarget)) = (Stor.rest (Devm.getStor s' sevm.currentTarget)) := by
  intro h_nv h_pfx h_run
  rcases sstore_getStor_setStorVal h_run h_pfx with ⟨v, h_set⟩
  rw [h_set]
  funext a
  have hne : a.toB256 ≠ x := fun hc => h_nv ⟨a, hc⟩
  simp only [Stor.rest, Function.comp_apply]
  rw [Stor.get_set_ne _ hne.symm]

lemma sstore_getStor_set {sevm : Sevm} {s s' : Devm} {x y xs}
    (h_run : Ninst.Run sevm s Blanc.Ninst.sstore s') (hx : x :: y :: xs <<+ s.stack) :
    Devm.getStor s' sevm.currentTarget = (Devm.getStor s sevm.currentTarget).set x y := by
  rcases of_run_reg h_run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  cases hsg : sevm.benvStat.rules.stateGas
  · -- Legacy gas lane: the regime-selected eight-bind walk.
    simp only [hsg] at run
    split at run
    all_goals
      rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
      rcases Except.bind_eq_ok run₁ with ⟨⟨val, s₂⟩, h2, run₂⟩
      rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
      rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
      rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
      rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
      rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
      rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
      have hs : s.stack = key :: s₁.stack := (Devm.pop_of_pop h1).stack
      have hs2 : s₁.stack = val :: s₂.stack := (Devm.pop_of_pop h2).stack
      have hxy : x = key ∧ y = val := by
        rw [hs, hs2] at hx
        rcases hx with ⟨sfx, heq⟩
        injection heq with hk hrest
        injection hrest with hv _
        exact ⟨hk.symm, hv.symm⟩
      have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
      have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
      have e4 : Devm.getStor s₂ = Devm.getStor s₃ := by
        repeat' split at h4
        all_goals injection h4 with eq; injection eq with eq _; subst eq; rfl
      have e6 : Devm.getStor s₃ = Devm.getStor s₄ := by
        injection h6 with eq; rw [← eq]; rfl
      have e7 : Devm.getStor s₄ = Devm.getStor s₅ := chargeGas_getStor_eq h7
      have E : Devm.getStor s = Devm.getStor s₅ := e1.trans (e2.trans (e4.trans (e6.trans e7)))
      have E' : Devm.getStor s =
            Devm.getStor (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget s₅) :=
        E.trans rfl
      have eq := Except.ok.inj h9
      rw [← eq, setStorVal_getStor_self, hxy.left, hxy.right, E']
  · -- Amsterdam: static check first, state-gas second dimension.
    simp only [hsg] at run
    rcases Except.bind_eq_ok run with ⟨_, h0, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨⟨key, s₁⟩, h1, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨⟨val, s₂⟩, h2, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨_, h3, run₄⟩
    rcases Except.bind_eq_ok run₄ with ⟨s₃, hchg, run₅⟩
    rcases Except.bind_eq_ok run₅ with ⟨s₄, hstg, h9⟩
    have hs : s.stack = key :: s₁.stack := (Devm.pop_of_pop h1).stack
    have hs2 : s₁.stack = val :: s₂.stack := (Devm.pop_of_pop h2).stack
    have hxy : x = key ∧ y = val := by
      rw [hs, hs2] at hx
      rcases hx with ⟨sfx, heq⟩
      injection heq with hk hrest
      injection hrest with hv _
      exact ⟨hk.symm, hv.symm⟩
    have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
    have e2 : Devm.getStor s₁ = Devm.getStor s₂ := Devm.pop_getStor_eq h2
    have echg : Devm.getStor s₂ = Devm.getStor s₃ := by
      have e1' := chargeGas_getStor_eq hchg
      rw [← e1']
      simp only [Devm.creditStateGasRefund, Mach.creditStateGasRefund,
        Devm.withRefundCounter, Devm.balReadStorage]
      try split <;> (try split) <;> rfl
    have estg : Devm.getStor s₃ = Devm.getStor s₄ :=
      Devm.chargeStateGas_getStor hstg
    have E : Devm.getStor s = Devm.getStor s₄ := e1.trans (e2.trans (echg.trans estg))
    have E' : Devm.getStor s =
        Devm.getStor (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget s₄) :=
      E.trans rfl
    have eq := Except.ok.inj h9
    rw [← eq, setStorVal_getStor_self, hxy.left, hxy.right, E']

syntax "invariance" : tactic
macro_rules
| `(tactic| invariance) =>
  `(tactic| first | apply Line.of_inv _ _ (by assumption); line_inv
                  | apply Func.of_inv _ _ _ (by assumption); func_inv)

lemma of_run_next {fs sevm devm i f devm''}
    (h : Func.Run fs sevm devm (Func.next i f) devm'') :
    ∃ devm', Ninst.Run sevm devm i devm' ∧ Func.Run fs sevm devm' f devm'' := by
  cases h with
  | next h1 h2 => exact ⟨_, h1, h2⟩

/-- Inversion for `Func.call`, as a lemma rather than a `cases` at the use
site: `cases` on `Func.Run` inside a long walk's context generalizes the whole
context against the indices and can diverge in `whnf`, whereas `rcases` on
this existential is cheap. -/
lemma of_run_call {fs : List Func} {sevm : Sevm} {s r : Devm} {k : Nat}
    (h : Func.Run fs sevm s (.call k) r) :
    ∃ f s', fs[k]? = some f ∧ Devm.Burn s s' ∧ Func.Run fs sevm s' f r := by
  cases h with
  | call h_get h_burn h_run => exact ⟨_, _, h_get, h_burn, h_run⟩

/-- A successful conditional whose selected arm calls a known nonreturning
function must take the zero/fall-through arm. -/
theorem of_run_branch_call_of_not_run
    {fs : List Func} {sevm : Sevm} {s r : Devm} {k : Nat}
    {blocked next : Func}
    (hget : fs[k]? = some blocked)
    (blocked_not_run : ∀ {pre post : Devm},
      ¬ Func.Run fs sevm pre blocked post)
    (run : Func.Run fs sevm s ((.call k) <?> next) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run fs sevm s' next r := by
  rcases of_run_branch run with
    ⟨s', hpop, hnext⟩ |
    ⟨w, s', s'', hnz, hpop, hburn, hcall⟩
  · exact ⟨s', hpop, hnext⟩
  · rcases of_run_call hcall with
      ⟨f, callPre, hlookup, hcallBurn, hbody⟩
    have hf : f = blocked := by
      rw [hget] at hlookup
      exact Option.some.inj hlookup.symm
    subst f
    exact (blocked_not_run hbody).elim

/-- Successful fall-through past an auxiliary that is exactly `Func.revert`. -/
theorem of_run_branch_call_revert
    {fs : List Func} {sevm : Sevm} {s r : Devm} {k : Nat} {next : Func}
    (hget : fs[k]? = some Func.revert)
    (run : Func.Run fs sevm s ((.call k) <?> next) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run fs sevm s' next r := by
  exact of_run_branch_call_of_not_run hget
    (fun hbody => not_run_revert hbody) run

/-! ### `transfer`'s fragments -/

lemma of_transferTestDst {sevm : Sevm} {s s' : Devm} :
    Line.Run sevm s transferTestDst s' →
    ∃ na_dst dst,
      ([na_dst, dst] <<+ s'.stack) ∧
      (na_dst = 0 ↔ ValidAdr dst) := by
  simp only [transferTestDst]
  line_execute_with (arg 0)
  rcases prefix_of_cdl nil_pref h₁ with ⟨dst, hp₁⟩
  clear h₁
  line_execute 1
  have hp₂ : [dst, dst] <<+ s₂.stack := by generalize_line_prefix
  clear hp₁ h₂
  intro h
  rcases of_check_non_address hp₂ h with ⟨na_dst, h_pfx, h_iff⟩
  exact ⟨_, _, h_pfx, h_iff⟩

lemma of_transferTestLt {sevm : Sevm} {s s' : Devm} {dst}
    (h_stk : [dst] <<+ s.stack) :
    Line.Run sevm s transferTestLt s' →
    ∃ lt? caller wad,
      ([lt?, caller, Devm.getStorVal s' sevm.currentTarget caller - wad, wad, dst] <<+ s'.stack) ∧
      (lt? = 0 ↔ wad ≤ Devm.getStorVal s' sevm.currentTarget caller) ∧
      ValidAdr caller := by
  simp only [transferTestLt]
  -- arg 1 : push wad
  line_execute_with (arg 1)
  rcases prefix_of_cdl h_stk h₁ with ⟨wad, hp₁⟩
  clear h₁
  -- caller, dup 0 : [caller, caller, wad, dst]
  line_execute 2
  have hp₂ : [sevm.caller.toB256, sevm.caller.toB256, wad, dst] <<+ s₂.stack := by generalize_line_prefix
  clear h₂
  -- sload : [cbal, caller, wad, dst]
  line_execute 1
  rcases prefix_of_sload (of_run_singleton h₃) hp₂ with ⟨cbal, hp₃, h_cbal⟩
  have hstor23 : Devm.getStor s₂ = Devm.getStor s₃ := Line.of_inv Devm.getStor (by line_inv) h₃
  clear h₃
  -- swap 0, dup 2, dup 0, dup 3, sub, swap 2, lt :
  --   [cbal <? wad, caller, cbal - wad, wad, dst]
  intro h₄
  have hp₄ : [cbal <? wad, sevm.caller.toB256, cbal - wad, wad, dst] <<+ s'.stack := by generalize_line_prefix
  have hstor34 : Devm.getStor s₃ = Devm.getStor s' := Line.of_inv Devm.getStor (by line_inv) h₄
  have h_cbal' : cbal = Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 := by
    rw [h_cbal]
    show (Devm.getStor s₂ _).get _ = (Devm.getStor s' _).get _
    rw [hstor23, hstor34]
  refine ⟨cbal <? wad, sevm.caller.toB256, wad, ?_, ?_, validAdr_toB256 sevm.caller⟩
  · rw [← h_cbal']; exact hp₄
  · rw [← h_cbal', B256.ltCheck, Ne.ite_eq_right_iff B256.zero_ne_one.symm, B256.not_lt]

/-! ### Balance sums do not overflow across a run -/


lemma Exec.preserves_nof {pc : Nat} {sevm : Sevm} {devm : Devm} {exn : Execution}
    (run : Exec pc sevm devm exn) :
    ∀ r : Devm, exn = .ok r →
      sum devm.getBal < 2 ^ 256 → sum r.getBal < 2 ^ 256 := by
  intro r h_eq h_nof
  subst h_eq
  exact Nat.lt_of_le_of_lt (Exec.balance_effect run) h_nof

lemma Xinst.preserves_nof {sevm : Sevm} {s r : Devm} {x : Xinst} {xl : Xlot}
    (h : Xinst.Run sevm s x xl (.ok r)) (h_nof : sum s.getBal < 2 ^ 256)
    (h_fill : xl.Filled) :
    sum r.getBal < 2 ^ 256 := by
  have hxl : Xlot.Rel Devm.BalNoninc xl :=
    Xlot.rel_of_filled balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2
      Ninst.balance_effectRec Jinst.balance_effect Linst.balance_effect h_fill
  exact Nat.lt_of_le_of_lt (Xinst.balance_effectRec x hxl h) h_nof

lemma Ninst.preserves_nof {sevm : Sevm} {s r : Devm} {i : Ninst}
    (h : Ninst.Run sevm s i r) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Ninst.balance_effect i h) h_nof

lemma Func.preserves_nof {c : List Func} {sevm : Sevm} {s r : Devm} {f : Func}
    (run : Func.Run c sevm s f r) (h_nof : sum s.getBal < 2 ^ 256) :
    sum r.getBal < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Func.balance_effect run) h_nof

end Blanc
