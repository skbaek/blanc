-- Fork-independent actor accounting for PRORATA attack traces.

import Blanc.ProrataAttackModel

namespace Blanc

namespace Prorata

/-- Whether a non-victim economic flow is charged to the designated coalition
or to the diagnostic open context. -/
inductive AttackAttribution where
  | coalition
  | outside
deriving DecidableEq

namespace AttackAttribution

def coalitionAmount (attribution : AttackAttribution) (amount : Nat) : Nat :=
  match attribution with
  | .coalition => amount
  | .outside => 0

def outsideAmount (attribution : AttackAttribution) (amount : Nat) : Nat :=
  match attribution with
  | .coalition => 0
  | .outside => amount

end AttackAttribution

/-- The unique victim deposit, retaining its pre-credit snapshot and the P2
backing fact needed only by the later full-exit bridge. -/
structure VictimDeposit (o : Nat) where
  pre : AccountingSnapshot
  amount : Nat
  minted : Nat
  minted_eq : minted = mintN o amount pre.supply pre.balance
  backed : pre.supply ≤ o * pre.balance

namespace VictimDeposit

def post {o : Nat} (deposit : VictimDeposit o) : AccountingSnapshot :=
  ⟨deposit.pre.supply + deposit.minted,
    deposit.pre.balance + deposit.amount⟩

end VictimDeposit

/-- The optional exact full exit associated with the unique victim deposit. -/
structure VictimExit (o : Nat) (deposit : VictimDeposit o) where
  pre : AccountingSnapshot
  payout : Nat
  payout_eq : payout = payN o deposit.minted pre.supply pre.balance

/-- Chronology of the unique victim action pair.  `exited` is terminal because
no transition below can introduce another victim action from it. -/
inductive VictimPhase (o : Nat) where
  | before
  | open (deposit : VictimDeposit o)
  | exited (deposit : VictimDeposit o) (exit : VictimExit o deposit)

namespace VictimPhase

def input {o : Nat} : VictimPhase o → Nat
  | .before => 0
  | .open deposit | .exited deposit _ => deposit.amount

def output {o : Nat} : VictimPhase o → Nat
  | .before | .open _ => 0
  | .exited _ exit => exit.payout

def hasDeposit {o : Nat} : VictimPhase o → Prop
  | .before => False
  | .open _ | .exited _ _ => True

end VictimPhase

/-- The total actor overlay at one committed PRORATA boundary.  All
non-victim shares are aggregated, while their cash flows are partitioned into
the coalition and the diagnostic outside context. -/
structure ProrataAttackState (o : Nat) where
  accounting : AccountingSnapshot
  nonVictimShares : Nat
  victimShares : Nat
  inA : Nat
  outA : Nat
  outsideSubsidy : Nat
  outsideOut : Nat
  phase : VictimPhase o

namespace ProrataAttackState

def totalIn {o : Nat} (state : ProrataAttackState o) : Nat :=
  state.inA + state.outsideSubsidy

def totalOut {o : Nat} (state : ProrataAttackState o) : Nat :=
  state.outA + state.outsideOut

def nonVictimClaim {o : Nat} (state : ProrataAttackState o) : Nat :=
  claimN o state.nonVictimShares state.accounting.supply
    state.accounting.balance

def SharesPartition {o : Nat} (state : ProrataAttackState o) : Prop :=
  state.nonVictimShares + state.victimShares = state.accounting.supply

/-- Exact settled ETH conservation.  This is proved from the path rather than
accepted as a field of the carrier. -/
def FlowExact {o : Nat} (state : ProrataAttackState o) : Prop :=
  state.accounting.balance + state.totalOut + state.phase.output =
    state.totalIn + state.phase.input

/-- The stronger open-context invariant from which both P4 payout headlines
follow by dropping nonnegative terms. -/
def ClaimBound {o : Nat} (state : ProrataAttackState o) : Prop :=
  state.totalOut + state.nonVictimClaim ≤ state.totalIn

/-- Victim-ledger and price chronology facts retained by a reachable path. -/
def VictimConsistent {o : Nat} (state : ProrataAttackState o) : Prop :=
  match state.phase with
  | .before => state.victimShares = 0
  | .open deposit =>
      state.victimShares = deposit.minted ∧
        PriceLe o deposit.post state.accounting
  | .exited deposit exit =>
      state.victimShares = 0 ∧
        PriceLe o deposit.post exit.pre

def Invariant {o : Nat} (state : ProrataAttackState o) : Prop :=
  state.SharesPartition ∧ state.FlowExact ∧
    state.VictimConsistent ∧ state.ClaimBound

def genesis (o : Nat) : ProrataAttackState o where
  accounting := ⟨0, 0⟩
  nonVictimShares := 0
  victimShares := 0
  inA := 0
  outA := 0
  outsideSubsidy := 0
  outsideOut := 0
  phase := .before

theorem genesis_invariant (o : Nat) : (genesis o).Invariant := by
  simp [Invariant, SharesPartition, FlowExact, VictimConsistent, ClaimBound,
    genesis, totalIn, totalOut, nonVictimClaim, VictimPhase.input,
    VictimPhase.output, claimN, payN]

theorem victimConsistent_of_priceLe {o : Nat} (ho : o ≠ 0)
    {pre post : ProrataAttackState o}
    (hshares : post.victimShares = pre.victimShares)
    (hphase : post.phase = pre.phase)
    (hprice : PriceLe o pre.accounting post.accounting)
    (hpre : pre.VictimConsistent) : post.VictimConsistent := by
  unfold VictimConsistent at hpre ⊢
  rw [hphase]
  cases hp : pre.phase with
  | before =>
      simp only [hp] at hpre
      change post.victimShares = 0
      omega
  | «open» deposit =>
      simp only [hp] at hpre
      change post.victimShares = deposit.minted ∧
        PriceLe o deposit.post post.accounting
      exact ⟨by omega, PriceLe.trans ho hpre.2 hprice⟩
  | exited deposit exit =>
      simp only [hp] at hpre
      change post.victimShares = 0 ∧ PriceLe o deposit.post exit.pre
      exact ⟨by omega, hpre.2⟩

end ProrataAttackState

/-- Exhaustive actor-level classifications over a settled PRORATA boundary. -/
inductive ProrataAttackKind where
  | nonVictimDeposit (attribution : AttackAttribution)
      (amount minted : Nat)
  | nonVictimWithdraw (attribution : AttackAttribution)
      (shares paid : Nat)
  | externalCredit (attribution : AttackAttribution) (amount : Nat)
  | victimDeposit (amount minted : Nat)
  | victimExit (shares paid : Nat)
  | silent
deriving DecidableEq

namespace ProrataAttackKind

def accountingKind : ProrataAttackKind → ProrataAccountingKind
  | .nonVictimDeposit _ amount minted | .victimDeposit amount minted =>
      .deposit amount minted
  | .nonVictimWithdraw _ shares paid | .victimExit shares paid =>
      .withdraw shares paid
  | .externalCredit _ amount => .externalCredit amount
  | .silent => .silent

end ProrataAttackKind

/-- Exact state change for one actor-classified accounting step. -/
inductive ProrataAttackEffect (o : Nat) :
    ProrataAttackState o → ProrataAttackKind →
      ProrataAttackState o → Prop where
  | nonVictimDeposit (pre : ProrataAttackState o)
      (attribution : AttackAttribution) (amount minted : Nat)
      (hminted : minted = mintN o amount pre.accounting.supply
        pre.accounting.balance) :
      ProrataAttackEffect o pre
        (.nonVictimDeposit attribution amount minted)
        { accounting :=
            ⟨pre.accounting.supply + minted,
              pre.accounting.balance + amount⟩
          nonVictimShares := pre.nonVictimShares + minted
          victimShares := pre.victimShares
          inA := pre.inA + attribution.coalitionAmount amount
          outA := pre.outA
          outsideSubsidy :=
            pre.outsideSubsidy + attribution.outsideAmount amount
          outsideOut := pre.outsideOut
          phase := pre.phase }
  | nonVictimWithdraw (pre : ProrataAttackState o)
      (attribution : AttackAttribution) (shares paid : Nat)
      (hshares : shares ≤ pre.nonVictimShares)
      (hpaid : paid = payN o shares pre.accounting.supply
        pre.accounting.balance) :
      ProrataAttackEffect o pre
        (.nonVictimWithdraw attribution shares paid)
        { accounting :=
            ⟨pre.accounting.supply - shares,
              pre.accounting.balance - paid⟩
          nonVictimShares := pre.nonVictimShares - shares
          victimShares := pre.victimShares
          inA := pre.inA
          outA := pre.outA + attribution.coalitionAmount paid
          outsideSubsidy := pre.outsideSubsidy
          outsideOut := pre.outsideOut + attribution.outsideAmount paid
          phase := pre.phase }
  | externalCredit (pre : ProrataAttackState o)
      (attribution : AttackAttribution) (amount : Nat)
      (hpositive : 0 < amount) :
      ProrataAttackEffect o pre (.externalCredit attribution amount)
        { accounting :=
            ⟨pre.accounting.supply, pre.accounting.balance + amount⟩
          nonVictimShares := pre.nonVictimShares
          victimShares := pre.victimShares
          inA := pre.inA + attribution.coalitionAmount amount
          outA := pre.outA
          outsideSubsidy :=
            pre.outsideSubsidy + attribution.outsideAmount amount
          outsideOut := pre.outsideOut
          phase := pre.phase }
  | victimDeposit (pre : ProrataAttackState o) (amount minted : Nat)
      (hphase : pre.phase = .before)
      (hminted : minted = mintN o amount pre.accounting.supply
        pre.accounting.balance)
      (hbacked : pre.accounting.supply ≤
        o * pre.accounting.balance) :
      ProrataAttackEffect o pre (.victimDeposit amount minted)
        { accounting :=
            ⟨pre.accounting.supply + minted,
              pre.accounting.balance + amount⟩
          nonVictimShares := pre.nonVictimShares
          victimShares := pre.victimShares + minted
          inA := pre.inA
          outA := pre.outA
          outsideSubsidy := pre.outsideSubsidy
          outsideOut := pre.outsideOut
          phase := .open
            ⟨pre.accounting, amount, minted, hminted, hbacked⟩ }
  | victimExit (pre : ProrataAttackState o)
      (deposit : VictimDeposit o) (paid : Nat)
      (hphase : pre.phase = .open deposit)
      (hfull : pre.victimShares = deposit.minted)
      (hpaid : paid = payN o deposit.minted pre.accounting.supply
        pre.accounting.balance) :
      ProrataAttackEffect o pre (.victimExit deposit.minted paid)
        { accounting :=
            ⟨pre.accounting.supply - deposit.minted,
              pre.accounting.balance - paid⟩
          nonVictimShares := pre.nonVictimShares
          victimShares := pre.victimShares - deposit.minted
          inA := pre.inA
          outA := pre.outA
          outsideSubsidy := pre.outsideSubsidy
          outsideOut := pre.outsideOut
          phase := .exited deposit
            ⟨pre.accounting, paid, hpaid⟩ }
  | silent (state : ProrataAttackState o) :
      ProrataAttackEffect o state .silent state

namespace ProrataAttackEffect

theorem sharesPartition {o : Nat} {pre post : ProrataAttackState o}
    {kind : ProrataAttackKind} (effect : ProrataAttackEffect o pre kind post)
    (hpre : pre.SharesPartition) : post.SharesPartition := by
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      simp only [ProrataAttackState.SharesPartition] at hpre ⊢
      omega
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      simp only [ProrataAttackState.SharesPartition] at hpre ⊢
      omega
  | externalCredit attribution amount hpositive =>
      exact hpre
  | victimDeposit amount minted hphase hminted hbacked =>
      simp only [ProrataAttackState.SharesPartition] at hpre ⊢
      omega
  | victimExit deposit paid hphase hfull hpaid =>
      simp only [ProrataAttackState.SharesPartition] at hpre ⊢
      omega
  | silent =>
      exact hpre

theorem accountingEffect {o : Nat} {pre post : ProrataAttackState o}
    {kind : ProrataAttackKind} (effect : ProrataAttackEffect o pre kind post)
    (hpre : pre.SharesPartition) :
    ProrataAccountingEffect o pre.accounting kind.accountingKind
      post.accounting := by
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      exact .deposit _ _ _ _ hminted
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      apply ProrataAccountingEffect.withdraw _ _ _ _ _ hpaid
      unfold ProrataAttackState.SharesPartition at hpre
      omega
  | externalCredit attribution amount hpositive =>
      exact .externalCredit _ _ _ hpositive
  | victimDeposit amount minted hphase hminted hbacked =>
      exact .deposit _ _ _ _ hminted
  | victimExit deposit paid hphase hfull hpaid =>
      apply ProrataAccountingEffect.withdraw _ _ _ _ _ hpaid
      unfold ProrataAttackState.SharesPartition at hpre
      omega
  | silent =>
      exact .silent _

theorem flowExact {o : Nat} (ho : o ≠ 0)
    {pre post : ProrataAttackState o} {kind : ProrataAttackKind}
    (effect : ProrataAttackEffect o pre kind post)
    (hpart : pre.SharesPartition) (hflow : pre.FlowExact) :
    post.FlowExact := by
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      cases attribution <;>
        simp [ProrataAttackState.FlowExact, ProrataAttackState.totalIn,
          ProrataAttackState.totalOut, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] at hflow ⊢ <;>
        omega
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      have hsharesSupply : shares ≤ pre.accounting.supply := by
        unfold ProrataAttackState.SharesPartition at hpart
        omega
      have hpaidBalance : paid ≤ pre.accounting.balance := by
        rw [hpaid]
        exact payN_le_balance ho hsharesSupply
      cases attribution <;>
        simp [ProrataAttackState.FlowExact, ProrataAttackState.totalIn,
          ProrataAttackState.totalOut, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] at hflow ⊢ <;>
        omega
  | externalCredit attribution amount hpositive =>
      cases attribution <;>
        simp [ProrataAttackState.FlowExact, ProrataAttackState.totalIn,
          ProrataAttackState.totalOut, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] at hflow ⊢ <;>
        omega
  | victimDeposit amount minted hphase hminted hbacked =>
      simp [ProrataAttackState.FlowExact, ProrataAttackState.totalIn,
        ProrataAttackState.totalOut, VictimPhase.input, VictimPhase.output,
        hphase] at hflow ⊢
      omega
  | victimExit deposit paid hphase hfull hpaid =>
      have hsharesSupply : deposit.minted ≤ pre.accounting.supply := by
        unfold ProrataAttackState.SharesPartition at hpart
        omega
      have hpaidBalance : paid ≤ pre.accounting.balance := by
        rw [hpaid]
        exact payN_le_balance ho hsharesSupply
      simp [ProrataAttackState.FlowExact, ProrataAttackState.totalIn,
        ProrataAttackState.totalOut, VictimPhase.input, VictimPhase.output,
        hphase] at hflow ⊢
      omega
  | silent =>
      exact hflow

theorem victimConsistent {o : Nat} (ho : o ≠ 0)
    {pre post : ProrataAttackState o} {kind : ProrataAttackKind}
    (effect : ProrataAttackEffect o pre kind post)
    (hpart : pre.SharesPartition) (hpre : pre.VictimConsistent) :
    post.VictimConsistent := by
  have hprice : PriceLe o pre.accounting post.accounting :=
    ProrataAccountingEffect.priceLe ho (effect.accountingEffect hpart)
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      apply ProrataAttackState.victimConsistent_of_priceLe (pre := pre) ho
      · rfl
      · rfl
      · exact hprice
      · exact hpre
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      apply ProrataAttackState.victimConsistent_of_priceLe (pre := pre) ho
      · rfl
      · rfl
      · exact hprice
      · exact hpre
  | externalCredit attribution amount hpositive =>
      apply ProrataAttackState.victimConsistent_of_priceLe (pre := pre) ho
      · rfl
      · rfl
      · exact hprice
      · exact hpre
  | victimDeposit amount minted hphase hminted hbacked =>
      unfold ProrataAttackState.VictimConsistent at hpre ⊢
      simp only [hphase] at hpre
      change pre.victimShares + minted = minted ∧
        PriceLe o
          (VictimDeposit.post
            ⟨pre.accounting, amount, minted, hminted, hbacked⟩)
          ⟨pre.accounting.supply + minted,
            pre.accounting.balance + amount⟩
      exact ⟨by omega, PriceLe.refl o _⟩
  | victimExit deposit paid hphase hfull hpaid =>
      unfold ProrataAttackState.VictimConsistent at hpre ⊢
      simp only [hphase] at hpre
      change pre.victimShares - deposit.minted = 0 ∧
        PriceLe o deposit.post pre.accounting
      exact ⟨by omega, hpre.2⟩
  | silent =>
      exact hpre

/-- Every actor-classified step preserves the coalition claim bound. -/
theorem claimBound {o : Nat} (ho : 2 ≤ o)
    {pre post : ProrataAttackState o} {kind : ProrataAttackKind}
    (effect : ProrataAttackEffect o pre kind post)
    (hpre : pre.Invariant) : post.ClaimBound := by
  rcases hpre with ⟨hpart, hflow, hvictim, hclaim⟩
  have ho0 : o ≠ 0 := by omega
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      have hshares :
          pre.nonVictimShares ≤ pre.accounting.supply := by
        unfold ProrataAttackState.SharesPartition at hpart
        omega
      have hupdate :=
        claimN_deposit_le ho0 hshares hminted
      cases attribution <;>
        simp only [ProrataAttackState.ClaimBound,
          ProrataAttackState.totalIn, ProrataAttackState.totalOut,
          ProrataAttackState.nonVictimClaim,
          AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] at hclaim ⊢ <;>
        omega
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      have hnonVictimSupply :
          pre.nonVictimShares ≤ pre.accounting.supply := by
        unfold ProrataAttackState.SharesPartition at hpart
        omega
      have hupdate :=
        claimN_withdraw_le ho0 hshares hnonVictimSupply hpaid
      cases attribution <;>
        simp only [ProrataAttackState.ClaimBound,
          ProrataAttackState.totalIn, ProrataAttackState.totalOut,
          ProrataAttackState.nonVictimClaim,
          AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] at hclaim ⊢ <;>
        omega
  | externalCredit attribution amount hpositive =>
      have hshares :
          pre.nonVictimShares ≤ pre.accounting.supply := by
        unfold ProrataAttackState.SharesPartition at hpart
        omega
      have hupdate :=
        claimN_externalCredit_le
          (o := o) (shares := pre.nonVictimShares)
          (supply := pre.accounting.supply)
          (balance := pre.accounting.balance) (amount := amount)
          ho0 hshares
      cases attribution <;>
        simp only [ProrataAttackState.ClaimBound,
          ProrataAttackState.totalIn, ProrataAttackState.totalOut,
          ProrataAttackState.nonVictimClaim,
          AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] at hclaim ⊢ <;>
        omega
  | victimDeposit amount minted hphase hminted hbacked =>
      unfold ProrataAttackState.VictimConsistent at hvictim
      simp only [hphase] at hvictim
      unfold ProrataAttackState.SharesPartition at hpart
      have hfullSupply :
          pre.nonVictimShares = pre.accounting.supply := by
        omega
      have hpostClaim :
          claimN o pre.nonVictimShares
              (pre.accounting.supply + minted)
              (pre.accounting.balance + amount) ≤
            pre.accounting.balance := by
        rw [hfullSupply]
        exact fullSupply_claim_after_deposit_le ho0 hminted
      unfold ProrataAttackState.FlowExact at hflow
      simp only [ProrataAttackState.totalIn,
        ProrataAttackState.totalOut, hphase, VictimPhase.input,
        VictimPhase.output] at hflow
      simp only [ProrataAttackState.ClaimBound,
        ProrataAttackState.totalIn, ProrataAttackState.totalOut,
        ProrataAttackState.nonVictimClaim]
      omega
  | victimExit deposit paid hphase hfull hpaid =>
      unfold ProrataAttackState.VictimConsistent at hvictim
      simp only [hphase] at hvictim
      unfold ProrataAttackState.SharesPartition at hpart
      have hsupply :
          pre.accounting.supply =
            pre.nonVictimShares + deposit.minted := by
        omega
      have hsupplyAfter :
          pre.accounting.supply - deposit.minted =
            pre.nonVictimShares := by
        omega
      have hdepositPrice :
          PriceLe o deposit.pre deposit.post := by
        simpa only [PriceLe, VictimDeposit.post, deposit.minted_eq] using
          (deposit_price_nondecreasing o deposit.amount
            deposit.pre.supply deposit.pre.balance)
      have hcurrentPrice :
          PriceLe o deposit.pre
            ⟨pre.nonVictimShares + deposit.minted,
              pre.accounting.balance⟩ := by
        rw [← hsupply]
        exact PriceLe.trans ho0 hdepositPrice hvictim.2
      have hpaidCurrent :
          paid = payN o deposit.minted
            (pre.nonVictimShares + deposit.minted)
              pre.accounting.balance := by
        rw [← hsupply]
        exact hpaid
      have hpostClaim :
          claimN o pre.nonVictimShares pre.nonVictimShares
              (pre.accounting.balance - paid) ≤
            pre.accounting.balance - deposit.amount :=
        victim_full_exit_claim_le
          (o := o) (initialSupply := deposit.pre.supply)
          (initialBalance := deposit.pre.balance)
          (victim := deposit.amount) (minted := deposit.minted)
          (attacker := pre.nonVictimShares)
          (balance := pre.accounting.balance) (paid := paid)
          ho deposit.backed deposit.minted_eq hcurrentPrice hpaidCurrent
      have hpostClaimActual :
          claimN o pre.nonVictimShares
              (pre.accounting.supply - deposit.minted)
              (pre.accounting.balance - paid) ≤
            pre.accounting.balance - deposit.amount := by
        rw [hsupplyAfter]
        exact hpostClaim
      unfold ProrataAttackState.FlowExact at hflow
      simp only [ProrataAttackState.totalIn,
        ProrataAttackState.totalOut, hphase, VictimPhase.input,
        VictimPhase.output] at hflow
      simp only [ProrataAttackState.ClaimBound,
        ProrataAttackState.totalIn, ProrataAttackState.totalOut,
        ProrataAttackState.nonVictimClaim]
      simp only [ProrataAttackState.ClaimBound,
        ProrataAttackState.totalIn, ProrataAttackState.totalOut,
        ProrataAttackState.nonVictimClaim] at hclaim
      by_cases hvictimBalance :
          deposit.amount ≤ pre.accounting.balance <;> omega
  | silent =>
      exact hclaim

/-- Every actor-classified step preserves the full attack-state invariant. -/
theorem invariant {o : Nat} (ho : 2 ≤ o)
    {pre post : ProrataAttackState o} {kind : ProrataAttackKind}
    (effect : ProrataAttackEffect o pre kind post)
    (hpre : pre.Invariant) : post.Invariant := by
  exact
    ⟨effect.sharesPartition hpre.1,
      effect.flowExact (by omega) hpre.1 hpre.2.1,
      effect.victimConsistent (by omega) hpre.1 hpre.2.2.1,
      effect.claimBound ho hpre⟩

end ProrataAttackEffect

/-- One exact actor-classified step with retained committed chronology. -/
structure ProrataAttackStep (o : Nat) where
  pre : ProrataAttackState o
  post : ProrataAttackState o
  kind : ProrataAttackKind
  provenance : ProrataAccountingProvenance
  effect : ProrataAttackEffect o pre kind post

/-- A finite actor path beginning at the initialized deployment boundary. -/
inductive ProrataAttackPath (o : Nat) : ProrataAttackState o → Prop where
  | genesis : ProrataAttackPath o (ProrataAttackState.genesis o)
  | snoc (step : ProrataAttackStep o)
      (path : ProrataAttackPath o step.pre) :
      ProrataAttackPath o step.post

end Prorata

end Blanc
