import Blanc.Composition.ProrataWethVaultAccounting
import Blanc.ProrataWethVaultDust

/-!
# Coalition overlay for the PRORATA/WETH vault pair (model level)

PRORATA's `ProrataAttackState` prices "caller = share holder" and has no share
transfer.  The vault separates caller, owner and receiver, its shares move
(`transfer`, `transferFrom`, delegated `withdraw`/`redeem`), and two of its four
entry points are inverse-quoted.  This module is the actor overlay that
survives all of that.  It is independent of any realized history: the trace
adapter consumes `PairAttackEffect`, `PairAttackPath` and the three
`*_of_pairAttackPath` bounds.

## Pricing convention (decision `vault-coalition-share-pricing-20260916`, D1(a))

A share movement across the boundary is priced at the **pre-step** snapshot:
an inflow at `ceilClaimN` (`ceilDiv (m * X) D`), an outflow at `claimN`
(floor).  Both round in the pool's favour, so the bound needs no tolerance.

## Which boundary

`ProrataAttackState` aggregates every non-victim share in `nonVictimShares`
and partitions only cash by `AttackAttribution`.  `ClaimBound` contains
`claimN nonVictimShares`, so a share that moves between two non-victims moves
nothing in it; charging such a move to `sharesOut` would count the same shares
twice.  The share boundary is therefore **victim ↔ non-victim**, and a `Bool`
side flag in `PairAttackKind` reads "on the non-victim side".  A genuine
sub-coalition is still expressed the PRORATA way, by attribution: an
outsider's cash is `outsideSubsidy`, the shares it buys are aggregated, and a
gift of them to the coalition is already paid for by that subsidy.  The only
shares the non-victim side can obtain without any non-victim having paid cash
are the victim's, and `sharesIn` is exactly their price.

## What each role split is

* payer non-victim, receiver victim: the cash is attributed as usual and the
  minted shares are an outflow (`sharesOut`, floor, pre-step).
* payer victim, receiver non-victim: `nonVictimDeposit .outside`.  The cash is
  booked at face value as an outside subsidy, which already covers the claim
  it buys; pricing the shares as well would count it twice, and `FlowExact`
  leaves no other place for victim cash outside the victim's own phase.
* owner non-victim, receiver victim: `nonVictimWithdraw` with whatever
  attribution the adapter charges.  No share crosses the boundary.
* owner victim, receiver non-victim (a delegated burn): the burnt shares **are**
  an inflow.  The step is a victim gift followed by a non-victim exit, and is
  charged as one: `sharesIn` rises by `ceilClaimN`, `totalOut` by the payout.
  Leaving the burn uncharged is refuted by `deposit 1 to the victim; burn its 2
  shares for 1` at offset 2.
* a self-outbound burn (receiver = vault) is `nonVictimWithdraw` with
  `paid = 0`; `mint` and `withdraw` are the same constructors as `deposit` and
  `redeem`, whose quotes are inequalities in the pool's favour
  (`minted_le_mintN_of_previewMintN`, `paid_le_payN_of_previewWithdrawN`).

## The victim

The protected party keeps PRORATA's schedule: one exact deposit, one exact
exit of the shares that deposit minted.  What non-victims do *to* it is
unrestricted: it may be gifted shares before, during and after its phase.
Shares it holds beyond the deposit (`giftShares`) it may give away or have
burnt; the deposit's own shares stay until the exit.  `GiftBook` is the
auxiliary invariant that makes the two victim steps provable once the victim
holds gifted shares: the net priced outflow never exceeds the floor claim of
the gifted shares the victim still holds.
-/

namespace Blanc.Composition.ProrataWethVault

open Blanc.Prorata

/-! ## Arithmetic -/

/-- The ceiling-priced claim of `shares`: the D1(a) price of a share inflow. -/
def ceilClaimN (o shares supply balance : Nat) : Nat :=
  Jaune.ceilDiv (shares * (balance + 1)) (supply + o)

theorem claimN_mono_shares {o c c' supply balance : Nat} (h : c ≤ c') :
    claimN o c supply balance ≤ claimN o c' supply balance := by
  unfold claimN payN
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ h)

/-- Floor claims are superadditive: splitting a holding never raises its claim. -/
theorem claimN_add_ge (o c m supply balance : Nat) :
    claimN o c supply balance + claimN o m supply balance ≤
      claimN o (c + m) supply balance := by
  unfold claimN payN
  rw [Nat.add_mul]
  exact Nat.add_div_le_add_div _ _ _

/-- The floor/ceil subadditivity behind every share inflow:
`floor ((c + m) X / D) ≤ floor (c X / D) + ceilDiv (m X) D`. -/
theorem claimN_add_le_ceil {o : Nat} (ho : o ≠ 0) (c m supply balance : Nat) :
    claimN o (c + m) supply balance ≤
      claimN o c supply balance + ceilClaimN o m supply balance := by
  unfold claimN payN ceilClaimN
  have hD : 0 < supply + o := by omega
  have hceil := Jaune.le_ceilDiv_mul (Nat.ne_of_gt hD) (m * (balance + 1))
  rw [Nat.add_mul]
  calc
    (c * (balance + 1) + m * (balance + 1)) / (supply + o)
        ≤ (c * (balance + 1) +
            Jaune.ceilDiv (m * (balance + 1)) (supply + o) * (supply + o)) /
              (supply + o) :=
      Nat.div_le_div_right (Nat.add_le_add_left hceil _)
    _ = c * (balance + 1) / (supply + o) +
          Jaune.ceilDiv (m * (balance + 1)) (supply + o) :=
      Nat.add_mul_div_right _ _ hD

/-- Minting `extra` further shares to an accounted holder at a fixed balance
cannot lower its claim; read right to left, burning them cannot raise it. -/
theorem claimN_mono_minted {o c supply balance : Nat} (ho : o ≠ 0)
    (hc : c ≤ supply) (extra : Nat) :
    claimN o c supply balance ≤
      claimN o (c + extra) (supply + extra) balance := by
  unfold claimN payN
  have hD : 0 < supply + o := by omega
  rw [Nat.le_div_iff_mul_le (by omega)]
  have hq : c * (balance + 1) / (supply + o) * (supply + o) ≤
      c * (balance + 1) := Nat.div_mul_le_self _ _
  have hqX : c * (balance + 1) / (supply + o) ≤ balance + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hD]
    have : c * (balance + 1) ≤ (supply + o) * (balance + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hextra := Nat.mul_le_mul_right extra hqX
  calc
    c * (balance + 1) / (supply + o) * (supply + extra + o) =
        c * (balance + 1) / (supply + o) * (supply + o) +
          c * (balance + 1) / (supply + o) * extra := by
      rw [← Nat.mul_add]
      congr 1
      omega
    _ ≤ c * (balance + 1) + (balance + 1) * extra :=
      Nat.add_le_add hq hextra
    _ = (c + extra) * (balance + 1) := by ring

/-- Paying out less than the quote raises the remaining claim by at most the
shortfall. -/
theorem claimN_mono_paid {o c supply balance paid quote : Nat} (ho : o ≠ 0)
    (hc : c ≤ supply) (hpaid : paid ≤ quote) (hquote : quote ≤ balance) :
    paid + claimN o c supply (balance - paid) ≤
      quote + claimN o c supply (balance - quote) := by
  have h := claimN_externalCredit_le (o := o) (shares := c) (supply := supply)
    (balance := balance - quote) (amount := quote - paid) ho hc
  rw [show balance - quote + (quote - paid) = balance - paid by omega] at h
  omega

/-- An inbound step quoted at or below the forward quote never lowers the price. -/
theorem priceLe_of_minted_le {o supply balance amount minted : Nat}
    (hminted : minted ≤ mintN o amount supply balance) :
    PriceLe o ⟨supply, balance⟩ ⟨supply + minted, balance + amount⟩ := by
  unfold PriceLe
  have hquote : minted * (balance + 1) ≤ amount * (supply + o) :=
    (Nat.mul_le_mul_right _ hminted).trans (mintN_never_overmints o amount supply balance)
  simp only
  calc
    (balance + 1) * (supply + minted + o) =
        (balance + 1) * (supply + o) + minted * (balance + 1) := by
      rw [show supply + minted + o = supply + o + minted by omega, Nat.mul_add,
        Nat.mul_comm (balance + 1) minted]
    _ ≤ (balance + 1) * (supply + o) + amount * (supply + o) :=
      Nat.add_le_add_left hquote _
    _ = (balance + amount + 1) * (supply + o) := by ring

/-- An outbound step paying at most the redemption quote never lowers the price. -/
theorem priceLe_of_paid_le {o supply balance shares paid : Nat} (ho : o ≠ 0)
    (hshares : shares ≤ supply)
    (hpaid : paid ≤ payN o shares supply balance) :
    PriceLe o ⟨supply, balance⟩ ⟨supply - shares, balance - paid⟩ := by
  unfold PriceLe
  have hquote : paid * (supply + o) ≤ shares * (balance + 1) :=
    (Nat.mul_le_mul_right _ hpaid).trans (payN_never_overpays o shares supply balance)
  have hbalance : paid ≤ balance := hpaid.trans (payN_le_balance ho hshares)
  simp only
  rw [show supply - shares + o = supply + o - shares by omega,
    show balance - paid + 1 = balance + 1 - paid by omega, Nat.mul_sub, Nat.sub_mul,
    Nat.mul_comm (balance + 1) shares]
  omega

/-- Same-side inbound step under an inequality quote (`deposit` and `mint`). -/
theorem claimN_inbound_le {o c supply balance amount minted : Nat} (ho : o ≠ 0)
    (hc : c ≤ supply) (hminted : minted ≤ mintN o amount supply balance) :
    claimN o (c + minted) (supply + minted) (balance + amount) ≤
      claimN o c supply balance + amount := by
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le hminted
  have hmono := claimN_mono_minted (o := o) (c := c + minted)
    (supply := supply + minted) (balance := balance + amount) ho (by omega) extra
  have hexact := claimN_deposit_le (o := o) (attacker := c) (supply := supply)
    (balance := balance) (amount := amount) ho hc rfl
  rw [hextra] at hexact
  rw [show c + minted + extra = c + (minted + extra) by omega,
    show supply + minted + extra = supply + (minted + extra) by omega] at hmono
  exact hmono.trans hexact

/-- Cross-role inbound step: a non-victim pays, the victim receives.  The
shares leave at their pre-step floor price and the payer's remaining claim
plus that price is still covered by the cash. -/
theorem claimN_inbound_cross_le {o c supply balance amount minted : Nat}
    (ho : o ≠ 0) (hc : c ≤ supply)
    (hminted : minted ≤ mintN o amount supply balance) :
    claimN o c (supply + minted) (balance + amount) +
        claimN o minted supply balance ≤
      claimN o c supply balance + amount := by
  have hprice := payN_mono_price (shares := minted) ho (priceLe_of_minted_le hminted)
  have hsplit := claimN_add_ge o c minted (supply + minted) (balance + amount)
  have hsame := claimN_inbound_le ho hc hminted
  unfold claimN at hsplit hsame ⊢
  simp only at hprice
  omega

/-- Same-side outbound step under an inequality quote (`redeem`, `withdraw`,
and with `paid = 0` a self-outbound burn). -/
theorem claimN_outbound_le {o c supply balance burned paid : Nat} (ho : o ≠ 0)
    (hburned : burned ≤ c) (hc : c ≤ supply)
    (hpaid : paid ≤ payN o burned supply balance) :
    paid + claimN o (c - burned) (supply - burned) (balance - paid) ≤
      claimN o c supply balance := by
  have hexact := claimN_withdraw_le (o := o) (attacker := c) (supply := supply)
    (balance := balance) (burned := burned) ho hburned hc rfl
  have hslack := claimN_mono_paid (o := o) (c := c - burned)
    (supply := supply - burned) (balance := balance) ho (by omega) hpaid
    (payN_le_balance ho (hburned.trans hc))
  omega

/-- Delegated outbound step: a non-victim receives the proceeds of burning the
victim's shares.  The burnt shares are an inflow at their pre-step ceiling. -/
theorem claimN_outbound_delegated_le {o c supply balance burned paid : Nat}
    (ho : o ≠ 0) (hc : c + burned ≤ supply)
    (hpaid : paid ≤ payN o burned supply balance) :
    paid + claimN o c (supply - burned) (balance - paid) ≤
      claimN o c supply balance + ceilClaimN o burned supply balance := by
  have hgift := claimN_add_le_ceil ho c burned supply balance
  have hexit := claimN_outbound_le (o := o) (c := c + burned) ho
    (Nat.le_add_left burned c) hc hpaid
  rw [Nat.add_sub_cancel] at hexit
  omega

/-! ## Vault quotes as model quotes -/

theorem mintN_offsetN_eq (amount supply balance : Nat) :
    mintN Blanc.ProrataWethVault.offsetN amount supply balance =
      Blanc.ProrataWethVault.convertToSharesN amount balance supply := rfl

theorem payN_offsetN_eq (shares supply balance : Nat) :
    payN Blanc.ProrataWethVault.offsetN shares supply balance =
      Blanc.ProrataWethVault.convertToAssetsN shares balance supply := rfl

/-- The inverse-quoted `mint` satisfies the inbound inequality quote. -/
theorem minted_le_mintN_of_previewMintN (shares supply balance : Nat) :
    shares ≤ mintN Blanc.ProrataWethVault.offsetN
      (Blanc.ProrataWethVault.previewMintN shares balance supply) supply balance :=
  Blanc.ProrataWethVault.mint_never_overmints shares balance supply

/-- The inverse-quoted `withdraw` satisfies the outbound inequality quote. -/
theorem paid_le_payN_of_previewWithdrawN (amount supply balance : Nat) :
    amount ≤ payN Blanc.ProrataWethVault.offsetN
      (Blanc.ProrataWethVault.previewWithdrawN amount balance supply) supply balance :=
  Blanc.ProrataWethVault.withdraw_never_overpays amount balance supply

/-! ## State -/

/-- PRORATA's attack state with the two priced share-crossing totals. -/
structure PairAttackState (o : Nat) extends ProrataAttackState o where
  /-- Ceiling-priced value of the shares the non-victim side received from the victim. -/
  sharesIn : Nat
  /-- Floor-priced value of the shares the non-victim side sent to the victim. -/
  sharesOut : Nat

namespace PairAttackState

variable {o : Nat}

/-- The shares the victim's open deposit minted; they stay until its exit. -/
def lockedShares (state : PairAttackState o) : Nat :=
  match state.phase with
  | .before | .exited _ _ => 0
  | .open deposit => deposit.minted

/-- The victim's shares beyond its own deposit: what non-victims gave it. -/
def giftShares (state : PairAttackState o) : Nat :=
  state.victimShares - state.lockedShares

/-- D1(a) inflow price of `shares` at this state's snapshot. -/
def inflowPrice (state : PairAttackState o) (shares : Nat) : Nat :=
  ceilClaimN o shares state.accounting.supply state.accounting.balance

/-- D1(a) outflow price of `shares` at this state's snapshot. -/
def outflowPrice (state : PairAttackState o) (shares : Nat) : Nat :=
  claimN o shares state.accounting.supply state.accounting.balance

/-- The coalition claim bound with both priced share crossings. -/
def ClaimBound (state : PairAttackState o) : Prop :=
  state.totalOut + state.sharesOut + state.nonVictimClaim ≤
    state.totalIn + state.sharesIn

/-- The net priced outflow is covered by the gifted shares the victim holds. -/
def GiftBook (state : PairAttackState o) : Prop :=
  state.sharesOut ≤ state.sharesIn +
    claimN o state.giftShares state.accounting.supply state.accounting.balance

/-- Victim chronology.  Unlike PRORATA's, it lets the victim hold gifted shares
in every phase. -/
def VictimConsistent (state : PairAttackState o) : Prop :=
  match state.phase with
  | .before => True
  | .open deposit =>
      deposit.minted ≤ state.victimShares ∧
        PriceLe o deposit.post state.accounting
  | .exited deposit exit => PriceLe o deposit.post exit.pre

def Invariant (state : PairAttackState o) : Prop :=
  state.SharesPartition ∧ state.FlowExact ∧ state.VictimConsistent ∧
    state.GiftBook ∧ state.ClaimBound

def genesis (o : Nat) : PairAttackState o where
  toProrataAttackState := ProrataAttackState.genesis o
  sharesIn := 0
  sharesOut := 0

theorem genesis_invariant (o : Nat) : (genesis o).Invariant := by
  have h := ProrataAttackState.genesis_invariant o
  refine ⟨h.1, h.2.1, trivial, ?_, ?_⟩
  · simp [GiftBook, genesis]
  · have hclaim := h.2.2.2
    unfold ProrataAttackState.ClaimBound at hclaim
    unfold ClaimBound
    simpa [genesis] using hclaim

/-- Inbound step paid by a non-victim, shares to a non-victim. -/
def inbound (pre : PairAttackState o) (attribution : AttackAttribution)
    (amount minted : Nat) : PairAttackState o :=
  { pre with
    accounting := ⟨pre.accounting.supply + minted, pre.accounting.balance + amount⟩
    nonVictimShares := pre.nonVictimShares + minted
    inA := pre.inA + attribution.coalitionAmount amount
    outsideSubsidy := pre.outsideSubsidy + attribution.outsideAmount amount }

/-- Inbound step paid by a non-victim, shares to the victim. -/
def inboundCross (pre : PairAttackState o) (attribution : AttackAttribution)
    (amount minted : Nat) : PairAttackState o :=
  { pre with
    accounting := ⟨pre.accounting.supply + minted, pre.accounting.balance + amount⟩
    victimShares := pre.victimShares + minted
    inA := pre.inA + attribution.coalitionAmount amount
    outsideSubsidy := pre.outsideSubsidy + attribution.outsideAmount amount
    sharesOut := pre.sharesOut + pre.outflowPrice minted }

/-- Outbound step burning non-victim shares. -/
def outbound (pre : PairAttackState o) (attribution : AttackAttribution)
    (shares paid : Nat) : PairAttackState o :=
  { pre with
    accounting := ⟨pre.accounting.supply - shares, pre.accounting.balance - paid⟩
    nonVictimShares := pre.nonVictimShares - shares
    outA := pre.outA + attribution.coalitionAmount paid
    outsideOut := pre.outsideOut + attribution.outsideAmount paid }

/-- Outbound step burning the victim's gifted shares for a non-victim receiver. -/
def outboundDelegated (pre : PairAttackState o) (attribution : AttackAttribution)
    (shares paid : Nat) : PairAttackState o :=
  { pre with
    accounting := ⟨pre.accounting.supply - shares, pre.accounting.balance - paid⟩
    victimShares := pre.victimShares - shares
    outA := pre.outA + attribution.coalitionAmount paid
    outsideOut := pre.outsideOut + attribution.outsideAmount paid
    sharesIn := pre.sharesIn + pre.inflowPrice shares }

def credited (pre : PairAttackState o) (attribution : AttackAttribution)
    (amount : Nat) : PairAttackState o :=
  { pre with
    accounting := ⟨pre.accounting.supply, pre.accounting.balance + amount⟩
    inA := pre.inA + attribution.coalitionAmount amount
    outsideSubsidy := pre.outsideSubsidy + attribution.outsideAmount amount }

/-- Share transfer from a non-victim to the victim. -/
def sharesToVictim (pre : PairAttackState o) (amount : Nat) : PairAttackState o :=
  { pre with
    nonVictimShares := pre.nonVictimShares - amount
    victimShares := pre.victimShares + amount
    sharesOut := pre.sharesOut + pre.outflowPrice amount }

/-- Share transfer from the victim to a non-victim. -/
def sharesFromVictim (pre : PairAttackState o) (amount : Nat) : PairAttackState o :=
  { pre with
    nonVictimShares := pre.nonVictimShares + amount
    victimShares := pre.victimShares - amount
    sharesIn := pre.sharesIn + pre.inflowPrice amount }

def victimDeposited (pre : PairAttackState o) (deposit : VictimDeposit o) :
    PairAttackState o :=
  { pre with
    accounting := deposit.post
    victimShares := pre.victimShares + deposit.minted
    phase := .open deposit }

def victimExited (pre : PairAttackState o) (deposit : VictimDeposit o)
    (exit : VictimExit o deposit) : PairAttackState o :=
  { pre with
    accounting :=
      ⟨pre.accounting.supply - deposit.minted, pre.accounting.balance - exit.payout⟩
    victimShares := pre.victimShares - deposit.minted
    phase := .exited deposit exit }

end PairAttackState

/-! ## Steps -/

/-- Actor-level classification of one pair step.  A `Bool` side flag reads "on
the non-victim side".  `nonVictimDeposit` covers `deposit` and `mint`,
`nonVictimWithdraw` covers `redeem`, `withdraw` and the self-outbound burn. -/
inductive PairAttackKind where
  | nonVictimDeposit (attribution : AttackAttribution) (amount minted : Nat)
      (receiverIn : Bool)
  | nonVictimWithdraw (attribution : AttackAttribution) (shares paid : Nat)
      (ownerIn : Bool)
  | externalCredit (attribution : AttackAttribution) (amount : Nat)
  | shareMove (fromIn toIn : Bool) (amount : Nat)
  | victimDeposit (amount minted : Nat)
  | victimExit (shares paid : Nat)
  | silent
deriving DecidableEq

/-- Exact state change of one classified pair step. -/
inductive PairAttackEffect (o : Nat) :
    PairAttackState o → PairAttackKind → PairAttackState o → Prop where
  | nonVictimDeposit (pre : PairAttackState o) (attribution : AttackAttribution)
      (amount minted : Nat)
      (hminted : minted ≤ mintN o amount pre.accounting.supply pre.accounting.balance) :
      PairAttackEffect o pre (.nonVictimDeposit attribution amount minted true)
        (pre.inbound attribution amount minted)
  | depositToVictim (pre : PairAttackState o) (attribution : AttackAttribution)
      (amount minted : Nat)
      (hminted : minted ≤ mintN o amount pre.accounting.supply pre.accounting.balance) :
      PairAttackEffect o pre (.nonVictimDeposit attribution amount minted false)
        (pre.inboundCross attribution amount minted)
  | nonVictimWithdraw (pre : PairAttackState o) (attribution : AttackAttribution)
      (shares paid : Nat) (hshares : shares ≤ pre.nonVictimShares)
      (hpaid : paid ≤ payN o shares pre.accounting.supply pre.accounting.balance) :
      PairAttackEffect o pre (.nonVictimWithdraw attribution shares paid true)
        (pre.outbound attribution shares paid)
  | delegatedWithdraw (pre : PairAttackState o) (attribution : AttackAttribution)
      (shares paid : Nat) (hshares : shares ≤ pre.giftShares)
      (hpaid : paid ≤ payN o shares pre.accounting.supply pre.accounting.balance) :
      PairAttackEffect o pre (.nonVictimWithdraw attribution shares paid false)
        (pre.outboundDelegated attribution shares paid)
  | externalCredit (pre : PairAttackState o) (attribution : AttackAttribution)
      (amount : Nat) :
      PairAttackEffect o pre (.externalCredit attribution amount)
        (pre.credited attribution amount)
  | shareMoveToVictim (pre : PairAttackState o) (amount : Nat)
      (hamount : amount ≤ pre.nonVictimShares) :
      PairAttackEffect o pre (.shareMove true false amount) (pre.sharesToVictim amount)
  | shareMoveFromVictim (pre : PairAttackState o) (amount : Nat)
      (hamount : amount ≤ pre.giftShares) :
      PairAttackEffect o pre (.shareMove false true amount) (pre.sharesFromVictim amount)
  | shareMoveWithin (pre : PairAttackState o) (side : Bool) (amount : Nat) :
      PairAttackEffect o pre (.shareMove side side amount) pre
  | victimDeposit (pre : PairAttackState o) (deposit : VictimDeposit o)
      (hphase : pre.phase = .before) (hpre : deposit.pre = pre.accounting) :
      PairAttackEffect o pre (.victimDeposit deposit.amount deposit.minted)
        (pre.victimDeposited deposit)
  | victimExit (pre : PairAttackState o) (deposit : VictimDeposit o)
      (exit : VictimExit o deposit) (hphase : pre.phase = .open deposit)
      (hpre : exit.pre = pre.accounting) :
      PairAttackEffect o pre (.victimExit deposit.minted exit.payout)
        (pre.victimExited deposit exit)
  | silent (state : PairAttackState o) : PairAttackEffect o state .silent state

namespace PairAttackState

variable {o : Nat}

theorem lockedShares_le (state : PairAttackState o)
    (hvictim : state.VictimConsistent) : state.lockedShares ≤ state.victimShares := by
  unfold VictimConsistent at hvictim
  unfold lockedShares
  cases hp : state.phase with
  | before => exact Nat.zero_le _
  | «open» deposit =>
      simp only [hp] at hvictim
      exact hvictim.1
  | exited deposit exit => exact Nat.zero_le _

/-- A step that keeps the phase, keeps the locked shares with the victim and
does not lower the price keeps the victim chronology. -/
theorem victimConsistent_of_priceLe (ho : o ≠ 0) {pre post : PairAttackState o}
    (hphase : post.phase = pre.phase)
    (hshares : pre.lockedShares ≤ post.victimShares)
    (hprice : PriceLe o pre.accounting post.accounting)
    (hpre : pre.VictimConsistent) : post.VictimConsistent := by
  unfold VictimConsistent at hpre ⊢
  unfold lockedShares at hshares
  rw [hphase]
  cases hp : pre.phase with
  | before => trivial
  | «open» deposit =>
      simp only [hp] at hpre hshares
      exact ⟨hshares, PriceLe.trans ho hpre.2 hprice⟩
  | exited deposit exit =>
      simp only [hp] at hpre
      exact hpre

end PairAttackState

namespace PairAttackEffect

variable {o : Nat}

theorem sharesPartition {pre post : PairAttackState o} {kind : PairAttackKind}
    (effect : PairAttackEffect o pre kind post) (hpart : pre.SharesPartition)
    (hvictim : pre.VictimConsistent) : post.SharesPartition := by
  have hlocked := pre.lockedShares_le hvictim
  unfold ProrataAttackState.SharesPartition at hpart ⊢
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      simp only [PairAttackState.inbound]
      omega
  | depositToVictim attribution amount minted hminted =>
      simp only [PairAttackState.inboundCross]
      omega
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      simp only [PairAttackState.outbound]
      omega
  | delegatedWithdraw attribution shares paid hshares hpaid =>
      unfold PairAttackState.giftShares at hshares
      simp only [PairAttackState.outboundDelegated]
      omega
  | externalCredit attribution amount => exact hpart
  | shareMoveToVictim amount hamount =>
      simp only [PairAttackState.sharesToVictim]
      omega
  | shareMoveFromVictim amount hamount =>
      unfold PairAttackState.giftShares at hamount
      simp only [PairAttackState.sharesFromVictim]
      omega
  | shareMoveWithin side amount => exact hpart
  | victimDeposit deposit hphase hdeposit =>
      simp only [PairAttackState.victimDeposited, VictimDeposit.post, hdeposit]
      omega
  | victimExit deposit exit hphase hexit =>
      simp only [PairAttackState.lockedShares, hphase] at hlocked
      simp only [PairAttackState.victimExited]
      omega
  | silent => exact hpart

/-- Every classified pair step weakly raises the share price. -/
theorem priceLe (ho : o ≠ 0) {pre post : PairAttackState o} {kind : PairAttackKind}
    (effect : PairAttackEffect o pre kind post) (hpart : pre.SharesPartition)
    (hvictim : pre.VictimConsistent) : PriceLe o pre.accounting post.accounting := by
  have hlocked := pre.lockedShares_le hvictim
  unfold ProrataAttackState.SharesPartition at hpart
  cases effect with
  | nonVictimDeposit attribution amount minted hminted => exact priceLe_of_minted_le hminted
  | depositToVictim attribution amount minted hminted => exact priceLe_of_minted_le hminted
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      exact priceLe_of_paid_le (supply := pre.accounting.supply) ho (by omega) hpaid
  | delegatedWithdraw attribution shares paid hshares hpaid =>
      unfold PairAttackState.giftShares at hshares
      exact priceLe_of_paid_le (supply := pre.accounting.supply) ho (by omega) hpaid
  | externalCredit attribution amount =>
      unfold PriceLe
      exact Nat.mul_le_mul_right _ (by simp only [PairAttackState.credited]; omega)
  | shareMoveToVictim amount hamount => exact PriceLe.refl o _
  | shareMoveFromVictim amount hamount => exact PriceLe.refl o _
  | shareMoveWithin side amount => exact PriceLe.refl o _
  | victimDeposit deposit hphase hdeposit =>
      have h := priceLe_of_minted_le (o := o) (supply := deposit.pre.supply)
        (balance := deposit.pre.balance) (amount := deposit.amount)
        (Nat.le_of_eq deposit.minted_eq)
      rw [← hdeposit]
      exact h
  | victimExit deposit exit hphase hexit =>
      simp only [PairAttackState.lockedShares, hphase] at hlocked
      have h := priceLe_of_paid_le (o := o) (supply := pre.accounting.supply)
        (balance := pre.accounting.balance) (shares := deposit.minted) ho (by omega)
        (Nat.le_of_eq (hexit ▸ exit.payout_eq))
      exact h
  | silent => exact PriceLe.refl o _

theorem flowExact (ho : o ≠ 0) {pre post : PairAttackState o} {kind : PairAttackKind}
    (effect : PairAttackEffect o pre kind post) (hpart : pre.SharesPartition)
    (hvictim : pre.VictimConsistent) (hflow : pre.FlowExact) : post.FlowExact := by
  have hlocked := pre.lockedShares_le hvictim
  unfold ProrataAttackState.SharesPartition at hpart
  unfold ProrataAttackState.FlowExact ProrataAttackState.totalIn
    ProrataAttackState.totalOut at hflow ⊢
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      cases attribution <;>
        simp only [PairAttackState.inbound, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] <;> omega
  | depositToVictim attribution amount minted hminted =>
      cases attribution <;>
        simp only [PairAttackState.inboundCross, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] <;> omega
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      have hbalance : paid ≤ pre.accounting.balance :=
        hpaid.trans (payN_le_balance ho (by omega))
      cases attribution <;>
        simp only [PairAttackState.outbound, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] <;> omega
  | delegatedWithdraw attribution shares paid hshares hpaid =>
      unfold PairAttackState.giftShares at hshares
      have hbalance : paid ≤ pre.accounting.balance :=
        hpaid.trans (payN_le_balance ho (by omega))
      cases attribution <;>
        simp only [PairAttackState.outboundDelegated, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] <;> omega
  | externalCredit attribution amount =>
      cases attribution <;>
        simp only [PairAttackState.credited, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] <;> omega
  | shareMoveToVictim amount hamount => exact hflow
  | shareMoveFromVictim amount hamount => exact hflow
  | shareMoveWithin side amount => exact hflow
  | victimDeposit deposit hphase hdeposit =>
      simp only [hphase, VictimPhase.input, VictimPhase.output] at hflow
      simp only [PairAttackState.victimDeposited, VictimDeposit.post, hdeposit,
        VictimPhase.input, VictimPhase.output]
      omega
  | victimExit deposit exit hphase hexit =>
      simp only [PairAttackState.lockedShares, hphase] at hlocked
      have hbalance : exit.payout ≤ pre.accounting.balance := by
        rw [exit.payout_eq, hexit]
        exact payN_le_balance ho (by omega)
      simp only [hphase, VictimPhase.input, VictimPhase.output] at hflow
      simp only [PairAttackState.victimExited, VictimPhase.input, VictimPhase.output]
      omega
  | silent => exact hflow

theorem victimConsistent (ho : o ≠ 0) {pre post : PairAttackState o}
    {kind : PairAttackKind} (effect : PairAttackEffect o pre kind post)
    (hpart : pre.SharesPartition) (hpre : pre.VictimConsistent) :
    post.VictimConsistent := by
  have hprice := effect.priceLe ho hpart hpre
  have hlocked := pre.lockedShares_le hpre
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      exact PairAttackState.victimConsistent_of_priceLe (pre := pre) ho rfl hlocked hprice hpre
  | depositToVictim attribution amount minted hminted =>
      exact PairAttackState.victimConsistent_of_priceLe (pre := pre) ho rfl
        (hlocked.trans (Nat.le_add_right _ _)) hprice hpre
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      exact PairAttackState.victimConsistent_of_priceLe (pre := pre) ho rfl hlocked hprice hpre
  | delegatedWithdraw attribution shares paid hshares hpaid =>
      unfold PairAttackState.giftShares at hshares
      exact PairAttackState.victimConsistent_of_priceLe (pre := pre) ho rfl
        (by simp only [PairAttackState.outboundDelegated]; omega) hprice hpre
  | externalCredit attribution amount =>
      exact PairAttackState.victimConsistent_of_priceLe (pre := pre) ho rfl hlocked hprice hpre
  | shareMoveToVictim amount hamount =>
      exact PairAttackState.victimConsistent_of_priceLe (pre := pre) ho rfl
        (hlocked.trans (Nat.le_add_right _ _)) hprice hpre
  | shareMoveFromVictim amount hamount =>
      unfold PairAttackState.giftShares at hamount
      exact PairAttackState.victimConsistent_of_priceLe (pre := pre) ho rfl
        (by simp only [PairAttackState.sharesFromVictim]; omega) hprice hpre
  | shareMoveWithin side amount => exact hpre
  | victimDeposit deposit hphase hdeposit =>
      unfold PairAttackState.VictimConsistent
      simp only [PairAttackState.victimDeposited]
      exact ⟨Nat.le_add_left _ _, PriceLe.refl o _⟩
  | victimExit deposit exit hphase hexit =>
      unfold PairAttackState.VictimConsistent at hpre ⊢
      simp only [hphase] at hpre
      simp only [PairAttackState.victimExited]
      rw [hexit]
      exact hpre.2
  | silent => exact hpre

/-- A step that moves no priced share and does not lower the price keeps the
gift book. -/
theorem giftBook_of_priceLe (ho : o ≠ 0) {pre post : PairAttackState o}
    (hgift : post.giftShares = pre.giftShares) (hin : post.sharesIn = pre.sharesIn)
    (hout : post.sharesOut = pre.sharesOut)
    (hprice : PriceLe o pre.accounting post.accounting) (hpre : pre.GiftBook) :
    post.GiftBook := by
  unfold PairAttackState.GiftBook at hpre ⊢
  have hmono := payN_mono_price (shares := pre.giftShares) ho hprice
  rw [hgift, hin, hout]
  unfold claimN
  unfold claimN at hpre
  omega

theorem giftBook (ho : o ≠ 0) {pre post : PairAttackState o} {kind : PairAttackKind}
    (effect : PairAttackEffect o pre kind post) (hpart : pre.SharesPartition)
    (hvictim : pre.VictimConsistent) (hpre : pre.GiftBook) : post.GiftBook := by
  have hprice := effect.priceLe ho hpart hvictim
  have hlocked := pre.lockedShares_le hvictim
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      exact giftBook_of_priceLe (pre := pre) ho rfl rfl rfl hprice hpre
  | depositToVictim attribution amount minted hminted =>
      have hmono := payN_mono_price (shares := pre.giftShares) ho hprice
      have hmonoMinted := payN_mono_price (shares := minted) ho hprice
      have hsplit := claimN_add_ge o pre.giftShares minted
        (pre.accounting.supply + minted) (pre.accounting.balance + amount)
      have hgift : (pre.inboundCross attribution amount minted).giftShares =
          pre.giftShares + minted := by
        unfold PairAttackState.giftShares
        change pre.victimShares + minted - pre.lockedShares = _
        omega
      unfold PairAttackState.GiftBook at hpre ⊢
      rw [hgift]
      simp only [PairAttackState.inboundCross, PairAttackState.outflowPrice] at hmono hmonoMinted ⊢
      unfold claimN at hpre hsplit ⊢
      omega
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      exact giftBook_of_priceLe (pre := pre) ho rfl rfl rfl hprice hpre
  | delegatedWithdraw attribution shares paid hshares hpaid =>
      have hmono := payN_mono_price (shares := pre.giftShares - shares) ho hprice
      have hsub := claimN_add_le_ceil ho (pre.giftShares - shares) shares
        pre.accounting.supply pre.accounting.balance
      rw [Nat.sub_add_cancel hshares] at hsub
      have hgift : (pre.outboundDelegated attribution shares paid).giftShares =
          pre.giftShares - shares := by
        unfold PairAttackState.giftShares
        change pre.victimShares - shares - pre.lockedShares = _
        omega
      unfold PairAttackState.GiftBook at hpre ⊢
      rw [hgift]
      simp only [PairAttackState.outboundDelegated, PairAttackState.inflowPrice] at hmono ⊢
      unfold claimN at hpre hsub ⊢
      omega
  | externalCredit attribution amount =>
      exact giftBook_of_priceLe (pre := pre) ho rfl rfl rfl hprice hpre
  | shareMoveToVictim amount hamount =>
      have hsplit := claimN_add_ge o pre.giftShares amount
        pre.accounting.supply pre.accounting.balance
      have hgift : (pre.sharesToVictim amount).giftShares = pre.giftShares + amount := by
        unfold PairAttackState.giftShares
        change pre.victimShares + amount - pre.lockedShares = _
        omega
      unfold PairAttackState.GiftBook at hpre ⊢
      rw [hgift]
      simp only [PairAttackState.sharesToVictim, PairAttackState.outflowPrice]
      omega
  | shareMoveFromVictim amount hamount =>
      have hsub := claimN_add_le_ceil ho (pre.giftShares - amount) amount
        pre.accounting.supply pre.accounting.balance
      rw [Nat.sub_add_cancel hamount] at hsub
      have hgift : (pre.sharesFromVictim amount).giftShares = pre.giftShares - amount := by
        unfold PairAttackState.giftShares
        change pre.victimShares - amount - pre.lockedShares = _
        omega
      unfold PairAttackState.GiftBook at hpre ⊢
      rw [hgift]
      simp only [PairAttackState.sharesFromVictim, PairAttackState.inflowPrice]
      omega
  | shareMoveWithin side amount => exact hpre
  | victimDeposit deposit hphase hdeposit =>
      refine giftBook_of_priceLe (pre := pre) ho ?_ rfl rfl hprice hpre
      simp only [PairAttackState.giftShares, PairAttackState.lockedShares,
        PairAttackState.victimDeposited, hphase]
      omega
  | victimExit deposit exit hphase hexit =>
      refine giftBook_of_priceLe (pre := pre) ho ?_ rfl rfl hprice hpre
      simp only [PairAttackState.giftShares, PairAttackState.lockedShares,
        PairAttackState.victimExited, hphase]
      omega
  | silent => exact hpre

/-- Every classified pair step preserves the coalition claim bound. -/
theorem claimBound (ho : 2 ≤ o) {pre post : PairAttackState o} {kind : PairAttackKind}
    (effect : PairAttackEffect o pre kind post) (hpre : pre.Invariant) :
    post.ClaimBound := by
  rcases hpre with ⟨hpart, hflow, hvictim, hbook, hclaim⟩
  have ho0 : o ≠ 0 := by omega
  have hprice := effect.priceLe ho0 hpart hvictim
  have hlocked := pre.lockedShares_le hvictim
  have hnonVictim : pre.nonVictimShares ≤ pre.accounting.supply := by
    unfold ProrataAttackState.SharesPartition at hpart
    omega
  unfold PairAttackState.ClaimBound ProrataAttackState.totalIn
    ProrataAttackState.totalOut ProrataAttackState.nonVictimClaim at hclaim ⊢
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      have hstep := claimN_inbound_le ho0 hnonVictim hminted
      cases attribution <;>
        simp only [PairAttackState.inbound, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] <;> omega
  | depositToVictim attribution amount minted hminted =>
      have hstep := claimN_inbound_cross_le ho0 hnonVictim hminted
      cases attribution <;>
        simp only [PairAttackState.inboundCross, PairAttackState.outflowPrice,
          AttackAttribution.coalitionAmount, AttackAttribution.outsideAmount] <;> omega
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      have hstep := claimN_outbound_le ho0 hshares hnonVictim hpaid
      cases attribution <;>
        simp only [PairAttackState.outbound, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] <;> omega
  | delegatedWithdraw attribution shares paid hshares hpaid =>
      have hroom : pre.nonVictimShares + shares ≤ pre.accounting.supply := by
        unfold PairAttackState.giftShares at hshares
        unfold ProrataAttackState.SharesPartition at hpart
        omega
      have hstep := claimN_outbound_delegated_le ho0 hroom hpaid
      cases attribution <;>
        simp only [PairAttackState.outboundDelegated, PairAttackState.inflowPrice,
          AttackAttribution.coalitionAmount, AttackAttribution.outsideAmount] <;> omega
  | externalCredit attribution amount =>
      have hstep := claimN_externalCredit_le (o := o) (shares := pre.nonVictimShares)
        (supply := pre.accounting.supply) (balance := pre.accounting.balance)
        (amount := amount) ho0 hnonVictim
      cases attribution <;>
        simp only [PairAttackState.credited, AttackAttribution.coalitionAmount,
          AttackAttribution.outsideAmount] <;> omega
  | shareMoveToVictim amount hamount =>
      have hstep := claimN_add_ge o (pre.nonVictimShares - amount) amount
        pre.accounting.supply pre.accounting.balance
      rw [Nat.sub_add_cancel hamount] at hstep
      simp only [PairAttackState.sharesToVictim, PairAttackState.outflowPrice]
      omega
  | shareMoveFromVictim amount hamount =>
      have hstep := claimN_add_le_ceil ho0 pre.nonVictimShares amount
        pre.accounting.supply pre.accounting.balance
      simp only [PairAttackState.sharesFromVictim, PairAttackState.inflowPrice]
      omega
  | shareMoveWithin side amount => exact hclaim
  | victimDeposit deposit hphase hdeposit =>
      have hgift : pre.giftShares = pre.victimShares := by
        simp only [PairAttackState.giftShares, PairAttackState.lockedShares, hphase]
        omega
      have hmono := payN_mono_price (shares := pre.victimShares) ho0 hprice
      have hsplit := claimN_add_ge o pre.nonVictimShares pre.victimShares
        (pre.accounting.supply + deposit.minted)
        (pre.accounting.balance + deposit.amount)
      have hfull := fullSupply_claim_after_deposit_le (o := o)
        (supply := pre.accounting.supply) (balance := pre.accounting.balance)
        (amount := deposit.amount) (minted := deposit.minted) ho0
        (hdeposit ▸ deposit.minted_eq)
      unfold ProrataAttackState.SharesPartition at hpart
      rw [hpart] at hsplit
      unfold PairAttackState.GiftBook at hbook
      rw [hgift] at hbook
      unfold ProrataAttackState.FlowExact ProrataAttackState.totalIn
        ProrataAttackState.totalOut at hflow
      simp only [hphase, VictimPhase.input, VictimPhase.output] at hflow
      simp only [PairAttackState.victimDeposited, VictimDeposit.post, hdeposit] at hmono ⊢
      unfold claimN at hbook hsplit hfull ⊢
      omega
  | victimExit deposit exit hphase hexit =>
      unfold PairAttackState.VictimConsistent at hvictim
      simp only [hphase] at hvictim
      have hgift : pre.giftShares = pre.victimShares - deposit.minted := by
        simp only [PairAttackState.giftShares, PairAttackState.lockedShares, hphase]
      unfold ProrataAttackState.SharesPartition at hpart
      have hsupply : pre.accounting.supply =
          pre.nonVictimShares + pre.giftShares + deposit.minted := by
        omega
      have hdepositPrice : PriceLe o deposit.pre deposit.post := by
        simpa only [PriceLe, VictimDeposit.post, deposit.minted_eq] using
          (deposit_price_nondecreasing o deposit.amount deposit.pre.supply
            deposit.pre.balance)
      have hcurrent : PriceLe o deposit.pre
          ⟨pre.nonVictimShares + pre.giftShares + deposit.minted,
            pre.accounting.balance⟩ := by
        rw [← hsupply]
        exact PriceLe.trans ho0 hdepositPrice hvictim.2
      have hpaid : exit.payout = payN o deposit.minted
          (pre.nonVictimShares + pre.giftShares + deposit.minted)
          pre.accounting.balance := by
        rw [← hsupply, exit.payout_eq, hexit]
      have hfull := victim_full_exit_claim_le (o := o)
        (initialSupply := deposit.pre.supply) (initialBalance := deposit.pre.balance)
        (victim := deposit.amount) (minted := deposit.minted)
        (attacker := pre.nonVictimShares + pre.giftShares)
        (balance := pre.accounting.balance) (paid := exit.payout)
        ho deposit.backed deposit.minted_eq hcurrent hpaid
      have hsplit := claimN_add_ge o pre.nonVictimShares pre.giftShares
        (pre.nonVictimShares + pre.giftShares) (pre.accounting.balance - exit.payout)
      have hmono := payN_mono_price (shares := pre.giftShares) ho0 hprice
      have hsupplyAfter : pre.accounting.supply - deposit.minted =
          pre.nonVictimShares + pre.giftShares := by
        omega
      unfold PairAttackState.GiftBook at hbook
      unfold ProrataAttackState.FlowExact ProrataAttackState.totalIn
        ProrataAttackState.totalOut at hflow
      simp only [hphase, VictimPhase.input, VictimPhase.output] at hflow
      simp only [PairAttackState.victimExited, hsupplyAfter] at hmono ⊢
      unfold claimN at hbook hsplit hfull hclaim ⊢
      by_cases hbalance : deposit.amount ≤ pre.accounting.balance <;> omega
  | silent => exact hclaim

/-- Every classified pair step preserves the full overlay invariant. -/
theorem preservesInvariant (ho : 2 ≤ o) {pre post : PairAttackState o}
    {kind : PairAttackKind} (effect : PairAttackEffect o pre kind post)
    (hpre : pre.Invariant) : post.Invariant :=
  ⟨effect.sharesPartition hpre.1 hpre.2.2.1,
    effect.flowExact (by omega) hpre.1 hpre.2.2.1 hpre.2.1,
    effect.victimConsistent (by omega) hpre.1 hpre.2.2.1,
    effect.giftBook (by omega) hpre.1 hpre.2.2.1 hpre.2.2.2.1,
    effect.claimBound ho hpre⟩

end PairAttackEffect

/-- One classified pair step with retained committed chronology. -/
structure PairAttackStep (o : Nat) where
  pre : PairAttackState o
  post : PairAttackState o
  kind : PairAttackKind
  provenance : ProrataAccountingProvenance
  effect : PairAttackEffect o pre kind post

/-- A finite pair actor path from the initialized deployment boundary. -/
inductive PairAttackPath (o : Nat) : PairAttackState o → Prop where
  | genesis : PairAttackPath o (PairAttackState.genesis o)
  | snoc (step : PairAttackStep o) (path : PairAttackPath o step.pre) :
      PairAttackPath o step.post

namespace PairAttackPath

variable {o : Nat}

theorem invariant (ho : 2 ≤ o) {state : PairAttackState o}
    (path : PairAttackPath o state) : state.Invariant := by
  induction path with
  | genesis => exact PairAttackState.genesis_invariant o
  | snoc step path ih => exact step.effect.preservesInvariant ho ih

theorem claimBound (ho : 2 ≤ o) {state : PairAttackState o}
    (path : PairAttackPath o state) : state.ClaimBound :=
  (path.invariant ho).2.2.2.2

/-- Pure open-context bound: coalition cash out plus priced share outflow is
covered by coalition cash in, the outside subsidy and the priced share inflow. -/
theorem attacker_open_context_of_pairAttackPath (ho : 2 ≤ o)
    {state : PairAttackState o} (path : PairAttackPath o state) :
    state.outA + state.sharesOut ≤
      state.inA + state.outsideSubsidy + state.sharesIn := by
  have hclaim := path.claimBound ho
  unfold PairAttackState.ClaimBound ProrataAttackState.totalIn
    ProrataAttackState.totalOut at hclaim
  omega

/-- Pure closed-context no-profit bound.  Share gifts from the victim are
named, not assumed absent: the hypothesis is `sharesIn = 0`. -/
theorem attacker_no_profit_of_pairAttackPath (ho : 2 ≤ o)
    {state : PairAttackState o} (path : PairAttackPath o state)
    (hclosed : state.outsideSubsidy = 0) (hnoGifts : state.sharesIn = 0) :
    state.outA + state.sharesOut ≤ state.inA := by
  have hopen := path.attacker_open_context_of_pairAttackPath ho
  omega

/-- Pure victim-loss bound, unchanged by anything non-victims do to the victim. -/
theorem victim_loss_bound_of_pairAttackPath (ho : 2 ≤ o)
    {state : PairAttackState o} (path : PairAttackPath o state)
    {deposit : VictimDeposit o} {exit : VictimExit o deposit}
    (hphase : state.phase = .exited deposit exit) :
    deposit.amount - exit.payout ≤
      Nat.div (deposit.pre.balance + 1) (deposit.pre.supply + o) + 1 := by
  have hvictim := (path.invariant ho).2.2.1
  unfold PairAttackState.VictimConsistent at hvictim
  simp only [hphase] at hvictim
  apply victim_loss_le_div_add_one (by omega) deposit.minted_eq ?_ exit.payout_eq
  simpa only [VictimDeposit.post] using hvictim

/-- The fixed WETH port's offset discharges the guard. -/
theorem claimBound_offsetN {state : PairAttackState Blanc.ProrataWethVault.offsetN}
    (path : PairAttackPath Blanc.ProrataWethVault.offsetN state) : state.ClaimBound :=
  path.claimBound Blanc.ProrataWethVault.two_le_offsetN

end PairAttackPath

/-! ## PRORATA is the same-role fragment -/

/-- A PRORATA classification read as a pair classification with every role on
its own side. -/
def PairAttackKind.ofProrata : ProrataAttackKind → PairAttackKind
  | .nonVictimDeposit attribution amount minted =>
      .nonVictimDeposit attribution amount minted true
  | .nonVictimWithdraw attribution shares paid =>
      .nonVictimWithdraw attribution shares paid true
  | .externalCredit attribution amount => .externalCredit attribution amount
  | .victimDeposit amount minted => .victimDeposit amount minted
  | .victimExit shares paid => .victimExit shares paid
  | .silent => .silent

/-- Where the roles coincide the overlay is PRORATA's effect verbatim and the
priced totals do not move. -/
theorem PairAttackEffect.ofProrata {o : Nat} {pre post : ProrataAttackState o}
    {kind : ProrataAttackKind} (effect : ProrataAttackEffect o pre kind post)
    (sharesIn sharesOut : Nat) :
    PairAttackEffect o ⟨pre, sharesIn, sharesOut⟩ (.ofProrata kind)
      ⟨post, sharesIn, sharesOut⟩ := by
  cases effect with
  | nonVictimDeposit attribution amount minted hminted =>
      exact .nonVictimDeposit ⟨pre, sharesIn, sharesOut⟩ attribution amount minted
        (Nat.le_of_eq hminted)
  | nonVictimWithdraw attribution shares paid hshares hpaid =>
      exact .nonVictimWithdraw ⟨pre, sharesIn, sharesOut⟩ attribution shares paid
        hshares (Nat.le_of_eq hpaid)
  | externalCredit attribution amount hpositive =>
      exact .externalCredit ⟨pre, sharesIn, sharesOut⟩ attribution amount
  | victimDeposit amount minted hphase hminted hbacked =>
      exact .victimDeposit ⟨pre, sharesIn, sharesOut⟩
        ⟨pre.accounting, amount, minted, hminted, hbacked⟩ hphase rfl
  | victimExit deposit paid hphase hfull hpaid =>
      exact .victimExit ⟨pre, sharesIn, sharesOut⟩ deposit
        ⟨pre.accounting, paid, hpaid⟩ hphase rfl
  | silent => exact .silent _

/-- Every PRORATA attack path is a pair attack path with no priced crossing. -/
theorem PairAttackPath.ofProrata {o : Nat} {state : ProrataAttackState o}
    (path : ProrataAttackPath o state) : PairAttackPath o ⟨state, 0, 0⟩ := by
  induction path with
  | genesis => exact .genesis
  | snoc step path ih =>
      exact .snoc
        ⟨⟨step.pre, 0, 0⟩, ⟨step.post, 0, 0⟩, .ofProrata step.kind, step.provenance,
          .ofProrata step.effect 0 0⟩ ih

end Blanc.Composition.ProrataWethVault
