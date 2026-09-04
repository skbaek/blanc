-- ProrataWethVaultDust.lean : the port's dust and attack headlines.

import Blanc.ProrataWethVaultArithmetic
import Blanc.ProrataAttackModel
import Blanc.ProrataAttackPath

/-!
# Dust and attack headlines, WETH-denominated

The port changes the asset, not the arithmetic. `Blanc/OffsetPricing.lean`
states virtual-offset pricing over the naturals with the offset as a parameter,
and `Blanc/ProrataAttackModel.lean` proves the dust and inflation-attack
results about it. The vault's converters *are* that pricing at `offsetN`, by
`rfl` — see `convertToSharesN_eq_mintN` — so the results below are those
theorems instantiated, not restated.

That instantiation is the point. Re-proving the same inequalities in
WETH-denominated notation would have produced a second copy of an argument the
tree already carries, which is exactly what the proof-duplication ratchet
exists to prevent, and it would have left two places to be wrong.

**The carrier.** `ProrataAccountingPath offsetN` is the reachable carrier: a
connected sequence of classified steps — deposits, withdrawals, third-party
donations, and no-ops — each carrying an exact effect. Every such step weakly
increases the share price, so a whole path does, and that is what discharges
the price premise of the attack bound for an arbitrary history rather than for
a hand-picked pair.

Each class the vault can produce is exhibited below as the accounting step it
induces, so a sequence of vault operations builds a path and the history-level
results apply to it.

What is still missing is the *coalition* accounting: pricing every share and
asset movement into or out of an attacker coalition, so that an unaccounted
gift cannot be counted as attack profit. Until that lands, the bounds here are
about a single victim's round trip across a history, not about a coalition's
net position.
-/

namespace Blanc

open Jaune

namespace ProrataWethVault

/-- **Immediate round trip does not profit.** Depositing `amount` and redeeming
the shares it minted, against the same snapshot, returns at most `amount`, and
the shortfall is at most the pre-deposit price rounded up.

This is the rounding-favours-the-vault property the offset exists to guarantee,
in its exact form rather than as an inequality with slack. -/
theorem roundtrip_loss_le
    {amount assets supply : Nat} :
    amount -
        convertToAssetsN (convertToSharesN amount assets supply)
          (assets + amount)
          (supply + convertToSharesN amount assets supply) ≤
      Jaune.ceilDiv ((assets + 1) - 1) (supply + offsetN) :=
  Blanc.Prorata.immediate_roundtrip_loss_le offsetN_ne_zero

/-- **A redemption never overdraws the held assets.** A holder of at most the
whole supply is paid at most the vault's whole WETH row. -/
theorem redemption_le_assets
    {shares assets supply : Nat} (hshares : shares ≤ supply) :
    convertToAssetsN shares assets supply ≤ assets :=
  Blanc.Prorata.claimN_le_balance offsetN_ne_zero hshares

/-- **The victim's loss is bounded by the pre-attack price, plus one.**

The inflation attack's shape: a victim deposits `victim` assets into a snapshot
the attacker has already moved, and exits at a later snapshot no cheaper than
the one it entered. Whatever the attacker did in between, the victim's shortfall
is at most `(assets + 1) / (supply + offsetN) + 1` — a bound that shrinks as the
offset grows, which is what the offset buys. -/
theorem victim_loss_le
    {initialSupply initialAssets victim minted exitSupply exitAssets paid : Nat}
    (hminted : minted = convertToSharesN victim initialAssets initialSupply)
    (hprice : Blanc.Prorata.PriceLe offsetN
      ⟨initialSupply + minted, initialAssets + victim⟩
      ⟨exitSupply, exitAssets⟩)
    (hpaid : paid = convertToAssetsN minted exitAssets exitSupply) :
    victim - paid ≤
      Nat.div (initialAssets + 1) (initialSupply + offsetN) + 1 :=
  Blanc.Prorata.victim_loss_le_div_add_one offsetN_ne_zero hminted hprice hpaid



/-- **The attack bound over a whole history.**  Take any history the pricing
admits — any sequence of deposits, withdrawals, third-party donations and
no-ops — beginning immediately after a victim's deposit.  However the attacker
arranges it, the victim's shortfall on exiting at the end is at most the
pre-deposit price plus one.

The price premise is discharged by the carrier rather than assumed: every
classified step weakly increases the price, so the path does. -/
theorem victim_loss_le_over_history
    {initialSupply initialAssets victim minted paid : Nat}
    (path : Blanc.Prorata.ProrataAccountingPath offsetN)
    (hminted : minted = convertToSharesN victim initialAssets initialSupply)
    (hstart : path.first =
      ⟨initialSupply + minted, initialAssets + victim⟩)
    (hpaid : paid =
      convertToAssetsN minted path.last.balance path.last.supply) :
    victim - paid ≤
      Nat.div (initialAssets + 1) (initialSupply + offsetN) + 1 := by
  refine victim_loss_le hminted ?_ hpaid
  rw [← hstart]
  exact Blanc.Prorata.ProrataAccountingPath.priceLe_first_last
    offsetN_ne_zero path

/-- **Cumulative rounding residue over a whole history, exactly.**

Not a bound: an equality.  The numerator at the end of a history, scaled by the
product of the denominators along it, is the initial numerator scaled the same
way plus the exact sum of the per-step residues, each weighted by the
denominators on either side of it.  This is the port's dust accounting, and it
is the ETH-denominated statement at `offsetN` because the arithmetic is the
same. -/
theorem dust_trace_exact
    (path : Blanc.Prorata.ProrataAccountingPath offsetN) :
    let n := path.steps.length
    path.XAt n * (∏ j ∈ Finset.range n, path.DAt j) =
      path.XAt 0 * (∏ j ∈ Finset.Icc 1 n, path.DAt j) +
        ∑ i ∈ Finset.range n,
          (path.rhoAt i + path.kappaAt i) *
            (∏ j ∈ Finset.range i, path.DAt j) *
              (∏ j ∈ Finset.Icc (i + 2) n, path.DAt j) :=
  Blanc.Prorata.ProrataAccountingPath.prorata_dust_trace_exact
    offsetN_ne_zero path



/-! ## Vault operations are accounting steps

The three classes the vault can produce, each exhibited as the accounting step
it induces at `offsetN`.  With these, a sequence of vault operations builds a
`ProrataAccountingPath`, and the history-level results above apply to it.

The compiled effect theorems already state the vault's supply and asset
transitions in exactly these terms — `deposit_compiled_effect` concludes with
`convertToSharesN`, and the outbound pair with `convertToAssetsN` — so the
bridges are the constructors applied to the pricing equalities, with no
arithmetic of their own. -/

/-- A deposit or mint is a `deposit` step: supply and assets each rise by the
quoted amount. -/
theorem depositStep (amount assets supply : Nat) :
    Blanc.Prorata.ProrataAccountingEffect offsetN
      ⟨supply, assets⟩
      (.deposit amount (convertToSharesN amount assets supply))
      ⟨supply + convertToSharesN amount assets supply, assets + amount⟩ :=
  Blanc.Prorata.ProrataAccountingEffect.deposit supply assets amount _
    (convertToSharesN_eq_mintN amount assets supply)

/-- A redemption is a `withdraw` step, for a holder whose shares are part of the
accounted supply. -/
theorem redeemStep {shares : Nat} (assets supply : Nat)
    (hshares : shares ≤ supply) :
    Blanc.Prorata.ProrataAccountingEffect offsetN
      ⟨supply, assets⟩
      (.withdraw shares (convertToAssetsN shares assets supply))
      ⟨supply - shares, assets - convertToAssetsN shares assets supply⟩ :=
  Blanc.Prorata.ProrataAccountingEffect.withdraw supply assets shares _ hshares
    (convertToAssetsN_eq_payN shares assets supply)

/-- A third-party WETH transfer to the vault is an `externalCredit` step: the
assets rise and no share is minted.  This is the donation classification, in
the carrier's own vocabulary. -/
theorem donationStep {amount : Nat} (assets supply : Nat)
    (hpositive : 0 < amount) :
    Blanc.Prorata.ProrataAccountingEffect offsetN
      ⟨supply, assets⟩ (.externalCredit amount)
      ⟨supply, assets + amount⟩ :=
  Blanc.Prorata.ProrataAccountingEffect.externalCredit supply assets amount
    hpositive



/-! ## The P4 headlines, coalition-priced

`Blanc/ProrataAttackPath.lean` carries the attacker/victim bookkeeping: an
attack state records everything the coalition put in (`inA`), everything it
took out (`outA`), and — separately — every asset that entered the coalition
from outside it (`outsideSubsidy`). Pricing the outside gift explicitly is what
stops an unaccounted transfer from being read as attack profit.

The three headlines below are those results at `offsetN`. None of them carries
a callee-honesty or no-donation premise: donations are a step class the carrier
already admits, and the open-context bound prices them rather than excluding
them. -/

/-- The offset is at least two, which is the guard the no-profit bounds carry. -/
theorem two_le_offsetN : 2 ≤ offsetN := by decide

/-- **Open context.**  Whatever the coalition takes out is at most what it put
in, plus whatever it was given from outside.  A gift cannot masquerade as
profit because it is on the right-hand side by name. -/
theorem attacker_open_context
    {state : Blanc.Prorata.ProrataAttackState offsetN}
    (path : Blanc.Prorata.ProrataAttackPath offsetN state) :
    state.outA ≤ state.inA + state.outsideSubsidy :=
  path.attacker_open_context_of_attackPath two_le_offsetN

/-- **No profit in a closed context.**  With no outside subsidy, the coalition
cannot end ahead. -/
theorem attacker_no_profit
    {state : Blanc.Prorata.ProrataAttackState offsetN}
    (path : Blanc.Prorata.ProrataAttackPath offsetN state)
    (hclosed : state.outsideSubsidy = 0) :
    state.outA ≤ state.inA :=
  path.attacker_no_profit_of_attackPath two_le_offsetN hclosed

/-- **Victim loss, over an attack path.**  A victim who has deposited and
exited loses at most the pre-deposit price plus one, whatever the coalition did
in between. -/
theorem victim_loss_bound
    {state : Blanc.Prorata.ProrataAttackState offsetN}
    (path : Blanc.Prorata.ProrataAttackPath offsetN state)
    {deposit : Blanc.Prorata.VictimDeposit offsetN}
    {exit : Blanc.Prorata.VictimExit offsetN deposit}
    (hphase : state.phase = .exited deposit exit) :
    deposit.amount - exit.payout ≤
      Nat.div (deposit.pre.balance + 1) (deposit.pre.supply + offsetN) + 1 :=
  path.victim_loss_bound_of_attackPath offsetN_ne_zero hphase



/-! ## The carrier is inhabited

A concrete first-depositor inflation trace, built from the constructors so that
Lean computes every intermediate state.  It exists to rule out the failure mode
where the headlines above are true only because nothing satisfies their
hypotheses.

The numbers are the ones the independent oracle predicts for the same
transcript, and the same ones the ETH-denominated PRORATA oracle froze: the
coalition seeds one wei, donates a million, the victim deposits a million and
is minted 1999 shares, and the coalition's exit pays it 500125 against the
1000001 it put in — a loss, not a profit, which is what the offset buys. -/

/-- The coalition seeds the vault, donates, the victim deposits, the coalition
exits, and the victim exits.

Built one step at a time rather than as a single nested term: each `have` fully
elaborates before the next, so every side condition sees the concrete state its
step runs from.  The intermediate states are computed by the constructors and
never written out. -/
theorem attack_carrier_inhabited :
    ∃ state : Blanc.Prorata.ProrataAttackState offsetN,
      Blanc.Prorata.ProrataAttackPath offsetN state ∧
        state.inA = 1000001 ∧ state.outA = 500125 ∧
        state.outsideSubsidy = 0 := by
  have prov : Blanc.Prorata.ProrataAccountingProvenance := ⟨0, none, [], none⟩
  -- The coalition seeds one wei and is minted the offset's worth of shares.
  have p1 : Blanc.Prorata.ProrataAttackPath offsetN _ :=
    .snoc ⟨_, _, _, prov,
      .nonVictimDeposit
        (Blanc.Prorata.ProrataAttackState.genesis offsetN)
        .coalition 1 1000 (by norm_num [offsetN, Blanc.Prorata.ProrataAttackState.genesis,
          Blanc.Prorata.mintN, Blanc.Prorata.payN])⟩ .genesis
  -- and donates a million, which moves the price and not the supply.
  have p2 : Blanc.Prorata.ProrataAttackPath offsetN _ :=
    .snoc ⟨_, _, _, prov,
      .externalCredit _ .coalition 1000000 (by decide)⟩ p1
  -- The victim deposits a million into the moved price.
  have p3 : Blanc.Prorata.ProrataAttackPath offsetN _ :=
    .snoc ⟨_, _, _, prov,
      .victimDeposit _ 1000000 1999 rfl (by norm_num [offsetN, Blanc.Prorata.ProrataAttackState.genesis,
          Blanc.Prorata.mintN, Blanc.Prorata.payN])
        (by norm_num [offsetN, Blanc.Prorata.ProrataAttackState.genesis,
          Blanc.Prorata.mintN, Blanc.Prorata.payN])⟩ p2
  -- The coalition exits.
  have p4 : Blanc.Prorata.ProrataAttackPath offsetN _ :=
    .snoc ⟨_, _, _, prov,
      .nonVictimWithdraw _ .coalition 1000 500125 (by norm_num [offsetN, Blanc.Prorata.ProrataAttackState.genesis,
          Blanc.Prorata.mintN, Blanc.Prorata.payN])
        (by norm_num [offsetN, Blanc.Prorata.ProrataAttackState.genesis,
          Blanc.Prorata.mintN, Blanc.Prorata.payN])⟩ p3
  refine ⟨_, p4, ?_, ?_, ?_⟩ <;>
    simp [offsetN, Blanc.Prorata.ProrataAttackState.genesis,
      Blanc.Prorata.AttackAttribution.coalitionAmount,
      Blanc.Prorata.AttackAttribution.outsideAmount,
      Blanc.Prorata.mintN, Blanc.Prorata.payN]

end ProrataWethVault

end Blanc
