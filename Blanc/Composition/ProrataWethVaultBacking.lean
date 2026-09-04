import Blanc.Composition.ProrataWethVaultInbound
import Blanc.Composition.ProrataWethVaultOutbound
import Blanc.ProrataAccounting
import Blanc.ProrataWethVaultDust
import Blanc.ProrataWethVaultShares
import Blanc.ProrataWethVaultLedgerSpec

/-!
# The joint two-contract backing invariant

The vault issues shares against WETH it holds in WETH's own ledger.  Nothing
about that relation is visible to either contract alone: the vault's storage
knows the supply, WETH's storage knows the balance, and only a statement over
both can say the shares are backed.

The invariant has three conjuncts.  The first is ledger conservation inside the
vault.  The second is the arithmetic cap the vault's own guards maintain.  The
third is the backing bound proper, and it is the only one that mentions WETH.

The bound is `supply ≤ offset * assets` and it is exactly what makes every
share redeemable: with the virtual offset, redeeming the whole supply pays
`supply * (assets + 1) / (supply + offset)`, and that is at most `assets`
precisely when the bound holds.  `backing_corollary` is that calculation.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Source

/-- Total issued shares, read from the vault's distinguished supply slot. -/
def supplyN (s : Stor) : Nat :=
  (s.get Blanc.ProrataWethVault.supplySlot).toNat

/-- The joint invariant: the vault's share ledger is conserved, its supply
respects the arithmetic cap, and the supply is backed by the WETH row the
vault holds in WETH's own ledger. -/
def PairBacked (vault : Adr) (vaultStor wethStor : Stor) : Prop :=
  LedgerConserved Blanc.ProrataWethVault.supplySlot vaultStor ∧
    supplyN vaultStor ≤ Blanc.ProrataWethVault.maxSupplyN ∧
    supplyN vaultStor ≤
      Blanc.ProrataWethVault.offsetN * (Stor.rest wethStor vault).toNat

/-- **The backing corollary.**  Redeeming the entire supply pays at most the
WETH the vault actually holds.  This is the statement the invariant exists to
support, and it is where the virtual offset earns its place: without it the
bound would be an equality that rounding could break. -/
theorem PairBacked.redeemable {vault : Adr} {vaultStor wethStor : Stor}
    (h : PairBacked vault vaultStor wethStor) :
    Blanc.ProrataWethVault.convertToAssetsN (supplyN vaultStor)
        (Stor.rest wethStor vault).toNat (supplyN vaultStor) ≤
      (Stor.rest wethStor vault).toNat := by
  obtain ⟨-, -, backed⟩ := h
  unfold Blanc.ProrataWethVault.convertToAssetsN
    Blanc.ProrataWethVault.assetFactorN Blanc.ProrataWethVault.denominatorN
  refine Nat.div_le_of_le_mul ?_
  have expand :
      supplyN vaultStor * ((Stor.rest wethStor vault).toNat + 1) =
        supplyN vaultStor * (Stor.rest wethStor vault).toNat +
          supplyN vaultStor := by
    ring
  have target :
      (supplyN vaultStor + Blanc.ProrataWethVault.offsetN) *
          (Stor.rest wethStor vault).toNat =
        supplyN vaultStor * (Stor.rest wethStor vault).toNat +
          Blanc.ProrataWethVault.offsetN *
            (Stor.rest wethStor vault).toNat := by
    ring
  rw [expand, target]
  omega

/-! ## The two arithmetic bounds preservation rests on

Both are statements about the floor-divided quote alone.  They are where the
invariant is actually earned; everything above and below them is bookkeeping. -/

/-- A deposit mints at most `offset` shares per asset it brings.  This is the
mint side of preservation, and it is exactly the invariant fed back through the
quote: the price cannot be better than the bound already guarantees. -/
theorem mint_bound {supply weth amount shares : Nat}
    (backed : supply ≤ Blanc.ProrataWethVault.offsetN * weth)
    (quote : shares * (weth + 1) ≤ amount * (supply +
      Blanc.ProrataWethVault.offsetN)) :
    shares ≤ Blanc.ProrataWethVault.offsetN * amount := by
  by_contra tooMany
  have big : Blanc.ProrataWethVault.offsetN * amount + 1 ≤ shares := by omega
  have step : (Blanc.ProrataWethVault.offsetN * amount + 1) * (weth + 1) ≤
      amount * (supply + Blanc.ProrataWethVault.offsetN) :=
    le_trans (Nat.mul_le_mul_right _ big) quote
  have cap : amount * (supply + Blanc.ProrataWethVault.offsetN) ≤
      Blanc.ProrataWethVault.offsetN * amount * (weth + 1) := by
    have inner : supply + Blanc.ProrataWethVault.offsetN ≤
        Blanc.ProrataWethVault.offsetN * (weth + 1) := by
      have : Blanc.ProrataWethVault.offsetN * (weth + 1) =
          Blanc.ProrataWethVault.offsetN * weth +
            Blanc.ProrataWethVault.offsetN := by ring
      omega
    calc amount * (supply + Blanc.ProrataWethVault.offsetN)
        ≤ amount * (Blanc.ProrataWethVault.offsetN * (weth + 1)) :=
          Nat.mul_le_mul_left _ inner
      _ = Blanc.ProrataWethVault.offsetN * amount * (weth + 1) := by ring
  have collapse : (Blanc.ProrataWethVault.offsetN * amount + 1) * (weth + 1) ≤
      Blanc.ProrataWethVault.offsetN * amount * (weth + 1) :=
    le_trans step cap
  have expand : (Blanc.ProrataWethVault.offsetN * amount + 1) * (weth + 1) =
      Blanc.ProrataWethVault.offsetN * amount * (weth + 1) + (weth + 1) := by
    ring
  omega

/-- A redemption pays out little enough to keep the bound.  Stated additively
so no truncated subtraction appears: `supply + offset * assets ≤ offset * weth
+ shares` is the subtraction-free form of "the remaining supply is still backed
by the remaining WETH". -/
theorem burn_bound {supply weth shares assets : Nat}
    (backed : supply ≤ Blanc.ProrataWethVault.offsetN * weth)
    (burnable : shares ≤ supply)
    (quote : assets * (supply + Blanc.ProrataWethVault.offsetN) ≤
      shares * (weth + 1)) :
    supply + Blanc.ProrataWethVault.offsetN * assets ≤
      Blanc.ProrataWethVault.offsetN * weth + shares := by
  obtain ⟨slack, slackEq⟩ : ∃ slack,
      Blanc.ProrataWethVault.offsetN * weth = supply + slack :=
    ⟨Blanc.ProrataWethVault.offsetN * weth - supply, by omega⟩
  -- It suffices to bound `offset * assets` by `shares + slack`.
  have goal : Blanc.ProrataWethVault.offsetN * assets ≤ shares + slack := by
    have positive : 0 < supply + Blanc.ProrataWethVault.offsetN := by
      unfold Blanc.ProrataWethVault.offsetN
      omega
    refine Nat.le_of_mul_le_mul_right ?_ positive
    have left :
        Blanc.ProrataWethVault.offsetN * assets *
            (supply + Blanc.ProrataWethVault.offsetN) ≤
          Blanc.ProrataWethVault.offsetN * (shares * (weth + 1)) := by
      calc Blanc.ProrataWethVault.offsetN * assets *
            (supply + Blanc.ProrataWethVault.offsetN)
          = Blanc.ProrataWethVault.offsetN *
              (assets * (supply + Blanc.ProrataWethVault.offsetN)) := by ring
        _ ≤ Blanc.ProrataWethVault.offsetN * (shares * (weth + 1)) :=
            Nat.mul_le_mul_left _ quote
    have middle : Blanc.ProrataWethVault.offsetN * (shares * (weth + 1)) =
        shares * (supply + slack) + Blanc.ProrataWethVault.offsetN * shares := by
      calc Blanc.ProrataWethVault.offsetN * (shares * (weth + 1))
          = shares * (Blanc.ProrataWethVault.offsetN * weth) +
              Blanc.ProrataWethVault.offsetN * shares := by ring
        _ = shares * (supply + slack) +
              Blanc.ProrataWethVault.offsetN * shares := by rw [slackEq]
    have right : shares * (supply + slack) +
          Blanc.ProrataWethVault.offsetN * shares ≤
        (shares + slack) * (supply + Blanc.ProrataWethVault.offsetN) := by
      have expand : (shares + slack) *
          (supply + Blanc.ProrataWethVault.offsetN) =
          shares * supply + Blanc.ProrataWethVault.offsetN * shares +
            slack * (supply + Blanc.ProrataWethVault.offsetN) := by ring
      have inner : shares * slack ≤
          slack * (supply + Blanc.ProrataWethVault.offsetN) := by
        calc shares * slack = slack * shares := by ring
          _ ≤ slack * (supply + Blanc.ProrataWethVault.offsetN) :=
              Nat.mul_le_mul_left _ (by omega)
      have lhs : shares * (supply + slack) +
          Blanc.ProrataWethVault.offsetN * shares =
          shares * supply + shares * slack +
            Blanc.ProrataWethVault.offsetN * shares := by ring
      omega
    calc Blanc.ProrataWethVault.offsetN * assets *
          (supply + Blanc.ProrataWethVault.offsetN)
        ≤ Blanc.ProrataWethVault.offsetN * (shares * (weth + 1)) := left
      _ = shares * (supply + slack) +
            Blanc.ProrataWethVault.offsetN * shares := middle
      _ ≤ (shares + slack) * (supply + Blanc.ProrataWethVault.offsetN) := right
  omega

/-- **Genesis.**  A vault whose storage reads zero everywhere is backed, for
any WETH ledger: it has issued no shares. -/
theorem PairBacked.of_vault_empty {vault : Adr} {vaultStor wethStor : Stor}
    (h : ∀ k, vaultStor.get k = 0) :
    PairBacked vault vaultStor wethStor := by
  refine ⟨LedgerConserved.of_get_eq_zero h, ?_, ?_⟩
  · show (vaultStor.get Blanc.ProrataWethVault.supplySlot).toNat ≤ _
    rw [h, show ((0 : B256)).toNat = 0 by decide +kernel]
    exact Nat.zero_le _
  · show (vaultStor.get Blanc.ProrataWethVault.supplySlot).toNat ≤ _
    rw [h, show ((0 : B256)).toNat = 0 by decide +kernel]
    exact Nat.zero_le _

/-- The credited side of a transfer between two distinct accounts. -/
theorem credited_of_transfer {b d : Adr → B256} {kd ki : Adr} {v : B256}
    (h : Transfer b kd v ki d) (distinct : kd ≠ ki) :
    d ki = b ki + v := by
  obtain ⟨-, c, decrease, increase⟩ := h
  have middle : b ki = c ki := (decrease ki).2 distinct
  have credited : c ki + v = d ki := (increase ki).1 rfl
  rw [middle, credited]

/-- The debited side of a transfer between two distinct accounts. -/
theorem debited_of_transfer {b d : Adr → B256} {kd ki : Adr} {v : B256}
    (h : Transfer b kd v ki d) (distinct : kd ≠ ki) :
    b kd = d kd + v := by
  obtain ⟨-, c, decrease, increase⟩ := h
  have debited : b kd - v = c kd := (decrease kd).1 rfl
  have untouched : c kd = d kd := (increase kd).2 (Ne.symm distinct)
  have expand : (b kd - v) + v = b kd := B256.sub_add_cancel
  rw [← untouched, ← debited, expand]

/-- The debited side of a transfer, in subtraction form. -/
theorem debitedSub_of_transfer {b d : Adr → B256} {kd ki : Adr} {v : B256}
    (h : Transfer b kd v ki d) (distinct : kd ≠ ki) :
    d kd = b kd - v := by
  obtain ⟨-, c, decrease, increase⟩ := h
  have debited : b kd - v = c kd := (decrease kd).1 rfl
  have untouched : c kd = d kd := (increase kd).2 (Ne.symm distinct)
  rw [← untouched, ← debited]

/-- **Donation.**  A third-party WETH transfer *into* the vault can only help:
the backing bound is monotone in the WETH row, so a rise in that row preserves
the invariant with the vault's own storage untouched. -/
theorem PairBacked.donation {vault : Adr} {vaultStor wethStor wethStor' : Stor}
    (h : PairBacked vault vaultStor wethStor)
    (rise : (Stor.rest wethStor vault).toNat ≤
      (Stor.rest wethStor' vault).toNat) :
    PairBacked vault vaultStor wethStor' := by
  obtain ⟨conserved, capped, backed⟩ := h
  exact ⟨conserved, capped, le_trans backed (Nat.mul_le_mul_left _ rise)⟩

/-! ## Preservation -/

/-- An inbound flow preserves the joint invariant.

Two premises are honest side conditions rather than hidden assumptions.  The
depositor must not be the vault itself: a self-deposit nets to zero in WETH's
ledger while still minting shares, and no arithmetic could rescue the bound
from that.  And WETH's own balance sum must not overflow a word — that is
WETH's solvency, which is precisely the predicate G6 asks this invariant to be
coupled with, and it is what bounds the vault's credited row. -/
theorem inboundEffect_preserves_backed
    {sevm : Sevm} {pre post : Devm}
    {receiver assets shares returned supply : B256}
    (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
    (receiverValid : ValidAdr receiver)
    (wethSumNof : SumNof (Stor.rest (Devm.getStor pre wethAccount)))
    (supplyEq : supply = Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (roomFits : shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat)
    (quote : shares.toNat *
        ((Stor.rest (Devm.getStor pre wethAccount)
          sevm.currentTarget).toNat + 1) ≤
      assets.toNat * (supply.toNat + Blanc.ProrataWethVault.offsetN))
    (effect : InboundEffect sevm receiver assets shares returned pre post)
    (backed : PairBacked sevm.currentTarget
      (Devm.getStor pre sevm.currentTarget)
      (Devm.getStor pre wethAccount)) :
    PairBacked sevm.currentTarget
      (Devm.getStor post sevm.currentTarget)
      (Devm.getStor post wethAccount) := by
  obtain ⟨conserved, capped, bound⟩ := backed
  have effectWhole := effect
  obtain ⟨-, movement, vaultStorage, -, -⟩ := effect
  have roomNat : Blanc.ProrataWethVault.shareRoomN supply.toNat =
      Blanc.ProrataWethVault.maxSupplyN - supply.toNat := rfl
  have maxLt : Blanc.ProrataWethVault.maxSupplyN < 2 ^ 256 := by
    unfold Blanc.ProrataWethVault.maxSupplyN maxWordN wordModulusN
    omega
  have supplyNat : supplyN (Devm.getStor pre sevm.currentTarget) =
      supply.toNat := congrArg B256.toNat supplyEq.symm
  have supplyNof : B256.Nof supply shares := by
    unfold B256.Nof
    rw [roomNat] at roomFits
    omega
  have supplyAfter : supplyN (Devm.getStor post sevm.currentTarget) =
      supply.toNat + shares.toNat := by
    show (_ : B256).toNat = _
    rw [vaultStorage, Stor.get_set_self, ← supplyEq]
    exact B256.toNat_add_eq_of_nof _ _ supplyNof
  -- The credited WETH row cannot wrap, because WETH's own sum does not.
  have covered : assets ≤
      Stor.rest (Devm.getStor pre wethAccount) sevm.caller := movement.1
  have pairBound :
      (Stor.rest (Devm.getStor pre wethAccount) sevm.caller).toNat +
        (Stor.rest (Devm.getStor pre wethAccount)
          sevm.currentTarget).toNat ≤
        sum (Stor.rest (Devm.getStor pre wethAccount)) :=
    add_le_sum_of_ne _ depositorNotVault
  have rowNof : B256.Nof
      (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget) assets := by
    unfold B256.Nof
    have coveredNat := B256.toNat_le_toNat covered
    have sumLt : sum (Stor.rest (Devm.getStor pre wethAccount)) < 2 ^ 256 :=
      wethSumNof
    omega
  have wethNat : (Stor.rest (Devm.getStor post wethAccount)
      sevm.currentTarget).toNat =
      (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat +
        assets.toNat := by
    rw [credited_of_transfer movement depositorNotVault]
    exact B256.toNat_add_eq_of_nof _ _ rowNof
  -- The mint bound is the invariant fed back through the quote.
  have mintable : shares.toNat ≤
      Blanc.ProrataWethVault.offsetN * assets.toNat := by
    refine mint_bound (supply := supply.toNat) ?_ quote
    rw [← supplyNat]
    exact bound
  refine ⟨?_, ?_, ?_⟩
  · exact inboundEffect_preserves_conserved receiverValid supplyEq stable
      roomFits effectWhole conserved
  · rw [supplyAfter]
    rw [roomNat] at roomFits
    omega
  · rw [supplyAfter, wethNat]
    have expand : Blanc.ProrataWethVault.offsetN *
        ((Stor.rest (Devm.getStor pre wethAccount)
          sevm.currentTarget).toNat + assets.toNat) =
        Blanc.ProrataWethVault.offsetN *
          (Stor.rest (Devm.getStor pre wethAccount)
            sevm.currentTarget).toNat +
          Blanc.ProrataWethVault.offsetN * assets.toNat := by ring
    rw [supplyNat] at bound
    omega

/-- A share operation preserves the joint invariant for the simplest possible
reason: it moves no WETH and leaves the supply where it was, so only the
conservation conjunct has any work to do. -/
theorem PairBacked.of_share_operation {vault : Adr}
    {vaultStor vaultStor' wethStor wethStor' : Stor}
    (h : PairBacked vault vaultStor wethStor)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot vaultStor')
    (supplyKept : vaultStor'.get Blanc.ProrataWethVault.supplySlot =
      vaultStor.get Blanc.ProrataWethVault.supplySlot)
    (wethKept : wethStor' = wethStor) :
    PairBacked vault vaultStor' wethStor' := by
  obtain ⟨-, capped, bound⟩ := h
  subst wethKept
  refine ⟨conserved, ?_, ?_⟩
  · show (vaultStor'.get _).toNat ≤ _
    rw [supplyKept]
    exact capped
  · show (vaultStor'.get _).toNat ≤ _
    rw [supplyKept]
    exact bound

/-- An outbound flow preserves the joint invariant.

As with the inbound direction the receiver must not be the vault: paying
yourself nets to zero in WETH's ledger while still burning shares, which would
*strengthen* the bound rather than break it, but the transfer projections only
speak about distinct accounts. -/
theorem outboundEffect_preserves_backed
    {sevm : Sevm} {pre post : Devm}
    {receiver owner assets shares returned : B256}
    (receiverNotVault : sevm.currentTarget ≠ receiver.toAdr)
    (ownerValid : ValidAdr owner)
    (covered : shares.toNat ≤
      (Devm.getStorVal pre sevm.currentTarget owner).toNat)
    (burnable : shares.toNat ≤ supplyN (Devm.getStor pre sevm.currentTarget))
    (quote : assets.toNat *
        (supplyN (Devm.getStor pre sevm.currentTarget) +
          Blanc.ProrataWethVault.offsetN) ≤
      shares.toNat *
        ((Stor.rest (Devm.getStor pre wethAccount)
          sevm.currentTarget).toNat + 1))
    (effect :
      OutboundEffect sevm receiver owner assets shares returned pre post)
    (backed : PairBacked sevm.currentTarget
      (Devm.getStor pre sevm.currentTarget)
      (Devm.getStor pre wethAccount)) :
    PairBacked sevm.currentTarget
      (Devm.getStor post sevm.currentTarget)
      (Devm.getStor post wethAccount) := by
  obtain ⟨conserved, capped, bound⟩ := backed
  have effectWhole := effect
  obtain ⟨-, movement, -, supplyRow, -, -, -, -⟩ := effect
  have wethCovered : assets ≤
      Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget :=
    movement.1
  have wethAfter : Stor.rest (Devm.getStor post wethAccount)
      sevm.currentTarget =
      Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget - assets :=
    debitedSub_of_transfer movement receiverNotVault
  have wethNat : (Stor.rest (Devm.getStor post wethAccount)
      sevm.currentTarget).toNat =
      (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat -
        assets.toNat := by
    rw [wethAfter]
    exact B256.toNat_sub_eq_of_le _ _ wethCovered
  have supplyAfter : supplyN (Devm.getStor post sevm.currentTarget) =
      supplyN (Devm.getStor pre sevm.currentTarget) - shares.toNat := by
    show (Devm.getStorVal post sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat = _
    rw [supplyRow]
    exact B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat burnable)
  have keeps : supplyN (Devm.getStor pre sevm.currentTarget) +
      Blanc.ProrataWethVault.offsetN * assets.toNat ≤
      Blanc.ProrataWethVault.offsetN *
        (Stor.rest (Devm.getStor pre wethAccount)
          sevm.currentTarget).toNat + shares.toNat :=
    burn_bound bound burnable quote
  refine ⟨?_, ?_, ?_⟩
  · exact outboundEffect_preserves_conserved ownerValid covered effectWhole
      conserved
  · rw [supplyAfter]
    omega
  · rw [supplyAfter, wethNat]
    have shrink : Blanc.ProrataWethVault.offsetN *
        ((Stor.rest (Devm.getStor pre wethAccount)
          sevm.currentTarget).toNat - assets.toNat) =
        Blanc.ProrataWethVault.offsetN *
          (Stor.rest (Devm.getStor pre wethAccount)
            sevm.currentTarget).toNat -
          Blanc.ProrataWethVault.offsetN * assets.toNat := by
      rw [Nat.mul_sub]
    have coveredNat := B256.toNat_le_toNat wethCovered
    omega


/-! ## The pair's own accounting snapshot

The carrier in `Blanc/ProrataAccounting.lean` is a sequence of steps over
`⟨supply, balance⟩`. For this port the supply is the vault's own supply word
and the balance is the vault's *row in WETH's storage* — the two accounts the
invariant spans. Reading that pair off a machine state is what lets a compiled
vault execution be exhibited as an accounting step, and so lets the attack and
dust results in `Blanc/ProrataWethVaultDust.lean` speak about histories the
deployed pair can produce rather than histories the arithmetic merely admits. -/

/-- The accounting snapshot the vault and WETH jointly present at a state. -/
def snapshotAt (sevm : Sevm) (state : Devm) : Blanc.Prorata.AccountingSnapshot :=
  ⟨(Devm.getStorVal state sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat,
   (Stor.rest (Devm.getStor state wethAccount) sevm.currentTarget).toNat⟩

/-- **A successful inbound flow is a `deposit` accounting step.**

The two non-wrap premises are the ones the backing proof already establishes at
this boundary, and they are stated rather than re-derived so that this theorem
says only what it is for: the pair's snapshot moves exactly the way the carrier
says a deposit moves it. -/
theorem inboundEffect_accountingStep
    {sevm : Sevm} {pre post : Devm}
    {receiver assets shares returned : B256}
    (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
    (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) shares)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
      sevm.currentTarget) assets)
    (effect : InboundEffect sevm receiver assets shares returned pre post)
    (quote : shares.toNat =
      Blanc.ProrataWethVault.convertToSharesN assets.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply) :
    Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre)
      (.deposit assets.toNat shares.toNat)
      (snapshotAt sevm post) := by
  obtain ⟨-, movement, vaultStorage, -, -⟩ := effect
  have supplyAfter : (snapshotAt sevm post).supply =
      (snapshotAt sevm pre).supply + shares.toNat := by
    show ((Devm.getStor post sevm.currentTarget).get
      Blanc.ProrataWethVault.supplySlot).toNat = _
    rw [vaultStorage, Stor.get_set_self]
    exact B256.toNat_add_eq_of_nof _ _ supplyNof
  have balanceAfter : (snapshotAt sevm post).balance =
      (snapshotAt sevm pre).balance + assets.toNat := by
    show (Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget).toNat = _
    rw [credited_of_transfer movement depositorNotVault]
    exact B256.toNat_add_eq_of_nof _ _ rowNof
  have shape : snapshotAt sevm post =
      ⟨(snapshotAt sevm pre).supply + shares.toNat,
        (snapshotAt sevm pre).balance + assets.toNat⟩ :=
    congrArg₂ Blanc.Prorata.AccountingSnapshot.mk supplyAfter balanceAfter
  rw [shape, quote]
  exact Blanc.ProrataWethVault.depositStep assets.toNat
    (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply


/-- **A successful outbound flow is a `withdraw` accounting step.**

The mirror of the inbound bridge: the supply and the vault's WETH row each fall
by exactly the burned and paid amounts, which is how the carrier's `withdraw`
moves a snapshot.  `shares ≤ supply` is the carrier's own side condition and is
the burn coverage the outbound effect already needs. -/
theorem outboundEffect_accountingStep
    {sevm : Sevm} {pre post : Devm}
    {receiver owner assets shares returned : B256}
    (receiverNotVault : sevm.currentTarget ≠ receiver.toAdr)
    (burnable : shares.toNat ≤ (snapshotAt sevm pre).supply)
    (covered : assets.toNat ≤ (snapshotAt sevm pre).balance)
    (effect : OutboundEffect sevm receiver owner assets shares returned pre post)
    (quote : assets.toNat =
      Blanc.ProrataWethVault.convertToAssetsN shares.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply) :
    Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre)
      (.withdraw shares.toNat assets.toNat)
      (snapshotAt sevm post) := by
  obtain ⟨-, movement, -, supplyRow, -, -, -, -⟩ := effect
  have supplyAfter : (snapshotAt sevm post).supply =
      (snapshotAt sevm pre).supply - shares.toNat := by
    show (Devm.getStorVal post sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat = _
    rw [supplyRow]
    exact B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat burnable)
  have balanceAfter : (snapshotAt sevm post).balance =
      (snapshotAt sevm pre).balance - assets.toNat := by
    show (Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget).toNat = _
    rw [debitedSub_of_transfer movement receiverNotVault]
    exact B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat covered)
  have shape : snapshotAt sevm post =
      ⟨(snapshotAt sevm pre).supply - shares.toNat,
        (snapshotAt sevm pre).balance - assets.toNat⟩ :=
    congrArg₂ Blanc.Prorata.AccountingSnapshot.mk supplyAfter balanceAfter
  rw [shape, quote]
  exact Blanc.ProrataWethVault.redeemStep (snapshotAt sevm pre).balance
    (snapshotAt sevm pre).supply burnable


/-- **A step that moves neither the supply word nor the vault's WETH row is a
`silent` accounting step.**

This is what carries the share surface into the carrier.  A share transfer, a
`transferFrom` and an approval all rearrange the vault's own storage without
touching either coordinate the snapshot reads, so the carrier sees them as
no-ops — which is the honest classification, not a convenience: they move no
value between the vault and its asset. -/
theorem silent_accountingStep
    {sevm : Sevm} {pre post : Devm}
    (distinct : wethAccount ≠ sevm.currentTarget)
    (supplyKept : Devm.getStorVal post sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot =
      Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot)
    (foreign : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor post account = Devm.getStor pre account) :
    Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre) .silent (snapshotAt sevm post) := by
  have shape : snapshotAt sevm post = snapshotAt sevm pre := by
    refine congrArg₂ Blanc.Prorata.AccountingSnapshot.mk ?_ ?_
    · show (Devm.getStorVal post sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat = _
      rw [supplyKept]
    · show (Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget).toNat
        = _
      rw [foreign wethAccount (Ne.symm distinct)]
  rw [shape]
  exact Blanc.Prorata.ProrataAccountingEffect.silent _

/-- A share transfer is a `silent` accounting step. -/
theorem transferEffect_accountingStep
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "transfer" [.address, .uint256]) :
    Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre) .silent (snapshotAt sevm post) := by
  obtain ⟨-, -, -, -, -, supplyKept, -, -, -, -, -, -, -, foreign, -⟩ :=
    Blanc.ProrataWethVault.transfer_compiled_effect memoryWf run selectorEq
  exact silent_accountingStep config.distinct supplyKept foreign

/-- An approval is a `silent` accounting step: the guard has shown its write
lands away from the supply word, and it never touches WETH. -/
theorem approveEffect_accountingStep
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "approve" [.address, .uint256]) :
    Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre) .silent (snapshotAt sevm post) := by
  obtain ⟨-, -, -, -, -, keyNotSupply, -, allowanceSet, foreign, -⟩ :=
    Blanc.ProrataWethVault.approve_compiled_effect memoryWf run selectorEq
  refine silent_accountingStep config.distinct ?_ foreign
  show (Devm.getStor post sevm.currentTarget).get _ = _
  rw [allowanceSet, Stor.get_set_ne _ keyNotSupply]
  rfl


/-- The same conclusion from the *observation* rather than from `Stor` equality.

A target that only reads storage — every view — preserves `Devm.storageView`
and not the `Stor` tree, because entering interpreted code through a
`STATICCALL` cannot promise the representation.  Both carrier coordinates are
observations, so the weaker equality is enough. -/
theorem silent_accountingStep_of_view
    {sevm : Sevm} {pre post : Devm}
    (view : ∀ account key,
      (Devm.getStor post account).get key = (Devm.getStor pre account).get key) :
    Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre) .silent (snapshotAt sevm post) := by
  have shape : snapshotAt sevm post = snapshotAt sevm pre := by
    refine congrArg₂ Blanc.Prorata.AccountingSnapshot.mk ?_ ?_
    · show ((Devm.getStor post sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot).toNat = _
      rw [view]
      rfl
    · show (Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget).toNat
        = _
      show ((Devm.getStor post wethAccount).get _).toNat = _
      rw [view]
      rfl
  rw [shape]
  exact Blanc.Prorata.ProrataAccountingEffect.silent _

/-- A read-only endpoint is a `silent` accounting step.

The certificate is `Func.SilentIn` at `Devm.storageView`, which is what the
live-quoting views admit: they reach WETH through a `STATICCALL`, so what they
preserve is the observation. -/
theorem readOnlyEffect_accountingStep
    {sevm : Sevm} {pre post : Devm} {sig : B256} {words : Nat} {body : Func}
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = sig)
    (memberAll : (sig, Blanc.ProrataWethVault.routed words body) ∈
      Blanc.ProrataWethVault.vaultFuncs)
    (memberRO : (sig, Blanc.ProrataWethVault.routed words body) ∈
      Blanc.ProrataWethVault.readOnlyFuncs) :
    Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre) .silent (snapshotAt sevm post) := by
  obtain ⟨endpointPre, entryState, -, -, -, endpointRun⟩ :=
    Blanc.ProrataWethVault.runCompiled_enters_endpoint_compiled_logs run
      selectorEq memberAll
  have entry : ∀ account key,
      (Devm.getStor endpointPre account).get key =
        (Devm.getStor pre account).get key := by
    intro account key
    rw [getStor_eq_of_state_eq entryState account]
  have walk := Func.observe_eq_of_run_silentIn
    Blanc.ProrataWethVault.readOnlySilentSlot_closed
    (Func.WalkInv.toRun (R := Func.RunOk) endpointRun)
    (Blanc.ProrataWethVault.readOnly_silent _ memberRO)
  refine silent_accountingStep_of_view (fun account key => ?_)
  exact (congrFun (congrFun walk account) key).trans (entry account key)


/-- A delegated share transfer is a `silent` accounting step: the allowance
write lands away from the supply word and WETH is untouched. -/
theorem transferFromEffect_accountingStep
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]) :
    Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre) .silent (snapshotAt sevm post) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, supplyKept, -, -, -, -, -, -, -, -, -, -,
      -, -, foreign, -⟩ :=
    Blanc.ProrataWethVault.transferFrom_compiled_effect memoryWf run selectorEq
  exact silent_accountingStep config.distinct supplyKept foreign



/-! ## The flows' message-level step

Not written.  The bridge itself (`inboundEffect_accountingStep`) is proved; what
is missing is the wrapper that derives its two non-wrap premises from
`deposit_compiled_effect` instead of taking them.

The obstruction is mechanical and worth recording so it is not rediscovered.
That effect's conclusion binds the quoted share count under an existential and
mentions it as a full `Nat.toB256 (convertToSharesN …)` term in several places.
Rewriting the supply equation inside that term exceeds the elaborator's
heartbeat budget, and substituting it instead exceeds the recursion depth.
Neither ceiling may be raised to get past this: the proof-debt gate tracks both,
and raising one to make a proof land is weakening a gate rather than doing the
work.

The fix belongs upstream: give `deposit_compiled_effect` a form that names the
quoted amount once — an abbreviation or a separate equation — so the wrapper
can reason about a variable rather than about the term.  With that, this
wrapper is the same shape as the three silent ones below.
-/


/-! ## Every non-flow message is a silent accounting step

The twenty-one targets that make no external call move neither the vault's
supply word nor its row in WETH's storage, so the carrier sees each as a no-op.
Stated at the message level rather than per target, so that a caller composing
an execution history need not case on the selector itself. -/

/-- **A non-flow vault message is a `silent` accounting step.** -/
theorem nonflow_message_accountingStep
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (notDeposit :
      Sevm.selector sevm ≠ selector "deposit" [.uint256, .address])
    (notMint : Sevm.selector sevm ≠ selector "mint" [.uint256, .address])
    (notWithdraw : Sevm.selector sevm ≠
      selector "withdraw" [.uint256, .address, .address])
    (notRedeem : Sevm.selector sevm ≠
      selector "redeem" [.uint256, .address, .address]) :
    Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre) .silent (snapshotAt sevm post) := by
  obtain ⟨body, member⟩ :=
    Blanc.ProrataWethVault.selector_mem_vaultFuncs_of_ok run
  simp only [Blanc.ProrataWethVault.vaultFuncs, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩
  · exact readOnlyEffect_accountingStep (words := 0)
      (body := Blanc.ProrataWethVault.totalAssets) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 0)
      (body := Blanc.ProrataWethVault.name) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.convertToAssets) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact approveEffect_accountingStep config memoryWf run sel
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.previewWithdraw) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 0)
      (body := Blanc.ProrataWethVault.totalSupply) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact transferFromEffect_accountingStep config memoryWf run sel
  · exact readOnlyEffect_accountingStep (words := 0)
      (body := Blanc.ProrataWethVault.decimals) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 0)
      (body := Blanc.ProrataWethVault.asset) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.maxDeposit) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.previewRedeem) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact absurd sel notDeposit
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.balanceOf) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact absurd sel notMint
  · exact readOnlyEffect_accountingStep (words := 0)
      (body := Blanc.ProrataWethVault.symbol) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact transferEffect_accountingStep config memoryWf run sel
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.previewMint) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact absurd sel notWithdraw
  · exact absurd sel notRedeem
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.maxMint) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.convertToShares) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.maxWithdraw) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.maxRedeem) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 2)
      (body := Blanc.ProrataWethVault.allowance) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnlyEffect_accountingStep (words := 1)
      (body := Blanc.ProrataWethVault.previewDeposit) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])

end Blanc.Composition.ProrataWethVault
