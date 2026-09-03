import Blanc.Composition.ProrataWethVaultInbound
import Blanc.Composition.ProrataWethVaultOutbound

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

end Blanc.Composition.ProrataWethVault
