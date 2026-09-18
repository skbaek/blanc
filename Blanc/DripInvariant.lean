-- DripInvariant.lean : full-address storage invariant for DRIP.

import Blanc.DripDeploy
import Blanc.DripRpow
import Blanc.LedgerConservation
import Blanc.StorageOnlySpec

namespace Blanc

open Jaune

namespace Drip

/-- Natural-number view of DRIP's accrued index. -/
def chiN (s : Stor) : Nat :=
  (s.get chiSlot).toNat

/-- Natural-number view of DRIP's last-accrual timestamp. -/
def rhoN (s : Stor) : Nat :=
  (s.get rhoSlot).toNat

/-- Natural-number view of the caller-indexed normalized-unit ledger. -/
def pieN (s : Stor) (holder : Adr) : Nat :=
  (s.get (pieSlot holder)).toNat

/-- Natural-number view of DRIP's distinguished total-unit word. -/
def totalN (s : Stor) : Nat :=
  (s.get totalUnitsSlot).toNat

/-- The storage facts preserved by every successful DRIP endpoint.

`balSum` ranges over every address-shaped storage key, so its equality with
`totalN` is full-address conservation rather than a finite-address surrogate.
Balances and callvalue are intentionally absent: their no-wrap accounting is
provided later by configured trace bounds. -/
def AccountingInv (s : Stor) : Prop :=
  scale.toNat ≤ chiN s ∧
    chiN s ≤ maxChi.toNat ∧
    totalN s ≤ maxPie.toNat ∧
    balSum s = totalN s ∧
    ∀ holder, pieN s holder ≤ maxUnits.toNat

theorem AccountingInv.chi_lower {s : Stor} (h : AccountingInv s) :
    scale.toNat ≤ chiN s :=
  h.1

theorem AccountingInv.chi_upper {s : Stor} (h : AccountingInv s) :
    chiN s ≤ maxChi.toNat :=
  h.2.1

theorem AccountingInv.total_upper {s : Stor} (h : AccountingInv s) :
    totalN s ≤ maxPie.toNat :=
  h.2.2.1

theorem AccountingInv.balSum_eq {s : Stor} (h : AccountingInv s) :
    balSum s = totalN s :=
  h.2.2.2.1

theorem AccountingInv.row_upper {s : Stor} (h : AccountingInv s) (holder : Adr) :
    pieN s holder ≤ maxUnits.toNat :=
  h.2.2.2.2 holder

/-- A booked row is bounded by the certified full-address total. -/
theorem AccountingInv.row_le_total {s : Stor} (h : AccountingInv s) (holder : Adr) :
    pieN s holder ≤ totalN s := by
  calc
    pieN s holder = (Stor.rest s holder).toNat := rfl
    _ ≤ balSum s := le_sum
    _ = totalN s := h.balSum_eq

/-- Full-address conservation makes the ledger sum a non-wrapping word sum. -/
theorem AccountingInv.sumNof {s : Stor} (h : AccountingInv s) :
    SumNof (Stor.rest s) := by
  show balSum s < 2 ^ 256
  rw [h.balSum_eq]
  exact lt_of_le_of_lt h.total_upper (B256.toNat_lt maxPie)

theorem Stor.rest_set_chiSlot (s : Stor) (value : B256) :
    Stor.rest (s.set chiSlot value) = Stor.rest s :=
  rest_set_of_not_validAdr chiSlot_not_valid

theorem Stor.rest_set_rhoSlot (s : Stor) (value : B256) :
    Stor.rest (s.set rhoSlot value) = Stor.rest s :=
  rest_set_of_not_validAdr rhoSlot_not_valid

theorem Stor.rest_set_totalUnitsSlot (s : Stor) (value : B256) :
    Stor.rest (s.set totalUnitsSlot value) = Stor.rest s :=
  rest_set_of_not_validAdr totalUnitsSlot_not_valid

theorem balSum_eq_zero_of_rows_zero {s : Stor}
    (hrows : ∀ holder, pieN s holder = 0) : balSum s = 0 := by
  have hrest : Stor.rest s = fun _ => (0 : B256) := by
    funext holder
    have hnat : (s.get (pieSlot holder)).toNat = 0 := hrows holder
    apply B256.toNat_inj
    change (s.get holder.toB256).toNat = (0 : B256).toNat
    rw [B256.toNat_zero]
    simpa [pieSlot] using hnat
  rw [balSum, hrest, sum, sumBelow_zero]

/-- The constructor's actual scalar and all-row facts establish the storage
invariant.  This proof uses the frozen scalar/address disjointness rather than
assuming an empty finite holder set. -/
theorem DeploymentRoot.accountingInv
    {cfg : ChainConfig} {base deployed : BlockChain} {ca : Adr}
    (hroot : DeploymentRoot cfg base deployed ca) :
    AccountingInv (deployed.state.getStor ca) := by
  let s := deployed.state.getStor ca
  have hchi : s.get chiSlot = scale := hroot.chi
  have htotal : s.get totalUnitsSlot = 0 := by
    exact hroot.pie totalUnitsSlot scalarSlots_distinct.2.1.symm
      scalarSlots_distinct.2.2.symm
  have hrows : ∀ holder, pieN s holder = 0 := by
    intro holder
    unfold pieN
    rw [hroot.pie (pieSlot holder) (pieSlot_ne_chiSlot holder)
      (pieSlot_ne_rhoSlot holder), B256.toNat_zero]
  have hsum : balSum s = 0 := balSum_eq_zero_of_rows_zero hrows
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold chiN
    rw [hchi]
  · unfold chiN
    rw [hchi]
    exact B256.toNat_le_toNat (by
      rw [scale_literal, maxChi_literal]
      decide)
  · unfold totalN
    rw [htotal, B256.toNat_zero]
    exact Nat.zero_le _
  · unfold totalN
    rw [hsum, htotal, B256.toNat_zero]
  · intro holder
    rw [hrows holder]
    exact Nat.zero_le _

/-- DRIP's storage-only adapter to the retained execution ladder. -/
def dripSpec : ContractSpec :=
  ContractSpec.ofStorageOnly runtime AccountingInv

end Drip

end Blanc
