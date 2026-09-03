-- DRIP's frozen constants, ABI identities, and total storage projection.
-- This low family layer contains no callable program or proof ladder.

import Blanc.CommonCore

namespace Blanc

open Jaune

namespace Drip

/-! ## Frozen arithmetic domain -/

/-- Ray scale `S = 10^27`. -/
def scale : B256 := 1000000000000000000000000000

/-- Fixed per-second factor `R`. -/
def rate : B256 := 1000000001547125957863212448

/-- Half-up offset `H = S / 2` used only inside the rpow loop. -/
def half : B256 := 500000000000000000000000000

/-- Largest elapsed interval admitted by one successful accrual. -/
def maxElapsed : B256 := Nat.toB256 (2 ^ 32 - 1)

/-- Frozen symmetric word-safety ceilings. -/
def maxChi : B256 := Nat.toB256 (2 ^ 128 - 1)
def maxAsset : B256 := Nat.toB256 (2 ^ 128 - 1)
def maxUnits : B256 := Nat.toB256 (2 ^ 128 - 1)
def maxPie : B256 := Nat.toB256 (2 ^ 128 - 1)

theorem scale_literal :
    scale = 1000000000000000000000000000 := by
  rfl

theorem rate_literal :
    rate = 1000000001547125957863212448 := by
  rfl

theorem half_literal :
    half = 500000000000000000000000000 := by
  rfl

theorem maxElapsed_literal : maxElapsed = 4294967295 := by
  decide +kernel

theorem maxChi_literal :
    maxChi = 340282366920938463463374607431768211455 := by
  decide +kernel

theorem maxAsset_literal :
    maxAsset = 340282366920938463463374607431768211455 := by
  decide +kernel

theorem maxUnits_literal :
    maxUnits = 340282366920938463463374607431768211455 := by
  decide +kernel

theorem maxPie_literal :
    maxPie = 340282366920938463463374607431768211455 := by
  decide +kernel

/-! ## Frozen ABI identities

The list is in increasing selector order, which is the order used by DRIP's
source dispatcher. Exact calldata lengths, payability, and return shapes live
beside the endpoint bodies rather than being duplicated here.
-/

def convertToAssetsSelector : B256 :=
  selector "convertToAssets" [.uint256]

def exitSelector : B256 := selector "exit" [.uint256]

def convertToUnitsSelector : B256 :=
  selector "convertToUnits" [.uint256]

def dripSelector : B256 := selector "drip" []

def joinSelector : B256 := selector "join" []

def selectors : List B256 :=
  [convertToAssetsSelector, exitSelector, convertToUnitsSelector,
    dripSelector, joinSelector]

theorem selectors_literal :
    selectors =
      [0x07a2d13a, 0x7f8661a1, 0x9227149a, 0x9f678cca, 0xb688a363] := by
  decide +kernel

/-! ## Frozen storage coordinates and total projection -/

/-- `chi` occupies `2^256 - 1`. -/
def chiSlot : B256 := B256.max

/-- `rho` occupies `2^256 - 2`. -/
def rhoSlot : B256 := B256.max - 1

/-- Total normalized supply `Pie` occupies `2^256 - 3`. -/
def totalUnitsSlot : B256 := B256.max - 2

/-- A holder's normalized balance `pie[holder]` is keyed by the raw address. -/
def pieSlot (holder : Adr) : B256 := holder.toB256

theorem chiSlot_literal :
    chiSlot =
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by
  decide +kernel

theorem rhoSlot_literal :
    rhoSlot =
      0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe := by
  decide +kernel

theorem totalUnitsSlot_literal :
    totalUnitsSlot =
      0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd := by
  decide +kernel

theorem scalarSlots_distinct :
    chiSlot ≠ rhoSlot ∧ chiSlot ≠ totalUnitsSlot ∧
      rhoSlot ≠ totalUnitsSlot := by
  decide +kernel

theorem pieSlot_injective : Function.Injective pieSlot := by
  intro a b h
  exact Adr.toB256_inj h

theorem pieSlot_valid (holder : Adr) : ValidAdr (pieSlot holder) :=
  ⟨holder, rfl⟩

private theorem not_valid_of_high_ne_zero (w : B256) (h : w.1.1 ≠ 0) :
    ¬ ValidAdr w := by
  rintro ⟨a, ha⟩
  apply h
  rw [← ha]
  rfl

theorem chiSlot_not_valid : ¬ ValidAdr chiSlot := by
  apply not_valid_of_high_ne_zero
  decide +kernel

theorem rhoSlot_not_valid : ¬ ValidAdr rhoSlot := by
  apply not_valid_of_high_ne_zero
  decide +kernel

theorem totalUnitsSlot_not_valid : ¬ ValidAdr totalUnitsSlot := by
  apply not_valid_of_high_ne_zero
  decide +kernel

theorem pieSlot_ne_chiSlot (holder : Adr) :
    pieSlot holder ≠ chiSlot := by
  intro h
  exact chiSlot_not_valid (h ▸ pieSlot_valid holder)

theorem pieSlot_ne_rhoSlot (holder : Adr) :
    pieSlot holder ≠ rhoSlot := by
  intro h
  exact rhoSlot_not_valid (h ▸ pieSlot_valid holder)

theorem pieSlot_ne_totalUnitsSlot (holder : Adr) :
    pieSlot holder ≠ totalUnitsSlot := by
  intro h
  exact totalUnitsSlot_not_valid (h ▸ pieSlot_valid holder)

/-- Total logical projection of DRIP-owned storage. `totalUnits` is the
Maker-style `Pie`; `pie` is the address-indexed normalized ledger. -/
structure LogicalState where
  chi : B256
  rho : B256
  pie : Adr → B256
  totalUnits : B256

def project (stor : Stor) : LogicalState where
  chi := stor.get chiSlot
  rho := stor.get rhoSlot
  pie := fun holder => stor.get (pieSlot holder)
  totalUnits := stor.get totalUnitsSlot

@[simp] theorem project_chi (stor : Stor) :
    (project stor).chi = stor.get chiSlot := rfl

@[simp] theorem project_rho (stor : Stor) :
    (project stor).rho = stor.get rhoSlot := rfl

@[simp] theorem project_pie (stor : Stor) (holder : Adr) :
    (project stor).pie holder = stor.get (pieSlot holder) := rfl

@[simp] theorem project_totalUnits (stor : Stor) :
    (project stor).totalUnits = stor.get totalUnitsSlot := rfl

end Drip

end Blanc
