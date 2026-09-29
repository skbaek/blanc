import Blanc.Lift.Curve3Crv.Layout

/-!
# Satisfiability of the Curve 3Crv checkpoint premise

The Curve history theorem carries `VyInv stor s K` at its checkpoint.  This module shows that
the premise is inhabited over the empty live-key set: the all-zero storage abstracts the model
state with empty name and symbol, zero decimals, zero supply and minter, and zero balances and
allowances.

This proves satisfiability of the checkpoint premise, not deployment: the state is not the
constructor's output, and no keccak is evaluated (`vyNameBase`, `vySymbolBase` stay symbolic).
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Conserved)

/-- The all-zero model state. -/
def curveInitState : Curve3Crv.State where
  name := []
  symbol := []
  decimals := 0
  balanceOf := fun _ => 0
  allowances := fun _ _ => 0
  totalSupply := 0
  minter := 0

/-- The empty storage. -/
def curveInitStor : Stor := Stor.empty

theorem curveInitStor_get (x : B256) : curveInitStor.get x = 0 := by
  simp [curveInitStor, Stor.get, Stor.empty]

/-- **The Curve checkpoint premise is satisfiable** over the empty live-key set. -/
theorem curve_init_vyInv : VyInv curveInitStor curveInitState (fun _ => False) where
  decimals := by rw [curveInitStor_get]; rfl
  supply := by rw [curveInitStor_get]; rfl
  minter := by rw [curveInitStor_get]; rfl
  name := by simp [VyStr, curveInitState, curveInitStor_get, B256.toNat_zero]
  symbol := by simp [VyStr, curveInitState, curveInitStor_get, B256.toNat_zero]
  known := fun _ h => h.elim
  unknown := fun k _ => by cases k <;> rfl
  support := fun x hx => absurd (curveInitStor_get x) hx
  inj := fun _ _ h => h.elim
  apart := fun _ h => h.elim
  conserved := by
    show (0 : B256).toNat = sum (fun _ : Adr => (0 : B256))
    rw [sum, sumBelow_zero, B256.toNat_zero]

/-! ## A deployed-shaped state

Name, symbol, decimals and minter set as the deployed token has them, supply and every balance
and allowance zero.  The five fixed-slot writes sit at `2`, `6`, `vyNameBase`, `vyNameBase + 1`,
`vySymbolBase`, `vySymbolBase + 1`; their pairwise distinctness and the values read back are
kernel-evaluated facts about two keccak hashes of one word each (`vyNameBase`, `vySymbolBase`).
No other slot is written. -/

def curveShapedName : Bytes := "Curve.fi DAI/USDC/USDT".toUTF8.toList
def curveShapedSymbol : Bytes := "3Crv".toUTF8.toList

/-- Decimals 18, minter `1`, supply and all mappings zero. -/
def curveShapedState : Curve3Crv.State where
  name := curveShapedName
  symbol := curveShapedSymbol
  decimals := 18
  balanceOf := fun _ => 0
  allowances := fun _ _ => 0
  totalSupply := 0
  minter := 1

/-- The left-aligned data word of a string of at most 32 bytes. -/
def curveStrWord (bs : Bytes) : B256 := Bytes.toB256 (bs ++ List.replicate (32 - bs.length) 0)

/-- The storage the constructor and name/symbol setters leave: decimals, minter, and the two
strings' length and data words; no other slot is written. -/
def curveShapedStor : Stor :=
  ((((Stor.empty.set vyDecimalsSlot 18).set vyMinterSlot (1 : Adr).toB256).set vyNameBase
      (Nat.toB256 curveShapedName.length)).set (vyNameBase + Nat.toB256 1)
      (curveStrWord curveShapedName)).set vySymbolBase
      (Nat.toB256 curveShapedSymbol.length) |>.set (vySymbolBase + Nat.toB256 1)
      (curveStrWord curveShapedSymbol)

theorem get_ne_zero_mem_set {s : Stor} {l : List B256} (h : ∀ x, s.get x ≠ 0 → x ∈ l)
    (k v : B256) : ∀ x, (s.set k v).get x ≠ 0 → x ∈ k :: l := by
  intro x hx
  rw [Stor.get_set_ite] at hx
  by_cases e : k = x
  · simp [e]
  · simp only [e, ↓reduceIte] at hx
    exact List.mem_cons_of_mem _ (h x hx)

end Blanc.Lift.Curve3Crv
