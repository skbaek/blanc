import Blanc.Lift.Usdc.Book

/-!
# Controls on the USDC book (C3, C5)

Two kernel counterexamples on the pure ledger, each a one-line mutation of `usdcBookS`'s step:

* C3 (`mutantBookS`): `transferFrom` that skips the allowance check.  A stranger's
  `transferFrom(1, 2, 1)` lowers holder `1`'s balance with no allowance and no signature, so
  `holder_only` fails.
* C5 (`thirdPartyBookS`): `transfer` that debits a third party `x` instead of the caller.  A
  `transfer(1, 1)` from a caller other than `x` and `1` leaves the caller's balance unchanged, so
  `transfer_exact` fails.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift.Token

open Classical in
/-- The C3 control's mutant: `transferFrom` that skips the allowance check. -/
noncomputable def mutantBookS (P : Adr) : BookS :=
  { usdcBookS P with
    step := fun l e => if e.caller = l.admin then (if adminGetter e then some l else none)
      else match decodeCall e with
        | some (.transferFrom src dst v) => l.move src dst v
        | none => none
        | some c => l.step P e.caller c }

open Classical in
/-- The C5 control's mutant: `transfer` that debits a third party `x` instead of the caller. -/
noncomputable def thirdPartyBookS (P x : Adr) : BookS :=
  { usdcBookS P with
    step := fun l e => if e.caller = l.admin then (if adminGetter e then some l else none)
      else match decodeCall e with
        | some (.transfer dst v) => l.move x dst v
        | none => none
        | some c => l.step P e.caller c }

/-! ## The witnesses -/

namespace Ledger

/-- A good ledger in which `a` holds one unit and is the admin word; nothing else is set. -/
def oneAt (a : Adr) : Ledger where
  bal y := if y = a then 1 else 0
  frozen _ := false
  allow _ _ := 0
  nonce _ := 0
  authUsed _ _ := false
  paused := false
  owner := 0
  pauser := 0
  blacklister := 0
  masterMinter := 0
  rescuer := 0
  minter _ := false
  minterAllowance _ := 0
  supply := 1
  initialized := true
  version := 3
  admin := a

theorem oneAt_bal_le (a y : Adr) : (oneAt a).bal y ≤ 1 := by
  change (if y = a then 1 else 0) ≤ 1
  split_ifs <;> omega

theorem oneAt_good (a : Adr) : (oneAt a).Good :=
  ⟨fun y => lt_of_le_of_lt (oneAt_bal_le a y) (by decide), rfl, rfl⟩

/-- A one-unit move out of `src`'s single unit commits (no frozen account, small balances). -/
theorem oneAt_move {a src dst : Adr} (hs : src ≠ 0) (hd : dst ≠ 0) (one : (oneAt a).bal src = 1) :
    (oneAt a).move src dst 1 = some { oneAt a with bal := moveBal (oneAt a).bal src dst 1 } := by
  have small : Function.update (oneAt a).bal src ((oneAt a).bal src - 1) dst + 1 < 2 ^ 255 := by
    by_cases e : dst = src
    · rw [e, Function.update_self]
      omega
    · rw [Function.update_of_ne e]
      have := oneAt_bal_le a dst
      omega
  have guard : ¬ (src = 0 ∨ dst = 0 ∨ (oneAt a).bal src < 1) := by
    rintro (h | h | h)
    · exact hs h
    · exact hd h
    · rw [one] at h
      exact lt_irrefl 1 h
  have first : ¬ (2 ^ 255 ≤ (oneAt a).bal src - 1 ∨ (oneAt a).frozen src = true) := by
    rintro (h | h)
    · rw [one] at h
      exact absurd h (by decide)
    · exact Bool.false_ne_true h
  have second : ¬ (2 ^ 255 ≤ Function.update (oneAt a).bal src ((oneAt a).bal src - 1) dst + 1 ∨
      (oneAt a).frozen dst = true) := by
    rintro (h | h)
    · exact absurd small (not_lt.mpr h)
    · exact Bool.false_ne_true h
  unfold move setBalance
  rw [ite_eq_right guard, ite_eq_right first, Option.bind_some]
  exact ite_eq_right second

end Ledger

/-- `transferFrom(1, 2, 1)`'s calldata. -/
def transferFromData : List UInt8 :=
  [0x23, 0xb8, 0x72, 0xdd] ++ List.replicate 31 0 ++ [1] ++ List.replicate 31 0 ++ [2] ++
    List.replicate 31 0 ++ [1]

/-- `transfer(1, 1)`'s calldata. -/
def transferData : List UInt8 :=
  [0xa9, 0x05, 0x9c, 0xbb] ++ List.replicate 31 0 ++ [1] ++ List.replicate 31 0 ++ [1]

/-- A nonpayable message from `c` with calldata `d`. -/
def witness (c : Adr) (d : List UInt8) : Sevm := { (default : Sevm) with caller := c, data := d }

theorem witness_value (c : Adr) (d : List UInt8) : (witness c d).value = 0 := rfl

theorem witness_data (c : Adr) (d : List UInt8) : (witness c d).data = d := rfl

theorem decode_transferFrom (c : Adr) :
    decodeCall (witness c transferFromData) = some (.transferFrom 1 2 1) := by
  have sel : Sevm.selector (witness c transferFromData) = 0x23b872dd := by
    unfold Sevm.selector Sevm.dataWord
    rw [witness_data]
    decide +kernel
  have w4 : (Sevm.dataWord (witness c transferFromData) 4).toAdr = 1 := by
    unfold Sevm.dataWord
    rw [witness_data]
    decide +kernel
  have w36 : (Sevm.dataWord (witness c transferFromData) 36).toAdr = 2 := by
    unfold Sevm.dataWord
    rw [witness_data]
    decide +kernel
  have w68 : (Sevm.dataWord (witness c transferFromData) 68).toNat = 1 := by
    unfold Sevm.dataWord
    rw [witness_data]
    decide +kernel
  have len : 100 ≤ (witness c transferFromData).data.length := by
    rw [witness_data]
    decide
  rw [decodeCall_transferFrom sel len (witness_value c _), w4, w36, w68]

theorem transfer_sel (c : Adr) : Sevm.selector (witness c transferData) = 0xa9059cbb := by
  unfold Sevm.selector Sevm.dataWord
  rw [witness_data]
  decide +kernel

theorem transfer_len (c : Adr) : 68 ≤ (witness c transferData).data.length := by
  rw [witness_data]
  decide

theorem transfer_words (c : Adr) :
    (Sevm.dataWord (witness c transferData) 4).toAdr = 1 ∧
      (Sevm.dataWord (witness c transferData) 36).toNat = 1 := by
  unfold Sevm.dataWord
  rw [witness_data]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem decode_transfer (c : Adr) :
    decodeCall (witness c transferData) = some (.transfer 1 1) := by
  rw [decodeCall_transfer (transfer_sel c) (transfer_len c) (witness_value c _),
    (transfer_words c).1, (transfer_words c).2]

theorem op_transfer (c : Adr) : usdcOp (witness c transferData) = .transfer 1 1 := by
  have notBal : ¬ (36 ≤ (witness c transferData).data.length ∧
      Blanc.Sevm.selector (witness c transferData) = 0x70a08231) := by
    rw [transfer_sel]
    exact fun h => absurd h.2 (by decide)
  unfold usdcOp
  rw [ite_eq_right notBal, ite_eq_left ⟨transfer_len c, transfer_sel c⟩, (transfer_words c).1,
    (transfer_words c).2]

/-! ## The controls -/

/-- **C3 control** (U5): the mutated model violates the holder law. -/
theorem control_usdc_mutant_not_lawsS (P : Adr) : ¬ BookLawsS (mutantBookS P) := by
  intro laws
  have step : (mutantBookS P).step (Ledger.oneAt 1) (witness 3 transferFromData) =
      some { Ledger.oneAt 1 with bal := Ledger.moveBal (Ledger.oneAt 1).bal 1 2 1 } := by
    have ne : (witness 3 transferFromData).caller ≠ (Ledger.oneAt 1).admin := by decide
    simp only [mutantBookS, ne, ↓reduceIte, decode_transferFrom]
    exact Ledger.oneAt_move (by decide) (by decide) (by decide)
  have lower : Ledger.moveBal (Ledger.oneAt 1).bal 1 2 1 1 < (Ledger.oneAt 1).bal 1 := by
    unfold Ledger.moveBal
    rw [Function.update_of_ne (by decide), Function.update_self]
    decide
  rcases laws.holder_only (h := 1) (Ledger.oneAt_good 1) step lower with caller | allowed | signed
  · exact absurd caller (by decide)
  · exact absurd allowed (lt_irrefl 0)
  · change usdcSigner (witness 3 transferFromData) = some 1 at signed
    rw [usdcSigner_eq, decode_transferFrom] at signed
    cases signed

/-- **C5 control** (U5): an implementation whose `transfer` debits a third party breaks the laws. -/
theorem control_usdc_thirdParty_not_lawsS (P : Adr) {x : Adr} (hx : x ≠ 0) :
    ¬ BookLawsS (thirdPartyBookS P x) := by
  intro laws
  -- a caller other than `x` and the recipient `1`
  let c : Adr := if x = 2 then 3 else 2
  have cx : c ≠ x := by
    change (if x = 2 then (3 : Adr) else 2) ≠ x
    split_ifs with h
    · rw [h]; decide
    · exact Ne.symm h
  have c1 : (1 : Adr) ≠ c := by
    change (1 : Adr) ≠ if x = 2 then 3 else 2
    split_ifs <;> decide
  have one : (Ledger.oneAt x).bal x = 1 := ite_eq_left rfl
  have step : (thirdPartyBookS P x).step (Ledger.oneAt x) (witness c transferData) =
      some { Ledger.oneAt x with bal := Ledger.moveBal (Ledger.oneAt x).bal x 1 1 } := by
    have ne : (witness c transferData).caller ≠ (Ledger.oneAt x).admin := cx
    simp only [thirdPartyBookS, ne, ↓reduceIte, decode_transfer]
    exact Ledger.oneAt_move hx (by decide) one
  have exact := laws.transfer_exact (Ledger.oneAt_good x) step (op_transfer c) c1
  change Ledger.moveBal (Ledger.oneAt x).bal x 1 1 c + 1 = (Ledger.oneAt x).bal c at exact
  unfold Ledger.moveBal at exact
  rw [Function.update_of_ne (Ne.symm c1), Function.update_of_ne cx] at exact
  omega

end Blanc.Lift.Usdc
