import Blanc.Lift.Token.Signed
import Blanc.Lift.Usdc.Decode
import Blanc.Lift.Usdc.ModelLaws

/-!
# The USDC book and its signature laws (C3/C4)

`usdcBookS P` reads FiatTokenV2_2 behind its proxy at `P` as a signature book (`BookS`): an entry
frame from the proxy's admin word commits only as one of the proxy's own getters (`admin()`,
`implementation()`) and changes nothing; every other entry frame is the implementation's call,
decoded by `decodeCall` and applied by `Ledger.step`.  The interface reads `balanceOf`/`transfer`
by selector (what `Erc20Abi` needs) and `transferFrom`/`approve` by decode; the signer is the
permit owner, the authorization's `from`, or the cancel authorizer (`Call.signer`).

`usdcBook_lawsS` is assembly over the per-call laws of `Blanc/Lift/Usdc/ModelLaws.lean`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift.Token

/-- The proxy's own getters the admin may call (`admin()`, `implementation()`). -/
def adminGetter (e : Sevm) : Prop :=
  Blanc.Sevm.selector e = 0xf851a440 ∨ Blanc.Sevm.selector e = 0x5c60da1b

/-- What a USDC entry frame asks, as the interface reads it (by selector and argument words). -/
noncomputable def usdcOp (e : Sevm) : Op :=
  if 36 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0x70a08231 then .balanceOf (Sevm.dataWord e 4).toAdr
  else if 68 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0xa9059cbb then
    .transfer (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36).toNat
  else match decodeCall e with
    | some (.transferFrom src dst v) => .transferFrom src dst v
    | some (.approve s v) => .approve s v
    | _ => .other

/-- Who must have signed: a permit's owner, an authorization's `from` or authorizer. -/
noncomputable def usdcSigner (e : Sevm) : Option Adr :=
  match decodeCall e with
  | some (.permit o _ _) => some o
  | some (.transferWithAuthorization src _ _ _) => some src
  | some (.receiveWithAuthorization src _ _ _) => some src
  | some (.cancelAuthorization a _) => some a
  | _ => none

open Classical in
/-- **The USDC book** at proxy `P`: an entry frame from the admin word commits only as a getter;
every other entry frame is the implementation's call. -/
noncomputable def usdcBookS (P : Adr) : BookS where
  Ledger := Ledger
  step l e := if e.caller = l.admin then (if adminGetter e then some l else none)
    else match decodeCall e with
      | none => none
      | some c => l.step P e.caller c
  op := usdcOp
  bal l a := l.bal a
  allow l o s := l.allow o s
  Good := Ledger.Good
  signer := usdcSigner

/-! ## Reading the book -/

/-- The signer is the decoded call's (`Call.signer`). -/
theorem usdcSigner_eq (e : Sevm) : usdcSigner e = (decodeCall e).bind Call.signer := by
  unfold usdcSigner
  rcases decodeCall e with _ | c
  · rfl
  · cases c <;> rfl

/-- A message with nonzero value decodes to nothing (no function is payable). -/
theorem decodeCall_value {e : Sevm} (value : e.value ≠ 0) : decodeCall e = none := by
  unfold decodeCall
  simp only [ne_eq, value, not_false_eq_true, true_or, ↓reduceIte]

open Classical in
/-- A committed step of the book: an admin getter (no effect), or the implementation's call. -/
theorem usdcBookS_step {P : Adr} {l l' : Ledger} {e : Sevm}
    (h : (usdcBookS P).step l e = some l') :
    (adminGetter e ∧ l' = l) ∨ ∃ c, decodeCall e = some c ∧ l.step P e.caller c = some l' := by
  change (if e.caller = l.admin then (if adminGetter e then some l else none)
    else match decodeCall e with
      | none => none
      | some c => l.step P e.caller c) = some l' at h
  split_ifs at h with admin getter
  · exact Or.inl ⟨getter, (Option.some.inj h).symm⟩
  · rcases hd : decodeCall e with _ | c
    · rw [hd] at h
      cases h
    · rw [hd] at h
      exact Or.inr ⟨c, rfl, h⟩

/-- A holder-safe ask reverts, is a `balanceOf` (a view), or is a `transfer` read alike by selector
and by decode. -/
theorem usdcOp_safe {e : Sevm} (safe : (usdcOp e).HolderSafe) :
    decodeCall e = none ∨ decodeCall e = some .view ∨
      ∃ dst v, decodeCall e = some (.transfer dst v) ∧ usdcOp e = .transfer dst v := by
  by_cases bal : 36 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0x70a08231
  · rcases decodeCall_balanceOf bal.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_cases xfer : 68 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0xa9059cbb
    · by_cases value : e.value = 0
      · refine Or.inr (Or.inr ⟨_, _, decodeCall_transfer xfer.2 xfer.1 value, ?_⟩)
        unfold usdcOp
        rw [ite_eq_right bal, ite_eq_left xfer]
      · exact Or.inl (decodeCall_value value)
    · unfold usdcOp at safe
      rw [ite_eq_right bal, ite_eq_right xfer] at safe
      split at safe <;> simp only [Op.HolderSafe] at safe

/-- A `transfer` ask has the transfer selector, and it reverts or decodes to that transfer. -/
theorem usdcOp_transfer {e : Sevm} {dst : Adr} {v : Nat} (op : usdcOp e = .transfer dst v) :
    Blanc.Sevm.selector e = 0xa9059cbb ∧
      (decodeCall e = none ∨ decodeCall e = some (.transfer dst v)) := by
  by_cases bal : 36 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0x70a08231
  · unfold usdcOp at op
    rw [ite_eq_left bal] at op
    cases op
  · by_cases xfer : 68 ≤ e.data.length ∧ Blanc.Sevm.selector e = 0xa9059cbb
    · unfold usdcOp at op
      rw [ite_eq_right bal, ite_eq_left xfer] at op
      obtain ⟨rfl, rfl⟩ := Op.transfer.inj op
      refine ⟨xfer.2, ?_⟩
      by_cases value : e.value = 0
      · exact Or.inr (decodeCall_transfer xfer.2 xfer.1 value)
      · exact Or.inl (decodeCall_value value)
    · unfold usdcOp at op
      rw [ite_eq_right bal, ite_eq_right xfer] at op
      split at op <;> cases op

/-- The admin getters are not `transfer`. -/
theorem adminGetter_not_transfer {e : Sevm} (getter : adminGetter e)
    (sel : Blanc.Sevm.selector e = 0xa9059cbb) : False := by
  unfold adminGetter at getter
  rw [sel] at getter
  rcases getter with h | h <;> exact absurd h (by decide)

/-! ## The laws -/

/-- **C3/C4: USDC's model satisfies the signature laws** (U5). -/
theorem usdcBook_lawsS (P : Adr) : BookLawsS (usdcBookS P) where
  holder_only {l l' a h} good step lower := by
    rcases usdcBookS_step step with ⟨-, rfl⟩ | ⟨c, hd, hs⟩
    · exact absurd lower (lt_irrefl _)
    · have signer : usdcSigner a = c.signer := by rw [usdcSigner_eq, hd]; rfl
      rw [show (usdcBookS P).signer a = c.signer from signer]
      exact Ledger.step_holder_only good hs lower
  allow_owner {l l' a h g} good step raise := by
    rcases usdcBookS_step step with ⟨-, rfl⟩ | ⟨c, hd, hs⟩
    · exact absurd raise (lt_irrefl _)
    · have signer : usdcSigner a = c.signer := by rw [usdcSigner_eq, hd]; rfl
      rw [show (usdcBookS P).signer a = c.signer from signer]
      exact Ledger.step_allow_owner good hs raise
  holder_debit {l l' a h} good step caller safe := by
    rcases usdcBookS_step step with ⟨-, rfl⟩ | ⟨c, hd, hs⟩
    · exact Nat.le_add_right _ _
    · rcases usdcOp_safe safe with hn | hv | ⟨dst, v, ht, op⟩
      · rw [hd] at hn
        cases hn
      · rw [hd] at hv
        cases hv
        rw [Ledger.step_view hs]
        exact Nat.le_add_right _ _
      · rw [hd] at ht
        cases ht
        subst caller
        change l.bal a.caller ≤ l'.bal a.caller + (usdcOp a).debit a.caller
        rw [op]
        exact Ledger.step_transfer_debit hs
  transfer_exact {l l' a dst v} good step op ne := by
    obtain ⟨sel, dec⟩ := usdcOp_transfer op
    rcases usdcBookS_step step with ⟨getter, -⟩ | ⟨c, hd, hs⟩
    · exact (adminGetter_not_transfer getter sel).elim
    · rcases dec with hn | ht
      · rw [hd] at hn
        cases hn
      · rw [hd] at ht
        cases ht
        exact Ledger.step_transfer_exact hs ne
  allow_safe {l l' a h g} good step caller safe := by
    rcases usdcBookS_step step with ⟨-, rfl⟩ | ⟨c, hd, hs⟩
    · exact le_refl _
    · rcases usdcOp_safe safe with hn | hv | ⟨dst, v, ht, -⟩
      · rw [hd] at hn
        cases hn
      · rw [hd] at hv
        cases hv
        rw [Ledger.step_view hs]
      · rw [hd] at ht
        cases ht
        change l'.allow h g ≤ l.allow h g
        rw [Ledger.step_transfer_allow hs]
  bal_lt {l h} good := Ledger.Good.bal_lt_word good h

end Blanc.Lift.Usdc
