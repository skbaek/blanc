import Blanc.Lift.Weth9.Ledger
import Blanc.Lift.LedgerFootprint
import Blanc.WordArithmetic

/-!
# WETH9 holder observers

`balHolders keys` is the set of owners of the balance rows a key list names, and
`EtherBacked keys s b` says that the stored balance words of those holders sum to at most the
ether `b`.  `FootInv.etherBacked` reads it back from the footprint invariant over exactly the keys a
history touched (no initial keys): an untracked holder's word is not summed, and every summed word
is a tracked one.

`NetFlow keys calls s` says that every such holder's stored balance word is, modulo `2 ^ 256`, the
credits minus the debits the decoded writer calls `calls` name for it (`inflow`, `outflow`);
`Ledger.run_netFlow` proves it for every successful model run from an all-zero ledger.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc

/-- The owners of the balance rows named by `keys`. -/
def balHolders (keys : List Key) : Finset Adr :=
  (keys.filterMap fun
    | .bal a => some a
    | .allow _ _ => none).toFinset

/-- **Ether backing over storage words**: the balance words of every holder `keys` names sum to at
most the ether balance `b`. -/
def EtherBacked (keys : List Key) (s : Stor) (b : B256) : Prop :=
  ledgerSumOn (balHolders keys) (fun a => s.get (balSlot a)) ≤ b.toNat

theorem mem_balHolders {keys : List Key} {a : Adr} :
    a ∈ balHolders keys ↔ Key.bal a ∈ keys := by
  unfold balHolders
  rw [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨k, member, eq⟩
    cases k with
    | bal b => cases eq; exact member
    | allow _ _ => cases eq
  · intro member
    exact ⟨_, member, rfl⟩

/-- The footprint invariant over exactly the touched keys gives ether backing over storage. -/
theorem FootInv.etherBacked {keys : List Key} {s : Stor} {b : B256}
    (foot : FootInv (Key.extend (fun _ => False) keys) s b) : EtherBacked keys s b := by
  have tracked_iff : ∀ a, Key.extend (fun _ => False) keys (.bal a) ↔ a ∈ balHolders keys :=
    fun a => ⟨fun h => mem_balHolders.mpr (h.resolve_left id),
      fun h => .inr (mem_balHolders.mp h)⟩
  have total : trackedSum (Key.extend (fun _ => False) keys) s =
      ledgerSumOn (balHolders keys) (fun a => s.get (balSlot a)) := by
    unfold trackedSum
    rw [sum_eq_ledgerSumOn (coalition := balHolders keys) (fun a nonzero => by
      unfold tracked at nonzero
      by_contra outside
      rw [ite_eq_right (fun h => outside ((tracked_iff a).mp h))] at nonzero
      exact nonzero rfl)]
    apply ledgerSumOn_congr
    intro a member
    unfold tracked
    rw [ite_eq_left ((tracked_iff a).mpr member)]
  unfold EtherBacked
  rw [← total]
  exact foot.backed

/-! ## Net flow -/

/-- What one writer call credits to `a`: a deposit's value, or a transfer's amount to `a`. -/
def Call.credit (a : Adr) : Call → Nat
  | .deposit who v => if who = a then v.toNat else 0
  | .transfer _ dst w => if dst = a then w.toNat else 0
  | .transferFrom _ _ dst w => if dst = a then w.toNat else 0
  | _ => 0

/-- What one writer call debits from `a`: a withdrawal, or a transfer's amount from `a`. -/
def Call.debit (a : Adr) : Call → Nat
  | .withdraw who w => if who = a then w.toNat else 0
  | .transfer who _ w => if who = a then w.toNat else 0
  | .transferFrom _ src _ w => if src = a then w.toNat else 0
  | _ => 0

/-- The total the calls credit to `a`. -/
def inflow (calls : List Call) (a : Adr) : Nat := (calls.map (Call.credit a)).sum

/-- The total the calls debit from `a`. -/
def outflow (calls : List Call) (a : Adr) : Nat := (calls.map (Call.debit a)).sum

/-- **Net flow over storage words**: every holder `keys` names has, as its stored balance word,
the credits minus the debits that `calls` name for it, modulo `2 ^ 256`. -/
def NetFlow (keys : List Key) (calls : List Call) (s : Stor) : Prop :=
  ∀ a ∈ balHolders keys,
    ((s.get (balSlot a)).toNat : Int) ≡ (inflow calls a : Int) - outflow calls a [ZMOD 2 ^ 256]

private theorem modulus_cast : ((wordModulusN : Nat) : Int) = 2 ^ 256 := by
  unfold wordModulusN
  push_cast

private theorem add_modEq (x y : B256) :
    ((x + y).toNat : Int) ≡ (x.toNat : Int) + y.toNat [ZMOD 2 ^ 256] := by
  rw [B256.toNat_add, Nat.lo_eq]
  have := Int.mod_modEq ((x.toNat + y.toNat : Nat) : Int) (2 ^ 256)
  push_cast at this ⊢
  exact this

private theorem sub_modEq (x y : B256) :
    ((x - y).toNat : Int) ≡ (x.toNat : Int) - y.toNat [ZMOD 2 ^ 256] := by
  have := b256_sub_modEq_wordModulus x y
  rw [modulus_cast] at this
  exact this

private theorem setBal_bal_apply (l : Ledger) (b a : Adr) (w : B256) :
    (l.setBal b w).bal a = if a = b then w else l.bal a := by
  rw [Ledger.setBal_bal, Function.update_apply]

private theorem xfer_modEq (l : Ledger) (src dst a : Adr) (wad : B256) :
    (((l.xfer src dst wad).bal a).toNat : Int) ≡
      (l.bal a).toNat + (if dst = a then wad.toNat else 0 : Nat) -
        (if src = a then wad.toNat else 0 : Nat) [ZMOD 2 ^ 256] := by
  unfold Ledger.xfer
  simp only [setBal_bal_apply]
  by_cases hd : dst = a <;> by_cases hs : src = a
  · subst hd; subst hs
    simp only [↓reduceIte]
    refine (add_modEq _ _).trans ?_
    refine ((sub_modEq _ _).add_right _).trans ?_
    push_cast; ring_nf; rfl
  · subst hd
    simp only [↓reduceIte, Ne.symm hs, hs]
    refine (add_modEq _ _).trans ?_
    push_cast; ring_nf; rfl
  · subst hs
    simp only [↓reduceIte, Ne.symm hd, hd]
    refine (sub_modEq _ _).trans ?_
    push_cast; ring_nf; rfl
  · simp only [Ne.symm hd, Ne.symm hs, hd, hs, ↓reduceIte]
    push_cast; ring_nf; rfl

private theorem transferFrom_modEq {l l' : Ledger} {who src dst a : Adr} {wad : B256}
    (ok : l.transferFrom who src dst wad = some l') :
    ((l'.bal a).toNat : Int) ≡
      (l.bal a).toNat + (if dst = a then wad.toNat else 0 : Nat) -
        (if src = a then wad.toNat else 0 : Nat) [ZMOD 2 ^ 256] := by
  unfold Ledger.transferFrom at ok
  split at ok
  · cases ok
  · split at ok
    · split at ok
      · cases ok
      · cases ok
        exact xfer_modEq _ src dst a wad
    · cases ok
      exact xfer_modEq _ src dst a wad

/-- One successful call moves `a`'s balance by its credit minus its debit, modulo `2 ^ 256`. -/
theorem Ledger.step_netFlow {l l' : Ledger} {c : Call} (ok : l.step c = some l') (a : Adr) :
    ((l'.bal a).toNat : Int) ≡ (l.bal a).toNat + (c.credit a : Int) - c.debit a
      [ZMOD 2 ^ 256] := by
  cases c with
  | deposit who v =>
    cases ok
    simp only [Call.credit, Call.debit, setBal_bal_apply]
    by_cases h : who = a
    · subst h
      simp only [↓reduceIte]
      refine (add_modEq _ _).trans ?_
      push_cast; ring_nf; rfl
    · simp only [Ne.symm h, h, ↓reduceIte]
      push_cast; ring_nf; rfl
  | withdraw who w =>
    simp only [Ledger.step] at ok
    split at ok
    · cases ok
    · cases ok
      simp only [Call.credit, Call.debit, setBal_bal_apply]
      by_cases h : who = a
      · subst h
        simp only [↓reduceIte]
        refine (sub_modEq _ _).trans ?_
        push_cast; ring_nf; rfl
      · simp only [Ne.symm h, h, ↓reduceIte]
        push_cast; ring_nf; rfl
  | transfer who dst w =>
    have := transferFrom_modEq (a := a) ok
    simpa only [Call.credit, Call.debit] using this
  | transferFrom who src dst w =>
    have := transferFrom_modEq (a := a) ok
    simpa only [Call.credit, Call.debit] using this
  | approve who g w =>
    cases ok
    simp only [Call.credit, Call.debit, Ledger.setAllow_bal]
    push_cast; ring_nf; rfl

/-- A successful run moves every balance by its inflow minus its outflow, modulo `2 ^ 256`. -/
theorem Ledger.run_netFlow {l l' : Ledger} {calls : List Call} (ok : l.run calls = some l')
    (a : Adr) :
    ((l'.bal a).toNat : Int) ≡ (l.bal a).toNat + (inflow calls a : Int) - outflow calls a
      [ZMOD 2 ^ 256] := by
  induction calls generalizing l with
  | nil =>
    cases ok
    simp only [inflow, outflow, List.map_nil, List.sum_nil]
    push_cast; ring_nf; rfl
  | cons c cs ih =>
    rw [Ledger.run_cons] at ok
    cases first : l.step c with
    | none => rw [first] at ok; cases ok
    | some mid =>
      rw [first] at ok
      have rest := ih (l := mid) ok
      have one := Ledger.step_netFlow first a
      refine rest.trans ?_
      refine (one.add_right _).sub_right _ |>.trans ?_
      simp only [inflow, outflow, List.map_cons, List.sum_cons]
      push_cast; ring_nf; rfl

/-- From the deployment ledger (no tracked key), a successful replay to the ledger read over exactly
the touched keys gives the net flow over storage. -/
theorem netFlow_of_replay {keys : List Key} {s s₀ : Stor} {calls : List Call}
    (replay : (ledger (fun _ => False) s₀).run calls =
      some (ledger (Key.extend (fun _ => False) keys) s)) :
    NetFlow keys calls s := by
  intro a member
  have flow := Ledger.run_netFlow replay a
  have start : (ledger (fun _ => False) s₀).bal a = 0 := by
    simp only [ledger, tracked, ↓reduceIte]
  have finish : (ledger (Key.extend (fun _ => False) keys) s).bal a = s.get (balSlot a) := by
    simp only [ledger, tracked]
    exact ite_eq_left
      (Or.inr (mem_balHolders.mp member) : Key.extend (fun _ => False) keys (.bal a))
  rw [start, finish, B256.toNat_zero] at flow
  refine flow.trans ?_
  push_cast; ring_nf; rfl

end Blanc.Lift.Weth9
