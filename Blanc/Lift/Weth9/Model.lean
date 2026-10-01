import Blanc.BalanceAlgebra

/-!
# The WETH9 pure model

The deployed WETH9 (solc 0.4.19) is a token whose state is two mappings, `balanceOf` and `allowance`, and
whose only external effect is the ETH the contract holds (received by `deposit`, sent by `withdraw`).
`Ledger` is the two mappings as functions on addresses; `Call` is a writer call with its message sender
(and, for `deposit`, its callvalue); `Ledger.step` is the call's effect, `none` when the call reverts.
Arithmetic is on 256-bit words, exactly the runtime's (`+` and `-` wrap), and the model follows the
runtime's control flow, which the bytecode walks confirm:

* `withdraw(wad)` reverts unless `wad ≤ balanceOf[sender]`, then debits (the ETH send follows);
* `transferFrom(src, dst, wad)` reverts unless `wad ≤ balanceOf[src]`; if `src ≠ sender` and
  `allowance[src][sender] ≠ 2^256 - 1` it further requires `wad ≤ allowance[src][sender]` and debits the
  allowance (the maximal allowance is an infinite sentinel in this code); then it debits `src` and credits
  `dst` one after the other, so a self-transfer is the identity;
* `transfer(dst, wad)` is `transferFrom(sender, dst, wad)`, which never touches the allowance;
* `approve(guy, wad)` overwrites `allowance[sender][guy]`;
* `deposit` (and the payable fallback) credits `balanceOf[sender]` with the callvalue.

The contract's ETH is tracked by `State` alongside the ledger.  `State.step_backed` and `Ledger.step_sum_le`
say the ledger stays backed by the ETH moved in and out, with no overflow hypothesis: a wrapped credit can
only shrink the natural-number total.  `Ledger.sum_run` is the conservation identity over a run.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc

/-- The two mappings of WETH9: `balanceOf` and `allowance[owner][spender]`. -/
structure Ledger where
  bal : Adr → B256
  allow : Adr → Adr → B256

/-- A writer call of WETH9 with its message sender; `deposit` carries the callvalue. -/
inductive Call
  | deposit (who : Adr) (value : B256)
  | withdraw (who : Adr) (wad : B256)
  | transfer (who dst : Adr) (wad : B256)
  | transferFrom (who src dst : Adr) (wad : B256)
  | approve (who guy : Adr) (wad : B256)

/-- The maximal allowance, which `transferFrom` does not debit. -/
def maxAllowance : B256 := B256.max

namespace Ledger

/-- Overwrite one balance. -/
def setBal (l : Ledger) (a : Adr) (w : B256) : Ledger :=
  { l with bal := Function.update l.bal a w }

/-- Overwrite one allowance. -/
def setAllow (l : Ledger) (o p : Adr) (w : B256) : Ledger :=
  { l with allow := Function.update l.allow o (Function.update (l.allow o) p w) }

/-- `balanceOf[src] -= wad; balanceOf[dst] += wad`, in that order. -/
def xfer (l : Ledger) (src dst : Adr) (wad : B256) : Ledger :=
  let l₁ := l.setBal src (l.bal src - wad)
  l₁.setBal dst (l₁.bal dst + wad)

/-- `transferFrom(src, dst, wad)` called by `who`. -/
def transferFrom (l : Ledger) (who src dst : Adr) (wad : B256) : Option Ledger :=
  if l.bal src < wad then none
  else if src ≠ who ∧ l.allow src who ≠ maxAllowance then
    if l.allow src who < wad then none
    else some ((l.setAllow src who (l.allow src who - wad)).xfer src dst wad)
  else some (l.xfer src dst wad)

/-- One call's effect on the ledger, `none` when it reverts. -/
def step (l : Ledger) : Call → Option Ledger
  | .deposit who v => some (l.setBal who (l.bal who + v))
  | .withdraw who w => if l.bal who < w then none else some (l.setBal who (l.bal who - w))
  | .transfer who dst w => l.transferFrom who who dst w
  | .transferFrom who src dst w => l.transferFrom who src dst w
  | .approve who g w => some (l.setAllow who g w)

/-- Run a list of calls in order. -/
def run (l : Ledger) : List Call → Option Ledger
  | [] => some l
  | c :: cs => (l.step c).bind fun l' => l'.run cs

@[simp] theorem run_nil (l : Ledger) : l.run [] = some l := rfl

@[simp] theorem run_cons (l : Ledger) (c : Call) (cs : List Call) :
    l.run (c :: cs) = (l.step c).bind fun l' => l'.run cs := rfl

theorem run_append (l : Ledger) (xs ys : List Call) :
    l.run (xs ++ ys) = (l.run xs).bind fun l' => l'.run ys := by
  induction xs generalizing l with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append, run_cons]
      cases l.step c with
      | none => rfl
      | some l' => exact ih l'

/-- The total booked balance, as a natural number. -/
def total (l : Ledger) : Nat := sum l.bal

@[simp] theorem setBal_bal (l : Ledger) (a : Adr) (w : B256) : (l.setBal a w).bal = Function.update l.bal a w := rfl
@[simp] theorem setBal_allow (l : Ledger) (a : Adr) (w : B256) : (l.setBal a w).allow = l.allow := rfl
@[simp] theorem setAllow_bal (l : Ledger) (o p : Adr) (w : B256) : (l.setAllow o p w).bal = l.bal := rfl

theorem increase_setBal (l : Ledger) (a : Adr) (v : B256) :
    Increase a v l.bal (l.setBal a (l.bal a + v)).bal := by
  intro b
  by_cases h : a = b
  · subst h
    refine ⟨fun _ => ?_, fun h' => absurd rfl h'⟩
    simp only [setBal_bal, Function.update_self]
  · refine ⟨fun h' => absurd h' h, fun _ => ?_⟩
    simp only [setBal_bal, Function.update_of_ne (Ne.symm h)]

theorem decrease_setBal (l : Ledger) (a : Adr) (v : B256) :
    Decrease a v l.bal (l.setBal a (l.bal a - v)).bal := by
  intro b
  by_cases h : a = b
  · subst h
    refine ⟨fun _ => ?_, fun h' => absurd rfl h'⟩
    simp only [setBal_bal, Function.update_self]
  · refine ⟨fun h' => absurd h' h, fun _ => ?_⟩
    simp only [setBal_bal, Function.update_of_ne (Ne.symm h)]

/-- A credit raises the total by at most the credit. -/
theorem sum_deposit_le (l : Ledger) (a : Adr) (v : B256) :
    (l.setBal a (l.bal a + v)).total ≤ l.total + v.toNat :=
  sum_increase_le (increase_setBal l a v)

/-- A debit of at most the holder's balance lowers the total by exactly the debit. -/
theorem sum_withdraw (l : Ledger) (a : Adr) {v : B256} (h : v ≤ l.bal a) :
    (l.setBal a (l.bal a - v)).total + v.toNat = l.total := by
  have hs := sum_sub_assoc (decrease_setBal l a v) h
  have hle : v.toNat ≤ sum l.bal := (B256.toNat_le_toNat h).trans le_sum
  unfold total
  omega

/-- A balance transfer does not raise the total, even when the credit wraps. -/
theorem sum_xfer_le (l : Ledger) (src dst : Adr) {wad : B256} (h : wad ≤ l.bal src) :
    (l.xfer src dst wad).total ≤ l.total := by
  unfold xfer total
  exact transfer_does_not_increase_sum
    (b := l.bal) (d := ((l.setBal src (l.bal src - wad)).setBal dst
      ((l.setBal src (l.bal src - wad)).bal dst + wad)).bal) (kd := src) (ki := dst) (v := wad)
    ⟨h, (l.setBal src (l.bal src - wad)).bal, decrease_setBal l src wad,
      increase_setBal (l.setBal src (l.bal src - wad)) dst wad⟩

theorem transferFrom_total_le {l l' : Ledger} {who src dst : Adr} {wad : B256}
    (h : l.transferFrom who src dst wad = some l') : l'.total ≤ l.total := by
  unfold transferFrom at h
  split at h
  · cases h
  rename_i hb
  have hle : wad ≤ l.bal src := B256.not_lt.mp hb
  split at h
  · split at h
    · cases h
    · cases h
      have := sum_xfer_le (l.setAllow src who (l.allow src who - wad)) src dst
        (wad := wad) (by simpa only [setAllow_bal] using hle)
      simpa only [total, ge_iff_le, setAllow_bal] using this
  · cases h
    exact sum_xfer_le l src dst hle

theorem step_deposit (l : Ledger) (who : Adr) (v : B256) :
    l.step (.deposit who v) = some (l.setBal who (l.bal who + v)) := rfl

theorem step_withdraw (l : Ledger) (who : Adr) (w : B256) :
    l.step (.withdraw who w) =
      if l.bal who < w then none else some (l.setBal who (l.bal who - w)) := rfl

theorem step_transfer (l : Ledger) (who dst : Adr) (w : B256) :
    l.step (.transfer who dst w) = l.transferFrom who who dst w := rfl

theorem step_transferFrom (l : Ledger) (who src dst : Adr) (w : B256) :
    l.step (.transferFrom who src dst w) = l.transferFrom who src dst w := rfl

theorem step_approve (l : Ledger) (who g : Adr) (w : B256) :
    l.step (.approve who g w) = some (l.setAllow who g w) := rfl

end Ledger

/-- The ETH a call brings into the contract. -/
def Call.inflow : Call → Nat
  | .deposit _ v => v.toNat
  | _ => 0

/-- The ETH a call sends out of the contract. -/
def Call.outflow : Call → Nat
  | .withdraw _ w => w.toNat
  | _ => 0

namespace Ledger

/-- **A call does not raise the total by more than the callvalue it credits.** -/
theorem step_total_le {l l' : Ledger} {c : Call} (h : l.step c = some l') :
    l'.total ≤ l.total + c.inflow := by
  cases c with
  | deposit who v =>
      rw [step_deposit] at h
      cases h
      exact sum_deposit_le l who v
  | withdraw who w =>
      rw [step_withdraw] at h
      by_cases hb : l.bal who < w
      · simp only [hb, ↓reduceIte] at h; cases h
      · simp only [hb, ↓reduceIte] at h
        cases h
        have := sum_withdraw l who (B256.not_lt.mp hb)
        simp only [Call.inflow]
        omega
  | transfer who dst w =>
      rw [step_transfer] at h
      exact (transferFrom_total_le h).trans (Nat.le_add_right _ _)
  | transferFrom who src dst w =>
      rw [step_transferFrom] at h
      exact (transferFrom_total_le h).trans (Nat.le_add_right _ _)
  | approve who g w =>
      rw [step_approve] at h
      cases h
      simp only [total, setAllow_bal, Call.inflow, add_zero, Std.le_refl]

end Ledger

/-- The ledger together with the contract's ETH. -/
structure State where
  ledger : Ledger
  eth : Nat

namespace State

/-- One call: the ledger step, and the ETH it moves. -/
def step (s : State) (c : Call) : Option State :=
  (s.ledger.step c).map fun l => ⟨l, s.eth + c.inflow - c.outflow⟩

/-- The ledger is backed by the ETH. -/
def Backed (s : State) : Prop := s.ledger.total ≤ s.eth

/-- **Backing is invariant**, with no overflow hypothesis. -/
theorem step_backed {s s' : State} {c : Call} (backed : s.Backed) (h : s.step c = some s') :
    s'.Backed := by
  unfold step at h
  cases hl : s.ledger.step c with
  | none => rw [hl] at h; cases h
  | some l' =>
    rw [hl] at h
    cases h
    have hle := Ledger.step_total_le hl
    unfold Backed at backed
    show l'.total ≤ s.eth + c.inflow - c.outflow
    cases c with
    | withdraw who w =>
        rw [Ledger.step_withdraw] at hl
        by_cases hb : s.ledger.bal who < w
        · simp only [hb, ↓reduceIte] at hl; cases hl
        · simp only [hb, ↓reduceIte] at hl
          cases hl
          have := Ledger.sum_withdraw s.ledger who (B256.not_lt.mp hb)
          simp only [Call.inflow, Call.outflow]
          omega
    | deposit who v =>
        simp only [Call.inflow, Call.outflow] at hle ⊢
        omega
    | transfer who dst w =>
        simp only [Call.inflow, Call.outflow] at hle ⊢
        omega
    | transferFrom who src dst w =>
        simp only [Call.inflow, Call.outflow] at hle ⊢
        omega
    | approve who g w =>
        simp only [Call.inflow, Call.outflow] at hle ⊢
        omega

/-- Run a list of calls in order. -/
def run (s : State) : List Call → Option State
  | [] => some s
  | c :: cs => (s.step c).bind fun s' => s'.run cs

theorem run_backed {s s' : State} {cs : List Call} (backed : s.Backed)
    (h : s.run cs = some s') : s'.Backed := by
  induction cs generalizing s with
  | nil => cases h; exact backed
  | cons c cs ih =>
      simp only [run] at h
      cases hs : s.step c with
      | none => rw [hs] at h; cases h
      | some t =>
          rw [hs] at h
          exact ih (step_backed backed hs) h

/-- The ledger part of a state run is the ledger run. -/
theorem run_ledger (s : State) (cs : List Call) :
    (s.run cs).map State.ledger = s.ledger.run cs := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
      simp only [run, Ledger.run_cons, step]
      cases hl : s.ledger.step c with
      | none => rfl
      | some l' => simpa [Option.bind] using ih ⟨l', s.eth + c.inflow - c.outflow⟩

end State

end Blanc.Lift.Weth9
