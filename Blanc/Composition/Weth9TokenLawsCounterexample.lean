import Blanc.Composition.Weth9Token

/-!
# Evidence: the frozen `weth9Book_laws` is false (statement defect, U4)

`BookLaws.holder_debit` asks a holder's own holder-safe call to debit it by at most the declared
amount, under `Good l := l.total < 2 ^ 256` of the incoming ledger only.  A WETH9 deposit is `.credit`
(holder-safe, declared debit `0`), and the model credits `bal who + value` modulo `2 ^ 256`: a holder
with one unit depositing `B256.max` wraps to `0` although the incoming total is `1`.  `Good` cannot see
the deposit's value, so no per-ledger predicate fixes this; the master's amendment decides the repair.

This file exists only to carry the kernel-checked counterexample to the master.
-/

namespace Blanc.Composition.Weth9Token

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token

/-- A fallback deposit of `B256.max` by address `0` (empty calldata). -/
def depositWitness : Sevm := { (default : Sevm) with value := B256.max }

theorem depositWitness_decode :
    decodeCall depositWitness = some (.deposit 0 B256.max) := by
  have short : shortCall depositWitness := by decide +kernel
  unfold decodeCall
  rw [ite_eq_left short]
  rfl

theorem depositWitness_op : weth9Op depositWitness = .credit := by
  have short : shortCall depositWitness := by decide +kernel
  unfold weth9Op
  rw [ite_eq_right (fun h => h.1 short), depositWitness_decode]

/-- **The frozen `weth9Book_laws` is false**: `holder_debit` fails at a wrapping deposit. -/
theorem weth9Book_not_laws : ¬ BookLaws weth9Book := by
  intro laws
  have good : weth9Book.Good (oneLedger 0) := by
    change (oneLedger 0).total < 2 ^ 256
    have := oneLedger_total 0
    omega
  have step : weth9Book.step (oneLedger 0) depositWitness =
      some ((oneLedger 0).setBal 0 ((oneLedger 0).bal 0 + B256.max)) := by
    have h : weth9Book.step (oneLedger 0) depositWitness =
        (oneLedger 0).step (.deposit 0 B256.max) := by
      unfold weth9Book
      dsimp only
      rw [depositWitness_decode]
    rw [h]
    rfl
  have safe : (weth9Book.op depositWitness).HolderSafe := by
    change (weth9Op depositWitness).HolderSafe
    rw [depositWitness_op]
    trivial
  have debit := laws.holder_debit good step rfl safe
  change ((oneLedger 0).bal 0).toNat ≤
    (((oneLedger 0).setBal 0 ((oneLedger 0).bal 0 + B256.max)).bal 0).toNat +
      (weth9Op depositWitness).debit 0 at debit
  rw [depositWitness_op] at debit
  exact absurd debit (by decide +kernel)

end Blanc.Composition.Weth9Token
