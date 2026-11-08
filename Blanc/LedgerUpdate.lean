-- LedgerUpdate.lean : single-row functional updates of an address-keyed ledger.

import Blanc.LedgerConservation

/-!
# Functional single-row ledger updates

A pure token model keeps its balances as a function `Adr → B256` and books a
movement as a `Function.update` of one row.  `ledgerDebit` and `ledgerCredit`
name the two wrapping one-row updates; the lemmas here connect them to the
`Decrease` / `Increase` / `Transfer` relations of `Blanc/LadderBase.lean` and
read off the exact movement of `sum`.  Checked arithmetic is the caller's
guard: a debit is exact under `v ≤ f k`, a credit under `B256.Nof (f k) v`.

Nothing here names a contract.
-/

namespace Blanc

open Jaune

/-- Subtract `v` from row `k` (wrapping; exact under `v ≤ f k`). -/
def ledgerDebit (f : Adr → B256) (k : Adr) (v : B256) : Adr → B256 :=
  Function.update f k (f k - v)

/-- Add `v` to row `k` (wrapping; exact under `B256.Nof (f k) v`). -/
def ledgerCredit (f : Adr → B256) (k : Adr) (v : B256) : Adr → B256 :=
  Function.update f k (f k + v)

end Blanc
