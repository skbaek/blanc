import Blanc.Lift.FreePtrChain
import Blanc.Lift.WriteSite

/-! Range assembly of `wsCert` from range decisions (contract-neutral): the write-site instance
of the generic kit `chainRange`/`chainFrom` (`Blanc/Lift/FreePtrChain.lean`). -/

namespace Blanc.Lift.WriteSite

open Jaune

/-- The write-site walk of one certificate entry under its annotation. -/
def wsChk (c : Cert) (ann : List WAnn) (p : Entry × SFunc) (A : WAnn) : Bool :=
  wsNode c.entries ann A.ret p.1.frame A.entry p.2

/-- Every entry from `k` on passes: the third conjunct of `wsCert c ann` at `k = 0`. -/
def wsFrom (c : Cert) (ann : List WAnn) (k : Nat) : Bool := chainFrom (wsChk c ann) c ann k

/-- The entries `k .. k + n - 1` pass the write-site walk: one generated kernel decision. -/
def wsRange (c : Cert) (ann : List WAnn) (k n : Nat) : Bool :=
  chainRange (wsChk c ann) c ann k n

/-- One link of the chain. -/
theorem wsFrom_range {c : Cert} {ann : List WAnn} (k n : Nat) (h : wsRange c ann k n = true)
    (hrest : wsFrom c ann (k + n) = true) : wsFrom c ann k = true :=
  chainFrom_range k n h hrest

/-- The chain's end: past the last entry nothing is left to check. -/
theorem wsFrom_of_le {c : Cert} {ann : List WAnn} {k : Nat} (h : c.length ≤ k) :
    wsFrom c ann k = true :=
  chainFrom_of_le h

/-- Assemble `wsCert` from its head conditions and the chain. -/
theorem wsCert_of_wsFrom {c : Cert} {ann : List WAnn}
    (hhead : (ann.length == c.length && (ann[0]?.map WAnn.entry) == some WSt.init) = true)
    (h : wsFrom c ann 0 = true) : wsCert c ann = true := by
  unfold wsCert
  unfold wsFrom chainFrom at h
  rw [List.drop_zero] at h
  rw [hhead]
  exact h

end Blanc.Lift.WriteSite
