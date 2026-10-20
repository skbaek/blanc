import Blanc.Lift.FreePtrChain
import Blanc.Lift.WriteSite

/-! Chain assembly of `wsCert` from per-entry decisions (contract-neutral): the write-site
instance of the generic chain kit `chainEntry`/`chainFrom` (`Blanc/Lift/FreePtrChain.lean`). -/

namespace Blanc.Lift.WriteSite

open Jaune

/-- The write-site walk of one certificate entry under its annotation. -/
def wsChk (c : Cert) (ann : List WAnn) (p : Entry × SFunc) (A : WAnn) : Bool :=
  wsNode c.entries ann A.ret p.1.frame A.entry p.2

/-- Entry `k` passes the write-site walk under its annotation (`false` past either end). -/
def wsEntry (c : Cert) (ann : List WAnn) (k : Nat) : Bool := chainEntry (wsChk c ann) c ann k

/-- Every entry from `k` on passes: the third conjunct of `wsCert c ann` at `k = 0`. -/
def wsFrom (c : Cert) (ann : List WAnn) (k : Nat) : Bool := chainFrom (wsChk c ann) c ann k

/-- One step of the chain. -/
theorem wsFrom_step {c : Cert} {ann : List WAnn} (k : Nat) (h : wsEntry c ann k = true)
    (hrest : wsFrom c ann (k + 1) = true) : wsFrom c ann k = true :=
  chainFrom_step k h hrest

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
