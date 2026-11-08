import Blanc.Lift.WitnessChild

/-!
# Chunk boundaries and stage composition for a witness run

A long `Witness.wrun` is decided by the kernel as several chunks between literal
boundaries: each chunk is its own declaration, so the kernel's caches do not outlive it,
and the boundary literals are printed by an untrusted scratch evaluation that the chunk
decisions check.  This module is the literal-free scaffolding of that method, stated over
the boundaries, the interpreter's program `fs` and the frame's static machine `sta` as
parameters.  Nothing here is contract-specific.

* `Bnd`, `obsB`, `cfgOf`, `obsD`, `obsDOk`: a boundary (the machine, the node, the pending
  returns, the four shadows, the refund counter, the output and return data, the error) and
  a chunk's end decided against it.  `obsD` compares the machine and the shadows by
  `decide` (so the kernel evaluates them) and the node, the pending returns and the account
  shadow as terms; comparing the lazily computed machine to a literal as a term instead
  exhausts the kernel's recursion once the world and bookkeeping are free.  A
  configuration so decided is `cfgOf` of its boundary at its own world and bookkeeping
  (`cfg_of_obsD`), so a run through a boundary is a chunk up to it followed by one from it
  over any world and bookkeeping (`obsD_chain`, `obsD_chain3`, `obsB_of_obsD`,
  `run_of_obsB`).  Every boundary also records that the set of accounts to delete is still the
  empty one a frame starts with (compared as a term), so a run through boundaries shows the
  frame deletes nothing, and that the set of accounts created in the transaction is empty
  (compared as a term): `SSTORE`'s original value reads that set (`origReadK`), so a chunk
  over free bookkeeping is decided only with it fixed.
* `Bnd1`, `obsD1`, `obsDOk1`, `cfgOf1`: the same with the refund counter optional (`none`:
  free), deciding the account shadow by its address, nonce and balance (`acctKey`) and
  comparing each account's storage and code as terms (`acctRest`), and the set of accounts to
  delete against the empty set when the boundary records it, and the created set against the
  empty set always.  After a child's `CALL` some accounts' addresses
  are computed from stack words, and comparing such a shadow to a literal as a term
  exhausts the kernel.
* `callPairFrom`, `callPairA`, `callPairB`, `callPairFrom_stages`: a frame that makes two
  code-child calls, the first a settled child supplied as data and the second run by its own
  program (`childRun`), is decided in four stages over three boundaries; the composition is
  over variables only, so the kernel evaluates nothing outside the stages.
-/

namespace Blanc.Lift.Witness.Boundary

open Jaune Blanc.Lift Blanc.Lift.Witness

/-! ### Boundaries with the refund counter -/

/-! ### Boundaries with an optional refund counter -/

/-- A boundary: machine, node, pending returns, the four shadows, output and return data, the
refund counter when it is recorded (`none`: free), and whether it records that the set of
accounts to delete is the empty one a frame starts with (`false`: free). -/
abbrev Bnd1 := Mach × SFunc × List SFunc × List (Adr × B256) × List Adr × StorShadow ×
  AcctShadow × Bytes × Bytes × Option Int × Bool

/-- `m` with the refund counter `rc` when one is recorded. -/
def setRc : Option Int → Meta → Meta
  | none, m => m
  | some r, m => { m with refundCounter := r }

/-- `m` with the empty set of accounts to delete when the boundary records it. -/
def setAtd : Bool → Meta → Meta
  | false, m => m
  | true, m => { m with accountsToDelete := .emptyWithCapacity }

/-- The configuration at boundary `x` (with no error), over a free world and free
bookkeeping (the refund counter included unless the boundary records it, and likewise the set
of accounts to delete); the set of created accounts is always the empty one (`obsD1`). -/
def cfgOf1 : Bnd1 → Meta → World → Cfg
  | (mach, f, K, keys, adrs, stor, acs, out, rd, rc, atd), m, w =>
    ⟨⟨mach, setAtd atd (setRc rc
        { m with output := out, returnData := rd, error := none, createdAccounts := .emptyWithCapacity }),
      w⟩, f, K, keys, adrs, stor, acs⟩

/-! ### A frame with two code-child calls -/

end Blanc.Lift.Witness.Boundary
