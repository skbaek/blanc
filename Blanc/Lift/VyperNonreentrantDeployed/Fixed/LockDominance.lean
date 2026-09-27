import Blanc.Lift.LockCheckFlow
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Check
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.LockCheck

/-!
# Dominance of the corrected comparator's reentrancy lock

The corrected Vyper 0.3.7 comparator 0x847e (`Fixed/Cert.lean`) meets the
per-code obligation `LockSpec.Dominance` of `Blanc/LockExclusion.lean` for its
lock (`Fixed/LockSpec.lean`: slot `0`, held word `2`, seven guarded bodies,
five mutating), with the strong form (inside a guarded mutating body only the
five release `SSTORE`s write the slot) and the absence of `DELEGATECALL`,
`CALLCODE`, `CREATE`, `CREATE2` and `SELFDESTRUCT`.

Each is `LockCheck.dominance` (`Blanc/Lift/LockCheckFlow.lean`) applied to the
certificate check `cert_check` and the lock check `lock_cert`; both kernel
decisions live in their own modules, so this module elaborates none.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed

open Jaune Blanc.LockExclusion Blanc.Lift.LockCheck

/-- The comparator's lock as a `LockSpec` over its runtime. -/
def lockL : LockSpec := ⟨code, 0, 2, lockBodies, lockMutBodies⟩


/-- **The comparator's lock dominance.** -/
theorem lock_dominance : lockL.Dominance :=
  dominance cert_check lock_cert

/-- **Strong form.**  In a frame of the comparator, once a mutating body
start is reached, every slot-addressed `SSTORE` at or after it is a release
`SSTORE`. -/
theorem lock_dominance_strong {F : Exec.Deriv} (hpc : F.pc = 0)
    (hfork : CoveredFork F.sevm.benvStat.fork) (hcode : F.sevm.code = code)
    (hhash : HashAvoid 0 F) {b n : Exec.Deriv} (hb : Exec.Deriv.ParentPrefix F b)
    (hbn : Exec.Deriv.ParentPrefix b n) (hmb : b.pc ∈ lockMutBodies)
    (hst : SstoreAt n 0) : n.pc ∈ lockReleasePcs :=
  dominance_strong cert_check lock_cert hpc hfork hcode hhash hb hbn hmb hst

/-- **No forbidden opcode.**  No node of a comparator frame executes
`DELEGATECALL`, `CALLCODE`, `CREATE`, `CREATE2` or `SELFDESTRUCT`. -/
theorem lock_no_forbidden {F : Exec.Deriv} (hpc : F.pc = 0)
    (hfork : CoveredFork F.sevm.benvStat.fork) (hcode : F.sevm.code = code)
    (hhash : HashAvoid 0 F) {n : Exec.Deriv} (hp : Exec.Deriv.ParentPrefix F n) :
    (∀ x, Ninst.At n.sevm.code n.pc (.exec x) → x = .call ∨ x = .staticcall) ∧
      ¬ Linst.At n.sevm.code n.pc .selfdestruct :=
  no_forbidden cert_check lock_cert hpc hfork hcode hhash hp

end Blanc.Lift.VyperNonreentrantDeployed.Fixed
