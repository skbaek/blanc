import Blanc.Lift.ExactWalkCut
import Blanc.ForwardSha256
import Blanc.ForwardStorageAccess
import Jaune.WordFacts
import Blanc.Lift.ExactWalkCutOps

/-!
# More walk steps for exact runs and exact cut runs

Companions to `Blanc/Lift/ExactWalk.lean`, `ExactWalkOps.lean` and
`ExactWalkCut.lean` for what a solc `sha256(abi.encodePacked(…))` site and a
storage read of a state-dependent key need:

* `SLOAD` with the warm/cold choice left to the neutral carriers `sloadCost`
  and `afterSload` (`Blanc/ForwardCall.lean`), so one lemma covers both;
* `GAS`, `RETURNDATASIZE`, an `MLOAD` that extends memory;
* the `STATICCALL` of the SHA-256 precompile over a 64-byte window
  (`Ninst.runCompiled_staticcall_sha256_64_warm`), whose successor's world
  is only known through `ShaCallPost`;
* for exact cut runs (`SFunc.RunExactCut`), the same steps and the named-value
  binary operations and `CALLDATACOPY`, plus the goto `rxc_jump` into an entry outside the
  cut.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## Word arithmetic on small pointers -/

/-! ## What the SHA-256 precompile call leaves -/

theorem BaseRel.trans {b b' b'' : Devm} (h1 : BaseRel b b') (h2 : BaseRel b' b'') :
    BaseRel b b'' :=
  ⟨fun a => (h2.stor a).trans (h1.stor a), fun a => (h2.code a).trans (h1.code a),
    h2.addrs.trans h1.addrs, h2.logs.trans h1.logs, h2.output.trans h1.output,
    h2.error.trans h1.error⟩

/-! ## Exact-run steps -/

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f g : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

end Steps

/-! ## Exact cut-run steps -/

section CutSteps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f g : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

/-- An internal call that returns, inside a cut run (the callee runs uncut). -/
theorem rxc_callRet {d : B256} {j : Nat} {D : Devm} (hj : fs[j]? = some g)
    (hcall : SFunc.RunExact fs sevm (St b S M G) g (.returned D))
    (k : SFunc.RunExactCut fs sevm C D f r) :
    SFunc.RunExactCut fs sevm C (St b (d :: S) M (G + 8)) (.callNext j f) r :=
  .callRet d hj popBurnBy_St1 hcall k

end CutSteps

end Blanc.Lift
