import Blanc.Lift.StaticCall

/-!
# A callee silent on one selector (contract-neutral seam predicate, A11)

`NoStaticAnswer code sel`: no static child message to an account holding `code`,
outside the precompile range, answers calldata whose selector is `sel`.  This is
the contract-neutral shape of `not_staticAnswered_pair` (the Pair proves the
instance for its own code in `Blanc.Lift.UniswapV2Pair.StaticSilent`; the USDC
library side takes it as the hypothesis `hsilent`, discharged in composition).
Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.Lift

/-- **Code `code` answers no static call with selector `sel`.**  A static child
message to an account holding `code`, whose code address is not a precompile,
with calldata whose selector is `sel`, never settles cleanly. -/
def NoStaticAnswer (code : ByteArray) (sel : B256) : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {t : Adr} {input out : Bytes},
    b.getCode t = code → ¬ sevm.benvStat.rules.isPrecomp t →
    CoveredFork sevm.benvStat.fork →
    (∀ e : Sevm, e.data = input → Blanc.Sevm.selector e = sel) →
    ¬ StaticAnswered sevm b t input out

end Blanc.Lift
