import Blanc.Lift.Usdc.Footprint
import Blanc.Lift.Usdc.Governance
import Blanc.Lift.Usdc.Proxy.Contract
import Blanc.Lift.Usdc.Impl.Contract
import Blanc.Lift.Usdc.Lib.Contract

/-!
# USDC's checkpoint and trace-local premises (design §4.2, Appendix A §9)

`UsdcInstalled P w` is the one-world fact that the three certified runtimes (`proxySem`, `implSem`,
`libSem`) sit at the proxy, the implementation and the library, that the proxy's implementation
slot names the implementation, and that the proxy is neither of the other two addresses.
`UsdcHist P K₀ tr` bundles USDC's trace-local premises: the installed codes at the checkpoint, the
governance premise F2 (`UsdcGovernance`), the footprint invariant over `K₀` at the checkpoint, and
HASH-T over the keys the history touches (`KeysFresh`).  `checkUsdc` (`FiniteFootprint.lean`)
decides the checkpoint half on fetched rows.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift.Token

/-- The three runtimes installed, the implementation slot naming the implementation (state facts of
one world, like the Pair's `installed`). -/
structure UsdcInstalled (P : Adr) (w : State) : Prop where
  proxy : some (w.getCode P).toList = proxySem.image
  impl : some (w.getCode usdcImpl).toList = implSem.image
  lib : some (w.getCode usdcLib).toList = libSem.image
  slot : (w.getStor P).get implSlot = usdcImpl.toB256
  implApart : P ≠ usdcImpl
  libApart : P ≠ usdcLib

/-- USDC's trace-local premises: installed codes at the checkpoint, F2, the footprint invariant and
HASH-T over the keys the history touches. -/
def UsdcHist (P : Adr) (K₀ : Key → Prop) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  UsdcInstalled P checkpoint.state ∧ UsdcGovernance P tr ∧ FootInv K₀ (checkpoint.state.getStor P) ∧
    KeysFresh K₀ (historyTouchedKeys P tr)

end Blanc.Lift.Usdc
