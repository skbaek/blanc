import Blanc.Lift.UniswapV2Pair.Creation.DeployInit
import Blanc.Lift.UniswapV2Pair.ReplayWriterGas

/-! Replay and positive writer gas from the checkpoint established by the
actual CREATE2/initialize theorem. Configured-history authentication must still
produce the connected storage replay and its original source invocations. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The initialized deployment checkpoint carries the empty LP ledger. -/
theorem initializedState_ledger (factory : Adr) (domain : B256) (token0 token1 : Adr) :
    (initializedState factory domain token0 token1).Ledger :=
  (State.initialized_ledgerOn factory domain token0 token1).ledger

end Blanc.Lift.UniswapV2Pair
