import Blanc.Lift.UniswapV2Factory.TerminalSafety
import Blanc.ExecutionInstalledCertCuts

/-! Factory code preservation from a finite historical anchor to an actual cut.
The anchor and original history remain explicit; no constructor-from-scratch,
endpoint-code observation or assumed raw safety is required. -/
namespace Blanc.Lift.UniswapV2Factory

open Jaune Blanc.ExecutionTrace

/-- A finite code observation at an earlier checkpoint supplies factory code
at the original target transaction, through the original history and prefix. -/
theorem code_before_txSplit {wa : Adr} {F : Fork → Prop} {cfg : ChainConfig}
    {anchor pre post : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg anchor pre)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F)
    (installed : anchor.state.getCode wa = code) :
    cut.benv.state.getCode wa = code := by
  exact block.code_before_txSplit_of_runtimeSafety runtimeSafety cut capabilities
    (history.noDel_of_runtimeSafety runtimeSafety capabilities installed).2

/-- A factory anchor at an actual settled transaction cut can instead feed
an original mid-history, including its source block's remaining transactions. -/
theorem code_before_txSplit_of_midHistory {wa : Adr} {F : Fork → Prop}
    {cfg : ChainConfig} {anchor : Benv} {pre post : BlockChain}
    (history : MidHistoryTraceIn F cfg anchor pre)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F)
    (installed : anchor.state.getCode wa = code) :
    cut.benv.state.getCode wa = code := by
  exact history.code_before_txSplit_of_runtimeSafety runtimeSafety block cut capabilities installed

end Blanc.Lift.UniswapV2Factory
