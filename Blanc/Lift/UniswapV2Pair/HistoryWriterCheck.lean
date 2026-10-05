import Blanc.Lift.UniswapV2Pair.Check
import Blanc.Lift.ReachWalk

/-! Small contract-local certificates for the noncalling writer routes. Kept
separate so the language-server proof loop imports the kernel-checked facts. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive NoncallingWriter where
  | approve | transfer | transferFrom | initialize

def NoncallingWriter.selector : NoncallingWriter → B256
  | .approve => 0x095ea7b3
  | .transfer => 0xa9059cbb
  | .transferFrom => 0x23b872dd
  | .initialize => 0x485cc955

def NoncallingWriter.wrapper : NoncallingWriter → SFunc
  | .approve => t_0315_c96
  | .transfer => t_055e_c85
  | .transferFrom => t_03ad_c93
  | .initialize => t_041e_c90

/-- The closed exec-free components of this literal certificate. -/
def historyWriterExecFreeEntries : List Nat :=
  [1, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
   25, 26, 27, 28, 30, 32, 33, 35, 36, 38, 39, 40, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 55, 56, 58, 59, 60, 61, 62, 63, 64, 65, 66, 69,
   70, 72, 73, 74, 75, 77, 79, 81, 82, 84, 85, 87, 88, 89, 90, 91, 92, 93,
   94, 95, 96, 97, 98, 100, 101]

theorem historyWriterExecFreeEntries_set :
    ExecFreeSet cert.prog historyWriterExecFreeEntries = true := by
  decide +kernel

theorem NoncallingWriter.wrapper_execFree (writer : NoncallingWriter) :
    writer.wrapper.execFreeIn historyWriterExecFreeEntries = true := by
  cases writer <;> decide +kernel

theorem historyWriterRevert_execFree :
    t_000c_c0.execFreeIn historyWriterExecFreeEntries = true ∧
    t_01b9_c0.execFreeIn historyWriterExecFreeEntries = true := by
  decide +kernel

end Blanc.Lift.UniswapV2Pair
