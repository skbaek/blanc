import Blanc.Lift.UniswapV2Factory.Cert
import Blanc.ExecutionLogImage

/-! The factory's final own LOG, over an entirely symbolic machine memory. -/
namespace Blanc.Lift.UniswapV2Factory.CreatePairInverse

open Jaune Blanc Blanc.Lift

/-- The factory's own PairCreated entry, before receipt authentication fixes
its symbolic CREATE2 result or the actual re-read count. -/
def symbolicPairCreated (sevm : Sevm) (w count : B256) : Log :=
  ⟨sevm.currentTarget,
    [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
     0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
     0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2], w.toBytes ++ count.toBytes⟩



/-- A successful factory LOG3 with its derived symbolic operands identifies
its own emitted entry. The memory remains an opaque projection of the node. -/
theorem own_log_image {node : Exec.Deriv} {post : Devm} {w count : B256} {rest : Stack}
    (success : node.exn = .ok post)
    (decoded : Ninst.At node.sevm.code node.pc (.reg (.log 3)))
    (stack : node.devm.stack = 11880 :: 64 ::
      0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9 ::
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 ::
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 :: rest)
    (payload : (node.devm.memory.read 11880 64).1 = w.toBytes ++ count.toBytes) :
    Exec.Deriv.successfulLog? node = some (symbolicPairCreated node.sevm w count) := by
  exact Exec.Deriv.successfulLog?_eq success decoded stack payload

end Blanc.Lift.UniswapV2Factory.CreatePairInverse
