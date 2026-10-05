import Blanc.Lift.ExactWalkMemory
import Blanc.Lift.UniswapV2Pair.WriterStorage

/-! Cut interface of the actual swap body at the post-callback join `0x09c3`
(certificate entry `t_09c3_c5`, stack shape `[11 × .unk, .ret]`).

Both successful arms reach this entry with the same eleven words: the callback
arm after the successful `CALL` at `0x09ad` and its four pops at `0x09be`, and
the no-callback arm by the `JUMPI` at `0x08e7` (`data.length = 0`). The front
half (pc 0 to here) establishes `SwapCut`; the back half (the two post-callback
`balanceOf` STATICCALLs, input inference, the SafeMath `K` check, `_update`, the
`Swap` log and the unlock) consumes it.

The free pointer `p` is a parameter: each optimistic `_safeTransfer` allocates
its call payload and its optional reply, so `p` depends on the transfers taken
and on the tokens' reply lengths. The callback payload is built at `p` without
moving it. The back half itself never moves `p`. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The eleven body words live at `0x09c3`, named by their source meaning.
`reserve0/1` are the cached `getReserves` values, `token0/1` the cached
`token0`/`token1` loads, and `dataOffset/dataLength` the ABI calldata view of
`data` (unused after the join). -/
structure SwapCutWords where
  token1 : B256
  token0 : B256
  reserve1 : B256
  reserve0 : B256
  dataLength : B256
  dataOffset : B256
  recipient : B256
  amount1Out : B256
  amount0Out : B256

/-- Actual stack at `0x09c3`, top first. The two zero words are the still
unassigned `balance1` and `balance0` locals; `ρ` is the body's return address
(the wrapper's `0x0257`). -/
def swapCutStack (w : SwapCutWords) (ρ : B256) (R : List B256) : List B256 :=
  w.token1 :: w.token0 :: 0 :: 0 :: w.reserve1 :: w.reserve0 :: w.dataLength ::
    w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: ρ :: R

/-- What the machine at `0x09c3` must satisfy for the back half, relative to the
suspended typed frame `frame` (whose next request is `balanceOf(pair)` to
`locals.token0`) and its swap locals. Pair storage is the locked finite
representation of the frame's current typed state; foreign storage and the
remaining machine state are unconstrained. -/
structure SwapCut (K : WriterKey → Prop) (frame : Frame) (locals : SwapLocals)
    (sevm : Sevm) (d : Devm) (w : SwapCutWords) (p : B256) (n : Nat) (M : Mem) : Prop where
  /-- Well-formed memory with the free pointer word `p` at `0x40`. -/
  mem : PtrMem p n M
  /-- The free pointer lies above the reserved scratch and zero slots. -/
  lower : 128 ≤ p.toNat
  /-- Pointer arithmetic over the back half's scratch area does not wrap. -/
  width : p.toNat + 260 < 2 ^ 256
  /-- The frame's return buffer is still empty. -/
  output : d.output = []
  /-- Locked finite Pair storage represents the frame's current typed state. -/
  rep : WriterRep K (d.getStor sevm.currentTarget) frame.current.state
  locked : frame.current.state.unlocked = 0
  pair : frame.context.pair = sevm.currentTarget
  sender : frame.context.sender = sevm.caller
  time : frame.context.timestamp = sevm.benvStat.time
  token0 : w.token0 = locals.token0.toB256
  token1 : w.token1 = locals.token1.toB256
  reserve0 : w.reserve0 = Nat.toB256 locals.reserves.reserve0.val
  reserve1 : w.reserve1 = Nat.toB256 locals.reserves.reserve1.val
  recipient : w.recipient = locals.recipient.toB256
  amount0Out : w.amount0Out = locals.amount0Out
  amount1Out : w.amount1Out = locals.amount1Out
  /-- The `INSUFFICIENT_LIQUIDITY` guard already passed. -/
  out0 : locals.amount0Out.toNat < locals.reserves.reserve0.val
  out1 : locals.amount1Out.toNat < locals.reserves.reserve1.val

end Blanc.Lift.UniswapV2Pair
