import Blanc.Lift.MapSlot
import Blanc.Lift.InvWalkOps
import Blanc.Lift.WalkSteps
import Blanc.Lift.HistAccessWalk
import Blanc.Lift.WalkInvKit

/-!
# Vyper 0.2.x front end: the frame prologue and mapping slots

Vyper 0.2.x runtimes (no internal calls) start every frame past the `CALLDATASIZE < 4` test with a
fixed prologue: `mstore(0x1c, calldataload(0))`, so that `mload(0)` is the selector, and five
clamp constants at `0x20 … 0xa0` (`2^160` for address arguments at `0x20`; the `int128` and
`decimal` bounds at `0x40 … 0xa0`).  The walks carry them in memory:

* `vyPrologue f`: the prologue as a lifted tree before `f`; `ric_vyPrologue` (inverted, over any
  memory) and `rx_vyPrologue` (forward from empty memory, 75 gas);
* `vyMem M w`: memory after it; `VyClamps img`: the five constants in a memory image
  (`vyImg_clamps` establishes it, `VyClamps.clamp` reads the address clamp);
* `mapSlot slot key` (`MapSlot.lean`) is Vyper's `HashMap` slot `keccak(slot ‖ key)`, and
  `vySlot_read` the scratch window `mstore(0xe0, key); mstore(0xc0, slot)` hashes.

The world-touching steps are proved for any fork from the rule facts they read, over the actual
access schedule's successors (`afterSloadH`, `afterSstoreH`) and charges (`sloadCostH`,
`sstoreCostH`): the inversions `ric_vySubStoreH`, `ric_vyAddStoreH`, `ric_vyLoadIterH`,
`ric_vyStoreIterH` exist only in that form, and the forward passes (`rx_vySubStore`,
`rx_vyAddStore`, `rx_vyLoadStep`/`Last`, `rx_vyStoreStep`/`Last`) are the `CoveredFork`
corollaries of their `…H` forms over the EIP-2929 ones.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The clamp constants, as the prologue pushes them -/

/-- `2^160`, the address clamp at `0x20`. -/
abbrev vyC20 : Bytes := [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
/-- `2^127 - 1` at `0x40`. -/
abbrev vyC40 : Bytes := [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff]
/-- `-2^127` at `0x60`. -/
abbrev vyC60 : Bytes := [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00]
/-- The largest `decimal` at `0x80`. -/
abbrev vyC80 : Bytes := [0x01, 0x2a, 0x05, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xfd, 0xab, 0xf4, 0x1c, 0x00]
/-- The smallest `decimal` at `0xa0`. -/
abbrev vyCa0 : Bytes := [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
  0xd5, 0xfa, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00]

/-- Memory after the prologue over `M`, with `w` the calldata's first word. -/
def vyMem (M : Mem) (w : B256) : Mem :=
  ((((((M.write 28 w.toBytes).write 32 (Bytes.toB256 vyC20).toBytes).write 64
    (Bytes.toB256 vyC40).toBytes).write 96 (Bytes.toB256 vyC60).toBytes).write 128
    (Bytes.toB256 vyC80).toBytes).write 160 (Bytes.toB256 vyCa0).toBytes)

/-- Its image over an image `img` of `M`. -/
def vyImg (img : Bytes) (w : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 28
    w.toBytes) 32 (Bytes.toB256 vyC20).toBytes) 64 (Bytes.toB256 vyC40).toBytes) 96
    (Bytes.toB256 vyC60).toBytes) 128 (Bytes.toB256 vyC80).toBytes) 160
    (Bytes.toB256 vyCa0).toBytes

/-! ## The constants as a carried memory invariant -/

/-! ## The prologue, inverted and forward -/

section Walks

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f : SFunc} {r : Seg}

end Walks


/-! ## The two argument guards every function body starts with -/

section Guards

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f g ok : SFunc}

end Guards

/-! ## Mapping slots -/


/-! ## Mapping slots and checked storage updates, as trees -/

section Stores

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f : SFunc} {r : Seg}

end Stores
section StoresForward

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome}

end StoresForward

/-! ## The string load loop (storage to memory)

Vyper 0.2 copies a stored `String[n]` into memory with one loop: the stack is
`cap :: 0x120 :: lp :: dst :: base :: R` (`lp` the length word plus 32), and the counter `i`
lives in memory at `0x120`.  The head tests `32 i ≤ lp`; the body copies storage word `base + i`
to memory `dst + 32 i`, stores `i + 1` at `0x120`, and loops back to its entry `k` unless the
counter reached `cap`, when it falls through to `exitT`.  A failing test jumps to entry `j`.
The forward steps: `rx_vyLoadStep` (an iteration that loops back), `rx_vyLoadLast` (one that
falls through), `rx_vyLoadExit` (the failing test). -/

section LoadLoop

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
  {cap lp dst base : B256} {R : List B256} {e0 e1 x0 x1 r0 r1 : UInt8} {j k : Nat}
  {exitT : SFunc}

end LoadLoop

/-! ## The string store loop (memory to storage)

The setter's side of the string copy: stack `cap :: 0x120 :: lp :: base :: src :: R`, counter
`i` at `0x120`; while `32 i ≤ lp` it stores the memory word at `src + 32 i` to storage slot
`base + i`, bumps the counter, and loops back to its entry `k` unless the counter reached `cap`
(then `exitT`); a failing test jumps to entry `j`.  Forward: `rx_vyStoreStep`, `rx_vyStoreLast`,
`rx_vyStoreExit`; inverted: `ric_vyStoreIterH` (one pass, either way out). -/

/-- An `SSTORE`'s selected charge is at most a cold access plus a fresh set. -/
theorem sstoreCost_le (sevm : Sevm) (d : Devm) (key value : B256) :
    sstoreCost sevm d key value ≤ gasColdSload + gasStorageSet := by
  have hv : sstoreValueCost (d.getOrigStorVal sevm sevm.currentTarget key)
      (d.getStorVal sevm.currentTarget key) value ≤ gasStorageSet := by
    rw [sstoreValueCost]
    split_ifs <;> decide +kernel
  unfold sstoreCost
  split <;> omega

section StoreLoop

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
  {cap lp base src : B256} {R : List B256} {e0 e1 x0 x1 r0 r1 : UInt8} {j k : Nat}
  {exitT : SFunc}

end StoreLoop

section StoreHead

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {o : Outcome} {s0 s1 sl cp : UInt8} {loopT : SFunc}

end StoreHead

/-! ## A stored `String` view (storage to returned ABI string)

A Vyper 0.2 view of a stored `String[32 (cp - 1)]` at slot `sl`: the non-payable guard, the
string's base `keccak(sl)` via `mstore(0xc0, sl); keccak(0xc0, 0x20)`, the length word plus 32,
the counter `0` at `0x120`, and the load loop `loopT` (stack `vyLoadStack`, destination
`0x180`).  The join after the loop zero-pads with `CALLDATACOPY` from `CALLDATASIZE`
(`sliceD_data_end`) to `ceil32` (`ceil32_eq`). -/

end Blanc.Lift
