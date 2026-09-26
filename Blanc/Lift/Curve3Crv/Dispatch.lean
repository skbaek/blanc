import Blanc.Lift.Curve3Crv.Spec
import Blanc.Lift.InvWalkWorld

/-!
# The dispatcher (entry 0 up to the thirteen bodies)

`CALLDATASIZE < 4` jumps to the fallback (entry 7, `revert(0, 0)`); otherwise the Vyper prologue
(`vyPrologue`) and a linear chain of thirteen tests `mload(0) == sel`, each `EQ ISZERO PUSH2 next
JUMPI`, falling through into its body on a hit; the last miss (`t_08dd_c0`) reverts.

* `safe_dispatch` (safety): a successful run from the frame's start entered body `k` with the
  selector `sels[k]`, from `entrySt`;
* `live_dispatch` (liveness): body `k`'s run from `entrySt` is a run of entry 0, for
  `dispatchGas k` more gas;
* `decodeCall_at`: the call `decodeCall` reads is the one body `k` implements.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Call)

-- SEGMENT: safeDispatch (about 150 nodes: prologue 19, size test 6, 13 tests of 8)
/-- **Dispatcher inversion.**

Proof sketch.  `run.cut`; `t_0000_c0`: `ri_push`, `ri_calldatasize`, `ri_lt`, `ri_iszero`,
`ri_push`, `ric_branch`: the fall-through arm is `t_0009_c0` (`PUSH2 0x08de; JUMP 7`), whose
target entry 7 (`t_08de_c7`) is `noOk`, so `ric_jump` then `false_of_noOk`; the taken arm gives
`4 ≤ sevm.data.length` (`toNat_ge_of_ltCheck_eq_zero`-style: `iszero (lt size 4) ≠ 0`).
`t_000d_c0` is `.dest (vyPrologue _)` by `rfl`: `ric_dest`, `ric_vyPrologue`.  Each test is
`PUSH4 sel PUSH1 0 MLOAD EQ ISZERO PUSH2 next JUMPI`: `ri_mload` at 0 reads the selector
(the prologue image `vyImg [] w` at `0 … 32` is 28 zero bytes and `w`'s first four bytes, so
`Bytes.toB256` of it is `w >>> 224 = Sevm.selector sevm`: a byte lemma to prove once, via
`Bytes.sliceD_writeAt_before`/`inside` and `B256.toBytes`), `read_covered` keeps the memory,
`ri_eq`, `ri_iszero`, `ri_push`, `ric_branch`; the zero arm is the body with `sels[k]` equal to
the selector, the other arm `ric_dest` into the next test.  The final miss `t_08dd_c0` is `noOk`.
Gas is irrelevant: each step's successor is some `St pre S M G'`. -/
theorem safe_dispatch {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : SFunc.Run prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post)) :
    ∃ (k : Nat) (f : SFunc) (sel : B256) (G' : Nat), bodies[k]? = some f ∧ sels[k]? = some sel ∧ Sevm.selector sevm = sel ∧
      4 ≤ sevm.data.length ∧ SFunc.Run prog sevm (entrySt sevm b G') f (.halted post) := by
  sorry

-- SEGMENT: liveDispatch (about 150 nodes, as `safeDispatch`)
/-- **Dispatcher, forward.**  `dispatchGas k = 128 + 29 k`: the size test 24, `JUMPDEST` 1,
the prologue 75, and per test 28 (`PUSH4` 3, `PUSH1` 3, `MLOAD` 3, `EQ` 3, `ISZERO` 3, `PUSH2` 3,
`JUMPI` 10) plus 1 for each missed test's `JUMPDEST`.

Proof sketch.  `rx_push`, `rx_calldatasize`, `rx_lt (v := 0)` (`4 ≤ size`), `rx_iszero (v := 1)`,
`rx_push`, `rx_branch_succ`, `rx_dest`, `rx_vyPrologue`; then induction-free: a `match` on `k`
(13 cases), each `k` misses `k` tests (`rx_mload` of the selector as in `safeDispatch`, `rx_eq
(v := 0)` from the selectors' distinctness, `decide`; `rx_iszero (v := 1)`, `rx_branch_succ`,
`rx_dest`) and hits the `k`-th (`rx_eq (v := 1)`, `rx_iszero (v := 0)`, `rx_branch_zero`).
A helper for one missed test and one for the hit, over `vyMem Mem.empty w`, keeps each case to a
few lines. -/
theorem live_dispatch {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome} {k : Nat} {f : SFunc}
    {sel : B256} (hk : bodies[k]? = some f) (hs : sels[k]? = some sel)
    (hsel : Sevm.selector sevm = sel) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256)
    (hrun : SFunc.RunExact prog sevm (entrySt sevm b G) f o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (G + dispatchGas k)) t_0000_c0 o := by
  sorry

/-- The call the model receives in the frame of body `k`. -/
def callAt (sevm : Sevm) : Nat → Call
  | 0 => .setMinter (Sevm.argWord sevm 0)
  | 1 => .setName (strArg sevm 0) (strArg sevm 1)
  | 2 => .totalSupply
  | 3 => .allowance (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 4 => .transfer (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 5 => .transferFrom (Sevm.argWord sevm 0) (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
  | 6 => .approve (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 7 => .mint (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 8 => .burnFrom (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
  | 9 => .name
  | 10 => .symbol
  | 11 => .decimals
  | 12 => .balanceOf (Sevm.argWord sevm 0)
  | _ => .other

/-- The selector of body `k` makes `decodeCall` read body `k`'s call. -/
theorem decodeCall_at {sevm : Sevm} {k : Nat} {sel : B256} (hs : sels[k]? = some sel)
    (hsel : Sevm.selector sevm = sel) (hlen : 4 ≤ sevm.data.length) :
    decodeCall sevm = callAt sevm k := by
  have hlen' : ¬ sevm.data.length < 4 := by omega
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp only [sels, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hs
  all_goals
    subst hs
    simp (config := { decide := true }) only [decodeCall, hlen', hsel, callAt, selSetMinter,
      selSetName, selTotalSupply, selAllowance, selTransfer, selTransferFrom, selApprove, selMint,
      selBurnFrom, selName, selSymbol, selDecimals, selBalanceOf, ite_true, ite_false]

end Blanc.Lift.Curve3Crv
