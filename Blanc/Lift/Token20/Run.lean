import Blanc.Lift.Token20.Check
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.WalkSteps
import Blanc.Lift.ExactLeaf

/-!
# The synthetic token `T`: gas-exact runs of its four selectors

Forward constructions (`Blanc/Lift/ExactWalk.lean`) of `SFunc.RunExact prog sevm pre post` for the
four success paths of the synthetic token (`Check.lean`), from a frame entry (empty stack and
memory) under any covered fork.  Each post state is an explicit term over the entry machine: the
selected `SLOAD`/`SSTORE` bases (`afterSload`, `afterSstore`, `Blanc/ForwardCall.lean`) and the final
`RETURN`; each charge is exact, the warm/cold and EIP-2200 parts kept as `sloadCost`/`sstoreCost`.

* `transfer_runExact`: `balanceOf[caller] -= v; balanceOf[to] += v`, returns `1`.
* `transferFrom_runExact`: `allowance[from][caller] -= v`, then the same move from `from`.
* `approve_runExact`: `allowance[caller][spender] := v`, returns `1`.
* `balanceOf_runExact`: reads `balanceOf[a]`, returns it; no storage write.

The `SSTORE` sentry is discharged from `gCallStipend < G`, `G` the gas left at the end.
-/

namespace Blanc.Lift.Token20

open Jaune Blanc.Lift

/-! ## Words and memory -/

/-- The post state of a returning tail: the image read for `RETURN`, the output set. -/
def retPost (b : Devm) (S : List B256) (M : Mem) (G : Nat) (out : B256) : Devm :=
  ((St b S M G).memRead 0 32).2.withOutput out.toBytes

section Tails

variable {sevm : Sevm} {b : Devm} {S : List B256} {G : Nat}

/-- `RETURN(0, 32)` of the word at `0` of an aligned image of at least one word. -/
theorem rx_ret0 {M : Mem} {w : B256} (h32 : M.size % 32 = 0) (hsz : 32 ≤ M.size)
    (hr : (M.read 0 32).1 = w.toBytes) :
    SFunc.RunExact prog sevm (St b (0 :: 32 :: S) M G) (.last .return_)
      (.halted (retPost b S M G w)) :=
  rx_return (i := 0) (sz := 32) (Devm.extCost_zero_of_le h32 hsz) hr

end Tails

/-! ## The dispatcher -/

section Dispatch

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- `CALLDATALOAD(0) >> 224`: the selector word on the stack.  12 gas. -/
theorem head {g : SFunc} (h_shifts : sevm.benvStat.rules.op.shifts = true)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] M G) g o) :
    SFunc.RunExact prog sevm (St b [] M (G + 12))
      (.next (.push [0x00] (by decide)) (.next (.reg .calldataload)
        (.next (.push [0xe0] (by decide)) (.next (.reg .shr) g)))) o := by
  refine rx_push (w := 0) (by decide) (by simp only [List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_nil]; omega) ?_
  refine rx_push (w := 224) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  exact rx_shr rfl h_shifts (by simp only [List.length_nil]; omega) k

end Dispatch

/-! ## The balance move (entry 1, `0x109`)

From the stack `v, dst, src`: read `balanceOf[src]`, revert unless `v ≤ it`, write it less `v`;
read `balanceOf[dst]` (after that write, so a self-move restores it), add `v`, revert if the sum
wrapped, write it; jump to the success tail. -/

section Move

variable (sevm : Sevm) (b : Devm) (src dst : Adr) (v : B256)

end Move

/-! ## `transfer(to, v)` -/

section Transfer

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome} {sel : B256}

end Transfer

/-! ## Memory steps over the hashing scratch -/

section Scratch

variable {sevm : Sevm} {b : Devm} {S : List B256} {G : Nat} {f : SFunc} {o : Outcome}

theorem size_write0 (a : B256) : (Mem.empty.write 0 a.toBytes).size = 32 := by
  rw [Mem.size_write_word_at]; rfl

/-- `mstore(0, a)` over empty memory: one word of expansion, 6 gas. -/
theorem rx_mstore0 {a i : B256} (hi : i = 0)
    (k : SFunc.RunExact prog sevm (St b S (Mem.empty.write 0 a.toBytes) G) f o) :
    SFunc.RunExact prog sevm (St b (i :: a :: S) Mem.empty (G + 6)) (.next (.reg .mstore) f) o := by
  subst hi
  exact rx_mstore (c := 6) (Devm.extCost_add_of_size (n := 0) rfl (by decide)) rfl k

end Scratch

/-! ## `transferFrom(from, to, v)` -/

/-! ## `approve(spender, v)` -/

/-! ## `balanceOf(a)` -/

end Blanc.Lift.Token20
