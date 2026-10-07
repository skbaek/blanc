import Blanc.Lift.VyperNonreentrantDeployed.Token20.Check
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

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20

open Jaune Blanc.Lift

/-! ## Words and memory -/

/-- The memory after the `RETURN` word `1` is written into an image. -/
def okMem (M : Mem) : Mem := M.write 0 (1 : B256).toBytes

/-- The two-word hashing scratch: `a` at `0`, `c` at `0x20`, over empty memory. -/
def scratch (a c : B256) : Mem := (Mem.empty.write 0 a.toBytes).write 32 c.toBytes

theorem size_scratch (a c : B256) : (scratch a c).size = 64 := by
  unfold scratch
  rw [Mem.size_write_word_at, Mem.size_write_word_at]
  rfl

theorem wf_scratch (a c : B256) : Mem.Wf (scratch a c) :=
  (Mem.wf_empty.write _ _).write _ _

theorem size_okMem_scratch (a c : B256) : (okMem (scratch a c)).size = 64 := by
  unfold okMem; rw [Mem.size_write_word_at, size_scratch]; rfl

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

/-- The success tail over the hashing scratch: no expansion. -/
theorem ok_scratch {a c : B256} (hroom : S.length < 1022) :
    SFunc.RunExact prog sevm (St b S (scratch a c) (G + 16)) t_00fe_c2
      (.halted (retPost b S (okMem (scratch a c)) G 1)) := by
  refine rx_dest ?_
  refine rx_push (w := 1) (by decide) (by omega) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) (M' := okMem (scratch a c)) ?_ rfl ?_
  · exact Devm.extCost_add_of_size (size_scratch a c) (by decide)
  refine rx_push (w := 32) (by decide) (by omega) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  exact rx_ret0 (by rw [size_okMem_scratch]) (by rw [size_okMem_scratch]; omega)
    (Mem.read_write_word_of_wf (wf_scratch a c) 0 1)

end Tails

/-! ## The dispatcher -/

section Dispatch

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- `CALLDATALOAD(0) >> 224`: the selector word on the stack.  12 gas. -/
theorem head {g : SFunc}
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] M G) g o) :
    SFunc.RunExact prog sevm (St b [] M (G + 12))
      (.next (.push [0x00] (by decide)) (.next (.reg .calldataload)
        (.next (.push [0xe0] (by decide)) (.next (.reg .shr) g)))) o := by
  refine rx_push (w := 0) (by decide) (by simp only [List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_nil]; omega) ?_
  refine rx_push (w := 224) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  exact rx_shr rfl (by simp only [List.length_nil]; omega) k

/-- `approve`: the fourth comparison matches, jumping to entry 6.  100 gas. -/
theorem dispatch_approve (hsel : Sevm.selector sevm = 0x095ea7b3)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] M G) t_00d4_c6 o) :
    SFunc.RunExact prog sevm (St b [] M (G + 100)) t_0000_c0 o :=
  head (cmp_miss (by rw [hsel]; decide) (cmp_miss (by rw [hsel]; decide)
    (cmp_miss (by rw [hsel]; decide) (cmp_hit (j := 6) (by rw [hsel]; decide) rfl k))))

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

/-- `mstore(32, c)` after `mstore(0, a)`: one more word, 6 gas. -/
theorem rx_mstore32 {a c i : B256} (hi : i = 32)
    (k : SFunc.RunExact prog sevm (St b S (scratch a c) G) f o) :
    SFunc.RunExact prog sevm (St b (i :: c :: S) (Mem.empty.write 0 a.toBytes) (G + 6))
      (.next (.reg .mstore) f) o := by
  subst hi
  exact rx_mstore (c := 6) (Devm.extCost_add_of_size (size_write0 a) (by decide)) rfl k

/-- `keccak256(0, 64)` of the scratch: the mapping slot, 42 gas. -/
theorem rx_keccak_scratch {a c i sz : B256} (hi : i = 0) (hsz : sz = 64) (hroom : S.length < 1024)
    (k : SFunc.RunExact prog sevm (St b (mapSlot a c :: S) (scratch a c) G) f o) :
    SFunc.RunExact prog sevm (St b (i :: sz :: S) (scratch a c) (G + 42))
      (.next (.reg .keccak256) f) o := by
  subst hi hsz
  refine rx_keccak (c := 42) (Devm.extCost_add_of_size (size_scratch a c) (by decide)) ?_ ?_ hroom k
  · show Bytes.keccak (((Mem.empty.write 0 a.toBytes).write 32 c.toBytes).read 0 64).1 = _
    rw [scratch_read]; rfl
  · exact Mem.read_snd_eq_self (memExtSize_of_le (by rw [size_scratch]) (by rw [size_scratch]; decide))

end Scratch

/-! ## `transferFrom(from, to, v)` -/

/-! ## `approve(spender, v)` -/

/-- `approve`'s spender. -/
abbrev apSpender (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr
/-- `approve`'s value. -/
abbrev apVal (sevm : Sevm) : B256 := Sevm.dataWord sevm 36

/-- The base after a successful `approve`. -/
def approveBase (sevm : Sevm) (pre : Devm) : Devm :=
  afterSstore sevm pre (allowSlot sevm.caller (apSpender sevm)) (apVal sevm)

/-- **What `approve(spender, v)` costs**: dispatcher 100, wrapper 87, the `SSTORE`, the tail 16. -/
def approveGas (sevm : Sevm) (pre : Devm) : Nat :=
  203 + sstoreCost sevm pre (allowSlot sevm.caller (apSpender sevm)) (apVal sevm)

/-- The machine a successful `approve` halts with. -/
def approvePost (sevm : Sevm) (pre : Devm) (G : Nat) : Devm :=
  retPost (approveBase sevm pre) [Sevm.selector sevm]
    (okMem (scratch sevm.caller.toB256 (apSpender sevm).toB256)) G 1

/-- **`approve(spender, v)` succeeds** from a frame entry, at exactly `approveGas`, returning `1`. -/
theorem approve_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsel : Sevm.selector sevm = 0x095ea7b3)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hgas : pre.gasLeft = G + approveGas sevm pre) (hsent : gCallStipend < G) :
    SProg.RunExact prog sevm pre (approvePost sevm pre G) := by
  refine ⟨_, rfl, ?_⟩
  have hg : G + 16 + sstoreCost sevm pre (allowSlot sevm.caller (apSpender sevm)) (apVal sevm) + 87 +
      100 = pre.gasLeft := by
    rw [hgas]; unfold approveGas; omega
  have hrun : SFunc.RunExact prog sevm (St pre [] Mem.empty (G + 16 + sstoreCost sevm pre (allowSlot sevm.caller (apSpender sevm)) (apVal sevm) + 87 +
      100)) t_0000_c0
      (.halted (approvePost sevm pre G)) := by
    refine dispatch_approve hsel ?_
    refine rx_dest ?_
    refine rx_caller (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_mstore0 rfl ?_
    refine rx_push (w := 4) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_mask20 (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_push (w := 32) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_mstore32 rfl ?_
    refine rx_push (w := 36) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_push (w := 64) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_keccak_scratch rfl rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_sstore hfork (Nat.lt_of_lt_of_le hsent (by omega)) hstatic ?_
    exact ok_scratch (S := [Sevm.selector sevm]) (by simp only [List.length_cons, List.length_nil]; omega)
  rwa [pre_eq_St hstack hmem hg] at hrun

/-! ## `balanceOf(a)` -/

end Blanc.Lift.VyperNonreentrantDeployed.Token20
