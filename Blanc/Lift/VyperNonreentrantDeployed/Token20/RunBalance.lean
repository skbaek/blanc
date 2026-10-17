import Blanc.Lift.VyperNonreentrantDeployed.Token20.Run

/-!
# The synthetic token `T`: the gas-exact run of `balanceOf(a)`

Restored from the token's pre-sweep `Run.lean` for the Uniswap V2 / WETH9 composition, whose
closed instance has the pair `STATICCALL` `T.balanceOf(pair)` inside its `swap`.  From a frame
entry (empty stack and memory), static or not, under any covered fork: the dispatcher, the read of
`balanceOf[a]` and the return of that word.  No storage write.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20

open Jaune Blanc.Lift

section BalanceDispatch

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- `balanceOf`: the third comparison matches, jumping to entry 5.  78 gas. -/
theorem dispatch_balanceOf (hsel : Sevm.selector sevm = 0x70a08231)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] M G) t_0037_c5 o) :
    SFunc.RunExact prog sevm (St b [] M (G + 78)) t_0000_c0 o :=
  head (cmp_miss (by rw [hsel]; decide) (cmp_miss (by rw [hsel]; decide)
    (cmp_hit (j := 5) (by rw [hsel]; decide) rfl k)))

end BalanceDispatch

/-- `balanceOf`'s holder. -/
abbrev boHolder (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr

/-- **What `balanceOf(a)` costs**: dispatcher 78, the read and its tail 28 and the `SLOAD`. -/
def balanceOfGas (sevm : Sevm) (pre : Devm) : Nat := 106 + sloadCost sevm pre (balSlot (boHolder sevm))

/-- The machine a `balanceOf` halts with: the slot warmed, the balance returned. -/
def balanceOfPost (sevm : Sevm) (pre : Devm) (G : Nat) : Devm :=
  retPost (afterSload sevm pre (balSlot (boHolder sevm))) [Sevm.selector sevm]
    (Mem.empty.write 0 (pre.getStorVal sevm.currentTarget (balSlot (boHolder sevm))).toBytes) G
    (pre.getStorVal sevm.currentTarget (balSlot (boHolder sevm)))

/-- **`balanceOf(a)` succeeds** from a frame entry (static or not), at exactly `balanceOfGas`,
returning `balanceOf[a]`. -/
theorem balanceOf_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hsel : Sevm.selector sevm = 0x70a08231)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hgas : pre.gasLeft = G + balanceOfGas sevm pre) :
    SProg.RunExact prog sevm pre (balanceOfPost sevm pre G) := by
  refine ⟨_, rfl, ?_⟩
  have hg : G + 15 + sloadCost sevm pre (balSlot (boHolder sevm)) + 13 + 78 = pre.gasLeft := by
    rw [hgas]; unfold balanceOfGas; omega
  have hrun : SFunc.RunExact prog sevm (St pre [] Mem.empty (G + 15 + sloadCost sevm pre (balSlot (boHolder sevm)) + 13 + 78)) t_0000_c0
      (.halted (balanceOfPost sevm pre G)) := by
    refine dispatch_balanceOf hsel ?_
    refine rx_dest ?_
    refine rx_push (w := 4) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_mask20 (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_sload_sel hfork (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_mstore0 rfl ?_
    refine rx_push (w := 32) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
    exact rx_ret0 (by rw [size_write0]) (by rw [size_write0])
      (Mem.read_write_word_of_wf Mem.wf_empty 0
        (pre.getStorVal sevm.currentTarget (balSlot (boHolder sevm))))
  rwa [pre_eq_St hstack hmem hg] at hrun

end Blanc.Lift.VyperNonreentrantDeployed.Token20
