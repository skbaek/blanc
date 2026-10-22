import Blanc.Lift.VyperNonreentrantDeployed.Token20.RunTransfer

/-!
# The synthetic token `T`: the gas-exact run of `transferFrom(from, to, v)`

Restored from the token's pre-sweep `Run.lean` for the Curve 3pool closed instance (U9(b)), whose
`exchange` pulls coin `i` with `transferFrom(trader, pool, dx)`.  The dispatcher's second branch,
the `transferFrom` wrapper (hash the allowance slot `allowance[from][caller]`, read it, revert
unless `v ≤ allowance`, write it less `v`), the balance move of `RunTransfer.lean` from `from` to
`to`, and the success tail returning the word `1`, under any covered fork.  The charge is exact,
its warm/cold and EIP-2200 parts kept as `sloadCost`/`sstoreCost`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20

open Jaune Blanc.Lift

/-- `GT` of a covered value is `0`. -/
theorem tf_gtCheck_zero {x y : B256} (h : x ≤ y) : B256.gtCheck x y = 0 := by
  simp only [B256.gtCheck, GT.gt, B256.not_lt.mpr h, ↓reduceIte]

section TransferFromDispatch

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- `transferFrom`: the second comparison matches, jumping to entry 4.  56 gas. -/
theorem dispatch_transferFrom (h_shifts : sevm.benvStat.rules.op.shifts = true)
    (hsel : Sevm.selector sevm = 0x23b872dd)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] M G) t_007c_c4 o) :
    SFunc.RunExact prog sevm (St b [] M (G + 56)) t_0000_c0 o :=
  head h_shifts (cmp_miss (by rw [hsel]; decide) (cmp_hit (j := 4) (by rw [hsel]; decide) rfl k))

end TransferFromDispatch

/-! ## `transferFrom(from, to, v)` -/

/-- `transferFrom`'s owner. -/
abbrev tfFrom (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr
/-- `transferFrom`'s recipient. -/
abbrev tfTo (sevm : Sevm) : Adr := (Sevm.dataWord sevm 36).toAdr
/-- `transferFrom`'s value. -/
abbrev tfVal (sevm : Sevm) : B256 := Sevm.dataWord sevm 68

/-- `allowance[from][caller]` before. -/
def tfAllow (sevm : Sevm) (b : Devm) : B256 :=
  b.getStorVal sevm.currentTarget (allowSlot (tfFrom sevm) sevm.caller)
/-- After reading it. -/
def tf1 (sevm : Sevm) (b : Devm) : Devm := afterSload sevm b (allowSlot (tfFrom sevm) sevm.caller)
/-- After its decrement: the move's entry base. -/
def tf2 (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (tf1 sevm b) (allowSlot (tfFrom sevm) sevm.caller) (tfAllow sevm b - tfVal sevm)

/-- The `transferFrom` wrapper (entry 4, `0x7c`): hash the allowance slot, read it, revert unless
`v ≤ allowance`, write it less `v`, stack `v, to, from`, jump to the move. -/
theorem transferFrom_entry {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome} {sel : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsent : gCallStipend < G) (hal : tfVal sevm ≤ tfAllow sevm b)
    (k : SFunc.RunExact prog sevm
      (St (tf2 sevm b) (tfVal sevm :: (tfTo sevm).toB256 :: (tfFrom sevm).toB256 :: [sel])
        (scratch (tfFrom sevm).toB256 sevm.caller.toB256) G) t_0109_c1 o) :
    SFunc.RunExact prog sevm (St b [sel] Mem.empty
      (G + 26 + sstoreCost sevm (tf1 sevm b) (allowSlot (tfFrom sevm) sevm.caller)
        (tfAllow sevm b - tfVal sevm) + 45 +
        sloadCost sevm b (allowSlot (tfFrom sevm) sevm.caller) + 87)) t_007c_c4 o := by
  refine rx_dest ?_
  refine rx_push (w := 4) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_mask20 (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_mstore0 rfl ?_
  refine rx_caller (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_mstore32 rfl ?_
  refine rx_push (w := 64) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_keccak_scratch rfl rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_sload_sel hfork (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 68) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_gt (v := 0) (tf_gtCheck_zero hal) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_branch_zero ?_
  refine rx_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_sub (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_swap2 ?_
  refine rx_pop ?_
  refine rx_swap2 ?_
  refine rx_sstore hfork (Nat.lt_of_lt_of_le hsent (by omega)) hstatic ?_
  refine rx_push (w := 36) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_mask20 (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_swap1 ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  exact rx_jump (j := 1) rfl k

/-- **What `transferFrom(from, to, v)` costs**: dispatcher 56, wrapper 158 and its two allowance
charges, the move's fixed 88 and its four storage charges, the success tail 16. -/
def transferFromGas (sevm : Sevm) (pre : Devm) : Nat :=
  318 + mvCost sevm (tf2 sevm pre) (tfFrom sevm) (tfTo sevm) (tfVal sevm) +
    sstoreCost sevm (tf1 sevm pre) (allowSlot (tfFrom sevm) sevm.caller)
      (tfAllow sevm pre - tfVal sevm) +
    sloadCost sevm pre (allowSlot (tfFrom sevm) sevm.caller)

/-- The base after a successful `transferFrom`. -/
def transferFromBase (sevm : Sevm) (pre : Devm) : Devm :=
  mv4 sevm (tf2 sevm pre) (tfFrom sevm) (tfTo sevm) (tfVal sevm)

/-- The machine a successful `transferFrom` halts with. -/
def transferFromPost (sevm : Sevm) (pre : Devm) (G : Nat) : Devm :=
  retPost (transferFromBase sevm pre)
    [tfVal sevm, (tfTo sevm).toB256, (tfFrom sevm).toB256, Sevm.selector sevm]
    (okMem (scratch (tfFrom sevm).toB256 sevm.caller.toB256)) G 1

/-- **`transferFrom(from, to, v)` succeeds**, from a frame entry with `v ≤ allowance[from][caller]`,
`v ≤ balanceOf[from]` after the allowance write, and a credit that does not wrap, at exactly
`transferFromGas`, returning the word `1`. -/
theorem transferFrom_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsel : Sevm.selector sevm = 0x23b872dd)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hgas : pre.gasLeft = G + transferFromGas sevm pre) (hsent : gCallStipend < G)
    (hal : tfVal sevm ≤ tfAllow sevm pre)
    (hle : tfVal sevm ≤ mvFrom sevm (tf2 sevm pre) (tfFrom sevm))
    (hnof : tfVal sevm ≤ tfVal sevm + mvTo sevm (tf2 sevm pre) (tfFrom sevm) (tfTo sevm) (tfVal sevm)) :
    SProg.RunExact prog sevm pre (transferFromPost sevm pre G) := by
  refine ⟨_, rfl, ?_⟩
  have hg : G + 16 + 11 + sstoreCost sevm (mv3 sevm (tf2 sevm pre) (tfFrom sevm) (tfTo sevm) (tfVal sevm))
        (balSlot (tfTo sevm)) (tfVal sevm + mvTo sevm (tf2 sevm pre) (tfFrom sevm) (tfTo sevm) (tfVal sevm)) +
      31 + sloadCost sevm (mv2 sevm (tf2 sevm pre) (tfFrom sevm) (tfVal sevm)) (balSlot (tfTo sevm)) + 3 +
      sstoreCost sevm (mv1 sevm (tf2 sevm pre) (tfFrom sevm)) (balSlot (tfFrom sevm))
        (mvFrom sevm (tf2 sevm pre) (tfFrom sevm) - tfVal sevm) + 39 +
      sloadCost sevm (tf2 sevm pre) (balSlot (tfFrom sevm)) + 4 + 26 +
      sstoreCost sevm (tf1 sevm pre) (allowSlot (tfFrom sevm) sevm.caller)
        (tfAllow sevm pre - tfVal sevm) + 45 +
      sloadCost sevm pre (allowSlot (tfFrom sevm) sevm.caller) + 87 + 56 = pre.gasLeft := by
    rw [hgas]; unfold transferFromGas mvCost; omega
  have hrun : SFunc.RunExact prog sevm (St pre [] Mem.empty (G + 16 + 11 + sstoreCost sevm (mv3 sevm (tf2 sevm pre) (tfFrom sevm) (tfTo sevm) (tfVal sevm))
        (balSlot (tfTo sevm)) (tfVal sevm + mvTo sevm (tf2 sevm pre) (tfFrom sevm) (tfTo sevm) (tfVal sevm)) +
      31 + sloadCost sevm (mv2 sevm (tf2 sevm pre) (tfFrom sevm) (tfVal sevm)) (balSlot (tfTo sevm)) + 3 +
      sstoreCost sevm (mv1 sevm (tf2 sevm pre) (tfFrom sevm)) (balSlot (tfFrom sevm))
        (mvFrom sevm (tf2 sevm pre) (tfFrom sevm) - tfVal sevm) + 39 +
      sloadCost sevm (tf2 sevm pre) (balSlot (tfFrom sevm)) + 4 + 26 +
      sstoreCost sevm (tf1 sevm pre) (allowSlot (tfFrom sevm) sevm.caller)
        (tfAllow sevm pre - tfVal sevm) + 45 +
      sloadCost sevm pre (allowSlot (tfFrom sevm) sevm.caller) + 87 + 56)) t_0000_c0
      (.halted (transferFromPost sevm pre G)) := by
    refine dispatch_transferFrom hfork.rules_shifts hsel (transferFrom_entry hfork hstatic (Nat.lt_of_lt_of_le hsent
      (by omega)) hal ?_)
    refine move hfork hstatic (by simp only [List.length_cons, List.length_nil]; omega)
      (Nat.lt_add_right _ hsent) hle hnof ?_
    exact ok_scratch (by simp only [List.length_cons, List.length_nil]; omega)
  rwa [pre_eq_St hstack hmem hg] at hrun

end Blanc.Lift.VyperNonreentrantDeployed.Token20
