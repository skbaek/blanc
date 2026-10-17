import Blanc.Lift.VyperNonreentrantDeployed.Token20.Run

/-!
# The synthetic token `T`: the gas-exact run of `transfer(to, v)`

Restored from the token's pre-sweep `Run.lean` for the Uniswap V2 / WETH9 composition, whose
closed instance sends `T.transfer(pair, a)` as its first transaction.  The forward construction
(`Blanc/Lift/ExactWalk.lean`) of `SProg.RunExact prog sevm pre post` from a frame entry (empty stack
and memory) under any covered fork: the dispatcher, the `transfer` wrapper, the balance move
(`balanceOf[caller] -= v; balanceOf[to] += v`) and the success tail returning the word `1`.  The
post state is an explicit term over the entry machine (`afterSload`/`afterSstore`); the charge is
exact, its warm/cold and EIP-2200 parts kept as `sloadCost`/`sstoreCost`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20

open Jaune Blanc.Lift

theorem size_okMem_empty : (okMem Mem.empty).size = 32 := by
  unfold okMem; rw [Mem.size_write_word_at]; rfl

section TransferTail

variable {sevm : Sevm} {b : Devm} {S : List B256} {G : Nat}

/-- The success tail (entry 2, `0xfe`): `mstore(0, 1); return(0, 32)` over empty memory. -/
theorem ok_empty (hroom : S.length < 1022) :
    SFunc.RunExact prog sevm (St b S Mem.empty (G + 19)) t_00fe_c2
      (.halted (retPost b S (okMem Mem.empty) G 1)) := by
  refine rx_dest ?_
  refine rx_push (w := 1) (by decide) (by omega) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 6) (M' := okMem Mem.empty) ?_ rfl ?_
  · exact Devm.extCost_add_of_size (n := 0) rfl (by decide)
  refine rx_push (w := 32) (by decide) (by omega) ?_
  refine rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  exact rx_ret0 (by rw [size_okMem_empty]) (by rw [size_okMem_empty])
    (Mem.read_write_word_of_wf Mem.wf_empty 0 1)

end TransferTail

section TransferDispatch

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- `transfer`: the first comparison matches, jumping to entry 3.  34 gas. -/
theorem dispatch_transfer (hsel : Sevm.selector sevm = 0xa9059cbb)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] M G) t_005a_c3 o) :
    SFunc.RunExact prog sevm (St b [] M (G + 34)) t_0000_c0 o :=
  head (cmp_hit (j := 3) (by rw [hsel]; decide) rfl k)

end TransferDispatch

/-! ## The balance move (entry 1, `0x109`)

From the stack `v, dst, src`: read `balanceOf[src]`, revert unless `v ≤ it`, write it less `v`;
read `balanceOf[dst]` (after that write, so a self-move restores it), add `v`, revert if the sum
wrapped, write it; jump to the success tail. -/

section Move

variable (sevm : Sevm) (b : Devm) (src dst : Adr) (v : B256)

/-- `balanceOf[src]` before the move. -/
def mvFrom : B256 := b.getStorVal sevm.currentTarget (balSlot src)
/-- After reading `balanceOf[src]`. -/
def mv1 : Devm := afterSload sevm b (balSlot src)
/-- After the debit. -/
def mv2 : Devm := afterSstore sevm (mv1 sevm b src) (balSlot src) (mvFrom sevm b src - v)
/-- `balanceOf[dst]` after the debit. -/
def mvTo : B256 := (mv2 sevm b src v).getStorVal sevm.currentTarget (balSlot dst)
/-- After reading it. -/
def mv3 : Devm := afterSload sevm (mv2 sevm b src v) (balSlot dst)
/-- After the credit: the move's base. -/
def mv4 : Devm := afterSstore sevm (mv3 sevm b src dst v) (balSlot dst) (v + mvTo sevm b src dst v)

/-- The four storage charges of a move. -/
def mvCost : Nat :=
  sstoreCost sevm (mv3 sevm b src dst v) (balSlot dst) (v + mvTo sevm b src dst v) +
    sloadCost sevm (mv2 sevm b src v) (balSlot dst) +
    sstoreCost sevm (mv1 sevm b src) (balSlot src) (mvFrom sevm b src - v) +
    sloadCost sevm b (balSlot src)

end Move

theorem move {sevm : Sevm} {b : Devm} {src dst : Adr} {v : B256} {S : List B256} {M : Mem}
    {G : Nat} {o : Outcome}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hroom : S.length < 1000) (hsent : gCallStipend < G)
    (hle : v ≤ mvFrom sevm b src) (hnof : v ≤ v + mvTo sevm b src dst v)
    (k : SFunc.RunExact prog sevm
      (St (mv4 sevm b src dst v) (v :: dst.toB256 :: src.toB256 :: S) M G) t_00fe_c2 o) :
    SFunc.RunExact prog sevm
      (St b (v :: dst.toB256 :: src.toB256 :: S) M
        (G + 11 + sstoreCost sevm (mv3 sevm b src dst v) (balSlot dst) (v + mvTo sevm b src dst v) +
          31 + sloadCost sevm (mv2 sevm b src v) (balSlot dst) + 3 +
          sstoreCost sevm (mv1 sevm b src) (balSlot src) (mvFrom sevm b src - v) + 39 +
          sloadCost sevm b (balSlot src) + 4)) t_0109_c1 o := by
  refine rx_dest ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sload_sel hfork (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le hle) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_zero ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sub (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sstore hfork (Nat.lt_of_lt_of_le hsent (by omega)) hstatic ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sload_sel hfork (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le hnof) (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_zero ?_
  refine rx_dup (n := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_sstore hfork (Nat.lt_of_lt_of_le hsent (by omega)) hstatic ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  exact rx_jump (j := 2) rfl k

/-! ## `transfer(to, v)` -/

section Transfer

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome} {sel : B256}

/-- The `transfer` wrapper (entry 3, `0x5a`): stack `v, to, caller`, jump to the move.  32 gas. -/
theorem transfer_entry
    (k : SFunc.RunExact prog sevm
      (St b (Sevm.dataWord sevm 36 :: (Sevm.dataWord sevm 4).toAdr.toB256 :: sevm.caller.toB256 ::
        [sel]) M G) t_0109_c1 o) :
    SFunc.RunExact prog sevm (St b [sel] M (G + 32)) t_005a_c3 o := by
  refine rx_dest ?_
  refine rx_caller (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 4) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_mask20 (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push (w := 36) (by decide) (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ?_
  exact rx_jump (j := 1) rfl k

end Transfer

/-- `transfer`'s recipient. -/
abbrev trTo (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr
/-- `transfer`'s value. -/
abbrev trVal (sevm : Sevm) : B256 := Sevm.dataWord sevm 36

/-- **What `transfer(to, v)` costs**: dispatcher 34, wrapper 32, the move's fixed 88 and its four
storage charges (`mvCost`), the success tail 19. -/
def transferGas (sevm : Sevm) (pre : Devm) : Nat :=
  173 + mvCost sevm pre sevm.caller (trTo sevm) (trVal sevm)

/-- The base after a successful `transfer`. -/
def transferBase (sevm : Sevm) (pre : Devm) : Devm :=
  mv4 sevm pre sevm.caller (trTo sevm) (trVal sevm)

/-- The machine a successful `transfer` halts with: the move's base, word `1` returned. -/
def transferPost (sevm : Sevm) (pre : Devm) (G : Nat) : Devm :=
  retPost (transferBase sevm pre)
    [trVal sevm, (trTo sevm).toB256, sevm.caller.toB256, Sevm.selector sevm]
    (okMem Mem.empty) G 1

/-- **`transfer(to, v)` succeeds**, from a frame entry with `v ≤ balanceOf[caller]` and a credit
that does not wrap, at exactly `transferGas`, returning the word `1`. -/
theorem transfer_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsel : Sevm.selector sevm = 0xa9059cbb)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hgas : pre.gasLeft = G + transferGas sevm pre) (hsent : gCallStipend < G)
    (hle : trVal sevm ≤ mvFrom sevm pre sevm.caller)
    (hnof : trVal sevm ≤ trVal sevm + mvTo sevm pre sevm.caller (trTo sevm) (trVal sevm)) :
    SProg.RunExact prog sevm pre (transferPost sevm pre G) := by
  refine ⟨_, rfl, ?_⟩
  have hg : G + 19 + 11 + sstoreCost sevm (mv3 sevm pre sevm.caller (trTo sevm) (trVal sevm))
        (balSlot (trTo sevm)) (trVal sevm + mvTo sevm pre sevm.caller (trTo sevm) (trVal sevm)) +
      31 + sloadCost sevm (mv2 sevm pre sevm.caller (trVal sevm)) (balSlot (trTo sevm)) + 3 +
      sstoreCost sevm (mv1 sevm pre sevm.caller) (balSlot sevm.caller)
        (mvFrom sevm pre sevm.caller - trVal sevm) + 39 +
      sloadCost sevm pre (balSlot sevm.caller) + 4 + 32 + 34 = pre.gasLeft := by
    rw [hgas]; unfold transferGas mvCost; omega
  have hrun : SFunc.RunExact prog sevm (St pre [] Mem.empty (G + 19 + 11 + sstoreCost sevm (mv3 sevm pre sevm.caller (trTo sevm) (trVal sevm))
        (balSlot (trTo sevm)) (trVal sevm + mvTo sevm pre sevm.caller (trTo sevm) (trVal sevm)) +
      31 + sloadCost sevm (mv2 sevm pre sevm.caller (trVal sevm)) (balSlot (trTo sevm)) + 3 +
      sstoreCost sevm (mv1 sevm pre sevm.caller) (balSlot sevm.caller)
        (mvFrom sevm pre sevm.caller - trVal sevm) + 39 +
      sloadCost sevm pre (balSlot sevm.caller) + 4 + 32 + 34)) t_0000_c0
      (.halted (transferPost sevm pre G)) := by
    refine dispatch_transfer hsel (transfer_entry ?_)
    refine move hfork hstatic (by simp only [List.length_cons, List.length_nil]; omega)
      (Nat.lt_add_right _ hsent) hle hnof ?_
    exact ok_empty (by simp only [List.length_cons, List.length_nil]; omega)
  rwa [pre_eq_St hstack hmem hg] at hrun

end Blanc.Lift.VyperNonreentrantDeployed.Token20
