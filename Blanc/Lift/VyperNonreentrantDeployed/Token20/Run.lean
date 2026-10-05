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

theorem size_okMem_empty : (okMem Mem.empty).size = 32 := by
  unfold okMem; rw [Mem.size_write_word_at]; rfl

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

/-- `transfer`: the first comparison matches, jumping to entry 3.  34 gas. -/
theorem dispatch_transfer (hsel : Sevm.selector sevm = 0xa9059cbb)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] M G) t_005a_c3 o) :
    SFunc.RunExact prog sevm (St b [] M (G + 34)) t_0000_c0 o :=
  head (cmp_hit (j := 3) (by rw [hsel]; decide) rfl k)

/-- `transferFrom`: the second comparison matches, jumping to entry 4.  56 gas. -/
theorem dispatch_transferFrom (hsel : Sevm.selector sevm = 0x23b872dd)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] M G) t_007c_c4 o) :
    SFunc.RunExact prog sevm (St b [] M (G + 56)) t_0000_c0 o :=
  head (cmp_miss (by rw [hsel]; decide) (cmp_hit (j := 4) (by rw [hsel]; decide) rfl k))

/-- `balanceOf`: the third comparison matches, jumping to entry 5.  78 gas. -/
theorem dispatch_balanceOf (hsel : Sevm.selector sevm = 0x70a08231)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] M G) t_0037_c5 o) :
    SFunc.RunExact prog sevm (St b [] M (G + 78)) t_0000_c0 o :=
  head (cmp_miss (by rw [hsel]; decide) (cmp_miss (by rw [hsel]; decide)
    (cmp_hit (j := 5) (by rw [hsel]; decide) rfl k)))

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
  refine rx_gt (v := 0) (gtCheck_zero_of_le hal) (by simp only [List.length_cons, List.length_nil]; omega) ?_
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
    refine dispatch_transferFrom hsel (transferFrom_entry hfork hstatic (Nat.lt_of_lt_of_le hsent
      (by omega)) hal ?_)
    refine move hfork hstatic (by simp only [List.length_cons, List.length_nil]; omega)
      (Nat.lt_add_right _ hsent) hle hnof ?_
    exact ok_scratch (by simp only [List.length_cons, List.length_nil]; omega)
  rwa [pre_eq_St hstack hmem hg] at hrun

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
