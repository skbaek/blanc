import Blanc.Lift.Weth9.Live
import Blanc.Lift.ExactWalkSolc

namespace Blanc.Lift.Weth9

open Jaune Blanc.Lift

theorem fp_memFp : FpMem 96 memFp := FpMem.init

/-- The memory image the `approve` body leaves: the two hashing scratches and the event word. -/
def apMem (M : Mem) (C guy h1 wad : B256) : Mem :=
  ((((M.write 0 C.toBytes).write 32 (4 : B256).toBytes).write 0 guy.toBytes).write 32
    h1.toBytes).write 96 wad.toBytes

theorem apMem_fp {M : Mem} (h : FpMem 96 M) (C guy h1 wad : B256) : FpMem 128 (apMem M C guy h1 wad) :=
  ((((h.write 0 C (by omega) (by omega)).write 32 _ (by omega) (by omega)).write 0 guy
    (by omega) (by omega)).write 32 h1 (by omega) (by omega)).write_out wad

/-- The boolean-result tail of the writers' wrappers: `mstore(0x60, iszero^4 flag)` and
`return(0x60, 0x20)`; 62 gas. -/
theorem bool_tail {sevm : Sevm} {b : Devm} {G : Nat} {M1 : Mem} {sel : B256}
    (hM : FpMem 128 M1) :
    ∃ post, SFunc.RunExact prog sevm (St b [1, sel] M1 (G + 62)) t_0187_c27 (.halted post) ∧
      post.gasLeft = G ∧ post.output = (1 : B256).toBytes := by
  refine ⟨?post, ?run, ?gas, ?out⟩
  case run =>
    rdest
    rpush
    rmld
    rdup
    rdup
    riszero
    riszero
    riszero
    riszero
    rdup
    rmst 96
    rpush
    radd
    rswap
    rpop
    rpop
    rpush
    rmld
    rdup
    rswap
    rsub
    rswap
    refine rx_returnW hM ?_ ?_ <;> decide
  case gas => rfl
  case out => rfl

/-- The `approve` body (entry 11, `0x057b`), from the stack `wad, guy, return, …`: two mapping-slot
hashes, the allowance `SSTORE`, the `Approval` event, `true`.  `1859` gas after the `SSTORE` (`1756`
for the `LOG3`, three words of event data expansion included), `195` before it; the `SSTORE` costs
`sstoreCost`. -/
theorem approve_body {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {guy : Adr}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hsentry : gCallStipend < G + 1859 + sstoreCost sevm b (allowSlot sevm.caller guy) wad) :
    ∃ b', SFunc.RunExact prog sevm
      (St b (wad :: guy.toB256 :: ret :: S) M
        (G + 1859 + sstoreCost sevm b (allowSlot sevm.caller guy) wad + 195)) t_057b_c11
      (.returned (St b' (1 :: S)
        (apMem M sevm.caller.toB256 guy.toB256 (mapSlot sevm.caller.toB256 4) wad) G)) := by
  refine ⟨?b', ?run⟩
  case run =>
    rdest
    rpush
    rdup
    rpush
    rpush
    refine rx_caller (by rroom) ?_
    rmask
    rmask
    rdup
    rmst 0
    rpush
    radd
    rswap
    rdup
    rmst 32
    rpush
    radd
    rpush
    rkec
    rpush
    rdup
    rmask
    rmask
    rdup
    rmst 0
    rpush
    radd
    rswap
    rdup
    rmst 32
    rpush
    radd
    rpush
    rkec
    rdup
    rswap
    refine rx_sstore hfork hsentry hstatic ?_
    rpop
    rdup
    rmask
    refine rx_caller (by rroom) ?_
    rmask
    rpush
    rdup
    rpush
    rmld
    rdup
    rdup
    rdup
    refine rx_mstoreOut (by assumption) (by decide) (fun _ => ?_)
    rpush
    radd
    rswap
    rpop
    rpop
    rpush
    rmld
    rdup
    rswap
    rsub
    rswap
    rlog3
    rpush
    rswap
    rpop
    rswap
    rswap
    rpop
    rpop
    exact rx_ret

/-- The `approve` wrapper (entry 27, `0x0147`): the `nonpayable` guard, the two argument decodes, the
call into the body, the boolean tail.  `98` gas before the body, `62` after it. -/
theorem approve_entry {sevm : Sevm} {b : Devm} {G : Nat} {sel : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hval : sevm.value = 0)
    (hsentry : gCallStipend < G + 62 + 1859 +
      sstoreCost sevm b (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
        (Sevm.dataWord sevm 36)) :
    ∃ post, SFunc.RunExact prog sevm (St b [sel] memFp
      (G + 62 + 1859 + sstoreCost sevm b (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
        (Sevm.dataWord sevm 36) + 195 + 98)) t_0147_c27 (.halted post) ∧
      post.gasLeft = G ∧ post.output = (1 : B256).toBytes := by
  obtain ⟨b', hbody⟩ := approve_body (S := [sel]) (ret := Bytes.toB256 [1, 135]) (G := G + 62)
    (wad := Sevm.dataWord sevm 36) (guy := (Sevm.dataWord sevm 4).toAdr) hfork hstatic
    fp_memFp (by simp) hsentry
  obtain ⟨post, htail, hg, ho⟩ := bool_tail (sevm := sevm) (b := b') (G := G)
    (sel := sel) (apMem_fp fp_memFp _ _ _ _)
  refine ⟨post, ?_, hg, ho⟩
  rdest
  refine rx_callvalue (by simp) ?_
  refine rx_iszero (v := 1) (by simp [B256.eqCheck, hval]) (by simp) ?_
  rpush
  refine rx_branch_succ (by decide) ?_
  rdest
  rpush
  rpush
  rdup
  rdup
  refine rx_calldataload (by rroom) ?_
  rmask
  rswap
  rpush
  radd
  rswap
  rswap
  rswap
  rdup
  refine rx_calldataload (by rroom) ?_
  rswap
  rpush
  radd
  rswap
  rswap
  rswap
  rpop
  rpop
  rpush
  exact rx_callRet (j := 11) rfl hbody htail

/-- WETH9's `approve(address,uint256)` selector. -/
abbrev apSel : B256 := selector "approve" [.address, .uint256]

theorem apSel_eq : apSel = 0x095ea7b3 := by decide +kernel

/-- The dispatcher path to `approve`: the `name()` miss, then the match at the second comparison,
jumping to entry 27.  106 gas. -/
theorem dispatch_approve {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0x095ea7b3)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g) t_0147_c27 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 106)) t_0000_c0 o :=
  dispatch_head h_len h_len' (by rw [hsel]; decide) (cmp_hit (j := 27) (by rw [hsel]; decide) rfl k)

/-- **What `approve(guy, wad)` costs on the deployed WETH9** (successful, from a fresh frame): the
dispatcher (106), the wrapper (98), the body before the `SSTORE` (195) and after it (1859), the boolean
tail (62), and the `SSTORE` of `allowance[caller][guy] := wad` at its `sstoreCost`: the cold surcharge
`gasColdSload` if the slot is not yet accessed, plus `gasStorageSet` for a first write over a zero
original, `gasStorageUpdate - gasColdSload` for a first change of a nonzero one, `gasWarmAccess`
otherwise. -/
def approveGas (sevm : Sevm) (pre : Devm) : Nat :=
  2320 + sstoreCost sevm pre (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
    (Sevm.dataWord sevm 36)

/-- A frame entering `approve` succeeds at exactly `approveGas`, ending with `true` at the top of the
return data; the `SSTORE` needs the EIP-2200 sentry (more than `gCallStipend` gas left when it
runs, `399` gas in). -/
theorem weth9_approve_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = apSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + approveGas sevm pre)
    (h_sentry : gCallStipend + 399 < pre.gasLeft) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes := by
  have hsel : Sevm.selector sevm = 0x095ea7b3 := h_sel.trans apSel_eq
  have hg : G + 62 + 1859 + sstoreCost sevm pre (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
      (Sevm.dataWord sevm 36) + 195 + 98 + 106 = pre.gasLeft := by
    rw [h_gas]; unfold approveGas
    generalize sstoreCost sevm pre (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
      (Sevm.dataWord sevm 36) = s
    omega
  have hs : gCallStipend < G + 62 + 1859 + sstoreCost sevm pre
      (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr) (Sevm.dataWord sevm 36) := by
    generalize sstoreCost sevm pre (allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr)
      (Sevm.dataWord sevm 36) = s at hg ⊢
    have e : gCallStipend = 2300 := rfl
    rw [e] at h_sentry ⊢
    omega
  obtain ⟨post, hrun, hpg, hpo⟩ := approve_entry (sevm := sevm) (b := pre) (G := G)
    (sel := Sevm.selector sevm) hfork h_static h_value hs
  refine ⟨post, ⟨_, rfl, ?_⟩, hpg, hpo⟩
  have h0 := dispatch_approve (b := pre) h_len h_len' hsel hrun
  rw [pre_eq_St h_stack h_mem hg] at h0
  exact h0

end Blanc.Lift.Weth9
