import Blanc.Lift.Weth9.LiveDeposit
import Blanc.Lift.ExactWalkCall
import Blanc.ForwardStorageAccess

namespace Blanc.Lift.Weth9

open Jaune Blanc.Lift

section WChain

variable (sevm : Sevm) (b : Devm) (wad : B256)

/-- After the balance check's `SLOAD`. -/
abbrev wB1 : Devm := afterSload sevm b (balSlot sevm.caller)
/-- After the debit's `SLOAD`. -/
abbrev wB2 : Devm := afterSload sevm (wB1 sevm b) (balSlot sevm.caller)
/-- The debited balance of the caller. -/
abbrev wV : B256 := (wB1 sevm b).getStorVal sevm.currentTarget (balSlot sevm.caller) - wad
/-- After the debit's `SSTORE`: the state the ether is sent from. -/
abbrev wB3 : Devm := afterSstore sevm (wB2 sevm b) (balSlot sevm.caller) (wV sevm b wad)

end WChain

/-- The topic of `Withdrawal(address indexed src, uint wad)`. -/
def wdTopic : B256 := Bytes.toB256 [0x7f, 0xcf, 0x53, 0x2c, 0x15, 0xf0, 0xa6, 0xdb, 0x0b, 0xd6, 0xd0, 0xe0, 0x38, 0xbe, 0xa7, 0x1d, 0x30, 0xd8, 0x08, 0xc7, 0xd9, 0x8c, 0xb3, 0xbf, 0x72, 0x68, 0xa9, 0x5b, 0xf5, 0x08, 0x1b, 0x65]

/-- The memory image the `withdraw` body leaves: the two balance-slot hashes and the event word. -/
def wdMem (M : Mem) (C wad : B256) : Mem :=
  (scratchW (scratchW M C 3) C 3).write 96 wad.toBytes

theorem wdMem_fp {M : Mem} (h : FpMem 96 M) (C wad : B256) : FpMem 128 (wdMem M C wad) :=
  (((h.scratchW C 3).scratchW C 3).write_out wad)

/-- The `withdraw` body (entry 8, `0x09d9`) for `wad ≠ 0`, from the stack `wad, return, …`: the
balance check, the debit, the ether send to the caller (a code-free, non-precompile account) and
the `Withdrawal` event.  The charges are named atoms: the balance check's `SLOAD` (`cH`), the debit's
(`c2`) and `SSTORE` (`cS`), the send (`cC`, `callNet`).  `96` gas up to the first `SLOAD`, `130` to the
second, `16` to the `SSTORE`, `69` from it to the `CALL`, `1488` after it (`1381` for the `LOG2`, a word
of expansion included).  The run ends in a `post` the `CALL` leaves. -/
theorem withdraw_body {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {cH c2 cS cC : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hM : FpMem 96 M) (hroom : S.length < 1000) (hwad : wad ≠ 0)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h0 : cH = sloadCost sevm b (balSlot sevm.caller))
    (h1 : c2 = sloadCost sevm (wB1 sevm b) (balSlot sevm.caller))
    (hS : cS = sstoreCost sevm (wB2 sevm b) (balSlot sevm.caller) (wV sevm b wad))
    (hC : cC = callNet (wB3 sevm b wad) sevm.caller)
    (hsentry : gCallStipend < G + 1488 + cC + 69 + cS)
    (hcallgas : gCallStipend ≤ G + 1488)
    (hcode : ((wB3 sevm b wad).getCode sevm.caller).size = 0)
    (hprec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (hbal : ¬ ((wB3 sevm b wad).getAcct sevm.currentTarget).bal < wad) :
    ∃ post, CallPost sevm (wB3 sevm b wad) post sevm.caller wad ∧
      SFunc.RunExact prog sevm (St b (wad :: ret :: S) M
        (G + 1488 + cC + 69 + cS + 16 + c2 + 130 + cH + 96)) t_09d9_c8
        (.returned (St (post.addLog ⟨sevm.currentTarget, [wdTopic, sevm.caller.toB256],
          wad.toBytes⟩) S (wdMem M sevm.caller.toB256 wad) G)) := by
  obtain ⟨post, hrunc, hpost, hSt⟩ := callNZ_ex (sevm := sevm) (b := wB3 sevm b wad)
    (M := scratchW (scratchW M sevm.caller.toB256 3) sevm.caller.toB256 3)
    (S := 96 :: wad :: 0 :: sevm.caller.toB256 :: wad :: ret :: S) (G := G + 1488) (c := cC)
    (gw := 0) (cw := sevm.caller.toB256) (vw := wad) (iiw := 96) (isw := 96 - 96) (oiw := 96)
    (osw := 0) hfork hwad (by decide) (by decide) (by decide)
    (by simpa [toAdr_toB256] using hcode) (by simpa [toAdr_toB256] using hprec) hstatic hdepth hbal
    (by simp; omega) (by rw [toAdr_toB256]; exact hC) hcallgas
  rw [toAdr_toB256] at hpost
  refine ⟨post, hpost, ?_⟩
  rdest
  rdup
  rpush
  rpush
  refine rx_caller (by rroom) ?_
  rhash
  rsloadC
  rreq hle
  rdest
  rdup
  rpush
  rpush
  refine rx_caller (by rroom) ?_
  rhash
  rpush
  rdup
  rdup
  rsloadC
  rsub
  rswap
  rpop
  rpop
  rdup
  rswap
  rsstoreC
  rpop
  refine rx_caller (by rroom) ?_
  rmask
  rpush
  rdup
  rswap
  rdup
  refine rx_iszero (v := 0) (by simp [B256.eqCheck, hwad]) (by rroom) ?_
  refine rx_mul (v := 0) (by decide) (by rroom) ?_
  rswap
  rpush
  rmld
  rpush
  rpush
  rmld
  rdup
  rdup
  rsub
  rdup
  rdup
  rdup
  rdup
  refine .next hrunc ?_
  rw [hSt]
  rswap
  rpop
  rpop
  rpop
  rpop
  riszero
  riszero
  rpush
  refine rx_branch_succ (by decide) ?_
  rdest
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
  rlog2
  rpop
  refine rx_ret (d := ret) (b := ?_) (M := ?_)


/-- **The `withdraw` body around an abstract send.**  The `CALL` to the caller is any step `hsend` says
succeeds from the state the debit leaves, entering at gas `X` and leaving `post` (stack `1`, memory kept)
at gas `G + 1488`; `Q post` is what the callee's run guarantees.  This is the body for a recipient
*with* code: nothing is assumed of the callee except `hsend`. -/
theorem withdraw_body_send {sevm : Sevm} {b : Devm} {G X : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {cH c2 cS : Nat} {Q : Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000) (hwad : wad ≠ 0)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h0 : cH = sloadCost sevm b (balSlot sevm.caller))
    (h1 : c2 = sloadCost sevm (wB1 sevm b) (balSlot sevm.caller))
    (hS : cS = sstoreCost sevm (wB2 sevm b) (balSlot sevm.caller) (wV sevm b wad))
    (hsentry : gCallStipend < X + 69 + cS)
    (hsend : ∃ post, Ninst.RunCompiled sevm
        (St (wB3 sevm b wad) (0 :: sevm.caller.toB256 :: wad :: 96 :: (96 - 96) :: 96 :: 0 :: 96 ::
          wad :: 0 :: sevm.caller.toB256 :: wad :: ret :: S)
          (scratchW (scratchW M sevm.caller.toB256 3) sevm.caller.toB256 3) X) (.exec .call) post ∧
      post = St post (1 :: 96 :: wad :: 0 :: sevm.caller.toB256 :: wad :: ret :: S)
        (scratchW (scratchW M sevm.caller.toB256 3) sevm.caller.toB256 3) (G + 1488) ∧ Q post) :
    ∃ post, Q post ∧
      SFunc.RunExact prog sevm (St b (wad :: ret :: S) M
        (X + 69 + cS + 16 + c2 + 130 + cH + 96)) t_09d9_c8
        (.returned (St (post.addLog ⟨sevm.currentTarget, [wdTopic, sevm.caller.toB256],
          wad.toBytes⟩) S (wdMem M sevm.caller.toB256 wad) G)) := by
  obtain ⟨post, hrunc, hSt, hQ⟩ := hsend
  refine ⟨post, hQ, ?_⟩
  rdest
  rdup
  rpush
  rpush
  refine rx_caller (by rroom) ?_
  rhash
  rsloadC
  rreq hle
  rdest
  rdup
  rpush
  rpush
  refine rx_caller (by rroom) ?_
  rhash
  rpush
  rdup
  rdup
  rsloadC
  rsub
  rswap
  rpop
  rpop
  rdup
  rswap
  rsstoreC
  rpop
  refine rx_caller (by rroom) ?_
  rmask
  rpush
  rdup
  rswap
  rdup
  refine rx_iszero (v := 0) (by simp [B256.eqCheck, hwad]) (by rroom) ?_
  refine rx_mul (v := 0) (by decide) (by rroom) ?_
  rswap
  rpush
  rmld
  rpush
  rpush
  rmld
  rdup
  rdup
  rsub
  rdup
  rdup
  rdup
  rdup
  refine .next hrunc ?_
  rw [hSt]
  rswap
  rpop
  rpop
  rpop
  rpop
  riszero
  riszero
  rpush
  refine rx_branch_succ (by decide) ?_
  rdest
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
  rlog2
  rpop
  refine rx_ret (d := ret) (b := ?_) (M := ?_)

/-- The `withdraw` body for `wad = 0`: the send is a zero-value `CALL` with the stipend as its gas
argument (`0x08fc · iszero(0)`); the callee returns it, so the send costs the account access alone.
Same walk as `withdraw_body`. -/
theorem withdraw_body_zero {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {cH c2 cS cC : Nat} (hw0 : wad = 0)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h0 : cH = sloadCost sevm b (balSlot sevm.caller))
    (h1 : c2 = sloadCost sevm (wB1 sevm b) (balSlot sevm.caller))
    (hS : cS = sstoreCost sevm (wB2 sevm b) (balSlot sevm.caller) (wV sevm b wad))
    (hC : cC = accessCost sevm.caller (wB3 sevm b wad).accessedAddresses)
    (hsentry : gCallStipend < G + 1488 + cC + 69 + cS)
    (hcode : ((wB3 sevm b wad).getCode sevm.caller).size = 0)
    (hprec : sevm.benvStat.rules.isPrecomp sevm.caller = false) :
    ∃ post, CallPost sevm (wB3 sevm b wad) post sevm.caller 0 ∧
      SFunc.RunExact prog sevm (St b (wad :: ret :: S) M
        (G + 1488 + cC + 69 + cS + 16 + c2 + 130 + cH + 96)) t_09d9_c8
        (.returned (St (post.addLog ⟨sevm.currentTarget, [wdTopic, sevm.caller.toB256],
          wad.toBytes⟩) S (wdMem M sevm.caller.toB256 wad) G)) := by
  subst hw0
  obtain ⟨post, hrunc, hpost, hSt⟩ := callZ_ex (sevm := sevm) (b := wB3 sevm b 0)
    (M := scratchW (scratchW M sevm.caller.toB256 3) sevm.caller.toB256 3)
    (S := 96 :: 0 :: 2300 :: sevm.caller.toB256 :: 0 :: ret :: S) (G := G + 1488) (c := cC)
    (gw := 2300) (cw := sevm.caller.toB256) (iiw := 96) (isw := 96 - 96) (oiw := 96)
    (osw := 0) hfork (by decide) (by decide) (by decide)
    (by simpa [toAdr_toB256] using hcode) (by simpa [toAdr_toB256] using hprec) hdepth
    (by simp; omega) (by rw [toAdr_toB256]; exact hC)
  rw [toAdr_toB256] at hpost
  refine ⟨post, hpost, ?_⟩
  rdest
  rdup
  rpush
  rpush
  refine rx_caller (by rroom) ?_
  rhash
  rsloadC
  rreq hle
  rdest
  rdup
  rpush
  rpush
  refine rx_caller (by rroom) ?_
  rhash
  rpush
  rdup
  rdup
  rsloadC
  rsub
  rswap
  rpop
  rpop
  rdup
  rswap
  rsstoreC
  rpop
  refine rx_caller (by rroom) ?_
  rmask
  rpush
  rdup
  rswap
  rdup
  refine rx_iszero (v := 1) (by simp [B256.eqCheck]) (by rroom) ?_
  refine rx_mul (v := 2300) (by decide) (by rroom) ?_
  rswap
  rpush
  rmld
  rpush
  rpush
  rmld
  rdup
  rdup
  rsub
  rdup
  rdup
  rdup
  rdup
  refine .next hrunc ?_
  rw [hSt]
  rswap
  rpop
  rpop
  rpop
  rpop
  riszero
  riszero
  rpush
  refine rx_branch_succ (by decide) ?_
  rdest
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
  rlog2
  rpop
  refine rx_ret (d := ret) (b := ?_) (M := ?_)

/-- The ether send's net charge does not see the debit's storage writes. -/
theorem callNet_wB3 {sevm : Sevm} {b : Devm} {wad : B256} (a : Adr) :
    callNet (wB3 sevm b wad) a = callNet b a := by
  unfold callNet
  simp only [wB3, wB2, wB1, afterSstore_accessedAddresses, afterSload_accessedAddresses,
    afterSstore_empty, afterSload_getAcct]

/-- The `withdraw` wrapper (entry 24, `0x0243`): the `nonpayable` guard, the argument decode, the call
into the body, the closing `STOP`.  `68` gas before the body, `1` after it. -/
theorem withdraw_wrapper {sevm : Sevm} {b b' : Devm} {G X : Nat} {sel : B256} {M' : Mem}
    (hval : sevm.value = 0)
    (hbody : SFunc.RunExact prog sevm
      (St b [Sevm.dataWord sevm 4, Bytes.toB256 [0x02, 0x64], sel] memFp X) t_09d9_c8
      (.returned (St b' [sel] M' (G + 1)))) :
    ∃ post, SFunc.RunExact prog sevm (St b [sel] memFp (X + 68)) t_0243_c24 (.halted post) ∧
      post = St b' [sel] M' G := by
  refine ⟨St b' [sel] M' G, ?_, rfl⟩
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
  rswap
  rpush
  radd
  rswap
  rswap
  rswap
  rpop
  rpop
  rpush
  refine rx_callRet (j := 8) rfl hbody ?_
  rdest
  exact rx_stop

/-- WETH9's `withdraw(uint256)` selector. -/
abbrev wdSel : B256 := selector "withdraw" [.uint256]

theorem wdSel_eq : wdSel = 0x2e1a7d4d := by decide +kernel

/-- The dispatcher path to `withdraw`: three non-matching comparisons after the head's, then the match
at the fifth, jumping to entry 24.  172 gas. -/
theorem dispatch_withdraw {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0x2e1a7d4d)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g) t_0243_c24 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 172)) t_0000_c0 o := by
  refine dispatch_head h_len h_len' (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  exact cmp_hit (j := 24) (by rw [hsel]; decide) rfl k


/-- **What `withdraw(wad)` costs** for `wad ≠ 0` to a code-free caller: the dispatcher (172), the wrapper
(68 + 1), the body's fixed part (`96 + 130 + 16 + 69 + 1488`), the balance check's `SLOAD`, the debit's
`SLOAD` and `SSTORE`, and the ether send at its net charge (`callNet`: the caller's access, warm or
cold, a new-account charge if the caller is an empty account, the value-transfer charge, less the
stipend the callee returns). -/
def withdrawGas (sevm : Sevm) (pre : Devm) : Nat :=
  2040 + sloadCost sevm pre (balSlot sevm.caller) +
    sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller) +
    sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4)) +
    callNet pre sevm.caller

/-- What a successful `withdraw(wad)` frame leaves of its final machine besides the gas, stack and
memory: the output, the frame error, the refund counter the debit's `SSTORE` leaves, the emptiness of the
accounts to delete, the `Withdrawal` event appended to the logs, and the world: the debited state with
`wad` ether moved from the contract to the caller. -/
structure WithdrawPost (sevm : Sevm) (pre post : Devm) (wad : B256) : Prop where
  output : post.output = pre.output
  error : post.error = pre.error
  logs : post.logs = pre.logs ++ [⟨sevm.currentTarget, [wdTopic, sevm.caller.toB256], wad.toBytes⟩]
  refund : post.refundCounter = sstoreNewRefundCounter sevm.benvStat.rules.gas (wV sevm pre wad)
    (getOrigStorVal sevm sevm.currentTarget (balSlot sevm.caller))
    (pre.getStorVal sevm.currentTarget (balSlot sevm.caller)) pre.refundCounter
  accountsToDelete : post.accountsToDelete.isEmpty = pre.accountsToDelete.isEmpty
  state : ∃ stmid, (wB3 sevm pre wad).state.subBal sevm.currentTarget wad = some stmid ∧
    post.state = stmid.addBal sevm.caller wad

/-- **Liveness of `withdraw(wad)` to an externally owned account, gas-exact, with the final machine.**  A frame entering
`withdraw(wad)` with `0 < wad ≤ balanceOf[caller]`, whose caller has no code and is no precompile, and
whose contract holds the ether, succeeds at exactly `withdrawGas` (the recipient's empty code returns
the whole stipend, so the send is a single step); it debits the caller's balance slot and touches no
other storage.  (`h_sentry`: the debit's `SSTORE` runs with more than `gCallStipend` gas;
`h_callgas`: the `CALL` leaves the frame at least the stipend the callee returns.) -/
theorem weth9_withdraw_runExact_post {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (hwad : Sevm.dataWord sevm 4 ≠ 0)
    (hle : Sevm.dataWord sevm 4 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h_code : (pre.getCode sevm.caller).size = 0)
    (h_prec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (h_eth : ¬ (pre.getAcct sevm.currentTarget).bal < Sevm.dataWord sevm 4)
    (h_gas : pre.gasLeft = G + withdrawGas sevm pre)
    (h_sentry : gCallStipend < G + 1 + 1488 + callNet pre sevm.caller + 69 +
      sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4)))
    (h_callgas : gCallStipend ≤ G + 1 + 1488) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧
      WithdrawPost sevm pre post (Sevm.dataWord sevm 4) ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
      ∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a := by
  have hsel : Sevm.selector sevm = 0x2e1a7d4d := h_sel.trans wdSel_eq
  have hg : G + 1 + 1488 + callNet pre sevm.caller + 69 +
      sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4)) + 16 +
      sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller) + 130 +
      sloadCost sevm pre (balSlot sevm.caller) + 96 + 68 + 172 = pre.gasLeft := by
    rw [h_gas]; unfold withdrawGas; omega
  obtain ⟨post, hcp, hbody⟩ := withdraw_body (S := [Sevm.selector sevm]) (ret := Bytes.toB256 [2, 100])
    (G := G + 1) (b := pre) (wad := Sevm.dataWord sevm 4) (M := memFp)
    (cH := sloadCost sevm pre (balSlot sevm.caller))
    (c2 := sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller))
    (cS := sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4)))
    (cC := callNet pre sevm.caller) hfork h_static h_depth fp_memFp (by simp) hwad hle rfl rfl rfl
    (by rw [callNet_wB3]) h_sentry h_callgas
    (by simpa [wB3, wB2, wB1] using h_code) h_prec
    (by
      have e : ((wB3 sevm pre (Sevm.dataWord sevm 4)).getAcct sevm.currentTarget).bal =
          (pre.getAcct sevm.currentTarget).bal := by
        have h1 := afterSstore_getBal (sevm := sevm) (b := wB2 sevm pre) (key := balSlot sevm.caller)
          (value := wV sevm pre (Sevm.dataWord sevm 4)) sevm.currentTarget
        simpa [Devm.getBal, wB3, wB2, wB1, afterSload_getAcct] using h1
      rw [e]; exact h_eth)
  obtain ⟨postW, hw, hpe⟩ := withdraw_wrapper (sevm := sevm) (b := pre) (G := G) (X := _)
    (sel := Sevm.selector sevm) h_value hbody
  refine ⟨postW, ⟨_, rfl, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have h0 := dispatch_withdraw (b := pre) h_len h_len' hsel hw
    rw [pre_eq_St h_stack h_mem hg] at h0
    exact h0
  · rw [hpe]; rfl
  · rw [hpe]
    show post.output = pre.output
    rw [hcp.output]
    simp [wB3, wB2, wB1]
  · rw [hpe]
    show post.error = pre.error
    rw [hcp.error]
    simp [wB3, wB2, wB1]
  · rw [hpe]
    show post.logs ++ _ = pre.logs ++ _
    rw [hcp.logs]
    simp [wB3, wB2, wB1]
  · rw [hpe]
    show post.refundCounter = _
    rw [hcp.refund]
    simp [wB3, wB2, wB1, wV, getStorVal_afterSload, afterSload_refundCounter]
  · rw [hpe]
    show post.accountsToDelete.isEmpty = _
    rw [hcp.accountsToDelete]
    simp [wB3, wB2, wB1, afterSload_accountsToDelete]
  · rw [hpe]
    obtain ⟨stmid, hsub, hst⟩ := hcp.state
    exact ⟨stmid, hsub, hst⟩
  · rw [hpe]
    show Devm.getStor post sevm.currentTarget = _
    rw [hcp.getStor]
    simp [wB3, wB2, wB1, wV, getStorVal_afterSload]
  · intro a ha
    rw [hpe]
    show Devm.getStor post a = _
    rw [hcp.getStor]
    simp [wB3, wB2, wB1, ha.symm]


/-- **Liveness of `withdraw(wad)` to an externally owned account, gas-exact.**  A frame entering
`withdraw(wad)` with `0 < wad ≤ balanceOf[caller]`, whose caller has no code and is no precompile, and
whose contract holds the ether, succeeds at exactly `withdrawGas` (the recipient's empty code returns
the whole stipend, so the send is a single step); it debits the caller's balance slot and touches no
other storage.  (`h_sentry`: the debit's `SSTORE` runs with more than `gCallStipend` gas;
`h_callgas`: the `CALL` leaves the frame at least the stipend the callee returns.) -/
theorem weth9_withdraw_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (hwad : Sevm.dataWord sevm 4 ≠ 0)
    (hle : Sevm.dataWord sevm 4 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h_code : (pre.getCode sevm.caller).size = 0)
    (h_prec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (h_eth : ¬ (pre.getAcct sevm.currentTarget).bal < Sevm.dataWord sevm 4)
    (h_gas : pre.gasLeft = G + withdrawGas sevm pre)
    (h_sentry : gCallStipend < G + 1 + 1488 + callNet pre sevm.caller + 69 +
      sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4)))
    (h_callgas : gCallStipend ≤ G + 1 + 1488) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
      ∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a := by
  obtain ⟨post, hrun, hg, hp, hs1, hs2⟩ := weth9_withdraw_runExact_post hfork h_static h_value h_sel
    h_len h_len' h_stack h_mem h_depth hwad hle h_code h_prec h_eth h_gas h_sentry h_callgas
  exact ⟨post, hrun, hg, hp.output, hs1, hs2⟩

/-- **What `withdraw(0)` costs** for a code-free caller: as `withdrawGas` with the send at the account
access alone (the zero-value `CALL` forwards the stipend and gets it all back). -/
def withdrawZeroGas (sevm : Sevm) (pre : Devm) : Nat :=
  2040 + sloadCost sevm pre (balSlot sevm.caller) +
    sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller) +
    sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4)) +
    accessCost sevm.caller pre.accessedAddresses

/-- **Liveness of `withdraw(0)` to an externally owned account, gas-exact, with the final machine.**
(`h_sentry`: the debit's no-op `SSTORE` runs with more than `gCallStipend` gas.) -/
theorem weth9_withdraw_zero_runExact_post {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (hw0 : Sevm.dataWord sevm 4 = 0)
    (h_code : (pre.getCode sevm.caller).size = 0)
    (h_prec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (h_gas : pre.gasLeft = G + withdrawZeroGas sevm pre)
    (h_sentry : gCallStipend < G + 1 + 1488 + accessCost sevm.caller pre.accessedAddresses + 69 +
      sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4))) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧
      WithdrawPost sevm pre post (Sevm.dataWord sevm 4) ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
      ∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a := by
  have hsel : Sevm.selector sevm = 0x2e1a7d4d := h_sel.trans wdSel_eq
  have hg : G + 1 + 1488 + accessCost sevm.caller pre.accessedAddresses + 69 +
      sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4)) + 16 +
      sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller) + 130 +
      sloadCost sevm pre (balSlot sevm.caller) + 96 + 68 + 172 = pre.gasLeft := by
    rw [h_gas]; unfold withdrawZeroGas; omega
  obtain ⟨post, hcp, hbody⟩ := withdraw_body_zero (S := [Sevm.selector sevm])
    (ret := Bytes.toB256 [2, 100]) (G := G + 1) (b := pre) (wad := Sevm.dataWord sevm 4) (M := memFp)
    (cH := sloadCost sevm pre (balSlot sevm.caller))
    (c2 := sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller))
    (cS := sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4)))
    (cC := accessCost sevm.caller pre.accessedAddresses) hw0 hfork h_static h_depth fp_memFp
    (by simp) (by rw [hw0]; exact B256.zero_le _) rfl rfl rfl (by simp [wB3, wB2, wB1]) h_sentry
    (by simpa [wB3, wB2, wB1] using h_code) h_prec
  obtain ⟨postW, hw, hpe⟩ := withdraw_wrapper (sevm := sevm) (b := pre) (G := G) (X := _)
    (sel := Sevm.selector sevm) h_value hbody
  refine ⟨postW, ⟨_, rfl, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have h0 := dispatch_withdraw (b := pre) h_len h_len' hsel hw
    rw [pre_eq_St h_stack h_mem hg] at h0
    exact h0
  · rw [hpe]; rfl
  · rw [hpe]
    show post.output = pre.output
    rw [hcp.output]
    simp [wB3, wB2, wB1]
  · rw [hpe]
    show post.error = pre.error
    rw [hcp.error]
    simp [wB3, wB2, wB1]
  · rw [hpe]
    show post.logs ++ _ = pre.logs ++ _
    rw [hcp.logs]
    simp [wB3, wB2, wB1]
  · rw [hpe]
    show post.refundCounter = _
    rw [hcp.refund]
    simp [wB3, wB2, wB1, wV, getStorVal_afterSload, afterSload_refundCounter]
  · rw [hpe]
    show post.accountsToDelete.isEmpty = _
    rw [hcp.accountsToDelete]
    simp [wB3, wB2, wB1, afterSload_accountsToDelete]
  · rw [hpe]
    obtain ⟨stmid, hsub, hst⟩ := hcp.state
    rw [hw0] at hsub ⊢
    exact ⟨stmid, hsub, hst⟩
  · rw [hpe]
    show Devm.getStor post sevm.currentTarget = _
    rw [hcp.getStor]
    simp [wB3, wB2, wB1, wV, getStorVal_afterSload]
  · intro a ha
    rw [hpe]
    show Devm.getStor post a = _
    rw [hcp.getStor]
    simp [wB3, wB2, wB1, ha.symm]

/-- **Liveness of `withdraw(0)` to an externally owned account, gas-exact.**  (`h_sentry`: the debit's
no-op `SSTORE` runs with more than `gCallStipend` gas.) -/
theorem weth9_withdraw_zero_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (hw0 : Sevm.dataWord sevm 4 = 0)
    (h_code : (pre.getCode sevm.caller).size = 0)
    (h_prec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (h_gas : pre.gasLeft = G + withdrawZeroGas sevm pre)
    (h_sentry : gCallStipend < G + 1 + 1488 + accessCost sevm.caller pre.accessedAddresses + 69 +
      sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller) (wV sevm pre (Sevm.dataWord sevm 4))) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post sevm.currentTarget = (Devm.getStor pre sevm.currentTarget).set
        (balSlot sevm.caller)
        (pre.getStorVal sevm.currentTarget (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
      ∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a := by
  obtain ⟨post, hrun, hg, hp, hs1, hs2⟩ := weth9_withdraw_zero_runExact_post hfork h_static h_value
    h_sel h_len h_len' h_stack h_mem h_depth hw0 h_code h_prec h_gas h_sentry
  exact ⟨post, hrun, hg, hp.output, hs1, hs2⟩

end Blanc.Lift.Weth9
