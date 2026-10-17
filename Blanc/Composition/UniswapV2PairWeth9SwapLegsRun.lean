import Blanc.Composition.Weth9Token

/-!
# WETH9's `transfer` run with its post state named (for the swap's WETH9 leg)

`weth9_transfer_runExact` (`Blanc/Lift/Weth9/LiveTransfer.lean`) states the post of a successful
`transfer` frame existentially.  The swap's WETH9 leg needs the post itself: its error flag (the
caller's success flag reads it) and its gas-free columns (the caller's call gas is a fixed point
of them).  This file replays the same walk (tail, self body, wrapper, boolean tail) with the post
written out: `weth9TransferPost`, a function of the entry state's gas-free columns and the gas left.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9

/-- The tail's world after both balance writes and the `Transfer` event. -/
def xferTailPost (sevm : Sevm) (t0 : Devm) (src dst : Adr) (wad : B256) : Devm :=
  (afterSstore sevm (tT3 sevm t0 src dst wad) (balSlot dst) (tV2 sevm t0 src dst wad)).addLog
    { address := sevm.currentTarget,
      topics := [Bytes.toB256
          [221, 242, 82, 173, 27, 226, 200, 155, 105, 194, 176, 104, 252, 55, 141, 170, 149, 43,
            167, 241, 99, 196, 161, 22, 40, 245, 90, 77, 245, 35, 179, 239],
        src.toB256, dst.toB256],
      data := wad.toBytes }

/-- `xfer_tail` with its post named (charges as atoms). -/
theorem xfer_tail_post_gen {sevm : Sevm} {t0 : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {src dst : Adr} {cL2 cS1 cL3 cS2 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (h1 : cL2 = sloadCost sevm t0 (balSlot src))
    (h2 : cS1 = sstoreCost sevm (tT1 sevm t0 src) (balSlot src) (tV1 sevm t0 src wad))
    (h3 : cL3 = sloadCost sevm (tT2 sevm t0 src wad) (balSlot dst))
    (h4 : cS2 = sstoreCost sevm (tT3 sevm t0 src dst wad) (balSlot dst) (tV2 sevm t0 src dst wad))
    (hsentry : gCallStipend < G + 1862 + cS2) (x : B256) :
    SFunc.RunExact prog sevm (St t0 (x :: wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (G + 1862 + cS2 + 16 + cL3 + 107 + cS1 + 16 + cL2 + 106)) t_08cf_c9
      (.returned (St (xferTailPost sevm t0 src dst wad) (1 :: S)
        ((scratchW (scratchW M src.toB256 3) dst.toB256 3).write 96 wad.toBytes) G)) := by
  rdest
  rdup
  rpush
  rpush
  rdup
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
  rdup
  rpush
  rpush
  rdup
  rhash
  rpush
  rdup
  rdup
  rsloadC
  refine rx_add (by rroom) ?_
  rswap
  rpop
  rpop
  rdup
  rswap
  rsstoreC
  rpop
  rdup
  rmask
  rdup
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
  rpop
  exact rx_ret (d := ret)

/-- `xfer_body_self_gen` with its post named. -/
theorem xfer_body_self_post {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {src dst : Adr} {cH cL2 cS1 cL3 cS2 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot src)) (hcs : sevm.caller = src)
    (h0 : cH = sloadCost sevm b (balSlot src))
    (h1 : cL2 = sloadCost sevm (pB1 sevm b src) (balSlot src))
    (h2 : cS1 = sstoreCost sevm (tT1 sevm (pB1 sevm b src) src) (balSlot src)
      (tV1 sevm (pB1 sevm b src) src wad))
    (h3 : cL3 = sloadCost sevm (tT2 sevm (pB1 sevm b src) src wad) (balSlot dst))
    (h4 : cS2 = sstoreCost sevm (tT3 sevm (pB1 sevm b src) src dst wad) (balSlot dst)
      (tV2 sevm (pB1 sevm b src) src dst wad))
    (hsentry : gCallStipend < G + 1862 + cS2) :
    SFunc.RunExact prog sevm (St b (wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (G + 1862 + cS2 + 16 + cL3 + 107 + cS1 + 16 + cL2 + 106 + 60 + 25 + cH + 100)) t_068c_c9
      (.returned (St (xferTailPost sevm (pB1 sevm b src) src dst wad) (1 :: S)
        ((scratchW (scratchW (scratchW M src.toB256 3) src.toB256 3) dst.toB256 3).write 96
          wad.toBytes) G)) := by
  have htail := xfer_tail_post_gen (t0 := pB1 sevm b src) (M := scratchW M src.toB256 3) (G := G)
    (S := S) (wad := wad) (ret := ret) hfork hstatic (hM.scratchW _ _) hroom h1 h2 h3 h4 hsentry
  rxf_head hle
  refine rx_caller (by rroom) ?_
  rmask
  rdup
  rmask
  refine rx_eq (v := 1) (by simp only [B256.eqCheck, hcs, ↓reduceIte]) (by rroom) ?_
  riszero
  rdup
  riszero
  rpush
  refine rx_branch_succ (by decide) ?_
  rdest
  riszero
  rpush
  refine rx_branch_succ (by decide) ?_
  exact htail _

/-- The boolean tail with its post named. -/
theorem bool_tail_post {sevm : Sevm} {b : Devm} {G : Nat} {M1 : Mem} {sel : B256}
    (hM : FpMem 128 M1) :
    SFunc.RunExact prog sevm (St b [1, sel] M1 (G + 62)) t_0187_c27
      (.halted (((St b [sel] (M1.write 96 (B256.toBytes 1)) G).memRead (B256.toNat 96)
        (B256.toNat 32)).2.withOutput (B256.toBytes 1))) := by
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

/-- The post a `transfer` wrapper leaves after a body that returns in `b'` with memory `M'`. -/
def transferWrapperPost (b' : Devm) (sel : B256) (M' : Mem) (G : Nat) : Devm :=
  ((St b' [sel] (M'.write 96 (B256.toBytes 1)) G).memRead (B256.toNat 96)
    (B256.toNat 32)).2.withOutput (B256.toBytes 1)

/-- `transfer_wrapper` with its post named. -/
theorem transfer_wrapper_post {sevm : Sevm} {b b' : Devm} {G X : Nat} {sel : B256} {M' : Mem}
    (hval : sevm.value = 0)
    (hbody : SFunc.RunExact prog sevm
      (St b [Sevm.dataWord sevm 36, (Sevm.dataWord sevm 4).toAdr.toB256, sevm.caller.toB256,
        Bytes.toB256 [0x0b, 0xdb], 0, Sevm.dataWord sevm 36, (Sevm.dataWord sevm 4).toAdr.toB256,
        Bytes.toB256 [0x03, 0xb0], sel] memFp X) t_068c_c9
      (.returned (St b' [1, 0, Sevm.dataWord sevm 36, (Sevm.dataWord sevm 4).toAdr.toB256,
        Bytes.toB256 [0x03, 0xb0], sel] M' (G + 24 + 62))))
    (hM' : FpMem 128 M') :
    SFunc.RunExact prog sevm (St b [sel] memFp (X + 26 + 98)) t_0370_c20
      (.halted (transferWrapperPost b' sel M' G)) := by
  have htail := bool_tail_post (sevm := sevm) (b := b') (G := G) (sel := sel) hM'
  rdest
  refine rx_callvalue (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, hval, ↓reduceIte]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
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
  refine rx_callRet (D := St b' [1, sel] M' (G + 62)) (j := 3) rfl ?_ htail
  · rdest
    rpush
    rpush
    refine rx_caller (by rroom) ?_
    rdup
    rdup
    rpush
    refine rx_callRet (j := 9) rfl hbody ?_
    rdest
    rswap
    rpop
    rswap
    rswap
    rpop
    rpop
    exact rx_ret

/-- The body's memory on a `transfer` frame. -/
def transferBodyMem (sevm : Sevm) : Mem :=
  (scratchW (scratchW (scratchW memFp sevm.caller.toB256 3) sevm.caller.toB256 3)
    (Sevm.dataWord sevm 4).toAdr.toB256 3).write 96 (Sevm.dataWord sevm 36).toBytes

/-- **The post of a successful WETH9 `transfer` frame**, from its entry state and the gas left. -/
def weth9TransferPost (sevm : Sevm) (pre : Devm) (G : Nat) : Devm :=
  transferWrapperPost (xferTailPost sevm (pB1 sevm pre sevm.caller) sevm.caller
    (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)) (Sevm.selector sevm) (transferBodyMem sevm) G

/-- `weth9_transfer_runExact` with its post named. -/
theorem weth9_transfer_runExact_post {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = trSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hle : Sevm.dataWord sevm 36 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h_gas : pre.gasLeft = G + transferGas sevm pre)
    (h_sentry : gCallStipend < G + 24 + 62 + 1862 + sstoreCost sevm
      (tT3 sevm (pB1 sevm pre sevm.caller) sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36)) (balSlot (Sevm.dataWord sevm 4).toAdr)
      (tV2 sevm (pB1 sevm pre sevm.caller) sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36))) :
    SProg.RunExact prog sevm pre (weth9TransferPost sevm pre G) := by
  have hsel : Sevm.selector sevm = 0xa9059cbb := h_sel.trans trSel_eq
  have hg : xferGasSelf sevm pre sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)
      (G + 24 + 62) + 26 + 98 + 260 = pre.gasLeft := by
    rw [h_gas, xferGasSelf_eq]; unfold transferGas; omega
  have hb := xfer_body_self_post (S := [0, Sevm.dataWord sevm 36, (Sevm.dataWord sevm 4).toAdr.toB256,
      Bytes.toB256 [0x03, 0xb0], Sevm.selector sevm]) (ret := Bytes.toB256 [0x0b, 0xdb])
    (G := G + 24 + 62) (b := pre) hfork h_static fp_memFp (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) hle rfl rfl rfl rfl rfl rfl h_sentry
  have hw := transfer_wrapper_post (sevm := sevm) (b := pre) (G := G)
    (sel := Sevm.selector sevm) h_value hb
    (((((fp_memFp.scratchW _ _).scratchW _ _).scratchW _ _)).write_out _)
  refine ⟨_, rfl, ?_⟩
  have h0 : SFunc.RunExact prog sevm (St pre [] Mem.empty
      (xferGasSelf sevm pre sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)
        (G + 24 + 62) + 26 + 98 + 260)) t_0000_c0 (.halted (weth9TransferPost sevm pre G)) :=
    dispatch_transfer (b := pre) h_len h_len' hsel hw
  rw [pre_eq_St h_stack h_mem hg] at h0
  exact h0

/-! ## `balanceOf` -/

/-- The post the one-word view tail leaves. -/
def wordTailPost (b : Devm) (v r sel : B256) (μ : Mem) (g : Nat) : Devm :=
  ((St b [r, sel] (memOut μ v) g).memRead (B256.toNat 96) ((32 : B256) + 96 - 96).toNat).2.withOutput
    v.toBytes

/-- `word_tail` with its post named. -/
theorem word_tail_post {sevm : Sevm} {b : Devm} {g : Nat} {v r sel : B256} {μ : Mem} {bs : Bytes}
    (hs : μ.size = 96) (hwf : Mem.Wf μ) (hr : Mem.Reads μ bs)
    (hfp : (μ.read 64 32).1 = (0x60 : B256).toBytes) :
    SFunc.RunExact prog sevm (St b [v, r, sel] μ (g + 53)) t_02cc_c22
      (.halted (wordTailPost b v r sel μ g)) := by
  refine rx_dest ?_
  refine rx_push (w := 64) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mload (c := 3) (v := 0x60) ?_ ?_ (read_covered hs (by decide) (by decide))
    (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  · rw [St.extCost_eq hs]; decide
  · show Bytes.toB256 (μ.read 64 32).1 = _
    rw [hfp, B256.toB256_toBytes]
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup3 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_mstore (c := 6) (M' := memOut μ v) ?_ rfl ?_
  · rw [St.extCost_eq hs]; decide
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_swap2 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 64) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_mload (c := 3) (v := 0x60) ?_ ?_
    (read_covered (memOut_size hs v) (by decide) (by decide)) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  · rw [St.extCost_eq (memOut_size hs v)]; decide
  · show Bytes.toB256 ((memOut μ v).read 64 32).1 = _
    rw [memOut_fp hwf hr hfp, B256.toB256_toBytes]
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_swap2 ?_
  refine rx_sub (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_swap1 ?_
  refine rx_return (out := v.toBytes) ?_ ?_
  · rw [St.extCost_eq (memOut_size hs v)]; decide
  · have h32 : ((32 : B256) + 0x60 - 0x60).toNat = 32 := by decide
    rw [h32]
    exact memOut_val hwf hr v

/-- `bal_entry` with its post named. -/
theorem bal_entry_post {sevm : Sevm} {b b' : Devm} {g G : Nat} {sel v : B256} {μ : Mem} {bs : Bytes}
    (hval : sevm.value = 0)
    (hcall : SFunc.RunExact prog sevm
      (St b [(Sevm.dataWord sevm 4).toAdr.toB256, Bytes.toB256 [0x02, 0xcc], sel] memFp G)
      t_0b18_c6 (.returned (St b' [v, Bytes.toB256 [0x02, 0xcc], sel] μ (g + 53))))
    (hs : μ.size = 96) (hwf : Mem.Wf μ) (hr : Mem.Reads μ bs)
    (hfp : (μ.read 64 32).1 = (0x60 : B256).toBytes) :
    SFunc.RunExact prog sevm (St b [sel] memFp (G + 74)) t_0295_c22
      (.halted (wordTailPost b' v (Bytes.toB256 [0x02, 0xcc]) sel μ g)) := by
  have hrun := word_tail_post (sevm := sevm) (b := b') (g := g) (v := v)
    (r := Bytes.toB256 [0x02, 0xcc]) (sel := sel) hs hwf hr hfp
  refine rx_dest ?_
  refine rx_callvalue (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, hval, ↓reduceIte]) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rx_push (w := 4) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_and (ff20_and_word _) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_swap1 ?_
  refine rx_push (w := 32) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rx_add (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  exact rx_callRet (j := 6) rfl hcall hrun

/-- The balance `balanceOf` reads on a frame. -/
def weth9BalanceAnswer (sevm : Sevm) (pre : Devm) : B256 :=
  pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr)

/-- What a `balanceOf` frame costs: its one `SLOAD`, warm or cold. -/
def weth9BalanceGas (sevm : Sevm) (pre : Devm) : Nat :=
  if (⟨sevm.currentTarget, balSlot (Sevm.dataWord sevm 4).toAdr⟩ : Adr × B256) ∈
    pre.accessedStorageKeys then 534 else 2534

/-- **The post of a successful WETH9 `balanceOf` frame**, from its entry state and the gas left. -/
def weth9BalancePost (sevm : Sevm) (pre : Devm) (G : Nat) : Devm :=
  wordTailPost (afterSload sevm pre (balSlot (Sevm.dataWord sevm 4).toAdr)) (weth9BalanceAnswer sevm pre)
    (Bytes.toB256 [0x02, 0xcc]) (Sevm.selector sevm) (memBal (Sevm.dataWord sevm 4).toAdr.toB256) G

/-- `weth9_balanceOf_runExact` with its post named. -/
theorem weth9_balanceOf_runExact_post {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = 0x70a08231)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + weth9BalanceGas sevm pre) :
    SProg.RunExact prog sevm pre (weth9BalancePost sevm pre G) := by
  have hleg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  refine ⟨_, rfl, ?_⟩
  unfold weth9BalanceGas at h_gas
  by_cases hw : (⟨sevm.currentTarget, balSlot (Sevm.dataWord sevm 4).toAdr⟩ : Adr × B256) ∈
      pre.accessedStorageKeys
  · rw [ite_eq_left hw] at h_gas
    have hrun := bal_entry_post (b := pre) (g := G) (G := G + 53 + 191) h_value
      (bal_callee_warm (b := pre) (g := G + 53) (S := [Sevm.selector sevm])
        (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) hleg hw)
      (memBal_size _) (wf_memBal _) (reads_memBal _) (memBal_fp _)
    have h0 := dispatch_balanceOf (b := pre) h_len h_len' h_sel hrun
    rw [pre_eq_St h_stack h_mem (by omega)] at h0
    have hw' : afterSload sevm pre (balSlot (Sevm.dataWord sevm 4).toAdr) = pre := ite_eq_left hw
    unfold weth9BalancePost
    rw [hw']
    exact h0
  · rw [ite_eq_right hw] at h_gas
    have hrun := bal_entry_post (b := pre) (g := G) (G := G + 53 + 2191) h_value
      (bal_callee_cold (b := pre) (g := G + 53) (S := [Sevm.selector sevm])
        (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) hleg hw)
      (memBal_size _) (wf_memBal _) (reads_memBal _) (memBal_fp _)
    have h0 := dispatch_balanceOf (b := pre) h_len h_len' h_sel hrun
    rw [pre_eq_St h_stack h_mem (by omega)] at h0
    have hw' : afterSload sevm pre (balSlot (Sevm.dataWord sevm 4).toAdr) =
        addAccessedStorageKey pre sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr) := ite_eq_right hw
    unfold weth9BalancePost
    rw [hw']
    exact h0

/-! ## The named posts' columns -/

theorem weth9TransferPost_gasLeft (sevm : Sevm) (pre : Devm) (G : Nat) :
    (weth9TransferPost sevm pre G).gasLeft = G := rfl

theorem weth9TransferPost_output (sevm : Sevm) (pre : Devm) (G : Nat) :
    (weth9TransferPost sevm pre G).output = (1 : B256).toBytes := rfl

theorem weth9TransferPost_error (sevm : Sevm) (pre : Devm) (G : Nat) :
    (weth9TransferPost sevm pre G).error = pre.error := by
  simp only [weth9TransferPost, transferWrapperPost, xferTailPost, Devm.withOutput_error,
    Devm.memRead_error, St, Devm.setMach_error, Devm.addLog_error, afterSstore_error, afterSload_error]

theorem weth9BalancePost_gasLeft (sevm : Sevm) (pre : Devm) (G : Nat) :
    (weth9BalancePost sevm pre G).gasLeft = G := rfl

theorem weth9BalancePost_output (sevm : Sevm) (pre : Devm) (G : Nat) :
    (weth9BalancePost sevm pre G).output = (weth9BalanceAnswer sevm pre).toBytes := rfl

theorem weth9BalancePost_error (sevm : Sevm) (pre : Devm) (G : Nat) :
    (weth9BalancePost sevm pre G).error = pre.error := by
  simp only [weth9BalancePost, wordTailPost, Devm.withOutput_error, Devm.memRead_error, St, Devm.setMach_error,
    afterSload_error]

end Blanc.Composition.UniswapV2PairWeth9Joint
