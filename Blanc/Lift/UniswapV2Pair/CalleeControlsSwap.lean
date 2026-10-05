import Blanc.Lift.UniswapV2Pair.CalleeControls
import Blanc.Lift.UniswapV2Pair.SwapTransfer
import Blanc.Lift.UniswapV2Pair.SwapCallback
import Blanc.Lift.UniswapV2Pair.SwapFrontCanonical

/-!
# U6 callee-premise controls for `swap`: a failing transfer token or callback recipient

`swap`'s token calls and its callback are `CALL`s, so its callee premise is a `SendOk`-shaped
success premise. These controls show it is needed, at pc-zero EVM altitude and universally over
raw runs: if the called account holds `revertingCode` (`PUSH0 PUSH0 REVERT`) and is not a
precompile, there is NO successful raw `swap` run, whatever the gas or remaining state.

* the optimistic `token0` transfer (`amount0Out ≠ 0`), whose helper requires the `CALL`'s
  success flag (`safeTransfer_dynamicCall_post_inv` retains it as the stack word `1`);
* the optimistic `token1` transfer (`amount1Out ≠ 0`), after the optional `token0` transfer has
  moved the free pointer (this needs the CALL reply bound `short`, as the swap front does);
* the `uniswapV2Call` callback (`data` non-empty) to the recipient, whose flag the body tests
  (`SwapCallbackCall` retains `flag ≠ 0`).

`call_flag_zero_of_reverting` refutes each flag; `revertingCode_kept` carries the installed code
across the earlier calls. These are controls, not an instantiation of a liveness theorem.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- One literal transfer site whose callee (the masked `token`) holds reverting code: the
helper's `CALL` cannot leave the success flag the helper requires. -/
private theorem transferSite_false {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {L : List B256} {M : Mem} {G : Nat} {w p amount toWord token rho : B256} {n : Nat}
    {k : SFunc} {seg : Seg} {tok : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (callee : (token &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (w :: amount :: toWord :: token :: rho :: L) M G) (.callNext 57 k) seg) : False := by
  cases run with
  | callHalt d lookup pop body =>
    change some t_1fdb_c57 = _ at lookup
    cases lookup
    exact body.not_halted_entry (S := [16,17,57,71])
      (by decide) (by decide : 57 ∈ [16,17,57,71]) (by rfl : cert.prog[57]? = some t_1fdb_c57) rfl
  | callRet d lookup pop body _ =>
    change some t_1fdb_c57 = _ at lookup
    cases lookup
    obtain ⟨_, _, d', step, _, stack, _⟩ :=
      safeTransfer_dynamicCall_post_inv StepIn.toRun fork mem lower width
        (by decide : 71 ∉ []) (by decide : 16 ∉ []) (by decide : 17 ∉ [])
        (SFunc.runP_iff_runCutP_nil.mp ((St.of_pop1 pop).2 ▸ body))
    subst callee
    exact absurd (call_flag_zero_of_reverting tokenCode notPrecompile fork (StepIn.toRun step)
      stack) (by decide)

/-- The second transfer branch `t_08d0_c4` with a nonzero `amount1Out` and a reverting masked
`token1`: no run continues. -/
private theorem secondTransfer_false {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G n : Nat} {p t1 t0 r1 r0 len start toWord a1 a0 ρ : B256} {seg : Seg} {tok : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (upper : p.toNat < 2 ^ 161) (amount1 : a1 ≠ 0)
    (callee : (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G)
      t_08d0_c4 seg) : False := by
  unfold t_08d0_c4 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, run⟩ | ⟨skip, _, _⟩
  · unfold t_08d7_c4 at run
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    exact transferSite_false fork mem lower (by omega) callee tokenCode notPrecompile run
  · exact amount1 (eq_zero_of_iszero_ne_zero skip)

/-- A masked slot word names the slot's address. -/
private theorem masked_slot (x : B256) :
    ((0xffffffffffffffffffffffffffffffffffffffff &&& x) &&&
      0xffffffffffffffffffffffffffffffffffffffff).toAdr = x.toAdr := by
  have maskWord : ∀ y : B256, 0xffffffffffffffffffffffffffffffffffffffff &&& y = y.toAdr.toB256 :=
    ff20_and_word
  rw [B256.and_comm, maskWord, toAdr_toB256, maskWord, toAdr_toB256]

/-- The cached token slots and the installed code at the transfer branch are the entry's. -/
private theorem prefix_slot (sevm : Sevm) (b : Devm) {k : B256} (k12 : k ≠ 12) :
    (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget k =
      b.getStorVal sevm.currentTarget k := by
  change ((afterSload sevm (mintLockedWorld sevm b) 8).getStor sevm.currentTarget).get k =
    (b.getStor sevm.currentTarget).get k
  rw [afterSload_getStor]
  unfold mintLockedWorld
  rw [afterSstore_getStor_self, afterSload_getStor, Stor.get_set_ne _ (Ne.symm k12)]

private theorem prefix_code (sevm : Sevm) (b : Devm) (t : Adr) :
    (afterSload sevm (afterSload sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6) 7).getCode t =
      b.getCode t := by
  unfold mintLockedWorld
  rw [afterSload_getCode, afterSload_getCode, afterSload_getCode, afterSstore_getCode,
    afterSload_getCode]

/-- An optional transfer keeps `revertingCode` installed. -/
private theorem transferOpt_kept {D : Exec.Deriv} {sevm : Sevm} {b b' : Devm} {L : List B256}
    {M M' : Mem} {p p' amount toWord token rho : B256} {t : Adr}
    (opt : SwapTransferOpt D sevm b L M p amount toWord token rho b' M' p')
    (codeEq : b.getCode t = revertingCode) : b'.getCode t = revertingCode := by
  rcases opt with ⟨_, rfl, _, _⟩ | ⟨_, ⟨⟨_, _, step⟩, _⟩, _, _⟩
  · exact codeEq
  · exact revertingCode_kept (StepIn.toRun step) (by unfold St; rw [Devm.getCode_setMach]; exact codeEq)

/-- **U6 control (swap, token0 transfer).** With `amount0Out ≠ 0` and a reverting,
non-precompile `token0`, no raw pc-zero `swap` run succeeds: the optimistic `token0` transfer's
`CALL` cannot succeed. No reply-bound premise is needed: the transfer runs at the PC0 pointer. -/
theorem swap_no_success_of_reverting_token0 {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (amount0 : swapAmount0Out sevm ≠ 0)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) : False := by
  obtain ⟨f, entry, derived⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, _, _, _, _, body, _⟩ := swapPc0_inv selector derived
  obtain ⟨_, _, _, _, run0⟩ := swapLockOutput_inv fork (SFunc.runP_iff_runCutP_nil.mp body)
  obtain ⟨_, _, _, _, _, run⟩ := swapGuards_inv fork run0
  unfold t_08bf_c4 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, run⟩ | ⟨skip, _, _⟩
  · unfold t_08c6_c4 at run
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    exact transferSite_false fork getterInitMemory_ptr (by decide) (by decide)
      (by rw [masked_slot, prefix_slot sevm b (by decide)]; exact token0)
      (by rw [prefix_code]; exact tokenCode) notPrecompile run
  · exact amount0 (eq_zero_of_iszero_ne_zero skip)

/-- **U6 control (swap, token1 transfer).** With `amount1Out ≠ 0` and a reverting,
non-precompile `token1`, no raw pc-zero `swap` run succeeds: the code survives the optional
`token0` transfer, and the optimistic `token1` transfer's `CALL` cannot succeed. The moved
pointer is placed by the transfer's own actual 68-byte CALL reply bound
(`swapTransferCall_replyShort`). -/
theorem swap_no_success_of_reverting_token1 {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (amount1 : swapAmount1Out sevm ≠ 0)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) : False := by
  obtain ⟨f, entry, derived⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, _, _, _, _, body, _⟩ := swapPc0_inv selector derived
  obtain ⟨_, _, _, _, run0⟩ := swapLockOutput_inv fork (SFunc.runP_iff_runCutP_nil.mp body)
  obtain ⟨_, _, _, _, _, run⟩ := swapGuards_inv fork run0
  have callee := (masked_slot _).trans
    ((congrArg B256.toAdr (prefix_slot sevm b (by decide : (7 : B256) ≠ 12))).trans token1)
  have code0 := (prefix_code sevm b tok).trans tokenCode
  unfold t_08bf_c4 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, run⟩ | ⟨_, _, run⟩
  · unfold t_08c6_c4 at run
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    simp only [show Bytes.toB256 [0x08, 0xd0] = (0x8d0 : B256) from rfl] at run
    obtain ⟨d, _, call, ⟨_, ptr⟩, cont⟩ :=
      swapTransferSite_inv fork getterInitMemory_ptr (by decide) (by decide) run
    obtain ⟨_, _, step⟩ := call.1
    have sh := swapTransferCall_replyShort fork call
    have layout := swapMovedPointer_layout sh
      (by decide : (128 : B256).toNat + 2 ^ 161 < 2 ^ 256)
    have n128 : (128 : B256).toNat = 128 := rfl
    exact secondTransfer_false fork ptr (by omega) (by omega) amount1 callee
      (revertingCode_kept (StepIn.toRun step)
        (by unfold St; rw [Devm.getCode_setMach]; exact code0))
      notPrecompile cont
  · exact secondTransfer_false fork getterInitMemory_ptr (by decide) (by decide) amount1 callee
      code0 notPrecompile run

/-- **U6 control (swap, callback).** With non-empty `data` and a reverting, non-precompile
recipient `to`, no raw pc-zero `swap` run succeeds: the code survives both optional transfers,
and the `uniswapV2Call` `CALL` cannot leave the nonzero flag the body requires. Both
transfers' reply bounds are derived from their own actual 68-byte CALLs
(`swapTransferCall_replyShort`). -/
theorem swap_no_success_of_reverting_callback {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (data : swapDataLength sevm ≠ 0)
    (recipientCode : b.getCode (swapRecipient sevm) = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp (swapRecipient sevm))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) : False := by
  obtain ⟨f, entry, derived⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, _, guards, _, _, body, _⟩ := swapPc0_inv selector derived
  obtain ⟨_, _, _, _, run0⟩ := swapLockOutput_inv fork (SFunc.runP_iff_runCutP_nil.mp body)
  obtain ⟨_, _, _, _, _, run1⟩ := swapGuards_inv fork run0
  obtain ⟨_, _, _, b2, _, _, _, _, opt0, opt1, ptr2, lower2, upper2, run2⟩ :=
    swapTransfers_inv fork getterInitMemory_ptr run1
  obtain ⟨_, _, _, _, optC, _, _⟩ := swapCallback_inv fork ptr2 lower2 upper2 guards.length run2
  rcases optC with ⟨zero, _, _⟩ | ⟨_, call, _⟩
  · exact data zero
  obtain ⟨_, ⟨_, _, step⟩, _, flag, nonzero, settled⟩ := call
  have code2 : b2.getCode (swapRecipient sevm) = revertingCode :=
    transferOpt_kept opt1 (transferOpt_kept opt0 ((prefix_code sevm b _).trans recipientCode))
  have maskWord : ∀ y : B256, 0xffffffffffffffffffffffffffffffffffffffff &&& y = y.toAdr.toB256 :=
    ff20_and_word
  have target : ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
      swapRecipientWord sevm).toAdr = swapRecipient sevm := by
    rw [swapRecipientWord_eq, maskWord, toAdr_toB256, toAdr_toB256]
  exact nonzero (call_flag_zero_of_reverting (by rw [warm_getCode, target]; exact code2)
    (by rw [target]; exact notPrecompile) fork (StepIn.toRun step) settled.stack)

end Blanc.Lift.UniswapV2Pair
