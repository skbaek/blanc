import Blanc.Lift.UniswapV2Pair.SyncWalk

/-! Actual Burn selector and public ABI caller retain the source derivation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Actual Burn selector dispatch retains the supplied derivation into050a. -/
theorem burnSelector_dispatch_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [] M G) t_001a_c0 (.done o)) :
    ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [0x89afcb44] M gas) t_050a_c83 (.done o) := by
  unfold t_001a_c0 at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_shr (StepIn.toRun hs)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0x89afcb44 : B256) from selector] at eq
  subst d
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a,0x62,0x78,0x42]) (0x89afcb44 : B256) = 0
    from by decide, ite_true] at run
  unfold t_002b_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0xba,0x9a,0x7a,0x56]) (0x89afcb44 : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_0097_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x7e,0xce,0xbe,0x00]) (0x89afcb44 : B256) = 0
    from by decide, ite_true] at run
  unfold t_00a3_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_eqP (fun h => StepIn.toRun h)
    (g := t_04d7_c82) (by intro bad; cases bad) rfl run
  simp only [show B256.eqCheck (Bytes.toB256 [0x7e,0xce,0xbe,0x00]) (0x89afcb44 : B256) = 0
    from by decide, ite_true] at run
  unfold t_00ae_c0 at run
  obtain ⟨gas, run⟩ := ric_cmp_eqP (fun h => StepIn.toRun h)
    (g := t_050a_c83) (by intro bad; cases bad) rfl run
  simp only [show B256.eqCheck (Bytes.toB256 [0x89,0xaf,0xcb,0x44]) (0x89afcb44 : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  exact ⟨gas, run⟩

/-- The public Burn ABI caller retains its actual callee and, on a normal
return, the original64-byte encoding continuation. All address masks are literal. -/
theorem burnAbi_caller_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (run : SFunc.RunCutP P cert.prog sevm []
      (St b [0x89afcb44] M G) t_050a_c83 (.done o)) :
    ∃ gas calleeOutcome,
      SFunc.RunP P cert.prog sevm
        (St b [(0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord sevm 4,
          0x053d, 0x89afcb44] M gas) t_13f5_c37 calleeOutcome ∧
      (match calleeOutcome with
       | .returned post => SFunc.RunCutP P cert.prog sevm [] post t_053d_c83 (.done o)
       | .halted post => o = .halted post) := by
  have h := run
  unfold t_050a_c83 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldatasize (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sub (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨_, _, h⟩
  · exact (failed.false_of_noOk (by decide : t_051c_c83.noOk = true)).elim
  unfold t_0520_c83 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldataload (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  cases h with
  | callRet d lookup pop callee continuation =>
    change some t_13f5_c37 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    simp only [show Bytes.toB256 [0x05, 0x3d] = (0x053d : B256) from rfl,
      show Bytes.toB256 [0x04] = (4 : B256) from rfl,
      show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] =
        (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl] at callee
    exact ⟨_, _, callee, continuation⟩
  | callHalt d lookup pop callee =>
    change some t_13f5_c37 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    simp only [show Bytes.toB256 [0x05, 0x3d] = (0x053d : B256) from rfl,
      show Bytes.toB256 [0x04] = (4 : B256) from rfl,
      show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] =
        (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl] at callee
    exact ⟨_, _, callee, rfl⟩

/-- Actual pc-zero guards and selector route retain the Burn callee from the
same D, with the public wrapper attached to every normal return. -/
theorem burnPc0_caller_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b [] Mem.empty G) t_0000_c0 o) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
    ∃ gas calleeOutcome,
      SFunc.RunP (StepIn D) cert.prog sevm
        (St b [(0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord sevm 4,
          0x053d, 0x89afcb44] getterInitMemory gas) t_13f5_c37 calleeOutcome ∧
      (match calleeOutcome with
       | .returned post => SFunc.RunCutP (StepIn D) cert.prog sevm [] post t_053d_c83 (.done o)
       | .halted post => o = .halted post) := by
  obtain ⟨value, size, _, routed⟩ := syncGuards_inv run
  obtain ⟨_, dispatched⟩ := burnSelector_dispatch_inv selector (SFunc.runP_iff_runCutP_nil.mp routed)
  obtain ⟨gas, outcome, callee, continuation⟩ := burnAbi_caller_inv (fun h => StepIn.toRun h) dispatched
  exact ⟨value, size, gas, outcome, callee, continuation⟩

/-- The real pc-zero memory initialization leaves Burn's helper sentinel zero. -/
theorem burnEntryMemory_sentinel : memWord getterInitMemory 96 = 0 := by
  simp only [getterInitMemory, memWord]
  rw [(Mem.Reads.write Mem.wf_empty Mem.reads_empty 64 (128 : B256).toBytes).read,
    Bytes.readWord_writeAt_of_disjoint [] 96 64 (128 : B256) (Or.inr (by decide : 64 + 32 ≤ 96))]
  rfl

end Blanc.Lift.UniswapV2Pair
