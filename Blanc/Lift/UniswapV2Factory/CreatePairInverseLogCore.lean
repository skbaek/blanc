import Blanc.Lift.UniswapV2Factory.CreatePairInversePrefix
import Blanc.Lift.UniswapV2Factory.CreatePairInverseLogImage
import Blanc.Lift.StepMemory
import Blanc.Lift.HistWindow
import Blanc.Lift.HistCursorCalls
import Blanc.Lift.HistStaticCall
import Blanc.Lift.CommittedLogs

/-! The same actual CREATE2 result remains symbolic through the factory log. -/
namespace Blanc.Lift.UniswapV2Factory.CreatePairInverse

open Jaune Blanc Blanc.Lift

/-- The original CREATE2 return leaves a canonical address word, possibly zero,
and the original parent memory. This does not infer successful creation. -/
theorem create2_symbolic_return {root : Exec.Deriv}
    (step : CallOccurrenceStep root .create2)
    (hsg : step.occurrence.node.sevm.benvStat.rules.stateGas = none)
    (enabled : step.occurrence.node.sevm.benvStat.rules.op.create2 = true)
    (before : step.occurrence.node.devm.stack = [0, 0xa0, 0x2d74, fk3, fk3, 0x80,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396])
    (memory : step.occurrence.node.devm.memory = fm12) :
    ∃ w : B256,
      (w = 0 ∨ ∃ a : Adr, w = a.toB256) ∧
      (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& w = w ∧
      step.returned.devm = St step.returned.devm
       [w, fk3, 0x80,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]
       fm12 step.returned.devm.gasLeft := by
  have run : Ninst.Run step.occurrence.node.sevm step.occurrence.node.devm
      (.exec .create2) step.returned.devm := by
    refine ⟨step.occurrence.slot, step.occurrence.filled, step.occurrence.node.pc, ?_⟩
    rw [← step.instruction, ← step.result]
    exact step.occurrence.stepRun
  obtain ⟨v, i, size, salt, w, rest, stack, after, result⟩ :=
    create2_run_resultH hsg enabled run
  rw [before] at stack
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := List.cons.inj stack
  have mem := run_create2_memory_noStateGas hsg before run
  rw [memory, Mem.extends_covered (by rw [fm12_size]; decide)] at mem
  have canonical : w = 0 ∨ ∃ a : Adr, w = a.toB256 := by
    rcases result with zero | ⟨a, eq, _⟩
    · exact Or.inl zero
    · exact Or.inr ⟨a, eq⟩
  refine ⟨w, canonical, ?_, St.self after mem⟩
  rcases canonical with rfl | ⟨a, rfl⟩
  · rfl
  · exact ff20_and_adr a

private def windowLine : List Ninst :=
  [(.push [0x40] (by decide)),
   (.reg (.dup 0)),
   (.reg .mload),
   (.push [0x48, 0x5c, 0xc9, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)),
   (.reg (.dup 1)),
   (.reg .mstore),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg (.dup 7)),
   (.reg (.dup 1)),
   (.reg .and),
   (.push [0x04] (by decide)),
   (.reg (.dup 3)),
   (.reg .add),
   (.reg .mstore),
   (.reg (.dup 6)),
   (.reg (.dup 1)),
   (.reg .and),
   (.push [0x24] (by decide)),
   (.reg (.dup 3)),
   (.reg .add),
   (.reg .mstore),
   (.reg (.swap 1)),
   (.reg .mload),
   (.reg (.swap 2)),
   (.reg (.swap 7)),
   (.reg .pop),
   (.reg (.swap 0)),
   (.reg (.dup 7)),
   (.reg .and),
   (.reg (.swap 1)),
   (.push [0x48, 0x5c, 0xc9, 0x55] (by decide)),
   (.reg (.swap 1)),
   (.push [0x44] (by decide)),
   (.reg (.dup 0)),
   (.reg (.dup 2)),
   (.reg .add),
   (.reg (.swap 2)),
   (.push [0x00] (by decide)),
   (.reg (.swap 2)),
   (.reg (.swap 0)),
   (.reg (.swap 1)),
   (.reg (.swap 0)),
   (.reg (.dup 2)),
   (.reg (.swap 0)),
   (.reg .sub),
   (.reg .add),
   (.reg (.dup 1)),
   (.reg (.dup 3)),
   (.reg (.dup 7)),
   (.reg (.dup 0)),
   (.reg .extcodesize),
   (.reg .iszero),
   (.reg (.dup 0)),
   (.reg .iszero),
   (.push [0x06, 0x5e] (by decide))]

/-- The actual symbolic result traverses initialize's request preparation.
The EXTCODESIZE guard derives code size only; zero remains an allowed result. -/
theorem symbolic_window {start : Exec.Deriv} {b post : Devm} {w : B256}
    (cut : CursorStateAt code cert start (SFunc.lineDrop 81 t_0531_c10) b
      [w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]
      fm12 [t_0095_c13])
    (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (masked : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& w = w) :
    Nonempty (CursorStateAt code cert start (SFunc.lineDrop 2 t_065e_c10)
      (accountAccessH start.sevm b w.toAdr) [w, 0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 [t_0095_c13]) := by
  have maskedRight : w &&& (0xffffffffffffffffffffffffffffffffffffffff : B256) = w := by
    rw [B256.and_comm]
    exact masked
  let sizeWord : B256 := (b.getCode w.toAdr).size.toB256
  obtain ⟨guard⟩ := cut.lineH cert_check success hsg windowLine rfl
    (by intro ni member xi eq; subst ni; simp only [windowLine, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := accountAccessH start.sevm b w.toAdr)
    (S' := [0x65e, B256.eqCheck (B256.eqCheck (sizeWord) 0) 0, B256.eqCheck (sizeWord) 0, w, 0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (M' := fm15) (by
      intro G d run
      unfold windowLine at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x40, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b ((fm12.read 64 32).1.toB256 :: [0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm12.read 64 32).2 _) _ d at run
      rw [fm12_mload_40, read_covered fm12_size (by decide) (by decide)] at run
      change Line.Run start.sevm (St b [0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x485cc95500000000000000000000000000000000000000000000000000000000, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x485cc95500000000000000000000000000000000000000000000000000000000, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm12 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm13 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm13 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm13 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm13 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm13 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x4, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm13 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x4, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm13 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e6c, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm13 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm14 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm14 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm14 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm14 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x24, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm14 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x24, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm14 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e8c, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm14 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x40, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x40, 0x2e68, 0xffffffffffffffffffffffffffffffffffffffff, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b ((fm15.read 64 32).1.toB256 :: [0x2e68, 0xffffffffffffffffffffffffffffffffffffffff, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm15.read 64 32).2 _) _ d at run
      rw [fm15_mload_40, read_covered fm15_size (by decide) (by decide)] at run
      change Line.Run start.sevm (St b [0x2e68, 0x2e68, 0xffffffffffffffffffffffffffffffffffffffff, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [w, 0x2e68, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x0, 0x2e68, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x2e68, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [w, 0xffffffffffffffffffffffffffffffffffffffff, 0x2e68, 0x2e68, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      rw [maskedRight] at run
      change Line.Run start.sevm (St b [w, 0x2e68, 0x2e68, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x2e68, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x485cc955, 0x2e68, 0x2e68, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x2e68, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x44, 0x2e68, 0x2e68, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x44, 0x44, 0x2e68, 0x2e68, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x44, 0x44, 0x2e68, 0x2e68, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2eac, 0x44, 0x2e68, 0x2e68, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x44, 0x2e68, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x0, 0x2e68, 0x44, 0x2e68, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x2e68, 0x44, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x2e68, 0x44, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x44, 0x2e68, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x0, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [w, 0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St b [w, w, 0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_extcodesizeH bal step
      change Line.Run start.sevm (St (accountAccessH start.sevm b w.toAdr) [sizeWord, w, 0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St (accountAccessH start.sevm b w.toAdr) [B256.eqCheck (sizeWord) 0, w, 0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St (accountAccessH start.sevm b w.toAdr) [B256.eqCheck (sizeWord) 0, B256.eqCheck (sizeWord) 0, w, 0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St (accountAccessH start.sevm b w.toAdr) [B256.eqCheck (B256.eqCheck (sizeWord) 0) 0, B256.eqCheck (sizeWord) 0, w, 0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      obtain ⟨_, step, run⟩ := Line.of_run_cons run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      change Line.Run start.sevm (St (accountAccessH start.sevm b w.toAdr) [0x65e, B256.eqCheck (B256.eqCheck (sizeWord) 0) 0, B256.eqCheck (sizeWord) 0, w, 0x0, 0x2e68, 0x44, 0x2e68, 0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
      cases run
      exact ⟨_, rfl⟩)
  have zeroFlag : B256.eqCheck sizeWord 0 = 0 := by
    obtain ⟨G, state⟩ := guard.state
    obtain ⟨outcome, source⟩ := guard.placed.sourceRunH cert_check
      (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact hsg)
    rw [guard.tree, state, guard.sevm_eq] at source
    have run := SFunc.runP_iff_runCutP_nil.mp source
    rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, _, _⟩
    · exact (failed.false_of_noOk (by decide +kernel)).elim
    · exact eq_zero_of_iszero_ne_zero accepted
  rw [zeroFlag, show B256.eqCheck (0 : B256) 0 = 1 from rfl] at guard
  obtain ⟨cut⟩ := guard.branchSuccH cert_check success hsg (by decide : (1 : B256) ≠ 0)
  obtain ⟨cut⟩ := cut.destH cert_check success hsg
  apply cut.lineH cert_check success hsg [.reg .pop] rfl
  · intro ni member xi eq
    subst ni
    simp only [List.mem_singleton, reduceCtorEq] at member
  · intro G d run
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_pop step
    cases run
    exact ⟨_, rfl⟩

/-- The caller's zero output window preserves its actual request memory for
any child outcome and arbitrary child logs/state. -/
theorem initialize_return_state {root : Exec.Deriv}
    (step : CallOccurrenceStep root .call) {gas : B256} {w : B256}
    (hsg : step.occurrence.node.sevm.benvStat.rules.stateGas = none)
    (before : step.occurrence.node.devm.stack = [gas,w,0,0x2e68,0x44,0x2e68,0,
      0x2eac,0x485cc955,w,fk3,0x80,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,w,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396])
    (memory : step.occurrence.node.devm.memory = fm15) :
    ∃ flag : B256, step.returned.devm = St step.returned.devm
      [flag,0x2eac,0x485cc955,w,fk3,0x80,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,w,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396]
      fm15 step.returned.devm.gasLeft := by
  have run : Ninst.Run step.occurrence.node.sevm step.occurrence.node.devm
      (.exec .call) step.returned.devm := by
    refine ⟨step.occurrence.slot, step.occurrence.filled, step.occurrence.node.pc, ?_⟩
    rw [← step.instruction, ← step.result]
    exact step.occurrence.stepRun
  obtain ⟨⟨flag, stack⟩, ys, length, mem⟩ := CallEffects.call_run_effects hsg before run
  have empty : ys = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero length)
  rw [memory, empty, Mem.extends_covered (by rw [fm15_size]; decide)] at mem
  simp only [Mem.write] at mem
  exact ⟨flag, St.self stack mem⟩

private def initializeGuard : List Ninst :=
  [.reg .iszero, .reg (.dup 0), .reg .iszero, .push [0x06,0x72] (by decide)]

/-- The same successful suffix derives a nonzero actual CALL flag and takes
its checked success branch. No restriction on the child log list is used. -/
theorem initialize_success_branch {start : Exec.Deriv} {b post : Devm} {flag w : B256}
    (cut : CursorStateAt code cert start (SFunc.lineDrop 4 t_065e_c10) b
      [flag,0x2eac,0x485cc955,w,fk3,0x80,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,w,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396]
      fm15 [t_0095_c13])
    (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none) :
    flag ≠ 0 ∧ Nonempty (CursorStateAt code cert start t_0672_c10 b
      [0,0x2eac,0x485cc955,w,fk3,0x80,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,w,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396]
      fm15 [t_0095_c13]) := by
  have zeroFlag : B256.eqCheck flag 0 = 0 := by
    obtain ⟨G, state⟩ := cut.state
    obtain ⟨outcome, source⟩ := cut.placed.sourceRunH cert_check
      (cut.exn_eq.trans success) (by rw [cut.sevm_eq]; exact hsg)
    rw [cut.tree, state, cut.sevm_eq] at source
    have run := SFunc.runP_iff_runCutP_nil.mp source
    change SFunc.RunCutP _ _ _ _ _ (initializeGuard.foldr SFunc.next
      (.branch t_0669_c10 t_0672_c10)) _ at run
    dsimp only [initializeGuard, List.foldr] at run
    iterate 4
      obtain ⟨_, step, run⟩ := ric_nextP run
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step.toRun rfl
    rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, _, _⟩
    · exact (failed.false_of_noOk (by decide +kernel)).elim
    · exact eq_zero_of_iszero_ne_zero accepted
  have nonzero : flag ≠ 0 := by
    intro zero
    rw [zero] at zeroFlag
    exact (by decide : B256.eqCheck (0 : B256) 0 ≠ 0) zeroFlag
  refine ⟨nonzero, ?_⟩
  obtain ⟨guard⟩ := cut.lineH cert_check success hsg initializeGuard rfl
    (by intro ni member xi eq; subst ni; simp only [initializeGuard, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (M' := fm15)
    (S' := [0x672,1,0,0x2eac,0x485cc955,w,fk3,0x80,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,w,
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2,0x95,0xc9c65396]) (by
      intro G d run
      unfold initializeGuard at run
      iterate 4
        obtain ⟨_, step, run⟩ := Line.of_run_cons run
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      cases run
      exact ⟨_, by rw [zeroFlag]; rfl⟩)
  exact guard.branchSuccH cert_check success hsg (by decide : (1 : B256) ≠ 0)


/-- Final factory log memory with the still symbolic CREATE2 word. -/
def symbolicWordMemory (w : B256) : Mem := fm23.write 11880 w.toBytes

def symbolicLogMemory (w count : B256) : Mem := (symbolicWordMemory w).write 11912 count.toBytes

private theorem symbolicWordMemory_size (w : B256) : (symbolicWordMemory w).size = 11968 := by
  rw [symbolicWordMemory, Mem.size_write_of_size fm23_size (by decide) (B256.length_toBytes _)]; decide

private theorem symbolicLogMemory_size (w count : B256) : (symbolicLogMemory w count).size = 11968 := by
  rw [symbolicLogMemory, Mem.size_write_of_size (symbolicWordMemory_size w)
    (by decide) (B256.length_toBytes _)]; decide

private theorem symbolicLogMemory_mload40 (w count : B256) :
    ((symbolicLogMemory w count).read 64 32).1.toB256 = 0x2e68 := by
  have reads1 := Mem.Reads.write fm23_wf fm23_reads 11880 w.toBytes
  have reads2 := Mem.Reads.write (fm23_wf.write 11880 w.toBytes) reads1 11912 count.toBytes
  rw [show symbolicLogMemory w count = (fm23.write 11880 w.toBytes).write 11912 count.toBytes from rfl,
    Mem.Reads.read reads2,
    Bytes.sliceD_writeAt_before _ _ 64 32 11912 (by decide),
    Bytes.sliceD_writeAt_before _ _ 64 32 11880 (by decide),
    ← Mem.Reads.read fm23_reads]
  exact fm23_mload_40

theorem symbolicLogMemory_payload (w count : B256) :
    ((symbolicLogMemory w count).read 11880 64).1 = w.toBytes ++ count.toBytes :=
  Mem.read_two_word_writes_at_raw fm23 11880 w count

def suffixLine : List Ninst :=
  [(.reg .pop),
   (.reg .pop),
   (.reg .pop),
   (.reg .pop),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
   (.reg (.dup 4)),
   (.reg (.dup 1)),
   (.reg .and),
   (.push [0x00] (by decide)),
   (.reg (.dup 1)),
   (.reg (.dup 1)),
   (.reg .mstore),
   (.push [0x02] (by decide)),
   (.push [0x20] (by decide)),
   (.reg (.dup 1)),
   (.reg (.dup 1)),
   (.reg .mstore),
   (.push [0x40] (by decide)),
   (.reg (.dup 0)),
   (.reg (.dup 4)),
   (.reg .keccak256),
   (.reg (.dup 9)),
   (.reg (.dup 7)),
   (.reg .and),
   (.reg (.dup 0)),
   (.reg (.dup 6)),
   (.reg .mstore),
   (.reg (.swap 0)),
   (.reg (.dup 3)),
   (.reg .mstore),
   (.reg (.dup 1)),
   (.reg (.dup 5)),
   (.reg .keccak256),
   (.reg (.dup 0)),
   (.reg .sload),
   (.reg (.swap 7)),
   (.reg (.dup 13)),
   (.reg .and),
   (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)),
   (.reg (.swap 8)),
   (.reg (.dup 9)),
   (.reg .and),
   (.reg (.dup 1)),
   (.reg .or),
   (.reg (.swap 0)),
   (.reg (.swap 1)),
   (.reg .sstore),
   (.reg (.swap 3)),
   (.reg (.dup 3)),
   (.reg .mstore),
   (.reg (.dup 1)),
   (.reg (.dup 5)),
   (.reg .keccak256),
   (.reg (.dup 6)),
   (.reg (.dup 6)),
   (.reg .mstore),
   (.reg (.dup 3)),
   (.reg .mstore),
   (.reg (.dup 1)),
   (.reg (.dup 5)),
   (.reg .keccak256),
   (.reg (.dup 0)),
   (.reg .sload),
   (.reg (.dup 8)),
   (.reg .and),
   (.reg (.dup 5)),
   (.reg .or),
   (.reg (.swap 0)),
   (.reg .sstore),
   (.push [0x03] (by decide)),
   (.reg (.dup 0)),
   (.reg .sload),
   (.push [0x01] (by decide)),
   (.reg (.dup 1)),
   (.reg .add),
   (.reg (.dup 2)),
   (.reg .sstore),
   (.reg (.swap 5)),
   (.reg (.dup 1)),
   (.reg (.swap 0)),
   (.reg .mstore),
   (.push [0xc2, 0x57, 0x5a, 0x0e, 0x9e, 0x59, 0x3c, 0x00, 0xf9, 0x59, 0xf8, 0xc9, 0x2f, 0x12, 0xdb, 0x28, 0x69, 0xc3, 0x39, 0x5a, 0x3b, 0x05, 0x02, 0xd0, 0x5e, 0x25, 0x16, 0x44, 0x6f, 0x71, 0xf8, 0x5b] (by decide)),
   (.reg (.swap 0)),
   (.reg (.swap 5)),
   (.reg .add),
   (.reg (.dup 0)),
   (.reg .sload),
   (.reg (.swap 0)),
   (.reg (.swap 7)),
   (.reg .and),
   (.reg (.dup 4)),
   (.reg .or),
   (.reg (.swap 0)),
   (.reg (.swap 6)),
   (.reg .sstore),
   (.reg (.swap 2)),
   (.reg .sload),
   (.reg (.dup 3)),
   (.reg .mload),
   (.reg (.swap 2)),
   (.reg (.dup 3)),
   (.reg .mstore),
   (.reg (.swap 0)),
   (.reg (.dup 2)),
   (.reg .add),
   (.reg .mstore),
   (.reg (.dup 1)),
   (.reg .mload),
   (.push [0x0d, 0x36, 0x48, 0xbd, 0x0f, 0x6b, 0xa8, 0x01, 0x34, 0xa3, 0x3b, 0xa9, 0x27, 0x5a, 0xc5, 0x85, 0xd9, 0xd3, 0x15, 0xf0, 0xad, 0x83, 0x55, 0xcd, 0xde, 0xfd, 0xe3, 0x1a, 0xfa, 0x28, 0xd0, 0xe9] (by decide)),
   (.reg (.swap 2)),
   (.reg (.swap 1)),
   (.reg (.dup 1)),
   (.reg (.swap 0)),
   (.reg .sub),
   (.reg (.swap 0)),
   (.reg (.swap 1)),
   (.reg .add),
   (.reg (.swap 0))]

theorem suffixLine_inverse {sevm : Sevm} {b d : Devm} {w : B256} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none)
    (masked : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& w = w)
    (run : Line.Run sevm (St b [0x0, 0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 G) suffixLine d) :
    ∃ b' count G', d = St b' [0x2e68, 0x40, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w count) G' := by
  have maskedRight : w &&& (0xffffffffffffffffffffffffffffffffffffffff : B256) = w := by
    rw [B256.and_comm]
    exact masked
  unfold suffixLine at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x2eac, 0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x485cc955, w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [w, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm15 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm16 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm16 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm16 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x2, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm16 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x20, 0x2, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm16 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x40, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x0, 0x40, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b ((fm17.read 0 64).1.keccak :: [0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm17.read 0 64).2 _) _ d at run
  rw [fm17_keccak_0, read_covered_len fm17_size (by decide) (by decide)] at run
  change Line.Run sevm (St b [fk1, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk1, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xffffffffffffffffffffffffffffffffffffffff, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk1, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk1, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk1, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x0, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk1, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm17 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk1, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm18 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [fk1, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm18 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x20, fk1, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm18 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [0x0, 0x40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b ((fm19.read 0 64).1.keccak :: [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm19.read 0 64).2 _) _ d at run
  rw [fm19_keccak_0, read_covered_len fm19_size (by decide) (by decide)] at run
  change Line.Run sevm (St b [fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St b [fk2, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sloadH bal step
  let load1 : B256 := b.getStorVal sevm.currentTarget fk2
  let world1 : Devm := afterSloadH sevm b fk2
  change Line.Run sevm (St world1 [load1, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffffffffffffffffffff, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [0xffffffffffffffffffffffffffffffffffffffff, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, load1, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [w, 0xffffffffffffffffffffffffffffffffffffffff, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, load1, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  rw [maskedRight] at run
  change Line.Run sevm (St world1 [w, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, load1, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [0xffffffffffffffffffffffff0000000000000000000000000000000000000000, w, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, load1, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [load1, w, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [0xffffffffffffffffffffffff0000000000000000000000000000000000000000, load1, w, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [(0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load1), w, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [w, (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load1), w, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [(w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load1)), w, fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [w, (w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load1)), fk2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world1 [fk2, (w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load1)), w, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sstoreH hsg bal step
  let world2 : Devm := afterSstoreH sevm world1 fk2 (w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load1))
  change Line.Run sevm (St world2 [w, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, 0x2, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0x2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0x20, 0x2, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm19 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm20 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0x40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm20 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0x0, 0x40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm20 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 ((fm20.read 0 64).1.keccak :: [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm20.read 0 64).2 _) _ d at run
  rw [fm20_keccak_0, read_covered_len fm20_size (by decide) (by decide)] at run
  change Line.Run sevm (St world2 [fk4, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm20 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, fk4, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm20 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, fk4, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm20 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [fk4, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm21 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0x20, fk4, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm21 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0x40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [0x0, 0x40, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 ((fm22.read 0 64).1.keccak :: [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm22.read 0 64).2 _) _ d at run
  rw [fm22_keccak_0, read_covered_len fm22_size (by decide) (by decide)] at run
  change Line.Run sevm (St world2 [fk5, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world2 [fk5, fk5, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sloadH bal step
  let load2 : B256 := world2.getStorVal sevm.currentTarget fk5
  let world3 : Devm := afterSloadH sevm world2 fk5
  change Line.Run sevm (St world3 [load2, fk5, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world3 [0xffffffffffffffffffffffff0000000000000000000000000000000000000000, load2, fk5, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world3 [(0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load2), fk5, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world3 [w, (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load2), fk5, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world3 [(w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load2)), fk5, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world3 [fk5, (w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load2)), 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sstoreH hsg bal step
  let world4 : Devm := afterSstoreH sevm world3 fk5 (w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load2))
  change Line.Run sevm (St world4 [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world4 [0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world4 [0x3, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sloadH bal step
  let load3 : B256 := world4.getStorVal sevm.currentTarget 0x3
  let world5 : Devm := afterSloadH sevm world4 0x3
  change Line.Run sevm (St world5 [load3, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world5 [0x1, load3, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world5 [load3, 0x1, load3, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world5 [(load3 + 0x1), load3, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world5 [0x3, (load3 + 0x1), load3, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sstoreH hsg bal step
  let world6 : Devm := afterSstoreH sevm world5 0x3 (load3 + 0x1)
  change Line.Run sevm (St world6 [load3, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x0, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world6 [0x0, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, load3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world6 [0x3, 0x0, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, load3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world6 [0x0, 0x3, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, load3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm22 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world6 [0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, load3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world6 [0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b, 0x3, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, load3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world6 [0x3, 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, load3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world6 [load3, 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world6 [(load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world6 [(load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sloadH bal step
  let load4 : B256 := world6.getStorVal sevm.currentTarget (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b)
  let world7 : Devm := afterSloadH sevm world6 (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b)
  change Line.Run sevm (St world7 [load4, (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world7 [(load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), load4, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world7 [0xffffffffffffffffffffffff0000000000000000000000000000000000000000, load4, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world7 [(0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load4), 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world7 [w, (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load4), 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world7 [(w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load4)), 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world7 [0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, (w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load4)), 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world7 [(load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b), (w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load4)), 0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sstoreH hsg bal step
  let world8 : Devm := afterSstoreH sevm world7 (load3 + 0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b) (w ||| (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 &&& load4))
  change Line.Run sevm (St world8 [0x40, 0x20, w, 0x3, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world8 [0x3, 0x20, w, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sloadH bal step
  let load5 : B256 := world8.getStorVal sevm.currentTarget 0x3
  let world9 : Devm := afterSloadH sevm world8 0x3
  change Line.Run sevm (St world9 [load5, 0x20, w, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x40, load5, 0x20, w, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 ((fm23.read 64 32).1.toB256 :: [load5, 0x20, w, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) (fm23.read 64 32).2 _) _ d at run
  rw [fm23_mload_40, read_covered fm23_size (by decide) (by decide)] at run
  change Line.Run sevm (St world9 [0x2e68, load5, 0x20, w, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [w, load5, 0x20, 0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x2e68, w, load5, 0x20, 0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] fm23 _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [load5, 0x20, 0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicWordMemory w) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x20, load5, 0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicWordMemory w) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x2e68, 0x20, load5, 0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicWordMemory w) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x2e88, load5, 0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicWordMemory w) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x40, 0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 (((symbolicLogMemory w load5).read 64 32).1.toB256 :: [0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396]) ((symbolicLogMemory w load5).read 64 32).2 _) _ d at run
  rw [symbolicLogMemory_mload40, read_covered (symbolicLogMemory_size w load5) (by decide) (by decide)] at run
  change Line.Run sevm (St world9 [0x2e68, 0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0x2e68, 0x2e68, 0x40, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x40, 0x2e68, 0x2e68, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x2e68, 0x2e68, 0x40, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x2e68, 0x2e68, 0x2e68, 0x40, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x2e68, 0x2e68, 0x2e68, 0x40, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x0, 0x2e68, 0x40, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x2e68, 0x0, 0x40, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x40, 0x0, 0x2e68, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x40, 0x2e68, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
  change Line.Run sevm (St world9 [0x2e68, 0x40, 0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, fk3, 0x80, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, w, 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2, 0x95, 0xc9c65396] (symbolicLogMemory w load5) _) _ d at run
  cases run
  exact ⟨world9, load5, _, rfl⟩


end Blanc.Lift.UniswapV2Factory.CreatePairInverse
