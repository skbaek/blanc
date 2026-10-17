import Blanc.Composition.UniswapV2PairWeth9XLegCall
import Blanc.StaticStorage

/-!
# WETH9's footprint across a `STATICCALL` to another contract

The token1 rows of Burn and Skim query the other token `X` (and Burn the factory) by `STATICCALL`
before X's `transfer`.  The X-leg quiescence (`xleg_call`) needs WETH9's footprint invariant and the
ether-supply bound at the transfer's world, so they must cross those queries.  Storage is silent
across a `STATICCALL` (`Ninst.staticcall_getStor_eq`); WETH9's ether balance and the supply are
carried by WETH9's footprint specification over the child's run (`footSpec`, as in `xleg_call`),
under HASH-T over the keys the child's WETH9 frames touch (`StaticChildFresh`).  The universe stays
the given one: the child writes no storage, so the tracked ledger over the extended universe is the
one over the given universe.
-/

namespace Blanc.Composition.UniswapV2PairWeth9XLeg

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token Blanc.ExecutionTrace
  Blanc.Composition.Weth9Token Blanc.Composition.Weth9TokenFrames

/-- **HASH-T for the child a `STATICCALL` enters**: `P` holds of every derivation of the frame the
instruction spawns and enters. -/
def StaticChildFresh (sevm : Sevm) (devm : Devm) (P : Exec.Deriv → Prop) : Prop :=
  ∀ {frame : Frame} {rsm : Resume} {cevm : Evm} {raw : Execution},
    Xinst.step sevm devm .staticcall = .spawn frame rsm → frame.enter = .run cevm →
    ∀ child : Exec cevm.pc cevm.sta cevm.dyna raw, P ⟨cevm.pc, cevm.sta, cevm.dyna, raw, child⟩

/-- A spawning `STATICCALL` enters the account its second stack word names. -/
theorem staticcall_spawn_target {sevm : Sevm} {s : Devm} {f : Frame} {rsm : Resume}
    (fork : CoveredFork sevm.benvStat.fork) (hx : Xinst.step sevm s .staticcall = .spawn f rsm) :
    ∃ g c rest, s.stack = g :: c :: rest ∧ f.inner.currentTarget = c.toAdr := by
  simp only [Xinst.step, Bind.bind, Except.bind] at hx
  rw [fork.rules_stateGas_none] at hx
  rcases eq1 : Devm.pop s with _ | ⟨g, d1⟩ <;> simp only [eq1] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have e1 := (Devm.pop_of_pop eq1).stack
  rcases eq2 : Devm.popToAdr d1 with _ | ⟨t, d2⟩ <;> simp only [eq2] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨c, ht, p2⟩ := Devm.pop_of_popToAdr eq2
  have e2 := (Devm.pop_of_pop p2).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1 e2
  refine ⟨g, c, d2.stack, by rw [e1, e2], ?_⟩
  repeat' split at hx
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hx
  all_goals first
    | cases hx
    | rw [(genericCall_step_spawn_exact hx).1]; exact ht.symm

/-- **WETH9's footprint across a `STATICCALL` to another contract.**  From a frame other than WETH9,
a `STATICCALL` to an account other than WETH9, given as an arbitrary callee record: if WETH9's code,
its footprint over `U` and the ether-supply bound hold before, and HASH-T holds over the keys the
child's WETH9 frames touch, then they hold after, over the same `U`. -/
theorem static_foot {ca : Adr} {U : Key → Prop} {sevm : Sevm} {devm d : Devm}
    (run : Ninst.RunCompiled sevm devm (.exec .staticcall) d)
    (fork : CoveredFork sevm.benvStat.fork) (targetNe : sevm.currentTarget ≠ ca)
    (callee : ∀ g c rest, devm.stack = g :: c :: rest → c.toAdr ≠ ca)
    (wethCode : devm.getCode ca = Weth9.code)
    (foot : FootInv U (devm.state.getStor ca) (devm.state.bal ca))
    (bound : sum devm.state.bal < 2 ^ 256)
    (wethFresh : StaticChildFresh sevm devm fun D => KeysFresh U (wethRunKeys ca D)) :
    d.getCode ca = Weth9.code ∧ FootInv U (d.state.getStor ca) (d.state.bal ca) ∧
      sum d.state.bal < 2 ^ 256 := by
  have storEq : Devm.getStor devm ca = Devm.getStor d ca := by
    obtain ⟨xl, filled, steps⟩ := run
    exact congrFun (Ninst.staticcall_getStor_eq fork ⟨xl, filled, 0, steps 0⟩) ca
  -- the footprint over a universe `U'` extending `U` gives the backing at `d`
  suffices h : ∃ U' : Key → Prop, (∀ k, U k → U' k) ∧ KeyInj U' ∧ d.getCode ca = Weth9.code ∧
      trackedSum U' (d.state.getStor ca) ≤ (d.state.bal ca).toNat ∧
      trackedSum U' (d.state.getStor ca) = trackedSum U (d.state.getStor ca) ∧
      sum d.state.bal < 2 ^ 256 by
    obtain ⟨U', -, -, code, backed, same, side⟩ := h
    have storEq' : devm.state.getStor ca = d.state.getStor ca := storEq
    refine ⟨code, ⟨?_, foot.inj, foot.apart, ?_⟩, side⟩
    · rw [← storEq']
      exact foot.support
    · rw [← same]
      exact backed
  obtain ⟨xl, filled, steps⟩ := run
  have xrun : Xinst.Run sevm devm .staticcall xl (.ok d) := XStep.run_toStep.mp (steps 0)
  cases xl with
  | none =>
    have preD := ContractSpecSem.Ninst.none_preserves_precond (c := footSpec U) fork (steps 0)
      targetNe (foot_pre targetNe wethCode foot bound)
    have footD := footInv_of_pre targetNe foot.inj foot.apart preD
    exact ⟨U, fun _ h => h, foot.inj, code_eq_of_image preD.code, footD.backed, rfl, preD.side⟩
  | some slot =>
    obtain ⟨⟨cpc, csta, cdyna⟩, raw⟩ := slot
    obtain ⟨child⟩ := filled
    have hxrun := xrun
    cases spawnEq : Xinst.step sevm devm .staticcall with
    | done execution =>
      simp only [Xinst.Run, XStep.Run, spawnEq, ExceptT.stM_eq, reduceCtorEq, false_and] at hxrun
    | spawn frame resume =>
    simp only [Xinst.Run, spawnEq, XStep.Run] at hxrun
    obtain ⟨result, frameRun, resumeRun⟩ := hxrun
    cases result with
    | error error =>
      cases resume <;> simp only [ExceptT.stM_eq, Resume.run, liftToExecution, Except.bind_error,
        reduceCtorEq] at resumeRun
    | ok settled =>
    have enter := (RunFrame.some_inv frameRun).1
    obtain ⟨g, c, rest, hstack, cTarget⟩ := staticcall_spawn_target fork spawnEq
    have pc0 : cpc = 0 := Frame.enter_run_pc enter
    have cTarget' : csta.currentTarget = c.toAdr := by
      rw [Frame.enter_run_currentTarget enter]
      exact cTarget
    have cFork : CoveredFork csta.benvStat.fork := by
      rw [Frame.enter_run_benvStat enter, Xinst.step_spawn_benvStat spawnEq]
      exact fork
    subst pc0
    have childTargetNe : csta.currentTarget ≠ ca := by
      rw [cTarget']
      exact callee g c rest hstack
    have freshW := wethFresh spawnEq enter child
    have footW := foot.extend freshW
    have injW := footW.inj
    have preW := foot_pre targetNe wethCode footW bound
    obtain ⟨childPre, cont⟩ :=
      ContractSpecSem.Xinst.some_preserves_precond (c := footSpec (Key.extend U
        (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩))) fork xrun child targetNe preW
    have admittedW : Exec.FrameAdmitted ca (footEntry (Key.extend U
        (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩))) child := by
      intro root member target k hk
      exact Or.inr (List.mem_flatMap.mpr ⟨root, member, by rw [ite_eq_left target]; exact hk⟩)
    have preD : (footSpec (Key.extend U (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩))).Pre
        ca sevm d := by
      apply cont
      clear cont
      cases raw with
      | error e => trivial
      | ok post =>
        exact footSpec_preservesAdmitted ca injW csta cdyna post cFork child admittedW
          (fun t => (childTargetNe t).elim) (fun t => (childTargetNe t).elim) childPre
    have footD := footInv_of_pre targetNe injW footW.apart preD
    have same : trackedSum (Key.extend U (wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩))
        (d.state.getStor ca) = trackedSum U (d.state.getStor ca) := by
      have storEq' : devm.state.getStor ca = d.state.getStor ca := storEq
      rw [← storEq']
      unfold trackedSum
      congr 1
      funext a
      by_cases hK : U (.bal a)
      · rw [tracked_self hK, tracked_self (Or.inl hK)]
      · by_cases hks : Key.bal a ∈ wethRunKeys ca ⟨0, csta, cdyna, raw, child⟩
        · rw [tracked_self (Or.inr hks), tracked_of_not hK]
          exact foot.support.get_eq_zero (freshW.1 _ hks) hK
        · rw [tracked_of_not hK, tracked_of_not (fun hh => hh.elim hK hks)]
    exact ⟨_, fun _ h => Or.inl h, injW, code_eq_of_image preD.code, footD.backed, same, preD.side⟩

end Blanc.Composition.UniswapV2PairWeth9XLeg
