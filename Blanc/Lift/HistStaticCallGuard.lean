import Blanc.Lift.StaticCallGuard
import Blanc.Lift.HistStaticCall
import Blanc.ExecutionEntryAccounting

/-!
# Historical `STATICCALL` success guards

`staticCallGuard_invPH` and `staticCallGuard_exactH` are `StaticCallGuard`'s call-success guard
steps from `rules.stateGas = none` alone, through `ri_staticcall_boundedH`/`rx_staticcallH`;
`staticCallGuard_invPH_covered` recovers the modern conclusion.

A static child's entry under the two rule facts: `Evm.step_spawn_child_dataH` (short calldata,
and the parent's rule facts in the child); the child's opening world is
`Evm.step_spawn_child_world_noStateGas`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- `staticCallGuard_invP` from `rules.stateGas = none` under the actual access schedule and
delegation flag; the answer is `StaticAnsweredH`. -/
theorem staticCallGuard_invPH {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {C : List Nat} {M : Mem} {G : Nat} {z t ii is oi os : B256} {seg : Seg}
    {callTree failureTree successTree : SFunc} (destination : Bytes)
    (le : destination.length ≤ 32)
    (shape : callTree = .dest (.next (.reg .pop) (.next (.reg .gas)
      (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
        (.next (.reg .iszero) (.next (.push destination le)
          (.branch failureTree successTree)))))))))
    (project : ∀ {s d i d'}, P s d i d' → Ninst.Run s d i d')
    (hsg : sevm.benvStat.rules.stateGas = none) (noFail : failureTree.noOk = true)
    (run : SFunc.RunCutP P fs sevm C (St b (z :: t :: ii :: is :: oi :: os :: S) M G)
      callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      P sevm (St b (gw :: t :: ii :: is :: oi :: os :: S) M callGas) (.exec .staticcall) d ∧
      StaticCallPost b d S M ii is oi os 1 out ∧ out.length < 2^256 ∧
      StaticAnsweredH sevm b t.toAdr (M.read ii.toNat is.toNat).1 out ∧
      SFunc.RunCutP P fs sevm C
        (St d (0 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
          oi.toNat (out.take os.toNat)) tailGas) successTree seg := by
  rw [shape] at run
  obtain ⟨_, h⟩ := ric_destP run
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨gw, callGas, rfl⟩ := ri_gas (project hs)
  obtain ⟨d, hcall, h⟩ := ric_nextP h
  obtain ⟨flag, out, post, bound, answered⟩ := ri_staticcall_boundedH hsg (project hcall)
  rw [post.eq_St] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hs)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨accepted, tailGas, h⟩
  · exact (failed.false_of_noOk noFail).elim
  · have zeroFlag : B256.eqCheck flag 0 = 0 := eq_zero_of_iszero_ne_zero accepted
    rcases post.flag with zero | one
    · rw [zero, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zeroFlag
      exact False.elim ((by decide : (1 : B256) ≠ 0) zeroFlag)
    · subst flag
      refine ⟨gw, callGas, d, out, tailGas, hcall, post, bound, answered rfl, ?_⟩
      simpa only [show B256.eqCheck (1 : B256) 0 = 0 from by decide] using h

/-- `staticCallGuard_exact` from `rules.stateGas = none`. -/
theorem staticCallGuard_exactH {fs : List SFunc} {sevm : Sevm} {b d : Devm}
    {S : List B256} {M : Mem} {callGas tailGas : Nat} {z t ii is oi os : B256}
    {o : Outcome} {callTree failureTree successTree : SFunc} (destination : Bytes)
    (le : destination.length ≤ 32) (nonempty : destination ≠ [])
    (shape : callTree = .dest (.next (.reg .pop) (.next (.reg .gas)
      (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
        (.next (.reg .iszero) (.next (.push destination le)
          (.branch failureTree successTree)))))))))
    (hsg : sevm.benvStat.rules.stateGas = none) (room : S.length ≤ 1018)
    (call : Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: t :: ii :: is :: oi :: os :: S) M callGas)
      (.exec .staticcall) d)
    (success : d.stack = 1 :: S) (returnedGas : d.gasLeft = tailGas + 22)
    (body : SFunc.RunExact fs sevm
      (St d (0 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
        oi.toNat (d.returnData.take os.toNat)) tailGas) successTree o) :
    SFunc.RunExact fs sevm (St b (z :: t :: ii :: is :: oi :: os :: S) M (callGas + 5))
      callTree o := by
  cases destination with
  | nil => exact (nonempty rfl).elim
  | cons hd tl =>
    rw [shape]
    apply rx_dest
    apply rx_pop
    apply rx_gas (by simp only [List.length_cons]; omega)
    apply rx_staticcallH hsg call
    intro flag out post answered
    have flagEq : flag = 1 := (List.cons.inj (post.stack.symm.trans success)).1
    subst flag
    rw [returnedGas]
    apply rx_iszero (v := 0) (by decide) (by omega)
    apply rx_dup1 (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    rw [post.returnData] at body
    exact body

/-- `staticCallGuard_invPH` recovers the modern `staticCallGuard_invP` conclusion on a covered
fork. -/
theorem staticCallGuard_invPH_covered {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {C : List Nat} {M : Mem} {G : Nat} {z t ii is oi os : B256} {seg : Seg}
    {callTree failureTree successTree : SFunc} (destination : Bytes)
    (le : destination.length ≤ 32)
    (shape : callTree = .dest (.next (.reg .pop) (.next (.reg .gas)
      (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
        (.next (.reg .iszero) (.next (.push destination le)
          (.branch failureTree successTree)))))))))
    (project : ∀ {s d i d'}, P s d i d' → Ninst.Run s d i d')
    (fork : CoveredFork sevm.benvStat.fork) (noFail : failureTree.noOk = true)
    (run : SFunc.RunCutP P fs sevm C (St b (z :: t :: ii :: is :: oi :: os :: S) M G)
      callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      P sevm (St b (gw :: t :: ii :: is :: oi :: os :: S) M callGas) (.exec .staticcall) d ∧
      StaticCallPost b d S M ii is oi os 1 out ∧ out.length < 2^256 ∧
      StaticAnswered sevm b t.toAdr (M.read ii.toNat is.toNat).1 out ∧
      SFunc.RunCutP P fs sevm C
        (St d (0 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
          oi.toNat (out.take os.toNat)) tailGas) successTree seg := by
  obtain ⟨gw, callGas, d, out, tailGas, h1, h2, h3, h4, h5⟩ :=
    staticCallGuard_invPH destination le shape project fork.rules_stateGas_none noFail run
  exact ⟨gw, callGas, d, out, tailGas, h1, h2, h3, h4.of_covered fork, h5⟩

end Blanc.Lift

namespace Blanc

open Jaune

/-- `ExecutionTrace.Evm.step_spawn_child_data` from the two historical rule facts: an entered
child has short calldata and the parent's rule facts. -/
theorem Evm.step_spawn_child_dataH {pc : Nat} {sevm : Sevm} {pre : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none) (hbal : sevm.benvStat.rules.bal = none)
    (hs : Evm.step (⟨pc, sevm, pre⟩ : Evm) = .spawn f rsm pc')
    {cevm : Evm} (henter : f.enter = .run cevm) :
    cevm.sta.data.length < 2 ^ 256 ∧
      (cevm.sta.benvStat.rules.stateGas = none ∧ cevm.sta.benvStat.rules.bal = none) := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hs
  have hstat : cevm.sta.benvStat = sevm.benvStat := by
    rw [Frame.enter_run_benvStat henter, Xinst.step_spawn_benvStat hx]
  obtain ⟨short, childStateGas⟩ := ExecutionTrace.Evm.step_spawn_child_data_noStateGas hsg hs henter
  exact ⟨short, childStateGas, by rw [hstat]; exact hbal⟩

end Blanc
