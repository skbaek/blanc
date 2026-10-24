import Blanc.ExecutionModelAccounting
import Blanc.ExecutionWholeFrameAccountingIn
import Blanc.Lift.Quiet

/-!
# A model replay of a target frame over a selected fork domain

The modern model handler (`Blanc/ExecutionModelAccounting.lean`) reads `CoveredFork` at the spawn
seam (`Exec.spawn_seam`, whose `CREATE` arm uses the modern nonce retention), at the child's entry
storage and world, in the static case and in the contract's `SpawnReplay` obligation.

This module is the additive counterpart over a selected fork domain `F` whose forks have no state
gas, for code whose frames spawn only by `CALL`/`STATICCALL` (`SpawnKindsIn F`):

* `Exec.spawn_seam_callsIn` — the storage seam of a call-family spawning step, from
  `stateGas = none`; the create arm is excluded by the decoded instruction;
* `Exec.CoreAccountingIn.modelFrameIn` — `modelFrame` for a frame whose chain decodes only
  `CALL`/`STATICCALL`, with the child's entry storage and world from
  `Evm.step_spawn_child_world_noStateGas`;
* `SpawnReplayIn F`, `spawnReplayTargetIn` and `modelLadderIn`, producing
  `AccountingLadderAdmittedIn`; static frames and children go through `staticFrameIn`,
  `staticObservedNilIn` and `spawnChildIn`.
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-- **The storage across a call-family spawning step**, from `stateGas = none`: a settled child
hands its committed storage back to the parent, and a child that does not settle leaves the
parent's storage as it was. The node's instruction is `CALL` or `STATICCALL`. -/
theorem Exec.spawn_seam_callsIn {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm}
    {frame : Jaune.Frame} {resume : Resume} {cevm : Evm} {raw : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (calls : ∀ x, Ninst.At sevm.code pc (.exec x) → x = .call ∨ x = .staticcall)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run cevm) (_child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok inter) :
    (∀ h : Execution.commits raw = true, Frame.settlementCommits frame raw = true →
      ∀ a k, (Devm.getStor inter a).get k =
        (Devm.getStor (Execution.committedPost raw h) a).get k) ∧
    (Frame.settlementCommits frame raw ≠ true →
      ∀ a k, (Devm.getStor inter a).get k = (Devm.getStor pre a).get k) := by
  obtain ⟨x, instruction, spawn, -⟩ := Evm.step_spawn_inv step
  have family := calls x instruction
  refine ⟨?_, fun discarded a k => ?_⟩
  · intro committed settles a k
    rcases Lift.Xinst.step_shapeLogs_noStateGas sevm pre x hsg rfl rfl with
      ⟨execution, shape, -⟩ | ⟨creates, -⟩ |
      ⟨d, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, disablePrecompiles, -, shape⟩
    · rw [shape] at spawn
      cases spawn
    · exfalso
      rcases family with rfl | rfl <;> rcases creates with h | h <;> cases h
    · rw [shape] at spawn
      rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
      cases settledEq : (Frame.ofCall _).settle raw with
      | error error =>
          rw [settledEq] at hresume
          exact (Resume.call_run_error hresume).elim
      | ok settled =>
          have process := RunFrame.of_run (raw := raw) enter
          rw [settledEq] at process
          have stateEq := ProcessMessage.ok_state_eq_committedPost process committed
          rw [settledEq] at hresume
          have resumedState := Resume.call_state hresume
          change ((inter.state.get a).stor).get k =
            (((Execution.committedPost raw committed).state.get a).stor).get k
          rw [resumedState, stateEq]
  · exact congrArg (fun stor => stor.get k)
      (congrFun (Evm.step_spawn_rollback_getStor_noStateGas hsg step enter hresume discarded) a)

namespace Exec.CoreAccountingIn

variable {F : Fork → Prop}
variable {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop} {C : ReplayCarrier ca}
  {V : ReplayObservation C}

/-- **The model replay of a successful frame over a domain without state gas**, for a frame whose
chain decodes only `CALL`/`STATICCALL` external instructions (the statement of `modelFrame`, with
`stateGas = none` and that restriction in place of `CoveredFork`). -/
theorem modelFrameIn
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (hsg : sevm.benvStat.rules.stateGas = none)
    (calls : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .call ∨ x = .staticcall)
    (rootNonempty : (pre.getCode ca).toList ≠ []) (bound : sum pre.state.bal < 2 ^ 256)
    (children : Exec.CoreAccounting.ChildReplays C V run) {a : C.Snap} (own : List C.Step)
    (c3 : (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
      C.Replay a own (C.ofState post.state))
    (c12 : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        C.Replay a own (C.ofState N.devm.state) ∧
        ∀ N', Exec.Deriv.ParentStep N' N →
          C.Replay (C.ofState N'.devm.state) [] (C.ofState post.state) ∧
          ∀ M, Exec.Deriv.ParentPrefix N' M →
            ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y)) :
    ∃ steps, C.Replay a steps (C.ofState post.state) ∧
      V.obs steps = V.obs own ++ (Exec.descendantFrames run).flatMap V.frameObs := by
  rcases Exec.Deriv.exists_firstExec_or_none run with none | ⟨Vn, hV⟩
  · rw [Exec.descendantFrames_eq_nil_of_noExec run none]
    exact ⟨own, c3 none, by rw [List.flatMap_nil, List.append_nil]⟩
  · have hpV := hV.parentPrefix
    have dEq := hV.descendantFrames_eq
    obtain ⟨x, hx⟩ := hV.exec_at
    have hexn := Exec.Deriv.ParentPrefix.exn_eq hpV
    obtain ⟨vpc, vsevm, vd, vout, vrun⟩ := Vn
    dsimp only at hexn hx dEq
    subst hexn
    have nodeNonempty : (vd.getCode ca).toList ≠ [] := by
      rw [Blanc.Exec.Deriv.ParentPrefix.codePreserve hpV ca rootNonempty]
      exact rootNonempty
    cases vrun with
    | halt step =>
        rw [Evm.step_next hx] at step
        exact (Ninst.step_ne_halt_ok step).elim
    | cont step next =>
        rename_i pc' post'
        have nstep : Ninst.step ⟨vpc, vsevm, vd⟩ (.exec x) = .cont pc' post' := by
          rw [← Evm.step_next hx]
          exact step
        have nrun : Ninst.StepRun vpc vsevm vd (.exec x) .none (.ok post') := by
          unfold Ninst.StepRun
          rw [nstep]
          exact ⟨rfl, rfl⟩
        have hstor : Devm.getStor post' ca = Devm.getStor vd ca :=
          Ninst.none_getStor_eq_of_ne_sstore nrun (by intro h; cases h) ca
            (State.Protected.of_code_ne_nil nodeNonempty)
        obtain ⟨hc1, hc2⟩ := c12 _ hpV x hx
        obtain ⟨hrep2, hnoexec⟩ := hc2 _ (Exec.Deriv.ParentStep.cont step next)
        have hdf : Exec.descendantFrames next = [] :=
          Exec.descendantFrames_eq_nil_of_noExec next fun M hM y => hnoexec M hM y
        have hE : C.ofState vd.state = C.ofState post'.state :=
          ofStateGet fun k => by
            exact (congrArg (fun t => Stor.get t k) hstor).symm
        rw [dEq]
        simp only [Exec.descendantFrames, hdf, List.flatMap_nil, List.append_nil]
        refine ⟨own ++ [], append (hE ▸ hc1) hrep2, ?_⟩
        rw [V.obs_append, V.obs_nil, List.append_nil]
    | doneOk step enter resume next =>
        rename_i settled pc' post'
        have hstor : Devm.getStor post' ca = Devm.getStor vd ca :=
          Evm.step_doneOk_getStor_eq step enter resume ca
            (State.Protected.of_code_ne_nil nodeNonempty)
        obtain ⟨hc1, hc2⟩ := c12 _ hpV x hx
        obtain ⟨hrep2, hnoexec⟩ := hc2 _ (Exec.Deriv.ParentStep.doneOk step enter resume next)
        have hdf : Exec.descendantFrames next = [] :=
          Exec.descendantFrames_eq_nil_of_noExec next fun M hM y => hnoexec M hM y
        have hE : C.ofState vd.state = C.ofState post'.state :=
          ofStateGet fun k => by
            exact (congrArg (fun t => Stor.get t k) hstor).symm
        rw [dEq]
        simp only [Exec.descendantFrames, hdf, List.flatMap_nil, List.append_nil]
        refine ⟨own ++ [], append (hE ▸ hc1) hrep2, ?_⟩
        rw [V.obs_append, V.obs_nil, List.append_nil]
    | runOk step enter child resume next =>
        rename_i frame rsm pc' cevm raw inter
        have nodeHsg : vsevm.benvStat.rules.stateGas = none := by
          rw [show vsevm = sevm from Blanc.Exec.Deriv.ParentPrefix.sevm_eq hpV]
          exact hsg
        have nodeCodeNe : vd.getCode ca ≠ .empty := fun empty =>
          nodeNonempty (by rw [empty]; simp only [ByteArray.toList_empty])
        obtain ⟨hc1, hc2⟩ := c12 _ hpV x hx
        obtain ⟨hrep2, hnoexec⟩ := hc2 _ (Exec.Deriv.ParentStep.runOk step enter child resume next)
        have hdf : Exec.descendantFrames next = [] :=
          Exec.descendantFrames_eq_nil_of_noExec next fun M hM y => hnoexec M hM y
        obtain ⟨seamA, seamB⟩ :=
          Exec.spawn_seam_callsIn nodeHsg (calls _ hpV) step enter child resume
        obtain ⟨hentry, childBal⟩ :=
          Evm.step_spawn_child_world_noStateGas nodeHsg step enter nodeCodeNe
        rw [dEq, Exec.descendantFrames_flatMap_runOk, hdf, List.flatMap_nil, List.append_nil]
        by_cases settles : Frame.settlementCommits frame raw = true
        · have hcommit := Frame.raw_commits_of_settlementCommits settles
          have bound' : sum cevm.dyna.state.bal < 2 ^ 256 :=
            Nat.lt_of_le_of_lt
              (childBal.trans (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode hpV).1) bound
          obtain ⟨csteps, creplay, cobs⟩ := children step enter child resume next hpV hcommit bound'
          have e1 : C.frameEntry cevm.sta cevm.dyna.state = C.ofState vd.state := by
            rw [entryOfState]
            exact ofStateGet fun k => by
              exact congrArg (fun t => Stor.get t k) hentry
          have e2 : C.ofState (Execution.committedPost raw hcommit).state =
              C.ofState inter.state := ofStateGet fun k => (seamA hcommit settles ca k).symm
          rw [e1, e2] at creplay
          refine ⟨own ++ csteps ++ [], append (append hc1 creplay) hrep2, ?_⟩
          rw [V.obs_append, V.obs_append, cobs, V.obs_nil]
          simp only [settles, ↓reduceIte, List.append_nil]
        · have e3 : C.ofState vd.state = C.ofState inter.state :=
            ofStateGet fun k => (seamB settles ca k).symm
          refine ⟨own ++ [], append (e3 ▸ hc1) hrep2, ?_⟩
          rw [V.obs_append, V.obs_nil]
          have hf : Frame.settlementCommits frame raw = false := by
            simpa only [Bool.not_eq_true] using settles
          simp only [hf, Bool.false_eq_true, ↓reduceIte, List.append_nil]

/-- **The contract's model-replay obligations over `F`**: `Exec.CoreAccounting.SpawnReplay` with
`F sevm.benvStat.fork` in place of `CoveredFork`. -/
def SpawnReplayIn (F : Fork → Prop) (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop)
    (C : ReplayCarrier ca) (V : ReplayObservation C) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true),
    sem.Run sevm pre post → sevm.currentTarget = ca → F sevm.benvStat.fork →
    sem.At ca 0 sevm pre → Exec.FrameAdmitted ca entry run → sum pre.state.bal < 2 ^ 256 →
    sevm.isStatic = false →
    ∃ own : List C.Step, V.obs own = V.frameObs (Exec.Frame.ofRun run committed) ∧
      ((∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
          ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
        C.Replay (C.frameEntry sevm pre.state) own (C.ofState post.state)) ∧
      (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
          C.Replay (C.frameEntry sevm pre.state) own (C.ofState N.devm.state) ∧
          ∀ N', Exec.Deriv.ParentStep N' N →
            C.Replay (C.ofState N'.devm.state) [] (C.ofState post.state) ∧
            ∀ M, Exec.Deriv.ParentPrefix N' M →
              ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y))

/-- **The target handler for a model replay over `F`**, for code whose frames spawn only by
`CALL`/`STATICCALL`. -/
theorem spawnReplayTargetIn
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none)
    (kinds : SpawnKindsIn F ca sem) (spawn : SpawnReplayIn F ca sem entry C V)
    {sevm : Sevm} {pre post : Devm} (hrun : sem.Run sevm pre post)
    (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAtSem sevm.depth ca sem
      (fun pc s d e _ => Exec.CoreAccountingIn F ca sem entry C V pc s d e)) :
    Exec.CoreAccountingIn F ca sem entry C V 0 sevm pre (.ok post) := by
  intro run committed hF installed admitted
  have hsg : sevm.benvStat.rules.stateGas = none := hsgF hF
  have rootNonempty : (pre.getCode ca).toList ≠ [] := fun empty =>
    sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  by_cases hs : sevm.isStatic = true
  · exact staticFrameIn entryOfState ofStateGet obsStatic run committed hsg rootNonempty hs
      (staticObservedNilIn kinds run hrun target hF installed admitted deeper run (.refl _) hs)
  · have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
    refine ⟨fun h => absurd h hs, fun bound => ?_⟩
    obtain ⟨own, hown, c3, c12⟩ := spawn run committed hrun target hF installed admitted bound hs'
    obtain ⟨steps, replay, observed⟩ := modelFrameIn entryOfState ofStateGet append run hsg
      (fun N chain x hat => kinds run hrun target hF installed N chain x hat)
      rootNonempty bound
      (fun step enter child resume next chain childCommitted childBound => by
        obtain ⟨-, -, -, -, -, -, -, childCore⟩ := spawnChildIn kinds run hrun target hF
          installed admitted deeper step enter child resume next chain
        exact (childCore childCommitted).2 childBound)
      own c3 c12
    refine ⟨steps, replay, ?_⟩
    rw [observed, hown, Exec.committedFrames, dite_eq_left committed, List.flatMap_cons]

end Exec.CoreAccountingIn

namespace ExecutionAccountingReplay

/-- **The accounting ladder of a model replay over `F`**: the contract's `PreservesAdmittedIn` and
its `SpawnReplayIn` obligations give the observed accounting ladder; foreign frames, messages,
transactions, blocks and rollback are the generic ladder's. -/
def modelLadderIn {F : Fork → Prop} {c : ContractSpecSem} {ca : Adr}
    {entry : Sevm → Devm → Prop}
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none)
    (kinds : SpawnKindsIn F ca c.sem)
    (spawn : Exec.CoreAccountingIn.SpawnReplayIn F ca c.sem entry C V)
    (preserves : c.PreservesAdmittedIn F ca entry) : AccountingLadderAdmittedIn F c ca entry where
  carrier := C
  append := append
  tag := tag
  preserves := preserves
  view := V
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ hF
      bound
    obtain ⟨installed, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have core := Exec.coreAccountingIn F ca c.sem entry C V append frameTag
      (fun sevm state _ => entryOfState sevm state) obsForeign hsgF
      (fun hrun target deeper =>
        Exec.CoreAccountingIn.spawnReplayTargetIn entryOfState ofStateGet obsStatic append hsgF
          kinds spawn hrun target deeper)
    exact (core pc sevm pre out run installed run committed hF installed admitted).2 entryBound

end ExecutionAccountingReplay

end Blanc
