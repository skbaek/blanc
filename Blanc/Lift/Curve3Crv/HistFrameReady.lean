import Blanc.Lift.Curve3Crv.HistCommittedHistory
import Blanc.Lift.StaticOnlyFramesIn
import Blanc.ExecutionInOwnCode
import Blanc.ExecutionWholeFrameAccountingIn

/-!
# 3Crv at every settled frame of a historical mid history

`FrameReadyH ca U f`: a settled frame starts at pc `0` on a historical fork with 3Crv's code installed,
is admitted by 3Crv's entry condition below it, and its world balance total is a word. A frame-observing
accounting ladder over 3Crv's spec (`readyLadderH`) proves it of every settled frame of a mid history
(`c3crv_mid_readyH`); no separate own-code or balance walk over the trace is needed, because the root
law of the ladder has them.

* `c3crv_descendants_staticH` — every descendant of a settled 3Crv frame is static;
* `committedFrameInvocations_nil_of_static` — a static 3Crv frame runs no writer.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

theorem code_of_image {c : ByteArray} (h : some c.toList = c3crvSem.image) : c = code := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj h

/-- 3Crv's runtime spawns only by `STATICCALL`, on any fork without state gas. -/
theorem c3crv_ownSpawnsIn (ca : Adr) : OwnSpawnsIn ca code := by
  intro R N x pcZero hcode _ hsg chain instruction
  exact .inr (.inl (parentPrefix_exec_staticcall_of_cert_noStateGas cert_check cert_onlyStaticcall
    pcZero hcode hsg chain instruction))

/-- **The balance total does not grow below a run** on a fork without state gas. -/
theorem descendantFrames_balSum_leH {a : Adr} :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      sevm.benvStat.rules.stateGas = none → (pre.getCode a).toList ≠ [] →
      ∀ D ∈ Exec.descendantFrames run, sum D.pre.state.bal ≤ sum pre.state.bal := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro _ _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont hstep next ih =>
      intro hsg code D member
      have edge := Jaune.Exec.Deriv.ParentStep.cont hstep next
      have keep := Blanc.Exec.Deriv.ParentStep.codePreserve edge a code
      have hb := Blanc.Exec.Deriv.ParentStep.balSum_le edge
      dsimp only at keep hb
      exact Nat.le_trans (ih hsg (by rw [keep]; exact code) D
        (by simpa only [Exec.descendantFrames] using member)) hb
  | doneErr _ _ _ =>
      intro _ _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk hstep henter hresume next ih =>
      intro hsg code D member
      have edge := Jaune.Exec.Deriv.ParentStep.doneOk hstep henter hresume next
      have keep := Blanc.Exec.Deriv.ParentStep.codePreserve edge a code
      have hb := Blanc.Exec.Deriv.ParentStep.balSum_le edge
      dsimp only at keep hb
      exact Nat.le_trans (ih hsg (by rw [keep]; exact code) D
        (by simpa only [Exec.descendantFrames] using member)) hb
  | runErr _ _ _ _ =>
      intro _ _ D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      intro hsg code D member
      have world := (Evm.step_spawn_child_world_noStateGas hsg hstep henter (a := a) fun empty =>
        code (by rw [empty]; simp only [ByteArray.toList_empty])).2
      have childSg := (ExecutionTrace.Evm.step_spawn_child_data_noStateGas hsg hstep henter).2
      have childCode := (Evm.step_spawn_child hstep henter).2.1 a
      have edge := Jaune.Exec.Deriv.ParentStep.runOk hstep henter child hresume next
      have keep := Blanc.Exec.Deriv.ParentStep.codePreserve edge a code
      have hb := Blanc.Exec.Deriv.ParentStep.balSum_le edge
      dsimp only at keep hb
      simp only [Exec.descendantFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_cons] at here
          rcases here with rfl | deeper
          · exact world
          · exact Nat.le_trans (childIh childSg (by rw [childCode]; exact code) D deeper) world
        · simp only [List.not_mem_nil] at here
      · exact Nat.le_trans (nextIh hsg (by rw [keep]; exact code) D later) hb

/-- A settled frame's side conditions for 3Crv's accounting descent at the frame, over historical
forks. -/
def FrameReadyH (ca : Adr) (U : Key → Prop) (f : Exec.Frame) : Prop :=
  f.pc = 0 ∧ HistFork f.sevm.benvStat.fork ∧ c3crvSem.At ca 0 f.sevm f.pre ∧
    Exec.FrameAdmitted ca (carriedFrameEntry U) f.run ∧ sum f.pre.state.bal < 2 ^ 256

/-- The ladder observing every settled frame with `FrameReadyH`. -/
def readyLadderH (ca : Adr) (U : Key → Prop)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots) :
    AccountingLadderAdmittedIn HistFork (curveSpec U) ca (carriedFrameEntry U) where
  carrier :=
    { Snap := Unit
      Step := Exec.Frame
      Tag := Unit
      Replay := fun _ steps _ => ∀ f ∈ steps, FrameReadyH ca U f
      ofState := fun _ => ()
      frameEntry := fun _ _ => ()
      nil := fun _ f member => (List.not_mem_nil member).elim
      readsStorage := false
      silent := fun _ _ => rfl
      credit := by
        intros
        exact ⟨[], fun f member => (List.not_mem_nil member).elim⟩
      entry_eq_ofState := fun _ _ _ _ => rfl }
  append := fun left right f member => (List.mem_append.mp member).elim (left f) (right f)
  tag := fun _ _ => ()
  preserves := curveSpec_preservesAdmittedIn HistFork HistFork.stateGas_none ca U injective apart
  view :=
    { O := Exec.Frame
      obs := id
      obs_nil := rfl
      obs_append := fun _ _ => rfl
      frameObs := fun f => [f]
      credit := by
        intros
        exact ⟨[], fun f member => (List.not_mem_nil member).elim, rfl⟩ }
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork bound
    obtain ⟨installed, entryBound⟩ :=
      Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have hpc : pc = 0 := congrArg (fun e : Evm => e.pc) evmEq
    subst hpc
    have hsg : sevm.benvStat.rules.stateGas = none := fork.stateGas_none
    have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
      (curveSpec U).sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
    have nonempty : code.toList ≠ [] := fun empty =>
      c3crvSem.ne_nil (show c3crvSem.image = some code.toList from rfl) empty
    have nondelegating : ¬ isValidDelegation code :=
      c3crvSem.not_delegation (show some code.toList = c3crvSem.image from rfl)
    have rootCode : pre.getCode ca = code := code_of_image installed.1
    have rootTarget : sevm.currentTarget = ca → sevm.code = code := fun target =>
      code_of_image (installed.2 target).1
    have below := Exec.descendantFrames_ownCodeIn (F := HistFork) nonempty nondelegating
      (c3crv_ownSpawnsIn ca) run (R := ⟨0, sevm, pre, out, run⟩) (.refl _) rfl fork hsg rootCode
      rootTarget
    refine ⟨Exec.committedFrames run, ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    intro f member
    have hadm : Exec.FrameAdmitted ca (carriedFrameEntry U) f.run := admitted.mono fun r hr =>
      Exec.rawFrameRoots_trans (Exec.mem_rawFrameRoots_of_mem_committedFrames run f member) hr
    rw [Exec.committedFrames, dite_eq_left committed] at member
    rcases List.mem_cons.mp member with rfl | deeper
    · exact ⟨rfl, fork, installed, hadm, entryBound⟩
    · obtain ⟨hc, hpcF, hf, -, hown⟩ := below f deeper
      exact ⟨hpcF, hf, ⟨by rw [hc]; rfl, fun target => ⟨by rw [hown target]; rfl, rfl⟩⟩, hadm,
        Nat.lt_of_le_of_lt (descendantFrames_balSum_leH run hsg codeNe f deeper) entryBound⟩

/-- 3Crv's entry condition holds at every raw frame of a mid history, over its touched keys. -/
theorem c3crv_mid_admittedH {ca : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    {initialKeys : Key → Prop} (trace : MidHistoryTraceIn HistFork cfg start future) :
    trace.FrameAdmitted ca
      (carriedFrameEntry (Key.extend initialKeys (midTouchedKeysIn ca trace))) := by
  apply (trace.frameAdmitted_iff_rawFrames ca _).2
  intro root member target
  refine ⟨trace.rawFrames_entered enteredCondition_fresh root member,
    trace.calldata_bound BodyStageCapabilities.historical (fun _ hf => hf.dataNonZero_ge) root member,
    fun k hk => Or.inr ?_⟩
  exact List.mem_flatMap.mpr ⟨root, member, by simpa only [target, ite_true] using hk⟩

/-- **Every settled frame of a historical mid history is ready** for 3Crv's descent at it. -/
theorem c3crv_mid_readyH {ca : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (start.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (midTouchedKeysIn ca trace)) :
    ∀ f ∈ trace.settledFrames,
      FrameReadyH ca (Key.extend initialKeys (midTouchedKeysIn ca trace)) f := by
  let U := Key.extend initialKeys (midTouchedKeysIn ca trace)
  have topology : VyInv (start.state.getStor ca) initial U := invariant.extend fresh
  have capabilities := BodyStageCapabilities.historical
  have startInv : (curveSpec U).StateInv ca start.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  obtain ⟨steps, replay, observed⟩ :=
    (readyLadderH ca U topology.inj topology.apart).midHistoryIn trace (c3crv_mid_admittedH trace)
      capabilities (trace.rewardCreditsFunded capabilities) startInv
      c3crvInstalledCert.runtimeSafety rfl
  change steps = trace.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  intro f member
  exact replay f (observed ▸ member)

/-- **Every descendant of a settled 3Crv frame is static.** -/
theorem c3crv_descendants_staticH {ca : Adr} {U : Key → Prop} {A : Exec.Frame}
    (ready : FrameReadyH ca U A) (target : A.sevm.currentTarget = ca) :
    ∀ D ∈ Exec.descendantFrames A.run, D.sevm.isStatic = true := by
  obtain ⟨hpc, fork, at_, -, -⟩ := ready
  have hcode : A.sevm.code = code := code_of_image (at_.2 target).1
  have none := Exec.staticOnly_descendantFrames_flatMap_eq_nilIn (F := HistFork) ca c3crvSem
    (fun _ _ => True) (fun D : Exec.Frame => if D.sevm.isStatic = true then ([] : List Unit) else [()])
    (Blanc.Exec.Frame.rootDeriv A) target at_.1 fork
    (fun chain instruction =>
      parentPrefix_exec_staticcall_of_cert_noStateGas cert_check cert_onlyStaticcall
        (root := Blanc.Exec.Frame.rootDeriv A) hpc hcode fork.stateGas_none chain instruction)
    (fun run _ _ _ _ _ static => List.flatMap_eq_nil_iff.mpr fun D member => by
      rw [if_pos (Blanc.Exec.committedFrames_isStatic run static D member)])
    A.run (.refl _) (fun _ _ _ => trivial)
  intro D member
  have empty := List.flatMap_eq_nil_iff.mp none D member
  by_contra hs
  rw [if_neg hs] at empty
  cases empty

/-- **A static frame runs no 3Crv writer.** -/
theorem committedFrameInvocations_nil_of_static {ca : Adr} {U : Key → Prop} {f : Exec.Frame}
    (ready : FrameReadyH ca U f) (static : f.sevm.isStatic = true) :
    committedFrameInvocations ca f = [] := by
  unfold committedFrameInvocations
  split
  · rename_i sel
    exfalso
    obtain ⟨hpc, fork, at_, admitted, -⟩ := ready
    obtain ⟨⟨hstack, hmem⟩, hcd, -⟩ := admitted.root sel.1
    have hcode : f.sevm.code = code := code_of_image (at_.2 sel.1).1
    obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
    dsimp only at hpc static sel hstack hmem hcd hcode fork
    subst hpc
    cases out with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
      have := c3crv_writer_nonstaticH hcode fork.stateGas_none hcd hstack hmem run sel.2
      rw [static] at this
      cases this
  · rfl

end Blanc.Lift.Curve3Crv
