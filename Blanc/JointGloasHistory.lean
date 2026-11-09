import JauneConsensus.Facts.JointGloas
import Blanc.JointHistory
import Blanc.ExecutionKeptConfigured

/-!
# Gloas joint runs: `GJointRun` over `jointStepG`, with one kept execution history

A Gloas joint run (goal `eip8282-gloas-cross-layer-v1` §3; Plans `recon/statements.md` §0.1, rev 3.1) is a
sequence of successful `JauneConsensus.jointStepG` steps over the sum state `GJointState`, each one of three kinds:

* `.pre`: an Electra/Fulu step (`jointStep`), with the configured execution block trace of the 7002 joint
  history (`JointStepTrace`), before the Gloas fork slot;
* `.crossing`: the Fulu → Gloas step (`Gloas.crossFromFulu`, `upgrade_to_gloas`, then the first Gloas block,
  which settles its `.landed` parent FULL with empty requests);
* `.gloas`: a Gloas → Gloas step, with its post-slots state `postSlots` (the state Gloas `process_block`
  receives, at which the BF1 traces are read; `gloasStep_ok_iff`), its parent settlement, its block transition
  and its envelope (if any).

Each step carries the execution blocks it builds upon (`GJointRunStep.kept`): a `.pre` step its own payload's
block (the configured block's kept block, `ConfiguredBlockTrace.kept`), a `.gloas` step that settles its parent
FULL over a delivered payload that payload's block (an Amsterdam kept step), and nothing otherwise. The run's
execution side is one `KeptHistory` over `GJointRun.blocks` (`GJointRun.keptHistory`): the covered-fork prefix
spliced with the Amsterdam steps (R13, `KeptHistory.append`).

`GJointRunStep.exists_of_jointStepG` shows the run asks no more of a chain than successful joint steps: every
successful `jointStepG` step (with the 7002 balance no-wrap bound on a pre-Gloas step) from a state whose
delivered payload, if any, is the engine's verdict on its chain (`ParentCoherent`) is a run step; and every
step's post-state is coherent (`GJointRunStep.postState_coherent`), so only the anchor needs it.
-/

namespace Blanc

open Jaune JauneConsensus ExecutionTrace

variable {P : Preset}

/-! ## Coherence of a delivered payload with the built-upon chain -/

/-- A Gloas state's delivered payload, if any, is the engine's verdict on its request over the state's
built-upon chain. -/
def ParentCoherent (cfg : ChainConfig) : GJointState P → Prop
  | .gloas _ exec (.delivered _ req post) => engineVerdictG cfg exec req = .ok post
  | _ => True

/-- The 7002 balance no-wrap bound a pre-Gloas step's configured block trace needs; no bound otherwise. -/
def PreBound : GJointState P → GBlock P → Prop
  | .pre s, .pre b => sum s.exec.state.bal + wdsum (payloadWithdrawals b) < 2 ^ 256
  | _, _ => True

/-- **An accepted Gloas payload is an Amsterdam kept step** from the chain the engine ran it on to the
engine's chain. -/
theorem keptStep_of_engineVerdictG {cfg : ChainConfig} {exec post : BlockChain}
    {req : Gloas.NewPayloadRequest P} (h : engineVerdictG cfg exec req = .ok post) :
    ∃ b : KeptBlock, b.parent = exec ∧ b.block = payloadToBlockG req ∧ b.fork = .amsterdam ∧
      KeptStep cfg b post := by
  obtain ⟨_, _, _, hc, f, hf, hp, _, hs, _⟩ := engineVerdictG_ok_iff.mp h
  rw [consensusFork?_eq_gloas_iff] at hp
  subst hp
  obtain ⟨b, hb1, hb2, hk⟩ := exists_keptStep (stateTransitionUsing_of_scheduled hc hf hs)
    (fun fork hfork => by
      obtain rfl : fork = .amsterdam := Except.ok.inj (hfork.symm.trans hf)
      exact Or.inr rfl)
  refine ⟨b, hb1, hb2, ?_, hk⟩
  exact Except.ok.inj (hk.forkAt.symm.trans (hb2 ▸ hf))

/-- The engine's chain after an accepted Gloas payload ends with the payload's block. -/
theorem engineVerdictG_getLast {cfg : ChainConfig} {exec post : BlockChain}
    {req : Gloas.NewPayloadRequest P} (h : engineVerdictG cfg exec req = .ok post) :
    post.blocks.getLast? = some (payloadToBlockG req) := by
  obtain ⟨_, _, _, hc, f, hf, _, _, hs, _⟩ := engineVerdictG_ok_iff.mp h
  obtain ⟨_, _, _, _, _, _, rfl⟩ :=
    exists_configuredBody_of_transition (stateTransitionUsing_of_scheduled hc hf hs)
  exact appendBlock_getLast? _ _

/-! ## The three step kinds -/

/-- A pre-Gloas step (Electra, Fulu, or the Electra → Fulu crossing), before the Gloas fork slot, with its
configured execution block trace. -/
structure PreStepData (cfg : ChainConfig) (ccfg : Config) (bls : Bool) : Type where
  pre : JointState P
  post : JointState P
  block : AnySignedBlock P
  beforeGloas : block.2.message.slot.toNat < gloasForkSlot (P := P) ccfg
  step : jointStep cfg ccfg bls pre block = .ok post
  stepTrace : JointStepTrace cfg ccfg bls pre post block

/-- The Fulu → Gloas step: `Gloas.crossFromFulu` of the Fulu state (`process_slots` to the fork slot, then
`upgrade_to_gloas` of the state there, `atFork`), the crossing's slots to the block (`postSlots`), the FULL
settlement of the `.landed` synthetic bid with empty requests, the block transition, and the envelope. The
built-upon chain does not move. -/
structure CrossingData (cfg : ChainConfig) (ccfg : Config) (bls : Bool) : Type where
  preFulu : BeaconState P .fulu
  exec : BlockChain
  block : Gloas.SignedBeaconBlock P
  env? : Option (Gloas.SignedExecutionPayloadEnvelope P)
  atFork : BeaconState P .fulu
  upgraded : Gloas.BeaconState P
  postSlots : Gloas.BeaconState P
  postB : Gloas.BeaconState P
  postParent : ParentPayload P
  beforeFork : preFulu.slot.toNat < gloasForkSlot (P := P) ccfg
  atOrAfterFork : gloasForkSlot (P := P) ccfg ≤ block.message.slot.toNat
  cross : Gloas.crossFromFulu (gloasCtx ccfg bls) preFulu = .ok upgraded
  upgrade : Gloas.upgradeToGloas (gloasCtx ccfg bls) atFork = .ok upgraded
  slots : crossingSlots (gloasCtx ccfg bls) upgraded block.message.slot = .ok postSlots
  full : parentFull postSlots block.message = true
  emptyRequests : block.message.body.parent_execution_requests = Gloas.ExecutionRequests.empty
  transition : gloasBlockTransition (gloasCtx ccfg bls) postSlots block = .ok postB
  deliver : gloasDeliverOpt cfg ccfg bls postB exec env? = .ok (.gloas postB exec postParent)

/-- A Gloas → Gloas step: Gloas `process_slots` to the block's slot (`postSlots`), the execution-side
settlement of the parent payload keyed on the FULL test at `postSlots` (`settle`, giving `postExec`), the rest
of `state_transition` (`postB`), and the block's envelope or `.withheld` (`postParent`). `kept` is the
execution block the step builds upon: the delivered payload's block when it settles FULL over one, else
nothing. -/
structure GloasStepData (cfg : ChainConfig) (ccfg : Config) (bls : Bool) : Type where
  preB : Gloas.BeaconState P
  preExec : BlockChain
  preParent : ParentPayload P
  block : Gloas.SignedBeaconBlock P
  env? : Option (Gloas.SignedExecutionPayloadEnvelope P)
  postSlots : Gloas.BeaconState P
  postB : Gloas.BeaconState P
  postExec : BlockChain
  postParent : ParentPayload P
  settle : ParentSettle P
  slots : Gloas.processSlots (gloasCtx ccfg bls) preB block.message.slot = .ok postSlots
  settleOk : settleParent preParent preExec (parentFull postSlots block.message)
    block.message.body.parent_execution_requests = .ok (postExec, settle)
  transition : gloasBlockTransition (gloasCtx ccfg bls) postSlots block = .ok postB
  deliver : gloasDeliverOpt cfg ccfg bls postB postExec env? = .ok (.gloas postB postExec postParent)
  kept : List KeptBlock
  keptHistory : KeptHistory cfg preExec kept postExec
  keptSpec : (∃ env req post, settle = .full env req post ∧
      ∃ b, kept = [b] ∧ b.block = payloadToBlockG req ∧ b.fork = .amsterdam) ∨
    ((settle = .landed ∨ settle = .empty) ∧ kept = [])

/-- `D.requests`: the block's `parent_execution_requests`. -/
abbrev GloasStepData.requests {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GloasStepData (P := P) cfg ccfg bls) : Gloas.ExecutionRequests :=
  D.block.message.body.parent_execution_requests

/-- The block's builder deposit requests, as a list. -/
abbrev GloasStepData.builderDeposits {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GloasStepData (P := P) cfg ccfg bls) : List Gloas.BuilderDepositRequest :=
  D.requests.builder_deposits.toArray.toList

/-- The block's builder exit requests, as a list. -/
abbrev GloasStepData.builderExits {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GloasStepData (P := P) cfg ccfg bls) : List Gloas.BuilderExitRequest :=
  D.requests.builder_exits.toArray.toList

/-- Whether the step settled its parent FULL over a delivered payload. -/
def GloasStepData.isFull {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GloasStepData (P := P) cfg ccfg bls) : Prop :=
  ∃ env req post, D.settle = .full env req post

/-- One step of a Gloas joint run. -/
inductive GJointRunStep (cfg : ChainConfig) (ccfg : Config) (bls : Bool) : Type where
  | pre (D : PreStepData (P := P) cfg ccfg bls)
  | crossing (D : CrossingData (P := P) cfg ccfg bls)
  | gloas (D : GloasStepData (P := P) cfg ccfg bls)

namespace GJointRunStep

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-- The step's pre-state. -/
def preState : GJointRunStep (P := P) cfg ccfg bls → GJointState P
  | .pre D => .pre D.pre
  | .crossing D => .pre ⟨.fulu, D.preFulu, D.exec⟩
  | .gloas D => .gloas D.preB D.preExec D.preParent

/-- The step's post-state. -/
def postState : GJointRunStep (P := P) cfg ccfg bls → GJointState P
  | .pre D => .pre D.post
  | .crossing D => .gloas D.postB D.exec D.postParent
  | .gloas D => .gloas D.postB D.postExec D.postParent

/-- The step's block. -/
def block : GJointRunStep (P := P) cfg ccfg bls → GBlock P
  | .pre D => .pre D.block
  | .crossing D => .gloas D.block
  | .gloas D => .gloas D.block

/-- The step's envelope. -/
def env? : GJointRunStep (P := P) cfg ccfg bls → Option (Gloas.SignedExecutionPayloadEnvelope P)
  | .pre _ => none
  | .crossing D => D.env?
  | .gloas D => D.env?

/-- The execution blocks the step builds upon, in order. -/
noncomputable def kept : GJointRunStep (P := P) cfg ccfg bls → List KeptBlock
  | .pre D => [D.stepTrace.trace.kept]
  | .crossing _ => []
  | .gloas D => D.kept

/-- **Every run step is a successful joint step.** -/
theorem ok (D : GJointRunStep (P := P) cfg ccfg bls) :
    jointStepG cfg ccfg bls D.preState D.block D.env? = .ok D.postState := by
  cases D with
  | pre D => exact jointStepG_pre_ok_iff.mpr ⟨rfl, D.beforeGloas, D.post, D.step, rfl⟩
  | crossing D =>
    exact jointStepG_cross_ok_iff.mpr ⟨D.beforeFork, D.atOrAfterFork, D.upgraded, D.postSlots, D.postB,
      D.cross, D.slots, D.full, D.emptyRequests, D.transition, D.deliver⟩
  | gloas D =>
    exact jointStepG_gloas_ok_iff.mpr ⟨D.postSlots, D.postB, D.postExec, D.settle, D.slots, D.settleOk,
      D.transition, D.deliver⟩

/-- **The step's built-upon blocks form a kept history** from its pre-state's chain to its post-state's. -/
theorem keptHistory (D : GJointRunStep (P := P) cfg ccfg bls) :
    KeptHistory cfg D.preState.exec D.kept D.postState.exec := by
  cases D with
  | pre D => exact .step (blocks := []) .refl D.stepTrace.trace.keptStep
  | crossing D => exact .refl
  | gloas D => exact D.keptHistory

end GJointRunStep

/-- The end of a Gloas step leaves a coherent state: the block's envelope, if any, was accepted by the
engine over the step's built-upon chain. -/
theorem gloasDeliverOpt_coherent {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {post : Gloas.BeaconState P} {exec : BlockChain} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    {s' : GJointState P} (h : gloasDeliverOpt cfg ccfg bls post exec env? = .ok s') : ParentCoherent cfg s' := by
  rcases gloasDeliverOpt_ok_iff.mp h with ⟨-, rfl⟩ | ⟨e, req, postE, -, hv, rfl⟩
  · trivial
  · exact (verifyEnvelopeG_ok_iff.mp hv).2.2.2

/-- **Every run step's post-state is coherent**, whatever its pre-state. -/
theorem GJointRunStep.postState_coherent {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GJointRunStep (P := P) cfg ccfg bls) : ParentCoherent cfg D.postState := by
  cases D with
  | pre D => trivial
  | crossing D => exact gloasDeliverOpt_coherent D.deliver
  | gloas D => exact gloasDeliverOpt_coherent D.deliver

/-- **The run asks no more than the joint step.** A successful joint step, with the 7002 balance bound on a
pre-Gloas step and a coherent pre-state, is a run step between the same states, with the same block and
envelope. -/
theorem GJointRunStep.exists_of_jointStepG {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : GJointState P} {b : GBlock P} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (h : jointStepG cfg ccfg bls s b env? = .ok s') (bound : PreBound s b) (coh : ParentCoherent cfg s) :
    ∃ D : GJointRunStep (P := P) cfg ccfg bls, D.preState = s ∧ D.block = b ∧ D.env? = env? ∧ D.postState = s' := by
  cases s with
  | pre s =>
    cases b with
    | pre b =>
      obtain ⟨rfl, hslot, j, hj, rfl⟩ := jointStepG_pre_ok_iff.mp h
      obtain ⟨t⟩ := nonempty_jointStepTrace hj bound
      exact ⟨.pre ⟨s, j, b, hslot, hj, t⟩, rfl, rfl, rfl, rfl⟩
    | gloas b =>
      obtain ⟨f, beacon, exec⟩ := s
      cases f with
      | fulu =>
        obtain ⟨h1, h2, upgraded, postSlots, post, hup, h0, hf, hr, hp, hd⟩ := jointStepG_cross_ok_iff.mp h
        obtain ⟨atFork, hat⟩ := crossFromFulu_upgrade hup
        rcases gloasDeliverOpt_ok_iff.mp hd with ⟨henv, rfl⟩ | ⟨e, req, postE, henv, hv, rfl⟩
        · exact ⟨.crossing ⟨beacon, exec, b, env?, atFork, upgraded, postSlots, post, .withheld, h1, h2, hup, hat,
            h0, hf, hr, hp, hd⟩, rfl, rfl, rfl, rfl⟩
        · exact ⟨.crossing ⟨beacon, exec, b, env?, atFork, upgraded, postSlots, post, .delivered e req postE, h1,
            h2, hup, hat, h0, hf, hr, hp, hd⟩, rfl, rfl, rfl, rfl⟩
      | _ =>
        rw [jointStepG_refuses_cross_of_ne_fulu (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])] at h
        cases h
  | gloas beacon exec parent =>
    cases b with
    | pre b => rw [jointStepG_refuses_gloas_pre] at h; cases h
    | gloas b =>
      obtain ⟨postSlots, post, exec', o, h0, hs, hp, hd⟩ := jointStepG_gloas_ok_iff.mp h
      obtain ⟨parent', rfl⟩ : ∃ parent', s' = .gloas post exec' parent' := by
        rcases gloasDeliverOpt_ok_iff.mp hd with ⟨-, rfl⟩ | ⟨e, req, postE, -, -, rfl⟩
        exacts [⟨_, rfl⟩, ⟨_, rfl⟩]
      obtain ⟨kept, hk, hspec⟩ : ∃ kept, KeptHistory cfg exec kept exec' ∧
          ((∃ env req post, o = .full env req post ∧
            ∃ b, kept = [b] ∧ b.block = payloadToBlockG req ∧ b.fork = .amsterdam) ∨
          ((o = .landed ∨ o = .empty) ∧ kept = [])) := by
        rcases settleParent_ok_iff.mp hs with
          ⟨-, env, req, _, rfl, -, rfl, rfl⟩ | ⟨-, rfl, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
        · obtain ⟨kb, hk1, hk2, hk3, hk4⟩ :=
            keptStep_of_engineVerdictG (coh : engineVerdictG cfg exec req = .ok exec')
          exact ⟨[kb], .step (blocks := []) (hk1 ▸ .refl) hk4, Or.inl ⟨env, req, exec', rfl, kb, rfl, hk2, hk3⟩⟩
        · exact ⟨[], .refl, Or.inr ⟨Or.inl rfl, rfl⟩⟩
        · exact ⟨[], .refl, Or.inr ⟨Or.inr rfl, rfl⟩⟩
      exact ⟨.gloas ⟨beacon, exec, parent, b, env?, postSlots, post, exec', parent', o, h0, hs, hp, hd, kept,
        hk, hspec⟩, rfl, rfl, rfl, rfl⟩

/-! ## Runs -/

/-- A Gloas joint run from `s₀`: run steps, each from the state the run has reached. Snoc-shaped, like
`JointRun`. -/
inductive GJointRun (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (s₀ : GJointState P) :
    GJointState P → Type
  | nil : GJointRun cfg ccfg bls s₀ s₀
  | snoc {s : GJointState P} : GJointRun cfg ccfg bls s₀ s → (D : GJointRunStep (P := P) cfg ccfg bls) →
      D.preState = s → GJointRun cfg ccfg bls s₀ D.postState

namespace GJointRun

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ : GJointState P}

/-- The steps of a run, in order. -/
def steps : {s : GJointState P} → GJointRun cfg ccfg bls s₀ s → List (GJointRunStep (P := P) cfg ccfg bls)
  | _, .nil => []
  | _, .snoc run D _ => run.steps ++ [D]

/-- The joint states of a run: its start, then each step's post-state. -/
def states {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) : List (GJointState P) :=
  s₀ :: run.steps.map GJointRunStep.postState

/-- The execution blocks the run builds upon, in order: each step's, in step order. -/
noncomputable def blocks {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) : List KeptBlock :=
  run.steps.flatMap GJointRunStep.kept

/-- The index into `run.blocks` at which step `j`'s built-upon blocks begin. -/
noncomputable def payloadIndex {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) (j : Nat) : Nat :=
  ((run.steps.take j).flatMap GJointRunStep.kept).length


theorem steps_snoc {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) (D : GJointRunStep (P := P) cfg ccfg bls)
    (hD : D.preState = s) : (run.snoc D hD).steps = run.steps ++ [D] := rfl

/-- The end of a run's last step is the run's end. -/
private theorem getElem?_append_singleton {α : Type} {l : List α} {x y : α} {i : Nat}
    (h : (l ++ [x])[i]? = some y) : l[i]? = some y ∨ (i = l.length ∧ x = y) := by
  by_cases hi : i < l.length
  · rw [List.getElem?_append_left hi] at h
    exact Or.inl h
  · rw [List.getElem?_append_right (by omega)] at h
    cases hk : i - l.length with
    | zero =>
      rw [hk, List.getElem?_cons_zero, Option.some.injEq] at h
      exact Or.inr ⟨by omega, h⟩
    | succ k =>
      rw [hk, List.getElem?_cons_succ, List.getElem?_nil] at h
      cases h

/-- **The run's execution side is one kept history** from the start's chain to the end's, over the run's
built-upon blocks. -/
theorem keptHistory : {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) →
    KeptHistory cfg s₀.exec run.blocks s.exec
  | _, .nil => .refl
  | _, .snoc run D hD => by
    have h := KeptHistory.append (keptHistory run) (hD ▸ D.keptHistory)
    simpa only [blocks, steps, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using h

/-- The end of a run is one of its states. -/
theorem end_mem_states : {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) → s ∈ run.states
  | _, .nil => List.mem_cons_self
  | _, .snoc run D _ => by
    simp only [states, steps, List.map_append, List.map_cons, List.map_nil]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))

/-- **The run's states are coherent** from a coherent start. -/
theorem coherent (h₀ : ParentCoherent cfg s₀) :
    {s : GJointState P} → GJointRun cfg ccfg bls s₀ s → ParentCoherent cfg s
  | _, .nil => h₀
  | _, .snoc _ D _ => D.postState_coherent

/-- Step `j` of a run splits its built-upon blocks: those before step `j` form a kept history from the start
to step `j`'s pre-state, then step `j`'s own, then those after, a kept history from step `j`'s post-state to
the run's end. Step `j`'s blocks begin at `run.payloadIndex j`. -/
theorem extendsBy : {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) → {j : Nat} →
    {D : GJointRunStep (P := P) cfg ccfg bls} → run.steps[j]? = some D →
    ∃ before after, run.blocks = before ++ D.kept ++ after ∧ before.length = run.payloadIndex j ∧
      KeptHistory cfg s₀.exec before D.preState.exec ∧ KeptHistory cfg D.postState.exec after s.exec
  | _, .nil, _, _, h => by simp only [steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run C hC, j, D, h => by
    rw [steps_snoc] at h
    rcases getElem?_append_singleton h with h | ⟨rfl, rfl⟩
    · obtain ⟨before, after, hb, hl, h1, h2⟩ := extendsBy run h
      have hj : j < run.steps.length := (List.getElem?_eq_some_iff.mp h).1
      refine ⟨before, after ++ C.kept, ?_, ?_, h1, KeptHistory.append h2 (hC ▸ C.keptHistory)⟩
      · simp only [blocks, steps, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [show run.steps.flatMap GJointRunStep.kept = run.blocks from rfl, hb]
        simp only [List.append_assoc]
      · rw [hl]
        simp only [payloadIndex, steps, List.take_append_of_le_length (Nat.le_of_lt hj)]
    · refine ⟨run.blocks, [], ?_, ?_, hC ▸ keptHistory run, .refl⟩
      · simp only [blocks, steps, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      · simp only [payloadIndex, steps, List.take_left', blocks]

end GJointRun

/-! ## Reachability -/

/-- States joined by successful joint steps. -/
inductive GJointReach (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (s₀ : GJointState P) :
    GJointState P → Prop
  | refl : GJointReach cfg ccfg bls s₀ s₀
  | step {s s' : GJointState P} (b : GBlock P) (env? : Option (Gloas.SignedExecutionPayloadEnvelope P)) :
      GJointReach cfg ccfg bls s₀ s → jointStepG cfg ccfg bls s b env? = .ok s' → GJointReach cfg ccfg bls s₀ s'

namespace GJointRun

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ : GJointState P}

/-- The end of a run is reachable from its start. -/
theorem reach : {s : GJointState P} → GJointRun cfg ccfg bls s₀ s → GJointReach cfg ccfg bls s₀ s
  | _, .nil => .refl
  | _, .snoc run D hD => .step D.block D.env? (hD ▸ reach run) D.ok

/-- The pre-state of every step of a run is reachable from its start. -/
theorem reach_pre : {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) → {j : Nat} →
    {D : GJointRunStep (P := P) cfg ccfg bls} → run.steps[j]? = some D → GJointReach cfg ccfg bls s₀ D.preState
  | _, .nil, _, _, h => by simp only [steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run C hC, _, D, h => by
    rw [steps_snoc] at h
    rcases getElem?_append_singleton h with h | ⟨-, rfl⟩
    · exact reach_pre run h
    · exact hC ▸ reach run

/-- The end of a run is reachable from the post-state of each of its steps. -/
theorem reach_post : {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) → {j : Nat} →
    {D : GJointRunStep (P := P) cfg ccfg bls} → run.steps[j]? = some D → GJointReach cfg ccfg bls D.postState s
  | _, .nil, _, _, h => by simp only [steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run C hC, _, D, h => by
    rw [steps_snoc] at h
    rcases getElem?_append_singleton h with h | ⟨-, rfl⟩
    · have r := reach_post run h
      exact .step C.block C.env? (hC ▸ r) C.ok
    · exact .refl

/-- Steps `i < j` of a run: step `j`'s pre-state is reachable from step `i`'s post-state. -/
theorem reach_post_pre : {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) → {i j : Nat} →
    {A C : GJointRunStep (P := P) cfg ccfg bls} → i < j → run.steps[i]? = some A → run.steps[j]? = some C →
    GJointReach cfg ccfg bls A.postState C.preState
  | _, .nil, _, _, _, _, _, h, _ => by simp only [steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run B hB, i, j, A, C, hij, hA, hC => by
    rw [steps_snoc] at hA hC
    rcases getElem?_append_singleton hC with hC | ⟨hj, rfl⟩
    · rcases getElem?_append_singleton hA with hA | ⟨hi, -⟩
      · exact reach_post_pre run hij hA hC
      · have := (List.getElem?_eq_some_iff.mp hC).1
        omega
    · rcases getElem?_append_singleton hA with hA | ⟨hi, -⟩
      · exact hB ▸ reach_post run hA
      · omega

end GJointRun

end Blanc
