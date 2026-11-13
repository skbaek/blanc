import Blanc.JointGloasHistory
import Blanc.ConcreteRunKept

/-! Computational success certificates for the original Gloas joint step. -/
namespace Blanc.JointGloasReplayStep

open Jaune JauneConsensus

variable {P : Preset}

/-- The exact successful post-state and equation of the original interpreter. -/
def replay (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (s : GJointState P) (b : GBlock P)
    (env? : Option (Gloas.SignedExecutionPayloadEnvelope P)) :
    Option {post : GJointState P // jointStepG cfg ccfg bls s b env? = .ok post} :=
  match _h : jointStepG cfg ccfg bls s b env? with
  | .error _ => none
  | .ok post => some ⟨post, rfl⟩

/-- A returned certificate constructs a run step with exactly the original premises. -/
theorem sound {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s : GJointState P} {b : GBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    (cert : {post : GJointState P // jointStepG cfg ccfg bls s b env? = .ok post})
    (bound : PreBound s b) (coherent : ParentCoherent cfg s) :
    ∃ D : GJointRunStep (P := P) cfg ccfg bls,
      D.preState = s ∧ D.block = b ∧ D.env? = env? ∧ D.postState = cert.val :=
  GJointRunStep.exists_of_jointStepG cert.property bound coherent

/-- One original joint-step input, retaining both the beacon block and its optional envelope. -/
abbrev Input (P : Preset) := GBlock P × Option (Gloas.SignedExecutionPayloadEnvelope P)

/-- An existing run with exactly the supplied input sequence and intermediate states,
including every envelope position and the anchor state.
This predicate adds no execution carrier and assumes no successful transition. -/
def Admits (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (origin final : GJointState P) (inputs : List (Input P))
    (states : List (GJointState P)) : Prop :=
  ∃ run : GJointRun cfg ccfg bls origin final,
    run.steps.map (fun D => (D.block, D.env?)) = inputs ∧ run.states = states

private def boundDecidable (s : GJointState P) (b : GBlock P) : Decidable (PreBound s b) := by
  cases s with
  | pre s =>
    cases b with
    | pre b =>
      exact decidable_of_iff
        (footprintSum s.exec.state.keys s.exec.state.bal + wdsum (payloadWithdrawals b) < 2 ^ 256)
        (by rw [State.footprintSum_eq_sum]; rfl)
    | gloas _ => exact isTrue True.intro
  | gloas => cases b <;> exact isTrue True.intro

/-- The execution block a successful joint step builds upon, if any. This
reads the original request converter, slots transition and parent settlement;
crossing and non-FULL settlement contribute no built-upon payload. -/
def builtBlock? (ccfg : Config) (bls : Bool) : GJointState P → GBlock P → Option (Option Block)
  | .pre _, .pre b =>
      match NewPayloadRequest.ofBlock b.2.message with
      | .error _ => none
      | .ok req => some (some (payloadToBlock req))
  | .pre _, .gloas _ => some none
  | .gloas beacon exec parent, .gloas b =>
      match Gloas.processSlots (gloasCtx ccfg bls) beacon b.message.slot with
      | .error _ => none
      | .ok slots =>
          match settleParent parent exec (parentFull slots b.message) b.message.body.parent_execution_requests with
          | .error _ => none
          | .ok (_, .full _ req _) => some (some (payloadToBlockG req))
          | .ok (_, _) => some none
  | .gloas .., .pre _ => none

/-- The computed built-upon block is exactly the block in the original step's
kept history. No delivered-but-not-built-upon envelope is included. -/
theorem builtBlock_spec {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GJointRunStep (P := P) cfg ccfg bls) :
    ∃ block, builtBlock? ccfg bls D.preState D.block = some block ∧
      D.kept.map KeptBlock.block = block.toList := by
  cases D with
  | pre D =>
      refine ⟨some (payloadToBlock D.stepTrace.req), ?_, ?_⟩
      · simp only [builtBlock?, GJointRunStep.preState, GJointRunStep.block, D.stepTrace.ofBlock]
      · change [D.stepTrace.trace.block] = [payloadToBlock D.stepTrace.req]
        rw [D.stepTrace.block_eq]
  | crossing D => exact ⟨none, rfl, rfl⟩
  | gloas D =>
      rcases D.keptSpec with ⟨env, req, post, settled, b, blocks, block, -⟩ | ⟨settled, blocks⟩
      · refine ⟨some (payloadToBlockG req), ?_, ?_⟩
        · simp only [builtBlock?, GJointRunStep.preState, GJointRunStep.block, D.slots, D.settleOk, settled]
        · change D.kept.map KeptBlock.block = [payloadToBlockG req]
          rw [blocks]
          simp only [List.map_cons, List.map_nil, block]
      · refine ⟨none, ?_, ?_⟩
        · rcases settled with landed | empty
          · simp only [builtBlock?, GJointRunStep.preState, GJointRunStep.block, D.slots, D.settleOk, landed]
          · simp only [builtBlock?, GJointRunStep.preState, GJointRunStep.block, D.slots, D.settleOk, empty]
        · change D.kept.map KeptBlock.block = []
          rw [blocks]
          rfl

/-- An original joint step with exactly the retained blocks computed by replay. -/
def StepAdmits (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (state post : GJointState P) (block : GBlock P)
    (env? : Option (Gloas.SignedExecutionPayloadEnvelope P)) (kept : List KeptBlock) : Prop :=
  ∃ D : GJointRunStep (P := P) cfg ccfg bls,
    D.preState = state ∧ D.block = block ∧ D.env? = env? ∧ D.postState = post ∧ D.kept = kept

private theorem stepAdmits_of_history {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {state : GJointState P} {block : GBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {kept : List KeptBlock} {exec : BlockChain}
    (cert : {post : GJointState P // jointStepG cfg ccfg bls state block env? = .ok post})
    (bound : PreBound state block) (coherent : ParentCoherent cfg state) {built : Option Block}
    (computed : builtBlock? ccfg bls state block = some built)
    (history : KeptHistory cfg state.exec kept exec) (mapped : kept.map KeptBlock.block = built.toList) :
    StepAdmits cfg ccfg bls state cert.val block env? kept := by
  obtain ⟨D, hp, hb, he, ho⟩ := sound cert bound coherent
  obtain ⟨expected, produced, blocks⟩ := builtBlock_spec D
  rw [hp, hb, computed] at produced
  obtain rfl := Option.some.inj produced
  have original := D.keptHistory
  rw [hp] at original
  have same := (original.unique history (blocks.trans mapped.symm)).1
  exact ⟨D, hp, hb, he, ho, same⟩

/-- Replay an original joint step and reconstruct the exact built-upon kept
blocks. Original history uniqueness binds the computed body derivations to
the original run, rather than choosing ghost data for a runtime checker. -/
def replayKeptStep (depth : Nat) (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (state : GJointState P) (block : GBlock P)
    (env? : Option (Gloas.SignedExecutionPayloadEnvelope P)) (coherent : ParentCoherent cfg state) :
    Option {out : GJointState P × List KeptBlock //
      StepAdmits cfg ccfg bls state out.1 block env? out.2} :=
  letI := boundDecidable state block
  if bound : PreBound state block then do
    let cert ← replay cfg ccfg bls state block env?
    match computed : builtBlock? ccfg bls state block with
    | none => none
    | some none => pure ⟨(cert.val, []), stepAdmits_of_history cert bound coherent computed .refl rfl⟩
    | some (some built) =>
        let ⟨post, b, parentEq, blockEq, step⟩ ← ConcreteRun.deriveKept depth cfg state.exec built
        have history : KeptHistory cfg state.exec [b] post :=
          .step (blocks := []) (by rw [parentEq]; exact .refl) step
        pure ⟨(cert.val, [b]), stepAdmits_of_history cert bound coherent computed history
          (by simp only [List.map_cons, List.map_nil, blockEq, Option.toList_some])⟩
  else none

private theorem extend {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {origin state : GJointState P} {seen : List (Input P)}
    {states : List (GJointState P)} {input : Input P}
    (accepted : Admits cfg ccfg bls origin state seen states)
    (cert : {post : GJointState P //
      jointStepG cfg ccfg bls state input.1 input.2 = .ok post})
    (bound : PreBound state input.1) (coherent : ParentCoherent cfg state) :
    Admits cfg ccfg bls origin cert.val (seen ++ [input]) (states ++ [cert.val]) ∧
      ParentCoherent cfg cert.val := by
  obtain ⟨D, hpre, hblock, henv, hpost⟩ := sound cert bound coherent
  obtain ⟨run, hrun, hstates⟩ := accepted
  have extended : Admits cfg ccfg bls origin D.postState (seen ++ [input])
      (states ++ [D.postState]) := by
    refine ⟨run.snoc D hpre, ?_, ?_⟩
    · simp only [GJointRun.steps_snoc, List.map_append, List.map_cons, List.map_nil,
        hrun, hblock, henv]
    · rw [← hstates]
      simp only [GJointRun.states, GJointRun.steps_snoc, List.map_append, List.map_cons,
        List.map_nil, List.cons_append]
  exact ⟨hpost ▸ extended, hpost ▸ D.postState_coherent⟩

/-- A successful prefix is kept only when the entire remaining input list succeeds.
The original interpreter executes once per step; run witnesses and coherence proofs are erased.
The extra pre-Gloas balance bound is checked computationally rather than assumed at each step. -/
private def replaySuffix (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    {origin state : GJointState P} (seen : List (Input P))
    (states : List (GJointState P)) (accepted : Admits cfg ccfg bls origin state seen states)
    (coherent : ParentCoherent cfg state) :
    (todo : List (Input P)) →
      Option {out : GJointState P × List (GJointState P) //
        Admits cfg ccfg bls origin out.1 (seen ++ todo) out.2}
  | [] => some ⟨(state, states), by simpa only [List.append_nil] using accepted⟩
  | input :: rest =>
    letI := boundDecidable state input.1
    if bound : PreBound state input.1 then
      match replay cfg ccfg bls state input.1 input.2 with
      | none => none
      | some cert =>
        have extended := extend accepted cert bound coherent
        (replaySuffix cfg ccfg bls (seen ++ [input]) (states ++ [cert.val])
          extended.1 extended.2 rest).map
          (fun result => ⟨result.val, by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.property⟩)
    else none

/-- Replay a finite sequence through the original joint interpreter, returning a certificate
for one `GJointRun` with exactly those block/envelope inputs. A failed step rejects the whole
sequence. Initial delivered-payload coherence remains an explicit premise; it is trivial for
a pre-Gloas anchor. This checks neither the other `ValidJointG` fields nor nontrivial activity. -/
def replayMany (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (state : GJointState P) (coherent : ParentCoherent cfg state) (inputs : List (Input P)) :
    Option {out : GJointState P × List (GJointState P) //
      Admits cfg ccfg bls state out.1 inputs out.2} :=
  replaySuffix cfg ccfg bls (origin := state) (state := state) [] [state]
    ⟨.nil, rfl, rfl⟩ coherent inputs

/-- The P5 replay entry from a pre-Gloas anchor always uses real BLS. It supplies the initial
coherence proof internally; no caller-selected BLS switch or assumed successful trace is used.
A nonempty accepted input and the remaining applicability fields are still separate obligations. -/
def replayFromPre (cfg : ChainConfig) (ccfg : Config) (state : JointState P)
    (inputs : List (Input P)) :
    Option {out : GJointState P × List (GJointState P) //
      Admits cfg ccfg true (.pre state) out.1 inputs out.2} :=
  replayMany cfg ccfg true (.pre state) True.intro inputs

/-- An original run with exact inputs, intermediate states and computed
retained blocks, including every original interpreter derivation. -/
def AdmitsKept (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (origin final : GJointState P) (inputs : List (Input P))
    (states : List (GJointState P)) (blocks : List KeptBlock) : Prop :=
  ∃ run : GJointRun cfg ccfg bls origin final,
    run.steps.map (fun D => (D.block, D.env?)) = inputs ∧ run.states = states ∧ run.blocks = blocks

private theorem extendKept {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {origin state : GJointState P} {seen : List (Input P)} {states : List (GJointState P)}
    {blocks : List KeptBlock} {input : Input P}
    (accepted : AdmitsKept cfg ccfg bls origin state seen states blocks)
    (cert : {out : GJointState P × List KeptBlock //
      StepAdmits cfg ccfg bls state out.1 input.1 input.2 out.2}) :
    AdmitsKept cfg ccfg bls origin cert.val.1 (seen ++ [input]) (states ++ [cert.val.1])
      (blocks ++ cert.val.2) ∧ ParentCoherent cfg cert.val.1 := by
  obtain ⟨D, hp, hb, he, ho, hk⟩ := cert.property
  obtain ⟨run, inputs, priorStates, priorBlocks⟩ := accepted
  have extended : AdmitsKept cfg ccfg bls origin D.postState (seen ++ [input])
      (states ++ [D.postState]) (blocks ++ D.kept) := by
    refine ⟨run.snoc D hp, ?_, ?_, ?_⟩
    · simp only [GJointRun.steps_snoc, List.map_append, List.map_cons, List.map_nil, inputs, hb, he]
    · rw [← priorStates]
      simp only [GJointRun.states, GJointRun.steps_snoc, List.map_append, List.map_cons,
        List.map_nil, List.cons_append]
    · change (run.steps ++ [D]).flatMap GJointRunStep.kept = blocks ++ D.kept
      rw [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      change run.blocks ++ D.kept = blocks ++ D.kept
      rw [priorBlocks]
  rw [ho, hk] at extended
  exact ⟨extended, ho ▸ D.postState_coherent⟩

private def replayKeptSuffix (depth : Nat) (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    {origin state : GJointState P} (seen : List (Input P)) (states : List (GJointState P))
    (blocks : List KeptBlock) (accepted : AdmitsKept cfg ccfg bls origin state seen states blocks)
    (coherent : ParentCoherent cfg state) : (todo : List (Input P)) →
      Option {out : GJointState P × List (GJointState P) × List KeptBlock //
        AdmitsKept cfg ccfg bls origin out.1 (seen ++ todo) out.2.1 out.2.2}
  | [] => some ⟨(state, states, blocks), by simpa only [List.append_nil] using accepted⟩
  | input :: rest => do
      let cert ← replayKeptStep depth cfg ccfg bls state input.1 input.2 coherent
      have extended := extendKept accepted cert
      let result ← replayKeptSuffix depth cfg ccfg bls (seen ++ [input]) (states ++ [cert.val.1])
        (blocks ++ cert.val.2) extended.1 extended.2 rest
      pure ⟨result.val, by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.property⟩

/-- Replay real-BLS joint steps from a pre-Gloas anchor and compute their
exact built-upon retained blocks. The entire sequence rejects if any original
step, body, fork-coverage check or derivation branch fails. This does not yet
check the remaining clean/value/configuration fields of `ValidJointG`. -/
def replayFromPreKept (depth : Nat) (cfg : ChainConfig) (ccfg : Config) (state : JointState P)
    (inputs : List (Input P)) :
    Option {out : GJointState P × List (GJointState P) × List KeptBlock //
      AdmitsKept cfg ccfg true (.pre state) out.1 inputs out.2.1 out.2.2} :=
  replayKeptSuffix depth cfg ccfg true (origin := .pre state) (state := .pre state) [] [.pre state] []
    ⟨.nil, rfl, rfl, rfl⟩ True.intro inputs

end Blanc.JointGloasReplayStep
