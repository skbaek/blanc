import Blanc.JointGloasHistory

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
  cases s <;> cases b <;> dsimp only [PreBound] <;> infer_instance

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

end Blanc.JointGloasReplayStep
