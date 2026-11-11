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

end Blanc.JointGloasReplayStep
