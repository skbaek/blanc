import Blanc.Lift.BuilderRequest.Carrier
import Blanc.Lift.WithdrawalRequest.JointHistory

/-!
# The builder contracts' `Clean` premises on a joint history spliced at the Gloas crossing

A Gloas joint run's execution side is the EIP-7002 joint history up to the crossing (a configured history, the
`ValidJoint` shape: a deployment-rooted checkpoint, its admission, the pre-anchor trace and the pre-crossing run),
followed by Amsterdam kept steps. `ConfiguredHistoryTrace.splice` makes it one kept history, `v.history.kept ++ ys`.

* `JointRun.toExec_kept`: the kept blocks of a joint run's execution history are the pre-anchor history's, then each
  step's own block, in step order.
* `ValidJoint.depositClean`, `ValidJoint.exitClean`: what the builder contracts' `Clean` needs at the checkpoint and
  along the spliced history, given a valid EIP-7002 joint chain. The history and the system address's empty code
  come from the joint chain (its deployment history and admission), and so do the sender and authorization premises
  along its own blocks; the builder contract's code and fresh storage at the checkpoint, the creation and value
  (deposit) or count (exit) premises along the kept blocks, and the sender and authorization premises along the later
  blocks, are the explicit
  hypotheses: nothing in the EIP-7002 shape supplies them.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace ChainLink Blanc.Lift.WithdrawalRequest

/-- **The joint run's kept blocks.** The kept history of a joint run's execution history is the pre-anchor history's
kept blocks followed by each step's own block, in step order. -/
theorem JointRun.toExec_kept {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ s : JointState P}
    {checkpoint : BlockChain} (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec)
    (run : JointRun cfg ccfg bls s₀ s) :
    (run.toExec pre).kept = pre.kept ++ run.steps.map fun step => step.stepTrace.trace.kept := by
  induction run with
  | nil => simp only [JointRun.toExec_nil, JointRun.steps_nil, List.map_nil, List.append_nil]
  | snoc run b step bound ih =>
      rw [JointRun.toExec_snoc, JointRun.steps_snoc, List.map_append, ← List.append_assoc, ← ih]
      rfl

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint stop : BlockChain}
  {anchor final : JointState P} {ys : List KeptBlock}

/-- The joint chain's sender premise covers its kept blocks; with the later blocks', the spliced history's. -/
theorem ValidJoint.noSender (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    (later : History.NoSender systemAddress ys) : History.NoSender systemAddress (v.history.kept ++ ys) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact v.history.kept_noSender v.senders b hb
  · exact later b hb

/-- The joint chain's authorization premise covers its kept blocks; with the later blocks', the spliced history's. -/
theorem ValidJoint.noAuthority (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    (later : History.NoAuthority systemAddress ys) : History.NoAuthority systemAddress (v.history.kept ++ ys) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact v.history.kept_noAuthority v.authorities b hb
  · exact later b hb

/-- **The deposit contract's `Clean` on a spliced joint history.** A valid EIP-7002 joint chain to `final`, followed
by kept steps from `final`'s execution chain, satisfies the deposit contract's `Clean` given the deposit contract's
code and fresh storage at the checkpoint, the creation and value premises along the kept blocks, and the sender and
authorization premises along the later blocks. The system address's empty code at the checkpoint comes from the joint
chain's deployment history and admission, and the sender and authorization premises along its own blocks from its
own. -/
theorem ValidJoint.depositClean (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    (later : KeptHistory cfg final.exec ys stop)
    (installed : checkpoint.state.getCode Deposit.Creation.address = Deposit.code)
    (fresh : checkpoint.state.getStor Deposit.Creation.address = Stor.empty)
    (senders : History.NoSender systemAddress ys)
    (authorities : History.NoAuthority systemAddress ys)
    (creates : History.NoCreate systemAddress (v.history.kept ++ ys))
    (budget : History.paid Deposit.Creation.address (v.history.kept ++ ys) ≤ 2 ^ 256) :
    Deposit.Indexed.Clean cfg checkpoint (v.history.kept ++ ys) stop :=
  ⟨v.history.splice later, installed, fresh, (v.deployment.initialized v.admission).systemEmpty,
    ValidJoint.noSender v senders, ValidJoint.noAuthority v authorities, creates, budget⟩

/-- **The exit contract's `Clean` on a spliced joint history**, as `ValidJoint.depositClean`, with the exit contract's
deployed storage at the checkpoint and at most `2 ^ 64` exit submissions in place of the value bound. -/
theorem ValidJoint.exitClean (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    (later : KeptHistory cfg final.exec ys stop)
    (installed : checkpoint.state.getCode Exit.Creation.address = Exit.code)
    (fresh : checkpoint.state.getStor Exit.Creation.address = Exit.deployedStorage)
    (senders : History.NoSender systemAddress ys)
    (authorities : History.NoAuthority systemAddress ys)
    (creates : History.NoCreate systemAddress (v.history.kept ++ ys))
    (few : (History.submitted Exit.contract (v.history.kept ++ ys)).length ≤ 2 ^ 64) :
    Exit.Indexed.Clean cfg checkpoint (v.history.kept ++ ys) stop :=
  ⟨v.history.splice later, installed, fresh, (v.deployment.initialized v.admission).systemEmpty,
    ValidJoint.noSender v senders, ValidJoint.noAuthority v authorities, creates, few⟩

end Blanc.Lift.BuilderRequest
