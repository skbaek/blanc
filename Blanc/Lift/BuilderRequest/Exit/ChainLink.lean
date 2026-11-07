import Blanc.Lift.BuilderRequest.ChainLink
import Blanc.Lift.BuilderRequest.Exit.Delivery

/-!
# The exit contract over a history

`history_delivers` is the public form: what the blocks output as builder exit requests is a prefix of what the kept
frames submitted, in order. `history_chain` is the proof-level form, on which `delivery`, `excess_dynamics` and
`later_quote` apply.

Retention only: no gas or liveness claim.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune ChainLink
open Delivery (Chain systemOutput)
open Creation (address)

/-- The exit contract's place in the chain link. -/
def linked : Linked contract 4 where
  frames := frames
  code_eq := rfl
  classify := fun law => by
    cases law with
    | submission i o effect => exact .inl ⟨i, o, effect⟩
    | feeRead i o empty effect => exact .inr ⟨empty, i, o, effect⟩
  runnable := ⟨by decide +kernel, by decide +kernel⟩
  placed :=
    { precompile := KeptFork.forall (by decide) (by decide)
      beacon := by decide
      history := by decide }
  payload_ne := by decide
  ty_ne := by decide
  listed := by decide
  unlisted := fun f hf =>
    (by decide : ∀ f ∈ coveredForks, ∀ p ∈ f.ruleSet.requests, p.1 ≠ 4 ∧ p.2 ≠ address) f hf

/-- The records a history's kept frames at the contract submit, in order: a frame with the submission's calldata
length gives its record, the frame's caller as the source. -/
def submitted (blocks : List KeptBlock) : List Record :=
  (History.kept address blocks).filterMap fun f =>
    if h : f.sevm.data.length = 48 then some (recordOf f.sevm h) else none

/-- **Builder exit requests come out in order.** The bytes the blocks output as type 4 requests are a prefix of the
records the kept frames submitted, each in its output form, in order. -/
def DeliversInOrder (blocks : List KeptBlock) : Prop :=
  delivered 4 blocks <+: (submitted blocks).flatMap Record.out

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

/-- **The proof-level form.** From the deployed storage, the frames a history keeps at the contract are a chain of the
delivery sequence, one for one, whose output is the blocks' type 4 requests. So `delivery`, `excess_dynamics` and
`later_quote` hold of the history. -/
theorem history_chain (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) :
    ∃ frames : List Frame, Chain deployedStorage frames (stop.state.getStor address) ∧
      Corresponds contract frames (History.kept address blocks) ∧ systemOutput frames = delivered 4 blocks := by
  have := ChainLink.history_chain linked h installed noSystemCode senders authorities creates
  rw [show start.state.getStor contract.address = deployedStorage from fresh] at this
  exact this

/-- **Exact delivery over a history at the exit contract.** From the code at its address on the deployed storage, what
the blocks output as type 4 requests is a prefix of what the kept frames submitted, in order. `few` is the word range,
stated on the count: a submission's fee can be 1 wei, so no budget of value below `2 ^ 256` bounds it. -/
theorem history_delivers (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = deployedStorage)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks)
    (few : (submitted blocks).length ≤ 2 ^ 64) : DeliversInOrder blocks := by
  obtain ⟨frames, chain, corr, out⟩ := history_chain h installed fresh noSystemCode senders authorities creates
  have hsub : Delivery.submissions frames = submitted blocks := corr.submissions
  obtain ⟨-, -, output⟩ := delivery chain (by rw [hsub]; omega)
  rw [hsub, out] at output
  unfold DeliversInOrder
  rw [output]
  exact take_flatMap_prefix _ _ _

end Blanc.Lift.BuilderRequest.Exit
