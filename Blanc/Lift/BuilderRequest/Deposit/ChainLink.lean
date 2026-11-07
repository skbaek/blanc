import Blanc.Lift.BuilderRequest.ChainLink
import Blanc.Lift.BuilderRequest.Deposit.Delivery

/-!
# The deposit contract over a history

`history_delivers` is the public form: what the blocks output as builder deposit requests is a prefix of what the kept
frames submitted, in order. `history_chain` is the proof-level form, on which `delivery`, `excess_dynamics` and
`later_quote` apply.

Retention only: no gas or liveness claim.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune ChainLink
open Delivery (Chain systemOutput)
open Creation (address)

/-- The deposit contract's place in the chain link. -/
def linked : Linked contract 3 where
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
      history := by decide
      system := by decide }
  payload_ne := by decide
  ty_ne := by decide
  listed := by decide
  unlisted := fun f hf =>
    (by decide : ∀ f ∈ coveredForks, ∀ p ∈ f.ruleSet.requests, p.1 ≠ 3 ∧ p.2 ≠ address) f hf

/-- The records a history's kept frames at the contract submit, in order: a frame with the submission's calldata
length gives its record. -/
def submitted (blocks : List KeptBlock) : List Record :=
  (History.kept address blocks).filterMap fun f =>
    if h : f.sevm.data.length = 184 then some (recordOf f.sevm h) else none

/-- **Builder deposit requests come out in order.** The bytes the blocks output as type 3 requests are a prefix of the
records the kept frames submitted, each in its output form, in order. -/
def DeliversInOrder (blocks : List KeptBlock) : Prop :=
  delivered 3 blocks <+: (submitted blocks).flatMap Record.out

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

/-- **The proof-level form.** From the deployed storage, the frames a history keeps at the contract are a chain of the
delivery sequence, one for one, whose output is the blocks' type 3 requests. So `delivery`, `excess_dynamics` and
`later_quote` hold of the history. -/
theorem history_chain (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (data : History.DataWords blocks) :
    ∃ frames : List Frame, Chain Stor.empty frames (stop.state.getStor address) ∧
      Corresponds contract frames (History.kept address blocks) ∧ systemOutput frames = delivered 3 blocks := by
  have := ChainLink.history_chain linked h installed noSystemCode senders authorities creates data
  rw [show start.state.getStor contract.address = Stor.empty from fresh] at this
  exact this

/-- **Exact delivery over a history at the deposit contract.** From the code at its address on the deployed storage,
what the blocks output as type 3 requests is a prefix of what the kept frames submitted, in order. `budget` is the word
range: all the value the kept frames at the contract carry is at most `2 ^ 256` wei, far above all the ether that
exists, and each submission carries at least 1 ETH (`range_of_budget`). -/
theorem history_delivers (h : KeptHistory cfg start blocks stop) (installed : start.state.getCode address = code)
    (fresh : start.state.getStor address = Stor.empty)
    (noSystemCode : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (data : History.DataWords blocks)
    (budget : History.paid address blocks ≤ 2 ^ 256) : DeliversInOrder blocks := by
  obtain ⟨frames, chain, corr, out⟩ := history_chain h installed fresh noSystemCode senders authorities creates data
  obtain ⟨-, -, output⟩ := delivery_of_budget chain (corr.value_le.trans budget)
  have hsub : Delivery.submissions frames = submitted blocks := corr.submissions
  rw [hsub, out] at output
  unfold DeliversInOrder
  rw [output]
  exact take_flatMap_prefix _ _ _

end Blanc.Lift.BuilderRequest.Deposit
