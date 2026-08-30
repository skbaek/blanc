-- ExecutionHistoryEffects.lean : contract-invariant configured-history facts.

import Blanc.ExecutionHistory

/-!
Contract-neutral facts about the configured block and chain-history carriers.

This is the history-level sibling of `ExecutionBodyEffects`: everything a
contract lift needs in order to enter one `ConfiguredBlockTrace`'s body, and to
carry an arbitrary `ContractSpec` invariant across a whole
`ConfiguredHistoryTrace`.  Each fact is stated once over an arbitrary
`c : ContractSpec` and an arbitrary validated schedule, rather than once per
contract or once per fork.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

variable {c : ContractSpec}

/-- Block preparation moves no value and creates no account: the environment
`applyBody` opens on carries the parent chain's own world state unchanged. -/
theorem ConfiguredBlockTrace.openingState
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    (initBenv trace.rules pre trace.block.header).state = pre.state := rfl

/-- Every block opens with an empty created-account set, so a not-yet-created
side condition is discharged afresh at each block and never has to be carried
across a block boundary. -/
theorem ConfiguredBlockTrace.not_mem_openingCreatedAccounts
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) (a : Adr) :
    a ∉ (initBenv trace.rules pre trace.block.header).createdAccounts :=
  AdrSet.not_mem_empty

/-- An arbitrary contract invariant at the parent chain state is already the
full body-entry environment invariant of the block that follows it. -/
theorem ConfiguredBlockTrace.openingBenvInv
    {cfg : ChainConfig} {pre post : BlockChain} {ca : Adr}
    (trace : ConfiguredBlockTrace cfg pre post)
    (inv : c.StateInv ca pre.state) :
    c.BenvInv ca (initBenv trace.rules pre trace.block.header) :=
  ⟨inv, trace.not_mem_openingCreatedAccounts ca⟩

/-- The block's retained balance-sum bound, read at the body-entry
environment where `applyBody`-level rungs ask for it. -/
theorem ConfiguredBlockTrace.openingBound
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    sum (initBenv trace.rules pre trace.block.header).state.bal +
      wdsum trace.block.wds < 2 ^ 256 :=
  trace.bound

/-- The post-chain of a configured block carries exactly the world its body
left; the appended block list and the chain identity are the only other
changes. -/
theorem ConfiguredBlockTrace.postState
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    post.state = trace.bodyState :=
  congrArg (fun chain : BlockChain => chain.state) trace.postEq

/-- Any contract invariant the ladder preserves survives a whole retained
configured history, at any validated schedule and across every activation that
history crosses. -/
theorem ConfiguredHistoryTrace.stateInv
    {cfg : ChainConfig} {checkpoint future : BlockChain} {ca : Adr}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (hp : c.Preserves ca) (inv : c.StateInv ca checkpoint.state) :
    c.StateInv ca future.state :=
  c.chainUsing_preserves_inv ca hp cfg checkpoint future
    history.toReachUsing inv

end ExecutionTrace

end Blanc
