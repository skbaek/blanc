import Blanc.ExecutionKeptChain

/-!
# A kept history clean of SYSTEM_ADDRESS

Three per-block premises about `SYSTEM_ADDRESS` over a kept history: no kept block's transaction is sent by
it, no authorization recovers to it, and no kept frame creates at it. With no code there at the start, these
keep every frame with the system caller to the block's own request-phase call, so only that call can dequeue
a request contract. Contract-neutral: the EIP-8282 builder contracts and EIP-7251 state their kept-history
headlines over it.
-/

namespace Blanc

open Jaune

/-- No transaction sent by `SYSTEM_ADDRESS`, no authorization recovering to it, no frame creating at it. -/
structure HistoryClean (blocks : List KeptBlock) : Prop where
  /-- No kept block recovers the system address as a sender. -/
  senders : ∀ b ∈ blocks, NoSenderAt systemAddress b.run.senders
  /-- No kept block carries its authority. -/
  authorities : ∀ b ∈ blocks, NoAuthorityAt systemAddress b.run.senders
  /-- No kept block creates it. -/
  creates : ∀ b ∈ blocks, NoCreateAt systemAddress b.run.roots

/-- Mainnet's schedule names no Amsterdam activation, so every kept mainnet block is at a covered fork. -/
theorem KeptHistory.mainnet_covered {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory mainnetChainConfig checkpoint blocks final) : ∀ b ∈ blocks, CoveredFork b.fork := by
  intro b hb
  obtain ⟨_, step⟩ := history.mem_step b hb
  rcases step.kept with covered | amsterdam
  · exact covered
  · have mem := ChainConfig.forkAt_mem step.forkAt
    rw [amsterdam] at mem
    exact absurd mem (by decide +kernel)

end Blanc
