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

end Blanc
