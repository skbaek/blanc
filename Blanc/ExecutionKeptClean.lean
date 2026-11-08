import Blanc.ExecutionKeptChain

/-!
# A kept history clean of SYSTEM_ADDRESS

The three per-block premises every request-contract history theorem takes about `SYSTEM_ADDRESS`: no kept
block's transaction is sent by it, no authorization recovers to it, and no kept frame creates at it. With
no code there at the start, these are what keep a user frame from ever running as the system caller.
Contract-neutral: the EIP-8282 builder contracts and EIP-7251 state their history headlines over it.
-/

namespace Blanc

open Jaune

/-- No system-caller, no authority, no created-address frames: the O19 premises. -/
structure HistoryClean (blocks : List KeptBlock) : Prop where
  /-- No kept block recovers the system address as a sender. -/
  senders : ∀ b ∈ blocks, NoSenderAt systemAddress b.run.senders
  /-- No kept block carries its authority. -/
  authorities : ∀ b ∈ blocks, NoAuthorityAt systemAddress b.run.senders
  /-- No kept block creates it. -/
  creates : ∀ b ∈ blocks, NoCreateAt systemAddress b.run.roots

end Blanc
