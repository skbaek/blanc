import Blanc.Lift.Token.Core

/-!
# Token interface facet: no forwarded caller into a booked entry

A separate, instance-owned facet over a `Core`: every `IsEntry T` child of a settled non-static
frame at `T` is called by `T` itself, so no DELEGATECALL/CALLCODE into `T`'s own address carries a
foreign caller into a booked entry.  Contract-neutral.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace

/-- **Facet: the token never re-enters its own entry with a forwarded caller.**  Every `IsEntry T`
child of a settled non-static frame at `T` is called by `T` itself (no DELEGATECALL/CALLCODE into
`T`'s own address carries a foreign caller into a booked entry). -/
structure SelfCaller {T : Adr} {B : Book} (C : Core T B) : Prop where
  child_caller : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), C.Hist tr →
      ∀ G ∈ tr.settledFrames, G.sevm.currentTarget = T → G.sevm.isStatic = false →
        ∀ c ∈ Exec.childFrames G.run, IsEntry T c → c.sevm.caller = T

end Blanc.Lift.Token
