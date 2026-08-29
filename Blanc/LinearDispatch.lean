import Blanc.CommonCore

/-!
  Contract-neutral linear selector dispatch.

  Multiple runtimes use this exact structured dispatcher.  Keeping the
  definition here prevents compiler-shape and selector-route proofs from
  silently drifting apart.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

def linearDispatchWith (fallback : Nat) : List (B256 × Func) → Func
  | [] => .call fallback
  | [(word, body)] =>
      pushB256 word ::: eq ::: (body <?> .call fallback)
  | (word, body) :: rest =>
      dup 0 ::: pushB256 word ::: eq :::
        ((pop ::: body) <?> linearDispatchWith fallback rest)

def selectorUnique (entries : List (B256 × Func)) : Prop :=
  entries.Pairwise (fun a b => a.1 ≠ b.1)

end Blanc
