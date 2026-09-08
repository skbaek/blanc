-- Contract-neutral source-syntax instruction counts.

import Blanc.CommonCore

namespace Blanc

open Jaune

/-- Count instruction nodes in a source function that satisfy `predicate`.
Internal calls are represented by `Func.call` leaves and therefore contribute
no instruction node of their own. -/
def Func.sourceSiteCount (predicate : Ninst → Bool) : Func → Nat
  | .last _ => 0
  | .next instruction rest =>
      (if predicate instruction then 1 else 0) +
        Func.sourceSiteCount predicate rest
  | .branch left right =>
      Func.sourceSiteCount predicate left +
        Func.sourceSiteCount predicate right
  | .call _ => 0

end Blanc
