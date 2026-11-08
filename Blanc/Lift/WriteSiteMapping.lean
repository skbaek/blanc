import Blanc.Lift.WriteSiteReachHistory

/-!
# Which certified write sites may touch a one-level mapping

A write-site certificate lists every root site of a code (`wsRoot`). `mappingSites b` keeps the
sites that may write an entry of the solc mapping at base slot `b` by their shape: a site named
`keccak256(key ‖ b)`, or a `top` site, whose slot the checker does not follow.
`successfulSstore_mappingSite` reads `successfulSstore_site` through that filter. Its reach is that
theorem's premises: `root` is a frame entered at `pc = 0` whose code is the certified code (the
frame's storage owner is not constrained, so a delegatecall frame qualifies), the fork lane has
`stateGas = none`, and `node` is on `root`'s own same-frame `ParentPrefix`. For that `node` a table
proved equal to `mappingSites b (wsRoot ann)` covers its successful store, even if the frame later
reverts. Stores in child frames are not covered by this statement; each needs its own `root`.

What this does not give. A site of another shape names a known slot; that it is apart from a given
entry is hash freshness, for the consumer. Only `nonInc` speaks of a write's value: a site without
it may decrease, keep or increase its slot, so a credit is never certified here. A `top` site says
nothing about its slot. Contract-neutral: no address, base or selector is fixed here.
-/

namespace Blanc.Lift.WriteSite

open Jaune

/-- How a balance-table row reads its site. This is the table's reading of the source and the
named role, not a certified authority check; `BalanceRow.shapeOk` decides only the shape it states.
Nothing ties a site's `nonInc` flag to the label: a `recipient` row is not certified to credit, and
an `allowance` or `signed` row is not required to carry `nonInc`. -/
inductive BalancePath : Type
  /-- The entry is the frame caller's own. -/
  | holder
  /-- The entry is a calldata-named recipient's; the source credits it. -/
  | recipient
  /-- The entry is a calldata-named holder's, debited on the caller's allowance (or its own). -/
  | allowance
  /-- The entry is a calldata-named holder's, debited on the holder's signature. -/
  | signed
  /-- A write under a role check the source states. -/
  | operator (role : String)
  /-- An initializer's write. -/
  | initializer
  /-- A `top` site: the certificate fixes the selector and not the slot; `why` is the source's
  reading of the slot, which no certificate here checks. -/
  | unresolved (why : String)

end Blanc.Lift.WriteSite
