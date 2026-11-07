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

/-- The key term of a slot term `keccak256(key ‖ b)`. -/
def mappingKey? (b : B256) : Term → Option Term
  | .kecc k (.const c) => if c = b then some k else none
  | _ => none

/-- The site may write an entry of the mapping at base `b`, by its shape. -/
def Site.mayHitMapping (b : B256) (s : Site) : Bool :=
  !s.slot.known || (mappingKey? b s.slot).isSome

/-- The listed sites that may write an entry of the mapping at base `b`. -/
def mappingSites (b : B256) (sites : List Site) : List Site :=
  sites.filter (Site.mayHitMapping b)

/-- **A successful store meets a mapping site or a known slot of another shape**, for a `node` on
the same-frame `ParentPrefix` of a `root` entered at `pc = 0`, running the certified code, on a
lane with `stateGas = none`. -/
theorem successfulSstore_mappingSite (b : B256) {code : ByteArray} {c : Cert} {ann : List WAnn}
    (checked : Cert.check code c = true) (certified : wsCert c ann = true)
    {root node : Exec.Deriv} (pc : root.pc = 0) (hcode : root.sevm.code = code)
    (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ site ∈ wsRoot ann,
      (∀ guard ∈ site.guards, guard.1.Den (Env.root root.sevm) guard.2) ∧
      (site.nonInc = true →
        write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat) ∧
      (site ∈ mappingSites b (wsRoot ann) ∧ site.slot.Den (Env.root root.sevm) write.key ∨
        site.slot.known = true ∧ mappingKey? b site.slot = none ∧
          write.key = site.slot.eval (Env.root root.sevm)) := by
  obtain ⟨site, member, den, guards, nonInc⟩ :=
    successfulSstore_site checked certified pc hcode stateGas chain found
  refine ⟨site, member, guards, nonInc, ?_⟩
  by_cases hit : site.mayHitMapping b = true
  · exact .inl ⟨List.mem_filter.mpr ⟨member, hit⟩, den⟩
  · simp only [Site.mayHitMapping, Bool.or_eq_true, Bool.not_eq_true', not_or,
      Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hit
    have known : site.slot.known = true := Bool.eq_true_of_not_eq_false hit.1
    exact .inr ⟨known, hit.2, den known⟩

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

/-- One row of a coin's balance table. -/
structure BalanceRow : Type where
  path : BalancePath
  site : Site

/-- The frame caller's word, masked to an address or not. -/
def isCallerWord : Term → Bool
  | .caller => true
  | .op2 .and .caller (.const 0xffffffffffffffffffffffffffffffffffffffff) => true
  | _ => false

/-- The only shape the row's reading is checked against, at base `b`: an unresolved row is a site
of unknown slot; every other row's slot has the form `keccak256(key ‖ b)`; a holder row's key is
syntactically the caller word; a recipient, allowance or signed row's key is not that literal term
(the key's value may still equal the caller's in a given frame). Operator and initializer rows have
no check on their key. It reads neither `nonInc` nor the guards, and proves no authority. -/
def BalanceRow.shapeOk (b : B256) (r : BalanceRow) : Bool :=
  match r.path, mappingKey? b r.site.slot with
  | .unresolved _, _ => !r.site.slot.known
  | .holder, some k => isCallerWord k
  | .operator _, some _ => true
  | .initializer, some _ => true
  | _, some k => !isCallerWord k
  | _, none => false

end Blanc.Lift.WriteSite
