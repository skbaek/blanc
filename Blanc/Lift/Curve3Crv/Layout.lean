import Blanc.Curve3Crv.Properties
import Blanc.Lift.MapSlot

/-!
# The deployed 3Crv storage layout and its storage abstraction

Vyper 0.2.4 lays the source's storage out as (recon §3, read off the bytes):

* `decimals` at slot 2, `total_supply` at 5, `minter` at 6 (a word below `2^160`);
* `balanceOf[a]` at `keccak(3 ‖ a)` and `allowances[o][p]` at `keccak(keccak(4 ‖ o) ‖ p)`
  (`mapSlot`, slot first);
* the strings `name` (`String[64]`) and `symbol` (`String[32]`) at `keccak(0)` and `keccak(1)`:
  the length word there and the data words at the following slots (up to 2 and 1 of them).
  The copy loops store whole words, so data bytes past the length are whatever the setter's
  calldata held; only the first `length` bytes are the string.

## Collisions, and why the abstraction carries a key set

The two hashed maps can collide with each other and with the fixed slots, and for allowance
slots collisions are not merely possible: `allowSlot` has `2^320` arguments and `2^256` values,
so (for keccak as a random function) almost every word, every balance slot among them, is
*some* allowance slot.  An abstraction "every model key's slot holds its value" is therefore
not preserved by a transfer, and a premise "no allowance slot equals this balance slot" is
almost surely false.  `VyInv stor s K` instead relates storage to the model on a set `K` of
*live* keys: their slots are pairwise distinct, off the fixed slots, and hold the model's
values; every other key's model value is zero; and every nonzero storage word sits at a fixed
slot or a live key's slot (`support`).  A frame needs only the local premise `Fresh` for the
keys it touches — the key is live, or its slot is none of the finitely many slots in use —
the counterpart of WETH9's trace-local `AllowAdmitted` (`FreshKeys`: each touched key fresh, and
the touched keys' slots pairwise distinct).  The contract's history makes it true
of every frame whose touched slots avoid a hash collision with a slot already in use.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Conserved)

/-! ## Slots -/

def vyDecimalsSlot : B256 := 2
def vySupplySlot : B256 := 5
def vyMinterSlot : B256 := 6

/-- `balanceOf[a]`. -/
def vyBalSlot (a : Adr) : B256 := mapSlot 3 a.toB256

/-- `allowances[o][p]`. -/
def vyAllowSlot (o p : Adr) : B256 := mapSlot (mapSlot 4 o.toB256) p.toB256

/-- The length word of `name`; its data words follow. -/
def vyNameBase : B256 := ((0 : B256).toBytes).keccak

/-- The length word of `symbol`; its data word follows. -/
def vySymbolBase : B256 := ((1 : B256).toBytes).keccak

/-- The slots of the non-mapping variables: the three words and the string slots the setter's
copy loops can write (`name`: length and two data words; `symbol`: length and one). -/
def vyFixedSlots : List B256 :=
  [vyDecimalsSlot, vySupplySlot, vyMinterSlot, vyNameBase, vyNameBase + Nat.toB256 1,
    vyNameBase + Nat.toB256 2, vySymbolBase, vySymbolBase + Nat.toB256 1]

/-! ## Mapping keys -/

/-- A key of one of the two maps. -/
inductive Key
  | bal (a : Adr)
  | allow (o p : Adr)
  deriving DecidableEq

def Key.slot : Key → B256
  | .bal a => vyBalSlot a
  | .allow o p => vyAllowSlot o p

/-- The model's value at a key. -/
def Key.val (s : Curve3Crv.State) : Key → B256
  | .bal a => s.balanceOf a
  | .allow o p => s.allowances o p

/-! ## Strings -/

/-- The first `n` data words at `base + 1`, `base + 2`, …, as bytes. -/
def vyStrWords (stor : Stor) (base : B256) (n : Nat) : Bytes :=
  (List.range n).flatMap fun j => (stor.get (base + Nat.toB256 (j + 1))).toBytes

/-- The string stored at `base` with room for `n` data words is `bs`. -/
def VyStr (stor : Stor) (base : B256) (n : Nat) (bs : Bytes) : Prop :=
  (stor.get base).toNat = bs.length ∧ bs.length ≤ 32 * n ∧
    bs = (vyStrWords stor base n).take bs.length

/-! ## The storage abstraction -/

/-- **The storage abstraction** over the live keys `K` (see the module note). -/
structure VyInv (stor : Stor) (s : Curve3Crv.State) (K : Key → Prop) : Prop where
  decimals : stor.get vyDecimalsSlot = s.decimals
  supply : stor.get vySupplySlot = s.totalSupply
  minter : stor.get vyMinterSlot = s.minter.toB256
  name : VyStr stor vyNameBase 2 s.name
  symbol : VyStr stor vySymbolBase 1 s.symbol
  known : ∀ k, K k → stor.get k.slot = k.val s
  unknown : ∀ k, ¬ K k → k.val s = 0
  support : ∀ x, stor.get x ≠ 0 → x ∈ vyFixedSlots ∨ ∃ k, K k ∧ k.slot = x
  inj : ∀ k k', K k → K k' → k.slot = k'.slot → k = k'
  apart : ∀ k, K k → k.slot ∉ vyFixedSlots
  conserved : Conserved s

/-- The frame-local premise for a key a frame touches: it is live, or its slot is none of the
slots in use. -/
def Fresh (K : Key → Prop) (k : Key) : Prop :=
  K k ∨ (k.slot ∉ vyFixedSlots ∧ ∀ k', K k' → k'.slot ≠ k.slot)

/-- The frame-local premise for the keys `ks` a frame touches: each is `Fresh`, and their slots
are pairwise distinct. -/
def FreshKeys (K : Key → Prop) (ks : List Key) : Prop :=
  (∀ k ∈ ks, Fresh K k) ∧ ∀ k ∈ ks, ∀ k' ∈ ks, k.slot = k'.slot → k = k'

/-- The live keys after touching `ks`. -/
def Key.extend (K : Key → Prop) (ks : List Key) : Key → Prop := fun k => K k ∨ k ∈ ks

/-- A fresh key reads its model value. -/
theorem VyInv.get_slot {stor : Stor} {s : Curve3Crv.State} {K : Key → Prop} (h : VyInv stor s K) {k : Key}
    (hk : Fresh K k) : stor.get k.slot = k.val s := by
  rcases hk with hk | ⟨hfix, hoff⟩
  · exact h.known k hk
  · by_cases hK : K k
    · exact h.known k hK
    · rw [h.unknown k hK]
      by_contra hne
      rcases h.support _ hne with hx | ⟨k', hk', he⟩
      · exact hfix hx
      · exact hoff k' hk' he

/-- Touching fresh keys without writing keeps the abstraction over the extended live keys. -/
theorem VyInv.extend {stor : Stor} {s : Curve3Crv.State} {K : Key → Prop} {ks : List Key}
    (h : VyInv stor s K) (hf : FreshKeys K ks) : VyInv stor s (Key.extend K ks) := by
  refine ⟨h.decimals, h.supply, h.minter, h.name, h.symbol, ?_, ?_, ?_, ?_, ?_, h.conserved⟩
  · intro k _
    by_cases hk : k ∈ ks
    · exact h.get_slot (hf.1 k hk)
    · rename_i hK
      exact h.known k (hK.resolve_right hk)
  · intro k hk
    exact h.unknown k (fun hK => hk (.inl hK))
  · intro x hx
    rcases h.support x hx with hx | ⟨k, hK, he⟩
    · exact .inl hx
    · exact .inr ⟨k, .inl hK, he⟩
  · intro k k' hk hk' he
    rcases hk with hk | hk <;> rcases hk' with hk' | hk'
    · exact h.inj k k' hk hk' he
    · rcases hf.1 k' hk' with hK' | ⟨-, hoff⟩
      · exact h.inj k k' hk hK' he
      · exact absurd he (hoff k hk)
    · rcases hf.1 k hk with hK | ⟨-, hoff⟩
      · exact h.inj k k' hK hk' he
      · exact absurd he.symm (hoff k' hk')
    · exact hf.2 k hk k' hk' he
  · intro k hk
    rcases hk with hk | hk
    · exact h.apart k hk
    · rcases hf.1 k hk with hK | ⟨hfix, -⟩
      · exact h.apart k hK
      · exact hfix

end Blanc.Lift.Curve3Crv
