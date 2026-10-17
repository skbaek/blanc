import Blanc.SlotFootprintWord
import Blanc.ExecutionTraceFrames
import Blanc.Lift.Usdc.Constants
import Blanc.Lift.Usdc.Decode
import Blanc.Lift.Usdc.ModelLaws
import Blanc.Lift.Usdc.Slots

/-!
# The USDC storage footprint (C3, design §4.2)

FiatTokenV2_2's mappings live at hashed slots of the proxy's storage (`Slots.lean`).  A footprint
over a set `K` of tracked keys (`Key`) reads them through `Blanc/SlotFootprint.lean`: `Support`
(every nonzero word is a fixed word or a tracked key's word), `Inj`/`Apart`, and `KeysFresh`, the
trace-local collision premise.  `fixedSlots` are the implementation's value slots 0–18 (not the
mapping bases 3, 9, 10, 12, 13, 16, 17) and the proxy's two unstructured slots.

`ledger K s` is the model `Ledger` a storage carries: tracked mapping words (zero elsewhere) and
the fixed words, read as the deployed code reads them (C0 §4.2): the packed balance word
(`balanceBits`/`frozenBit`), `uint256` words whole, `bool`s by their low byte, the `bool`s packed at
byte 20 behind an address (`paused` in slot 1, `initialized` in slot 8), the `uint8`
`_initializedVersion` (slot 18) by its low byte, and addresses by their low 160 bits.

`frameKeys e` lists the keys a raw frame at the proxy may touch, from its calldata and caller: the
view getters' keys by selector, and the decoded writer's keys (`Call.keys`, including the
`msg.sender`-derived `bal[caller]`, `allow[src][caller]`, `minter[caller]`,
`minterAllowance[caller]`).  Entry, implementation and library frames carry the entry's calldata,
so one key function serves the three levels.

Read lemmas (`ledger_bal`, …), write lemmas (`ledger_set_bal`, …, one per storage-write family and
per fixed word) and `FootInv` preservation are below; `FootprintStep.lean` states that
`Ledger.step` reads and writes only `frameKeys`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.ExecutionTrace

/-- A mapping key of FiatTokenV2_2 (`_deprecatedBlacklisted` is empty at version 3 and never
written again, so it has no key). -/
inductive Key
  | bal (a : Adr)
  | allow (o s : Adr)
  | nonce (a : Adr)
  | auth (a : Adr) (n : B256)
  | minter (a : Adr)
  | minterAllowance (a : Adr)
  deriving DecidableEq

def Key.slot : Key → B256
  | .bal a => balSlot a
  | .allow o s => allowSlot o s
  | .nonce a => nonceSlot a
  | .auth a n => authSlot a n
  | .minter a => minterSlot a
  | .minterAllowance a => minterAllowanceSlot a

/-- The non-mapping words at the proxy's storage: the implementation's slots 0–18 that hold values,
and the proxy's two unstructured slots. -/
def fixedSlots : List B256 := [0, 1, 2, 4, 5, 6, 7, 8, 11, 14, 15, 18, implSlot, adminSlot]

abbrev KeysFresh (K : Key → Prop) (ks : List Key) : Prop :=
  SlotFootprint.FreshKeys Key.slot fixedSlots K ks

/-! ## Reading a storage word -/

/-- A storage `bool` at byte offset 0 (Solidity reads its low byte). -/
def boolBit (w : B256) : Bool := decide (w.toNat % 256 ≠ 0)

/-- A storage `bool` packed at byte offset 20, behind an address. -/
def flag20 (w : B256) : Bool := decide (w.toNat / 2 ^ 160 % 256 ≠ 0)

/-- The ledger that mapping words `m` (by key) and storage words `f` (by slot; only the fixed slots
are read) carry. -/
def ledgerOf (m : Key → B256) (f : B256 → B256) : Ledger where
  bal a := balanceBits (m (.bal a))
  frozen a := frozenBit (m (.bal a))
  allow o p := (m (.allow o p)).toNat
  nonce a := (m (.nonce a)).toNat
  authUsed a n := boolBit (m (.auth a n))
  paused := flag20 (f 1)
  owner := (f 0).toAdr
  pauser := (f 1).toAdr
  blacklister := (f 2).toAdr
  masterMinter := (f 8).toAdr
  rescuer := (f 14).toAdr
  minter a := boolBit (m (.minter a))
  minterAllowance a := (m (.minterAllowance a)).toNat
  supply := (f 11).toNat
  initialized := flag20 (f 8)
  version := (f 18).toNat % 256
  admin := (f adminSlot).toAdr

/-- The ledger the tracked keys and fixed words of a storage carry (tracked words; zero at an
untracked key). -/
noncomputable def ledger (K : Key → Prop) (s : Stor) : Ledger :=
  ledgerOf (SlotFootprint.trackedWord Key.slot K s) s.get

/-- The footprint invariant: support, injective and apart tracked slots, a good ledger. -/
structure FootInv (K : Key → Prop) (s : Stor) : Prop where
  support : SlotFootprint.Support Key.slot fixedSlots K s
  inj : SlotFootprint.Inj Key.slot K
  apart : SlotFootprint.Apart Key.slot fixedSlots K
  good : (ledger K s).Good

/-! ## The keys a frame touches -/

/-- The keys the model step of a decoded call by `caller` reads or writes. -/
def Call.keys (caller : Adr) : Call → List Key
  | .transfer dst _ => [.bal caller, .bal dst]
  | .transferFrom src dst _ => [.bal caller, .bal src, .bal dst, .allow src caller]
  | .approve s _ => [.allow caller s]
  | .increaseAllowance s _ => [.allow caller s]
  | .decreaseAllowance s _ => [.allow caller s]
  | .permit o s _ => [.nonce o, .allow o s]
  | .transferWithAuthorization src dst _ n => [.bal src, .bal dst, .auth src n]
  | .receiveWithAuthorization src dst _ n => [.bal src, .bal dst, .auth src n]
  | .cancelAuthorization a n => [.auth a n]
  | .mint dst _ => [.minter caller, .bal caller, .bal dst, .minterAllowance caller]
  | .burn _ => [.minter caller, .bal caller]
  | .configureMinter m _ => [.minter m, .minterAllowance m]
  | .removeMinter m => [.minter m, .minterAllowance m]
  | .blacklist a => [.bal a]
  | .unBlacklist a => [.bal a]
  | _ => []

/-- The keys the view getters read, by selector (`balanceOf`, `isBlacklisted`, `allowance`,
`nonces`, `authorizationState`, `isMinter`, `minterAllowance`; C0 `impl-selectors.json`). -/
def viewKeys (e : Sevm) : List Key :=
  let w := Sevm.dataWord e
  let sel := Blanc.Sevm.selector e
  if sel = 0x70a08231 ∨ sel = 0xfe575a87 then [.bal (w 4).toAdr]
  else if sel = 0xdd62ed3e then [.allow (w 4).toAdr (w 36).toAdr]
  else if sel = 0x7ecebe00 then [.nonce (w 4).toAdr]
  else if sel = 0xe94a0102 then [.auth (w 4).toAdr (w 36)]
  else if sel = 0xaa271e1a then [.minter (w 4).toAdr]
  else if sel = 0x8a6db9c3 then [.minterAllowance (w 4).toAdr]
  else []

/-- The keys a raw frame at the proxy may touch, read from its calldata (entry, implementation and
library frames alike carry the entry's calldata): the view getters' keys and the decoded writer's
keys, including those derived from `msg.sender`. -/
noncomputable def frameKeys (e : Sevm) : List Key :=
  viewKeys e ++ ((decodeCall e).map (Call.keys e.caller)).getD []

/-- The keys the raw frames at `P` of this history may touch. -/
noncomputable def historyTouchedKeys {cfg : ChainConfig} {checkpoint future : BlockChain}
    (P : Adr) (tr : ConfiguredHistoryTrace cfg checkpoint future) : List Key :=
  tr.rawFrames.flatMap fun root => if root.sevm.currentTarget = P then frameKeys root.sevm else []

def historyKeyUniverse {cfg : ChainConfig} {checkpoint future : BlockChain}
    (P : Adr) (tr : ConfiguredHistoryTrace cfg checkpoint future) (K₀ : Key → Prop) : Key → Prop :=
  SlotFootprint.extendBy K₀ (historyTouchedKeys P tr)

/-- A decoded writer's keys are among the frame's keys. -/
theorem keys_sub_frameKeys {e : Sevm} {c : Call} (dec : decodeCall e = some c) :
    ∀ k ∈ c.keys e.caller, k ∈ frameKeys e := by
  intro k hk
  simp only [frameKeys, dec, Option.map_some, Option.getD_some, List.mem_append]
  exact Or.inr hk

end Blanc.Lift.Usdc
