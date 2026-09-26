import Blanc.Lift.Curve3Crv.Dispatch

/-!
# The raw effects refine the model (pure)

For each function, under the storage abstraction `VyInv stor s K` and the frame-local premise
`Fresh` for the keys the call touches, the raw effect over storage (`Spec.lean`) and the model's
`step` succeed together, and when they do the new storage abstracts the model's new state
(for the live keys extended by the touched ones), the appended log entries are the model's
events, and the return data is the model's (`RawRefines`).  No bytecode appears here: these are
statements about `Stor.set`, `mapSlot`, and the model's functions.

Every lemma is a frozen segment; `refine_at` assembles them by the body index.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Call Ret)

/-- The raw effect of body `k`, with `ow` the owner answer (`set_name` only). -/
def rawOf (k : Nat) (sevm : Sevm) (ow : Option B256) (stor : Stor) : Option Raw :=
  match k with
  | 0 => rawSetMinter sevm stor
  | 1 => rawSetName sevm stor ow
  | 2 => rawTotalSupply sevm stor
  | 3 => rawAllowance sevm stor
  | 4 => rawTransfer sevm stor
  | 5 => rawTransferFrom sevm stor
  | 6 => rawApprove sevm stor
  | 7 => rawMint sevm stor
  | 8 => rawBurnFrom sevm stor
  | 9 => rawName sevm stor
  | 10 => rawSymbol sevm stor
  | 11 => rawDecimals sevm stor
  | 12 => rawBalanceOf sevm stor
  | _ => none

/-- The return data of a raw effect and a model result agree. -/
def RetMatch : Option Bytes → Ret → Prop
  | none, r => r = .stop
  | some out, r => RetOut out r

/-- A raw effect and a model result correspond: storage abstracts the new state over `K'`, the
log entries are the model's events, the return data the model's. -/
def Corr (sevm : Sevm) (K' : Key → Prop) (r : Raw) (o : Curve3Crv.Out) : Prop :=
  VyInv r.1 o.1 K' ∧ r.2.1 = o.2.1.map (eventLog sevm.currentTarget) ∧ RetMatch r.2.2 o.2.2

/-- The raw effect and the model's result succeed together and correspond. -/
def RawRefines (sevm : Sevm) (raw : Option Raw) (res : Curve3Crv.Result) (K' : Key → Prop) :
    Prop :=
  (∀ r, raw = some r → ∃ o, res = .ok o ∧ Corr sevm K' r o) ∧
    (∀ o, res = .ok o → ∃ r, raw = some r ∧ Corr sevm K' r o)

section Segments

variable {sevm : Sevm} {stor : Stor} {s : Curve3Crv.State} {K : Key → Prop} {ow : Option B256}

-- SEGMENT: refineSetMinter (pure, short)
/-- `set_minter`.  Proof sketch: unfold `rawSetMinter`, `step`, `setMinter`; the guards agree
(`VyInv.minter`: `stor.get 6 = s.minter.toB256`, and `Adr.toB256` is injective); the new storage
differs at slot 6 only, a fixed slot, so every `VyInv` field but `minter` transfers
(`Stor.get_set_ne` with `apart`, `support` gains nothing new); `minter`: `m.toAdr.toB256 = m`
for `m < 2^160`.  No keys. -/
theorem refine_setMinter (hinv : VyInv stor s K)
    (hf : ∀ k ∈ callKeys sevm.caller (callAt sevm 0), Fresh K k) :
    RawRefines sevm (rawOf 0 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 0) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 0))) := by
  sorry

-- SEGMENT: refineSetName (pure, medium: the string words)
/-- `set_name`.  Proof sketch: the guards agree (`strArg`'s length is the length word;
`c3ctx`'s `ownerOf` is `ow` at every address).  The new storage is `vyCopyStore` twice: the
name's `min 3 ((32 + L0)/32 + 1)` words at `vyNameBase + i`, the symbol's at `vySymbolBase + i`;
all eight string slots are in `vyFixedSlots`, pairwise distinct and distinct from 2, 5, 6
(`vyFixedSlots_nodup`, a kernel `decide` on two Keccak digests — put it in its own file, out of
the language server's way), so live keys and the three words are untouched.  `VyStr` for the new
name: the length word is `L0`; the first `L0` bytes of the two data words are the calldata's
content bytes (`vyStrWords` of the stored words is `(data.sliceD (s0+32) 64 0)` up to the words
the loop wrote, which cover `L0` bytes: `L0 ≤ 32 ((32 + L0)/32)`); likewise the symbol. -/
theorem refine_setName (hinv : VyInv stor s K)
    (hf : ∀ k ∈ callKeys sevm.caller (callAt sevm 1), Fresh K k) :
    RawRefines sevm (rawOf 1 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 1) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 1))) := by
  sorry

-- SEGMENT: refineWordViews (pure, short; four views)
/-- `totalSupply`, `decimals`, `balanceOf`, `allowance`.  Proof sketch: storage unchanged, the
model state unchanged, no events; the return word is `VyInv.supply`/`decimals`, or
`VyInv.get_slot` for the fresh key (`mapSlot 3 h = (Key.bal h.toAdr).slot` since
`h.toAdr.toB256 = h` below `2^160`).  `VyInv` over `K` extended by a fresh key: its slot
reads `0 = val` (`get_slot`), injectivity and `apart` from `Fresh`. -/
theorem refine_wordView {k : Nat} (hk : k = 2 ∨ k = 3 ∨ k = 11 ∨ k = 12) (hinv : VyInv stor s K)
    (hf : ∀ k' ∈ callKeys sevm.caller (callAt sevm k), Fresh K k') :
    RawRefines sevm (rawOf k sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm k) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm k))) := by
  sorry

-- SEGMENT: refineStringViews (pure, short)
/-- `name`, `symbol`.  Proof sketch: `VyInv.name`/`symbol` give the length bound and
`vyStrOf stor base n = s.name` (`VyStr`'s third clause is exactly `vyStrOf`); the return data is
`abiString` of it on both sides. -/
theorem refine_stringView {k : Nat} (hk : k = 9 ∨ k = 10) (hinv : VyInv stor s K)
    (hf : ∀ k' ∈ callKeys sevm.caller (callAt sevm k), Fresh K k') :
    RawRefines sevm (rawOf k sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm k) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm k))) := by
  sorry

-- SEGMENT: refineTransfer (pure, medium)
/-- `transfer`.  Proof sketch: `get_slot` for `bal caller` and `bal d` (both fresh) turns the raw
reads into the model's balances; with `a = caller`, `d' = d.toAdr`: if `d' = a` the second read
is of the first write (`Stor.get_set_self`), matching `ledgerDebit … d'` at `a`; otherwise the
slots differ (`inj` for live keys, `Fresh` otherwise) and `Stor.get_set_ne`.  The new storage
abstracts `ledgerCredit (ledgerDebit …)` on the two keys, everything else is unchanged;
`support` gains exactly the two slots, now live; `conserved` by the model's `step_conserved`.
The log entry is `eventLog` of `.transfer a d' v` (`d'.toB256 = d`). -/
theorem refine_transfer (hinv : VyInv stor s K)
    (hf : ∀ k ∈ callKeys sevm.caller (callAt sevm 4), Fresh K k) :
    RawRefines sevm (rawOf 4 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 4) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 4))) := by
  sorry

-- SEGMENT: refineTransferFrom (pure, medium-long)
/-- `transferFrom`.  Proof sketch: as `refineTransfer` for the two balance writes, then the
minter test reads slot 6 of the twice-written storage, which is `stor.get 6` (balance slots are
off `vyFixedSlots`); the allowance key `allow f caller` is fresh, so its slot is distinct from
both balance slots, and its read is the model's `s.allowances f caller`; the write matches
`Function.update … (ledgerDebit …)`. -/
theorem refine_transferFrom (hinv : VyInv stor s K)
    (hf : ∀ k ∈ callKeys sevm.caller (callAt sevm 5), Fresh K k) :
    RawRefines sevm (rawOf 5 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 5) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 5))) := by
  sorry

-- SEGMENT: refineApprove (pure, short)
/-- `approve`.  Proof sketch: one fresh key `allow caller p`; the guard `v = 0 ∨ current = 0`
reads the model's allowance (`get_slot`); one write. -/
theorem refine_approve (hinv : VyInv stor s K)
    (hf : ∀ k ∈ callKeys sevm.caller (callAt sevm 6), Fresh K k) :
    RawRefines sevm (rawOf 6 sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm 6) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm 6))) := by
  sorry

-- SEGMENT: refineMintBurn (pure, medium; `mint` and `burnFrom`)
/-- `mint`, `burnFrom`.  Proof sketch: slot 5 then one fresh balance key; the balance read after
the supply write is of the unchanged balance slot (off `vyFixedSlots`); guards and effects are
the model's clause by clause; `conserved` by `step_conserved`. -/
theorem refine_mintBurn {k : Nat} (hk : k = 7 ∨ k = 8) (hinv : VyInv stor s K)
    (hf : ∀ k' ∈ callKeys sevm.caller (callAt sevm k), Fresh K k') :
    RawRefines sevm (rawOf k sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm k) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm k))) := by
  sorry

end Segments

/-- **The refinement of every body's raw effect**, assembled. -/
theorem refine_at {sevm : Sevm} {stor : Stor} {s : Curve3Crv.State} {K : Key → Prop}
    {ow : Option B256} {k : Nat} (hk : k < 13) (hinv : VyInv stor s K)
    (hf : ∀ k' ∈ callKeys sevm.caller (callAt sevm k), Fresh K k') :
    RawRefines sevm (rawOf k sevm ow stor) (Curve3Crv.step (c3ctx sevm ow) (callAt sevm k) s)
      (Key.extend K (callKeys sevm.caller (callAt sevm k))) := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · exact refine_setMinter hinv hf
  · exact refine_setName hinv hf
  · exact refine_wordView (by simp) hinv hf
  · exact refine_wordView (by simp) hinv hf
  · exact refine_transfer hinv hf
  · exact refine_transferFrom hinv hf
  · exact refine_approve hinv hf
  · exact refine_mintBurn (by simp) hinv hf
  · exact refine_mintBurn (by simp) hinv hf
  · exact refine_stringView (by simp) hinv hf
  · exact refine_stringView (by simp) hinv hf
  · exact refine_wordView (by simp) hinv hf
  · exact refine_wordView (by simp) hinv hf
  · omega

end Blanc.Lift.Curve3Crv
