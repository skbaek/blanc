import Blanc.Lift.FiniteCheckpoint
import Blanc.Lift.Usdc.Hist

/-!
# USDC's checkpoint facts by a finite checker (C7, Appendix A §11)

`checkUsdc P rows w` decides `UsdcInstalled P w ∧ FootInv (rowKeys rows) (w.getStor P)` for a row
list of USDC keys with their precomputed slot words: the three runtimes byte for byte against the
certified images (`Proxy.code`, `Impl.code`, `Lib.code`), the implementation slot, the proxy apart
from the implementation and the library, the contract-neutral footprint checker
(`checkRows Key.slot fixedSlots rows`: complete support by one merge walk over the storage tree's
entries against the ascending row words, never a split over slots), and the ledger's goodness on the
fixed words (`initialized`, the flag at byte 20 of slot 8; `_initializedVersion`, the low byte of
slot 18, equal to 3).  The balance bound of `Ledger.Good` holds of every ledger, since balances are
read as the low 255 bits of the packed word.  `checkUsdc_sound` is its soundness theorem.

Cost: linear in the rows and the proxy's storage entries (one keccak per row for its slot word), and
linear in the three code lengths (2,186 + 23,464 + 1,741 bytes).

`checkUsdc_accepts` runs the checker in the kernel on a small synthetic world (the three runtimes
installed, four tracked rows); `checkUsdc_rejects_stray` is the control: one stray nonzero word at
an untracked, non-fixed slot makes it answer `false`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift.FiniteCheckpoint

/-- A world's code at `a` compared on the byte arrays' lists is the certified image of `c`. -/
theorem image_of_code_data {w : State} {a : Adr} {c : ByteArray}
    (h : (w.getCode a).data.toList = c.data.toList) : some (w.getCode a).toList = some c.toList := by
  rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data, h]

/-- **USDC's checkpoint checker** on fetched rows: the three code identities, the implementation
slot, `checkRows Key.slot fixedSlots rows`, and the ledger's goodness on the fixed words (version 3,
initialized). -/
def checkUsdc (P : Adr) (rows : List (Key × B256)) (w : State) : Bool :=
  decide ((w.getCode P).data.toList = Proxy.code.data.toList) &&
    decide ((w.getCode usdcImpl).data.toList = Impl.code.data.toList) &&
    decide ((w.getCode usdcLib).data.toList = Lib.code.data.toList) &&
    decide ((w.getStor P).get implSlot = usdcImpl.toB256) &&
    decide (P ≠ usdcImpl) && decide (P ≠ usdcLib) &&
    checkRows Key.slot fixedSlots rows (w.getStor P) &&
    flag20 ((w.getStor P).get 8) && decide (((w.getStor P).get 18).toNat % 256 = 3)

/-- **Soundness of USDC's checkpoint checker.** -/
theorem checkUsdc_sound {P : Adr} {rows : List (Key × B256)} {w : State}
    (h : checkUsdc P rows w = true) :
    UsdcInstalled P w ∧ FootInv (rowKeys rows) (w.getStor P) := by
  simp only [checkUsdc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hproxy, himpl⟩, hlib⟩, hslot⟩, hP⟩, hL⟩, hrows⟩, hinit⟩, hver⟩ := h
  have sound := checkRows_sound hrows
  refine ⟨⟨image_of_code_data hproxy, image_of_code_data himpl, image_of_code_data hlib, hslot, hP,
    hL⟩, ⟨sound.support, sound.inj, sound.apart, ⟨fun a => Nat.mod_lt _ (Nat.two_pow_pos 255),
    hinit, hver⟩⟩⟩

/-! ## Non-vacuity: a synthetic world the checker accepts, and a stray-slot control -/

/-- The synthetic holder `A` (balance, minter flag, permit nonce rows). -/
def synthA : Adr := 0x1111111111111111111111111111111111111111

/-- The synthetic holder `B` (balance row). -/
def synthB : Adr := 0x2222222222222222222222222222222222222222

/-- The tracked rows, in ascending slot-word order (as the checker requires). -/
def synthRows : List (Key × B256) :=
  [(.minter synthA, minterSlot synthA), (.bal synthA, balSlot synthA),
    (.bal synthB, balSlot synthB), (.nonce synthA, nonceSlot synthA)]

/-- The proxy's storage: owner, `initialized` (byte 20 of slot 8), version 3, the implementation and
admin words, and the four tracked words. -/
def synthStor : Stor := Stor.ofList
  [(0, synthA.toB256), (8, Nat.toB256 (2 ^ 160)), (18, 3), (implSlot, usdcImpl.toB256),
    (adminSlot, synthB.toB256), (minterSlot synthA, 1), (balSlot synthA, 1000000),
    (balSlot synthB, Nat.toB256 (2 ^ 255 + 7)), (nonceSlot synthA, 2)]

/-- The synthetic world: the proxy, implementation and library runtimes installed. -/
def synthWorld (s : Stor) : State :=
  (((.empty : State).insert usdcProxy { Acct.nil with stor := s, code := Proxy.code }).insert usdcImpl
    { Acct.nil with code := Impl.code }).insert usdcLib { Acct.nil with code := Lib.code }

/-- **The checker accepts the synthetic world** (kernel evaluation). -/
theorem checkUsdc_accepts : checkUsdc usdcProxy synthRows (synthWorld synthStor) = true := by
  decide +kernel

/-- **The control**: one stray nonzero word at an untracked, non-fixed slot is rejected. -/
theorem checkUsdc_rejects_stray :
    checkUsdc usdcProxy synthRows (synthWorld (synthStor.set 99 5)) = false := by
  decide +kernel

/-- The synthetic world satisfies USDC's checkpoint facts. -/
theorem synthWorld_installed_foot :
    UsdcInstalled usdcProxy (synthWorld synthStor) ∧
      FootInv (rowKeys synthRows) ((synthWorld synthStor).getStor usdcProxy) :=
  checkUsdc_sound checkUsdc_accepts

end Blanc.Lift.Usdc
