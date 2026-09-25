import Blanc.AddressSlotProofs

namespace Blanc.Lift.Weth9

open Jaune
open Blanc

/- The literal words used by the lifted WETH9 straight-line entries.  Keeping
   these facts public lets the entry proofs share the same normalization of
   bytecode literals. -/

theorem ff20_eq :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = ~~~ addressMask := by
  decide

theorem ff20_and_adr (a : Adr) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& a.toB256) =
      a.toB256 := by
  rw [ff20_eq]
  exact addressSlotReadWord_toB256 a

theorem w00_eq : Bytes.toB256 [0x00] = 0 := by decide
theorem w03_eq : Bytes.toB256 [0x03] = 3 := by decide
theorem w20_eq : Bytes.toB256 [0x20] = 32 := by decide
theorem w32_add_0 : (32 : B256) + 0 = 32 := by decide
theorem w32_add_32 : (32 : B256) + 32 = 64 := by decide
theorem w0_toNat : (0 : B256).toNat = 0 := by decide
theorem w32_toNat : (32 : B256).toNat = 32 := by decide
theorem w64_toNat : (64 : B256).toNat = 64 := by decide

theorem w04_eq : Bytes.toB256 [0x04] = 4 := by decide

theorem ff20_and_word (x : B256) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& x) =
      x.toAdr.toB256 := by
  rw [ff20_eq]
  exact addressSlotReadWord_eq_toAdr_toB256 x

theorem and_mask_word (x : B256) : (x &&& ~~~ addressMask) = x.toAdr.toB256 := by
  rw [B256.and_comm]
  exact addressSlotReadWord_eq_toAdr_toB256 x

theorem ff20_and_and (x : B256) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& x)) =
      x &&& ~~~ addressMask := by
  rw [ff20_eq, B256.and_comm (~~~ addressMask) x,
    B256.and_comm (~~~ addressMask) (x &&& ~~~ addressMask), B256.and_idem_right]

/-- `iszero(iszero(iszero(lt(bal, wad))))` is nonzero only when `wad ≤ bal`. -/
theorem le_of_check {bal wad : B256}
    (h : ((((bal <? wad) =? 0) =? 0) =? 0) ≠ 0) : wad ≤ bal := by
  rw [← B256.not_lt]
  intro hlt
  apply h
  rw [B256.ltCheck, ite_eq_left_of_eq_true _ _ (eq_true hlt)]
  decide

end Blanc.Lift.Weth9
