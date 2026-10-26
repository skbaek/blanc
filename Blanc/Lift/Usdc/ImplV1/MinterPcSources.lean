import Blanc.Lift.CursorCheckPrefix
import Blanc.Lift.Usdc.ImplV1.MinterPcPatterns

/-! Source pc consequences of the same checked V1 SSTORE-tail cursor.
These conditional facts do not establish that a family reaches the supplied tail. -/

namespace Blanc.Lift.Usdc.ImplV1

open Jaune

/-- The checked first removeMinter store tail fixes the actual raw pc. -/
theorem pc_eq_160b_of_store_tail {c : Cert} {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {tail : SFunc}
    (tree : κ.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.push [0x00] (by decide)) tail))) : F.pc = 0x160b := by
  refine ok.pc_eq_of_prefix_singleton
    [.reg .sstore, .reg .pop, .push [0x00] (by decide)] tail tree
    (suffix := []) ?_ minter160bPattern_ne_nil minter160bPattern_occurrences
  decide +kernel

/-- The checked second removeMinter store tail fixes the pc for any PUSH20 payload. -/
theorem pc_eq_1650_of_store_tail {c : Cert} {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {tail : SFunc} {bs : Bytes} (fits : bs.length ≤ 32)
    (width : bs.length = 20)
    (tree : κ.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.reg (.dup 1)) (.next (.push bs fits) tail)))) : F.pc = 0x1650 := by
  refine ok.pc_eq_of_prefix_singleton
    [.reg .sstore, .reg .pop, .reg (.dup 1), .push bs fits] tail tree
    (suffix := bs) ?_ minter1650Pattern_ne_nil minter1650Pattern_occurrences
  simp only [List.flatMap_cons, List.flatMap_nil, Ninst.toBytes, pushToB8L,
    pushToB8, List.append_nil]
  rw [width]
  rfl

/-- The checked first configureMinter store tail fixes the actual raw pc. -/
theorem pc_eq_20b2_of_store_tail {c : Cert} {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {tail : SFunc}
    (tree : κ.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.reg (.dup 1)) (.next (.push [0x0d] (by decide)) tail)))) : F.pc = 0x20b2 := by
  refine ok.pc_eq_of_prefix_singleton
    [.reg .sstore, .reg .pop, .reg (.dup 1), .push [0x0d] (by decide)] tail tree
    (suffix := []) ?_ minter20b2Pattern_ne_nil minter20b2Pattern_occurrences
  decide +kernel

/-- The checked second configureMinter store tail fixes the pc for any PUSH20 payload. -/
theorem pc_eq_20f6_of_store_tail {c : Cert} {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {tail : SFunc} {bs : Bytes} (fits : bs.length ≤ 32)
    (width : bs.length = 20)
    (tree : κ.f = .next (.reg .sstore) (.next (.reg .pop)
      (.next (.reg (.dup 2)) (.next (.push bs fits) tail)))) : F.pc = 0x20f6 := by
  refine ok.pc_eq_of_prefix_singleton
    [.reg .sstore, .reg .pop, .reg (.dup 2), .push bs fits] tail tree
    (suffix := bs) ?_ minter20f6Pattern_ne_nil minter20f6Pattern_occurrences
  simp only [List.flatMap_cons, List.flatMap_nil, Ninst.toBytes, pushToB8L,
    pushToB8, List.append_nil]
  rw [width]
  rfl

end Blanc.Lift.Usdc.ImplV1
