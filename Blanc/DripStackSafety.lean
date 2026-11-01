import Blanc.DripCode
import Blanc.DripStackSafetyData

namespace Blanc.Drip.StackSafety

open Jaune AbstractStackSafety

/-- Depth 11 covers all 1762 runtime byte positions. -/
def codeTries : Lift.CodeTries code.toByteArray 11 :=
  Lift.CodeTries.ofCode _ 11 (by decide +kernel) (by decide +kernel)

/-- The checker's trie reader of the runtime: every byte read is a depth-11 lookup. -/
def reader : CodeReader := .ofTries codeTries 1762

/-- Row and layout decisions on `reader` are decisions on the actual runtime bytes. -/
theorem reader_eq : reader = .ofCode code.toByteArray :=
  CodeReader.ofTries_eq codeTries (by decide +kernel)

/-- Every row uses the complete table, including the edge from PC13 to PC14. -/
theorem subtree7_rows_checked :
    subtree7.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree7_layout_checked : subtree7.checkLayout code.toByteArray 0 14 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree30_rows_checked :
    subtree30.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree30_layout_checked : subtree30.checkLayout code.toByteArray 19 41 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

/-- Named proofs join both children and the intervening row. -/
theorem subtree14_rows_checked :
    subtree14.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree7_rows_checked subtree30_rows_checked

/-- The join consumes PC14's actual five-byte PUSH, leaving no byte gap. -/
theorem subtree14_layout_checked : subtree14.checkLayout code.toByteArray 0 41 = true := by
  exact Table.checkLayout_node_reader (next := 19) reader_eq (by decide +kernel)
    subtree7_layout_checked subtree30_layout_checked (by decide)

theorem subtree49_rows_checked :
    subtree49.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree49_layout_checked : subtree49.checkLayout code.toByteArray 44 58 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree65_rows_checked :
    subtree65.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree65_layout_checked : subtree65.checkLayout code.toByteArray 59 88 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree58_rows_checked :
    subtree58.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree49_rows_checked subtree65_rows_checked

theorem subtree58_layout_checked : subtree58.checkLayout code.toByteArray 44 88 = true := by
  exact Table.checkLayout_node_reader (next := 59) reader_eq (by decide +kernel)
    subtree49_layout_checked subtree65_layout_checked (by decide)

theorem subtree41_rows_checked :
    subtree41.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree14_rows_checked subtree58_rows_checked

theorem subtree41_layout_checked : subtree41.checkLayout code.toByteArray 0 88 = true := by
  exact Table.checkLayout_node_reader (next := 44) reader_eq (by decide +kernel)
    subtree14_layout_checked subtree58_layout_checked (by decide)

theorem subtree111_rows_checked :
    subtree111.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree111_layout_checked : subtree111.checkLayout code.toByteArray 89 151 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree176_rows_checked :
    subtree176.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree176_layout_checked : subtree176.checkLayout code.toByteArray 153 185 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree151_rows_checked :
    subtree151.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree111_rows_checked subtree176_rows_checked

theorem subtree151_layout_checked : subtree151.checkLayout code.toByteArray 89 185 = true := by
  exact Table.checkLayout_node_reader (next := 153) reader_eq (by decide +kernel)
    subtree111_layout_checked subtree176_layout_checked (by decide)

theorem subtree191_rows_checked :
    subtree191.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree191_layout_checked : subtree191.checkLayout code.toByteArray 186 197 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree209_rows_checked :
    subtree209.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree209_layout_checked : subtree209.checkLayout code.toByteArray 198 214 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree197_rows_checked :
    subtree197.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree191_rows_checked subtree209_rows_checked

theorem subtree197_layout_checked : subtree197.checkLayout code.toByteArray 186 214 = true := by
  exact Table.checkLayout_node_reader (next := 198) reader_eq (by decide +kernel)
    subtree191_layout_checked subtree209_layout_checked (by decide)

theorem subtree185_rows_checked :
    subtree185.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree151_rows_checked subtree197_rows_checked

theorem subtree185_layout_checked : subtree185.checkLayout code.toByteArray 89 214 = true := by
  exact Table.checkLayout_node_reader (next := 186) reader_eq (by decide +kernel)
    subtree151_layout_checked subtree197_layout_checked (by decide)

/-- Complete initial 91-row region; successor lookup still uses all 735 rows. -/
theorem subtree88_rows_checked :
    subtree88.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree41_rows_checked subtree185_rows_checked

theorem subtree88_layout_checked : subtree88.checkLayout code.toByteArray 0 214 = true := by
  exact Table.checkLayout_node_reader (next := 89) reader_eq (by decide +kernel)
    subtree41_layout_checked subtree185_layout_checked (by decide)

end Blanc.Drip.StackSafety
