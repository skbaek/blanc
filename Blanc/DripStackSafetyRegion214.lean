import Blanc.DripStackSafety

/-!
Checked first 183-row region of the DRIP stack table. The first 91 rows are
imported from the prior checkpoint; every successor check uses the full table.
-/

namespace Blanc.Drip.StackSafety

open Jaune AbstractStackSafety

theorem subtree222_rows_checked :
    subtree222.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree222_layout_checked :
    subtree222.checkLayout code.toByteArray 217 231 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree239_rows_checked :
    subtree239.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree239_layout_checked :
    subtree239.checkLayout code.toByteArray 232 250 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree264_rows_checked :
    subtree264.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree264_layout_checked :
    subtree264.checkLayout code.toByteArray 251 270 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree278_rows_checked :
    subtree278.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree278_layout_checked :
    subtree278.checkLayout code.toByteArray 271 286 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree293_rows_checked :
    subtree293.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree293_layout_checked :
    subtree293.checkLayout code.toByteArray 287 316 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree328_rows_checked :
    subtree328.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree328_layout_checked :
    subtree328.checkLayout code.toByteArray 319 333 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree345_rows_checked :
    subtree345.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree345_layout_checked :
    subtree345.checkLayout code.toByteArray 334 357 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree365_rows_checked :
    subtree365.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_checkRow_reader reader_eq (by decide +kernel)

theorem subtree365_layout_checked :
    subtree365.checkLayout code.toByteArray 358 371 = true := by
  exact Table.checkLayout_reader reader_eq (by decide +kernel)

theorem subtree231_rows_checked :
    subtree231.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree222_rows_checked subtree239_rows_checked

theorem subtree231_layout_checked :
    subtree231.checkLayout code.toByteArray 217 250 = true := by
  exact Table.checkLayout_node_reader (next := 232) reader_eq (by decide +kernel)
    subtree222_layout_checked subtree239_layout_checked (by decide)

theorem subtree270_rows_checked :
    subtree270.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree264_rows_checked subtree278_rows_checked

theorem subtree270_layout_checked :
    subtree270.checkLayout code.toByteArray 251 286 = true := by
  exact Table.checkLayout_node_reader (next := 271) reader_eq (by decide +kernel)
    subtree264_layout_checked subtree278_layout_checked (by decide)

theorem subtree250_rows_checked :
    subtree250.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree231_rows_checked subtree270_rows_checked

theorem subtree250_layout_checked :
    subtree250.checkLayout code.toByteArray 217 286 = true := by
  exact Table.checkLayout_node_reader (next := 251) reader_eq (by decide +kernel)
    subtree231_layout_checked subtree270_layout_checked (by decide)

theorem subtree316_rows_checked :
    subtree316.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree293_rows_checked subtree328_rows_checked

theorem subtree316_layout_checked :
    subtree316.checkLayout code.toByteArray 287 333 = true := by
  exact Table.checkLayout_node_reader (next := 319) reader_eq (by decide +kernel)
    subtree293_layout_checked subtree328_layout_checked (by decide)

theorem subtree357_rows_checked :
    subtree357.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree345_rows_checked subtree365_rows_checked

theorem subtree357_layout_checked :
    subtree357.checkLayout code.toByteArray 334 371 = true := by
  exact Table.checkLayout_node_reader (next := 358) reader_eq (by decide +kernel)
    subtree345_layout_checked subtree365_layout_checked (by decide)

theorem subtree333_rows_checked :
    subtree333.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree316_rows_checked subtree357_rows_checked

theorem subtree333_layout_checked :
    subtree333.checkLayout code.toByteArray 287 371 = true := by
  exact Table.checkLayout_node_reader (next := 334) reader_eq (by decide +kernel)
    subtree316_layout_checked subtree357_layout_checked (by decide)

theorem subtree286_rows_checked :
    subtree286.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree250_rows_checked subtree333_rows_checked

theorem subtree286_layout_checked :
    subtree286.checkLayout code.toByteArray 217 371 = true := by
  exact Table.checkLayout_node_reader (next := 287) reader_eq (by decide +kernel)
    subtree250_layout_checked subtree333_layout_checked (by decide)

theorem subtree214_rows_checked :
    subtree214.all (checkRow code.toByteArray table 8) = true := by
  exact Table.all_node_reader reader_eq (by decide +kernel)
    subtree88_rows_checked subtree286_rows_checked

theorem subtree214_layout_checked :
    subtree214.checkLayout code.toByteArray 0 371 = true := by
  exact Table.checkLayout_node_reader (next := 217) reader_eq (by decide +kernel)
    subtree88_layout_checked subtree286_layout_checked (by decide)

end Blanc.Drip.StackSafety
