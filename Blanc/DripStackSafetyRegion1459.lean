import Blanc.DripStackSafety

/-!
Checked fourth 183-row region of the DRIP stack table. Every successor check
uses the complete 735-row table, including the conditional jump from PC 1227
in subtree1221 to PC 1735 in subtree1730.
-/

namespace Blanc.Drip.StackSafety

open Jaune AbstractStackSafety

theorem region1459_subtree1208_rows_checked :
    subtree1208.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1208_layout_checked :
    subtree1208.checkLayout code.toByteArray 1199 1214 = true := by
  decide +kernel

theorem region1459_subtree1221_rows_checked :
    subtree1221.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1221_layout_checked :
    subtree1221.checkLayout code.toByteArray 1215 1229 = true := by
  decide +kernel

theorem region1459_subtree1214_rows_checked :
    subtree1214.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1208_rows_checked
  · exact region1459_subtree1221_rows_checked

theorem region1459_subtree1214_layout_checked :
    subtree1214.checkLayout code.toByteArray 1199 1229 = true := by
  apply Table.checkLayout_node (next := 1215)
  · decide +kernel
  · exact region1459_subtree1208_layout_checked
  · exact region1459_subtree1221_layout_checked
  · decide +kernel

theorem region1459_subtree1239_rows_checked :
    subtree1239.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1239_layout_checked :
    subtree1239.checkLayout code.toByteArray 1231 1248 = true := by
  decide +kernel

theorem region1459_subtree1259_rows_checked :
    subtree1259.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1259_layout_checked :
    subtree1259.checkLayout code.toByteArray 1251 1265 = true := by
  decide +kernel

theorem region1459_subtree1248_rows_checked :
    subtree1248.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1239_rows_checked
  · exact region1459_subtree1259_rows_checked

theorem region1459_subtree1248_layout_checked :
    subtree1248.checkLayout code.toByteArray 1231 1265 = true := by
  apply Table.checkLayout_node (next := 1251)
  · decide +kernel
  · exact region1459_subtree1239_layout_checked
  · exact region1459_subtree1259_layout_checked
  · decide +kernel

theorem region1459_subtree1229_rows_checked :
    subtree1229.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1214_rows_checked
  · exact region1459_subtree1248_rows_checked

theorem region1459_subtree1229_layout_checked :
    subtree1229.checkLayout code.toByteArray 1199 1265 = true := by
  apply Table.checkLayout_node (next := 1231)
  · decide +kernel
  · exact region1459_subtree1214_layout_checked
  · exact region1459_subtree1248_layout_checked
  · decide +kernel

theorem region1459_subtree1283_rows_checked :
    subtree1283.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1283_layout_checked :
    subtree1283.checkLayout code.toByteArray 1266 1306 = true := by
  decide +kernel

theorem region1459_subtree1315_rows_checked :
    subtree1315.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1315_layout_checked :
    subtree1315.checkLayout code.toByteArray 1307 1338 = true := by
  decide +kernel

theorem region1459_subtree1306_rows_checked :
    subtree1306.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1283_rows_checked
  · exact region1459_subtree1315_rows_checked

theorem region1459_subtree1306_layout_checked :
    subtree1306.checkLayout code.toByteArray 1266 1338 = true := by
  apply Table.checkLayout_node (next := 1307)
  · decide +kernel
  · exact region1459_subtree1283_layout_checked
  · exact region1459_subtree1315_layout_checked
  · decide +kernel

theorem region1459_subtree1377_rows_checked :
    subtree1377.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1377_layout_checked :
    subtree1377.checkLayout code.toByteArray 1339 1447 = true := by
  decide +kernel

theorem region1459_subtree1454_rows_checked :
    subtree1454.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1454_layout_checked :
    subtree1454.checkLayout code.toByteArray 1448 1459 = true := by
  decide +kernel

theorem region1459_subtree1447_rows_checked :
    subtree1447.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1377_rows_checked
  · exact region1459_subtree1454_rows_checked

theorem region1459_subtree1447_layout_checked :
    subtree1447.checkLayout code.toByteArray 1339 1459 = true := by
  apply Table.checkLayout_node (next := 1448)
  · decide +kernel
  · exact region1459_subtree1377_layout_checked
  · exact region1459_subtree1454_layout_checked
  · decide +kernel

theorem region1459_subtree1338_rows_checked :
    subtree1338.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1306_rows_checked
  · exact region1459_subtree1447_rows_checked

theorem region1459_subtree1338_layout_checked :
    subtree1338.checkLayout code.toByteArray 1266 1459 = true := by
  apply Table.checkLayout_node (next := 1339)
  · decide +kernel
  · exact region1459_subtree1306_layout_checked
  · exact region1459_subtree1447_layout_checked
  · decide +kernel

theorem region1459_subtree1265_rows_checked :
    subtree1265.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1229_rows_checked
  · exact region1459_subtree1338_rows_checked

theorem region1459_subtree1265_layout_checked :
    subtree1265.checkLayout code.toByteArray 1199 1459 = true := by
  apply Table.checkLayout_node (next := 1266)
  · decide +kernel
  · exact region1459_subtree1229_layout_checked
  · exact region1459_subtree1338_layout_checked
  · decide +kernel

theorem region1459_subtree1465_rows_checked :
    subtree1465.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1465_layout_checked :
    subtree1465.checkLayout code.toByteArray 1460 1536 = true := by
  decide +kernel

theorem region1459_subtree1543_rows_checked :
    subtree1543.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1543_layout_checked :
    subtree1543.checkLayout code.toByteArray 1537 1561 = true := by
  decide +kernel

theorem region1459_subtree1536_rows_checked :
    subtree1536.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1465_rows_checked
  · exact region1459_subtree1543_rows_checked

theorem region1459_subtree1536_layout_checked :
    subtree1536.checkLayout code.toByteArray 1460 1561 = true := by
  apply Table.checkLayout_node (next := 1537)
  · decide +kernel
  · exact region1459_subtree1465_layout_checked
  · exact region1459_subtree1543_layout_checked
  · decide +kernel

theorem region1459_subtree1568_rows_checked :
    subtree1568.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1568_layout_checked :
    subtree1568.checkLayout code.toByteArray 1562 1575 = true := by
  decide +kernel

theorem region1459_subtree1625_rows_checked :
    subtree1625.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1625_layout_checked :
    subtree1625.checkLayout code.toByteArray 1588 1664 = true := by
  decide +kernel

theorem region1459_subtree1575_rows_checked :
    subtree1575.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1568_rows_checked
  · exact region1459_subtree1625_rows_checked

theorem region1459_subtree1575_layout_checked :
    subtree1575.checkLayout code.toByteArray 1562 1664 = true := by
  apply Table.checkLayout_node (next := 1588)
  · decide +kernel
  · exact region1459_subtree1568_layout_checked
  · exact region1459_subtree1625_layout_checked
  · decide +kernel

theorem region1459_subtree1561_rows_checked :
    subtree1561.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1536_rows_checked
  · exact region1459_subtree1575_rows_checked

theorem region1459_subtree1561_layout_checked :
    subtree1561.checkLayout code.toByteArray 1460 1664 = true := by
  apply Table.checkLayout_node (next := 1562)
  · decide +kernel
  · exact region1459_subtree1536_layout_checked
  · exact region1459_subtree1575_layout_checked
  · decide +kernel

theorem region1459_subtree1671_rows_checked :
    subtree1671.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1671_layout_checked :
    subtree1671.checkLayout code.toByteArray 1665 1711 = true := by
  decide +kernel

theorem region1459_subtree1717_rows_checked :
    subtree1717.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1717_layout_checked :
    subtree1717.checkLayout code.toByteArray 1712 1724 = true := by
  decide +kernel

theorem region1459_subtree1711_rows_checked :
    subtree1711.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1671_rows_checked
  · exact region1459_subtree1717_rows_checked

theorem region1459_subtree1711_layout_checked :
    subtree1711.checkLayout code.toByteArray 1665 1724 = true := by
  apply Table.checkLayout_node (next := 1712)
  · decide +kernel
  · exact region1459_subtree1671_layout_checked
  · exact region1459_subtree1717_layout_checked
  · decide +kernel

theorem region1459_subtree1730_rows_checked :
    subtree1730.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1730_layout_checked :
    subtree1730.checkLayout code.toByteArray 1725 1737 = true := by
  decide +kernel

theorem region1459_subtree1756_rows_checked :
    subtree1756.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1459_subtree1756_layout_checked :
    subtree1756.checkLayout code.toByteArray 1739 1762 = true := by
  decide +kernel

theorem region1459_subtree1737_rows_checked :
    subtree1737.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1730_rows_checked
  · exact region1459_subtree1756_rows_checked

theorem region1459_subtree1737_layout_checked :
    subtree1737.checkLayout code.toByteArray 1725 1762 = true := by
  apply Table.checkLayout_node (next := 1739)
  · decide +kernel
  · exact region1459_subtree1730_layout_checked
  · exact region1459_subtree1756_layout_checked
  · decide +kernel

theorem region1459_subtree1724_rows_checked :
    subtree1724.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1711_rows_checked
  · exact region1459_subtree1737_rows_checked

theorem region1459_subtree1724_layout_checked :
    subtree1724.checkLayout code.toByteArray 1665 1762 = true := by
  apply Table.checkLayout_node (next := 1725)
  · decide +kernel
  · exact region1459_subtree1711_layout_checked
  · exact region1459_subtree1737_layout_checked
  · decide +kernel

theorem region1459_subtree1664_rows_checked :
    subtree1664.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1561_rows_checked
  · exact region1459_subtree1724_rows_checked

theorem region1459_subtree1664_layout_checked :
    subtree1664.checkLayout code.toByteArray 1460 1762 = true := by
  apply Table.checkLayout_node (next := 1665)
  · decide +kernel
  · exact region1459_subtree1561_layout_checked
  · exact region1459_subtree1724_layout_checked
  · decide +kernel

theorem subtree1459_rows_checked :
    subtree1459.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1459_subtree1265_rows_checked
  · exact region1459_subtree1664_rows_checked

theorem subtree1459_layout_checked :
    subtree1459.checkLayout code.toByteArray 1199 1762 = true := by
  apply Table.checkLayout_node (next := 1460)
  · decide +kernel
  · exact region1459_subtree1265_layout_checked
  · exact region1459_subtree1664_layout_checked
  · decide +kernel

/-- PC 1227 lies in subtree1221; its taken successor PC 1735 lies in subtree1730. -/
theorem row1227_cross_pack_checked :
    checkRow code.toByteArray table 8 1227 [some 1735, none, none, none] = true := by
  decide +kernel

/-- Strict ordering and the exact region population are checked independently. -/
theorem subtree1459_order_and_size_checked :
    subtree1459.checkOrder = true ∧ subtree1459.size = 183 := by
  decide +kernel

end Blanc.Drip.StackSafety
