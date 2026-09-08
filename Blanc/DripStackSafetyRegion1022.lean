import Blanc.DripStackSafety

/-!
Checked third 183-row region of the DRIP stack table. Every successor check
uses the complete 735-row table, including the conditional jump from PC 1165
to PC 1212 outside this region.
-/

namespace Blanc.Drip.StackSafety

open Jaune AbstractStackSafety

theorem region1022_subtree861_rows_checked :
    subtree861.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree861_layout_checked :
    subtree861.checkLayout code.toByteArray 840 868 = true := by
  decide +kernel

theorem region1022_subtree888_rows_checked :
    subtree888.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree888_layout_checked :
    subtree888.checkLayout code.toByteArray 869 897 = true := by
  decide +kernel

theorem region1022_subtree868_rows_checked :
    subtree868.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree861_rows_checked
  · exact region1022_subtree888_rows_checked

theorem region1022_subtree868_layout_checked :
    subtree868.checkLayout code.toByteArray 840 897 = true := by
  apply Table.checkLayout_node (next := 869)
  · decide +kernel
  · exact region1022_subtree861_layout_checked
  · exact region1022_subtree888_layout_checked
  · decide +kernel

theorem region1022_subtree905_rows_checked :
    subtree905.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree905_layout_checked :
    subtree905.checkLayout code.toByteArray 898 927 = true := by
  decide +kernel

theorem region1022_subtree937_rows_checked :
    subtree937.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree937_layout_checked :
    subtree937.checkLayout code.toByteArray 930 942 = true := by
  decide +kernel

theorem region1022_subtree927_rows_checked :
    subtree927.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree905_rows_checked
  · exact region1022_subtree937_rows_checked

theorem region1022_subtree927_layout_checked :
    subtree927.checkLayout code.toByteArray 898 942 = true := by
  apply Table.checkLayout_node (next := 930)
  · decide +kernel
  · exact region1022_subtree905_layout_checked
  · exact region1022_subtree937_layout_checked
  · decide +kernel

theorem region1022_subtree897_rows_checked :
    subtree897.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree868_rows_checked
  · exact region1022_subtree927_rows_checked

theorem region1022_subtree897_layout_checked :
    subtree897.checkLayout code.toByteArray 840 942 = true := by
  apply Table.checkLayout_node (next := 898)
  · decide +kernel
  · exact region1022_subtree868_layout_checked
  · exact region1022_subtree927_layout_checked
  · decide +kernel

theorem region1022_subtree948_rows_checked :
    subtree948.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree948_layout_checked :
    subtree948.checkLayout code.toByteArray 943 954 = true := by
  decide +kernel

theorem region1022_subtree963_rows_checked :
    subtree963.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree963_layout_checked :
    subtree963.checkLayout code.toByteArray 955 968 = true := by
  decide +kernel

theorem region1022_subtree954_rows_checked :
    subtree954.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree948_rows_checked
  · exact region1022_subtree963_rows_checked

theorem region1022_subtree954_layout_checked :
    subtree954.checkLayout code.toByteArray 943 968 = true := by
  apply Table.checkLayout_node (next := 955)
  · decide +kernel
  · exact region1022_subtree948_layout_checked
  · exact region1022_subtree963_layout_checked
  · decide +kernel

theorem region1022_subtree976_rows_checked :
    subtree976.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree976_layout_checked :
    subtree976.checkLayout code.toByteArray 969 994 = true := by
  decide +kernel

theorem region1022_subtree1014_rows_checked :
    subtree1014.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree1014_layout_checked :
    subtree1014.checkLayout code.toByteArray 995 1022 = true := by
  decide +kernel

theorem region1022_subtree994_rows_checked :
    subtree994.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree976_rows_checked
  · exact region1022_subtree1014_rows_checked

theorem region1022_subtree994_layout_checked :
    subtree994.checkLayout code.toByteArray 969 1022 = true := by
  apply Table.checkLayout_node (next := 995)
  · decide +kernel
  · exact region1022_subtree976_layout_checked
  · exact region1022_subtree1014_layout_checked
  · decide +kernel

theorem region1022_subtree968_rows_checked :
    subtree968.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree954_rows_checked
  · exact region1022_subtree994_rows_checked

theorem region1022_subtree968_layout_checked :
    subtree968.checkLayout code.toByteArray 943 1022 = true := by
  apply Table.checkLayout_node (next := 969)
  · decide +kernel
  · exact region1022_subtree954_layout_checked
  · exact region1022_subtree994_layout_checked
  · decide +kernel

theorem region1022_subtree942_rows_checked :
    subtree942.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree897_rows_checked
  · exact region1022_subtree968_rows_checked

theorem region1022_subtree942_layout_checked :
    subtree942.checkLayout code.toByteArray 840 1022 = true := by
  apply Table.checkLayout_node (next := 943)
  · decide +kernel
  · exact region1022_subtree897_layout_checked
  · exact region1022_subtree968_layout_checked
  · decide +kernel

theorem region1022_subtree1028_rows_checked :
    subtree1028.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree1028_layout_checked :
    subtree1028.checkLayout code.toByteArray 1023 1036 = true := by
  decide +kernel

theorem region1022_subtree1045_rows_checked :
    subtree1045.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree1045_layout_checked :
    subtree1045.checkLayout code.toByteArray 1037 1054 = true := by
  decide +kernel

theorem region1022_subtree1036_rows_checked :
    subtree1036.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree1028_rows_checked
  · exact region1022_subtree1045_rows_checked

theorem region1022_subtree1036_layout_checked :
    subtree1036.checkLayout code.toByteArray 1023 1054 = true := by
  apply Table.checkLayout_node (next := 1037)
  · decide +kernel
  · exact region1022_subtree1028_layout_checked
  · exact region1022_subtree1045_layout_checked
  · decide +kernel

theorem region1022_subtree1062_rows_checked :
    subtree1062.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree1062_layout_checked :
    subtree1062.checkLayout code.toByteArray 1056 1070 = true := by
  decide +kernel

theorem region1022_subtree1090_rows_checked :
    subtree1090.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree1090_layout_checked :
    subtree1090.checkLayout code.toByteArray 1073 1097 = true := by
  decide +kernel

theorem region1022_subtree1070_rows_checked :
    subtree1070.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree1062_rows_checked
  · exact region1022_subtree1090_rows_checked

theorem region1022_subtree1070_layout_checked :
    subtree1070.checkLayout code.toByteArray 1056 1097 = true := by
  apply Table.checkLayout_node (next := 1073)
  · decide +kernel
  · exact region1022_subtree1062_layout_checked
  · exact region1022_subtree1090_layout_checked
  · decide +kernel

theorem region1022_subtree1054_rows_checked :
    subtree1054.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree1036_rows_checked
  · exact region1022_subtree1070_rows_checked

theorem region1022_subtree1054_layout_checked :
    subtree1054.checkLayout code.toByteArray 1023 1097 = true := by
  apply Table.checkLayout_node (next := 1056)
  · decide +kernel
  · exact region1022_subtree1036_layout_checked
  · exact region1022_subtree1070_layout_checked
  · decide +kernel

theorem region1022_subtree1119_rows_checked :
    subtree1119.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree1119_layout_checked :
    subtree1119.checkLayout code.toByteArray 1110 1125 = true := by
  decide +kernel

theorem region1022_subtree1131_rows_checked :
    subtree1131.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree1131_layout_checked :
    subtree1131.checkLayout code.toByteArray 1126 1137 = true := by
  decide +kernel

theorem region1022_subtree1125_rows_checked :
    subtree1125.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree1119_rows_checked
  · exact region1022_subtree1131_rows_checked

theorem region1022_subtree1125_layout_checked :
    subtree1125.checkLayout code.toByteArray 1110 1137 = true := by
  apply Table.checkLayout_node (next := 1126)
  · decide +kernel
  · exact region1022_subtree1119_layout_checked
  · exact region1022_subtree1131_layout_checked
  · decide +kernel

theorem region1022_subtree1148_rows_checked :
    subtree1148.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree1148_layout_checked :
    subtree1148.checkLayout code.toByteArray 1140 1156 = true := by
  decide +kernel

theorem region1022_subtree1165_rows_checked :
    subtree1165.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem region1022_subtree1165_layout_checked :
    subtree1165.checkLayout code.toByteArray 1157 1182 = true := by
  decide +kernel

theorem region1022_subtree1156_rows_checked :
    subtree1156.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree1148_rows_checked
  · exact region1022_subtree1165_rows_checked

theorem region1022_subtree1156_layout_checked :
    subtree1156.checkLayout code.toByteArray 1140 1182 = true := by
  apply Table.checkLayout_node (next := 1157)
  · decide +kernel
  · exact region1022_subtree1148_layout_checked
  · exact region1022_subtree1165_layout_checked
  · decide +kernel

theorem region1022_subtree1137_rows_checked :
    subtree1137.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree1125_rows_checked
  · exact region1022_subtree1156_rows_checked

theorem region1022_subtree1137_layout_checked :
    subtree1137.checkLayout code.toByteArray 1110 1182 = true := by
  apply Table.checkLayout_node (next := 1140)
  · decide +kernel
  · exact region1022_subtree1125_layout_checked
  · exact region1022_subtree1156_layout_checked
  · decide +kernel

theorem region1022_subtree1097_rows_checked :
    subtree1097.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree1054_rows_checked
  · exact region1022_subtree1137_rows_checked

theorem region1022_subtree1097_layout_checked :
    subtree1097.checkLayout code.toByteArray 1023 1182 = true := by
  apply Table.checkLayout_node (next := 1110)
  · decide +kernel
  · exact region1022_subtree1054_layout_checked
  · exact region1022_subtree1137_layout_checked
  · decide +kernel

theorem subtree1022_rows_checked :
    subtree1022.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact region1022_subtree942_rows_checked
  · exact region1022_subtree1097_rows_checked

theorem subtree1022_layout_checked :
    subtree1022.checkLayout code.toByteArray 840 1182 = true := by
  apply Table.checkLayout_node (next := 1023)
  · decide +kernel
  · exact region1022_subtree942_layout_checked
  · exact region1022_subtree1097_layout_checked
  · decide +kernel

/-- PC 1165 lies in subtree1022; its taken successor PC 1212 is outside subtree1022. -/
theorem row1165_cross_region_checked :
    checkRow code.toByteArray table 8 1165 [some 1212, none, none] = true := by
  decide +kernel

/-- Strict ordering and the exact region population are checked independently. -/
theorem subtree1022_order_and_size_checked :
    subtree1022.checkOrder = true ∧ subtree1022.size = 183 := by
  decide +kernel

end Blanc.Drip.StackSafety
