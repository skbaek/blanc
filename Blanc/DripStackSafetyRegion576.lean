import Blanc.DripStackSafety

/-!
Checked second 183-row region of the DRIP stack table. Every successor check
uses the complete 735-row table, including the conditional jump from PC 686
to PC 947 outside this region.
-/

namespace Blanc.Drip.StackSafety

open Jaune AbstractStackSafety

theorem subtree379_rows_checked :
    subtree379.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree379_layout_checked :
    subtree379.checkLayout code.toByteArray 372 387 = true := by
  decide +kernel

theorem subtree411_rows_checked :
    subtree411.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree411_layout_checked :
    subtree411.checkLayout code.toByteArray 388 433 = true := by
  decide +kernel

theorem subtree387_rows_checked :
    subtree387.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree379_rows_checked
  · exact subtree411_rows_checked

theorem subtree387_layout_checked :
    subtree387.checkLayout code.toByteArray 372 433 = true := by
  apply Table.checkLayout_node (next := 388)
  · decide +kernel
  · exact subtree379_layout_checked
  · exact subtree411_layout_checked
  · decide +kernel

theorem subtree473_rows_checked :
    subtree473.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree473_layout_checked :
    subtree473.checkLayout code.toByteArray 434 498 = true := by
  decide +kernel

theorem subtree508_rows_checked :
    subtree508.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree508_layout_checked :
    subtree508.checkLayout code.toByteArray 500 515 = true := by
  decide +kernel

theorem subtree498_rows_checked :
    subtree498.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree473_rows_checked
  · exact subtree508_rows_checked

theorem subtree498_layout_checked :
    subtree498.checkLayout code.toByteArray 434 515 = true := by
  apply Table.checkLayout_node (next := 500)
  · decide +kernel
  · exact subtree473_layout_checked
  · exact subtree508_layout_checked
  · decide +kernel

theorem subtree433_rows_checked :
    subtree433.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree387_rows_checked
  · exact subtree498_rows_checked

theorem subtree433_layout_checked :
    subtree433.checkLayout code.toByteArray 372 515 = true := by
  apply Table.checkLayout_node (next := 434)
  · decide +kernel
  · exact subtree387_layout_checked
  · exact subtree498_layout_checked
  · decide +kernel

theorem subtree525_rows_checked :
    subtree525.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree525_layout_checked :
    subtree525.checkLayout code.toByteArray 516 533 = true := by
  decide +kernel

theorem subtree539_rows_checked :
    subtree539.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree539_layout_checked :
    subtree539.checkLayout code.toByteArray 534 544 = true := by
  decide +kernel

theorem subtree533_rows_checked :
    subtree533.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree525_rows_checked
  · exact subtree539_rows_checked

theorem subtree533_layout_checked :
    subtree533.checkLayout code.toByteArray 516 544 = true := by
  apply Table.checkLayout_node (next := 534)
  · decide +kernel
  · exact subtree525_layout_checked
  · exact subtree539_layout_checked
  · decide +kernel

theorem subtree550_rows_checked :
    subtree550.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree550_layout_checked :
    subtree550.checkLayout code.toByteArray 545 562 = true := by
  decide +kernel

theorem subtree570_rows_checked :
    subtree570.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree570_layout_checked :
    subtree570.checkLayout code.toByteArray 563 576 = true := by
  decide +kernel

theorem subtree562_rows_checked :
    subtree562.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree550_rows_checked
  · exact subtree570_rows_checked

theorem subtree562_layout_checked :
    subtree562.checkLayout code.toByteArray 545 576 = true := by
  apply Table.checkLayout_node (next := 563)
  · decide +kernel
  · exact subtree550_layout_checked
  · exact subtree570_layout_checked
  · decide +kernel

theorem subtree544_rows_checked :
    subtree544.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree533_rows_checked
  · exact subtree562_rows_checked

theorem subtree544_layout_checked :
    subtree544.checkLayout code.toByteArray 516 576 = true := by
  apply Table.checkLayout_node (next := 545)
  · decide +kernel
  · exact subtree533_layout_checked
  · exact subtree562_layout_checked
  · decide +kernel

theorem subtree515_rows_checked :
    subtree515.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree433_rows_checked
  · exact subtree544_rows_checked

theorem subtree515_layout_checked :
    subtree515.checkLayout code.toByteArray 372 576 = true := by
  apply Table.checkLayout_node (next := 516)
  · decide +kernel
  · exact subtree433_layout_checked
  · exact subtree544_layout_checked
  · decide +kernel

theorem subtree584_rows_checked :
    subtree584.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree584_layout_checked :
    subtree584.checkLayout code.toByteArray 577 592 = true := by
  decide +kernel

theorem subtree617_rows_checked :
    subtree617.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree617_layout_checked :
    subtree617.checkLayout code.toByteArray 593 625 = true := by
  decide +kernel

theorem subtree592_rows_checked :
    subtree592.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree584_rows_checked
  · exact subtree617_rows_checked

theorem subtree592_layout_checked :
    subtree592.checkLayout code.toByteArray 577 625 = true := by
  apply Table.checkLayout_node (next := 593)
  · decide +kernel
  · exact subtree584_layout_checked
  · exact subtree617_layout_checked
  · decide +kernel

theorem subtree663_rows_checked :
    subtree663.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree663_layout_checked :
    subtree663.checkLayout code.toByteArray 626 683 = true := by
  decide +kernel

theorem subtree708_rows_checked :
    subtree708.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree708_layout_checked :
    subtree708.checkLayout code.toByteArray 686 716 = true := by
  decide +kernel

theorem subtree683_rows_checked :
    subtree683.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree663_rows_checked
  · exact subtree708_rows_checked

theorem subtree683_layout_checked :
    subtree683.checkLayout code.toByteArray 626 716 = true := by
  apply Table.checkLayout_node (next := 686)
  · decide +kernel
  · exact subtree663_layout_checked
  · exact subtree708_layout_checked
  · decide +kernel

theorem subtree625_rows_checked :
    subtree625.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree592_rows_checked
  · exact subtree683_rows_checked

theorem subtree625_layout_checked :
    subtree625.checkLayout code.toByteArray 577 716 = true := by
  apply Table.checkLayout_node (next := 626)
  · decide +kernel
  · exact subtree592_layout_checked
  · exact subtree683_layout_checked
  · decide +kernel

theorem subtree755_rows_checked :
    subtree755.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree755_layout_checked :
    subtree755.checkLayout code.toByteArray 749 764 = true := by
  decide +kernel

theorem subtree776_rows_checked :
    subtree776.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree776_layout_checked :
    subtree776.checkLayout code.toByteArray 765 794 = true := by
  decide +kernel

theorem subtree764_rows_checked :
    subtree764.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree755_rows_checked
  · exact subtree776_rows_checked

theorem subtree764_layout_checked :
    subtree764.checkLayout code.toByteArray 749 794 = true := by
  apply Table.checkLayout_node (next := 765)
  · decide +kernel
  · exact subtree755_layout_checked
  · exact subtree776_layout_checked
  · decide +kernel

theorem subtree802_rows_checked :
    subtree802.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree802_layout_checked :
    subtree802.checkLayout code.toByteArray 795 811 = true := by
  decide +kernel

theorem subtree833_rows_checked :
    subtree833.all (checkRow code.toByteArray table 8) = true := by
  decide +kernel

theorem subtree833_layout_checked :
    subtree833.checkLayout code.toByteArray 814 839 = true := by
  decide +kernel

theorem subtree811_rows_checked :
    subtree811.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree802_rows_checked
  · exact subtree833_rows_checked

theorem subtree811_layout_checked :
    subtree811.checkLayout code.toByteArray 795 839 = true := by
  apply Table.checkLayout_node (next := 814)
  · decide +kernel
  · exact subtree802_layout_checked
  · exact subtree833_layout_checked
  · decide +kernel

theorem subtree794_rows_checked :
    subtree794.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree764_rows_checked
  · exact subtree811_rows_checked

theorem subtree794_layout_checked :
    subtree794.checkLayout code.toByteArray 749 839 = true := by
  apply Table.checkLayout_node (next := 795)
  · decide +kernel
  · exact subtree764_layout_checked
  · exact subtree811_layout_checked
  · decide +kernel

theorem subtree716_rows_checked :
    subtree716.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree625_rows_checked
  · exact subtree794_rows_checked

theorem subtree716_layout_checked :
    subtree716.checkLayout code.toByteArray 577 839 = true := by
  apply Table.checkLayout_node (next := 749)
  · decide +kernel
  · exact subtree625_layout_checked
  · exact subtree794_layout_checked
  · decide +kernel

theorem subtree576_rows_checked :
    subtree576.all (checkRow code.toByteArray table 8) = true := by
  apply Table.all_node
  · decide +kernel
  · exact subtree515_rows_checked
  · exact subtree716_rows_checked

theorem subtree576_layout_checked :
    subtree576.checkLayout code.toByteArray 372 839 = true := by
  apply Table.checkLayout_node (next := 577)
  · decide +kernel
  · exact subtree515_layout_checked
  · exact subtree716_layout_checked
  · decide +kernel

/-- PC 686 lies in subtree716; its taken successor PC 947 is outside subtree576. -/
theorem row686_cross_region_checked :
    checkRow code.toByteArray table 8 686 [some 947, none] = true := by
  decide +kernel

/-- Strict ordering and the exact region population are checked independently. -/
theorem subtree576_order_and_size_checked :
    subtree576.checkOrder = true ∧ subtree576.size = 183 := by
  decide +kernel

end Blanc.Drip.StackSafety
