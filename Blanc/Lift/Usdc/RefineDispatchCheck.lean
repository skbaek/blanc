import Blanc.Lift.SelectorRoute
import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.Usdc.Decode

/-!
# Kernel checks for the USDC implementation's dispatcher

Decided facts about the generated implementation certificate (`Impl.cert`) that
`RefineDispatch.lean` consumes, kept in a module of their own so that the language server never
elaborates the kernel checks:

* `dispTree`, the selector comparison tree of entry `0` after the selector extraction;
* the 24 view selectors route into `viewEntries`, a reference-closed set of entries that is
  state-silent and exec-free (`view_routes`, `view_silent`, `view_execFree`);
* the four initializers route into wrappers that decode their arguments and call the function body
  (`init_routes`);
* every goto of the dispatcher is a row of `rows` whose wrapper checks the row's static head size,
  and every fallback leaf reverts (`decode_table`, `leaves_revert`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc.Lift

/-- The implementation's synthetic program. -/
abbrev implProg : List SFunc := Impl.cert.prog

/-- The dispatcher's comparison tree: entry `0` after `PUSH1 0 CALLDATALOAD PUSH1 0xe0 SHR`. -/
def dispTree : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide)) (.next (.reg .gt)
    (.next (.push [0x01, 0xd3] (by decide)) (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))

theorem tree_001a : Impl.t_001a_c0 = .next (.push [0x00] (by decide)) (.next (.reg .calldataload)
    (.next (.push [0xe0] (by decide)) (.next (.reg .shr) dispTree))) := rfl

theorem prog_zero : implProg[0]? = some Impl.t_0000_c0 := rfl

/-- The 24 selectors `decodeCall` reads as `view`. -/
def viewSels : List B256 :=
  [0xd9169487, 0x3644e515, 0x30adf81f, 0x7f2eecc3, 0xa0cc6a68, 0xdd62ed3e, 0xe94a0102, 0x70a08231,
   0xbd102430, 0xe5a6b10f, 0x313ce567, 0xfe575a87, 0xaa271e1a, 0x35d99f35, 0x8a6db9c3, 0x06fdde03,
   0x7ecebe00, 0x8da5cb5b, 0x5c975abb, 0x9fd0506d, 0x38a63183, 0x95d89b41, 0x18160ddd, 0x54fd4d50]

/-- The view wrappers and every entry they reach. -/
def viewEntries : List Nat :=
  [1, 2, 3, 6, 18, 21, 22, 23, 26, 27, 29, 32, 35, 38, 39, 40, 44, 45, 46, 47, 48, 49, 50, 57, 60,
   62, 63, 66, 70, 72, 73, 76, 77, 78, 83, 96, 106, 107, 128, 130, 131, 134, 135, 137, 140, 143,
   146, 147, 148, 152, 153, 154, 155, 156, 157, 164, 167, 169, 170, 173, 177, 179]

/-- Every view selector enters a wrapper in `viewEntries`. -/
theorem view_routes : viewSels.all (fun σ => match dispTree.selWalk σ with
    | .inl p => decide (p.2 ∈ viewEntries)
    | .inr _ => false) = true := by
  decide +kernel

/-- The view entries write no state. -/
theorem view_silent : SilentSet implProg viewEntries = true := by
  decide +kernel

/-- The view entries make no external call. -/
theorem view_execFree : ExecFreeSet implProg viewEntries = true := by
  decide +kernel

/-- The four initializers enter wrappers that decode their arguments and call the body. -/
theorem route_initialize : dispTree.selWalk 0x3357162b = .inl (0x3357162b, 168) := rfl
theorem route_initializeV2 : dispTree.selWalk 0xd608ea64 = .inl (0xd608ea64, 133) := rfl
theorem route_initializeV2_1 : dispTree.selWalk 0x2fc81e09 = .inl (0x2fc81e09, 171) := rfl
theorem route_initializeV2_2 : dispTree.selWalk 0x430239b4 = .inl (0x430239b4, 162) := rfl

theorem init_lookups : implProg[168]? = some Impl.t_058d_c168 ∧ implProg[61]? = some Impl.t_19e1_c61 ∧
    implProg[133]? = some Impl.t_0fc2_c133 ∧ implProg[25]? = some Impl.t_3744_c25 ∧
    implProg[171]? = some Impl.t_0501_c171 ∧ implProg[64]? = some Impl.t_1853_c64 ∧
    implProg[162]? = some Impl.t_0851_c162 ∧ implProg[55]? = some Impl.t_2538_c55 ∧
    implProg[5]? = some Impl.t_3771_c5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem init_toCall : Impl.t_058d_c168.toCall 61 = true ∧ Impl.t_0fc2_c133.toCall 25 = true ∧
    Impl.t_0501_c171.toCall 64 = true ∧ Impl.t_0851_c162.toCall 55 = true := by
  decide +kernel

/-- A wrapper that checks a static head of `h` words (none when `h = 0`). -/
def headOk (j h : Nat) : Bool :=
  h == 0 || match implProg[j]? with
    | some g => decide (g.headWord = some (Nat.toB256 (32 * h)))
    | none => false

/-- Every goto of the dispatcher is a row of `rows` whose wrapper checks the row's head size. -/
theorem decode_table : dispTree.selPairs.all (fun p =>
    match rows.find? (fun r => decide (r.sel = p.1)) with
    | some r => headOk p.2 r.headWords
    | none => false) = true := by
  decide +kernel

/-- Every fallback leaf of the dispatcher jumps to the revert at `0x36d` (entry 19). -/
theorem leaves_revert : dispTree.selLeaves.all (fun t => t.noHalt && t.refs.all (· ∈ [19])) = true ∧
    NoHaltSet implProg [19] = true := by
  decide +kernel

end Blanc.Lift.Usdc
