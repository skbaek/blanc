import Blanc.BeaconDeposit
import Blanc.ExecutionOccurrence

/-!
# Beacon deposit compiled runtime artifact

Compiler-owned bytes, selector and size metadata, and fail-closed structural
source-site inventories for the BeaconDeposit runtime.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-! ## Compiler artifact -/

def code : Bytes :=
  (Prog.compile runtime).getD []

def selectors : List B256 :=
  funcs.map Prod.fst

def eip170RuntimeLimit : Nat :=
  pragueCodeLimits.maxCodeSize

def codeSize : Nat := code.length

def codeHeadroom : Nat :=
  eip170RuntimeLimit - codeSize

theorem runtime_compiles : Prog.compiles runtime = true := by
  decide +kernel

theorem code_eq_compiler_output :
    code = (Prog.compile runtime).getD [] := by
  rfl

theorem code_compile : Prog.compile runtime = some code := by
  unfold code
  exact Prog.compile_eq_some_getD_of_compiles _ runtime_compiles

theorem selectors_eq_beaconSelectors : selectors = beaconSelectors := by
  rfl

theorem codeSize_exact : codeSize = 2891 := by
  decide +kernel

theorem eip170RuntimeLimit_exact : eip170RuntimeLimit = 24576 := by
  rfl

theorem code_eip170 : codeSize <= eip170RuntimeLimit := by
  rw [codeSize_exact, eip170RuntimeLimit_exact]
  decide

theorem codeHeadroom_exact : codeHeadroom = 21685 := by
  unfold codeHeadroom
  rw [codeSize_exact, eip170RuntimeLimit_exact]

/-! ## Exact structural source-site inventories -/

private def isSstore : Ninst → Bool
  | .reg .sstore => true
  | _ => false

private def isStaticcall : Ninst → Bool
  | .exec .staticcall => true
  | _ => false

private def isLog1 : Ninst → Bool
  | .reg (.log 1) => true
  | _ => false

private def isExternalExecution : Ninst → Bool
  | .exec _ => true
  | _ => false

private def isMstore8 : Ninst → Bool
  | .reg .mstore8 => true
  | _ => false

private def sourceSitesMatching
    (predicate : Ninst → Bool) : List Prog.SourceSite :=
  runtime.sourceSites.filter fun site => predicate site.instruction

def runtimeSstoreSourceSites : List Prog.SourceSite :=
  sourceSitesMatching isSstore

def runtimeStaticcallSourceSites : List Prog.SourceSite :=
  sourceSitesMatching isStaticcall

def runtimeLog1SourceSites : List Prog.SourceSite :=
  sourceSitesMatching isLog1

def runtimeExternalExecutionSourceSites : List Prog.SourceSite :=
  sourceSitesMatching isExternalExecution

def runtimeMstore8SourceSites : List Prog.SourceSite :=
  sourceSitesMatching isMstore8

/-- Membership in the runtime SSTORE inventory is exactly membership in the
compiler source map at a source-level SSTORE instruction. -/
theorem mem_runtimeSstoreSourceSites_iff
    {site : Prog.SourceSite} :
    site ∈ runtimeSstoreSourceSites ↔
      site ∈ runtime.sourceSites ∧ site.instruction = .reg .sstore := by
  rcases site with ⟨path, pc, instruction⟩
  cases instruction <;>
    simp [runtimeSstoreSourceSites, sourceSitesMatching, isSstore]
  rename_i regular
  cases regular <;>
    simp

theorem runtimeSstoreSourceSites_length :
    runtimeSstoreSourceSites.length = 2 := by
  decide +kernel

theorem runtimeSstoreSourceSites_pcs :
    Prog.SourceSite.pcs runtimeSstoreSourceSites = [1070, 2869] := by
  decide +kernel

/-- Coupled function-table/PC identities for the two runtime write sites.
Keeping the coordinates paired prevents a consumer from mixing the main-body
count site with the insertion-loop branch site. -/
theorem runtimeSstoreSourceSites_coordinates :
    Prog.SourceSite.coordinates runtimeSstoreSourceSites =
      [(0, 1070), (13, 2869)] := by
  decide +kernel

/-- The complete runtime source-level SSTORE population is the count write in
the main deposit body or the branch write in the insertion-loop auxiliary. -/
theorem runtimeSstoreSourceSite_pc
    {site : Prog.SourceSite}
    (member : site ∈ runtimeSstoreSourceSites) :
    site.pc = 1070 ∨ site.pc = 2869 := by
  have pcMember : site.pc ∈ Prog.SourceSite.pcs runtimeSstoreSourceSites :=
    List.mem_map_of_mem member
  rw [runtimeSstoreSourceSites_pcs] at pcMember
  simpa using pcMember

theorem runtimeSstoreSourceSite_coordinate
    {site : Prog.SourceSite}
    (member : site ∈ runtimeSstoreSourceSites) :
    (site.path.functionIndex = 0 ∧ site.pc = 1070) ∨
      (site.path.functionIndex = 13 ∧ site.pc = 2869) := by
  have coordinateMember :
      (site.path.functionIndex, site.pc) ∈
        Prog.SourceSite.coordinates runtimeSstoreSourceSites :=
    List.mem_map_of_mem member
  rw [runtimeSstoreSourceSites_coordinates] at coordinateMember
  simpa using coordinateMember

theorem runtimeStaticcallSourceSites_length :
    runtimeStaticcallSourceSites.length = 11 := by
  decide +kernel

theorem runtimeStaticcallSourceSites_pcs :
    Prog.SourceSite.pcs runtimeStaticcallSourceSites =
      [799, 826, 861, 899, 937, 975, 1013, 2618, 2690, 2745, 2830] := by
  decide +kernel

theorem runtimeLog1SourceSites_length :
    runtimeLog1SourceSites.length = 1 := by
  decide +kernel

theorem runtimeLog1SourceSites_pcs :
    Prog.SourceSite.pcs runtimeLog1SourceSites = [786] := by
  decide +kernel

theorem runtimeExternalExecutionSourceSites_all_staticcall :
    (runtimeExternalExecutionSourceSites.all fun site =>
      match site.instruction with
      | .exec .staticcall => true
      | _ => false) = true := by
  decide +kernel

theorem runtimeExternalExecutionSourceSites_length :
    runtimeExternalExecutionSourceSites.length = 11 := by
  decide +kernel

theorem runtimeExternalExecutionSourceSites_pcs :
    Prog.SourceSite.pcs runtimeExternalExecutionSourceSites =
      [799, 826, 861, 899, 937, 975, 1013, 2618, 2690, 2745, 2830] := by
  decide +kernel

theorem runtimeMstore8SourceSites_length :
    runtimeMstore8SourceSites.length = 32 := by
  decide +kernel

theorem runtimeMstore8SourceSites_pcs :
    Prog.SourceSite.pcs runtimeMstore8SourceSites =
      [134, 141, 148, 155, 162, 169, 176, 182,
       607, 615, 623, 631, 639, 647, 655, 662,
       693, 701, 709, 717, 725, 733, 741, 748,
       2558, 2565, 2572, 2579, 2586, 2593, 2600, 2606] := by
  decide +kernel

end Blanc.BeaconDeposit
