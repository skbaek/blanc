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

theorem codeSize_exact : codeSize = 2890 := by
  decide +kernel

theorem eip170RuntimeLimit_exact : eip170RuntimeLimit = 24576 := by
  rfl

theorem code_eip170 : codeSize <= eip170RuntimeLimit := by
  rw [codeSize_exact, eip170RuntimeLimit_exact]
  decide

theorem codeHeadroom_exact : codeHeadroom = 21686 := by
  unfold codeHeadroom
  rw [codeSize_exact, eip170RuntimeLimit_exact]

/-! ## Exact structural source-site inventories -/

private def isSstore : Ninst → Bool
  | .reg .sstore => true
  | _ => false

private def isStaticcall : Ninst → Bool
  | .exec .statcall => true
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

def sourceSitePcs (sites : List Prog.SourceSite) : List Nat :=
  sites.map fun site => site.pc

theorem runtimeSstoreSourceSites_length :
    runtimeSstoreSourceSites.length = 2 := by
  decide +kernel

theorem runtimeSstoreSourceSites_pcs :
    sourceSitePcs runtimeSstoreSourceSites = [1066, 2868] := by
  decide +kernel

theorem runtimeStaticcallSourceSites_length :
    runtimeStaticcallSourceSites.length = 11 := by
  decide +kernel

theorem runtimeStaticcallSourceSites_pcs :
    sourceSitePcs runtimeStaticcallSourceSites =
      [795, 822, 857, 895, 933, 971, 1009, 2617, 2689, 2744, 2829] := by
  decide +kernel

theorem runtimeLog1SourceSites_length :
    runtimeLog1SourceSites.length = 1 := by
  decide +kernel

theorem runtimeLog1SourceSites_pcs :
    sourceSitePcs runtimeLog1SourceSites = [782] := by
  decide +kernel

theorem runtimeExternalExecutionSourceSites_all_staticcall :
    (runtimeExternalExecutionSourceSites.all fun site =>
      match site.instruction with
      | .exec .statcall => true
      | _ => false) = true := by
  decide +kernel

theorem runtimeExternalExecutionSourceSites_length :
    runtimeExternalExecutionSourceSites.length = 11 := by
  decide +kernel

theorem runtimeExternalExecutionSourceSites_pcs :
    sourceSitePcs runtimeExternalExecutionSourceSites =
      [795, 822, 857, 895, 933, 971, 1009, 2617, 2689, 2744, 2829] := by
  decide +kernel

theorem runtimeMstore8SourceSites_length :
    runtimeMstore8SourceSites.length = 32 := by
  decide +kernel

theorem runtimeMstore8SourceSites_pcs :
    sourceSitePcs runtimeMstore8SourceSites =
      [122, 129, 136, 143, 150, 157, 164, 170,
       603, 611, 619, 627, 635, 643, 651, 658,
       689, 697, 705, 713, 721, 729, 737, 744,
       2557, 2564, 2571, 2578, 2585, 2592, 2599, 2605] := by
  decide +kernel

end Blanc.BeaconDeposit
