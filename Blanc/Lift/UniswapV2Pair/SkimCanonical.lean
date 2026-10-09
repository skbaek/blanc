import Blanc.Lift.UniswapV2Pair.SkimRawFacts
import Blanc.Lift.UniswapV2Pair.SkimHandler
import Blanc.Lift.UniswapV2Pair.LockedSupply
import Blanc.Lift.UniswapV2Pair.StaticViewTurns

/-!
# Canonical skim frame

Every successful raw skim run at the Pair code consumes the typed source skim over the
four external observations, with turn queues DERIVED from the actual child executions:
the two balance queries contribute their retained static Pair views, the two transfers
contribute their retained committed Pair frames (the lock-free entries, via
`lockedPairSupply`) and their actual foreign LOGs. The Pair storage after the run is the
final source state's finite representation; the trace-local key universe is HASH-T.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Decoded rows of every actually entered Pair frame of the run (HASH-T universe rows). -/
def skimTraceKeys (root : Exec.Deriv) : List WriterKey :=
  (Exec.rawFrameRoots root.exc).flatMap fun F =>
    if F.sevm.currentTarget = root.sevm.currentTarget
    then pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm else []

theorem skimTraceKeys_contains {root : Exec.Deriv} {F : Exec.Deriv}
    (member : F ∈ Exec.rawFrameRoots root.exc)
    (target : F.sevm.currentTarget = root.sevm.currentTarget) :
    (∀ k ∈ pairDecodedKeys F.sevm, k ∈ skimTraceKeys root) ∧
      ∀ k ∈ staticViewDecodedKeys F.sevm, k ∈ skimTraceKeys root := by
  have inside : ∀ k ∈ pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm,
      k ∈ skimTraceKeys root := by
    intro k touched
    apply List.mem_flatMap.mpr
    refine ⟨F, member, ?_⟩
    rw [ite_eq_left target]
    exact touched
  exact ⟨fun k touched => inside k (List.mem_append_left _ touched),
    fun k touched => inside k (List.mem_append_right _ touched)⟩

/-- The actual first query and transfer0 steps of the run, up to their forwarded gas. -/
def SkimFirstSteps (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (out0 : Bytes) (d : Devm) :
    Prop :=
  ∃ (S0 S1 : List B256) (M0 M1 : Mem) (g0 g1 : Nat) (d0 : Devm),
    Blanc.Lift.StepIn D sevm (St (temporalAccountAccessBase (skimCachedWorld sevm b)
      (skimToken0 sevm b).toAdr) S0 M0 g0) (.exec .staticcall) d0 ∧ d0.returnData = out0 ∧
    Blanc.Lift.StepIn D sevm (St d0 S1 M1 g1) (.exec .call) d

/-- The actual second query and transfer1 steps after transfer0's world `d`. -/
def SkimSecondSteps (D : Exec.Deriv) (sevm : Sevm) (d : Devm) (t1 : B256) (out1 : Bytes)
    (d2 : Devm) : Prop :=
  ∃ (S0 S1 : List B256) (M0 M1 : Mem) (g0 g1 : Nat) (d1 : Devm),
    Blanc.Lift.StepIn D sevm (St (temporalAccountAccessBase (afterSload sevm d 8)
      (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) S0 M0 g0) (.exec .staticcall) d1 ∧
    d1.returnData = out1 ∧ Blanc.Lift.StepIn D sevm (St d1 S1 M1 g1) (.exec .call) d2

end Blanc.Lift.UniswapV2Pair
