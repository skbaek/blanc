import Blanc.Composition.UniswapV2PairWeth9CapstoneKeys
import Blanc.Composition.UniswapV2PairWeth9ShareValue

/-!
# The closed history's Pair steps are swaps

`history_steps_swap`: every Pair step C4(a) attributes to the closed history decodes as a `swap`
entry: its frame is a settled non-static Pair frame, whose raw root is the history's only raw Pair
root, the `tx2` swap frame.  So C4(a)'s other-side (`X`) answer antecedent holds
(`answersSide_of_swaps`): `EntryFeeOff` and `EntryNoShrinkSide` are `True` at a `swap` (decision
uw9-c6-swap-kept: the history's only Pair step is the swap, whose `EntryNoShrinkSide` is `True`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.ExecutionTrace
  Blanc.Composition.UniswapV2PairWeth9Instance
open Blanc.Lift.Weth9.ClosedInstance (systemAddresses)

/-- A replay of `swap` invocations satisfies either side's answer condition. -/
theorem answersSide_of_swaps {side : TokenSide} :
    ∀ {st : UniswapV2Pair.State} {invs : List SourceInvocation},
      (∀ inv ∈ invs, ∃ a b r d, inv.entry = .swap a b r d) → sourceReplayAnswersSide side st invs
  | _, [], _ => trivial
  | st, inv :: rest, h => by
    obtain ⟨a, b, r, d, e⟩ := h inv List.mem_cons_self
    refine ⟨?_, ?_, answersSide_of_swaps (fun i hi => h i (List.mem_cons_of_mem _ hi))⟩
    · unfold EntryFeeOff; rw [e]; trivial
    · unfold EntryNoShrinkSide; rw [e]; trivial

/-- An entry authenticated at a root whose selector is `swap` is the decoded swap. -/
theorem pairEntryAt_swap {root : Exec.Deriv} {entry : UniswapV2Pair.Entry} (at_ : PairEntryAt root entry)
    (selector : Blanc.Sevm.selector root.sevm = 0x022c0d9f) :
    entry = swapDecodedEntry root.sevm := by
  cases at_
  case swap => rfl
  case view view sel =>
    rw [selector] at sel
    exfalso; revert sel
    rcases view with s | s | _ | s | _ | _
    all_goals (first | decide | (cases s <;> first | decide | (rename_i t; cases t <;> decide)))
  all_goals (rename_i sel; rw [selector] at sel; exact absurd sel (by decide))

/-- **Every Pair step of the closed history is a swap.** -/
theorem history_steps_swap {cfg : ChainConfig} {checkpoint future : BlockChain}
    {trace : ConfiguredHistoryTrace cfg checkpoint future} {sevm : Sevm} {b : Devm} {G : Nat}
    {out : Execution} {run : Exec 0 sevm (St b [] Mem.empty G) out}
    (h : Tx2Frame sevm (St b [] Mem.empty G))
    (cases : ∀ D ∈ trace.rawFrames, D.sevm.currentTarget ∈ systemAddresses ∨
      D.sevm.currentTarget = tokenX ∨ D = ⟨0, sevm, St b [] Mem.empty G, out, run⟩ ∨ Tx2Callee D)
    {steps : List PairStep}
    (observed : steps.flatMap (fun s => pairSubtreeFrames pair s.frame) =
      committedPairFrames pair trace)
    (auth : ∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) :
    ∀ inv ∈ steps.map PairStep.source, ∃ a b r d, inv.entry = .swap a b r d := by
  intro inv hinv
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hinv
  obtain ⟨-, -, target, static, entryAt⟩ := auth s hs
  have inSub : s.frame ∈ pairSubtreeFrames pair s.frame := by
    refine List.mem_flatMap.mpr ⟨s.frame, Exec.Frame.mem_committedFrames.mpr (Or.inl rfl), ?_⟩
    rw [pairFrameObs, ite_eq_left ⟨target, static⟩]
    exact List.mem_singleton_self _
  have inCommitted : s.frame ∈ committedPairFrames pair trace := by
    rw [← observed]
    exact List.mem_flatMap.mpr ⟨s, hs, inSub⟩
  obtain ⟨F, settled, obs⟩ := List.mem_flatMap.mp inCommitted
  have sameF : s.frame = F := by
    unfold pairFrameObs at obs
    split at obs
    · exact List.mem_singleton.mp obs
    · cases obs
  have raw := trace.mem_rawFrames_of_mem_settledFrames F settled
  have tF : (Blanc.Exec.Frame.rootDeriv F).sevm.currentTarget = pair := by
    rw [← sameF]; exact target
  have rootSevm : (Blanc.Exec.Frame.rootDeriv s.frame).sevm = sevm := by
    rw [sameF]
    rcases cases _ raw with hs' | hx | heq | callee
    · exact absurd tF (systemAddresses_ne hs' (Or.inr rfl))
    · rw [hx] at tF; exact absurd tF (by decide +kernel)
    · rw [heq]
    · exact absurd tF callee.target_ne_pair
  have entryEq := pairEntryAt_swap entryAt (by rw [rootSevm]; exact tx2_selector h.data)
  exact ⟨_, _, _, _, entryEq⟩

end Blanc.Composition.UniswapV2PairWeth9Capstone
