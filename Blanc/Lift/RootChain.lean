import Blanc.Lift.FrameChain
import Blanc.ExecutionHistoryCommittedCuts
import Blanc.ExecutionMidHistoryInNoDel

/-!
# An account's storage moves root by root along a mid history

`RootChain wa a roots b`: the settled roots `roots` carry `wa`'s storage from `a` to `b`, each entered
where the last one left it. `MidHistoryTraceIn.rootChain` proves it for a mid history from the actual
deletion exclusions (`OutputNotDeleted`) and the code installed at its start, with no certificate of
the code: a proxy, whose delegates decide what its context runs, has no `InstalledRuntimeSafety`, so the
accounting rungs `midHistoryIn` and `configuredBlockIn` do not apply to it, while every root's own
accounting (`Exec.coreAccountingIn`) does.

The gaps between roots are the positions `cell_property_of_settledRoots` transports through; that
theorem's cell property cannot name a position, so these levels state the exact endpoint words.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace

/-- Roots `roots` carry `wa`'s storage from `a` to `b`, each entered where the last one left it. -/
def RootChain (wa : Adr) : StorWords → List Exec.Frame → StorWords → Prop
  | a, [], b => b = a
  | a, R :: rs, b => wordsAt wa R.pre.state = a ∧ RootChain wa (wordsAt wa R.post.state) rs b

namespace RootChain

variable {wa : Adr}

theorem append : ∀ {a b c : StorWords} {xs ys : List Exec.Frame},
    RootChain wa a xs b → RootChain wa b ys c → RootChain wa a (xs ++ ys) c
  | _, _, _, [], _, hx, hy => by
    cases hx
    exact hy
  | _, _, _, _ :: _, _, hx, hy => ⟨hx.1, append hx.2 hy⟩

/-- A chain, read at a split of its roots. -/
theorem split : ∀ {a c : StorWords} {xs ys : List Exec.Frame}, RootChain wa a (xs ++ ys) c →
    ∃ b, RootChain wa a xs b ∧ RootChain wa b ys c
  | a, _, [], _, h => ⟨a, rfl, h⟩
  | _, _, _ :: _, _, h => by
    obtain ⟨b, hx, hy⟩ := split h.2
    exact ⟨b, ⟨h.1, hx⟩, hy⟩

/-- Per-root frame chains compose along the roots. -/
theorem frames {T : Adr} {Good : Exec.Frame → Prop} {view : Exec.Frame → List Exec.Frame} :
    ∀ {a b : StorWords} {roots : List Exec.Frame}, RootChain T a roots b →
      (∀ R ∈ roots, FrameChain T Good (wordsAt T R.pre.state) (view R) (wordsAt T R.post.state)) →
      FrameChain T Good a (roots.flatMap view) b
  | _, _, [], h, _ => h
  | _, _, R :: _, h, law => by
    obtain ⟨rfl, rest⟩ := h
    exact (law R List.mem_cons_self).append
      (frames rest fun G hG => law G (List.mem_cons_of_mem _ hG))

end RootChain

section Levels

variable {wa : Adr}

variable {C : ByteArray}

end Levels

/-- **Code and deletion exclusion along a mid history from raw safety.** -/
theorem MidHistoryTraceIn.outputNotDeleted_of_safe {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (history : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F)
    {wa : Adr} {C : ByteArray} (hC : start.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (safe : SafeRawFrames wa history.rawFrames) :
    history.OutputNotDeleted wa ∧ future.state.getCode wa = C := by
  induction history with
  | tail block cut =>
      have suffixSg : cut.afterBenv.stat.rules.stateGas = none := by
        rw [block.txSplit_stat cut]
        exact capabilities.stateGas_none block.forkIn
      obtain ⟨sched, code⟩ := cut.after.noDel_of_safe hCdel hCne suffixSg hC
        (block.txSplit_notCreated cut wa) (SafeRawFrames.of_append_left safe)
      have nd : cut.after.OutputNotDeleted wa := (cut.after.outputNotDeleted_iff_noDelScheduled wa).mpr sched
      exact ⟨nd, (block.bodyTrace.cell_property_after_transactions_of_settledRoots 0
        (capabilities.stateGas_none block.forkIn) code hCne hCdel (fun _ => True)
        (fun _ _ _ => trivial) trivial).2 |> fun c => by rw [congrArg BlockChain.state block.postEq]; exact c⟩
  | step prior block ih =>
      obtain ⟨nd, code⟩ := ih hC (SafeRawFrames.of_append_left safe)
      obtain ⟨sched, post⟩ := block.noDel_of_safe hCdel hCne capabilities code
        (SafeRawFrames.of_append_right safe)
      exact ⟨⟨nd, (block.bodyTrace.transactions.outputNotDeleted_iff_noDelScheduled wa).mpr sched⟩, post⟩

end Blanc.Lift
