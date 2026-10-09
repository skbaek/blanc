import Blanc.Lift.UniswapV2Pair.SwapCallback
import Blanc.Lift.UniswapV2Pair.SwapFrontTyped
import Blanc.Lift.UniswapV2Pair.LockedSupply
import Blanc.Lift.UniswapV2Pair.SwapCallWorld

/-! The swap front's three optional external calls as source turns. Each actual CALL step of
the same derivation is consumed by `mutable_call_turns` with the lock-free supply
`lockedPairSupply`: nested Pair frames run while the Pair is locked. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The transported invariant of the swap front between two external calls: the typed frame
keeps the context, its current state is the locked finite representation of the actual Pair
storage, the Pair code and the frame's output are unchanged, and the source logs extend
with the raw logs. -/
structure SwapFrontState (U : WriterKey → Prop) (pair : Adr) (ctx : Context)
    (current : Checkpoint) (b : Devm) (F : Frame) (w : Devm) : Prop where
  context : F.context = ctx
  rep : LockedRep U F.current.state (w.getStor pair)
  code : w.getCode pair = b.getCode pair
  output : w.output = b.output
  logs : ∃ (added : List PendingLog) (L : List Log), F.current.logs = current.logs ++ added ∧
    w.logs = b.logs ++ L ∧ added.map (PendingLog.rawWith (lockedOwnedRaw pair)) = L.map some
  checkpoint : F.checkpoint = current

/-- The Swap lock and cached read prefix preserve the initial finite source
invariant. Both canonical consumers share this single proof. -/
theorem swap_prefix_source_invariant {K U : WriterKey → Prop} {sevm : Sevm} {b : Devm}
    {current : Checkpoint} {ctx : Context}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sub : ∀ k, K k → U k) :
    SwapFrontState U sevm.currentTarget ctx current b
      (swapLockedFrame current ctx (swapDecodedEntry sevm)) (swapPrefixWorld sevm b) := by
  have lockedRep := rep.mint_locked_world (sevm := sevm) (b := b)
  refine ⟨rfl, ⟨K, sub, ?_, rfl⟩, ?_, ?_, ⟨[], [], ?_, ?_, rfl⟩, rfl⟩
  · unfold swapPrefixWorld
    rw [afterSload_getStor, afterSload_getStor, afterSload_getStor]
    exact lockedRep
  · unfold swapPrefixWorld mintLockedWorld
    rw [afterSload_getCode, afterSload_getCode, afterSload_getCode, afterSstore_getCode,
      afterSload_getCode]
  · unfold swapPrefixWorld mintLockedWorld
    rw [afterSload_output, afterSload_output, afterSload_output, afterSstore_output,
      afterSload_output]
  · rw [List.append_nil]
    rfl
  · unfold swapPrefixWorld mintLockedWorld
    rw [afterSload_logs, afterSload_logs, afterSload_logs, afterSstore_logs, afterSload_logs,
      List.append_nil]

theorem SwapFrontState.beginResume {U : WriterKey → Prop} {pair : Adr} {ctx : Context}
    {current : Checkpoint} {b : Devm} {F : Frame} {w : Devm}
    (h : SwapFrontState U pair ctx current b F w) (request : Request) :
    SwapFrontState U pair ctx current b (F.beginResume request) w :=
  ⟨h.context, h.rep, h.code, h.output, h.logs, h.checkpoint⟩

/-- What every external call of the swap frame consumes: the lock-free supply under a
trace-local universe `U` and admission of every raw Pair frame of the derivation. -/
structure SwapCallEnv (U : WriterKey → Prop) (D : Exec.Deriv) (sevm : Sevm) (sem : CodeSem) :
    Prop where
  supply : PairFrameSupply sevm.currentTarget (LockedRep U) (LockedGood U) LockedAuth
    (lockedOwnedRaw sevm.currentTarget)
  image : sem.image = some code.toList
  fork : CoveredFork sevm.benvStat.fork
  good : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = sevm.currentTarget → LockedGood U F

/-- The provenance of one actual mutable CALL of the swap frame from world `w` to world `d`
with turns `turns`: an actual CALL step of `D` whose pre-state has `w`'s storage and code, and
whose child derivation explains both the turns and the storage of every code-bearing account
after the call (`MutableCallWorld`). -/
def SwapCallProvenance (pair : Adr) (D : Exec.Deriv) (sevm : Sevm) (w d : Devm)
    (turns : List MutableTurn) : Prop :=
  ∃ pre : Devm, StepIn D sevm pre (.exec .call) d ∧ (∀ a, pre.getStor a = w.getStor a) ∧
    (∀ a, pre.getCode a = w.getCode a) ∧ MutableCallWorld pair D sevm pre .call d turns

/-- A nonzero word is positive. -/
theorem swap_pos_of_ne {a : B256} (h : a ≠ 0) : a > 0 := by
  apply B256.lt_of_toNat_lt_toNat
  have ne : a.toNat ≠ 0 := fun e => h (B256.toNat_inj _ _ (e.trans rfl))
  change 0 < a.toNat
  omega

end Blanc.Lift.UniswapV2Pair
