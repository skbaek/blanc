import Blanc.Lift.Weth9.WithdrawReach
import Blanc.Lift.Weth9.FootHistory

/-!
# The committed WETH9 invocations and their model replay

A WETH9 history is identified with the pure model (`Model.lean`) run over the writer invocations of the
settlement-committed frames at the contract.  This module fixes the two definitional pieces and the
generic carrier:

* `committedFrameInvocations ca frame` — a settled frame contributes its invocation exactly when it runs at
  `ca`, is non-static, and decodes as a writer (`decodeCall`, by the dispatcher's own table); a view
  contributes nothing.  `committedInvocations ca trace` is the flat-map over `trace.settledFrames`, in
  trace order, so a frame rolled back by settlement is never in it.  (A writer cannot succeed in a static
  frame; the filter is a statement-level one, and a static frame keeps the contract's storage, so it
  needs no proof about the runtime.)
* `wethCarrier ca U` — boundaries are the ledger the contract's storage carries over the tracked universe
  `U` (`ledger U`), a replay is the model run of the decoded calls, and value credits and foreign frames
  are invisible: the boundary reads storage only through its words.

`Blanc/Lift/Weth9/CommittedHistory.lean` supplies the frame-level obligations and the headline.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- One committed writer invocation: its frame's message and machines. -/
structure Invocation where
  sevm : Sevm
  pre : Devm
  post : Devm

/-- The invocation a committed frame records. -/
def frameInvocation (frame : Exec.Frame) : Invocation := ⟨frame.sevm, frame.pre, frame.post⟩

/-- A settled frame contributes its invocation exactly when it runs at the selected address, non-static,
with a writer selector. -/
def committedFrameInvocations (ca : Adr) (frame : Exec.Frame) : List Invocation :=
  if frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false ∧
      (decodeCall frame.sevm).isSome = true then
    [frameInvocation frame] else []

/-- The writer invocations of the settlement-committed frames of a configured history, in execution
order.  Interpreter and message settlement prune rolled-back subtrees first. -/
def committedInvocations {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future) : List Invocation :=
  trace.settledFrames.flatMap (committedFrameInvocations ca)

/-- Every extracted invocation is the record of a settlement-committed frame at the contract address
that runs non-statically with a writer selector. -/
theorem mem_committedInvocations {cfg : ChainConfig} {checkpoint future : BlockChain}
    {ca : Adr} {trace : ConfiguredHistoryTrace cfg checkpoint future} {inv : Invocation}
    (member : inv ∈ committedInvocations ca trace) :
    ∃ frame ∈ trace.settledFrames, Execution.commits frame.out = true ∧
      frame.sevm.currentTarget = ca ∧ frame.sevm.isStatic = false ∧
      (decodeCall frame.sevm).isSome = true ∧ inv = frameInvocation frame := by
  obtain ⟨frame, settled, selected⟩ := List.mem_flatMap.mp member
  refine ⟨frame, settled, frame.committed, ?_⟩
  unfold committedFrameInvocations at selected
  split at selected
  · rename_i h
    exact ⟨h.1, h.2.1, h.2.2, List.mem_singleton.mp selected⟩
  · cases selected

/-- The model calls an invocation list replays: the decoded writer call of each. -/
def replayCalls (invs : List Invocation) : List Call :=
  invs.filterMap fun inv => decodeCall inv.sevm

theorem replayCalls_append (xs ys : List Invocation) :
    replayCalls (xs ++ ys) = replayCalls xs ++ replayCalls ys := by
  simp only [replayCalls, List.filterMap_append]

/-- The connected replay: the model run of the decoded calls. -/
def LedgerReplay (a : Ledger) (invs : List Invocation) (b : Ledger) : Prop :=
  a.run (replayCalls invs) = some b

theorem LedgerReplay.nil (a : Ledger) : LedgerReplay a [] a := rfl

theorem LedgerReplay.append {a b c : Ledger} {xs ys : List Invocation}
    (h₁ : LedgerReplay a xs b) (h₂ : LedgerReplay b ys c) : LedgerReplay a (xs ++ ys) c := by
  unfold LedgerReplay at *
  rw [replayCalls_append, Ledger.run_append, h₁]
  exact h₂

/-- The ledger replay carrier over the tracked universe `U`: a boundary is the ledger the contract's
storage carries there, and reads the storage only through its words. -/
noncomputable def wethCarrier (ca : Adr) (U : Key → Prop) : ReplayCarrier ca where
  Snap := Ledger
  Step := Invocation
  Tag := Unit
  Replay := LedgerReplay
  ofState state := ledger U (state.getStor ca)
  frameEntry _ state := ledger U (state.getStor ca)
  nil := LedgerReplay.nil
  silent := fun storage _ => by rw [storage]
  credit := by
    intro _ pre post _ storage _ _
    exact ⟨[], by rw [storage]; exact LedgerReplay.nil _⟩
  entry_eq_ofState := by
    intro _ _ _ _ transfer _
    show ledger U _ = ledger U _
    rw [congrFun (benvAfterTransfer_getStor_eq transfer) ca]

/-- Replay steps and committed-frame invocations use the same ordered observation. -/
noncomputable def wethObservation (ca : Adr) (U : Key → Prop) :
    ReplayObservation (wethCarrier ca U) where
  O := Invocation
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := committedFrameInvocations ca
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    show LedgerReplay (ledger U (pre.getStor ca)) [] (ledger U (post.getStor ca))
    rw [storage]
    exact LedgerReplay.nil _

/-- The decoded withdraw call is the caller's and reads the first calldata word. -/
theorem decodeCall_withdraw_inv {e : Sevm} {who : Adr} {w : B256}
    (h : decodeCall e = some (.withdraw who w)) : who = e.caller ∧ w = Sevm.dataWord e 4 := by
  unfold decodeCall at h
  split_ifs at h <;> first | (cases h; exact ⟨rfl, rfl⟩) | (cases h)

/-- A calldata of at least four bytes selecting `withdraw` decodes as `withdraw`. -/
theorem decode_of_withdraw_selector {e : Sevm} (hshort : ¬ shortCall e)
    (hsel : Sevm.selector e = Bytes.toB256 [0x2e, 0x1a, 0x7d, 0x4d]) :
    decodeCall e = some (.withdraw e.caller (Sevm.dataWord e 4)) := by
  have h : Sevm.selector e = 0x2e1a7d4d := hsel.trans (by decide)
  unfold decodeCall
  simp only [hshort, ↓reduceIte, h]

end Blanc.Lift.Weth9
