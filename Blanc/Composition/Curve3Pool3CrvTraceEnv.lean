import Blanc.Composition.Curve3Pool3CrvTxFrame
import Blanc.Composition.Curve3Pool3CrvBlock
import Blanc.Lift.Curve3Pool.History
import Blanc.Lift.Curve3Crv.CarriedHistory
import Blanc.ExecutionWholeFrameAccounting

/-!
# U9(b): the pool's trace premises, from the closed block's frames

For a configured history whose raw frames are system frames (at the system addresses) around the raw
frames of one `exchange` frame entered at an `ExFrame` machine:

* `ex_trace_targets`: every raw frame is a system frame, the `exchange` frame itself (at the pool),
  or a direct committed child at a coin running `Token20` and entering nothing;
* `ex_poolTraceEnv`: the ENV premises of the pool's history headlines (`PoolTraceEnv`) hold — the
  per-frame callback premise from the coins' code (`exFrame_children`, `exRoot_coinChild_keepsAt`),
  the parties by kernel evaluation, the identity precompile's and the system exclusions from the
  frames' targets;
* `ex_touched_c3crv`: no raw frame runs at 3Crv, so the history touches no 3Crv key.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint
open Blanc.Lift.Weth9.ClosedInstance (systemAddresses)

theorem poolStor_token : (poolStor.get tokenSlot).toAdr = c3crvAddr := by decide +kernel

theorem systemAddresses_ne : ∀ a ∈ systemAddresses, a ≠ poolAddr ∧ a ≠ 4 ∧ a ≠ c3crvAddr := by
  decide +kernel

section Trace

variable {cfg : ChainConfig} {checkpoint future : BlockChain}
  (trace : ConfiguredHistoryTrace cfg checkpoint future)
  {sysRaw sysRaw' : List Exec.Deriv} {sevm : Sevm} {b post : Devm}
  (exc : Exec 0 sevm b (.ok post)) (hf : ExFrame sevm b)
  (hraw : trace.rawFrames = sysRaw ++ Exec.rawFrameRoots exc ++ sysRaw')
  (hsys : ∀ r ∈ sysRaw ++ sysRaw', r.sevm.currentTarget ∈ systemAddresses)

include hraw hsys hf in
/-- **Every raw frame of the history** is a system frame, the `exchange` frame, or a coin child. -/
theorem ex_trace_targets :
    ∀ r ∈ trace.rawFrames, r.sevm.currentTarget ∈ systemAddresses ∨
      r = ⟨0, sevm, b, .ok post, exc⟩ ∨
      ∃ k : Fin 3, r.sevm.currentTarget = exCoinAdr k ∧ Exec.rawFrameDescendants r.exc = [] := by
  intro r hr
  rw [hraw] at hr
  simp only [List.mem_append, Exec.rawFrameRoots, List.mem_cons] at hr
  rcases hr with (hr | rfl | hr) | hr
  · exact .inl (hsys r (List.mem_append_left _ hr))
  · exact .inr (.inl rfl)
  · obtain ⟨c, -, ⟨k, hk⟩, hrs, -, hnil⟩ := exFrame_raw hf exc r hr
    refine .inr (.inr ⟨k, ?_, hnil⟩)
    rw [hrs, hk]
    exact exFrame_coin hf k
  · exact .inl (hsys r (List.mem_append_right _ hr))

include hraw hsys hf in
theorem ex_trace_ne4 : ∀ r ∈ trace.rawFrames, r.sevm.currentTarget ≠ 4 := by
  intro r hr
  rcases ex_trace_targets trace exc hf hraw hsys r hr with h | rfl | ⟨k, hk, -⟩
  · exact (systemAddresses_ne _ h).2.1
  · show sevm.currentTarget ≠ 4
    rw [hf.target]; decide +kernel
  · rw [hk]; exact (exCoinAdr_ne k).2

include hraw hsys hf in
theorem ex_trace_neC3 : ∀ r ∈ trace.rawFrames, r.sevm.currentTarget ≠ c3crvAddr := by
  intro r hr
  rcases ex_trace_targets trace exc hf hraw hsys r hr with h | rfl | ⟨k, hk, -⟩
  · exact (systemAddresses_ne _ h).2.2
  · show sevm.currentTarget ≠ c3crvAddr
    rw [hf.target]; decide +kernel
  · rw [hk]
    match k with
    | 0 => decide +kernel
    | 1 => decide +kernel
    | 2 => decide +kernel

include hraw hsys hf in
/-- **The callback premise at the `exchange` frame**: its children keep the pool's and 3Crv's
storage. -/
theorem ex_root_callbacks :
    (fun D => PoolCallsKeep D ∧ PoolCoinCallsKeepToken D) ⟨0, sevm, b, .ok post, exc⟩ := by
  obtain ⟨coin, keep, -⟩ := exFrame_children hf exc
  refine ⟨keep, fun c hc _ hct x => ?_⟩
  obtain ⟨k, hk⟩ := coin c hc
  obtain ⟨htc, -, -⟩ := exFrame_coins hf k
  have htok : tokenAdr ⟨0, sevm, b, .ok post, exc⟩ = c3crvAddr := by
    change ((b.state.getStor sevm.currentTarget).get tokenSlot).toAdr = _
    rw [hf.target, hf.poolStor]
    exact poolStor_token
  rw [htok] at hct ⊢
  have hc3 : (b.getCode c3crvAddr).toList ≠ [] := by
    change (b.state.getCode c3crvAddr).toList ≠ []
    rw [hf.c3crvCode]
    decide +kernel
  exact (exRoot_coinChild_keepsAt hf.code (exFrame_fork hf) exc htc (fun e => hct (hk.trans e)) c hc
    hk).1 hc3 x

include hraw hsys hf in
/-- **The pool's trace premises** (`PoolTraceEnv`), given the identity precompile's account empty at
the checkpoint, no authorization recovering to it, and the system frames' list. -/
theorem ex_poolTraceEnv (hsysEq : trace.systemRawFrames = sysRaw ++ sysRaw')
    (idEmpty : checkpoint.state.getCode 4 = ByteArray.empty) (idNoAuthority : trace.NoAuthorityAt 4) :
    PoolTraceEnv trace poolAddr poolState.coins poolState.token where
  callbacks := by
    rw [trace.frameAdmitted_iff_rawFrames]
    intro r hr ht
    rcases ex_trace_targets trace exc hf hraw hsys r hr with h | rfl | ⟨k, hk, -⟩
    · exact absurd ht (systemAddresses_ne _ h).1
    · exact Exec.derivEntry_of_run exc (ex_root_callbacks trace exc hf hraw hsys)
    · rw [hk] at ht
      exact absurd ht (exCoinAdr_ne k).1
  parties := by
    intro r hr ht
    rcases ex_trace_targets trace exc hf hraw hsys r hr with h | rfl | ⟨k, hk, -⟩
    · exact absurd ht (systemAddresses_ne _ h).1
    · show (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (adrOf (poolState.coins.get k))) ∧
        ¬ sevm.benvStat.rules.isPrecomp (adrOf poolState.token)
      unfold BenvStat.rules
      rw [hf.fork]
      decide +kernel
    · rw [hk] at ht
      exact absurd ht (exCoinAdr_ne k).1
  idEmpty := idEmpty
  idNoAuthority := idNoAuthority
  idNoFrame := fun r hr _ => ex_trace_ne4 trace exc hf hraw hsys r hr
  sysNe := by
    intro r hr
    rw [hsysEq] at hr
    exact (systemAddresses_ne _ (hsys r hr)).1

include hraw hsys hf in
/-- **No raw frame runs at 3Crv**: the history touches no 3Crv key. -/
theorem ex_touched_c3crv : Lift.Curve3Crv.historyTouchedKeys c3crvAddr trace = [] := by
  unfold Lift.Curve3Crv.historyTouchedKeys
  rw [List.flatMap_eq_nil_iff]
  intro r hr
  rw [if_neg (ex_trace_neC3 trace exc hf hraw hsys r hr)]

end Trace

end Blanc.Composition.Curve3Pool3CrvInstance
