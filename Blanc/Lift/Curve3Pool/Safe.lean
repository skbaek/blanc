import Blanc.Lift.Curve3Pool.FrameEnv
import Blanc.Lift.Curve3Pool.Ladder
import Blanc.Lift.Curve3Pool.Walk.BridgeChecks
import Blanc.Lift.Curve3Pool.Walk.ExchangeSafe
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityChecks
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityRawK
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceRawChecks
import Blanc.Lift.Curve3Pool.Walk.OneCoinChecks
import Blanc.Lift.Curve3Pool.Walk.WithdrawAdminFeesRaw
import Blanc.Lift.Curve3Pool.Walk.DonateX
import Blanc.Lift.Curve3Pool.Walk.AdminBalancesX
import Blanc.Lift.Curve3Pool.Walk.AdminRaw
import Blanc.Lift.Curve3Pool.Walk.Fallback

/-!
# Curve 3pool: every successful pool frame refines the model (U2(a))

The all-selector frame headline (design §1.1).  A successful pc-`0` frame of the certified runtime,
entered fresh at a `Checkpoint`, is accepted by `Model.step` on its decoded call with the frame's
exact raw effect.  The proof splits on the dispatcher: short calldata or a selector missing every
test cannot succeed (`pool_other_fails`), and a hit on one of the 38 tests is that entry's `*_raw`,
its world premises projected from the ENV bundle `PoolFrameEnv`.

* `pool_frame_refines_env` — the headline with explicit machine premises and `PoolFrameEnv`;
* `poolEntry` — the entry condition the history ladder admits frames by: fresh machine, calldata and
  gas words in range, and `PoolFrameEnv` of the frame's own derivation;
* `pool_frame_refines` — `PoolFrameRefines poolEntry`, the hypothesis of
  `pool_history_committed_with` (`Ladder.lean`).

Static frames are covered by `pool_static_noEffect` (`Walk/Fallback.lean`, imported here): a
committing static frame of the runtime keeps every account's storage and the log list.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.Lift

/-- **U2(a) headline.** Every successful pc-`0` frame of the certified runtime on a covered fork,
entered with empty stack and memory at a `Checkpoint` abstracting `s`, whose target carries code
and whose world satisfies the ENV bundle `PoolFrameEnv`, is accepted by `Model.step` on its decoded
call and some environment `e`, with the frame's exact raw effect. -/
theorem pool_frame_refines_env {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (henv : PoolFrameEnv ⟨0, sevm, pre, .ok post, exc⟩) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  by_cases hlen : 4 ≤ sevm.data.length
  · by_cases hin : Sevm.selector sevm ∈ sels
    · simp only [sels, List.mem_cons, List.not_mem_nil, or_false] at hin
      have htok := henv.htok
      have hcoin := henv.hcoin
      have hid := henv.id
      have hkeep := henv.keep
      have hidk := henv.hidk
      rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact a_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact gvp_raw exc hcode hfork hlen hcd h hstack hmem hgas hck htok
      · exact cta_raw exc hcode hfork hlen hcd h hstack hmem hgas hck htok
      · exact addLiquidity_raw exc hcode hfork hlen hcd h hstack hmem hgas hck htok hcoin hpc hid
          hkeep hidk
      · exact dy_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact dyu_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact exchange_raw exc hcode hfork hlen hcd h hstack hmem hgas hck hcoin hpc hid hkeep hidk
      · exact removeLiquidity_rawK exc hcode hfork hlen hcd h hstack hmem hgas hck htok hcoin hpc
          hid hkeep hidk
      · exact removeLiquidityImbalance_raw exc hcode hfork hlen hcd h hstack hmem hgas hck htok
          hcoin hpc hid hkeep hidk
      · exact cwo_raw exc hcode hfork hlen hcd h hstack hmem hgas hck htok
      · exact removeLiquidityOneCoin_raw exc hcode hfork hlen hcd h hstack hmem hgas hck htok hcoin
          hpc hid hkeep hidk
      · exact rampA_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact stopRampA_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact commitNewFee_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact applyNewFee_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact revertNewParameters_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact commitTransferOwnership_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact applyTransferOwnership_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact revertTransferOwnership_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact adminBalances_raw exc hcode hfork hlen hcd h hstack hmem hgas hck hcoin
      · exact withdrawAdminFees_raw exc hcode hfork hlen hcd h hstack hmem hgas hck hcoin hpc hid
          hkeep hidk
      · exact donate_raw exc hcode hfork hlen hcd h hstack hmem hgas hck hcoin
      · exact killMe_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact unkillMe_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact coins_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact balances_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact fee_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact adminFee_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact owner_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact initialA_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact futureA_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact initialATime_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact futureATime_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact adminActionsDeadline_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact transferOwnershipDeadline_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact futureFee_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact futureAdminFee_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
      · exact futureOwner_raw exc hcode hfork hlen hcd h hstack hmem hgas hck
    · exact absurd (decodeCall_miss fun s hs he => hin (he ▸ hs))
        (pool_other_fails exc hcode hcd hstack hmem hgas)
  · exact absurd (decodeCall_short (by omega))
      (pool_other_fails exc hcode hcd hstack hmem hgas)

/-! ## The entry condition of the history ladder -/

/-- **The pool frame entry condition**: a fresh machine (empty stack and memory), calldata length
and gas words in range, and the ENV bundle `PoolFrameEnv` of the frame's own derivation. -/
def poolEntry (sevm : Sevm) (pre : Devm) : Prop :=
  Exec.FreshEntry sevm pre ∧ sevm.data.length < 2 ^ 256 ∧ pre.gasMeasure < 2 ^ 256 ∧
    Exec.derivEntry PoolFrameEnv sevm pre

/-- **The frame refinement the history ladder consumes**, discharged for `poolEntry`. -/
theorem pool_frame_refines : PoolFrameRefines poolEntry := by
  intro sevm pre post s exc hcode hfork hentry _ hpc _ hck
  obtain ⟨⟨hstack, hmem⟩, hcd, hgas, henv⟩ := hentry
  exact pool_frame_refines_env exc hcode hfork hcd hstack hmem hgas hpc hck (henv _ exc)

/-! ## The entry condition at fixed parties

The coins and the token are fixed model fields (`Keeps.coins_token`), so the history can name them
as the fixed addresses `adrOf (cs.get k)` and `adrOf tok` instead of the words a frame finds in
storage.  `PoolParties cs tok` is the model invariant that carries them through the replay. -/

/-- The model states whose coins are `cs` and whose token is `tok`. -/
def PoolParties (cs : V3) (tok : Nat) (s : State) : Prop :=
  s.coins = cs ∧ s.token = tok

/-- Every accepted step keeps the coins and the token. -/
theorem poolParties_keeps (cs : V3) (tok : Nat) : StepKeeps (PoolParties cs tok) := by
  intro s e c o hstep hs
  obtain ⟨hc, ht⟩ := (step_keeps hstep).coins_token
  exact ⟨hc.trans hs.1, ht.trans hs.2⟩

/-- The per-child premises of a frame: every direct child keeps the pool's storage, every coin
child keeps the token's storage (R1), and every direct child keeps the code at `4`. -/
def PoolChildrenKeep (D : Exec.Deriv) : Prop :=
  PoolCallsKeep D ∧ PoolCoinCallsKeepToken D ∧
    ∀ c ∈ children D, c.post.getCode 4 = c.pre.getCode 4

/-- **The pool frame entry condition at fixed parties**: a fresh machine, calldata length and gas
words in range, the identity precompile ready, the fixed coins and token not precompiles under the
frame's rules, and the per-child premises of the frame's own derivation. -/
def poolEntryAt (cs : V3) (tok : Nat) (sevm : Sevm) (pre : Devm) : Prop :=
  Exec.FreshEntry sevm pre ∧ sevm.data.length < 2 ^ 256 ∧ pre.gasMeasure < 2 ^ 256 ∧
    IdReady sevm pre ∧ (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (adrOf (cs.get k))) ∧
    ¬ sevm.benvStat.rules.isPrecomp (adrOf tok) ∧ Exec.derivEntry PoolChildrenKeep sevm pre

/-- **The frame refinement at fixed parties**: on the model states with coins `cs` and token
`tok`, `poolEntryAt cs tok` supplies `PoolFrameEnv`. -/
theorem pool_frame_refines_at (cs : V3) (tok : Nat) :
    PoolFrameRefinesIn (PoolParties cs tok) (poolEntryAt cs tok) := by
  intro sevm pre post s exc hcode hfork hentry _ hpc _ hck hq
  obtain ⟨⟨hstack, hmem⟩, hcd, hgas, hid, hcs, htk, hkids⟩ := hentry
  obtain ⟨hkeep, hkeepT, hcode4⟩ := hkids _ exc
  have habs : Abstracts (entryStor ⟨0, sevm, pre, .ok post, exc⟩) s := hck.abs
  refine pool_frame_refines_env exc hcode hfork hcd hstack hmem hgas hpc hck
    ⟨hkeep, hkeepT, hcode4, hid, fun k => ?_, ?_⟩
  · rw [coinAdr_eq habs k, hq.1]
    exact hcs k
  · rw [tokenAdr_eq habs, hq.2]
    exact htk

end Blanc.Lift.Curve3Pool
