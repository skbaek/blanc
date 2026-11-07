import Blanc.Composition.Curve3PoolBackedUsdt
import Blanc.Composition.Curve3PoolPublicTx
import Blanc.Lift.Curve3Pool.HistoryWindow

/-!
# The pool's books at a transaction boundary

`Moment.coin_window`: right after any transaction of mainnet, the books are at most what the coin's storage reads there.
The walk runs over the settled frames through the moment's transaction. What the frames after it carry, from the world at
the moment to the block's end, names that position: `chain_start`.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolPublic Blanc.Composition.Curve3PoolCoinKeep

variable {d : Deployment} {B : CoinBook}

/-- Two chains over the same frames to the same end start from the same view. -/
theorem chain_start {x y b : StorWords} : ∀ {zs : List Exec.Frame}, B.Chain x zs b → B.Chain y zs b → x = y
  | [], hx, hy => hx.symm.trans hy
  | _ :: _, hx, hy => hx.2.1.symm.trans hy.2.1

end Blanc.Composition.Curve3PoolBacked

namespace Blanc.Composition.Curve3PoolPublic.Moment

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolBacked Blanc.Composition.Curve3PoolCoinKeep

variable {d : Deployment} {B : CoinBook} (m : Moment d)

/-- Mainnet from right after the pool's creation through the moment's transaction: its settled frames. -/
noncomputable def throughFrames : List Exec.Frame :=
  (d.sincePool m.history).settledFrames ++ m.block.settledThroughCut m.cut

/-- The frames after the moment, in its block. -/
noncomputable def tailFrames : List Exec.Frame := (MidHistoryTraceIn.tail m.block m.cut).settledFrames

theorem settled_split : (d.sincePool m.through).settledFrames = m.throughFrames ++ m.tailFrames := by
  change (d.sincePool m.history).settledFrames ++ m.block.settledFrames = _
  rw [ConfiguredBlockTraceIn.settledFrames_throughCut m.block m.cut]
  simp only [throughFrames, tailFrames, List.append_assoc]

theorem through_closed : TargetClosed pool m.throughFrames := by
  unfold throughFrames ConfiguredBlockTraceIn.settledThroughCut
  have piece : ∀ {fs roots : List Exec.Frame}, fs = roots.flatMap (fun R => Exec.committedFrames R.run) →
      TargetClosed pool fs := fun h => Curve3PoolSupply.targetClosed_of_forest h
  refine (piece (d.sincePool m.history).settledFrames_eq).append
    ((((piece m.block.bodyTrace.beacon.settledFrames_eq).append (piece m.block.bodyTrace.history.settledFrames_eq)).append
      (piece m.cut.before.settledFrames_eq)).append (piece m.cut.head.settledFrames_eq))

/-- **The books at the moment are at most what the position there reads.** -/
theorem coin_window (A : Assumes d m.through) {k : Fin 3} {a b : StorWords}
    (W : CoinWalk B pool k (d.sincePool m.through).settledFrames (d.sincePool m.through).settledRoots a b
      Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN)
    (tail : B.Chain (B.V (wordsAt B.T m.world)) (B.cf m.tailFrames) b) :
    recorded m.world k ≤ B.Rd (B.cf m.throughFrames) (B.V (wordsAt B.T m.world)) := by
  obtain ⟨installed, initial⟩ := A.poolStart
  have env : Curve3Pool.PoolMidEnv (d.sinceC3Block m.through) (d.sincePool m.through) pool
      (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat).coins
      (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat).token :=
    { A.midFactsPool with
      callbacks := pool_keepAt_of_frames A.midFactsPool party_words' A.framesPool }
  obtain ⟨-, invs, obs, auth, entries, s, run, -, hc, -⟩ :=
    Curve3Pool.pool_window_history (d.sincePool m.history) m.block m.cut installed initial env
  have zero : (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat).balances.get k = 0 := by
    match k with
    | 0 | 1 | 2 => rfl
  have start : B.Covered a [] ((Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat).balances.get k) :=
    ⟨a, rfl, by rw [zero]; exact Nat.zero_le _⟩
  obtain ⟨⟨m₀, hm, hr⟩, -⟩ := coin_walk W invs (pre := []) (fs := m.throughFrames) (post := m.tailFrames) run
    entries auth obs (by rw [List.nil_append]; exact m.settled_split) (TargetClosed.nil pool)
    (by rw [List.nil_append]; exact m.through_closed) rfl rfl start
  rw [List.nil_append] at hm hr
  obtain ⟨m₁, m₂, h₁, h₂⟩ := W.ledger.position (pre := m.throughFrames) (post := m.tailFrames) m.settled_split
  obtain rfl := chain_det hm h₁
  have whole := W.ledger.loc.chain
  rw [m.settled_split, coinFrames_append] at whole
  obtain ⟨m₃, h₃, h₄⟩ := chain_split whole
  obtain rfl := chain_det h₃ hm
  rw [chain_start h₄ tail] at hr
  rw [show recorded m.world k = s.balances.get k from recorded_of_abstracts hc.abs k]
  exact hr

end Blanc.Composition.Curve3PoolPublic.Moment

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolPublic Blanc.Composition.Curve3PoolCoinKeep

variable {d : Deployment}

/-- **DAI's books at a transaction boundary.** -/
theorem dai_window (m : Moment d) (A : Assumes d m.through) : recorded m.world 0 ≤ coinHeld m.world pool 0 := by
  have code : m.world.getCode dai = Lift.Dai.code :=
    cutCode_of_cert daiInstalledCert (d.sinceC3Block m.history) m.block m.cut A.code.daiCode
  exact m.coin_window A (daiWalk A) (viewChain_id ((CurveCoins.Dai.dai_chain (MidHistoryTraceIn.tail m.block m.cut) code).1
    fun _ _ => trivial))

/-- USDT's frames after the moment carry its storage from the world at the moment to the block's end. -/
theorem usdt_tail (m : Moment d) (A : Assumes d m.through) :
    FrameChain usdt (CodeFrame usdt HistFork Lift.Usdt.code) (wordsAt usdt m.world)
      (coinFrames usdt (fun _ => True) m.tailFrames) (wordsAt usdt m.post.state) := by
  have code : m.world.getCode usdt = Lift.Usdt.code :=
    cutCode_of_cert usdtInstalledCert (d.sinceC3Block m.history) m.block m.cut A.code.usdtCode
  refine (CurveCoins.Usdt.usdt_chain BodyStageCapabilities.historical
    (MidHistoryTraceIn.tail m.block m.cut) code).1 fun F hF => ?_
  obtain ⟨member, target, mutable, -⟩ := mem_coinFrames.mp hF
  refine A.notDeprecated F (mem_coinFrames.mpr ⟨?_, target, mutable, trivial⟩)
  rw [m.settled_split]
  exact List.mem_append_right _ member

/-- **USDT's books at a transaction boundary.** -/
theorem usdt_window (m : Moment d) (A : Assumes d m.through) :
    recorded m.world 2 ≤ coinHeld m.world pool 2 :=
  m.coin_window A (usdtWalk A) (viewChain_id (usdt_tail m A))

end Blanc.Composition.Curve3PoolBacked

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolBacked

/-- **USDT is not redirected at a moment of mainnet**: clear when the pool is created, and no `deprecate` since. -/
theorem Moment.usdtLive {d : Deployment} (m : Moment d) (A : Assumes d m.through) :
    Usdt.flag20 ((m.world.getStor usdt).get 10) = 0 := by
  have whole := (CurveCoins.Usdt.usdt_chain BodyStageCapabilities.historical (d.sincePool m.through) A.usdtStart).1
    A.notDeprecated
  rw [m.settled_split, coinFrames_append] at whole
  obtain ⟨b, before, after⟩ := whole.split
  obtain rfl := chain_start (B := usdtBook) (viewChain_id (usdt_tail m A)) (viewChain_id after)
  exact usdt_flag_clear A (fun F hF => by rw [m.settled_split]; exact List.mem_append_left _ hF) before

end Blanc.Composition.Curve3PoolPublic
