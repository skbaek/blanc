import Blanc.Composition.Curve3PoolBackedWalk

/-!
# What `Assumes` gives the pool over the history from its creation

`Curve3PoolVirtualPriceDeploy` reads `Assumes` over the history since the minter assignment. Backing starts earlier, at
the pool's creation, where its books are empty.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolCoinKeep Blanc.Composition.Curve3PoolBlockAnchor

variable {d : Deployment} {future : BlockChain} {h : MainnetHistory d.minter.post future}

theorem sincePool_raw_sub :
    ∀ r ∈ (d.sincePool h).rawFrames, r ∈ (d.sinceC3Block h).rawFrames := by
  intro r member
  rw [sinceC3Block_raw]
  simp only [Deployment.sincePool, MidHistoryTraceIn.append_rawFrames, ConfiguredHistoryTraceIn.rawFrames_append,
    ConfiguredHistoryTraceIn.rawFrames, List.mem_append] at member ⊢
  rcases member with m | ((m | m) | m)
  · exact .inl (.inl (.inl (.inr (tail_raw_sub _ _ r m))))
  · exact .inl (.inl (.inr m))
  · exact .inl (.inr m)
  · exact .inr m

namespace Assumes

variable (A : Assumes d h)

include A

/-- The pool's facts over the history from its creation. -/
theorem midFactsPool : Curve3Pool.PoolMidFacts (d.sinceC3Block h) (d.sincePool h) pool Curve3Pool.Creation.coinsN
    Curve3Pool.Creation.tokenN where
  subset := sincePool_raw_sub
  parties := fun root member _ => Curve3PoolJointRoot.parties_not_precompile ((d.sincePool h).rootEntryIn root member).2
  idEmpty := A.code.idEmpty
  idNoAuthority := A.keys.idNoAuthority
  idNoFrame := A.hashes.noCreateAt4
  sysNe := d.system_ne A.system Curve3PoolBlockAnchor.AnchoredDeployment.pool_not_system

/-- The coins over the history from the pool's creation. -/
theorem coinsPool : CoinsHold (d.sincePool h) dai usdc usdt :=
  A.coinsHold (d.sincePool h) (fun _ m => m)
    (cutCode_of_cert daiInstalledCert d.toPool d.pool.trace d.poolCut A.code.daiCode)
    (cutCode_of_cert usdtInstalledCert d.toPool d.pool.trace d.poolCut A.code.usdtCode)

/-- 3Crv's runtime stays at every raw frame from the pool's creation. -/
theorem c3CodePool : ∀ R ∈ (d.sincePool h).rawFrames, R.devm.getCode c3 = Curve3Crv.code := by
  obtain ⟨hcode, -, -⟩ := (Deployment.toJoint d A.facts).c3Created
  intro R member
  refine midCode_of_cert Curve3Crv.c3crvInstalledCert (d.sinceCreation h)
    (Curve3Crv.code_of_image ((congrArg some hcode).trans rfl)) R ?_
  simp only [Deployment.sinceCreation, MidHistoryTraceIn.append_rawFrames, List.mem_append]
  exact .inr (sincePool_raw_sub R member)

/-- What each settled frame finds. -/
theorem framesPool : FramesHold (d.sincePool h) dai usdc usdt c3 :=
  framesHold_of_coins A.coinsPool A.c3CodePool

/-- The pool at its creation: installed, with its constructor's state, whose books are empty. -/
theorem poolStart : some (d.poolCut.afterBenv.state.getCode pool).toList = Curve3Pool.poolSem.image ∧
    Curve3Pool.Checkpoint (d.poolCut.afterBenv.state.getStor pool)
      (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat) := by
  obtain ⟨hfork, hbasefee, htime, _, head, success⟩ := (Deployment.toJoint d A.facts).pool_head
  obtain ⟨hcode, hstor⟩ := Curve3PoolJointRoot.pool_created_of_head head hfork hbasefee htime success
  refine ⟨?_, ?_⟩
  · change some ((Deployment.toJoint d A.facts).poolCut.txState.getCode Curve3Pool.Creation.poolAddress).toList = _
    rw [hcode]
    rfl
  · change Curve3Pool.Checkpoint ((Deployment.toJoint d A.facts).poolCut.txState.getStor Curve3Pool.Creation.poolAddress) _
    rw [hstor]
    exact Curve3Pool.Creation.deployedStor_checkpoint (by decide)

end Assumes

end Blanc.Composition.Curve3PoolPublic
