import Blanc.Composition.Curve3PoolBackedFlat

/-!
# The pool's books of DAI are covered

`daiWalk`: DAI's `CoinWalk`. Its only premises are `Assumes`' code at the start, the key premises and the signature
premise; the pool's own calls are a theorem. `dai_covered`: the books at every position and at the end.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolPublic Blanc.Composition.Curve3PoolCoinKeep
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun PoolEntries poolFrameObs answerWord balanceOfData)
open Blanc.Lift.CurveCoins (PoolCoinSel)

variable {d : Deployment} {future : BlockChain} {h : MainnetHistory d.minter.post future}

/-- DAI's entry for the pool, as a book. -/
def daiBook : CoinBook :=
  flatBook dai (CodeFrame dai HistFork Lift.Dai.code) (fun σ => (σ (Lift.Dai.balSlot pool)).toNat)
    (ownDebit pool) (ownCredit pool)

theorem dai_start_code (A : Assumes d h) : d.poolCut.afterBenv.state.getCode dai = Lift.Dai.code :=
  cutCode_of_cert daiInstalledCert d.toPool d.pool.trace d.poolCut A.code.daiCode

/-- Below a settled non-static frame at DAI every frame is static. -/
theorem dai_below (A : Assumes d h) : ∀ G ∈ (d.sincePool h).settledFrames, G.sevm.currentTarget = dai →
    G.sevm.isStatic = false → ∀ f ∈ Exec.descendantFrames G.run, f.sevm.isStatic = true := by
  intro G member target mutable f hf
  have whole := (CurveCoins.Dai.dai_chain (d.sincePool h) (dai_start_code A)).1 fun _ _ => trivial
  have good := whole.good G (mem_coinFrames.mpr ⟨member, target, mutable, trivial⟩)
  obtain ⟨hpc, hcode, fork, -⟩ := good
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
  dsimp only at hpc hcode fork hf
  subst hpc
  exact Exec.staticOnly_rawFrameDescendants_isStatic Lift.Dai.cert_check CurveCoins.Dai.staticOnly
    (root := ⟨0, sevm, pre, out, run⟩) rfl hcode fork.stateGas_none run (.refl _) _
    (Blanc.Exec.mem_rawFrameDescendants_of_mem_descendantFrames run f hf)

/-- **DAI's locality over the history from the pool's creation**, from `Assumes` alone. -/
theorem dai_local (A : Assumes d h) :
    EntryLocal dai (fun _ => True) (CodeFrame dai HistFork Lift.Dai.code)
      (fun σ => (σ (Lift.Dai.balSlot pool)).toNat) (ownDebit pool) (ownCredit pool)
      (wordsAt dai d.poolCut.afterBenv.state) (wordsAt dai future.state) (d.sincePool h).settledFrames := by
  refine CurveCoins.Dai.dai_entry_local (d.sincePool h) (dai_start_code A)
    (NoKeyHolder.daiAuthority (d.sincePool h) A.keys (dai_start_code A) fun F hF caller => ?_) A.hashes.coinKeys.dai
  obtain ⟨member, target, mutable, -⟩ := mem_coinFrames.mp hF
  refine pool_ownCalls_history A (T := dai) (by decide) member target mutable caller fun G hG child mg te => ?_
  have := dai_below A G hG (te.trans target) mg F (Exec.mem_descendantFrames_of_mem_childFrames G.run F child)
  rw [mutable] at this
  cases this

/-- **DAI's `CoinWalk`.** -/
theorem daiWalk (A : Assumes d h) :
    CoinWalk daiBook pool 0 (d.sincePool h).settledFrames (d.sincePool h).settledRoots
      (wordsAt dai d.poolCut.afterBenv.state) (wordsAt dai future.state)
      Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN :=
  flat_walk A (dai_local A) coin0_eq
    (fun j hj => by
      match j, hj with
      | 1, _ => decide +kernel
      | 2, _ => decide +kernel
      | 0, hj => exact absurd rfl hj)
    (by decide +kernel) (by decide)
    (fun _ _ ne => ite_eq_left ne)
    (dai_below A)
    (fun _ _ _ hd => ownDebit_transfer hd)
    (fun _ _ _ hd hs => ownDebit_transferFrom hd hs)
    (fun _ _ _ _ caller hd hs fits => ownCredit_transferFrom caller hd hs fits)
    (fun H c hc member tc hd _ _ _ => by
      have good := H.child_good H.world.daiCode (by decide +kernel) (by decide +kernel) hc tc
      have sel : Blanc.Sevm.selector c.sevm = 0x70a08231 :=
        selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
      have word4 : Sevm.dataWord c.sevm 4 = pool.toB256 :=
        Curve3PoolSupply.dataWord_eq_of_append (pre := Curve3Pool.balanceOfSel) (rest := [])
          (by rw [hd, List.append_nil]; rfl) (by decide)
      have out := CurveCoins.Dai.frame_balanceOf_answer good tc (CurveCoins.settled_wf _ member) sel
      rw [word4, toAdr_toB256] at out
      rw [answerWord, out, List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes])

/-- **The pool's books of DAI are at most what DAI's storage says it holds.** -/
theorem dai_backed (A : Assumes d h) : recorded future.state 0 ≤ coinHeld future.state pool 0 :=
  (A.coin_walk_whole (daiWalk A)).1

end Blanc.Composition.Curve3PoolBacked
