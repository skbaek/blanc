import Blanc.Composition.Curve3PoolBackedDai

/-!
# The pool's books of USDT are covered

USDT's debit is its `transfer`'s amount and its credit is nothing: the pool measures what comes in by asking. So its
walk reads `balanceOf`, which forwards when the flag is set; `TetherRestrained` keeps it from forwarding at any reader,
by the flag clear at the cut and no `deprecate` frame.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolPublic Blanc.Composition.Curve3PoolCoinKeep
open Blanc.Lift.Curve3Pool (answerWord balanceOfData transferSel transferFromSel adrOf)
open Blanc.Lift.CurveCoins (PoolCoinSel)
open Blanc.Lift.CurveCoins.Usdt (NotDeprecated usdtDebit)

variable {d : Deployment} {future : BlockChain} {h : MainnetHistory d.minter.post future}

theorem usdt_start_code (A : Assumes d h) : d.poolCut.afterBenv.state.getCode usdt = Lift.Usdt.code := A.usdtStart

/-- A settled non-static frame at USDT encloses no frame. -/
theorem usdt_below (A : Assumes d h) {G : Exec.Frame} (member : G ∈ (d.sincePool h).settledFrames)
    (target : G.sevm.currentTarget = usdt) (mutable : G.sevm.isStatic = false) :
    Exec.descendantFrames G.run = [] :=
  CurveCoins.Usdt.descendants_nil
    (CurveCoins.Usdt.settled_codeFrame BodyStageCapabilities.historical (d.sincePool h) (usdt_start_code A) member target)
    target (A.notDeprecated G (mem_coinFrames.mpr ⟨member, target, mutable, trivial⟩))

/-- **USDT's locality over the history from the pool's creation.** -/
theorem usdt_local (A : Assumes d h) :
    EntryLocal usdt (fun _ => True) (CodeFrame usdt HistFork Lift.Usdt.code)
      (fun σ => (σ (Lift.Usdt.balSlot pool)).toNat) (usdtDebit pool) (fun _ => 0)
      (wordsAt usdt d.poolCut.afterBenv.state) (wordsAt usdt future.state) (d.sincePool h).settledFrames := by
  refine CurveCoins.Usdt.usdt_entry_local BodyStageCapabilities.historical (d.sincePool h) (usdt_start_code A)
    (NoKeyHolder.usdtAuthority A.keys fun F hF caller => ?_) A.notDeprecated A.tether.noConfiscation
    A.hashes.coinKeys.usdt
  obtain ⟨member, target, mutable, -⟩ := mem_coinFrames.mp hF
  refine pool_ownCalls_history A (T := usdt) (by decide) member target mutable caller fun G hG child mg te => ?_
  have nil := usdt_below A hG (te.trans target) mg
  have := Exec.mem_descendantFrames_of_mem_childFrames G.run F child
  rw [nil] at this
  cases this

/-- USDT's entry for the pool, as a book. -/
def usdtBook : CoinBook :=
  flatBook usdt (CodeFrame usdt HistFork Lift.Usdt.code) (fun σ => (σ (Lift.Usdt.balSlot pool)).toNat)
    (usdtDebit pool) (fun _ => 0)

/-- **The flag is clear at every position.** -/
theorem usdt_flag_clear (A : Assumes d h) {before : List Exec.Frame}
    (sub : ∀ F ∈ before, F ∈ (d.sincePool h).settledFrames) {m : StorWords}
    (chain : FrameChain usdt (CodeFrame usdt HistFork Lift.Usdt.code) (wordsAt usdt d.poolCut.afterBenv.state)
      (coinFrames usdt (fun _ => True) before) m) : Usdt.flag20 (m 10) = 0 := by
  refine (chain.fold (held := fun _ => 0) (credit := fun _ => 0) (debit := fun _ => 0)
    (I := fun w => Usdt.flag20 (w 10) = 0) (fun G hG good flag => ⟨?_, Nat.le_refl _⟩) A.tether.notRedirected).1
  obtain ⟨member, target, mutable, -⟩ := mem_coinFrames.mp hG
  have whole : G ∈ coinFrames usdt (fun _ => True) (d.sincePool h).settledFrames :=
    mem_coinFrames.mpr ⟨sub G member, target, mutable, trivial⟩
  have keep := CurveCoins.Usdt.frame_flag_keep whole A.hashes.coinKeys.usdt good target
    (A.notDeprecated G whole) (A.tether.noDeprecate G whole)
  change Usdt.flag20 ((G.post.getStor usdt).get 10) = 0
  rw [keep]
  exact flag

/-- **USDT's `CoinWalk`.** -/
theorem usdtWalk (A : Assumes d h) :
    CoinWalk usdtBook pool 2 (d.sincePool h).settledFrames (d.sincePool h).settledRoots
      (wordsAt usdt d.poolCut.afterBenv.state) (wordsAt usdt future.state)
      Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN :=
  flat_walk A (usdt_local A) coin2_eq
    (fun j hj => by
      match j, hj with
      | 0, _ => decide +kernel
      | 1, _ => decide +kernel
      | 2, hj => exact absurd rfl hj)
    (by decide +kernel) (by decide)
    (fun _ _ ne => ite_eq_right fun c => absurd c.1 ne)
    (fun G hG target mutable f hf => by
      rw [usdt_below A hG target mutable] at hf
      cases hf)
    (fun e dst amt hd => by
      obtain ⟨-, -, w36⟩ := transfer_words hd
      unfold usdtDebit
      split
      · rw [w36]
        exact toB256_toNat_le amt
      · exact Nat.zero_le _)
    (fun e src amt hd _ => by
      obtain ⟨sel, -, -, -⟩ := transferFrom_words hd
      exact ite_eq_right fun c => absurd (c.2.symm.trans sel) sel_ne)
    (fun ne => absurd rfl ne)
    (fun H c hc member tc hd _ sub chain =>
      H.usdt_answer hc (Blanc.Lift.settled_wf _ member) tc hd (usdt_flag_clear A sub chain))

/-- **The pool's books of USDT are at most what USDT's storage says it holds.** -/
theorem usdt_backed (A : Assumes d h) :
    recorded future.state 2 ≤ coinHeld future.state pool 2 :=
  (A.coin_walk_whole (usdtWalk A)).1

end Blanc.Composition.Curve3PoolBacked
