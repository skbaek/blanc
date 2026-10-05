import Blanc.Lift.Weth9.LiveWriters
import Blanc.Lift.Weth9.FootFrame
import Blanc.Composition.UniswapV2PairWeth9
import Blanc.Composition.UniswapV2PairWeth9GasFree
import Blanc.ExecDeterminism

/-!
# WETH9 side of the Uniswap V2 composition: the frames the pair observes

The pair reads its WETH9 balance with `balanceOf(pair)` and pays out with `transfer(to, amount)`.  This
module reads both back from *any* successful frame of the deployed WETH9 code (an `Exec` derivation,
not a constructed witness):

* `weth9_view_keeps_storage`: a successful `balanceOf(who)` frame leaves the WETH9 storage unchanged,
  whatever its gas;
* `weth9_transfer_effect`: a successful `transfer(to, wad)` frame has exactly the storage effect
  `xferStorStep` (so `wad` was at most the caller's balance), whatever its gas;
  `weth9_transfer_fails_of_lt` says a transfer of more than the caller's balance has no successful
  frame at all.

The output facts carry no gas premise: the actual frame is compared with the gas-exact forward run
(`weth9_balanceOf_runExact`, `weth9_transfer_runExact`) from the same state with its gas raised to cover
the certified cost.  The dispatcher and the `balanceOf`/`transfer` wrappers are gas-free, so the two
runs end in states equal modulo `gasLeft` (`weth9_balanceOf_eqModGas`, `weth9_transfer_eqModGas`), and
the forward run's output is the actual frame's.
-/

namespace Blanc.Composition.UniswapV2PairWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9

/-- A successful frame of the deployed WETH9 code runs the lifted program. -/
theorem weth9_runP {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork) (run : Exec 0 sevm pre (.ok post)) :
    SProg.RunP (StepIn ⟨0, sevm, pre, .ok post, run⟩) prog sevm pre post :=
  lift_sound_in cert_check hcode fork run

theorem decodeCall_balanceOf {sevm : Sevm} (h_sel : Sevm.selector sevm = boSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256) :
    decodeCall sevm = none := by
  have hs : Sevm.selector sevm = 0x70a08231 := h_sel.trans boSel_eq
  unfold decodeCall
  simp (config := {decide := true}) only [not_shortCall h_len h_len', hs, ↓reduceIte, true_or,
    or_true]

theorem decodeCall_transfer {sevm : Sevm} (h_sel : Sevm.selector sevm = trSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256) :
    decodeCall sevm =
      some (.transfer sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)) := by
  have hs : Sevm.selector sevm = 0xa9059cbb := h_sel.trans trSel_eq
  unfold decodeCall
  simp (config := {decide := true}) only [not_shortCall h_len h_len', hs, ↓reduceIte]

/-- **A successful WETH9 view frame keeps the WETH9 storage.** -/
theorem weth9_view_keeps_storage {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork) (run : Exec 0 sevm pre (.ok post))
    (hview : decodeCall sevm = none) :
    Devm.getStor post sevm.currentTarget = Devm.getStor pre sevm.currentTarget := by
  rcases weth9_frame_effect StepIn.toRun fork (weth9_runP hcode fork run) with ⟨-, hst⟩ |
      ⟨c, hd, -, -⟩ | ⟨who, w, hd, -⟩
  · exact hst
  · rw [hview] at hd; cases hd
  · rw [hview] at hd; cases hd

/-- **Every successful `transfer(to, wad)` frame of the deployed WETH9 is the ledger move.**  Its
storage effect is `xferStorStep` from the caller to `to` (whatever the gas). -/
theorem weth9_transfer_effect {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (h_sel : Sevm.selector sevm = trSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (run : Exec 0 sevm pre (.ok post)) :
    xferStorStep (Devm.getStor pre sevm.currentTarget) sevm.caller sevm.caller
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) =
      some (Devm.getStor post sevm.currentTarget) := by
  have hdec := decodeCall_transfer h_sel h_len h_len'
  rcases weth9_frame_effect StepIn.toRun fork (weth9_runP hcode fork run) with ⟨hd, -⟩ |
      ⟨c, hd, -, hst⟩ | ⟨who, w, hd, -⟩
  · rw [hdec] at hd; cases hd
  · rw [hdec] at hd
    cases hd
    simpa only [Call.stor] using hst
  · rw [hdec] at hd; cases hd

/-- A successful transfer moved at most the caller's balance. -/
theorem xferStorStep_le {s s' : Stor} {who src dst : Adr} {wad : B256}
    (h : xferStorStep s who src dst wad = some s') : wad ≤ s.get (balSlot src) := by
  unfold xferStorStep at h
  by_cases hlt : s.get (balSlot src) < wad
  · simp only [hlt, ↓reduceIte, reduceCtorEq] at h
  · exact B256.not_lt.mp hlt

/-- **A transfer of more than the caller's balance is a genuine failure**: no frame of it succeeds. -/
theorem weth9_transfer_fails_of_lt {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (h_sel : Sevm.selector sevm = trSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hlt : (Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) < Sevm.dataWord sevm 36) :
    Exec 0 sevm pre (.ok post) → False := fun run =>
  B256.not_lt.mpr (xferStorStep_le (weth9_transfer_effect hcode fork h_sel h_len h_len' run)) hlt

end Blanc.Composition.UniswapV2PairWeth9
