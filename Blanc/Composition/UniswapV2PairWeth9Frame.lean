import Blanc.Lift.Weth9.LiveWriters
import Blanc.Lift.Weth9.FootFrame
import Blanc.Composition.UniswapV2PairWeth9
import Blanc.ExecDeterminism

/-!
# WETH9 side of the Uniswap V2 composition: the frames the pair observes

The pair reads its WETH9 balance with `balanceOf(pair)` and pays out with `transfer(to, amount)`.  This
module reads both back from *any* successful frame of the deployed WETH9 code (an `Exec` derivation,
not a constructed witness):

* `weth9_view_keeps_storage`, `weth9_balanceOf_answer`: a successful `balanceOf(who)` frame leaves the
  WETH9 storage unchanged, and, when its gas covers the certified cost `weth9Gas`, returns the stored
  balance word of `who` (the answer the pair decodes from the first 32 returned bytes);
* `weth9_transfer_effect`, `weth9_transfer_returns_true`: a successful `transfer(to, wad)` frame has
  exactly the storage effect `xferStorStep` (so `wad` was at most the caller's balance), and, when its gas
  is at least `transferGas + 353`, returns the true word; `weth9_transfer_fails_of_lt` says a transfer of
  more than the caller's balance has no successful frame at all;
* `weth9_frame_holder_noShrink`: a successful non-`withdraw` WETH9 frame entered under the footprint
  frame invariant, called by someone other than a holder `p` whose tracked allowances are zero, keeps
  them zero and does not lower `p`'s balance word.

The output facts are read through determinism (`Exec.result_unique`) against the gas-exact forward runs
`weth9_balanceOf_runExact` and `weth9_transfer_live`, so they carry those runs' gas premises: a
successful frame with less gas than the certified cost is not excluded by a theorem here.
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

/-- **Every successful `balanceOf(who)` frame of the deployed WETH9 answers the stored balance.**  A
fresh frame (empty stack and memory, no value) with gas at least the certified cost: its output is the
balance word of `who`, the pair's decoded answer (`Bytes.toB256` of the first 32 bytes) is that word, and
the WETH9 storage is unchanged. -/
theorem weth9_balanceOf_answer {sevm : Sevm} {pre post : Devm} {cost : Nat}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = boSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_cost : weth9Gas (Sevm.selector sevm) sevm pre = some cost) (h_gas : cost ≤ pre.gasLeft)
    (run : Exec 0 sevm pre (.ok post)) :
    post.output = (Devm.getStorVal pre sevm.currentTarget
        (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes ∧
      Bytes.toB256 (post.output.take 32) =
        Devm.getStorVal pre sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr) ∧
      Devm.getStor post sevm.currentTarget = Devm.getStor pre sevm.currentTarget := by
  obtain ⟨post0, hrun0, -, hout⟩ :=
    weth9_balanceOf_runExact fork h_value h_sel h_len h_len' h_stack h_mem h_cost h_gas
  obtain ⟨run0⟩ := exec_of_runExact hcode fork hrun0
  have heq := Exec.result_unique run run0
  injection heq with heq
  subst heq
  refine ⟨hout, ?_, weth9_view_keeps_storage hcode fork run (decodeCall_balanceOf h_sel h_len h_len')⟩
  rw [hout, List.take_of_length_le (Nat.le_of_eq (B256.length_toBytes _)), B256.toB256_toBytes]

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

/-- **Every successful `transfer(to, wad)` frame with enough gas returns the true word.**  A fresh,
non-static, zero-value frame whose gas is `G + transferGas` with `353 ≤ G` returns `(1).toBytes` (the
word the pair's `_safeTransfer` decodes as success) and ends at gas `G`. -/
theorem weth9_transfer_returns_true {sevm : Sevm} {pre post : Devm} {G : Nat}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = trSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + transferGas sevm pre) (hG : 353 ≤ G)
    (run : Exec 0 sevm pre (.ok post)) :
    post.output = (1 : B256).toBytes ∧ post.gasLeft = G := by
  have hle := xferStorStep_le (weth9_transfer_effect hcode fork h_sel h_len h_len' run)
  obtain ⟨post0, hexec, hg, hout, -⟩ := weth9_transfer_live hcode fork h_static h_value h_sel h_len
    h_len' h_stack h_mem hle h_gas hG
  have run0 := (exec_iff_exec_eq 0 sevm pre (.ok post0)).mpr hexec
  obtain ⟨run0⟩ := run0
  have heq := Exec.result_unique run run0
  injection heq with heq
  subst heq
  exact ⟨hout, hg⟩

/-- **A WETH9 frame by someone else does not lower a holder's balance.**  A successful frame of the
deployed WETH9 code, entered under the footprint frame invariant over `U` (`(footSpec U).Pre`, the
invariant WETH9's history ladder carries to every admitted frame) with its keys tracked, that does not
decode as `withdraw` and whose caller is not `p`: if `p`'s balance row is tracked and every tracked
allowance granted by `p` is zero, they stay zero and `p`'s balance word does not fall.  (`withdraw` sends
ether and may be re-entered; its own debit is the caller's, and its re-entered calls are separate frames,
which the history reading `weth9_history_holder_noShrink` replays in order.) -/
theorem weth9_frame_holder_noShrink {U : Key → Prop} {sevm : Sevm} {pre post : Devm} {p : Adr}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (run : Exec 0 sevm pre (.ok post))
    (hpre : (footSpec U).Pre sevm.currentTarget sevm pre)
    (hinj : KeyInj U) (hkeys : ∀ k ∈ frameKeys sevm, U k)
    (hnw : ∀ who w, decodeCall sevm ≠ some (.withdraw who w))
    (hcaller : sevm.caller ≠ p) (holderTracked : U (.bal p))
    (allowZero : ∀ g, U (.allow p g) → (Devm.getStor pre sevm.currentTarget).get (allowSlot p g) = 0) :
    ((Devm.getStor pre sevm.currentTarget).get (balSlot p)).toNat ≤
        ((Devm.getStor post sevm.currentTarget).get (balSlot p)).toNat ∧
      ∀ g, U (.allow p g) → (Devm.getStor post sevm.currentTarget).get (allowSlot p g) = 0 := by
  rcases weth9_frame_effect StepIn.toRun fork (weth9_runP hcode fork run) with ⟨-, hst⟩ |
      ⟨c, hd, -, hstor⟩ | ⟨who, w, hd, -⟩
  · rw [hst]
    exact ⟨Nat.le_refl _, allowZero⟩
  · have hstep := Call.stor_ledger hinj (fun k hk => hkeys k (decodeCall_keys hd k hk)) hstor
    have hbound : trackedSum U (Devm.getStor pre sevm.currentTarget) + sevm.value.toNat <
        2 ^ 256 := by
      have h := (footSpec_inv.mp (hpre.inv.left rfl)).2
      have hlt := B256.toNat_lt (pre.getBal sevm.currentTarget)
      omega
    have hcallerOf : callCaller c = sevm.caller ∧ c.inflow ≤ sevm.value.toNat := by
      unfold decodeCall at hd
      split_ifs at hd <;> cases hd <;>
        exact ⟨rfl, by simp only [Call.inflow, Nat.le_refl, Nat.zero_le]⟩
    have hc : HolderCall p c := fun h => absurd (hcallerOf.1.symm.trans h) hcaller
    have hfit : (ledger U (Devm.getStor pre sevm.currentTarget)).total + c.inflow < 2 ^ 256 := by
      have ht : (ledger U (Devm.getStor pre sevm.currentTarget)).total =
          trackedSum U (Devm.getStor pre sevm.currentTarget) := rfl
      omega
    obtain ⟨hz, hbal⟩ := Ledger.step_holder (ledger_allowZero allowZero) hc hfit hstep
    have hdeb : holderDebit p c = 0 := by
      cases c with
      | transfer who dst w =>
        have hw : who ≠ p := fun h => hcaller (hcallerOf.1.symm.trans h)
        simp only [holderDebit, hw, false_and, ↓reduceIte]
      | _ => rfl
    have h0 : (ledger U (Devm.getStor pre sevm.currentTarget)).bal p =
        (Devm.getStor pre sevm.currentTarget).get (balSlot p) := tracked_self holderTracked
    have h1 : (ledger U (Devm.getStor post sevm.currentTarget)).bal p =
        (Devm.getStor post sevm.currentTarget).get (balSlot p) := tracked_self holderTracked
    rw [hdeb, Nat.add_zero, h0, h1] at hbal
    refine ⟨hbal, fun g hg => ?_⟩
    have := hz g
    rwa [show (ledger U (Devm.getStor post sevm.currentTarget)).allow p g =
      (Devm.getStor post sevm.currentTarget).get (allowSlot p g) from trackedAllow_self hg] at this
  · exact absurd hd (hnw who w)

end Blanc.Composition.UniswapV2PairWeth9
