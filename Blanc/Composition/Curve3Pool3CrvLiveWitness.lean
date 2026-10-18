import Blanc.Composition.Curve3Pool3CrvCoinAnswers
import Blanc.Composition.Curve3Pool3CrvHeadlines
import Blanc.Lift.VyperNonreentrantDeployed.Token20.RunBalance

/-!
# The liveness premises are satisfiable by `Token20` coins and the deployed 3Crv

Every state-changing callee call of a pool liveness theorem maps its world invariant to a fresh
one (`removeLiquidity_live`, `addLiquidity_live`, `removeLiquidityImbalance_live`,
`removeLiquidityOneCoin_live`).  Here each theorem's callee premises are instantiated, with
explicit world chains, by actual callees: coins running `Token20` (`token20_coinPullOkAt`,
`token20_coinPushOkAt`, `token20_coinBalOkAt` — the token's own code answers) and the deployed
3Crv (`c3crv_supplyOkAt`, `c3crv_burnOkAt`, `c3crv_mintOkAt`).

`<entry>_premises_satisfiable`: from a frame's pre-state where the coins hold `Token20`, each
coin call fits the coin's ledger (`T20MoveFits`, `T20PullFits`, any amounts, positive ones
included), 3Crv holds its code with supply `T` and accepts the burn/mint (`BurnFits`,
`MintFits`), and the accounts involved are distinct, non-precompile and not the pool, there are
world chains `W` with `W 0 pre` satisfying every callee premise of the entry's liveness theorem
at `U = 80000`.  Only the callee premises are proved here: the model step (`hstep`) at the entry
is not discharged, agreement of the chosen amounts with the model's outputs is not proved, and
the composed `_live_entry` forms are not instantiated.  The chains pin, at each call, 3Crv's
storage (the entry storage before its state-changing call, the model's result after) and the
storage of every coin not yet called (its entry storage), so each coin call's acceptance is a
fact about the entry state.  (`exchange`'s end-to-end instance is `ex_frame_live`.)

* `WClosed.of_foreign`: an invariant reading only code and storage outside the pool survives the
  pool's own steps;
* `token20_coinBalOkAt`: `balanceOf(self)` answered by `Token20`'s code, at any window.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3At c3At_burn c3At_mint precomp_false)
open VyperNonreentrantDeployed.Token20 (balSlot allowSlot balanceOfGas balanceOfPost boHolder
  balanceOf_runExact cert_check cert_jumpsOk)

/-! ## `balanceOf(self)` from `Token20`'s code -/

section Bal

variable {sevm : Sevm} {t B : B256} {W W' : Devm → Prop} {c : Adr} {U : Nat} {ii oi : B256}

/-- **A coin answers the pool's `balanceOf(self)` from `Token20`'s code** (`CoinBalOkAt` at any
window inside `[0, 4096)`): wherever the coin holds `Token20` and the pool's balance is `B`. -/
theorem token20_coinBalOkAt (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp c) (ht : t.toAdr = c) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode c = VyperNonreentrantDeployed.Token20.code ∧
      (b.getStor c).get (balSlot sevm.currentTarget) = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    CoinBalOkAt sevm W W' t B U ii oi := by
  refine staticWordOkAt_of_child 2206 (by decide) hfork hdepth
    (by rw [ht]; exact prec_false hprec) hU
    (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hin hfwd
  obtain ⟨hc, hB⟩ := hW b hWb
  have hcC : (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).code =
      VyperNonreentrantDeployed.Token20.code := by
    rw [staticMsg_code, ht]; exact hc
  have hfC : CoveredFork (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).benvStat.fork := by
    rw [staticMsg_benvStat]; exact hfork
  have hd : (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).data =
      abiSelectorBytes 0x70a08231 ++ sevm.currentTarget.toB256.toBytes := by
    rw [staticMsg_data, hin]
    unfold balanceOfData
    rw [balanceOfSel_abi]
  have hsel : Sevm.selector (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have hhold : boHolder (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)) =
      sevm.currentTarget := by
    unfold boHolder
    rw [cc_dataWord_oneWord hd, toAdr_toB256]
  have hbg : balanceOfGas (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
      (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)) ≤ 2206 := by
    unfold balanceOfGas
    have := sloadCost_le (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
      (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
      (balSlot (boHolder (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))))
    unfold gasColdSload at *
    omega
  have hgl : (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).gasLeft =
      fwd b S M G t ii 0x24 oi 0x20 := rfl
  have run := balanceOf_runExact (pre := initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
    (G := fwd b S M G t ii 0x24 oi 0x20 - balanceOfGas
      (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
      (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)))
    hfC hsel rfl rfl (by rw [hgl]; omega)
  have hexec := (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact cert_check cert_jumpsOk hcC hfC run)
  obtain ⟨pe, po, pg, ps⟩ := retPost_facts
    (afterSload (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
      (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
      (balSlot (boHolder (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)))))
    [Sevm.selector (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))]
    (Mem.empty.write 0 ((initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).getStorVal
      (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).currentTarget
      (balSlot (boHolder (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))))).toBytes)
    (fwd b S M G t ii 0x24 oi 0x20 - balanceOfGas
      (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
      (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)))
    ((initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).getStorVal
      (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)).currentTarget
      (balSlot (boHolder (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)))))
  have hst : (balanceOfPost (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
      (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
      (fwd b S M G t ii 0x24 oi 0x20 - balanceOfGas
        (initSevm (staticMsg sevm b S M G t ii 0x24 oi 0x20))
        (initDevm (staticMsg sevm b S M G t ii 0x24 oi 0x20)))).state = b.state := by
    unfold balanceOfPost
    rw [ps]
    unfold afterSload
    split <;> rfl
  refine ⟨by rw [ht, hc]; exact token20_undelegated, _, hexec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold balanceOfPost
    rw [pe, afterSload_error]
    rfl
  · unfold balanceOfPost
    rw [pg]
    omega
  · unfold balanceOfPost
    rw [pg]
    omega
  · unfold balanceOfPost
    rw [po, hhold, getStorVal_eq_getStor, staticMsg_currentTarget, staticMsg_getStor, ht, hB]
  · rw [getCode_of_state hst]
  · refine hW' b _ hWb (fun a => ?_) (fun a => ?_)
    · rw [getStor_of_state (callChildPost_state' _ _ _ _), getStor_of_state hst]
    · rw [getCode_of_state (callChildPost_state' _ _ _ _), getCode_of_state hst]

end Bal

/-! ## The frame's coins and 3Crv at its entry -/

section Entry

variable (sevm : Sevm) (pre : Devm)

/-- The pool's coin `k`, as the frame's entry storage names it. -/
abbrev coinOf (k : Fin 3) : Adr := ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr

/-- The pool's token, as the frame's entry storage names it. -/
abbrev tokOf : Adr := ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr

/-- **The frame's coins as `Token20` coins**: `Token20`'s code at the entry, no precompile,
neither the pool nor its token, pairwise distinct. -/
structure T20Coins : Prop where
  code : ∀ k : Fin 3, pre.getCode (coinOf sevm pre k) = VyperNonreentrantDeployed.Token20.code
  prec : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (coinOf sevm pre k)
  pool : ∀ k : Fin 3, coinOf sevm pre k ≠ sevm.currentTarget
  tok : ∀ k : Fin 3, coinOf sevm pre k ≠ tokOf sevm pre
  apart : ∀ j k : Fin 3, j ≠ k → coinOf sevm pre j ≠ coinOf sevm pre k

/-- **3Crv at the frame's entry**: the pool's token holds 3Crv's code with supply `T`, and is
neither the pool nor a precompile. -/
structure C3Entry (T : B256) : Prop where
  code : pre.getCode (tokOf sevm pre) = Curve3Crv.code
  supply : (Devm.getStor pre (tokOf sevm pre)).get Curve3Crv.vySupplySlot = T
  pool : tokOf sevm pre ≠ sevm.currentTarget
  prec : ¬ sevm.benvStat.rules.isPrecomp (tokOf sevm pre)

/-- **Coin `k` as at the frame's entry**: `Token20`'s code and its entry ledger. -/
def CoinPinned (k : Fin 3) (b : Devm) : Prop :=
  b.getCode (coinOf sevm pre k) = VyperNonreentrantDeployed.Token20.code ∧
    b.getStor (coinOf sevm pre k) = pre.getStor (coinOf sevm pre k)

end Entry

/-- A pinned coin survives a step keeping the code everywhere and its storage. -/
theorem coinPinned_keep {sevm : Sevm} {pre b d : Devm} {k : Fin 3} (h : CoinPinned sevm pre k b)
    (hs : Devm.getStor d (coinOf sevm pre k) = Devm.getStor b (coinOf sevm pre k))
    (hc : ∀ a, d.getCode a = b.getCode a) : CoinPinned sevm pre k d :=
  ⟨(hc _).trans h.1, hs.trans h.2⟩

/-- 3Crv as given survives a step keeping the code everywhere and 3Crv's storage. -/
theorem c3At_keep' {c3 : Adr} {σ : Stor} {b d : Devm} (h : C3At c3 σ b)
    (hs : Devm.getStor d c3 = Devm.getStor b c3) (hc : ∀ a, d.getCode a = b.getCode a) :
    C3At c3 σ d :=
  ⟨(hc c3).trans h.1, hs.trans h.2⟩

theorem fin3_ne_of_lt {j k : Fin 3} (h : k.val < j.val) : j ≠ k := fun e => by
  rw [e] at h; exact Nat.lt_irrefl _ h

/-! ## `remove_liquidity` -/

section RemoveLiquidity

variable (sevm : Sevm) (pre : Devm)

/-- `remove_liquidity`'s world chain: 3Crv at its entry storage up to the burn and at the burned
storage after (`W 4`); before coin `k`'s push, coins `k, …, 2` as at the entry. -/
def rlWorld (k : Nat) (b : Devm) : Prop :=
  C3At (tokOf sevm pre) (if 4 ≤ k then burnStor (Devm.getStor pre (tokOf sevm pre))
    sevm.caller.toB256 (rlAmt sevm) else Devm.getStor pre (tokOf sevm pre)) b ∧
    ∀ j : Fin 3, k ≤ j.val → CoinPinned sevm pre j b

end RemoveLiquidity

/-- **`removeLiquidity_live`'s callee premises are satisfiable**: with `Token20` coins whose
ledgers cover the pushes and the deployed 3Crv accepting the burn, the world chain `rlWorld`
satisfies every callee premise at `U = 80000`, starting from the frame's entry. -/
theorem removeLiquidity_premises_satisfiable {sevm : Sevm} {pre : Devm} {T : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre)
    (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256
      (rlAmt sevm))
    (hfits : ∀ k : Fin 3, T20MoveFits (pre.getStor (coinOf sevm pre k)) sevm.currentTarget
      sevm.caller (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T)) :
    (∀ k, k ≤ 3 → WClosed sevm (rlWorld sevm pre k)) ∧ rlWorld sevm pre 0 pre ∧
      SupplyOk sevm (rlWorld sevm pre 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T
        80000 ∧
      (∀ k : Fin 3, CoinPushOkAt sevm (rlWorld sevm pre k) (rlWorld sevm pre (k + 1))
        ((pre.getStor sevm.currentTarget).get (coinSlot k))
        (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) 80000 0x520 0x5c0) ∧
      BurnOkTo sevm (rlWorld sevm pre 3) (rlWorld sevm pre 4)
        ((pre.getStor sevm.currentTarget).get tokenSlot) (rlAmt sevm) 80000 := by
  have e0 : ∀ n, n ≤ 3 → (if 4 ≤ n then burnStor (Devm.getStor pre (tokOf sevm pre))
      sevm.caller.toB256 (rlAmt sevm) else Devm.getStor pre (tokOf sevm pre)) =
      Devm.getStor pre (tokOf sevm pre) := fun n hn => ite_eq_right (by omega)
  refine ⟨fun k _ => WClosed.of_foreign fun b d hb hs hc => ⟨c3At_keep' hb.1 (hs _ hc3.pool) hc,
    fun j hj => coinPinned_keep (hb.2 j hj) (hs _ (hcoins.pool j)) hc⟩,
    ⟨⟨hc3.code, (e0 0 (by decide)).symm⟩, fun j _ => ⟨hcoins.code j, rfl⟩⟩, ?_, fun k => ?_, ?_⟩
  · exact c3crv_supplyOk hfork hdepth (precomp_false hc3.prec) (by decide)
      (fun b hb => ⟨hb.1.1, by rw [hb.1.2, e0 0 (by decide)]; exact hc3.supply⟩)
      (fun b d hb hs hc => ⟨c3At_keep' hb.1 (hs _) hc,
        fun j hj => coinPinned_keep (hb.2 j hj) (hs _) hc⟩)
  · refine token20_coinPushOkAt hfork hstatic hdepth (hcoins.prec k) rfl (hcoins.pool k)
      (le_refl _) (by decide) (by decide) (fun b hb => ⟨(hb.2 k (le_refl _)).1, ?_⟩)
      (fun b d hb hl => ⟨?_, fun j hj => ?_⟩)
    · rw [(hb.2 k (le_refl _)).2]; exact hfits k
    · have h1 := hb.1
      rw [e0 _ (by omega)] at h1
      rw [e0 _ (by omega)]
      exact c3At_keep' h1 (hl.other _ (Ne.symm (hcoins.tok k))) hl.code
    · exact coinPinned_keep (hb.2 j (by omega))
        (hl.other _ (hcoins.apart j k (fin3_ne_of_lt (by omega)))) hl.code
  · refine (c3crv_burnOkAt (ii := 0x61c) (oi := 0x6a0) hfork hstatic hdepth
      (precomp_false hc3.prec) (by decide) (by decide) (by decide) ?_ ?_).burnOkTo
    · intro b hb
      exact ⟨hb.1.1, hc3.pool, by rw [hb.1.2, e0 3 (by decide)]; exact hburn⟩
    · intro b d hb _ hs hc
      refine ⟨⟨(hc _).trans hb.1.1, ?_⟩, fun j hj => absurd j.isLt (by omega)⟩
      rw [hs, hb.1.2, e0 3 (by decide), ite_eq_left (by decide)]

/-! ## `add_liquidity` -/

section AddLiquidity

variable (sevm : Sevm) (pre : Devm)

/-- The fee coin's ledger after its pull. -/
abbrev alFeeStor : Stor :=
  t20Move (t20Allow (pre.getStor (coinOf sevm pre 2)) sevm.caller sevm.currentTarget
    (alAmt sevm 2)) sevm.caller sevm.currentTarget (alAmt sevm 2)

/-- `add_liquidity`'s world chain: 3Crv at its entry storage up to the mint and at the minted
storage after (`W 4`); before coin `k`'s pull, coins `k, …, 2` as at the entry; after the fee
coin's pull (`W 3`), its ledger as the pull leaves it. -/
def alWorld (m : B256) (k : Nat) (b : Devm) : Prop :=
  C3At (tokOf sevm pre) (if 4 ≤ k then mintStor (Devm.getStor pre (tokOf sevm pre))
    sevm.caller.toB256 m else Devm.getStor pre (tokOf sevm pre)) b ∧
    (∀ j : Fin 3, k ≤ j.val → CoinPinned sevm pre j b) ∧
    (k = 3 → alAmt sevm 2 ≠ 0 →
      b.getCode (coinOf sevm pre 2) = VyperNonreentrantDeployed.Token20.code ∧
        b.getStor (coinOf sevm pre 2) = alFeeStor sevm pre)

end AddLiquidity

/-- **`addLiquidity_live`'s callee premises are satisfiable**: with `Token20` coins whose
ledgers and allowances cover the pulls (the fee coin's two `balanceOf(self)` answers are its
ledger before and after) and the deployed 3Crv accepting the mint of `m`, the world chain
`alWorld` satisfies every callee premise at `U = 80000`, starting from the frame's entry. -/
theorem addLiquidity_premises_satisfiable {sevm : Sevm} {pre : Devm} {T m : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre)
    (hmint : MintFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 m)
    (hfits : ∀ k : Fin 3, alAmt sevm k.val ≠ 0 → T20PullFits (pre.getStor (coinOf sevm pre k))
      sevm.caller sevm.currentTarget sevm.currentTarget (alAmt sevm k.val)) :
    (∀ k, k ≤ 4 → WClosed sevm (alWorld sevm pre m k)) ∧ alWorld sevm pre m 0 pre ∧
      SupplyOkAt sevm (alWorld sevm pre m 0) (alWorld sevm pre m 0)
        ((pre.getStor sevm.currentTarget).get tokenSlot) T 80000 0x27c 0x2c0 ∧
      (∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
        CoinPullOkAt sevm (alWorld sevm pre m k) (alWorld sevm pre m (k + 1))
          ((pre.getStor sevm.currentTarget).get (coinSlot k)) (alAmt sevm k.val) 80000 0x760
          0x820) ∧
      (∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, alWorld sevm pre m k b →
        alWorld sevm pre m (k + 1) b) ∧
      (alAmt sevm 2 ≠ 0 →
        CoinBalOkAt sevm (alWorld sevm pre m 2) (alWorld sevm pre m 2)
          ((pre.getStor sevm.currentTarget).get (coinSlot 2))
          ((pre.getStor (coinOf sevm pre 2)).get
            (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget)) 80000 0x53c 0x5a0 ∧
        CoinPullOkAt sevm (alWorld sevm pre m 2) (alWorld sevm pre m 3)
          ((pre.getStor sevm.currentTarget).get (coinSlot 2)) (alAmt sevm 2) 80000 0x760 0x820 ∧
        CoinBalOkAt sevm (alWorld sevm pre m 3) (alWorld sevm pre m 3)
          ((pre.getStor sevm.currentTarget).get (coinSlot 2))
          ((alFeeStor sevm pre).get (VyperNonreentrantDeployed.Token20.balSlot sevm.currentTarget))
          80000 0x87c 0x8e0) ∧
      MintOkAt sevm (alWorld sevm pre m 3) (alWorld sevm pre m 4)
        ((pre.getStor sevm.currentTarget).get tokenSlot) m 80000 0xc7c 0xd00 := by
  have e0 : ∀ n, n ≤ 3 → (if 4 ≤ n then mintStor (Devm.getStor pre (tokOf sevm pre))
      sevm.caller.toB256 m else Devm.getStor pre (tokOf sevm pre)) =
      Devm.getStor pre (tokOf sevm pre) := fun n hn => ite_eq_right (by omega)
  have keep : ∀ k b d, alWorld sevm pre m k b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → alWorld sevm pre m k d :=
    fun k b d hb hs hc => ⟨c3At_keep' hb.1 (hs _) hc,
      fun j hj => coinPinned_keep (hb.2.1 j hj) (hs _) hc,
      fun h3 ha => ⟨(hc _).trans (hb.2.2 h3 ha).1, (hs _).trans (hb.2.2 h3 ha).2⟩⟩
  refine ⟨fun k _ => WClosed.of_foreign fun b d hb hs hc => ⟨c3At_keep' hb.1 (hs _ hc3.pool) hc,
    fun j hj => coinPinned_keep (hb.2.1 j hj) (hs _ (hcoins.pool j)) hc,
    fun h3 ha => ⟨(hc _).trans (hb.2.2 h3 ha).1, (hs _ (hcoins.pool 2)).trans (hb.2.2 h3 ha).2⟩⟩,
    ⟨⟨hc3.code, (e0 0 (by decide)).symm⟩, fun j _ => ⟨hcoins.code j, rfl⟩,
      fun h => absurd h (by decide)⟩, ?_, fun k hk ha => ?_, fun k hz b hb => ?_, fun ha => ?_, ?_⟩
  · exact c3crv_supplyOkAt hfork hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, by rw [hb.1.2, e0 0 (by decide)]; exact hc3.supply⟩)
      (fun b d hb hs hc => keep 0 b d hb hs hc)
  · have hk2 : k.val ≠ 2 := fun h => hk (Fin.ext h)
    refine token20_coinPullOkAt hfork hstatic hdepth (hcoins.prec k) rfl (hcoins.pool k)
      (le_refl _) (by decide) (by decide) (fun b hb => ⟨(hb.2.1 k (le_refl _)).1, ?_⟩)
      (fun b d hb hl => ⟨?_, fun j hj => ?_, fun h3 => absurd h3 (by omega)⟩)
    · rw [(hb.2.1 k (le_refl _)).2]; exact hfits k ha
    · have h1 := hb.1
      rw [e0 _ (by omega)] at h1
      rw [e0 _ (by omega)]
      exact c3At_keep' h1 (hl.other _ (Ne.symm (hcoins.tok k))) hl.code
    · exact coinPinned_keep (hb.2.1 j (by omega))
        (hl.other _ (hcoins.apart j k (fin3_ne_of_lt (by omega)))) hl.code
  · refine ⟨?_, fun j hj => hb.2.1 j (by omega), fun h3 ha => ?_⟩
    · have h1 := hb.1
      rw [e0 _ (by omega)] at h1
      rw [e0 _ (by omega)]
      exact h1
    · have hk : k = 2 := Fin.ext (by omega)
      subst hk
      exact absurd hz ha
  · refine ⟨token20_coinBalOkAt hfork hdepth (hcoins.prec 2) rfl (by decide) (by decide)
      (by decide) (fun b hb => ⟨(hb.2.1 2 (le_refl _)).1, by rw [(hb.2.1 2 (le_refl _)).2]⟩)
      (fun b d hb hs hc => keep 2 b d hb hs hc), ?_,
      token20_coinBalOkAt hfork hdepth (hcoins.prec 2) rfl (by decide) (by decide) (by decide)
      (fun b hb => ⟨(hb.2.2 rfl ha).1, by rw [(hb.2.2 rfl ha).2]⟩)
      (fun b d hb hs hc => keep 3 b d hb hs hc)⟩
    refine token20_coinPullOkAt hfork hstatic hdepth (hcoins.prec 2) rfl (hcoins.pool 2)
      (le_refl _) (by decide) (by decide) (fun b hb => ⟨(hb.2.1 2 (le_refl _)).1, ?_⟩)
      (fun b d hb hl => ⟨?_, fun j hj => absurd j.isLt (by omega), fun _ _ => ⟨?_, ?_⟩⟩)
    · rw [(hb.2.1 2 (le_refl _)).2]; exact hfits 2 ha
    · have h1 := hb.1
      rw [e0 2 (by decide)] at h1
      rw [e0 3 (by decide)]
      exact c3At_keep' h1 (hl.other _ (Ne.symm (hcoins.tok 2))) hl.code
    · exact (hl.code _).trans (hb.2.1 2 (le_refl _)).1
    · rw [hl.stor, (hb.2.1 2 (le_refl _)).2]
  · refine c3crv_mintOkAt hfork hstatic hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, hc3.pool, by rw [hb.1.2, e0 3 (by decide)]; exact hmint⟩)
      (fun b d hb _ hs hc => ⟨⟨(hc _).trans hb.1.1, ?_⟩, fun j hj => absurd j.isLt (by omega),
        fun h3 => absurd h3 (by decide)⟩)
    rw [hs, hb.1.2, e0 3 (by decide), ite_eq_left (by decide)]

/-! ## `remove_liquidity_imbalance` -/

section Imbalance

variable (sevm : Sevm) (pre : Devm)

/-- `remove_liquidity_imbalance`'s world chain: 3Crv at its entry storage before the burn
(`W 0`) and at the burned storage after; before coin `k`'s push (`W (k + 1)`), coins
`k, …, 2` as at the entry. -/
def rliWorld (m : B256) (j : Nat) (b : Devm) : Prop :=
  C3At (tokOf sevm pre) (if 1 ≤ j then burnStor (Devm.getStor pre (tokOf sevm pre))
    sevm.caller.toB256 m else Devm.getStor pre (tokOf sevm pre)) b ∧
    ∀ i : Fin 3, j - 1 ≤ i.val → CoinPinned sevm pre i b

end Imbalance

/-- **`removeLiquidityImbalance_live`'s callee premises are satisfiable**: with `Token20` coins
whose ledgers cover the nonzero pushes and the deployed 3Crv accepting the burn of `m`, the world
chain `rliWorld` satisfies every callee premise at `U = 80000`, starting from the frame's
entry. -/
theorem removeLiquidityImbalance_premises_satisfiable {sevm : Sevm} {pre : Devm} {T m : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre)
    (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 m)
    (hfits : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → T20MoveFits (pre.getStor (coinOf sevm pre k))
      sevm.currentTarget sevm.caller (rliAmt sevm k.val)) :
    (∀ j, j ≤ 4 → WClosed sevm (rliWorld sevm pre m j)) ∧ rliWorld sevm pre m 0 pre ∧
      SupplyOkAt sevm (rliWorld sevm pre m 0) (rliWorld sevm pre m 0)
        ((pre.getStor sevm.currentTarget).get tokenSlot) T 80000 0x17c 0x1c0 ∧
      BurnOkAt sevm (rliWorld sevm pre m 0) (rliWorld sevm pre m 1)
        ((pre.getStor sevm.currentTarget).get tokenSlot) m 80000 0x85c 0x8e0 ∧
      (∀ k : Fin 3, rliAmt sevm k.val ≠ 0 →
        CoinPushOkAt sevm (rliWorld sevm pre m (k + 1)) (rliWorld sevm pre m (k + 2))
          ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) 80000 0xaa0
          0xb40) ∧
      (∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, rliWorld sevm pre m (k + 1) b →
        rliWorld sevm pre m (k + 2) b) := by
  have e1 : ∀ n, 1 ≤ n → (if 1 ≤ n then burnStor (Devm.getStor pre (tokOf sevm pre))
      sevm.caller.toB256 m else Devm.getStor pre (tokOf sevm pre)) =
      burnStor (Devm.getStor pre (tokOf sevm pre)) sevm.caller.toB256 m := fun n hn => ite_eq_left hn
  have e0 : (if 1 ≤ 0 then burnStor (Devm.getStor pre (tokOf sevm pre))
      sevm.caller.toB256 m else Devm.getStor pre (tokOf sevm pre)) =
      Devm.getStor pre (tokOf sevm pre) := ite_eq_right (by decide)
  refine ⟨fun k _ => WClosed.of_foreign fun b d hb hs hc => ⟨c3At_keep' hb.1 (hs _ hc3.pool) hc,
    fun j hj => coinPinned_keep (hb.2 j hj) (hs _ (hcoins.pool j)) hc⟩,
    ⟨⟨hc3.code, e0.symm⟩, fun j _ => ⟨hcoins.code j, rfl⟩⟩, ?_, ?_, fun k ha => ?_,
    fun k hz b hb => ⟨?_, fun j hj => hb.2 j (by omega)⟩⟩
  · exact c3crv_supplyOkAt hfork hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, by rw [hb.1.2, e0]; exact hc3.supply⟩)
      (fun b d hb hs hc => ⟨c3At_keep' hb.1 (hs _) hc,
        fun j hj => coinPinned_keep (hb.2 j hj) (hs _) hc⟩)
  · refine c3crv_burnOkAt hfork hstatic hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, hc3.pool, by rw [hb.1.2, e0]; exact hburn⟩)
      (fun b d hb ho hs hc => ⟨⟨(hc _).trans hb.1.1, ?_⟩,
        fun j hj => coinPinned_keep (hb.2 j (by omega)) (ho _ (hcoins.tok j)) hc⟩)
    rw [hs, hb.1.2, e0, e1 1 (le_refl _)]
  · refine token20_coinPushOkAt hfork hstatic hdepth (hcoins.prec k) rfl (hcoins.pool k)
      (le_refl _) (by decide) (by decide) (fun b hb => ⟨(hb.2 k (by omega)).1, ?_⟩)
      (fun b d hb hl => ⟨?_, fun j hj => ?_⟩)
    · rw [(hb.2 k (by omega)).2]; exact hfits k ha
    · have h1 := hb.1
      rw [e1 _ (by omega)] at h1
      rw [e1 _ (by omega)]
      exact c3At_keep' h1 (hl.other _ (Ne.symm (hcoins.tok k))) hl.code
    · exact coinPinned_keep (hb.2 j (by omega))
        (hl.other _ (hcoins.apart j k (fin3_ne_of_lt (by omega)))) hl.code
  · have h1 := hb.1
    rw [e1 _ (by omega)] at h1
    rw [e1 _ (by omega)]
    exact h1

/-! ## `remove_liquidity_one_coin` -/

section OneCoin

variable (sevm : Sevm) (pre : Devm)

/-- `remove_liquidity_one_coin`'s worlds before the burn and between the burn and the push: 3Crv
at the storage `σ` (its entry storage, resp. the burned one), coin `i` as at the entry. -/
def ocWorld (σ : Stor) (i : Fin 3) (b : Devm) : Prop :=
  C3At (tokOf sevm pre) σ b ∧ CoinPinned sevm pre i b

end OneCoin

/-- **`removeLiquidityOneCoin_live`'s callee premises are satisfiable**: with coin `i` running
`Token20` whose ledger covers the push of `v` and the deployed 3Crv accepting the burn of
`_token_amount`, the worlds `ocWorld` at 3Crv's entry storage, at its burned storage, and `True`
satisfy every callee premise at `U = 80000`, starting from the frame's entry. -/
theorem removeLiquidityOneCoin_premises_satisfiable {sevm : Sevm} {pre : Devm} {T v : B256}
    {i : Fin 3} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcode : pre.getCode (coinOf sevm pre i) = VyperNonreentrantDeployed.Token20.code)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp (coinOf sevm pre i))
    (hpool : coinOf sevm pre i ≠ sevm.currentTarget) (htok : coinOf sevm pre i ≠ tokOf sevm pre)
    (hburn : BurnFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256
      (ocAmt sevm))
    (hfits : T20MoveFits (pre.getStor (coinOf sevm pre i)) sevm.currentTarget sevm.caller v) :
    WClosed sevm (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i) ∧
      WClosed sevm (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre))
        sevm.caller.toB256 (ocAmt sevm)) i) ∧
      ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i pre ∧
      SupplyOkAt sevm (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i)
        (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i)
        ((pre.getStor sevm.currentTarget).get tokenSlot) T 80000 0x2bc 0x300 ∧
      BurnOkAt sevm (ocWorld sevm pre (Devm.getStor pre (tokOf sevm pre)) i)
        (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre)) sevm.caller.toB256
          (ocAmt sevm)) i)
        ((pre.getStor sevm.currentTarget).get tokenSlot) (ocAmt sevm) 80000 0x31c 0x3a0 ∧
      WClosed sevm (fun _ => True) ∧
      CoinPushOkAt sevm (ocWorld sevm pre (burnStor (Devm.getStor pre (tokOf sevm pre))
          sevm.caller.toB256 (ocAmt sevm)) i) (fun _ => True)
        ((pre.getStor sevm.currentTarget).get (coinSlot i)) v 80000 0x540 0x5e0 := by
  have hcl : ∀ σ, WClosed sevm (ocWorld sevm pre σ i) := fun _ =>
    WClosed.of_foreign fun b d hb hs hc =>
      ⟨c3At_keep' hb.1 (hs _ hc3.pool) hc, coinPinned_keep hb.2 (hs _ hpool) hc⟩
  refine ⟨hcl _, hcl _, ⟨⟨hc3.code, rfl⟩, ⟨hcode, rfl⟩⟩, ?_, ?_,
    WClosed.of_foreign fun _ _ _ _ _ => trivial, ?_⟩
  · exact c3crv_supplyOkAt hfork hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, by rw [hb.1.2]; exact hc3.supply⟩)
      (fun b d hb hs hc => ⟨c3At_keep' hb.1 (hs _) hc, coinPinned_keep hb.2 (hs _) hc⟩)
  · refine c3crv_burnOkAt hfork hstatic hdepth (precomp_false hc3.prec) (by decide) (by decide)
      (by decide) (fun b hb => ⟨hb.1.1, hc3.pool, by rw [hb.1.2]; exact hburn⟩)
      (fun b d hb ho hs hc => ⟨c3At_burn hb.1 hs hc, coinPinned_keep hb.2 (ho _ htok) hc⟩)
  · exact token20_coinPushOkAt hfork hstatic hdepth hprec rfl hpool (le_refl _) (by decide)
      (by decide) (fun b hb => ⟨hb.2.1, by rw [hb.2.2]; exact hfits⟩) (fun _ _ _ _ => trivial)

end Blanc.Composition.Curve3Pool3CrvInstance
