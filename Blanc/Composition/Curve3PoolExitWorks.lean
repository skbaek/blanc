import Blanc.Composition.Curve3PoolExitFits
import Blanc.Composition.Curve3PoolExitTx
import Blanc.Composition.Curve3PoolExitMoment
import Blanc.Composition.Curve3Pool3CrvCoinExactFloor

/-!
# `lp_exit`, from a moment of mainnet, under marked hypotheses

`exit_run`: at a `ColdEntry`, the frame commits with exactly the requested residual gas, ending at the canonical
final state. **Marked, not proved here:** `ExitMarked` (coverage, USDC at the moment, the hash class of the new `E`, the
fee's bound, the minter and address 4 at the cut) and `ExitCold` (the canonical chain's cost, refund and effect).
`lp_exit_of_marked` is the theorem those give.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (rlExactCost rlBurnBase rlBurnMem rlHeadMem3 rlAmt rlEnv Checkpoint RLExactCalls WClosed)
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins exitPushD exitPushN exit_pushesF rlFloorPremises_c3crv
  pinsFrom pinsFrom_entry pinsFrom_blind pinsFrom_wClosed pinsFrom_stable)
open Blanc.Composition.Curve3Pool3CrvExactAssembly (rlC3Calls rlC3W)
open Blanc.Composition.Curve3Pool3CrvHeadlines (c3With_wClosed)
open Blanc.Composition.Curve3Pool3CrvInstance (coinOf tokOf)

/-! ## The frame's run, ending at its canonical final state -/

/-- `remove_liquidity`'s calls with the real coins. -/
noncomputable abbrev exitCalls (msg : Msg) : RLExactCalls :=
  rlC3Calls (initSevm msg) (initDevm msg) (exitPushD (initSevm msg) ((initDevm msg).getStor msg.currentTarget))
    (exitPushN (initSevm msg) ((initDevm msg).getStor msg.currentTarget))

/-- The state after the burn, canonically. -/
noncomputable abbrev exitAfterBurn (msg : Msg) (T : B256) : Devm :=
  (exitCalls msg).burnNext (rlBurnBase (initSevm msg) (initDevm msg) T (exitCalls msg)) []
    (rlBurnMem (initSevm msg) (rlHeadMem3 (initSevm msg) (initDevm msg) T (exitCalls msg)))

/-- The frame's last state from the state after the burn: its event, then the lock's release. -/
noncomputable abbrev exitLast (msg : Msg) (d : Devm) (l : Log) : Devm :=
  afterSstore (initSevm msg) (d.addLog l) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])

/-- The canonical schedule ignores the frame's static initial gas. -/
theorem rlBurn_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (T : B256) (P : RLExactCalls) :
    rlBurnBase {sevm with gas := F} pre T P = rlBurnBase sevm pre T P ∧
      rlHeadMem3 {sevm with gas := F} pre T P = rlHeadMem3 sevm pre T P := by
  simp only [rlBurnBase, Curve3Pool.rlHead3, Curve3Pool.rlHead2, Curve3Pool.rlHead1, Curve3Pool.rlHead0,
    rlHeadMem3, Curve3Pool.rlHeadMem2, Curve3Pool.rlHeadMem1, Curve3Pool.rlHeadMem0, Curve3Pool.rlIterBase,
    Curve3Pool.rlIterMem, Curve3Pool.rlSupplyBase, Curve3Pool.rlSupplyMem, Curve3Pool.rlLoopMem0, Curve3Pool.rlPushNext,
    Curve3Pool.rlPushBase, Curve3Pool.rlPushMem, Curve3Pool.rlReplyLen, Curve3Pool.rlS2Base, Curve3Pool.rlS2MemOf,
    Curve3Pool.rlS1Base, Curve3Pool.rlS2Next, Curve3Pool.rlS2Mem, Curve3Pool.rlS2Mem2, Curve3Pool.rlS2Base1,
    Curve3Pool.rlV, Curve3Pool.rlB, rlAmt, afterSload_withStaticGas, afterSstore_withStaticGas,
    dataWord_withStaticGas, identityCallNext_withStaticGas, rawTailBaseNext_withStaticGas, and_self]

/-- `rx_rl_frame_floor` at message entry, keeping the frame's end. -/
theorem rl_msg_end {msg : Msg} {s : Curve3Pool.State} {o : Curve3Pool.Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat}
    (P : RLExactCalls) (hcode : (initSevm msg).code = Curve3Pool.code)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hlen : 4 ≤ (initSevm msg).data.length)
    (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = Curve3Pool.selRemoveLiquidity)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : Curve3Pool.step s (rlEnv (initSevm msg) T) (Curve3Pool.decodeCall (initSevm msg)) = some o)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (W k)) (hWb : W 0 (initDevm msg))
    (hP : Curve3Pool.RLFloorPremises (initSevm msg) (initDevm msg) T W U P)
    {R : Nat} (hR : 2201 ≤ R) (hG : R + rlExactCost (initSevm msg) (initDevm msg) T P < 2 ^ 256) :
    ∃ post, exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) = .ok post ∧
      post.gasLeft = R ∧ ∃ d l, Devm.EqModGas d (P.burnNext (rlBurnBase (initSevm msg) (initDevm msg) T P) []
          (rlBurnMem (initSevm msg) (rlHeadMem3 (initSevm msg) (initDevm msg) T P))) ∧
        ∃ S M G, post = St (afterSstore (initSevm msg) (d.addLog l) (Bytes.toB256 [255, 255, 255])
          (Bytes.toB256 [0])) S M G := by
  obtain ⟨hval, hT0, hmulw, hminw, hlew, hTa⟩ := Curve3Pool.removeLiquidity_walkChecks hlen hsel hck hstep
  obtain ⟨F, hF⟩ : ∃ F, F = R + rlExactCost (initSevm msg) (initDevm msg) T P := ⟨_, rfl⟩
  have hcost := Curve3Pool.rlExactCost_withStaticGas (initSevm msg) F (initDevm msg) T P
  obtain ⟨r, hr, D, rfl, hDg, ⟨d, l, hd, S, M, G, hD⟩, -⟩ := Curve3Pool.rx_rl_frame_floor
    (sevm := {initSevm msg with gas := F}) (pre := initDevm msg) (T := T) P hfork hstatic hdepth hlen hcd hsel
    (hid.withStaticGas F) hck.unlocked hval (fun k hk => (hWc k hk).withStaticGas F) hWb (hP.withStaticGas F)
    hmulw hT0 hminw hlew hTa hR (by rw [hcost]; omega)
  rw [hcost, ← hF] at hr
  obtain ⟨exD⟩ := Lift.lift_exactM (sevm := {initSevm msg with gas := F}) Curve3Pool.cert_checkM
    Curve3Pool.cert_jumpsOkM hcode hfork ⟨Curve3Pool.t_0000_c0, rfl, hr⟩
  rw [← hF]
  obtain ⟨e1, e2⟩ := rlBurn_withStaticGas (initSevm msg) F (initDevm msg) T P
  have hb : rlBurnMem {initSevm msg with gas := F} (rlHeadMem3 (initSevm msg) (initDevm msg) T P) =
      rlBurnMem (initSevm msg) (rlHeadMem3 (initSevm msg) (initDevm msg) T P) := by
    simp only [rlBurnMem, rlAmt, dataWord_withStaticGas]
  rw [e1, e2, hb] at hd
  exact ⟨D, Lift.exec_withGas_of_frame exD, hDg, d, l, hd, S, M, G, hD⟩

/-- **The frame's run at any residual `R ≥ 2201`, ending at its canonical final state.** -/
theorem exit_run {msg : Msg} {s : Curve3Pool.State} {o : Curve3Pool.Out} {T : B256}
    (hcode : (initSevm msg).code = Curve3Pool.code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : 2 ≤ (initSevm msg).depth)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = Curve3Pool.selRemoveLiquidity)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : Curve3Pool.step s (rlEnv (initSevm msg) T) (Curve3Pool.decodeCall (initSevm msg)) = some o)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hc3 : Blanc.Composition.Curve3Pool3CrvInstance.C3Entry (initSevm msg) (initDevm msg) T)
    (hC : RealCoins (initSevm msg) (initDevm msg))
    (hburn : Blanc.Composition.Curve3PoolCalleeLive.BurnFits
      (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (initSevm msg).currentTarget
      (initSevm msg).caller.toB256 (rlAmt (initSevm msg)))
    (hf0 : Lift.Dai.MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 0))
      (initSevm msg).currentTarget (initSevm msg).caller
      (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0 * rlAmt (initSevm msg) / T))
    (hf1 : Blanc.Composition.UsdcLive.MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 1))
      (initSevm msg).currentTarget (initSevm msg).caller
      (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1 * rlAmt (initSevm msg) / T))
    (hf2 : Lift.Usdt.XferFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2))
      (initSevm msg).currentTarget (initSevm msg).caller
      (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2 * rlAmt (initSevm msg) / T))
    {R : Nat} (hR : 2201 ≤ R) (hG : R + rlExactCost (initSevm msg) (initDevm msg) T (exitCalls msg) < 2 ^ 256) :
    ∃ post, exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (exitCalls msg)))) = .ok post ∧
      post.gasLeft = R ∧ ∃ d l, Devm.EqModGas d (exitAfterBurn msg T) ∧
        ∃ S M G, post = St (exitLast msg d l) S M G := by
  have hne : (initSevm msg).currentTarget ≠ tokOf (initSevm msg) (initDevm msg) := Ne.symm hc3.pool
  have hdep0 : (initSevm msg).depth ≠ 0 := by omega
  have hpush := exit_pushesF (c3 := tokOf (initSevm msg) (initDevm msg))
    (σ := Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (T := T)
    hfork hstatic hdepth hC hC.tok hf0 hf1 hf2
  have hP := rlFloorPremises_c3crv rfl hne hfork hstatic hdep0 hc3.prec hc3.supply hburn (pinsFrom_blind hC.tok)
    (fun k _ => pinsFrom_stable k) hpush
  have hWc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (rlC3W (tokOf (initSevm msg) (initDevm msg))
      (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
      (Blanc.Composition.Curve3PoolCalleeLive.burnStor (Devm.getStor (initDevm msg)
        (tokOf (initSevm msg) (initDevm msg))) (initSevm msg).caller.toB256 (rlAmt (initSevm msg)))
      (pinsFrom (initSevm msg) (initDevm msg)) k) := fun k hk => by
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl
    all_goals exact c3With_wClosed hne (pinsFrom_wClosed hC _)
  exact rl_msg_end (exitCalls msg) hcode hfork hstatic hdep0 hlen hcd hsel hck hstep hid hWc
    ⟨⟨hc3.code, rfl⟩, pinsFrom_entry 0⟩ hP hR hG

/-! ## The message, from the moment's facts -/

/-- **Marked: what the proof takes and this module does not prove.** -/
structure ExitMarked (w : State) (E : Adr) (a : Nat) : Prop where
  /-- MARKED, the Mac's `Moment.backed`: the pool's books are covered at the moment. -/
  covered : PoolBacked w
  /-- MARKED, the Mac's read at the cut: USDC's proxy, and V2_2 at its word. -/
  usdcCode : w.getCode usdc = Usdc.Proxy.code ∧ w.getCode (usdcImplOf w) = Usdc.Impl.code
  /-- MARKED, for the statement: the pool is not USDC's proxy admin. `proxy_notAdmin` needs a committed frame. -/
  notAdmin : pool ≠ ((w.getStor usdc).get Blanc.Composition.UsdcLive.pKA).toAdr
  /-- MARKED, for the statement: the hash class of the new `E`. -/
  apart : ExitApart w E
  /-- MARKED, for the statement: USDT's fee is at most the amount, which `sub` needs. -/
  feeLe : usdtFee w (share w a 2) ≤ share w a 2
  /-- MARKED, provable: 3Crv's minter at the cut (`supply_walk` over the window). -/
  minter : (w.getStor c3).get Curve3Crv.vyMinterSlot = pool.toB256
  /-- MARKED, provable: address 4's code at the cut (`codeAt_empty` over the window). -/
  id4 : w.getCode 4 = ByteArray.empty

/-- A message as a transaction's entry prepares it, beyond `Asked`. -/
structure ColdEntry (msg : Msg) (w : State) (E : Adr) (data : Bytes) : Prop where
  asked : Asked msg w E data
  /-- Address 4 is warm and a precompile, and its code is as in `w`. -/
  warm4 : (4 : Adr) ∈ msg.accessedAddresses
  code4 : msg.benv.state.getCode 4 = w.getCode 4
  gasFits : msg.gas < 2 ^ 256

theorem parties_not_precomp {f : Fork} (h : HistFork f) :
    ¬ (Fork.ruleSet f).isPrecomp pool ∧ ¬ (Fork.ruleSet f).isPrecomp Usdc.usdcImpl := by
  revert h
  cases f <;> decide +kernel

/-- **The cost, refund and effect of the canonical chain at a cold entry.** MARKED: the evaluation still to prove. -/
structure ExitCold (msg : Msg) (w : State) (E : Adr) (a : Nat) (T : B256) : Prop where
  cost : rlExactCost (initSevm msg) (initDevm msg) T (exitCalls msg) = exitFrameGas w E a
  last : ∀ d l S M G, Devm.EqModGas d (exitAfterBurn msg T) →
    (St (exitLast msg d l) S M G).error = none ∧
      (St (exitLast msg d l) S M G).refundCounter = (exitRefund w E a : Int) ∧
      ExitPaid w (St (exitLast msg d l) S M G).state E a

section Message

variable {w : State} {E : Adr} {a : Nat} {mins : Curve3Pool.V3} {msg : Msg}

/-- The storage and code a cold entry reads are the moment's, at the parties. -/
theorem ColdEntry.stor (e : ColdEntry msg w E (exitCalldata a mins)) {x : Adr} (hx : x ∈ parties w) :
    (initDevm msg).getStor x = w.getStor x ∧ (initDevm msg).getCode x = w.getCode x := by
  have h := (e.asked.entry.world x hx).1
  exact ⟨congrArg Acct.stor h, congrArg Acct.code h⟩

/-- **The message under the marked hypotheses.** `MsgDoes` with the gas bound its walks need, which `MsgDoes` does
not state. -/
theorem exit_message (mf : MomentFacts w) (mk : ExitMarked w E a) (e : ColdEntry msg w E (exitCalldata a mins))
    (hE : E ≠ 0) (req : ExitRequest w E a mins)
    (cold : ExitCold msg w E a ((w.getStor c3).get Curve3Crv.vySupplySlot))
    (R : Nat) (hR : callRoom ≤ R) (hG : R + exitFrameGas w E a < 2 ^ 256) :
    ∃ post, exec (initEvm (msg.withGas (R + exitFrameGas w E a))) = .ok post ∧ post.error = none ∧
      post.gasLeft = R ∧ post.refundCounter = (exitRefund w E a : Int) ∧ ExitPaid w post.state E a := by
  have ht : msg.currentTarget = pool := e.asked.entry.named.1
  have hcaller : msg.caller = E := e.asked.entry.named.2.1
  have hopen := e.asked.coinsOpen
  have hfork : CoveredFork (initSevm msg).benvStat.fork := e.asked.entry.plain.2.2.2
  have hH : HistFork (initSevm msg).benvStat.fork := hfork.histFork
  have hdata : (initSevm msg).data = exitCalldata a mins := e.asked.data
  have hmemP : pool ∈ parties w := by unfold parties; exact List.mem_cons_self
  have hmemC : c3 ∈ parties w := by simp only [parties, List.mem_cons, true_or, or_true]
  have hmemD : dai ∈ parties w := by simp only [parties, List.mem_cons, true_or, or_true]
  have hmemU : usdc ∈ parties w := by simp only [parties, List.mem_cons, true_or, or_true]
  have hmemT : usdt ∈ parties w := by simp only [parties, List.mem_cons, true_or, or_true]
  have hmemI : usdcImplOf w ∈ parties w := by simp only [parties, List.mem_cons, true_or, or_true]
  obtain ⟨sP, cP⟩ := e.stor hmemP
  obtain ⟨sC, cC⟩ := e.stor hmemC
  obtain ⟨sD, cD⟩ := e.stor hmemD
  obtain ⟨sU, cU⟩ := e.stor hmemU
  obtain ⟨sT, cT⟩ := e.stor hmemT
  obtain ⟨-, cI⟩ := e.stor hmemI
  obtain ⟨s, hck0, hsc, hst⟩ := mf.ck
  have hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s := by rw [ht, sP]; exact hck0
  have hcn : ∀ k : Fin 3, ((w.getStor pool).get (Curve3Pool.coinSlot k)).toAdr = coinAt k := by
    intro k
    have h : ((w.getStor pool).get (Curve3Pool.coinSlot k)).toAdr = Curve3Pool.adrOf (s.coins.get k) := by
      rw [Curve3Pool.adrOf, ← hck0.abs.coins k, toB256_toNat]
    rw [h, hsc]
    match k with
    | 0 => exact coin0_eq
    | 1 => exact coin1_eq
    | 2 => exact coin2_eq
  have htn : ((w.getStor pool).get Curve3Pool.tokenSlot).toAdr = c3 := by
    have h : ((w.getStor pool).get Curve3Pool.tokenSlot).toAdr = Curve3Pool.adrOf s.token := by
      rw [Curve3Pool.adrOf, ← hck0.abs.token, toB256_toNat]
    rw [h, hst]
    decide +kernel
  have hT0 : 0 < supply w := req.holds.2.2
  have hle : a ≤ supply w := req.holds.2.1
  have hla : a < 2 ^ 256 := Nat.lt_of_le_of_lt hle (word_lt _ _)
  obtain ⟨wa, w0, w1, w2⟩ := exit_words (e := initSevm msg) hdata
  have hamt : rlAmt (initSevm msg) = Nat.toB256 a := wa
  obtain ⟨T, hTdef⟩ : ∃ T, T = (w.getStor c3).get Curve3Crv.vySupplySlot := ⟨_, rfl⟩
  rw [← hTdef] at cold
  have hTn : T.toNat = supply w := by rw [hTdef]; rfl
  have hTne : T ≠ 0 := by
    intro h
    rw [h] at hTn
    have : (0 : B256).toNat = 0 := by decide
    omega
  have hV : ∀ k : Fin 3, Curve3Pool.balAt (w.getStor pool) k.val * Nat.toB256 a / T = Nat.toB256 (share w a k) := by
    intro k
    refine B256.toNat_inj _ _ ?_
    have hm : recorded w k * (Nat.toB256 a).toNat < 2 ^ 256 := by
      rw [B256.toNat_toB256_of_lt hla]; exact req.mulFits k
    show ((w.getStor pool).get (Curve3Pool.balanceSlot k) * Nat.toB256 a / T).toNat = _
    rw [Lift.rlOut_toNat hm hTne, share_word hT0 hle k, B256.toNat_toB256_of_lt hla, hTn]
    rfl
  -- the model accepts
  have hlen : (initSevm msg).data.length = 132 := exit_length hdata
  have hsel := exit_selector (e := initSevm msg) hdata
  have hval : (initSevm msg).value = 0 := e.asked.entry.plain.1
  have hmn : ∀ k, mins.get k < 2 ^ 256 := fun k => Nat.lt_of_le_of_lt (req.mins k) (share_lt hT0 hle k)
  have hmin : ∀ k, mins.get k ≤ s.balances.get k * a / T.toNat := fun k => by
    have := req.mins k
    rw [hTn, ← recorded_of_abstracts hck0.abs k]
    exact this
  have hmul : ∀ k, s.balances.get k * a < 2 ^ 256 := fun k => by
    rw [← recorded_of_abstracts hck0.abs k]; exact req.mulFits k
  obtain ⟨o, ho⟩ := removeLiquidity_accepts (s := s) (e := rlEnv (initSevm msg) T) (T := T.toNat) rfl
    (by omega) (by omega) hmul hmin (fun _ => rfl) rfl
  have hdec : Curve3Pool.decodeCall (initSevm msg) =
      .removeLiquidity a mins := by
    rw [Curve3Pool.decodeCall_at (k := 7) rfl hsel (by omega)]
    show Curve3Pool.Call.removeLiquidity (Curve3Pool.arg (initSevm msg) 0) (Curve3Pool.argV3 (initSevm msg) 1) = _
    have a0 : Curve3Pool.arg (initSevm msg) 0 = a := by
      show (Sevm.dataWord (initSevm msg) (32 * 0 + 4)).toNat = a
      rw [show (32 * 0 + 4 : B256) = 4 by decide, wa, B256.toNat_toB256_of_lt hla]
    have a1 : Curve3Pool.arg (initSevm msg) 1 = mins.v0 := by
      show (Sevm.dataWord (initSevm msg) (32 * 1 + 4)).toNat = _
      rw [show (32 * 1 + 4 : B256) = 36 by decide, w0]
      exact B256.toNat_toB256_of_lt (hmn 0)
    have a2 : Curve3Pool.arg (initSevm msg) (1 + 1) = mins.v1 := by
      show (Sevm.dataWord (initSevm msg) (32 * (1 + 1) + 4)).toNat = _
      rw [show (32 * (1 + 1) + 4 : B256) = 68 by decide, w1]
      exact B256.toNat_toB256_of_lt (hmn 1)
    have a3 : Curve3Pool.arg (initSevm msg) (1 + 2) = mins.v2 := by
      show (Sevm.dataWord (initSevm msg) (32 * (1 + 2) + 4)).toNat = _
      rw [show (32 * (1 + 2) + 4 : B256) = 100 by decide, w2]
      exact B256.toNat_toB256_of_lt (hmn 2)
    show Curve3Pool.Call.removeLiquidity _ (Curve3Pool.V3.mk _ _ _) = _
    rw [a0, a1, a2, a3]
  have hval0 : (rlEnv (initSevm msg) T).value = 0 := by
    show (initSevm msg).value.toNat = 0
    rw [hval]; rfl
  have hstep : Curve3Pool.step s (rlEnv (initSevm msg) T) (Curve3Pool.decodeCall (initSevm msg)) = some o := by
    rw [hdec]
    show (if (rlEnv (initSevm msg) T).value = 0 then
      Curve3Pool.removeLiquidity s (rlEnv (initSevm msg) T) a mins else none) = some o
    rw [ite_eq_left hval0]
    exact ho
  -- the coins and 3Crv
  have hprec := Curve3PoolJointRoot.parties_not_precompile hH
  have hprecP := parties_not_precomp hH
  have hw : (initSevm msg).currentTarget = pool := ht
  have hco : ∀ k, coinOf (initSevm msg) (initDevm msg) k = coinAt k := fun k => by
    show ((initDevm msg).getStor msg.currentTarget |>.get _).toAdr = _
    rw [ht, sP]; exact hcn k
  have hto : tokOf (initSevm msg) (initDevm msg) = c3 := by
    show ((initDevm msg).getStor msg.currentTarget |>.get _).toAdr = _
    rw [ht, sP]; exact htn
  have hKI : (initDevm msg).getStorVal usdc Blanc.Composition.UsdcLive.pKI = Usdc.usdcImpl.toB256 := by
    rw [getStorVal_eq_getStor, sU]
    exact hopen.usdcV22
  have himplC : (initDevm msg).getCode ((initDevm msg).getStorVal usdc Blanc.Composition.UsdcLive.pKI).toAdr =
      Usdc.Impl.code := by
    rw [hKI, toAdr_toB256]
    have hI : usdcImplOf w = Usdc.usdcImpl := by
      unfold usdcImplOf
      rw [show (w.getStor usdc).get Usdc.implSlot = Usdc.usdcImpl.toB256 from hopen.usdcV22, toAdr_toB256]
    rw [← hI, cI]
    exact mk.usdcCode.2
  have hC : RealCoins (initSevm msg) (initDevm msg) :=
    { dai := by rw [hco 0]; show (initDevm msg).getCode dai = _; rw [cD]; exact mf.daiCode
      usdc := by rw [hco 1]; show (initDevm msg).getCode usdc = _; rw [cU]; exact mk.usdcCode.1
      impl := by
        rw [hco 1]
        refine ⟨getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel), himplC, ?_, ?_⟩
        · show (initSevm msg).benvStat.rules.isPrecomp
            ((initDevm msg).getStorVal usdc Blanc.Composition.UsdcLive.pKI).toAdr = _
          rw [hKI, toAdr_toB256]
          exact Blanc.Composition.Curve3Pool3CrvHeadlines.precomp_false hprecP.2
        · rw [hw]
          show pool ≠ ((initDevm msg).getStorVal usdc Blanc.Composition.UsdcLive.pKA).toAdr
          rw [getStorVal_eq_getStor, sU]
          exact mk.notAdmin
      usdt := by rw [hco 2]; show (initDevm msg).getCode usdt = _; rw [cT]; exact mf.usdtCode
      live := by rw [hco 2]; show Lift.Usdt.NotDeprecated ((initDevm msg).getStor usdt); rw [sT]; exact hopen.usdtLive
      prec := fun k => by
        rw [hco k]
        have := hprec.1 k
        match k with
        | 0 => rw [coin0_eq] at this; exact this
        | 1 => rw [coin1_eq] at this; exact this
        | 2 => rw [coin2_eq] at this; exact this
      pool := fun k => by rw [hco k, hw]; match k with
        | 0 => decide
        | 1 => decide
        | 2 => decide
      tok := fun k => by rw [hco k, hto]; match k with
        | 0 => decide
        | 1 => decide
        | 2 => decide
      apart := fun j k hjk => by
        rw [hco j, hco k]
        match j, k with
        | 0, 0 => exact absurd rfl hjk
        | 0, 1 => decide
        | 0, 2 => decide
        | 1, 0 => decide
        | 1, 1 => exact absurd rfl hjk
        | 1, 2 => decide
        | 2, 0 => decide
        | 2, 1 => decide
        | 2, 2 => exact absurd rfl hjk }
  have hc3 : Blanc.Composition.Curve3Pool3CrvInstance.C3Entry (initSevm msg) (initDevm msg) T :=
    { code := by rw [hto, cC]; exact mf.c3Code
      supply := by rw [hto, sC, hTdef]
      pool := by rw [hto, hw]; decide
      prec := by
        rw [hto]
        have := hprec.2
        rwa [show Curve3Pool.adrOf Curve3Pool.Creation.tokenN = c3 by decide +kernel] at this }
  have hcode : (initSevm msg).code = Curve3Pool.code := by
    show msg.code = _
    rw [e.asked.entry.named.2.2]; exact mf.poolCode
  have hid : IdReady (initSevm msg) (initDevm msg) :=
    ⟨by
      show getDelegatedCodeAddress (msg.benv.state.getCode 4) = none
      rw [e.code4, mk.id4]
      exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide), e.warm4,
      decide_eq_true (Curve3Pool.pool_four_mem_precompilesH hH), hfork⟩
  have hb : ∀ k : Fin 3, Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) k.val *
      rlAmt (initSevm msg) / T = Nat.toB256 (share w a k) := fun k => by
    rw [hw, sP, hamt]; exact hV k
  have hpc : ∀ k, recorded w k ≤ coinHeld w pool k := mk.covered
  have hE0 : E ≠ 0 := hE
  have hcall : (initSevm msg).caller = E := hcaller
  have hRm : 2201 ≤ R := hR
  obtain ⟨post, hex, hg, d, l, hd, S, M, G, rfl⟩ := exit_run (msg := msg) (T := T) (R := R) hcode hfork
    e.asked.entry.plain.2.1 (by have : (2 : Nat) ≤ msg.depth := e.asked.entry.plain.2.2.1; exact this)
    (by omega) (by omega) hsel hck hstep hid hc3 hC
    (by rw [hto, sC, hw, hcall, hamt]; exact burn_fits mk.minter hE0 mk.apart req.holds.1 req.holds.2.1)
    (by have := hb 0; rw [show (0 : Fin 3).val = 0 from rfl] at this; rw [this, hco 0, hw, hcall]
        show Lift.Dai.MoveFits ((initDevm msg).getStor dai) _ _ _
        rw [sD]; exact dai_fits (hpc 0) hT0 hle mk.apart (req.creditFits 0))
    (by have := hb 1; rw [show (1 : Fin 3).val = 1 from rfl] at this; rw [this, hco 1, hw, hcall]
        show Blanc.Composition.UsdcLive.MoveFits ((initDevm msg).getStor usdc) _ _ _
        rw [sU]; exact usdc_fits hopen hE0 (hpc 1) hT0 hle mk.apart (req.creditFits 1))
    (by have := hb 2; rw [show (2 : Fin 3).val = 2 from rfl] at this; rw [this, hco 2, hw, hcall]
        show Lift.Usdt.XferFits ((initDevm msg).getStor usdt) _ _ _
        rw [sT]; exact usdt_fits hopen (hpc 2) hT0 hle mk.apart (req.creditFits 2) req.feeFits mk.feeLe)
    hRm (by rw [cold.cost]; exact hG)
  rw [cold.cost] at hex
  obtain ⟨herr, hrf, hpaid⟩ := cold.last d l S M G hd
  exact ⟨_, hex, herr, hg, hrf, hpaid⟩

end Message

end Blanc.Composition.Curve3PoolPublic
