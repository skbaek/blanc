import Blanc.Composition.Curve3PoolExitCold
import Blanc.Composition.Curve3PoolBacked

/-!
# `lp_exit`: the message and the transaction

`exit_message`: the frame's run from the moment's facts, its cost and effect from `ExitFrame.cold`. `Moment.id4` and
`Moment.minter`: address 4 and 3Crv's minter at the cut. `lp_exit_holds` and `lp_exit_message_holds` close the two statements.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (rlExactCost rlBurnBase rlBurnMem rlHeadMem3 rlAmt rlEnv Checkpoint RLExactCalls WClosed)
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins exitPushD exitPushN exit_pushesF rlFloorPremises_c3crv
  pinsFrom pinsFrom_entry pinsFrom_blind pinsFrom_wClosed pinsFrom_stable)
open Blanc.Composition.Curve3Pool3CrvExactAssembly (rlC3Calls rlC3W)
open Blanc.Composition.Curve3Pool3CrvHeadlines (c3With_wClosed)
open Blanc.Composition.Curve3Pool3CrvInstance (coinOf tokOf)

section Message

variable {w : State} {E : Adr} {a : Nat} {mins : Curve3Pool.V3} {msg : Msg}

/-- The storage and code a cold entry reads are the moment's, at the parties. -/
theorem ColdEntry.stor (e : ColdEntry msg w E (exitCalldata a mins)) {x : Adr} (hx : x ∈ parties w) :
    (initDevm msg).getStor x = w.getStor x ∧ (initDevm msg).getCode x = w.getCode x := by
  have h := (e.entry.world x hx).1
  exact ⟨congrArg Acct.stor h, congrArg Acct.code h⟩

/-- **The message under the marked hypotheses.** `MsgDoes` with the gas bound its walks need, which `MsgDoes` does
not state. -/
theorem exit_message (mf : MomentFacts w) (mk : ExitMarked w) (e : ColdEntry msg w E (exitCalldata a mins))
    (req : ExitRequest w E a mins) (R : Nat) (hR : callRoom ≤ R) (hG : R + exitFrameGas w E a < 2 ^ 256) :
    ∃ post, exec (initEvm (msg.withGas (R + exitFrameGas w E a))) = .ok post ∧ post.error = none ∧
      post.gasLeft = R ∧ post.refundCounter = (exitRefund w E a : Int) ∧ post.accountsToDelete.toList = [] ∧
      ExitPaid w post.state E a := by
  have ht : msg.currentTarget = pool := e.entry.named.1
  have hcaller : msg.caller = E := e.entry.named.2.1
  have hopen := e.coinsOpen
  have hE : E ≠ 0 := e.nonzero
  have hfork : CoveredFork (initSevm msg).benvStat.fork := e.entry.plain.2.2.2
  have hH : HistFork (initSevm msg).benvStat.fork := hfork.histFork
  have hdata : (initSevm msg).data = exitCalldata a mins := e.data
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
  have hval : (initSevm msg).value = 0 := e.entry.plain.1
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
    rw [← hI, cI, hI]
    exact hopen.usdcImplCode
  have hC : RealCoins (initSevm msg) (initDevm msg) :=
    { dai := by rw [hco 0]; show (initDevm msg).getCode dai = _; rw [cD]; exact mf.daiCode
      usdc := by rw [hco 1]; show (initDevm msg).getCode usdc = _; rw [cU]; exact mk.usdcProxy
      impl := by
        rw [hco 1]
        refine ⟨getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel), himplC, ?_, ?_⟩
        · show (initSevm msg).benvStat.rules.isPrecomp
            ((initDevm msg).getStorVal usdc Blanc.Composition.UsdcLive.pKI).toAdr = _
          rw [hKI, toAdr_toB256]
          exact Blanc.Composition.Curve3Pool3CrvHeadlines.precomp_false hprecP.2.1
        · rw [hw]
          show pool ≠ ((initDevm msg).getStorVal usdc Blanc.Composition.UsdcLive.pKA).toAdr
          rw [getStorVal_eq_getStor, sU]
          rw [show Blanc.Composition.UsdcLive.pKA = Usdc.adminSlot by decide +kernel]
          exact hopen.usdcAdmin
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
    rw [e.entry.named.2.2]; exact mf.poolCode
  have hid : IdReady (initSevm msg) (initDevm msg) :=
    ⟨by
      show getDelegatedCodeAddress (msg.benv.state.getCode 4) = none
      rw [e.entry.identity.2, mk.id4]
      exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide), e.entry.identity.1,
      decide_eq_true (Curve3Pool.pool_four_mem_precompilesH hH), hfork⟩
  have hb : ∀ k : Fin 3, Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) k.val *
      rlAmt (initSevm msg) / T = Nat.toB256 (share w a k) := fun k => by
    rw [hw, sP, hamt]; exact hV k
  have hpc : ∀ k, recorded w k ≤ coinHeld w pool k := mk.covered
  have hE0 : E ≠ 0 := hE
  have hcall : (initSevm msg).caller = E := hcaller
  have hRm : 2201 ≤ R := hR
  have hTl : Curve3Pool.lockSlot = lockW := by decide
  obtain ⟨_, _, _, _, _, _, _, win0⟩ := exit_run (msg := msg) (T := T) (R := 2201) hcode hfork
    e.entry.plain.2.1 (by have : (2 : Nat) ≤ msg.depth := e.entry.plain.2.2.1; exact this)
    (by omega) (by omega) hsel hck hstep hid hc3 hC
    (by rw [hto, sC, hw, hcall, hamt]; exact burn_fits mk.minter hE0 req.apart req.holds.1 req.holds.2.1)
    (by have := hb 0; rw [show (0 : Fin 3).val = 0 from rfl] at this; rw [this, hco 0, hw, hcall]
        show Lift.Dai.MoveFits ((initDevm msg).getStor dai) _ _ _
        rw [sD]; exact dai_fits (hpc 0) hT0 hle req.apart (req.creditFits 0))
    (by have := hb 1; rw [show (1 : Fin 3).val = 1 from rfl] at this; rw [this, hco 1, hw, hcall]
        show Blanc.Composition.UsdcLive.MoveFits ((initDevm msg).getStor usdc) _ _ _
        rw [sU]; exact usdc_fits hopen hE0 (hpc 1) hT0 hle req.apart (req.creditFits 1))
    (by have := hb 2; rw [show (2 : Fin 3).val = 2 from rfl] at this; rw [this, hco 2, hw, hcall]
        show Lift.Usdt.XferFits ((initDevm msg).getStor usdt) _ _ _
        rw [sT]; exact usdt_fits hopen (hpc 2) hT0 hle req.apart (req.creditFits 2) req.feeFits)
    (le_refl _) (by have := exit_cost_lt (msg := msg) (T := T); omega)

  have frame : ExitFrame msg w E a T :=
    { fork := hfork
      static := e.entry.plain.2.1
      target := ht
      caller := hcaller
      keysCold := fun k hk => by
        have h0 : (initDevm msg).accessedStorageKeys.isEmpty = true := e.entry.cold.1
        exact absurd (Std.HashSet.isEmpty_eq_false_iff_exists_mem.2 ⟨k, hk⟩) (by simpa only [Bool.not_eq_false] using h0)
      clean := ⟨e.entry.fresh.1, e.entry.fresh.2, rfl⟩
      stor := fun x hx => by
        have hm : x ∈ parties w := by
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [parties, List.mem_cons, true_or, or_true]
        have h := e.entry.world x hm
        exact ⟨congrArg Acct.stor h.1, congrArg Acct.stor h.2⟩
      warm := fun x hx => by
        have hI : usdcImplOf w = Usdc.usdcImpl := by
          unfold usdcImplOf
          rw [show (w.getStor usdc).get Usdc.implSlot = Usdc.usdcImpl.toB256 from hopen.usdcV22, toAdr_toB256]
        refine e.entry.cold.2 x ?_
        simp only [parties, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false, hI]
        exact hx
      coins := fun k => hco k
      token := hto
      lock := by rw [hw, sP, ← hTl, ← sP, ← hw]; exact hck.unlocked
      amount := hamt
      sharesW := hb
      supplyW := hTdef.symm
      apart := req.apart
      open' := hopen
      backed := mk.covered
      holds := req.holds
      fits := req.creditFits
      feeFits := req.feeFits
      minter := mk.minter }
  have cold := frame.cold hE win0
  obtain ⟨post, hex, hg, d, l, hd, ⟨S, M, G, rfl⟩, win⟩ := exit_run (msg := msg) (T := T) (R := R) hcode hfork
    e.entry.plain.2.1 (by have : (2 : Nat) ≤ msg.depth := e.entry.plain.2.2.1; exact this)
    (by omega) (by omega) hsel hck hstep hid hc3 hC
    (by rw [hto, sC, hw, hcall, hamt]; exact burn_fits mk.minter hE0 req.apart req.holds.1 req.holds.2.1)
    (by have := hb 0; rw [show (0 : Fin 3).val = 0 from rfl] at this; rw [this, hco 0, hw, hcall]
        show Lift.Dai.MoveFits ((initDevm msg).getStor dai) _ _ _
        rw [sD]; exact dai_fits (hpc 0) hT0 hle req.apart (req.creditFits 0))
    (by have := hb 1; rw [show (1 : Fin 3).val = 1 from rfl] at this; rw [this, hco 1, hw, hcall]
        show Blanc.Composition.UsdcLive.MoveFits ((initDevm msg).getStor usdc) _ _ _
        rw [sU]; exact usdc_fits hopen hE0 (hpc 1) hT0 hle req.apart (req.creditFits 1))
    (by have := hb 2; rw [show (2 : Fin 3).val = 2 from rfl] at this; rw [this, hco 2, hw, hcall]
        show Lift.Usdt.XferFits ((initDevm msg).getStor usdt) _ _ _
        rw [sT]; exact usdt_fits hopen (hpc 2) hT0 hle req.apart (req.creditFits 2) req.feeFits)
    hRm (by rw [cold.cost]; exact hG)
  rw [cold.cost] at hex
  obtain ⟨herr, hrf, hdel, hpaid⟩ := cold.last d l S M G hd
  exact ⟨_, hex, herr, hg, hrf, hdel, hpaid⟩

end Message

/-! ## The transaction -/

/-! ## Address 4 at the cut -/

/-- **A transaction cut of a block keeps an empty address empty.** -/
theorem cut_code_empty {cfg : ChainConfig} {pre post : BlockChain} (block : ConfiguredBlockTraceIn HistFork cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) {a : Adr}
    (hdis : block.fork.ruleSet.delegationEnabled = false ∨
      ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ block.rawFrames, root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (hempty : pre.state.getCode a = ByteArray.empty) :
    cut.afterBenv.state.getCode a = ByteArray.empty := by
  have hsg := BodyStageCapabilities.historical.stateGas_none block.forkIn
  have avoidBeacon : ∀ root ∈ block.bodyTrace.beacon.rawFrames, root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inl member)))
  have avoidHistory : ∀ root ∈ block.bodyTrace.history.rawFrames, root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inr member)))
  have avoidTx : ∀ root ∈ block.bodyTrace.transactions.rawFrames, root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inr member))
  obtain ⟨hbeacon, -⟩ := block.bodyTrace.beacon.codeAt_empty_noStateGas hsg hempty avoidBeacon
  obtain ⟨hhistory, -⟩ := block.bodyTrace.history.codeAt_empty_noStateGas hsg hbeacon avoidHistory
  obtain ⟨-, hb⟩ := cut.before.codeAt_empty_noStateGas hsg
    (by
      rcases hdis with h | h
      · exact Or.inl h
      · exact Or.inr fun p hp => h p (List.mem_of_mem_take hp))
    (fun root member => avoidTx root (by rw [cut.rawFrames_eq]; simp only [List.mem_append]; exact Or.inl (Or.inl member)))
    hhistory
  have hst := cut.before.stat_eq
  have hmem : (cut.index, cut.tx) ∈ block.bodyTrace.decodedTxs.putIndex :=
    List.mem_of_mem_drop (by rw [cut.at_eq]; exact List.mem_cons_self)
  obtain ⟨-, hh⟩ := cut.head.codeAt_empty_noStateGas (by rw [hst]; exact hsg)
    (by
      rcases hdis with h | h
      · exact Or.inl (by rw [hst]; exact h)
      · exact Or.inr (h _ hmem))
    (fun root member => avoidTx root (by rw [cut.rawFrames_eq]; simp only [List.mem_append]; exact Or.inl (Or.inr member)))
    hb
  exact hh

/-- **Address 4 holds no code at a moment of mainnet.** -/
theorem Moment.id4 {d : Deployment} (m : Moment d) (A : Assumes d m.through) : m.world.getCode 4 = ByteArray.empty := by
  have hauth : (d.sinceC3Block m.through).PragueNoAuthorityAt 4 := A.keys.idNoAuthority
  have hfr := A.hashes.noCreateAt4
  have hE : (d.sinceC3Block m.through) = (d.sinceC3Block m.history).step m.block := rfl
  rw [hE] at hauth hfr
  obtain ⟨-, hpre⟩ := (d.sinceC3Block m.history).codeAt_empty_pragueNoAuthority BodyStageCapabilities.historical hauth.1
    (fun root member => hfr root (by
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
      exact Or.inl member)) A.code.idEmpty
  refine cut_code_empty m.block m.cut ?_ (fun root member => hfr root (by
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
      exact Or.inr member)) hpre
  by_cases hp : PrePrague m.block.fork
  · exact Or.inl (m.block.forkIn.delegationDisabled_of_prePrague hp)
  · exact Or.inr (hauth.2 hp)

/-! ## 3Crv's minter at the cut -/

/-- **The pool stays 3Crv's minter at a moment of mainnet.** -/
theorem Moment.minter {d : Deployment} (m : Moment d) (A : Assumes d m.through) :
    (m.world.getStor c3).get Curve3Crv.vyMinterSlot = pool.toB256 := by
  obtain ⟨hpool, hc3, invs₀, ps, cs, -, -, -, run₀, -, -, joint⟩ :=
    Curve3PoolJointRoot.joint_root_replay (Deployment.toJoint d A.facts)
  obtain ⟨hcoins, htoken⟩ := run₀.coins_token
  have envAt : Curve3Pool.PoolMidEnv (d.sinceC3Block m.through) ((d.sinceMinter m.history).step m.block)
      pool ps.coins ps.token := by
    rw [hcoins, htoken]
    exact A.env
  obtain ⟨-, invs, obs, auth, entries, s, run, -, -, h1, h2⟩ :=
    Curve3Pool.pool_window_history (d.sinceMinter m.history) m.block m.cut hpool joint.poolCk envAt
  have W := Blanc.Composition.Curve3PoolSupply.mid_walkEnv ((d.sinceMinter m.history).step m.block) hpool hc3 joint A.fresh envAt (by decide)
  have split : ((d.sinceMinter m.history).step m.block).settledFrames =
      [] ++ ((d.sinceMinter m.history).settledFrames ++ m.block.settledThroughCut m.cut) ++
        (MidHistoryTraceIn.tail m.block m.cut).settledFrames := by
    change (d.sinceMinter m.history).settledFrames ++ m.block.settledFrames = _
    rw [ConfiguredBlockTraceIn.settledFrames_throughCut m.block m.cut]
    simp only [List.nil_append, List.append_assoc]
  have closed : TargetClosed pool ((d.sinceMinter m.history).settledFrames ++ m.block.settledThroughCut m.cut) := by
    unfold ConfiguredBlockTraceIn.settledThroughCut
    have piece : ∀ {fs roots : List Exec.Frame}, fs = roots.flatMap (fun R => Exec.committedFrames R.run) →
        TargetClosed pool fs := fun h => Curve3PoolSupply.targetClosed_of_forest h
    exact (piece (d.sinceMinter m.history).settledFrames_eq).append
      (((((piece m.block.bodyTrace.beacon.settledFrames_eq).append (piece m.block.bodyTrace.history.settledFrames_eq)).append
        (piece m.cut.before.settledFrames_eq)).append (piece m.cut.head.settledFrames_eq)))
  obtain ⟨Y, hY, hYm, -⟩ := Curve3PoolSupply.supply_walk W invs (pre := []) run entries auth obs split (TargetClosed.nil pool)
    (by rw [List.nil_append]; exact closed) rfl joint.tokenIs rfl joint.minterIs
  obtain ⟨-, s', runS, inv⟩ := Curve3Crv.c3crv_window_framesHist (d.sinceMinter m.history) m.block m.cut hc3 joint.c3 A.fresh
  have hview := Curve3PoolSupply.viewObs_eq_committed (ca := Curve3Crv.Creation.tokenAddress)
    (frames := (d.sinceMinter m.history).settledFrames ++ m.block.settledThroughCut m.cut) (fun f hf => W.ready f (by
    rw [split]
    simp only [List.nil_append, List.mem_append]
    exact Or.inl (List.mem_append.1 hf)))
  rw [List.nil_append] at hY
  rw [hview] at hY
  have hs : Y = s' := Option.some.inj (hY.symm.trans runS.runInvocations_eq)
  subst hs
  have := inv.minter
  rw [hYm] at this
  exact this

/-- The observers read only the five contracts. -/
theorem ExitPaid.congr {w w₁ w₂ : State} {E : Adr} {a : Nat} (h : ExitPaid w w₁ E a)
    (hs : ∀ x, x = pool ∨ x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt → w₂.getStor x = w₁.getStor x) :
    ExitPaid w w₂ E a := by
  have hp := hs pool (by simp only [true_or])
  have hc := hs c3 (by simp only [true_or, or_true])
  have hd := hs dai (by simp only [true_or, or_true])
  have hu := hs usdc (by simp only [true_or, or_true])
  have ht := hs usdt (by simp only [or_true])
  have hcoin : ∀ x k, coinHeld w₂ x k = coinHeld w₁ x k := by
    intro x k
    unfold coinHeld UsdcPacked word
    rw [hu]
    match k with
    | 0 => simp only [coinAt, hd]
    | 1 => simp only [coinAt, hu]
    | 2 => simp only [coinAt, ht]
  refine ⟨?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · have := h.burned
    unfold supply shares word at this ⊢
    rwa [hc]
  · have := h.books k
    unfold recorded word at this ⊢
    rwa [hp]
  · rw [hcoin]; exact h.coins k
  · rw [hcoin]; exact h.paid k

/-- **`lp_exit`.** -/
theorem lp_exit_holds : lp_exit := by
  intro d m A tx E a mins hdata adm hopen req
  obtain ⟨prio, maxFee, form, ready⟩ := adm.form
  have mf := m.facts A
  have mk : ExitMarked m.world :=
    { covered := m.backed A
      usdcProxy := Usdc.usdc_code_at_cut (d.sincePool m.history) m.block m.cut BodyStageCapabilities.historical A.usdcCode
        A.circle.usdcCertified
      minter := m.minter A
      id4 := m.id4 A }
  have hw : m.benv.state = m.world := rfl
  have hE0 : E ≠ 0 := ready.named.1
  have hrec : tx.type.receiver? = some pool := by rw [form.type]; rfl
  have hnoE : ∀ x, x = pool ∨ x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt → E ≠ x := by
    intro x hx hEx
    have hz := ready.noCode
    rw [hEx, hw] at hz
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [mf.poolCode] at hz; exact absurd hz (by decide +kernel)
    · rw [mf.c3Code] at hz; exact absurd hz (by decide +kernel)
    · rw [mf.daiCode] at hz; exact absurd hz (by decide +kernel)
    · rw [mk.usdcProxy] at hz; exact absurd hz (by decide +kernel)
    · rw [mf.usdtCode] at hz; exact absurd hz (by decide +kernel)
  have hstatFork := adm.fork
  have hpn := parties_not_precomp hstatFork.histFork
  obtain ⟨debit, post, bout', hq, process, cum⟩ := tx_of_frame (r := exitRefund m.world E a) (index := m.nextIndex)
    (Q := fun _ p => p.accountsToDelete.toList = [] ∧ ExitPaid m.world p.state E a)
    adm.fork form ready adm.room
    (by rw [hdata]; exact exitCalldata_length)
    (by unfold exitFrameGas; omega)
    (by rw [hw, mf.poolCode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel))
    (by
      have h := hpn.1
      show (Fork.ruleSet m.benv.stat.fork).isPrecomp pool = false
      exact Blanc.Composition.Curve3Pool3CrvHeadlines.precomp_false h)
    (by
      intro debit msg after hd hp he
      obtain ⟨hm, ha⟩ := tx_message (index := m.nextIndex) hrec form.value hp he
      subst hm
      subst ha
      obtain ⟨-, hdeb⟩ := State.of_subBal hd
      have hget : ∀ x, E ≠ x → debit.get x = m.world.get x := by
        intro x hx
        have hin : (m.benv.state.incrNonce E).get x = m.benv.state.get x := by
          unfold State.incrNonce
          exact State.setAccount_get_ne _ hx _
        rw [hdeb, State.setBal_get_ne hx, hin]
        rfl
      have hI : usdcImplOf m.world = Usdc.usdcImpl := by
        unfold usdcImplOf
        rw [show (m.world.getStor usdc).get Usdc.implSlot = Usdc.usdcImpl.toB256 from hopen.usdcV22, toAdr_toB256]
      have hEp : ∀ x ∈ parties m.world, E ≠ x := by
        intro x hx
        simp only [parties, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hnoE _ (by simp only [true_or])
        · exact hnoE _ (by simp only [true_or, or_true])
        · exact hnoE _ (by simp only [true_or, or_true])
        · exact hnoE _ (by simp only [true_or, or_true])
        · exact hnoE _ (by simp only [or_true])
        · intro hEx
          have hz := ready.noCode
          rw [hEx, hw, hI, hopen.usdcImplCode] at hz
          exact absurd hz (by decide +kernel)
      have hE4 : E ≠ 4 := by
        intro h4
        have h1 := ready.named.2
        rw [h4] at h1
        have h2 : m.benv.stat.rules.isPrecomp 4 := hpn.2.2.1
        rw [h1] at h2
        exact absurd h2 (by decide)
      have hl : tx.accessList = [] := by simp only [Tx.accessList, TxType.accessList, form.type]
      obtain ⟨M, hM⟩ : ∃ M, M = (callMessage { m.benv.beginTransaction with state := debit }
          (transactionTenv m.benv.beginTransaction tx m.nextIndex E
            (min prio (maxFee - m.benv.stat.baseFeePerGas) + m.benv.stat.baseFeePerGas)
            (callIntrinsic tx.data) []) tx pool) := ⟨_, rfl⟩
      have hTail : ∀ x ∈ (parties m.world).tail, x ∉ M.accessedAddresses := by
        intro x hx hmem
        have hx' : x = c3 ∨ x = dai ∨ x = usdc ∨ x = usdt ∨ x = Usdc.usdcImpl := by
          simpa only [parties, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false, hI] using hx
        rw [hM] at hmem
        rcases tx_addr_mem form.type hmem with h | h | h | h
        · apply adm.block.2
          rw [← h]
          exact List.mem_of_mem_tail hx
        · rcases hx' with rfl | rfl | rfl | rfl | rfl
          · exact hpn.2.2.2.1 h
          · exact hpn.2.2.2.2.1 h
          · exact hpn.2.2.2.2.2.1 h
          · exact hpn.2.2.2.2.2.2.1 h
          · exact hpn.2.2.2.2.2.2.2 h
        · exact hEp x (List.mem_of_mem_tail hx) h.symm
        · rcases hx' with rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide +kernel)
      have ce : ColdEntry M m.world E (exitCalldata a mins) :=
        { entry :=
            { named := ⟨by rw [hM]; rfl, by rw [hM]; rfl, by
                rw [hM]
                exact congrArg Acct.code (hget pool (hEp pool List.mem_cons_self))⟩
              plain := ⟨by rw [hM]; show tx.value.toB256 = 0; rw [form.value]; decide, by rw [hM]; rfl,
                by rw [hM]; show (2 : Nat) ≤ 1024; decide, by rw [hM]; exact adm.fork⟩
              cold := ⟨by
                  rw [hM]
                  show (Std.HashSet.ofList ((tx.accessList.map _).flatten)).isEmpty = true
                  rw [hl]
                  rfl, hTail⟩
              world := fun x hx => ⟨by rw [hM]; exact hget x (hEp x hx), by rw [hM]; rfl⟩
              identity := ⟨by
                  rw [hM]
                  exact tx_addr_precomp (Curve3Pool.pool_four_mem_precompilesH hstatFork.histFork),
                by rw [hM]; exact congrArg Acct.code (hget 4 hE4)⟩
              fresh := ⟨fun x => by
                  rw [hM]
                  exact m.block.txSplit_notCreated m.cut x, fun x => by rw [hM]; exact Std.HashSet.not_mem_emptyWithCapacity⟩ }
          data := by rw [hM]; exact hdata
          coinsOpen := hopen
          nonzero := hE0 }
      have hFd : M.gas = tx.gas - callIntrinsic tx.data := by rw [hM]; rfl
      have hneed := adm.room.enough
      have hlim : exitLimit m.world tx.data E a = callIntrinsic tx.data + exitFrameGas m.world E a + callRoom := rfl
      rw [hlim] at hneed
      have hsum : tx.gas - (callIntrinsic tx.data + exitFrameGas m.world E a) + exitFrameGas m.world E a = M.gas := by
        rw [hFd]; omega
      have hcap := adm.room.cap
      obtain ⟨post, hx, herr, hg, hrf, hdel, hpaid⟩ := exit_message mf mk ce req
        (tx.gas - (callIntrinsic tx.data + exitFrameGas m.world E a)) (by omega) (by rw [hsum, hFd]; omega)
      rw [hsum] at hx
      refine ⟨post, ?_, herr, hg, hrf, hdel, hpaid⟩
      rw [hM] at hx
      exact hx)
  refine ⟨_, bout', process, cum, ?_⟩
  obtain ⟨hdel, hpaid⟩ := hq
  rw [hdel]
  refine hpaid.congr ?_
  intro x hx
  have hEx := hnoE x hx
  have hCx : m.benv.stat.coinbase ≠ x := by
    intro hc
    apply adm.block.2
    rw [hc]
    show x ∈ parties m.benv.state
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [parties, List.mem_cons, true_or, or_true]
  show ((_ : State).get x).stor = (post.state.get x).stor
  simp only [List.foldl_nil, State.addBal]
  rw [State.setBal_get_ne hCx, State.setBal_get_ne hEx]

/-- **`lp_exit`'s message.** -/
theorem lp_exit_message_holds : lp_exit_message := by
  intro d m A msg E a mins ask req R hR hG
  have mk : ExitMarked m.world :=
    { covered := m.backed A
      usdcProxy := Usdc.usdc_code_at_cut (d.sincePool m.history) m.block m.cut BodyStageCapabilities.historical A.usdcCode
        A.circle.usdcCertified
      minter := m.minter A
      id4 := m.id4 A }
  obtain ⟨post, hx, herr, hg, hrf, -, hpaid⟩ := exit_message (m.facts A) mk ask req R hR hG
  exact ⟨post, hx, herr, hg, by rw [hrf, Int.toNat_natCast], hpaid⟩

end Blanc.Composition.Curve3PoolPublic
