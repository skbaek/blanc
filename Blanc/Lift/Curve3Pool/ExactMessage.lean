import Blanc.Lift.StaticGasMessage
import Blanc.Lift.Curve3Pool.ExactStaticGas

/-!
# Exact-gas liveness at message entry

The five exact frame theorems (`removeLiquidity_live_exact`, `exchange_live_exact`,
`addLiquidity_live_exact`, `removeLiquidityImbalance_live_exact`,
`removeLiquidityOneCoin_live_exact`) are stated at an arbitrary static machine. Here each is stated
for a message `msg`: every premise, the model's words and the closed cost
`c` are fixed at the base message's `(initSevm msg, initDevm msg)`, before any residual gas; then
for every `R` with the frame theorem's headroom, the message entered with the grant `R + c`
(`msg.withGas (R + c)`) executes (`exec (initEvm …) = .ok post`), ends with exactly `R` gas, and
has the frame theorem's effect.

The proof instantiates the frame theorem at `{initSevm msg with gas := R + c}` (which is
`initSevm (msg.withGas (R + c))`) and `initDevm msg`, with the same call data `P` and premises
transported across the static initial gas (`*.withStaticGas`); the cost is rewritten back to `c`
(`*ExactCost_withStaticGas`) before the residual gas is chosen, so no execution is transported
across gas. Where the frame theorem chooses the model's words after the static machine, the words
it chooses at the grant are the base message's (`xpWords_unique`, `alExactCost_words_eq`,
`RliWordsPin.unique`, `ocWords_unique`, from the model's own checks).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **`remove_liquidity`, exact gas at message entry.** -/
theorem removeLiquidity_msg_exact {msg : Msg} {s : State} {o : Out} {T : B256}
    {W : Nat → Devm → Prop} {U : Nat} (P : RLExactCalls)
    (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o)
    (htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
    (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (W k)) (hWb : W 0 (initDevm msg))
    (hP : RLExactPremises (initSevm msg) (initDevm msg) T W U P) :
    ∀ R, 167000 + 5 * U ≤ R →
      R + rlExactCost (initSevm msg) (initDevm msg) T P < 2 ^ 256 →
      (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
          (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post)),
        PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
          ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
          (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post),
        exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) =
          .ok post ∧
        post.gasLeft = R ∧
        RawEffect ⟨0, _, _, .ok post, exc⟩ post (rlEnv (initSevm msg) T) o ∧
        Checkpoint (post.getStor msg.currentTarget) o.state := by
  intro R hR hGm hkeep
  obtain ⟨F, hF⟩ : ∃ F, F = R + rlExactCost (initSevm msg) (initDevm msg) T P := ⟨_, rfl⟩
  have h := removeLiquidity_live_exact (sevm := {initSevm msg with gas := F})
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc
    (hid.withStaticGas F) (fun k hk => (hWc k hk).withStaticGas F) hWb (hP.withStaticGas F)
  rw [rlExactCost_withStaticGas (initSevm msg) F] at h
  have h' := h R
  rw [← hF] at h' hGm hkeep ⊢
  obtain ⟨post, exc, hg, hraw, hckp⟩ := h' hR hGm hkeep
  exact ⟨post, exc, exec_withGas_of_frame exc, hg, hraw, hckp⟩


/-- **`exchange`, exact gas at message entry.** The model's words are fixed at the base message,
before the residual gas. -/
theorem exchange_msg_exact {msg : Msg} {s : State} {o : Out} {i j : Fin 3}
    {B1 B2 : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : ExchangeExactCalls)
    (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = selExchange)
    (hi : i.val = (exI (initSevm msg)).toNat) (hj : j.val = (exJ (initSevm msg)).toNat)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : step s (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2))
      (decodeCall (initSevm msg)) = some o)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
    (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : WClosed (initSevm msg) W) (hW'c : WClosed (initSevm msg) W') (hWb : W (initDevm msg))
    (hbal : i = feeIndex →
      StaticWordCallProfile (initSevm msg) W W
        (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
        (balanceOfData msg.currentTarget) B1 U 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
      StaticWordCallProfile (initSevm msg) W' W'
        (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
        (balanceOfData msg.currentTarget) B2 U 0x71c 0x24 0x780 P.balD2 P.balN2)
    (hpull : MutableCallProfile (initSevm msg) W W'
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot i))
      (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++
        (exDx (initSevm msg)).toBytes) RawCallOk U 0x600 0x64 0x6c0 P.pullD P.pullN)
    (hW''c : WClosed (initSevm msg) W'')
    (hpush : MutableCallProfile (initSevm msg) W' W''
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot j))
      (transferSel ++ msg.caller.toB256.toBytes ++ (Nat.toB256 (exPushAmt o)).toBytes) RawCallOk U
      0xb60 0x44 0xc00 P.pushD P.pushN) :
    ∃ (x0 x1 x2 : B256) (amp v : Nat),
      xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
        (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
        (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ =
          some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
      (∃ (hi3 : (exI (initSevm msg)).toNat < 3) (hj3 : (exJ (initSevm msg)).toNat < 3),
        getYChk amp ⟨(exI (initSevm msg)).toNat, hi3⟩ ⟨(exJ (initSevm msg)).toNat, hj3⟩
          (exW3 x0 x1 x2 (exI (initSevm msg)).toNat + exCred (initSevm msg) B1 B2 *
            exRate (exI (initSevm msg)).toNat / exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get =
          some v) ∧
      ∀ R, 60000 + U ≤ R →
        costExchange (initSevm msg) (initDevm msg) s
          (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i j
          (exDx (initSevm msg)).toNat + 4 * U ≤
            R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v →
        R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v < 2 ^ 256 →
        (∀ post (exc : Exec 0 (initSevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
            (initDevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post)),
          PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v)))
            (initDevm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) (.ok post),
          exec (initEvm (msg.withGas
            (R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v))) = .ok post ∧
          post.gasLeft = R ∧ ∃ bp bq,
          pullIn (exEnv (initSevm msg) i j bp bq) i (exDx (initSevm msg)).toNat =
            pullIn (exEnv (initSevm msg) i j (exBalOpt i B1) (exBalOpt i B2)) i
              (exDx (initSevm msg)).toNat ∧
          RawEffect ⟨0, _, _, .ok post, exc⟩ post (exEnv (initSevm msg) i j bp bq) o ∧
          Checkpoint (post.getStor msg.currentTarget) o.state ∧ W'' post := by
  obtain ⟨x0, x1, x2, amp, v, hX, hA, hY, -⟩ := exchange_live_exact (sevm := initSevm msg)
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hi hj hck hstep hcoin hpc hid
    hWc hW'c hWb hbal hpull hW''c hpush
  refine ⟨x0, x1, x2, amp, v, hX, hA, hY, fun R hR hRc hGm hkeep => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F, F = R + exExactCost (initSevm msg) (initDevm msg) P x0 x1 x2 B1 B2 amp v :=
    ⟨_, rfl⟩
  obtain ⟨x0', x1', x2', amp', v', hX', hA', hY', h⟩ := exchange_live_exact
    (sevm := {initSevm msg with gas := F})
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hi hj hck hstep hcoin hpc
    (hid.withStaticGas F) (hWc.withStaticGas F) (hW'c.withStaticGas F) hWb
    (fun e => ⟨(hbal e).1.withStaticGas F, (hbal e).2.withStaticGas F⟩) (hpull.withStaticGas F)
    (hW''c.withStaticGas F) (hpush.withStaticGas F)
  obtain ⟨rfl, rfl, rfl⟩ := xpWords_unique hX hX'
  obtain rfl : amp = amp' := Option.some.inj (hA.symm.trans hA')
  obtain ⟨hi3, hj3, hY⟩ := hY
  obtain ⟨hi3', hj3', hY'⟩ := hY'
  obtain rfl : v = v' := Option.some.inj (hY.symm.trans hY')
  rw [exExactCost_withStaticGas (initSevm msg) F] at h
  have h' := h R
  rw [← hF] at h' hRc hGm hkeep ⊢
  obtain ⟨post, exc, bp, bq, hpe, hraw, hckp, hW'', hg⟩ := h' hR hRc hGm hkeep
  exact ⟨post, exc, exec_withGas_of_frame exc, hg, bp, bq, hpe, hraw, hckp, hW''⟩

/-- **`add_liquidity`, exact gas at message entry.** The model's words are fixed at the base
message, before the residual gas. -/
theorem addLiquidity_msg_exact {msg : Msg} {s : State} {o : Out} {T B1 B2 : B256}
    {W : Nat → Devm → Prop} {U : Nat} (P : ALExactCalls)
    (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = selAddLiquidity)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : step s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (decodeCall (initSevm msg)) =
      some o)
    (htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
    (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j)) (hWb : W 0 (initDevm msg))
    (hskip : ∀ k : Fin 3, alAmt (initSevm msg) k.val = 0 → ∀ b, W k b → W (k + 1) b)
    (hP : ALExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T B1 B2
      (Nat.toB256 (alMintAmt o)) W U P) :
    ∃ (amp v0 v1 v2 : Nat) (xa xb xc : V3) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
      aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
      xpChk ⟨(alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
          0).toNat,
        (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1).toNat,
        (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
          2).toNat⟩ = some xb ∧
      getDChk xb.get amp 1 = some v1 ∧
      (T ≠ 0 →
        xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
          (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
          (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ = some xa ∧
        getDChk xa.get amp 1 = some v0 ∧
        RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
          (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
          (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 0)
          (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 0)
          f0 s0 x0 ∧
        RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
          (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
          (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 1)
          (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1)
          f1 s1 x1 ∧
        RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
          (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
          (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 2)
          (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 2)
          f2 s2 x2 ∧
        xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2) ∧
      ∀ R, 100000 + 5 * U ≤ R →
      costAddLiquidity s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (argV3 (initSevm msg) 0) +
          7 * U ≤
        R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0
          s1 s2 x0 x1 x2 →
      R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1
          s2 x0 x1 x2 + 6000 < 2 ^ 256 →
      (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P
            amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
          (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb
            xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post)),
        PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
          ∀ c' ∈ Exec.childFrames exc, c'.post.getCode 4 = c'.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P
            amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
          (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb
            xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post),
        exec (initEvm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa
          xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) = .ok post ∧
        post.gasLeft = R ∧
        ∃ e : Env, e.supply = some T.toNat ∧ step s e (decodeCall (initSevm msg)) = some o ∧
          RawEffect ⟨0, _, _, .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor msg.currentTarget) o.state := by
  obtain ⟨amp, v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1, x2, hA, hXb, hD1, hT, -⟩ :=
    addLiquidity_live_exact (sevm := initSevm msg) (pre := initDevm msg) P hcode hfork hstatic
      hdepth hlen hcd hsel hck hstep htok hcoin hpc hid hWc hWb hskip hP
  refine ⟨amp, v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1, x2, hA, hXb, hD1, hT,
    fun R hR hRc hGm hkeep => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F, F = R + alExactCost (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc
    v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 := ⟨_, rfl⟩
  obtain ⟨amp', v0', v1', v2', xa', xb', xc', f0', f1', f2', s0', s1', s2', x0', x1', x2', hA',
    hXb', hD1', hT', h⟩ := addLiquidity_live_exact (sevm := {initSevm msg with gas := F})
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc
    (hid.withStaticGas F) (fun k hk => (hWc k hk).withStaticGas F) hWb hskip (hP.withStaticGas F)
  rw [alExactCost_withStaticGas (initSevm msg) F] at h
  have hc := alExactCost_words_eq (sevm := initSevm msg) (pre := initDevm msg) (P := P) (B1 := B1)
    (B2 := B2) hA hXb hD1
    hT hA' hXb' hD1' hT'
  rw [hc] at h
  have h' := h R
  rw [← hF] at h' hRc hGm hkeep ⊢
  obtain ⟨post, exc, hg, e, he, hstep', hraw, hckp⟩ := h' hR hRc (by
    rw [initDevm_gasMeasure]; exact hGm) hkeep
  exact ⟨post, exc, exec_withGas_of_frame exc, hg, e, he, hstep', hraw, hckp⟩

/-- **`remove_liquidity_imbalance`, exact gas at message entry.** The model's words are fixed at
the base message, before the residual gas. -/
theorem removeLiquidityImbalance_msg_exact {msg : Msg} {s : State} {o : Out}
    {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLIExactCalls)
    (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityImbalance)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : step s (rliEnvW (initSevm msg) T.toNat) (decodeCall (initSevm msg)) = some o)
    (htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
    (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j)) (hWb : W 0 (initDevm msg))
    (hP : RLIExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T
      (Nat.toB256 (rliBurnAmt o)) W U P)
    (hskip : ∀ k : Fin 3, rliAmt (initSevm msg) k.val = 0 → ∀ b, W (k + 1) b → W (k + 2) b) :
    ∃ w : RliWords, RliWordsPin (initSevm msg) (initDevm msg) s w ∧
      ∀ R, 66000 + 3 * U ≤ R →
        costImbalance s (rliEnvW (initSevm msg) T.toNat) (argV3 (initSevm msg) 0) + 5 * U ≤
          R + rliExactCost (initSevm msg) (initDevm msg) P T w →
        R + rliExactCost (initSevm msg) (initDevm msg) P T w + 3000 < 2 ^ 256 →
        (∀ post (exc : Exec 0
            (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
            (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
            (.ok post)),
          PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0
            (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
            (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w)))
            (.ok post),
          exec (initEvm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) P T w))) =
            .ok post ∧
          post.gasLeft = R ∧
          RawEffect ⟨0, _, _, .ok post, exc⟩ post (rliEnvW (initSevm msg) T.toNat) o ∧
          Checkpoint (post.getStor msg.currentTarget) o.state ∧ W 4 post := by
  obtain ⟨w, hw, -⟩ := removeLiquidityImbalance_live_exact (sevm := initSevm msg)
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc hid
    hWc hWb hP hskip
  refine ⟨w, hw, fun R hR hRc hGm hkeep => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F, F = R + rliExactCost (initSevm msg) (initDevm msg) P T w := ⟨_, rfl⟩
  obtain ⟨w', hw', h⟩ := removeLiquidityImbalance_live_exact (sevm := {initSevm msg with gas := F})
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc
    (hid.withStaticGas F) (fun k hk => (hWc k hk).withStaticGas F) hWb (hP.withStaticGas F) hskip
  obtain rfl : w = w' := hw.unique hw'.ofStaticGas
  rw [rliExactCost_withStaticGas (initSevm msg) F] at h
  have h' := h R
  rw [← hF] at h' hRc hGm hkeep ⊢
  obtain ⟨post, exc, hg, hraw, hckp, hW4⟩ := h' hR hRc (by rw [initDevm_gasMeasure]; exact hGm)
    hkeep
  exact ⟨post, exc, exec_withGas_of_frame exc, hg, hraw, hckp, hW4⟩

/-- **`remove_liquidity_one_coin`, exact gas at message entry.** The model's words are fixed at
the base message, before the residual gas. -/
theorem removeLiquidityOneCoin_msg_exact {msg : Msg} {s : State} {o : Out}
    {i : Fin 3} {T : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : OCExactCalls)
    (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityOneCoin)
    (hi : i.val = (ocI (initSevm msg)).toNat)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : step s (ocEnv (initSevm msg) i T.toNat) (decodeCall (initSevm msg)) = some o)
    (htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
    (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : WClosed (initSevm msg) W) (hW'c : WClosed (initSevm msg) W') (hWb : W (initDevm msg))
    (hW''c : WClosed (initSevm msg) W'')
    (hP : OCExactPremises (initSevm msg) (initDevm msg) T (Nat.toB256 (ocPushAmt o)) W W' W'' U P) :
    ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI (initSevm msg)).toNat < 3),
      aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
      getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
        (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y.toNat ∧
      CwStep (Bytes.toB256 [0] = ocI (initSevm msg)) x0 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
        (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x0 r0 ∧
      CwStep (Bytes.toB256 [1] = ocI (initSevm msg)) x1 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
        (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x1 r1 ∧
      CwStep (Bytes.toB256 [2] = ocI (initSevm msg)) x2 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
        (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x2 r2 ∧
      getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
        (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y2.toNat ∧
      ∀ R, 131000 + 3 * U ≤ R →
      R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2 + 2000 <
        2 ^ 256 →
      (∀ post (exc : Exec 0 (initSevm (msg.withGas
            (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
          (initDevm (msg.withGas
            (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
          (.ok post)),
        PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
          ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
            (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
          (initDevm (msg.withGas
            (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2)))
          (.ok post),
        exec (initEvm (msg.withGas
          (R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0 r1 r2 y2))) =
          .ok post ∧
        post.gasLeft = R ∧ ∃ T' : Nat,
        RawEffect ⟨0, _, _, .ok post, exc⟩ post (ocEnv (initSevm msg) i T') o ∧
        Checkpoint (post.getStor msg.currentTarget) o.state ∧ W'' post := by
  obtain ⟨amp, x0, x1, x2, D0, y, r0, r1, r2, y2, hi3, hA, hX, hD0, hy, h0, h1, h2, hy2, -⟩ :=
    removeLiquidityOneCoin_live_exact (sevm := initSevm msg) (pre := initDevm msg) P hcode hfork
      hstatic hdepth hlen hcd hsel hi hck hstep htok hcoin hpc hid hWc hW'c hWb hW''c hP
  refine ⟨amp, x0, x1, x2, D0, y, r0, r1, r2, y2, hi3, hA, hX, hD0, hy, h0, h1, h2, hy2,
    fun R hR hGm hkeep => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F, F = R + ocExactCost (initSevm msg) (initDevm msg) T P amp x0 x1 x2 D0 y r0
    r1 r2 y2 := ⟨_, rfl⟩
  obtain ⟨amp', x0', x1', x2', D0', y', r0', r1', r2', y2', hi3', hA', hX', hD0', hy', h0', h1',
    h2', hy2', h⟩ := removeLiquidityOneCoin_live_exact (sevm := {initSevm msg with gas := F})
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hi hck hstep htok hcoin hpc
    (hid.withStaticGas F) (hWc.withStaticGas F) (hW'c.withStaticGas F) hWb
    (hW''c.withStaticGas F) (hP.withStaticGas F)
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    ocWords_unique hA hX hD0 hy h0 h1 h2 hy2 hA' hX' hD0' hy' h0' h1' h2' hy2'
  rw [ocExactCost_withStaticGas (initSevm msg) F] at h
  have h' := h R
  rw [← hF] at h' hGm hkeep ⊢
  obtain ⟨post, exc, T', hg, hraw, hckp, hW''⟩ := h' hR (by rw [initDevm_gasMeasure]; exact hGm)
    hkeep
  exact ⟨post, exc, exec_withGas_of_frame exc, hg, T', hraw, hckp, hW''⟩

end Blanc.Lift.Curve3Pool
