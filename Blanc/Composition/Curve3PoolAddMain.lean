import Blanc.Composition.Curve3PoolAddCost

/-!
# `add_liquidity_message`

`add_pulled_eq`: the ledger the chain carries is the one `pulled_held` reads. `add_run`: the frame's run ends in a post whose refund is
fixed, whose world is the chain's last, and whose books are the walk's. `add_core`: the message under the moment's facts.
`add_liquidity_message_holds` closes the statement.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (V3 Env Out ALExactCalls ALExactPremises WClosed alAmt coinSlot alEnvW alFrontCost alExactCost0 alExactCost1 alRefund0 alRefund1
  AlEndX alLocked1 alUnlock alStor3 alOld alLiveNew alNewW alMintW t_0000_c0 cert cert_checkM cert_jumpsOkM Checkpoint rx_al_frame0_exact rx_al_frame1_exact
  feeDen precMul arg argV3 aChk)
open Blanc.Composition.Curve3PoolCalleeLive (MintFits mintStor)
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins pulledK PullFitsK)
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3With)
open Blanc.Composition.Curve3Pool3CrvExactAssembly (alC3W)
open Blanc.Composition.Curve3Pool3CrvInstance (coinOf tokOf)

variable {w w' : Jaune.State} {E : Adr} {v : Nat}

/-! ## The ledgers -/

/-- The chain's pulled ledger is `pulledAll`. -/
theorem add_pulled_eq (ho : CoinsOpen w E) (hap : SwapApart w E) (i : Fin 3) (hv : v < 2 ^ 256) (hle : v ≤ coinHeld w E i) (hal : v ≤ allowanceOf w E i)
    (hcr : CreditFits w pool i (netOf w i v)) :
    pulledK i (w.getStor (coinAt i)) E pool (Nat.toB256 v) = pulledAll w E i v := by
  have hs : (Nat.toB256 v).toNat = v := B256.toNat_toB256_of_lt hv
  have hEp : E ≠ pool := fun e => hap.poolEntry 0 (by rw [e])
  match i with
  | 0 =>
    obtain ⟨a1, a2⟩ := hap.allow 0
    have hne : Dai.balSlot E ≠ Dai.balSlot pool := hap.poolEntry 0
    show Dai.moveStor (Dai.spendStor (w.getStor dai) E pool (Nat.toB256 v)) E pool (Nat.toB256 v) =
      daiPulled (w.getStor dai) (Dai.balSlot E) (Dai.balSlot pool) (Dai.allowSlot E pool) (Nat.toB256 v)
    have hsp : Dai.spendStor (w.getStor dai) E pool (Nat.toB256 v) = if (w.getStor dai).get (Dai.allowSlot E pool) = Dai.maxUint then w.getStor dai else
        (w.getStor dai).set (Dai.allowSlot E pool) ((w.getStor dai).get (Dai.allowSlot E pool) - Nat.toB256 v) := by
      unfold Dai.spendStor
      by_cases h : (w.getStor dai).get (Dai.allowSlot E pool) = Dai.maxUint
      · rw [if_pos h, if_neg (fun c => c.2 h)]
      · rw [if_neg h, if_pos ⟨hEp, h⟩]
    unfold Dai.moveStor daiPulled
    rw [hsp, Stor.get_set_ne _ hne]
  | 1 =>
    obtain ⟨a1, a2⟩ := hap.allow 1
    have a1' : Usdc.allowSlot E pool ≠ Usdc.balSlot E := a1
    have a2' : Usdc.allowSlot E pool ≠ Usdc.balSlot pool := a2
    have hne : Usdc.balSlot E ≠ Usdc.balSlot pool := hap.poolEntry 1
    have hPf := unfrozen_lt ho.usdcParties.1
    have hEf := unfrozen_lt ho.usdcParties.2
    have hle' : v ≤ ((w.getStor usdc).get (Usdc.balSlot E)).toNat := by
      rw [held_one ho.usdcV22.1, bits_of hEf] at hle; exact hle
    have hc' : ((w.getStor usdc).get (Usdc.balSlot pool)).toNat + v < 2 ^ 255 := hcr
    have hal' : v ≤ ((w.getStor usdc).get (Usdc.allowSlot E pool)).toNat := hal
    show UsdcLive.pullStor (w.getStor usdc) E pool pool (Nat.toB256 v) = _
    have e1 : Nat.toB256 (Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot E)) - v) = (w.getStor usdc).get (Usdc.balSlot E) - Nat.toB256 v := by
      refine B256.toNat_inj _ _ ?_
      rw [bits_of hEf, B256.toNat_toB256_of_lt (by have := B256.toNat_lt ((w.getStor usdc).get (Usdc.balSlot E)); omega), sub_nat (by rw [hs]; exact hle'), hs]
    have e2 : Nat.toB256 (Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot pool)) + v) = (w.getStor usdc).get (Usdc.balSlot pool) + Nat.toB256 v := by
      refine B256.toNat_inj _ _ ?_
      rw [bits_of hPf, B256.toNat_toB256_of_lt (by omega), toNat_add_of (by rw [hs]; omega), hs]
    have e3 : Nat.toB256 (((w.getStor usdc).get (Usdc.allowSlot E pool)).toNat - v) = (w.getStor usdc).get (Usdc.allowSlot E pool) - Nat.toB256 v := by
      refine B256.toNat_inj _ _ ?_
      rw [B256.toNat_toB256_of_lt (by have := B256.toNat_lt ((w.getStor usdc).get (Usdc.allowSlot E pool)); omega), sub_nat (by rw [hs]; exact hal'), hs]
    show UsdcLive.pullStor (w.getStor usdc) E pool pool (Nat.toB256 v) = (((w.getStor usdc).set (Usdc.balSlot E) ((w.getStor usdc).get (Usdc.balSlot E) - Nat.toB256 v)).set
      (Usdc.balSlot pool) ((w.getStor usdc).get (Usdc.balSlot pool) + Nat.toB256 v)).set
      (Usdc.allowSlot E pool) ((w.getStor usdc).get (Usdc.allowSlot E pool) - Nat.toB256 v)
    unfold UsdcLive.pullStor Usdc.creditStor Usdc.debitStor
    rw [hs, Stor.get_set_ne _ hne, Stor.get_set_ne _ (Ne.symm a2'), Stor.get_set_ne _ (Ne.symm a1'), e1, e2, e3]
  | 2 =>
    obtain ⟨a1, a2⟩ := hap.allow 2
    have a1' : Usdt.allowSlot E pool ≠ Usdt.balSlot E := a1
    have a2' : Usdt.allowSlot E pool ≠ Usdt.balSlot pool := a2
    have hAu := hap.allowUsdt
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hAu
    obtain ⟨a0, -, -, -, -, aO⟩ := hAu
    have hne : Usdt.balSlot E ≠ Usdt.balSlot pool := hap.poolEntry 2
    have hE1 := hap.usdtE.1
    simp only [usdtGateSlots, List.mem_cons, List.not_mem_nil, or_false, not_or] at hE1
    have hE0 : Usdt.balSlot E ≠ 0 := fun e => hE1.2.2.2.2 (by
      show Usdt.balSlot E = _
      rw [e]; decide)
    have hp0 : Usdt.balSlot pool ≠ 0 := usdt_pool_ne_zero
    have hS : ∀ k, k ≠ Usdt.allowSlot E pool → (Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v)).get k = (w.getStor usdt).get k := fun k hk => by
      unfold Usdt.spendStor
      split
      · rfl
      · exact Stor.get_set_ne _ (Ne.symm hk) _
    have hSp : Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v) = usdtSpent (w.getStor usdt) (Usdt.allowSlot E pool) (Nat.toB256 v) := rfl
    show Usdt.moveStor (Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v)) E pool (Nat.toB256 v) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v)) =
      usdtAfter (usdtSpent (w.getStor usdt) (Usdt.allowSlot E pool) (Nat.toB256 v)) (Usdt.balSlot E) (Usdt.balSlot pool) (Nat.toB256 v)
        (Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))
    rw [← hSp]
    obtain ⟨σ', hσ'⟩ : ∃ σ', σ' = Usdt.spendStor (w.getStor usdt) E pool (Nat.toB256 v) := ⟨_, rfl⟩
    rw [← hσ']
    have h0 : σ'.get 0 = (w.getStor usdt).get 0 := by
      rw [hσ', hS _ (fun e => a0 (show Usdt.allowSlot E pool = _ by rw [← e]; decide))]
    have hown : Usdt.ownerOf (Usdt.credit (Usdt.debit σ' E (Nat.toB256 v)) pool (Nat.toB256 v - Usdt.feeOf (w.getStor usdt) (Nat.toB256 v))) = Usdt.ownerOf σ' := by
      unfold Usdt.ownerOf Usdt.credit Usdt.debit
      rw [Stor.get_set_ne _ hp0, Stor.get_set_ne _ hE0]
    have hown' : Usdt.ownerOf σ' = Usdt.ownerOf (w.getStor usdt) := by
      unfold Usdt.ownerOf; rw [h0]
    have hPO : Usdt.balSlot pool ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := Ne.symm hap.usdtOwner.2
    have hEO : Usdt.balSlot E ≠ Usdt.balSlot (Usdt.ownerOf (w.getStor usdt)) := hap.usdtE.2
    unfold Usdt.moveStor usdtAfter
    split
    · unfold Usdt.credit Usdt.debit
      rw [Stor.get_set_ne _ hne]
    · rw [hown, ownerKey_eq]
      unfold Usdt.credit Usdt.debit
      rw [Stor.get_set_ne _ hne, hown', Stor.get_set_ne _ hPO, Stor.get_set_ne _ hEO]

/-- `v3Of`'s reading of the deposit's books. -/
theorem afterDeposit_get (w : Jaune.State) (am : V3) (k : Fin 3) : (afterDeposit w am).get k = recorded w k + netOf w k (am.get k) :=
  v3Of_get _ k

theorem netOf_zero (w : Jaune.State) (k : Fin 3) : netOf w k 0 = 0 := by
  unfold netOf
  split
  · exact Nat.zero_sub _
  · rfl

/-! ## The front's own charge -/

/-- **The lock's first write alone covers the walk's no-wrap margin.** -/
theorem add_front {s : Sevm} {p : Devm} (f : CoinStand s p w E) (hlock : (w.getStor pool).get lockW = 0) (P : ALExactCalls) (amp : Nat) :
    6000 ≤ alFrontCost s p P amp := by
  have hS : p.getStor s.currentTarget = w.getStor pool := by rw [f.target]; exact (f.stor pool (Or.inl rfl)).1
  have hO : (getOrigAcct s s.currentTarget).stor = w.getStor pool := by rw [f.target]; exact (f.stor pool (Or.inl rfl)).2
  have hA : At s.currentTarget [] (w.getStor pool) p :=
    ⟨fun k => ⟨fun h => absurd h (f.keysCold _), fun h => absurd h List.not_mem_nil⟩, hS⟩
  have a1 := hA.sload lockW
  have c1 := (mv_afterSload s p lockW).clean f.clean
  have hv : (afterSload s p lockW).getOrigStorVal s s.currentTarget lockW = 0 := by
    rw [c1.orig, hO, hlock]
  have hc : sstoreCost s (afterSload s p lockW) lockW (Bytes.toB256 [1]) = 20000 := by
    rw [a1.sstoreCost_warm List.mem_cons_self, hv, hlock, first_value]
    rfl
  unfold alFrontCost Curve3Pool.alPreCost1
  rw [hc]
  omega

/-! ## The effect -/

/-- A ledger left alone reads the same. -/
theorem held_same {k : Fin 3} (h : w'.getStor (coinAt k) = w.getStor (coinAt k)) (a : Adr) : coinHeld w' a k = coinHeld w a k := by
  match k with
  | 0 =>
    have h0 : w'.getStor dai = w.getStor dai := h
    rw [held_word (by decide), held_word (by decide)]
    unfold word
    rw [show coinAt 0 = dai from rfl, h0]
  | 1 =>
    have h1 : w'.getStor usdc = w.getStor usdc := h
    unfold coinHeld UsdcPacked word
    rw [show coinAt 1 = usdc from rfl, h1]
  | 2 =>
    have h2 : w'.getStor usdt = w.getStor usdt := h
    rw [held_word (by decide), held_word (by decide)]
    unfold word
    rw [show coinAt 2 = usdt from rfl, h2]

/-- **The final state is `AddPaid`.** -/
theorem add_paid {am : V3} {minted : Nat} {stored : V3} (ho : CoinsOpen w E) (hap : AddApart w E)
    (hheld : ∀ k, am.get k ≤ coinHeld w E k) (hcr : ∀ k, CreditFits w pool k (netOf w k (am.get k))) (hfee : UsdtFeeFits w (am.get 2))
    (hcoin0 : ∀ k, am.get k = 0 → w'.getStor (coinAt k) = w.getStor (coinAt k))
    (hcoin : ∀ k, am.get k ≠ 0 → w'.getStor (coinAt k) = pulledAll w E k (am.get k))
    (hc3 : w'.getStor c3 = mintStor (w.getStor c3) E.toB256 (Nat.toB256 minted))
    (hbook : ∀ k, recorded w' k = stored.get k)
    (hfit : supply w + minted < 2 ^ 256 ∧ shares w E + minted < 2 ^ 256) :
    AddPaid w w' E am minted stored := by
  have hml : minted < 2 ^ 256 := by omega
  have hmn : (Nat.toB256 minted).toNat = minted := B256.toNat_toB256_of_lt hml
  have hne : mapSlot 3 E.toB256 ≠ Curve3Crv.vySupplySlot := hap.c3
  refine ⟨⟨?_, ?_, hbook⟩, fun k => ?_⟩
  · show ((w'.getStor c3).get Curve3Crv.vySupplySlot).toNat = ((w.getStor c3).get Curve3Crv.vySupplySlot).toNat + minted
    have h1 : ((w.getStor c3).get Curve3Crv.vySupplySlot).toNat + minted < 2 ^ 256 := hfit.1
    rw [hc3]
    unfold mintStor
    rw [Stor.get_set_ne _ hne, Stor.get_set_self, toNat_add_of (by rw [hmn]; exact h1), hmn]
  · show ((w'.getStor c3).get (mapSlot 3 E.toB256)).toNat = ((w.getStor c3).get (mapSlot 3 E.toB256)).toNat + minted
    have h2 : ((w.getStor c3).get (mapSlot 3 E.toB256)).toNat + minted < 2 ^ 256 := hfit.2
    rw [hc3]
    unfold mintStor
    rw [Stor.get_set_self, Stor.get_set_ne _ (Ne.symm hne), toNat_add_of (by rw [hmn]; exact h2), hmn]
  · by_cases hz : am.get k = 0
    · rw [held_same (hcoin0 k hz), held_same (hcoin0 k hz), hz, netOf_zero]
      exact ⟨rfl, rfl⟩
    · exact pulled_held ho hap.toSwapApart k (hcoin k hz) (Nat.lt_of_le_of_lt (hheld k) coinHeld_lt) (hheld k) (hcr k) (fun h => by rw [h]; exact hfee)

/-! ## The run's end -/

/-- **The walk's end as a message's post.** -/
theorem add_end {msg : Msg} {F R : Nat} {σ' : Stor} {f0 f1 f2 : B256} {Wm : Devm → Prop} {rf : Int}
    (hcode : (initSevm msg).code = Curve3Pool.code) (hfork : ShanghaiOnwards (initSevm msg).benvStat.fork)
    (hrun : SFunc.RunEx cert.prog {initSevm msg with gas := F} (St (initDevm msg) [] Mem.empty F) t_0000_c0
      (AlEndX {initSevm msg with gas := F} σ' f0 f1 f2 R Wm rf)) :
    ∃ post, exec (initEvm (msg.withGas F)) = .ok post ∧ post.error = none ∧ post.gasLeft = R ∧ post.refundCounter = rf ∧ Wm post ∧
      ∀ x, (post.getStor msg.currentTarget).get x = σ'.get x := by
  obtain ⟨r, hr, ⟨D, rfl, hst, -⟩, D', hD', hg, hW, hrf⟩ := hrun
  obtain rfl : D = D' := by injection hD'
  obtain ⟨exD⟩ := Lift.lift_exactM (sevm := {initSevm msg with gas := F}) cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  exact ⟨D, Lift.exec_withGas_of_frame exD, (Exec.ok_error_eq exD hfork.rules_stateGas_none).trans rfl, hg, hrf, hW, hst⟩

/-- The books the walk leaves. -/
theorem add_books {σ : Stor} {s0 s1 s2 : B256} {stored : V3} (he : stored = ⟨s0.toNat, s1.toNat, s2.toNat⟩) {p : Devm}
    (h : ∀ x, (p.getStor pool).get x = (alUnlock (alStor3 (alLocked1 σ) s0 s1 s2)).get x) (k : Fin 3) :
    ((p.getStor pool).get (Curve3Pool.balanceSlot k)).toNat = stored.get k := by
  subst he
  rw [h]
  match k with
  | 0 =>
    show ((alUnlock (alStor3 (alLocked1 σ) s0 s1 s2)).get (Curve3Pool.balanceSlot 0)).toNat = s0.toNat
    unfold alUnlock alStor3
    rw [Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide)]
    exact congrArg B256.toNat (Stor.get_set_self _ _ _)
  | 1 =>
    show ((alUnlock (alStor3 (alLocked1 σ) s0 s1 s2)).get (Curve3Pool.balanceSlot 1)).toNat = s1.toNat
    unfold alUnlock alStor3
    rw [Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide)]
    exact congrArg B256.toNat (Stor.get_set_self _ _ _)
  | 2 =>
    show ((alUnlock (alStor3 (alLocked1 σ) s0 s1 s2)).get (Curve3Pool.balanceSlot 2)).toNat = s2.toNat
    unfold alUnlock alStor3
    rw [Stor.get_set_ne _ (by decide)]
    exact congrArg B256.toNat (Stor.get_set_self _ _ _)

/-- **The first deposit's run, at any residual above the walk's headroom.** -/
theorem add_run0 {msg : Msg} {s : Curve3Pool.State} {W : Nat → Devm → Prop} {U amp v1 : Nat} {B1 B2 : B256} {xb : V3} (P : ALExactCalls)
    (hcode : (initSevm msg).code = Curve3Pool.code) (hfork : ShanghaiOnwards (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdep : (initSevm msg).depth ≠ 0) (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = Curve3Pool.selAddLiquidity) (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j)) (hWb : W 0 (initDevm msg))
    (ha : Curve3Pool.Abstracts ((initDevm msg).getStor (initSevm msg).currentTarget) s)
    (hlock : ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.lockSlot = 0) (hval : (initSevm msg).value = 0)
    (hkill : ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.isKilledSlot = 0)
    (hA : aChk s (initSevm msg).benvStat.time.toNat = some amp)
    (hmf : ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.feeSlot * Bytes.toB256 [0x03] /
        ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.feeSlot = Bytes.toB256 [0x03] ∨
      ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.feeSlot = 0)
    (hP : ALExactPremises (initSevm msg) ((initDevm msg).getStor (initSevm msg).currentTarget) 0 B1 B2 (Nat.toB256 v1) W U P)
    (hskip : ∀ k, k < 3 → alAmt (initSevm msg) k = 0 → ∀ b, W k b → W (k + 1) b)
    (ht0 : alAmt (initSevm msg) 0 ≠ 0 ∧ alAmt (initSevm msg) 1 ≠ 0 ∧ alAmt (initSevm msg) 2 ≠ 0)
    (hsub : alAmt (initSevm msg) 2 ≠ 0 → ¬ B2 < B1)
    (a0 : ¬ Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0 + alAmt (initSevm msg) 0 < Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0)
    (a1 : ¬ Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1 + alAmt (initSevm msg) 1 < Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1)
    (a2 : ¬ Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2 + Curve3Pool.alCr2 (initSevm msg) B1 B2 < Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2)
    (hXb : Curve3Pool.xpChk (alNewW (initSevm msg) ((initDevm msg).getStor (initSevm msg).currentTarget) B1 B2) = some xb)
    (hD1 : Blanc.StableSwapNewton.getDChk xb.get amp 1 = some v1) (hlt : 0 < Nat.toB256 v1)
    (hslip : ¬ Nat.toB256 v1 < Sevm.dataWord (initSevm msg) (Bytes.toB256 [0x64])) (hadd : ¬ 0 + Nat.toB256 v1 < 0)
    (hfront : 6000 ≤ alFrontCost (initSevm msg) (initDevm msg) P amp) {R : Nat} (hR : 100000 + 5 * U ≤ R)
    (hG : R + alExactCost0 (initSevm msg) (initDevm msg) P amp B1 B2 xb v1 < 2 ^ 256) :
    ∃ post, exec (initEvm (msg.withGas (R + alExactCost0 (initSevm msg) (initDevm msg) P amp B1 B2 xb v1))) = .ok post ∧ post.error = none ∧ post.gasLeft = R ∧
      post.refundCounter = alRefund0 (initSevm msg) (initDevm msg) P amp B1 B2 xb v1 ∧ W 4 post ∧
      ∀ x, (post.getStor msg.currentTarget).get x = (alUnlock (alStor3 (alLocked1 ((initDevm msg).getStor (initSevm msg).currentTarget))
        (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor (initSevm msg).currentTarget)) B1 B2 0)
        (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor (initSevm msg).currentTarget)) B1 B2 1)
        (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor (initSevm msg).currentTarget)) B1 B2 2))).get x := by
  obtain ⟨F, hF⟩ : ∃ F, F = R + alExactCost0 (initSevm msg) (initDevm msg) P amp B1 B2 xb v1 := ⟨_, rfl⟩
  have hcost := Curve3Pool.alExactCost0_withStaticGas (initSevm msg) F (initDevm msg) P amp B1 B2 xb v1
  have hrf := Curve3Pool.alRefund0_withStaticGas (initSevm msg) F (initDevm msg) P amp B1 B2 xb v1
  have hfrontF := Curve3Pool.alFrontCost_withStaticGas (initSevm msg) F (initDevm msg) P amp
  have hr := rx_al_frame0_exact (sevm := {initSevm msg with gas := F}) (pre := initDevm msg) (s := s) (U := U) (amp := amp) (B1 := B1) (B2 := B2) (m := 0) (R := R) (W := W)
    P hfork hstatic hdep hlen hcd hsel (hid.withStaticGas F) (fun j hj => (hWc j hj).withStaticGas F) hWb ha hlock hval hkill hA hmf
    (hP.withStaticGas F) hskip ht0 hsub a0 a1 a2 hXb hD1 hlt hslip hadd hR (by rw [hfrontF]; exact hfront) (by rw [hcost]; exact hG)
  rw [hcost, hrf, ← hF] at hr
  obtain ⟨post, hx, herr, hg, hrfp, hWp, hst⟩ := add_end hcode hfork hr
  exact ⟨post, by rw [← hF]; exact hx, herr, hg, hrfp, hWp, hst⟩

/-- **A deposit's run on a positive supply, at any residual above the walk's headroom.** -/
theorem add_run1 {msg : Msg} {s : Curve3Pool.State} {W : Nat → Devm → Prop} {U amp v0 v1 v2 : Nat} {T B1 B2 f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256} {xa xb xc : V3} (P : ALExactCalls)
    (hcode : (initSevm msg).code = Curve3Pool.code) (hfork : ShanghaiOnwards (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdep : (initSevm msg).depth ≠ 0) (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = Curve3Pool.selAddLiquidity) (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : ∀ j, j ≤ 4 → WClosed (initSevm msg) (W j)) (hWb : W 0 (initDevm msg))
    (ha : Curve3Pool.Abstracts ((initDevm msg).getStor (initSevm msg).currentTarget) s)
    (hlock : ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.lockSlot = 0) (hval : (initSevm msg).value = 0)
    (hkill : ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.isKilledSlot = 0)
    (hA : aChk s (initSevm msg).benvStat.time.toNat = some amp)
    (hmf : ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.feeSlot * Bytes.toB256 [0x03] /
        ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.feeSlot = Bytes.toB256 [0x03] ∨
      ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.feeSlot = 0)
    (hP : ALExactPremises (initSevm msg) ((initDevm msg).getStor (initSevm msg).currentTarget) T B1 B2 (alMintW T (Nat.toB256 v0) (Nat.toB256 v2)) W U P)
    (hskip : ∀ k, k < 3 → alAmt (initSevm msg) k = 0 → ∀ b, W k b → W (k + 1) b)
    (hT : T ≠ 0) (hnz : ¬ (alAmt (initSevm msg) 0 = 0 ∧ alAmt (initSevm msg) 1 = 0 ∧ alAmt (initSevm msg) 2 = 0))
    (hsub : alAmt (initSevm msg) 2 ≠ 0 → ¬ B2 < B1)
    (a0 : ¬ Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0 + alAmt (initSevm msg) 0 < Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0)
    (a1 : ¬ Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1 + alAmt (initSevm msg) 1 < Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1)
    (a2 : ¬ Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2 + Curve3Pool.alCr2 (initSevm msg) B1 B2 < Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2)
    (hX0 : Curve3Pool.xpChk ⟨(Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0).toNat, (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1).toNat,
      (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2).toNat⟩ = some xa)
    (hD0 : Blanc.StableSwapNewton.getDChk xa.get amp 1 = some v0)
    (hXb : Curve3Pool.xpChk (alNewW (initSevm msg) ((initDevm msg).getStor (initSevm msg).currentTarget) B1 B2) = some xb)
    (hD1 : Blanc.StableSwapNewton.getDChk xb.get amp 1 = some v1) (hlt : Nat.toB256 v0 < Nat.toB256 v1)
    (i0 : Curve3Pool.RliFeeIter (Curve3Pool.cwFee (((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.feeSlot)) (((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.adminFeeSlot)
      (Nat.toB256 v0) (Nat.toB256 v1) (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0) (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor (initSevm msg).currentTarget)) B1 B2 0) f0 s0 x0)
    (i1 : Curve3Pool.RliFeeIter (Curve3Pool.cwFee (((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.feeSlot)) (((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.adminFeeSlot)
      (Nat.toB256 v0) (Nat.toB256 v1) (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1) (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor (initSevm msg).currentTarget)) B1 B2 1) f1 s1 x1)
    (i2 : Curve3Pool.RliFeeIter (Curve3Pool.cwFee (((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.feeSlot)) (((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.adminFeeSlot)
      (Nat.toB256 v0) (Nat.toB256 v1) (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2) (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor (initSevm msg).currentTarget)) B1 B2 2) f2 s2 x2)
    (hXc : Curve3Pool.xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc) (hD2 : Blanc.StableSwapNewton.getDChk xc.get amp 1 = some v2)
    (hge : ¬ Nat.toB256 v2 < Nat.toB256 v0) (hmul : B256.Nofm T (Nat.toB256 v2 - Nat.toB256 v0)) (hD00 : Nat.toB256 v0 ≠ 0)
    (hslip : ¬ alMintW T (Nat.toB256 v0) (Nat.toB256 v2) < Sevm.dataWord (initSevm msg) (Bytes.toB256 [0x64]))
    (hadd : ¬ T + alMintW T (Nat.toB256 v0) (Nat.toB256 v2) < T)
    (hfront : 6000 ≤ alFrontCost (initSevm msg) (initDevm msg) P amp) {R : Nat} (hR : 100000 + 5 * U ≤ R)
    (hG : R + alExactCost1 (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 < 2 ^ 256) :
    ∃ post, exec (initEvm (msg.withGas (R + alExactCost1 (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) = .ok post ∧ post.error = none ∧ post.gasLeft = R ∧
      post.refundCounter = alRefund1 (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 ∧ W 4 post ∧
      ∀ x, (post.getStor msg.currentTarget).get x = (alUnlock (alStor3 (alLocked1 ((initDevm msg).getStor (initSevm msg).currentTarget)) s0 s1 s2)).get x := by
  obtain ⟨F, hF⟩ : ∃ F, F = R + alExactCost1 (initSevm msg) (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 := ⟨_, rfl⟩
  have hcost := Curve3Pool.alExactCost1_withStaticGas (initSevm msg) F (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2
  have hrf := Curve3Pool.alRefund1_withStaticGas (initSevm msg) F (initDevm msg) P amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2
  have hfrontF := Curve3Pool.alFrontCost_withStaticGas (initSevm msg) F (initDevm msg) P amp
  have hr := rx_al_frame1_exact (sevm := {initSevm msg with gas := F}) (pre := initDevm msg) (s := s) (U := U) (amp := amp) (T := T) (B1 := B1) (B2 := B2) (m := 0) (R := R) (W := W)
    P hfork hstatic hdep hlen hcd hsel (hid.withStaticGas F) (fun j hj => (hWc j hj).withStaticGas F) hWb ha hlock hval hkill hA hmf
    (hP.withStaticGas F) hskip hT hnz hsub a0 a1 a2 hX0 hD0 hXb hD1 hlt i0 i1 i2 hXc hD2 hge hmul hD00 hslip hadd hR (by rw [hfrontF]; exact hfront) (by rw [hcost]; exact hG)
  rw [hcost, hrf, ← hF] at hr
  obtain ⟨post, hx, herr, hg, hrfp, hWp, hst⟩ := add_end hcode hfork hr
  exact ⟨post, by rw [← hF]; exact hx, herr, hg, hrfp, hWp, hst⟩

/-! ## The message -/

section Core

variable {msg : Msg} {am : V3} {minMint minted : Nat} {stored : V3}

/-- The world chain's closure over the frame. -/
theorem add_wClosed {s : Sevm} {p : Devm} {σa σm : Stor} {c : Adr} (hC : RealCoins s p) (hne : s.currentTarget ≠ c) :
    ∀ j, j ≤ 4 → WClosed s (alC3W c σa σm (addV s p) j) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
  all_goals exact Blanc.Composition.Curve3Pool3CrvHeadlines.c3With_wClosed hne (addV_wClosed hC _)

/-- A zero amount's pull is skipped by the chain. -/
theorem add_skip {s : Sevm} {p : Devm} {σa σm : Stor} {c : Adr} :
    ∀ k, k < 3 → alAmt s k = 0 → ∀ b, alC3W c σa σm (addV s p) k b → alC3W c σa σm (addV s p) (k + 1) b := by
  intro k hk hz b hb
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact ⟨hb.1, addV_skip (k := 0) hz hb.2⟩
  · exact ⟨hb.1, addV_skip (k := 1) hz hb.2⟩
  · exact ⟨hb.1, addV_skip (k := 2) hz hb.2⟩

/-- `addCalldata`'s amounts and minimum, as the walk and the model read them. -/
theorem add_args (h : (initSevm msg).data = addCalldata am minMint) (hN : ∀ k, am.get k < 2 ^ 256) (hmm : minMint < 2 ^ 256) :
    (∀ k : Fin 3, alAmt (initSevm msg) k.val = Nat.toB256 (am.get k)) ∧ argV3 (initSevm msg) 0 = am ∧ Curve3Pool.arg (initSevm msg) 3 = minMint := by
  obtain ⟨w0, w1, w2, w3⟩ := add_words h
  have hN0 : am.v0 < 2 ^ 256 := hN 0
  have hN1 : am.v1 < 2 ^ 256 := hN 1
  have hN2 : am.v2 < 2 ^ 256 := hN 2
  refine ⟨fun k => ?_, ?_, ?_⟩
  · match k with
    | 0 =>
      show Sevm.dataWord _ (Bytes.toB256 [0x20] * Nat.toB256 0 + Bytes.toB256 [4]) = _
      rw [show Bytes.toB256 [0x20] * Nat.toB256 0 + Bytes.toB256 [4] = 4 by decide]
      exact w0
    | 1 =>
      show Sevm.dataWord _ (Bytes.toB256 [0x20] * Nat.toB256 1 + Bytes.toB256 [4]) = _
      rw [show Bytes.toB256 [0x20] * Nat.toB256 1 + Bytes.toB256 [4] = 36 by decide]
      exact w1
    | 2 =>
      show Sevm.dataWord _ (Bytes.toB256 [0x20] * Nat.toB256 2 + Bytes.toB256 [4]) = _
      rw [show Bytes.toB256 [0x20] * Nat.toB256 2 + Bytes.toB256 [4] = 68 by decide]
      exact w2
  · have a0 : Curve3Pool.arg (initSevm msg) 0 = am.v0 := by
      show (Sevm.dataWord (initSevm msg) (32 * 0 + 4)).toNat = _
      rw [show (32 * 0 + 4 : B256) = 4 by decide, w0, B256.toNat_toB256_of_lt hN0]
    have a1 : Curve3Pool.arg (initSevm msg) (0 + 1) = am.v1 := by
      show (Sevm.dataWord (initSevm msg) (32 * (0 + 1) + 4)).toNat = _
      rw [show (32 * (0 + 1) + 4 : B256) = 36 by decide, w1, B256.toNat_toB256_of_lt hN1]
    have a2 : Curve3Pool.arg (initSevm msg) (0 + 2) = am.v2 := by
      show (Sevm.dataWord (initSevm msg) (32 * (0 + 2) + 4)).toNat = _
      rw [show (32 * (0 + 2) + 4 : B256) = 68 by decide, w2, B256.toNat_toB256_of_lt hN2]
    show (⟨Curve3Pool.arg (initSevm msg) 0, Curve3Pool.arg (initSevm msg) (0 + 1), Curve3Pool.arg (initSevm msg) (0 + 2)⟩ : V3) = am
    rw [a0, a1, a2]
  · show (Sevm.dataWord (initSevm msg) (32 * 3 + 4)).toNat = _
    rw [show (32 * 3 + 4 : B256) = 100 by decide, w3, B256.toNat_toB256_of_lt hmm]

/-- The model's `pullAdd` at the premised environment. -/
theorem add_pullAdd {s : Curve3Pool.State} {env : Env} {T : Nat} (hb : books w = s.balances)
    (hpi : ∀ k : Fin 3, 0 < am.get k → Curve3Pool.pullIn env k (am.get k) = some (netOf w k (am.get k)))
    (hT : T = 0 → ∀ k, 0 < am.get k) (hfit : ∀ k, recorded w k + netOf w k (am.get k) < 2 ^ 256) (k : Fin 3) :
    Curve3Pool.pullAdd env T s.balances am k = some (recorded w k + netOf w k (am.get k)) := by
  have hrec : s.balances.get k = recorded w k := by
    rw [← hb]
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  have hadd : ∀ c, recorded w k + c < 2 ^ 256 → Blanc.StableSwapNewton.chkAdd (s.balances.get k) c = some (recorded w k + c) := fun c hc => by
    rw [hrec]; exact ite_eq_left hc
  by_cases hz : 0 < am.get k
  · unfold Curve3Pool.pullAdd
    simp only [Option.bind_eq_bind, gt_iff_lt, hz, ↓reduceIte, Option.bind_some, hpi k hz]
    split
    · rw [show Curve3Pool.req True = some () from ite_eq_left trivial]
      exact hadd _ (hfit k)
    · exact hadd _ (hfit k)
  · have h0 : am.get k = 0 := by omega
    have hT0 : T ≠ 0 := fun e => hz (hT e k)
    have hf := hfit k
    rw [h0, netOf_zero] at hf
    unfold Curve3Pool.pullAdd
    simp only [hT0, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, gt_iff_lt, hz, h0, netOf_zero, Nat.lt_irrefl]
    exact hadd _ hf

/-- **The message under the moment's facts.** -/
theorem add_core (mf : MomentFacts w) (mk : ExitMarked w) (e : Asked msg w E (addCalldata am minMint))
    (req : AddRequest w E msg.benv.stat.time.toNat am minMint minted stored) (hfee : word w pool Curve3Pool.feeSlot ≤ feeDen) :
    ∃ cost refund, cost ≤ addCostBound ∧ MsgDoes msg liquidityRoom cost refund (fun st => AddPaid w st E am minted stored) := by
  obtain ⟨s, hck0, hck, hco, hto, hC, hcode, hid⟩ := asked_facts mf mk e
  have ht : msg.currentTarget = pool := e.entry.named.1
  have hTt : (initSevm msg).currentTarget = pool := ht
  have hTc : (initSevm msg).caller = E := e.entry.named.2.1
  have hopen := e.coinsOpen
  have hE0 : E ≠ 0 := e.nonzero
  have hfork : ShanghaiOnwards (initSevm msg).benvStat.fork := e.entry.plain.2.2.2
  have hH : HistFork (initSevm msg).benvStat.fork := hfork.histFork
  have hdata : (initSevm msg).data = addCalldata am minMint := e.data
  have hstatic : (initSevm msg).isStatic = false := e.entry.plain.2.1
  have hdep : 2 ≤ (initSevm msg).depth := e.entry.plain.2.2.1
  have hdep0 : (initSevm msg).depth ≠ 0 := by omega
  have hval : (initSevm msg).value = 0 := e.entry.plain.1
  have hstor : ∀ x ∈ parties w, (initDevm msg).getStor x = w.getStor x := fun x hx => congrArg Acct.stor (e.entry.world x hx).1
  have hσ : (initDevm msg).getStor (initSevm msg).currentTarget = w.getStor pool := by
    rw [hTt]; exact hstor pool List.mem_cons_self
  have hc3S : (initDevm msg).getStor c3 = w.getStor c3 := hstor _ (by simp only [parties, List.mem_cons, true_or, or_true])
  have hcoinS : ∀ k : Fin 3, (initDevm msg).getStor (coinAt k) = w.getStor (coinAt k) := fun k => hstor _ (by
    match k with
    | 0 => simp only [coinAt, parties, List.mem_cons, true_or, or_true]
    | 1 => simp only [coinAt, parties, List.mem_cons, true_or, or_true]
    | 2 => simp only [coinAt, parties, List.mem_cons, true_or, or_true])
  obtain ⟨hLive, ⟨hheld, hcr, hfees, hsrc⟩, hall, ⟨amp, hamp, hout⟩, ⟨⟨hmin, hpos⟩, hfit⟩, hap⟩ := req
  have hN : ∀ k, am.get k < 2 ^ 256 := fun k => Nat.lt_of_le_of_lt (hheld k) coinHeld_lt
  have hmm : minMint < 2 ^ 256 := by have := hfit.1; omega
  obtain ⟨hamW, hargs, harg3⟩ := add_args (msg := msg) hdata hN hmm
  have hlen : (initSevm msg).data.length = 132 := by rw [hdata]; exact addCalldata_length
  have hsel := add_selector hdata
  obtain ⟨T, hTdef⟩ : ∃ T, T = (w.getStor c3).get Curve3Crv.vySupplySlot := ⟨_, rfl⟩
  have hTn : T.toNat = supply w := by rw [hTdef]; rfl
  have hT3 : (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))).get Curve3Crv.vySupplySlot = T := by
    rw [hto, hc3S, hTdef]
  have hS3 : Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)) = w.getStor c3 := by rw [hto, hc3S]
  have hkill : s.isKilled = false := by
    have h0 : (w.getStor pool).get Curve3Pool.isKilledSlot = 0 := B256.toNat_inj _ _ hLive
    have h1 := hck0.abs.isKilled
    rw [h0] at h1
    cases hs : s.isKilled with
    | false => rfl
    | true => rw [hs] at h1; exact absurd h1 (by decide)
  have hkillW : ((initDevm msg).getStor (initSevm msg).currentTarget).get Curve3Pool.isKilledSlot = 0 := by
    rw [hσ]; exact B256.toNat_inj _ _ hLive
  have hpf : ∀ k : Fin 3, alAmt (initSevm msg) k.val ≠ 0 → PullFitsK k ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k))
      (initSevm msg).caller (initSevm msg).currentTarget (alAmt (initSevm msg) k.val) := fun k _ => by
    rw [hco k, hcoinS, hTt, hTc, hamW k]
    exact pull_fits hopen hE0 hap.toSwapApart hsrc k (hN k) (hheld k) (hall k) (hcr k) (fun h => by rw [h]; exact hfees)
  have hP2 := usdt_pulled_get (w := w) (E := E) (v := am.get 2) hap.toSwapApart (hN 2) hfees.2.2 hfees.1 (hcr 2)
  have hcE : pulledK 2 ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2)) (initSevm msg).caller (initSevm msg).currentTarget (alAmt (initSevm msg) 2) =
      pulledK 2 (w.getStor usdt) E pool (Nat.toB256 (am.get 2)) := by
    rw [hco 2, show coinAt 2 = usdt from rfl, show (initDevm msg).getStor usdt = w.getStor usdt from hcoinS 2, hTt, hTc,
      show alAmt (initSevm msg) 2 = Nat.toB256 (am.get 2) from hamW 2]
  have hlive : alAmt (initSevm msg) 2 ≠ 0 → Usdt.NotDeprecated (pulledK 2 ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2)) (initSevm msg).caller
      (initSevm msg).currentTarget (alAmt (initSevm msg) 2)) := fun _ => by
    rw [hcE]
    show Usdt.flag20 _ = 0
    rw [hP2.2]
    exact mk.usdtLive
  have hml : minted < 2 ^ 256 := by have := hfit.1; omega
  have hmn : (Nat.toB256 minted).toNat = minted := B256.toNat_toB256_of_lt hml
  have hmintF : MintFits (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (initSevm msg).currentTarget (initSevm msg).caller.toB256 (Nat.toB256 minted) := by
    have hne : Curve3Crv.vySupplySlot ≠ mapSlot 3 E.toB256 := Ne.symm hap.c3
    rw [hS3, hTt, hTc]
    refine ⟨mk.minter, fun h => hE0 (by rw [← toAdr_toB256 E, h]; rfl), ?_, ?_⟩
    · rw [hmn]; exact hfit.1
    · rw [Stor.get_set_ne _ hne, hmn]; exact hfit.2
  have hprecT : ¬ (initSevm msg).benvStat.rules.isPrecomp (tokOf (initSevm msg) (initDevm msg)) := by
    rw [hto]
    have := (Curve3PoolJointRoot.parties_not_precompile hH).2
    rwa [show Curve3Pool.adrOf Curve3Pool.Creation.tokenN = c3 by decide +kernel] at this
  have hneT : (initSevm msg).currentTarget ≠ tokOf (initSevm msg) (initDevm msg) := by rw [hTt, hto]; decide
  have hPrem := add_premises (T := T) (mint := Nat.toB256 minted) hfork hstatic hdep hC hneT hprecT hT3 hmintF hpf hlive
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = addB1 (initSevm msg) (initDevm msg) := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = addB2 (initSevm msg) (initDevm msg) := ⟨_, rfl⟩
  rw [← hB1, ← hB2] at hPrem
  have hwB1 : B1.toNat = word w usdt (Usdt.balSlot pool) := by
    rw [hB1]
    show ((((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2))).get (Usdt.balSlot (initSevm msg).currentTarget)).toNat = _
    rw [hco 2, show coinAt 2 = usdt from rfl, show (initDevm msg).getStor usdt = w.getStor usdt from hcoinS 2, hTt]
    rfl
  have hwB2 : B2.toNat = word w usdt (Usdt.balSlot pool) + netOf w 2 (am.get 2) := by
    rw [hB2]
    show ((pulledK 2 ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2)) (initSevm msg).caller (initSevm msg).currentTarget (alAmt (initSevm msg) 2)).get
      (Usdt.balSlot (initSevm msg).currentTarget)).toNat = _
    rw [hcE, hTt]
    exact hP2.1
  obtain ⟨env, henv⟩ : ∃ env, env = alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat := ⟨_, rfl⟩
  have hbk : books w = s.balances := books_of_abstracts hck0.abs
  have hcredit : ∀ k, recorded w k + netOf w k (am.get k) < 2 ^ 256 := fun k => books_credit_lt (mk.covered k) (hcr k)
  have hpi : ∀ k : Fin 3, 0 < am.get k → Curve3Pool.pullIn env k (am.get k) = some (netOf w k (am.get k)) := fun k _ => by
    rw [henv]
    by_cases hk2 : k = 2
    · subst hk2
      refine (Blanc.Lift.Curve3Pool.alEnvW_pullIn2 _).trans ?_
      rw [hwB1, hwB2]
      unfold Blanc.StableSwapNewton.chkSub
      rw [ite_eq_left (by omega)]
      congr 1
      omega
    · have hn : netOf w k (am.get k) = am.get k := if_neg hk2
      rw [hn]
      exact Blanc.Lift.Curve3Pool.alEnvW_pullIn01 hk2 _
  have hpull := add_pullAdd (am := am) (T := supply w) hbk hpi hpos hcredit
  obtain ⟨o, hal, hobal, homint⟩ := add_accepts (e := env) (minMint := minMint) hck0.abs hkill hfee
    (by rw [henv, ← ampAt_of_abstracts hck0.abs]; exact hamp) (by rw [henv, ← hTn]; rfl) (by rw [henv]; rfl) hpull hout hmin hfit.1
    (fun h => hpos h 0)
  have hal' : Curve3Pool.addLiquidity s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (argV3 (initSevm msg) 0) (Curve3Pool.arg (initSevm msg) 3) = some o := by
    rw [hargs, harg3, ← henv]; exact hal
  obtain ⟨ampW, v1, xb, mint, T', -, hampW, -, -, hmf, t0, sub, a0, a1, a2, hxb, hD1, hminW, hT', hbr⟩ :=
    Blanc.Lift.Curve3Pool.al_words_common (sevm := initSevm msg) (σ := (initDevm msg).getStor (initSevm msg).currentTarget) (T := T) (B1 := B1) (B2 := B2) hck.abs hal'
  have hfin : ∀ (post : Devm) (s0 s1 s2 : B256), stored = ⟨s0.toNat, s1.toNat, s2.toNat⟩ →
      C3With (tokOf (initSevm msg) (initDevm msg)) (mintStor (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (initSevm msg).caller.toB256 (Nat.toB256 minted))
        (addV (initSevm msg) (initDevm msg) 3) post →
      (∀ x, (post.getStor msg.currentTarget).get x = (alUnlock (alStor3 (alLocked1 ((initDevm msg).getStor (initSevm msg).currentTarget)) s0 s1 s2)).get x) →
      AddPaid w post.state E am minted stored := by
    intro post s0 s1 s2 hs hW hst
    have hLed : ∀ k : Fin 3, post.state.getStor (coinAt k) = addLedger (initSevm msg) (initDevm msg) 3 k := fun k => by
      rw [← hco k]; exact hW.2.2 k
    refine add_paid hopen hap hheld hcr hfees (fun k hz => ?_) (fun k hz => ?_) ?_ (fun k => ?_) hfit
    · rw [hLed k]
      unfold addLedger
      rw [if_neg (fun h => h.2 (by rw [hamW k, hz]; rfl)), hco k, hcoinS]
    · have hane : alAmt (initSevm msg) k.val ≠ 0 := by
        rw [hamW k]
        intro h0
        have := congrArg B256.toNat h0
        rw [B256.toNat_toB256_of_lt (hN k), B256.toNat_zero] at this
        exact hz this
      rw [hLed k]
      unfold addLedger
      rw [if_pos ⟨k.isLt, hane⟩, hco k, hcoinS, hTt, hTc, hamW k]
      exact add_pulled_eq hopen hap.toSwapApart k (hN k) (hheld k) (hall k) (hcr k)
    · have h := hW.1.2
      rw [hS3, hTc, hto] at h
      exact h
    · have h : ∀ x, (post.getStor pool).get x = (alUnlock (alStor3 (alLocked1 ((initDevm msg).getStor (initSevm msg).currentTarget)) s0 s1 s2)).get x := fun x => by
        rw [← ht]; exact hst x
      exact add_books hs h k
  have hWc := add_wClosed (s := initSevm msg) (p := initDevm msg)
    (σa := Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
    (σm := mintStor (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (initSevm msg).caller.toB256 (Nat.toB256 minted)) hC hneT
  have hWb : alC3W (tokOf (initSevm msg) (initDevm msg)) (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
      (mintStor (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (initSevm msg).caller.toB256 (Nat.toB256 minted)) (addV (initSevm msg) (initDevm msg)) 0 (initDevm msg) :=
    ⟨⟨by rw [hto]; rw [show (initDevm msg).getCode c3 = w.getCode c3 from congrArg Acct.code (e.entry.world c3 (by simp only [parties, List.mem_cons, true_or, or_true])).1]; exact mf.c3Code, rfl⟩, addV_entry⟩
  have hfront0 : ∀ a, 6000 ≤ alFrontCost (initSevm msg) (initDevm msg) (addCalls (initSevm msg) (initDevm msg)) a := fun a => by
    have h := add_front (asked_stand e hap.toSwapApart.toCoinsApart (initSevm msg).gas) hck0.unlocked (addCalls (initSevm msg) (initDevm msg)) a
    rwa [Curve3Pool.alFrontCost_withStaticGas] at h
  have hroom : ∀ R, liquidityRoom ≤ R → 100000 + 5 * 129555 ≤ R := fun R h => by
    have : liquidityRoom = 800000 := rfl
    omega
  have hcdl : (initSevm msg).data.length < 2 ^ 256 := by rw [hlen]; decide
  have hl4 : 4 ≤ (initSevm msg).data.length := by rw [hlen]; decide
  rcases hbr with ⟨hT0, hD1pos, hmv, ho⟩ | ⟨hT0, D0, fees, st, after, D2, x, y, hD0, hlt, hfl, hD2, hx, hy, hm, ho⟩
  · subst hmv
    subst hT0
    obtain ⟨hlt0, hslip, hadd0, -, -⟩ := Blanc.Lift.Curve3Pool.al_words0 (sevm := initSevm msg) hD1 hD1pos hminW hT'
    have hme : mint = minted := by rw [ho] at homint; rw [← homint]; exact Blanc.Lift.Curve3Pool.alMintAmt_eq.symm
    subst hme
    have hse : stored = alNewW (initSevm msg) ((initDevm msg).getStor (initSevm msg).currentTarget) B1 B2 := by rw [ho] at hobal; exact hobal.symm
    refine ⟨Curve3Pool.alExactCost0 (initSevm msg) (initDevm msg) (addCalls (initSevm msg) (initDevm msg)) ampW B1 B2 xb mint,
      (alRefund0 (initSevm msg) (initDevm msg) (addCalls (initSevm msg) (initDevm msg)) ampW B1 B2 xb mint).toNat, al_cost0_le (addCalls_debits _ _) _ _ _ _ _, fun R hR hG => ?_⟩
    obtain ⟨post, hx, herr, hg, hrfp, hWp, hst⟩ := add_run0 (msg := msg) (s := s) (U := 129555) _ hcode hfork hstatic hdep0 hl4 hcdl hsel hid hWc hWb hck.abs hck.unlocked hval hkillW hampW hmf
      hPrem add_skip (t0 rfl) sub a0 a1 a2 hxb hD1 hlt0 hslip hadd0 (hfront0 _) (hroom R hR) hG
    exact ⟨post, hx, herr, hg, by rw [hrfp], hfin post _ _ _ hse hWp hst⟩
  · obtain ⟨xa, xc, v0, v2, f0, f1, f2, s0, s1, s2, x0, x1, x2, hxa, hD0', hlt', i0, i1, i2, hxc, hD2', hge, hmul, hD00, hslip, hadd, hmintv, -, -, hst', hD0e, -⟩ :=
      Blanc.Lift.Curve3Pool.al_words1 (sevm := initSevm msg) hck.abs hD1 hD0 hlt hfl hD2 hx hy hm hminW hT'
    subst hD0e
    have hme : mint = minted := by rw [ho] at homint; rw [← homint]; exact Blanc.Lift.Curve3Pool.alMintAmt_eq.symm
    subst hme
    have hse : stored = ⟨s0.toNat, s1.toNat, s2.toNat⟩ := by rw [ho] at hobal; rw [← hobal]; exact hst'
    have hmw : alMintW T (Nat.toB256 D0) (Nat.toB256 v2) = Nat.toB256 mint := by rw [hmintv, toB256_toNat]
    have hP1 : ALExactPremises (initSevm msg) ((initDevm msg).getStor (initSevm msg).currentTarget) T B1 B2 (alMintW T (Nat.toB256 D0) (Nat.toB256 v2))
        (alC3W (tokOf (initSevm msg) (initDevm msg)) (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
          (mintStor (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (initSevm msg).caller.toB256 (Nat.toB256 mint)) (addV (initSevm msg) (initDevm msg)))
        129555 (addCalls (initSevm msg) (initDevm msg)) := by
      rw [hmw]; exact hPrem
    have hbal : s.balances = ⟨(Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0).toNat,
        (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1).toNat,
        (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2).toNat⟩ :=
      (Curve3Pool.V3.ext_get fun k => by rw [← Curve3Pool.ex_w3_nat]; exact Curve3Pool.ex_bal_nat hck.abs k).symm
    have hnz := Curve3Pool.al_amounts_nz (sevm := initSevm msg) (pre := initDevm msg) hbal hxa hD0' hxb hD1 hlt
    refine ⟨Curve3Pool.alExactCost1 (initSevm msg) (initDevm msg) (addCalls (initSevm msg) (initDevm msg)) ampW T B1 B2 xa xb xc D0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2,
      (alRefund1 (initSevm msg) (initDevm msg) (addCalls (initSevm msg) (initDevm msg)) ampW T B1 B2 xa xb xc D0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2).toNat, al_cost1_le (addCalls_debits _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, fun R hR hG => ?_⟩
    obtain ⟨post, hx', herr, hg, hrfp, hWp, hst⟩ := add_run1 (msg := msg) (s := s) (U := 129555) _ hcode hfork hstatic hdep0 hl4 hcdl hsel hid hWc hWb hck.abs hck.unlocked hval hkillW hampW hmf
      hP1 add_skip hT0 hnz sub a0 a1 a2 hxa hD0' hxb hD1 hlt' i0 i1 i2 hxc hD2' hge hmul hD00 hslip hadd (hfront0 _) (hroom R hR) hG
    exact ⟨post, hx', herr, hg, by rw [hrfp], hfin post _ _ _ hse hWp hst⟩

end Core

/-- **`add_liquidity_message`, with its named cost bounded**: at most `addCostBound`, below EIP-7825's per-transaction cap. -/
theorem add_liquidity_message_bounded {d : Deployment} (m : Moment d) (A : Assumes d m.through) {msg : Msg} {E : Adr} {am : V3} {minMint minted : Nat} {stored : V3}
    (ask : Asked msg m.world E (addCalldata am minMint))
    (req : AddRequest m.world E msg.benv.stat.time.toNat am minMint minted stored) :
    ∃ cost refund, cost ≤ addCostBound ∧ MsgDoes msg liquidityRoom cost refund (fun st => AddPaid m.world st E am minted stored) :=
  add_core (m.facts A) (m.marked A ask.coinsOpen.usdcParties.1) ask req (m.feesWithin A).1

/-- **`add_liquidity_message`.** -/
theorem add_liquidity_message_holds : add_liquidity_message := by
  intro d m A msg E am minMint minted stored ask req
  obtain ⟨cost, refund, hc, h⟩ := add_liquidity_message_bounded m A ask req
  exact ⟨cost, refund, Nat.le_trans hc addCostBound_le_cap, h⟩

end Blanc.Composition.Curve3PoolPublic
