import Blanc.Composition.Curve3PoolRemoveMessage
import Blanc.Composition.Curve3PoolSwapRequest

/-!
# `one_coin_message`

`oneCoin_accepts`: the model's `remove_liquidity_one_coin` from `oneCoinOutcome`, whose checks are the contract's. `one_coin_run`:
the frame's run from the moment's facts, with the chain's cost and refund fixed before the residual gas.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.StableSwapNewton
open Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3With C3At C3Blind c3With_wClosed)
open Blanc.Composition.Curve3Pool3CrvExactAssembly (ocC3Calls ocExactPremises_c3crv tokW)
open Blanc.Composition.Curve3Pool3CrvInstance (coinOf tokOf C3Entry c3At_keep')
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins Pin pin_keep PushFitsK)

/-! ## The calldata -/

section Calldata

variable {e : Sevm} {a minDy : Nat} {i : Fin 3}

theorem oneCoinCalldata_length : (oneCoinCalldata a i minDy).length = 100 := by
  simp only [oneCoinCalldata, Curve3Pool.word, List.length_append, B256.length_toBytes, abiSelectorBytes_length]

/-- `oneCoinCalldata`'s selector. -/
theorem oneCoin_selector (h : e.data = oneCoinCalldata a i minDy) : Sevm.selector e = selRemoveLiquidityOneCoin := by
  refine selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
    (tail := Curve3Pool.word a ++ Curve3Pool.word i ++ Curve3Pool.word minDy) ?_
  rw [h]
  simp only [oneCoinCalldata, List.append_assoc]

/-- `oneCoinCalldata`'s three words. -/
theorem oneCoin_words (h : e.data = oneCoinCalldata a i minDy) :
    Sevm.dataWord e 4 = Nat.toB256 a ∧ Sevm.dataWord e 36 = Nat.toB256 i ∧ Sevm.dataWord e 68 = Nat.toB256 minDy := by
  have l4 := abiSelectorBytes_length selRemoveLiquidityOneCoin
  refine ⟨?_, ?_, ?_⟩
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes selRemoveLiquidityOneCoin)
      (rest := Curve3Pool.word i ++ Curve3Pool.word minDy) ?_ (by rw [l4]; rfl)
    rw [h]; simp only [oneCoinCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes selRemoveLiquidityOneCoin ++ Curve3Pool.word a)
      (rest := Curve3Pool.word minDy) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [oneCoinCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append
      (pre := abiSelectorBytes selRemoveLiquidityOneCoin ++ Curve3Pool.word a ++ Curve3Pool.word i)
      (rest := []) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [oneCoinCalldata, Curve3Pool.word, List.append_assoc, List.append_nil]

end Calldata

/-! ## The model -/

theorem bind_of {α β : Type} {x : Option α} {a : α} {f : α → Option β} {b : β} (h : x = some a) (k : f a = some b) :
    (x >>= f) = some b := by
  subst h; exact k

/-- `oneCoinOutcome`'s steps. -/
theorem oneCoinOutcome_parts {w : Jaune.State} {amp a dy admin : Nat} {i : Fin 3}
    (h : oneCoinOutcome w amp a i = some (dy, admin)) :
    ∃ D0 m q D1 newY d dy0 r y2 e1 e2 c p,
      invariant w amp = some D0 ∧ chkMul a D0 = some m ∧ chkDiv m (supply w) = some q ∧ chkSub D0 q = some D1 ∧
      getYDChk amp i (scaled w) D1 = some newY ∧ chkSub (scaled w i) newY = some d ∧
      chkDiv d (Curve3Pool.precMul.get i) = some dy0 ∧
      oneCoinReduced w i D0 D1 newY (word w pool Curve3Pool.feeSlot * 3 / 8) = some r ∧
      getYDChk amp i r.get D1 = some y2 ∧ chkSub (r.get i) y2 = some e1 ∧ chkSub e1 1 = some e2 ∧
      chkDiv e2 (Curve3Pool.precMul.get i) = some dy ∧ chkSub dy0 dy = some c ∧
      chkMul c (word w pool Curve3Pool.adminFeeSlot) = some p ∧ chkDiv p feeDen = some admin := by
  unfold oneCoinOutcome at h
  obtain ⟨D0, h0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨m, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨q, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨D1, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨newY, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨d, h5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dy0, h6, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, h7, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y2, h8, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e1, h9, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e2, h10, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dyv, h11, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, h12, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p, h13, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨adv, h14, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨D0, m, q, D1, newY, d, dy0, r, y2, e1, e2, c, p, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- **The model accepts what `oneCoinOutcome` computes**, and the books cover what leaves. -/
theorem oneCoin_accepts {w : Jaune.State} {s : Curve3Pool.State} {e : Env} {amp a dy admin minDy : Nat} {i : Fin 3}
    (hab : Abstracts (w.getStor pool) s) (hk : s.isKilled = false) (hA : aChk s e.time = some amp)
    (hT : e.supply = some (supply w)) (hb : e.burnOk = true) (hp : (e.coin i).pushOk = true)
    (hfee : word w pool Curve3Pool.feeSlot ≤ feeDen) (hadm : word w pool Curve3Pool.adminFeeSlot ≤ feeDen)
    (hmin : minDy ≤ dy) (ho : oneCoinOutcome w amp a i = some (dy, admin)) :
    dy + admin ≤ recorded w i ∧
      removeLiquidityOneCoin s e a i minDy = some ⟨{ s with balances := s.balances.set i (recorded w i - (dy + admin)) }, none,
        [.removeLiquidityOne e.caller a dy], [.burn e.caller a, .push i e.caller dy]⟩ := by
  obtain ⟨D0, m, q, D1, newY, d, dy0, r, y2, e1, e2, c, p, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    oneCoinOutcome_parts ho
  have hbk := books_of_abstracts hab
  have e_fee : s.fee = word w pool Curve3Pool.feeSlot := (hab.fee).symm
  have e_adm : s.adminFee = word w pool Curve3Pool.adminFeeSlot := (hab.adminFee).symm
  have e_rec : s.balances.get i = recorded w i := (recorded_of_abstracts hab i).symm
  -- `_xp`
  rw [invariant, hbk] at h0
  obtain ⟨xp, hxp, hD0⟩ := bind_some h0
  have hxg : xp.get = scaled w := by
    rw [xpChk_some hxp]; unfold scaled; rw [hbk]
  rw [hxg] at hD0
  -- the fee
  have hF : feeAdj s = some (word w pool Curve3Pool.feeSlot * 3 / 8) := by
    unfold feeAdj
    rw [e_fee]
    have hm3 : word w pool Curve3Pool.feeSlot * 3 < wordSize := by
      unfold wordSize; have : feeDen = 10 ^ 10 := rfl; omega
    simp only [chkMul, hm3, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, chkDiv]
    rfl
  have hcw : calcWithdrawOne s e a i = some (dy, c) := by
    have h7' := h7
    unfold oneCoinReduced at h7'
    unfold calcWithdrawOne
    exact bind_of hA <| bind_of hF <| bind_of hT <| bind_of hxp <| bind_of (by rw [hxg]; exact hD0) <| bind_of h1 <| bind_of h2 <|
      bind_of h3 <| bind_of (by rw [hxg]; exact h4) <| bind_of (by rw [hxg]; exact h5) <| bind_of h6 <|
      bind_of (by rw [hxg]; exact h7') <| bind_of h8 <| bind_of h9 <| bind_of h10 <| bind_of h11 <| bind_of h12 rfl
  -- what leaves
  have hsc : scaled w i = Curve3Pool.precMul.get i * recorded w i := by
    show Curve3Pool.xpOf (books w) i = _
    unfold Curve3Pool.xpOf books recorded
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  have hprec := precMul_pos i
  have hdl : dy0 ≤ recorded w i := by
    rw [ex_chkDiv_eq h6, chkSub_eq' h5]
    refine Nat.le_trans (Nat.div_le_div_right (Nat.sub_le _ _)) ?_
    rw [hsc, Nat.mul_div_cancel_left _ hprec]
  have hc : c = dy0 - dy := chkSub_eq' h12
  have hdy0 : dy ≤ dy0 := by
    unfold chkSub at h12; split at h12
    · assumption
    · cases h12
  have hadmin : admin = c * word w pool Curve3Pool.adminFeeSlot / feeDen := by
    rw [ex_chkDiv_eq h14, ex_chkMul_eq h13]
  have hac : admin ≤ c := by
    rw [hadmin]
    refine Nat.div_le_of_le_mul ?_
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ hadm
  have htake : dy + admin ≤ recorded w i := by omega
  have hlt : recorded w i < 2 ^ 256 := word_lt _ _
  refine ⟨htake, ?_⟩
  unfold removeLiquidityOneCoin req
  have hmul : chkMul c s.adminFee = some p := by rw [e_adm]; exact h13
  have hadd : chkAdd dy admin = some (dy + admin) := by
    unfold chkAdd wordSize
    exact ite_eq_left (by omega)
  have hsub : chkSub (s.balances.get i) (dy + admin) = some (recorded w i - (dy + admin)) := by
    rw [e_rec]; unfold chkSub; exact ite_eq_left htake
  simp only [Option.bind_eq_bind, hk, ↓reduceIte, hcw, Option.bind_some, hmul, h14, hadd, hsub, hb, hp, hmin, ge_iff_le]


/-! ## The frame -/

/-- The chain's end ignores the frame's static initial gas. -/
theorem ocEnd_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (P : OCExactCalls) (T : B256) (amp : Nat)
    (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) :
    ocEnd {sevm with gas := F} pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2 = ocEnd sevm pre P T amp x0 x1 x2 D0 y r0 r1 r2 y2 := by
  simp only [ocEnd, ocSupNext, ocCwMem, ocBurnNext, ocPushNext, ocSupBase, ocSupMem, ocM1, ocσ1, ocCwBase, ocDy, ocFee, ocBurnIn,
    ocBurnMem, ocPushIn, ocAmt, ocI, dataWord_withStaticGas, afterSload_withStaticGas, rawTailBaseNext_withStaticGas,
    aBase_withStaticGas, ocPreBase_withStaticGas, ocPreMem_withStaticGas, cwSupBase_withStaticGas, cwAMem_withStaticGas,
    ocBurnBase_withStaticGas, ocP1Mem_withStaticGas, ocPushMem_withStaticGas, ocPushI2_withStaticGas, xpBase_withStaticGas]

section Error

variable (sevm : Sevm) (b : Devm)

theorem identityCallNext_error (S : List B256) (M : Mem) (ii is oi os : B256) :
    (identityCallNext sevm b S M ii is oi os).error = b.error := rfl

theorem ocPreBase_error : (ocPreBase sevm b).error = b.error := by
  unfold ocPreBase
  simp only [afterSload_error, afterSstore_error]

theorem aBase_error : (aBase sevm b).error = b.error := by
  unfold aBase
  split <;> simp only [afterSload_error]

theorem xpBase_error : (xpBase sevm b).error = b.error := by
  unfold xpBase
  simp only [afterSload_error]

theorem cwSupBase_error : (cwSupBase sevm b).error = b.error := by
  unfold cwSupBase
  simp only [afterSload_error]

theorem ocBurnBase_error (σ : Stor) (dy fee : B256) : (ocBurnBase sevm b σ dy fee).error = b.error := by
  unfold ocBurnBase
  simp only [afterSload_error, afterSstore_error]

theorem rawTailBaseNext_error (S : List B256) (M : Mem) (p : VyRawSite) : (rawTailBaseNext sevm b S M p).error = b.error := rfl

end Error

/-- The chain's end has the entry's error. -/
theorem ocEnd_error (sevm : Sevm) (pre : Devm) (T tk : B256) (i : Fin 3) (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) :
    (ocEnd sevm pre (ocC3Calls sevm pre (pushDk sevm tk 0x540 0x5e0 i) (pushNk sevm tk 0x540 0x5e0 i)) T amp x0 x1 x2 D0 y r0 r1 r2 y2).error =
      pre.error := by
  have hpush : ∀ b S M, (pushNk sevm tk 0x540 0x5e0 i b S M).error = b.error := fun b S M => by
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  have hburn : ∀ b S M, ((ocC3Calls sevm pre (pushDk sevm tk 0x540 0x5e0 i) (pushNk sevm tk 0x540 0x5e0 i)).burnNext b S M).error = b.error := fun _ _ _ => rfl
  have hsup : ∀ b S M, ((ocC3Calls sevm pre (pushDk sevm tk 0x540 0x5e0 i) (pushNk sevm tk 0x540 0x5e0 i)).supplyNext b S M).error = b.error := fun _ _ _ => rfl
  simp only [ocEnd, rawTailBaseNext_error, ocPushNext, ocPushIn, ocPushI2, ocPushI1, ocBurnNext, ocBurnIn, ocCwBase, ocSupNext, ocSupBase]
  simp only [show ∀ b S M, (ocC3Calls sevm pre (pushDk sevm tk 0x540 0x5e0 i) (pushNk sevm tk 0x540 0x5e0 i)).pushNext b S M = pushNk sevm tk 0x540 0x5e0 i b S M from fun _ _ _ => rfl,
    hpush, afterSload_error, identityCallNext_error, hburn, ocBurnBase_error, xpBase_error, hsup, cwSupBase_error, aBase_error, ocPreBase_error]

/-- The books after the store and the lock's release. -/
theorem oc_final_bal (σ : Stor) (iw dyw fw : B256) (hi3 : iw.toNat < 3) :
    (((σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])).set (balancesBase + iw)
      (ocBal (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) iw dyw fw)).set
        (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])).get (balancesBase + iw) = ocBal σ iw dyw fw := by
  have hIw : iw = Nat.toB256 iw.toNat := (toB256_toNat _).symm
  have hne : Bytes.toB256 [0xff, 0xff, 0xff] ≠ balancesBase + iw := by
    rw [hIw, lockSlot_lit]; exact bal_ne_lock hi3
  have hadm : Bytes.toB256 [0xff, 0xff, 0xff] ≠ adminFeeSlot := by decide
  rw [Stor.get_set_ne _ hne, Stor.get_set_self]
  simp only [ocBal, Stor.get_set_ne _ hne, Stor.get_set_ne _ hadm]

/-- The one-coin world chain: coin `i` as at the entry, then as its `transfer` leaves it. -/
def ocV (sevm : Sevm) (pre : Devm) (i : Fin 3) (v : B256) : Nat → Devm → Prop
  | 0 => Pin sevm pre i
  | _ => fun b => (∀ a, b.getCode a = pre.getCode a) ∧ b.getStor (coinOf sevm pre i) =
      pushedK i (pre.getStor (coinOf sevm pre i)) sevm.currentTarget sevm.caller v

/-- The one-coin chain's closure and its exact premises with the real coin. -/
theorem oc_premises {sevm : Sevm} {pre : Devm} {T : B256} {i : Fin 3} {v : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : 2 ≤ sevm.depth)
    (hC : RealCoins sevm pre) (hto : tokOf sevm pre = c3) (hne : sevm.currentTarget ≠ c3)
    (htok : ¬ sevm.benvStat.rules.isPrecomp c3)
    (hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
    (hburn : BurnFits (Devm.getStor pre c3) sevm.currentTarget sevm.caller.toB256 (ocAmt sevm))
    (hci : coinSlot i = coinsBase + ocI sevm)
    (hq : PushFitsK i (pre.getStor (coinOf sevm pre i)) sevm.currentTarget sevm.caller v) :
    OCExactPremises sevm pre T v (C3With c3 (Devm.getStor pre c3) (ocV sevm pre i v 0))
      (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (ocV sevm pre i v 0))
      (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (ocV sevm pre i v 1)) 104744
      (ocC3Calls sevm pre (pushDk sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)) 0x540 0x5e0 i)
        (pushNk sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)) 0x540 0x5e0 i)) := by
  have htc : coinOf sevm pre i ≠ c3 := by rw [← hto]; exact hC.tok i
  refine ocExactPremises_c3crv (V := ocV sevm pre i v) hto hne hfork hstatic (by omega) htok (by decide) hT hburn
    (fun _ _ hb hs hc => pin_keep hb (hs _ htc) hc) ?_
  rw [← hci]
  refine pushK_profile i hfork hstatic hdepth hC (by decide) (by decide) hq (fun b hb => hb.2)
    (fun b d R hb hl => ⟨c3At_keep' hb.1 (hl.other _ (Ne.symm htc)) hl.code, fun a => (hl.code a).trans (hb.2.1 a), hl.stor⟩)

/-- **`remove_liquidity_one_coin`'s message under the moment's facts.** -/
theorem one_coin_run {w : Jaune.State} {E : Adr} {msg : Msg} {a minDy dy admin : Nat} {i : Fin 3}
    (mf : MomentFacts w) (mk : ExitMarked w) (hfee : word w pool Curve3Pool.feeSlot ≤ feeDen)
    (hadm : word w pool Curve3Pool.adminFeeSlot ≤ feeDen) (ask : Asked msg w E (oneCoinCalldata a i minDy))
    (req : OneCoinRequest w E msg.benv.stat.time.toNat a i minDy dy admin) :
    MsgDoesAtNamedCost msg (fun st => OneCoinPaid w st E a i dy admin) := by
  have ht : msg.currentTarget = pool := ask.entry.named.1
  have hcaller : msg.caller = E := ask.entry.named.2.1
  have hopen := ask.coinsOpen
  have hE : E ≠ 0 := ask.nonzero
  have hfork : CoveredFork (initSevm msg).benvStat.fork := ask.entry.plain.2.2.2
  have hH : HistFork (initSevm msg).benvStat.fork := hfork.histFork
  have hdata : (initSevm msg).data = oneCoinCalldata a i minDy := ask.data
  have hstatic : (initSevm msg).isStatic = false := ask.entry.plain.2.1
  have hdepth : 2 ≤ (initSevm msg).depth := ask.entry.plain.2.2.1
  have hval : (initSevm msg).value = 0 := ask.entry.plain.1
  have hst : ∀ {x : Adr}, x ∈ parties w → (initDevm msg).getStor x = w.getStor x := fun hx =>
    congrArg Acct.stor (ask.entry.world _ hx).1
  have sP : (initDevm msg).getStor pool = w.getStor pool := hst (by simp only [parties, List.mem_cons, true_or])
  have sC : (initDevm msg).getStor c3 = w.getStor c3 := hst (by simp only [parties, List.mem_cons, true_or, or_true])
  have sK : ∀ k : Fin 3, (initDevm msg).getStor (coinAt k) = w.getStor (coinAt k) := fun k => hst (by
    match k with
    | 0 => simp only [coinAt, parties, List.mem_cons, true_or, or_true]
    | 1 => simp only [coinAt, parties, List.mem_cons, true_or, or_true]
    | 2 => simp only [coinAt, parties, List.mem_cons, true_or, or_true])
  obtain ⟨s, hck0, hck, hco, hto, hC, hcode, hid⟩ := asked_facts mf mk ask
  obtain ⟨amp, hamp, hout⟩ := req.outcome
  obtain ⟨hm0, hsh, hsu⟩ := req.limits
  have hap := req.apart
  obtain ⟨T, hTdef⟩ : ∃ T, T = (w.getStor c3).get Curve3Crv.vySupplySlot := ⟨_, rfl⟩
  have hTn : T.toNat = supply w := by rw [hTdef]; rfl
  have hA : aChk s msg.benv.stat.time.toNat = some amp := by rw [← ampAt_of_abstracts hck0.abs]; exact hamp
  have hk : s.isKilled = false := by
    have h1 := hck0.abs.isKilled
    have h2 : ((w.getStor pool).get Curve3Pool.isKilledSlot).toNat = 0 := req.live
    cases hs : s.isKilled with
    | false => rfl
    | true => rw [hs] at h1; rw [h1] at h2; exact absurd h2 (by decide)
  have hsupp : (ocEnv (initSevm msg) i T.toNat).supply = some (supply w) := by rw [← hTn]; rfl
  obtain ⟨htake, hrl⟩ := oneCoin_accepts (e := ocEnv (initSevm msg) i T.toNat) (minDy := minDy) hck0.abs hk hA hsupp rfl
    (by simp only [ocEnv, decide_true]) hfee hadm hm0 hout
  have hdlt : dy < 2 ^ 256 := by have : recorded w i < 2 ^ 256 := word_lt _ _; omega
  have hla : a < 2 ^ 256 := Nat.lt_of_le_of_lt hsu (word_lt _ _)
  have hmlt : minDy < 2 ^ 256 := by omega
  have hilt : i.val < 2 ^ 256 := by have := i.isLt; omega
  obtain ⟨wa, wi, wm⟩ := oneCoin_words (e := initSevm msg) hdata
  have eA : ocAmt (initSevm msg) = Nat.toB256 a := wa
  have eI : ocI (initSevm msg) = Nat.toB256 i := wi
  have eM : ocMin (initSevm msg) = Nat.toB256 minDy := wm
  have nA : (ocAmt (initSevm msg)).toNat = a := by rw [eA]; exact B256.toNat_toB256_of_lt hla
  have nI : (ocI (initSevm msg)).toNat = i.val := by rw [eI]; exact B256.toNat_toB256_of_lt hilt
  have nM : (ocMin (initSevm msg)).toNat = minDy := by rw [eM]; exact B256.toNat_toB256_of_lt hmlt
  have hrl' : ∀ {o : Out}, removeLiquidityOneCoin s (ocEnv (initSevm msg) i T.toNat) a i minDy = some o →
      removeLiquidityOneCoin s (ocEnv (initSevm msg) i T.toNat) (ocAmt (initSevm msg)).toNat i
        (ocMin (initSevm msg)).toNat = some o := fun h => by rw [nA, nM]; exact h
  obtain ⟨amp', x0, x1, x2, D0, y, r0, r1, r2, y2, hi3, -, hA', hmf, hX, hD0, hm, hT0, hle, hy, hyl, h0, h1, h2, hy2, hs0, hs1, hs2,
    hmin, hma, hadd, hsub, ho, -⟩ := oc_words hck.abs nI.symm (hrl' hrl)
  have hF3 : (⟨(ocI (initSevm msg)).toNat, hi3⟩ : Fin 3) = i := Fin.ext nI
  have hdyW : (cwDy (ocI (initSevm msg)) r0 r1 r2 y2).toNat = dy := by
    have := congrArg Out.events ho
    simp only [Event.removeLiquidityOne.injEq, List.cons.injEq, and_true] at this
    exact this.2.2.symm
  have hset : ∀ (k : Fin 3) (v : V3) (x : Nat), (v.set k x).get k = x := fun k v x => by
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  have hbalN := congrArg (fun o : Out => o.state.balances.get i) ho
  simp only [hF3, hset] at hbalN
  have hvw : cwDy (ocI (initSevm msg)) r0 r1 r2 y2 = Nat.toB256 dy := by rw [← hdyW, toB256_toNat]
  have hheld : dy ≤ coinHeld w pool i := by have := mk.covered i; omega
  have hq : PushFitsK i ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i)) (initSevm msg).currentTarget (initSevm msg).caller
      (cwDy (ocI (initSevm msg)) r0 r1 r2 y2) := by
    show PushFitsK i _ msg.currentTarget msg.caller _
    rw [hco i, sK i, ht, hcaller, hvw]
    exact push_fits hopen hE hap.toCoinsApart i hdlt hheld req.fits.1 (fun _ => req.fits.2)
  have hburn : BurnFits (Devm.getStor (initDevm msg) c3) (initSevm msg).currentTarget (initSevm msg).caller.toB256 (ocAmt (initSevm msg)) := by
    show BurnFits _ msg.currentTarget msg.caller.toB256 _
    rw [show Devm.getStor (initDevm msg) c3 = w.getStor c3 from sC, ht, hcaller, eA]
    exact burn_fits mk.minter hE hap hsh hsu
  have hci : coinSlot i = coinsBase + ocI (initSevm msg) := by rw [eI]; rfl
  have hne : (initSevm msg).currentTarget ≠ c3 := by show msg.currentTarget ≠ c3; rw [ht]; decide
  have htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3 := (parties_not_precomp hH).2.2.2.1
  have hP := oc_premises (T := T) (i := i) hfork hstatic hdepth hC hto hne htok (by rw [show Devm.getStor (initDevm msg) c3 = w.getStor c3 from sC, hTdef]) hburn hci hq
  have hV0 : WClosed (initSevm msg) (ocV (initSevm msg) (initDevm msg) i (cwDy (ocI (initSevm msg)) r0 r1 r2 y2) 0) :=
    WClosed.of_foreign fun b d hb hs hc => pin_keep hb (hs _ (hC.pool i)) hc
  have hV1 : WClosed (initSevm msg) (ocV (initSevm msg) (initDevm msg) i (cwDy (ocI (initSevm msg)) r0 r1 r2 y2) 1) :=
    WClosed.of_foreign fun b d hb hs hc => ⟨fun a => (hc a).trans (hb.1 a), (hs _ (hC.pool i)).trans hb.2⟩
  have hc3 : (initDevm msg).getCode c3 = Curve3Crv.code :=
    (congrArg Acct.code (ask.entry.world c3 (by simp only [parties, List.mem_cons, true_or, or_true])).1).trans mf.c3Code
  have hkill : ((initDevm msg).getStor (initSevm msg).currentTarget).get isKilledSlot = 0 := by
    rw [show ((initDevm msg).getStor (initSevm msg).currentTarget).get isKilledSlot = _ from hck.abs.isKilled, hk]
    rfl
  have hlen : (initSevm msg).data.length = 100 := by rw [hdata]; exact oneCoinCalldata_length
  have hroom : 131000 + 3 * 104744 ≤ liquidityRoom := by decide
  refine ⟨ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg)
      (pushDk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)
      (pushNk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)) amp' x0 x1 x2 D0 y r0 r1 r2 y2,
    (afterSstore (initSevm msg) (ocEnd (initSevm msg) (initDevm msg) (ocC3Calls (initSevm msg) (initDevm msg)
      (pushDk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)
      (pushNk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)) T amp' x0 x1 x2 D0 y r0 r1 r2 y2)
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])).refundCounter.toNat, fun R hR hG => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F, F = R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg)
      (pushDk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)
      (pushNk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)) amp' x0 x1 x2 D0 y r0 r1 r2 y2 := ⟨_, rfl⟩
  have hcost := ocExactCost_withStaticGas (initSevm msg) F (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg)
      (pushDk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)
      (pushNk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)) amp' x0 x1 x2 D0 y r0 r1 r2 y2
  obtain ⟨r, hr, D, rfl, hDg, herr, hrf, hpaid⟩ := rx_oc_frame_exact (sevm := {initSevm msg with gas := F}) (pre := initDevm msg) (s := s)
    (Q := fun r => ∃ D, r = .halted D ∧ D.gasLeft = R ∧ D.error = none ∧
      D.refundCounter.toNat = (afterSstore (initSevm msg) (ocEnd (initSevm msg) (initDevm msg) (ocC3Calls (initSevm msg) (initDevm msg)
        (pushDk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)
        (pushNk (initSevm msg) (((initDevm msg).getStor (initSevm msg).currentTarget).get (coinSlot i)) 0x540 0x5e0 i)) T amp' x0 x1 x2 D0 y r0 r1 r2 y2)
        (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])).refundCounter.toNat ∧ OneCoinPaid w D.state E a i dy admin)
    _ hfork hstatic (by have := hdepth; show (initSevm msg).depth ≠ 0; omega) (show 4 ≤ (initSevm msg).data.length by omega) (show (initSevm msg).data.length < 2 ^ 256 by rw [hlen]; decide) (oneCoin_selector hdata)
    (hid.withStaticGas F) ((c3With_wClosed hne hV0).withStaticGas F) ((c3With_wClosed hne hV0).withStaticGas F) ⟨⟨hc3, rfl⟩, fun _ => rfl, rfl⟩
    hck.abs hck.unlocked hval hkill hi3 hA' (hP.withStaticGas F) hmf hX hD0 hm hT0 hle hy hyl h0 h1 h2 hy2 hs0 hs1 hs2 hmin hma hadd hsub
    ((c3With_wClosed hne hV1).withStaticGas F) (R := R) (Nat.le_trans hroom hR) (by rw [hcost]; exact hG)
    (fun D' hL _ hg hDe => by
      obtain ⟨d, l, S', M', G', hd, hDeq⟩ := hDe
      rw [ocEnd_withStaticGas] at hd
      refine ⟨_, rfl, hg, ?_, ?_, ?_⟩
      · rw [hDeq]
        show (afterSstore (initSevm msg) (d.addLog l) _ _).error = none
        rw [afterSstore_error]
        show d.error = none
        rw [hd.error, ocEnd_error]
        rfl
      · rw [hDeq]
        exact congrArg Int.toNat (afterSstore_refund_congr (initSevm msg) hd l _ _)
      · have hb1 := hL.w.1.2
        have hb2 := hL.w.2.2
        have htg : (initSevm msg).currentTarget = pool := ht
        have hcl : (initSevm msg).caller = E := hcaller
        rw [show Devm.getStor (initDevm msg) c3 = w.getStor c3 from sC, hcl, eA] at hb1
        rw [hco i, sK i, htg, hcl, hvw] at hb2
        refine ⟨burn_paid hap hsh hsu hb1, pushed_held hopen hap.toCoinsApart i hb2 hdlt hheld req.fits.1 (fun _ => req.fits.2), ?_⟩
        have hS : (D'.getStor msg.currentTarget).get (balancesBase + ocI (initSevm msg)) =
            ocBal ((initDevm msg).getStor msg.currentTarget) (ocI (initSevm msg)) (cwDy (ocI (initSevm msg)) r0 r1 r2 y2)
              ((pickWord3 (ocI (initSevm msg)).toNat x0 x1 x2 - y) / pickWord3 (ocI (initSevm msg)).toNat cwP1 cwPm cwPm -
                cwDy (ocI (initSevm msg)) r0 r1 r2 y2) :=
          (hL.stor _).trans (oc_final_bal _ _ _ _ hi3)
        have hrec : recorded D'.state i = recorded w i - (dy + admin) := by
          rw [hbalN, ← hS, ht, eI]
          rfl
        rw [hrec]
        omega)
  rw [hcost, ← hF] at hr
  obtain ⟨exD⟩ := Lift.lift_exactM (sevm := {initSevm msg with gas := F}) cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  rw [← hF]
  exact ⟨D, Lift.exec_withGas_of_frame exD, herr, hDg, hrf, hpaid⟩

/-- **`one_coin_message`.** -/
theorem one_coin_message_holds : one_coin_message := by
  intro d m A msg E a minDy dy admin i ask req
  have fees := m.feesWithin A
  exact one_coin_run (m.facts A) (m.marked A) fees.1 fees.2 ask req

end Blanc.Composition.Curve3PoolPublic
