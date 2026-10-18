import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceWalk
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceModel
import Blanc.Lift.Curve3Pool.Walk.OneCoinRaw

/-!
# `remove_liquidity_imbalance`'s raw effect

From the walk (`xa_rli`): one fee iteration as the model's `feeAt` (`rli_feeAt`), the model's step
(`rli_model`), the environment the frame observed (`rliEnvOf`: the supply reply, the burn, and
the transfer of each coin with a nonzero amount), its calls in order (the burn, then the
transfers), the event and the storage effect, giving `removeLiquidityImbalance_raw_of`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem rli_den : rliDen.toNat = feeDen := by decide

theorem rli_req {P : Prop} [Decidable P] (h : P) : req P = some () := by
  unfold req; rw [ite_eq_left h]

set_option hygiene false in
/-- One `bind` on a `some`, in either elaborated form. -/
local macro "bstep" : tactic => `(tactic| first | rw [Option.bind_some] | rw [cw_some_bind])

/-- One fee iteration of the walk is the model's `feeAt`. -/
theorem rli_feeAt {F AF D0 D1 B N f st af : B256} {fee adminFee : Nat} {old new : V3} {i : Fin 3}
    (hit : RliFeeIter F AF D0 D1 B N f st af) (hF : F.toNat = fee) (hAF : AF.toNat = adminFee)
    (hB : old.get i = B.toNat) (hN : new.get i = N.toNat) :
    feeAt fee adminFee D0.toNat D1.toNat old new i = some (f.toNat, st.toNat, af.toNat) := by
  obtain ⟨hm1, hD0, dif, hdif, hm2, rfl, hm3, hs3, rfl, hs4, rfl⟩ := hit
  subst hF hAF
  unfold feeAt
  rw [hB, hN, chkMul_toNat_of_nofm hm1]
  bstep
  rw [chkDiv_toNat_of_ne hD0]
  bstep
  have tail : ∀ d : B256, F.Nofm d → (F * d / rliDen).Nofm AF →
      ¬ N < F * d / rliDen * AF / rliDen → ¬ N < F * d / rliDen →
      (do
        let __do_lift ← chkMul F.toNat d.toNat
        let f ← chkDiv __do_lift feeDen
        let __do_lift ← chkMul f AF.toNat
        let __do_lift ← chkDiv __do_lift feeDen
        let stored ← chkSub N.toNat __do_lift
        let after ← chkSub N.toNat f
        some (f, stored, after)) =
      some ((F * d / rliDen).toNat, (N - F * d / rliDen * AF / rliDen).toNat,
        (N - F * d / rliDen).toNat) := by
    intro d h2 h3 h4 h5
    rw [chkMul_toNat_of_nofm h2]
    bstep
    rw [← rli_den, chkDiv_toNat_of_ne (by decide)]
    bstep
    rw [chkMul_toNat_of_nofm h3]
    bstep
    rw [chkDiv_toNat_of_ne (by decide)]
    bstep
    rw [chkSub_toNat_of_le (toNat_le_of_not_lt h4)]
    bstep
    rw [chkSub_toNat_of_le (toNat_le_of_not_lt h5)]
    bstep
  rcases hdif with ⟨hlt, rfl⟩ | ⟨hge, rfl⟩
  · rw [ite_eq_left (B256.lt_iff_toNat_lt_toNat.mp hlt),
      chkSub_toNat_of_le (le_of_lt (B256.lt_iff_toNat_lt_toNat.mp hlt))]
    bstep
    exact tail _ hm2 hm3 hs3 hs4
  · rw [ite_eq_right (by rwa [B256.lt_iff_toNat_lt_toNat] at hge),
      chkSub_toNat_of_le (toNat_le_of_not_lt hge)]
    bstep
    exact tail _ hm2 hm3 hs3 hs4

/-- The model's `feeLoop` from the walk's three iterations. -/
theorem rli_feeLoop {F AF D0 D1 B0 B1 B2 N0 N1 N2 f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256}
    {fee adminFee : Nat}
    (h0 : RliFeeIter F AF D0 D1 B0 N0 f0 s0 x0) (h1 : RliFeeIter F AF D0 D1 B1 N1 f1 s1 x1)
    (h2 : RliFeeIter F AF D0 D1 B2 N2 f2 s2 x2) (hF : F.toNat = fee) (hAF : AF.toNat = adminFee) :
    feeLoop fee adminFee D0.toNat D1.toNat ⟨B0.toNat, B1.toNat, B2.toNat⟩
      ⟨N0.toNat, N1.toNat, N2.toNat⟩ =
      some (⟨f0.toNat, f1.toNat, f2.toNat⟩, ⟨s0.toNat, s1.toNat, s2.toNat⟩,
        ⟨x0.toNat, x1.toNat, x2.toNat⟩) := by
  unfold feeLoop
  rw [rli_feeAt (i := 0) h0 hF hAF rfl rfl]
  bstep
  rw [rli_feeAt (i := 1) h1 hF hAF rfl rfl]
  bstep
  rw [rli_feeAt (i := 2) h2 hF hAF rfl rfl]
  bstep

/-- The model's `remove_liquidity_imbalance` from the walk's checked words. -/
theorem rli_model {s : State} {e : Env} {σ : Stor} {a0 a1 a2 mx T A D0 D1 D2 f0 f1 f2 : B256}
    (ha : Abstracts σ s) (hk : s.isKilled = false) (hT : e.supply = some T.toNat) (hT0 : T ≠ 0)
    (hm3 : (σ.get feeSlot).Nofm (Bytes.toB256 [3])) (hA : aChk s e.time = some A.toNat)
    (hD0 : getDMem ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ A.toNat =
      some D0.toNat)
    (hu0 : ¬ balAt σ 0 < a0) (hu1 : ¬ balAt σ 1 < a1) (hu2 : ¬ balAt σ 2 < a2)
    (hD1 : getDMem ⟨(balAt σ 0 - a0).toNat, (balAt σ 1 - a1).toNat, (balAt σ 2 - a2).toNat⟩
      A.toNat = some D1.toNat)
    (h0 : RliFeeIter (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) (σ.get adminFeeSlot)
      D0 D1 (balAt σ 0) (balAt σ 0 - a0) f0 (balAt σ 0 - a0 - f0 * σ.get adminFeeSlot / rliDen)
      (balAt σ 0 - a0 - f0))
    (h1 : RliFeeIter (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) (σ.get adminFeeSlot)
      D0 D1 (balAt σ 1) (balAt σ 1 - a1) f1 (balAt σ 1 - a1 - f1 * σ.get adminFeeSlot / rliDen)
      (balAt σ 1 - a1 - f1))
    (h2 : RliFeeIter (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]) (σ.get adminFeeSlot)
      D0 D1 (balAt σ 2) (balAt σ 2 - a2) f2 (balAt σ 2 - a2 - f2 * σ.get adminFeeSlot / rliDen)
      (balAt σ 2 - a2 - f2))
    (hD2 : getDMem ⟨(balAt σ 0 - a0 - f0).toNat, (balAt σ 1 - a1 - f1).toNat,
      (balAt σ 2 - a2 - f2).toNat⟩ A.toNat = some D2.toNat)
    (hD02 : ¬ D0 < D2) (hmT : (D0 - D2).Nofm T) (hbn : (D0 - D2) * T / D0 ≠ 0)
    (hb1 : ¬ (D0 - D2) * T / D0 + Bytes.toB256 [1] < (D0 - D2) * T / D0)
    (hslip : ¬ mx < (D0 - D2) * T / D0 + Bytes.toB256 [1])
    (hTX : ¬ T < (D0 - D2) * T / D0 + Bytes.toB256 [1])
    (hburn : e.burnOk = true)
    (hpush : (a0.toNat ≠ 0 → (e.coin 0).pushOk = true) ∧ (a1.toNat ≠ 0 → (e.coin 1).pushOk = true) ∧
      (a2.toNat ≠ 0 → (e.coin 2).pushOk = true)) :
    removeLiquidityImbalance s e ⟨a0.toNat, a1.toNat, a2.toNat⟩ mx.toNat = some
      ⟨{s with balances := ⟨(balAt σ 0 - a0 - f0 * σ.get adminFeeSlot / rliDen).toNat,
          (balAt σ 1 - a1 - f1 * σ.get adminFeeSlot / rliDen).toNat,
          (balAt σ 2 - a2 - f2 * σ.get adminFeeSlot / rliDen).toNat⟩}, none,
        [.removeLiquidityImbalance e.caller ⟨a0.toNat, a1.toNat, a2.toNat⟩
          ⟨f0.toNat, f1.toNat, f2.toNat⟩ D1.toNat (T - ((D0 - D2) * T / D0 + Bytes.toB256 [1])).toNat],
        .burn e.caller ((D0 - D2) * T / D0 + Bytes.toB256 [1]).toNat ::
          pushCalls e.caller ⟨a0.toNat, a1.toNat, a2.toNat⟩⟩ := by
  have hb : s.balances = ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ :=
    (V3.ext_get fun k => by rw [← ex_w3_nat]; exact ex_bal_nat ha k).symm
  have rk : req (s.isKilled = false) = some () := by unfold req; rw [ite_eq_left hk]
  have rT : req (T.toNat ≠ 0) = some () := by
    unfold req; rw [ite_eq_left (B256.toNat_ne_zero hT0)]
  have hfee : feeAdj s = some (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]).toNat := by
    unfold feeAdj
    rw [← ha.fee, show (3 : Nat) = (Bytes.toB256 [3]).toNat from rfl, chkMul_toNat_of_nofm hm3,
      Option.bind_eq_bind, Option.bind_some, show (8 : Nat) = (Bytes.toB256 [8]).toNat from rfl,
      chkDiv_toNat_of_ne (by decide)]
  have hnew : V3.ofFnM (fun k => chkSub ((⟨(balAt σ 0).toNat, (balAt σ 1).toNat,
      (balAt σ 2).toNat⟩ : V3).get k) ((⟨a0.toNat, a1.toNat, a2.toNat⟩ : V3).get k)) =
      some ⟨(balAt σ 0 - a0).toNat, (balAt σ 1 - a1).toNat, (balAt σ 2 - a2).toNat⟩ :=
    cw_ofFnM_some (chkSub_toNat_of_le (toNat_le_of_not_lt hu0))
      (chkSub_toNat_of_le (toNat_le_of_not_lt hu1)) (chkSub_toNat_of_le (toNat_le_of_not_lt hu2))
  unfold removeLiquidityImbalance
  rw [rk]
  bstep
  rw [hT]
  bstep
  rw [rT]
  bstep
  rw [hfee]
  bstep
  rw [hA]
  bstep
  rw [hb]
  dsimp only
  rw [hD0]
  bstep
  rw [hnew]
  bstep
  rw [hD1]
  bstep
  rw [rli_feeLoop h0 h1 h2 rfl ha.adminFee]
  bstep
  dsimp only
  rw [hD2]
  bstep
  rw [chkSub_toNat_of_le (toNat_le_of_not_lt hD02)]
  bstep
  rw [chkMul_toNat_of_nofm hmT]
  bstep
  rw [chkDiv_toNat_of_ne h0.2.1]
  bstep
  rw [rli_req (B256.toNat_ne_zero hbn)]
  bstep
  rw [show (1 : Nat) = (Bytes.toB256 [1]).toNat from rfl,
    chkAdd_toNat_of_lt ((B256.nof_iff_not_add_lt _ _).mpr hb1)]
  bstep
  rw [rli_req (toNat_le_of_not_lt hslip)]
  bstep
  rw [rli_req hburn]
  bstep
  rw [rli_req hpush]
  bstep
  rw [chkSub_toNat_of_le (toNat_le_of_not_lt hTX)]
  bstep

theorem rli_amt0 (sevm : Sevm) : rliAmt sevm 0 = Sevm.dataWord sevm (Bytes.toB256 [4]) := by
  unfold rliAmt
  rw [show (Bytes.toB256 [0x20] * Nat.toB256 0 + Bytes.toB256 [4] : B256) = Bytes.toB256 [4] from
    by decide]

theorem rli_amt1 (sevm : Sevm) : rliAmt sevm 1 = Sevm.dataWord sevm (Bytes.toB256 [0x24]) := by
  unfold rliAmt
  rw [show (Bytes.toB256 [0x20] * Nat.toB256 1 + Bytes.toB256 [4] : B256) = Bytes.toB256 [0x24] from
    by decide]

theorem rli_amt2 (sevm : Sevm) : rliAmt sevm 2 = Sevm.dataWord sevm (Bytes.toB256 [0x44]) := by
  unfold rliAmt
  rw [show (Bytes.toB256 [0x20] * Nat.toB256 2 + Bytes.toB256 [4] : B256) = Bytes.toB256 [0x44] from
    by decide]

/-- `pushCalls`, coin by coin. -/
theorem rli_pushCalls_eq (c : Nat) (a : V3) :
    pushCalls c a = (if a.v0 ≠ 0 then [.push 0 c a.v0] else []) ++
      (if a.v1 ≠ 0 then [.push 1 c a.v1] else []) ++ (if a.v2 ≠ 0 then [.push 2 c a.v2] else []) := by
  unfold pushCalls
  by_cases h0 : a.v0 = 0 <;> by_cases h1 : a.v1 = 0 <;> by_cases h2 : a.v2 = 0 <;>
    simp (config := {decide := true}) only [List.filterMap_cons, List.filterMap_nil, V3.get,
      Fin.isValue, h0, h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte,
      List.nil_append, List.append_nil, List.cons_append]

/-- The environment `remove_liquidity_imbalance` observes: the supply reply `T`, the burn, and
the transfer of each coin with a nonzero amount. -/
def rliEnvW (sevm : Sevm) (T : Nat) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun k => ⟨none, none, false, decide ((rliAmt sevm k.val).toNat ≠ 0)⟩, some T, false, true⟩

/-- A coin with a nonzero amount was called with `transfer`. -/
theorem rli_called {D : Exec.Deriv} {σ : Stor} {k : Nat} {Lk : List Exec.Frame}
    (hP : RliPushK D.sevm σ k Lk) (hmem : ∀ c ∈ Lk, c ∈ children D) (hne : rliAmt D.sevm k ≠ 0) :
    CalledWith D (σ.get (coinsBase + Nat.toB256 k)).toAdr transferSel RawCallOk := by
  rcases hP with ⟨h0, -⟩ | ⟨-, c, rfl, ht, hd, -, -, hok⟩
  · exact absurd h0 hne
  refine ⟨c, hmem c List.mem_cons_self, ht, ?_, hok⟩
  rw [hd]; unfold exPushData; rw [List.append_assoc]; exact List.take_left' rfl

/-- Coin `k`'s transfer children are the model's `push` of coin `k`, as calls. -/
theorem rli_calls_k {D : Exec.Deriv} {σ : Stor} {k : Fin 3} {Lk : List Exec.Frame}
    (hP : RliPushK D.sevm σ k.val Lk) (hσ : entryStor D = σ) (hs : D.sevm.isStatic = false)
    (hco : ¬ D.sevm.benvStat.rules.isPrecomp (σ.get (coinsBase + Nat.toB256 k.val)).toAdr) :
    Lk.filterMap (fun c => if c.sevm.isStatic then none else
      some (⟨c.sevm.currentTarget, c.sevm.data, c.sevm.value⟩ : CallReq)) =
    ((if (rliAmt D.sevm k.val).toNat ≠ 0 then
        [ExtCall.push k D.sevm.caller.toB256.toNat (rliAmt D.sevm k.val).toNat] else []).map
      (encodeCall D.sevm.currentTarget (coinAdr D) (tokenAdr D))).filter
      (fun r => framed D r.target) := by
  have hca : coinAdr D k = (σ.get (coinsBase + Nat.toB256 k.val)).toAdr := by
    rw [← hσ]; rfl
  rcases hP with ⟨h0, rfl⟩ | ⟨hne, c, rfl, ht, hd, hv, hst, -⟩
  · rw [h0]
    simp only [B256.toNat_zero, ne_eq, not_true_eq_false, ↓reduceIte, List.filterMap_nil,
      List.map_nil, List.filter_nil]
  · rw [ite_eq_left (B256.toNat_ne_zero hne)]
    simp only [List.filterMap_cons, List.filterMap_nil, hst, hs, Bool.false_eq_true, ↓reduceIte,
      List.map_cons, List.map_nil, encodeCall, List.filter_cons, List.filter_nil, framed, hca,
      decide_eq_false hco, Bool.not_false, Bool.true_or, ht, hd, hv, exPushData, word,
      toB256_toNat]

section

variable {sevm : Sevm} {pre post : Devm} {s : State}

/-- **`remove_liquidity_imbalance`'s raw effect**, given the certificate's checkedness, with the
observed environment exposed: `rliEnvW` at the supply reply `T`. -/
theorem removeLiquidityImbalance_rawE_of (hc : Cert.CheckedM code cert mems true)
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩)
    (hidk : ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ (T : B256) (o : Out), step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post (rliEnvW sevm T.toNat) o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  have hcoin' : ∀ k, k < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 k)).toAdr :=
    fun k hk => hcoin ⟨k, hk⟩
  obtain ⟨hlock, hval, hkill, cs, cb, L0, L1, L2, A, D0, D1, D2, f0, f1, f2, hL, hsw, hT0, hm3,
    hA, hD0, hu0, hu1, hu2, hD1, h0, h1, h2, hD2, hD02, hmT, hbn, hb1, hslip, hTX, hbt, hbd, hbv,
    hbs, hblen, hP0, hP1, hP2, hstor, hlogs, hout⟩ :=
    xa_rli hc hcode hfork hlen hcd hsel rfl hck.abs htok hcoin' hpc hid hkeep hidk hx
  have hch : children ⟨0, sevm, pre, .ok post, exc⟩ = cs :: cb :: (L0 ++ L1 ++ L2) := hL
  have hdec := rli_decode hsel hlen
  have hav : argV3 sevm 0 = ⟨(Sevm.dataWord sevm (Bytes.toB256 [4])).toNat,
      (Sevm.dataWord sevm (Bytes.toB256 [0x24])).toNat,
      (Sevm.dataWord sevm (Bytes.toB256 [0x44])).toNat⟩ := by
    unfold argV3 arg Sevm.argWord
    rw [show (32 * 0 + 4 : B256) = Bytes.toB256 [4] by decide,
      show (32 * (0 + 1) + 4 : B256) = Bytes.toB256 [0x24] by decide,
      show (32 * (0 + 2) + 4 : B256) = Bytes.toB256 [0x44] by decide]
  have hmx : arg sevm 3 = (Sevm.dataWord sevm (Bytes.toB256 [0x64])).toNat := by
    unfold arg Sevm.argWord
    rw [show (32 * 3 + 4 : B256) = Bytes.toB256 [0x64] by decide]
  have hk : s.isKilled = false := boolWord_inj (hck.abs.isKilled.symm.trans hkill)
  have hmodel := rli_model (e := rliEnvW sevm (vSupply cs).toNat) (mx := Sevm.dataWord sevm
    (Bytes.toB256 [0x64])) hck.abs hk rfl hT0 hm3 hA hD0 hu0 hu1 hu2 hD1 h0 h1 h2 hD2 hD02 hmT
    hbn hb1 hslip hTX rfl
    ⟨fun h => by
      show decide ((rliAmt sevm 0).toNat ≠ 0) = true
      rw [rli_amt0]; exact decide_eq_true h,
    fun h => by
      show decide ((rliAmt sevm 1).toNat ≠ 0) = true
      rw [rli_amt1]; exact decide_eq_true h,
    fun h => by
      show decide ((rliAmt sevm 2).toNat ≠ 0) = true
      rw [rli_amt2]; exact decide_eq_true h⟩
  refine ⟨vSupply cs, ?o, ?step, ?raw⟩
  case step =>
    rw [hdec, rli_step (by show sevm.value.toNat = 0; rw [hval]; rfl), hav, hmx]
    exact hmodel
  case raw =>
    have m0 : ∀ c ∈ L0, c ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := fun c hc => by
      rw [hch]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _ hc)))
    have m1 : ∀ c ∈ L1, c ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := fun c hc => by
      rw [hch]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_right _ hc)))
    have m2 : ∀ c ∈ L2, c ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := fun c hc => by
      rw [hch]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hc))
    have hcbm : cb ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := by
      rw [hch]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have hbSel : cb.sevm.data.take 4 = burnFromSel := by
      rw [hbd, List.append_assoc]; exact List.take_left' rfl
    have hne : ∀ k : Nat, decide ((rliAmt sevm k).toNat ≠ 0) = true → rliAmt sevm k ≠ 0 :=
      fun k h e => of_decide_eq_true h (by rw [e]; rfl)
    refine ⟨⟨rfl, rfl, rfl, fun k => ⟨fun _ h => (by cases h), fun _ h => (by cases h),
      fun h => (by cases h), fun h => ?_⟩, fun T hT => ?_, fun h => (by cases h),
      fun _ => .inr ⟨cb, hcbm, hbt, hbSel, hblen⟩⟩, ?stor, ?logs, hout, ?calls⟩
    · match k with
      | 0 => exact .inr (rli_called hP0 m0 (hne 0 h))
      | 1 => exact .inr (rli_called hP1 m1 (hne 1 h))
      | 2 => exact .inr (rli_called hP2 m2 (hne 2 h))
    · cases hT
      exact .inr ⟨0, cs, by rw [hch]; rfl, hsw.target, hsw.data, hsw.len, rfl⟩
    case stor =>
      rw [hdec]
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · rw [hstor,
          Stor.get_set_ne _ (show balancesBase + Nat.toB256 2 ≠ x from hx (.bal 2) (bal_mem 2)),
          Stor.get_set_ne _ (show balancesBase + Nat.toB256 1 ≠ x from hx (.bal 1) (bal_mem 1)),
          Stor.get_set_ne _ (show balancesBase + Nat.toB256 0 ≠ x from hx (.bal 0) (bal_mem 0))]
        rfl
      · have hf' : f = .bal 0 ∨ f = .bal 1 ∨ f = .bal 2 := by
          simpa only [footprint, balFlds, List.mem_cons, List.not_mem_nil, or_false] using hf
        rcases hf' with rfl | rfl | rfl
        · show ((post.getStor sevm.currentTarget).get (balanceSlot 0)).toNat = _
          rw [hstor, Stor.get_set_ne _ (show balancesBase + Nat.toB256 2 ≠ balanceSlot 0 from bal_ne_bal (by decide) (by decide) (by decide)),
            Stor.get_set_ne _ (show balancesBase + Nat.toB256 1 ≠ balanceSlot 0 from bal_ne_bal (by decide) (by decide) (by decide))]
          exact congrArg B256.toNat (Stor.get_set_self _ _ _)
        · show ((post.getStor sevm.currentTarget).get (balanceSlot 1)).toNat = _
          rw [hstor, Stor.get_set_ne _ (show balancesBase + Nat.toB256 2 ≠ balanceSlot 1 from bal_ne_bal (by decide) (by decide) (by decide))]
          exact congrArg B256.toNat (Stor.get_set_self _ _ _)
        · show ((post.getStor sevm.currentTarget).get (balanceSlot 2)).toNat = _
          rw [hstor]
          exact congrArg B256.toNat (Stor.get_set_self _ _ _)
    case logs =>
      have ht : topicRemoveLiquidityImbalance = rliTopic := by decide
      rw [hlogs, hch]
      show _ = _ ++ _ ++ [eventLog sevm.currentTarget _]
      simp only [eventLog, rliEnvW, wordsV3, word, toB256_toNat, ht, List.append_assoc]
    case calls =>
      intro hs
      replace hs : sevm.isStatic = false := hs
      have e0 := rli_calls_k (D := ⟨0, sevm, pre, .ok post, exc⟩) (k := 0) hP0 rfl hs
        (hcoin' 0 (by decide))
      have e1 := rli_calls_k (D := ⟨0, sevm, pre, .ok post, exc⟩) (k := 1) hP1 rfl hs
        (hcoin' 1 (by decide))
      have e2 := rli_calls_k (D := ⟨0, sevm, pre, .ok post, exc⟩) (k := 2) hP2 rfl hs
        (hcoin' 2 (by decide))
      unfold CallsOf modelCalls
      rw [hch, rli_pushCalls_eq, List.filterMap_cons, List.filterMap_cons, List.filterMap_append,
        List.filterMap_append, e0, e1, e2]
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, rli_amt0, rli_amt1,
        rli_amt2, hsw.static, hbs, hs, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.map_append, List.filter_cons, List.filter_append, encodeCall, framed, tokenAdr,
        entryStor, decide_eq_false htok, Bool.not_false, Bool.true_or, hbt, hbd, hbv, word,
        toB256_toNat, rliEnvW]

/-- **`remove_liquidity_imbalance`'s raw effect**, given the certificate's checkedness. -/
theorem removeLiquidityImbalance_raw_of (hc : Cert.CheckedM code cert mems true)
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩)
    (hidk : ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  obtain ⟨T, o, h1, h2⟩ := removeLiquidityImbalance_rawE_of hc exc hcode hfork hlen hcd hsel
    hstack hmem hgas hck htok hcoin hpc hid hkeep hidk
  exact ⟨_, o, h1, h2⟩

end

end Blanc.Lift.Curve3Pool
