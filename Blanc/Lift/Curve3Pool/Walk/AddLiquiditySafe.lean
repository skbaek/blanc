import Blanc.Lift.Curve3Pool.Walk.AddLiquidityBack
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquiditySafe
import Blanc.Lift.Curve3Pool.Refine

/-!
# `add_liquidity`: the raw effect

`addLiquidity_raw_of`: a successful frame of the pool on the `add_liquidity` selector, from a
`Checkpoint` at entry and the frame premises (the exchange-style environmental premises: coins
and token not precompiles, nonempty pool code, the identity precompile ready, every child keeps
the pool's storage and address 4's code), given the certificate's checkedness, has the model's
step on the decoded call and the `RawEffect` Spec states, with the environment read off its
children (`totalSupply`'s reply, each positive amount's `transferFrom` `RawCallOk`, for coin 2
the `balanceOf` pair around it, `mint`'s word). Both branches: the first deposit (supply `0`)
and the fee path.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-! ## The model's step -/

/-- **The model's `add_liquidity` on a first deposit** (supply `0`) when every step succeeds. -/
theorem al_model_first {s : State} {e : Env} {amounts : V3} {minMint fee amp D1 T' : Nat}
    {new : V3}
    (hk : s.isKilled = false) (hfee : feeAdj s = some fee) (ha : aChk s e.time = some amp)
    (hT : e.supply = some 0)
    (hnew : V3.ofFnM (pullAdd e 0 s.balances amounts) = some new)
    (hD1 : getDMem new amp = some D1) (hlt : 0 < D1)
    (hmin : minMint ≤ D1) (hok : e.mintOk = true) (hT' : chkAdd 0 D1 = some T') :
    addLiquidity s e amounts minMint = some ⟨{ s with balances := new }, none,
      [.addLiquidity e.caller amounts V3.zero D1 T'],
      pullCalls e.caller amounts ++ [.mint e.caller D1]⟩ := by
  have rk : req (s.isKilled = false) = some () := by unfold req; rw [ite_eq_left hk]
  have rlt : req (D1 > 0) = some () := by unfold req; rw [ite_eq_left hlt]
  have rmin : req (D1 ≥ minMint) = some () := by unfold req; rw [ite_eq_left hmin]
  have rok : req (e.mintOk = true) = some () := by unfold req; rw [ite_eq_left hok]
  unfold addLiquidity
  simp only [rk, hfee, ha, hT, gt_iff_lt, Nat.lt_irrefl, ↓reduceIte, hnew, hD1, rlt, rmin, rok,
    hT', Option.bind_eq_bind, Option.bind_some]

/-- **The model's `add_liquidity` with a positive supply** when every step succeeds. -/
theorem al_model_fee {s : State} {e : Env} {amounts : V3}
    {minMint fee amp T D0 D1 D2 x y mint T' : Nat} {new fees stored after : V3}
    (hk : s.isKilled = false) (hfee : feeAdj s = some fee) (ha : aChk s e.time = some amp)
    (hT : e.supply = some T) (hTp : 0 < T) (hD0 : getDMem s.balances amp = some D0)
    (hnew : V3.ofFnM (pullAdd e T s.balances amounts) = some new)
    (hD1 : getDMem new amp = some D1) (hlt : D0 < D1)
    (hfl : feeLoop fee s.adminFee D0 D1 s.balances new = some (fees, stored, after))
    (hD2 : getDMem after amp = some D2) (hsub : chkSub D2 D0 = some x)
    (hmul : chkMul T x = some y) (hdiv : chkDiv y D0 = some mint)
    (hmin : minMint ≤ mint) (hok : e.mintOk = true) (hT' : chkAdd T mint = some T') :
    addLiquidity s e amounts minMint = some ⟨{ s with balances := stored }, none,
      [.addLiquidity e.caller amounts fees D1 T'],
      pullCalls e.caller amounts ++ [.mint e.caller mint]⟩ := by
  have rk : req (s.isKilled = false) = some () := by unfold req; rw [ite_eq_left hk]
  have rlt : req (D1 > D0) = some () := by unfold req; rw [ite_eq_left hlt]
  have rmin : req (mint ≥ minMint) = some () := by unfold req; rw [ite_eq_left hmin]
  have rok : req (e.mintOk = true) = some () := by unfold req; rw [ite_eq_left hok]
  have hT0 : T ≠ 0 := Nat.pos_iff_ne_zero.mp hTp
  unfold addLiquidity
  simp only [rk, hfee, ha, hT, gt_iff_lt, hTp, hT0, ↓reduceIte, hD0, hnew, hD1, rlt, hfl, hD2,
    hsub, hmul, hdiv, rmin, rok, hT', Option.bind_eq_bind, Option.bind_some]

/-! ## What the frame observed -/

/-- A coin's answers read off its pull children: the `balanceOf` pair around the
`transferFrom` (coin 2), the `transferFrom` alone, or nothing (a zero amount). -/
def alObs : List Exec.Frame → CoinObs
  | [c0, _, c1] => ⟨some (alWord c0).toNat, some (alWord c1).toNat, true, false⟩
  | [] => ⟨none, none, false, false⟩
  | _ => ⟨none, none, true, false⟩

/-- **The environment an `add_liquidity` frame observed**: the supply word `T`, each coin's
answers read off its pull children `L0, L1, L2`, the `mint` accepted. -/
def alEnv (sevm : Sevm) (T : B256) (L0 L1 L2 : List Exec.Frame) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun k => alObs (if k.val = 0 then L0 else if k.val = 1 then L1 else L2),
    some T.toNat, true, false⟩

theorem al_getElem_mid {A L B : List Exec.Frame} {j : Nat} {c : Exec.Frame}
    (h : L[j]? = some c) : (A ++ L ++ B)[A.length + j]? = some c := by
  have hj : j < L.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]
  exact h

theorem al_take_tf {X Y Z : Bytes} : (transferFromSel ++ X ++ Y ++ Z).take 4 = transferFromSel := by
  rw [List.append_assoc, List.append_assoc]; exact List.take_left' rfl

/-- **One coin's pull children witness its answers.** -/
theorem al_coinObs {D : Exec.Deriv} {k : Fin 3} {C amt cr : B256} {A Lc B : List Exec.Frame}
    (hk : AlPullKids D.sevm C k.val amt Lc cr) (hL : children D = A ++ Lc ++ B)
    (hC : coinAdr D k = C.toAdr) : CoinObsOf D k (alObs Lc) := by
  have hmem : ∀ c ∈ Lc, c ∈ children D := fun c hc => by
    rw [hL]; exact List.mem_append_left _ (List.mem_append_right _ hc)
  rcases hk with ⟨-, rfl, -⟩ | ⟨-, -, c, rfl, hp, -⟩ | ⟨-, -, c0, c, c1, rfl, hb0, hp, hb1, -, -⟩
  · exact ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun h => (by cases h),
      fun h => (by cases h)⟩
  · refine ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ => Or.inr ?_,
      fun h => (by cases h)⟩
    exact ⟨c, hmem c List.mem_cons_self, by rw [hp.target, hC], by rw [hp.data]; exact al_take_tf,
      hp.ok⟩
  · refine ⟨fun w hw => Or.inr ?_, fun w hw => Or.inr ?_, fun _ => Or.inr ?_,
      fun h => (by cases h)⟩
    · cases hw
      exact ⟨A.length + 0, c0, by rw [hL]; exact al_getElem_mid rfl, by rw [hb0.target, hC],
        hb0.data, hb0.len, rfl⟩
    · cases hw
      exact ⟨(alWord c0).toNat, A.length + 0, A.length + 2, rfl, by omega,
        ⟨c0, by rw [hL]; exact al_getElem_mid rfl, by rw [hb0.target, hC], hb0.data, hb0.len, rfl⟩,
        ⟨c1, by rw [hL]; exact al_getElem_mid rfl, by rw [hb1.target, hC], hb1.data, hb1.len, rfl⟩⟩
    · exact ⟨c, hmem c (List.mem_cons_of_mem _ List.mem_cons_self), by rw [hp.target, hC],
        by rw [hp.data]; exact al_take_tf, hp.ok⟩

/-- **One coin's credit is the model's `pullIn`.** -/
theorem al_pullIn {sevm : Sevm} {e : Env} {k : Fin 3} {C amt cr : B256} {Lc : List Exec.Frame}
    (hk : AlPullKids sevm C k.val amt Lc cr) (he : e.coin k = alObs Lc) (hne : amt ≠ 0) :
    pullIn e k amt.toNat = some cr.toNat := by
  rcases hk with ⟨h0, -, -⟩ | ⟨-, hk2, c, rfl, -, rfl⟩ | ⟨-, hk2, c0, c, c1, rfl, -, -, -, hge, rfl⟩
  · exact absurd h0 hne
  · have hf : k ≠ feeIndex := fun h => hk2 (by rw [h]; rfl)
    unfold pullIn
    rw [ite_eq_right hf, he]
    rfl
  · have hf : k = feeIndex := Fin.ext hk2
    unfold pullIn
    rw [ite_eq_left hf, he]
    exact chkSub_toNat_of_le (toNat_le_of_not_lt hge)

/-- **One coin's new balance is the model's `pullAdd`.** -/
theorem al_pullAdd {sevm : Sevm} {e : Env} {T : Nat} {old amounts : V3} {k : Fin 3}
    {C amt cr B : B256} {Lc : List Exec.Frame}
    (hk : AlPullKids sevm C k.val amt Lc cr) (he : e.coin k = alObs Lc)
    (hamt : amounts.get k = amt.toNat) (hold : old.get k = B.toNat)
    (hT : T = 0 → 0 < amt.toNat) (hadd : ¬ B + cr < B) :
    pullAdd e T old amounts k = some (B + cr).toNat := by
  have hsum := chkAdd_toNat_of_lt ((B256.nof_iff_not_add_lt _ _).mpr hadd)
  unfold pullAdd
  by_cases ha : amt = 0
  · have hc : cr = 0 := by
      rcases hk with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd ha h
      · exact absurd ha h
    have hz : ¬ amounts.get k > 0 := by rw [hamt, ha]; exact Nat.lt_irrefl 0
    have h0 : ¬ T = 0 := fun h => by have := hT h; rw [ha] at this; exact Nat.lt_irrefl 0 this
    rw [hc, B256.toNat_zero] at hsum
    simp only [h0, hz, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, hold]
    rw [hc]; exact hsum
  · have hp : amounts.get k > 0 := by rw [hamt]; exact Nat.pos_of_ne_zero (toNat_ne_zero ha)
    have hpi := al_pullIn hk he ha
    rw [← hamt] at hpi
    by_cases h0 : T = 0
    · simp only [h0, hp, ↓reduceIte, req, Option.bind_eq_bind, Option.bind_some, hpi, hold]
      exact hsum
    · simp only [h0, hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, hpi, hold]
      exact hsum

/-! ## The fee loop -/

theorem al_feeDen_toNat : (Nat.toB256 feeDen).toNat = feeDen := by decide

/-- **One fee iteration's checks are the model's `feeAt`.** -/
theorem al_feeAt {F AF D0 D1 B N f st a : B256} {old new : V3} {i : Fin 3}
    (h : AlFeeFacts F AF D0 D1 B N f st a) (hB : old.get i = B.toNat) (hN : new.get i = N.toNat) :
    feeAt F.toNat AF.toNat D0.toNat D1.toNat old new i = some (f.toNat, st.toNat, a.toNat) := by
  obtain ⟨dif, hm1, hD0, hdif, hm2, rfl, hm3, hle, rfl, hle2, rfl⟩ := h
  have e1 := chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hm1)
  have e2 := chkDiv_toNat_of_ne (x := D1 * B) hD0
  have e3 := chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hm2)
  have e4 := chkDiv_toNat_of_ne (x := F * dif) (y := Nat.toB256 feeDen) (by decide)
  have e5 := chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hm3)
  have e6 := chkDiv_toNat_of_ne (x := F * dif / Nat.toB256 feeDen * AF) (y := Nat.toB256 feeDen)
    (by decide)
  have e7 := chkSub_toNat_of_le (toNat_le_of_not_lt hle)
  have e8 := chkSub_toNat_of_le (toNat_le_of_not_lt hle2)
  rw [al_feeDen_toNat] at e4 e6
  unfold feeAt
  rw [hB, hN]
  rcases hdif with ⟨hgt, rfl⟩ | ⟨hgt, rfl⟩
  · have hgt' : (D1 * B / D0).toNat > N.toNat := B256.lt_iff_toNat_lt_toNat.mp hgt
    have e9 := chkSub_toNat_of_le (Nat.le_of_lt hgt')
    simp only [e1, e2, hgt', ↓reduceIte, e9, e3, e4, e5, e6, e7, e8, Option.bind_eq_bind,
      Option.bind_some]
  · have hgt' : ¬ (D1 * B / D0).toNat > N.toNat := fun h' =>
      hgt (B256.lt_iff_toNat_lt_toNat.mpr h')
    have e9 := chkSub_toNat_of_le (toNat_le_of_not_lt hgt)
    simp only [e1, e2, hgt', ↓reduceIte, e9, e3, e4, e5, e6, e7, e8, Option.bind_eq_bind,
      Option.bind_some]

/-! ## The calls -/

/-- The call a positive amount's `transferFrom` is, from the pool `pool` for coin word `C`. -/
abbrev alPullReq (sevm : Sevm) (C : Adr) (k : Nat) : List CallReq :=
  if alAmt sevm k = 0 then [] else
    [⟨C, transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
      (alAmt sevm k).toBytes, 0⟩]

/-- **One coin's pull children make exactly its `transferFrom` call**, in a non-static frame. -/
theorem al_kids_calls {sevm : Sevm} {C amt cr : B256} {k : Nat} {Lc : List Exec.Frame}
    (hk : AlPullKids sevm C k amt Lc cr) (hamt : amt = alAmt sevm k)
    (hs : sevm.isStatic = false) :
    Lc.filterMap (fun c => if c.sevm.isStatic then none else
      some (⟨c.sevm.currentTarget, c.sevm.data, c.sevm.value⟩ : CallReq)) =
      alPullReq sevm C.toAdr k := by
  subst hamt
  rcases hk with ⟨h0, rfl, -⟩ | ⟨hne, -, c, rfl, hp, -⟩ | ⟨hne, -, c0, c, c1, rfl, hb0, hp, hb1, -, -⟩
  · rw [alPullReq, ite_eq_left h0]; rfl
  · rw [alPullReq, ite_eq_right hne]
    simp only [List.filterMap_cons, List.filterMap_nil, hp.static, hs, Bool.false_eq_true,
      ↓reduceIte, hp.target, hp.data, hp.value]
  · rw [alPullReq, ite_eq_right hne]
    simp only [List.filterMap_cons, List.filterMap_nil, hb0.static, hb1.static, hp.static, hs,
      Bool.false_eq_true, ↓reduceIte, hp.target, hp.data, hp.value]

/-- The model's `transferFrom` list, coin by coin. -/
theorem al_pullCalls (caller : Nat) (a : V3) :
    pullCalls caller a =
      ((if a.get 0 > 0 then [.pull 0 caller (a.get 0)] else []) ++
        (if a.get 1 > 0 then [.pull 1 caller (a.get 1)] else [])) ++
        (if a.get 2 > 0 then [.pull 2 caller (a.get 2)] else []) := by
  unfold pullCalls
  by_cases h0 : a.get 0 > 0 <;> by_cases h1 : a.get 1 > 0 <;> by_cases h2 : a.get 2 > 0 <;>
    simp only [List.filterMap_cons, List.filterMap_nil, h0, h1, h2, ↓reduceIte, List.nil_append,
      List.cons_append, List.append_nil]

/-- **The model's calls, encoded at the frame's parties**, when the coins and the token enter
code frames and the amounts are the calldata words. -/
theorem al_modelCalls {D : Exec.Deriv} {a : V3} {m : Nat}
    (hamt : ∀ k : Fin 3, a.get k = (alAmt D.sevm k.val).toNat)
    (hcoin : ∀ k : Fin 3, framed D (coinAdr D k) = true) (htok : framed D (tokenAdr D) = true) :
    modelCalls D (pullCalls D.sevm.caller.toB256.toNat a ++ [.mint D.sevm.caller.toB256.toNat m]) =
      ((alPullReq D.sevm (coinAdr D 0) 0 ++ alPullReq D.sevm (coinAdr D 1) 1) ++
        alPullReq D.sevm (coinAdr D 2) 2) ++
        [⟨tokenAdr D, mintSel ++ D.sevm.caller.toB256.toBytes ++ word m, 0⟩] := by
  have hpos : ∀ k : Fin 3, (a.get k > 0) = ¬ (alAmt D.sevm k.val = 0) := fun k => by
    rw [hamt k]
    exact propext ⟨fun h e => by rw [e, B256.toNat_zero] at h; exact Nat.lt_irrefl 0 h,
      fun h => Nat.pos_of_ne_zero (toNat_ne_zero h)⟩
  have one : ∀ k : Fin 3,
      ((if a.get k > 0 then [ExtCall.pull k D.sevm.caller.toB256.toNat (a.get k)] else []).map
        (encodeCall D.sevm.currentTarget (coinAdr D) (tokenAdr D))).filter
        (fun r => framed D r.target) = alPullReq D.sevm (coinAdr D k) k.val := fun k => by
    by_cases h : alAmt D.sevm k.val = 0
    · have hn : ¬ a.get k > 0 := by rw [hpos k]; exact not_not_intro h
      rw [ite_eq_right hn, alPullReq, ite_eq_left h]; rfl
    · have hp : a.get k > 0 := by rw [hpos k]; exact h
      rw [ite_eq_left hp, alPullReq, ite_eq_right h]
      simp only [List.map_cons, List.map_nil, encodeCall, List.filter_cons, List.filter_nil,
        hcoin k, ↓reduceIte, word_toNat, hamt k]
  rw [modelCalls, al_pullCalls, List.map_append, List.map_append, List.map_append,
    List.filter_append, List.filter_append, List.filter_append, one 0, one 1, one 2]
  simp only [List.map_cons, List.map_nil, encodeCall, List.filter_cons, List.filter_nil, htok,
    ↓reduceIte, word_toNat]
  rfl

/-! ## Calldata words and the event -/

theorem al_arg0 (sevm : Sevm) : Sevm.argWord sevm 0 = alAmt sevm 0 :=
  congrArg (Sevm.dataWord sevm) (by decide)

theorem al_arg1 (sevm : Sevm) : Sevm.argWord sevm (0 + 1) = alAmt sevm 1 :=
  congrArg (Sevm.dataWord sevm) (by decide)

theorem al_arg2 (sevm : Sevm) : Sevm.argWord sevm (0 + 2) = alAmt sevm 2 :=
  congrArg (Sevm.dataWord sevm) (by decide)

/-- The decoded amounts are the words the body reads. -/
theorem al_amt (sevm : Sevm) : ∀ k : Fin 3, (argV3 sevm 0).get k = (alAmt sevm k.val).toNat
  | ⟨0, _⟩ => by show (Sevm.argWord sevm 0).toNat = _; rw [al_arg0]
  | ⟨1, _⟩ => by show (Sevm.argWord sevm (0 + 1)).toNat = _; rw [al_arg1]
  | ⟨2, _⟩ => by show (Sevm.argWord sevm (0 + 2)).toNat = _; rw [al_arg2]

/-- The decoded minimum is the word the slippage check reads. -/
theorem al_minArg (sevm : Sevm) : arg sevm 3 = (Sevm.dataWord sevm (Bytes.toB256 [0x64])).toNat :=
  congrArg (fun x => (Sevm.dataWord sevm x).toNat) (by decide)

/-- **The model's `AddLiquidity` event is the logged entry.** -/
theorem al_eventLog (sevm : Sevm) (f0 f1 f2 D1 T' : B256) :
    eventLog sevm.currentTarget (.addLiquidity sevm.caller.toB256.toNat (argV3 sevm 0)
      ⟨f0.toNat, f1.toNat, f2.toNat⟩ D1.toNat T'.toNat) = alLog sevm f0 f1 f2 D1 T' := by
  have ht : topicAddLiquidity = alTopic := by decide
  have h4 : alAmt sevm 0 = Sevm.dataWord sevm (Bytes.toB256 [4]) :=
    congrArg (Sevm.dataWord sevm) (by decide)
  have h24 : alAmt sevm 1 = Sevm.dataWord sevm (Bytes.toB256 [0x24]) :=
    congrArg (Sevm.dataWord sevm) (by decide)
  have h44 : alAmt sevm 2 = Sevm.dataWord sevm (Bytes.toB256 [0x44]) :=
    congrArg (Sevm.dataWord sevm) (by decide)
  simp only [eventLog, wordsV3, alLog, ht, toB256_toNat, word_toNat, argV3, arg, al_arg0, al_arg1,
    al_arg2, h4, h24, h44, List.append_assoc]

/-! ## The raw effect -/

/-- **Safety of `add_liquidity`**, given the certificate's checkedness. A successful frame of the
pool's runtime on the `add_liquidity` selector, entered at a `Checkpoint` with empty stack and
memory, under the frame premises (the coins and 3Crv are not precompiles; the pool's code is
nonempty; the identity precompile is ready; every child keeps the pool's storage and address
4's code), computed the model's step on the decoded call in the environment it observed, with
the raw effect Spec states. -/
theorem addLiquidity_raw_of (hchk : Cert.CheckedM code cert mems true)
    {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity)
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
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hlock, hval, hkill, hfee, A, cT, L0, L1, L2, L', D0, D1, cr0, cr1, cr2, b', M, img, G',
    hamp, hL, hTt, hTd, hTs, hTl, hTlogs, hD00, hD0, hk0, hk1, hk2, hT0, hc0, hc1, hc2, hD1, hlt,
    hst, hl, ho, hcd', -, hR, hW, hA, hm, w900, h⟩ :=
    xa_al_front hchk hcode hfork hlen hcd hsel hck.abs htok (fun i hi => hcoin ⟨i, hi⟩) hpc hid
      hkeep hidk hx
  have hkeep' : ∀ c ∈ L', ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x := fun c hc =>
    hkeep c (by rw [hL]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hc))
  have htokL : ((alLocked (pre.getStor sevm.currentTarget)).get tokenSlot) =
      (pre.getStor sevm.currentTarget).get tokenSlot := Stor.get_set_ne _ lock_ne_token _
  have htokB : ∀ k : Nat, k < 3 → balancesBase + Nat.toB256 k ≠ tokenSlot := fun k hk => by
    rcases three_cases hk with rfl | rfl | rfl <;> decide
  obtain ⟨f0, f1, f2, s0, s1, s2, D2, mint, cm, rfl, hbr, hmint, hslip, hadd, hmt, hmd, hmv, hms,
    hml, hsP, hlP, hoP⟩ := xa_al_back hchk hcode hfork hR hW hA hm w900 hst
      (by rw [htokL]; exact htok) htokB (by rw [hcd']; exact hpc) hkeep' h
  clear h hkeep' hkeep hidk hx
  -- the frame's children
  have hch : children ⟨0, sevm, pre, .ok post, exc⟩ = cT :: (L0 ++ L1 ++ L2 ++ [cm]) := hL
  -- storage words as the model's numbers
  have hbalL : ∀ k : Fin 3, balAt (alLocked (pre.getStor sevm.currentTarget)) k.val =
      (pre.getStor sevm.currentTarget).get (balanceSlot k) := fun k => by
    rw [balAt, Stor.get_set_ne _ (bal_ne_lock k.isLt)]; rfl
  have hbal : ∀ k : Fin 3, s.balances.get k =
      (balAt (alLocked (pre.getStor sevm.currentTarget)) k.val).toNat := fun k => by
    rw [hbalL]; exact (hck.abs.balances k).symm
  have hsb : s.balances = ⟨(balAt (alLocked (pre.getStor sevm.currentTarget)) 0).toNat,
      (balAt (alLocked (pre.getStor sevm.currentTarget)) 1).toNat,
      (balAt (alLocked (pre.getStor sevm.currentTarget)) 2).toNat⟩ :=
    V3.ext_get fun k => by
      rw [hbal k]
      rcases k with ⟨_ | _ | _ | n, hk⟩
      · rfl
      · rfl
      · rfl
      · omega
  have hcoinL : ∀ k : Fin 3, coinAdr ⟨0, sevm, pre, .ok post, exc⟩ k =
      (coinAt (alLocked (pre.getStor sevm.currentTarget)) k.val).toAdr := fun k => by
    rw [coinAt, Stor.get_set_ne _ (coin_ne_lock k.isLt)]; rfl
  have hk' : s.isKilled = false := by
    have e := hck.abs.isKilled
    rw [hkill] at e
    cases hs : s.isKilled
    · rfl
    · rw [hs] at e; exact absurd e (by decide)
  have hfeeN : feeAdj s = some (alFee (pre.getStor sevm.currentTarget)).toNat := by
    have hg := B256.or_eqCheck_ne_zero hfee
    have e1 := chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hg)
    have e2 := chkDiv_toNat_of_ne
      (x := (pre.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3])
      (y := Bytes.toB256 [8]) (by decide)
    rw [show (Bytes.toB256 [3]).toNat = 3 by decide] at e1
    rw [show (Bytes.toB256 [8]).toNat = 8 by decide] at e2
    unfold feeAdj
    rw [← hck.abs.fee, e1, Option.bind_eq_bind, Option.bind_some, e2]
  -- the environment
  generalize hTw : alWord cT = T at hD00 hD0 hT0 hbr hmint hadd hm hlP
  have hamt := al_amt sevm
  have hTnat : T.toNat = 0 → T = 0 := fun h => B256.toNat_inj _ _ (by rw [h]; rfl)
  have hT0' : ∀ k : Fin 3, T.toNat = 0 → 0 < (alAmt sevm k.val).toNat :=
    fun k h => hT0 (hTnat h) k.val k.isLt
  have hnew : V3.ofFnM (pullAdd (alEnv sevm T L0 L1 L2) T.toNat s.balances (argV3 sevm 0)) =
      some ⟨(alNew (pre.getStor sevm.currentTarget) cr0 cr1 cr2 0).toNat,
        (alNew (pre.getStor sevm.currentTarget) cr0 cr1 cr2 1).toNat,
        (alNew (pre.getStor sevm.currentTarget) cr0 cr1 cr2 2).toNat⟩ := by
    have p0 := al_pullAdd (k := 0) (e := alEnv sevm T L0 L1 L2) (T := T.toNat) hk0 rfl (hamt 0)
      (hbal 0) (hT0' 0) hc0
    have p1 := al_pullAdd (k := 1) (e := alEnv sevm T L0 L1 L2) (T := T.toNat) hk1 rfl (hamt 1)
      (hbal 1) (hT0' 1) hc1
    have p2 := al_pullAdd (k := 2) (e := alEnv sevm T L0 L1 L2) (T := T.toNat) hk2 rfl (hamt 2)
      (hbal 2) (hT0' 2) hc2
    unfold V3.ofFnM
    rw [p0, Option.bind_eq_bind, Option.bind_some, p1, Option.bind_some, p2, Option.bind_some]
    rfl
  have hT' := chkAdd_toNat_of_lt ((B256.nof_iff_not_add_lt _ _).mpr hadd)
  have hmin : arg sevm 3 ≤ mint.toNat := by rw [al_minArg]; exact toNat_le_of_not_lt hslip
  -- the model's step
  have hmodel : addLiquidity s (alEnv sevm T L0 L1 L2) (argV3 sevm 0) (arg sevm 3) =
      some ⟨{ s with balances := ⟨s0.toNat, s1.toNat, s2.toNat⟩ }, none,
        [.addLiquidity sevm.caller.toB256.toNat (argV3 sevm 0) ⟨f0.toNat, f1.toNat, f2.toNat⟩
          D1.toNat (T + mint).toNat],
        pullCalls sevm.caller.toB256.toNat (argV3 sevm 0) ++
          [.mint sevm.caller.toB256.toNat mint.toNat]⟩ := by
    rcases hbr with ⟨hT, rfl, rfl, rfl, rfl, rfl, rfl, hD2⟩ | ⟨hT, a0, a1, a2, hF0, hF1, hF2, hD2⟩
    · subst hT D2
      rcases hmint with ⟨-, hmD⟩ | ⟨h, -⟩
      · subst mint
        have hz : (⟨(0 : B256).toNat, (0 : B256).toNat, (0 : B256).toNat⟩ : V3) = V3.zero := by
          rw [B256.toNat_zero]; rfl
        have hD0z := hD00 rfl
        subst hD0z
        have hpos : 0 < D1.toNat := by
          have := B256.lt_iff_toNat_lt_toNat.mp hlt
          rw [B256.toNat_zero] at this; exact this
        rw [B256.toNat_zero] at hT' hnew
        rw [hz]
        exact al_model_first hk' hfeeN hamp (by rw [← B256.toNat_zero]; rfl) hnew hD1 hpos hmin
          rfl hT'
      · exact absurd rfl h
    · rcases hmint with ⟨h, -⟩ | ⟨-, hge, hmul, hD0ne, rfl⟩
      · exact absurd h hT
      have hTp : 0 < T.toNat := Nat.pos_of_ne_zero (toNat_ne_zero hT)
      have hfl : feeLoop (alFee (pre.getStor sevm.currentTarget)).toNat s.adminFee D0.toNat
          D1.toNat s.balances ⟨(alNew (pre.getStor sevm.currentTarget) cr0 cr1 cr2 0).toNat,
            (alNew (pre.getStor sevm.currentTarget) cr0 cr1 cr2 1).toNat,
            (alNew (pre.getStor sevm.currentTarget) cr0 cr1 cr2 2).toNat⟩ =
          some (⟨f0.toNat, f1.toNat, f2.toNat⟩, ⟨s0.toNat, s1.toNat, s2.toNat⟩,
            ⟨a0.toNat, a1.toNat, a2.toNat⟩) := by
        rw [hsb, ← hck.abs.adminFee]
        unfold feeLoop
        rw [al_feeAt (i := 0) hF0 rfl rfl, Option.bind_eq_bind, Option.bind_some,
          al_feeAt (i := 1) hF1 rfl rfl, Option.bind_some, al_feeAt (i := 2) hF2 rfl rfl,
          Option.bind_some]
      exact al_model_fee hk' hfeeN hamp rfl hTp (by rw [hsb]; exact hD0 hT) hnew hD1
        (B256.lt_iff_toNat_lt_toNat.mp hlt) hfl hD2 (chkSub_toNat_of_le (toNat_le_of_not_lt hge))
        (chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hmul)) (chkDiv_toNat_of_ne hD0ne) hmin rfl hT'
  have hdec : decodeCall sevm = .addLiquidity (argV3 sevm 0) (arg sevm 3) :=
    decodeCall_at (k := 3) rfl hsel hlen
  refine ⟨alEnv sevm T L0 L1 L2, ⟨{ s with balances := ⟨s0.toNat, s1.toNat, s2.toNat⟩ }, none,
        [.addLiquidity sevm.caller.toB256.toNat (argV3 sevm 0) ⟨f0.toNat, f1.toNat, f2.toNat⟩
          D1.toNat (T + mint).toNat],
        pullCalls sevm.caller.toB256.toNat (argV3 sevm 0) ++
          [.mint sevm.caller.toB256.toNat mint.toNat]⟩, ?step, ?raw⟩
  case step =>
    rw [hdec]
    show (if (alEnv sevm T L0 L1 L2).value = 0 then body s _ _ else none) = _
    rw [show (alEnv sevm T L0 L1 L2).value = 0 by rw [alEnv, hval]; rfl, ite_eq_left rfl]
    exact hmodel
  case raw =>
    refine ⟨?env, ?stor, ?logs, ?output, ?calls⟩
    case env =>
      refine ⟨rfl, rfl, rfl, fun k => ?_, fun T' hT' => ?_, fun _ => Or.inr ?_,
        fun h => (by cases h)⟩
      · rcases k with ⟨_ | _ | _ | n, hk⟩
        · exact al_coinObs (A := [cT]) (B := L1 ++ L2 ++ [cm]) (Lc := L0) hk0
            (by rw [hch]; simp only [List.cons_append, List.nil_append, List.append_assoc])
            (hcoinL ⟨0, hk⟩)
        · exact al_coinObs (A := cT :: L0) (Lc := L1) (B := L2 ++ [cm]) hk1
            (by rw [hch]; simp only [List.cons_append, List.append_assoc]) (hcoinL ⟨1, hk⟩)
        · exact al_coinObs (A := cT :: (L0 ++ L1)) (Lc := L2) (B := [cm]) hk2
            (by rw [hch]; simp only [List.cons_append, List.append_assoc]) (hcoinL ⟨2, hk⟩)
        · omega
      · cases hT'
        exact Or.inr ⟨0, cT, by rw [hch]; rfl, hTt, hTd, hTl, by rw [← hTw]; rfl⟩
      · exact ⟨cm, by rw [hch]; exact List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_singleton_self _)), by rw [hmt, htokL]; rfl,
          by rw [hmd, List.append_assoc]; exact List.take_left' rfl, hml⟩
    case stor =>
      rw [hdec]
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · have e0 : balancesBase + Nat.toB256 0 ≠ x := hx (.bal 0) (bal_mem 0)
        have e1 : balancesBase + Nat.toB256 1 ≠ x := hx (.bal 1) (bal_mem 1)
        have e2 : balancesBase + Nat.toB256 2 ≠ x := hx (.bal 2) (bal_mem 2)
        rw [hsP x, alStored, Stor.get_set_ite]
        by_cases hxl : lockSlot = x
        · subst hxl
          rw [ite_eq_left rfl]
          exact hlock.symm
        · rw [ite_eq_right hxl, Stor.get_set_ne _ e2, Stor.get_set_ne _ e1, Stor.get_set_ne _ e0,
            alLocked, Stor.get_set_ne _ hxl]
          rfl
      · have hf' : f = .bal 0 ∨ f = .bal 1 ∨ f = .bal 2 := by
          simpa only [footprint, balFlds, List.mem_cons, List.not_mem_nil, or_false] using hf
        rcases hf' with rfl | rfl | rfl
        · show ((post.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 0)).toNat = _
          rw [hsP, alStored, Stor.get_set_ne _ (bal_ne_lock (by decide)),
            Stor.get_set_ne _ (bal_ne_bal (i := 2) (j := 0) (by decide) (by decide) (by decide)),
            Stor.get_set_ne _ (bal_ne_bal (i := 1) (j := 0) (by decide) (by decide) (by decide)),
            Stor.get_set_self]
          rfl
        · show ((post.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 1)).toNat = _
          rw [hsP, alStored, Stor.get_set_ne _ (bal_ne_lock (by decide)),
            Stor.get_set_ne _ (bal_ne_bal (i := 2) (j := 1) (by decide) (by decide) (by decide)),
            Stor.get_set_self]
          rfl
        · show ((post.getStor sevm.currentTarget).get (balancesBase + Nat.toB256 2)).toNat = _
          rw [hsP, alStored, Stor.get_set_ne _ (bal_ne_lock (by decide)), Stor.get_set_self]
          rfl
    case logs =>
      rw [hlP, hl, hch]
      show _ = _ ++ _ ++ [eventLog sevm.currentTarget (.addLiquidity sevm.caller.toB256.toNat
        (argV3 sevm 0) ⟨f0.toNat, f1.toNat, f2.toNat⟩ D1.toNat (T + mint).toNat)]
      rw [al_eventLog]
      simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil, hTlogs,
        List.nil_append, List.append_nil, List.append_assoc]
    case output =>
      rw [hoP, ho]; rfl
    case calls =>
      intro hs
      replace hs : sevm.isStatic = false := hs
      have hfc : ∀ k : Fin 3, framed ⟨0, sevm, pre, .ok post, exc⟩
          (coinAdr ⟨0, sevm, pre, .ok post, exc⟩ k) = true := fun k => by
        simp only [framed, coinAdr, entryStor, hcoin k, decide_false, Bool.not_false,
          Bool.true_or]
      have hft : framed ⟨0, sevm, pre, .ok post, exc⟩ (tokenAdr ⟨0, sevm, pre, .ok post, exc⟩) =
          true := by
        simp only [framed, tokenAdr, entryStor, htok, decide_false, Bool.not_false,
          Bool.true_or]
      have hmc := al_modelCalls (D := ⟨0, sevm, pre, .ok post, exc⟩) (a := argV3 sevm 0)
        (m := mint.toNat) hamt hfc hft
      change _ = modelCalls _ (pullCalls sevm.caller.toB256.toNat (argV3 sevm 0) ++
        [.mint sevm.caller.toB256.toNat mint.toNat])
      rw [hmc, CallsOf, hch, List.filterMap_cons, hTs, ite_eq_left rfl, List.filterMap_append,
        List.filterMap_append, List.filterMap_append, al_kids_calls hk0 rfl hs,
        al_kids_calls hk1 rfl hs, al_kids_calls hk2 rfl hs, hcoinL 0, hcoinL 1, hcoinL 2]
      simp only [List.filterMap_cons, List.filterMap_nil, hms, hs, Bool.false_eq_true,
        ↓reduceIte, hmt, hmd, hmv, htokL, word_toNat, tokenAdr, entryStor]
      rfl

end Blanc.Lift.Curve3Pool
