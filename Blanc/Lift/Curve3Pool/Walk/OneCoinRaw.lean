import Blanc.Lift.Curve3Pool.Walk.OneCoin
import Blanc.Lift.Curve3Pool.Walk.ExchangeSafe

/-!
# `remove_liquidity_one_coin`'s raw effect

From the walk (`xa_oneCoin`): the model's step on the decoded call (`oc_model`, the checked
arithmetic of lines 678–681 read off the machine words), the environment the frame observed
(`ocEnv`: the `totalSupply()` reply, the burn, and the push of coin `i`), its calls in order
(the burn, then the push), the event and the storage effect, giving
`removeLiquidityOneCoin_raw_of` (the certificate's checkedness as a premise).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The model result from the walk's checked words. -/
theorem oc_model {s : State} {e : Env} {i : Fin 3} {σ : Stor} {amount minAmt : Nat}
    {dy fee : B256} (ha : Abstracts σ s) (hk : s.isKilled = false)
    (hcw : calcWithdrawOne s e amount i = some (dy.toNat, fee.toNat))
    (hmin : minAmt ≤ dy.toNat) (hmf : fee.Nofm (σ.get adminFeeSlot))
    (hadd : ¬ dy + fee * σ.get adminFeeSlot / ocDen < dy)
    (hsub : ¬ σ.get (balanceSlot i) < dy + fee * σ.get adminFeeSlot / ocDen)
    (hburn : e.burnOk = true) (hpush : (e.coin i).pushOk = true) :
    removeLiquidityOneCoin s e amount i minAmt = some
      ⟨{s with balances := s.balances.set i (σ.get (balanceSlot i) -
          (dy + fee * σ.get adminFeeSlot / ocDen)).toNat}, none,
        [.removeLiquidityOne e.caller amount dy.toNat],
        [.burn e.caller amount, .push i e.caller dy.toNat]⟩ := by
  have rk : req (s.isKilled = false) = some () := by unfold req; rw [ite_eq_left hk]
  have rmin : req (dy.toNat ≥ minAmt) = some () := by unfold req; rw [ite_eq_left hmin]
  have rburn : req (e.burnOk = true) = some () := by unfold req; rw [ite_eq_left hburn]
  have rpush : req ((e.coin i).pushOk = true) = some () := by
    unfold req; rw [ite_eq_left hpush]
  have hd : ocDen.toNat = feeDen := by decide
  unfold removeLiquidityOneCoin
  rw [rk, Option.bind_eq_bind, Option.bind_some]
  change (calcWithdrawOne s e amount i).bind _ = _
  rw [hcw, Option.bind_some]
  dsimp only
  have hm : chkMul fee.toNat s.adminFee = some (fee * σ.get adminFeeSlot).toNat := by
    rw [← ha.adminFee]; exact chkMul_toNat_of_nofm hmf
  have hq : chkDiv (fee * σ.get adminFeeSlot).toNat feeDen =
      some (fee * σ.get adminFeeSlot / ocDen).toNat := by
    rw [← hd]; exact chkDiv_toNat_of_ne (by decide)
  have hb : chkSub (s.balances.get i) (dy + fee * σ.get adminFeeSlot / ocDen).toNat =
      some (σ.get (balanceSlot i) - (dy + fee * σ.get adminFeeSlot / ocDen)).toNat := by
    rw [← ha.balances i]; exact chkSub_toNat_of_le (toNat_le_of_not_lt hsub)
  rw [rmin, Option.bind_some, hm, cw_some_bind, hq, cw_some_bind,
    chkAdd_toNat_of_lt ((B256.nof_iff_not_add_lt _ _).mpr hadd), cw_some_bind, hb, cw_some_bind,
    rburn, Option.bind_some, rpush, Option.bind_some]

/-- The environment `remove_liquidity_one_coin` observes: the supply reply `T`, the burn, and
the push of coin `i` (no balance reads, no pull, no mint). -/
def ocEnv (sevm : Sevm) (i : Fin 3) (T : Nat) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun k => ⟨none, none, false, decide (k = i)⟩, some T, false, true⟩

/-- One balance store and the model's one balance write agree at every balance field. -/
theorem oc_stor_bal {σ : Stor} {s : State} (ha : Abstracts σ s) (i k : Fin 3) (v : B256) :
    ((σ.set (balanceSlot i) v).get (balanceSlot k)).toNat = (s.balances.set i v.toNat).get k := by
  have hget (w : V3) (a b : Fin 3) (n : Nat) :
      (w.set a n).get b = if a = b then n else w.get b := by
    rcases a with ⟨_ | _ | _ | m, ha⟩ <;>
      rcases b with ⟨_ | _ | _ | m, hb⟩ <;>
      first | omega | simp only [V3.set,V3.get,Fin.ext_iff,Nat.reduceAdd,Nat.reduceEqDiff,↓reduceIte]
  rw [hget]
  by_cases hik : i = k
  · subst k
    rw [Stor.get_set_self, ite_eq_left rfl]
  · have hne : balanceSlot i ≠ balanceSlot k :=
      fun h => hik (Fld.bal.inj (Fld.slot_inj (f := .bal i) (g := .bal k) h))
    rw [Stor.get_set_ne _ hne, ite_eq_right hik]
    exact ha.balances k

section

variable {sevm : Sevm} {pre post : Devm} {s : State}

/-- **`remove_liquidity_one_coin`'s raw effect**, given the certificate's checkedness. -/
theorem removeLiquidityOneCoin_raw_of (hc : Cert.CheckedM code cert mems true)
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
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
  have hcoinJ : (exJ sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinsBase + exJ sevm)).toAdr := fun hi => by
    simpa only [coinSlot, toB256_toNat] using hcoin ⟨(exJ sevm).toNat, hi⟩
  obtain ⟨hlock, hval, hkill, cs, cb, cp, hi, dy, fee, hL, hsw, hmod, hmin, hmf, hadd, hsub,
    hbt, hbd, hbv, hbs, hblen, hpt, hpd, hpv, hps, hpok, hstor, hlogs, hout⟩ :=
    xa_oneCoin hc hcode hfork hlen hcd hsel rfl hck.abs htok hcoinJ hpc hid hkeep hidk hx
  let i : Fin 3 := ⟨(exJ sevm).toNat, hi⟩
  have hI : Nat.toB256 i.val = exJ sevm := toB256_toNat _
  have hch : children ⟨0, sevm, pre, .ok post, exc⟩ = [cs, cb, cp] := hL
  have ha0 : arg sevm 0 = (ocAmt sevm).toNat := by
    unfold arg Sevm.argWord
    rw [show (32 * 0 + 4 : B256) = Bytes.toB256 [4] by decide]
  have ha1 : arg sevm 1 = (exJ sevm).toNat := by
    unfold arg Sevm.argWord
    rw [show (32 * 1 + 4 : B256) = Bytes.toB256 [0x24] by decide]
  have ha2 : arg sevm 2 = (Sevm.dataWord sevm (Bytes.toB256 [0x44])).toNat := by
    unfold arg Sevm.argWord
    rw [show (32 * 2 + 4 : B256) = Bytes.toB256 [0x44] by decide]
  have hdec : decodeCall sevm = .removeLiquidityOneCoin (arg sevm 0) (arg sevm 1) (arg sevm 2) :=
    decodeCall_at (k := 10) rfl hsel hlen
  have hi1 : arg sevm 1 < 3 := by rw [ha1]; exact hi
  have hk : s.isKilled = false := boolWord_inj (hck.abs.isKilled.symm.trans hkill)
  have hbK : balanceSlot i = balancesBase + exJ sevm := by rw [balanceSlot, hI]
  have hmodel := oc_model (i := i) (e := ocEnv sevm i (vSupply cs).toNat) hck.abs hk
    (hmod _ rfl rfl) (toNat_le_of_not_lt hmin) hmf hadd (by rw [hbK]; exact hsub) rfl
    (by simp only [ocEnv, decide_true])
  refine ⟨ocEnv sevm i (vSupply cs).toNat, ?o, ?step, ?raw⟩
  case step =>
    rw [hdec]
    show (if (ocEnv sevm i (vSupply cs).toNat).value = 0 then _ else none) = _
    rw [show (ocEnv sevm i (vSupply cs).toNat).value = 0 by rw [ocEnv, hval]; rfl,
      ite_eq_left rfl]
    simp only [body, idx, hi1, ↓reduceDIte, Option.bind_eq_bind, Option.bind_some]
    rw [show (⟨arg sevm 1, hi1⟩ : Fin 3) = i from Fin.ext ha1, ha0, ha2]
    exact hmodel
  case raw =>
    have hci : coinAdr ⟨0, sevm, pre, .ok post, exc⟩ i =
        ((pre.getStor sevm.currentTarget).get (coinsBase + exJ sevm)).toAdr := by
      change ((pre.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i.val)).toAdr = _
      rw [hI]
    have hcbm : cb ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := by
      rw [hch]; simp only [List.mem_cons, true_or, or_true]
    have hcpm : cp ∈ children ⟨0, sevm, pre, .ok post, exc⟩ := by
      rw [hch]; simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]
    have hbSel : cb.sevm.data.take 4 = burnFromSel := by
      rw [hbd, List.append_assoc]; exact List.take_left' rfl
    have hpSel : cp.sevm.data.take 4 = transferSel := by
      rw [hpd]; unfold exPushData; rw [List.append_assoc]; exact List.take_left' rfl
    refine ⟨⟨rfl, rfl, rfl, fun k => ⟨fun _ h => (by cases h), fun _ h => (by cases h),
      fun h => (by cases h), fun h => ?_⟩, fun T hT => ?_, fun h => (by cases h),
      fun _ => .inr ⟨cb, hcbm, hbt, hbSel, hblen⟩⟩, ?stor, ?logs, hout, ?calls⟩
    · have heq : k = i := of_decide_eq_true h
      subst heq
      exact .inr ⟨cp, hcpm, by rw [hci]; exact hpt, hpSel, hpok⟩
    · cases hT
      exact .inr ⟨0, cs, by rw [hch]; rfl, hsw.target, hsw.data, hsw.len, rfl⟩
    case stor =>
      rw [hdec]
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · have hne : balancesBase + exJ sevm ≠ x := by
          simpa only [Fld.slot, balanceSlot, hI] using hx (.bal i) (bal_mem i)
        rw [hstor, Stor.get_set_ne _ hne]
        rfl
      · have hf' : ∃ k : Fin 3, f = .bal k := by
          have h : f = .bal 0 ∨ f = .bal 1 ∨ f = .bal 2 := by
            simpa only [footprint, balFlds, List.mem_cons, List.not_mem_nil, or_false] using hf
          rcases h with rfl | rfl | rfl
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
        obtain ⟨k, rfl⟩ := hf'
        show ((post.getStor sevm.currentTarget).get (balanceSlot k)).toNat = _
        rw [hstor, ocBal, ← hbK]
        exact oc_stor_bal hck.abs i k _
    case logs =>
      have ht : topicRemoveLiquidityOne = ocTopic := by decide
      rw [hlogs, hch]
      show _ = _ ++ _ ++ [eventLog sevm.currentTarget _]
      simp only [eventLog, ocEnv, word, toB256_toNat, ht]
    case calls =>
      intro hs
      replace hs : sevm.isStatic = false := hs
      simp only [CallsOf, modelCalls, hch, List.filterMap_cons, List.filterMap_nil, hsw.static,
        hbs, hps, hs, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, encodeCall,
        List.filter_cons, List.filter_nil, framed, tokenAdr, entryStor, hci,
        decide_eq_false htok, decide_eq_false (hcoinJ hi), Bool.not_false, Bool.true_or,
        hbt, hpt, hbd, hpd, hbv, hpv, exPushData, word, toB256_toNat, ocEnv]

end

end Blanc.Lift.Curve3Pool
