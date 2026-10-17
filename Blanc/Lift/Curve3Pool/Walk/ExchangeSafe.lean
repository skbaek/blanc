import Blanc.Lift.Curve3Pool.Walk.ExchangeModel
import Blanc.Lift.Curve3Pool.Walk.ExchangeObserve

/-! # Safety of the exchange frame -/
namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- Storage writes and model vector writes have the same order, including coincident indices. -/
theorem ex_stor_bal {σ : Stor} {s : State} (ha : Abstracts σ s) (i j k : Fin 3) (vi vj : B256) :
    (((σ.set (balanceSlot i) vi).set (balanceSlot j) vj).get (balanceSlot k)).toNat =
      ((s.balances.set i vi.toNat).set j vj.toNat).get k := by
  have hget (v : V3) (a b : Fin 3) (n : Nat) :
      (v.set a n).get b = if a = b then n else v.get b := by
    rcases a with ⟨_ | _ | _ | m, ha⟩ <;>
      rcases b with ⟨_ | _ | _ | m, hb⟩ <;>
      first | omega | simp only [V3.set,V3.get,Fin.ext_iff,Nat.reduceAdd,Nat.reduceEqDiff,↓reduceIte]
  have hinj (a b : Fin 3) : balanceSlot a = balanceSlot b ↔ a = b := by
    constructor
    · intro h; exact Fld.bal.inj (Fld.slot_inj (f := .bal a) (g := .bal b) h)
    · intro h; rw [h]
  rw [hget,hget]
  by_cases hj : j = k
  · subst k
    rw [Stor.get_set_self,ite_eq_left rfl]
  · rw [Stor.get_set_ne _ (fun h => hj ((hinj j k).mp h)),ite_eq_right hj]
    by_cases hi : i = k
    · subst k; rw [Stor.get_set_self,ite_eq_left rfl]
    · rw [Stor.get_set_ne _ (fun h => hi ((hinj i k).mp h)),ite_eq_right hi]
      exact ha.balances k

/-- A successful exchange on the deployed runtime computes the model step and raw effect. -/
theorem exchange_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : PoolCallsKeep ⟨0,sevm,pre,.ok post,exc⟩)
    (hidk : ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧ RawEffect ⟨0,sevm,pre,.ok post,exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  have hcoinI : (exI sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm)).toAdr := fun hi => by
    simpa only [coinSlot,toB256_toNat] using hcoin ⟨(exI sevm).toNat,hi⟩
  have hcoinJ : (exJ sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinsBase + exJ sevm)).toAdr := fun hj => by
    simpa only [coinSlot,toB256_toNat] using hcoin ⟨(exJ sevm).toNat,hj⟩
  obtain ⟨hlock,hval,hkill,hi3,hj3,x0,x1,x2,hxp,Lp,cp,cq,D,y,amp,hL,hcpm,hpt,hpd,hpv,hps,hpok,
    hpull,hmx,hax,hamp,⟨hi,hj,hy⟩,hy1,hy2,hmf,hsf,hmo,hmin,hma,hmap,hbi,hbj1,hbj2,
    hqt,hqd,hqv,hqs,hqok,hstor,hlogs,hout⟩ :=
    xa_exchange hcode hfork hlen hcd hsel rfl hck.abs hcoinI hcoinJ hpc hid hkeep hidk hx
  let i : Fin 3 := ⟨(exI sevm).toNat,hi3⟩
  let j : Fin 3 := ⟨(exJ sevm).toNat,hj3⟩
  have hI : Nat.toB256 i.val = exI sevm := toB256_toNat _
  have hJ : Nat.toB256 j.val = exJ sevm := toB256_toNat _
  have hpt' : cp.sevm.currentTarget = coinAdr ⟨0,sevm,pre,.ok post,exc⟩ i := by
    simpa only [coinAdr,entryStor,coinSlot,hI] using hpt
  have hqt' : cq.sevm.currentTarget = coinAdr ⟨0,sevm,pre,.ok post,exc⟩ j := by
    simpa only [coinAdr,entryStor,coinSlot,hJ] using hqt
  obtain ⟨bp,bq,henv,hpn,hcalls⟩ := ex_observed (i := i) (j := j) rfl rfl hL hcpm hpt' hpd hpv
    hps hpok hqt' hqd hqv hqs hqok hpull hcoin
  have hb : V3.mk (balAt (pre.getStor sevm.currentTarget) 0).toNat
      (balAt (pre.getStor sevm.currentTarget) 1).toNat
      (balAt (pre.getStor sevm.currentTarget) 2).toNat = s.balances :=
    V3.ext_get fun k => by rw [← ex_w3_nat]; exact ex_bal_nat hck.abs k
  rw [hb] at hxp
  have hk : s.isKilled = false := boolWord_inj (hck.abs.isKilled.symm.trans hkill)
  have hmodel := ex_model_words (i := i) (j := j) (e := exEnv sevm i j bp bq) hck.abs hk hxp hpn hmx hax hamp hy
    hy1 hy2 hmf hsf hmo (toNat_le_of_not_lt hmin) hma hmap hbi hbj1 hbj2
    (by simp only [exEnv,decide_true])
  have hdec : decodeCall sevm = .exchange i.val j.val (exDx sevm).toNat (exMinDy sevm).toNat := by
    have hd := decodeCall_at (k := 6) rfl hsel hlen
    change decodeCall sevm = .exchange (exI sevm).toNat (exJ sevm).toNat
      (exDx sevm).toNat (exMinDy sevm).toNat
    convert hd using 1; congr 1
  refine ⟨exEnv sevm i j bp bq,?o,?step,?raw⟩
  case step =>
    rw [hdec]
    show (if (exEnv sevm i j bp bq).value = 0 then _ else none) = _
    rw [show (exEnv sevm i j bp bq).value = 0 by rw [exEnv,hval]; rfl]
    simp only [body,idx,i.isLt,j.isLt,↓reduceDIte,↓reduceIte,Option.bind_eq_bind,Option.bind_some]
    exact hmodel
  case raw =>
    refine ⟨henv,?stor,?logs,?output,?calls⟩
    case stor =>
      rw [hdec]
      refine ⟨fun x hx => ?_,fun f hf => ?_⟩
      · have hni : balancesBase + exI sevm ≠ x := by
          simpa only [Fld.slot,balanceSlot,hI] using hx (.bal i) (bal_mem i)
        have hnj : balancesBase + exJ sevm ≠ x := by
          simpa only [Fld.slot,balanceSlot,hJ] using hx (.bal j) (bal_mem j)
        rw [hstor,Stor.get_set_ne _ hnj,Stor.get_set_ne _ hni]
        rfl
      · have hf' : ∃ k : Fin 3, f = .bal k := by
          have h : f = .bal 0 ∨ f = .bal 1 ∨ f = .bal 2 := by
            simpa only [footprint,balFlds,List.mem_cons,List.not_mem_nil,or_false] using hf
          rcases h with rfl | rfl | rfl
          · exact ⟨0,rfl⟩
          · exact ⟨1,rfl⟩
          · exact ⟨2,rfl⟩
        obtain ⟨k,rfl⟩ := hf'
        show ((post.getStor sevm.currentTarget).get (balanceSlot k)).toNat = _
        have hki : balancesBase + exI sevm = balanceSlot i := by rw [balanceSlot,hI]
        have hkj : balancesBase + exJ sevm = balanceSlot j := by rw [balanceSlot,hJ]
        rw [hstor,hki,hkj]
        exact ex_stor_bal hck.abs i j k _ _
    case logs =>
      have ht : topicTokenExchange = exTopic := by decide
      rw [hlogs,hL]
      show _ = _ ++ _ ++ [eventLog sevm.currentTarget _]
      simp only [eventLog,exEnv,word,toB256_toNat,hI,hJ,ht]
      rfl
    case output =>
      exact hout
    case calls =>
      exact hcalls
end Blanc.Lift.Curve3Pool
