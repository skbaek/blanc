import Blanc.Lift.Curve3Pool.Walk.Exchange

/-! # The environment and physical calls observed by exchange -/
namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- Only the selected input coin is pulled and the selected output coin is pushed. -/
def exEnv (sevm : Sevm) (i j : Fin 3) (bp bq : Option Nat) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun k => ⟨if k = i then bp else none, if k = i then bq else none,
      decide (k = i), decide (k = j)⟩, none, false, false⟩

/-- The optional balance reads, the pull, and the push witness the model environment. -/
theorem ex_observed {sevm : Sevm} {pre post : Devm} {exc : Exec 0 sevm pre (.ok post)}
    {i j : Fin 3} (hi : i.val = (exI sevm).toNat) (_hj : j.val = (exJ sevm).toNat)
    {Lp : List Exec.Frame} {cp cq : Exec.Frame} {D out : B256}
    (hL : children ⟨0,sevm,pre,.ok post,exc⟩ = Lp ++ [cq])
    (hcpm : cp ∈ Lp)
    (hpt : cp.sevm.currentTarget = coinAdr ⟨0,sevm,pre,.ok post,exc⟩ i)
    (hpd : cp.sevm.data = exPullData sevm) (hpv : cp.sevm.value = 0)
    (hps : cp.sevm.isStatic = sevm.isStatic) (hpok : RawCallOk cp.post.output)
    (hqt : cq.sevm.currentTarget = coinAdr ⟨0,sevm,pre,.ok post,exc⟩ j)
    (hqd : cq.sevm.data = exPushData sevm out) (hqv : cq.sevm.value = 0)
    (hqs : cq.sevm.isStatic = sevm.isStatic) (hqok : RawCallOk cq.post.output)
    (hpull : ExPull sevm ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm)) D Lp cp)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) :
    ∃ bp bq, EnvOf ⟨0,sevm,pre,.ok post,exc⟩ (exEnv sevm i j bp bq) ∧
      pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat = some D.toNat ∧
      (sevm.isStatic = false →
        CallsOf ⟨0,sevm,pre,.ok post,exc⟩ =
          modelCalls ⟨0,sevm,pre,.ok post,exc⟩
            [.pull i sevm.caller.toB256.toNat (exDx sevm).toNat, .push j sevm.caller.toB256.toNat out.toNat]) := by
  have hI : Nat.toB256 i.val = exI sevm := by rw [hi, toB256_toNat]
  have hci : coinAdr ⟨0,sevm,pre,.ok post,exc⟩ i =
      ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm)).toAdr := by
    change ((pre.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i.val)).toAdr = _
    rw [hI]
  have hpm : cp ∈ children ⟨0,sevm,pre,.ok post,exc⟩ := by
    rw [hL]; exact List.mem_append_left _ hcpm
  have hqm : cq ∈ children ⟨0,sevm,pre,.ok post,exc⟩ := by
    rw [hL]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hpSel : cp.sevm.data.take 4 = transferFromSel := by
    rw [hpd]; unfold exPullData
    rw [List.append_assoc, List.append_assoc]
    exact List.take_left' rfl
  have hqSel : cq.sevm.data.take 4 = transferSel := by
    rw [hqd]; unfold exPushData
    rw [List.append_assoc]
    exact List.take_left' rfl
  have hiEq : i = feeIndex ↔ exI sevm = 2 := by
    constructor
    · intro h; subst i; rw [← hI]; rfl
    · intro h; apply Fin.ext; rw [hi, h]; rfl
  rcases hpull with ⟨hne, rfl, rfl⟩ | ⟨he, c1, c2, rfl, hb1, hb2, hsub, rfl⟩
  · refine ⟨none, none, ?_, ?_, ?_⟩
    · refine ⟨rfl,rfl,rfl,fun k => ?_,fun _ h => (by cases h),
        fun h => (by cases h),fun h => (by cases h)⟩
      refine ⟨fun _ h => ?_,fun _ h => ?_,fun h => ?_,fun h => ?_⟩
      · simp only [exEnv, ite_self] at h; cases h
      · simp only [exEnv, ite_self] at h; cases h
      · have heq : k = i := of_decide_eq_true h
        subst k; exact Or.inr ⟨cp,hpm,hpt,hpSel,hpok⟩
      · have heq : k = j := of_decide_eq_true h
        subst k; exact Or.inr ⟨cq,hqm,hqt,hqSel,hqok⟩
    · simp only [pullIn, exEnv, decide_true,
        ite_eq_right (fun h => hne (hiEq.mp h)), req, ite_true, Option.bind_eq_bind,
        Option.bind_some]
    · intro hs
      simp only [CallsOf, modelCalls, hL, List.cons_append, List.nil_append, List.filterMap_cons, List.filterMap_nil,
        hps,hqs,hs, Bool.false_eq_true, ↓reduceIte, List.map_cons,List.map_nil,encodeCall,
        List.filter_cons,List.filter_nil,framed,coinAdr,entryStor,
        decide_eq_false (hcoin i),decide_eq_false (hcoin j),Bool.not_false,Bool.true_or,
        hpt,hqt,hpd,hqd,hpv,hqv,exPullData,exPushData,word,toB256_toNat]
  · refine ⟨some (exAns c1).toNat, some (exAns c2).toNat, ?_, ?_, ?_⟩
    · refine ⟨rfl,rfl,rfl,fun k => ?_,fun _ h => (by cases h),
        fun h => (by cases h),fun h => (by cases h)⟩
      refine ⟨fun w hw => ?_,fun w hw => ?_,fun h => ?_,fun h => ?_⟩
      · by_cases hk : k = i
        · subst k
          simp only [exEnv,ite_true,Option.some.injEq] at hw
          subst w
          exact Or.inr ⟨0,c1,by rw [hL]; rfl,by rw [hci]; exact hb1.target,
            hb1.data,hb1.len,rfl⟩
        · simp only [exEnv,ite_eq_right hk] at hw; cases hw
      · by_cases hk : k = i
        · subst k
          simp only [exEnv,ite_true,Option.some.injEq] at hw
          subst w
          exact Or.inr ⟨(exAns c1).toNat,0,2,by simp only [exEnv,ite_true],by decide,
            ⟨c1,by rw [hL]; rfl,by rw [hci]; exact hb1.target,hb1.data,hb1.len,rfl⟩,
            ⟨c2,by rw [hL]; rfl,by rw [hci]; exact hb2.target,hb2.data,hb2.len,rfl⟩⟩
        · simp only [exEnv,ite_eq_right hk] at hw; cases hw
      · have heq : k = i := of_decide_eq_true h
        subst k; exact Or.inr ⟨cp,hpm,hpt,hpSel,hpok⟩
      · have heq : k = j := of_decide_eq_true h
        subst k; exact Or.inr ⟨cq,hqm,hqt,hqSel,hqok⟩
    · simp only [pullIn,exEnv,ite_eq_left (hiEq.mpr he),ite_true,decide_true,req,
        Option.bind_eq_bind,Option.bind_some]
      exact chkSub_toNat_of_le (toNat_le_of_not_lt hsub)
    · intro hs
      simp only [CallsOf, modelCalls, hL, List.cons_append, List.nil_append, List.filterMap_cons, List.filterMap_nil,
        hb1.static,hb2.static,hps,hqs,hs, Bool.false_eq_true, ↓reduceIte,
        List.map_cons,List.map_nil,encodeCall,List.filter_cons,List.filter_nil,
        framed,coinAdr,entryStor,decide_eq_false (hcoin i),decide_eq_false (hcoin j),
        Bool.not_false,Bool.true_or,hpt,hqt,hpd,hqd,hpv,hqv,exPullData,exPushData,word,toB256_toNat]
end Blanc.Lift.Curve3Pool
