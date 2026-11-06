import Blanc.Composition.Curve3PoolExitCoins

/-!
# `exchange`'s pulls from a cold start

Each coin's `transferFrom` in terms of what the frame stands on: `dai_pull_child`, `usdt_pull_child`, `usdc_pull_child`.
A child's cost, what it moves, and the ledger it leaves. USDT's is the only one entered with warm slots, after the pool's
first `balanceOf`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool

/-! ## DAI -/

section Dai

open Blanc.Lift.Dai

variable {s : Sevm} {b : Devm}

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The allowance's charge in DAI's `transferFrom`, beyond the fixed cost: its reads, and its write unless unlimited. -/
def daiAllowG (al v : Nat) : Nat := if al = 2 ^ 256 - 1 then 9184 else 10041 + debitG v

/-- The allowance's refund in DAI's `transferFrom`. -/
def allowEmpties (al v : Nat) : Nat := if al = 2 ^ 256 - 1 then 0 else empties al v

/-- DAI's `transferFrom` leaves its ledger: the allowance step, then the move. -/
def daiPulled (σ : Stor) (kr kt ka v : B256) : Stor :=
  let σ1 := if σ.get ka = maxUint then σ else σ.set ka (σ.get ka - v)
  (σ1.set kr (σ1.get kr - v)).set kt (σ1.get kt + v)

theorem max_iff (x : B256) : x = maxUint ↔ x.toNat = 2 ^ 256 - 1 :=
  ⟨fun h => by rw [h]; decide, fun h => B256.toNat_inj _ _ (h.trans (by decide))⟩

/-- **DAI's `transferFrom` from a cold start**, its source not its spender. -/
theorem dai_pull_child {σ : Stor} {kr kt ka v : B256} (hσ : b.getStor s.currentTarget = σ)
    (hkr : ky (pSrc s) = kr) (hkt : ky (pTo s) = kt) (hka : ak (pSrc s) s.caller.toB256 = ka) (hv : pVal s = v)
    (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hc : Clean b)
    (hk : ∀ k, (⟨s.currentTarget, k⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (ho : (getOrigAcct s s.currentTarget).stor = σ)
    (hself : (pSrc s).toAdr ≠ s.caller) (hne : kr ≠ kt) (hra : ka ≠ kr) (hta : ka ≠ kt)
    (hle : v.toNat ≤ (σ.get kr).toNat)
    (hal : σ.get ka ≠ maxUint → v.toNat ≤ (σ.get ka).toNat)
    (hnof : v.toNat + (σ.get kt).toNat < 2 ^ 256) :
    pullG s b = 434 + daiAllowG (σ.get ka).toNat v.toNat + debitG v.toNat + creditG (σ.get kt).toNat v.toNat ∧
      Mv [s.currentTarget] ((4800 * (allowEmpties (σ.get ka).toNat v.toNat + empties (σ.get kr).toNat v.toNat) : Nat) : Int) b (pullPost s b 0) ∧
      (pullPost s b 0).getStor s.currentTarget = daiPulled σ kr kt ka v := by
  have hpMax : pMax s b ↔ σ.get ka = maxUint := by
    unfold pMax
    rw [← hka, ak_allow, hσ]
  have hA0 : At s.currentTarget [] σ b :=
    ⟨fun k => ⟨fun h => absurd h (hk k), fun h => absurd h List.not_mem_nil⟩, hσ⟩
  have hor : ∀ k, (getOrigAcct s s.currentTarget).stor.get k = σ.get k := fun k => by rw [ho]
  have hG : pullG s b = 434 + if pMax s b then e34MaxG s b (pVal s) (pTo s) (pSrc s) else e34LimG s b (pVal s) (pTo s) (pSrc s) := by
    unfold pullG
    rw [if_neg (show ¬ pSelf s from hself)]
  have hP : pullPost s b 0 = retAt (pullB s b) [selW s] ((pullM s b).write 128 okWord.toBytes) okWord 0 := rfl
  by_cases hmax : σ.get ka = maxUint
  · have hM : pMax s b := hpMax.2 hmax
    have a2 := (hA0.sload kr).sload ka
    have m2 := (mv_afterSload s b kr).trans (mv_afterSload s _ ka)
    obtain ⟨hmA, hmM⟩ := move_view (s := s) (kr := kr) (kt := kt) (v := v) (u := v) hg a2 (m2.clean hc) (hor _) (hor _) hne hle hnof
    have hB : pullB s b = (moved s (afterSload s (afterSload s b kr) ka) kr kt v v).addLog
        { address := s.currentTarget, topics := [Dai.transferTopic, m20 &&& pSrc s, m20 &&& pTo s], data := v.toBytes } := by
      unfold pullB
      rw [if_neg (show ¬ pSelf s from hself), if_pos hM]
      unfold mvBase mvDebited moved
      rw [hkr, hkt, hka, hv]
    have hae : (σ.get ka).toNat = 2 ^ 256 - 1 := (max_iff _).1 hmax
    refine ⟨?_, ?_, ?_⟩
    · rw [hG, if_pos hM, e34MaxG_cold (hk _) (hk _) (hk _) (by rw [hkr, hkt]; exact hne) (by rw [hka, hkr]; exact hra)
        (by rw [hka, hkt]; exact hta)]
      simp only [hc.orig, ho, hA0.val]
      rw [hkr, hkt, hv, debit_class hle, credit_class hnof]
      unfold daiAllowG
      rw [if_pos hae]
      omega
    · rw [hP, hB]
      refine (retAt_mv ((m2.trans hmM).trans (mv_addLog _ _))).one (fun x hx => by
        simpa only [List.append_nil, List.mem_append, List.mem_singleton, or_self] using hx) ?_
      unfold allowEmpties
      rw [if_pos hae]
      simp only [Nat.zero_add, Int.zero_add, Int.add_zero]
    · rw [hP, hB]
      refine (retAt_at (h := hmA)).stor.trans ?_
      unfold daiPulled
      simp only [hmax, ↓reduceIte]
  · have hL : ¬ pMax s b := fun h => hmax (hpMax.1 h)
    obtain ⟨B3, hB3⟩ : ∃ B3, B3 = afterSload s (afterSload s (afterSload s b kr) ka) ka := ⟨_, rfl⟩
    have a3 : At s.currentTarget (ka :: ka :: kr :: []) σ B3 := by rw [hB3]; exact ((hA0.sload kr).sload ka).sload ka
    have m3 : Mv ([s.currentTarget] ++ [s.currentTarget] ++ [s.currentTarget]) (0 + 0 + 0) b B3 := by
      rw [hB3]; exact ((mv_afterSload s b kr).trans (mv_afterSload s _ ka)).trans (mv_afterSload s _ ka)
    have a4 := a3.sload ka
    have m4 := m3.trans (mv_afterSload s B3 ka)
    have c4 := m4.clean hc
    have hal' := hal hmax
    have f4 : Fresh s (afterSload s B3 ka) ka (σ.get ka) := ⟨c4, hor _, a4.val _⟩
    have m5 := mv_debit (v := v) f4 hal' hg
    have a5 := a4.sstore ka (σ.get ka - v)
    obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = σ.set ka (σ.get ka - v) := ⟨_, rfl⟩
    rw [← hσ1] at a5
    have vr : σ1.get kr = σ.get kr := by rw [hσ1]; exact Stor.get_set_ne _ hra _
    have vt : σ1.get kt = σ.get kt := by rw [hσ1]; exact Stor.get_set_ne _ hta _
    obtain ⟨A, hA⟩ : ∃ A, A = afterSstore s (afterSload s B3 ka) ka (σ.get ka - v) := ⟨_, rfl⟩
    rw [← hA] at a5 m5
    have c5 := m5.clean c4
    have hlim : limBase s b (pVal s) (pSrc s) s.caller.toB256 = A := by
      unfold limBase
      rw [hkr, hka, hv, ← hB3, a3.val, hA]
    obtain ⟨hmA, hmM⟩ := move_view (s := s) (kr := kr) (kt := kt) (v := v) (u := v) hg a5 c5 (by rw [hor, vr]) (by rw [hor, vt]) hne
      (by rw [vr]; exact hle) (by rw [vt]; exact hnof)
    have hB : pullB s b = (moved s A kr kt v v).addLog
        { address := s.currentTarget, topics := [Dai.transferTopic, m20 &&& pSrc s, m20 &&& pTo s], data := v.toBytes } := by
      unfold pullB
      rw [if_neg (show ¬ pSelf s from hself), if_neg hL, hlim]
      unfold mvBase mvDebited moved
      rw [hkr, hkt, hv]
    have hae : (σ.get ka).toNat ≠ 2 ^ 256 - 1 := fun e => hmax ((max_iff _).2 e)
    refine ⟨?_, ?_, ?_⟩
    · rw [hG, if_neg hL, e34LimG_cold (hk _) (hk _) (hk _) (by rw [hkr, hkt]; exact hne) (by rw [hka, hkr]; exact hra)
        (by rw [hka, hkt]; exact hta)]
      simp only [hc.orig, ho, hA0.val]
      rw [hkr, hkt, hka, hv, debit_class hal', debit_class hle, credit_class hnof]
      unfold daiAllowG
      rw [if_neg hae]
      omega
    · rw [hP, hB]
      refine (retAt_mv (((m4.trans m5).trans hmM).trans (mv_addLog _ _))).one (fun x hx => by
        simpa only [List.append_nil, List.mem_append, List.mem_singleton, or_self] using hx) ?_
      unfold allowEmpties
      rw [if_neg hae, vr]
      push_cast
      omega
    · rw [hP, hB]
      refine (retAt_at (h := hmA)).stor.trans ?_
      unfold daiPulled
      simp only [hmax, ↓reduceIte, hσ1]

end Dai

/-! ## USDT -/

section Usdt

open Blanc.Lift.Usdt

variable {s : Sevm} {b : Devm}

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

theorem usdt_max_iff (x : B256) : x = Usdt.maxUint ↔ x.toNat = 2 ^ 256 - 1 :=
  ⟨fun h => by rw [h]; decide, fun h => B256.toNat_inj _ _ (h.trans (by decide))⟩

/-- USDT's `balanceOf`: `10`'s word and the holder's. -/
theorem usdt_bal_child {K : List B256} {σ : Stor} (hA : At s.currentTarget K σ b) (h10 : Bytes.toB256 [10] ∉ K) (hk : ky (bHolder s) ∉ K)
    (hne : Bytes.toB256 [10] ≠ ky (bHolder s)) :
    balG s b = 5031 ∧ Mv [s.currentTarget] 0 b (balP s b 0) ∧
      At s.currentTarget (ky (bHolder s) :: Bytes.toB256 [10] :: K) σ (balP s b 0) ∧ (balP s b 0).output = (σ.get (ky (bHolder s))).toBytes := by
  refine ⟨balG_cold (fun m => h10 ((hA.keys _).1 m)) (fun m => hk ((hA.keys _).1 m)) hne, ?_, ?_, ?_⟩
  · exact (((mv_afterSload s b _).trans (mv_afterSload s _ _)).halted _ _ _ _ _ _).one (fun a ha => by
      simpa only [List.append_nil, List.mem_append, List.mem_singleton, or_self] using ha) (by simp only [Int.zero_add])
  · exact ⟨(((hA.sload _).sload _)).keys, ((hA.sload _).sload _).stor⟩
  · show (bAns s b).toBytes = _
    unfold bAns
    rw [(hA.sload _).val]

/-- USDT's `balanceOf` with both its slots warm. -/
theorem usdt_bal_warm {σ : Stor} (hst : b.getStor s.currentTarget = σ)
    (h10 : (⟨s.currentTarget, Bytes.toB256 [10]⟩ : Adr × B256) ∈ b.accessedStorageKeys)
    (hk : (⟨s.currentTarget, ky (bHolder s)⟩ : Adr × B256) ∈ b.accessedStorageKeys) :
    balG s b = 1031 ∧ Mv [s.currentTarget] 0 b (balP s b 0) ∧ (balP s b 0).output = (σ.get (ky (bHolder s))).toBytes ∧
      (balP s b 0).getStor s.currentTarget = σ := by
  refine ⟨balG_warm h10 hk, ?_, ?_, ?_⟩
  · exact (((mv_afterSload s b _).trans (mv_afterSload s _ _)).halted _ _ _ _ _ _).one (fun a ha => by
      simpa only [List.append_nil, List.mem_append, List.mem_singleton, or_self] using ha) (by simp only [Int.zero_add])
  · show (bAns s b).toBytes = _
    unfold bAns
    rw [getStorVal_afterSload, getStorVal_eq, hst]
  · show (afterSload s (afterSload s b _) _).getStor s.currentTarget = _
    rw [afterSload_getStor, afterSload_getStor, hst]

/-- The move's end from a state where the source's slot is cold, the destination's warm and slot `0` warm. -/
theorem mv_tail {K : List B256} {σ : Stor} {a : Devm} {v f t r kr kt : B256} (hkr : ky r = kr) (hkt : ky t = kt)
    (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hA : At s.currentTarget K σ a) (hc : Clean a)
    (hor : (getOrigAcct s s.currentTarget).stor.get kr = σ.get kr) (hot : (getOrigAcct s s.currentTarget).stor.get kt = σ.get kt)
    (hne : kr ≠ kt) (hrK : kr ∉ K) (htK : kt ∈ K) (h0K : Bytes.toB256 [0] ∈ K) (hr0 : kr ≠ Bytes.toB256 [0]) (ht0 : kt ≠ Bytes.toB256 [0])
    (hle : v.toNat ≤ (σ.get kr).toNat) (hnof : (v - f).toNat + (σ.get kt).toNat < 2 ^ 256)
    (hown : f ≠ 0 → ownerKey σ ∉ K ∧ ownerKey σ ≠ kr ∧ ownerKey σ ≠ kt ∧ ownerKey σ ≠ Bytes.toB256 [0] ∧
      (getOrigAcct s s.currentTarget).stor.get (ownerKey σ) = σ.get (ownerKey σ) ∧ f.toNat + (σ.get (ownerKey σ)).toNat < 2 ^ 256) :
    mvG 2593 4838 s a v f t r = (if f = 0 then 2593 else 7238 + creditG (σ.get (ownerKey σ)).toNat f.toNat) + 2200 + debitG v.toNat +
        creditG (σ.get kt).toNat (v - f).toNat ∧
      Mv [s.currentTarget] ((4800 * empties (σ.get kr).toNat v.toNat : Nat) : Int) a (mvPost s a v f t r) ∧
      (∀ k ∈ K, (⟨s.currentTarget, k⟩ : Adr × B256) ∈ (mvPost s a v f t r).accessedStorageKeys) ∧
      (mvPost s a v f t r).getStor s.currentTarget = usdtAfter σ kr kt v f := by
  subst hkr hkt
  obtain ⟨hmA, hmM⟩ := move_view (s := s) (kr := ky r) (kt := ky t) (v := v) (u := v - f) hg hA hc hor hot hne hle hnof
  have hcC := hmM.clean hc
  obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = (σ.set (ky r) (σ.get (ky r) - v)).set (ky t) (σ.get (ky t) + (v - f)) := ⟨_, rfl⟩
  rw [← hσ1] at hmA
  have hmc : mvCredited s a v (v - f) t r = moved s a (ky r) (ky t) v (v - f) := rfl
  have h10 : σ1.get (Bytes.toB256 [0]) = σ.get (Bytes.toB256 [0]) := by
    rw [hσ1, Stor.get_set_ne _ ht0, Stor.get_set_ne _ hr0]
  have hkey : ownerKey σ1 = ownerKey σ := by rw [ownerKey, ownerKey, h10]
  have h0m : Bytes.toB256 [0] ∈ ky t :: ky t :: ky r :: ky r :: K := by
    simp only [List.mem_cons, h0K, or_true]
  have hoV : f ≠ 0 → ownG s (moved s a (ky r) (ky t) v (v - f)) f = 2400 + creditG (σ.get (ownerKey σ)).toNat f.toNat ∧
      Mv [s.currentTarget] 0 (moved s a (ky r) (ky t) v (v - f)) (ownCredited s (moved s a (ky r) (ky t) v (v - f)) f) ∧
      At s.currentTarget (ownerKey σ :: Bytes.toB256 [0] :: ownerKey σ :: Bytes.toB256 [0] :: ky t :: ky t :: ky r :: ky r :: K)
        (σ1.set (ownerKey σ) (σ.get (ownerKey σ) + f)) (ownCredited s (moved s a (ky r) (ky t) v (v - f)) f) := by
    intro hf0
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hown hf0
    have hv1 : σ1.get (ownerKey σ) = σ.get (ownerKey σ) := by
      rw [hσ1, Stor.get_set_ne _ o3.symm, Stor.get_set_ne _ o2.symm]
    have := own_view (s := s) (f := f) hg hmA hcC h0m (by
        rw [hkey]
        simp only [List.mem_cons, not_or]
        exact ⟨o3, o3, o2, o2, o1⟩)
      (by rw [hkey, hv1]; exact o5) (by rw [hkey, hv1]; exact o6) (by rw [hkey]; exact o4)
    rw [hkey, hv1] at this
    exact this
  have hlog : ∀ {T : List Adr} {r : Int} {B : Devm} {l : Log}, Mv T r a B → Mv T r a (B.addLog l) :=
    fun h => ⟨fun x hx => ⟨(h.same x hx).keys, (h.same x hx).stor, (h.same x hx).warm⟩, h.refund,
      fun hc' => ⟨(h.clean hc').created, (h.clean hc').del, (h.clean hc').error⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · have a1 := hA.sload (ky r)
    have m1 := mv_afterSload s a (ky r)
    have c1 := m1.clean hc
    have f1 : Fresh s (afterSload s a (ky r)) (ky r) (σ.get (ky r)) := ⟨c1, hor, a1.val _⟩
    have m2 := mv_debit (v := v) f1 hle hg
    have c2 := m2.clean c1
    have a2 := a1.sstore (ky r) (σ.get (ky r) - v)
    have vt : (σ.set (ky r) (σ.get (ky r) - v)).get (ky t) = σ.get (ky t) := Stor.get_set_ne _ hne _
    have a3 := a2.sload (ky t)
    have c3 := (mv_afterSload s (afterSstore s (afterSload s a (ky r)) (ky r) (σ.get (ky r) - v)) (ky t)).clean c2
    have f3 : Fresh s (afterSload s (afterSstore s (afterSload s a (ky r)) (ky r) (σ.get (ky r) - v)) (ky t)) (ky t) (σ.get (ky t)) :=
      ⟨c3, hot, by rw [a3.val, vt]⟩
    have hcore : mvCoreG s a v (v - f) t r = 2200 + debitG v.toNat + creditG (σ.get (ky t)).toNat (v - f).toNat := by
      unfold mvCoreG mvDebited
      rw [hA.val, a2.val, vt, hA.sloadCost_cold hrK, cost_debit f1 a1 List.mem_cons_self hle,
        a2.sloadCost_warm (by simp only [List.mem_cons, htK, or_true]), cost_credit f3 a3 List.mem_cons_self hnof]
      omega
    unfold mvG
    rw [hcore]
    by_cases hf0 : f = 0
    · simp only [hf0, ↓reduceIte]
      omega
    · have hO := hoV hf0
      rw [hmc]
      simp only [hf0, ↓reduceIte, hO.1]
      omega
  · unfold mvPost
    split
    · refine hlog ?_
      rw [hmc]
      exact hmM
    · rename_i hf0
      refine hlog ?_
      unfold ownLogged
      refine hlog ?_
      rw [hmc]
      refine ((hmM.trans (hoV hf0).2.1).trans (mv_afterSload ..)).one ?_ ?_
      · intro a ha
        simp only [List.mem_append, List.mem_singleton, or_self] at ha
        exact ha
      · rw [Int.add_zero, Int.add_zero]
  · have hmK : ∀ k ∈ K, k ∈ ky t :: ky t :: ky r :: ky r :: K := fun k hk => by simp only [List.mem_cons, hk, or_true]
    have hlogK : ∀ (B : Devm) (l : Log) (x : Adr × B256), x ∈ (B.addLog l).accessedStorageKeys ↔ x ∈ B.accessedStorageKeys :=
      fun _ _ _ => Iff.rfl
    unfold mvPost usdtAfter
    split
    · refine ⟨fun k hk => (hlogK _ _ _).2 ?_, ?_⟩
      · rw [hmc]
        exact (hmA.keys k).2 (hmK k hk)
      rw [Devm.addLog_getStor, hmc, ← hσ1]
      exact hmA.stor
    · rename_i hf0
      refine ⟨fun k hk => ?_, ?_⟩
      · refine (hlogK _ _ _).2 ?_
        unfold ownLogged
        refine (hlogK _ _ _).2 (mem_afterSload_of_mem ?_)
        rw [hmc]
        exact ((hoV hf0).2.2.keys k).2 (by simp only [List.mem_cons, hk, or_true])
      · unfold ownLogged
        rw [Devm.addLog_getStor, Devm.addLog_getStor, afterSload_getStor, hmc, ← hσ1]
        exact (hoV hf0).2.2.stor

/-- USDT's allowance step on its ledger. -/
def usdtSpent (σ : Stor) (ka v : B256) : Stor := if σ.get ka = Usdt.maxUint then σ else σ.set ka (σ.get ka - v)

/-- The allowance step's charge in USDT's `transferFrom`. -/
def usdtAllowG (al v : Nat) : Nat := if al = 2 ^ 256 - 1 then 26 else 320 + debitG v

/-- **USDT's `transferFrom`, after the pool's first `balanceOf`**: `10` and the destination's slot warm. -/
theorem usdt_pull_child {σ : Stor} {kr kt ka v f : B256} (hσ : b.getStor s.currentTarget = σ)
    (hkr : ky (pSrc s) = kr) (hkt : ky (pTo s) = kt) (hka : ak (pSrc s) s.caller.toB256 = ka) (hv : pVal s = v)
    (hf : feeOf σ v = f) (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hc : Clean b)
    (hA : At s.currentTarget [kt, Bytes.toB256 [10]] σ b) (ho : (getOrigAcct s s.currentTarget).stor = σ)
    (hrR : kr ∉ usdtRead (pSrc s)) (htR : kt ∉ usdtRead (pSrc s)) (haR : ka ∉ usdtRead (pSrc s))
    (hne : kr ≠ kt) (hra : ka ≠ kr) (hta : ka ≠ kt)
    (hL : Bytes.toB256 [0] ≠ mapSlot (m20 &&& (m20 &&& pSrc s)) (Bytes.toB256 [6]) ∧
      mapSlot (m20 &&& (m20 &&& pSrc s)) (Bytes.toB256 [6]) ≠ Bytes.toB256 [10] ∧
      mapSlot (m20 &&& (m20 &&& pSrc s)) (Bytes.toB256 [6]) ≠ Bytes.toB256 [3] ∧
      mapSlot (m20 &&& (m20 &&& pSrc s)) (Bytes.toB256 [6]) ≠ Bytes.toB256 [4])
    (hle : v.toNat ≤ (σ.get kr).toNat) (hal : σ.get ka ≠ Usdt.maxUint → v.toNat ≤ (σ.get ka).toNat)
    (hnof : (v - f).toNat + (σ.get kt).toNat < 2 ^ 256)
    (hown : f ≠ 0 → ownerKey σ ∉ usdtRead (pSrc s) ∧ ownerKey σ ≠ kr ∧ ownerKey σ ≠ kt ∧ ownerKey σ ≠ ka ∧
      f.toNat + (σ.get (ownerKey σ)).toNat < 2 ^ 256) :
    pullG s b = 11545 + e61G v + (if Capped σ v then 336 else 228) + usdtAllowG (σ.get ka).toNat v.toNat +
        ((if f = 0 then 2593 else 7238 + creditG (σ.get (ownerKey σ)).toNat f.toNat) + 2200 + debitG v.toNat +
          creditG (σ.get kt).toNat (v - f).toNat) ∧
      Mv [s.currentTarget] ((4800 * (allowEmpties (σ.get ka).toNat v.toNat + empties (σ.get kr).toNat v.toNat) : Nat) : Int) b (pullP s b 0) ∧
      (∀ k ∈ [kt, Bytes.toB256 [10]], (⟨s.currentTarget, k⟩ : Adr × B256) ∈ (pullP s b 0).accessedStorageKeys) ∧
      (pullP s b 0).getStor s.currentTarget = usdtAfter (usdtSpent σ ka v) kr kt v f := by
  obtain ⟨Ls, hLs⟩ : ∃ Ls, Ls = mapSlot (m20 &&& (m20 &&& pSrc s)) (Bytes.toB256 [6]) := ⟨_, rfl⟩
  have hRead : usdtRead (pSrc s) = [Bytes.toB256 [4], Bytes.toB256 [3], Bytes.toB256 [10], Ls, Bytes.toB256 [0]] := by rw [hLs]
  rw [hRead] at hrR htR haR
  rw [← hLs] at hL
  obtain ⟨L0, L10, L3, L4⟩ := hL
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrR htR haR
  obtain ⟨r4, r3, r10, rL, r0⟩ := hrR
  obtain ⟨t4, t3, t10, tL, t0⟩ := htR
  obtain ⟨a4, a3', a10, aL, a0⟩ := haR
  have hor : ∀ k, (getOrigAcct s s.currentTarget).stor.get k = σ.get k := fun k => by rw [ho]
  obtain ⟨G, hG⟩ : ∃ G, G = gateBase s b (pSrc s) := ⟨_, rfl⟩
  have hgA : At s.currentTarget [Bytes.toB256 [10], Ls, Bytes.toB256 [0], kt, Bytes.toB256 [10]] σ G := by
    rw [hG, hLs]; exact ((hA.sload _).sload _).sload _
  have hgM : Mv [s.currentTarget] 0 b G := by
    rw [hG]
    exact (((mv_afterSload ..).trans (mv_afterSload ..)).trans (mv_afterSload ..)).one
      (fun a ha => by simpa only [List.mem_append, List.mem_singleton, or_self] using ha) rfl
  have hgate : gateG s b (pSrc s) = 4300 := by
    unfold gateG
    rw [← hLs, hA.sloadCost_cold (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨fun e => t0 e.symm, by decide⟩),
      (hA.sload _).sloadCost_cold (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨fun e => L0 e.symm, fun e => tL e.symm, L10⟩),
      ((hA.sload _).sload _).sloadCost_warm (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])]
  have a2 := hgA.sload ka
  obtain ⟨hfA, hfM⟩ := feeBase_view (s := s) v a2
  have hcG := hgM.clean hc
  have hcA := (mv_afterSload s G ka).clean hcG
  have hcF := hfM.clean hcA
  have hfC : feeG s (afterSload s G ka) v = 4200 + e61G v + if Capped σ v then 336 else 228 := by
    rw [feeG_cold (fun m => ?_) (fun m => ?_), show Devm.getStor (afterSload s G ka) s.currentTarget = σ from a2.stor]
    · have := (a2.keys _).1 m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with e | e | e | e | e | e
      · exact a3' e.symm
      · exact absurd e (by decide)
      · exact L3 e.symm
      · exact absurd e (by decide)
      · exact t3 e.symm
      · exact absurd e (by decide)
    · have := (a2.keys _).1 m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with e | e | e | e | e | e
      · exact a4 e.symm
      · exact absurd e (by decide)
      · exact L4 e.symm
      · exact absurd e (by decide)
      · exact t4 e.symm
      · exact absurd e (by decide)
  obtain ⟨F, hF⟩ : ∃ F, F = feeBase s (afterSload s G ka) v := ⟨_, rfl⟩
  rw [← hF] at hfA hfM hcF
  have hAcold : sloadCost s G ka = 2100 := hgA.sloadCost_cold (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a10, aL, a0, hta, a10⟩)
  have hGval : G.getStorVal s.currentTarget ka = σ.get ka := hgA.val _
  have hGst : Devm.getStor G s.currentTarget = σ := hgA.stor
  have hCost : pullG s b = 755 + 4300 + (190 + 2100 + (4200 + e61G v + (if Capped σ v then 336 else 228)) +
      e10G s F (σ.get ka) v f (pTo s) (pSrc s)) := by
    unfold pullG e56G
    rw [hgate, ← hG, hka, hAcold, hGval, hGst, hv, hf]
    have : alBase s G (pSrc s) = afterSload s G ka := by rw [alBase, hka]
    rw [this, hfC, ← hF]
  have hPost : pullP s b 0 = St (mvPost s (spentBase s F (σ.get ka) v (pSrc s)) v f (pTo s) (pSrc s)) [selL s] (pullI s b) 0 := by
    have hB : pullB s b = mvPost s (spentBase s F (σ.get ka) v (pSrc s)) v f (pTo s) (pSrc s) := by
      unfold pullB pullPost
      rw [← hG, hka, hGval, hGst, hv, hf]
      have : alBase s G (pSrc s) = afterSload s G ka := by rw [alBase, hka]
      rw [this, ← hF]
    rw [← hB]
    rfl
  have hstM : ∀ {T : List Adr} {r : Int} {B : Devm} {S : List B256} {M : Mem}, Mv T r b B → Mv T r b (St B S M 0) :=
    fun h => ⟨fun x hx => ⟨(h.same x hx).keys, (h.same x hx).stor, (h.same x hx).warm⟩, h.refund,
      fun hc' => ⟨(h.clean hc').created, (h.clean hc').del, (h.clean hc').error⟩⟩
  have hbase : Mv [s.currentTarget] 0 b F := by
    exact ((hgM.trans (mv_afterSload s G ka)).trans hfM).one
      (fun a ha => by simpa only [List.mem_append, List.mem_singleton, or_self] using ha) rfl
  have hsub : ∀ k, k = kt ∨ k = Bytes.toB256 [10] → k ∈ [Bytes.toB256 [4], Bytes.toB256 [3], ka, Bytes.toB256 [10], Ls, Bytes.toB256 [0], kt, Bytes.toB256 [10]] := by
    rintro k (rfl | rfl) <;> simp only [List.mem_cons, true_or, or_true]
  by_cases hmax : σ.get ka = Usdt.maxUint
  · have hae : (σ.get ka).toNat = 2 ^ 256 - 1 := (usdt_max_iff _).1 hmax
    have hS : spentBase s F (σ.get ka) v (pSrc s) = F := ite_eq_left hmax
    have hsp : usdtSpent σ ka v = σ := ite_eq_left hmax
    obtain ⟨c1, c2, c3, c4⟩ := mv_tail (s := s) (a := F) (σ := σ) (v := v) (f := f) hkr hkt hg hfA hcF (hor _) (hor _) hne
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨r4, r3, fun e => hra e.symm, r10, rL, r0, hne, r10⟩)
      (by simp only [List.mem_cons, true_or, or_true]) (by simp only [List.mem_cons, true_or, or_true]) r0 t0 hle hnof
      (fun hf0 => by
        obtain ⟨o1, o2, o3, o4, o5⟩ := hown hf0
        rw [hRead] at o1
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o1 ⊢
        exact ⟨⟨o1.1, o1.2.1, o4, o1.2.2.1, o1.2.2.2.1, o1.2.2.2.2, o3, o1.2.2.1⟩, o2, o3, o1.2.2.2.2, hor _, o5⟩)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hCost]
      have hw : (⟨s.currentTarget, ak (pSrc s) s.caller.toB256⟩ : Adr × B256) ∈ F.accessedStorageKeys := by
        rw [hka]; exact (hfA.keys _).2 (by simp only [List.mem_cons, true_or, or_true])
      rw [e10G_warm hw, ite_eq_left hmax, c1]
      unfold usdtAllowG
      rw [ite_eq_left hae]
      omega
    · rw [hPost, hS]
      refine hstM ((hbase.trans c2).one (fun a ha => by simpa only [List.mem_append, List.mem_singleton, or_self] using ha) ?_)
      unfold allowEmpties
      rw [ite_eq_left hae]
      simp only [Nat.zero_add, Int.zero_add]
    · rw [hPost, hS]
      intro k hk
      exact c3 k (hsub k (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hk) |> fun h => by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using h)
    · rw [hPost, hS, hsp]
      exact c4
  · have hae : (σ.get ka).toNat ≠ 2 ^ 256 - 1 := fun e => hmax ((usdt_max_iff _).2 e)
    have hS : spentBase s F (σ.get ka) v (pSrc s) = afterSstore s F (ak (pSrc s) s.caller.toB256) (σ.get ka - v) := ite_eq_right hmax
    have hal' := hal hmax
    have f5 : Fresh s F ka (σ.get ka) := ⟨hcF, hor _, hfA.val _⟩
    have m5 := mv_debit (v := v) f5 hal' hg
    have a5 := hfA.sstore ka (σ.get ka - v)
    have c5 := m5.clean hcF
    obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = σ.set ka (σ.get ka - v) := ⟨_, rfl⟩
    rw [← hσ1] at a5
    have hsp : usdtSpent σ ka v = σ1 := by rw [hσ1]; exact ite_eq_right hmax
    have vr : σ1.get kr = σ.get kr := by rw [hσ1]; exact Stor.get_set_ne _ hra _
    have vt : σ1.get kt = σ.get kt := by rw [hσ1]; exact Stor.get_set_ne _ hta _
    have v0 : σ1.get (Bytes.toB256 [0]) = σ.get (Bytes.toB256 [0]) := by rw [hσ1]; exact Stor.get_set_ne _ a0 _
    have hkey : ownerKey σ1 = ownerKey σ := by rw [ownerKey, ownerKey, v0]
    obtain ⟨A, hAd⟩ : ∃ A, A = afterSstore s F ka (σ.get ka - v) := ⟨_, rfl⟩
    rw [← hAd] at a5 m5 c5
    have vo : f ≠ 0 → σ1.get (ownerKey σ) = σ.get (ownerKey σ) := fun hf0 => by
      rw [hσ1]; exact Stor.get_set_ne _ (hown hf0).2.2.2.1.symm _
    obtain ⟨c1, c2, c3, c4⟩ := mv_tail (s := s) (a := A) (σ := σ1) (v := v) (f := f) hkr hkt hg a5 c5 (by rw [hor, vr]) (by rw [hor, vt]) hne
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun e => hra e.symm, r4, r3, fun e => hra e.symm, r10, rL, r0, hne, r10⟩)
      (by simp only [List.mem_cons, true_or, or_true]) (by simp only [List.mem_cons, true_or, or_true]) r0 t0
      (by rw [vr]; exact hle) (by rw [vt]; exact hnof)
      (fun hf0 => by
        obtain ⟨o1, o2, o3, o4, o5⟩ := hown hf0
        rw [hRead] at o1
        rw [hkey]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o1 ⊢
        exact ⟨⟨o4, o1.1, o1.2.1, o4, o1.2.2.1, o1.2.2.2.1, o1.2.2.2.2, o3, o1.2.2.1⟩, o2, o3, o1.2.2.2.2, by rw [hor, vo hf0], by rw [vo hf0]; exact o5⟩)
    have hkey' : (if f = 0 then 2593 else 7238 + creditG (σ1.get (ownerKey σ1)).toNat f.toNat) =
        if f = 0 then 2593 else 7238 + creditG (σ.get (ownerKey σ)).toNat f.toNat := by
      by_cases hf0 : f = 0
      · rw [ite_eq_left hf0, ite_eq_left hf0]
      · rw [ite_eq_right hf0, ite_eq_right hf0, hkey, vo hf0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hCost]
      have hw : (⟨s.currentTarget, ak (pSrc s) s.caller.toB256⟩ : Adr × B256) ∈ F.accessedStorageKeys := by
        rw [hka]; exact (hfA.keys _).2 (by simp only [List.mem_cons, true_or, or_true])
      rw [e10G_warm hw, ite_eq_right hmax, hka]
      simp only [hcF.orig, ho]
      rw [hfA.val, debit_class hal', ← hAd, c1, hkey', vt]
      unfold usdtAllowG
      rw [ite_eq_right hae]
      omega
    · rw [hPost, hS, hka, ← hAd]
      refine hstM ((((hbase.trans m5).trans c2)).one (fun a ha => by simpa only [List.mem_append, List.mem_singleton, or_self] using ha) ?_)
      unfold allowEmpties
      rw [ite_eq_right hae, vr]
      push_cast
      omega
    · rw [hPost, hS, hka, ← hAd]
      intro k hk
      exact c3 k (by
        have := hsub k (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hk)
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using Or.inr this)
    · rw [hPost, hS, hka, ← hAd, hsp]
      exact c4

end Usdt

/-! ## USDC -/

section Usdc

open Blanc.Lift.Usdc Blanc.Composition.UsdcLive

/-- `l255`. -/
local notation "l255" => Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

variable {s : Sevm} {b : Devm} {K : List B256} {σ : Stor}

/-- **V2_2's `transferFrom` frame**, the caller being the destination, its slots cold. -/
theorem impl_pull_child {kz kp ka v : B256} (hkz : ky (pFrom s) = kz) (hkp : ky (pTo s) = kp) (hkc : ky s.caller.toB256 = kp)
    (hka : kA' s (pFrom s) = ka) (hv : pVal s = v) (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hc : Clean b)
    (hA : At s.currentTarget K σ b) (ho : (getOrigAcct s s.currentTarget).stor = σ)
    (h1 : Bytes.toB256 [1] ∉ K) (hzK : kz ∉ K) (hpK : kp ∉ K) (haK : ka ∉ K)
    (h1z : Bytes.toB256 [1] ≠ kz) (h1p : Bytes.toB256 [1] ≠ kp) (h1a : Bytes.toB256 [1] ≠ ka)
    (hne : kz ≠ kp) (haz : ka ≠ kz) (hap : ka ≠ kp)
    (fz : frozenBit (σ.get kz) = false) (fp : frozenBit (σ.get kp) = false)
    (hle : v.toNat ≤ (σ.get kz).toNat) (hnof : v.toNat + (σ.get kp).toNat < 2 ^ 256) (hal : v.toNat ≤ (σ.get ka).toNat) :
    implPullG s b = 13454 + debitG v.toNat + debitG v.toNat + creditG (σ.get kp).toNat v.toNat ∧
      Mv [s.currentTarget] ((4800 * (empties (σ.get ka).toNat v.toNat + empties (σ.get kz).toNat v.toNat) : Nat) : Int)
        b (implPullPost s b 0) ∧
      (implPullPost s b 0).getStor s.currentTarget =
        ((σ.set kz (σ.get kz - v)).set kp (σ.get kp + v)).set ka (σ.get ka - v) := by
  have hkz' : ky' (pFrom s) = kz := by rw [← hkz, ky'_bal, ky_bal]
  have hkp' : ky' (pTo s) = kp := by rw [← hkp, ky'_bal, ky_bal]
  have a1 := hA.sload (Bytes.toB256 [1])
  have a2 := a1.sload kp
  have a3 := a2.sload kz
  have a4 := a3.sload kp
  have a5 := a4.sload ka
  have m5 := ((((mv_afterSload s b (Bytes.toB256 [1])).trans (mv_afterSload s _ kp)).trans (mv_afterSload s _ kz)).trans
    (mv_afterSload s _ kp)).trans (mv_afterSload s _ ka)
  have c5 := m5.clean hc
  obtain ⟨P, hP⟩ : ∃ P, P = afterSload s (afterSload s (afterSload s (afterSload s (afterSload s b (Bytes.toB256 [1])) kp) kz) kp) ka := ⟨_, rfl⟩
  rw [← hP] at a5 m5 c5
  have hP' : e68Pre s b (pTo s) (pFrom s) = P := by
    simp only [e68Pre, hkc, hkz, hkp, hka, hP]
  have wz : (⟨s.currentTarget, kz⟩ : Adr × B256) ∈ P.accessedStorageKeys :=
    (a5.keys _).2 (by simp only [List.mem_cons, true_or, or_true])
  have wp : (⟨s.currentTarget, kp⟩ : Adr × B256) ∈ P.accessedStorageKeys :=
    (a5.keys _).2 (by simp only [List.mem_cons, true_or, or_true])
  have hor : ∀ k, (getOrigAcct s s.currentTarget).stor.get k = σ.get k := fun k => by rw [ho]
  obtain ⟨X, hX⟩ : ∃ X, X = σ.get kz := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = σ.get kp := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = σ.get ka := ⟨_, rfl⟩
  rw [← hX] at fz hle ⊢
  rw [← hY] at fp hnof ⊢
  rw [← hZ] at hal ⊢
  have hXl := l255_unfrozen fz
  have hYl := l255_unfrozen fp
  obtain ⟨D, hD⟩ : ∃ D, D = afterSstore s P kz (X - v) := ⟨_, rfl⟩
  have a6 : At s.currentTarget (kz :: ka :: kp :: kz :: kp :: Bytes.toB256 [1] :: K) (σ.set kz (X - v)) D := by
    rw [hD]; exact a5.sstore _ _
  have f6 : Fresh s P kz X := ⟨c5, by rw [hor, hX], by rw [a5.val, hX]⟩
  have m6 : Mv [s.currentTarget] ((4800 * empties X.toNat v.toNat : Nat) : Int) P D := by
    rw [hD]; exact mv_debit f6 hle hg
  have c6 := m6.clean c5
  have vy : D.getStorVal s.currentTarget kp = Y := by
    rw [a6.val, Stor.get_set_ne _ hne, hY]
  have wp6 : (⟨s.currentTarget, kp⟩ : Adr × B256) ∈ D.accessedStorageKeys := by
    rw [hD]; exact mem_afterSstore_of_mem wp
  have f7 : Fresh s D kp Y := ⟨c6, by rw [hor, hY], vy⟩
  have m7 := mv_credit (v := v) f7 hnof
  have hDeb : e93Debited s P (pVal s) (pFrom s) = D := by
    unfold e93Debited
    rw [hv, hkz, hkz', afterSload_of_warm wz, afterSload_of_warm wz, afterSload_of_warm wz, a5.val, ← hX, hXl, hD]
  obtain ⟨E, hE⟩ : ∃ E, E = afterSstore s D kp (Y + v) := ⟨_, rfl⟩
  have hPost : ∃ l, e93Post s P (pVal s) (pTo s) (pFrom s) = E.addLog l := by
    unfold e93Post
    rw [hDeb, hv, hkp, hkp', afterSload_of_warm wp6, afterSload_of_warm wp6, vy, hYl, (B256.add_comm : v + Y = Y + v), ← hE]
    exact ⟨_, rfl⟩
  obtain ⟨l, hl⟩ := hPost
  have a7 : At s.currentTarget (kp :: kz :: ka :: kp :: kz :: kp :: Bytes.toB256 [1] :: K) ((σ.set kz (X - v)).set kp (Y + v)) (E.addLog l) := by
    rw [hE]; exact ⟨(a6.sstore kp (Y + v)).keys, by rw [Devm.addLog_getStor]; exact (a6.sstore kp (Y + v)).stor⟩
  have mE : Mv ([s.currentTarget] ++ []) ((0 : Int) + 0) D (E.addLog l) := by
    rw [hE]; exact m7.trans (mv_addLog _ l)
  have cE := mE.clean c6
  have wa : (⟨s.currentTarget, ka⟩ : Adr × B256) ∈ (E.addLog l).accessedStorageKeys :=
    (a7.keys _).2 (by simp only [List.mem_cons, true_or, or_true])
  have vz : (E.addLog l).getStorVal s.currentTarget ka = Z := by
    rw [a7.val, Stor.get_set_ne _ hap.symm, Stor.get_set_ne _ haz.symm, hZ]
  have f8 : Fresh s (E.addLog l) ka Z := ⟨cE, by rw [hor, hZ], vz⟩
  have m8 := mv_debit (v := v) f8 hal hg
  have hBase : UsdcLive.pullBase s b = afterSstore s (E.addLog l) ka (Z - v) := by
    show e68Post s b (pVal s) (pTo s) (pFrom s) = _
    unfold e68Post
    rw [hP', hl, hka, afterSload_of_warm wa, vz, hv]
  have hAll := (((m5.trans m6).trans mE).trans m8)
  refine ⟨?_, ?_, ?_⟩
  · have e : implPullG s b = 364 + (1052 + sloadCost s b (Bytes.toB256 [1]) + sloadCost s (afterSload s b (Bytes.toB256 [1])) kp +
        sloadCost s (afterSload s (afterSload s b (Bytes.toB256 [1])) kp) kz +
        sloadCost s (afterSload s (afterSload s (afterSload s b (Bytes.toB256 [1])) kp) kz) kp +
        sloadCost s (afterSload s (afterSload s (afterSload s (afterSload s b (Bytes.toB256 [1])) kp) kz) kp) ka +
        e93G s P v (pTo s) (pFrom s) + sloadCost s (E.addLog l) ka + sstoreCost s (E.addLog l) ka (Z - v)) := by
      unfold implPullG e68G
      rw [hP', hl, hv, hkc, hkz, hkp, hka, afterSload_of_warm wa, vz]
    rw [e]
    have hv' : e93Debited s P v (pFrom s) = D := by rw [← hv]; exact hDeb
    unfold e93G e99G
    rw [hv', hkz, hkp, hkz', hkp', afterSload_of_warm wz, afterSload_of_warm wz, afterSload_of_warm wp6,
      sloadCost_of_warm wz, sloadCost_of_warm wp6, a5.val, ← hX, hXl, vy, hYl, (B256.add_comm : v + Y = Y + v),
      hA.sloadCost_cold h1, a1.sloadCost_cold (by simp only [List.mem_cons, not_or]; exact ⟨fun e => h1p e.symm, hpK⟩),
      a2.sloadCost_cold (by simp only [List.mem_cons, not_or]; exact ⟨hne, fun e => h1z e.symm, hzK⟩),
      a3.sloadCost_warm (by simp only [List.mem_cons, true_or, or_true]),
      a4.sloadCost_cold (by simp only [List.mem_cons, not_or]; exact ⟨hap, haz, hap, fun e => h1a e.symm, haK⟩),
      afterSload_of_warm wz, afterSload_of_warm wp6,
      cost_debit f6 a5 (by simp only [List.mem_cons, true_or, or_true]) hle,
      cost_credit f7 a6 (by simp only [List.mem_cons, true_or, or_true]) hnof,
      sloadCost_of_warm wa, cost_debit f8 a7 (by simp only [List.mem_cons, true_or, or_true]) hal]
    simp only [gasWarmAccess]
    omega
  · have hF : implPullPost s b 0 = retV (Bytes.toB256 [128]) (UsdcLive.pullBase s b) [selW s] (pullMem s) okW 0 := rfl
    rw [hF, hBase]
    exact (hAll.halted _ _ _ _ _ _).one (fun a ha => by
      simpa only [List.append_nil, List.mem_append, List.mem_singleton, or_self] using ha) (by
      push_cast
      omega)
  · have hF : implPullPost s b 0 = retV (Bytes.toB256 [128]) (UsdcLive.pullBase s b) [selW s] (pullMem s) okW 0 := rfl
    rw [hF, hBase]
    show (afterSstore s (E.addLog l) ka (Z - v)).getStor s.currentTarget = _
    exact (a7.sstore ka (Z - v)).stor

theorem pMem_size100 {s : Sevm} (hlen : s.data.length = 100) : 100 ≤ (pMem s).size := by
  have h0 : (Bytes.toB256 [0]).toNat = 0 := by decide
  have hl : (Nat.toB256 s.data.length).toNat = 100 := by rw [hlen]; decide
  unfold pMem
  have hL : (s.data.sliceD 0 100 0).length = 100 := List.length_sliceD ..
  have hne : s.data.sliceD 0 100 0 ≠ [] := fun e => by
    rw [e] at hL
    exact absurd hL (by decide)
  rw [h0, hl, Mem.size_write_eq, ite_eq_right hne, hL]
  split
  · omega
  · decide

theorem dExt_zero100 (s : Sevm) (p : Devm) (hlen : s.data.length = 100) : dExt s p = 0 := by
  obtain ⟨h32, -⟩ := pMem_size s
  have h100 := pMem_size100 hlen
  have hl : (Nat.toB256 s.data.length).toNat = 100 := by rw [hlen]; decide
  have h0 : (Bytes.toB256 [0]).toNat = 0 := by decide
  simp only [dExt, Devm.extCost, memExtsSize, hl, h0]
  show calculateMemoryGasCost (memExtSize (memExtSize (pMem s).size 0 100) 0 0) - calculateMemoryGasCost (pMem s).size = 0
  rw [memExtSize_of_le h32 (by omega), memExtSize_of_le h32 (by omega), Nat.sub_self]

/-- The proxy's charge up to its `DELEGATECALL` on `transferFrom`'s calldata, both its slots cold. -/
theorem proxyPreG_cold100 {s : Sevm} {p : Devm} {σ : Stor} (hA : At s.currentTarget [] σ p) (hKK : pKA ≠ pKI)
    (hlen : s.data.length = 100) : proxyPreG s p = 4651 := by
  have h96 : (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes).size = 96 := by
    rw [Mem.size_write_word_at]; rfl
  have hl : (Nat.toB256 s.data.length).toNat = 100 := by rw [hlen]; decide
  have h0 : (Bytes.toB256 [0]).toNat = 0 := by decide
  have he : preExt s p = 3 := by
    unfold preExt
    rw [hl, h0, St]
    simp only [Devm.extCost, memExtsSize]
    show calculateMemoryGasCost (memExtSize (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes).size 0 100) -
      calculateMemoryGasCost (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes).size = 3
    rw [h96]
    decide
  unfold proxyPreG
  rw [he, hl, hA.sloadCost_cold List.not_mem_nil, (hA.sload pKA).sloadCost_cold (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun e => hKK e.symm)]
  rfl

/-- **USDC's `transferFrom` through the proxy, from a cold start**, the caller being the destination. -/
theorem usdc_pull_child {s : Sevm} {p : Devm} {σ : Stor} {kz kq ka v : B256} (hσ : p.getStor s.currentTarget = σ)
    (hkz : ky (pFrom s) = kz) (hkq : ky (pTo s) = kq) (hkc : ky s.caller.toB256 = kq)
    (hka : kA' s (pFrom s) = ka) (hv : pVal s = v) (hg : s.benvStat.rules.gas.storageClearRefund = 4800) (hc : Clean p)
    (hk : ∀ k, (⟨s.currentTarget, k⟩ : Adr × B256) ∉ p.accessedStorageKeys)
    (ho : (getOrigAcct s s.currentTarget).stor = σ)
    (hlen : s.data.length = 100) (himpl : (σ.get pKI).toAdr ∉ p.accessedAddresses)
    (hKK : pKA ≠ pKI)
    (hz : kz ≠ pKA ∧ kz ≠ pKI) (hq : kq ≠ pKA ∧ kq ≠ pKI) (ha : ka ≠ pKA ∧ ka ≠ pKI)
    (h1 : Bytes.toB256 [1] ≠ pKA ∧ Bytes.toB256 [1] ≠ pKI)
    (h1z : Bytes.toB256 [1] ≠ kz) (h1q : Bytes.toB256 [1] ≠ kq) (h1a : Bytes.toB256 [1] ≠ ka)
    (hne : kz ≠ kq) (haz : ka ≠ kz) (haq : ka ≠ kq)
    (fz : frozenBit (σ.get kz) = false) (fq : frozenBit (σ.get kq) = false)
    (hle : v.toNat ≤ (σ.get kz).toNat) (hnof : v.toNat + (σ.get kq).toNat < 2 ^ 256) (hal : v.toNat ≤ (σ.get ka).toNat) :
    UsdcLive.pullG s p = 20749 + debitG v.toNat + debitG v.toNat + creditG (σ.get kq).toNat v.toNat ∧
      Mv [s.currentTarget, (σ.get pKI).toAdr]
        ((4800 * (empties (σ.get ka).toNat v.toNat + empties (σ.get kz).toNat v.toNat) : Nat) : Int)
        p (proxyCanon 1 (fun s p => implPullPost s p 0) s p) ∧
      (proxyCanon 1 (fun s p => implPullPost s p 0) s p).getStor s.currentTarget =
        ((σ.set kz (σ.get kz - v)).set kq (σ.get kq + v)).set ka (σ.get ka - v) := by
  have hA0 : At s.currentTarget [] σ p :=
    ⟨fun k => ⟨fun h => absurd h (hk k), fun h => absurd h List.not_mem_nil⟩, hσ⟩
  have a1 := hA0.sload pKA
  have a2 := a1.sload pKI
  have m2 := (mv_afterSload s p pKA).trans (mv_afterSload s _ pKI)
  have c2 := m2.clean hc
  have hpI : pI s p = σ.get pKI := by
    show (afterSload s p pKA).getStorVal s.currentTarget pKI = _
    rw [a1.val]
  have hdI : dI s p = (σ.get pKI).toAdr := by rw [dI, hpI]
  have hdata := dMsg_data s p 0 (by omega)
  have hdw : Sevm.dataWord (initSevm (dMsg s p 0)) = Sevm.dataWord s := by
    funext i; unfold Sevm.dataWord; rw [hdata]
  have hxv : pVal (initSevm (dMsg s p 0)) = pVal s := by unfold pVal; rw [hdw]
  have hxt : pTo (initSevm (dMsg s p 0)) = pTo s := by unfold pTo; rw [hdw]
  have hxf : pFrom (initSevm (dMsg s p 0)) = pFrom s := by unfold pFrom; rw [hdw]
  have hcc : (initSevm (dMsg s p 0)).caller = s.caller := rfl
  have aC : At (initSevm (dMsg s p 0)).currentTarget [pKI, pKA] σ (initDevm (dMsg s p 0)) := ⟨a2.keys, a2.stor⟩
  have hcC : Clean (initDevm (dMsg s p 0)) := by
    refine ⟨c2.created, fun a hm => ?_, rfl⟩
    have hm' : a ∈ (if s.benvStat.rules.settle.selfdestructRefund = 0 then (.emptyWithCapacity : AdrSet)
        else (dParent s p 0).accountsToDelete) := hm
    split at hm'
    · exact Std.HashSet.not_mem_emptyWithCapacity hm'
    · exact c2.del a hm'
  have hm2 : ∀ k, k ≠ pKA → k ≠ pKI → k ∉ [pKI, pKA] := fun k h h' hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact hm.elim h' h
  obtain ⟨iC, iM, iS⟩ := impl_pull_child (s := initSevm (dMsg s p 0)) (b := initDevm (dMsg s p 0)) (K := [pKI, pKA]) (σ := σ)
    (kz := kz) (kp := kq) (ka := ka) (v := v)
    (by rw [hxf]; exact hkz) (by rw [hxt]; exact hkq) (by rw [hcc]; exact hkc)
    (by rw [hxf]; exact hka) (by rw [hxv]; exact hv) hg hcC aC ho (hm2 _ h1.1 h1.2)
    (hm2 _ hz.1 hz.2) (hm2 _ hq.1 hq.2) (hm2 _ ha.1 ha.2) h1z h1q h1a hne haz haq fz fq hle hnof hal
  have hAd : (pBase s p).accessedAddresses = p.accessedAddresses := by
    simp only [pBase, afterSload_accessedAddresses]
  refine ⟨?_, ?_, ?_⟩
  · have hT : tailG s (dParent s p 0) (pRest s p) (dParent s p 0).memory 1 = 44 := by
      obtain ⟨h32, hge⟩ := dParent_size s p 0
      have hl32 : (Nat.toB256 (1 : B256).toBytes.length).toNat = 32 := by rw [B256.length_toBytes]; decide
      have h0 : (Bytes.toB256 [0]).toNat = 0 := by decide
      unfold tailG
      rw [hl32, h0, St, Devm.extCost_zero_of_le h32 (by omega)]
      rfl
    have hAc : dAcc s p = 2600 := by
      unfold dAcc accessCost
      rw [hAd, hdI, ite_eq_right himpl]
      rfl
    show proxyPreG s p + (tailG s (dParent s p 0) (pRest s p) (dParent s p 0).memory 1 + dAcc s p + dExt s p +
      implPullG (initSevm (dMsg s p 0)) (initDevm (dMsg s p 0))) = _
    rw [proxyPreG_cold100 hA0 hKK hlen, hT, hAc, dExt_zero100 s p hlen, iC]
    omega
  · have hS : ∀ a, a ∉ [(σ.get pKI).toAdr, s.currentTarget] → Same a (pBase s p) (dParent s p 0) := fun a ha => by
      refine ⟨fun _ => Iff.rfl, rfl, ?_⟩
      show a ∈ (pBase s p).accessedAddresses.insert (dI s p) ↔ _
      rw [Std.HashSet.mem_insert, hdI]
      refine ⟨fun h => h.elim (fun e => absurd (List.mem_cons.2 (Or.inl (by simpa only [beq_iff_eq] using e : (σ.get pKI).toAdr = a).symm)) ha) id, Or.inr⟩
    have hch : ∀ a, a ∉ [(σ.get pKI).toAdr, s.currentTarget] → Same a (dParent s p 0) (implPullPost (initSevm (dMsg s p 0)) (initDevm (dMsg s p 0)) 0) := fun a ha => by
      have e : Same a (dParent s p 0) (initDevm (dMsg s p 0)) := ⟨fun _ => Iff.rfl, rfl, Iff.rfl⟩
      exact e.trans (iM.same a (fun hm => ha (List.mem_cons_of_mem _ hm)))
    have hRf : (dParent s p 0).refundCounter = (pBase s p).refundCounter := spawn_refund _ _ _ _ _ _ _
    have hc' : Mv [(σ.get pKI).toAdr, s.currentTarget] ((4800 * (empties (σ.get ka).toNat v.toNat + empties (σ.get kz).toNat v.toNat) : Nat) : Int) (pBase s p) _ :=
      mv_callChild (Bytes.toB256 [0]).toNat (Bytes.toB256 [0]).toNat hS hRf
        (fun h => spawn_clean (St_clean h _ _ _) _ _ _ _ _ _) hch (iM.refund.trans (Int.zero_add _)) (fun _ => iM.clean hcC)
    have h2 := (m2.trans hc').mono (T' := [s.currentTarget, (σ.get pKI).toAdr]) (fun a ha => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at ha ⊢
      exact ha.elim Or.inl (fun h => h.elim Or.inr Or.inl))
    rw [Int.zero_add, Int.zero_add] at h2
    exact proxyPost_mv h2
  · unfold proxyCanon
    rw [proxyPost_stor]
    exact iS

end Usdc

end Blanc.Composition.Curve3PoolPublic
