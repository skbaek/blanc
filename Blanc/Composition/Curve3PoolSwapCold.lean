import Blanc.Composition.Curve3PoolSwapBack

/-!
# `exchange`'s pull in the canonical chain

`front_nofee`: DAI's or USDC's pull from the fee test. `front_fee`: USDT's, between the pool's two reads of its balance.
Each ends at the base and memory `swap_back` starts from.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (swapPullD swapPullN swapPushD swapPushN)

section

variable {b : Devm} {S : List B256} {M : Mem}

theorem ext_pullSite (h : M.size = 0x680) : ext b S M 0x600 0x64 0x6c0 0x20 = 9 := by
  rw [ext_size _ _ _ _ h]; decide

theorem ext_bal1 (h : M.size = 0x400) : ext b S M 0x3dc 0x24 0x440 0x20 = 9 := by
  rw [ext_size _ _ _ _ h]; decide

theorem ext_bal2 (h : M.size = 0x740) : ext b S M 0x71c 0x24 0x780 0x20 = 10 := by
  rw [ext_size _ _ _ _ h]; decide

end

variable {s : Sevm} {p : Devm} {w : Jaune.State} {E : Adr}

theorem coinNext_keep (canon : Sevm → Devm → Devm) (s : Sevm) (t ii is oi : B256) (b : Devm) (S : List B256) (M : Mem) {x : Adr × B256}
    (h : x ∈ b.accessedStorageKeys) : x ∈ (coinNext canon s t ii is oi b S M).accessedStorageKeys :=
  Std.HashSet.mem_union_iff.2 (Or.inl h)

theorem coinNext_warm (canon : Sevm → Devm → Devm) (s : Sevm) (t ii is oi : B256) (b : Devm) (S : List B256) (M : Mem) :
    t.toAdr ∈ (coinNext canon s t ii is oi b S M).accessedAddresses :=
  Std.HashSet.mem_union_iff.2 (Or.inl (Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _))))

/-- The identities of the pull's payload change nothing. -/
theorem mv_pullIn (s : Sevm) (n : Devm) (M : Mem) : Mv ([] ++ []) (0 + 0) n (exPullN2 s n M) := by
  unfold exPullN2 exPullN1
  exact (mv_identity ..).trans (mv_identity ..)

/-- **DAI's or USDC's pull from the fee test.** -/
theorem front_nofee (f : CoinStand s p w E) (hap : SwapApart w E) {i : Fin 3} (hi : i ≠ 2) {n : Devm} {M : Mem} {t : B256} {dx : Nat}
    (hdx : exDx s = Nat.toB256 dx) (htx : t.toAdr = coinAt i) (win : ExPullWin s M)
    (mv : Mv [pool] 0 p n) {K : List B256} {σ : Stor} (hA : At s.currentTarget K σ n)
    (hv : dx < 2 ^ 256) (hle : dx ≤ coinHeld w E i) (hal : dx ≤ allowanceOf w E i) (hcr : CreditFits w pool i dx) :
    exPullCost s n M 31 (swapPullD s t i) (swapPullN s t i) = 575 + 31 + (2600 + 9 + pullAG w E i dx) + 414 ∧
      Mv ([pool] ++ coinT i) ((4800 * pullAR w E i dx : Nat) : Int) p (exPullTail s n M (swapPullN s t i)) ∧
      At s.currentTarget K σ (exPullTail s n M (swapPullN s t i)) ∧
      Devm.getStor (exPullTail s n M (swapPullN s t i)) (coinAt i) = pulledStor w E i dx := by
  have hpi : pool ∉ coinT i := by
    match i with
    | 0 => decide
    | 1 => decide
    | 2 => decide
  have hni : ∀ x ∈ coinT i, x ∉ [pool] := fun x hx hm => hpi (by rw [← List.mem_singleton.1 hm]; exact hx)
  have mI := mv_pullIn s n M
  have m1 : Mv [pool] 0 p (exPullN2 s n M) := Mv.cast (mv.trans mI) (fun a ha => by
    simpa only [List.mem_append, List.not_mem_nil, or_false] using ha) (by simp only [Int.add_zero])
  have hread : ((exPullI2 M s).read (0x600 : B256).toNat (0x64 : B256).toNat).1 =
      transferFromSel ++ s.caller.toB256.toBytes ++ s.currentTarget.toB256.toBytes ++ (Nat.toB256 dx).toBytes := by
    have h := win.read
    rw [hdx] at h
    exact h
  obtain ⟨d1, m2, st, len⟩ := f.pullA hap i hi (b := exPullN2 s n M) (S := []) (M := exPullI2 M s) (t := t) (v := dx) htx m1
    (fun x hx => hni x hx) hread hv hle hal hcr
  have hN : swapPullN s t i (exPullN2 s n M) [] (exPullI2 M s) = exPullNext s n M (swapPullN s t i) := rfl
  rw [hN] at m2 st len
  have hTail := mv_rawTail s (exPullNext s n M (swapPullN s t i)) [] (exPullNext s n M (swapPullN s t i)).memory exPullSite
  have hEq : rawTailBaseNext s (exPullNext s n M (swapPullN s t i)) [] (exPullNext s n M (swapPullN s t i)).memory exPullSite =
      exPullTail s n M (swapPullN s t i) := rfl
  rw [hEq] at hTail
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold exPullCost
    rw [d1, ext_pullSite win.size, len]
    rfl
  · exact Mv.cast ((m1.trans m2).trans hTail) (fun a ha => by
      simpa only [List.mem_append, List.not_mem_nil, or_false] using ha) (by simp only [Int.zero_add, Int.add_zero])
  · refine ((hA.ofMv mI (by simp only [List.append_nil, List.not_mem_nil, not_false_eq_true])).ofMv m2 (by rw [f.target]; exact hpi)).ofMv hTail List.not_mem_nil
  · rw [(hTail.same (coinAt i) List.not_mem_nil).stor]
    exact st

/-- **USDT's pull from the fee test**, between the pool's two reads of its balance. -/
theorem front_fee (f : CoinStand s p w E) (hap : SwapApart w E) {n : Devm} {M : Mem} {t B1 : B256} {dx : Nat}
    (hdx : exDx s = Nat.toB256 dx) (htx : t.toAdr = coinAt 2) (mv : Mv [pool] 0 p n) {K : List B256} {σ : Stor} (hA : At s.currentTarget K σ n)
    (w1 : ExBalWin s M 0x3c0)
    (w2 : ExPullWin s (exBal1Mem s n M B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440)))
    (w3 : ExBalWin s (exPullMem s (exBal1Next s n M (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440))
      (exBal1Mem s n M B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440)) (swapPullN s t 2)) 0x700)
    (hv : dx < 2 ^ 256) (hle : dx ≤ coinHeld w E 2) (hal : dx ≤ allowanceOf w E 2) (hcr : CreditFits w pool 2 (netOf w 2 dx)) (hfee : UsdtFeeFits w dx) :
    exFeeMidCost s n M B1 (coinStaticDebit Usdt.balG s t 0x3dc 0x24 0x440) (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440)
        (swapPullD s t 2) (swapPullN s t 2) (coinStaticDebit Usdt.balG s t 0x71c 0x24 0x780) =
      10 + (97 + (2600 + 9 + 5031)) + (575 + 15 + (100 + 9 + usdtPullG w E dx) + 274) + 29 + (151 + (100 + 10 + 1031)) ∧
    ∀ {B2 : B256}, Mv ([pool] ++ coinT 2 ++ coinT 2) ((4800 * (allowEmpties (allowanceOf w E 2) dx + empties (rawHeld w E 2) dx) : Nat) : Int) p
        (exBal2Next s (exPullTail s (exBal1Next s n M (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440))
            (exBal1Mem s n M B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440)) (swapPullN s t 2))
          (exPullMem s (exBal1Next s n M (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440))
            (exBal1Mem s n M B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440)) (swapPullN s t 2))
          (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x71c 0x24 0x780)) ∧
      At s.currentTarget K σ
        (exBal2Next s (exPullTail s (exBal1Next s n M (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440))
            (exBal1Mem s n M B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440)) (swapPullN s t 2))
          (exPullMem s (exBal1Next s n M (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440))
            (exBal1Mem s n M B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440)) (swapPullN s t 2))
          (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x71c 0x24 0x780)) ∧
      Devm.getStor
        (exBal2Next s (exPullTail s (exBal1Next s n M (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440))
            (exBal1Mem s n M B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440)) (swapPullN s t 2))
          (exPullMem s (exBal1Next s n M (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440))
            (exBal1Mem s n M B1 (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440)) (swapPullN s t 2))
          (coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x71c 0x24 0x780)) usdt =
        usdtAfter (usdtSpent (w.getStor usdt) (Usdt.allowSlot E pool) (Nat.toB256 dx))
          (Usdt.balSlot E) (Usdt.balSlot pool) (Nat.toB256 dx) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 dx)) := by
  have htx' : t.toAdr = usdt := htx
  have hpu : pool ∉ coinT 2 := by decide
  obtain ⟨bN1, hbN1⟩ : ∃ bN1, bN1 = coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x3dc 0x24 0x440 := ⟨_, rfl⟩
  obtain ⟨bN2, hbN2⟩ : ∃ bN2, bN2 = coinStaticNext (fun s p => Usdt.balP s p 0) s t 0x71c 0x24 0x780 := ⟨_, rfl⟩
  rw [← hbN1] at w2 w3
  rw [← hbN1, ← hbN2]
  have hAc := f.party (x := usdt) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) mv (by decide)
  have hAc' : At t.toAdr [] (w.getStor usdt) n := by rw [htx']; exact hAc
  have hr1 : ((exBalIn M s 0x3c0).read (0x3dc : B256).toNat (0x24 : B256).toNat).1 = balanceOfData s.currentTarget := by
    rw [show (0x3dc : B256).toNat = 0x3c0 + 0x1c by decide, show (0x24 : B256).toNat = 0x24 by decide]
    exact w1.read
  obtain ⟨d1, m1, a1, wm1⟩ := usdt_bal_site (s := s) (b := n) (S := []) (M := exBalIn M s 0x3c0) (t := t) (ii := 0x3dc) (oi := 0x440)
    f.fork (mv.clean f.clean) hAc' hr1 (by rw [f.target]; decide +kernel)
  rw [← hbN1, htx'] at m1 a1 wm1
  have hb1 : bN1 n [] (exBalIn M s 0x3c0) = exBal1Next s n M bN1 := rfl
  rw [hb1] at m1 a1 wm1
  obtain ⟨b1, hb1d⟩ : ∃ b1, b1 = exBal1Next s n M bN1 := ⟨_, rfl⟩
  obtain ⟨M1, hM1⟩ : ∃ M1, M1 = exBal1Mem s n M B1 bN1 := ⟨_, rfl⟩
  rw [← hb1d] at m1 a1 wm1
  rw [← hb1d, ← hM1]
  rw [← hb1d, ← hM1] at w3
  rw [← hM1] at w2
  have mI := mv_pullIn s b1 M1
  have mN : Mv [pool, usdt, usdt] 0 p (exPullN2 s b1 M1) :=
    Mv.cast ((mv.trans m1).trans mI) (fun a ha => by
      simpa only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, or_assoc] using ha) (by simp only [Int.add_zero])
  have hnI : usdt ∉ ([] : List Adr) ++ [] := by simp only [List.append_nil, List.not_mem_nil, not_false_eq_true]
  have a2 := a1.ofMv mI hnI
  have wm2 : usdt ∈ (exPullN2 s b1 M1).accessedAddresses := ((mI.same usdt hnI).warm).2 wm1
  have hread : ((exPullI2 M1 s).read (0x600 : B256).toNat (0x64 : B256).toNat).1 =
      transferFromSel ++ s.caller.toB256.toBytes ++ s.currentTarget.toB256.toBytes ++ (Nat.toB256 dx).toBytes := by
    have h := w2.read
    rw [hdx] at h
    exact h
  rw [f.target] at a2
  obtain ⟨d2, m2, st2, len2⟩ := f.pullT hap (b := exPullN2 s b1 M1) (S := []) (M := exPullI2 M1 s) (t := t) (v := dx) htx mN a2 wm2 hread hv hle hal hcr hfee
  have hN : swapPullN s t 2 (exPullN2 s b1 M1) [] (exPullI2 M1 s) = exPullNext s b1 M1 (swapPullN s t 2) := rfl
  rw [hN] at m2 st2 len2
  have hTail := mv_rawTail s (exPullNext s b1 M1 (swapPullN s t 2)) [] (exPullNext s b1 M1 (swapPullN s t 2)).memory exPullSite
  have hEq : rawTailBaseNext s (exPullNext s b1 M1 (swapPullN s t 2)) [] (exPullNext s b1 M1 (swapPullN s t 2)).memory exPullSite =
      exPullTail s b1 M1 (swapPullN s t 2) := rfl
  rw [hEq] at hTail
  obtain ⟨T, hT⟩ : ∃ T, T = exPullTail s b1 M1 (swapPullN s t 2) := ⟨_, rfl⟩
  obtain ⟨M2, hM2⟩ : ∃ M2, M2 = exPullMem s b1 M1 (swapPullN s t 2) := ⟨_, rfl⟩
  rw [← hT] at hTail
  rw [← hM2] at w3
  rw [← hT, ← hM2]
  have hNx : exPullNext s b1 M1 (swapPullN s t 2) = coinNext (fun s p => Usdt.pullP s p 0) s t 0x600 0x64 0x6c0 (exPullN2 s b1 M1) [] (exPullI2 M1 s) := rfl
  have keep : ∀ k, (⟨usdt, k⟩ : Adr × B256) ∈ (exPullN2 s b1 M1).accessedStorageKeys → (⟨usdt, k⟩ : Adr × B256) ∈ T.accessedStorageKeys := fun k hk => by
    refine ((hTail.same usdt List.not_mem_nil).keys k).2 ?_
    rw [hNx]
    exact coinNext_keep _ _ _ _ _ _ _ _ _ hk
  have wmT : usdt ∈ T.accessedAddresses := by
    refine ((hTail.same usdt List.not_mem_nil).warm).2 ?_
    rw [hNx, ← htx']
    exact coinNext_warm _ _ _ _ _ _ _ _ _
  have hr2 : ((exBalIn M2 s 0x700).read (0x71c : B256).toNat (0x24 : B256).toNat).1 = balanceOfData s.currentTarget := by
    rw [show (0x71c : B256).toNat = 0x700 + 0x1c by decide, show (0x24 : B256).toNat = 0x24 by decide]
    exact w3.read
  have hstT : T.getStor t.toAdr = usdtAfter (usdtSpent (w.getStor usdt) (Usdt.allowSlot E pool) (Nat.toB256 dx))
      (Usdt.balSlot E) (Usdt.balSlot pool) (Nat.toB256 dx) (Usdt.feeOf (w.getStor usdt) (Nat.toB256 dx)) := by
    rw [htx', (hTail.same usdt List.not_mem_nil).stor]
    exact st2
  obtain ⟨d3, m3, st3⟩ := usdt_bal_warm_site (s := s) (b := T) (S := []) (M := exBalIn M2 s 0x700) (t := t) (ii := 0x71c) (oi := 0x780) hstT hr2
    (by rw [htx']; exact keep _ ((a2.keys _).2 (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])))
    (by rw [htx', f.target]; exact keep _ ((a2.keys _).2 (by simp only [List.mem_cons, true_or])))
  rw [← hbN2, htx'] at m3 st3
  have hb2 : bN2 T [] (exBalIn M2 s 0x700) = exBal2Next s T M2 bN2 := rfl
  rw [hb2] at m3 st3
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold exFeeMidCost
    rw [← hb1d, ← hM1]
    have e1 : coinStaticDebit Usdt.balG s t 0x3dc 0x24 0x440 n [] (exBalIn M s 0x3c0) = 2600 + 9 + 5031 := by
      rw [d1, acc_cold (by rw [htx']; exact f.coldAddr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) mv (by decide)), ext_bal1 w1.size]
    have e3 : coinStaticDebit Usdt.balG s t 0x71c 0x24 0x780 T [] (exBalIn M2 s 0x700) = 100 + 10 + 1031 := by
      rw [d3, acc_warm (by rw [htx']; exact wmT), ext_bal2 w3.size]
    have e2 : exPullCost s b1 M1 15 (swapPullD s t 2) (swapPullN s t 2) = 575 + 15 + (100 + 9 + usdtPullG w E dx) + 274 := by
      unfold exPullCost
      rw [d2, ext_pullSite w2.size, len2]
      rfl
    rw [e1, e2, ← hT, ← hM2, e3]
  · exact Mv.cast (((mN.trans m2).trans hTail).trans m3) (fun a ha => by
      simpa only [coinT, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, false_or, or_assoc, or_self] using ha)
      (by simp only [Int.zero_add, Int.add_zero])
  · have hA2 : At s.currentTarget K σ (exPullN2 s b1 M1) :=
      ((hA.ofMv m1 (by rw [f.target]; exact hpu)).ofMv mI (by simp only [List.append_nil, List.not_mem_nil, not_false_eq_true]))
    exact ((hA2.ofMv m2 (by rw [f.target]; exact hpu)).ofMv hTail List.not_mem_nil).ofMv m3 (by rw [f.target]; exact hpu)
  · exact st3

end Blanc.Composition.Curve3PoolPublic
