import Blanc.Composition.Curve3PoolExitSites
import Blanc.Composition.Curve3PoolSwapCoins

/-!
# `exchange`'s pulls and balance reads at the frame's call sites

Each coin's `coinDebit` and `coinNext` for `transferFrom` at a site whose memory holds its calldata (`dai_pull_site`,
`usdt_pull_site`, `usdc_pull_site`), and USDT's `balanceOf` around its pull (`usdt_bal_site`, `usdt_bal_warm_site`).
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvInstance (transferFromSel_abi)

variable {s : Sevm} {b : Devm} {S : List B256} {M : Mem} {t ii oi : B256} {V : B256}

/-- The child's calldata words, from the site's memory. -/
theorem pull_words (hread : (M.read ii.toNat (0x64 : B256).toNat).1 =
      transferFromSel ++ s.caller.toB256.toBytes ++ s.currentTarget.toB256.toBytes ++ V.toBytes) :
    Sevm.dataWord (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) 4 = s.caller.toB256 ∧
    Sevm.dataWord (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) 36 = s.currentTarget.toB256 ∧
    Sevm.dataWord (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)) 68 = V ∧
    (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)).data.length = 100 := by
  have hd : (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20)).data =
      abiSelectorBytes 0x23b872dd ++ s.caller.toB256.toBytes ++ s.currentTarget.toB256.toBytes ++ V.toBytes := by
    rw [callMsg0_data, hread, transferFromSel_abi]
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd
  refine ⟨w4, w36, w68, ?_⟩
  rw [hd]
  simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]

section Dai

open Blanc.Lift.Dai

/-- **DAI's `transferFrom` at a site.** -/
theorem dai_pull_site (h : CoinSite s b t.toAdr)
    (hread : (M.read ii.toNat (0x64 : B256).toNat).1 =
      transferFromSel ++ s.caller.toB256.toBytes ++ s.currentTarget.toB256.toBytes ++ V.toBytes)
    (hself : s.caller ≠ s.currentTarget) (hne : balSlot s.caller ≠ balSlot s.currentTarget)
    (hra : allowSlot s.caller s.currentTarget ≠ balSlot s.caller)
    (hta : allowSlot s.caller s.currentTarget ≠ balSlot s.currentTarget)
    (hle : V.toNat ≤ ((b.getStor t.toAdr).get (balSlot s.caller)).toNat)
    (hal : (b.getStor t.toAdr).get (allowSlot s.caller s.currentTarget) ≠ maxUint →
      V.toNat ≤ ((b.getStor t.toAdr).get (allowSlot s.caller s.currentTarget)).toNat)
    (hnof : V.toNat + ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat < 2 ^ 256) :
    coinDebit pullG s t ii 0x64 oi b S M = acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 0x64 oi 0x20 +
        (434 + daiAllowG ((b.getStor t.toAdr).get (allowSlot s.caller s.currentTarget)).toNat V.toNat + debitG V.toNat +
          creditG ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat V.toNat) ∧
      Mv (t.toAdr :: [t.toAdr]) ((4800 * (allowEmpties ((b.getStor t.toAdr).get (allowSlot s.caller s.currentTarget)).toNat V.toNat +
          empties ((b.getStor t.toAdr).get (balSlot s.caller)).toNat V.toNat) : Nat) : Int) b
        (coinNext (fun s p => pullPost s p 0) s t ii 0x64 oi b S M) ∧
      Devm.getStor (coinNext (fun s p => pullPost s p 0) s t ii 0x64 oi b S M) t.toAdr =
        daiPulled (b.getStor t.toAdr) (balSlot s.caller) (balSlot s.currentTarget) (allowSlot s.caller s.currentTarget) V := by
  obtain ⟨hg, hcl, hcold, hor⟩ := h.child (S := S) (M := M) (ii := ii) (oi := oi) (is := 0x64)
  obtain ⟨w4, w36, w68, -⟩ := pull_words (t := t) (oi := oi) (b := b) hread
  obtain ⟨c, hc⟩ : ∃ c, c = callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20 := ⟨_, rfl⟩
  rw [← hc] at hg hcl hcold hor w4 w36 w68
  have hsrc : pSrc (initSevm c) = s.caller.toB256 := by unfold pSrc; rw [lit4, w4, ff20_and_word, toAdr_toB256]
  have hto : pTo (initSevm c) = s.currentTarget.toB256 := by unfold pTo; rw [lit36, w36, ff20_and_word, toAdr_toB256]
  have hval : pVal (initSevm c) = V := by
    unfold pVal; rw [lit36, show Bytes.toB256 [32] + (36 : B256) = 68 by decide, w68]
  have hcaller : (initSevm c).caller = s.currentTarget := by rw [hc]; rfl
  have hstor : (initDevm c).getStor (initSevm c).currentTarget = b.getStor t.toAdr := by rw [hc]; rfl
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  obtain ⟨cc, cm, cs⟩ := dai_pull_child (s := initSevm c) (b := initDevm c) (kr := balSlot s.caller) (kt := balSlot s.currentTarget)
    (ka := allowSlot s.caller s.currentTarget) (v := V) hstor
    (by rw [hsrc, ky_bal, toAdr_toB256]) (by rw [hto, ky_bal, toAdr_toB256])
    (by rw [hsrc, hcaller, ak_allow, toAdr_toB256]) hval hg hcl hcold (by rw [hor, hstor])
    (by rw [hsrc, hcaller, toAdr_toB256]; exact hself) hne hra hta hle hal hnof
  rw [ct] at cm cs
  refine ⟨?_, ?_, ?_⟩
  · unfold coinDebit
    rw [← hc, cc]
  · refine mv_coinNext _ s t ii 0x64 oi b S M ?_ ?_
    · rw [← hc]; exact cm
    · rw [← hc, cm.refund]; exact Int.zero_add _
  · rw [coinNext_getStor, ← hc]
    exact cs

end Dai

section Usdt

open Blanc.Lift.Usdt

theorem usdt_bal_site {σ : Stor} (hfork : ShanghaiOnwards s.benvStat.fork) (hclean : Clean b) (hA : At t.toAdr [] σ b)
    (hread : (M.read ii.toNat (0x24 : B256).toNat).1 = balanceOfData s.currentTarget)
    (hne : Bytes.toB256 [10] ≠ balSlot s.currentTarget) :
    coinStaticDebit balG s t ii 0x24 oi b S M = acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 0x24 oi 0x20 + 5031 ∧
      Mv (t.toAdr :: [t.toAdr]) 0 b (coinStaticNext (fun s p => balP s p 0) s t ii 0x24 oi b S M) ∧
      At t.toAdr [balSlot s.currentTarget, Bytes.toB256 [10]] σ (coinStaticNext (fun s p => balP s p 0) s t ii 0x24 oi b S M) ∧
      t.toAdr ∈ (coinStaticNext (fun s p => balP s p 0) s t ii 0x24 oi b S M).accessedAddresses := by
  obtain ⟨c, hc⟩ : ∃ c, c = staticMsg s (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20 := ⟨_, rfl⟩
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  have hAc : At (initSevm c).currentTarget [] σ (initDevm c) := by
    rw [ct, hc]; exact ⟨hA.keys, hA.stor⟩
  have hclp : Clean (parent (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20) :=
    parent_clean _ S M 0 t ii 0x24 oi 0x20 ⟨hclean.created, hclean.del, hclean.error⟩
  have hcC : Clean (initDevm c) := by
    rw [hc]
    refine ⟨hclp.created, fun a hm => ?_, rfl⟩
    have hm' : a ∈ (if s.benvStat.rules.settle.selfdestructRefund = 0 then (.emptyWithCapacity : AdrSet)
        else (parent (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20).accountsToDelete) := hm
    split at hm'
    · exact Std.HashSet.not_mem_emptyWithCapacity hm'
    · exact hclp.del a hm'
  have hdata : (initSevm c).data = abiSelectorBytes 0x70a08231 ++ s.currentTarget.toB256.toBytes := by
    rw [hc]
    show (M.read ii.toNat (0x24 : B256).toNat).1 = _
    rw [hread]
    rfl
  have hhold : ky (bHolder (initSevm c)) = balSlot s.currentTarget := by
    unfold bHolder
    rw [lit4, Blanc.Lift.Curve3Pool.cc_dataWord_oneWord hdata, ff20_and_word, toAdr_toB256, ky_bal, toAdr_toB256]
  obtain ⟨cc, cm, ca, -⟩ := usdt_bal_child (s := initSevm c) (b := initDevm c) hAc List.not_mem_nil (by rw [hhold]; exact List.not_mem_nil)
    (by rw [hhold]; exact hne)
  rw [hhold, ct] at ca
  rw [ct] at cm
  have hNext : coinStaticNext (fun s p => balP s p 0) s t ii 0x24 oi b S M = callChildPost (parent (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20)
      (balP (initSevm c) (initDevm c) 0) oi.toNat (0x20 : B256).toNat := by
    rw [hc]; rfl
  refine ⟨by unfold coinStaticDebit; rw [← hc, cc], ?_, ?_, ?_⟩
  · rw [hNext]
    refine mv_callChild (T := t.toAdr :: [t.toAdr]) _ _ (fun a ha => parent_same _ _ _ 0 t ii 0x24 oi 0x20 (fun e => ha (e ▸ List.mem_cons_self))) rfl
      (fun h => parent_clean _ _ _ 0 t ii 0x24 oi 0x20 ⟨h.created, h.del, h.error⟩) (fun a ha => ?_) (cm.refund.trans (Int.zero_add _)) (fun _ => cm.clean hcC)
    have e : Same a (parent (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20) (initDevm c) := by
      rw [hc]; exact ⟨fun _ => Iff.rfl, rfl, Iff.rfl⟩
    exact e.trans (cm.same a (fun hm => ha (List.mem_cons_of_mem _ hm)))
  · rw [hNext]
    refine ⟨fun k => ?_, ca.stor⟩
    have hkp : ∀ k, (⟨t.toAdr, k⟩ : Adr × B256) ∉ (parent (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20).accessedStorageKeys :=
      fun k hm => absurd ((hA.keys k).1 hm) List.not_mem_nil
    refine Iff.trans ⟨fun hm => (Std.HashSet.mem_union_iff.1 hm).elim (fun e => absurd e (hkp k)) id,
      fun hm => Std.HashSet.mem_union_iff.2 (Or.inr hm)⟩ (ca.keys k)
  · rw [hNext]
    exact Std.HashSet.mem_union_iff.2 (Or.inl (Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _))))

/-- USDT's second `balanceOf`, its two slots warm. -/
theorem usdt_bal_warm_site {σ : Stor} (hst : b.getStor t.toAdr = σ)
    (hread : (M.read ii.toNat (0x24 : B256).toNat).1 = balanceOfData s.currentTarget)
    (h10 : (⟨t.toAdr, Bytes.toB256 [10]⟩ : Adr × B256) ∈ b.accessedStorageKeys)
    (hk : (⟨t.toAdr, balSlot s.currentTarget⟩ : Adr × B256) ∈ b.accessedStorageKeys) :
    coinStaticDebit balG s t ii 0x24 oi b S M = acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 0x24 oi 0x20 + 1031 ∧
      Mv (t.toAdr :: [t.toAdr]) 0 b (coinStaticNext (fun s p => balP s p 0) s t ii 0x24 oi b S M) ∧
      Devm.getStor (coinStaticNext (fun s p => balP s p 0) s t ii 0x24 oi b S M) t.toAdr = σ := by
  obtain ⟨c, hc⟩ : ∃ c, c = staticMsg s (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20 := ⟨_, rfl⟩
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  have hdata : (initSevm c).data = abiSelectorBytes 0x70a08231 ++ s.currentTarget.toB256.toBytes := by
    rw [hc]
    show (M.read ii.toNat (0x24 : B256).toNat).1 = _
    rw [hread]
    rfl
  have hhold : ky (bHolder (initSevm c)) = balSlot s.currentTarget := by
    unfold bHolder
    rw [lit4, Blanc.Lift.Curve3Pool.cc_dataWord_oneWord hdata, ff20_and_word, toAdr_toB256, ky_bal, toAdr_toB256]
  obtain ⟨cc, cm, -, ckS⟩ := usdt_bal_warm (s := initSevm c) (b := initDevm c) (σ := σ)
    (by rw [ct, hc]; exact hst) (by rw [ct, hc]; exact h10) (by rw [hhold, ct, hc]; exact hk)
  rw [ct] at cm ckS
  have hNext : coinStaticNext (fun s p => balP s p 0) s t ii 0x24 oi b S M = callChildPost (parent (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20)
      (balP (initSevm c) (initDevm c) 0) oi.toNat (0x20 : B256).toNat := by
    rw [hc]; rfl
  have hcp : Clean (parent (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20) → Clean (initDevm c) := fun hclp => by
    rw [hc]
    refine ⟨hclp.created, fun a hm => ?_, rfl⟩
    have hm' : a ∈ (if s.benvStat.rules.settle.selfdestructRefund = 0 then (.emptyWithCapacity : AdrSet)
        else (parent (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20).accountsToDelete) := hm
    split at hm'
    · exact Std.HashSet.not_mem_emptyWithCapacity hm'
    · exact hclp.del a hm'
  refine ⟨by unfold coinStaticDebit; rw [← hc, cc], ?_, by rw [hNext]; exact ckS⟩
  rw [hNext]
  refine mv_callChild (T := t.toAdr :: [t.toAdr]) _ _ (fun a ha => parent_same _ _ _ 0 t ii 0x24 oi 0x20 (fun e => ha (e ▸ List.mem_cons_self))) rfl
    (fun h => parent_clean _ _ _ 0 t ii 0x24 oi 0x20 ⟨h.created, h.del, h.error⟩) (fun a ha => ?_) (cm.refund.trans (Int.zero_add _)) (fun hp => cm.clean (hcp hp))
  have e : Same a (parent (b.withGasLeft 0) S M 0 t ii 0x24 oi 0x20) (initDevm c) := by
    rw [hc]; exact ⟨fun _ => Iff.rfl, rfl, Iff.rfl⟩
  exact e.trans (cm.same a (fun hm => ha (List.mem_cons_of_mem _ hm)))

/-- USDT's reply to `transferFrom` is the frame's initial, empty output. -/
theorem pullP_output (s : Sevm) (b : Devm) : (pullP s b 0).output = b.output := by
  show (pullPost s (gateBase s b (pSrc s)) (pVal s) (pTo s) (pSrc s)).output = _
  unfold pullPost mvPost spentBase feeBase
  split <;> split <;> split <;>
    simp only [Devm.addLog_output, ownLogged, ownCredited, ownRead, mvCredited, mvDebited, afterSstore_output, afterSload_output, gateBase, alBase]

/-- **USDT's `transferFrom` at a site**, after the pool's first `balanceOf`. -/
theorem usdt_pull_site {σ : Stor} (hfork : ShanghaiOnwards s.benvStat.fork) (hclean : Clean b)
    (hst : b.getStor t.toAdr = σ) (hor : (getOrigAcct s t.toAdr).stor = σ)
    (hA : At t.toAdr [balSlot s.currentTarget, Bytes.toB256 [10]] σ b)
    (hread : (M.read ii.toNat (0x64 : B256).toNat).1 =
      transferFromSel ++ s.caller.toB256.toBytes ++ s.currentTarget.toB256.toBytes ++ V.toBytes)
    (hrR : balSlot s.caller ∉ usdtRead s.caller.toB256) (htR : balSlot s.currentTarget ∉ usdtRead s.caller.toB256)
    (haR : allowSlot s.caller s.currentTarget ∉ usdtRead s.caller.toB256)
    (hne : balSlot s.caller ≠ balSlot s.currentTarget) (hra : allowSlot s.caller s.currentTarget ≠ balSlot s.caller)
    (hta : allowSlot s.caller s.currentTarget ≠ balSlot s.currentTarget)
    (hL : Bytes.toB256 [0] ≠ listKey s.caller ∧ listKey s.caller ≠ Bytes.toB256 [10] ∧ listKey s.caller ≠ Bytes.toB256 [3] ∧
      listKey s.caller ≠ Bytes.toB256 [4])
    (hle : V.toNat ≤ (σ.get (balSlot s.caller)).toNat)
    (hal : σ.get (allowSlot s.caller s.currentTarget) ≠ maxUint → V.toNat ≤ (σ.get (allowSlot s.caller s.currentTarget)).toNat)
    (hnof : (V - feeOf σ V).toNat + (σ.get (balSlot s.currentTarget)).toNat < 2 ^ 256)
    (hown : feeOf σ V ≠ 0 → ownerKey σ ∉ usdtRead s.caller.toB256 ∧ ownerKey σ ≠ balSlot s.caller ∧ ownerKey σ ≠ balSlot s.currentTarget ∧
      ownerKey σ ≠ allowSlot s.caller s.currentTarget ∧ (feeOf σ V).toNat + (σ.get (ownerKey σ)).toNat < 2 ^ 256) :
    coinDebit pullG s t ii 0x64 oi b S M = acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 0x64 oi 0x20 +
        (11545 + e61G V + (if Capped σ V then 336 else 228) + usdtAllowG (σ.get (allowSlot s.caller s.currentTarget)).toNat V.toNat +
          ((if feeOf σ V = 0 then 2593 else 7238 + creditG (σ.get (ownerKey σ)).toNat (feeOf σ V).toNat) + 2200 + debitG V.toNat +
            creditG (σ.get (balSlot s.currentTarget)).toNat (V - feeOf σ V).toNat)) ∧
      Mv (t.toAdr :: [t.toAdr]) ((4800 * (allowEmpties (σ.get (allowSlot s.caller s.currentTarget)).toNat V.toNat +
          empties (σ.get (balSlot s.caller)).toNat V.toNat) : Nat) : Int) b
        (coinNext (fun s p => pullP s p 0) s t ii 0x64 oi b S M) ∧
      Devm.getStor (coinNext (fun s p => pullP s p 0) s t ii 0x64 oi b S M) t.toAdr =
        usdtAfter (usdtSpent σ (allowSlot s.caller s.currentTarget) V) (balSlot s.caller) (balSlot s.currentTarget) V (feeOf σ V) := by
  obtain ⟨w4, w36, w68, -⟩ := pull_words (t := t) (oi := oi) (b := b) (S := S) hread
  obtain ⟨c, hc⟩ : ∃ c, c = callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20 := ⟨_, rfl⟩
  rw [← hc] at w4 w36 w68
  have hsrc : pSrc (initSevm c) = s.caller.toB256 := by unfold pSrc; rw [lit4, w4, ff20_and_word, toAdr_toB256]
  have hto : pTo (initSevm c) = s.currentTarget.toB256 := by unfold pTo; rw [lit36, w36, ff20_and_word, toAdr_toB256]
  have hval : pVal (initSevm c) = V := by
    unfold pVal; rw [lit36, show Bytes.toB256 [32] + (36 : B256) = 68 by decide, w68]
  have hcaller : (initSevm c).caller = s.currentTarget := by rw [hc]; rfl
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  have hstor : (initDevm c).getStor (initSevm c).currentTarget = σ := by rw [hc]; exact hst
  have hcl : Clean (initDevm c) := by
    rw [hc]; exact site_clean_of s _ S M 0 t ii 0x64 oi 0x20 (parent_clean _ S M 0 t ii 0x64 oi 0x20 ⟨hclean.created, hclean.del, hclean.error⟩)
  obtain ⟨cc, cm, -, cs⟩ := usdt_pull_child (s := initSevm c) (b := initDevm c) (σ := σ) (kr := balSlot s.caller) (kt := balSlot s.currentTarget)
    (ka := allowSlot s.caller s.currentTarget) (v := V) (f := feeOf σ V) hstor
    (by rw [hsrc, ky_bal, toAdr_toB256]) (by rw [hto, ky_bal, toAdr_toB256])
    (by rw [hsrc, hcaller, ak_allow, toAdr_toB256]) hval rfl (ShanghaiOnwards.rules_storageClearRefund (by rw [hc]; exact hfork)) hcl
    (by rw [ct, hc]; exact ⟨hA.keys, hA.stor⟩) (by rw [ct, hc]; exact hor)
    (by rw [hsrc]; exact hrR) (by rw [hsrc]; exact htR) (by rw [hsrc]; exact haR) hne hra hta
    (by rw [hsrc]; exact hL) hle hal hnof (by rw [hsrc]; exact hown)
  rw [ct] at cm cs
  refine ⟨?_, ?_, ?_⟩
  · unfold coinDebit
    rw [← hc, cc]
  · refine mv_coinNext _ s t ii 0x64 oi b S M ?_ ?_
    · rw [← hc]; exact cm
    · rw [← hc, cm.refund]; exact Int.zero_add _
  · rw [coinNext_getStor, ← hc]
    exact cs

end Usdt

section Usdc

open Blanc.Lift.Usdc Blanc.Composition.UsdcLive

/-- **USDC's `transferFrom` through its proxy at a site.** -/
theorem usdc_pull_site (h : CoinSite s b t.toAdr)
    (hread : (M.read ii.toNat (0x64 : B256).toNat).1 =
      transferFromSel ++ s.caller.toB256.toBytes ++ s.currentTarget.toB256.toBytes ++ V.toBytes)
    (himpl : ((b.getStor t.toAdr).get pKI).toAdr ∉ b.accessedAddresses) (himplT : ((b.getStor t.toAdr).get pKI).toAdr ≠ t.toAdr)
    (hKK : pKA ≠ pKI) (h1 : Bytes.toB256 [1] ≠ pKA ∧ Bytes.toB256 [1] ≠ pKI)
    (hz : balSlot s.caller ≠ pKA ∧ balSlot s.caller ≠ pKI) (hq : balSlot s.currentTarget ≠ pKA ∧ balSlot s.currentTarget ≠ pKI)
    (ha : allowSlot s.caller s.currentTarget ≠ pKA ∧ allowSlot s.caller s.currentTarget ≠ pKI)
    (h1z : Bytes.toB256 [1] ≠ balSlot s.caller) (h1q : Bytes.toB256 [1] ≠ balSlot s.currentTarget)
    (h1a : Bytes.toB256 [1] ≠ allowSlot s.caller s.currentTarget)
    (hne : balSlot s.caller ≠ balSlot s.currentTarget) (haz : allowSlot s.caller s.currentTarget ≠ balSlot s.caller)
    (haq : allowSlot s.caller s.currentTarget ≠ balSlot s.currentTarget)
    (fz : frozenBit ((b.getStor t.toAdr).get (balSlot s.caller)) = false)
    (fq : frozenBit ((b.getStor t.toAdr).get (balSlot s.currentTarget)) = false)
    (hle : V.toNat ≤ ((b.getStor t.toAdr).get (balSlot s.caller)).toNat)
    (hnof : V.toNat + ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat < 2 ^ 256)
    (hal : V.toNat ≤ ((b.getStor t.toAdr).get (allowSlot s.caller s.currentTarget)).toNat) :
    coinDebit UsdcLive.pullG s t ii 0x64 oi b S M = acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 0x64 oi 0x20 +
        (20749 + debitG V.toNat + debitG V.toNat + creditG ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat V.toNat) ∧
      Mv (t.toAdr :: [t.toAdr, ((b.getStor t.toAdr).get pKI).toAdr])
        ((4800 * (empties ((b.getStor t.toAdr).get (allowSlot s.caller s.currentTarget)).toNat V.toNat +
          empties ((b.getStor t.toAdr).get (balSlot s.caller)).toNat V.toNat) : Nat) : Int) b
        (coinNext (proxyCanon 1 (fun s p => implPullPost s p 0)) s t ii 0x64 oi b S M) ∧
      Devm.getStor (coinNext (proxyCanon 1 (fun s p => implPullPost s p 0)) s t ii 0x64 oi b S M) t.toAdr =
        (((b.getStor t.toAdr).set (balSlot s.caller) ((b.getStor t.toAdr).get (balSlot s.caller) - V)).set
          (balSlot s.currentTarget) ((b.getStor t.toAdr).get (balSlot s.currentTarget) + V)).set
          (allowSlot s.caller s.currentTarget) ((b.getStor t.toAdr).get (allowSlot s.caller s.currentTarget) - V) := by
  obtain ⟨hg, hcl, hcold, hor⟩ := h.child (S := S) (M := M) (ii := ii) (oi := oi) (is := 0x64)
  obtain ⟨w4, w36, w68, hl⟩ := pull_words (t := t) (oi := oi) (b := b) (S := S) hread
  obtain ⟨c, hc⟩ : ∃ c, c = callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x64 oi 0x20 := ⟨_, rfl⟩
  rw [← hc] at hg hcl hcold hor w4 w36 w68 hl
  have hsrc : pFrom (initSevm c) = s.caller.toB256 := by
    unfold pFrom; rw [show Bytes.toB256 [4] = (4 : B256) by decide, w4, ff20_and_word, toAdr_toB256]
  have hto : pTo (initSevm c) = s.currentTarget.toB256 := by
    unfold pTo; rw [show Bytes.toB256 [4] + Bytes.toB256 [32] = (36 : B256) by decide, w36, ff20_and_word, toAdr_toB256]
  have hval : pVal (initSevm c) = V := by
    unfold pVal; rw [show Bytes.toB256 [64] + Bytes.toB256 [4] = (68 : B256) by decide, w68]
  have hcaller : (initSevm c).caller = s.currentTarget := by rw [hc]; rfl
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  have hstor : (initDevm c).getStor (initSevm c).currentTarget = b.getStor t.toAdr := by rw [hc]; rfl
  have haddr : ((b.getStor t.toAdr).get pKI).toAdr ∉ (initDevm c).accessedAddresses := fun hm => by
    rw [hc] at hm
    have hm' : ((b.getStor t.toAdr).get pKI).toAdr ∈ b.accessedAddresses.insert t.toAdr := hm
    rcases Std.HashSet.mem_insert.1 hm' with e | e
    · exact himplT (by simpa only [beq_iff_eq] using e : t.toAdr = _).symm
    · exact himpl e
  obtain ⟨cc, cm, cs⟩ := usdc_pull_child (s := initSevm c) (p := initDevm c) (σ := b.getStor t.toAdr)
    (kz := balSlot s.caller) (kq := balSlot s.currentTarget) (ka := allowSlot s.caller s.currentTarget) (v := V) hstor
    (by rw [hsrc, ky_bal, toAdr_toB256]) (by rw [hto, ky_bal, toAdr_toB256]) (by rw [hcaller, ky_bal, toAdr_toB256])
    (by rw [hsrc, kA'_allow, toAdr_toB256, hcaller]) hval hg hcl hcold (by rw [hor, hstor]) hl haddr hKK hz hq ha h1 h1z h1q h1a hne haz haq fz fq hle hnof hal
  rw [ct] at cm cs
  refine ⟨?_, ?_, ?_⟩
  · unfold coinDebit
    rw [← hc, cc]
  · refine mv_coinNext _ s t ii 0x64 oi b S M ?_ ?_
    · rw [← hc]; exact cm
    · rw [← hc, cm.refund]; exact Int.zero_add _
  · rw [coinNext_getStor, ← hc]
    exact cs

end Usdc

end Blanc.Composition.Curve3PoolPublic
