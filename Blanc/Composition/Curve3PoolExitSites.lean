import Blanc.Composition.Curve3PoolExitCoins

/-!
# `remove_liquidity`'s coin calls from a cold start, at the frame's call sites

Each coin's `coinDebit` and `coinNext` at a site whose memory holds the `transfer`'s calldata, in terms of what the
frame stands on: `dai_site`, `usdt_site`, `usdc_site`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.Lift.AccumulatedWalk Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvInstance (transferSel_abi)

theorem coinNext_getStor (canon : Sevm → Devm → Devm) (s : Sevm) (t ii is oi : B256) (b : Devm) (S : List B256) (M : Mem)
    (x : Adr) : Devm.getStor (coinNext canon s t ii is oi b S M) x =
      Devm.getStor (canon (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initDevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20))) x := rfl

/-- What a site's child sees. -/
structure CoinSite (s : Sevm) (b : Devm) (x : Adr) : Prop where
  fork : CoveredFork s.benvStat.fork
  clean : Clean b
  cold : ∀ k, (⟨x, k⟩ : Adr × B256) ∉ b.accessedStorageKeys
  orig : (getOrigAcct s x).stor = b.getStor x

variable {s : Sevm} {b : Devm} {S : List B256} {M : Mem} {t ii oi : B256} {V : B256}

/-- The child's frame at a site, from the site's facts. -/
theorem CoinSite.child {is : B256} (h : CoinSite s b t.toAdr) :
    (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20)).benvStat.rules.gas.storageClearRefund = 4800 ∧
    Clean (initDevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20)) ∧
    (∀ k, (⟨(initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20)).currentTarget, k⟩ : Adr × B256) ∉
      (initDevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20)).accessedStorageKeys) ∧
    (getOrigAcct (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20)).currentTarget).stor =
      Devm.getStor (initDevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii is oi 0x20)).currentTarget :=
  ⟨CoveredFork.rules_storageClearRefund h.fork, site_clean_of s _ S M 0 t ii is oi 0x20 (parent_clean _ S M 0 t ii is oi 0x20
    ⟨h.clean.created, h.clean.del, h.clean.error⟩), h.cold, h.orig⟩

/-- The child's calldata words, from the site's memory. -/
theorem site_words (hread : (M.read ii.toNat (0x44 : B256).toNat).1 = transferSel ++ s.caller.toB256.toBytes ++ V.toBytes) :
    Sevm.dataWord (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) 4 = s.caller.toB256 ∧
    Sevm.dataWord (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) 36 = V ∧
    (initSevm (callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)).data.length = 68 :=
  Blanc.Lift.dataWord_twoWords (by rw [callMsg0_data, hread, transferSel_abi])

section Dai

open Blanc.Lift.Dai

/-- **DAI at a site.** -/
theorem dai_site (h : CoinSite s b t.toAdr)
    (hread : (M.read ii.toNat (0x44 : B256).toNat).1 = transferSel ++ s.caller.toB256.toBytes ++ V.toBytes)
    (hne : balSlot s.currentTarget ≠ balSlot s.caller)
    (hle : V.toNat ≤ ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat)
    (hnof : V.toNat + ((b.getStor t.toAdr).get (balSlot s.caller)).toNat < 2 ^ 256) :
    coinDebit xferG s t ii 0x44 oi b S M = acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 0x44 oi 0x20 +
        (7274 + debitG V.toNat + creditG ((b.getStor t.toAdr).get (balSlot s.caller)).toNat V.toNat) ∧
      Mv (t.toAdr :: [t.toAdr]) ((4800 * empties ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat V.toNat : Nat) : Int) b
        (coinNext (fun s p => xferPost s p 0) s t ii 0x44 oi b S M) ∧
      Devm.getStor (coinNext (fun s p => xferPost s p 0) s t ii 0x44 oi b S M) t.toAdr =
        ((b.getStor t.toAdr).set (balSlot s.currentTarget) ((b.getStor t.toAdr).get (balSlot s.currentTarget) - V)).set
          (balSlot s.caller) ((b.getStor t.toAdr).get (balSlot s.caller) + V) := by
  obtain ⟨hg, hcl, hcold, hor⟩ := h.child (S := S) (M := M) (ii := ii) (oi := oi)
  obtain ⟨w4, w36, -⟩ := site_words (t := t) (oi := oi) (b := b) hread
  obtain ⟨c, hc⟩ : ∃ c, c = callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20 := ⟨_, rfl⟩
  rw [← hc] at hg hcl hcold hor w4 w36
  have hxt : xTo (initSevm c) = s.caller.toB256 := by unfold xTo; rw [lit4, w4, ff20_and_word, toAdr_toB256]
  have hxv : xVal (initSevm c) = V := by unfold xVal; rw [lit36, w36]
  have hcaller : (initSevm c).caller = s.currentTarget := by rw [hc]; rfl
  have hky : ky (initSevm c).caller.toB256 = balSlot s.currentTarget := by rw [hcaller, ky_bal, toAdr_toB256]
  have hkt : ky (xTo (initSevm c)) = balSlot s.caller := by rw [hxt, ky_bal, toAdr_toB256]
  have hstor : (initDevm c).getStor (initSevm c).currentTarget = b.getStor t.toAdr := by rw [hc]; rfl
  obtain ⟨cc, cm, cs⟩ := dai_child hg hcl hcold hor (by rw [hky, hkt]; exact hne)
    (by rw [hky, hxv, hstor]; exact hle) (by rw [hkt, hxv, hstor]; exact hnof)
  simp only [hky, hkt, hxv, hstor] at cc cm cs
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  rw [ct] at cm cs
  refine ⟨?_, ?_, ?_⟩
  · unfold coinDebit
    rw [← hc, cc]
  · refine mv_coinNext _ s t ii 0x44 oi b S M ?_ ?_
    · rw [← hc]; exact cm
    · rw [← hc, cm.refund]; exact Int.zero_add _
  · rw [coinNext_getStor, ← hc]
    exact cs

end Dai

section Usdt

open Blanc.Lift.Usdt

/-- USDT's blacklist word of `a`, as the walk computes it. -/
abbrev listKey (a : Adr) : B256 :=
  mapSlot (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& a.toB256))
    (Bytes.toB256 [6])

/-- **USDT at a site.** -/
theorem usdt_site (h : CoinSite s b t.toAdr)
    (hread : (M.read ii.toNat (0x44 : B256).toNat).1 = transferSel ++ s.caller.toB256.toBytes ++ V.toBytes)
    (hL : Bytes.toB256 [0] ≠ listKey s.currentTarget ∧ listKey s.currentTarget ≠ Bytes.toB256 [10] ∧
      listKey s.currentTarget ≠ Bytes.toB256 [3] ∧ listKey s.currentTarget ≠ Bytes.toB256 [4])
    (hr : balSlot s.currentTarget ∉ usdtRead s.currentTarget.toB256) (ht : balSlot s.caller ∉ usdtRead s.currentTarget.toB256)
    (hne : balSlot s.currentTarget ≠ balSlot s.caller)
    (hle : V.toNat ≤ ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat)
    (hnof : (V - feeOf (b.getStor t.toAdr) V).toNat + ((b.getStor t.toAdr).get (balSlot s.caller)).toNat < 2 ^ 256)
    (hown : feeOf (b.getStor t.toAdr) V ≠ 0 →
      ownerKey (b.getStor t.toAdr) ∉ usdtRead s.currentTarget.toB256 ∧
      ownerKey (b.getStor t.toAdr) ≠ balSlot s.currentTarget ∧ ownerKey (b.getStor t.toAdr) ≠ balSlot s.caller ∧
      (feeOf (b.getStor t.toAdr) V).toNat + ((b.getStor t.toAdr).get (ownerKey (b.getStor t.toAdr))).toNat < 2 ^ 256) :
    coinDebit xferG s t ii 0x44 oi b S M = acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 0x44 oi 0x20 +
        (15749 + e61G V + (if Capped (b.getStor t.toAdr) V then 336 else 228) +
          (if feeOf (b.getStor t.toAdr) V = 0 then 2586
            else 7230 + creditG ((b.getStor t.toAdr).get (ownerKey (b.getStor t.toAdr))).toNat (feeOf (b.getStor t.toAdr) V).toNat) +
          debitG V.toNat + creditG ((b.getStor t.toAdr).get (balSlot s.caller)).toNat (V - feeOf (b.getStor t.toAdr) V).toNat) ∧
      Mv (t.toAdr :: [t.toAdr]) ((4800 * empties ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat V.toNat : Nat) : Int) b
        (coinNext (fun s p => xferPost s p 0) s t ii 0x44 oi b S M) ∧
      Devm.getStor (coinNext (fun s p => xferPost s p 0) s t ii 0x44 oi b S M) t.toAdr =
        usdtAfter (b.getStor t.toAdr) (balSlot s.currentTarget) (balSlot s.caller) V (feeOf (b.getStor t.toAdr) V) := by
  obtain ⟨hg, hcl, hcold, hor⟩ := h.child (S := S) (M := M) (ii := ii) (oi := oi)
  obtain ⟨w4, w36, -⟩ := site_words (t := t) (oi := oi) (b := b) hread
  obtain ⟨c, hc⟩ : ∃ c, c = callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20 := ⟨_, rfl⟩
  rw [← hc] at hg hcl hcold hor w4 w36
  have hxt : xTo (initSevm c) = s.caller.toB256 := by unfold xTo; rw [lit4, w4, ff20_and_word, toAdr_toB256]
  have hxv : xVal (initSevm c) = V := by unfold xVal; rw [lit36, w36]
  have hcaller : (initSevm c).caller = s.currentTarget := by rw [hc]; rfl
  have hky : ky (initSevm c).caller.toB256 = balSlot s.currentTarget := by rw [hcaller, ky_bal, toAdr_toB256]
  have hkt : ky (xTo (initSevm c)) = balSlot s.caller := by rw [hxt, ky_bal, toAdr_toB256]
  have hstor : (initDevm c).getStor (initSevm c).currentTarget = b.getStor t.toAdr := by rw [hc]; rfl
  obtain ⟨cc, cm, cs⟩ := usdt_child hg hcl hcold hor (by rw [hcaller]; exact hL) (by rw [hky, hcaller]; exact hr)
    (by rw [hkt, hcaller]; exact ht) (by rw [hky, hkt]; exact hne)
    (by rw [hky, hxv, hstor]; exact hle) (by rw [hkt, hxv, hstor]; exact hnof)
    (by rw [hxv, hstor, hky, hkt, hcaller]; exact hown)
  simp only [hky, hkt, hxv, hstor] at cc cm cs
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  rw [ct] at cm cs
  refine ⟨?_, ?_, ?_⟩
  · unfold coinDebit
    rw [← hc, cc]
  · refine mv_coinNext _ s t ii 0x44 oi b S M ?_ ?_
    · rw [← hc]; exact cm
    · rw [← hc, cm.refund]; exact Int.zero_add _
  · rw [coinNext_getStor, ← hc]
    exact cs

end Usdt

section Usdc

open Blanc.Lift.Usdc Blanc.Composition.UsdcLive

/-- **USDC through its proxy at a site.** -/
theorem usdc_site (h : CoinSite s b t.toAdr)
    (hread : (M.read ii.toNat (0x44 : B256).toNat).1 = transferSel ++ s.caller.toB256.toBytes ++ V.toBytes)
    (himpl : ((b.getStor t.toAdr).get pKI).toAdr ∉ b.accessedAddresses) (himplT : ((b.getStor t.toAdr).get pKI).toAdr ≠ t.toAdr)
    (hKK : pKA ≠ pKI) (h1 : Bytes.toB256 [1] ≠ pKA ∧ Bytes.toB256 [1] ≠ pKI)
    (hz : balSlot s.currentTarget ≠ pKA ∧ balSlot s.currentTarget ≠ pKI) (hy : balSlot s.caller ≠ pKA ∧ balSlot s.caller ≠ pKI)
    (h1z : Bytes.toB256 [1] ≠ balSlot s.currentTarget) (h1y : Bytes.toB256 [1] ≠ balSlot s.caller)
    (hne : balSlot s.currentTarget ≠ balSlot s.caller)
    (fz : frozenBit ((b.getStor t.toAdr).get (balSlot s.currentTarget)) = false)
    (fy : frozenBit ((b.getStor t.toAdr).get (balSlot s.caller)) = false)
    (hle : V.toNat ≤ ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat)
    (hnof : V.toNat + ((b.getStor t.toAdr).get (balSlot s.caller)).toNat < 2 ^ 256) :
    coinDebit xferG s t ii 0x44 oi b S M = acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii 0x44 oi 0x20 +
        (17752 + debitG V.toNat + creditG ((b.getStor t.toAdr).get (balSlot s.caller)).toNat V.toNat) ∧
      Mv (t.toAdr :: [t.toAdr, ((b.getStor t.toAdr).get pKI).toAdr])
        ((4800 * empties ((b.getStor t.toAdr).get (balSlot s.currentTarget)).toNat V.toNat : Nat) : Int) b
        (coinNext (proxyCanon 1 (fun s p => implXferPost s p 0)) s t ii 0x44 oi b S M) ∧
      Devm.getStor (coinNext (proxyCanon 1 (fun s p => implXferPost s p 0)) s t ii 0x44 oi b S M) t.toAdr =
        ((b.getStor t.toAdr).set (balSlot s.currentTarget) ((b.getStor t.toAdr).get (balSlot s.currentTarget) - V)).set
          (balSlot s.caller) ((b.getStor t.toAdr).get (balSlot s.caller) + V) := by
  obtain ⟨hg, hcl, hcold, hor⟩ := h.child (S := S) (M := M) (ii := ii) (oi := oi)
  obtain ⟨w4, w36, hl⟩ := site_words (t := t) (oi := oi) (b := b) hread
  obtain ⟨c, hc⟩ : ∃ c, c = callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20 := ⟨_, rfl⟩
  rw [← hc] at hg hcl hcold hor w4 w36 hl
  have hxt : xTo (initSevm c) = s.caller.toB256 := by
    unfold xTo; rw [show Bytes.toB256 [4] = (4 : B256) by decide, w4, word_ff20, toAdr_toB256]
  have hxv : xVal (initSevm c) = V := by
    unfold xVal; rw [show Bytes.toB256 [32] + Bytes.toB256 [4] = (36 : B256) by decide, w36]
  have hcaller : (initSevm c).caller = s.currentTarget := by rw [hc]; rfl
  have hky : ky (initSevm c).caller.toB256 = balSlot s.currentTarget := by rw [hcaller, ky_bal, toAdr_toB256]
  have hkt : ky (xTo (initSevm c)) = balSlot s.caller := by rw [hxt, ky_bal, toAdr_toB256]
  have hstor : (initDevm c).getStor (initSevm c).currentTarget = b.getStor t.toAdr := by rw [hc]; rfl
  have haddr : ((b.getStor t.toAdr).get pKI).toAdr ∉ (initDevm c).accessedAddresses := fun hm => by
    rw [hc] at hm
    have hm' : ((b.getStor t.toAdr).get pKI).toAdr ∈ b.accessedAddresses.insert t.toAdr := hm
    rcases Std.HashSet.mem_insert.1 hm' with e | e
    · exact himplT (by simpa only [beq_iff_eq] using e : t.toAdr = _).symm
    · exact himpl e
  obtain ⟨cc, cm, cs⟩ := usdc_child hg hcl hcold hor hl (by rw [hstor]; exact haddr) hKK h1
    (by rw [hky]; exact hz) (by rw [hkt]; exact hy) (by rw [hky]; exact h1z) (by rw [hkt]; exact h1y)
    (by rw [hky, hkt]; exact hne) (by rw [hky, hstor]; exact fz) (by rw [hkt, hstor]; exact fy)
    (by rw [hky, hxv, hstor]; exact hle) (by rw [hkt, hxv, hstor]; exact hnof)
  simp only [hky, hkt, hxv, hstor] at cc cm cs
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  rw [ct] at cm cs
  refine ⟨?_, ?_, ?_⟩
  · unfold coinDebit
    rw [← hc, cc]
  · refine mv_coinNext _ s t ii 0x44 oi b S M ?_ ?_
    · rw [← hc]; exact cm
    · rw [← hc, cm.refund]; exact Int.zero_add _
  · rw [coinNext_getStor, ← hc]
    exact cs

end Usdc

/-! ## 3Crv -/

section C3

open Blanc.Lift.Curve3Crv Blanc.Composition.Curve3PoolCalleeExactProfiles

theorem h_stor_c3 (B : Devm) (S : List B256) (M : Mem) (G a n : Nat) (w : Bytes) (x : Adr) :
    (((St B S M G).memRead a n).2.withOutput w).getStor x = B.getStor x := rfl

/-- A body's named run identifies its canonical post. -/
theorem canon_of_run {e : Sevm} {d post : Devm} {f : SFunc} {c : Nat} (hsg : e.benvStat.rules.stateGas = none)
    (hf : f.gasFree = true) (hrefs : f.refs = [])
    (hrun : SFunc.RunExact Curve3Crv.prog e (Curve3Crv.entrySt e d (gCallStipend + 1 + c)) f (.halted post)) :
    Devm.EqModGas post (bodyCanon e d f c) :=
  bodyCanon_spec (F := e.gas) hsg hf hrefs ⟨post, hrun⟩ hrun

/-- **`totalSupply()` at a site**, its slot cold. -/
theorem supply_site {ii oi : B256} (hfork : CoveredFork s.benvStat.fork) (hclean : Clean b) {σ : Stor}
    (hA : At t.toAdr [] σ b) :
    supplyBodyCost s t ii oi b S M = 2134 ∧
      Mv (t.toAdr :: [t.toAdr]) 0 b (supplyNext s t ii oi b S M) ∧ At t.toAdr [vySupplySlot] σ (supplyNext s t ii oi b S M) ∧
      t.toAdr ∈ (supplyNext s t ii oi b S M).accessedAddresses := by
  obtain ⟨c, hc⟩ : ∃ c, c = staticMsg s (b.withGasLeft 0) S M 0 t ii 4 oi 0x20 := ⟨_, rfl⟩
  have hfc : CoveredFork (initSevm c).benvStat.fork := by rw [hc]; exact hfork
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  have hAc : At (initSevm c).currentTarget [] σ (initDevm c) := by
    rw [ct, hc]; exact ⟨hA.keys, hA.stor⟩
  have hclp : Clean (parent (b.withGasLeft 0) S M 0 t ii 4 oi 0x20) :=
    parent_clean _ S M 0 t ii 4 oi 0x20 ⟨hclean.created, hclean.del, hclean.error⟩
  have hcC : Clean (initDevm c) := by
    rw [hc]
    refine ⟨hclp.created, fun a hm => ?_, rfl⟩
    have hm' : a ∈ (if s.benvStat.rules.settle.selfdestructRefund = 0 then (.emptyWithCapacity : AdrSet)
        else (parent (b.withGasLeft 0) S M 0 t ii 4 oi 0x20).accountsToDelete) := hm
    split at hm'
    · exact Std.HashSet.not_mem_emptyWithCapacity hm'
    · exact hclp.del a hm'
  have hcost : totalSupplyBodyCost (initSevm c) (initDevm c) = 2134 := by
    unfold totalSupplyBodyCost
    rw [hAc.sloadCost_cold List.not_mem_nil]
  have hraw : rawTotalSupply (initSevm c) (Devm.getStor (initDevm c) (initSevm c).currentTarget) =
      some (Devm.getStor (initDevm c) (initSevm c).currentTarget, [],
        some ((Devm.getStor (initDevm c) (initSevm c).currentTarget).get vySupplySlot).toBytes) := by
    unfold rawTotalSupply
    rw [ite_eq_left (by rw [hc]; exact staticMsg_value ..)]
  obtain ⟨post, hrun, -, -, hp⟩ := live_totalSupply_post hfc hraw (gCallStipend + 1) (by omega)
  have hcan := canon_of_run hfc.rules_stateGas_none supply_body_certificate.1 supply_body_certificate.2 hrun
  have hm := (mv_afterSload (initSevm c) (initDevm c) vySupplySlot).halted [] ((vyMem Mem.empty (Sevm.dataWord (initSevm c) 0)).write 0
    ((initDevm c).getStorVal (initSevm c).currentTarget vySupplySlot).toBytes) (gCallStipend + 1) 0 32
    ((initDevm c).getStorVal (initSevm c).currentTarget vySupplySlot).toBytes
  rw [← hp] at hm
  have ha : At (initSevm c).currentTarget [vySupplySlot] σ post := by
    rw [hp]; exact halted_at _ _ _ _ _ _ (hAc.sload _)
  have hm' := hm.congr hcan
  have ha' := ha.congr_gas hcan
  rw [ct] at hm' ha'
  have hNext : supplyNext s t ii oi b S M = callChildPost (parent (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)
      (bodyCanon (initSevm c) (initDevm c) t_0240_c0 (totalSupplyBodyCost (initSevm c) (initDevm c))) oi.toNat (0x20 : B256).toNat := by
    rw [hc]; rfl
  refine ⟨by unfold supplyBodyCost; rw [← hc]; exact hcost, ?_, ?_, ?_⟩
  · rw [hNext]
    refine mv_callChild (T := t.toAdr :: [t.toAdr]) _ _ (fun a ha => parent_same _ _ _ 0 t ii 4 oi 0x20 (fun e => ha (e ▸ List.mem_cons_self))) rfl
      (fun h => parent_clean _ _ _ 0 t ii 4 oi 0x20 ⟨h.created, h.del, h.error⟩) (fun a ha => ?_) (hm'.refund.trans (Int.zero_add _)) (fun _ => hm'.clean hcC)
    have e : Same a (parent (b.withGasLeft 0) S M 0 t ii 4 oi 0x20) (initDevm c) := by
      rw [hc]; exact ⟨fun _ => Iff.rfl, rfl, Iff.rfl⟩
    exact e.trans (hm'.same a (fun hm => ha (List.mem_cons_of_mem _ hm)))
  · rw [hNext]
    refine ⟨fun k => ?_, ha'.stor⟩
    have hkp : ∀ k, (⟨t.toAdr, k⟩ : Adr × B256) ∉ (parent (b.withGasLeft 0) S M 0 t ii 4 oi 0x20).accessedStorageKeys :=
      fun k hm => absurd ((hA.keys k).1 hm) List.not_mem_nil
    refine Iff.trans ⟨fun hm => (Std.HashSet.mem_union_iff.1 hm).elim (fun e => absurd e (hkp k)) id,
      fun hm => Std.HashSet.mem_union_iff.2 (Or.inr hm)⟩ (ha'.keys k)
  · rw [hNext]
    exact Std.HashSet.mem_union_iff.2 (Or.inl (Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _))))

/-- **`burnFrom` at a site**, the supply warm. -/
theorem burn_site {ii oi : B256} (hfork : CoveredFork s.benvStat.fork) (hclean : Clean b) (hstatic : s.isStatic = false)
    (hA : At t.toAdr [vySupplySlot] (b.getStor t.toAdr) b)
    (hor : (getOrigAcct s t.toAdr).stor = b.getStor t.toAdr)
    (hread : (M.read ii.toNat (0x44 : B256).toNat).1 = burnFromSel ++ s.caller.toB256.toBytes ++ V.toBytes)
    (hfits : BurnFits (b.getStor t.toAdr) s.currentTarget s.caller.toB256 V)
    (hmin : mapSlot 3 s.caller.toB256 ≠ vySupplySlot ∧ mapSlot 3 s.caller.toB256 ≠ vyMinterSlot) (hms : vyMinterSlot ≠ vySupplySlot) :
    mutBodyCost burnBodyCost s t ii oi b S M = 6407 + debitG V.toNat + debitG V.toNat ∧
      Mv (t.toAdr :: [t.toAdr])
        ((4800 * (empties ((b.getStor t.toAdr).get vySupplySlot).toNat V.toNat +
          empties ((b.getStor t.toAdr).get (mapSlot 3 s.caller.toB256)).toNat V.toNat) : Nat) : Int) b
        (mutNext burnBodyCost t_0644_c0 s t ii oi b S M) ∧
      Devm.getStor (mutNext burnBodyCost t_0644_c0 s t ii oi b S M) t.toAdr = burnStor (b.getStor t.toAdr) s.caller.toB256 V := by
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = b.getStor t.toAdr := ⟨_, rfl⟩
  simp only [← hσ] at hA hor hfits ⊢
  obtain ⟨c, hc⟩ : ∃ c, c = callMsg0 s (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20 := ⟨_, rfl⟩
  have hfc : CoveredFork (initSevm c).benvStat.fork := by rw [hc]; exact hfork
  have ct : (initSevm c).currentTarget = t.toAdr := by rw [hc]; rfl
  have hAc : At (initSevm c).currentTarget [vySupplySlot] σ (initDevm c) := by
    rw [ct, hc]; exact ⟨hA.keys, hA.stor⟩
  have hclp : Clean (parent (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20) :=
    parent_clean _ S M 0 t ii 0x44 oi 0x20 ⟨hclean.created, hclean.del, hclean.error⟩
  have hcC : Clean (initDevm c) := by
    rw [hc]; exact site_clean_of s _ S M 0 t ii 0x44 oi 0x20 hclp
  have hdata : (initSevm c).data = burnFromSel ++ s.caller.toB256.toBytes ++ V.toBytes := by
    rw [hc]; exact (callMsg0_data ..).trans hread
  have hcaller : (initSevm c).caller = s.currentTarget := by rw [hc]; rfl
  have hstor : Devm.getStor (initDevm c) (initSevm c).currentTarget = σ := hAc.stor
  have hraw := rawBurnFrom_of_fits (e := initSevm c) (stor := σ) (by rw [hc]; exact callMsg0_value ..) hdata
    (adr_toB256_lt _) (by rw [hcaller]; exact hfits)
  obtain ⟨a0, a1, -⟩ := argWords (e := initSevm c) (by rw [hdata, burnFromSel_eq])
  obtain ⟨Mp, hrun⟩ := live_burnFrom_post (sevm := initSevm c) (b := initDevm c) hfc
    (by rw [hc, callMsg0_isStatic]; exact hstatic) (by rw [hstor]; exact hraw) (gCallStipend + 1) (by omega)
  have hcan := canon_of_run hfc.rules_stateGas_none burn_body_certificate.1 burn_body_certificate.2 hrun
  obtain ⟨hmn, hnz, hsup, hbal⟩ := hfits
  obtain ⟨k, hk⟩ : ∃ k, k = mapSlot 3 s.caller.toB256 := ⟨_, rfl⟩
  have hak : mapSlot 3 (Sevm.argWord (initSevm c) 0) = k := by rw [a0, hk]
  simp only [← hk] at hmin hbal ⊢
  obtain ⟨u, hu⟩ : ∃ u, u = σ.get vySupplySlot := ⟨_, rfl⟩
  have hs1 : ((σ.set vySupplySlot (σ.get vySupplySlot - V)).get k) = σ.get k := Stor.get_set_ne _ (Ne.symm hmin.1) _
  rw [hs1] at hbal
  have hor' : ∀ x, (getOrigAcct (initSevm c) (initSevm c).currentTarget).stor.get x = σ.get x := fun x => by
    rw [ct, show getOrigAcct (initSevm c) t.toAdr = getOrigAcct s t.toAdr by rw [hc]; rfl, hor]
  have m1 := mv_afterSload (initSevm c) (initDevm c) vyMinterSlot
  have a1' := hAc.sload vyMinterSlot
  have m2 := mv_afterSload (initSevm c) (afterSload (initSevm c) (initDevm c) vyMinterSlot) vySupplySlot
  have a2 := a1'.sload vySupplySlot
  have c2 := m2.clean (m1.clean hcC)
  have hg : (initSevm c).benvStat.rules.gas.storageClearRefund = 4800 := CoveredFork.rules_storageClearRefund hfc
  have f3 : Fresh (initSevm c) (afterSload (initSevm c) (afterSload (initSevm c) (initDevm c) vyMinterSlot) vySupplySlot) vySupplySlot (σ.get vySupplySlot) :=
    ⟨c2, hor' _, a2.val _⟩
  have hle1 : V.toNat ≤ (σ.get vySupplySlot).toNat := B256.le_iff_toNat_le_toNat.1 hsup
  have hle2 : V.toNat ≤ (σ.get k).toNat := B256.le_iff_toNat_le_toNat.1 hbal
  have m3 := mv_debit (v := V) f3 hle1 hg
  have a3 := a2.sstore vySupplySlot (σ.get vySupplySlot - V)
  have c3 := m3.clean c2
  obtain ⟨b3, hb3⟩ : ∃ b3, b3 = afterSstore (initSevm c) (afterSload (initSevm c) (afterSload (initSevm c) (initDevm c) vyMinterSlot) vySupplySlot) vySupplySlot (σ.get vySupplySlot - V) := ⟨_, rfl⟩
  rw [← hb3] at m3 a3 c3
  have m4 := mv_afterSload (initSevm c) b3 k
  have a4 := a3.sload k
  have c4 := m4.clean c3
  have f5 : Fresh (initSevm c) (afterSload (initSevm c) b3 k) k (σ.get k) :=
    ⟨c4, hor' _, by rw [a4.val, hs1]⟩
  have m5 := mv_debit (v := V) f5 hle2 hg
  have a5 := a4.sstore k (σ.get k - V)
  have hy3 : b3.getStorVal (initSevm c).currentTarget k = σ.get k := by rw [a3.val, hs1]
  have hbp : ∃ l, burnPost (initSevm c) (initDevm c) Mp (gCallStipend + 1) =
      ((St ((afterSstore (initSevm c) (afterSload (initSevm c) b3 k) k (σ.get k - V)).addLog l) [] Mp (gCallStipend + 1)).memRead 0 32).2.withOutput (1 : B256).toBytes := by
    refine ⟨⟨(initSevm c).currentTarget, [Blanc.Lift.Curve3Crv.transferTopic, s.caller.toB256, 0], V.toBytes⟩, ?_⟩
    unfold burnPost
    simp only [a0, a1, ← hk]
    rw [a1'.val, ← hb3, hy3]
  obtain ⟨l, hl⟩ := hbp
  have mAll := (((((m1.trans m2).trans m3).trans m4).trans m5).trans (mv_addLog _ l)).halted [] Mp (gCallStipend + 1) 0 32 (1 : B256).toBytes
  rw [← hl] at mAll
  have mC := mAll.congr hcan
  rw [ct] at mC
  have hNext : mutNext burnBodyCost t_0644_c0 s t ii oi b S M = callChildPost (parent (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)
      (bodyCanon (initSevm c) (initDevm c) t_0644_c0 (burnBodyCost (initSevm c) (initDevm c))) oi.toNat (0x20 : B256).toNat := by
    rw [hc]; rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold mutBodyCost burnBodyCost
    rw [← hc]
    simp only [a0, a1, ← hk]
    rw [a1'.val, ← hb3, hy3, hAc.sloadCost_cold (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hms),
      a1'.sloadCost_warm (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]),
      cost_debit f3 a2 (by simp only [List.mem_cons, true_or]) hle1,
      a3.sloadCost_cold (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hmin.1, hmin.1, hmin.2, hmin.1⟩),
      cost_debit f5 a4 (by simp only [List.mem_cons, true_or]) hle2]
    omega
  · rw [hNext]
    have mC2 := mC.mono (T' := [t.toAdr]) (fun a ha => by
      simp only [List.append_nil, List.mem_append, List.mem_singleton, or_self] at ha
      exact List.mem_singleton.2 ha)
    refine mv_callChild (T := t.toAdr :: [t.toAdr]) _ _ (fun a ha => parent_same _ _ _ 0 t ii 0x44 oi 0x20 (fun e => ha (e ▸ List.mem_cons_self))) rfl
      (fun h => parent_clean _ _ _ 0 t ii 0x44 oi 0x20 ⟨h.created, h.del, h.error⟩) (fun a ha => ?_) ?_ (fun _ => mC.clean hcC)
    · have e : Same a (parent (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20) (initDevm c) := by
        rw [hc]; exact ⟨fun _ => Iff.rfl, rfl, Iff.rfl⟩
      exact e.trans (mC2.same a (fun hm => ha (List.mem_cons_of_mem _ hm)))
    · rw [mC.refund]
      show (0 : Int) + _ = _
      push_cast
      omega
  · rw [hNext]
    show Devm.getStor (bodyCanon (initSevm c) (initDevm c) t_0644_c0 (burnBodyCost (initSevm c) (initDevm c))) t.toAdr = _
    rw [← hcan.getStor_eq, hl, h_stor_c3, Devm.addLog_getStor]
    have := a5.stor
    rw [ct] at this
    unfold burnStor
    rw [← hk, hs1]
    exact this

end C3

end Blanc.Composition.Curve3PoolPublic
