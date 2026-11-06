import Blanc.Composition.Curve3PoolCalleeExactProfiles
import Blanc.Composition.Curve3PoolCoinFloorKit
import Blanc.Lift.WalkCostExact

/-!
# 3Crv's exact profiles at their floors

`c3crv_supplyFloor`, `c3crv_burnFloor`: the selected-cost profiles of `Curve3PoolCalleeExactProfiles`, lowered by
`coinStaticFloor` and `coinMutFloor`. The bodies' runs need only the sentry above their cost.
-/

namespace Blanc.Composition.Curve3PoolCalleeExactProfiles

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Lift.AccumulatedWalk (afterSload_withGasLeft afterSstore_withGasLeft sloadCost_withGasLeft sstoreCost_withGasLeft
  getStorVal_withGasLeft)
open Curve3Crv

theorem totalSupplyBodyCost_reframe (s : Sevm) (p : Devm) (G' : Nat) :
    totalSupplyBodyCost {s with gas := G'} (p.withGasLeft G') = totalSupplyBodyCost s p := by
  simp only [totalSupplyBodyCost, sloadCost_withStaticGas, sloadCost_withGasLeft]

theorem burnBodyCost_reframe (s : Sevm) (p : Devm) (G' : Nat) :
    burnBodyCost {s with gas := G'} (p.withGasLeft G') = burnBodyCost s p := by
  simp only [burnBodyCost, Sevm.argWord, dataWord_withStaticGas, afterSload_withStaticGas, afterSload_withGasLeft,
    afterSstore_withStaticGas, afterSstore_withGasLeft, sloadCost_withStaticGas, sloadCost_withGasLeft,
    sstoreCost_withStaticGas, sstoreCost_withGasLeft, getStorVal_withGasLeft]

variable {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {U : Nat} {ii oi : B256}

/-- **`totalSupply()` at its floor.** -/
theorem c3crv_supplyFloor {T : B256} {K : Nat} (hK : 2301 + (K + 2320) / 64 + 1 ≤ K)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hU : 70000 ≤ U) (hUw : U < 2 ^ 256) (hs : GasStable W') (hii : ii.toNat + 4 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧
      (b.getStor t.toAdr).get vySupplySlot = T)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    StaticWordFloorProfile sevm W W' t totalSupplyData T U K ii 4 oi (supplyDebit sevm t ii oi)
      (supplyNext sevm t ii oi) := by
  refine coinStaticFloor 2301 K 2320 (fun s p => totalSupplyBodyCost s p + dispatchGas 2)
    (fun s p => bodyCanon s p t_0240_c0 (totalSupplyBodyCost s p))
    (fun s p G' => congrArg (· + dispatchGas 2) (totalSupplyBodyCost_reframe s p G'))
    hfork hdepth hprec hK hUw hs (c3crv_supplyProfile hfork hdepth hprec hU hii hoi hW hW')
    (fun b S M _ _ => by
      have h := Blanc.sloadCost_le (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
        (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)) vySupplySlot
      have hcs : gasColdSload = 2100 := rfl
      have hdisp : dispatchGas 2 = 186 := rfl
      unfold totalSupplyBodyCost
      omega) ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hcode, hT⟩ := hW b hWb
  have hused : totalSupplyBodyCost (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20))
      (initDevm (staticMsg sevm b S M G t ii 4 oi 0x20)) = supplyBodyCost sevm t ii oi b S M :=
    totalSupplyBodyCost_reframe (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
      (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)) (fwd b S M G t ii 4 oi 0x20)
  rw [hused] at hfwd
  have hfork0 : CoveredFork
      (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)).benvStat.fork := hfork
  have hraw : rawTotalSupply (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
      (Devm.getStor (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
        (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)).currentTarget) =
      some (Devm.getStor b t.toAdr, [],
        some ((Devm.getStor b t.toAdr).get vySupplySlot).toBytes) := by
    unfold rawTotalSupply
    rw [ite_eq_left (staticMsg_value ..)]
    rfl
  have hbody := live_totalSupply_cost hfork0 hraw
  have hdisp : dispatchGas 2 = 186 := rfl
  obtain ⟨p0, h0, -, -⟩ := hbody (gCallStipend + 1) (Nat.lt_succ_self _)
  obtain ⟨post, hrun, hpg, hl⟩ := hbody
    (fwd b S M G t ii 4 oi 0x20 - (supplyBodyCost sevm t ii oi b S M + dispatchGas 2))
    (by unfold gCallStipend; omega)
  have hrunF := hrun.withStaticGas (fwd b S M G t ii 4 oi 0x20)
  have hrunA : SFunc.RunExact prog (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20))
      (entrySt (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20))
        (initDevm (staticMsg sevm b S M G t ii 4 oi 0x20))
        (fwd b S M G t ii 4 oi 0x20 - (supplyBodyCost sevm t ii oi b S M + dispatchGas 2) +
          supplyBodyCost sevm t ii oi b S M)) t_0240_c0 (.halted post) := hrunF
  have hdata : (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)).data =
      abiSelectorBytes selTotalSupply ++ [] := by
    rw [staticMsg_data, hin, List.append_nil, totalSupplySel_eq]
  have hsel : Sevm.selector (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)) =
      selTotalSupply := selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hdata
  have hlen : (initSevm (staticMsg sevm b S M G t ii 4 oi 0x20)).data.length = 4 := by
    rw [hdata]; decide
  obtain ⟨hexec, -, -⟩ :=
    c3crv_msg_exact (msg := staticMsg sevm b S M G t ii 4 oi 0x20) (k := 2)
    (by rw [staticMsg_code]; exact hcode) hfork
    (by rw [staticMsg_codeAddress]; exact Option.some_ne_none _) rfl (by rw [hsel]; rfl)
    (by rw [hlen]) (by rw [hlen]; decide) (staticMsg_error ..)
    (by rw [staticMsg_gas]; omega) hrunA
  have hsg0 :
      (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)).benvStat.rules.stateGas =
        none := hfork.rules_stateGas_none
  refine ⟨by rw [hcode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel), post, hexec,
    by rw [hused]; exact hpg, bodyCanon_spec hsg0 supply_body_certificate.1 supply_body_certificate.2
      ⟨p0, h0⟩ hrunF⟩

/-- The supply read's debit at a window inside the frame's memory. -/
theorem supplyDebit_le (hii : ii.toNat + 4 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096) (b : Devm) (S : List B256) (M : Mem) :
    supplyDebit sevm t ii oi b S M ≤ 5336 := by
  have he := ext_le (b := b.withGasLeft 0) (S := S) (M := M) (ii := ii) (is := 4) (oi := oi) (os := 0x20)
    (by rw [show (4 : B256).toNat = 4 from rfl]; exact hii)
    (by rw [show (0x20 : B256).toNat = 0x20 from rfl]; exact hoi)
  have ha := acc_le (b := b.withGasLeft 0) (t := t)
  have h := Blanc.sloadCost_le (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20))
    (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii 4 oi 0x20)) vySupplySlot
  have hcs : gasColdSload = 2100 := rfl
  have hdisp : dispatchGas 2 = 186 := rfl
  unfold supplyDebit supplyBodyCost totalSupplyBodyCost
  omega

/-- **`burnFrom` at its floor.** -/
theorem c3crv_burnFloor {amt : B256} {K : Nat} (hK : 2301 + (K + 60000) / 64 + 1 ≤ K)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hU : 70000 ≤ U) (hUw : U < 2 ^ 256) (hs : GasStable W')
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 0x20 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Curve3Crv.code ∧ t.toAdr ≠ sevm.currentTarget ∧
      BurnFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller.toB256 amt)
    (hW' : ∀ b d, W b → (∀ a, a ≠ t.toAdr → Devm.getStor d a = Devm.getStor b a) →
      Devm.getStor d t.toAdr = burnStor (b.getStor t.toAdr) sevm.caller.toB256 amt →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    MutableFloorProfile sevm W W' t (burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes)
      (fun r => 32 ≤ r.length) U K ii 0x44 oi (mutDebit burnBodyCost 8 sevm t ii oi)
      (mutNext burnBodyCost t_0644_c0 sevm t ii oi) := by
  refine coinMutFloor 2301 K 60000 (fun s p => burnBodyCost s p + dispatchGas 8)
    (fun s p => bodyCanon s p t_0644_c0 (burnBodyCost s p))
    (fun s p G' => congrArg (· + dispatchGas 8) (burnBodyCost_reframe s p G'))
    hfork hdepth hprec hK hUw hs
    (c3crv_burnProfile hfork hstatic hdepth hprec hU hii hoi hW hW')
    (fun b S M _ _ => by
      have h := burnBodyCost_le (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
        (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      have hdisp : dispatchGas 8 ≤ 1000 := by decide
      omega) ?_
  intro b S M G hWb hG hin hfwd
  obtain ⟨hcode, hne, hfits⟩ := hW b hWb
  have hused : burnBodyCost (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)) = mutBodyCost burnBodyCost sevm t ii oi b S M :=
    burnBodyCost_reframe (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) (fwd b S M G t ii 0x44 oi 0x20)
  rw [hused] at hfwd
  have hdata : (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)).data =
      burnFromSel ++ sevm.caller.toB256.toBytes ++ amt.toBytes :=
    (callMsg0_data ..).trans hin
  have hraw := rawBurnFrom_of_fits
    (stor := Devm.getStor (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
      (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)).currentTarget)
    (callMsg0_value ..) hdata (adr_toB256_lt _) hfits
  have hlen0 := (argWords (by rw [hdata, burnFromSel_eq])).2.2
  have hsel0 : Sevm.selector (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)) = selBurnFrom :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hdata, burnFromSel_eq, List.append_assoc])
  have hbody := live_burnFrom_cost (sevm := initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20))
    hfork (by rw [callMsg0_isStatic]; exact hstatic) hraw
  obtain ⟨p0, h0, -, -⟩ := hbody (gCallStipend + 1) (Nat.lt_succ_self _)
  obtain ⟨post, hrun, hpg, hl⟩ := hbody
    (fwd b S M G t ii 0x44 oi 0x20 - (mutBodyCost burnBodyCost sevm t ii oi b S M + dispatchGas 8))
    (by unfold gCallStipend; omega)
  have hrunF := hrun.withStaticGas (fwd b S M G t ii 0x44 oi 0x20)
  have hrunA : SFunc.RunExact prog (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20))
      (entrySt (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20))
        (initDevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20))
        (fwd b S M G t ii 0x44 oi 0x20 - (mutBodyCost burnBodyCost sevm t ii oi b S M + dispatchGas 8) +
          mutBodyCost burnBodyCost sevm t ii oi b S M)) t_0644_c0 (.halted post) := hrunF
  have hlen : (initSevm (callMsg0 sevm b S M G t ii 0x44 oi 0x20)).data.length = 68 := by
    rw [callMsg0_data, hin]; rw [← hdata]; exact hlen0
  obtain ⟨hexec, -, -⟩ :=
    c3crv_msg_exact (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20) (k := 8)
    (by rw [callMsg0_code]; exact hcode) hfork
    (by rw [callMsg0_codeAddress]; exact Option.some_ne_none _) rfl
    (by exact congrArg some hsel0.symm)
    (by rw [hlen]; decide) (by rw [hlen]; decide) (callMsg0_error ..)
    (by rw [callMsg0_gas]; omega) hrunA
  have hsg0 :
      (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii 0x44 oi 0x20)).benvStat.rules.stateGas
        = none := hfork.rules_stateGas_none
  refine ⟨by rw [hcode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel), post, hexec,
    by rw [hused]; exact hpg, bodyCanon_spec hsg0 burn_body_certificate.1 burn_body_certificate.2 ⟨p0, h0⟩ hrunF⟩

end Blanc.Composition.Curve3PoolCalleeExactProfiles
