import Blanc.Composition.Curve3PoolCoinExactKit
import Blanc.Lift.ExactCallFloor

/-!
# A child's exact profile at its true floor

`coinMutFloor`, `coinStaticFloor`: an existing profile (admitted on one constant `U`) lowered to its floor. Only the
run needs low gas: the child, given what the site forwards once `K` is left over, halts at its closed cost. Everything
else the profile says is about a state equal modulo gas to the canonical successor, so it comes from the existing
profile at gas `U`, through `W'`'s stability. The floor's arithmetic: `L` the gas after the parent's charges, `c ≤ Cb`
the child's cost, `L ≥ c + K`; the 64th retained leaves the child `c + X` when `X + (K + Cb) / 64 + 1 ≤ K`.
-/

namespace Blanc.Composition.Curve3PoolCoinExactKit

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive

/-- A world predicate that does not read execution gas. -/
def GasStable (W : Devm → Prop) : Prop := ∀ d d', Devm.EqModGas d d' → W d → W d'

theorem _root_.Blanc.Devm.EqModGas.getStor_eq {a b : Devm} (h : Devm.EqModGas a b) (x : Adr) :
    Devm.getStor a x = Devm.getStor b x := by
  have hst : a.state = b.state := h.state
  unfold Devm.getStor Devm.getAcct; rw [hst]

theorem _root_.Blanc.Devm.EqModGas.getCode_eq {a b : Devm} (h : Devm.EqModGas a b) (x : Adr) :
    a.getCode x = b.getCode x := by
  have hst : a.state = b.state := h.state
  unfold Devm.getCode Devm.getAcct; rw [hst]

/-- What an equality modulo gas keeps of what identity readiness reads. -/
theorem _root_.Blanc.Devm.EqModGas.baseRel {a b : Devm} (h : Devm.EqModGas a b) : BaseRel a b :=
  ⟨fun x => (h.getStor_eq x).symm, fun x => (h.getCode_eq x).symm, h.accessedAddresses.symm, h.logs.symm,
    h.output.symm, h.error.symm⟩

theorem floor_fwd {b : Devm} {S : List B256} {M : Mem} {G : Nat} {t ii is oi : B256} {c X K Cb : Nat}
    (hK : X + (K + Cb) / 64 + 1 ≤ K) (hc : c ≤ Cb)
    (h : acc b t + ext b S M ii is oi 0x20 + c + K ≤ G) :
    c + X ≤ fwd b S M G t ii is oi 0x20 := by
  unfold fwd except64th
  omega

variable {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes} {U : Nat} {ii is oi : B256}

/-- **A `CALL`'s exact profile lowered to its floor.** -/
theorem coinMutFloor {ok : Bytes → Prop} (X K Cb : Nat) (cost : Sevm → Devm → Nat) (canon : Sevm → Devm → Devm)
    (hcost : ∀ s p G', cost {s with gas := G'} (p.withGasLeft G') = cost s p)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hK : X + (K + Cb) / 64 + 1 ≤ K) (hU : U < 2 ^ 256) (hs : GasStable W')
    (hp : MutableCallProfile sevm W W' t data ok U ii is oi (coinDebit cost sevm t ii is oi)
      (coinNext canon sevm t ii is oi))
    (hCb : ∀ b S M, W b → (M.read ii.toNat is.toNat).1 = data →
      cost (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) ≤ Cb)
    (hchild : ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → G < 2 ^ 256 →
      (M.read ii.toNat is.toNat).1 = data →
      cost (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
          (initDevm (callMsg0 sevm b S M G t ii is oi 0x20)) + X ≤ fwd b S M G t ii is oi 0x20 →
      getDelegatedCodeAddress (b.getCode t.toAdr) = none ∧
      ∃ cpost, exec (initEvm (callMsg0 sevm b S M G t ii is oi 0x20)) = .ok cpost ∧
        cpost.gasLeft = fwd b S M G t ii is oi 0x20 -
          cost (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
            (initDevm (callMsg0 sevm b S M G t ii is oi 0x20)) ∧
        Devm.EqModGas cpost (canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)))) :
    MutableFloorProfile sevm W W' t data ok U K ii is oi (coinDebit cost sevm t ii is oi)
      (coinNext canon sevm t ii is oi) := by
  refine { entry_gas := ?_, congr := hp.congr, sound := ?_ }
  · intros; rfl
  · rintro b S M G ⟨hWb, hfl, hG, hin, hS⟩
    have hd : coinDebit cost sevm t ii is oi b S M = acc b t + ext b S M ii is oi 0x20 +
        cost (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) := rfl
    obtain ⟨hle, dH, -, -, hnH, -, hok, hlen, hstor, hW', hid⟩ :=
      hp.sound b S M U ⟨hWb, le_refl _, hU, hin, hS⟩
    have hfwd := floor_fwd (b := b) (S := S) (M := M) (G := G) (t := t) (ii := ii) (is := is) (oi := oi)
      hK (hCb b S M hWb hin) (by rw [← hd]; exact hfl)
    have hused : cost (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
        (initDevm (callMsg0 sevm b S M G t ii is oi 0x20)) =
        cost (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) :=
      hcost (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) (fwd b S M G t ii is oi 0x20)
    obtain ⟨hdel, cpost, hexec, hg, hcp⟩ := hchild b S M G hWb hG hin (by rw [hused]; exact hfwd)
    rw [hused] at hg
    have herr : cpost.error = none := by
      obtain ⟨run⟩ := (exec_iff_exec_eq 0 _ _ _).mpr hexec
      exact (Exec.ok_error_eq run hfork.rules_stateGas_none).trans (callMsg0_error ..)
    have hcharge : acc b t + ext b S M ii is oi 0x20 ≤ G := by omega
    have hrun := call0_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
    have hc := fwd_charge hcharge
    have hgas : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
        (0x20 : B256).toNat).gasLeft =
        G - (fwd b S M G t ii is oi 0x20 + acc b t + ext b S M ii is oi 0x20) + cpost.gasLeft := rfl
    have hpr : Devm.EqModGas (parent b S M G t ii is oi 0x20)
        (parent (b.withGasLeft 0) S M 0 t ii is oi 0x20) := by
      apply Devm.EqModGas.of_normalized_eq
      rfl
    have hn : Devm.EqModGas (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
        (0x20 : B256).toNat) (coinNext canon sevm t ii is oi b S M) := hpr.callChildPost hcp _ _
    have hL := hn.trans hnH.symm
    refine ⟨hle, _, hrun, by rw [hgas, hd, hg]; omega, hn, ?_, ?_, ?_, ?_, hs _ _ hL.symm hW',
      fun hb => (hid hb).of_rel hL.symm.baseRel⟩
    · obtain ⟨flag, hpost⟩ := ri_call_post hfork (Ninst.Run.of_runCompiled hrun)
      have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
        (callChildPost_stack' _ _ _ _))).1
      subst hflag
      exact hpost
    · rw [hL.returnData]; exact hok
    · rw [hL.returnData]; exact hlen
    · exact (hL.getStor_eq _).trans hstor

/-- **A `STATICCALL`'s exact profile lowered to its floor**, as `coinMutFloor`. -/
theorem coinStaticFloor {A : B256} (X K Cb : Nat) (cost : Sevm → Devm → Nat) (canon : Sevm → Devm → Devm)
    (hcost : ∀ s p G', cost {s with gas := G'} (p.withGasLeft G') = cost s p)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hK : X + (K + Cb) / 64 + 1 ≤ K) (hU : U < 2 ^ 256) (hs : GasStable W')
    (hp : StaticWordCallProfile sevm W W' t data A U ii is oi (coinStaticDebit cost sevm t ii is oi)
      (coinStaticNext canon sevm t ii is oi))
    (hCb : ∀ b S M, W b → (M.read ii.toNat is.toNat).1 = data →
      cost (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) ≤ Cb)
    (hchild : ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → G < 2 ^ 256 →
      (M.read ii.toNat is.toNat).1 = data →
      cost (initSevm (staticMsg sevm b S M G t ii is oi 0x20))
          (initDevm (staticMsg sevm b S M G t ii is oi 0x20)) + X ≤ fwd b S M G t ii is oi 0x20 →
      getDelegatedCodeAddress (b.getCode t.toAdr) = none ∧
      ∃ cpost, exec (initEvm (staticMsg sevm b S M G t ii is oi 0x20)) = .ok cpost ∧
        cpost.gasLeft = fwd b S M G t ii is oi 0x20 -
          cost (initSevm (staticMsg sevm b S M G t ii is oi 0x20))
            (initDevm (staticMsg sevm b S M G t ii is oi 0x20)) ∧
        Devm.EqModGas cpost (canon (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)))) :
    StaticWordFloorProfile sevm W W' t data A U K ii is oi (coinStaticDebit cost sevm t ii is oi)
      (coinStaticNext canon sevm t ii is oi) := by
  refine { entry_gas := ?_, congr := hp.congr, sound := ?_ }
  · intros; rfl
  · rintro b S M G ⟨hWb, hfl, hG, hin, hS⟩
    have hd : coinStaticDebit cost sevm t ii is oi b S M = acc b t + ext b S M ii is oi 0x20 +
        cost (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) := rfl
    obtain ⟨hle, dH, -, -, hnH, out, hpH, hl32, hllt, hA, hW', hid⟩ :=
      hp.sound b S M U ⟨hWb, le_refl _, hU, hin, hS⟩
    have hfwd := floor_fwd (b := b) (S := S) (M := M) (G := G) (t := t) (ii := ii) (is := is) (oi := oi)
      hK (hCb b S M hWb hin) (by rw [← hd]; exact hfl)
    have hused : cost (initSevm (staticMsg sevm b S M G t ii is oi 0x20))
        (initDevm (staticMsg sevm b S M G t ii is oi 0x20)) =
        cost (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) :=
      hcost (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) (fwd b S M G t ii is oi 0x20)
    obtain ⟨hdel, cpost, hexec, hg, hcp⟩ := hchild b S M G hWb hG hin (by rw [hused]; exact hfwd)
    rw [hused] at hg
    have herr : cpost.error = none := by
      obtain ⟨run⟩ := (exec_iff_exec_eq 0 _ _ _).mpr hexec
      exact (Exec.ok_error_eq run hfork.rules_stateGas_none).trans (staticMsg_error ..)
    have hcharge : acc b t + ext b S M ii is oi 0x20 ≤ G := by omega
    have hrun := static_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
    have hc := fwd_charge hcharge
    have hgas : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
        (0x20 : B256).toNat).gasLeft =
        G - (fwd b S M G t ii is oi 0x20 + acc b t + ext b S M ii is oi 0x20) + cpost.gasLeft := rfl
    have hpr : Devm.EqModGas (parent b S M G t ii is oi 0x20)
        (parent (b.withGasLeft 0) S M 0 t ii is oi 0x20) := by
      apply Devm.EqModGas.of_normalized_eq
      rfl
    have hn : Devm.EqModGas (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
        (0x20 : B256).toNat) (coinStaticNext canon sevm t ii is oi b S M) := hpr.callChildPost hcp _ _
    have hL := hn.trans hnH.symm
    obtain ⟨flag, out', hpost, -, -⟩ := ri_staticcall_bounded hfork (Ninst.Run.of_runCompiled hrun)
    have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
      (callChildPost_stack' _ _ _ _))).1
    subst hflag
    have hout : out' = out := by
      rw [← hpost.returnData, ← hpH.returnData, hL.returnData]
    subst hout
    exact ⟨hle, _, hrun, by rw [hgas, hd, hg]; omega, hn, out', hpost, hl32, hllt, hA,
      hs _ _ hL.symm hW', fun hb => (hid hb).of_rel hL.symm.baseRel⟩

end Blanc.Composition.Curve3PoolCoinExactKit
