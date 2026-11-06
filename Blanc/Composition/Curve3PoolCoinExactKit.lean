import Blanc.Composition.Curve3PoolCoinChild
import Blanc.Lift.Curve3Pool.ExactLivePremises
import Blanc.Lift.CallProfileTransport

/-!
# A coin child's exact profile at the pool's call sites

`coinMutProfile` and `coinStaticProfile`: if a child's cost `cost` and canonical post `canon` are functions
of the child's own entry, unchanged by the entry's gas, then the call site is an exact profile, with debit
`coinDebit` (the parent's access and expansion charges plus `cost`) and successor `coinNext`, both fixed at
the normalized site before any gas. No coin is named: each coin supplies `cost`, `canon` and its run.
-/

namespace Blanc.Composition.Curve3PoolCoinExactKit

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive

section Mutable

variable (cost : Sevm → Devm → Nat) (canon : Sevm → Devm → Devm) (sevm : Sevm) (t ii is oi : B256)
  (b : Devm) (S : List B256) (M : Mem)

/-- A value-`0` `CALL`'s debit: the parent's access and expansion, and the child's cost at the normalized
site's entry. It excludes the forwarded grant, which comes back. -/
def coinDebit : Nat :=
  acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii is oi 0x20 +
    cost (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))

/-- A value-`0` `CALL`'s canonical successor, from the normalized site. -/
def coinNext : Devm :=
  callChildPost (parent (b.withGasLeft 0) S M 0 t ii is oi 0x20)
    (canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
      (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)))
    oi.toNat (0x20 : B256).toNat

/-- A `STATICCALL`'s debit, as `coinDebit`. -/
def coinStaticDebit : Nat :=
  acc (b.withGasLeft 0) t + ext (b.withGasLeft 0) S M ii is oi 0x20 +
    cost (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
      (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))

/-- A `STATICCALL`'s canonical successor, as `coinNext`. -/
def coinStaticNext : Devm :=
  callChildPost (parent (b.withGasLeft 0) S M 0 t ii is oi 0x20)
    (canon (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
      (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)))
    oi.toNat (0x20 : B256).toNat

end Mutable

variable {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes} {U : Nat} {ii is oi : B256}

/-- **A value-`0` `CALL`'s exact profile from a child with a closed cost.** At every call-site world the
child of the site's message, given at least `F`, halts cleanly having spent exactly `cost` (at most `Cb`) of
its entry, in a post that agrees with `canon` of the normalized entry modulo gas. -/
theorem coinMutProfile {ok : Bytes → Prop} (F Cb : Nat) (cost : Sevm → Devm → Nat) (canon : Sevm → Devm → Devm)
    (hcost : ∀ s p G', cost {s with gas := G'} (p.withGasLeft G') = cost s p)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hF : F + F / 63 + 3100 ≤ U)
    (hCb : Cb + 3016 ≤ U) (hCF : Cb ≤ F)
    (hii : ii.toNat + is.toNat ≤ 4096) (hoi : oi.toNat + (0x20 : B256).toNat ≤ 4096)
    (hchild : ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → G < 2 ^ 256 →
      (M.read ii.toNat is.toNat).1 = data → F ≤ fwd b S M G t ii is oi 0x20 →
      getDelegatedCodeAddress (b.getCode t.toAdr) = none ∧
      cost (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
        (initDevm (callMsg0 sevm b S M G t ii is oi 0x20)) ≤ Cb ∧
      ∃ cpost, exec (initEvm (callMsg0 sevm b S M G t ii is oi 0x20)) = .ok cpost ∧
        cpost.error = none ∧
        cpost.gasLeft = fwd b S M G t ii is oi 0x20 -
          cost (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
            (initDevm (callMsg0 sevm b S M G t ii is oi 0x20)) ∧
        Devm.EqModGas cpost (canon (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))) ∧
        ok cpost.output ∧ cpost.output.length < 2 ^ 256 ∧
        Devm.getStor cpost sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
        cpost.getCode 4 = b.getCode 4 ∧
        W' (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat (0x20 : B256).toNat)) :
    MutableCallProfile sevm W W' t data ok U ii is oi (coinDebit cost sevm t ii is oi)
      (coinNext canon sevm t ii is oi) := by
  refine { entry_gas := ?_, congr := ?_, sound := ?_ }
  · intros; rfl
  · intro b b' S M h
    unfold coinDebit coinNext
    rw [h.withGasLeft_eq 0]
    exact ⟨rfl, .refl _⟩
  · rintro b S M G ⟨hWb, hUG, hG, hin, hS⟩
    have he := ext_le (b := b) (S := S) (M := M) (ii := ii) (is := is) (oi := oi) (os := 0x20) hii hoi
    have ha := acc_le (b := b) (t := t)
    have hcharge : acc b t + ext b S M ii is oi 0x20 ≤ G := by omega
    have hfwd : F ≤ fwd b S M G t ii is oi 0x20 := by
      unfold fwd except64th
      omega
    obtain ⟨hdel, hle, cpost, hexec, herr, hg, hcp, hok, hlen, hstor, hcode4, hW'⟩ :=
      hchild b S M G hWb hG hin hfwd
    have hused : cost (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
        (initDevm (callMsg0 sevm b S M G t ii is oi 0x20)) =
        cost (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) :=
      hcost (initSevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initDevm (callMsg0 sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) (fwd b S M G t ii is oi 0x20)
    have hdebit : coinDebit cost sevm t ii is oi b S M = acc b t + ext b S M ii is oi 0x20 +
        cost (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
          (initDevm (callMsg0 sevm b S M G t ii is oi 0x20)) := by
      unfold coinDebit
      rw [hused]
      rfl
    have hrun := call0_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
    have hc := fwd_charge hcharge
    have hgas : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
        (0x20 : B256).toNat).gasLeft =
        G - (fwd b S M G t ii is oi 0x20 + acc b t + ext b S M ii is oi 0x20) + cpost.gasLeft := rfl
    have hp : Devm.EqModGas (parent b S M G t ii is oi 0x20)
        (parent (b.withGasLeft 0) S M 0 t ii is oi 0x20) := by
      apply Devm.EqModGas.of_normalized_eq
      rfl
    refine ⟨by rw [hdebit]; omega, _, hrun, by rw [hgas, hdebit, hg]; omega,
      hp.callChildPost hcp _ _, ?_, ?_, ?_, hstor, hW', fun hid => ⟨?_, ?_, hid.pre, hid.fork⟩⟩
    · obtain ⟨flag, hpost⟩ := ri_call_post hfork (Ninst.Run.of_runCompiled hrun)
      have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
        (callChildPost_stack' _ _ _ _))).1
      subst hflag
      exact hpost
    · rw [callChildPost_returnData']; exact hok
    · rw [callChildPost_returnData']; exact hlen
    · show getDelegatedCodeAddress (cpost.getCode 4) = none
      rw [hcode4]; exact hid.nodeleg
    · exact callChildPost_mem_warm _ _ _ _ 4 (parent_mem_warm b S M G t ii is oi 0x20 4 hid.warm)

/-- **A `STATICCALL`'s exact profile from a child with a closed cost**, as `coinMutProfile`. -/
theorem coinStaticProfile {A : B256} (F Cb : Nat) (cost : Sevm → Devm → Nat) (canon : Sevm → Devm → Devm)
    (hcost : ∀ s p G', cost {s with gas := G'} (p.withGasLeft G') = cost s p)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hF : F + F / 63 + 3100 ≤ U)
    (hCb : Cb + 3016 ≤ U) (hCF : Cb ≤ F)
    (hii : ii.toNat + is.toNat ≤ 4096) (hoi : oi.toNat + (0x20 : B256).toNat ≤ 4096)
    (hchild : ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → G < 2 ^ 256 →
      (M.read ii.toNat is.toNat).1 = data → F ≤ fwd b S M G t ii is oi 0x20 →
      getDelegatedCodeAddress (b.getCode t.toAdr) = none ∧
      cost (initSevm (staticMsg sevm b S M G t ii is oi 0x20))
        (initDevm (staticMsg sevm b S M G t ii is oi 0x20)) ≤ Cb ∧
      ∃ cpost, exec (initEvm (staticMsg sevm b S M G t ii is oi 0x20)) = .ok cpost ∧
        cpost.error = none ∧
        cpost.gasLeft = fwd b S M G t ii is oi 0x20 -
          cost (initSevm (staticMsg sevm b S M G t ii is oi 0x20))
            (initDevm (staticMsg sevm b S M G t ii is oi 0x20)) ∧
        Devm.EqModGas cpost (canon (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))) ∧
        cpost.output = A.toBytes ∧ cpost.getCode 4 = b.getCode 4 ∧
        W' (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat (0x20 : B256).toNat)) :
    StaticWordCallProfile sevm W W' t data A U ii is oi (coinStaticDebit cost sevm t ii is oi)
      (coinStaticNext canon sevm t ii is oi) := by
  refine { entry_gas := ?_, congr := ?_, sound := ?_ }
  · intros; rfl
  · intro b b' S M h
    unfold coinStaticDebit coinStaticNext
    rw [h.withGasLeft_eq 0]
    exact ⟨rfl, .refl _⟩
  · rintro b S M G ⟨hWb, hUG, hG, hin, hS⟩
    have he := ext_le (b := b) (S := S) (M := M) (ii := ii) (is := is) (oi := oi) (os := 0x20) hii hoi
    have ha := acc_le (b := b) (t := t)
    have hcharge : acc b t + ext b S M ii is oi 0x20 ≤ G := by omega
    have hfwd : F ≤ fwd b S M G t ii is oi 0x20 := by
      unfold fwd except64th
      omega
    obtain ⟨hdel, hle, cpost, hexec, herr, hg, hcp, hout, hcode4, hW'⟩ :=
      hchild b S M G hWb hG hin hfwd
    have hused : cost (initSevm (staticMsg sevm b S M G t ii is oi 0x20))
        (initDevm (staticMsg sevm b S M G t ii is oi 0x20)) =
        cost (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
          (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) :=
      hcost (initSevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20))
        (initDevm (staticMsg sevm (b.withGasLeft 0) S M 0 t ii is oi 0x20)) (fwd b S M G t ii is oi 0x20)
    have hdebit : coinStaticDebit cost sevm t ii is oi b S M = acc b t + ext b S M ii is oi 0x20 +
        cost (initSevm (staticMsg sevm b S M G t ii is oi 0x20))
          (initDevm (staticMsg sevm b S M G t ii is oi 0x20)) := by
      unfold coinStaticDebit
      rw [hused]
      rfl
    have hrun := static_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
    have hc := fwd_charge hcharge
    have hgas : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
        (0x20 : B256).toNat).gasLeft =
        G - (fwd b S M G t ii is oi 0x20 + acc b t + ext b S M ii is oi 0x20) + cpost.gasLeft := rfl
    have hp : Devm.EqModGas (parent b S M G t ii is oi 0x20)
        (parent (b.withGasLeft 0) S M 0 t ii is oi 0x20) := by
      apply Devm.EqModGas.of_normalized_eq
      rfl
    obtain ⟨flag, out, hpost, -, -⟩ := ri_staticcall_bounded hfork (Ninst.Run.of_runCompiled hrun)
    have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
      (callChildPost_stack' _ _ _ _))).1
    subst hflag
    have hout' : out = A.toBytes := by
      rw [← hpost.returnData, callChildPost_returnData', hout]
    subst hout'
    refine ⟨by rw [hdebit]; omega, _, hrun, by rw [hgas, hdebit, hg]; omega,
      hp.callChildPost hcp _ _, _, hpost, ?_, ?_, ?_, hW', fun hid => ⟨?_, ?_, hid.pre, hid.fork⟩⟩
    · rw [B256.length_toBytes]
    · rw [B256.length_toBytes]; decide
    · rw [List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes]
    · show getDelegatedCodeAddress (cpost.getCode 4) = none
      rw [hcode4]; exact hid.nodeleg
    · exact callChildPost_mem_warm _ _ _ _ 4 (parent_mem_warm b S M G t ii is oi 0x20 4 hid.warm)

end Blanc.Composition.Curve3PoolCoinExactKit
