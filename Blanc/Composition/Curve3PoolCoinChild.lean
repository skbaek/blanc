import Blanc.Lift.CoinFrame
import Blanc.Lift.HistStaticCall
import Blanc.Composition.Curve3Pool3CrvCoinExactTransport

/-!
# A coin child, at the pool's call sites

`mutCallOkAt_of_childWith` is `mutCallOkAt_of_child` at any forwarded-gas floor and charge and any
reply test: a coin's empty reply and a worst case above `60000` go through it. `leaves_of_lands`
reads a clean coin child's `FrameLands` as the `CoinLeaves` the caller's world invariant closes under.
Neither names a coin.
-/

namespace Blanc.Composition.Curve3PoolCoinChild

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves getCode_of_state getStor_of_state)
open Blanc.Lift.AccumulatedWalk (FrameLands)

section Shapes

variable {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes} {U : Nat} {ii is oi : B256}

/-- **A value-`0` `CALL` premise from a clean child, at any floor and reply test**: if at every
call-site world the child of the site's message, given at least `F`, halts cleanly within `Cb` gas
with a reply passing `ok`, keeping the caller's storage and the code at the identity precompile, and
leaving a world in `W'`, the premise holds with `U` covering the floor and the charge. -/
theorem mutCallOkAt_of_childWith {ok : Bytes → Prop} (F Cb : Nat)
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hF : F + F / 63 + 3100 ≤ U)
    (hCb : Cb + 3016 ≤ U)
    (hii : ii.toNat + is.toNat ≤ 4096) (hoi : oi.toNat + (0x20 : B256).toNat ≤ 4096)
    (hchild : ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → G < 2 ^ 256 →
      (M.read ii.toNat is.toNat).1 = data → F ≤ fwd b S M G t ii is oi 0x20 →
      getDelegatedCodeAddress (b.getCode t.toAdr) = none ∧
      ∃ cpost, exec (initEvm (callMsg0 sevm b S M G t ii is oi 0x20)) = .ok cpost ∧
        cpost.error = none ∧ fwd b S M G t ii is oi 0x20 ≤ cpost.gasLeft + Cb ∧
        cpost.gasLeft ≤ fwd b S M G t ii is oi 0x20 ∧ ok cpost.output ∧ cpost.output.length < 2 ^ 256 ∧
        Devm.getStor cpost sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
        cpost.getCode 4 = b.getCode 4 ∧
        W' (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat (0x20 : B256).toNat)) :
    MutCallOkAt sevm W W' t data ok U ii is oi := by
  intro b S M G hWb hUG hG hin hS
  have he := ext_le (b := b) (S := S) (M := M) hii hoi
  have ha := acc_le (b := b) (t := t)
  have hcharge : acc b t + ext b S M ii is oi 0x20 ≤ G := by omega
  have hfwd : F ≤ fwd b S M G t ii is oi 0x20 := by
    unfold fwd except64th
    omega
  obtain ⟨hdel, cpost, hexec, herr, hg1, hg2, hok, hlen, hstor, hcode4, hW'⟩ :=
    hchild b S M G hWb hG hin hfwd
  have hrun := call0_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
  have hc := fwd_charge hcharge
  have hgas : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
      (0x20 : B256).toNat).gasLeft =
      G - (fwd b S M G t ii is oi 0x20 + acc b t + ext b S M ii is oi 0x20) + cpost.gasLeft := rfl
  refine ⟨_, hrun, ?_, ?_, ?_, ?_, ?_, hstor, hW', fun hid => ⟨?_, ?_, hid.pre, hid.fork⟩⟩
  · obtain ⟨flag, hpost⟩ := ri_call_postH hfork.rules_stateGas_none (Ninst.Run.of_runCompiled hrun)
    have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
      (callChildPost_stack' _ _ _ _))).1
    subst hflag
    exact hpost
  · rw [callChildPost_returnData']; exact hok
  · rw [callChildPost_returnData']; exact hlen
  · rw [hgas]; omega
  · rw [hgas]; omega
  · show getDelegatedCodeAddress (cpost.getCode 4) = none
    rw [hcode4]; exact hid.nodeleg
  · exact callChildPost_mem_warm _ _ _ _ 4 (parent_mem_warm b S M G t ii is oi 0x20 4 hid.warm)

/-- `staticWordOkAt_of_child` at any floor and with the call's gas below `2 ^ 256`, which a child that
itself reads `GAS` needs. -/
theorem staticWordOkAt_of_childWith {A : B256} (F Cb : Nat)
    (hfork : ShanghaiOnwards sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hF : F + F / 63 + 3100 ≤ U)
    (hCb : Cb ≤ 60000) (hU : 70000 ≤ U)
    (hii : ii.toNat + is.toNat ≤ 4096) (hoi : oi.toNat + (0x20 : B256).toNat ≤ 4096)
    (hchild : ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b → G < 2 ^ 256 →
      (M.read ii.toNat is.toNat).1 = data → F ≤ fwd b S M G t ii is oi 0x20 →
      getDelegatedCodeAddress (b.getCode t.toAdr) = none ∧
      ∃ cpost, exec (initEvm (staticMsg sevm b S M G t ii is oi 0x20)) = .ok cpost ∧
        cpost.error = none ∧ fwd b S M G t ii is oi 0x20 ≤ cpost.gasLeft + Cb ∧
        cpost.gasLeft ≤ fwd b S M G t ii is oi 0x20 ∧ cpost.output = A.toBytes ∧
        cpost.getCode 4 = b.getCode 4 ∧
        W' (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat (0x20 : B256).toNat)) :
    StaticWordOkAt sevm W W' t data A U ii is oi := by
  intro b S M G hWb hUG hG hin hS
  obtain ⟨hcharge, hfwd⟩ := fwd_ge (b := b) (S := S) (M := M) (t := t) (G := G) (by omega) hii hoi
  have hfwdF : F ≤ fwd b S M G t ii is oi 0x20 := by
    have he := ext_le (b := b) (S := S) (M := M) hii hoi
    have ha := acc_le (b := b) (t := t)
    unfold fwd except64th
    omega
  obtain ⟨hdel, cpost, hexec, herr, hg1, hg2, hout, hcode4, hW'⟩ :=
    hchild b S M G hWb hG hin hfwdF
  have hrun := static_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
  have he := ext_le (b := b) (S := S) (M := M) hii hoi
  have ha := acc_le (b := b) (t := t)
  have hc := fwd_charge hcharge
  have hgas : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
      (0x20 : B256).toNat).gasLeft =
      G - (fwd b S M G t ii is oi 0x20 + acc b t + ext b S M ii is oi 0x20) + cpost.gasLeft := rfl
  obtain ⟨flag, out, hpost, -, -⟩ := ri_staticcall_boundedH hfork.rules_stateGas_none (Ninst.Run.of_runCompiled hrun)
  have hflag : flag = 1 := (List.cons.inj (hpost.stack.symm.trans
    (callChildPost_stack' _ _ _ _))).1
  subst hflag
  have hout' : out = A.toBytes := by
    rw [← hpost.returnData, callChildPost_returnData', hout]
  subst hout'
  refine ⟨_, _, hrun, hpost, ?_, ?_, ?_, ?_, ?_, hW', fun hid => ⟨?_, ?_, hid.pre, hid.fork⟩⟩
  · rw [B256.length_toBytes]
  · rw [B256.length_toBytes]; decide
  · rw [List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes]
  · rw [hgas]; omega
  · rw [hgas]; omega
  · show getDelegatedCodeAddress (cpost.getCode 4) = none
    rw [hcode4]; exact hid.nodeleg
  · exact callChildPost_mem_warm _ _ _ _ 4 (parent_mem_warm b S M G t ii is oi 0x20 4 hid.warm)

end Shapes

/-- What a clean coin child's post leaves, seen from the parent's resumed state. -/
theorem leaves_of_lands {sevm : Sevm} {t ii oi : B256} {prog : List SFunc} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {is : B256}
    {cpost : Devm} {used : Nat} {w : B256} {σ' : Stor} {R R' : Prop}
    (L : FrameLands prog (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
      (initDevm (callMsg0 sevm b S M G t ii is oi 0x20)) cpost used w σ' R') (hR : R → R') :
    CoinLeaves t.toAdr σ' R b
      (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat (0x20 : B256).toNat) := by
  have hst := callChildPost_state' (parent b S M G t ii is oi 0x20) cpost oi.toNat (0x20 : B256).toNat
  refine ⟨fun a => ?_, fun a ha => ?_, ?_, rfl, L.keeps.created, fun r => ?_⟩
  · rw [getCode_of_state hst]; exact L.keeps.code a
  · rw [getStor_of_state hst]; exact L.keeps.other a ha
  · rw [getStor_of_state hst]; exact L.stor
  · have h0 : (0 : Int) ≤ cpost.refundCounter := L.refund (hR r)
    have : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
        (0x20 : B256).toNat).refundCounter = b.refundCounter + cpost.refundCounter := rfl
    rw [this]
    omega

end Blanc.Composition.Curve3PoolCoinChild
