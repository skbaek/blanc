import Blanc.Lift.DaiForward
import Blanc.Composition.Curve3Pool3CrvCoinExactTransport

/-!
# The pool's coin premises, discharged by DAI's deployed bytes

`CoinPushOkAt`, `CoinPullOkAt` and `CoinBalOkAt` for a coin holding DAI's certified runtime: the
child of the pool's call site is DAI's actual run (`DaiForward`, lifted by `lift_exact`), so the
coin's replies and ledger are its code's, not premises. The world invariants are any the pool's
caller picks, closed under what the clean child leaves (`CoinLeaves`).

`mutCallOkAt_of_childWith` is `mutCallOkAt_of_child` at any forwarded-gas floor and charge and any
reply test: USDT's empty reply and its higher worst case go through it.
-/

namespace Blanc.Composition.Curve3PoolDai

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves prec_false rawCallOk_one getCode_of_state
  getStor_of_state transferSel_abi transferFromSel_abi balanceOfSel_abi)
open Blanc.Lift.Dai (MoveFits PullFits moveStor spendStor balSlot allowSlot FrameLands)

section Shapes

variable {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes} {U : Nat} {ii is oi : B256}

/-- **A value-`0` `CALL` premise from a clean child, at any floor and reply test**: if at every
call-site world the child of the site's message, given at least `F`, halts cleanly within `Cb` gas
with a reply passing `ok`, keeping the caller's storage and the code at the identity precompile, and
leaving a world in `W'`, the premise holds with `U` covering the floor and the charge. -/
theorem mutCallOkAt_of_childWith {ok : Bytes → Prop} (F Cb : Nat)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false) (hF : F + F / 63 + 3100 ≤ U)
    (hCb : Cb + 3016 ≤ U)
    (hii : ii.toNat + is.toNat ≤ 4096) (hoi : oi.toNat + (0x20 : B256).toNat ≤ 4096)
    (hchild : ∀ (b : Devm) (S : List B256) (M : Mem) (G : Nat), W b →
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
    hchild b S M G hWb hin hfwd
  have hrun := call0_cross hfork hdepth hprec hdel hS hG hcharge hexec herr
  have hc := fwd_charge hcharge
  have hgas : (callChildPost (parent b S M G t ii is oi 0x20) cpost oi.toNat
      (0x20 : B256).toNat).gasLeft =
      G - (fwd b S M G t ii is oi 0x20 + acc b t + ext b S M ii is oi 0x20) + cpost.gasLeft := rfl
  refine ⟨_, hrun, ?_, ?_, ?_, ?_, ?_, hstor, hW', fun hid => ⟨?_, ?_, hid.pre, hid.fork⟩⟩
  · obtain ⟨flag, hpost⟩ := ri_call_post hfork (Ninst.Run.of_runCompiled hrun)
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

end Shapes

/-! ## DAI's calls as messages -/

open Blanc.Lift.Dai

theorem xfer_msg {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Dai.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : 58800 ≤ (initDevm msg).gasLeft)
    (hfits : MoveFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ 56500 ∧
      FrameLands (initSevm msg) (initDevm msg) post used 1
        (moveStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v)
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
          balSlot (initSevm msg).caller ≠ balSlot dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨w4, w36, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  obtain ⟨post, used, hu, L⟩ := xfer_lands (dst := dst) (v := v) (pre := initDevm msg) fork static
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold xTo; rw [lit4, w4, ff20_and_word, toAdr_toB256])
    (by unfold xVal; rw [lit36, w36]) rfl rfl hgas hfits
  exact ⟨post, used, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact cert_check jumps_ok hcode fork L.run),
    hu, L⟩

theorem pull_msg {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Dai.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++
      v.toBytes)
    (hgas : 90300 ≤ (initDevm msg).gasLeft)
    (hfits : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller
      dst v) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ 88000 ∧
      FrameLands (initSevm msg) (initDevm msg) post used 1
        (moveStor (spendStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src
          (initSevm msg).caller v) src dst v)
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
          allowSlot src (initSevm msg).caller ≠ balSlot src ∧
          allowSlot src (initSevm msg).caller ≠ balSlot dst ∧ balSlot src ≠ balSlot dst) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨post, used, hu, L⟩ := pull_lands (src := src) (dst := dst) (v := v) (pre := initDevm msg) fork static
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold pSrc; rw [lit4, w4, ff20_and_word, toAdr_toB256])
    (by unfold pTo; rw [lit36, w36, ff20_and_word, toAdr_toB256])
    (by unfold pVal; rw [lit36, show Bytes.toB256 [32] + (36 : B256) = 68 by decide, w68]) rfl rfl hgas hfits
  exact ⟨post, used, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact cert_check jumps_ok hcode fork L.run),
    hu, L⟩

theorem bal_msg {msg : Msg} {a : Adr} (hcode : (initSevm msg).code = Dai.code)
    (fork : CoveredFork (initSevm msg).benvStat.fork) (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x70a08231 ++ a.toB256.toBytes)
    (hgas : 5300 ≤ (initDevm msg).gasLeft) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ 3000 ∧
      FrameLands (initSevm msg) (initDevm msg) post used
        ((Devm.getStor (initDevm msg) (initSevm msg).currentTarget).get (balSlot a))
        (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) True := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have hl : (initSevm msg).data.length = 36 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨post, used, hu, L⟩ := bal_lands (a := a) (pre := initDevm msg) fork
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold bHolder; rw [lit4, Blanc.Lift.Curve3Pool.cc_dataWord_oneWord hd, ff20_and_word, toAdr_toB256])
    rfl rfl hgas
  exact ⟨post, used, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact cert_check jumps_ok hcode fork L.run),
    hu, L⟩

/-! ## The coin premises -/

section Premises

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {U : Nat} {ii oi : B256}

/-- What a clean DAI child's post leaves, seen from the parent's resumed state. -/
theorem leaves_of_lands {b : Devm} {S : List B256} {M : Mem} {G : Nat} {is : B256}
    {cpost : Devm} {used : Nat} {w : B256} {σ' : Stor} {R R' : Prop}
    (L : FrameLands (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
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

/-- **The pool's `transfer(msg.sender, amt)` into DAI succeeds**, at any window inside the first
4 KiB and `U ≥ 63000`, wherever the transfer fits the coin's ledger. -/
theorem dai_coinPushOkAt (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 63000 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Dai.code ∧
      MoveFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr (moveStor (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        balSlot sevm.currentTarget ≠ balSlot sevm.caller) b d → W' d) :
    CoinPushOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_childWith 58800 56500 hfork hdepth (by rw [prec_false hprec]) (by omega) (by omega)
    (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hin hfwd
  obtain ⟨hc, hfits⟩ := hW b hWb
  refine ⟨by rw [hc]; exact dai_undelegated, ?_⟩
  obtain ⟨cpost, used, hexec, hu, L⟩ := xfer_msg (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20)
    (dst := sevm.caller) (v := amt) hc hfork
    (by rw [callMsg0_isStatic]; exact hstatic) rfl
    (by rw [callMsg0_data, hin, transferSel_abi]) hfwd hfits
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x44 oi 0x20 - used := L.gas
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **The pool's `transferFrom(msg.sender, self, amt)` into DAI succeeds**, at any window inside the
first 4 KiB and `U ≥ 95000`, wherever the pull fits the coin's ledger. -/
theorem dai_coinPullOkAt (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 95000 ≤ U)
    (hii : ii.toNat + 0x64 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Dai.code ∧
      PullFits (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (moveStor (spendStor (b.getStor t.toAdr) sevm.caller sevm.currentTarget amt)
          sevm.caller sevm.currentTarget amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.caller ∧
        allowSlot sevm.caller sevm.currentTarget ≠ balSlot sevm.currentTarget ∧
        balSlot sevm.caller ≠ balSlot sevm.currentTarget) b d → W' d) :
    CoinPullOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_childWith 90300 88000 hfork hdepth (by rw [prec_false hprec]) (by omega) (by omega)
    (by rw [show (0x64 : B256).toNat = 0x64 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hin hfwd
  obtain ⟨hc, hfits⟩ := hW b hWb
  refine ⟨by rw [hc]; exact dai_undelegated, ?_⟩
  obtain ⟨cpost, used, hexec, hu, L⟩ := pull_msg (msg := callMsg0 sevm b S M G t ii 0x64 oi 0x20)
    (src := sevm.caller) (dst := sevm.currentTarget) (v := amt) hc hfork
    (by rw [callMsg0_isStatic]; exact hstatic) rfl
    (by rw [callMsg0_data, hin, transferFromSel_abi]) hfwd hfits
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x64 oi 0x20 - used := L.gas
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_lands L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_one
  · rw [L.out]; decide +kernel

/-- **The pool's `balanceOf(self)` into DAI answers the coin's entry**, at any window inside the
first 4 KiB and `U ≥ 70000`. -/
theorem dai_coinBalOkAt {B : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Dai.code ∧
      (b.getStor t.toAdr).get (balSlot sevm.currentTarget) = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    CoinBalOkAt sevm W W' t B U ii oi := by
  refine staticWordOkAt_of_child 3000 (by decide) hfork hdepth (by rw [prec_false hprec]) hU
    (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hin hfwd
  obtain ⟨hc, hB⟩ := hW b hWb
  refine ⟨by rw [hc]; exact dai_undelegated, ?_⟩
  obtain ⟨cpost, used, hexec, hu, L⟩ := bal_msg (msg := staticMsg sevm b S M G t ii 0x24 oi 0x20)
    (a := sevm.currentTarget) hc hfork rfl
    (by rw [staticMsg_data, hin]; unfold balanceOfData; rw [balanceOfSel_abi]) (by
      exact le_trans (by decide) hfwd)
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x24 oi 0x20 - used := L.gas
  have hst := callChildPost_state' (parent b S M G t ii 0x24 oi 0x20) cpost oi.toNat (0x20 : B256).toNat
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, L.keeps.code 4, hW' b _ hWb (fun a => ?_) (fun a => ?_)⟩
  · rw [L.out, ← hB]; rfl
  · rw [getStor_of_state hst]
    by_cases ha : a = t.toAdr
    · subst ha; exact L.stor
    · exact L.keeps.other a ha
  · rw [getCode_of_state hst]; exact L.keeps.code a

end Premises

end Blanc.Composition.Curve3PoolDai
