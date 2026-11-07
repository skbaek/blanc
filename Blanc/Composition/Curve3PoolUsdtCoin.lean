import Blanc.Lift.UsdtForwardLaws
import Blanc.Composition.Curve3PoolCoinChild

/-!
# The pool's coin premises, discharged by USDT's deployed bytes

`CoinPushOkAt`, `CoinPullOkAt` and `CoinBalOkAt` for a coin holding TetherToken's certified runtime. Its
`transfer` and `transferFrom` end in `STOP`, so the pool's `raw_call` sees an empty reply: `RawCallOk`
holds by its first disjunct, `length = 0`, and no byte of the reply is read. The ledger a world invariant
receives is `Usdt.moveStor` with the fee read from storage.

What remains are the operators' gates, on the world invariant: `NotDeprecated`, and through `XferFits`
and `PullFits` `NotPaused` and `NotListed`, with the fits of the fee rule and the move. While the token is
deprecated nothing is claimed.
-/

namespace Blanc.Composition.Curve3PoolUsdt

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Lift.AccumulatedWalk (FrameLands StopLands)
open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves prec_false getCode_of_state
  getStor_of_state transferSel_abi transferFromSel_abi balanceOfSel_abi)
open Blanc.Composition.Curve3PoolCoinChild

open Blanc.Lift.Usdt

/-- The pool's `raw_call` accepts a missing return value: an empty reply is `RawCallOk`'s first
disjunct, read as success without looking at a byte. -/
theorem rawCallOk_empty : RawCallOk [] := Or.inl rfl

/-! ## USDT's calls as messages -/

theorem xfer_msg {msg : Msg} {dst : Adr} {v : B256} (hcode : (initSevm msg).code = Usdt.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0xa9059cbb ++ dst.toB256.toBytes ++ v.toBytes)
    (hgas : 100056 ≤ (initDevm msg).gasLeft)
    (hdep : NotDeprecated (Devm.getStor (initDevm msg) (initSevm msg).currentTarget))
    (hfits : XferFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ 97756 ∧
      StopLands Usdt.cert.prog (initSevm msg) (initDevm msg) post used
        (moveStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v
          (feeOf (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) v))
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
          MoveApart (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) (initSevm msg).caller dst v
            (feeOf (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) v)) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨w4, w36, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  obtain ⟨post, used, hu, L⟩ := xfer_lands (dst := dst) (v := v) (pre := initDevm msg) fork static
    (lguards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold xTo; rw [lit4, w4, ff20_and_word, toAdr_toB256])
    (by unfold xVal; rw [lit36, w36]) rfl rfl rfl hgas hdep hfits
  exact ⟨post, used, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Usdt.cert_check Usdt.jumps_ok hcode fork L.run),
    hu, L⟩

theorem pull_msg {msg : Msg} {src dst : Adr} {v : B256} (hcode : (initSevm msg).code = Usdt.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (static : (initSevm msg).isStatic = false)
    (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x23b872dd ++ src.toB256.toBytes ++ dst.toB256.toBytes ++
      v.toBytes)
    (hgas : 124480 ≤ (initDevm msg).gasLeft)
    (hdep : NotDeprecated (Devm.getStor (initDevm msg) (initSevm msg).currentTarget))
    (hfits : PullFits (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller
      dst v) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ 122180 ∧
      StopLands Usdt.cert.prog (initSevm msg) (initDevm msg) post used
        (moveStor (spendStor (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src
          (initSevm msg).caller v) src dst v (feeOf (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) v))
        ((getOrigAcct (initSevm msg) (initSevm msg).currentTarget).stor =
            Devm.getStor (initDevm msg) (initSevm msg).currentTarget ∧
          (initSevm msg).currentTarget ∉ (initDevm msg).createdAccounts ∧
          PullApart (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) src (initSevm msg).caller dst v
            (feeOf (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) v)) := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨post, used, hu, L⟩ := pull_lands (src := src) (dst := dst) (v := v) (pre := initDevm msg) fork static
    (lguards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold pSrc; rw [lit4, w4, ff20_and_word, toAdr_toB256])
    (by unfold pTo; rw [lit36, w36, ff20_and_word, toAdr_toB256])
    (by unfold pVal; rw [lit36, show Bytes.toB256 [32] + (36 : B256) = 68 by decide, w68]) rfl rfl rfl hgas hdep hfits
  exact ⟨post, used, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Usdt.cert_check Usdt.jumps_ok hcode fork L.run),
    hu, L⟩

theorem bal_msg {msg : Msg} {a : Adr} (hcode : (initSevm msg).code = Usdt.code)
    (fork : ShanghaiOnwards (initSevm msg).benvStat.fork) (hval : (initSevm msg).value = 0)
    (hd : (initSevm msg).data = abiSelectorBytes 0x70a08231 ++ a.toB256.toBytes)
    (hgas : 7331 ≤ (initDevm msg).gasLeft)
    (hdep : NotDeprecated (Devm.getStor (initDevm msg) (initSevm msg).currentTarget)) :
    ∃ post used, exec (initEvm msg) = .ok post ∧ used ≤ 5031 ∧
      FrameLands Usdt.cert.prog (initSevm msg) (initDevm msg) post used
        ((Devm.getStor (initDevm msg) (initSevm msg).currentTarget).get (balSlot a))
        (Devm.getStor (initDevm msg) (initSevm msg).currentTarget) True := by
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have hl : (initSevm msg).data.length = 36 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨post, used, hu, L⟩ := bal_lands (a := a) (pre := initDevm msg) fork
    (lguards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold bHolder; rw [lit4, Blanc.Lift.Curve3Pool.cc_dataWord_oneWord hd, ff20_and_word, toAdr_toB256])
    rfl rfl hgas hdep
  exact ⟨post, used, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact Usdt.cert_check Usdt.jumps_ok hcode fork L.run),
    hu, L⟩

/-- What a stopped coin child's post leaves, seen from the parent's resumed state. -/
theorem leaves_of_stop {sevm : Sevm} {t ii oi : B256} {prog : List SFunc} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {is : B256}
    {cpost : Devm} {used : Nat} {σ' : Stor} {R R' : Prop}
    (L : StopLands prog (initSevm (callMsg0 sevm b S M G t ii is oi 0x20))
      (initDevm (callMsg0 sevm b S M G t ii is oi 0x20)) cpost used σ' R') (hR : R → R') :
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

/-! ## The coin premises -/

section Premises

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {U : Nat} {ii oi : B256}

/-- **The pool's `transfer(msg.sender, amt)` into USDT succeeds with no reply**, at any window inside the
first 4 KiB and `U ≥ 104744`, wherever the owner's gates are open and the transfer fits the coin's ledger,
the recipient credited `amt - fee` and the owner `fee`. -/
theorem usdt_coinPushOkAt (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 104744 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Usdt.code ∧ NotDeprecated (b.getStor t.toAdr) ∧
      XferFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (moveStor (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt (feeOf (b.getStor t.toAdr) amt))
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        MoveApart (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt (feeOf (b.getStor t.toAdr) amt)) b d → W' d) :
    CoinPushOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_childWith 100056 97756 hfork hdepth (by rw [prec_false hprec]) (by omega) (by omega)
    (by rw [show (0x44 : B256).toNat = 0x44 from rfl]; exact hii) hoi ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hdep, hfits⟩ := hW b hWb
  refine ⟨by rw [hc]; exact usdt_undelegated, ?_⟩
  obtain ⟨cpost, used, hexec, hu, L⟩ := xfer_msg (msg := callMsg0 sevm b S M G t ii 0x44 oi 0x20)
    (dst := sevm.caller) (v := amt) hc hfork
    (by rw [callMsg0_isStatic]; exact hstatic) rfl
    (by rw [callMsg0_data, hin, transferSel_abi]) hfwd hdep hfits
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x44 oi 0x20 - used := L.gas
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_stop L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_empty
  · rw [L.out]; decide

/-- **The pool's `transferFrom(msg.sender, self, amt)` into USDT succeeds with no reply**, at any window
inside the first 4 KiB and `U ≥ 129555`, wherever the owner's gates are open and the pull fits the coin's
ledger, the pool credited `amt - fee`. -/
theorem usdt_coinPullOkAt (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 129555 ≤ U)
    (hii : ii.toNat + 0x64 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Usdt.code ∧ NotDeprecated (b.getStor t.toAdr) ∧
      PullFits (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (moveStor (spendStor (b.getStor t.toAdr) sevm.caller sevm.currentTarget amt)
          sevm.caller sevm.currentTarget amt (feeOf (b.getStor t.toAdr) amt))
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        PullApart (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt
          (feeOf (b.getStor t.toAdr) amt)) b d → W' d) :
    CoinPullOkAt sevm W W' t amt U ii oi := by
  refine mutCallOkAt_of_childWith 124480 122180 hfork hdepth (by rw [prec_false hprec]) (by omega) (by omega)
    (by rw [show (0x64 : B256).toNat = 0x64 from rfl]; exact hii) hoi ?_
  intro b S M G hWb _ hin hfwd
  obtain ⟨hc, hdep, hfits⟩ := hW b hWb
  refine ⟨by rw [hc]; exact usdt_undelegated, ?_⟩
  obtain ⟨cpost, used, hexec, hu, L⟩ := pull_msg (msg := callMsg0 sevm b S M G t ii 0x64 oi 0x20)
    (src := sevm.caller) (dst := sevm.currentTarget) (v := amt) hc hfork
    (by rw [callMsg0_isStatic]; exact hstatic) rfl
    (by rw [callMsg0_data, hin, transferFromSel_abi]) hfwd hdep hfits
  have hgas : cpost.gasLeft = fwd b S M G t ii 0x64 oi 0x20 - used := L.gas
  refine ⟨cpost, hexec, L.keeps.error, by omega, by omega, ?_, ?_, L.keeps.other _ (Ne.symm hne), L.keeps.code 4,
    hW' b _ hWb (leaves_of_stop L (fun r => r))⟩
  · rw [L.out]; exact rawCallOk_empty
  · rw [L.out]; decide

/-- **The pool's `balanceOf(self)` into USDT answers the coin's entry**, at any window inside the first
4 KiB and `U ≥ 70000`, wherever the token is not deprecated. -/
theorem usdt_coinBalOkAt {B : B256} (hfork : ShanghaiOnwards sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Usdt.code ∧ NotDeprecated (b.getStor t.toAdr) ∧
      (b.getStor t.toAdr).get (balSlot sevm.currentTarget) = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    CoinBalOkAt sevm W W' t B U ii oi := by
  refine staticWordOkAt_of_child 5031 (by decide) hfork hdepth (by rw [prec_false hprec]) hU
    (by rw [show (0x24 : B256).toNat = 0x24 from rfl]; exact hii) hoi ?_
  intro b S M G hWb hin hfwd
  obtain ⟨hc, hdep, hB⟩ := hW b hWb
  refine ⟨by rw [hc]; exact usdt_undelegated, ?_⟩
  obtain ⟨cpost, used, hexec, hu, L⟩ := bal_msg (msg := staticMsg sevm b S M G t ii 0x24 oi 0x20)
    (a := sevm.currentTarget) hc hfork rfl
    (by rw [staticMsg_data, hin]; unfold balanceOfData; rw [balanceOfSel_abi]) (by
      exact le_trans (by decide) hfwd) hdep
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

end Blanc.Composition.Curve3PoolUsdt
