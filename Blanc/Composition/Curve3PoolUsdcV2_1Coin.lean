import Blanc.Lift.Usdc.V2_1Forward
import Blanc.Composition.Curve3PoolUsdcCoin

/-!
# USDC's FiatTokenV2_1 laws on messages

`xferLaw`, `pullLaw`, `balLaw`: FiatTokenV2_1's certified runtime, entered with the pool's calls, by
`V2_1Forward` lifted through `lift_exact`. `Curve3PoolUsdcCoin` carries them through the proxy to the
pool's coin premises (`usdcV2_1_coinPushOkAt` and siblings fix the numbers).
-/

namespace Blanc.Composition.Curve3PoolUsdcV2_1

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Lift.Curve3Pool
open ImplV2 (xTo xVal pFrom pTo pVal bHolder)
open Blanc.Composition.UsdcLive (XferLaw PullLaw BalLaw ProxyAt usdc_coinPushOkAt usdc_coinPullOkAt usdc_coinBalOkAt)
open Blanc.Lift.AccumulatedWalk (FrameLands guards_of)

theorem litA : Bytes.toB256 [4] = 4 := by decide
theorem litB : Bytes.toB256 [32] + Bytes.toB256 [4] = 36 := by decide

/-- **FiatTokenV2_1's `transfer` law.** -/
theorem xferLaw : XferLaw ImplV2_1.code ImplV2_1.cert.prog 70300 68000 ImplV2.MoveFits ImplV2.moveStor
    (fun a d => ImplV2.balSlot a ≠ ImplV2.balSlot d) := by
  intro msg dst v hcode fork static hval hd hF hfits
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0xa9059cbb :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) (by rw [hd, List.append_assoc])
  obtain ⟨w4, w36, hl⟩ := Blanc.Lift.dataWord_twoWords hd
  obtain ⟨C, u, hu, L⟩ := ImplV2_1.xfer_lands (dst := dst) (v := v)
    (sevm := initSevm msg) (pre := initDevm msg) fork static
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold xTo; rw [litA, w4, word_ff20, toAdr_toB256])
    (by unfold xVal; rw [litB, w36]) rfl rfl hF hfits
  exact ⟨C, u, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact ImplV2_1.cert_check ImplV2_1.jumps_ok hcode fork L.run), hu, L⟩

/-- **FiatTokenV2_1's `transferFrom` law.** -/
theorem pullLaw : PullLaw ImplV2_1.code ImplV2_1.cert.prog 98300 96000 ImplV2.PullFits ImplV2.fromStor
    (fun s sp d => ImplV2.allowSlot s sp ≠ ImplV2.balSlot s ∧ ImplV2.allowSlot s sp ≠ ImplV2.balSlot d ∧
      ImplV2.balSlot s ≠ ImplV2.balSlot d) := by
  intro msg src dst v hcode fork static hval hd hF hfits
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x23b872dd :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
      (by rw [hd, List.append_assoc, List.append_assoc])
  obtain ⟨w4, w36, w68⟩ := Blanc.Lift.Curve3Pool.cc_dataWord_threeWords hd
  have hl : (initSevm msg).data.length = 100 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨C, u, hu, L⟩ := ImplV2_1.pull_lands (src := src) (dst := dst) (v := v)
    (sevm := initSevm msg) (pre := initDevm msg) fork static
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold pFrom; rw [litA, w4, ff20_and_word, toAdr_toB256])
    (by unfold pTo; rw [litA, show (4 : B256) + Bytes.toB256 [32] = 36 by decide, w36, ff20_and_word, toAdr_toB256])
    (by unfold pVal; rw [show Bytes.toB256 [64] + Bytes.toB256 [4] = 68 by decide, w68]) rfl rfl hF hfits
  exact ⟨C, u, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact ImplV2_1.cert_check ImplV2_1.jumps_ok hcode fork L.run), hu, L⟩

/-- **FiatTokenV2_1's `balanceOf` law**: the answer is the entry. -/
theorem balLaw : BalLaw ImplV2_1.code ImplV2_1.cert.prog 5300 3000 (fun σ a => σ.get (ImplV2.balSlot a)) := by
  intro msg a hcode fork hval hd hF
  have hsel : Blanc.Sevm.selector (initSevm msg) = 0x70a08231 :=
    selector_eq_of_data_eq_abiSelectorBytes_append (by decide) hd
  have hl : (initSevm msg).data.length = 36 := by
    rw [hd]
    simp only [List.length_append, B256.length_toBytes, abiSelectorBytes_length]
  obtain ⟨C, u, hu, L⟩ := ImplV2_1.bal_lands (a := a)
    (sevm := initSevm msg) (pre := initDevm msg) fork
    (guards_of hval hsel (by rw [hl]; decide) (by rw [hl]; decide))
    (by unfold bHolder; rw [litA, Blanc.Lift.Curve3Pool.cc_dataWord_oneWord hd, ff20_and_word, toAdr_toB256])
    rfl rfl hF
  exact ⟨C, u, (exec_iff_exec_eq 0 _ _ (.ok _)).mp (lift_exact ImplV2_1.cert_check ImplV2_1.jumps_ok hcode fork L.run), hu, L⟩

section Premises

open Blanc.Composition.Curve3Pool3CrvInstance (CoinLeaves)

variable {sevm : Sevm} {t amt : B256} {W W' : Devm → Prop} {U : Nat} {ii oi : B256}

/-- **The pool's `transfer(msg.sender, amt)` into USDC over FiatTokenV2_1 succeeds** at `U ≥ 85000`. -/
theorem usdcV2_1_coinPushOkAt (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 85000 ≤ U)
    (hii : ii.toNat + 0x44 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr ImplV2_1.code ∧
      ImplV2.MoveFits (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr (ImplV2.moveStor (b.getStor t.toAdr) sevm.currentTarget sevm.caller amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        ImplV2.balSlot sevm.currentTarget ≠ ImplV2.balSlot sevm.caller) b d → W' d) :
    CoinPushOkAt sevm W W' t amt U ii oi :=
  usdc_coinPushOkAt @xferLaw (by omega) hfork hstatic hdepth hprec hne (by omega) hii hoi hW hW'

/-- **The pool's `transferFrom(msg.sender, self, amt)` into USDC over FiatTokenV2_1 succeeds** at
`U ≥ 113000`. -/
theorem usdcV2_1_coinPullOkAt (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr)
    (hne : t.toAdr ≠ sevm.currentTarget) (hU : 113000 ≤ U)
    (hii : ii.toNat + 0x64 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr ImplV2_1.code ∧
      ImplV2.PullFits (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
    (hW' : ∀ b d, W b → CoinLeaves t.toAdr
        (ImplV2.fromStor (b.getStor t.toAdr) sevm.caller sevm.currentTarget sevm.currentTarget amt)
      ((getOrigAcct sevm t.toAdr).stor = b.getStor t.toAdr ∧ t.toAdr ∉ b.createdAccounts ∧
        ImplV2.allowSlot sevm.caller sevm.currentTarget ≠ ImplV2.balSlot sevm.caller ∧
        ImplV2.allowSlot sevm.caller sevm.currentTarget ≠ ImplV2.balSlot sevm.currentTarget ∧
        ImplV2.balSlot sevm.caller ≠ ImplV2.balSlot sevm.currentTarget) b d → W' d) :
    CoinPullOkAt sevm W W' t amt U ii oi :=
  usdc_coinPullOkAt @pullLaw (by omega) hfork hstatic hdepth hprec hne (by omega) hii hoi hW hW'

/-- **The pool's `balanceOf(self)` into USDC over FiatTokenV2_1 answers the entry** at `U ≥ 70000`. -/
theorem usdcV2_1_coinBalOkAt {B : B256} (hfork : CoveredFork sevm.benvStat.fork) (hdepth : 2 ≤ sevm.depth)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) (hU : 70000 ≤ U)
    (hii : ii.toNat + 0x24 ≤ 4096) (hoi : oi.toNat + 32 ≤ 4096)
    (hW : ∀ b, W b → b.getCode t.toAdr = Proxy.code ∧ ProxyAt sevm b t.toAdr ImplV2_1.code ∧
      (b.getStor t.toAdr).get (ImplV2.balSlot sevm.currentTarget) = B)
    (hW' : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → W' d) :
    CoinBalOkAt sevm W W' t B U ii oi :=
  usdc_coinBalOkAt @balLaw (by omega) (by omega) (by omega) hfork hdepth hprec hU hii hoi hW hW'

end Premises

end Blanc.Composition.Curve3PoolUsdcV2_1
