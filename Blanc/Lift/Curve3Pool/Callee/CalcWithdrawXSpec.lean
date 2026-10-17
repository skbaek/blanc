import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXD
import Blanc.Lift.Curve3Pool.Walk.ViewsDyKit

/-!
# `_calc_withdraw_one_coin` on the derivation: the composed walk and the model

`xa_cw` composes the segments of `CalcWithdrawX*.lean`: entered at `0x3cca` with the return
address, `_token_amount` and `i` on the stack, the frame's next child is the `totalSupply()`
`STATICCALL` and the function returns to the caller with `(dy, dy_fee)` on the stack, where
`calcWithdrawOne` computes exactly `(dy, dy_fee)` in every environment whose time is the
frame's and whose supply is the reply. The first `get_y_D` call is exposed with its actual
stack arguments (`amp`, `i`, `xp`, `D1`) and the model's checked prefix producing them.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The model's `k = i` from the counter word's. -/
theorem cw_eq_iff {i w : B256} {k : Fin 3} (hi : i.toNat < 3) (hw : w.toNat = k.val) :
    (k = ⟨i.toNat, hi⟩) ↔ (w = i) := by
  constructor
  · intro h
    apply B256.toNat_inj
    rw [hw, h]
  · intro h
    apply Fin.ext
    rw [← hw, h]

theorem cw_feeDen : cwFeeDen.toNat = feeDen := by decide

theorem cw_precMul_toNat {n : Nat} (hn : n < 3) :
    (pickWord3 n cwP1 cwPm cwPm).toNat = precMul.get ⟨n, hn⟩ :=
  dy_pickWord3_toNat hn cwP1 cwPm cwPm

/-- A monadic `bind` on `some`, as the model's `do` blocks elaborate. -/
theorem cw_some_bind {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

set_option hygiene false in
/-- One `bind` on a `some`, in either elaborated form. -/
local macro "bstep" : tactic => `(tactic| first | rw [Option.bind_some] | rw [cw_some_bind])

theorem cw_ofFnM_some {f : Fin 3 → Option Nat} {a b c : Nat} (h0 : f 0 = some a)
    (h1 : f 1 = some b) (h2 : f 2 = some c) : V3.ofFnM f = some ⟨a, b, c⟩ := by
  unfold V3.ofFnM
  rw [h0]
  bstep
  rw [h1]
  bstep
  rw [h2]
  bstep

/-- One fee-loop step, as the model computes it. -/
theorem cwStep_chk {P eqk : Prop} [Decidable P] (hP : P ↔ eqk) {xk D1 D0 y F r' : B256}
    (hs : CwStep eqk xk D1 D0 y F xk r') :
    (do
      let scaled ← chkDiv (← chkMul xk.toNat D1.toNat) D0.toNat
      let dxExp ← if P then chkSub scaled y.toNat else chkSub xk.toNat scaled
      chkSub xk.toNat (← chkDiv (← chkMul F.toNat dxExp) feeDen)) = some r'.toNat := by
  obtain ⟨hm, hd, dx, hbr, hm2, hs2, rfl⟩ := hs
  simp only [Option.bind_eq_bind]
  rw [chkMul_toNat_of_nofm hm, Option.bind_some, chkDiv_toNat_of_ne hd, Option.bind_some]
  rcases hbr with ⟨he, hle, rfl⟩ | ⟨hne, hle, rfl⟩
  · rw [ite_eq_left (hP.mpr he), chkSub_toNat_of_le hle, Option.bind_some,
      chkMul_toNat_of_nofm hm2, Option.bind_some, ← cw_feeDen, chkDiv_toNat_of_ne (by decide),
      Option.bind_some, chkSub_toNat_of_le hs2]
  · rw [ite_eq_right (fun h => hne (hP.mp h)), chkSub_toNat_of_le hle, Option.bind_some,
      chkMul_toNat_of_nofm hm2, Option.bind_some, ← cw_feeDen, chkDiv_toNat_of_ne (by decide),
      Option.bind_some, chkSub_toNat_of_le hs2]

/-- **The model's `_calc_withdraw_one_coin`** from the walk's checked words. -/
theorem calcWithdrawOne_eq {s : State} {e : Env} {a iw A F T x0 x1 x2 D0 y r0 r1 r2 y2 : B256}
    (hi : iw.toNat < 3)
    (hamp : aChk s e.time = some A.toNat) (hfee : feeAdj s = some F.toNat)
    (hT : e.supply = some T.toNat) (hxp : xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hD0 : getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get A.toNat 1 = some D0.toNat)
    (hm : B256.Nofm a D0) (hT0 : T ≠ 0) (hle : (a * D0 / T).toNat ≤ D0.toNat)
    (hy : getYDChk A.toNat ⟨iw.toNat, hi⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
      (D0 - a * D0 / T).toNat = some y.toNat)
    (hyl : y.toNat ≤ (pickWord3 iw.toNat x0 x1 x2).toNat)
    (hp : pickWord3 iw.toNat cwP1 cwPm cwPm ≠ 0)
    (h0 : CwStep (Bytes.toB256 [0] = iw) x0 (D0 - a * D0 / T) D0 y F x0 r0)
    (h1 : CwStep (Bytes.toB256 [1] = iw) x1 (D0 - a * D0 / T) D0 y F x1 r1)
    (h2 : CwStep (Bytes.toB256 [2] = iw) x2 (D0 - a * D0 / T) D0 y F x2 r2)
    (hy2 : getYDChk A.toNat ⟨iw.toNat, hi⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
      (D0 - a * D0 / T).toNat = some y2.toNat)
    (hs0 : y2.toNat ≤ (pickWord3 iw.toNat r0 r1 r2).toNat)
    (hs1 : (Bytes.toB256 [1]).toNat ≤ (pickWord3 iw.toNat r0 r1 r2 - y2).toNat)
    (hs2 : (cwDy iw r0 r1 r2 y2).toNat ≤
      ((pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm).toNat) :
    calcWithdrawOne s e a.toNat ⟨iw.toNat, hi⟩ =
      some ((cwDy iw r0 r1 r2 y2).toNat,
        ((pickWord3 iw.toNat x0 x1 x2 - y) / pickWord3 iw.toNat cwP1 cwPm cwPm -
          cwDy iw r0 r1 r2 y2).toNat) := by
  unfold calcWithdrawOne
  rw [hamp]
  bstep
  rw [hfee]
  bstep
  rw [hT]
  bstep
  rw [hxp]
  bstep
  rw [hD0]
  bstep
  rw [chkMul_toNat_of_nofm hm]
  bstep
  rw [chkDiv_toNat_of_ne hT0]
  bstep
  rw [chkSub_toNat_of_le hle]
  bstep
  rw [hy]
  bstep
  rw [← dy_pickWord3_toNat hi x0 x1 x2, chkSub_toNat_of_le hyl]
  bstep
  rw [← cw_precMul_toNat hi, chkDiv_toNat_of_ne hp]
  bstep
  rw [cw_ofFnM_some (a := r0.toNat) (b := r1.toNat) (c := r2.toNat)
    (cwStep_chk (cw_eq_iff hi (by decide)) h0) (cwStep_chk (cw_eq_iff hi (by decide)) h1)
    (cwStep_chk (cw_eq_iff hi (by decide)) h2)]
  bstep
  rw [hy2]
  bstep
  rw [← dy_pickWord3_toNat hi r0 r1 r2, chkSub_toNat_of_le hs0]
  bstep
  rw [show (1 : Nat) = (Bytes.toB256 [1]).toNat from rfl, chkSub_toNat_of_le hs1]
  bstep
  rw [chkDiv_toNat_of_ne hp]
  bstep
  rw [chkSub_toNat_of_le hs2]
  bstep

section

variable {sevm : Sevm} {post b : Devm} {ρ : B256} {S : List B256} {M : Mem} {G : Nat}
  {L : List Exec.Frame} {s : State}

/-- **`_calc_withdraw_one_coin` on the derivation.** Entered at `0x3cca` with the return
address `ρ`, `_token_amount` `a` and `i` above `S` (carrier memory, storage abstracting `s`, the
token not a precompile): the frame's next child `c` is the static `totalSupply()` call at the
token; the function returns to `ρ` with `(dy, dy_fee)` above `S`, storage and logs unchanged,
and `calcWithdrawOne` computes `(dy, dy_fee)` in every environment with the frame's time and
the reply as supply. The first `get_y_D` call is exposed with its actual stack arguments
`(amp, i, xp, D1)` at `0x3999` and the model's checked prefix that produces them. -/
theorem xa_cw (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {a i : B256}
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hV : VW M [])
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (h : XAt sevm post 0x3cca (St b (ρ :: a :: i :: S) M G) L) :
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (hi : i.toNat < 3) (dy fee : B256) (b' : Devm)
      (M' : Mem) (G' : Nat), L = c :: L' ∧
      StaticWordChild ((b.getStor sevm.currentTarget).get tokenSlot).toAdr totalSupplyData c ∧
      (∀ e : Env, e.time = sevm.benvStat.time.toNat → e.supply = some (vSupply c).toNat →
        calcWithdrawOne s e a.toNat ⟨i.toNat, hi⟩ = some (dy.toNat, fee.toNat)) ∧
      (∃ (A x0 x1 x2 D0 D1 y ρ' : B256) (R : List B256) (b0 : Devm) (M0 : Mem) (G0 : Nat),
        aChk s sevm.benvStat.time.toNat = some A.toNat ∧
        xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
        getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get A.toNat 1 = some D0.toNat ∧
        ((chkMul a.toNat D0.toNat).bind fun m => (chkDiv m (vSupply c).toNat).bind fun q =>
          chkSub D0.toNat q) = some D1.toNat ∧
        XAt sevm post 0x3999 (St b0 (ρ' :: A :: i :: x0 :: x1 :: x2 :: D1 :: R) M0 G0) L' ∧
        getYDChk A.toNat ⟨i.toNat, hi⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get D1.toNat =
          some y.toNat) ∧
      (∀ x, b'.getStor x = b.getStor x) ∧ b'.logs = b.logs ∧
      XAt sevm post ρ.toNat (St b' (dy :: fee :: S) M' G') L' ∧ VW M' [] := by
  obtain ⟨A, F, c, d, M1, G1, L1, hL, hsw, hamp, hfee, hdst, hdlg, h, hV⟩ :=
    xa_cw_a hc hcode hfork ha hV htok h
  have had : Abstracts (d.getStor sevm.currentTarget) s := by rw [hdst]; exact ha
  obtain ⟨x0, x1, x2, D0, b1, M2, G2, hb1, hxp, hD0, hm, hT0, hle, h, hV⟩ :=
    xa_cw_b hc hcode hfork had hV h
  obtain ⟨y, hi, M3, G3, hcall, hy, hyl, hp, h, hV⟩ := xa_cw_c hc hcode hfork hV h
  obtain ⟨r0, M4, G4, h0, h, hV⟩ := xa_cw_it0 hcode rfl hV h
  obtain ⟨r1, M5, G5, h1, h, hV⟩ := xa_cw_it1 hcode (by decide) hV h
  obtain ⟨r2, M6, G6, h2, h, hV⟩ := xa_cw_it2 hcode (by decide) hV h
  obtain ⟨y2, M7, G7, hy2, hs0, hs1, hp', hs2, h, hV⟩ := xa_cw_d hc hcode hfork hi hV h
  obtain ⟨ρ', R, M0, G0, hcall⟩ := hcall
  refine ⟨c, L1, hi, _, _, b1, M7, G7, hL, hsw, fun e ht hT => ?_, ⟨A, x0, x1, x2, D0, _, y, ρ',
    R, b1, M0, G0, hamp, hxp, hD0, ?_, hcall, hy⟩, fun x => by rw [hb1.getStor, hdst],
    by rw [hb1.logs, hdlg], h, hV⟩
  · rw [← ht] at hamp
    exact calcWithdrawOne_eq hi hamp hfee hT hxp hD0 hm hT0 hle hy hyl hp h0 h1 h2 hy2 hs0 hs1 hs2
  · rw [chkMul_toNat_of_nofm hm, Option.bind_some, chkDiv_toNat_of_ne hT0, Option.bind_some,
      chkSub_toNat_of_le hle]

end

end Blanc.Lift.Curve3Pool
