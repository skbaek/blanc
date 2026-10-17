import Blanc.Composition.UniswapV2PairUsdcWeth9LegsKit
import Blanc.Lift.Usdc.RefineTransfer

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Impl

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
local notation "l255" => Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The scratch image of one mapping-slot hash of `k` at base slot `9`. -/
abbrev sc9 (M : Mem) (k : B256) : Mem := (M.write 0 k.toBytes).write 32 (Bytes.toB256 [9]).toBytes

theorem prog99 : cert.prog[99]? = some t_4430_c99 := rfl

theorem l255_and_toNat (w : B256) : (l255 &&& w).toNat = balanceBits w := by
  rw [litMask255]; exact low255_and_toNat w

theorem l255_and_le (w : B256) : (l255 &&& w).toNat ≤ 2 ^ 255 - 1 := by
  rw [l255_and_toNat]; unfold balanceBits; omega

theorem sub_l255_le {w x : B256} (h : x.toNat ≤ (l255 &&& w).toNat) :
    ((l255 &&& w) - x).toNat ≤ 2 ^ 255 - 1 := by
  rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr h)]
  have := l255_and_le w
  omega

theorem add_l255_lt {x : B256} (hx : x.toNat ≤ 2 ^ 255 - 1) (w : B256) :
    x.toNat + (l255 &&& w).toNat < 2 ^ 256 := by
  have := l255_and_le w
  omega

theorem add_l255_toNat_le {x w : B256} (hx : x.toNat ≤ 2 ^ 255 - 1)
    (h : x.toNat + (l255 &&& w).toNat ≤ 2 ^ 255 - 1) : (x + (l255 &&& w)).toNat ≤ 2 ^ 255 - 1 := by
  rw [B256.toNat_add_eq_of_nof _ _ (add_l255_lt hx w)]
  exact h

/-- **Entry 83, `_isBlacklisted(a)`**, forward: reads `a`'s packed word, returns its top-bit test. -/
@[irreducible] noncomputable def e83W (sevm : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) (n : Nat) :
    {c : Nat // CoveredFork sevm.benvStat.fork →
      FpM (Bytes.toB256 [128]) n M → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (a :: ret :: S) M (X + c)) t_3f6a_c83
        (.returned (St (afterSload sevm b (mapSlot (m20 &&& a) (Bytes.toB256 [9])))
          (B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget
            (mapSlot (m20 &&& a) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) :: S)
          (sc9 M (m20 &&& a)) X))} :=
  ⟨_, fun fork hM room X => by
    have := hM.ge
    xrun
  ⟩

/-- **Entry 96, `_balanceOf(a)`**, forward: the low 255 bits of `a`'s packed word. -/
@[irreducible] noncomputable def e96W (sevm : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) (n : Nat) :
    {c : Nat // CoveredFork sevm.benvStat.fork →
      FpM (Bytes.toB256 [128]) n M → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (a :: ret :: S) M (X + c)) t_41da_c96
        (.returned (St (afterSload sevm b (mapSlot (m20 &&& a) (Bytes.toB256 [9])))
          ((l255 &&& b.getStorVal sevm.currentTarget (mapSlot (m20 &&& a) (Bytes.toB256 [9]))) :: S)
          (sc9 M (m20 &&& a)) X))} :=
  ⟨_, fun fork hM room X => by
    have := hM.ge
    xrun
  ⟩

/-- **Entry 100, SafeMath `sub(y, x)`**, forward. -/
@[irreducible] noncomputable def e100W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // x.toNat ≤ y.toNat → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_4163_c100
        (.returned (St b ((y - x) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have := gtCheck_zero_of_toNat_le hle
    xrun
  ⟩

/-- **Entry 98, SafeMath `add(x, y)`**, forward. -/
@[irreducible] noncomputable def e98W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) :
    {c : Nat // x.toNat + y.toNat < 2 ^ 256 → S.length < 1000 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_43b5_c98
        (.returned (St b ((x + y) :: S) M X))} :=
  ⟨_, fun hle room X => by
    have := ltCheck_add_zero hle
    xrun
  ⟩

/-- **Entry 99, `_setBalance(y, x)`**, forward: the packed word of `y` set to `x`. -/
@[irreducible] noncomputable def e99W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256) (M : Mem) (n : Nat) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) n M → S.length < 990 → x.toNat ≤ 2 ^ 255 - 1 →
      B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget
        (mapSlot y.toAdr.toB256 (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) = 0 → ∀ X,
      2293 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_4430_c99
        (.returned (St (afterSstore sevm (afterSload sevm b (mapSlot (m20 &&& y) (Bytes.toB256 [9])))
            (mapSlot (y &&& m20) (Bytes.toB256 [9])) x) S
          (sc9 (sc9 M (m20 &&& y)) (y &&& m20)) X))} :=
  ⟨_, fun fork static hM room hx hfz X hX => by
    have := hM.ge
    have hx' := gtCheck_zero_of_toNat_le (x := x) (y := l255) (by rw [litMask255, toNat_low255]; exact hx)
    xrun
    xcallM e83W 2 [_] fork (by xfp) (by xroom)
    xrun
    all_goals ((try unfold gCallStipend); omega)
  ⟩

@[irreducible] noncomputable def e93W (sevm : Sevm) (b : Devm) (x y z ret : B256) (S : List B256) (M : Mem)
    :
    {p : Nat × Devm × List B256 × Mem // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 980 → z.toAdr.toB256 ≠ 0 → y.toAdr.toB256 ≠ 0 →
      B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget
        (mapSlot z.toAdr.toB256 (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) = 0 →
      B256.gtCheck x (Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff] &&& b.getStorVal sevm.currentTarget
          (mapSlot z.toAdr.toB256 (Bytes.toB256 [9]))) = 0 →
      x.toNat + (l255 &&& ((Devm.getStor b sevm.currentTarget).set
        (mapSlot z.toAdr.toB256 (Bytes.toB256 [9]))
        ((l255 &&& b.getStorVal sevm.currentTarget (mapSlot z.toAdr.toB256 (Bytes.toB256 [9]))) - x)).get
          (mapSlot y.toAdr.toB256 (Bytes.toB256 [9]))).toNat ≤ 2 ^ 255 - 1 →
      B256.eqCheck (Bytes.toB256 [1]) (((Devm.getStor b sevm.currentTarget).set
        (mapSlot z.toAdr.toB256 (Bytes.toB256 [9]))
        ((l255 &&& b.getStorVal sevm.currentTarget (mapSlot z.toAdr.toB256 (Bytes.toB256 [9]))) - x)).get
          (mapSlot y.toAdr.toB256 (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) = 0 →
      ∀ X, 443 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (x :: y :: z :: ret :: S) M (X + p.1)) t_3f98_c93
        (.returned (St p.2.1 p.2.2.1 p.2.2.2 X))} :=
  ⟨(_, _, _, _), fun fork static hM room hz hy hfz hle hcr hfy X hX => by
    have hx255 : x.toNat ≤ 2 ^ 255 - 1 := Nat.le_trans (toNat_le_of_gtCheck_eq_zero hle) (l255_and_le _)
    dsimp only
    xrun
    xcallM e96W 2 [_] fork (by xfp) (by xroom)
    xrun
    xcallM e96W 2 [_] fork (by xfp) (by xroom)
    xrun
    xcallM e100W 3 [] (by xle) (by xroom)
    xrun
    xcallMT e99W 3 [_] fork static (by xfp) (by xroom) (sub_l255_le (by xle)) (by xnorm; with_reducible assumption)
    xrun
    xcallM e96W 2 [_] fork (by xfp) (by xroom)
    xrun
    xcallM e98W 3 [] (add_l255_lt hx255 _) (by xroom)
    xrun
    xcallMT e99W 3 [_] fork static (by xfp) (by xroom) (add_l255_toNat_le hx255 (by xnorm; with_reducible assumption))
      (by xnorm; with_reducible assumption)
    xrun
    all_goals ((try unfold gCallStipend); omega)
  ⟩

end Blanc.Composition.UsdcLive
