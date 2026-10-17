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

/-- The packed-balance key of `a` as the walks compute it (`mapping(address => uint256)` at slot 9),
in its two operand orders. -/
abbrev ky (a : B256) : B256 := mapSlot (m20 &&& a) (Bytes.toB256 [9])
abbrev ky' (a : B256) : B256 := mapSlot (a &&& m20) (Bytes.toB256 [9])

/-- The ERC-20 `Transfer` event topic. -/
abbrev transferTopic : B256 := Bytes.toB256 [221, 242, 82, 173, 27, 226, 200, 155, 105, 194, 176, 104,
  252, 55, 141, 170, 149, 43, 167, 241, 99, 196, 161, 22, 40, 245, 90, 77, 245, 35, 179, 239]

/-- The base after `_transfer(z, y, x)` debits `z` (its reads and the debit store). -/
def e93Debited (sevm : Sevm) (b : Devm) (x z : B256) : Devm :=
  afterSstore sevm (afterSload sevm (afterSload sevm (afterSload sevm b (ky z)) (ky z)) (ky z)) (ky' z)
    ((l255 &&& (afterSload sevm b (ky z)).getStorVal sevm.currentTarget (ky z)) - x)

/-- The base `_transfer(z, y, x)` returns with: the credit store and the `Transfer` log. -/
def e93Post (sevm : Sevm) (b : Devm) (x y z : B256) : Devm :=
  (afterSstore sevm (afterSload sevm (afterSload sevm (e93Debited sevm b x z) (ky y)) (ky y)) (ky' y)
    (x + (l255 &&& (e93Debited sevm b x z).getStorVal sevm.currentTarget (ky y)))).addLog
    { address := sevm.currentTarget, topics := [transferTopic, m20 &&& z, m20 &&& y], data := x.toBytes }

/-- The memory `_transfer` returns with. -/
abbrev e93Mem (M : Mem) (x y z : B256) : Mem :=
  (sc9 (sc9 (sc9 (sc9 (sc9 (sc9 (sc9 M (m20 &&& z)) (m20 &&& z)) (m20 &&& z)) (z &&& m20)) (m20 &&& y))
    (m20 &&& y)) (y &&& m20)).write 128 x.toBytes

@[irreducible] noncomputable def e93W (sevm : Sevm) (b : Devm) (x y z ret : B256) (S : List B256) (M : Mem)
    :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
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
      SFunc.RunExact cert.prog sevm (St b (x :: y :: z :: ret :: S) M (X + c)) t_3f98_c93
        (.returned (St (e93Post sevm b x y z) S (e93Mem M x y z) X))} :=
  ⟨_, fun fork static hM room hz hy hfz hle hcr hfy X hX => by
    have hx255 : x.toNat ≤ 2 ^ 255 - 1 := Nat.le_trans (toNat_le_of_gtCheck_eq_zero hle) (l255_and_le _)
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

/-- The caller's balance key, the destination's, and the debited storage the credit reads. -/
abbrev kC (sevm : Sevm) : B256 := mapSlot sevm.caller.toB256 (Bytes.toB256 [9])
abbrev kT (y : B256) : B256 := mapSlot y.toAdr.toB256 (Bytes.toB256 [9])

/-- The base after `transfer`'s modifiers read `paused` and both blacklist flags. -/
abbrev e37Pre (sevm : Sevm) (b : Devm) (y : B256) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [1])) (ky sevm.caller.toB256)) (ky y)

@[irreducible] noncomputable def e37W (sevm : Sevm) (b : Devm) (x y ret : B256) (S : List B256)
    (M : Mem) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false →
      FpM (Bytes.toB256 [128]) 96 M → S.length < 970 →
      (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [1]) /
        Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = 0 →
      B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget (kC sevm) >>>
        (Bytes.toB256 [255]).toNat) = 0 →
      B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget (kT y) >>>
        (Bytes.toB256 [255]).toNat) = 0 →
      sevm.caller.toB256 ≠ 0 → y.toAdr.toB256 ≠ 0 →
      B256.gtCheck x (l255 &&& b.getStorVal sevm.currentTarget (kC sevm)) = 0 →
      x.toNat + (l255 &&& ((Devm.getStor b sevm.currentTarget).set (kC sevm)
        ((l255 &&& b.getStorVal sevm.currentTarget (kC sevm)) - x)).get (kT y)).toNat ≤ 2 ^ 255 - 1 →
      B256.eqCheck (Bytes.toB256 [1]) (((Devm.getStor b sevm.currentTarget).set (kC sevm)
        ((l255 &&& b.getStorVal sevm.currentTarget (kC sevm)) - x)).get (kT y) >>>
          (Bytes.toB256 [255]).toNat) = 0 →
      ∀ X, 415 ≤ X →
      SFunc.RunExact cert.prog sevm (St b (x :: y :: ret :: S) M (X + c)) t_2fa6_c37
        (.returned (St (e93Post sevm (e37Pre sevm b y) x y sevm.caller.toB256) (Bytes.toB256 [1] :: S)
          (e93Mem (sc9 (sc9 M (m20 &&& sevm.caller.toB256)) (m20 &&& y)) x y sevm.caller.toB256) X))} :=
  ⟨_, fun fork static hM room hp hfc hft hz hy hle hcr hfy X hX => by
    xrun
    xcallM e83W 2 [_] fork (by xfp) (by xroom)
    xrun
    xcallM e83W 2 [_] fork (by xfp) (by xroom)
    xrun
    xcallMT e93W 4 [] fork static (by xfp) (by xroom) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption) (by xnorm; with_reducible assumption)
      (by xnorm; with_reducible assumption)
    xrun
    all_goals ((try unfold gCallStipend); omega)
  ⟩

/-- The `transfer` arguments as the ABI wrapper decodes them. -/
abbrev xTo (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [4]) &&& m20
abbrev xVal (sevm : Sevm) : B256 := Sevm.dataWord sevm (Bytes.toB256 [32] + Bytes.toB256 [4])

/-- The `transfer` frame's branch facts in the forms its walk meets them. -/
structure XferFacts (sevm : Sevm) (b : Devm) : Prop where
  value : sevm.value = 0
  short : (Nat.toB256 sevm.data.length <? Bytes.toB256 [4]) = 0
  args : ((Nat.toB256 sevm.data.length - Bytes.toB256 [4]) <? Bytes.toB256 [64]) = 0
  sel : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [224]).toNat = 0xa9059cbb
  paused : (Bytes.toB256 [255] &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [1]) /
    Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = 0
  fc : B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget (kC sevm) >>>
    (Bytes.toB256 [255]).toNat) = 0
  ft : B256.eqCheck (Bytes.toB256 [1]) (b.getStorVal sevm.currentTarget (kT (xTo sevm)) >>>
    (Bytes.toB256 [255]).toNat) = 0
  hz : sevm.caller.toB256 ≠ 0
  hy : (xTo sevm).toAdr.toB256 ≠ 0
  hle : B256.gtCheck (xVal sevm) (l255 &&& b.getStorVal sevm.currentTarget (kC sevm)) = 0
  hcr : (xVal sevm).toNat + (l255 &&& ((Devm.getStor b sevm.currentTarget).set (kC sevm)
    ((l255 &&& b.getStorVal sevm.currentTarget (kC sevm)) - xVal sevm)).get (kT (xTo sevm))).toNat ≤
      2 ^ 255 - 1
  hfy : B256.eqCheck (Bytes.toB256 [1]) (((Devm.getStor b sevm.currentTarget).set (kC sevm)
    ((l255 &&& b.getStorVal sevm.currentTarget (kC sevm)) - xVal sevm)).get (kT (xTo sevm)) >>>
      (Bytes.toB256 [255]).toNat) = 0

/-- The implementation frame's memory at `transfer`'s `RETURN`. -/
abbrev implXferMem (sevm : Sevm) : Mem :=
  (e93Mem (sc9 (sc9 (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes) (m20 &&& sevm.caller.toB256))
    (m20 &&& xTo sevm)) (xVal sevm) (xTo sevm) sevm.caller.toB256).write 128
    (B256.eqCheck (B256.eqCheck (Bytes.toB256 [1]) 0) 0).toBytes

/-- The implementation frame's halting state after `transfer`, with `G` gas left. -/
def implXferPost (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  ((St (e93Post sevm (e37Pre sevm b (xTo sevm)) (xVal sevm) (xTo sevm) sevm.caller.toB256)
    [Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [224]).toNat] (implXferMem sevm) G).memRead
      (Bytes.toB256 [128]).toNat (Bytes.toB256 [32] + (Bytes.toB256 [128] - Bytes.toB256 [128])).toNat).2.withOutput
    (B256.eqCheck (B256.eqCheck (Bytes.toB256 [1]) 0) 0).toBytes

/-- **The implementation frame of `transfer(to, value)`, forward**: from a fresh frame, the whole run
to `RETURN`, its charge `c` synthesized by the walk. -/
@[irreducible] noncomputable def implXferW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → sevm.isStatic = false → XferFacts sevm b → ∀ G, 415 ≤ G →
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (implXferPost sevm b G))} :=
  ⟨_, fun fork static facts G hG => by
    obtain ⟨value, short, args, sel, hp, hfc, hft, hz, hy, hle, hcr, hfy⟩ := facts
    xrun
    xcallMT e37W 3 [] fork static (by xfp) (by xroom) hp hfc hft hz hy hle hcr hfy
    xrun
    xunfold
    refine rk0 ?_
    apply rx_returnP
    · with_reducible rfl
    · xfp
    · xfp
    · decide
    · decide
    all_goals ((try unfold gCallStipend); omega)
  ⟩

end Blanc.Composition.UsdcLive
