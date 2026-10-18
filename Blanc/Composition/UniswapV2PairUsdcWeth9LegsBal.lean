import Blanc.Composition.UniswapV2PairUsdcWeth9LegsImpl

/-!
# The USDC implementation's `balanceOf` frame, forward (U9a)
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Impl

local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
local notation "l255" => Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- **Entry 46, `balanceOf`'s body**: `_balanceOf(a)`. -/
@[irreducible] noncomputable def e46W (sevm : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) (n : Nat) :
    {c : Nat // CoveredFork sevm.benvStat.fork →
      FpM (Bytes.toB256 [128]) n M → S.length < 990 → ∀ X,
      SFunc.RunExact cert.prog sevm (St b (a :: ret :: S) M (X + c)) t_2adf_c46
        (.returned (St (afterSload sevm b (mapSlot (m20 &&& a) (Bytes.toB256 [9])))
          ((l255 &&& b.getStorVal sevm.currentTarget (mapSlot (m20 &&& a) (Bytes.toB256 [9]))) :: S)
          (sc9 M (m20 &&& a)) X))} :=
  ⟨_, fun fork hM room X => by
    xrun
    xcallM e96W 2 [_] fork hM (by xroom)
    xrun⟩

/-- The `balanceOf` argument as the wrapper and `_balanceOf` mask it. -/
abbrev bTo (sevm : Sevm) : B256 := m20 &&& (m20 &&& Sevm.dataWord sevm (Bytes.toB256 [4]))

/-- The balance slot `balanceOf` reads. -/
abbrev bKey (sevm : Sevm) : B256 := mapSlot (bTo sevm) (Bytes.toB256 [9])

/-- The word `balanceOf` returns: the packed word's low 255 bits. -/
abbrev bWord (sevm : Sevm) (b : Devm) : B256 := l255 &&& b.getStorVal sevm.currentTarget (bKey sevm)

/-- The memory at `balanceOf`'s `RETURN`. -/
abbrev implBalMem (sevm : Sevm) (b : Devm) : Mem :=
  (sc9 (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes) (bTo sevm)).write 128 (bWord sevm b).toBytes

/-- The implementation frame's halting state after `balanceOf`, with `G` gas left. -/
def implBalPost (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  ((St (afterSload sevm b (bKey sevm)) [Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [224]).toNat]
    (implBalMem sevm b) G).memRead (Bytes.toB256 [128]).toNat
      (Bytes.toB256 [32] + (Bytes.toB256 [128] - Bytes.toB256 [128])).toNat).2.withOutput (bWord sevm b).toBytes

/-- The `balanceOf` frame's branch facts in the forms its walk meets them. -/
structure BalFacts (sevm : Sevm) : Prop where
  value : sevm.value = 0
  short : (Nat.toB256 sevm.data.length <? Bytes.toB256 [4]) = 0
  args : ((Nat.toB256 sevm.data.length - Bytes.toB256 [4]) <? Bytes.toB256 [32]) = 0
  sel : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [224]).toNat = 0x70a08231

/-- **The implementation frame of `balanceOf(a)`, forward**: from a fresh frame, the whole run to
`RETURN`, its charge `c` synthesized by the walk. -/
@[irreducible] noncomputable def implBalW (sevm : Sevm) (b : Devm) :
    {c : Nat // CoveredFork sevm.benvStat.fork → BalFacts sevm → ∀ G,
      SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + c)) t_0000_c0
        (.halted (implBalPost sevm b G))} :=
  ⟨_, fun fork facts G => by
    obtain ⟨value, short, args, sel⟩ := facts
    xrun
    xcallM e46W 2 [_] fork (by xfp) (by xroom)
    xrun
    xunfold
    refine rk0 ?_
    apply rx_returnP
    · with_reducible rfl
    · xfp
    · xfp
    · decide
    · decide⟩

theorem e46W_gas (s : Sevm) (b : Devm) (a ret : B256) (S : List B256) (M : Mem) (n f : Nat) :
    (e46W { s with gas := f } b a ret S M n).1 = (e46W s b a ret S M n).1 := by
  unfold e46W; simp only [e96W_gas]

theorem implBalW_gas (s : Sevm) (b : Devm) (f : Nat) :
    (implBalW { s with gas := f } b).1 = (implBalW s b).1 := by
  unfold implBalW
  simp only [e46W_gas, UniswapV2PairWeth9Joint.dataWord_gasField]

end Blanc.Composition.UsdcLive
