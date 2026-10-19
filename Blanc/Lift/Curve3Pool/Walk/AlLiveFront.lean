import Blanc.Lift.Curve3Pool.Walk.RliLiveFront
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityPre
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactKit

/-!
# `add_liquidity`, forward: the dispatcher, the guards, `_A`, the supply and the balances

`rx_dispatch_al`: with the `add_liquidity` selector the frame's entry tree runs to the arm's body
`t_0e55_c0`. `rx_al_pre` (`t_0e55_c0` → the supply test): the lock, no value, the pool alive,
`fees` zeroed at `0x140 … 0x180`, the adjusted fee `fee · 3 / 8` (checked) at `0x1a0`,
`admin_fee` at `0x1c0`, `_A` (`a_exact`) at `0x1e0`, 3Crv's `totalSupply()` (`SupplyOkAt`,
window `0x27c`/`0x2c0`) at `0x240`, `D0 = 0` at `0x2e0` and the balances at `0x300 … 0x340`; then
the supply test: `T = 0` runs on at `t_1031_c4`, `T ≠ 0` at `t_0f8f_c0` (`D0`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **The dispatcher, forward** (`add_liquidity`). -/
theorem rx_dispatch_al {sevm : Sevm} {b : Devm} {G : Nat} {Q : Outcome → Prop}
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity)
    (k : SFunc.RunEx cert.prog sevm (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G)
      t_0e55_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [] Mem.empty (G + 315)) t_0000_c0 Q := by
  have hR0 := vyMem_reads Mem.wf_empty Mem.reads_empty (Sevm.dataWord sevm 0)
  have hsz0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hX : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD 0 32 0) = 0x4515cef3 := by
    rw [vyImg_selector]; exact hsel
  have hlen4 : B256.eqCheck (B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [0x04]))
      0 ≠ 0 := by
    rw [ltCheck_eq_zero_of_le (by rw [B256.toNat_toB256_of_lt hcd]; exact hlen)]; decide
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldatasize (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ hlen4 ·)
  xr (rx_dest ·)
  xr (rx_vyPrologue (by simp only [List.length_nil]; omega) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hX]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0) hR0 hsz0 rfl (by decide) (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_zero' (by rw [hX]; decide) ·)
  exact k

set_option hygiene false in
/-- `wsimp` over the goal and the memory carriers `hR`, `hW`, `hsz` alike, so a literal memory
term holding a loaded word stays one term in all four. -/
macro "wsimpA" : tactic => `(tactic| simp (disch := first | decide | (simp only
    [B256.length_toBytes, List.length_take, List.length_sliceD, List.length_cons, List.length_nil,
      List.length_append, transferFromSel, transferSel, burnFromSel, mintSel, balanceOfSel]; omega))
  only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self,
    Bytes.sliceD_writeAt_before, Bytes.sliceD_writeAt_after] at hR hW hsz ⊢)

theorem al_prog_27 : cert.prog[27]? = some t_00a9_c27 := prog_27

/-- The supply test falls through on a positive supply. -/
theorem al_supply_test {T : B256} (hT : T ≠ 0) :
    B256.eqCheck (B256.gtCheck T (Bytes.toB256 [0])) 0 = 0 := by
  have hgt : B256.gtCheck T (Bytes.toB256 [0]) ≠ 0 := by
    apply gtCheck_ne_zero_of_lt
    rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0]).toNat = 0 by decide]
    exact Nat.pos_of_ne_zero fun h => hT (B256.toNat_inj _ _ (by rw [h]; rfl))
  by_contra h
  exact hgt (eqCheck_ne_zero_eq h)

/-! ## `add_liquidity`'s prologue, exact

The canonical data of the prologue as the stage core `rx_al_preE` reports it: the base `_A` runs
from (`alPreBaseA`, after the lock read and set and the `is_killed`, `fee`, `admin_fee` reads),
the `totalSupply()` call's base and literal input memory (`alSupBase`, `alSupMem`), the charges
before and after the call (`alPreCost1`, `alPreCost2`), and the base and memory at the supply
test (`alPreBase2`, `alPreMem2`). -/

/-- The base `_A` runs from: the lock read and set, `is_killed`, `fee` and `admin_fee` read. -/
def alPreBaseA (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm (afterSstore sevm
    (afterSload sevm b (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255])
    (Bytes.toB256 [1])) (Bytes.toB256 [15])) (Bytes.toB256 [2])) (Bytes.toB256 [3])

/-- The `totalSupply()` call's base: the token slot read after `_A`. -/
def alSupBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (aBase sevm (alPreBaseA sevm b)) (Bytes.toB256 [5])

/-- The memory `_A` is called over: `fees` zeroed by `CALLDATACOPY` past the calldata, the
adjusted fee at `0x1a0`, `admin_fee` at `0x1c0`, the `MLOAD` of `0x1e0` growing it to `0x200`. -/
def alPreMemA (M : Mem) (σ : Stor) : Mem :=
  (((M.write 0x140 (List.replicate 96 0)).write 0x1a0
    (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]).toBytes).write 0x1c0
    (σ.get adminFeeSlot).toBytes).extend 0x1e0 32

/-- The `totalSupply()` call's memory: `_A`'s, with `A` at `0x220`, the six saved frame words
restored, `A` at `0x1e0` and the selector at `0x260`. -/
def alSupMem (sevm : Sevm) (b : Devm) (M : Mem) (σ : Stor) (amp : Nat) : Mem :=
  ((((((((((aMemNext sevm (alPreBaseA sevm b) (alPreMemA M σ) (Nat.toB256 (3810 + 6))
    (Nat.toB256 amp)).write 0x220 (Nat.toB256 amp).toBytes).write 0x1e0
    (Bytes.toB256 ((alPreMemA M σ).read 0x1e0 32).1).toBytes).write 0x1c0 (σ.get adminFeeSlot).toBytes).write
    0x1a0 (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]).toBytes).write 0x180
    (B256.toBytes 0)).write 0x160 (B256.toBytes 0)).write 0x140 (B256.toBytes 0)).write 0x1e0
    (Nat.toB256 amp).toBytes).write 0x260 (Bytes.toB256 [24, 22, 13, 221]).toBytes)

/-- The prologue's charge before the `totalSupply()` call: `394` for its instructions, the
lock read and set, the three reads, `_A`'s `aGas` and the token slot read, each at its actual
world. -/
def alPreCost1 (sevm : Sevm) (b : Devm) : Nat :=
  394 + sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
    sstoreCost sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
    sloadCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15]) +
    sloadCost sevm (afterSload sevm (afterSstore sevm (afterSload sevm b
      (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
      (Bytes.toB256 [15])) (Bytes.toB256 [2]) +
    sloadCost sevm (afterSload sevm (afterSload sevm (afterSstore sevm (afterSload sevm b
      (Bytes.toB256 [255, 255, 255])) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
      (Bytes.toB256 [15])) (Bytes.toB256 [2])) (Bytes.toB256 [3]) +
    aGas sevm (alPreBaseA sevm b) + sloadCost sevm (aBase sevm (alPreBaseA sevm b)) (Bytes.toB256 [5])

/-- The base at the supply test: the three balance reads after the call. -/
def alPreBase2 (sevm : Sevm) (d : Devm) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm d balancesBase)
    (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2])

/-- The prologue's charge after the `totalSupply()` call: `307` for its instructions and the
three balance reads at their actual worlds. -/
def alPreCost2 (sevm : Sevm) (d : Devm) : Nat :=
  307 + sloadCost sevm d balancesBase +
    sloadCost sevm (afterSload sevm d balancesBase) (balancesBase + Bytes.toB256 [1]) +
    sloadCost sevm (afterSload sevm (afterSload sevm d balancesBase)
      (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2])

/-- The memory at the supply test, from the call's input memory and reply: the reply word at
`0x2c0`, `T` at `0x240`, `D0 = 0` at `0x2e0`, the balances at `0x300 … 0x340` (the key word at
`0xc0` between). -/
def alPreMem2 (Ms : Mem) (out : Bytes) (T : B256) (σ : Stor) : Mem :=
  ((((((((((Ms.extends [(0x27c, 4), (0x2c0, 32)]).write 0x2c0 (out.take 32)).write 0x240
    T.toBytes).write 0x2e0 (Bytes.toB256 [0]).toBytes).write 0xc0 (Bytes.toB256 [1]).toBytes).write
    0x300 (balAt σ 0).toBytes).write 0xc0 (Bytes.toB256 [1]).toBytes).write 0x320
    (balAt σ 1).toBytes).write 0xc0 (Bytes.toB256 [1]).toBytes).write 0x340 (balAt σ 2).toBytes)

/-! ### The prologue core's bookkeeping, outside the walk -/

theorem alPreBaseA_eq {sevm : Sevm} {b b2 b4 b6 b8 b10 : Devm}
    (hb2 : b2 = afterSload sevm b (Bytes.toB256 [255, 255, 255])) (hb4 : b4 = afterSstore sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
    (hb6 : b6 = afterSload sevm b4 (Bytes.toB256 [15])) (hb8 : b8 = afterSload sevm b6 (Bytes.toB256 [2]))
    (hb10 : b10 = afterSload sevm b8 (Bytes.toB256 [3])) : b10 = alPreBaseA sevm b := by
  subst hb10 hb8 hb6 hb4 hb2; rfl

theorem alPreCost1_eq {sevm : Sevm} {b b2 b4 b6 b8 b10 : Devm} {g1 g3 g5 g7 g9 g11 p1 p3 : Nat}
    (hb2 : b2 = afterSload sevm b (Bytes.toB256 [255, 255, 255])) (hb4 : b4 = afterSstore sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
    (hb6 : b6 = afterSload sevm b4 (Bytes.toB256 [15])) (hb8 : b8 = afterSload sevm b6 (Bytes.toB256 [2]))
    (hb10 : b10 = afterSload sevm b8 (Bytes.toB256 [3]))
    (g2x : g1 = g3 + 23 + sloadCost sevm b (Bytes.toB256 [255, 255, 255]))
    (g4x : g3 = g5 + 22 + sstoreCost sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]))
    (g6x : g5 = g7 + 61 + sloadCost sevm b4 (Bytes.toB256 [15]))
    (g8x : g7 = g9 + 125 + sloadCost sevm b6 (Bytes.toB256 [2]))
    (g10x : g9 = g11 + 48 + sloadCost sevm b8 (Bytes.toB256 [3]))
    (hg12 : g11 = p1 + 91 + aGas sevm b10 + 19)
    (p2x : p1 = p3 + 2 + sloadCost sevm (aBase sevm b10) (Bytes.toB256 [5])) :
    g1 + 3 = p3 + alPreCost1 sevm b := by
  subst hb10 hb8 hb6 hb4 hb2
  unfold alPreCost1 alPreBaseA
  omega

theorem alPreCost2_eq {sevm : Sevm} {d c5 c7 : Devm} {dg p4 p6 p8 p10 : Nat}
    (hc5 : c5 = afterSload sevm d balancesBase)
    (hc7 : c7 = afterSload sevm c5 (balancesBase + Bytes.toB256 [1]))
    (hp4 : dg = p4 + 122) (p5x : p4 = p6 + 66 + sloadCost sevm d balancesBase)
    (p7x : p6 = p8 + 72 + sloadCost sevm c5 (balancesBase + Bytes.toB256 [1]))
    (p9x : p8 = p10 + 47 + sloadCost sevm c7 (balancesBase + Bytes.toB256 [2])) :
    dg = p10 + alPreCost2 sevm d := by
  subst hc7 hc5
  unfold alPreCost2
  omega

theorem alSupMem_eq {sevm : Sevm} {b b10 : Devm} {σ : Stor} {amp : Nat} {w : B256}
    {M20 M1 M2 M21 M3 M' M4 M5 M6 M7 M8 M9 M10 M11 Ms : Mem}
    (hb10 : b10 = alPreBaseA sevm b) (hw : Nat.toB256 amp = w)
    (h20 : M1 = M20.write 320 (List.replicate 96 0))
    (h1 : M2 = M1.write 416 (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]).toBytes)
    (h2 : M21 = M2.write 448 (σ.get adminFeeSlot).toBytes) (h21 : M3 = M21.extend 480 32)
    (hA : M' = aMemNext sevm b10 M3 (Nat.toB256 (3810 + 6)) (Nat.toB256 amp))
    (h3 : M4 = M'.write 544 w.toBytes) (h4 : M5 = M4.write 480 (M3.read 480 32).1.toB256.toBytes)
    (h5 : M6 = M5.write 448 (σ.get adminFeeSlot).toBytes)
    (h6 : M7 = M6.write 416 (σ.get feeSlot * Bytes.toB256 [3] / Bytes.toB256 [8]).toBytes)
    (h7 : M8 = M7.write 384 (B256.toBytes 0)) (h8 : M9 = M8.write 352 (B256.toBytes 0))
    (h9 : M10 = M9.write 320 (B256.toBytes 0)) (h10 : M11 = M10.write 480 w.toBytes)
    (h11 : Ms = M11.write 608 (Bytes.toB256 [24, 22, 13, 221]).toBytes) :
    Ms = alSupMem sevm b M20 σ amp := by
  rw [h11, h10, h9, h8, h7, h6, h5, h4, h3, hA, h21, h2, h1, h20, hb10, ← hw]; rfl

theorem alPreMem2_eq {Ms M12 M13 M14 M15 M16 M17 M18 M19 M : Mem} {out : Bytes} {T : B256}
    {σ : Stor}
    (hMd : M12 = (Ms.extends [(B256.toNat 636, B256.toNat 4), (B256.toNat 704, 32)]).write 704
      (List.take 32 out))
    (h12 : M13 = M12.write 576 T.toBytes) (h13 : M14 = M13.write 736 (Bytes.toB256 [0]).toBytes)
    (h14 : M15 = M14.write 192 (Bytes.toB256 [1]).toBytes) (h15 : M16 = M15.write 768 (balAt σ 0).toBytes)
    (h16 : M17 = M16.write 192 (Bytes.toB256 [1]).toBytes) (h17 : M18 = M17.write 800 (balAt σ 1).toBytes)
    (h18 : M19 = M18.write 192 (Bytes.toB256 [1]).toBytes) (h19 : M = M19.write 832 (balAt σ 2).toBytes) :
    M = alPreMem2 Ms out T σ := by
  subst h19 h18 h17 h16 h15 h14 h13 h12 hMd
  rfl

/-- **The guards, `_A`, the supply and the balances, forward** (`t_0e55_c0` → the supply
test). -/
theorem rx_al_preE {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {G R U amp : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W : Devm → Prop} {T : B256}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcd : sevm.data.length < 2 ^ 256)
    (hL : ExLive sevm W b σ) (ha : Abstracts σ s) (hlock : σ.get lockSlot = 0)
    (hval : sevm.value = 0) (hkill : σ.get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xc0)
    (hsup : StaticWordOkAtE sevm W W (σ.get tokenSlot) totalSupplyData T U 0x27c 4 0x2c0 E)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hG : 60000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g : Nat) (Aw : B256), Aw.toNat = amp →
      ExLive sevm W b1 (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x360 →
      WordAt img1 0x140 0 → WordAt img1 0x160 0 → WordAt img1 0x180 0 →
      WordAt img1 0x1a0 (cwFee (σ.get feeSlot)) → WordAt img1 0x1c0 (σ.get adminFeeSlot) →
      WordAt img1 0x1e0 Aw → WordAt img1 0x240 T → WordAt img1 0x2e0 0 →
      WordAt img1 0x300 (balAt σ 0) → WordAt img1 0x320 (balAt σ 1) →
      WordAt img1 0x340 (balAt σ 2) → R ≤ g → g ≤ G →
      ∀ (Gs : Nat) (d : Devm), E (alSupBase sevm b) [] (alSupMem sevm b M σ amp) Gs d →
      G = Gs + alPreCost1 sevm b → d.gasLeft = g + alPreCost2 sevm d → b1 = alPreBase2 sevm d →
      M1 = alPreMem2 (alSupMem sevm b M σ amp) d.returnData T σ →
      (T = 0 → SFunc.RunEx cert.prog sevm (St b1 [] M1 g) t_1031_c4 Q) ∧
      (T ≠ 0 → SFunc.RunEx cert.prog sevm (St b1 [] M1 g) t_0f8f_c0 Q)) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_0e55_c0 Q := by
  have hWc := hL.wc
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 3 := ⟨G - 3, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadVE hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 g2x; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 23 := ⟨g2 - 23, by omega⟩
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hv2, lockSlot_lit, hlock]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sstoreVE hfork hstatic (by omega) ?_; intro g4 b4 hb4 hg41 hg42 g4x; replace hL := hL.sstoreE hb4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 22 := ⟨g4 - 22, by omega⟩
  xr (rx_callvalue (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hval]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadVE hfork (by hrs) (by omega) ?_; intro g6 b6 v6 hb6 hv6 hg61 hg62 g6x; replace hv6 := hL.val hv6; replace hL := hL.sloadE hb6
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 61 := ⟨g6 - 61, by omega⟩
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hv6, isKilledSlot_lit, Stor.get_set_ne _ (by decide) _, hkill]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldatasize (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_calldatacopyL (o := 0x140) (z := 0x60) (c := 33) hR hW hsz (by decide) (by decide) (by decide) ?_; clear hR hW hsz; rename' M => M20; intro M hM20 hR hW hsz; rw [show memExtSize 0xc0 0x140 0x60 = 0x1a0 by decide] at hsz
  rw [B256.toNat_toB256_of_lt hcd, sliceD_data_end] at hR hM20
  have z0 : WordAt (Bytes.writeAt img 0x140 (List.replicate 0x60 0)) 0x140 0 := al_zeroWord img (j := 0) (by omega)
  have z1 : WordAt (Bytes.writeAt img 0x140 (List.replicate 0x60 0)) 0x160 0 := al_zeroWord img (j := 1) (by omega)
  have z2 : WordAt (Bytes.writeAt img 0x140 (List.replicate 0x60 0)) 0x180 0 := al_zeroWord img (j := 2) (by omega)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadVE hfork (by hrs) (by omega) ?_; intro g8 b8 v8 hb8 hv8 hg81 hg82 g8x; replace hv8 := hL.val hv8; replace hL := hL.sloadE hb8
  rw [show Bytes.toB256 [2] = feeSlot by decide, Stor.get_set_ne _ (by decide) _] at hv8; subst hv8
  obtain ⟨g9, rfl⟩ : ∃ g, g8 = g + 125 := ⟨g8 - 125, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_mulGuard hmf) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x1a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M1; intro M hM1 hR hW hsz; rw [show memExtSize 0x1a0 0x1a0 32 = 0x1c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadVE hfork (by hrs) (by omega) ?_; intro g10 b10 v10 hb10 hv10 hg101 hg102 g10x; replace hv10 := hL.val hv10; replace hL := hL.sloadE hb10
  rw [show Bytes.toB256 [3] = adminFeeSlot by decide, Stor.get_set_ne _ (by decide) _] at hv10; subst hv10
  obtain ⟨g11, rfl⟩ : ∃ g, g10 = g + 48 := ⟨g10 - 48, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x1c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M2; intro M hM2 hR hW hsz; rw [show memExtSize 0x1c0 0x1c0 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x140) (v := 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH z0) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x160) (v := 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH z1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x180) (v := 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH z2) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x1a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mloadXE (o := 0x1e0) (c := 6) hR hW hsz rfl (by decide) (by hrs) ?_; clear hR hW hsz; rename' M => M21; intro M hM21 hR hW hsz; rw [show memExtSize 0x1e0 0x1e0 32 = 0x200 by decide] at hsz; rw [← hR.read]
  -- `_A`
  have ha' : Abstracts (b10.getStor sevm.currentTarget) s := ha.of_lock fun x hx => by
    rw [hL.stor x]; exact Stor.get_set_ne _ (by rw [lockSlot_lit]; exact Ne.symm hx) _
  have haG := aGas_le sevm b10
  obtain ⟨g12, hg12⟩ : ∃ g, g11 = g + aGas sevm b10 + 19 := ⟨g11 - aGas sevm b10 - 19, by omega⟩
  rw [hg12]
  obtain ⟨w, ⟨M', hrun, ⟨-, hW', hsz'⟩, hMA⟩, hw⟩ := a_exactL (G := g12)
    (ret := Nat.toB256 (0xee2 + 6)) (S := _ :: _ :: _ :: _ :: _ :: _ :: []) hfork ha' hA hW
    hsz (by decide) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
  refine rxe_pcCall al_prog_27 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    hrun ?_
  replace hL := hL.aBaseE
  clear hR hW hsz hrun
  have hR := Mem.reads_data M'
  have hW := hW'
  have hsz := hsz'
  clear hW' hsz'
  obtain ⟨p1, rfl⟩ : ∃ g, g12 = g + 91 := ⟨g12 - 91, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x220) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M3; intro M hM3 hR hW hsz; rw [show memExtSize 0x200 0x220 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x1e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M4; intro M hM4 hR hW hsz; rw [show memExtSize 0x240 0x1e0 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x1c0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M5; intro M hM5 hR hW hsz; rw [show memExtSize 0x240 0x1c0 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x1a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M6; intro M hM6 hR hW hsz; rw [show memExtSize 0x240 0x1a0 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x180) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M7; intro M hM7 hR hW hsz; rw [show memExtSize 0x240 0x180 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M8; intro M hM8 hR hW hsz; rw [show memExtSize 0x240 0x160 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M9; intro M hM9 hR hW hsz; rw [show memExtSize 0x240 0x140 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x220) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x1e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M10; intro M hM10 hR hW hsz; rw [show memExtSize 0x240 0x1e0 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x260) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M11; intro M hM11 hR hW hsz; rw [show memExtSize 0x240 0x260 32 = 0x280 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadVE hfork (by hrs) (by omega) ?_; intro p2 c2 u2 hc2 hu2 hp21 hp22 p2x; replace hu2 := hL.val hu2; replace hL := hL.sloadE hc2
  obtain ⟨p3, rfl⟩ : ∃ g, p2 = g + 2 := ⟨p2 - 2, by omega⟩
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [5] = tokenSlot by decide, Stor.get_set_ne _ (by decide) _] at hu2; subst hu2
  rw [show Bytes.toB256 [2, 124] = (0x27c : B256) by decide, show Bytes.toB256 [4] = (4 : B256) by decide,
    show Bytes.toB256 [2, 192] = (0x2c0 : B256) by decide, show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read (0x27c : B256).toNat (4 : B256).toNat).1 = totalSupplyData := by
    rw [hR.read, show (0x27c : B256).toNat = 0x27c by decide, show (4 : B256).toNat = 4 by decide,
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide) (by rw [B256.length_toBytes])]
    decide
  refine rxe_staticWordAlE (o := 0x2c0) (s := 0x2e0) hL hWc hsup (by omega) (by omega) (by hrs) hin hR hW rfl
    (by show memExtsSize M.size _ = _; rw [hsz]; decide) (by decide) ?_
  intro d Md out hLd hR' hW' hsz' hlen hlt hA' hrd hgd1 hgd2 hMd hE
  clear hR hW hsz hin hL
  rename' M => Ms; rename' Md => M
  have hR := hR'; have hW := hW'; have hsz := hsz'; have hL := hLd; clear hR' hW' hsz' hLd
  obtain ⟨p4, hp4⟩ : ∃ g, d.gasLeft = g + 122 := ⟨d.gasLeft - 122, by omega⟩
  rw [hp4]
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_returndatasize (by hrs) ·)
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [hrd]; exact ex_rds_gt hlen hlt) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hrs) ·)
  rw [ex_ans_read _ _ _ hlen, hA']
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x240) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M12; intro M hM12 hR hW hsz; rw [show memExtSize 0x2e0 0x240 32 = 0x2e0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x2e0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M13; intro M hM13 hR hW hsz; rw [show memExtSize 0x2e0 0x2e0 32 = 0x300 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M14; intro M hM14 hR hW hsz; rw [show memExtSize 0x300 0xc0 32 = 0x300 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  refine rxe_sloadVE hfork (by hrs) (by omega) ?_; intro p5 c5 u5 hc5 hu5 hp51 hp52 p5x; replace hu5 := hL.val hu5; replace hL := hL.sloadE hc5
  obtain ⟨p6, rfl⟩ : ∃ g, p5 = g + 66 := ⟨p5 - 66, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x300) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M15; intro M hM15 hR hW hsz; rw [show memExtSize 0x300 0x300 32 = 0x320 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M16; intro M hM16 hR hW hsz; rw [show memExtSize 0x320 0xc0 32 = 0x320 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  refine rxe_sloadVE hfork (by hrs) (by omega) ?_; intro p7 c7 u7 hc7 hu7 hp71 hp72 p7x; replace hu7 := hL.val hu7; replace hL := hL.sloadE hc7
  obtain ⟨p8, rfl⟩ : ∃ g, p7 = g + 72 := ⟨p7 - 72, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x320) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M17; intro M hM17 hR hW hsz; rw [show memExtSize 0x320 0x320 32 = 0x340 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M18; intro M hM18 hR hW hsz; rw [show memExtSize 0x340 0xc0 32 = 0x340 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hrs) ·)
  refine rxe_sloadVE hfork (by hrs) (by omega) ?_; intro p9 c9 u9 hc9 hu9 hp91 hp92 p9x; replace hu9 := hL.val hu9; replace hL := hL.sloadE hc9
  obtain ⟨p10, rfl⟩ : ∃ g, p9 = g + 47 := ⟨p9 - 47, by omega⟩
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x340) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => M19; intro M hM19 hR hW hsz; rw [show memExtSize 0x340 0x340 32 = 0x360 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x240) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  have e5 : u5 = balAt σ 0 := by
    rw [hu5, Stor.get_set_ne _ (by decide) _]; exact congrArg σ.get (by decide)
  have e7 : u7 = balAt σ 1 := by
    rw [hu7, Stor.get_set_ne _ (by decide) _]; exact congrArg σ.get (by decide)
  have e9 : u9 = balAt σ 2 := by
    rw [hu9, Stor.get_set_ne _ (by decide) _]; exact congrArg σ.get (by decide)
  subst e5 e7 e9
  have hw' : Nat.toB256 amp = w := by rw [← hw, toB256_toNat]
  have hbA := alPreBaseA_eq hb2 hb4 hb6 hb8 hb10
  have e1 : c2 = alSupBase sevm b := by rw [hc2, hbA]; rfl
  have e2 := alSupMem_eq (σ := σ) hbA hw' hM20 hM1 hM2 hM21 hMA hM3 hM4 hM5 hM6 hM7 hM8 hM9 hM10
    hM11
  rw [e1, e2] at hE
  have hG1 := alPreCost1_eq hb2 hb4 hb6 hb8 hb10 g2x g4x g6x g8x g10x hg12 p2x
  have hG2 := alPreCost2_eq hc5 hc7 hp4 p5x p7x p9x
  have hB2 : c9 = alPreBase2 sevm d := by rw [hc9, hc7, hc5]; rfl
  have hM2' := alPreMem2_eq (σ := σ) hMd hM12 hM13 hM14 hM15 hM16 hM17 hM18 hM19
  rw [e2, ← hrd] at hM2'
  have hk := k c9 M _ p10 w hw hL hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega)
    p3 d hE hG1 hG2 hB2 hM2'
  by_cases hT : T = 0
  · subst hT
    xr (rx_branchTo_succ (by decide) (g := t_1031_c4) rfl ·)
    exact hk.1 rfl
  · xr (rx_branchTo_zero' (al_supply_test hT) ·)
    exact hk.2 hT

/-- **The guards, `_A`, the supply and the balances, forward** (`t_0e55_c0` → the supply
test). -/
theorem rx_al_pre {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {G R U amp : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W : Devm → Prop} {T : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcd : sevm.data.length < 2 ^ 256)
    (hL : ExLive sevm W b σ) (ha : Abstracts σ s) (hlock : σ.get lockSlot = 0)
    (hval : sevm.value = 0) (hkill : σ.get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xc0)
    (hsup : SupplyOkAt sevm W W (σ.get tokenSlot) T U 0x27c 0x2c0)
    (hmf : σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
      σ.get feeSlot = 0)
    (hG : 60000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g : Nat) (Aw : B256), Aw.toNat = amp →
      ExLive sevm W b1 (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])) →
      Mem.Reads M1 img1 → Mem.Wf M1 → M1.size = 0x360 →
      WordAt img1 0x140 0 → WordAt img1 0x160 0 → WordAt img1 0x180 0 →
      WordAt img1 0x1a0 (cwFee (σ.get feeSlot)) → WordAt img1 0x1c0 (σ.get adminFeeSlot) →
      WordAt img1 0x1e0 Aw → WordAt img1 0x240 T → WordAt img1 0x2e0 0 →
      WordAt img1 0x300 (balAt σ 0) → WordAt img1 0x320 (balAt σ 1) →
      WordAt img1 0x340 (balAt σ 2) → R ≤ g → g ≤ G →
      (T = 0 → SFunc.RunEx cert.prog sevm (St b1 [] M1 g) t_1031_c4 Q) ∧
      (T ≠ 0 → SFunc.RunEx cert.prog sevm (St b1 [] M1 g) t_0f8f_c0 Q)) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_0e55_c0 Q :=
  rx_al_preE (E := fun _ _ _ _ _ => True) hfork hstatic hcd hL ha hlock hval hkill hA hR hW hsz
    hsup.withE hmf hG hGb fun b1 M1 img1 g Aw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 _ _ _ _ _ _ _ =>
      k b1 M1 img1 g Aw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

end Blanc.Lift.Curve3Pool
