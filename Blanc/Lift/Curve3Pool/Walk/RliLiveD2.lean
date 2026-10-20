import Blanc.Lift.Curve3Pool.Walk.RliLiveFee
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceBurn

/-!
# `remove_liquidity_imbalance`, forward: `D2` and the burn

`rx_rli_d2` (the fee loop's exit `rliExit` → the transfer loop's head `t_3769_c1368`): the save
of `[0x140, 0x680)`, `D2 = get_D_mem(new_balances, amp)` (`getDMem_exact`), the restore, the
checked `token_amount = (D0 - D2) * token_supply / D0 + 1` at `0x780` (nonzero, within
`max_burn_amount`), and `burnFrom(msg.sender, token_amount)` answered by `BurnOkAt` (window
`0x85c`/`0x8e0`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def rliIdx5 : List Nat := [1056, 1064, 1071, 1078, 1085, 1092, 1099, 1106, 1113, 1120, 1127, 1134,
  1141, 1148, 1155, 1162, 1169, 1175, 1180, 1185, 1190, 1195, 1200, 1205, 1210, 1215, 1220, 1225,
  1230, 1235, 1240, 1245, 1250, 1255, 1260, 1265, 1270, 1275, 1279, 1283, 1286]

def rliIdx6 : List Nat := [1289, 1292, 1295, 1298, 1301, 1304, 1307, 1310, 1313, 1316, 1319, 1322,
  1325, 1328, 1331, 1334, 1337, 1340, 1343, 1345, 1347, 1349, 1350, 1351, 1352, 1353, 1354, 1355,
  1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368]

theorem rli_sv3_first :
    t_35a9_c1055 = svIt 0x06 0x80 0x35 0xcb (lpBr 41 rliIdx5 0x35 0xa9 t_35cb_c1286 0) := rfl

theorem rli_sv3_chain : ∀ n, n < 41 → cert.prog[rliIdx5.getD n 0]? =
    some (svIt 0x06 0x80 0x35 0xcb (lpBr 41 rliIdx5 0x35 0xa9 t_35cb_c1286 (n + 1))) := by
  decide +kernel

theorem rli_rs3_first :
    t_3618_c1286 = rsIt 0x06 0x80 0x36 0x3b (lpBr 41 rliIdx6 0x36 0x18 t_363b_c1368 0) := rfl

theorem rli_rs3_chain : ∀ n, n < 41 → cert.prog[rliIdx6.getD n 0]? =
    some (rsIt 0x06 0x80 0x36 0x3b (lpBr 41 rliIdx6 0x36 0x18 t_363b_c1368 (n + 1))) := by
  decide +kernel

/-- The burned amount: `(D0 - D2) * token_supply / D0 + 1`. -/
abbrev rliBurnW (D0 D2 T : B256) : B256 := (D0 - D2) * T / D0 + Bytes.toB256 [1]

/-- **The memory the burn is called over, exact**: the save counter at `0x680`, the save of
`[0x140, 0x680)`, `get_D_mem`'s arguments at `0x6a0 … 0x700`, its memory, `D2` parked at `0x760`
(a growing store: literal again), the restore counter, the restore, `D2` at `0x660`, the burned
amount at `0x780` (the quotient, then plus one), the slippage error buffer at `0x7a0 … 0x800`
(written on success too), and the `burnFrom` payload at `0x840 … 0x880`. -/
def rliBurnMem (sevm : Sevm) (M : Mem) (a0 a1 a2 Aw : B256) (x : V3) (v : Nat) (D0 T : B256) :
    Mem :=
  let M1 := M.write 0x680 (Bytes.toB256 [1, 64]).toBytes
  let M5 := ((((saveMem M1 0x680 (0x140 + 32 * 0) (41 + 1)).write 0x6a0 a0.toBytes).write 0x6c0
    a1.toBytes).write 0x6e0 a2.toBytes).write 0x700 Aw.toBytes
  ((((((((((restoreMem 0x680 (((getDMemNext M5 (Nat.toB256 (0x3606 + 6)) a0 a1 a2 Aw x v).write
    0x760 (Nat.toB256 v).toBytes).write 0x680 (Bytes.toB256 [6, 96]).toBytes) (0x140 + 32 * 41)
    (exSaved (memWord M1) 0x140 (41 + 1))).write 0x660 (Nat.toB256 v).toBytes).write 0x780
    ((D0 - Nat.toB256 v) * T / D0).toBytes).write 0x780 (rliBurnW D0 (Nat.toB256 v) T).toBytes).write
    0x7a0 (Bytes.toB256 [8, 195, 121, 160]).toBytes).write 0x7c0 (Bytes.toB256 [32]).toBytes).write
    0x7e0 (Bytes.toB256 [20]).toBytes).write 0x800 (Bytes.toB256 [83, 108, 105, 112, 112, 97, 103,
      101, 32, 115, 99, 114, 101, 119, 101, 100, 32, 121, 111, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0]).toBytes).write 0x840 (Bytes.toB256 [121, 204, 103, 144]).toBytes).write 0x860 sevm.caller.toB256.toBytes).write 0x880
    (rliBurnW D0 (Nat.toB256 v) T).toBytes

/-- **`D2` and the burn, forward, exact** (core of `rx_rli_d2`): the burn's relation `E` at its literal
input, the token slot read at its actual world. -/
theorem rx_rli_d2E {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {M : Mem}
    {img : Bytes} {G R U v : Nat} {Q : Outcome → Prop} {x : V3} {W W' : Devm → Prop}
    {T F AF Aw a0 a1 a2 D0 D1 f0 f1 f2 : B256}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hX : xpChk ⟨a0.toNat, a1.toNat, a2.toNat⟩ = some x)
    (hres : getDChk x.get Aw.toNat 1 = some v)
    (hD02 : ¬ D0 < Nat.toB256 v) (hmT : (D0 - Nat.toB256 v).Nofm T) (hD0 : D0 ≠ 0)
    (hbn : (D0 - Nat.toB256 v) * T / D0 ≠ 0)
    (hb1 : ¬ rliBurnW D0 (Nat.toB256 v) T < (D0 - Nat.toB256 v) * T / D0)
    (hslip : ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) < rliBurnW D0 (Nat.toB256 v) T)
    (hburn : MutCallOkAtE sevm W W' (σ.get tokenSlot) (burnFromSel ++ sevm.caller.toB256.toBytes ++
      (rliBurnW D0 (Nat.toB256 v) T).toBytes) (fun r => 32 ≤ r.length) U 0x85c 0x44 0x8e0 E)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hT : WordAt img 0x140 T) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hAw : WordAt img 0x220 Aw) (ha0 : WordAt img 0x2e0 a0) (ha1 : WordAt img 0x300 a1)
    (ha2 : WordAt img 0x320 a2) (hD0w : WordAt img 0x340 D0) (hD1 : WordAt img 0x480 D1)
    (hf0 : WordAt img 0x5a0 f0) (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2)
    (hG : costGetDMem x Aw.toNat + 13000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (hroom : S.length + 120 < 1024)
    (k : ∀ (d : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' d σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 → WordAt img' 0x140 T →
      WordAt img' 0x480 D1 → WordAt img' 0x5a0 f0 → WordAt img' 0x5c0 f1 →
      WordAt img' 0x5e0 f2 → WordAt img' 0x780 (rliBurnW D0 (Nat.toB256 v) T) →
      WordAt img' 0x900 (Bytes.toB256 [0]) → R ≤ g → g ≤ G →
      ∀ Gs : Nat, E (afterSload sevm b (Bytes.toB256 [5])) S
        (rliBurnMem sevm M a0 a1 a2 Aw x v D0 T) Gs d →
      G = Gs + (6358 + costGetDMem x Aw.toNat + sloadCost sevm b (Bytes.toB256 [5]) + 2) →
      d.gasLeft = g + 70 → M' = d.memory.write 0x900 (Bytes.toB256 [0]).toBytes →
      SFunc.RunEx cert.prog sevm (St d ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c1368 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) rliExit Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 441 + (70 * 41 + 59) + 26 + costGetDMem x Aw.toNat + 19 + 120 +
      (67 * 41 + 56) + 20 :=
    ⟨G - costGetDMem x Aw.toNat - 6358, by omega⟩
  -- the save counter, the save
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x680) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x660 0x680 32 = 0x6a0 by decide] at hsz
  have hct0 : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x680
      (Nat.toB256 (0x140 + 32 * 0)) := WordAt.write_eq (by decide) (by decide)
  replace hT : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x140 T := by
    wautoH hT
  replace hAw : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x220 Aw := by
    wautoH hAw
  replace ha0 : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x2e0 a0 := by
    wautoH ha0
  replace ha1 : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x300 a1 := by
    wautoH ha1
  replace ha2 : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x320 a2 := by
    wautoH ha2
  replace hD0w : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x340 D0 := by
    wautoH hD0w
  replace hD1 : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x480 D1 := by
    wautoH hD1
  replace hf0 : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x5a0 f0 := by
    wautoH hf0
  replace hf1 : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x5c0 f1 := by
    wautoH hf1
  replace hf2 : WordAt (Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes) 0x5e0 f2 := by
    wautoH hf2
  generalize Bytes.writeAt img 0x680 (Bytes.toB256 [1, 64]).toBytes = img0 at hR hct0 hT hAw ha0 ha1 ha2 hD0w hD1 hf0 hf1 hf2
  have hR0 := hR
  rw [rli_sv3_first]
  refine rx_svFromM (fun o => Bytes.toB256 (img0.sliceD o 32 0)) (C := 0x680) (sz := 0x6a0)
    (by decide) rfl (by decide) (by decide) rli_sv3_chain 41 (n := 0) rfl hR hW hsz hct0
    (fun m _ _ => wordAt_self _ _) (by omega) ?_
  clear hR hW hsz
  intro M1 img1 hMsv hR hW hsz hk1 hct1
  -- the arguments of `get_D_mem`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0) (v := a0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ ha0 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x6a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0x6a0 0x6a0 32 = 0x6c0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x300) (v := a1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ ha1 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x6c0) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0x6c0 0x6c0 32 = 0x6e0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := a2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ ha2 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x6e0) (c := 7) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0x6e0 0x6e0 32 = 0x700 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x220) (v := Aw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hAw (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x700) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0x700 0x700 32 = 0x720 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x700) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x6e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x6c0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x6a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hrun, ⟨-, hW2, hsz2⟩, hEq2⟩ := getDMem_exactL (G := g1 + 441 + (70 * 41 + 59) + 26)
    (ρ := Nat.toB256 (0x3606 + 6))
    (S := exSaved (fun o => Bytes.toB256 (img0.sliceD o 32 0)) (0x140 + 32 * 0) (41 + 1) ++ S)
    (M := M) hX hres hW hsz (by decide) (by decide)
    (by simp only [List.length_append, exSaved_length]; omega)
  refine rxe_pcCall rli_prog_29 (by decide)
    (by simp only [List.length_cons, List.length_append, exSaved_length]; omega) hrun ?_
  clear hR hW hsz hrun
  have hR := Mem.reads_data M2
  have hW := hW2
  have hsz := hsz2
  have hs2x := hsz2
  clear hW2 hsz2
  -- `D2` parked, the restore counter
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x760) (c := 13) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [show memExtSize 0x720 0x760 32 = 0x780 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x680) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0x780 0x680 32 = 0x780 by decide] at hsz
  rw [rli_rs3_first]
  refine rx_rsFromM (fun o => Bytes.toB256 (img0.sliceD o 32 0)) (C := 0x680) (sz := 0x780)
    (by decide) rfl (by decide) (by decide) rli_rs3_chain 41 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hMrs hR3 hW3 hsz3 hm3 hk3
  have hD3 : WordAt img3 0x760 (Nat.toB256 v) := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  have rT := cw_restored (hm3 0 (by omega)) hT
  have rD0 := cw_restored (hm3 16 (by omega)) hD0w
  have rD1 := cw_restored (hm3 26 (by omega)) hD1
  have rf0 := cw_restored (hm3 35 (by omega)) hf0
  have rf1 := cw_restored (hm3 36 (by omega)) hf1
  have rf2 := cw_restored (hm3 37 (by omega)) hf2
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  -- the burned amount, the burn
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x760) (v := Nat.toB256 v) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD3) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x660) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq8; intro M hMq8 hR hW hsz; rw [show memExtSize 0x780 0x660 32 = 0x780 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := D0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rD0) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x660) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hD02) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x140) (v := T) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rT) (by hrs) ·)
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
  xr (rx_branch_succ (B256.mulGuard_of_nofm hmT) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := D0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH rD0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ hD0 ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x780) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq9; intro M hMq9 hR hW hsz; rw [show memExtSize 0x780 0x780 32 = 0x7a0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x780) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_xor rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [zero_lit, B256.xor_zero]; exact hbn) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x780) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hb1) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x780) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq10; intro M hMq10 hR hW hsz; rw [show memExtSize 0x7a0 0x780 32 = 0x7a0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x7a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq11; intro M hMq11 hR hW hsz; rw [show memExtSize 0x7a0 0x7a0 32 = 0x7c0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x7c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq12; intro M hMq12 hR hW hsz; rw [show memExtSize 0x7c0 0x7c0 32 = 0x7e0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x7e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq13; intro M hMq13 hR hW hsz; rw [show memExtSize 0x7e0 0x7e0 32 = 0x800 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x800) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq14; intro M hMq14 hR hW hsz; rw [show memExtSize 0x800 0x800 32 = 0x820 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x780) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (gtCheck_iszero_of_not_lt (fun h => hslip (B256.lt_iff_toNat_lt_toNat.mpr h))) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x840) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq15; intro M hMq15 hR hW hsz; rw [show memExtSize 0x820 0x840 32 = 0x860 by decide] at hsz
  xr (rx_caller (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x860) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq16; intro M hMq16 hR hW hsz; rw [show memExtSize 0x860 0x860 32 = 0x880 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x780) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x880) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq17; intro M hMq17 hR hW hsz; rw [show memExtSize 0x880 0x880 32 = 0x8a0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadVX hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 g2x; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  rw [show Bytes.toB256 [5] = tokenSlot by decide] at hv2; subst hv2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 2 := ⟨g2 - 2, by omega⟩
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [0x08, 0x5c] = (0x85c : B256) by decide,
    show Bytes.toB256 [0x44] = (0x44 : B256) by decide,
    show Bytes.toB256 [0x08, 0xe0] = (0x8e0 : B256) by decide,
    show Bytes.toB256 [0x20] = (0x20 : B256) by decide]
  have hin : (M.read (0x85c : B256).toNat (0x44 : B256).toNat).1 =
      burnFromSel ++ sevm.caller.toB256.toBytes ++ (rliBurnW D0 (Nat.toB256 v) T).toBytes := by
    rw [hR.read, show (0x85c : B256).toNat = 0x85c by decide,
      show (0x44 : B256).toNat = 0x44 by decide]
    exact rli_burn_input _ _ _
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
    hburn b2 S M g3 hL.w (by omega) (by omega) hin (by hrs)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x85c : B256).toNat = 0x85c by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0x8e0 : B256).toNat = 0x8e0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d (1 :: S) d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd]
  have hext : (M.extends [(0x85c, 0x44), (0x8e0, 0x20)]).size = 0x900 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0x900 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 := (hR.extends [(0x85c, 0x44), (0x8e0, 0x20)]).write (hW.extends _) 0x8e0
    (d.returnData.take 0x20)
  rw [← hmem] at hR5
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have hLd : ExLive sevm W' d σ :=
    ⟨fun x => by rw [hstor]; exact hL.stor x, hidd hL.id, hW'c, hWd⟩
  clear hR hW hsz hext hmem hrun hpost hin
  have hR := hR5; have hW := hW5; have hsz := hsz5
  clear hR5 hW5 hsz5
  obtain ⟨g10, hg10⟩ : ∃ g, d.gasLeft = g + 70 := ⟨d.gasLeft - 70, by omega⟩
  rw [hg10]
  have hgt : B256.gtCheck (Nat.toB256 d.returnData.length) (Bytes.toB256 [0x1f]) ≠ 0 := by
    apply gtCheck_ne_zero_of_lt
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrdlt,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
    omega
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_returndatasize (by hrs) ·)
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by xbr) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x900) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq18; intro M hMq18 hR hW hsz; rw [show memExtSize 0x900 0x900 32 = 0x920 by decide] at hsz
  xr (rx_add (by hrs) ·)
  refine k d M _ g10 hLd hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by omega) (by omega) g3 ?_ (by omega) hg10 hMq18
  rw [slice_memWord_fun hR0] at hMrs
  rw [eqB_write_word_grow hEq2 _ (by rw [hs2x]; decide)] at hMq6
  rw [hb2, hMq17, hMq16, hMq15, hMq14, hMq13, hMq12, hMq11, hMq10, hMq9, hMq8, hMrs, hMq7, hMq6,
    hMq5, hMq4, hMq3, hMq2, hMsv, hMq1] at hE
  exact hE

/-- **`D2` and the burn, forward.** -/
theorem rx_rli_d2 {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {M : Mem}
    {img : Bytes} {G R U v : Nat} {Q : Outcome → Prop} {x : V3} {W W' : Devm → Prop}
    {T F AF Aw a0 a1 a2 D0 D1 f0 f1 f2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hX : xpChk ⟨a0.toNat, a1.toNat, a2.toNat⟩ = some x)
    (hres : getDChk x.get Aw.toNat 1 = some v)
    (hD02 : ¬ D0 < Nat.toB256 v) (hmT : (D0 - Nat.toB256 v).Nofm T) (hD0 : D0 ≠ 0)
    (hbn : (D0 - Nat.toB256 v) * T / D0 ≠ 0)
    (hb1 : ¬ rliBurnW D0 (Nat.toB256 v) T < (D0 - Nat.toB256 v) * T / D0)
    (hslip : ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) < rliBurnW D0 (Nat.toB256 v) T)
    (hburn : BurnOkAt sevm W W' (σ.get tokenSlot) (rliBurnW D0 (Nat.toB256 v) T) U 0x85c 0x8e0)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hT : WordAt img 0x140 T) (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF)
    (hAw : WordAt img 0x220 Aw) (ha0 : WordAt img 0x2e0 a0) (ha1 : WordAt img 0x300 a1)
    (ha2 : WordAt img 0x320 a2) (hD0w : WordAt img 0x340 D0) (hD1 : WordAt img 0x480 D1)
    (hf0 : WordAt img 0x5a0 f0) (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2)
    (hG : costGetDMem x Aw.toNat + 13000 + U + R ≤ G) (hGb : G < 2 ^ 256)
    (hroom : S.length + 120 < 1024)
    (k : ∀ (d : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' d σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 → WordAt img' 0x140 T →
      WordAt img' 0x480 D1 → WordAt img' 0x5a0 f0 → WordAt img' 0x5c0 f1 →
      WordAt img' 0x5e0 f2 → WordAt img' 0x780 (rliBurnW D0 (Nat.toB256 v) T) →
      WordAt img' 0x900 (Bytes.toB256 [0]) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St d ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c1368 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) rliExit Q :=
  rx_rli_d2E hfork hstatic hL hW'c hX hres hD02 hmT hD0 hbn hb1 hslip hburn.withE hR hW hsz hT hF hAF
    hAw ha0 ha1 ha2 hD0w hD1 hf0 hf1 hf2 hG hGb hroom
    fun d M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 _ _ _ _ _ =>
      k d M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

end Blanc.Lift.Curve3Pool
