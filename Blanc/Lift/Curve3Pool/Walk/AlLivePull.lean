import Blanc.Lift.Curve3Pool.Walk.AlLiveCredit

/-!
# `add_liquidity`, forward: the `transferFrom` pull

`alPullC` is the path skeleton of `0x110d` → the `raw_call` tail (the payload built at `0x680`
with two identity copies, then the `CALL` to `coins[i]`), its tail a parameter; every context's
pull tree is an instance. `rx_al_pullCore` runs it forward with the `CALL` answered by
`CoinPullOkAt` (input `0x760[0 : 0x64]`, output `0x820[0 : 0x20]`) and Vyper's `raw_call` success
test (`alPullSite`, join entry `5`), up to the fee-index test `t_1271_c5`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def alPullC (a1 : SFunc) (a2 : SFunc) (a3 : SFunc) : SFunc :=
  (.dest (.next (.push [0x00] (by decide)) (.next (.push [0x04] (by decide)) (.next (.push [0x06, 0x20] (by decide)) (.next (.reg .mstore) (.next (.push [0x23, 0xb8, 0x72, 0xdd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.push [0x06, 0x40] (by decide)) (.next (.reg .mstore) (.next (.push [0x06, 0x20] (by decide)) (.next (.push [0x04] (by decide)) (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 4)) (.next (.push [0x06, 0x80] (by decide)) (.next (.reg .add) (.next (.reg .add) (.next (.reg (.dup 2)) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 5)) (.next (.reg .add) (.next (.push [0x00] (by decide)) (.next (.push [0x04] (by decide)) (.next (.reg .gas) (.next (.exec .call) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .caller) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 2)) (.next (.push [0x06, 0x80] (by decide)) (.next (.reg .add) (.next (.reg .add) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg .address) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 2)) (.next (.push [0x06, 0x80] (by decide)) (.next (.reg .add) (.next (.reg .add) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x04] (by decide)) (.next (.push [0x04, 0xc0] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x11, 0x8f] (by decide)) (.branch a1 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .calldataload) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 2)) (.next (.push [0x06, 0x80] (by decide)) (.next (.reg .add) (.next (.reg .add) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.dup 0)) (.next (.push [0x06, 0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x06, 0x80] (by decide)) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.push [0x07, 0x40] (by decide)) (.next (.reg (.dup 2)) (.next (.reg (.dup 4)) (.next (.push [0x00] (by decide)) (.next (.push [0x04] (by decide)) (.next (.reg .gas) (.next (.exec .call) (.next (.push [0x11, 0xc7] (by decide)) (.branch a2 (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x20] (by decide)) (.next (.push [0x08, 0x20] (by decide)) (.next (.push [0x07, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x07, 0x60] (by decide)) (.next (.push [0x00] (by decide)) (.next (.push [0x05, 0x00] (by decide)) (.next (.reg .mload) (.next (.reg .gas) (.next (.exec .call) (.next (.push [0x11, 0xe6] (by decide)) a3)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem t_110d_c4_eq : t_110d_c4 = alPullC t_118b_c4 t_11c3_c4 ((.branch t_11e2_c4 t_11e6_c4)) := rfl
theorem t_110d_c40_eq : t_110d_c40 = alPullC t_118b_c40 t_11c3_c40 ((.branch t_11e2_c40 t_11e6_c40)) := rfl
theorem t_110d_c41_eq : t_110d_c41 = alPullC t_118b_c41 t_11c3_c41 ((.branch t_11e2_c41 t_11e6_c41)) := rfl
theorem t_110d_c66_eq : t_110d_c66 = alPullC t_118b_c66 t_11c3_c66 ((.branch t_11e2_c66 t_11e6_c66)) := rfl

/-- The `raw_call` site of the pull: length word at `0x800`, copy buffer at `0x5c0`. -/
def alPullSite : VyRawSite := ⟨0x08, 0x00, 0x05, 0xc0, 0x11, 0xe6, 0x11, 0xf7, 0x11, 0xf9, 0x12,
  0x1e, 0x12, 0x71, 0x12, 0x47, 0x12, 0x55, 0x12, 0x70⟩

theorem al_pull_join : cert.prog[5]? =
    some (vyRawCallJoin alPullSite t_121a_c5 t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5) := rfl

theorem al_pull_tail_c4 : SFunc.next (.push [0x11, 0xe6] (by decide)) (.branch t_11e2_c4 t_11e6_c4) =
    vyRawCallTail alPullSite 5 t_11e2_c4 t_121a_c5 t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5 := rfl

theorem al_pull_tail_c40 : SFunc.next (.push [0x11, 0xe6] (by decide)) (.branch t_11e2_c40 t_11e6_c40) =
    vyRawCallTail alPullSite 5 t_11e2_c40 t_121a_c5 t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5 := rfl

theorem al_pull_tail_c41 : SFunc.next (.push [0x11, 0xe6] (by decide)) (.branch t_11e2_c41 t_11e6_c41) =
    vyRawCallTail alPullSite 5 t_11e2_c41 t_121a_c5 t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5 := rfl

theorem al_pull_tail_c66 : SFunc.next (.push [0x11, 0xe6] (by decide)) (.branch t_11e2_c66 t_11e6_c66) =
    vyRawCallTail alPullSite 5 t_11e2_c66 t_121a_c5 t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5 := rfl

/-- The selector the first identity copy moves. -/
theorem al_pull_sel (img : Bytes) :
    ((Bytes.writeAt img 0x640 (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes).sliceD 0x640 4 0).take 4 =
      transferFromSel := by
  rw [(WordAt.write_self _ _ _).prefix (by decide)]; decide

/-! ## The pull, exact

The canonical data of the pull's two identity copies and its `CALL`, as the stage cores report
them: the first copy's input memory (`alPullMem1`, the length word and the selector), its
canonical successor (`alPullId1`), the second copy's input memory (`alPullMem2`, the payload's
words), its canonical successor (`alPullId2`, the `CALL`'s base), and the `CALL`'s input memory
(`alPullMemC`). -/

/-- The first identity copy's input memory: the length word `4` at `0x620`, the selector at
`0x640`. -/
def alPullMem1 (M : Mem) : Mem :=
  (M.write 1568 (Bytes.toB256 [4]).toBytes).write 1600 (Bytes.toB256
      [35, 184, 114, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toBytes

/-- The first identity copy's canonical successor. -/
def alPullId1 (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) : Devm :=
  identityCallNext sevm b (Bytes.toB256 [4] :: Bytes.toB256 [6, 32] :: Bytes.toB256 [0] :: 3 :: 1216 :: S)
    (alPullMem1 M) (Bytes.toB256 [6, 32] + Bytes.toB256 [32]) (Bytes.toB256 [4])
    (Bytes.toB256 [6, 128] + Bytes.toB256 [0] + Bytes.toB256 [32]) (Bytes.toB256 [4])

/-- The second identity copy's input memory: the copied selector, `caller`, `self`, the amount,
the payload length `0x64` at `0x680`. -/
def alPullMem2 (sevm : Sevm) (M : Mem) (i : Nat) : Mem :=
  (((((alPullMem1 M).extends [(1600, 4), (1696, 4)]).write 1696
    (List.take 4 ((alPullMem1 M).read 1600 4).1)).write 1700 sevm.caller.toB256.toBytes).write
    1732 sevm.currentTarget.toB256.toBytes).write 1764
    (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 i + Bytes.toB256 [4])).toBytes |>.write 1664
    (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes

/-- The second identity copy's canonical successor: the `transferFrom` call's base. -/
def alPullId2 (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (i : Nat) : Devm :=
  identityCallNext sevm (alPullId1 sevm b S M)
    ((Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] + Bytes.toB256 [32])) :: Bytes.toB256 [6, 128] :: 3 :: 1216 :: S)
    (alPullMem2 sevm M i) (Bytes.toB256 [6, 128]) (Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] + Bytes.toB256 [32]))
    (Bytes.toB256 [7, 64]) (Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] + Bytes.toB256 [32]))

/-- The `transferFrom` call's input memory: the payload copied to `0x740`. -/
def alPullMemC (sevm : Sevm) (M : Mem) (i : Nat) : Mem :=
  ((alPullMem2 sevm M i).extends [(1664, 132), (1856, 132)]).write 1856
    (List.take 132 ((alPullMem2 sevm M i).read 1664 132).1)

theorem alPull_eq {sevm : Sevm} {b bJ bI : Devm} {S : List B256} {i : Nat}
    {M0 Mq1 MqI1 Mq2 Mq3 Mq4 Mq5 MqI2 M : Mem}
    (h0 : Mq1 = M0.write 1568 (Bytes.toB256 [4]).toBytes)
    (h1 : MqI1 = Mq1.write 1600 (Bytes.toB256
      [35, 184, 114, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toBytes)
    (hc1 : Devm.EqModGas bJ (identityCallNext sevm b
      (Bytes.toB256 [4] :: Bytes.toB256 [6, 32] :: Bytes.toB256 [0] :: 3 :: 1216 :: S) MqI1
      (Bytes.toB256 [6, 32] + Bytes.toB256 [32]) (Bytes.toB256 [4])
      (Bytes.toB256 [6, 128] + Bytes.toB256 [0] + Bytes.toB256 [32]) (Bytes.toB256 [4])))
    (hI1 : Mq2 = (MqI1.extends [(1600, 4), (1696, 4)]).write 1696 (List.take 4 (MqI1.read 1600 4).1))
    (h2 : Mq3 = Mq2.write 1700 sevm.caller.toB256.toBytes)
    (h3 : Mq4 = Mq3.write 1732 sevm.currentTarget.toB256.toBytes)
    (h4 : Mq5 = Mq4.write 1764 (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 i + Bytes.toB256 [4])).toBytes)
    (h5 : MqI2 = Mq5.write 1664 (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes)
    (hc2 : Devm.EqModGas bI (identityCallNext sevm bJ
      ((Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] + Bytes.toB256 [32])) :: Bytes.toB256 [6, 128] :: 3 :: 1216 :: S) MqI2
      (Bytes.toB256 [6, 128]) (Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] + Bytes.toB256 [32])) (Bytes.toB256 [7, 64])
      (Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] + Bytes.toB256 [32]))))
    (hI2 : M = (MqI2.extends [(1664, 132), (1856, 132)]).write 1856 (List.take 132 (MqI2.read 1664 132).1)) :
    Devm.EqModGas bI (alPullId2 sevm b S M0 i) ∧ M = alPullMemC sevm M0 i := by
  have e1 : MqI1 = alPullMem1 M0 := by rw [h1, h0]; rfl
  have e2 : MqI2 = alPullMem2 sevm M0 i := by rw [h5, h4, h3, h2, hI1, e1]; rfl
  refine ⟨?_, by rw [hI2, e2]; rfl⟩
  rw [e2] at hc2
  rw [e1] at hc1
  exact hc2.trans (identityCallNext_congr sevm _ _ _ _ _ _ hc1)

/-- `rx_al_pullCore` over a relation premise, the continuation also receiving the call's
relation at its canonical input, the exact charges and the literal memories. -/
theorem rx_al_pullCoreE {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {G R U i : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W W' : Devm → Prop} {X C F AF A T D0 : B256}
    {old nv : Nat → B256} {a1 a2 a3 f1 : SFunc}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hdepth : sevm.depth ≠ 0) (hi : i < 3)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) {s c0 : Nat} (hsz : M.size = s)
    (hs : (s = 0x520 ∧ c0 = 31) ∨ (s = 0x5c0 ∧ c0 = 15))
    (hm : AlPullImg img i F AF A T D0 old nv) (hx : WordAt img 0x4e0 X) (hc : WordAt img 0x500 C)
    (htail : SFunc.next (.push [0x11, 0xe6] (by decide)) a3 =
      vyRawCallTail alPullSite 5 f1 t_121a_c5 t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5)
    (hpull : MutCallOkAtE sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes) RawCallOk U 0x760 0x64 0x820 E)
    (hG : 4000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 → AlPullImg img' i F AF A T D0 old nv →
      WordAt img' 0x4e0 X → WordAt img' 0x500 C → R ≤ g → g ≤ G →
      ∀ (g1 : Nat) (bI d : Devm), Devm.EqModGas bI (alPullId2 sevm b S M i) →
      E bI (3 :: 0x4c0 :: S) (alPullMemC sevm M i) g1 d → G = g1 + (615 + c0) →
      d.gasLeft = g + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d (3 :: 0x4c0 :: S) d.memory alPullSite) →
      M' = vyRawMem d.memory 0x800 0x5c0 (min d.returnData.length 32) →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_1271_c5 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) (alPullC a1 a2 a3) Q := by
  have hc0 : c0 ≤ 31 := by omega
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 605 + c0 + 10 := ⟨G - 615 - c0, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x620) (c := c0) hR hW hsz rfl
    (by rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) ?_
  have hs' : memExtSize s 0x620 32 = 0x640 := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  clear hR hW hsz; rename' M => Mq0; intro M hMq0 hR hW hsz; rw [hs'] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x640) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x640 0x640 32 = 0x660 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_gas (by hrs) ·)
  refine rxe_identityL (i := 0x640) (n := 0x4) (o := 0x6a0) (z := 0x4) (ext := 9) (X := 127) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 9 + 64 * idCost 0x4 = 1261 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqI1; intro bJ M hsha hcanI1 hMI1 hR hW hsz; rw [show memExtsSize 0x660 [(0x640, 0x4), (0x6a0, 0x4)] = 0x6c0 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [al_pull_sel] at hR
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x620) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap2 ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_caller (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x6a4) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0x6c0 0x6a4 32 = 0x6e0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_address (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x6c4) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0x6e0 0x6c4 32 = 0x700 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.ctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x6e4) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0x700 0x6e4 32 = 0x720 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x680) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0x720 0x680 32 = 0x720 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x680) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_gas (by hrs) ·)
  refine rxe_identityL (i := 0x680) (n := 0x84) (o := 0x740) (z := 0x84) (ext := 19) (X := 149) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 19 + 64 * idCost 0x84 = 2039 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqI2; intro bI M hsha hcanI2 hMI2 hR hW hsz; rw [show memExtsSize 0x720 [(0x680, 0x84), (0x740, 0x84)] = 0x7e0 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [al_tf_copy _ _ _ _ (Region.write_self _ _ _)] at hR
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have hdata : Region img3 0x740 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes ++ (transferFromSel ++
      sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  have hkeep3 : ∀ o w, WordAt img o w → o + 32 ≤ 0x620 → WordAt img3 o w := by
    intro o w hw ho; rw [hI]
    refine WordAt.write_other ?_ (by simp only [transferFromSel, List.length_append,
      B256.length_toBytes, List.length_cons, List.length_nil]; omega)
    wauto
  clear hI
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x740) hR hsz rfl (by decide) (by hrs) ·)
  rw [(Region.word hdata.left).read]
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x500) (v := C) hR hsz rfl ⟨by decide, by decide⟩ (hkeep3 _ _ hc (by decide)) (by hrs) ·)
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] +
      Bytes.toB256 [32] = (0x64 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [7, 96] = (0x760 : B256) by decide,
    show Bytes.toB256 [8, 32] = (0x820 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read 0x760 0x64).1 = transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes := by
    rw [hR.read]
    exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
    hpull bI (3 :: 0x4c0 :: S) M g1 hL.w (by omega) (by omega) hin (by hrs)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x760 : B256).toNat = 0x760 by decide, show (0x64 : B256).toNat = 0x64 by decide,
    show (0x820 : B256).toNat = 0x820 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d (1 :: 3 :: 0x4c0 :: S) d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, htail]
  have hext : (M.extends [(0x760, 0x64), (0x820, 0x20)]).size = 0x840 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0x840 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt img3 0x820 (d.returnData.take 0x20)) := by
    rw [hmem]; exact (hR.extends _).write (hW.extends _) _ _
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have htc : rawTailCost (min d.returnData.length 32) ≤ 500 := by
    unfold rawTailCost rawJoinCost rawCheckCost idCost ceilDiv
    split_ifs <;> omega
  obtain ⟨G2, hG2⟩ : ∃ G2, d.gasLeft = G2 + rawTailCost (min d.returnData.length 32) :=
    ⟨d.gasLeft - rawTailCost (min d.returnData.length 32), by omega⟩
  rw [hG2]
  have hLd : ExLive sevm W' d σ :=
    ⟨fun x => by rw [hstor]; exact hL.stor x, hidd hL.id, hW'c, hWd⟩
  refine SFunc.runEx_iff_runExCut_nil.mpr (rxce_vyRawCallTail_canonical hLd.id
    hdepth (by decide) al_pull_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hrs)
    ?_)
  · rw [show (Bytes.toB256 [alPullSite.lh, alPullSite.ll]).toNat + 32 = 0x820 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha hcanT
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  rw [show (Bytes.toB256 [alPullSite.lh, alPullSite.ll]).toNat = 0x800 by decide,
    show (Bytes.toB256 [alPullSite.bh, alPullSite.bl]).toNat = 0x5c0 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0x800 0x5c0 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img3 0x820 (d.returnData.take 0x20)) 0x800
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x5c0 ((Bytes.writeAt (Bytes.writeAt
        img3 0x820 (d.returnData.take 0x20)) 0x800
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x800
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0x800 0x5c0 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0x800 0x5c0 (min d.returnData.length 32)).size = 0x840 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0x800 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0x840 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  have hK : ∀ o w, WordAt img o w → o + 32 ≤ 0x5c0 → WordAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img3 0x820 (d.returnData.take 0x20)) 0x800
      (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x5c0 ((Bytes.writeAt (Bytes.writeAt
      img3 0x820 (d.returnData.take 0x20)) 0x800
      (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x800
      (min d.returnData.length 32 + 32) 0)) o w := by
    intro o w hw ho
    refine WordAt.write_other ?_ (by omega)
    refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
    refine WordAt.write_other ?_ (by rw [List.length_take]; omega)
    exact hkeep3 o w hw (by omega)
  have hEq := alPull_eq hMq0 hMq1 hcanI1 hMI1 hMq2 hMq3 hMq4 hMq5 hcanI2 hMI2
  exact k b' _ _ G2 (hLd.sha hsha) hR6 hW6 hsz6
    (al_pullImg_keep hm fun o w hw _ ho => hK o w hw (by omega)) (hK _ _ hx (by decide))
    (hK _ _ hc (by decide)) (by omega) (by omega)
    g1 bI d hEq.1 (by rw [← hEq.2]; exact hE)
    (by omega) (by omega) hcanT rfl

/-- **The pull, forward** (`0x110d` → `t_1271_c5`). -/
theorem rx_al_pullCore {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {G R U i : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W W' : Devm → Prop} {X C F AF A T D0 : B256}
    {old nv : Nat → B256} {a1 a2 a3 f1 : SFunc}
    (hdepth : sevm.depth ≠ 0) (hi : i < 3)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) {s c0 : Nat} (hsz : M.size = s)
    (hs : (s = 0x520 ∧ c0 = 31) ∨ (s = 0x5c0 ∧ c0 = 15))
    (hm : AlPullImg img i F AF A T D0 old nv) (hx : WordAt img 0x4e0 X) (hc : WordAt img 0x500 C)
    (htail : SFunc.next (.push [0x11, 0xe6] (by decide)) a3 =
      vyRawCallTail alPullSite 5 f1 t_121a_c5 t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5)
    (hpull : CoinPullOkAt sevm W W' C (alAmt sevm i) U 0x760 0x820)
    (hG : 4000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 → AlPullImg img' i F AF A T D0 old nv →
      WordAt img' 0x4e0 X → WordAt img' 0x500 C → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_1271_c5 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) (alPullC a1 a2 a3) Q :=
  rx_al_pullCoreE hdepth hi hL hW'c hR hW hsz hs hm hx hc htail hpull.withE hG hGb hroom
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ _ _ _ _ _ _ => k b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9
/-- `rx_al_pullCore840` over a relation premise, the continuation also receiving the call's
relation at its canonical input, the exact charges and the literal memories. -/
theorem rx_al_pullCore840E {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {G R U i : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W W' : Devm → Prop} {X C F AF A T D0 : B256}
    {old nv : Nat → B256} {a1 a2 a3 f1 : SFunc}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hdepth : sevm.depth ≠ 0) (hi : i < 3)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x840)
    (hm : AlPullImg img i F AF A T D0 old nv) (hx : WordAt img 0x4e0 X) (hc : WordAt img 0x500 C)
    (htail : SFunc.next (.push [0x11, 0xe6] (by decide)) a3 =
      vyRawCallTail alPullSite 5 f1 t_121a_c5 t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5)
    (hpull : MutCallOkAtE sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes) RawCallOk U 0x760 0x64 0x820 E)
    (hG : 4000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 → AlPullImg img' i F AF A T D0 old nv →
      WordAt img' 0x4e0 X → WordAt img' 0x500 C → R ≤ g → g ≤ G →
      ∀ (g1 : Nat) (bI d : Devm), Devm.EqModGas bI (alPullId2 sevm b S M i) →
      E bI (3 :: 0x4c0 :: S) (alPullMemC sevm M i) g1 d → G = g1 + 576 →
      d.gasLeft = g + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d (3 :: 0x4c0 :: S) d.memory alPullSite) →
      M' = vyRawMem d.memory 0x800 0x5c0 (min d.returnData.length 32) →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_1271_c5 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) (alPullC a1 a2 a3) Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 576 := ⟨G - 576, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x620) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x840 0x620 32 = 0x840 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x640) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0x840 0x640 32 = 0x840 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_gas (by hrs) ·)
  refine rxe_identityL (i := 0x640) (n := 0x4) (o := 0x6a0) (z := 0x4) (ext := 0) (X := 118) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 0 + 64 * idCost 0x4 = 1252 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqI1; intro bJ M hsha hcanI1 hMI1 hR hW hsz; rw [show memExtsSize 0x840 [(0x640, 0x4), (0x6a0, 0x4)] = 0x840 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [al_pull_sel] at hR
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x620) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap2 ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_caller (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x6a4) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0x840 0x6a4 32 = 0x840 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_address (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x6c4) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0x840 0x6c4 32 = 0x840 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.ctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x6e4) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0x840 0x6e4 32 = 0x840 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x680) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [show memExtSize 0x840 0x680 32 = 0x840 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x680) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_gas (by hrs) ·)
  refine rxe_identityL (i := 0x680) (n := 0x84) (o := 0x740) (z := 0x84) (ext := 0) (X := 130) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 0 + 64 * idCost 0x84 = 2020 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqI2; intro bI M hsha hcanI2 hMI2 hR hW hsz; rw [show memExtsSize 0x840 [(0x680, 0x84), (0x740, 0x84)] = 0x840 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [al_tf_copy _ _ _ _ (Region.write_self _ _ _)] at hR
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have hdata : Region img3 0x740 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes ++ (transferFromSel ++
      sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  have hkeep3 : ∀ o w, WordAt img o w → o + 32 ≤ 0x620 → WordAt img3 o w := by
    intro o w hw ho; rw [hI]
    refine WordAt.write_other ?_ (by simp only [transferFromSel, List.length_append,
      B256.length_toBytes, List.length_cons, List.length_nil]; omega)
    wauto
  clear hI
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x740) hR hsz rfl (by decide) (by hrs) ·)
  rw [(Region.word hdata.left).read]
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x500) (v := C) hR hsz rfl ⟨by decide, by decide⟩ (hkeep3 _ _ hc (by decide)) (by hrs) ·)
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] +
      Bytes.toB256 [32] = (0x64 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [7, 96] = (0x760 : B256) by decide,
    show Bytes.toB256 [8, 32] = (0x820 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read 0x760 0x64).1 = transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (alAmt sevm i).toBytes := by
    rw [hR.read]
    exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
    hpull bI (3 :: 0x4c0 :: S) M g1 hL.w (by omega) (by omega) hin (by hrs)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x760 : B256).toNat = 0x760 by decide, show (0x64 : B256).toNat = 0x64 by decide,
    show (0x820 : B256).toNat = 0x820 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d (1 :: 3 :: 0x4c0 :: S) d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, htail]
  have hext : (M.extends [(0x760, 0x64), (0x820, 0x20)]).size = 0x840 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0x840 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt img3 0x820 (d.returnData.take 0x20)) := by
    rw [hmem]; exact (hR.extends _).write (hW.extends _) _ _
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have htc : rawTailCost (min d.returnData.length 32) ≤ 500 := by
    unfold rawTailCost rawJoinCost rawCheckCost idCost ceilDiv
    split_ifs <;> omega
  obtain ⟨G2, hG2⟩ : ∃ G2, d.gasLeft = G2 + rawTailCost (min d.returnData.length 32) :=
    ⟨d.gasLeft - rawTailCost (min d.returnData.length 32), by omega⟩
  rw [hG2]
  have hLd : ExLive sevm W' d σ :=
    ⟨fun x => by rw [hstor]; exact hL.stor x, hidd hL.id, hW'c, hWd⟩
  refine SFunc.runEx_iff_runExCut_nil.mpr (rxce_vyRawCallTail_canonical hLd.id
    hdepth (by decide) al_pull_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hrs)
    ?_)
  · rw [show (Bytes.toB256 [alPullSite.lh, alPullSite.ll]).toNat + 32 = 0x820 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha hcanT
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  rw [show (Bytes.toB256 [alPullSite.lh, alPullSite.ll]).toNat = 0x800 by decide,
    show (Bytes.toB256 [alPullSite.bh, alPullSite.bl]).toNat = 0x5c0 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0x800 0x5c0 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img3 0x820 (d.returnData.take 0x20)) 0x800
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x5c0 ((Bytes.writeAt (Bytes.writeAt
        img3 0x820 (d.returnData.take 0x20)) 0x800
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x800
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0x800 0x5c0 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0x800 0x5c0 (min d.returnData.length 32)).size = 0x840 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0x800 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0x840 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  have hK : ∀ o w, WordAt img o w → o + 32 ≤ 0x5c0 → WordAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img3 0x820 (d.returnData.take 0x20)) 0x800
      (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x5c0 ((Bytes.writeAt (Bytes.writeAt
      img3 0x820 (d.returnData.take 0x20)) 0x800
      (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x800
      (min d.returnData.length 32 + 32) 0)) o w := by
    intro o w hw ho
    refine WordAt.write_other ?_ (by omega)
    refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
    refine WordAt.write_other ?_ (by rw [List.length_take]; omega)
    exact hkeep3 o w hw (by omega)
  have hEq := alPull_eq hMq1 hMq2 hcanI1 hMI1 hMq3 hMq4 hMq5 hMq6 hcanI2 hMI2
  exact k b' _ _ G2 (hLd.sha hsha) hR6 hW6 hsz6
    (al_pullImg_keep hm fun o w hw _ ho => hK o w hw (by omega)) (hK _ _ hx (by decide))
    (hK _ _ hc (by decide)) (by omega) (by omega)
    g1 bI d hEq.1 (by rw [← hEq.2]; exact hE)
    (by omega) (by omega) hcanT rfl


/-- **The pull over a memory of `0x840`, forward** (`0x110d` → `t_1271_c5`; an earlier pull
already grew the memory). -/
theorem rx_al_pullCore840 {sevm : Sevm} {b : Devm} {σ : Stor} {S : List B256} {G R U i : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W W' : Devm → Prop} {X C F AF A T D0 : B256}
    {old nv : Nat → B256} {a1 a2 a3 f1 : SFunc}
    (hdepth : sevm.depth ≠ 0) (hi : i < 3)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x840)
    (hm : AlPullImg img i F AF A T D0 old nv) (hx : WordAt img 0x4e0 X) (hc : WordAt img 0x500 C)
    (htail : SFunc.next (.push [0x11, 0xe6] (by decide)) a3 =
      vyRawCallTail alPullSite 5 f1 t_121a_c5 t_1243_c5 t_1251_c5 t_126c_c5 t_1271_c5)
    (hpull : CoinPullOkAt sevm W W' C (alAmt sevm i) U 0x760 0x820)
    (hG : 4000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x840 → AlPullImg img' i F AF A T D0 old nv →
      WordAt img' 0x4e0 X → WordAt img' 0x500 C → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_1271_c5 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) (alPullC a1 a2 a3) Q :=
  rx_al_pullCore840E hdepth hi hL hW'c hR hW hsz hm hx hc htail hpull.withE hG hGb hroom
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ _ _ _ _ _ _ => k b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9
end Blanc.Lift.Curve3Pool
