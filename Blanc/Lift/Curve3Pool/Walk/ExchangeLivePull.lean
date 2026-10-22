import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveMid

/-!
# `exchange`, forward: the `transferFrom` pull and its `raw_call` test

`rx_ex_pull` is the forward twin of `xa_ex_pull` and `xa_ex_tail1`: the payload built at `0x520`
with two identity copies, the `CALL` to `input_coin` answered by `CoinPullOkAt` (input
`0x600[0 : 0x64]`, output `0x6c0[0 : 0x20]`), and Vyper's `raw_call` success test, up to the
second fee test (`t_2666_c12`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `raw_call` site of the pull: length word at `0x6a0`, copy buffer at `0x460`. -/
def exPullSite : VyRawSite := ⟨0x06, 0xa0, 0x04, 0x60, 0x25, 0xdb, 0x25, 0xec, 0x25, 0xee, 0x26,
  0x13, 0x26, 0x66, 0x26, 0x3c, 0x26, 0x4a, 0x26, 0x65⟩

theorem ex_pull_join : cert.prog[12]? =
    some (vyRawCallJoin exPullSite t_260f_c12 t_2638_c12 t_2646_c12 t_2661_c12 t_2666_c12) := rfl

theorem ex_pull_tail : (SFunc.next (.push [0x25, 0xdb] (by decide)) (.branch t_25d7_c11 t_25db_c11)) =
    vyRawCallTail exPullSite 12 t_25d7_c11 t_260f_c12 t_2638_c12 t_2646_c12 t_2661_c12
      t_2666_c12 := rfl

/-- The selector the first identity copy moves. -/
theorem ex_pull_sel (img : Bytes) :
    ((Bytes.writeAt img 0x4e0 (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes).sliceD 0x4e0 4 0).take 4 =
      transferFromSel := by
  rw [(WordAt.write_self _ _ _).prefix (by decide)]; decide

/-- The pull payload's selector word (`transferFrom`, left-aligned). -/
def exPullSel : B256 := Bytes.toB256 [35, 184, 114, 221, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The pull payload's length word. -/
abbrev exPullLen : B256 :=
  Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] + Bytes.toB256 [32]

/-- The stack under the first payload identity copy. -/
def exPullS1 : List B256 := [Bytes.toB256 [4], Bytes.toB256 [4, 192], Bytes.toB256 [0]]

/-- The stack under the second payload identity copy. -/
def exPullS2 : List B256 :=
  (Bytes.toB256 [32] + exPullLen) ::
    ((((([Bytes.toB256 [0]].set 0 (Bytes.toB256 [0] + Bytes.toB256 [4])).set (↑(0 : Nat))
      (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32])).set (↑(0 : Nat))
      (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32])).set
      (↑(0 : Nat)) exPullLen).set (↑(0 : Nat)) (Bytes.toB256 [5, 32]))

/-- The memory at the first payload identity copy: length and selector staged. -/
def exPullM1 (M : Mem) : Mem :=
  (M.write 1216 (Bytes.toB256 [4]).toBytes).write 1248 exPullSel.toBytes

/-- The memory after the first identity copy. -/
def exPullI1 (M : Mem) : Mem :=
  ((exPullM1 M).extends [(1248, 4), (1344, 4)]).write 1344 (((exPullM1 M).read 1248 4).1.take 4)

/-- The memory at the second payload identity copy: caller, pool, `dx`, the length word. -/
def exPullM2 (M : Mem) (sevm : Sevm) : Mem :=
  ((((exPullI1 M).write 1348 sevm.caller.toB256.toBytes).write 1380
    sevm.currentTarget.toB256.toBytes).write 1412 (Sevm.dataWord sevm (Bytes.toB256 [68])).toBytes).write
    1312 exPullLen.toBytes

/-- The memory at the `transferFrom` call: the payload copied to `0x5e0`. -/
def exPullI2 (M : Mem) (sevm : Sevm) : Mem :=
  ((exPullM2 M sevm).extends [(1312, 132), (1504, 132)]).write 1504
    (((exPullM2 M sevm).read 1312 132).1.take 132)

/-- **The pull, forward, exactly**: `rx_ex_pull` over the relation-carrying premise, the
continuation also receiving the two payload identity copies' canonical successors, `E` at the
coin call's literal input, the raw tail's canonical successor and charge, and the literal memory. -/
theorem rx_ex_pull_core {sevm : Sevm} {b : Devm} {σ : Stor} {G R U : Nat} {Q : Outcome → Prop}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {B X : Nat → B256} {D C : B256}
    (_hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) {s c0 : Nat} (hsz : M.size = s)
    (hs : (s = 0x3c0 ∧ c0 = 31) ∨ (s = 0x460 ∧ c0 = 15)) (hF : ExFrame img B X D C)
    (hpull : MutCallOkAtE sevm W W' C (transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes) RawCallOk U 0x600 0x64 0x6c0 E)
    (hG : 4000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x6e0 → ExFrame img' B X D C →
      R ≤ g → g ≤ G → ∀ bI1 bI d : Devm,
      Devm.EqModGas bI1 (identityCallNext sevm b exPullS1 (exPullM1 M) (Bytes.toB256 [4, 192] +
        Bytes.toB256 [32]) (Bytes.toB256 [4]) (Bytes.toB256 [5, 32] + Bytes.toB256 [0] +
        Bytes.toB256 [32]) (Bytes.toB256 [4])) →
      Devm.EqModGas bI (identityCallNext sevm bI1 exPullS2 (exPullM2 M sevm) (Bytes.toB256 [5, 32])
        (Bytes.toB256 [32] + exPullLen) (Bytes.toB256 [5, 224]) (Bytes.toB256 [32] + exPullLen)) →
      E bI [] (exPullI2 M sevm) (G - (575 + c0)) d →
      d.gasLeft = g + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d [] d.memory exPullSite) →
      M' = vyRawMem d.memory 0x6a0 0x460 (min d.returnData.length 32) →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_2666_c12 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_2517_c11 Q := by
  have hc0 : c0 ≤ 31 := by omega
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 565 + c0 + 10 := ⟨G - 575 - c0, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x4c0) (c := c0) hR hW hsz rfl
    (by rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) ?_
  have hs' : memExtSize s 0x4c0 32 = 0x4e0 := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  clear hR hW hsz; intro hR hW hsz; rw [hs'] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x4e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x4e0 0x4e0 32 = 0x500 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  refine rxe_identityL (i := 0x4e0) (n := 0x4) (o := 0x540) (z := 0x4) (ext := 9) (X := 127) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 9 + 64 * idCost 0x4 = 1261 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz; intro bI1 M hsha hcan1 hMI1 hR hW hsz; rw [show memExtsSize 0x500 [(0x4e0, 0x4), (0x540, 0x4)] = 0x560 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [ex_pull_sel] at hR
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rxm_mload (o := 0x4c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap rfl ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreW (o := 0x544) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x560 0x544 32 = 0x580 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap rfl ·)
  xr (rx_pop ·)
  xr (rx_address (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreW (o := 0x564) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x580 0x564 32 = 0x5a0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap rfl ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreW (o := 0x584) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x5a0 0x584 32 = 0x5c0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap rfl ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0x520) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x5c0 0x520 32 = 0x5c0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_swap rfl ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rxm_mload (o := 0x520) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  refine rxe_identityL (i := 0x520) (n := 0x84) (o := 0x5e0) (z := 0x84) (ext := 19) (X := 149) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 19 + 64 * idCost 0x84 = 2039 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz; intro bI M hsha hcan2 hMI2 hR hW hsz; rw [show memExtsSize 0x5c0 [(0x520, 0x84), (0x5e0, 0x84)] = 0x680 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [transferFrom_copy] at hR
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have hdata : Region img3 0x5e0 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes ++ exPullData sevm) := by
    rw [hI]; exact Region.write_self _ _ _
  have hF3 : ExFrame img3 B X D C := hF.mono fun o v hv ho => by rw [hI]; wauto
  clear hI hF
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_25bc_c11
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x5e0) hR hsz rfl (by decide) (by hr) ·)
  rw [(Region.word hdata.left).read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x3a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  rw [hF3.coin.read]
  xr (rx_gas (by hr) ·)
  rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] +
      Bytes.toB256 [32] = (0x64 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [6, 0] = (0x600 : B256) by decide,
    show Bytes.toB256 [6, 192] = (0x6c0 : B256) by decide,
    show Bytes.toB256 [32] = (0x20 : B256) by decide]
  have hin : (M.read 0x600 0x64).1 = transferFromSel ++ sevm.caller.toB256.toBytes ++
      sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes := by
    rw [hR.read]
    exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
    hpull bI [] M g1 hL.w (by omega) (by omega) hin (by hr)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0x600 : B256).toNat = 0x600 by decide, show (0x64 : B256).toNat = 0x64 by decide,
    show (0x6c0 : B256).toNat = 0x6c0 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d [1] d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd, ex_pull_tail]
  have hext : (M.extends [(0x600, 0x64), (0x6c0, 0x20)]).size = 0x6e0 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0x6e0 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 : Mem.Reads d.memory (Bytes.writeAt img3 0x6c0 (d.returnData.take 0x20)) := by
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
    hdepth (by decide) ex_pull_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
    ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega) (by hr)
    ?_)
  · rw [show (Bytes.toB256 [exPullSite.lh, exPullSite.ll]).toNat + 32 = 0x6c0 by decide]
    intro j hj
    exact (rawCall_window hmem rfl j hj).2
  intro b' rd' hsha hcanT
  refine SFunc.runEx_iff_runExCut_nil.mp ?_
  rw [show (Bytes.toB256 [exPullSite.lh, exPullSite.ll]).toNat = 0x6a0 by decide,
    show (Bytes.toB256 [exPullSite.bh, exPullSite.bl]).toNat = 0x460 by decide]
  have hn32 : min d.returnData.length 32 ≤ 32 := by omega
  have hR6 : Mem.Reads (vyRawMem d.memory 0x6a0 0x460 (min d.returnData.length 32))
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img3 0x6c0 (d.returnData.take 0x20)) 0x6a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x460 ((Bytes.writeAt (Bytes.writeAt
        img3 0x6c0 (d.returnData.take 0x20)) 0x6a0
        (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0x6a0
        (min d.returnData.length 32 + 32) 0)) := by
    unfold vyRawMem
    rw [(hR5.write hW5 _ _).read]
    exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
  have hW6 : Mem.Wf (vyRawMem d.memory 0x6a0 0x460 (min d.returnData.length 32)) := by
    unfold vyRawMem; exact (hW5.write _ _).write _ _
  have hsz6 : (vyRawMem d.memory 0x6a0 0x460 (min d.returnData.length 32)).size = 0x6e0 := by
    unfold vyRawMem
    have h1 : (d.memory.write 0x6a0 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
        0x6e0 := by
      rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
    rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
  refine k b' _ _ G2 (hLd.sha hsha) hR6 hW6 hsz6 (hF3.mono fun o v hv ho => by wauto)
    (by omega) (by omega) bI1 bI d hcan1 ?_ ?_ hG2 hcanT rfl
  · rw [hMI1] at hcan2; exact hcan2
  · rw [hMI2, hMI1] at hE
    rw [show g1 + 565 + c0 + 10 - (575 + c0) = g1 by omega]; exact hE

/-- **The pull, forward** (`t_2517_c11` → `t_2666_c12`). -/
theorem rx_ex_pull {sevm : Sevm} {b : Devm} {σ : Stor} {G R U : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W W' : Devm → Prop} {B X : Nat → B256} {D C : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) {s c0 : Nat} (hsz : M.size = s)
    (hs : (s = 0x3c0 ∧ c0 = 31) ∨ (s = 0x460 ∧ c0 = 15)) (hF : ExFrame img B X D C)
    (hpull : CoinPullOkAt sevm W W' C (exDx sevm) U 0x600 0x6c0)
    (hG : 4000 + U + R ≤ G) (hGb : G + 2000 < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x6e0 → ExFrame img' B X D C →
      R ≤ g → g ≤ G → SFunc.RunEx cert.prog sevm (St b' [] M' g) t_2666_c12 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_2517_c11 Q :=
  rx_ex_pull_core hfork hdepth hL hW'c hR hW hsz hs hF hpull.withE hG hGb
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ _ _ _ _ => k b' M' img' g h1 h2 h3 h4 h5 h6 h7

end Blanc.Lift.Curve3Pool
