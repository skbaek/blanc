import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveDy

/-!
# `exchange`, forward: the admin share, the two balance stores and the push payload

`rx_ex_store` is the forward twin of `xa_ex_store` and the first half of `xa_ex_push`
(`t_296f_c1174` → `t_2b49_c1174`): the admin share, `balances[i] = old[i] + dx_w_fee`,
`balances[j] = old[j] - dy - dy_admin_fee` (both checked), and the `transfer` payload built at
`0xaa0` with two identity copies.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The selector the push payload's first identity copy moves. -/
theorem ex_push_sel (img : Bytes) :
    ((Bytes.writeAt img 0xa60 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes).sliceD 0xa60 4 0).take 4 =
      transferSel := by
  rw [(WordAt.write_self _ _ _).prefix (by decide)]; decide

/-- The push payload's selector word (`transfer`, left-aligned). -/
def exPushSelW : B256 := Bytes.toB256 [169, 5, 156, 187, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The push payload's length word. -/
abbrev exPushLen : B256 := Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32]

/-- The base after the admin-fee load and the two balance stores. -/
def exStoreBase (sevm : Sevm) (b : Devm) (vi vj : B256) : Devm :=
  afterSstore sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [3]))
    (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4])) vi)
    (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) vj

/-- The storage charges of the stores stage, each at its actual intermediate base. -/
def exStoreCost (sevm : Sevm) (b : Devm) (vi vj : B256) : Nat :=
  sloadCost sevm b (Bytes.toB256 [3]) +
    sstoreCost sevm (afterSload sevm b (Bytes.toB256 [3]))
      (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4])) vi +
    sstoreCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [3]))
      (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4])) vi)
      (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36])) vj

/-- The stack under the push payload's first identity copy. -/
def exStoreS1 : List B256 := [Bytes.toB256 [4], Bytes.toB256 [10, 64], Bytes.toB256 [0]]

/-- The stack under the push payload's second identity copy. -/
def exStoreS2 : List B256 := [Bytes.toB256 [32] + exPushLen, Bytes.toB256 [10, 160]]

/-- The memory at the first push-payload identity copy: the admin share, the key scratch, the
length and selector. -/
def exStoreM1 (M : Mem) (sevm : Sevm) (fee af : B256) : Mem :=
  M.write 2592 (exAdm0 fee af).toBytes |>.write 2592 (exAdm fee af (exRate (exJ sevm).toNat)).toBytes
    |>.write 192 (Bytes.toB256 [1]).toBytes |>.write 192 (Bytes.toB256 [1]).toBytes
    |>.write 2624 (Bytes.toB256 [4]).toBytes |>.write 2656 exPushSelW.toBytes

/-- The memory after the first identity copy. -/
def exStoreI1 (M : Mem) (sevm : Sevm) (fee af : B256) : Mem :=
  ((exStoreM1 M sevm fee af).extends [(2656, 4), (2752, 4)]).write 2752
    (((exStoreM1 M sevm fee af).read 2656 4).1.take 4)

/-- The memory at the second push-payload identity copy: caller, `dy`, the length word. -/
def exStoreM2 (M : Mem) (sevm : Sevm) (fee af dy : B256) : Mem :=
  (((exStoreI1 M sevm fee af).write 2756 sevm.caller.toB256.toBytes).write 2788 dy.toBytes).write
    2720 exPushLen.toBytes

/-- The memory after the second identity copy: the payload at `0xb40`. -/
def exStoreI2 (M : Mem) (sevm : Sevm) (fee af dy : B256) : Mem :=
  ((exStoreM2 M sevm fee af dy).extends [(2720, 100), (2880, 100)]).write 2880
    (((exStoreM2 M sevm fee af dy).read 2720 100).1.take 100)

/-- **The stores and the push payload, forward, exactly**: `rx_ex_store`, the continuation also
receiving the exact charge (`1225` plus the admin-fee load and the two balance stores at their
actual bases), the two payload identity copies' canonical successors and the literal memory. -/
theorem rx_ex_store_core {sevm : Sevm} {b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C dyOut dyFee : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa00)
    (hF : ExFrame img B X D C) (hout : WordAt img 0x920 dyOut) (hfee : WordAt img 0x940 dyFee)
    (hma : dyFee * σ.get adminFeeSlot / dyFee = σ.get adminFeeSlot ∨ dyFee = 0)
    (hmap : exAdm0 dyFee (σ.get adminFeeSlot) * exR0 / exAdm0 dyFee (σ.get adminFeeSlot) = exR0 ∨
      exAdm0 dyFee (σ.get adminFeeSlot) = 0)
    (hbi : ¬ B (exI sevm).toNat + D < B (exI sevm).toNat)
    (hbj1 : ¬ B (exJ sevm).toNat < dyOut)
    (hbj2 : ¬ B (exJ sevm).toNat - dyOut <
      exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))
    (hG : 60000 + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' ((σ.set (balancesBase + exI sevm) (B (exI sevm).toNat + D)).set
        (balancesBase + exJ sevm) (B (exJ sevm).toNat - dyOut -
          exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xbc0 →
      Region img' 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ exPushData sevm dyOut) → WordAt img' 0x920 dyOut →
      R ≤ g → g ≤ G →
      G = g + 1225 + exStoreCost sevm b (B (exI sevm).toNat + D)
        (B (exJ sevm).toNat - dyOut - exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat)) →
      ∀ bI1 : Devm, Devm.EqModGas bI1 (identityCallNext sevm (exStoreBase sevm b
        (B (exI sevm).toNat + D) (B (exJ sevm).toNat - dyOut -
          exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))) exStoreS1
        (exStoreM1 M sevm dyFee (σ.get adminFeeSlot)) (Bytes.toB256 [10, 64] + Bytes.toB256 [32])
        (Bytes.toB256 [4]) (Bytes.toB256 [10, 160] + Bytes.toB256 [0] + Bytes.toB256 [32])
        (Bytes.toB256 [4])) →
      Devm.EqModGas b' (identityCallNext sevm bI1 exStoreS2
        (exStoreM2 M sevm dyFee (σ.get adminFeeSlot) dyOut) (Bytes.toB256 [10, 160])
        (Bytes.toB256 [32] + exPushLen) (Bytes.toB256 [11, 64]) (Bytes.toB256 [32] + exPushLen)) →
      M' = exStoreI2 M sevm dyFee (σ.get adminFeeSlot) dyOut →
      SFunc.RunEx cert.prog sevm (St b' [Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] +
        Bytes.toB256 [32] + Bytes.toB256 [32]), Bytes.toB256 [10, 160]] M' g) t_2b49_c1174 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_296f_c1174 Q := by
  have hrj := hF.rate _ hj
  have hoi := hF.old _ hi
  have hoj := hF.old _ hj
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 10 := ⟨G - 10, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x940) hR hsz rfl (by decide) (by hr) ·)
  rw [hfee.read]
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 hx_g2; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  rw [adminFeeSlot_lit] at hv2; subst hv2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 477 := ⟨g2 - 477, by omega⟩
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_or rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_mulGuard hma) ·)
  -- tree t_298a_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  -- tree t_29a2_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0xa20) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa00 0xa20 32 = 0xa40 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0xa20) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_or rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_mulGuard hmap) ·)
  -- tree t_29cd_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_29e7_c1174
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mloadW (v := exRate (exJ sevm).toNat) (o := 0x140 + 32 * (exJ sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [1, 0x40]) hj (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoH hrj) (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ exRate_ne ·)
  -- tree t_29f7_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_div rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0xa20) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa40 0xa20 32 = 0xa40 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hi) ·)
  -- tree t_2a14_c1174
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mloadW (v := B (exI sevm).toNat) (o := 0x1a0 + 32 * (exI sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [1, 0xa0]) hi (by decide) (by decide)) ⟨by omega, by decide⟩ ((hoi.write_other (by simp only [B256.length_toBytes]; omega)).write_other (by simp only [B256.length_toBytes]; omega)) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x380) hR hsz rfl (by decide) (by hr) ·); try wsimp
  try rw [hF.dx.read]
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_geGuard hbi) ·)
  -- tree t_2a2c_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hi) ·)
  -- tree t_2a43_c1174
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa40 0xc0 32 = 0xa40 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  refine rxe_sstoreVX hfork hstatic (by omega) ?_; intro g4 b4 hb4 hg41 hg42 hx_g4; replace hL := hL.sstoreE hb4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 231 := ⟨g4 - 231, by omega⟩
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_2a62_c1174
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_mul rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mloadW (v := B (exJ sevm).toNat) (o := 0x1a0 + 32 * (exJ sevm).toNat) hR hsz (ex_off (bw := Bytes.toB256 [1, 0xa0]) hj (by decide) (by decide)) ⟨by omega, by decide⟩ (by wautoH hoj) (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x920) hR hsz rfl (by decide) (by hr) ·); try wsimp
  try rw [hout.read]
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_geGuard hbj1) ·)
  -- tree t_2a78_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0xa20) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_geGuard hbj2) ·)
  -- tree t_2a90_c1174
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_sub (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hj) ·)
  -- tree t_2aa7_c1174
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa40 0xc0 32 = 0xa40 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  refine rxe_sstoreVX hfork hstatic (by omega) ?_; intro g6 b6 hb6 hg61 hg62 hx_g6; replace hL := hL.sstoreE hb6
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 507 := ⟨g6 - 507, by omega⟩
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0xa40) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa40 0xa40 32 = 0xa60 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0xa60) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xa60 0xa60 32 = 0xa80 by decide] at hsz
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
  refine rxe_identityL (i := 0xa60) (n := 0x4) (o := 0xac0) (z := 0x4) (ext := 10) (X := 128) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 10 + 64 * idCost 0x4 = 1262 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz; intro bI1 M hsha hcan1 hMI1 hR hW hsz; rw [show memExtsSize 0xa80 [(0xa60, 0x4), (0xac0, 0x4)] = 0xae0 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [ex_push_sel] at hR
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rxm_mload (o := 0xa40) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap2 ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_caller (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreW (o := 0xac4) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xae0 0xac4 32 = 0xb00 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x920) hR hsz rfl (by decide) (by hr) ·); try wsimp
  try rw [hout.read]
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreW (o := 0xae4) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xb00 0xae4 32 = 0xb20 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreW (o := 0xaa0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xb20 0xaa0 32 = 0xb20 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rxm_mload (o := 0xaa0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_gas (by hr) ·)
  refine rxe_identityL (i := 0xaa0) (n := 0x64) (o := 0xb40) (z := 0x64) (ext := 17) (X := 144) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 17 + 64 * idCost 0x64 = 1845 := (by decide); omega) (by omega) (by hr) ?_; clear hR hW hsz; intro bI M hsha hcan2 hMI2 hR hW hsz; rw [show memExtsSize 0xb20 [(0xaa0, 0x64), (0xb40, 0x64)] = 0xbc0 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
  rw [transfer_copy2] at hR
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by decide) ·)
  obtain ⟨img3, hR, hI⟩ := Mem.Reads.forget hR
  have hdata : Region img3 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
      Bytes.toB256 [32]).toBytes ++ exPushData sevm dyOut) := by
    rw [hI]; exact Region.write_self _ _ _
  have hout3 : WordAt img3 0x920 dyOut := by rw [hI]; wautoH hout
  have hc : exStoreCost sevm b (B (exI sevm).toNat + D)
      (B (exJ sevm).toNat - dyOut - exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat)) =
      sloadCost sevm b (Bytes.toB256 [3]) +
        sstoreCost sevm b2 (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4]))
          (B (exI sevm).toNat + D) +
        sstoreCost sevm b4 (balancesBase + Sevm.dataWord sevm (Bytes.toB256 [36]))
          (B (exJ sevm).toNat - dyOut - dyFee * σ.get adminFeeSlot / Bytes.toB256 [2, 84, 11, 228, 0] *
            Bytes.toB256 [13, 224, 182, 179, 167, 100, 0, 0] / exRate (exJ sevm).toNat) := by
    rw [hb4, hb2]; rfl
  refine k bI M img3 g7 hL hR hW hsz hdata hout3 (by omega) (by omega) (by omega) bI1 ?_ ?_ ?_
  · rw [hb6, hb4, hb2] at hcan1; exact hcan1
  · rw [hMI1] at hcan2; exact hcan2
  · rw [hMI2, hMI1]; rfl

/-- **The stores and the push payload, forward.** -/
theorem rx_ex_store {sevm : Sevm} {b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C dyOut dyFee : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa00)
    (hF : ExFrame img B X D C) (hout : WordAt img 0x920 dyOut) (hfee : WordAt img 0x940 dyFee)
    (hma : dyFee * σ.get adminFeeSlot / dyFee = σ.get adminFeeSlot ∨ dyFee = 0)
    (hmap : exAdm0 dyFee (σ.get adminFeeSlot) * exR0 / exAdm0 dyFee (σ.get adminFeeSlot) = exR0 ∨
      exAdm0 dyFee (σ.get adminFeeSlot) = 0)
    (hbi : ¬ B (exI sevm).toNat + D < B (exI sevm).toNat)
    (hbj1 : ¬ B (exJ sevm).toNat < dyOut)
    (hbj2 : ¬ B (exJ sevm).toNat - dyOut <
      exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))
    (hG : 60000 + R ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' ((σ.set (balancesBase + exI sevm) (B (exI sevm).toNat + D)).set
        (balancesBase + exJ sevm) (B (exJ sevm).toNat - dyOut -
          exAdm dyFee (σ.get adminFeeSlot) (exRate (exJ sevm).toNat))) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xbc0 →
      Region img' 0xb40 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ exPushData sevm dyOut) → WordAt img' 0x920 dyOut →
      R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' [Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] +
        Bytes.toB256 [32] + Bytes.toB256 [32]), Bytes.toB256 [10, 160]] M' g) t_2b49_c1174 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_296f_c1174 Q :=
  rx_ex_store_core hfork hstatic hdepth hL hi hj hR hW hsz hF hout hfee hma hmap hbi hbj1 hbj2 hG hGb
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ => k b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8

end Blanc.Lift.Curve3Pool
