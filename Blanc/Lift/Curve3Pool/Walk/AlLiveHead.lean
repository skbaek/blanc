import Blanc.Lift.Curve3Pool.Walk.AlLiveD0
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityPull

/-!
# `add_liquidity`, forward: the pull loop's head

The loop's trees are unrolled per checker context (`c4`, `c40`, `c66` for a counter the checker
knows, `c41` after a pull); along the run they carry the same instructions. `alHead` is the
iteration head's path skeleton (`0x105d` → the amount test at `0x10b6`) with its off-path arms
as parameters, and each context's head is an instance (`t_105d_c4_eq`, …, by `rfl`).

`rx_al_head`: from the head with counter `i < 3`, `amounts[i]` is stored at `0x4e0` (on a first
deposit asserted positive), `coins[i]` at `0x500`, and the run goes on at the pull arm for a
positive amount and at the credit arm otherwise.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def alHead (a1 : SFunc) (a2 : SFunc) (a3 : SFunc) (a4 : SFunc) (a5 : SFunc) : SFunc :=
  (.dest (.next (.push [0x04] (by decide)) (.next (.push [0x04, 0xc0] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x10, 0x70] (by decide)) (.branch a1 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .calldataload) (.next (.push [0x04, 0xe0] (by decide)) (.next (.reg .mstore) (.next (.push [0x02, 0x40] (by decide)) (.next (.reg .mload) (.next (.reg .iszero) (.next (.reg .iszero) (.next (.push [0x10, 0x94] (by decide)) (.branch (.next (.push [0x00] (by decide)) (.next (.push [0x04, 0xe0] (by decide)) (.next (.reg .mload) (.next (.reg .gt) (.next (.push [0x10, 0x93] (by decide)) (.branch a2 (.dest (.dest (.next (.push [0x04, 0xc0] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x10, 0xa5] (by decide)) (.branch a3 (.dest (.next (.push [0x00] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256) (.next (.reg .add) (.next (.reg .sload) (.next (.push [0x05, 0x00] (by decide)) (.next (.reg .mstore) (.next (.push [0x00] (by decide)) (.next (.push [0x04, 0xe0] (by decide)) (.next (.reg .mload) (.next (.reg .gt) (.next (.reg .iszero) (.next (.push [0x12, 0xd6] (by decide)) (.branch a4 a5))))))))))))))))))))))))))))))))) (.dest (.next (.push [0x04, 0xc0] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x10, 0xa5] (by decide)) (.branch a3 (.dest (.next (.push [0x00] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256) (.next (.reg .add) (.next (.reg .sload) (.next (.push [0x05, 0x00] (by decide)) (.next (.reg .mstore) (.next (.push [0x00] (by decide)) (.next (.push [0x04, 0xe0] (by decide)) (.next (.reg .mload) (.next (.reg .gt) (.next (.reg .iszero) (.next (.push [0x12, 0xd6] (by decide)) (.branch a4 a5))))))))))))))))))))))))))))))))))))))))))))))))
theorem t_105d_c4_eq : t_105d_c4 = alHead .undefined t_108f_c4 .undefined t_10c2_c4 t_12d6_c4 := rfl
theorem t_105d_c40_eq : t_105d_c40 = alHead .undefined t_108f_c40 .undefined t_10c2_c40 t_12d6_c40 := rfl
theorem t_105d_c41_eq : t_105d_c41 = alHead t_106c_c41 t_108f_c41 t_10a1_c41 t_10c2_c41 t_12d6_c41 := rfl
theorem t_105d_c66_eq : t_105d_c66 = alHead .undefined t_108f_c66 .undefined t_10c2_c66 t_12d6_c66 := rfl


/-- **`MSTORE` inside the memory**: cost `3`, size kept. -/
theorem rxe_mstoreK {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat} {f : SFunc} {Q : Outcome → Prop} {i v : B256} {o s : Nat}
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s) (ho : i.toNat = o)
    (hin : o + 32 ≤ s ∧ s % 32 = 0)
    (k : ∀ M', Mem.Reads M' (Bytes.writeAt img o v.toBytes) → Mem.Wf M' → M'.size = s →
      SFunc.RunEx fs sevm (St b S M' G) f Q) :
    SFunc.RunEx fs sevm (St b (i :: v :: S) M (G + 3)) (.next (.reg .mstore) f) Q :=
  rxe_mstore hR hW hsz ho ⟨by rw [memExtSize_of_le hin.2 hin.1, Nat.sub_self]; rfl, hin.2⟩
    fun M' h1 h2 h3 => k M' h1 h2 (by rw [h3, memExtSize_of_le hin.2 hin.1])

/-- The pull loop's words survive writes off `[0x140, 0x4e0)`. -/
theorem al_pullImg_keep {img img' : Bytes} {i : Nat} {F AF A T D0 : B256} {old nv : Nat → B256}
    (h : AlPullImg img i F AF A T D0 old nv)
    (P : ∀ o w, WordAt img o w → 0x140 ≤ o → o + 32 ≤ 0x4e0 → WordAt img' o w) :
    AlPullImg img' i F AF A T D0 old nv where
  m0 := ⟨P _ _ h.m0.f0 (by decide) (by decide), P _ _ h.m0.f1 (by decide) (by decide),
    P _ _ h.m0.f2 (by decide) (by decide), P _ _ h.m0.fee (by decide) (by decide),
    P _ _ h.m0.adm (by decide) (by decide), P _ _ h.m0.amp (by decide) (by decide),
    P _ _ h.m0.supply (by decide) (by decide), P _ _ h.m0.d0 (by decide) (by decide),
    P _ _ h.m0.o0 (by decide) (by decide), P _ _ h.m0.o1 (by decide) (by decide),
    P _ _ h.m0.o2 (by decide) (by decide)⟩
  ctr := P _ _ h.ctr (by decide) (by decide)
  n0 := P _ _ h.n0 (by decide) (by decide)
  n1 := P _ _ h.n1 (by decide) (by decide)
  n2 := P _ _ h.n2 (by decide) (by decide)

/-- A positive amount passes `amount > 0`. -/
theorem al_pos_gt {x : B256} (h : x ≠ 0) : B256.gtCheck x (Bytes.toB256 [0]) ≠ 0 := by
  apply gtCheck_ne_zero_of_lt
  rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0]).toNat = 0 by decide]
  exact Nat.pos_of_ne_zero fun h' => h (B256.toNat_inj _ _ (by rw [h']; rfl))

/-- **The loop head, forward** (memory at `0x520`). -/
theorem rx_al_head {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256}
    {M : Mem} {img : Bytes} {G R i : Nat} {Q : Outcome → Prop} {F AF A T D0 : B256}
    {old nv : Nat → B256} {a1 a2 a3 a4 a5 : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hi : i < 3) (hL : ExLive sevm W b σ)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) {s : Nat} (hsz : M.size = s) (hs : 0x520 ≤ s)
    (hs32 : s % 32 = 0)
    (hm : AlPullImg img i F AF A T D0 old nv) (hT0 : T = 0 → alAmt sevm i ≠ 0)
    (hG : 2500 + R ≤ G) (hroom : S.length + 12 < 1024)
    (kp : alAmt sevm i ≠ 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = s →
      AlPullImg img' i F AF A T D0 old nv → WordAt img' 0x4e0 (alAmt sevm i) →
      WordAt img' 0x500 (coinAt σ i) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) a4 Q)
    (kz : alAmt sevm i = 0 → ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = s →
      AlPullImg img' i F AF A T D0 old nv → WordAt img' 0x4e0 (alAmt sevm i) →
      WordAt img' 0x500 (coinAt σ i) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) a5 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) (alHead a1 a2 a3 a4 a5) Q := by
  by_cases hTz : T = 0
  · obtain ⟨g1, rfl⟩ : ∃ g, G = g + 188 := ⟨G - 188, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hm.ctr) (by hrs) ·)
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
    refine rxe_mstoreK (o := 0x4e0) hR hW hsz rfl ⟨by omega, hs32⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x240) (v := T) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hm.m0.supply) (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_zero' (by rw [hTz]; decide) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0x4e0) hR hsz rfl ⟨by omega, hs32⟩ (by hrs) ·); try wsimp
    xr (rx_gt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (al_pos_gt (hT0 hTz)) ·)
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hm.ctr) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreK (o := 0xc0) hR hW hsz rfl ⟨by omega, hs32⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by omega, hs32⟩ (by hrs) (by decide) ·)
    rw [keccak_zero]
    xr (rx_add (by hrs) ·)
    refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
    obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 34 := ⟨g2 - 34, by omega⟩
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreK (o := 0x500) hR hW hsz rfl ⟨by omega, hs32⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0x4e0) hR hsz rfl ⟨by omega, hs32⟩ (by hrs) ·); try wsimp
    xr (rx_gt rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    subst hv2
    by_cases ha : alAmt sevm i = 0
    · have ha' : Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 i + Bytes.toB256 [4]) = 0 := ha
      xr (rx_branch_succ (by rw [ha']; decide) ·)
      exact kz ha _ M _ g3 hL hR hW hsz (al_pullImg_keep hm fun o w hw h1 h2 => by wauto) (by wauto) (by wauto) (by omega) (by omega)
    · xr (rx_branch_zero' (al_supply_test ha) ·)
      exact kp ha _ M _ g3 hL hR hW hsz (al_pullImg_keep hm fun o w hw h1 h2 => by wauto) (by wauto) (by wauto) (by omega) (by omega)
  · obtain ⟨g1, rfl⟩ : ∃ g, G = g + 162 := ⟨G - 162, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hm.ctr) (by hrs) ·)
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
    refine rxe_mstoreK (o := 0x4e0) hR hW hsz rfl ⟨by omega, hs32⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x240) (v := T) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hm.m0.supply) (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (iszero_eqCheck_ne hTz) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hm.ctr) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreK (o := 0xc0) hR hW hsz rfl ⟨by omega, hs32⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by omega, hs32⟩ (by hrs) (by decide) ·)
    rw [keccak_zero]
    xr (rx_add (by hrs) ·)
    refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
    obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 34 := ⟨g2 - 34, by omega⟩
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreK (o := 0x500) hR hW hsz rfl ⟨by omega, hs32⟩ ?_; clear hR hW hsz M; intro M hR hW hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0x4e0) hR hsz rfl ⟨by omega, hs32⟩ (by hrs) ·); try wsimp
    xr (rx_gt rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    subst hv2
    by_cases ha : alAmt sevm i = 0
    · have ha' : Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 i + Bytes.toB256 [4]) = 0 := ha
      xr (rx_branch_succ (by rw [ha']; decide) ·)
      exact kz ha _ M _ g3 hL hR hW hsz (al_pullImg_keep hm fun o w hw h1 h2 => by wauto) (by wauto) (by wauto) (by omega) (by omega)
    · xr (rx_branch_zero' (al_supply_test ha) ·)
      exact kp ha _ M _ g3 hL hR hW hsz (al_pullImg_keep hm fun o w hw h1 h2 => by wauto) (by wauto) (by wauto) (by omega) (by omega)

/-- The words before the loop survive writes off `[0x140, 0x360)`. -/
theorem al_mem0_keep {img img' : Bytes} {F AF A T D0 : B256} {old : Nat → B256}
    (h : AlMem0 img F AF A T D0 old)
    (P : ∀ o w, WordAt img o w → 0x140 ≤ o → o + 32 ≤ 0x360 → WordAt img' o w) :
    AlMem0 img' F AF A T D0 old :=
  ⟨P _ _ h.f0 (by decide) (by decide), P _ _ h.f1 (by decide) (by decide),
    P _ _ h.f2 (by decide) (by decide), P _ _ h.fee (by decide) (by decide),
    P _ _ h.adm (by decide) (by decide), P _ _ h.amp (by decide) (by decide),
    P _ _ h.supply (by decide) (by decide), P _ _ h.d0 (by decide) (by decide),
    P _ _ h.o0 (by decide) (by decide), P _ _ h.o1 (by decide) (by decide),
    P _ _ h.o2 (by decide) (by decide)⟩

/-- **Before the loop, forward** (`t_1031_c4` → the head; memory from `0x360`): `new_balances =
old_balances`, counter `0`. -/
theorem rx_al_init0 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G : Nat}
    {Q : Outcome → Prop} {F AF A T D0 : B256} {old : Nat → B256}
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x360)
    (hm : AlMem0 img F AF A T D0 old) (hroom : S.length + 8 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes), Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x4e0 →
      AlPullImg img' 0 F AF A T D0 old old →
      SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M' G) t_105d_c4 Q) :
    SFunc.RunEx cert.prog sevm (St b S M (G + 129)) t_1031_c4 Q := by
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x300) (v := old 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.o0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x460) (c := 31) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x360 0x460 32 = 0x480 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := old 1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.o1) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x480) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x480 0x480 32 = 0x4a0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := old 2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.o2) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x4a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x4a0 0x4a0 32 = 0x4c0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x4c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x4c0 0x4c0 32 = 0x4e0 by decide] at hsz
  xr (rx_add (by hrs) ·)
  rw [show Bytes.toB256 [3] + Bytes.toB256 [0] = (3 : B256) by decide,
    show Bytes.toB256 [4, 192] = (0x4c0 : B256) by decide]
  exact k M _ hR hW hsz ⟨al_mem0_keep hm fun o w hw h1 h2 => by wauto, by wauto, by wauto, by wauto,
    by wauto⟩

/-- **Before the loop, forward** (`t_1031_c4` → the head; memory from `0x520`): `new_balances =
old_balances`, counter `0`. -/
theorem rx_al_init {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes} {G : Nat}
    {Q : Outcome → Prop} {F AF A T D0 : B256} {old : Nat → B256}
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x520)
    (hm : AlMem0 img F AF A T D0 old) (hroom : S.length + 8 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes), Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x520 →
      AlPullImg img' 0 F AF A T D0 old old →
      SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M' G) t_105d_c4 Q) :
    SFunc.RunEx cert.prog sevm (St b S M (G + 92)) t_1031_c4 Q := by
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x300) (v := old 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.o0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x460 32 = 0x520 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := old 1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.o1) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x480) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x480 32 = 0x520 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x340) (v := old 2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.o2) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x4a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x4a0 32 = 0x520 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x4c0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x520 0x4c0 32 = 0x520 by decide] at hsz
  xr (rx_add (by hrs) ·)
  rw [show Bytes.toB256 [3] + Bytes.toB256 [0] = (3 : B256) by decide,
    show Bytes.toB256 [4, 192] = (0x4c0 : B256) by decide]
  exact k M _ hR hW hsz ⟨al_mem0_keep hm fun o w hw h1 h2 => by wauto, by wauto, by wauto, by wauto,
    by wauto⟩

/-- **The loop head on a first deposit, iteration `0`, forward** (memory at `0x4e0`; the amount
must be positive). -/
theorem rx_al_head0 {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256}
    {M : Mem} {img : Bytes} {G R : Nat} {Q : Outcome → Prop} {F AF A T D0 : B256}
    {old nv : Nat → B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x4e0)
    (hm : AlPullImg img 0 F AF A T D0 old nv) (hTz : T = 0) (hT0 : T = 0 → alAmt sevm 0 ≠ 0)
    (hG : 2500 + R ≤ G) (hroom : S.length + 12 < 1024)
    (kp : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' σ → Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x520 →
      AlPullImg img' 0 F AF A T D0 old nv → WordAt img' 0x4e0 (alAmt sevm 0) →
      WordAt img' 0x500 (coinAt σ 0) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' (3 :: 0x4c0 :: S) M' g) t_10c2_c4 Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) t_105d_c4 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 192 := ⟨G - 192, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.ctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three (i := 0) (by decide))) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x4e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x4e0 0x4e0 32 = 0x500 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x240) (v := T) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.m0.supply) (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_zero' (by rw [hTz]; decide) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x4e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (al_pos_gt (hT0 hTz)) ·)
  xr (rx_dest ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm.ctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three (i := 0) (by decide))) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x500 0xc0 32 = 0x500 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
  rw [keccak_zero]
  xr (rx_add (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 37 := ⟨g2 - 37, by omega⟩
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x500) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x500 0x500 32 = 0x520 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x4e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_zero' (al_supply_test (hT0 hTz)) ·)
  subst hv2
  exact kp _ M _ g3 hL hR hW hsz (al_pullImg_keep hm fun o w hw h1 h2 => by wauto) (by wauto) (by wauto)
    (by omega) (by omega)

end Blanc.Lift.Curve3Pool
