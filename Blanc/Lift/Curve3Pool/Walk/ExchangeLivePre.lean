import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveFront

/-!
# `exchange`, forward: the guards, `rates`, `old_balances`, up to `_xp_mem`

`rx_ex_pre` is `xa_ex_pre`'s forward twin: from the arm's body (`0x2319`) to the call idiom of
`_xp_mem(old_balances)` at `0x2452`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `int128` upper clamp passes for an index below `3`. -/
theorem ex_clamp_hi {x : B256} (h : x.toNat < 3) :
    B256.eqCheck (B256.sgtCheck x (Bytes.toB256 vyC40)) 0 ≠ 0 := by
  rw [← toB256_toNat x]
  obtain h' | h' | h' : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 := by omega
  all_goals rw [h']; decide

/-- The `int128` lower clamp passes for an index below `3`. -/
theorem ex_clamp_lo {x : B256} (h : x.toNat < 3) :
    B256.eqCheck (B256.sltCheck x (Bytes.toB256 vyC60)) 0 ≠ 0 := by
  rw [← toB256_toNat x]
  obtain h' | h' | h' : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 := by omega
  all_goals rw [h']; decide

/-- Across an `SSTORE` of the pool. -/
theorem ExBase.sstore {sevm : Sevm} {b0 b : Devm} {σ : Stor} (h : ExBase sevm b0 b σ)
    (k v : B256) : ExBase sevm b0 (afterSstore sevm b k v) (σ.set k v) :=
  ⟨fun x => by simp only [afterSstore_getStor_self, Stor.get_set_ite, h.stor],
    by rw [afterSstore_getCode]; exact h.code, by rw [afterSstore_output]; exact h.output,
    h.id.afterSstore k v⟩

/-- The base `exchange`'s prefix leaves after its lock load and store and the `is_killed` load. -/
def exPreLockBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
    (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15])

/-- The base `exchange`'s prefix leaves: the lock loaded and set, `is_killed` and the three
`balances` loaded. -/
def exPreBase (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm (exPreLockBase sevm b) balancesBase)
    (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2])

/-- The storage charges of `exchange`'s prefix, each at the actual intermediate base. -/
def exPreCost (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
    sstoreCost sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
    sloadCost sevm (afterSstore sevm (afterSload sevm b (Bytes.toB256 [255, 255, 255]))
      (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1])) (Bytes.toB256 [15]) +
    sloadCost sevm (exPreLockBase sevm b) balancesBase +
    sloadCost sevm (afterSload sevm (exPreLockBase sevm b) balancesBase)
      (balancesBase + Bytes.toB256 [1]) +
    sloadCost sevm (afterSload sevm (afterSload sevm (exPreLockBase sevm b) balancesBase)
      (balancesBase + Bytes.toB256 [1])) (balancesBase + Bytes.toB256 [2])

/-- The literal memory `exchange`'s prefix leaves over its entry memory: `rates` at
`0x140 … 0x180`, `old_balances` at `0x1a0 … 0x1e0` (the key scratch at `0xc0` before each),
the three reads past the end at `0x200 … 0x240`, `old_balances` again at `0x280 … 0x2c0`. -/
def exPreMem (M : Mem) (σ : Stor) : Mem :=
  M.write 0x140 exR0.toBytes |>.write 0x160 exR1.toBytes |>.write 0x180 exR1.toBytes
    |>.write 0xc0 (Bytes.toB256 [1]).toBytes |>.write 0x1a0 (balAt σ 0).toBytes
    |>.write 0xc0 (Bytes.toB256 [1]).toBytes |>.write 0x1c0 (balAt σ 1).toBytes
    |>.write 0xc0 (Bytes.toB256 [1]).toBytes |>.write 0x1e0 (balAt σ 2).toBytes
    |>.extend 0x200 32 |>.extend 0x220 32 |>.extend 0x240 32
    |>.write 0x280 (balAt σ 0).toBytes |>.write 0x2a0 (balAt σ 1).toBytes
    |>.write 0x2c0 (balAt σ 2).toBytes

/-- **`exchange` up to `_xp_mem`, forward, exactly**: `rx_ex_pre`, the continuation also receiving
the exact charge (`661` plus the actual storage charges `exPreCost`), the literal base
`exPreBase`, the literal memory `exPreMem` and the three words read past the end. -/
theorem rx_ex_pre_core {sevm : Sevm} {b0 b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hB : ExBase sevm b0 b σ) (hWc : WClosed sevm W)
    (hWb : W b) (hlock : σ.get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : σ.get isKilledSlot = 0) (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xc0) (hcl : VyClamps img)
    (hG : 33261 + R ≤ G)
    (k : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g : Nat) (z0 z1 z2 : B256),
      ExBase sevm b0 b1 (σ.set lockSlot 1) → W b1 → Mem.Reads M1 img1 → Mem.Wf M1 →
      M1.size = 0x2e0 → R ≤ g → g + 600 ≤ G →
      G = g + 661 + exPreCost sevm b → b1 = exPreBase sevm b → M1 = exPreMem M σ →
      z0 = Bytes.toB256 (img.sliceD 0x200 32 0) → z1 = Bytes.toB256 (img.sliceD 0x220 32 0) →
      z2 = Bytes.toB256 (img.sliceD 0x240 32 0) →
      SFunc.RunEx cert.prog sevm (St b1 [balAt σ 0, balAt σ 1, balAt σ 2, z2, z1, z0,
        balAt σ 2, balAt σ 1, balAt σ 0, exR1, exR1, exR0, Bytes.toB256 [2, 0]] M1 g)
        (pcCallTree 0x2452 0x03 0xa1 34 t_2458_c0) Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_2319_c0 Q := by
  have e40 : Bytes.toB256 (img.sliceD 64 32 0) = Bytes.toB256 vyC40 := by
    rw [hcl.2.1, B256.toB256_toBytes]
  have e60 : Bytes.toB256 (img.sliceD 96 32 0) = Bytes.toB256 vyC60 := by
    rw [hcl.2.2.1, B256.toB256_toBytes]
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 3 := ⟨G - 3, by omega⟩
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 hx_g2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 23 := ⟨g2 - 23, by omega⟩
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hv2, getStorVal_eq, lockSlot_lit, hB.stor, hlock]; decide) ·)
  -- tree t_2327_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_sstoreVX hfork hstatic (by omega) ?_; intro g4 b4 hb4 hg41 hg42 hx_g4
  obtain ⟨g5, rfl⟩ : ∃ g, g4 = g + 172 := ⟨g4 - 172, by omega⟩
  xr (rx_callvalue (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hval]; decide) ·)
  -- tree t_2339_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x60) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x40) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_swap rfl ·)
  xr (rx_sgt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [e40]; exact ex_clamp_hi hi) ·)
  -- tree t_234f_c0
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_swap rfl ·)
  xr (rx_swap rfl ·)
  xr (rx_slt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [e60]; exact ex_clamp_lo hi) ·)
  -- tree t_235d_c0
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x60) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x40) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_swap rfl ·)
  xr (rx_sgt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [e40]; exact ex_clamp_hi hj) ·)
  -- tree t_2374_c0
  xr (rx_dest ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_swap rfl ·)
  xr (rx_swap rfl ·)
  xr (rx_slt rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [e60]; exact ex_clamp_lo hj) ·)
  -- tree t_2382_c0
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g6 b6 v6 hb6 hv6 hg61 hg62 hx_g6
  obtain ⟨g7, rfl⟩ : ∃ g, g6 = g + 139 := ⟨g6 - 139, by omega⟩
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (by rw [hv6, hb4, hb2, isKilledSlot_lit, getStorVal_afterSstore_ne (by decide), getStorVal_afterSload, getStorVal_eq, hB.stor, hkill]; decide) ·)
  -- tree t_2390_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x140) (c := 18) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0xc0 0x140 32 = 0x160 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x160) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x160 0x160 32 = 0x180 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x180) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x180 0x180 32 = 0x1a0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1a0 0xc0 32 = 0x1a0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g8 b8 v8 hb8 hv8 hg81 hg82 hx_g8
  obtain ⟨g9, rfl⟩ : ∃ g, g8 = g + 66 := ⟨g8 - 66, by omega⟩
  xr (rx_dup rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x1a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1a0 0x1a0 32 = 0x1c0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1c0 0xc0 32 = 0x1c0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g10 b10 v10 hb10 hv10 hg101 hg102 hx_g10
  obtain ⟨g11, rfl⟩ : ∃ g, g10 = g + 72 := ⟨g10 - 72, by omega⟩
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x1c0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1c0 0x1c0 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1e0 0xc0 32 = 0x1e0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_one]
  xr (rx_add (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro g12 b12 v12 hb12 hv12 hg121 hg122 hx_g12
  obtain ⟨g13, rfl⟩ : ∃ g, g12 = g + 186 := ⟨g12 - 186, by omega⟩
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x1e0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x1e0 0x1e0 32 = 0x200 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x160) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x180) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x1e0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  refine rxe_mloadXL (o := 0x200) (c := 6) hR hW hsz rfl (by decide) (by hr) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x200 0x200 32 = 0x220 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mloadXL (o := 0x220) (c := 6) hR hW hsz rfl (by decide) (by hr) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x220 0x220 32 = 0x240 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mloadXL (o := 0x240) (c := 6) hR hW hsz rfl (by decide) (by hr) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x240 0x240 32 = 0x260 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rxm_mload (o := 0x1a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x280) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x260 0x280 32 = 0x2a0 by decide] at hsz
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mload (o := 0x1c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x2a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x2a0 0x2a0 32 = 0x2c0 by decide] at hsz
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mload (o := 0x1e0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x2c0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x2c0 0x2c0 32 = 0x2e0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2c0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x2a0) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_push rfl (by hr) ·)
  xr (rxm_mload (o := 0x280) hR hsz rfl (by decide) (by hr) ·); try wsimp
  have hB4 : ExBase sevm b0 b4 (σ.set lockSlot 1) := by
    rw [hb4, hb2, lockSlot_lit, show Bytes.toB256 [1] = (1 : B256) by decide]
    exact (hB.sload _).sstore _ _
  have hW4 : W b4 := by rw [hb4, hb2]; exact hWc.sstore _ _ _ (hWc.sload _ _ hWb)
  have hB12 : ExBase sevm b0 b12 (σ.set lockSlot 1) := by
    rw [hb12, hb10, hb8, hb6]; exact (((hB4.sload _).sload _).sload _).sload _
  have hW12 : W b12 := by
    rw [hb12, hb10, hb8, hb6]
    exact hWc.sload _ _ (hWc.sload _ _ (hWc.sload _ _ (hWc.sload _ _ hW4)))
  have e8 : v8 = balAt σ 0 := by
    rw [hv8, getStorVal_eq, hb6, afterSload_getStor, hB4.stor, Stor.get_set_ne _ (by decide)]
    rfl
  have e10 : v10 = balAt σ 1 := by
    rw [hv10, getStorVal_eq, hb8, afterSload_getStor, hb6, afterSload_getStor, hB4.stor,
      Stor.get_set_ne _ (by decide)]
    rfl
  have e12 : v12 = balAt σ 2 := by
    rw [hv12, getStorVal_eq, hb10, afterSload_getStor, hb8, afterSload_getStor, hb6,
      afterSload_getStor, hB4.stor, Stor.get_set_ne _ (by decide)]
    rfl
  rw [e8, e10, e12] at hR hW hsz ⊢
  have hc : exPreCost sevm b = sloadCost sevm b (Bytes.toB256 [255, 255, 255]) +
      sstoreCost sevm b2 (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [1]) +
      sloadCost sevm b4 (Bytes.toB256 [15]) + sloadCost sevm b6 balancesBase +
      sloadCost sevm b8 (balancesBase + Bytes.toB256 [1]) +
      sloadCost sevm b10 (balancesBase + Bytes.toB256 [2]) := by
    rw [hb10, hb8, hb6, hb4, hb2]; rfl
  refine k b12 _ _ g13 _ _ _ hB12 hW12 hR hW hsz (by omega) (by omega) (by omega) ?_ rfl rfl rfl
    rfl
  rw [hb12, hb10, hb8, hb6, hb4, hb2]; rfl

/-- **`exchange` up to `_xp_mem`, forward** (`0x2319` → the call idiom at `0x2452`): the lock is
clear, no value, `i, j < 3`, the pool alive; the call idiom runs over a base whose pool storage
is `σ` with the lock set, with `old_balances` and the frame words on the stack. -/
theorem rx_ex_pre {sevm : Sevm} {b0 b : Devm} {σ : Stor} {G R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hB : ExBase sevm b0 b σ) (hWc : WClosed sevm W)
    (hWb : W b) (hlock : σ.get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : σ.get isKilledSlot = 0) (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xc0) (hcl : VyClamps img)
    (hG : 33261 + R ≤ G)
    (k : ∀ (b1 : Devm) (M1 : Mem) (img1 : Bytes) (g : Nat) (z0 z1 z2 : B256),
      ExBase sevm b0 b1 (σ.set lockSlot 1) → W b1 → Mem.Reads M1 img1 → Mem.Wf M1 →
      M1.size = 0x2e0 → R ≤ g → g + 600 ≤ G →
      SFunc.RunEx cert.prog sevm (St b1 [balAt σ 0, balAt σ 1, balAt σ 2, z2, z1, z0,
        balAt σ 2, balAt σ 1, balAt σ 0, exR1, exR1, exR0, Bytes.toB256 [2, 0]] M1 g)
        (pcCallTree 0x2452 0x03 0xa1 34 t_2458_c0) Q) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_2319_c0 Q :=
  rx_ex_pre_core hfork hstatic hB hWc hWb hlock hval hkill hi hj hR hW hsz hcl hG
    fun b1 M1 img1 g z0 z1 z2 h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ _ =>
      k b1 M1 img1 g z0 z1 z2 h1 h2 h3 h4 h5 h6 h7

end Blanc.Lift.Curve3Pool
