import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityFrames
import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidity
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `add_liquidity`, part 1: the guards, the fee and `_A`

From the dispatcher to `0xf05`: `assert lock == 0; lock = 1`, the non-payable guard,
`assert not is_killed`, `fees` zeroed past the calldata, `_fee = fee * 3 / 8` (checked) and
`_admin_fee`, then `amp = self._A()` with the six-word inline frame save and restore.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift


/-- **The dispatcher hands `add_liquidity` its body** (past the arm's own test), with the
prologue's exact memory and the frame's remaining children unchanged. -/
theorem xa_dispatch_addLiquidity {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0xe55 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L :=
  xa_dispatch hcode hlen hcd hsel h

/-- The base after `add_liquidity`'s guards and fee reads. -/
def alB1 (sevm : Sevm) (b : Devm) : Devm :=
  afterSloadH sevm (afterSloadH sevm (afterSloadH sevm (afterSstoreH sevm (afterSloadH sevm b
    (Bytes.toB256 [0xff, 0xff, 0xff])) (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0x01]))
    (Bytes.toB256 [0x0f])) feeSlot) adminFeeSlot


/-- A word inside a zero fill reads `0`. -/
theorem al_zeroWord (img : Bytes) {o n j : Nat} (hj : 32 * j + 32 ≤ n) :
    WordAt (Bytes.writeAt img o (List.replicate n 0)) (o + 32 * j) 0 := by
  unfold WordAt
  rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_replicate]; omega),
    List.sliceD_replicate_zero]
  decide

/-- Setting the lock keeps the storage abstraction. -/
theorem al_abstracts_lock {σ : Stor} {s : State} (h : Abstracts σ s) (v : B256) :
    Abstracts (σ.set lockSlot v) s where
  coins i := by
    rw [Stor.get_set_ne _ ((by decide : ∀ i : Fin 3, lockSlot ≠ coinSlot i) i)]; exact h.coins i
  balances i := by
    rw [Stor.get_set_ne _ ((by decide : ∀ i : Fin 3, lockSlot ≠ balanceSlot i) i)]
    exact h.balances i
  fee := by rw [Stor.get_set_ne _ (by decide)]; exact h.fee
  adminFee := by rw [Stor.get_set_ne _ (by decide)]; exact h.adminFee
  owner := by rw [Stor.get_set_ne _ (by decide)]; exact h.owner
  token := by rw [Stor.get_set_ne _ (by decide)]; exact h.token
  initialA := by rw [Stor.get_set_ne _ (by decide)]; exact h.initialA
  futureA := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureA
  initialATime := by rw [Stor.get_set_ne _ (by decide)]; exact h.initialATime
  futureATime := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureATime
  adminActionsDeadline := by rw [Stor.get_set_ne _ (by decide)]; exact h.adminActionsDeadline
  transferOwnershipDeadline := by
    rw [Stor.get_set_ne _ (by decide)]; exact h.transferOwnershipDeadline
  futureFee := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureFee
  futureAdminFee := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureAdminFee
  futureOwner := by rw [Stor.get_set_ne _ (by decide)]; exact h.futureOwner
  isKilled := by rw [Stor.get_set_ne _ (by decide)]; exact h.isKilled
  killDeadline := by rw [Stor.get_set_ne _ (by decide)]; exact h.killDeadline

theorem alB1_getStor (sevm : Sevm) (b : Devm) :
    (alB1 sevm b).getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set lockSlot 1 := by
  rw [alB1, afterSloadH_getStor, afterSloadH_getStor, afterSloadH_getStor, afterSstoreH_getStor_self,
    afterSloadH_getStor, lockSlot_lit]
  rfl

theorem xa_al_p1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {s : State} (hchk : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (h : XAt sevm post 0xe55 (St b [] M G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    (b.getStor sevm.currentTarget).get isKilledSlot = 0 ∧
    (B256.eqCheck ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] /
      (b.getStor sevm.currentTarget).get feeSlot) (Bytes.toB256 [3]) |||
      B256.eqCheck ((b.getStor sevm.currentTarget).get feeSlot) 0) ≠ 0 ∧
    ∃ (A : B256) (M1 : Mem) (img1 : Bytes) (G1 : Nat),
      aChk s sevm.benvStat.time.toNat = some A.toNat ∧ Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      M1.size % 32 = 0 ∧ WordAt img1 0x140 0 ∧ WordAt img1 0x160 0 ∧ WordAt img1 0x180 0 ∧
      WordAt img1 0x1a0 ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] /
        Bytes.toB256 [8]) ∧
      WordAt img1 0x1c0 ((b.getStor sevm.currentTarget).get adminFeeSlot) ∧
      WordAt img1 0x1e0 A ∧
      XAt sevm post 0xf0d (St (aBaseH sevm (alB1 sevm b)) [] M1 G1) L := by
  xs 0xe59 (.push [0xff, 0xff, 0xff] (by decide)) ri_push
  xw 0xe5a (.reg .sload) ri_sloadF
  xa 2
  xji 0xe5f 0xe63 hw
  · xdead
  have hlock : (b.getStor sevm.currentTarget).get lockSlot = 0 := by
    have e := B256.eq_of_eqCheck_ne_zero hw
    rw [lockSlot_lit] at e
    exact e
  clear hw
  xa 3
  xw 0xe6b (.reg .sstore) ri_sstoreF
  xa 3
  xji 0xe71 0xe75 hw
  · xdead
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xw 0xe79 (.reg .sload) ri_sloadF
  xa 2
  xji 0xe7e 0xe82 hw
  · xdead
  have hkill : (b.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    have e := B256.eq_of_eqCheck_ne_zero hw
    rw [getStorVal_afterSstoreH_ne (by decide), getStorVal_eq, afterSloadH_getStor,
      isKilledSlot_lit] at e
    exact e
  clear hw
  xa 4
  xma 0xe8a (.reg .calldatacopy) (ri_calldatacopy_imgAtA (o := 0x140) (z := 0x60) rfl rfl)
  xs 0xe8c (.push [0x02] (by decide)) ri_push
  xw 0xe8d (.reg .sload) ri_sloadF
  rw [getStorVal_afterSloadH, getStorVal_afterSstoreH_ne (by decide), getStorVal_eq, afterSloadH_getStor, feeSlot_lit] at h
  xa 13
  xji 0xe9e 0xea2 hw
  · xdead
  have hmulw := hw
  clear hw
  xa 12
  xji 0xeb2 0xeb6 hw
  · xdead
  clear hw
  xa 8
  xma 0xec1 (.reg .mstore) (ri_mstore_imgAtA (o := 0x1a0) rfl)
  xs 0xec3 (.push [0x03] (by decide)) ri_push
  xw 0xec4 (.reg .sload) ri_sloadF
  rw [getStorVal_afterSloadH, getStorVal_afterSloadH, getStorVal_afterSstoreH_ne (by decide), getStorVal_eq, afterSloadH_getStor, adminFeeSlot_lit] at h
  xs 0xec7 (.push [0x01, 0xc0] (by decide)) ri_push
  xma 0xec8 (.reg .mstore) (ri_mstore_imgAtA (o := 0x1c0) rfl)
  xs 0xecb (.push [0x01, 0x40] (by decide)) ri_push
  xma 0xecc (.reg .mload) (ri_mload_imgAtA (o := 0x140) rfl)
  xs 0xecf (.push [0x01, 0x60] (by decide)) ri_push
  xma 0xed0 (.reg .mload) (ri_mload_imgAtA (o := 0x160) rfl)
  xs 0xed3 (.push [0x01, 0x80] (by decide)) ri_push
  xma 0xed4 (.reg .mload) (ri_mload_imgAtA (o := 0x180) rfl)
  xs 0xed7 (.push [0x01, 0xa0] (by decide)) ri_push
  xma 0xed8 (.reg .mload) (ri_mload_imgAtA (o := 0x1a0) rfl)
  xs 0xedb (.push [0x01, 0xc0] (by decide)) ri_push
  xma 0xedc (.reg .mload) (ri_mload_imgAtA (o := 0x1c0) rfl)
  xs 0xedf (.push [0x01, 0xe0] (by decide)) ri_push
  xma 0xee0 (.reg .mload) (ri_mload_imgAtA (o := 0x1e0) rfl)
  have hZ : List.sliceD sevm.data (Nat.toB256 (List.length sevm.data)).toNat 96 0 =
      List.replicate 96 0 := by
    rw [B256.toNat_toB256_of_lt hcd]; exact List.sliceD_length_eq
  rw [hZ] at hR h
  have f0 : ∀ j, j < 3 → WordAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x140
      (List.replicate 96 0)) 0x1a0 ((b.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [3] /
      Bytes.toB256 [8]).toBytes) 0x1c0 ((b.getStor sevm.currentTarget).get adminFeeSlot).toBytes)
      (0x140 + 32 * j) 0 := by
    intro j hj
    exact WordAt.write_other (WordAt.write_other (al_zeroWord _ (by omega))
      (by simp only [B256.length_toBytes]; omega)) (by simp only [B256.length_toBytes]; omega)
  rw [(f0 0 (by decide)).read, (f0 1 (by decide)).read, (f0 2 (by decide)).read,
    (WordAt.write_other (WordAt.write_self _ 0x1a0 ((b.getStor sevm.currentTarget).get feeSlot *
      Bytes.toB256 [3] / Bytes.toB256 [8])) (by simp only [B256.length_toBytes]; omega)).read,
    (WordAt.write_self _ 0x1c0 ((b.getStor sevm.currentTarget).get adminFeeSlot)).read] at h
  xs 0xee2 (.push [0x06] (by decide)) ri_push
  replace h := xa_al_pc (atN hcode (by kernel_rfl)) h
  obtain ⟨_, h⟩ := h
  xs 0xee4 (.reg .add) ri_add
  rw [show Nat.toB256 0xee2 + Bytes.toB256 [6] = Nat.toB256 0xee8 by decide] at h
  xs 0xee7 (.push [0x00, 0xa9] (by decide)) ri_push
  xjmp 0xa9
  have ha1 : Abstracts ((alB1 sevm b).getStor sevm.currentTarget) s := by
    rw [alB1_getStor]; exact al_abstracts_lock ha 1
  replace h : XAt sevm post 0xa9 (St (alB1 sevm b) _ _ _) L := h
  obtain ⟨A, M1, G1, hAc, hk, hW1, hal, h⟩ := xa_al_A hchk hcode hfork ha1 hW h
  obtain ⟨img1, hR1, hag⟩ := Mem.Reads.keepsOff hR hk
  have hA1 := hal hA
  clear hR hW hk hA
  have hR := hR1
  have hW := hW1
  have hA := hA1
  clear hR1 hW1 hA1
  rw [show (Nat.toB256 0xee8).toNat = 0xee8 by decide] at h
  xa 2
  xma 0xeed (.reg .mstore) (ri_mstore_imgAtA (o := 0x220) rfl)
  xs 0xef0 (.push [0x01, 0xe0] (by decide)) ri_push
  xma 0xef1 (.reg .mstore) (ri_mstore_imgAtA (o := 0x1e0) rfl)
  xs 0xef4 (.push [0x01, 0xc0] (by decide)) ri_push
  xma 0xef5 (.reg .mstore) (ri_mstore_imgAtA (o := 0x1c0) rfl)
  xs 0xef8 (.push [0x01, 0xa0] (by decide)) ri_push
  xma 0xef9 (.reg .mstore) (ri_mstore_imgAtA (o := 0x1a0) rfl)
  xs 0xefc (.push [0x01, 0x80] (by decide)) ri_push
  xma 0xefd (.reg .mstore) (ri_mstore_imgAtA (o := 0x180) rfl)
  xs 0xf00 (.push [0x01, 0x60] (by decide)) ri_push
  xma 0xf01 (.reg .mstore) (ri_mstore_imgAtA (o := 0x160) rfl)
  xs 0xf04 (.push [0x01, 0x40] (by decide)) ri_push
  xma 0xf05 (.reg .mstore) (ri_mstore_imgAtA (o := 0x140) rfl)
  obtain ⟨img2, hR2, hI⟩ := Mem.Reads.forget hR
  clear hR
  have hR := hR2
  clear hR2
  have g220 : WordAt img2 0x220 A := by rw [hI]; wchain
  xs 0xf08 (.push [0x02, 0x20] (by decide)) ri_push
  xma 0xf09 (.reg .mload) (ri_mload_imgAtA (o := 0x220) rfl)
  rw [g220.read] at h
  xs 0xf0c (.push [0x01, 0xe0] (by decide)) ri_push
  xma 0xf0d (.reg .mstore) (ri_mstore_imgAtA (o := 0x1e0) rfl)
  refine ⟨hlock, hval, hkill, hmulw, A, _, _, _, hAc, hR, hW, hA, ?_, ?_, ?_, ?_, ?_, WordAt.write_self _ _ _,
    h⟩ <;> refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega) <;> rw [hI] <;>
    wchain

theorem al_bal0 : balancesBase = balancesBase + Nat.toB256 0 := by decide

/-- **`add_liquidity`, part 2** (`0xf0d` → `0xf83`): `token_supply = token.totalSupply()` (a
`STATICCALL` returning at least a word), `D0 = 0`, `old_balances = self.balances`. -/
theorem xa_al_p2C {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {σ : Stor} (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hst : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x)
    (htok : ¬ sevm.benvStat.rules.isPrecomp (σ.get tokenSlot).toAdr)
    (hidk : ∀ c ∈ L, c.sevm.currentTarget = (σ.get tokenSlot).toAdr →
      c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0xf0d (St b [] M G) L) :
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (b1 : Devm) (M1 : Mem) (G1 : Nat) (img1 : Bytes),
      L = c :: L' ∧ 0 < sevm.depth ∧
      c.sevm.currentTarget = (σ.get tokenSlot).toAdr ∧
      c.sevm.data = totalSupplyData ∧ c.sevm.isStatic = true ∧ 32 ≤ c.post.output.length ∧
      c.post.logs = [] ∧ (∀ a, c.pre.getCode a = b.getCode a) ∧
      (∀ a, b1.getCode a = c.post.getCode a) ∧
      (∀ x, (b1.getStor sevm.currentTarget).get x = σ.get x) ∧
      (∀ a, b1.getStor a = b.getStor a) ∧
      b1.logs = b.logs ∧ b1.output = b.output ∧ Devm.AccGrow b b1 ∧ b1.getCode 4 = b.getCode 4 ∧
      (∀ a, b.getCode a ≠ .empty → b1.getCode a = b.getCode a) ∧
      Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧ M1.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0xc0 ∨ 0xe0 ≤ o) → (o + 32 ≤ 0x240 ∨ 0x260 ≤ o) →
        (o + 32 ≤ 0x260 ∨ 0x2a0 ≤ o) → (o + 32 ≤ 0x2c0 ∨ 0x360 ≤ o) → WordAt img1 o w) ∧
      WordAt img1 0x240 (Bytes.toB256 (c.post.output.take 32)) ∧ WordAt img1 0x2e0 0 ∧
      (∀ j, j < 3 → WordAt img1 (0x300 + 32 * j) (balAt σ j)) ∧
      XAt sevm post 0xf83 (St b1 [] M1 G1) L' := by
  xa 5
  xma 0xf1d (.reg .mstore) (ri_mstore_imgAtA (o := 0x260) rfl)
  xa 2
  xw 0xf23 (.reg .sload) ri_sloadF
  rw [getStorVal_eq, hst, tokenSlot_lit] at h
  xs 0xf24 (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_imgAH (pc' := 0xf25) (i := 0x27c) (n := 4) (o := 0x2c0) (z := 0x20) hfork.stateGas_none (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW hA h
  clear hR hW hA
  obtain ⟨d1, flag, out, M, L1, h, ⟨d0, hrun0, hcd0⟩, hR, hW, hA, hrd, hob, hstor, hlogs, hk⟩ := h
  xs 0xf28 (.push [0x0f, 0x2d] (by decide)) ri_push
  xji 0xf29 0xf2d hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, hout, hacc, hcodeK, htgt, hdata, hstat, hcout, hclogs,
    hcpre, hcpost⟩
  · exact absurd hpre htok
  clear hk
  have h4 : d1.getCode 4 = b.getCode 4 := by
    rw [hcpost, hidk c (by rw [hL]; exact List.mem_cons_self) htgt, hcpre]
    show (afterSloadH sevm _ _).getCode 4 = _
    rw [afterSloadH_getCode]
  xa 5
  xji 0xf36 0xf3a hw2
  · xdead
  have hlen : 32 ≤ out.length := by
    have e := B256.lt_of_gtCheck_ne_zero hw2
    rw [hrd, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hob] at e
    exact e
  clear hw2
  have hst1 : ∀ x, (d1.getStor sevm.currentTarget).get x = σ.get x := by
    intro x; rw [hstor, afterSloadH_getStor, hst]
  xa 4
  xma 0xf42 (.reg .mload) (ri_mload_imgAtA (o := 0x2c0) rfl)
  xs 0xf45 (.push [0x02, 0x40] (by decide)) ri_push
  xma 0xf46 (.reg .mstore) (ri_mstore_imgAtA (o := 0x240) rfl)
  xa 2
  xma 0xf4c (.reg .mstore) (ri_mstore_imgAtA (o := 0x2e0) rfl)
  xa 4
  xma 0xf55 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc0) rfl)
  xa 2
  xma 0xf5a (.reg .keccak256) (ri_keccak_imgAtA (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one, al_bal0] at h
  xw 0xf5b (.reg .sload) ri_sloadF
  rw [getStorVal_eq, hst1] at h
  xs 0xf5c (.reg (.dup 2)) (ri_dup (by rfl))
  xma 0xf5d (.reg .mstore) (ri_mstore_imgAtA (o := 0x300) rfl)
  xa 3
  xma 0xf63 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc0) rfl)
  xa 2
  xma 0xf68 (.reg .keccak256) (ri_keccak_imgAtA (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0xf69 (.reg .add) ri_add
  rw [show balancesBase + Bytes.toB256 [1] = balancesBase + Nat.toB256 1 by decide] at h
  xw 0xf6a (.reg .sload) ri_sloadF
  rw [getStorVal_afterSloadH, getStorVal_eq, hst1] at h
  xa 3
  xma 0xf6f (.reg .mstore) (ri_mstore_imgAtA (o := 0x320) rfl)
  xa 3
  xma 0xf75 (.reg .mstore) (ri_mstore_imgAtA (o := 0xc0) rfl)
  xa 2
  xma 0xf7a (.reg .keccak256) (ri_keccak_imgAtA (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0xf7b (.reg .add) ri_add
  rw [show balancesBase + Bytes.toB256 [2] = balancesBase + Nat.toB256 2 by decide] at h
  xw 0xf7c (.reg .sload) ri_sloadF
  rw [getStorVal_afterSloadH, getStorVal_afterSloadH, getStorVal_eq, hst1] at h
  xa 3
  xma 0xf81 (.reg .mstore) (ri_mstore_imgAtA (o := 0x340) rfl)
  xa 2
  obtain ⟨img1, hR1, hI⟩ := Mem.Reads.forget hR
  have hTw : List.sliceD (Bytes.writeAt (Bytes.writeAt img 0x260
      (Bytes.toB256 [0x18, 0x16, 0x0d, 0xdd]).toBytes) 0x2c0 (List.take 32 out)) 0x2c0 32 0 =
      List.take 32 out := by
    rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (le_refl _)
      (by rw [List.length_take]; omega), Nat.sub_self]
    exact List.sliceD_zero_of_length (by rw [List.length_take]; omega)
  refine ⟨c, L1, _, M, _, img1, hL, hdepth, htgt, ?_, hstat, by rw [hcout]; exact hlen, hclogs, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR1, hW, hA, ?_, ?_, ?_, ?_, h⟩
  · rw [hdata, Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide)
      (by rw [B256.length_toBytes])]
    decide
  · intro a
    rw [hcpre, afterSloadH_getCode]
  · intro a
    rw [afterSloadH_getCode, afterSloadH_getCode, afterSloadH_getCode, hcpost]
  · intro x
    rw [afterSloadH_getStor, afterSloadH_getStor, afterSloadH_getStor, hst1]
  · intro a
    rw [afterSloadH_getStor, afterSloadH_getStor, afterSloadH_getStor, hstor, afterSloadH_getStor]
  · rw [afterSloadH_logs, afterSloadH_logs, afterSloadH_logs, hlogs, afterSloadH_logs]
  · rw [afterSloadH_output, afterSloadH_output, afterSloadH_output, hout, afterSloadH_output]
  · refine Devm.AccGrow.trans (Devm.AccGrow.of_eq ?_) (Devm.AccGrow.trans hacc
      (Devm.AccGrow.of_eq ?_))
    · rw [afterSloadH_accessedAddresses]
    · rw [afterSloadH_accessedAddresses, afterSloadH_accessedAddresses,
        afterSloadH_accessedAddresses]
  · rw [afterSloadH_getCode, afterSloadH_getCode, afterSloadH_getCode, h4]
  · intro a ha
    have e := hcodeK a (by rwa [afterSloadH_getCode])
    rw [afterSloadH_getCode] at e
    rw [afterSloadH_getCode, afterSloadH_getCode, afterSloadH_getCode, e]
  · intro o w hw h1 h2 h3 h4'
    rw [hI]; wchain; exact hw
  · rw [hI]; wchain
    rw [hTw, hcout]
    exact WordAt.write_self _ _ _
  · rw [hI]; wchain
  · intro j hj
    rw [hI]
    rcases three_cases hj with rfl | rfl | rfl <;> wchain

/-- **`xa_al_p2`**: `xa_al_p2C` with every child keeping the pool. -/
theorem xa_al_p2 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {σ : Stor} (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (hst : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x)
    (htok : ¬ sevm.benvStat.rules.isPrecomp (σ.get tokenSlot).toAdr)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0xf0d (St b [] M G) L) :
    ∃ (c : Exec.Frame) (L' : List Exec.Frame) (b1 : Devm) (M1 : Mem) (G1 : Nat) (img1 : Bytes),
      L = c :: L' ∧ 0 < sevm.depth ∧
      c.sevm.currentTarget = (σ.get tokenSlot).toAdr ∧
      c.sevm.data = totalSupplyData ∧ c.sevm.isStatic = true ∧ 32 ≤ c.post.output.length ∧
      c.post.logs = [] ∧ (∀ a, c.pre.getCode a = b.getCode a) ∧
      (∀ a, b1.getCode a = c.post.getCode a) ∧
      (∀ x, (b1.getStor sevm.currentTarget).get x = σ.get x) ∧
      (∀ a, b1.getStor a = b.getStor a) ∧
      b1.logs = b.logs ∧ b1.output = b.output ∧ Devm.AccGrow b b1 ∧ b1.getCode 4 = b.getCode 4 ∧
      (∀ a, b.getCode a ≠ .empty → b1.getCode a = b.getCode a) ∧
      Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧ M1.size % 32 = 0 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0xc0 ∨ 0xe0 ≤ o) → (o + 32 ≤ 0x240 ∨ 0x260 ≤ o) →
        (o + 32 ≤ 0x260 ∨ 0x2a0 ≤ o) → (o + 32 ≤ 0x2c0 ∨ 0x360 ≤ o) → WordAt img1 o w) ∧
      WordAt img1 0x240 (Bytes.toB256 (c.post.output.take 32)) ∧ WordAt img1 0x2e0 0 ∧
      (∀ j, j < 3 → WordAt img1 (0x300 + 32 * j) (balAt σ j)) ∧
      XAt sevm post 0xf83 (St b1 [] M1 G1) L' :=
  xa_al_p2C hcode hfork hR hW hA hst htok (fun c hc _ => hidk c hc) h

end Blanc.Lift.Curve3Pool
