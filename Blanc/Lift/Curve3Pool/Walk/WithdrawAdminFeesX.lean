import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Curve3Pool.Walk.AdminBalancesX
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLoop
import Blanc.Lift.Curve3Pool.Spec
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `withdraw_admin_fees`, on the actual derivation

From the frame's entry with the `withdraw_admin_fees` selector (`0x30c54085`) the
dispatcher walks past every earlier arm to the arm's test (`0x4d2c`) and falls into its
body (`0x4d3a`): the non-payable guard, the owner guard, the counter init at `0x140`,
then three iterations. Each iteration loads `coins[i]` at `keccak(0) + i`, does one
`balanceOf(self)` `STATICCALL` with the output window `0x220`, asserts the flag and
`RETURNDATASIZE > 31`, then loads `balances[i] = keccak(1) + i`: when the fresh answer
equals the recorded balance nothing moves; when it exceeds it the excess is sent
to the owner with a `raw_call`-shaped `CALL` (returndata-size check and three
identity-precompile copy `CALL`s); the tail bumps the counter and loops back until it
reaches `3`, exiting to `STOP`.

Reuse: the dispatcher walk `xa_dispatch` (`Walk.Dispatch`); the `xs`/`xji`/`xjd`/`xdead`
walk macros and `xa_staticcall_img`, `WordAt`/`Region` from `FrameWalkKit` via `Walk.Kit`;
`keccak_zero`/`keccak_one` via `Walk.RemoveLiquidityLoop`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## Guards and counter init -/

/-- **Guards of `withdraw_admin_fees`**: no value, the caller is the owner, the counter at
`0x140` set to `0` with `[3, 0x140]` on the stack, entering the loop at `0x4d5e`. -/
theorem wdx_guards {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (h : XAt sevm post 0x4d3a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    sevm.value = 0 ∧ sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
    ∃ G' M' img', Mem.Wf M' ∧ Mem.Reads M' img' ∧
      Region img' 0x140 (Nat.toB256 0).toBytes ∧
      XAt sevm post 0x4d5e
        (St (afterSloadH sevm b ownerSlot) [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]]
          M' G') L := by
  have hR : Mem.Reads (vyMem Mem.empty (Sevm.dataWord sevm 0))
      (vyImg [] (Sevm.dataWord sevm 0)) :=
    vyMem_reads Mem.wf_empty Mem.reads_empty _
  have hW : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  xa 3
  xji 0x4d40 0x4d44 hw
  · xdead
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xw 0x4d48 (.reg .sload) ri_sloadF
  rw [show Bytes.toB256 [4] = ownerSlot from by decide] at h
  xa 3
  xji 0x4d4e 0x4d52 hw
  · xdead
  have hown : sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot := by
    have e := B256.eq_of_eqCheck_ne_zero hw
    rw [getStorVal_eq] at e
    exact e
  clear hw
  xa 6
  xmo 0x4d5d (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  have hctrR : Region (Bytes.writeAt (vyImg [] (Sevm.dataWord sevm 0)) 320
      (Bytes.toB256 [0]).toBytes) 0x140 (Nat.toB256 0).toBytes :=
    Region.write_self _ _ _
  xs 0x4d5e (.reg .add) ri_add
  have h30 : Bytes.toB256 [0x03] + Bytes.toB256 [0x00] = Bytes.toB256 [0x03] := by decide
  rw [h30] at h
  exact ⟨hval, hown, _, _, _, hW, hR, hctrR, h⟩

/-! ## The `balanceOf` calldata in the image -/

/-- The `balanceOf(self)` calldata the staging writes leave at `0x1bc` (the zero word at
`0xc0` and the coin word at `0x160` are underneath; the selector word at `0x1a0` and the
address at `0x1c0` close the window). -/
theorem wdx_input (img coinB : Bytes) (self : Adr) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0 self.toB256.toBytes).sliceD
      0x1bc 0x24 0) = balanceOfData self := by
  show ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
    (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0 self.toB256.toBytes).sliceD
    0x1bc 0x24 0) = balanceOfSel ++ self.toB256.toBytes
  have hsel : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1bc balanceOfSel := by
    have := Region.write_self (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
    rw [adminBal_sel_bytes] at this
    exact this.right
  have hsel2 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0 self.toB256.toBytes) 0x1bc
      balanceOfSel :=
    Region.write_other hsel (by simp only [balanceOfSel, B256.length_toBytes,
      List.length_cons, List.length_nil]; omega)
  refine Region.slice (Region.append' (o' := 0x1c0) ?_ ?_ (by rfl))
    (by simp only [balanceOfSel, List.length_append, B256.length_toBytes, List.length_cons,
      List.length_nil])
  · exact hsel2
  · exact Region.write_self _ _ _

/-- The answer word the `STATICCALL` wrote at `0x220` reads back. -/
theorem wdx_read_out (img : Bytes) (out : Bytes) (hlen : (out.take 32).length = 32) :
    Bytes.toB256 ((Bytes.writeAt img 0x220 (out.take 32)).sliceD 0x220 32 0) =
      Bytes.toB256 (out.take 32) :=
  Region.read (Region.write_self img 0x220 (out.take 32)) hlen

/-! ## One loop iteration: staticcall half -/

/-- **One `withdraw_admin_fees` iteration, staticcall half** (`0x4d5e → 0x4dfb`): with the
counter at `k`, one `balanceOf` `STATICCALL`, the `ans ≥ rec` assert, and the recorded
balance load; either the fresh answer equals the recording (skip to the tail at `0x4f3c`)
or it exceeds it (fall into the transfer at `0x4dfc`). -/
theorem wdx_iter_static {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (k : Fin 3) (hid : IdReadyH sevm d)
    (hpc : d.getCode sevm.currentTarget ≠ .empty)
    (hkeep : KeepCoin sevm ((d.getStor sevm.currentTarget).get (coinSlot k)) L)
    (hctrR : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hcoinK : ¬ sevm.benvStat.rules.isPrecomp
      (((d.getStor sevm.currentTarget).get (coinSlot k)).toAdr))
    (h : XAt sevm post 0x4d5e
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ (c : Exec.Frame) (out : Bytes) (L' : List Exec.Frame) (d' : Devm) (M' : Mem)
      (img' : Bytes) (G' : Nat) (ansW recW : B256),
      L = c :: L' ∧
      c.sevm.currentTarget = ((d.getStor sevm.currentTarget).get (coinSlot k)).toAdr ∧
      c.sevm.data = balanceOfData sevm.currentTarget ∧
      c.sevm.isStatic = true ∧
      c.post.output = out ∧ 32 ≤ out.length ∧
      c.post.logs = [] ∧
      ansW = Bytes.toB256 (out.take 32) ∧
      recW = (d'.getStor sevm.currentTarget).get (balanceSlot k) ∧
      recW.toNat ≤ ansW.toNat ∧
      (d'.getStor sevm.currentTarget) = (d.getStor sevm.currentTarget) ∧
      d'.logs = d.logs ∧
      d'.output = d.output ∧
      0 < sevm.depth ∧ IdReadyH sevm d' ∧
      d'.getCode sevm.currentTarget = d.getCode sevm.currentTarget ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧
      Region img' 0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes ∧
      Region img' 0x180 (ansW - recW).toBytes ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      ((ansW = recW ∧ XAt sevm post 0x4f3c
        (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L') ∨
       (ansW ≠ recW ∧ XAt sevm post 0x4dfc
        (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L')) := by
  xa 2
  xmo 0x4d63 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 4
  have hltK : Nat.toB256 ↑k < Bytes.toB256 [0x03] := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
      show (Bytes.toB256 [0x03]).toNat = 3 by decide]
    exact k.isLt
  xji 0x4d6b 0x4d6f hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hltK)
  clear hw
  xa 3
  xmo 0x4d75 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  have hctrR_C : Region (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR (Or.inr (by decide))
  xa 2
  xmo 0x4d7a (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x4d7b (.reg .add) ri_add
  have hslot : coinsBase + Nat.toB256 ↑k = coinSlot k := rfl
  rw [hslot] at h
  xw 0x4d7c (.reg .sload) ri_sloadF
  rw [getStorVal_eq] at h
  xs 0x4d7f (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x4d80 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  have hctrR_D : Region (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_C (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hcoinW0 : Region (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
    Region.write_self _ _ _
  xa 5
  xmo 0x4d90 (.reg .mstore) (ri_mstore_imgAt (o := 0x1a0) rfl)
  have hctrR_E : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_D (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hcoinW1 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
    Region.write_other hcoinW0 (Or.inl (by simp only [B256.length_toBytes]; omega))
  xa 2
  xmo 0x4d95 (.reg .mstore) (ri_mstore_imgAt (o := 0x1c0) rfl)
  have hctrR_F : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_E (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hcoinW2 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
    Region.write_other hcoinW1 (Or.inl (by simp only [B256.length_toBytes]; omega))
  xa 2
  xmo 0x4d9c (.reg .mload) (ri_mload_imgAt (o := 0x160) rfl)
  rw [Region.read hcoinW2 (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4d9d (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_imgH (pc' := 0x4d9e) (i := 0x1bc) (n := 0x24) (o := 0x220)
    (z := 0x20) hfork.stateGas_none (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M', L1, h, -, hR, hW, hrd, hob, hstor1, hlogs1, hk⟩ := h
  have hctrR_G : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_F (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4da1 (.push [0x4d, 0xa6] (by decide)) ri_push
  xji 0x4da2 0x4da6 hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, houtKeep, hacc, hcodeKeep, htgt, hdata, hstat, hout,
    hclogs, hcpre, hcpost⟩
  · exact absurd hpre hcoinK
  clear hk hw
  rw [wdx_input] at hdata
  have h4 : d1.getCode 4 = d.getCode 4 := by
    rw [hcpost, (hkeep c (by rw [hL]; exact List.mem_cons_self) htgt
      (poolCoinSel_balanceOfData hdata)).2, hcpre, afterSloadH_getCode]
  have hid1 : IdReadyH sevm d1 :=
    ⟨by rw [h4]; exact hid.nodeleg,
      hacc _ (by rw [afterSloadH_accessedAddresses]; exact hid.warm), hid.pre, hid.stateGas⟩
  have hcode1 : d1.getCode sevm.currentTarget = d.getCode sevm.currentTarget := by
    have hpc0 : (afterSloadH sevm d (coinSlot k)).getCode sevm.currentTarget ≠ .empty := by
      rw [afterSloadH_getCode]; exact hpc
    rw [hcodeKeep _ hpc0, afterSloadH_getCode]
  xa 5
  xji 0x4daf 0x4db3 hw
  · xdead
  have hlen32 : 32 ≤ out.length := by
    have hgt := B256.lt_of_gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, hrd, B256.toNat_toB256_of_lt hob,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at hgt
    omega
  clear hw
  xa 4
  xmo 0x4dbb (.reg .mload) (ri_mload_imgAt (o := 0x220) rfl)
  have hlen : (out.take 32).length = 32 := by rw [List.length_take]; omega
  rw [wdx_read_out _ _ hlen] at h
  clear hlen
  xs 0x4dbe (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x4dbf (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR_G (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 4
  xji 0x4dc7 0x4dcb hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hltK)
  clear hw
  xa 3
  xmo 0x4dd1 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  have hctrR_H0 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_G (Or.inr (by decide))
  xa 2
  xmo 0x4dd6 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x4dd7 (.reg .add) ri_add
  have hslotB : balancesBase + Nat.toB256 ↑k = balanceSlot k := rfl
  rw [hslotB] at h
  xw 0x4dd8 (.reg .sload) ri_sloadF
  rw [getStorVal_eq] at h
  xa 5
  xji 0x4de0 0x4de4 hw
  · xdead
  have hge : ((d1.getStor sevm.currentTarget).get (balanceSlot k)).toNat ≤
      (Bytes.toB256 (out.take 32)).toNat := by
    have hge' := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    rw [B256.lt_iff_toNat_lt_toNat] at hge'
    omega
  have hgeB : (d1.getStor sevm.currentTarget).get (balanceSlot k) ≤
      Bytes.toB256 (out.take 32) :=
    not_lt.mp (B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw))
  clear hw
  xa 9
  xmo 0x4df0 (.reg .mstore) (ri_mstore_imgAt (o := 0x180) rfl)
  have hctrR_H : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_H0 (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hcoinR0 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
    Region.write_other (Region.write_other (Region.write_other hcoinW2
      (Or.inl (by simp only [B256.length_toBytes]; omega))) (Or.inr (by decide)))
      (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hfeesR0 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes :=
    Region.write_self _ _ _
  xa 2
  xmo 0x4df6 (.reg .mload) (ri_mload_imgAt (o := 0x180) rfl)
  have hfeesW : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes :=
    Region.write_self _ _ _
  rw [Region.read hfeesW (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 3
  have hfees : (Bytes.toB256 (out.take 32) -
      (d1.getStor sevm.currentTarget).get (balanceSlot k)).toNat =
      (Bytes.toB256 (out.take 32)).toNat -
        ((d1.getStor sevm.currentTarget).get (balanceSlot k)).toNat :=
    B256.toNat_sub_eq_of_le _ _ hgeB
  xji 0x4dfc 0x4f3c hw
  · have hneFees : B256.gtCheck (Bytes.toB256 (out.take 32) -
        (d1.getStor sevm.currentTarget).get (balanceSlot k)) 0 ≠ 0 :=
      ne_of_eqCheck_eq_zero hw
    have hpos := B256.lt_of_gtCheck_ne_zero hneFees
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero, hfees] at hpos
    have hne : Bytes.toB256 (out.take 32) ≠
        (d1.getStor sevm.currentTarget).get (balanceSlot k) := by
      intro e
      rw [e] at hpos
      omega
    refine ⟨c, out, L1, _, _, _, _,
      Bytes.toB256 (out.take 32),
      (d1.getStor sevm.currentTarget).get (balanceSlot k), hL, htgt, hdata, hstat, hout,
      hlen32, hclogs, rfl, by rw [afterSloadH_getStor sevm d1 (balanceSlot k)], hge,
      by rw [afterSloadH_getStor sevm d1 (balanceSlot k), hstor1,
        afterSloadH_getStor sevm d (coinSlot k)],
      by rw [afterSloadH_logs sevm d1 (balanceSlot k), hlogs1,
        afterSloadH_logs sevm d (coinSlot k)],
      by rw [afterSloadH_output sevm d1 (balanceSlot k), houtKeep,
        afterSloadH_output sevm d (coinSlot k)], hdepth, hid1.afterSloadH _,
      by rw [afterSloadH_getCode, hcode1], hctrR_H, hcoinR0, hfeesR0, hR, hW,
      Or.inr ⟨hne, h⟩⟩
  · have heqFees : B256.gtCheck (Bytes.toB256 (out.take 32) -
        (d1.getStor sevm.currentTarget).get (balanceSlot k)) 0 = 0 :=
      B256.eq_of_eqCheck_ne_zero hw
    have hle := gtCheck_eq_zero heqFees
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero, hfees] at hle
    have heq : Bytes.toB256 (out.take 32) =
        (d1.getStor sevm.currentTarget).get (balanceSlot k) := by
      apply B256.toNat_inj
      omega
    refine ⟨c, out, L1, _, _, _, _,
      Bytes.toB256 (out.take 32),
      (d1.getStor sevm.currentTarget).get (balanceSlot k), hL, htgt, hdata, hstat, hout,
      hlen32, hclogs, rfl, by rw [afterSloadH_getStor sevm d1 (balanceSlot k)], hge,
      by rw [afterSloadH_getStor sevm d1 (balanceSlot k), hstor1,
        afterSloadH_getStor sevm d (coinSlot k)],
      by rw [afterSloadH_logs sevm d1 (balanceSlot k), hlogs1,
        afterSloadH_logs sevm d (coinSlot k)],
      by rw [afterSloadH_output sevm d1 (balanceSlot k), houtKeep,
        afterSloadH_output sevm d (coinSlot k)], hdepth, hid1.afterSloadH _,
      by rw [afterSloadH_getCode, hcode1], hctrR_H, hcoinR0, hfeesR0, hR, hW,
      Or.inl ⟨heq, h⟩⟩

/-! ## The loop tail -/

/-- **The `withdraw_admin_fees` loop tail** (`0x4f3c`): the counter becomes `k + 1`; either
loop back to `0x4d5e` (still below `3`) or fall out to `0x4f50` (reached `3`). -/
theorem wdx_tail {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code)
    (k : Nat) (hk3 : k < 3)
    (hctrR : Region img 0x140 (Nat.toB256 k).toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4f3c
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    (k + 1 < 3 ∧ ∃ G' M' img',
      Region img' 0x140 (Nat.toB256 (k + 1)).toBytes ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      XAt sevm post 0x4d5e
        (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L)
    ∨ (k + 1 = 3 ∧ ∃ M' G', XAt sevm post 0x4f50 (St d [] M' G') L) := by
  have hplus : Bytes.toB256 [0x01] + Nat.toB256 k = Nat.toB256 (k + 1) := by
    apply B256.toNat_inj
    have hnof : B256.Nof (Bytes.toB256 [0x01]) (Nat.toB256 k) := by
      unfold B256.Nof
      rw [show (Bytes.toB256 [0x01]).toNat = 1 by decide,
        B256.toNat_toB256_of_lt (by omega : k < 2 ^ 256)]
      omega
    rw [B256.toNat_add_eq_of_nof _ _ hnof,
      show (Bytes.toB256 [0x01]).toNat = 1 by decide,
      B256.toNat_toB256_of_lt (by omega : k < 2 ^ 256),
      B256.toNat_toB256_of_lt (by omega : k + 1 < 2 ^ 256)]
    omega
  xa 3
  xmo 0x4f40 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 2
  rw [hplus] at h
  xa 2
  xmo 0x4f46 (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  have hctrR' : Region (Bytes.writeAt img 0x140 (Nat.toB256 (k + 1)).toBytes) 0x140
      (Nat.toB256 (k + 1)).toBytes :=
    Region.write_self _ _ _
  xa 4
  have h32 : (Bytes.toB256 [0x03]).toNat = 3 := by decide
  have hkp1 : (Nat.toB256 (k + 1)).toNat = k + 1 :=
    B256.toNat_toB256_of_lt (by omega : k + 1 < 2 ^ 256)
  by_cases hdone : k + 1 = 3
  · xji 0x4f4d 0x4d5e hw
    · xjd 0x4f4e
      xa 2
      exact Or.inr ⟨hdone, _, _, h⟩
    · have hne := isNe_jump hw
      have h3 : (Bytes.toB256 [0x03]).toNat ≠ (Nat.toB256 (k + 1)).toNat :=
        fun e => hne (B256.toNat_inj _ _ e)
      rw [h32, hkp1] at h3
      omega
  · have hback : k + 1 < 3 := by omega
    xji 0x4f4d 0x4d5e hw
    · have heq := isNe_fall hw
      have h3 : (Bytes.toB256 [0x03]).toNat = (Nat.toB256 (k + 1)).toNat :=
        congrArg B256.toNat heq
      rw [h32, hkp1] at h3
      omega
    · exact Or.inl ⟨hback, _, _, _, hctrR', hR, hW, h⟩

/-! ## The transfer: staging and first identity copy -/

/-- **Transfer staging and first identity copy** (`0x4dfc → 0x4e44`): the `transfer`
selector word staged at `0x2c0`, the selector's first four bytes copied through the
identity precompile to `0x320`; no child, storage/logs/output kept. -/
theorem wdx_xfer_stage {sevm : Sevm} {post d' : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code)
    (k : Fin 3) (feesW : B256) (hdepth : 0 < sevm.depth) (hid : IdReadyH sevm d')
    (hctrR : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hcoinR : Region img 0x160
      ((d'.getStor sevm.currentTarget).get (coinSlot k)).toBytes)
    (hfeesR : Region img 0x180 feesW.toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4dfc
      (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ (d1 : Devm) (M1 : Mem) (img1 : Bytes) (G1 : Nat),
      BaseRel d' d1 ∧
      Region img1 0x140 (Nat.toB256 ↑k).toBytes ∧
      Region img1 0x2a0 (Bytes.toB256 [0x04]).toBytes ∧
      Region img1 0x160 ((d'.getStor sevm.currentTarget).get (coinSlot k)).toBytes ∧
      Region img1 0x180 feesW.toBytes ∧
      Region img1 0x320 transferSel ∧
      Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      XAt sevm post 0x4e44
        (St d1 [Bytes.toB256 [0x02, 0xa0], Bytes.toB256 [0x00],
          Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M1 G1) L := by
  xa 3
  xmo 0x4e04 (.reg .mstore) (ri_mstore_imgAt (o := 0x2a0) rfl)
  have hctrR_1 : Region (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4e25 (.push [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x4e28 (.push [0x02, 0xc0] (by decide)) ri_push
  xmo 0x4e29 (.reg .mstore) (ri_mstore_imgAt (o := 0x2c0) rfl)
  have hctrR_2 : Region (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes)
      0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_1 (Or.inl (by simp only [B256.length_toBytes]; omega))
  xa 7
  have hadd1 : Bytes.toB256 [0x03, 0x00] + Bytes.toB256 [0x00] =
      Bytes.toB256 [0x03, 0x00] := by decide
  rw [hadd1] at h
  xs 0x4e37 (.reg .add) ri_add
  have hadd2 : Bytes.toB256 [0x03, 0x00] + Bytes.toB256 [0x20] =
      Bytes.toB256 [0x03, 0x20] := by decide
  rw [hadd2] at h
  xa 4
  have hadd3 : Bytes.toB256 [0x02, 0xa0] + Bytes.toB256 [0x20] =
      Bytes.toB256 [0x02, 0xc0] := by decide
  rw [hadd3] at h
  xa 3
  replace h := xa_identity_imgH (pc' := 0x4e42) (i := 0x2c0) (n := 4) (o := 0x320)
    (z := 4) hid (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide)
    (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L1, h, hk⟩ := h
  rcases hk with ⟨h0, hgas⟩ | ⟨rfl, b2, G2, M, hsha, rfl, hR, hW⟩
  · have hz := hgas rfl hdepth (by decide)
    obtain ⟨_, s, -⟩ := xa_next (n := .reg .pop) (atN hcode (by kernel_rfl)) (by nofun) h
    exact absurd (gasLeft_of_run_pop s) (by rw [hz]; decide)
  · xs 0x4e43 (.reg .pop) ri_pop
    xs 0x4e44 (.reg .pop) ri_pop
    have hctrR_2c : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00]).toBytes) 0x320 (((Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x140
        (Nat.toB256 ↑k).toBytes :=
      Region.write_other hctrR_2 (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hb12 : BaseRel d' b2 := by
      exact ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
    have hlen4a : Region (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes)
        0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x2a0
        (Bytes.toB256 [0x04]).toBytes :=
      Region.write_other (Region.write_self _ _ _)
        (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hlen4 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes) 0x320 (((Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x2a0 (Bytes.toB256 [0x04]).toBytes :=
      Region.write_other hlen4a (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hcoinR1a : Region (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes)
        0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x160
        ((d'.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
      Region.write_other (Region.write_other hcoinR
        (Or.inl (by simp only [B256.length_toBytes]; omega)))
        (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hcoinR1 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes) 0x320 (((Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x160
        ((d'.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
      Region.write_other hcoinR1a (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hfeesR1a : Region (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes)
        0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x180
        feesW.toBytes :=
      Region.write_other (Region.write_other hfeesR
        (Or.inl (by simp only [B256.length_toBytes]; omega)))
        (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hfeesR1 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes) 0x320 (((Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x180 feesW.toBytes :=
      Region.write_other hfeesR1a (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hselWord : WordAt (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) :=
      WordAt.write_self _ _ _
    have hsel4 : ((Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes).sliceD 0x2c0 4 0).take 4 = transferSel := by
      rw [hselWord.prefix (by decide)]; decide
    have hselCopy : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x320
        (((Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x320 transferSel := by
      rw [hsel4]; exact Region.write_self _ _ _
    exact ⟨b2, M, _, _, hb12, hctrR_2c, hlen4, hcoinR1, hfeesR1, hselCopy, hR, hW, h⟩

/-- Assemble the transfer payload after the selector copy, ending before the checked
identity copy (`0x4e44 → 0x4e78`). -/
theorem wdx_xfer_payload {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {M : Mem} {img : Bytes} {G : Nat} (hcode : sevm.code = code)
    (k : Fin 3) (coin fees : B256)
    (hctr : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hcoin : Region img 0x160 coin.toBytes) (hfees : Region img 0x180 fees.toBytes)
    (hlen : Region img 0x2a0 (Bytes.toB256 [4]).toBytes)
    (hsel : Region img 0x320 transferSel) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4e44
      (St b [Bytes.toB256 [0x02, 0xa0], Bytes.toB256 [0],
        Bytes.toB256 [3], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧
      Region img' 0x160 coin.toBytes ∧
      Region img' 0x300 ((0x44 : B256).toBytes ++
        (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)) ∧
      XAt sevm post 0x4e78
        (St b [Bytes.toB256 [3, 0], Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] M' G') L := by
  xs 0x4e45 (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x4e46 (.reg .mload) (ri_mload_imgAt (o := 0x2a0) rfl)
  rw [Region.read hlen (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 2
  have e4 : Bytes.toB256 [0] + Bytes.toB256 [4] = (4 : B256) := by decide
  rw [e4] at h
  xa 9
  xmo 0x4e55 (.reg .mstore) (ri_mstore_imgAt (o := 0x324) (by decide))
  xa 3
  have e24 : (4 : B256) + Bytes.toB256 [0x20] = (0x24 : B256) := by decide
  rw [e24] at h
  xa 3
  xmo 0x4e5f (.reg .mload) (ri_mload_imgAt (o := 0x180) rfl)
  rw [Region.read (Region.write_other hfees (Or.inl (by simp only [B256.length_toBytes]; omega)))
    (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 5
  xmo 0x4e68 (.reg .mstore) (ri_mstore_imgAt (o := 0x344) (by decide))
  xa 3
  have e44 : (0x24 : B256) + Bytes.toB256 [0x20] = (0x44 : B256) := by decide
  rw [e44] at h
  xa 4
  xmo 0x4e73 (.reg .mstore) (ri_mstore_imgAt (o := 0x300) rfl)
  xa 3
  obtain ⟨img', hR, hI⟩ := Mem.Reads.forget hR
  have fctr : Region img' 0x140 (Nat.toB256 ↑k).toBytes := by rw [hI]; wchainT; exact hctr
  have fcoin : Region img' 0x160 coin.toBytes := by rw [hI]; wchainT; exact hcoin
  have flen : Region img' 0x300 (0x44 : B256).toBytes := by rw [hI]; wchainT
  have fsel : Region img' 0x320 transferSel := by rw [hI]; wchainT; exact hsel
  have fdst : Region img' 0x324 sevm.caller.toB256.toBytes := by rw [hI]; wchainT
  have famt : Region img' 0x344 fees.toBytes := by rw [hI]; wchainT
  have fargs := Region.append' fdst famt (by simp only [B256.length_toBytes])
  have fcall := Region.append' fsel fargs (by decide)
  have fdata := Region.append' flen fcall (by simp only [B256.length_toBytes])
  exact ⟨_, img', _, hR, hW, fctr, fcoin, fdata, h⟩

/-- The checked identity copy of the complete transfer payload (`0x4e78 → 0x4e94`). -/
theorem wdx_xfer_copy {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {M : Mem} {img : Bytes} {G : Nat} (hcode : sevm.code = code)
    (k : Fin 3) (coin fees : B256) (hid : IdReadyH sevm b)
    (hctr : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hcoin : Region img 0x160 coin.toBytes)
    (hdata : Region img 0x300 ((0x44 : B256).toBytes ++
      (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)))
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4e78
      (St b [Bytes.toB256 [3, 0], Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] M G) L) :
    ∃ b' M' img' G', BaseRel b b' ∧ Mem.Reads M' img' ∧ Mem.Wf M' ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧
      Region img' 0x160 coin.toBytes ∧
      Region img' 0x3a0 ((0x44 : B256).toBytes ++
        (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)) ∧
      XAt sevm post 0x4e94
        (St b' [Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] M' G') L := by
  xs 0x4e79 (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x4e7a (.reg .mload) (ri_mload_imgAt (o := 0x300) rfl)
  rw [hdata.left.read (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 9
  replace h := xa_identity_imgH (pc' := 0x4e89) (i := 0x300) (n := 0x64)
    (o := 0x3a0) (z := 0x64) hid (atN hcode (by kernel_rfl)) rfl
    (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L', h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b', G', M', hsha, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x4e8c (.push [0x4e, 0x91] (by decide)) ri_push
    xji 0x4e8d 0x4e91 hw
    · xdead
    · exact absurd rfl hw
  have copied := hdata.copy (n := 0x64) (z := 0x64) (by simp only [List.length_append, B256.length_toBytes, transferSel,
    List.length_cons, List.length_nil]) (by simp only [List.length_append, B256.length_toBytes,
    transferSel, List.length_cons, List.length_nil])
  rw [copied] at hR
  have hbase : BaseRel b b' :=
    ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  obtain ⟨img', hR, hI⟩ := Mem.Reads.forget hR
  have fctr : Region img' 0x140 (Nat.toB256 ↑k).toBytes := by rw [hI]; wchainT; exact hctr
  have fcoin : Region img' 0x160 coin.toBytes := by rw [hI]; wchainT; exact hcoin
  have fdata : Region img' 0x3a0 ((0x44 : B256).toBytes ++
      (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  xs 0x4e8c (.push [0x4e, 0x91] (by decide)) ri_push
  xji 0x4e8d 0x4e91 hw
  · exact absurd hw (by decide)
  clear hw
  xa 3
  exact ⟨b', M', img', _, hbase, hR, hW, fctr, fcoin, fdata, h⟩

/-- The actual transfer CALL and its successful flag (`0x4e94 → 0x4eb1`). -/
theorem wdx_xfer_call {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {M : Mem} {img : Bytes} {G : Nat} (hcode : sevm.code = code)
    (hfork : HistFork sevm.benvStat.fork) (coin fees : B256)
    (hcoinR : Region img 0x160 coin.toBytes)
    (hdata : Region img 0x3a0 ((0x44 : B256).toBytes ++
      (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)))
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp coin.toAdr)
    (hK : KeepCoin sevm coin L)
    (h : XAt sevm post 0x4e94
      (St b [Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] M G) L) :
    ∃ c L' d G', L = c :: L' ∧
      ChildOf b d coin.toAdr (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)
        0 sevm.isStatic c ∧
      ((∀ x, (c.post.getStor sevm.currentTarget).get x =
        (c.pre.getStor sevm.currentTarget).get x) ∧ c.post.getCode 4 = c.pre.getCode 4) ∧
      Mem.Reads d.memory (Bytes.writeAt img 0x460 (d.returnData.take 32)) ∧
      Mem.Wf d.memory ∧ d.returnData.length < 2 ^ 256 ∧
      XAt sevm post 0x4eb1
        (St d [Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] d.memory G') L' := by
  xa 3
  xmo 0x4e9d (.reg .mload) (ri_mload_imgAt (o := 0x3a0) rfl)
  rw [hdata.left.read (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 3
  xmo 0x4ea6 (.reg .mload) (ri_mload_imgAt (o := 0x160) rfl)
  rw [hcoinR.read (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4ea7 (.reg .gas) ri_gas_remaining
  have hin : img.sliceD 0x3c0 0x44 0 =
      transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes := by
    refine Region.slice hdata.right ?_
    simp only [List.length_append, B256.length_toBytes, transferSel,
      List.length_cons, List.length_nil]
  replace h := xa_call_imgH (pc' := 0x4ea8) (i := 0x3c0) (n := 0x44)
    (o := 0x460) (z := 0x20) hfork.stateGas_none (atN hcode (by kernel_rfl)) rfl
    (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, flag, L', h, hrun, hrd, hk⟩ := h
  rw [hin] at hk
  xs 0x4eab (.push [0x4e, 0xb0] (by decide)) ri_push
  xji 0x4eac 0x4eb0 hw
  · xdead
  obtain ⟨hR, hW, hout, hch⟩ := hk hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp hcoin
  xjd 0x4eb1
  rw [zero_lit] at hc
  refine ⟨c, L', d, _, rfl, ?_, hK c List.mem_cons_self hc.target (poolCoinSel_transferData hc.data), hR, hW, hrd, h⟩
  exact hc.congr_left (fun _ => rfl) (fun _ => rfl) rfl rfl rfl

/-- The transfer reply passes the deployed raw-call check (`0x4eb1 → 0x4f3c`). -/
theorem wdx_xfer_tail {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hid : IdReadyH sevm d)
    (hR : Mem.Reads M (Bytes.writeAt img 0x460 (d.returnData.take 0x20))) (hW : Mem.Wf M)
    (hrd : d.returnData.length < 2 ^ 256)
    (h : XAt sevm post 0x4eb1 (St d [3, 0x140] M G) L) :
    RawCallOk d.returnData ∧ ∃ b6 M6 img6 G7, BaseRel d b6 ∧ Mem.Reads M6 img6 ∧ Mem.Wf M6 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x240 ∨ 0x280 ≤ o) →
        (o + 32 ≤ 0x440 ∨ 0x480 ≤ o) → WordAt img6 o w) ∧
      XAt sevm post 0x4f3c (St b6 [3, 0x140] M6 G7) L := by
  have hj : ∃ nW G5, nW.toNat = (d.returnData.take 32).length ∧
      XAt sevm post 0x4ec4 (St d (nW :: d.returnData.length.toB256 :: Bytes.toB256 [0x20] ::
        [3, 0x140]) M G5) L := by
    xa 7
    xji 0x4ebc 0x4ec1 hw
    · xs 0x4ebd (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x4ec0 (.push [0x4e, 0xc3] (by decide)) ri_push
      xjmp 0x4ec3
      xjd 0x4ec4
      refine ⟨_, _, ?_, h⟩
      have hlt := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x4ec2
      xa 2
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xa 5
  xmo 0x4ecc (.reg .mstore) (ri_mstore_imgAt (o := 0x440) rfl)
  xa 2
  xmo 0x4ed1 (.reg .mload) (ri_mload_imgAt (o := 0x440) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xa 9
  have hn32 : (d.returnData.take 32).length ≤ 32 := by rw [List.length_take]; omega
  have hsz : (Bytes.toB256 [0x20] + nW).toNat = 32 + (d.returnData.take 32).length := by
    rw [B256.toNat_add, hn, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  replace h := xa_identity_imgH (pc' := 0x4ee0) (i := 0x440) (n := 32 + (d.returnData.take 32).length)
    (o := 0x240) (z := 32 + (d.returnData.take 32).length) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) hsz (by decide) hsz hR hW h
  clear hR hW
  obtain ⟨d, L5, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b6, G6, M, hsha3, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x4ee3 (.push [0x4e, 0xe8] (by decide)) ri_push
    xji 0x4ee4 0x4ee8 hw
    · xdead
    · exact absurd rfl hw
  have r5 : Region (Bytes.writeAt (Bytes.writeAt img 0x460 (d.returnData.take 32)) 0x440
      nW.toBytes) 0x440 (nW.toBytes ++ d.returnData.take 32) :=
    Region.append' (o' := 0x460) (Region.write_self _ _ _)
      (Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega))
      (by simp only [B256.length_toBytes])
  rw [Region.copy r5 (by simp only [List.length_append, B256.length_toBytes])
    (by simp only [List.length_append, B256.length_toBytes])] at hR
  have hb46 : BaseRel d b6 :=
    ⟨hsha3.stor, hsha3.code, hsha3.addrs, hsha3.logs, hsha3.output, hsha3.error⟩
  clear hsha3 r5
  have e6 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img6, hR, hI⟩ := e6
  have k_keep : ∀ o w, WordAt img o w → (o + 32 ≤ 0x240 ∨ 0x280 ≤ o) →
      (o + 32 ≤ 0x440 ∨ 0x480 ≤ o) → WordAt img6 o w := by
    intro o w hw h1 h2
    rw [hI]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other hw ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, List.length_take, List.length_append] <;> omega
  have k_buf : Region img6 0x240 (nW.toBytes ++ d.returnData.take 32) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI
  xs 0x4ee3 (.push [0x4e, 0xe8] (by decide)) ri_push
  xji 0x4ee4 0x4ee8 hw
  · exact absurd hw (by decide)
  clear hw
  xa 3
  have kr : Region img6 0x260 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x240 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x4f3c (St b6 [3, 0x140] M7 G7) L := by
    xa 2
    xmo 0x4ef1 (.reg .mload) (ri_mload_imgAt (o := 0x240) rfl)
    rw [kn.read] at h
    xa 3
    xji 0x4ef7 0x4f3b hw
    · have hpos := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x0]).toNat = 0 by decide] at hpos
      clear hw
      xa 4
      xmo 0x4eff (.reg .mload) (ri_mload_imgAt (o := 0x260) (by decide))
      xa 2
      xmo 0x4f03 (.reg .mload) (ri_mload_imgAt (o := 0x240) rfl)
      rw [kn.read] at h
      xa 6
      xji 0x4f0d 0x4f11 hw
      · xdead
      clear hw
      xa 7
      xji 0x4f1b 0x4f1f hw
      · xdead
      clear hw
      xa 5
      xs 0x4f28 (.reg .exp) ri_exp
      xa 11
      xji 0x4f36 0x4f3a hq
      · xdead
      xa 2
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := ne_of_eqCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hq)
      have hxs : (img6.sliceD 0x260 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x0]).toNat = 0 by decide] at hz
      xjd 0x4f3c
      refine ⟨.inl ?_, _, _, hR, hW, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, k_keep, h⟩

end Blanc.Lift.Curve3Pool
