import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Curve3Pool.Walk.Donate
import Blanc.Lift.Curve3Pool.Walk.AdminBalancesX
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLoop
import Blanc.Lift.Curve3Pool.Spec
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `donate_admin_fees`, on the actual derivation

From the frame's entry with the `donate_admin_fees` selector (`0x524c3901`) the dispatcher
walks past every earlier arm to the arm's test (`0x4f52`) and falls into its body (`0x4f60`):
the non-payable guard, the owner guard, the counter init at `0x140`, then three iterations.
Each iteration loads `coins[i]` at `keccak(0) + i`, does one `balanceOf(self)` `STATICCALL`
with the output window `0x1e0`, asserts the flag and `RETURNDATASIZE > 31`, and stores the
answer word at `balances[i] = keccak(1) + i`; the tail bumps the counter and loops back
until it reaches `3`, exiting to `STOP`.

`xa_donate` is the frame theorem: a successful frame found no value, spawned exactly three
direct children (coin `k`'s `balanceOf(self)`, static, at least 32 bytes back), wrote the
three answers into `balances[0..2]`, left everything else as the children left it, and
halted with empty output. `donate_raw` is the `<entry>_raw` safety: the model's step on the
decoded call with the `RawEffect` Spec states.

Reuse: the dispatcher walk `xa_dispatch` (`Walk.Dispatch`); `donEnv`, `donate_step`, `fn3` from the lifted-program walk `Walk.Donate`; the `xs`/`xji`/
`xjd`/`xdead` walk macros and `xa_staticcall_img`, `WordAt`/`Region` from `FrameWalkKit`
via `Walk.Kit` (`Walk.Dispatch`); `keccak_zero`/`keccak_one` via `Walk.RemoveLiquidityLoop`;
`EnvOf`/`ReplyAt`/`answerWord` from `Observe.lean`; `RawEffect`/`StorEffect` from `Spec`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## Guards and counter init -/

/-- **Guards of `donate_admin_fees`**: no value, the caller is the owner, the counter at
`0x140` set to `0` with `[3, 0x140]` on the stack, entering the loop at `0x4f84`. -/
theorem donX_guards {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h : XAt sevm post 0x4f60 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    sevm.value = 0 ∧ sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
    ∃ G' M' img', Mem.Wf M' ∧ Mem.Reads M' img' ∧
      Region img' 0x140 (Nat.toB256 0).toBytes ∧
      XAt sevm post 0x4f84
        (St (afterSload sevm b ownerSlot) [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]]
          M' G') L := by
  have hR : Mem.Reads (vyMem Mem.empty (Sevm.dataWord sevm 0))
      (vyImg [] (Sevm.dataWord sevm 0)) :=
    vyMem_reads Mem.wf_empty Mem.reads_empty _
  have hW : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  xa 3
  xji 0x4f66 0x4f6a hw
  · xdead
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 2
  xw 0x4f6e (.reg .sload) ri_sload
  rw [show Bytes.toB256 [4] = ownerSlot from by decide] at h
  xa 3
  xji 0x4f74 0x4f78 hw
  · xdead
  have hown : sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot := by
    have e := B256.eq_of_eqCheck_ne_zero hw
    rw [getStorVal_eq] at e
    exact e
  clear hw
  xa 6
  xmo 0x4f83 (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  have hctrR : Region (Bytes.writeAt (vyImg [] (Sevm.dataWord sevm 0)) 320
      (Bytes.toB256 [0]).toBytes) 0x140 (Nat.toB256 0).toBytes :=
    Region.write_self _ _ _
  xs 0x4f84 (.reg .add) ri_add
  have h30 : Bytes.toB256 [0x03] + Bytes.toB256 [0x00] = Bytes.toB256 [0x03] := by decide
  rw [h30] at h
  exact ⟨hval, hown, _, _, _, hW, hR, hctrR, h⟩

/-! ## The `balanceOf` calldata in the image -/

/-- The `balanceOf(self)` calldata the staging writes leave at `0x17c` (the zero word at
`0xc0` and the counter word at `0x140` are disjoint from the window). -/
theorem donX_input (img : Bytes) (self : Adr) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180 self.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes).sliceD 0x17c 0x24 0) = balanceOfData self := by
  show ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x160
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180 self.toB256.toBytes) 0xc0
    (Bytes.toB256 [0]).toBytes).sliceD 0x17c 0x24 0) = balanceOfSel ++ self.toB256.toBytes
  have hsel : Region (Bytes.writeAt img 0x160 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes)
      0x17c balanceOfSel := by
    have := Region.write_self img 0x160 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
    rw [adminBal_sel_bytes] at this
    exact this.right
  have hsel2 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180 self.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes) 0x17c balanceOfSel :=
    Region.write_other
      (Region.write_other hsel (by simp only [balanceOfSel, B256.length_toBytes,
        List.length_cons, List.length_nil]; omega)) (Or.inr (by decide))
  refine Region.slice (Region.append' (o' := 0x180) ?_ ?_ (by rfl))
    (by simp only [balanceOfSel, List.length_append, B256.length_toBytes, List.length_cons,
      List.length_nil])
  · exact hsel2
  · exact Region.write_other (Region.write_self _ _ _) (Or.inr (by decide))

/-- The answer word the `STATICCALL` wrote at `0x1e0` reads back. -/
theorem donX_read_out (img : Bytes) (out : Bytes) (hlen : (out.take 32).length = 32) :
    Bytes.toB256 ((Bytes.writeAt img 0x1e0 (out.take 32)).sliceD 0x1e0 32 0) =
      Bytes.toB256 (out.take 32) :=
  Region.read (Region.write_self img 0x1e0 (out.take 32)) hlen

/-! ## The loop tail -/

/-- **The `donate_admin_fees` loop tail** (`0x4ff6`): the counter becomes `k + 1`; either
loop back to `0x4f84` (still below `3`) or fall out to `0x5009` (reached `3`). -/
theorem donX_tail {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code)
    (k : Nat) (hk3 : k < 3)
    (hctrR : Region img 0x140 (Nat.toB256 k).toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4ff6
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    (k + 1 < 3 ∧ ∃ G' M' img',
      Region img' 0x140 (Nat.toB256 (k + 1)).toBytes ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      XAt sevm post 0x4f84
        (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L)
    ∨ (k + 1 = 3 ∧ ∃ M' G', XAt sevm post 0x5009 (St d [] M' G') L) := by
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
  xa 2
  xmo 0x4ff9 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 2
  rw [hplus] at h
  xa 2
  xmo 0x4fff (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  have hctrR' : Region (Bytes.writeAt img 0x140 (Nat.toB256 (k + 1)).toBytes) 0x140
      (Nat.toB256 (k + 1)).toBytes :=
    Region.write_self _ _ _
  xa 4
  have h32 : (Bytes.toB256 [0x03]).toNat = 3 := by decide
  have hkp1 : (Nat.toB256 (k + 1)).toNat = k + 1 :=
    B256.toNat_toB256_of_lt (by omega : k + 1 < 2 ^ 256)
  by_cases hdone : k + 1 = 3
  · xji 0x5006 0x4f84 hw
    · xjd 0x5007
      xa 2
      exact Or.inr ⟨hdone, _, _, h⟩
    · have hne := isNe_jump hw
      have h3 : (Bytes.toB256 [0x03]).toNat ≠ (Nat.toB256 (k + 1)).toNat :=
        fun e => hne (B256.toNat_inj _ _ e)
      rw [h32, hkp1] at h3
      omega
  · have hback : k + 1 < 3 := by omega
    xji 0x5006 0x4f84 hw
    · have heq := isNe_fall hw
      have h3 : (Bytes.toB256 [0x03]).toNat = (Nat.toB256 (k + 1)).toNat :=
        congrArg B256.toNat heq
      rw [h32, hkp1] at h3
      omega
    · exact Or.inl ⟨hback, _, _, _, hctrR', hR, hW, h⟩

/-! ## One loop iteration -/

/-- **One `donate_admin_fees` iteration** (`0x4f84 → 0x4ff6`): with the counter at `k`, one
`balanceOf` `STATICCALL`, the answer stored at `balances[k]`. -/
theorem donX_iter {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (k : Fin 3)
    (hctrR : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hcoinK : ¬ sevm.benvStat.rules.isPrecomp
      (((d.getStor sevm.currentTarget).get (coinSlot k)).toAdr))
    (h : XAt sevm post 0x4f84
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ (c : Exec.Frame) (out : Bytes) (L' : List Exec.Frame) (d' : Devm) (M' : Mem)
      (img' : Bytes) (G' : Nat),
      L = c :: L' ∧
      c.sevm.currentTarget = ((d.getStor sevm.currentTarget).get (coinSlot k)).toAdr ∧
      c.sevm.data = balanceOfData sevm.currentTarget ∧
      c.sevm.isStatic = true ∧
      c.post.output = out ∧ 32 ≤ out.length ∧
      c.post.logs = [] ∧
      (d'.getStor sevm.currentTarget).get (balanceSlot k) =
        Bytes.toB256 (out.take 32) ∧
      (∀ x, x ≠ balanceSlot k → (d'.getStor sevm.currentTarget).get x =
        (d.getStor sevm.currentTarget).get x) ∧
      d'.logs = d.logs ∧
      d'.output = d.output ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      XAt sevm post 0x4ff6
        (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L' := by
  xa 6
  xmo 0x4f95 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  have hctrR_A : Region (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR (Or.inl (by simp only [B256.length_toBytes]; omega))
  xa 2
  xmo 0x4f9a (.reg .mstore) (ri_mstore_imgAt (o := 0x180) rfl)
  have hctrR_B : Region (Bytes.writeAt (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180
      sevm.currentTarget.toB256.toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_A (Or.inl (by simp only [B256.length_toBytes]; omega))
  xa 2
  xmo 0x4fa1 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR_B (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 4
  have hltK : Nat.toB256 ↑k < Bytes.toB256 [0x03] := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
      show (Bytes.toB256 [0x03]).toNat = 3 by decide]
    exact k.isLt
  xji 0x4fa9 0x4fad hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hltK)
  clear hw
  xa 3
  xmo 0x4fb3 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  have hctrR_C : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180
      sevm.currentTarget.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_B (Or.inr (by decide))
  xa 2
  xmo 0x4fb8 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x4fb9 (.reg .add) ri_add
  have hslot : coinsBase + Nat.toB256 ↑k = coinSlot k := rfl
  rw [hslot] at h
  xw 0x4fba (.reg .sload) ri_sload
  rw [getStorVal_eq] at h
  xs 0x4fbb (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x4fbc) (i := 0x17c) (n := 0x24) (o := 0x1e0)
    (z := 0x20) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M', L1, h, _, hR, hW, hrd, hob, hstor1, hlogs1, hk⟩ := h
  have hctrR_D : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img
      0x160 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180
      sevm.currentTarget.toB256.toBytes) 0xc0 (Bytes.toB256 [0]).toBytes) 0x1e0
      (out.take 32)) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_C (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4fbf (.push [0x4f, 0xc4] (by decide)) ri_push
  xji 0x4fc0 0x4fc4 hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, -, houtKeep, -, -, htgt, hdata, hstat, hout, hclogs, -, -⟩
  · exact absurd hpre hcoinK
  clear hk hw
  rw [donX_input] at hdata
  xa 5
  xji 0x4fcd 0x4fd1 hw
  · xdead
  have hlen32 : 32 ≤ out.length := by
    have hgt := B256.lt_of_gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, hrd, B256.toNat_toB256_of_lt hob,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at hgt
    omega
  clear hw
  xa 4
  xmo 0x4fd9 (.reg .mload) (ri_mload_imgAt (o := 0x1e0) rfl)
  have hlen : (out.take 32).length = 32 := by rw [List.length_take]; omega
  rw [donX_read_out _ _ hlen] at h
  clear hlen
  xs 0x4fdc (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x4fdd (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR_D (B256.length_toBytes _), B256.toB256_toBytes] at h
  xa 4
  xji 0x4fe5 0x4fe9 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hltK)
  clear hw
  xa 3
  xmo 0x4fef (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  have hctrR_E : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0x160 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180
      sevm.currentTarget.toB256.toBytes) 0xc0 (Bytes.toB256 [0]).toBytes) 0x1e0
      (out.take 32)) 0xc0 (Bytes.toB256 [1]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_D (Or.inr (by decide))
  xa 2
  xmo 0x4ff4 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x4ff5 (.reg .add) ri_add
  have hslotB : balancesBase + Nat.toB256 ↑k = balanceSlot k := rfl
  rw [hslotB] at h
  xw 0x4ff6 (.reg .sstore) ri_sstore
  refine ⟨c, out, L1, _, _, _, _, hL, htgt, hdata, hstat, hout, hlen32, hclogs,
    ?_, ?_, ?_, ?_, hctrR_E, hR, hW, h⟩
  · show (afterSstore sevm d1 (balanceSlot k) (Bytes.toB256 (out.take 32))).getStorVal
      sevm.currentTarget (balanceSlot k) = _
    rw [getStorVal_afterSstore_self, Stor.get_set_self]
  · intro x hx
    show (afterSstore sevm d1 (balanceSlot k) (Bytes.toB256 (out.take 32))).getStorVal
      sevm.currentTarget x = (d.getStor sevm.currentTarget).get x
    rw [getStorVal_afterSstore_ne (Ne.symm hx), getStorVal_eq, hstor1, afterSload_getStor]
  · rw [afterSstore_logs, hlogs1, afterSload_logs]
  · rw [afterSstore_output, houtKeep, afterSload_output]
/-! ## The frame theorem -/

/-- **The `donate_admin_fees` frame**: from the frame's start, past the dispatcher, the
guards and three loop iterations ran: no value; three static children (coin `k`'s
`balanceOf(self)`, at least 32 bytes back); the answers stored at `balances[0..2]`;
everything else kept; logs and output kept; halted at `STOP`. -/
theorem xa_donate {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selDonateAdminFees)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      (((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr))
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    sevm.value = 0 ∧ sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
    ∃ (c0 c1 c2 : Exec.Frame) (out0 out1 out2 : Bytes),
      L = [c0, c1, c2] ∧
      c0.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot 0)).toAdr ∧
      c0.sevm.data = balanceOfData sevm.currentTarget ∧
      c0.sevm.isStatic = true ∧
      c0.post.output = out0 ∧ 32 ≤ out0.length ∧
      c0.post.logs = [] ∧
      c1.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot 1)).toAdr ∧
      c1.sevm.data = balanceOfData sevm.currentTarget ∧
      c1.sevm.isStatic = true ∧
      c1.post.output = out1 ∧ 32 ≤ out1.length ∧
      c1.post.logs = [] ∧
      c2.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot 2)).toAdr ∧
      c2.sevm.data = balanceOfData sevm.currentTarget ∧
      c2.sevm.isStatic = true ∧
      c2.post.output = out2 ∧ 32 ≤ out2.length ∧
      c2.post.logs = [] ∧
      (post.getStor sevm.currentTarget).get (balanceSlot 0) =
        Bytes.toB256 (out0.take 32) ∧
      (post.getStor sevm.currentTarget).get (balanceSlot 1) =
        Bytes.toB256 (out1.take 32) ∧
      (post.getStor sevm.currentTarget).get (balanceSlot 2) =
        Bytes.toB256 (out2.take 32) ∧
      (∀ x, x ≠ balanceSlot 0 → x ≠ balanceSlot 1 → x ≠ balanceSlot 2 →
        (post.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) ∧
      post.logs = b.logs ∧
      post.output = b.output := by
  obtain ⟨G5, h⟩ := xa_dispatch (q := 0x4f60) hcode hlen hcd hsel h
  obtain ⟨hval, hown, G6, M6, img6, hW6, hR6, hctrR6, h⟩ := donX_guards hcode hfork h
  have hcoinK0 : ¬ sevm.benvStat.rules.isPrecomp
      (((afterSload sevm b ownerSlot).getStor sevm.currentTarget).get (coinSlot 0)).toAdr := by
    rw [afterSload_getStor]
    exact hcoin 0
  obtain ⟨c0, out0, L1, d1, M1, img1, G7, hL0, htgt0, hdata0, hstat0, hout0, hlen0,
    hclogs0, hbal0, hkept0, hlogs0, houtD0, hctrR1, hR1, hW1, h⟩ :=
    donX_iter hcode hfork 0 hctrR6 hR6 hW6 hcoinK0 h
  rcases donX_tail hcode 0 (by omega) hctrR1 hR1 hW1 h with backArm | exitArm
  · obtain ⟨-, G8, M8, img8, hctrR8, hR8, hW8, h⟩ := backArm
    have hcoinK1 : ¬ sevm.benvStat.rules.isPrecomp
        (((d1.getStor sevm.currentTarget).get (coinSlot 1)).toAdr) := by
      have e : (d1.getStor sevm.currentTarget).get (coinSlot 1) =
          (b.getStor sevm.currentTarget).get (coinSlot 1) := by
        rw [hkept0 _ (by decide), afterSload_getStor]
      rw [e]
      exact hcoin 1
    obtain ⟨c1, out1, L2, d2, M2, img2, G9, hL1, htgt1, hdata1, hstat1, hout1, hlen1,
      hclogs1, hbal1, hkept1, hlogs1, houtD1, hctrR9, hR9, hW9, h⟩ :=
      donX_iter hcode hfork 1 hctrR8 hR8 hW8 hcoinK1 h
    rcases donX_tail hcode 1 (by omega) hctrR9 hR9 hW9 h with backArm | exitArm
    · obtain ⟨-, G10, M10, img10, hctrR10, hR10, hW10, h⟩ := backArm
      have hcoinK2 : ¬ sevm.benvStat.rules.isPrecomp
          (((d2.getStor sevm.currentTarget).get (coinSlot 2)).toAdr) := by
        have e : (d2.getStor sevm.currentTarget).get (coinSlot 2) =
            (b.getStor sevm.currentTarget).get (coinSlot 2) := by
          rw [hkept1 _ (by decide), hkept0 _ (by decide), afterSload_getStor]
        rw [e]
        exact hcoin 2
      obtain ⟨c2, out2, L3, d3, M3, img3, G11, hL2, htgt2, hdata2, hstat2, hout2,
        hlen2, hclogs2, hbal2, hkept2, hlogs2, houtD2, hctrR11, hR11, hW11, h⟩ :=
        donX_iter hcode hfork 2 hctrR10 hR10 hW10 hcoinK2 h
      rcases donX_tail hcode 2 (by omega) hctrR11 hR11 hW11 h with backArm | exitArm
      · obtain ⟨hback2, _, _, _, _, _, _, _⟩ := backArm
        omega
      · obtain ⟨-, M4, G12, h⟩ := exitArm
        obtain ⟨hrun, hLfin⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
        simp only [Linst.Run, Linst.run] at hrun
        injection hrun with hpost
        have hL : L = [c0, c1, c2] := by rw [hL0, hL1, hL2, hLfin]
        have htgt0' : c0.sevm.currentTarget =
            ((b.getStor sevm.currentTarget).get (coinSlot 0)).toAdr := by
          rw [afterSload_getStor] at htgt0
          exact htgt0
        have e1 : (d1.getStor sevm.currentTarget).get (coinSlot 1) =
            (b.getStor sevm.currentTarget).get (coinSlot 1) := by
          rw [hkept0 _ (by decide), afterSload_getStor]
        have e2 : (d2.getStor sevm.currentTarget).get (coinSlot 2) =
            (b.getStor sevm.currentTarget).get (coinSlot 2) := by
          rw [hkept1 _ (by decide), hkept0 _ (by decide), afterSload_getStor]
        have htgt1' : c1.sevm.currentTarget =
            ((b.getStor sevm.currentTarget).get (coinSlot 1)).toAdr := by
          rw [e1] at htgt1
          exact htgt1
        have htgt2' : c2.sevm.currentTarget =
            ((b.getStor sevm.currentTarget).get (coinSlot 2)).toAdr := by
          rw [e2] at htgt2
          exact htgt2
        have hbal0' : (post.getStor sevm.currentTarget).get (balanceSlot 0) =
            Bytes.toB256 (out0.take 32) := by
          rw [← hpost]
          show (d3.getStor sevm.currentTarget).get (balanceSlot 0) = _
          rw [hkept2 _ (by decide), hkept1 _ (by decide)]
          exact hbal0
        have hbal1' : (post.getStor sevm.currentTarget).get (balanceSlot 1) =
            Bytes.toB256 (out1.take 32) := by
          rw [← hpost]
          show (d3.getStor sevm.currentTarget).get (balanceSlot 1) = _
          rw [hkept2 _ (by decide)]
          exact hbal1
        have hbal2' : (post.getStor sevm.currentTarget).get (balanceSlot 2) =
            Bytes.toB256 (out2.take 32) := by
          rw [← hpost]
          show (d3.getStor sevm.currentTarget).get (balanceSlot 2) = _
          exact hbal2
        have hkept' : ∀ x, x ≠ balanceSlot 0 → x ≠ balanceSlot 1 → x ≠ balanceSlot 2 →
            (post.getStor sevm.currentTarget).get x =
              (b.getStor sevm.currentTarget).get x := by
          intro x h0 h1 h2
          rw [← hpost]
          show (d3.getStor sevm.currentTarget).get x = _
          rw [hkept2 _ h2, hkept1 _ h1, hkept0 _ h0, afterSload_getStor]
        have hlogs' : post.logs = b.logs := by
          rw [← hpost]
          show d3.logs = _
          rw [hlogs2, hlogs1, hlogs0, afterSload_logs]
        have hout' : post.output = b.output := by
          rw [← hpost]
          show d3.output = _
          rw [houtD2, houtD1, houtD0, afterSload_output]
        exact ⟨hval, hown, c0, c1, c2, out0, out1, out2, hL, htgt0', hdata0, hstat0,
          hout0, hlen0, hclogs0, htgt1', hdata1, hstat1, hout1, hlen1, hclogs1,
          htgt2', hdata2, hstat2, hout2, hlen2, hclogs2, hbal0', hbal1', hbal2',
          hkept', hlogs', hout'⟩
    · obtain ⟨hdone1, _, _⟩ := exitArm
      omega
  · obtain ⟨hdone0, _, _⟩ := exitArm
    omega

/-- **Safety of `donate_admin_fees`.** A successful frame of the pool's runtime on the
`donate_admin_fees` selector, entered at a `Checkpoint` with empty stack and memory, under
the frame premises (no coin is a precompile), computed the model's step on the decoded call
in the environment `donEnv` it observed, with the raw effect Spec states. -/
theorem donate_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selDonateAdminFees)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      (((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hval, hown, c0, c1, c2, out0, out1, out2, hL, htgt0, hdata0, hstat0, hout0,
    hlen0, hclogs0, htgt1, hdata1, hstat1, hout1, hlen1, hclogs1, htgt2, hdata2,
    hstat2, hout2, hlen2, hclogs2, hbal0, hbal1, hbal2, hkept, hlogsF, houtF⟩ :=
    xa_donate hcode hfork hlen hcd hsel hcoin hx
  have hdec : decodeCall sevm = .donateAdminFees :=
    decodeCall_at (k := 21) rfl hsel hlen
  have hown' : (quietEnv sevm).caller = s.owner := by
    show sevm.caller.toB256.toNat = s.owner
    rw [hown]
    exact hck.abs.owner
  have hstep := donate_step (fn3 (answerWord out0) (answerWord out1) (answerWord out2))
    hval hown'
  have hchildren : children ⟨0, sevm, pre, .ok post, exc⟩ = [c0, c1, c2] := hL
  refine ⟨donEnv sevm (fn3 (answerWord out0) (answerWord out1) (answerWord out2)),
    ⟨{ s with balances := ⟨answerWord out0, answerWord out1, answerWord out2⟩ },
      none, [], []⟩, ?step, ?raw⟩
  case step =>
    rw [hdec]
    exact hstep
  case raw =>
    have hreply0 : ReplyAt ⟨0, sevm, pre, .ok post, exc⟩ 0
        ((pre.getStor sevm.currentTarget).get (coinSlot 0)).toAdr
        (balanceOfData sevm.currentTarget) (answerWord out0) := by
      refine ⟨c0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchildren]; rfl
      · exact htgt0
      · exact hdata0
      · rw [hout0]; exact hlen0
      · rw [hout0]
    have hreply1 : ReplyAt ⟨0, sevm, pre, .ok post, exc⟩ 1
        ((pre.getStor sevm.currentTarget).get (coinSlot 1)).toAdr
        (balanceOfData sevm.currentTarget) (answerWord out1) := by
      refine ⟨c1, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchildren]; rfl
      · exact htgt1
      · exact hdata1
      · rw [hout1]; exact hlen1
      · rw [hout1]
    have hreply2 : ReplyAt ⟨0, sevm, pre, .ok post, exc⟩ 2
        ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr
        (balanceOfData sevm.currentTarget) (answerWord out2) := by
      refine ⟨c2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchildren]; rfl
      · exact htgt2
      · exact hdata2
      · rw [hout2]; exact hlen2
      · rw [hout2]
    refine ⟨?env, ?stor, ?logs, ?output, ?calls⟩
    case env =>
      refine ⟨rfl, rfl, rfl, fun k => ?_, fun T h => (by cases h), fun h => (by cases h),
        fun h => (by cases h)⟩
      by_cases h0 : k.val = 0
      · have hk0 : k = 0 := Fin.ext h0
        subst hk0
        have hc : (donEnv sevm (fn3 (answerWord out0) (answerWord out1)
            (answerWord out2))).coin 0 =
            ⟨some (answerWord out0), none, false, false⟩ := rfl
        rw [hc]
        refine ⟨fun w' h => ?_, fun w' h => (by cases h), fun h => (by cases h),
          fun h => (by cases h)⟩
        have hw' : answerWord out0 = w' := Option.some_inj.mp h
        subst hw'
        exact Or.inr ⟨0, hreply0⟩
      · by_cases h1 : k.val = 1
        · have hk1 : k = 1 := Fin.ext h1
          subst hk1
          have hc : (donEnv sevm (fn3 (answerWord out0) (answerWord out1)
              (answerWord out2))).coin 1 =
              ⟨some (answerWord out1), none, false, false⟩ := rfl
          rw [hc]
          refine ⟨fun w' h => ?_, fun w' h => (by cases h), fun h => (by cases h),
            fun h => (by cases h)⟩
          have hw' : answerWord out1 = w' := Option.some_inj.mp h
          subst hw'
          exact Or.inr ⟨1, hreply1⟩
        · have hk2 : k = 2 := Fin.ext (by omega)
          subst hk2
          have hc : (donEnv sevm (fn3 (answerWord out0) (answerWord out1)
              (answerWord out2))).coin 2 =
              ⟨some (answerWord out2), none, false, false⟩ := rfl
          rw [hc]
          refine ⟨fun w' h => ?_, fun w' h => (by cases h), fun h => (by cases h),
            fun h => (by cases h)⟩
          have hw' : answerWord out2 = w' := Option.some_inj.mp h
          subst hw'
          exact Or.inr ⟨2, hreply2⟩
    case stor =>
      show StorEffect (decodeCall sevm) (pre.getStor sevm.currentTarget)
        (post.getStor sevm.currentTarget)
        { s with balances := ⟨answerWord out0, answerWord out1, answerWord out2⟩ }
      rw [hdec]
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · exact hkept x (Ne.symm (hx (.bal 0) (by decide)))
          (Ne.symm (hx (.bal 1) (by decide))) (Ne.symm (hx (.bal 2) (by decide)))
      · simp only [footprint, balFlds, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl
        · show ((post.getStor sevm.currentTarget).get (balanceSlot 0)).toNat =
            ({ s with balances :=
              ⟨answerWord out0, answerWord out1, answerWord out2⟩ }).balances.get 0
          rw [hbal0]
          rfl
        · show ((post.getStor sevm.currentTarget).get (balanceSlot 1)).toNat =
            ({ s with balances :=
              ⟨answerWord out0, answerWord out1, answerWord out2⟩ }).balances.get 1
          rw [hbal1]
          rfl
        · show ((post.getStor sevm.currentTarget).get (balanceSlot 2)).toNat =
            ({ s with balances :=
              ⟨answerWord out0, answerWord out1, answerWord out2⟩ }).balances.get 2
          rw [hbal2]
          rfl
    case logs =>
      rw [hlogsF, hchildren]
      simp only [List.flatMap_cons, List.flatMap_nil, hclogs0, hclogs1, hclogs2,
        List.map_nil, List.append_nil]
    case output =>
      rw [houtF]
      simp only [retOut]
    case calls =>
      intro hs
      have hcallsL : CallsOf ⟨0, sevm, pre, .ok post, exc⟩ = [] := by
        rw [CallsOf, hchildren]
        simp only [List.filterMap_cons, List.filterMap_nil, hstat0, hstat1, hstat2,
          ↓reduceIte]
      show CallsOf ⟨0, sevm, pre, .ok post, exc⟩ =
        modelCalls ⟨0, sevm, pre, .ok post, exc⟩ []
      rw [hcallsL]
      simp only [modelCalls, List.map_nil, List.filter_nil]

end Blanc.Lift.Curve3Pool
