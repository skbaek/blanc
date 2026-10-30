import Blanc.Lift.Curve3Pool.Walk.RliLiveD2
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalancePush

/-!
# `remove_liquidity_imbalance`, forward: the transfer loop

The loop of lines 573–575 over the counter at `0x900`: `transfer(msg.sender, amounts[k])` to
`coins[k]` for each nonzero amount, through two identity copies, the `CALL` answered by
`CoinPushOkAt` (window `0xaa0`/`0xb40`) and Vyper's `raw_call` test (`rliPushSite`, join entry
`17`). The certificate's trees depend on the path: iteration 0 runs at `t_3769_c1368`; after a
skip the next head is `t_3769_c1037` (then `t_3769_c1045`), after a transfer it is `t_3769_c48`
(memory grown to `0xb60`). Each `rx_rli_push*` runs one iteration.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The `raw_call` site of the transfers: length word at `0xb20`, copy buffer at `0x920`. -/
def rliPushSite : VyRawSite := ⟨0x0b, 0x20, 0x09, 0x20, 0x38, 0x6b, 0x38, 0x7c, 0x38, 0x7e, 0x38,
  0xa3, 0x38, 0xf6, 0x38, 0xcc, 0x38, 0xda, 0x38, 0xf5⟩

theorem rli_push_join : cert.prog[17]? =
    some (vyRawCallJoin rliPushSite t_389f_c17 t_38c8_c17 t_38d6_c17 t_38f1_c17 t_38f6_c17) := by
  decide +kernel

theorem rli_push_tail_1368 : (SFunc.next (.push [0x38, 0x6b] (by decide))
    (.branch t_3867_c1368 t_386b_c1368)) = vyRawCallTail rliPushSite 17 t_3867_c1368 t_389f_c17
      t_38c8_c17 t_38d6_c17 t_38f1_c17 t_38f6_c17 := rfl

theorem rli_push_tail_1037 : (SFunc.next (.push [0x38, 0x6b] (by decide))
    (.branch t_3867_c1037 t_386b_c1037)) = vyRawCallTail rliPushSite 17 t_3867_c1037 t_389f_c17
      t_38c8_c17 t_38d6_c17 t_38f1_c17 t_38f6_c17 := rfl

theorem rli_push_tail_1045 : (SFunc.next (.push [0x38, 0x6b] (by decide))
    (.branch t_3867_c1045 t_386b_c1045)) = vyRawCallTail rliPushSite 17 t_3867_c1045 t_389f_c17
      t_38c8_c17 t_38d6_c17 t_38f1_c17 t_38f6_c17 := rfl

theorem rli_push_tail_48 : (SFunc.next (.push [0x38, 0x6b] (by decide))
    (.branch t_3867_c48 t_386b_c48)) = vyRawCallTail rliPushSite 17 t_3867_c48 t_389f_c17
      t_38c8_c17 t_38d6_c17 t_38f1_c17 t_38f6_c17 := rfl

/-- The selector the transfer payload's first identity copy moves. -/
theorem rli_push_sel (img : Bytes) :
    ((Bytes.writeAt img 0x9a0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes).sliceD 0x9a0 4 0).take 4 =
      transferSel := by
  rw [(WordAt.write_self _ _ _).prefix (by decide)]; decide

theorem rli_prog_1037 : cert.prog[1037]? = some t_3769_c1037 := by decide +kernel

theorem rli_prog_1045 : cert.prog[1045]? = some t_3769_c1045 := by decide +kernel

theorem rli_prog_48 : cert.prog[48]? = some t_3769_c48 := by decide +kernel

/-- The transfer loop's exit. -/
abbrev rliEnd : SFunc := t_3908_c17

theorem rli_end_1045 : t_3908_c1045 = rliEnd := rfl


/-! ## The transfer's canonical data

`rliPushId1`/`rliPushId2` name the canonical base after the payload's two identity copies
(`identityCallNext`, at the copies' literal stacks and memories), `rliPushMemC` the literal
memory the `transfer` call runs over. -/

/-- The transfer payload's memory at its first identity copy: the selector's length word `4`
at `0x980`, the padded `transfer` selector at `0x9a0`. -/
def rliPushMem1 (M : Mem) : Mem :=
  (M.write 0x980 (Bytes.toB256 [4]).toBytes).write 0x9a0 (Bytes.toB256 [169, 5, 156, 187, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toBytes

/-- The canonical base after the first identity copy (the selector). -/
def rliPushId1 (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) : Devm :=
  identityCallNext sevm b (Bytes.toB256 [4] :: Bytes.toB256 [9, 128] :: Bytes.toB256 [0] ::
    (Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) (rliPushMem1 M)
    (Bytes.toB256 [9, 128] + Bytes.toB256 [32]) (Bytes.toB256 [4])
    (Bytes.toB256 [9, 224] + Bytes.toB256 [0] + Bytes.toB256 [32]) (Bytes.toB256 [4])

/-- The payload's copy length word (`0x64`), as the bytecode computes it. -/
abbrev rliPushLen : B256 :=
  Bytes.toB256 [32] + (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32])

/-- The payload's memory at its second identity copy: the copied selector at `0xa00`, the
caller at `0xa04`, amount `k` at `0xa24`, the payload length word at `0x9e0`. -/
def rliPushMem2 (sevm : Sevm) (M : Mem) (k : Nat) : Mem :=
  (((((rliPushMem1 M).extends [(0x9a0, 4), (0xa00, 4)]).write 0xa00
    (((rliPushMem1 M).read 0x9a0 4).1.take 4)).write 0xa04 sevm.caller.toB256.toBytes).write 0xa24
    (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 k + Bytes.toB256 [4])).toBytes).write 0x9e0
    (Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32]).toBytes

/-- The canonical base after the second identity copy (the whole calldata). -/
def rliPushId2 (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (k : Nat) : Devm :=
  identityCallNext sevm (rliPushId1 sevm b S M) (rliPushLen :: Bytes.toB256 [9, 224] ::
    (Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) (rliPushMem2 sevm M k)
    (Bytes.toB256 [9, 224]) rliPushLen (Bytes.toB256 [10, 128]) rliPushLen

/-- The memory the `transfer` of amount `k` runs over: both copies done, the key word at
`0xc0` for `coins[k]`. -/
def rliPushMemC (sevm : Sevm) (M : Mem) (k : Nat) : Mem :=
  (((rliPushMem2 sevm M k).extends [(0x9e0, 0x64), (0xa80, 0x64)]).write 0xa80
    (((rliPushMem2 sevm M k).read 0x9e0 0x64).1.take 0x64)).write 0xc0 (Bytes.toB256 [0]).toBytes

/-- Transfer iteration 0 at `t_3769_c1368`, forward, exact (core of `rx_rli_push0`). -/
theorem rx_rli_push0E {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hc : WordAt img 0x900 (Nat.toB256 0))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])) ≠ 0 → MutCallOkAtE sevm W W' (σ.get (coinsBase + Nat.toB256 0))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 E)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 1) → R ≤ g → g ≤ G →
      G = g + 114 → b' = b → M' = M.write 0x900 (Bytes.toB256 [1] + Nat.toB256 0).toBytes →
      rliAmt sevm 0 = 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c1037 Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 1) → R ≤ g → g ≤ G →
      ∀ (bI : Devm) (Gs : Nat) (d : Devm), Devm.EqModGas bI (rliPushId2 sevm b S M 0) →
      E (afterSload sevm bI (coinsBase + Nat.toB256 0)) ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) (rliPushMemC sevm M 0) Gs d →
      G = Gs + (732 + sloadCost sevm bI (coinsBase + Nat.toB256 0) + 2) →
      d.gasLeft = g + 46 + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) d.memory rliPushSite) →
      M' = (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).write 0x900 (Bytes.toB256 [1] + Nat.toB256 0).toBytes →
      rliAmt sevm 0 ≠ 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c48 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c1368 Q := by
  have hk : (Nat.toB256 0).toNat < 3 := by decide
  by_cases hz : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])) = 0
  · -- `amounts[0] == 0`: skipped
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + 114 := ⟨G - 114, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_calldataload (by hrs) ·)
    xr (rx_xor rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by rw [hz]; decide) ·)
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x920 0x900 32 = 0x920 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branchTo_succ (by decide) (g := t_3769_c1037) rli_prog_1037 ·)
    exact kS _ M _ _ (hL.mono hW'c (hskip hz)) hR hW hsz (fun o v h ho => by wautoH h) (by wauto) (by omega) (by omega)
      (by omega) rfl hMq1 hz
  · -- the transfer
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + 732 := ⟨G - 732, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_calldataload (by hrs) ·)
    xr (rx_xor rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_zero' (by rw [zero_lit, B256.xor_zero]; unfold B256.eqCheck; rw [if_neg hz]) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x980) (c := 16) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x920 0x980 32 = 0x9a0 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x9a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0x9a0 0x9a0 32 = 0x9c0 by decide] at hsz
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
    refine rxe_identityL (i := 0x9a0) (n := 0x4) (o := 0xa00) (z := 0x4) (ext := 10) (X := 128) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 10 + 64 * idCost 0x4 = 1262 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqA; intro bI1 M hsha hcan1 hMqA hR hW hsz; rw [show memExtsSize 0x9c0 [(0x9a0, 0x4), (0xa00, 0x4)] = 0xa20 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
    rw [rli_push_sel] at hR
    xr (rx_pop ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mload (o := 0x980) hR hsz rfl (by decide) (by hrs) ·); try wsimp
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
    refine rxe_mstoreL (o := 0xa04) (c := 7) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0xa20 0xa04 32 = 0xa40 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
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
    refine rxe_mstoreL (o := 0xa24) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0xa40 0xa24 32 = 0xa60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x9e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0xa60 0x9e0 32 = 0xa60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mload (o := 0x9e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_gas (by hrs) ·)
    refine rxe_identityL (i := 0x9e0) (n := 0x64) (o := 0xa80) (z := 0x64) (ext := 17) (X := 144) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 17 + 64 * idCost 0x64 = 1845 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqB; intro bI2 M hsha hcan2 hMqB hR hW hsz; rw [show memExtsSize 0xa60 [(0x9e0, 0x64), (0xa80, 0x64)] = 0xb00 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
    rw [rli_transfer_copy2] at hR
    obtain ⟨img3, hR3, hI⟩ := Mem.Reads.forget hR
    clear hR
    have hR := hR3
    clear hR3
    have hdata : Region img3 0xa80 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])).toBytes)) := by
      rw [hI]; exact Region.write_self _ _ _
    have hc3 : WordAt img3 0x900 (Nat.toB256 0) := by rw [hI]; wautoH hc
    have hk3 : ∀ o v, WordAt img o v → 0xe0 ≤ o → o + 32 ≤ 0x900 → WordAt img3 o v :=
      fun o v h h1 h2 => by rw [hI]; wautoH h
    clear hI
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by xbr) ·)
    xr (rx_dest ·)
    xr (rx_pop ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0xa80) hR hsz rfl (by decide) (by hrs) ·)
    rw [(Region.word hdata.left).read]
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc3) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [show memExtSize 0xb00 0xc0 32 = 0xb00 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
    rw [keccak_zero]
    xr (rx_add (by hrs) ·)
    refine rxe_sloadVX hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 g2x; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
    obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 2 := ⟨g2 - 2, by omega⟩
    xr (rx_gas (by hrs) ·)
    rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] =
        (0x44 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
      show Bytes.toB256 [0x0a, 0xa0] = (0xaa0 : B256) by decide,
      show Bytes.toB256 [0x0b, 0x40] = (0xb40 : B256) by decide,
      show Bytes.toB256 [32] = (0x20 : B256) by decide]
    subst hv2
    have hin : (M.read 0xaa0 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])).toBytes := by
      rw [hR.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp only [B256.length_toBytes]; omega)]
      exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
    obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
      hpush hz b2 ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) M g3 hL.w (by omega) (by omega) hin (by hrs)
    xr (.next hrun ·)
    obtain ⟨hmem, -⟩ := hpost.settled (by decide)
    rw [show (0xaa0 : B256).toNat = 0xaa0 by decide, show (0x44 : B256).toNat = 0x44 by decide,
      show (0xb40 : B256).toNat = 0xb40 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
    have hd : d = St d (1 :: _) d.memory d.gasLeft := St.self hpost.stack rfl
    rw [hd, rli_push_tail_1368]
    have hext : (M.extends [(0xaa0, 0x44), (0xb40, 0x20)]).size = 0xb60 := by
      show memExtsSize M.size _ = _
      rw [hsz]; decide
    have hsz5 : d.memory.size = 0xb60 := by
      rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
    have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
        0xb40 (d.returnData.take 0x20)) := by
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
      hdepth (by decide) rli_push_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
      ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega)
      (by hrs) ?_)
    · rw [show (Bytes.toB256 [rliPushSite.lh, rliPushSite.ll]).toNat + 32 = 0xb40 by decide]
      intro j hj
      exact (rawCall_window hmem rfl j hj).2
    intro b' rd' hsha hcanT
    refine SFunc.runEx_iff_runExCut_nil.mp ?_
    rw [show (Bytes.toB256 [rliPushSite.lh, rliPushSite.ll]).toNat = 0xb20 by decide,
      show (Bytes.toB256 [rliPushSite.bh, rliPushSite.bl]).toNat = 0x920 by decide]
    have hn32 : min d.returnData.length 32 ≤ 32 := by omega
    have hR6 : Mem.Reads (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32))
        (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
          0xb40 (d.returnData.take 0x20)) 0xb20
          (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x920 ((Bytes.writeAt (Bytes.writeAt
          (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes) 0xb40 (d.returnData.take 0x20)) 0xb20
          (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0xb20
          (min d.returnData.length 32 + 32) 0)) := by
      unfold vyRawMem
      rw [(hR5.write hW5 _ _).read]
      exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
    have hW6 : Mem.Wf (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)) := by
      unfold vyRawMem; exact (hW5.write _ _).write _ _
    have hsz6 : (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).size = 0xb60 := by
      unfold vyRawMem
      have h1 : (d.memory.write 0xb20 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
          0xb60 := by
        rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
      rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
    obtain ⟨img6, hR, hI⟩ := Mem.Reads.forget hR6
    have hc6 : WordAt img6 0x900 (Nat.toB256 0) := by
      rw [hI]
      refine WordAt.write_other ?_ (by simp only [List.length_sliceD]; omega)
      wautoH hc3
    have hk6 : ∀ o v, WordAt img o v → 0xe0 ≤ o → o + 32 ≤ 0x900 → WordAt img6 o v := by
      intro o v h h1 h2
      rw [hI]
      refine WordAt.write_other ?_ (by simp only [List.length_sliceD]; omega)
      have := hk3 o v h h1 h2
      wautoH this
    clear hI hR6
    have hW := hW6
    have hsz := hsz6
    replace hL := hLd.sha hsha
    clear hW6 hsz6 hR5 hW5 hmem
    obtain ⟨g8, rfl⟩ : ∃ g, G2 = g + 46 := ⟨G2 - 46, by omega⟩
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc6) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0xb60 0x900 32 = 0xb60 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branchTo_succ (by decide) (g := t_3769_c48) rli_prog_48 ·)
    refine kT _ M _ _ hL hR hW hsz (fun o v h ho => by wautoH (hk6 o v h ho.1 ho.2)) (by wauto)
      (by omega) (by omega) bI2 g3 d ?_ ?_ (by omega) (by omega) hcanT hMq7 hz
    · rw [hMq5, hMq4, hMq3, hMqA, hMq2, hMq1] at hcan2
      rw [hMq2, hMq1] at hcan1
      exact hcan2.trans (identityCallNext_congr sevm _ _ _ _ _ _ hcan1)
    · rw [hMq6, hMqB, hMq5, hMq4, hMq3, hMqA, hMq2, hMq1] at hE
      rw [hb2] at hE
      exact hE

/-- Transfer iteration 1 at `t_3769_c1037`, forward, exact (core of `rx_rli_push1a`). -/
theorem rx_rli_push1aE {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hc : WordAt img 0x900 (Nat.toB256 1))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) ≠ 0 → MutCallOkAtE sevm W W' (σ.get (coinsBase + Nat.toB256 1))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 E)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → R ≤ g → g ≤ G →
      G = g + 114 → b' = b → M' = M.write 0x900 (Bytes.toB256 [1] + Nat.toB256 1).toBytes →
      rliAmt sevm 1 = 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c1045 Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → R ≤ g → g ≤ G →
      ∀ (bI : Devm) (Gs : Nat) (d : Devm), Devm.EqModGas bI (rliPushId2 sevm b S M 1) →
      E (afterSload sevm bI (coinsBase + Nat.toB256 1)) ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) (rliPushMemC sevm M 1) Gs d →
      G = Gs + (732 + sloadCost sevm bI (coinsBase + Nat.toB256 1) + 2) →
      d.gasLeft = g + 46 + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) d.memory rliPushSite) →
      M' = (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).write 0x900 (Bytes.toB256 [1] + Nat.toB256 1).toBytes →
      rliAmt sevm 1 ≠ 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c48 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c1037 Q := by
  have hk : (Nat.toB256 1).toNat < 3 := by decide
  by_cases hz : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) = 0
  · -- `amounts[1] == 0`: skipped
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + 114 := ⟨G - 114, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_calldataload (by hrs) ·)
    xr (rx_xor rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by rw [hz]; decide) ·)
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x920 0x900 32 = 0x920 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branchTo_succ (by decide) (g := t_3769_c1045) rli_prog_1045 ·)
    exact kS _ M _ _ (hL.mono hW'c (hskip hz)) hR hW hsz (fun o v h ho => by wautoH h) (by wauto) (by omega) (by omega)
      (by omega) rfl hMq1 hz
  · -- the transfer
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + 732 := ⟨G - 732, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_calldataload (by hrs) ·)
    xr (rx_xor rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_zero' (by rw [zero_lit, B256.xor_zero]; unfold B256.eqCheck; rw [if_neg hz]) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x980) (c := 16) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x920 0x980 32 = 0x9a0 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x9a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0x9a0 0x9a0 32 = 0x9c0 by decide] at hsz
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
    refine rxe_identityL (i := 0x9a0) (n := 0x4) (o := 0xa00) (z := 0x4) (ext := 10) (X := 128) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 10 + 64 * idCost 0x4 = 1262 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqA; intro bI1 M hsha hcan1 hMqA hR hW hsz; rw [show memExtsSize 0x9c0 [(0x9a0, 0x4), (0xa00, 0x4)] = 0xa20 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
    rw [rli_push_sel] at hR
    xr (rx_pop ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mload (o := 0x980) hR hsz rfl (by decide) (by hrs) ·); try wsimp
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
    refine rxe_mstoreL (o := 0xa04) (c := 7) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0xa20 0xa04 32 = 0xa40 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
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
    refine rxe_mstoreL (o := 0xa24) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0xa40 0xa24 32 = 0xa60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x9e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0xa60 0x9e0 32 = 0xa60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mload (o := 0x9e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_gas (by hrs) ·)
    refine rxe_identityL (i := 0x9e0) (n := 0x64) (o := 0xa80) (z := 0x64) (ext := 17) (X := 144) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 17 + 64 * idCost 0x64 = 1845 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqB; intro bI2 M hsha hcan2 hMqB hR hW hsz; rw [show memExtsSize 0xa60 [(0x9e0, 0x64), (0xa80, 0x64)] = 0xb00 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
    rw [rli_transfer_copy2] at hR
    obtain ⟨img3, hR3, hI⟩ := Mem.Reads.forget hR
    clear hR
    have hR := hR3
    clear hR3
    have hdata : Region img3 0xa80 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])).toBytes)) := by
      rw [hI]; exact Region.write_self _ _ _
    have hc3 : WordAt img3 0x900 (Nat.toB256 1) := by rw [hI]; wautoH hc
    have hk3 : ∀ o v, WordAt img o v → 0xe0 ≤ o → o + 32 ≤ 0x900 → WordAt img3 o v :=
      fun o v h h1 h2 => by rw [hI]; wautoH h
    clear hI
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by xbr) ·)
    xr (rx_dest ·)
    xr (rx_pop ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0xa80) hR hsz rfl (by decide) (by hrs) ·)
    rw [(Region.word hdata.left).read]
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc3) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [show memExtSize 0xb00 0xc0 32 = 0xb00 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
    rw [keccak_zero]
    xr (rx_add (by hrs) ·)
    refine rxe_sloadVX hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 g2x; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
    obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 2 := ⟨g2 - 2, by omega⟩
    xr (rx_gas (by hrs) ·)
    rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] =
        (0x44 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
      show Bytes.toB256 [0x0a, 0xa0] = (0xaa0 : B256) by decide,
      show Bytes.toB256 [0x0b, 0x40] = (0xb40 : B256) by decide,
      show Bytes.toB256 [32] = (0x20 : B256) by decide]
    subst hv2
    have hin : (M.read 0xaa0 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])).toBytes := by
      rw [hR.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp only [B256.length_toBytes]; omega)]
      exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
    obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
      hpush hz b2 ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) M g3 hL.w (by omega) (by omega) hin (by hrs)
    xr (.next hrun ·)
    obtain ⟨hmem, -⟩ := hpost.settled (by decide)
    rw [show (0xaa0 : B256).toNat = 0xaa0 by decide, show (0x44 : B256).toNat = 0x44 by decide,
      show (0xb40 : B256).toNat = 0xb40 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
    have hd : d = St d (1 :: _) d.memory d.gasLeft := St.self hpost.stack rfl
    rw [hd, rli_push_tail_1037]
    have hext : (M.extends [(0xaa0, 0x44), (0xb40, 0x20)]).size = 0xb60 := by
      show memExtsSize M.size _ = _
      rw [hsz]; decide
    have hsz5 : d.memory.size = 0xb60 := by
      rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
    have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
        0xb40 (d.returnData.take 0x20)) := by
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
      hdepth (by decide) rli_push_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
      ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega)
      (by hrs) ?_)
    · rw [show (Bytes.toB256 [rliPushSite.lh, rliPushSite.ll]).toNat + 32 = 0xb40 by decide]
      intro j hj
      exact (rawCall_window hmem rfl j hj).2
    intro b' rd' hsha hcanT
    refine SFunc.runEx_iff_runExCut_nil.mp ?_
    rw [show (Bytes.toB256 [rliPushSite.lh, rliPushSite.ll]).toNat = 0xb20 by decide,
      show (Bytes.toB256 [rliPushSite.bh, rliPushSite.bl]).toNat = 0x920 by decide]
    have hn32 : min d.returnData.length 32 ≤ 32 := by omega
    have hR6 : Mem.Reads (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32))
        (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
          0xb40 (d.returnData.take 0x20)) 0xb20
          (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x920 ((Bytes.writeAt (Bytes.writeAt
          (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes) 0xb40 (d.returnData.take 0x20)) 0xb20
          (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0xb20
          (min d.returnData.length 32 + 32) 0)) := by
      unfold vyRawMem
      rw [(hR5.write hW5 _ _).read]
      exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
    have hW6 : Mem.Wf (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)) := by
      unfold vyRawMem; exact (hW5.write _ _).write _ _
    have hsz6 : (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).size = 0xb60 := by
      unfold vyRawMem
      have h1 : (d.memory.write 0xb20 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
          0xb60 := by
        rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
      rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
    obtain ⟨img6, hR, hI⟩ := Mem.Reads.forget hR6
    have hc6 : WordAt img6 0x900 (Nat.toB256 1) := by
      rw [hI]
      refine WordAt.write_other ?_ (by simp only [List.length_sliceD]; omega)
      wautoH hc3
    have hk6 : ∀ o v, WordAt img o v → 0xe0 ≤ o → o + 32 ≤ 0x900 → WordAt img6 o v := by
      intro o v h h1 h2
      rw [hI]
      refine WordAt.write_other ?_ (by simp only [List.length_sliceD]; omega)
      have := hk3 o v h h1 h2
      wautoH this
    clear hI hR6
    have hW := hW6
    have hsz := hsz6
    replace hL := hLd.sha hsha
    clear hW6 hsz6 hR5 hW5 hmem
    obtain ⟨g8, rfl⟩ : ∃ g, G2 = g + 46 := ⟨G2 - 46, by omega⟩
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc6) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0xb60 0x900 32 = 0xb60 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branchTo_succ (by decide) (g := t_3769_c48) rli_prog_48 ·)
    refine kT _ M _ _ hL hR hW hsz (fun o v h ho => by wautoH (hk6 o v h ho.1 ho.2)) (by wauto)
      (by omega) (by omega) bI2 g3 d ?_ ?_ (by omega) (by omega) hcanT hMq7 hz
    · rw [hMq5, hMq4, hMq3, hMqA, hMq2, hMq1] at hcan2
      rw [hMq2, hMq1] at hcan1
      exact hcan2.trans (identityCallNext_congr sevm _ _ _ _ _ _ hcan1)
    · rw [hMq6, hMqB, hMq5, hMq4, hMq3, hMqA, hMq2, hMq1] at hE
      rw [hb2] at hE
      exact hE

/-- **One transfer iteration, forward, at any counter `k < 3`** from the grown memory at
`t_3769_c48`: on through the back edges `hBS` (skipped) and `hBT` (the transfer). -/
theorem rx_rli_pushG {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop} {k : Nat} {gS gT : SFunc} (hk3 : k < 3)
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xb60)
    (hc : WordAt img 0x900 (Nat.toB256 k))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 k + Bytes.toB256 [4])) ≠ 0 → MutCallOkAtE sevm W W' (σ.get (coinsBase + Nat.toB256 k))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 k + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 E)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 k + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 (k + 1)) → R ≤ g → g ≤ G →
      G = g + 114 → b' = b → M' = M.write 0x900 (Bytes.toB256 [1] + Nat.toB256 k).toBytes →
      rliAmt sevm k = 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) gS Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 (k + 1)) → R ≤ g → g ≤ G →
      ∀ (bI : Devm) (Gs : Nat) (d : Devm), Devm.EqModGas bI (rliPushId2 sevm b S M k) →
      E (afterSload sevm bI (coinsBase + Nat.toB256 k)) ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) (rliPushMemC sevm M k) Gs d →
      G = Gs + (682 + sloadCost sevm bI (coinsBase + Nat.toB256 k) + 2) →
      d.gasLeft = g + 46 + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) d.memory rliPushSite) →
      M' = (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).write 0x900 (Bytes.toB256 [1] + Nat.toB256 k).toBytes →
      rliAmt sevm k ≠ 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) gT Q)
    (hBS : RliLoopB sevm (Bytes.toB256 [9, 0] :: S) (Bytes.toB256 [0x37, 0x69]) k Q
      (.branchTo t_3908_c48 48) gS)
    (hBT : RliLoopB sevm (Bytes.toB256 [9, 0] :: S) (Bytes.toB256 [0x37, 0x69]) k Q
      (.branchTo t_3908_c17 48) gT) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c48 Q := by
  have hk : (Nat.toB256 k).toNat < 3 := by rw [B256.toNat_toB256_of_lt (by omega)]; exact hk3
  have hk1 : Bytes.toB256 [1] + Nat.toB256 k = Nat.toB256 (k + 1) := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals decide
  by_cases hz : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 k + Bytes.toB256 [4])) = 0
  · -- `amounts[1] == 0`: skipped
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + 114 := ⟨G - 114, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_calldataload (by hrs) ·)
    xr (rx_xor rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by rw [hz]; decide) ·)
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0xb60 0x900 32 = 0xb60 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine hBS _ _ _ ?_
    exact kS _ M _ _ (hL.mono hW'c (hskip hz)) hR hW hsz (fun o v h ho => by wautoH h) (by rw [← hk1]; wauto) (by omega) (by omega)
      (by omega) rfl hMq1 hz
  · -- the transfer
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + 682 := ⟨G - 682, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_calldataload (by hrs) ·)
    xr (rx_xor rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_zero' (by rw [zero_lit, B256.xor_zero]; unfold B256.eqCheck; rw [if_neg hz]) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x980) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0xb60 0x980 32 = 0xb60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x9a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0xb60 0x9a0 32 = 0xb60 by decide] at hsz
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
    refine rxe_identityL (i := 0x9a0) (n := 0x4) (o := 0xa00) (z := 0x4) (ext := 0) (X := 118) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 0 + 64 * idCost 0x4 = 1252 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqA; intro bI1 M hsha hcan1 hMqA hR hW hsz; rw [show memExtsSize 0xb60 [(0x9a0, 0x4), (0xa00, 0x4)] = 0xb60 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
    rw [rli_push_sel] at hR
    xr (rx_pop ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mload (o := 0x980) hR hsz rfl (by decide) (by hrs) ·); try wsimp
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
    refine rxe_mstoreL (o := 0xa04) (c := 3) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0xb60 0xa04 32 = 0xb60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
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
    refine rxe_mstoreL (o := 0xa24) (c := 3) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0xb60 0xa24 32 = 0xb60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x9e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0xb60 0x9e0 32 = 0xb60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mload (o := 0x9e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_gas (by hrs) ·)
    refine rxe_identityL (i := 0x9e0) (n := 0x64) (o := 0xa80) (z := 0x64) (ext := 0) (X := 127) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 0 + 64 * idCost 0x64 = 1828 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqB; intro bI2 M hsha hcan2 hMqB hR hW hsz; rw [show memExtsSize 0xb60 [(0x9e0, 0x64), (0xa80, 0x64)] = 0xb60 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
    rw [rli_transfer_copy2] at hR
    obtain ⟨img3, hR3, hI⟩ := Mem.Reads.forget hR
    clear hR
    have hR := hR3
    clear hR3
    have hdata : Region img3 0xa80 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 k + Bytes.toB256 [4])).toBytes)) := by
      rw [hI]; exact Region.write_self _ _ _
    have hc3 : WordAt img3 0x900 (Nat.toB256 k) := by rw [hI]; wautoH hc
    have hk3 : ∀ o v, WordAt img o v → 0xe0 ≤ o → o + 32 ≤ 0x900 → WordAt img3 o v :=
      fun o v h h1 h2 => by rw [hI]; wautoH h
    clear hI
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by xbr) ·)
    xr (rx_dest ·)
    xr (rx_pop ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0xa80) hR hsz rfl (by decide) (by hrs) ·)
    rw [(Region.word hdata.left).read]
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc3) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [show memExtSize 0xb60 0xc0 32 = 0xb60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
    rw [keccak_zero]
    xr (rx_add (by hrs) ·)
    refine rxe_sloadVX hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 g2x; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
    obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 2 := ⟨g2 - 2, by omega⟩
    xr (rx_gas (by hrs) ·)
    rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] =
        (0x44 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
      show Bytes.toB256 [0x0a, 0xa0] = (0xaa0 : B256) by decide,
      show Bytes.toB256 [0x0b, 0x40] = (0xb40 : B256) by decide,
      show Bytes.toB256 [32] = (0x20 : B256) by decide]
    subst hv2
    have hin : (M.read 0xaa0 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 k + Bytes.toB256 [4])).toBytes := by
      rw [hR.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp only [B256.length_toBytes]; omega)]
      exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
    obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
      hpush hz b2 ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) M g3 hL.w (by omega) (by omega) hin (by hrs)
    xr (.next hrun ·)
    obtain ⟨hmem, -⟩ := hpost.settled (by decide)
    rw [show (0xaa0 : B256).toNat = 0xaa0 by decide, show (0x44 : B256).toNat = 0x44 by decide,
      show (0xb40 : B256).toNat = 0xb40 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
    have hd : d = St d (1 :: _) d.memory d.gasLeft := St.self hpost.stack rfl
    rw [hd, rli_push_tail_48]
    have hext : (M.extends [(0xaa0, 0x44), (0xb40, 0x20)]).size = 0xb60 := by
      show memExtsSize M.size _ = _
      rw [hsz]; decide
    have hsz5 : d.memory.size = 0xb60 := by
      rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
    have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
        0xb40 (d.returnData.take 0x20)) := by
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
      hdepth (by decide) rli_push_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
      ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega)
      (by hrs) ?_)
    · rw [show (Bytes.toB256 [rliPushSite.lh, rliPushSite.ll]).toNat + 32 = 0xb40 by decide]
      intro j hj
      exact (rawCall_window hmem rfl j hj).2
    intro b' rd' hsha hcanT
    refine SFunc.runEx_iff_runExCut_nil.mp ?_
    rw [show (Bytes.toB256 [rliPushSite.lh, rliPushSite.ll]).toNat = 0xb20 by decide,
      show (Bytes.toB256 [rliPushSite.bh, rliPushSite.bl]).toNat = 0x920 by decide]
    have hn32 : min d.returnData.length 32 ≤ 32 := by omega
    have hR6 : Mem.Reads (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32))
        (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
          0xb40 (d.returnData.take 0x20)) 0xb20
          (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x920 ((Bytes.writeAt (Bytes.writeAt
          (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes) 0xb40 (d.returnData.take 0x20)) 0xb20
          (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0xb20
          (min d.returnData.length 32 + 32) 0)) := by
      unfold vyRawMem
      rw [(hR5.write hW5 _ _).read]
      exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
    have hW6 : Mem.Wf (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)) := by
      unfold vyRawMem; exact (hW5.write _ _).write _ _
    have hsz6 : (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).size = 0xb60 := by
      unfold vyRawMem
      have h1 : (d.memory.write 0xb20 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
          0xb60 := by
        rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
      rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
    obtain ⟨img6, hR, hI⟩ := Mem.Reads.forget hR6
    have hc6 : WordAt img6 0x900 (Nat.toB256 k) := by
      rw [hI]
      refine WordAt.write_other ?_ (by simp only [List.length_sliceD]; omega)
      wautoH hc3
    have hk6 : ∀ o v, WordAt img o v → 0xe0 ≤ o → o + 32 ≤ 0x900 → WordAt img6 o v := by
      intro o v h h1 h2
      rw [hI]
      refine WordAt.write_other ?_ (by simp only [List.length_sliceD]; omega)
      have := hk3 o v h h1 h2
      wautoH this
    clear hI hR6
    have hW := hW6
    have hsz := hsz6
    replace hL := hLd.sha hsha
    clear hW6 hsz6 hR5 hW5 hmem
    obtain ⟨g8, rfl⟩ : ∃ g, G2 = g + 46 := ⟨G2 - 46, by omega⟩
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 k) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc6) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0xb60 0x900 32 = 0xb60 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine hBT _ _ _ ?_
    refine kT _ M _ _ hL hR hW hsz (fun o v h ho => by wautoH (hk6 o v h ho.1 ho.2)) (by rw [← hk1]; wauto)
      (by omega) (by omega) bI2 g3 d ?_ ?_ (by omega) (by omega) hcanT hMq7 hz
    · rw [hMq5, hMq4, hMq3, hMqA, hMq2, hMq1] at hcan2
      rw [hMq2, hMq1] at hcan1
      exact hcan2.trans (identityCallNext_congr sevm _ _ _ _ _ _ hcan1)
    · rw [hMq6, hMqB, hMq5, hMq4, hMq3, hMqA, hMq2, hMq1] at hE
      rw [hb2] at hE
      exact hE

/-- Transfer iteration 1 at `t_3769_c48`, forward, exact (core of `rx_rli_push1b`). -/
theorem rx_rli_push1bE {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xb60)
    (hc : WordAt img 0x900 (Nat.toB256 1))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) ≠ 0 → MutCallOkAtE sevm W W' (σ.get (coinsBase + Nat.toB256 1))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 E)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → R ≤ g → g ≤ G →
      G = g + 114 → b' = b → M' = M.write 0x900 (Bytes.toB256 [1] + Nat.toB256 1).toBytes →
      rliAmt sevm 1 = 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c48 Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → R ≤ g → g ≤ G →
      ∀ (bI : Devm) (Gs : Nat) (d : Devm), Devm.EqModGas bI (rliPushId2 sevm b S M 1) →
      E (afterSload sevm bI (coinsBase + Nat.toB256 1)) ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) (rliPushMemC sevm M 1) Gs d →
      G = Gs + (682 + sloadCost sevm bI (coinsBase + Nat.toB256 1) + 2) →
      d.gasLeft = g + 46 + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) d.memory rliPushSite) →
      M' = (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).write 0x900 (Bytes.toB256 [1] + Nat.toB256 1).toBytes →
      rliAmt sevm 1 ≠ 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c48 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c48 Q := by
  exact rx_rli_pushG (by decide) hfork hdepth hL hR hW hsz hc hpush hW'c hskip hG hGb hroom kS kT
    (rli_backS rli_prog_48 (by decide)) (rli_backS rli_prog_48 (by decide))

/-- Transfer iteration 2 at `t_3769_c1045`, forward, exact (core of `rx_rli_push2a`). -/
theorem rx_rli_push2aE {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hc : WordAt img 0x900 (Nat.toB256 2))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) ≠ 0 → MutCallOkAtE sevm W W' (σ.get (coinsBase + Nat.toB256 2))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 E)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → R ≤ g → g ≤ G →
      G = g + 114 → b' = b → M' = M.write 0x900 (Bytes.toB256 [1] + Nat.toB256 2).toBytes →
      rliAmt sevm 2 = 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) rliEnd Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → R ≤ g → g ≤ G →
      ∀ (bI : Devm) (Gs : Nat) (d : Devm), Devm.EqModGas bI (rliPushId2 sevm b S M 2) →
      E (afterSload sevm bI (coinsBase + Nat.toB256 2)) ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) (rliPushMemC sevm M 2) Gs d →
      G = Gs + (732 + sloadCost sevm bI (coinsBase + Nat.toB256 2) + 2) →
      d.gasLeft = g + 46 + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) d.memory rliPushSite) →
      M' = (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).write 0x900 (Bytes.toB256 [1] + Nat.toB256 2).toBytes →
      rliAmt sevm 2 ≠ 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) rliEnd Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c1045 Q := by
  have hk : (Nat.toB256 2).toNat < 3 := by decide
  by_cases hz : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) = 0
  · -- `amounts[2] == 0`: skipped
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + 114 := ⟨G - 114, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_calldataload (by hrs) ·)
    xr (rx_xor rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by rw [hz]; decide) ·)
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x920 0x900 32 = 0x920 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_zero' (by decide) ·)
    rw [rli_end_1045]
    exact kS _ M _ _ (hL.mono hW'c (hskip hz)) hR hW hsz (fun o v h ho => by wautoH h) (by wauto) (by omega) (by omega)
      (by omega) rfl hMq1 hz
  · -- the transfer
    obtain ⟨g1, rfl⟩ : ∃ g, G = g + 732 := ⟨G - 732, by omega⟩
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_mul rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_calldataload (by hrs) ·)
    xr (rx_xor rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_zero' (by rw [zero_lit, B256.xor_zero]; unfold B256.eqCheck; rw [if_neg hz]) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x980) (c := 16) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x920 0x980 32 = 0x9a0 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x9a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0x9a0 0x9a0 32 = 0x9c0 by decide] at hsz
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
    refine rxe_identityL (i := 0x9a0) (n := 0x4) (o := 0xa00) (z := 0x4) (ext := 10) (X := 128) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 10 + 64 * idCost 0x4 = 1262 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqA; intro bI1 M hsha hcan1 hMqA hR hW hsz; rw [show memExtsSize 0x9c0 [(0x9a0, 0x4), (0xa00, 0x4)] = 0xa20 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
    rw [rli_push_sel] at hR
    xr (rx_pop ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mload (o := 0x980) hR hsz rfl (by decide) (by hrs) ·); try wsimp
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
    refine rxe_mstoreL (o := 0xa04) (c := 7) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0xa20 0xa04 32 = 0xa40 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
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
    refine rxe_mstoreL (o := 0xa24) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0xa40 0xa24 32 = 0xa60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x9e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0xa60 0x9e0 32 = 0xa60 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_swap1 ·)
    xr (rx_pop ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mload (o := 0x9e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_gas (by hrs) ·)
    refine rxe_identityL (i := 0x9e0) (n := 0x64) (o := 0xa80) (z := 0x64) (ext := 17) (X := 144) hL.id hdepth hR hW hsz (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩ rfl (by have : 100 + 17 + 64 * idCost 0x64 = 1845 := (by decide); omega) (by omega) (by hrs) ?_; clear hR hW hsz; rename' M => MqB; intro bI2 M hsha hcan2 hMqB hR hW hsz; rw [show memExtsSize 0xa60 [(0x9e0, 0x64), (0xa80, 0x64)] = 0xb00 by decide] at hsz; replace hL := hL.sha hsha; clear hsha
    rw [rli_transfer_copy2] at hR
    obtain ⟨img3, hR3, hI⟩ := Mem.Reads.forget hR
    clear hR
    have hR := hR3
    clear hR3
    have hdata : Region img3 0xa80 ((Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] +
        Bytes.toB256 [32]).toBytes ++ (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])).toBytes)) := by
      rw [hI]; exact Region.write_self _ _ _
    have hc3 : WordAt img3 0x900 (Nat.toB256 2) := by rw [hI]; wautoH hc
    have hk3 : ∀ o v, WordAt img o v → 0xe0 ≤ o → o + 32 ≤ 0x900 → WordAt img3 o v :=
      fun o v h h1 h2 => by rw [hI]; wautoH h
    clear hI
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (by xbr) ·)
    xr (rx_dest ·)
    xr (rx_pop ·)
    xr (rx_pop ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mload (o := 0xa80) hR hsz rfl (by decide) (by hrs) ·)
    rw [(Region.word hdata.left).read]
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc3) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_lt rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branch_succ (ex_lt3_ne hk) ·)
    xr (rx_dest ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [show memExtSize 0xb00 0xc0 32 = 0xb00 by decide] at hsz
    xr (rx_push rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hrs) (by decide) ·)
    rw [keccak_zero]
    xr (rx_add (by hrs) ·)
    refine rxe_sloadVX hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22 g2x; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
    obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 2 := ⟨g2 - 2, by omega⟩
    xr (rx_gas (by hrs) ·)
    rw [show Bytes.toB256 [0] + Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] =
        (0x44 : B256) by decide, show Bytes.toB256 [0] = (0 : B256) by decide,
      show Bytes.toB256 [0x0a, 0xa0] = (0xaa0 : B256) by decide,
      show Bytes.toB256 [0x0b, 0x40] = (0xb40 : B256) by decide,
      show Bytes.toB256 [32] = (0x20 : B256) by decide]
    subst hv2
    have hin : (M.read 0xaa0 0x44).1 = transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])).toBytes := by
      rw [hR.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp only [B256.length_toBytes]; omega)]
      exact Region.slice hdata.right (by simp only [List.length_append, B256.length_toBytes]; rfl)
    obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd, hE⟩ :=
      hpush hz b2 ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) M g3 hL.w (by omega) (by omega) hin (by hrs)
    xr (.next hrun ·)
    obtain ⟨hmem, -⟩ := hpost.settled (by decide)
    rw [show (0xaa0 : B256).toNat = 0xaa0 by decide, show (0x44 : B256).toNat = 0x44 by decide,
      show (0xb40 : B256).toNat = 0xb40 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
    have hd : d = St d (1 :: _) d.memory d.gasLeft := St.self hpost.stack rfl
    rw [hd, rli_push_tail_1045]
    have hext : (M.extends [(0xaa0, 0x44), (0xb40, 0x20)]).size = 0xb60 := by
      show memExtsSize M.size _ = _
      rw [hsz]; decide
    have hsz5 : d.memory.size = 0xb60 := by
      rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
    have hR5 : Mem.Reads d.memory (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
        0xb40 (d.returnData.take 0x20)) := by
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
      hdepth (by decide) rli_push_join (by simp only [List.not_mem_nil, not_false_eq_true]) hrdlt hok
      ?_ (by rw [hsz5]) (by rw [hsz5]; decide) (by rw [hsz5]; decide) (by omega) (by omega)
      (by hrs) ?_)
    · rw [show (Bytes.toB256 [rliPushSite.lh, rliPushSite.ll]).toNat + 32 = 0xb40 by decide]
      intro j hj
      exact (rawCall_window hmem rfl j hj).2
    intro b' rd' hsha hcanT
    refine SFunc.runEx_iff_runExCut_nil.mp ?_
    rw [show (Bytes.toB256 [rliPushSite.lh, rliPushSite.ll]).toNat = 0xb20 by decide,
      show (Bytes.toB256 [rliPushSite.bh, rliPushSite.bl]).toNat = 0x920 by decide]
    have hn32 : min d.returnData.length 32 ≤ 32 := by omega
    have hR6 : Mem.Reads (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32))
        (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes)
          0xb40 (d.returnData.take 0x20)) 0xb20
          (Nat.toB256 (min d.returnData.length 32)).toBytes) 0x920 ((Bytes.writeAt (Bytes.writeAt
          (Bytes.writeAt img3 192 (Bytes.toB256 [0]).toBytes) 0xb40 (d.returnData.take 0x20)) 0xb20
          (Nat.toB256 (min d.returnData.length 32)).toBytes).sliceD 0xb20
          (min d.returnData.length 32 + 32) 0)) := by
      unfold vyRawMem
      rw [(hR5.write hW5 _ _).read]
      exact (hR5.write hW5 _ _).write (hW5.write _ _) _ _
    have hW6 : Mem.Wf (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)) := by
      unfold vyRawMem; exact (hW5.write _ _).write _ _
    have hsz6 : (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).size = 0xb60 := by
      unfold vyRawMem
      have h1 : (d.memory.write 0xb20 (Nat.toB256 (min d.returnData.length 32)).toBytes).size =
          0xb60 := by
        rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsz5]; decide), hsz5]
      rw [(hR5.write hW5 _ _).read, Mem.size_write_of_le (by rw [h1, List.length_sliceD]; omega), h1]
    obtain ⟨img6, hR, hI⟩ := Mem.Reads.forget hR6
    have hc6 : WordAt img6 0x900 (Nat.toB256 2) := by
      rw [hI]
      refine WordAt.write_other ?_ (by simp only [List.length_sliceD]; omega)
      wautoH hc3
    have hk6 : ∀ o v, WordAt img o v → 0xe0 ≤ o → o + 32 ≤ 0x900 → WordAt img6 o v := by
      intro o v h h1 h2
      rw [hI]
      refine WordAt.write_other ?_ (by simp only [List.length_sliceD]; omega)
      have := hk3 o v h h1 h2
      wautoH this
    clear hI hR6
    have hW := hW6
    have hsz := hsz6
    replace hL := hLd.sha hsha
    clear hW6 hsz6 hR5 hW5 hmem
    obtain ⟨g8, rfl⟩ : ∃ g, G2 = g + 46 := ⟨G2 - 46, by omega⟩
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dest ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rxm_mloadW (o := 0x900) (v := Nat.toB256 2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hc6) (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_add (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_dup rfl (by hrs) ·)
    refine rxe_mstoreL (o := 0x900) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0xb60 0x900 32 = 0xb60 by decide] at hsz
    xr (rx_dup rfl (by hrs) ·)
    xr (rx_eq rfl (by hrs) ·)
    xr (rx_iszero rfl (by hrs) ·)
    xr (rx_push rfl (by hrs) ·)
    xr (rx_branchTo_zero' (by decide) ·)
    refine kT _ M _ _ hL hR hW hsz (fun o v h ho => by wautoH (hk6 o v h ho.1 ho.2)) (by wauto)
      (by omega) (by omega) bI2 g3 d ?_ ?_ (by omega) (by omega) hcanT hMq7 hz
    · rw [hMq5, hMq4, hMq3, hMqA, hMq2, hMq1] at hcan2
      rw [hMq2, hMq1] at hcan1
      exact hcan2.trans (identityCallNext_congr sevm _ _ _ _ _ _ hcan1)
    · rw [hMq6, hMqB, hMq5, hMq4, hMq3, hMqA, hMq2, hMq1] at hE
      rw [hb2] at hE
      exact hE

/-- Transfer iteration 2 at `t_3769_c48`, forward, exact (core of `rx_rli_push2b`). -/
theorem rx_rli_push2bE {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xb60)
    (hc : WordAt img 0x900 (Nat.toB256 2))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) ≠ 0 → MutCallOkAtE sevm W W' (σ.get (coinsBase + Nat.toB256 2))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])).toBytes) RawCallOk U 0xaa0 0x44 0xb40 E)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → R ≤ g → g ≤ G →
      G = g + 114 → b' = b → M' = M.write 0x900 (Bytes.toB256 [1] + Nat.toB256 2).toBytes →
      rliAmt sevm 2 = 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) rliEnd Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → R ≤ g → g ≤ G →
      ∀ (bI : Devm) (Gs : Nat) (d : Devm), Devm.EqModGas bI (rliPushId2 sevm b S M 2) →
      E (afterSload sevm bI (coinsBase + Nat.toB256 2)) ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) (rliPushMemC sevm M 2) Gs d →
      G = Gs + (682 + sloadCost sevm bI (coinsBase + Nat.toB256 2) + 2) →
      d.gasLeft = g + 46 + rawTailCost (min d.returnData.length 32) →
      Devm.EqModGas b' (rawTailBaseNext sevm d ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [9, 0] :: S) d.memory rliPushSite) →
      M' = (vyRawMem d.memory 0xb20 0x920 (min d.returnData.length 32)).write 0x900 (Bytes.toB256 [1] + Nat.toB256 2).toBytes →
      rliAmt sevm 2 ≠ 0 →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) rliEnd Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c48 Q := by
  exact rx_rli_pushG (by decide) hfork hdepth hL hR hW hsz hc hpush hW'c hskip hG hGb hroom kS kT
    (rli_backX (by decide)) (rli_backX (by decide))

/-- Transfer iteration 0 at `t_3769_c1368`, forward. -/
theorem rx_rli_push0 {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hc : WordAt img 0x900 (Nat.toB256 0))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])) ≠ 0 → CoinPushOkAt sevm W W' (σ.get (coinsBase + Nat.toB256 0))
      (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])) U 0xaa0 0xb40)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 1) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c1037 Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 1) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c48 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c1368 Q :=
  rx_rli_push0E hfork hdepth hL hR hW hsz hc (fun h => (hpush h).withE) hW'c hskip hG hGb hroom
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ => kS b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ _ _ _ _ => kT b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)

/-- Transfer iteration 1 at `t_3769_c1037`, forward. -/
theorem rx_rli_push1a {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hc : WordAt img 0x900 (Nat.toB256 1))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) ≠ 0 → CoinPushOkAt sevm W W' (σ.get (coinsBase + Nat.toB256 1))
      (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) U 0xaa0 0xb40)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c1045 Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c48 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c1037 Q :=
  rx_rli_push1aE hfork hdepth hL hR hW hsz hc (fun h => (hpush h).withE) hW'c hskip hG hGb hroom
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ => kS b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ _ _ _ _ => kT b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)

/-- Transfer iteration 1 at `t_3769_c48`, forward. -/
theorem rx_rli_push1b {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xb60)
    (hc : WordAt img 0x900 (Nat.toB256 1))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) ≠ 0 → CoinPushOkAt sevm W W' (σ.get (coinsBase + Nat.toB256 1))
      (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) U 0xaa0 0xb40)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c48 Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) t_3769_c48 Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c48 Q :=
  rx_rli_push1bE hfork hdepth hL hR hW hsz hc (fun h => (hpush h).withE) hW'c hskip hG hGb hroom
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ => kS b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ _ _ _ _ => kT b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)

/-- Transfer iteration 2 at `t_3769_c1045`, forward. -/
theorem rx_rli_push2a {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hc : WordAt img 0x900 (Nat.toB256 2))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) ≠ 0 → CoinPushOkAt sevm W W' (σ.get (coinsBase + Nat.toB256 2))
      (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) U 0xaa0 0xb40)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) rliEnd Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) rliEnd Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c1045 Q :=
  rx_rli_push2aE hfork hdepth hL hR hW hsz hc (fun h => (hpush h).withE) hW'c hskip hG hGb hroom
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ => kS b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ _ _ _ _ => kT b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)

/-- Transfer iteration 2 at `t_3769_c48`, forward. -/
theorem rx_rli_push2b {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R U : Nat} {Q : Outcome → Prop}
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xb60)
    (hc : WordAt img 0x900 (Nat.toB256 2))
    (hpush : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) ≠ 0 → CoinPushOkAt sevm W W' (σ.get (coinsBase + Nat.toB256 2))
      (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) U 0xaa0 0xb40)
    (hW'c : WClosed sevm W') (hskip : (Sevm.dataWord sevm (Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [4])) = 0 → ∀ b, W b → W' b)
    (hG : 12000 + U + R ≤ G) (hGb : G + 3000 < 2 ^ 256) (hroom : S.length + 40 < 1024)
    (kS : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (o + 32 ≤ 0x900 ∨ 0x920 ≤ o) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) rliEnd Q)
    (kT : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W' b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0xb60 →
      (∀ o v, WordAt img o v → (0xe0 ≤ o ∧ o + 32 ≤ 0x900) → WordAt img' o v) →
      WordAt img' 0x900 (Nat.toB256 3) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [9, 0] :: S) M' g) rliEnd Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) t_3769_c48 Q :=
  rx_rli_push2bE hfork hdepth hL hR hW hsz hc (fun h => (hpush h).withE) hW'c hskip hG hGb hroom
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ => kS b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)
    (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ _ _ _ _ => kT b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8)

end Blanc.Lift.Curve3Pool
