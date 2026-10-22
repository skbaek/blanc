import Blanc.Lift.Curve3Pool.Walk.RliLivePush

/-!
# `remove_liquidity_imbalance`, forward: the event and `STOP`

`rx_rli_end920`, `rx_rli_endB60` (the transfer loop's exit `rliEnd` → `STOP`, over the memory
the loop left: `0x920` with no transfer, `0xb60` after one): `RemoveLiquidityImbalance(provider,
token_amounts, fees, invariant, token_supply - token_amount)` (checked) and the lock cleared. The
event's data words 3–7 (`fees`, `D1`, the new supply) are returned.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The event and `STOP`, forward, exact** (core of `rx_rli_end920`; memory `0x920`). -/
theorem rx_rli_end920E {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat} {Q : Outcome → Prop} {T D1 f0 f1 f2 Bw : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw) (hG : 30000 ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ D : Devm, ExLive sevm W D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧ Bytes.toB256 (data.sliceD 0xc0 32 0) = D1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - Bw) →
      G = D.gasLeft + (3432 + sstoreCost sevm b (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) rliEnd Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 3432 := ⟨G - 3432, by omega⟩
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xb80) (c := 69) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x920 0xb80 32 = 0xba0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xba0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xba0 0xba0 32 = 0xbc0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xbc0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xbc0 0xbc0 32 = 0xbe0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x5a0) (v := f0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hf0) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xbe0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xbe0 0xbe0 32 = 0xc00 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x5c0) (v := f1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hf1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc00) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc00 0xc00 32 = 0xc20 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x5e0) (v := f2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hf2) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc20) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc20 0xc20 32 = 0xc40 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x480) (v := D1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc40) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc40 0xc40 32 = 0xc60 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x140) (v := T) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hT) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x780) (v := Bw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hBw) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hTX) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc60) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc60 0xc60 32 = 0xc80 by decide] at hsz
  xr (rx_caller (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_log2 (c := 3173) hstatic (by rw [St.extCost_eq hsz]; decide) rfl (read_covered_len hsz (by decide) (by decide)) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sstoreVX hfork hstatic (by omega) ?_; intro g2 b2 hb2 hg21 hg22 g2x
  have hL2 := (hL.addLogE _).sstoreE hb2
  refine ⟨_, .last rfl, k _ (hL2.st _ _ _) ⟨_, _, _, by rw [hb2]; exact (afterSstore_logs _ _ _ _).trans rfl, ?_, ?_, ?_, ?_, ?_⟩
    (by show _ = g2 + _; rw [g2x, sstoreCost_addLog]; omega)⟩
  all_goals rw [hR.read, Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by decide)]
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0x60 = 0xbe0 by decide]
    exact (show WordAt _ 0xbe0 f0 by wauto).read
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0x80 = 0xc00 by decide]
    exact (show WordAt _ 0xc00 f1 by wauto).read
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0xa0 = 0xc20 by decide]
    exact (show WordAt _ 0xc20 f2 by wauto).read
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0xc0 = 0xc40 by decide]
    exact (show WordAt _ 0xc40 D1 by wauto).read
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0xe0 = 0xc60 by decide]
    exact (show WordAt _ 0xc60 (T - Bw) by wauto).read

/-- **The event and `STOP`, forward, exact** (core of `rx_rli_endB60`; memory `0xb60`). -/
theorem rx_rli_endB60E {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat} {Q : Outcome → Prop} {T D1 f0 f1 f2 Bw : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xb60)
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw) (hG : 30000 ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ D : Devm, ExLive sevm W D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧ Bytes.toB256 (data.sliceD 0xc0 32 0) = D1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - Bw) →
      G = D.gasLeft + (3372 + sstoreCost sevm b (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) rliEnd Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 3372 := ⟨G - 3372, by omega⟩
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xb80) (c := 9) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xb60 0xb80 32 = 0xba0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xba0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xba0 0xba0 32 = 0xbc0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xbc0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xbc0 0xbc0 32 = 0xbe0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x5a0) (v := f0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hf0) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xbe0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xbe0 0xbe0 32 = 0xc00 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x5c0) (v := f1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hf1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc00) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc00 0xc00 32 = 0xc20 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x5e0) (v := f2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hf2) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc20) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc20 0xc20 32 = 0xc40 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x480) (v := D1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc40) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc40 0xc40 32 = 0xc60 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x140) (v := T) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hT) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x780) (v := Bw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hBw) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hTX) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc60) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc60 0xc60 32 = 0xc80 by decide] at hsz
  xr (rx_caller (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_log2 (c := 3173) hstatic (by rw [St.extCost_eq hsz]; decide) rfl (read_covered_len hsz (by decide) (by decide)) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sstoreVX hfork hstatic (by omega) ?_; intro g2 b2 hb2 hg21 hg22 g2x
  have hL2 := (hL.addLogE _).sstoreE hb2
  refine ⟨_, .last rfl, k _ (hL2.st _ _ _) ⟨_, _, _, by rw [hb2]; exact (afterSstore_logs _ _ _ _).trans rfl, ?_, ?_, ?_, ?_, ?_⟩
    (by show _ = g2 + _; rw [g2x, sstoreCost_addLog]; omega)⟩
  all_goals rw [hR.read, Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by decide)]
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0x60 = 0xbe0 by decide]
    exact (show WordAt _ 0xbe0 f0 by wauto).read
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0x80 = 0xc00 by decide]
    exact (show WordAt _ 0xc00 f1 by wauto).read
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0xa0 = 0xc20 by decide]
    exact (show WordAt _ 0xc20 f2 by wauto).read
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0xc0 = 0xc40 by decide]
    exact (show WordAt _ 0xc40 D1 by wauto).read
  · rw [show (Bytes.toB256 [0x0b, 0x80]).toNat + 0xe0 = 0xc60 by decide]
    exact (show WordAt _ 0xc60 (T - Bw) by wauto).read

/-- **The event and `STOP`, forward** (memory `0x920`). -/
theorem rx_rli_end920 {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat} {Q : Outcome → Prop} {T D1 f0 f1 f2 Bw : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x920)
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw) (hG : 30000 ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ D : Devm, ExLive sevm W D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧ Bytes.toB256 (data.sliceD 0xc0 32 0) = D1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - Bw) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) rliEnd Q :=
  rx_rli_end920E hfork hstatic hL hR hW hsz hT hD1 hf0 hf1 hf2 hBw hTX hG hroom
    fun D h1 h2 _ => k D h1 h2

/-- **The event and `STOP`, forward** (memory `0xb60`). -/
theorem rx_rli_endB60 {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G : Nat} {Q : Outcome → Prop} {T D1 f0 f1 f2 Bw : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xb60)
    (hT : WordAt img 0x140 T) (hD1 : WordAt img 0x480 D1) (hf0 : WordAt img 0x5a0 f0)
    (hf1 : WordAt img 0x5c0 f1) (hf2 : WordAt img 0x5e0 f2) (hBw : WordAt img 0x780 Bw)
    (hTX : ¬ T < Bw) (hG : 30000 ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ D : Devm, ExLive sevm W D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧ Bytes.toB256 (data.sliceD 0xc0 32 0) = D1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - Bw) → Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [9, 0] :: S) M G) rliEnd Q :=
  rx_rli_endB60E hfork hstatic hL hR hW hsz hT hD1 hf0 hf1 hf2 hBw hTX hG hroom
    fun D h1 h2 _ => k D h1 h2

end Blanc.Lift.Curve3Pool
