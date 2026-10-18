import Blanc.Lift.Curve3Crv.Exec
import Blanc.StorageAccessGas

/-!
# 3Crv: the body costs as bounds (goal amendment §13)

The liveness form `BodyLive` (`Spec.lean`) states a body's exact cost behind an existential, so
nothing public bounds it uniformly over worlds.  A caller that must budget the call for every world
it admits (the pool's 3Crv call premises, `Curve3Pool/LivePremises.lean`) needs the bound.  This
file exposes the cost each existing walk already chooses, as a bound, for the three bodies the pool
calls; no existing statement changes.

* `BodyLiveLe sevm b f r U`: `BodyLive` with the cost at most `U` (`BodyLiveLe.live` forgets it);
* `live_totalSupply_le`: `totalSupply()`, `34 + sloadCost ≤ 34 + 2100`;
* `live_mint_le`, `live_burnFrom_le`: `2119` (`2107`) gas of fixed charges, three `SLOAD`s and two
  `SSTORE`s, each at most a cold access (`sloadCost_le`) or a cold fresh set (`sstoreCost_le`);
* `c3crv_exec_le`: the dispatcher's `dispatchGas k` on top, as a real execution of the deployed
  runtime.  Unlike `c3crv_exec` it asks no `isStatic = false`: the bound is the body's, and a
  `totalSupply()` body runs in a static frame.

The `mint` and `burnFrom` walks are the ones of `live_mint` and `live_burnFrom`
(`LiveBodies.lean`), read with their cost bounded.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

/-- **`BodyLive` with its cost bounded by `U`.** -/
def BodyLiveLe (sevm : Sevm) (b : Devm) (f : SFunc) (r : Raw) (U : Nat) : Prop :=
  ∃ c ≤ U, ∀ G, gCallStipend < G → ∃ post,
    SFunc.RunExact prog sevm (entrySt sevm b (G + c)) f (.halted post) ∧ post.gasLeft = G ∧
      Lands sevm b post r

/-- A bounded body is live. -/
theorem BodyLiveLe.live {sevm : Sevm} {b : Devm} {f : SFunc} {r : Raw} {U : Nat}
    (h : BodyLiveLe sevm b f r U) : BodyLive sevm b f r := by
  obtain ⟨c, -, hc⟩ := h
  exact ⟨c, hc⟩

section

variable {sevm : Sevm} {b : Devm}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

/-- `totalSupply()` costs at most `34 + 2100`: 34 gas and the `SLOAD` of slot 5. -/
theorem live_totalSupply_le (hfork : CoveredFork sevm.benvStat.fork) {r : Raw}
    (hr : rawTotalSupply sevm stor₀ = some r) :
    BodyLiveLe sevm b t_0240_c0 r (34 + 2100) := by
  unfold rawTotalSupply at hr
  split_ifs at hr with hv
  cases hr
  have hcost := Blanc.sloadCost_le sevm b vySupplySlot
  have hcs : gasColdSload = 2100 := rfl
  refine ⟨34 + sloadCost sevm b vySupplySlot, by omega, fun G _ => ?_⟩
  have hsz := vyMem_empty_size (Sevm.dataWord sevm 0)
  obtain ⟨post, hrun, hg, hl⟩ := word_tail (b := b) hfork (vyMem_wf Mem.wf_empty _)
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (by rw [hsz]; omega) (by rw [hsz]) vySupplySlot G
  refine ⟨post, ?_, hg, hl⟩
  unfold entrySt t_0240_c0
  rw [show G + (34 + sloadCost sevm b vySupplySlot) =
    G + 3 + 3 + 3 + 3 + sloadCost sevm b vySupplySlot + 3 + 1 + 10 + 3 + 3 + 2 by omega]
  refine rx_callvalue (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  rw [hv]
  refine rx_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte])
    (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_024a_c0
  refine rx_dest ?_
  refine rx_push (w := vySupplySlot) rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  exact hrun

-- SEGMENT: liveMintBurnLe (the walks of `live_mint` and `live_burnFrom`, cost bounded)
private theorem live_mint_le_mem (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawMint sevm stor₀ = some r)
    (M0 : Mem) (hM : M0.size = 192) (hwf0 : Mem.Wf M0)
    (hM0eq : M0 = vyMem Mem.empty (Sevm.dataWord sevm 0)) :
    BodyLiveLe sevm b t_056e_c0 r (2119 + 3 * 2100 + 2 * 22100) := by
  unfold rawMint at hr
  dsimp only at hr
  split_ifs at hr with hg
  obtain ⟨hv, hd, hmin, hnz, hsup, hbal⟩ := hg
  cases hr
  have h3 : Bytes.toB256 [0x03] = 3 := by decide
  have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
  set d := Sevm.argWord sevm 0
  set v := Sevm.argWord sevm 1
  set s2 := mapSlot 3 d
  set b1 := afterSload sevm b vyMinterSlot
  set sup := b1.getStorVal sevm.currentTarget vySupplySlot
  have hsup' : sup = (stor₀).get vySupplySlot := getStorVal_afterSload
  set b2 := afterSstore sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup + v)
  set y := b2.getStorVal sevm.currentTarget s2
  have hy : y = (((stor₀).set vySupplySlot ((stor₀).get vySupplySlot + v)).get s2) := by
    show b2.getStorVal _ _ = _
    rw [getStorVal_afterStore, afterSload_getStor, hsup']
  set M1 := (M0.write 224 d.toBytes).write 192 (3 : B256).toBytes
  have hM1 : M1.size = 256 := by simp only [M1, Mem.size_write_word_at, hM]; decide
  have hwf1 : Mem.Wf M1 := ((hwf0.write _ _).write _ _)
  set M3 := M1.write 320 v.toBytes
  have hM3 : M3.size = 352 := by simp only [M3, Mem.size_write_word_at, hM1]; decide
  have hcost0 := sstoreCost_le sevm (afterSload sevm b2 s2) s2 (y + v)
  have hcost1 := Blanc.sloadCost_le sevm b2 s2
  have hcost2 := sstoreCost_le sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup + v)
  have hcost3 := Blanc.sloadCost_le sevm b1 vySupplySlot
  have hcost4 := Blanc.sloadCost_le sevm b vyMinterSlot
  have hcs : gasColdSload = 2100 := rfl
  have hss : gasStorageSet = 20000 := rfl
  refine ⟨3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19, by omega, fun G hG => ?_⟩
  have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
  have hwf3 : Mem.Wf M3 := hwf1.write _ _
  set b4 := (afterSstore sevm (afterSload sevm b2 s2) s2 (y + v)).addLog
    ⟨sevm.currentTarget, [transferTopic, 0, d], v.toBytes⟩
  set M5 := M3.write 0 (1 : B256).toBytes
  refine ⟨((St b4 [] M5 G).memRead 0 32).2.withOutput (1 : B256).toBytes, ?_, rfl, ?_⟩
  · unfold entrySt
    rw [show G + (3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19) = G + 3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x05) (l := 0x78) (fail := t_0574_c0) hv (by simp only [List.length_nil,
      zero_add, Nat.reduceLT]) ?_
    rw [← hM0eq]
    refine rx_vyAddrArg (p := 0x04) (h := 0x05) (l := 0x89) (fail := t_0585_c0)
      (by rw [hM0eq]; exact vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega)
      (by rw [hd0]; exact hd) (by simp only [List.length_nil, zero_add, Nat.reduceLT]) ?_
    refine rx_push (w := vyMinterSlot) rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_sload_sel hfork (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_caller (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_eq (v := 1) ?_ (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    · have : b.getStorVal sevm.currentTarget vyMinterSlot = sevm.caller.toB256 := hmin
      simp only [B256.eqCheck, this, ↓reduceIte]
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    refine rx_push (w := 0) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add,
      Nat.one_lt_ofNat]) ?_
    rw [hd0]
    refine rx_xor (v := d) (B256.xor_zero d) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_branch_succ hnz (rx_dest ?_)
    refine rx_push (w := vySupplySlot) rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_vyAddStore (p := 0x24) (h := 0x05) (l := 0xbd) (fail := t_05b9_c0) hfork hstatic
      (by rw [hv1, getStorVal_afterSload]; exact hsup) (by omega) (by simp only [List.length_nil,
        zero_add, Nat.reduceLT]) ?_
    rw [hv1]
    refine rx_push (w := 3) h3 (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add,
      Nat.one_lt_ofNat]) ?_
    rw [hd0]
    refine rx_vySlot (c1 := 9) hM (by omega) (by decide) (by decide) (by simp only [List.length_nil,
      zero_add, Nat.reduceLT]) ?_
    refine rx_vyAddStore (p := 0x24) (h := 0x05) (l := 0xeb) (fail := t_05e7_c0) hfork hstatic
      (by rw [hv1]; show y.toNat + v.toNat < 2 ^ 256; rw [hy]; exact hbal) (by omega) (by simp only [List.length_nil,
        zero_add, Nat.reduceLT]) ?_
    rw [hv1]
    refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_calldataload (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    rw [hv1]
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_mstore (c := 12) ?_ (M' := M3) (by rw [h320]) ?_
    · rw [h320, St.extCost_eq hM1]; decide
    refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_calldataload (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    rw [hd0]
    refine rx_push (w := 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
      Nat.one_lt_ofNat]) ?_
    refine rx_push (w := transferTopic) (by decide) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLT]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLT]) ?_
    refine rx_log3 (c := 1756) (data := v.toBytes) hstatic ?_ ?_ ?_ ?_
    · rw [h320, h32, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3])]; decide
    · rw [h320, h32]; exact Mem.read_write_word_of_wf hwf1 320 v
    · rw [h320, h32]; exact read_covered hM3 (by decide) (by decide)
    refine rx_push (w := 1) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_mstore (c := 3) ?_ (M' := M5) (by rw [h0]) ?_
    · rw [h0, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3]; omega)]; rfl
    refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_return ?_ ?_
    · have hM5 : M5.size = 352 := by simp only [M5, Mem.size_write_word_at, hM3]; decide
      rw [h0, h32, St, Devm.extCost_zero_of_le (by rw [hM5]) (by rw [hM5]; omega)]
    · rw [h0, h32]; exact Mem.read_write_word_of_wf hwf3 0 1
  · refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore, getStor_afterStore,
        afterSload_getStor, hy, hsup']
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha,
        afterSload_getStor]
    · rw [logs_St_return, logs_addLog, logs_afterStore, logs_afterStore, afterSload_logs]
    · cases ho
      exact output_St_return _ _ _ _ _ _ _


private theorem live_burnFrom_le_mem (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawBurnFrom sevm stor₀ = some r)
    (M0 : Mem) (hM : M0.size = 192) (hwf0 : Mem.Wf M0)
    (hM0eq : M0 = vyMem Mem.empty (Sevm.dataWord sevm 0)) :
    BodyLiveLe sevm b t_0644_c0 r (2107 + 3 * 2100 + 2 * 22100) := by
  simp only [rawBurnFrom] at hr
  split_ifs at hr with hg
  obtain ⟨hv, hd, hmin, hnz, hsup, hbal⟩ := hg
  have hr' := (Option.some.inj hr).symm
  subst hr'
  have h3 : Bytes.toB256 [0x03] = 3 := by decide
  have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
  set d := Sevm.argWord sevm 0
  set v := Sevm.argWord sevm 1
  set s2 := mapSlot 3 d
  set b1 := afterSload sevm b vyMinterSlot
  set sup := b1.getStorVal sevm.currentTarget vySupplySlot
  have hsup' : sup = (stor₀).get vySupplySlot := getStorVal_afterSload
  set b2 := afterSstore sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup - v)
  set y := b2.getStorVal sevm.currentTarget s2
  have hy : y = (((stor₀).set vySupplySlot ((stor₀).get vySupplySlot - v)).get s2) := by
    show b2.getStorVal _ _ = _
    rw [getStorVal_afterStore, afterSload_getStor, hsup']
  set M1 := (M0.write 224 d.toBytes).write 192 (3 : B256).toBytes
  have hM1 : M1.size = 256 := by simp only [M1, Mem.size_write_word_at, hM]; decide
  have hwf1 : Mem.Wf M1 := ((hwf0.write _ _).write _ _)
  set M3 := M1.write 320 v.toBytes
  have hM3 : M3.size = 352 := by simp only [M3, Mem.size_write_word_at, hM1]; decide
  have hcost0 := sstoreCost_le sevm (afterSload sevm b2 s2) s2 (y - v)
  have hcost1 := Blanc.sloadCost_le sevm b2 s2
  have hcost2 := sstoreCost_le sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup - v)
  have hcost3 := Blanc.sloadCost_le sevm b1 vySupplySlot
  have hcost4 := Blanc.sloadCost_le sevm b vyMinterSlot
  have hcs : gasColdSload = 2100 := rfl
  have hss : gasStorageSet = 20000 := rfl
  refine ⟨3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19, by omega, fun G hG => ?_⟩
  have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
  have hwf3 : Mem.Wf M3 := hwf1.write _ _
  set b4 := (afterSstore sevm (afterSload sevm b2 s2) s2 (y - v)).addLog
    ⟨sevm.currentTarget, [transferTopic, d, 0], v.toBytes⟩
  set M5 := M3.write 0 (1 : B256).toBytes
  refine ⟨((St b4 [] M5 G).memRead 0 32).2.withOutput (1 : B256).toBytes, ?_, rfl, ?_⟩
  · unfold entrySt
    rw [show G + (3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19) = G + 3 + 3 + 3 + 3 + 3 + 1756 + 3 + 3 + 3 + 3 + 3 + 3 + 12 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b2 s2) s2 (y - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b2 s2 + 3 + 42 + 3 + 3 + 3 + 3 + 9 + 3 + 3 + 3 + 3 + 2 + sstoreCost sevm (afterSload sevm b1 vySupplySlot) vySupplySlot (sup - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b1 vySupplySlot + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 2 + sloadCost sevm b vyMinterSlot + 3 + 34 + 19 by omega]
    refine rx_vyNonpayable (h := 0x06) (l := 0x4e) (fail := t_064a_c0) hv (by simp only [List.length_nil,
      zero_add, Nat.reduceLT]) ?_
    rw [← hM0eq]
    refine rx_vyAddrArg (p := 0x04) (h := 0x06) (l := 0x5f) (fail := t_065b_c0)
      (by rw [hM0eq]; exact vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM]) (by rw [hM]; omega)
      (by rw [hd0]; exact hd) (by simp only [List.length_nil, zero_add, Nat.reduceLT]) ?_
    refine rx_push (w := vyMinterSlot) rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_sload_sel hfork (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_caller (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_eq (v := 1) ?_ (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    · have : b.getStorVal sevm.currentTarget vyMinterSlot = sevm.caller.toB256 := hmin
      simp only [B256.eqCheck, this, ↓reduceIte]
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_branch_succ (by decide) (rx_dest ?_)
    refine rx_push (w := 0) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add,
      Nat.one_lt_ofNat]) ?_
    rw [hd0]
    refine rx_xor (v := d) (B256.xor_zero d) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_branch_succ hnz (rx_dest ?_)
    refine rx_push (w := vySupplySlot) rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_vySubStore (p := 0x24) (h := 0x06) (l := 0x91) (fail := t_068d_c0) hfork hstatic
      (by rw [hv1, getStorVal_afterSload]; exact hsup) (by omega) (by simp only [List.length_nil,
        zero_add, Nat.reduceLT]) ?_
    rw [hv1]
    refine rx_push (w := 3) h3 (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add,
      Nat.one_lt_ofNat]) ?_
    rw [hd0]
    refine rx_vySlot (c1 := 9) hM (by omega) (by decide) (by decide) (by simp only [List.length_nil,
      zero_add, Nat.reduceLT]) ?_
    refine rx_vySubStore (p := 0x24) (h := 0x06) (l := 0xbd) (fail := t_06b9_c0) hfork hstatic
      (by rw [hv1]; show v ≤ y; rw [hy]; exact hbal) (by omega) (by simp only [List.length_nil,
        zero_add, Nat.reduceLT]) ?_
    rw [hv1]
    refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_calldataload (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    rw [hv1]
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_mstore (c := 12) ?_ (M' := M3) (by rw [h320]) ?_
    · rw [h320, St.extCost_eq hM1]; decide
    refine rx_push (w := 0) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_calldataload (by simp only [List.length_cons, List.length_nil, zero_add,
      Nat.one_lt_ofNat]) ?_
    rw [hd0]
    refine rx_push (w := transferTopic) (by decide) (by simp only [List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLT]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLT]) ?_
    refine rx_log3 (c := 1756) (data := v.toBytes) hstatic ?_ ?_ ?_ ?_
    · rw [h320, h32, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3])]; decide
    · rw [h320, h32]; exact Mem.read_write_word_of_wf hwf1 320 v
    · rw [h320, h32]; exact read_covered hM3 (by decide) (by decide)
    refine rx_push (w := 1) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_mstore (c := 3) ?_ (M' := M5) (by rw [h0]) ?_
    · rw [h0, St, Devm.extCost_zero_of_le (by rw [hM3]) (by rw [hM3]; omega)]; rfl
    refine rx_push rfl (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
    refine rx_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
    refine rx_return ?_ ?_
    · have hM5 : M5.size = 352 := by simp only [M5, Mem.size_write_word_at, hM3]; decide
      rw [h0, h32, St, Devm.extCost_zero_of_le (by rw [hM5]) (by rw [hM5]; omega)]
    · rw [h0, h32]; exact Mem.read_write_word_of_wf hwf3 0 1
  · refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore, getStor_afterStore,
        afterSload_getStor, hy, hsup']
    · rw [getStor_St_return, getStor_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha,
        afterSload_getStor]
    · rw [logs_St_return, logs_addLog, logs_afterStore, logs_afterStore, afterSload_logs]
    · cases ho
      exact output_St_return _ _ _ _ _ _ _


/-- `mint` costs at most `2119 + 3 * 2100 + 2 * 22100`. -/
theorem live_mint_le (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    {r : Raw} (hr : rawMint sevm stor₀ = some r) :
    BodyLiveLe sevm b t_056e_c0 r (2119 + 3 * 2100 + 2 * 22100) :=
  live_mint_le_mem hfork hstatic hr _ (vyMem_empty_size _) (vyMem_wf Mem.wf_empty _) rfl

/-- `burnFrom` costs at most `2107 + 3 * 2100 + 2 * 22100`. -/
theorem live_burnFrom_le (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) {r : Raw} (hr : rawBurnFrom sevm stor₀ = some r) :
    BodyLiveLe sevm b t_0644_c0 r (2107 + 3 * 2100 + 2 * 22100) :=
  live_burnFrom_le_mem hfork hstatic hr _ (vyMem_empty_size _) (vyMem_wf Mem.wf_empty _) rfl

end

/-- **A bounded body is a real execution of the deployed runtime within its bound plus the
dispatcher's** (`c3crv_exec` with the cost bounded; no `isStatic` premise). -/
theorem c3crv_exec_le {sevm : Sevm} {pre : Devm} {k : Nat} {f : SFunc} {r : Raw} {U : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hf : bodies[k]? = some f) (hk : sels[k]? = some (Sevm.selector sevm))
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hb : BodyLiveLe sevm pre f r U) :
    ∃ c ≤ U + dispatchGas k, ∀ G, gCallStipend < G → ∃ post,
      Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + c)) (.ok post)) ∧ post.gasLeft = G ∧
        Lands sevm pre post r := by
  obtain ⟨c, hcU, hc⟩ := hb
  refine ⟨c + dispatchGas k, by omega, fun G hG => ?_⟩
  obtain ⟨post, hrun, hg, hl⟩ := hc G hG
  have hd := live_dispatch hf hk rfl hlen hcd hrun
  rw [← Nat.add_assoc]
  exact ⟨post, exec_of_runExact hcode hfork ⟨_, rfl, hd⟩, hg, hl⟩

end Blanc.Lift.Curve3Crv
