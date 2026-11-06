import Blanc.Lift.Curve3Pool.Creation.Deploy
import Blanc.Lift.CreateSettlementMeta
import Blanc.Lift.HistCreate

/-!
# The 3pool constructor under Muir Glacier

`Creation/Walk.lean` states the constructor's stores over the modern `SSTORE` successors, so its
second half is `CoveredFork`-only; its first half `segA` touches no storage and is reused as it
stands. This module restates the second half over the actual-rule `afterSstoreH`/`sstoreCostH`
(`Blanc/Lift/HistAccessWalk.lean`), for any frame without state gas.

* `ctorCostH_muir`: in a freshly created account with empty storage the constructor costs exactly
  186,628 gas under Muir Glacier: nine fresh nonzero sets at 20,000, one zero write at 800
  (`admin_fee`), and 5,828 for everything else;
* `ctor_run_muir`: from `G + 186628` gas it halts with `G` left, returning the runtime window,
  leaving `deployedStor` of the block timestamp, the refund counter, log list and deletion set
  as they were;
* `pool_create_muir_meta`: the recorded creation input as a zero-value CREATE message under Muir
  Glacier succeeds, installs the certified runtime and leaves exactly `msg.gas - 4426428` gas: the
  constructor's 186,628 plus the code deposit `200 · 21199 = 4239800`.

The message and its pre-state are explicit premises; transaction validation, sender recovery,
settlement and block inclusion are in `HistoricalTx*.lean`.
-/

namespace Blanc.Lift.Curve3Pool.Creation

open Jaune Blanc.Lift Blanc.Lift.Curve3Pool

local macro "room" : term => `(Nat.le_of_ble_eq_true rfl)

/-- The frame facts the historical walk needs of the creation frame. -/
structure CtorFrameH (sevm : Sevm) : Prop where
  sg : sevm.benvStat.rules.stateGas = none
  static : sevm.isStatic = false

/-! ## The worlds and the cost of the stores -/

def twH1 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm b (coinSlot 0) coin0W
def twH2 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm (twH1 sevm b) (coinSlot 1) coin1W
def twH3 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm (twH2 sevm b) (coinSlot 2) coin2W
def twH4 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm (twH3 sevm b) initialASlot ampW
def twH5 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm (twH4 sevm b) futureASlot ampW
def twH6 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm (twH5 sevm b) feeSlot feeW
def twH7 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm (twH6 sevm b) adminFeeSlot adminFeeW
def twH8 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm (twH7 sevm b) ownerSlot ownerW
def twH9 (sevm : Sevm) (b : Devm) : Devm :=
  afterSstoreH sevm (twH8 sevm b) killDeadlineSlot (sevm.benvStat.time + 0x4f1a00)
def twH10 (sevm : Sevm) (b : Devm) : Devm := afterSstoreH sevm (twH9 sevm b) tokenSlot tokenW

/-- The stores' and the tail's exact cost from the world `b`. -/
def tailCostH (sevm : Sevm) (b : Devm) : Nat :=
  4821 + sstoreCostH sevm (twH9 sevm b) tokenSlot tokenW + 9 +
    sstoreCostH sevm (twH8 sevm b) killDeadlineSlot (sevm.benvStat.time + 0x4f1a00) + 59 +
    sstoreCostH sevm (twH7 sevm b) ownerSlot ownerW + 9 +
    sstoreCostH sevm (twH6 sevm b) adminFeeSlot adminFeeW + 9 +
    sstoreCostH sevm (twH5 sevm b) feeSlot feeW + 9 +
    sstoreCostH sevm (twH4 sevm b) futureASlot ampW + 9 +
    sstoreCostH sevm (twH3 sevm b) initialASlot ampW + 13 +
    sstoreCostH sevm (twH2 sevm b) (coinSlot 2) coin2W + 21 +
    sstoreCostH sevm (twH1 sevm b) (coinSlot 1) coin1W + 21 +
    sstoreCostH sevm b (coinSlot 0) coin0W + 68

/-- The constructor's exact cost from the world `b`. -/
def ctorCostH (sevm : Sevm) (b : Devm) : Nat := tailCostH sevm b + 780

/-! ## The second half of the walk -/

/-- `segB` over the actual-rule stores. -/
theorem segBH {sevm : Sevm} (fr : CtorFrameH sevm) (hcode : sevm.code = code)
    (ht : sevm.benvStat.time.toNat + killDeadlineDt < 2 ^ 256) {b : Devm} {G : Nat}
    (hG : gCallStipend < G) :
    SFunc.RunExact prog sevm (St b [3, 0x240] m13 (G + tailCostH sevm b + 222)) t_013c_c1
      (.halted (returnPost (St (twH10 sevm b) [0, 0x52cf] m17 G) 0 0x52cf [])) := by
  unfold t_013c_c1
  refine loopPass (ci := 1) (off := 0x20) (addr := 0x180) (v := coin1W) (cn := 2) (e := 0)
    (z := 1) (M' := m14) m13_size rfl (by rw [Mem.Reads.read m13_reads]; decide +kernel) (by decide)
    (by decide) (by decide) (by decide) (by rw [Mem.Reads.read m13_reads]; decide +kernel) rfl
    (by decide +kernel) (by decide) (by decide) (by decide) ?_
  refine rx_push rfl room ?_
  refine rx_branchTo_succ (by decide) rfl ?_
  unfold t_013c_c1
  refine loopPass (ci := 2) (off := 0x40) (addr := 0x1a0) (v := coin2W) (cn := 3) (e := 1)
    (z := 0) (M' := m15) m14_size rfl (by rw [Mem.Reads.read m14_reads]; decide +kernel) (by decide)
    (by decide) (by decide) (by decide) (by rw [Mem.Reads.read m14_reads]; decide +kernel) rfl
    (by decide +kernel) (by decide) (by decide) (by decide) ?_
  refine rx_push rfl room ?_
  refine rx_branchTo_zero ?_
  rw [show G + tailCostH sevm b = G + 4821 + sstoreCostH sevm (twH9 sevm b) tokenSlot tokenW + 9 +
    sstoreCostH sevm (twH8 sevm b) killDeadlineSlot (sevm.benvStat.time + 0x4f1a00) + 59 +
    sstoreCostH sevm (twH7 sevm b) ownerSlot ownerW + 9 +
    sstoreCostH sevm (twH6 sevm b) adminFeeSlot adminFeeW + 9 +
    sstoreCostH sevm (twH5 sevm b) feeSlot feeW + 9 +
    sstoreCostH sevm (twH4 sevm b) futureASlot ampW + 9 +
    sstoreCostH sevm (twH3 sevm b) initialASlot ampW + 13 +
    sstoreCostH sevm (twH2 sevm b) (coinSlot 2) coin2W + 21 +
    sstoreCostH sevm (twH1 sevm b) (coinSlot 1) coin1W + 21 +
    sstoreCostH sevm b (coinSlot 0) coin0W + 68 by unfold tailCostH; omega]
  have r16 := m16_wf.2
  unfold t_0172_c1
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 0) (by decide) room ?_
  refine rx_push (w := 0xc0) (by decide) room ?_
  refine rx_mstore (c := 3) (M' := m16) (charge_covered m15_size (by decide) (by decide)) rfl ?_
  refine rx_push (w := 0x20) (by decide) room ?_
  refine rx_push (w := 0xc0) (by decide) room ?_
  refine rx_keccak (c := 36) (v := coinSlot 0) ?_ ?_
    (read_covered_len m16_size (by decide) (by decide)) room ?_
  · rw [St.extCost_eq m16_size]; decide
  · rw [Mem.Reads.read r16, show img16.sliceD (0xc0 : B256).toNat (0x20 : B256).toNat 0 =
      (0 : B256).toBytes by decide +kernel, coinsBase_eq]
    decide +kernel
  refine rx_push (w := 0x160) (by decide) room ?_
  refine rx_dup (n := 0) rfl room ?_
  refine rx_mload (c := 3) (v := coin0W) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_dup (n := 2) rfl room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_dup (n := 0) rfl room ?_
  refine rx_push (w := 0x20) (by decide) room ?_
  refine rx_add' (v := 0x180) (by decide) room ?_
  refine rx_mload (c := 3) (v := coin1W) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := 1) (by decide) room ?_
  refine rx_dup (n := 3) rfl room ?_
  refine rx_add' (v := coinSlot 1) (by decide +kernel) room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_dup (n := 0) rfl room ?_
  refine rx_push (w := 0x40) (by decide) room ?_
  refine rx_add' (v := 0x1a0) (by decide) room ?_
  refine rx_mload (c := 3) (v := coin2W) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := 2) (by decide) room ?_
  refine rx_dup (n := 3) rfl room ?_
  refine rx_add' (v := coinSlot 2) (by decide +kernel) room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 0x1e0) (by decide) room ?_
  refine rx_mload (c := 3) (v := ampW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := initialASlot) (by decide) room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x1e0) (by decide) room ?_
  refine rx_mload (c := 3) (v := ampW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := futureASlot) (by decide) room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x200) (by decide) room ?_
  refine rx_mload (c := 3) (v := feeW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := feeSlot) (by decide) room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x220) (by decide) room ?_
  refine rx_mload (c := 3) (v := adminFeeW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := adminFeeSlot) (by decide) room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x140) (by decide) room ?_
  refine rx_mload (c := 3) (v := ownerW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := ownerSlot) (by decide) room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_timestamp room ?_
  refine rx_push (w := 0x4f1a00) (by decide) room ?_
  refine rx_dup (n := 1) rfl room ?_
  refine rx_dup (n := 1) rfl room ?_
  refine rx_dup (n := 3) rfl room ?_
  refine rx_add' (v := sevm.benvStat.time + 0x4f1a00) rfl room ?_
  refine rx_lt (v := 0) (kill_noWrap ht) room ?_
  refine rx_iszero (v := 1) (by decide) room ?_
  refine rx_push rfl room ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_01d2_c1
  refine rx_dest ?_
  refine rx_dup (n := 0) rfl room ?_
  refine rx_dup (n := 2) rfl room ?_
  refine rx_add' (v := sevm.benvStat.time + 0x4f1a00) rfl room ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_push (w := killDeadlineSlot) (by decide) room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push (w := 0x1c0) (by decide) room ?_
  refine rx_mload (c := 3) (v := tokenW) (charge_covered m16_size (by decide) (by decide))
    (by rw [Mem.Reads.read r16]; decide +kernel) (read_covered m16_size (by decide) (by decide))
    room ?_
  refine rx_push (w := tokenSlot) (by decide) room ?_
  refine rx_sstoreH fr.sg (fun _ => by unfold gCallStipend at hG ⊢; omega) fr.static ?_
  refine rx_push rfl room ?_
  refine rx_jump (j := 2) rfl ?_
  unfold t_54b7_c2
  refine rx_dest ?_
  refine rx_push (w := 0x1e8) (by decide) room ?_
  refine rx_push (w := 0x54b7) (by decide) room ?_
  refine rx_sub' (v := 0x52cf) (by decide) room ?_
  refine rx_push (w := 0x1e8) (by decide) room ?_
  refine rx_push (w := 0) (by decide) room ?_
  refine rx_codecopy (c := 4782) (M' := m17) ?_ ?_ ?_
  · rw [St.extCost_eq m16_size]; decide
  · rw [hcode]
    show m16.write 0 (code.sliceD 0x1e8 0x52cf (Linst.toUInt8 .stop)) = _
    rw [window_eq]; rfl
  refine rx_push (w := 0x1e8) (by decide) room ?_
  refine rx_push (w := 0x54b7) (by decide) room ?_
  refine rx_sub' (v := 0x52cf) (by decide) room ?_
  refine rx_push (w := 0) (by decide) room ?_
  exact rx_return_any (S := []) rfl (by rw [St.extCost_eq m17_size]; decide)

/-! ## The storage through the stores, and what each store finds -/

section
variable {sevm : Sevm} {b : Devm} (hempty : Devm.getStor b sevm.currentTarget = Stor.empty)
include hempty

/-- The storage after the eight stores before the kill deadline. -/
theorem stor_twH8 : Devm.getStor (twH8 sevm b) sevm.currentTarget = coreStor0 := by
  simp only [twH8, twH7, twH6, twH5, twH4, twH3, twH2, twH1, afterSstoreH_getStor_self, hempty,
    coreStor0]

/-- The storage the constructor leaves. -/
theorem stor_twH10 : Devm.getStor (twH10 sevm b) sevm.currentTarget =
    deployedStor sevm.benvStat.time := by
  simp only [twH10, twH9, afterSstoreH_getStor_self, stor_twH8 hempty, deployedStor, killWord]

/-- Every store but `admin_fee`'s finds its slot empty; the two conjuncts that the cost needs. -/
theorem fresh_stores :
    (Devm.getStor b sevm.currentTarget).get (coinSlot 0) = 0 ∧
    (Devm.getStor (twH1 sevm b) sevm.currentTarget).get (coinSlot 1) = 0 ∧
    (Devm.getStor (twH2 sevm b) sevm.currentTarget).get (coinSlot 2) = 0 ∧
    (Devm.getStor (twH3 sevm b) sevm.currentTarget).get initialASlot = 0 ∧
    (Devm.getStor (twH4 sevm b) sevm.currentTarget).get futureASlot = 0 ∧
    (Devm.getStor (twH5 sevm b) sevm.currentTarget).get feeSlot = 0 ∧
    (Devm.getStor (twH6 sevm b) sevm.currentTarget).get adminFeeSlot = 0 ∧
    (Devm.getStor (twH7 sevm b) sevm.currentTarget).get ownerSlot = 0 ∧
    (Devm.getStor (twH8 sevm b) sevm.currentTarget).get killDeadlineSlot = 0 ∧
    (Devm.getStor (twH9 sevm b) sevm.currentTarget).get tokenSlot = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hempty]; rfl
  · simp only [twH1, afterSstoreH_getStor_self, hempty]; decide +kernel
  · simp only [twH2, twH1, afterSstoreH_getStor_self, hempty]; decide +kernel
  · simp only [twH3, twH2, twH1, afterSstoreH_getStor_self, hempty]; decide +kernel
  · simp only [twH4, twH3, twH2, twH1, afterSstoreH_getStor_self, hempty]; decide +kernel
  · simp only [twH5, twH4, twH3, twH2, twH1, afterSstoreH_getStor_self, hempty]; decide +kernel
  · simp only [twH6, twH5, twH4, twH3, twH2, twH1, afterSstoreH_getStor_self, hempty]
    decide +kernel
  · simp only [twH7, twH6, twH5, twH4, twH3, twH2, twH1, afterSstoreH_getStor_self, hempty]
    decide +kernel
  · rw [stor_twH8 hempty]; decide +kernel
  · rw [twH9, afterSstoreH_getStor_self, stor_twH8 hempty, Stor.get_set_ite,
      ite_eq_right (by decide)]
    decide +kernel

end

/-! ## The exact Muir cost and the run -/

/-- The stores keep the creation metadata (refund, logs, deletions, the created target). -/
theorem meta_twH10 {sevm : Sevm} {b : Devm} {deletions : AdrSet}
    (hm : CreateRunMeta sevm.currentTarget deletions b)
    (hempty : Devm.getStor b sevm.currentTarget = Stor.empty) :
    CreateRunMeta sevm.currentTarget deletions (twH10 sevm b) := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := fresh_stores hempty
  exact (((((((((hm.afterSstoreH z0).afterSstoreH z1).afterSstoreH z2).afterSstoreH
    z3).afterSstoreH z4).afterSstoreH z5).afterSstoreH z6).afterSstoreH z7).afterSstoreH
    z8).afterSstoreH z9

/-- **The constructor's exact Muir Glacier cost**: 186,628 gas from a created account with empty
storage, at a timestamp whose kill deadline does not wrap. -/
theorem ctorCostH_muir {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules) {b : Devm}
    {deletions : AdrSet} (hm : CreateRunMeta sevm.currentTarget deletions b)
    (hempty : Devm.getStor b sevm.currentTarget = Stor.empty)
    (ht : sevm.benvStat.time.toNat + killDeadlineDt < 2 ^ 256) :
    ctorCostH sevm b = 186628 := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := fresh_stores hempty
  have m1 := hm.afterSstoreH (key := coinSlot 0) (value := coin0W) z0
  have m2 := m1.afterSstoreH (key := coinSlot 1) (value := coin1W) z1
  have m3 := m2.afterSstoreH (key := coinSlot 2) (value := coin2W) z2
  have m4 := m3.afterSstoreH (key := initialASlot) (value := ampW) z3
  have m5 := m4.afterSstoreH (key := futureASlot) (value := ampW) z4
  have m6 := m5.afterSstoreH (key := feeSlot) (value := feeW) z5
  have m7 := m6.afterSstoreH (key := adminFeeSlot) (value := adminFeeW) z6
  have m8 := m7.afterSstoreH (key := ownerSlot) (value := ownerW) z7
  have m9 := m8.afterSstoreH (key := killDeadlineSlot)
    (value := sevm.benvStat.time + 0x4f1a00) z8
  have hkill : sevm.benvStat.time + 0x4f1a00 ≠ 0 := by
    intro zero
    have word := kill_toNat ht
    rw [zero] at word
    have dt : killDeadlineDt = 5184000 := rfl
    have : (0 : B256).toNat = 0 := rfl
    omega
  unfold ctorCostH tailCostH
  rw [sstoreCostH_muir_fresh_set hmuir hm.created z0 (by decide),
    sstoreCostH_muir_fresh_set (base := twH1 sevm b) hmuir m1.created z1 (by decide),
    sstoreCostH_muir_fresh_set (base := twH2 sevm b) hmuir m2.created z2 (by decide),
    sstoreCostH_muir_fresh_set (base := twH3 sevm b) hmuir m3.created z3 (by decide),
    sstoreCostH_muir_fresh_set (base := twH4 sevm b) hmuir m4.created z4 (by decide),
    sstoreCostH_muir_fresh_set (base := twH5 sevm b) hmuir m5.created z5 (by decide),
    show adminFeeW = 0 from rfl,
    sstoreCostH_muir_created_zero (base := twH6 sevm b) hmuir m6.created,
    sstoreCostH_muir_fresh_set (base := twH7 sevm b) hmuir m7.created z7 (by decide),
    sstoreCostH_muir_fresh_set (base := twH8 sevm b) hmuir m8.created z8 hkill,
    sstoreCostH_muir_fresh_set (base := twH9 sevm b) hmuir m9.created z9 (by decide)]

/-- **The 3pool constructor under Muir Glacier, gas-exact, with its settlement facts.** -/
theorem ctor_run_muir {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules)
    (hstatic : sevm.isStatic = false) (hcode : sevm.code = code) (hvalue : sevm.value = 0)
    (ht : sevm.benvStat.time.toNat + killDeadlineDt < 2 ^ 256) {b : Devm} {deletions : AdrSet}
    (hm : CreateRunMeta sevm.currentTarget deletions b)
    (hempty : Devm.getStor b sevm.currentTarget = Stor.empty) {G : Nat} (hG : 2300 < G) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + 186628)) post ∧
      post.output = runtime ∧ post.error = b.error ∧
      Devm.getStor post sevm.currentTarget = deployedStor sevm.benvStat.time ∧
      post.gasLeft = G ∧ CreateRunMeta sevm.currentTarget deletions post := by
  have fr : CtorFrameH sevm := ⟨by rw [hmuir]; rfl, hstatic⟩
  have hrun : SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCostH sevm b))
      (returnPost (St (twH10 sevm b) [0, 0x52cf] m17 G) 0 0x52cf []) := by
    refine ⟨t_0000_c0, rfl, ?_⟩
    rw [show G + ctorCostH sevm b = G + tailCostH sevm b + 222 + 558 by unfold ctorCostH; omega]
    exact segA hcode hvalue (segBH fr hcode ht hG)
  rw [ctorCostH_muir hmuir hm hempty ht] at hrun
  obtain ⟨p1, p2, p3, p4⟩ := returnPost_facts (St (twH10 sevm b) [0, 0x52cf] m17 G) 0 0x52cf []
  refine ⟨_, hrun, ?_, ?_, ?_, p4, ((meta_twH10 hm hempty).st _ _ _).returnPost _ _ _⟩
  · rw [p1, St.memory]
    exact m17_read
  · rw [p2, St_error]
    simp only [twH10, twH9, twH8, twH7, twH6, twH5, twH4, twH3, twH2, twH1, afterSstoreH_error]
  · rw [p3, St_getStor, stor_twH10 hempty]

/-- **Real Muir Glacier CREATE-message execution of the 3pool constructor**, with the settlement
metadata a transaction pipeline consumes. -/
theorem pool_create_muir_meta (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code) (hgas : 4426428 ≤ msg.gas)
    (hmuir : msg.benv.stat.rules = muirGlacierRules) (hstatic : msg.isStatic = false)
    (ht : msg.benv.stat.time.toNat + killDeadlineDt < 2 ^ 256) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.Curve3Pool.code.toList ∧
      Devm.getStor post msg.currentTarget = deployedStor msg.benv.stat.time ∧
      post.error = none ∧ post.refundCounter = 0 ∧ post.logs = [] ∧
      post.accountsToDelete = msg.inheritedDeletions ∧
      post.gasLeft = msg.gas - 4426428 := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  set sevm := initSevm (createSeed msg benv) with hsevm
  set b := initDevm (createSeed msg benv) with hb
  have hstat : sevm.benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have hrules : sevm.benvStat.rules = muirGlacierRules := by rw [hstat]; exact hmuir
  have hsg : msg.benv.stat.rules.stateGas = none := by rw [hmuir]; rfl
  have hempty : Devm.getStor b sevm.currentTarget = Stor.empty := by
    show benv.state.getStor msg.currentTarget = _
    rw [benvAfterTransfer_ok_getStor htransfer msg.currentTarget (Or.inl hvalue),
      processCreateMessage_msg_getStor_currentTarget]
  have hcreated : sevm.currentTarget ∈ b.createdAccounts := by
    have heq := Msg.benvAfterTransfer_of_value_zero
      (msg := processCreateMessage.msg msg) hvalue
    have hbenv : benv = (processCreateMessage.msg msg).benv :=
      Except.ok.inj (htransfer.symm.trans heq)
    change msg.currentTarget ∈ benv.createdAccounts
    rw [hbenv]
    change msg.currentTarget ∈ msg.benv.createdAccounts.insert msg.currentTarget
    exact Std.HashSet.mem_insert_self
  have hlogs0 : b.logs = [] := initDevm_logs (by
    change sevm.benvStat.rules.stateGas = none
    rw [hrules]
    rfl)
  have hm : CreateRunMeta sevm.currentTarget b.accountsToDelete b :=
    ⟨rfl, hlogs0, rfl, hcreated⟩
  have ht' : sevm.benvStat.time.toNat + killDeadlineDt < 2 ^ 256 := by rw [hstat]; exact ht
  obtain ⟨raw, hrun, hout, herr, hst, hgasLeft, hmeta⟩ :=
    ctor_run_muir hrules hstatic hcode hvalue ht' hm hempty
      (G := msg.gas - 186628) (by omega)
  have hpre0 : St b [] Mem.empty (msg.gas - 186628 + 186628) = b :=
    pre_eq_St rfl rfl (by show _ = msg.gas; omega)
  rw [hpre0] at hrun
  have hlen : raw.output.length = 0x52cf := by rw [hout]; exact runtime_length
  have herr' : raw.error = .none := by rw [herr]; rfl
  have hprefix : raw.output.head? ≠ some 0xEF := by rw [hout]; exact runtime_head
  have hdep : raw.output.length * gasCodeDeposit ≤ raw.gasLeft := by
    rw [hlen, hgasLeft]; unfold gasCodeDeposit; omega
  have hmax : raw.output.length ≤ msg.benv.stat.rules.code.maxCodeSize := by
    rw [hlen, hmuir]; decide
  obtain ⟨post, hpost, hcodePost, hstorPost, herror⟩ := liftCreate_okH cert_check jumps_ok msg
    hcodeAddress hcode hsg htransfer hrun herr' hprefix hdep hmax
  have hexact := liftCreate_postH cert_check jumps_ok msg
    hcodeAddress hcode hsg htransfer hrun herr' hprefix hdep hmax
  have hpostEq : post = liftCreatePost msg.currentTarget
      (raw.recordTouch msg.benv.stat.rules true msg.currentTarget) :=
    Except.ok.inj (hpost.symm.trans hexact)
  have hnonempty : ¬ ({ raw.state.get msg.currentTarget with
      code := ⟨⟨raw.output⟩⟩ } : Acct).Empty := by
    intro empty
    have zero : raw.output.length = 0 := empty.1
    omega
  refine ⟨post, hpost, ?_, ?_, herror, ?_, ?_, ?_, ?_⟩
  · rw [hcodePost, hout, ByteArray.toList_eq_toList_data]
  · simp only [hstorPost, Acct.clearIfEmpty_stor, hnonempty, ↓reduceIte]
    show Devm.getStor raw sevm.currentTarget = _
    rw [hst, hstat]
  · rw [hpostEq]
    show raw.refundCounter = 0
    exact hmeta.refund
  · rw [hpostEq]
    show raw.logs = _
    exact hmeta.logs
  · rw [hpostEq]
    show raw.accountsToDelete = _
    rw [hmeta.deletions]
    rfl
  · rw [hpostEq, (liftCreatePost_facts _ _).2.1, (recordTouch_meta _ _ _ _).2.2.2,
      Devm.recordTouch_output, hgasLeft, hlen]
    unfold gasCodeDeposit
    omega

end Blanc.Lift.Curve3Pool.Creation
