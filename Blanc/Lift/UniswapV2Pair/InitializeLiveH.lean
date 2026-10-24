import Blanc.Lift.UniswapV2Pair.InitializeEntries
import Blanc.Lift.HistCreate

/-!
# The Pair's `initialize`, live, under historical rule facts

`initialize_bytecode_live_raw` (`InitializeEntries.lean`) constructs the successful pc-zero run of
the certified runtime's `initialize(address,address)` under a covered fork: its storage steps
charge the EIP-2929 warm/cold schedule. The forms below read only `rules.stateGas = none` and the
shifts (the dispatcher's `SHR`), and charge under the frame's actual access schedule and `SSTORE`
regime (`sloadCostH`, `sstoreCostH`), ending at `initializePublicPostH`:

* `initializeStorageChargeH` and its five parts;
* `initializeWrites_exactH`, `initialize45_exactH`, `initialize_decoder_exactH`,
  `initialize_entry_exactH`, `initialize_pc0_exactH` — the walks of their covered counterparts;
* `initialize_bytecode_live_rawH` — the successful run.
-/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The five storage charges of `initialize` under the frame's actual schedule. -/
def initializeFactoryChargeH (sevm : Sevm) (b : Devm) : Nat := sloadCostH sevm b 5
def initializeLoad0ChargeH (sevm : Sevm) (b : Devm) : Nat :=
  sloadCostH sevm (initializeFactoryBaseH sevm b) 6
def initializeStore0ChargeH (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCostH sevm (initializeLoaded0H sevm (initializeFactoryBaseH sevm b)) 6
    (initializeWord0 sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm))
def initializeLoad1ChargeH (sevm : Sevm) (b : Devm) : Nat :=
  sloadCostH sevm (initializeStored0H sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm)) 7
def initializeStore1ChargeH (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCostH sevm (initializeLoaded1H sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm))
    7 (initializeWord1H sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm)
      (initializeToken1 sevm))
def initializeStorageChargeH (sevm : Sevm) (b : Devm) : Nat :=
  initializeFactoryChargeH sevm b + initializeLoad0ChargeH sevm b + initializeStore0ChargeH sevm b +
    initializeLoad1ChargeH sevm b + initializeStore1ChargeH sevm b

/-- Under a flat `SLOAD` price of at most 2100, the five charges total at most 72,600. -/
theorem initializeStorageChargeH_le {sevm : Sevm} (b : Devm)
    (flat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 2100) :
    initializeStorageChargeH sevm b ≤ 72600 := by
  have := sloadCostH_le (base := b) (key := 5) flat
  have := sloadCostH_le (base := initializeFactoryBaseH sevm b) (key := 6) flat
  have := sloadCostH_le
    (base := initializeStored0H sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm))
    (key := 7) flat
  have := sstoreCostH_le (devm := initializeLoaded0H sevm (initializeFactoryBaseH sevm b)) (key := 6)
    (value := initializeWord0 sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm)) flat
  have := sstoreCostH_le
    (devm := initializeLoaded1H sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm))
    (key := 7) (value := initializeWord1H sevm (initializeFactoryBaseH sevm b) (initializeToken0 sevm)
      (initializeToken1 sevm)) flat
  unfold initializeStorageChargeH initializeFactoryChargeH initializeLoad0ChargeH
    initializeStore0ChargeH initializeLoad1ChargeH initializeStore1ChargeH
  omega

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

/-- `SLOAD` with its historical charge named. -/
theorem rx_sload_selCH {k' : B256} {c : Nat} (hsg : sevm.benvStat.rules.stateGas = none)
    (hc : c = sloadCostH sevm b k') (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (afterSloadH sevm b k') (b.getStorVal sevm.currentTarget k' :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + c)) (.next (.reg .sload) f) o := by
  subst hc; exact rx_sload_selH hsg hroom k

/-- `SSTORE` with its historical charge named. -/
theorem rx_sstoreCH {k' v : B256} {c : Nat} (hsg : sevm.benvStat.rules.stateGas = none)
    (hc : c = sstoreCostH sevm b k' v) (hsentry : gCallStipend < G + c)
    (hstatic : sevm.isStatic = false)
    (k : SFunc.RunExact fs sevm (St (afterSstoreH sevm b k' v) S M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: v :: S) M (G + c)) (.next (.reg .sstore) f) o := by
  subst hc; exact rx_sstoreH hsg (fun _ => hsentry) hstatic k

end Steps

/-- `initializeWrites_exact` under historical rule facts. -/
theorem initializeWrites_exactH {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G load0 store0 load1 store1 : Nat} {token0 token1 : Adr} {ρ : B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (cost0 : load0 = sloadCostH sevm b 6)
    (costS0 : store0 = sstoreCostH sevm (initializeLoaded0H sevm b) 6 (initializeWord0 sevm b token0))
    (cost1 : load1 = sloadCostH sevm (initializeStored0H sevm b token0) 7)
    (costS1 : store1 = sstoreCostH sevm (initializeLoaded1H sevm b token0) 7
      (initializeWord1H sevm b token0 token1))
    (sentry0 : gCallStipend < G + store0 + load1 + store1 + 38)
    (sentry1 : gCallStipend < G + store1 + 8)
    (nonstatic : sevm.isStatic = false) (room : R.length ≤ 1016) :
    SFunc.RunExact fs sevm (St b (token1.toB256 :: token0.toB256 :: ρ :: R) M
      (G + load0 + store0 + load1 + store1 + 78)) t_0fb2_c45
      (.returned (St (initializeWritesBaseH sevm b token0 token1) R M G)) := by
  unfold t_0fb2_c45
  refine rx_dest ?_
  refine rx_push (w := 6) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  rw [show G + load0 + store0 + load1 + store1 + 71 =
      (G + store0 + load1 + store1 + 71) + load0 from by omega]
  refine rx_sload_selCH hsg cost0 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 3) rfl ?_
  dsimp only [List.set]
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := token0.toB256) (addressSlotReadWord_toB256 token0)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := addressMask) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_and rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_or (v := initializeWord0 sevm b token0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  rw [show G + store0 + load1 + store1 + 38 =
      (G + load1 + store1 + 38) + store0 from by omega]
  refine rx_sstoreCH hsg costS0 (by omega) nonstatic ?_
  refine rx_push (w := 7) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  rw [show G + load1 + store1 + 32 = (G + store1 + 32) + load1 from by omega]
  refine rx_sload_selCH hsg cost1 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap3 ?_
  refine rx_swap1 ?_
  refine rx_swap (n := 3) rfl ?_
  dsimp only [List.set]
  refine rx_and (v := token1.toB256) (addressSlotReadWord_toB256 token1)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_and (v := addressMask &&& (initializeStored0H sevm b token0).getStorVal sevm.currentTarget 7)
    (B256.and_comm _ _) (by simp only [List.length_cons]; omega) ?_
  refine rx_or (v := initializeWord1H sevm b token0 token1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  rw [show G + store1 + 8 = (G + 8) + store1 from by omega]
  refine rx_sstoreCH hsg costS1 (by omega) nonstatic ?_
  exact rx_ret

/-- `initialize45_exact` under historical rule facts. -/
theorem initialize45_exactH {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G factoryLoad load0 store0 load1 store1 : Nat}
    {token0 token1 : Adr} {ρ : B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (factoryCost : factoryLoad = sloadCostH sevm b 5)
    (cost0 : load0 = sloadCostH sevm (initializeFactoryBaseH sevm b) 6)
    (costS0 : store0 = sstoreCostH sevm (initializeLoaded0H sevm (initializeFactoryBaseH sevm b)) 6
      (initializeWord0 sevm (initializeFactoryBaseH sevm b) token0))
    (cost1 : load1 = sloadCostH sevm (initializeStored0H sevm (initializeFactoryBaseH sevm b) token0) 7)
    (costS1 : store1 = sstoreCostH sevm (initializeLoaded1H sevm (initializeFactoryBaseH sevm b) token0) 7
      (initializeWord1H sevm (initializeFactoryBaseH sevm b) token0 token1))
    (sentry0 : gCallStipend < G + store0 + load1 + store1 + 38)
    (sentry1 : gCallStipend < G + store1 + 8)
    (nonstatic : sevm.isStatic = false) (room : R.length ≤ 1016) :
    SFunc.RunExact fs sevm (St b (token1.toB256 :: token0.toB256 :: ρ :: R) M
      (G + factoryLoad + load0 + store0 + load1 + store1 + 106)) t_0f2c_c45
      (.returned (St (initializeCoreBaseH sevm b token0 token1) R M G)) := by
  unfold t_0f2c_c45
  refine rx_dest ?_
  refine rx_push (w := 5) rfl (by simp only [List.length_cons]; omega) ?_
  rw [show G + factoryLoad + load0 + store0 + load1 + store1 + 102 =
    (G + load0 + store0 + load1 + store1 + 102) + factoryLoad from by omega]
  refine rx_sload_selCH hsg factoryCost (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := (b.getStorVal sevm.currentTarget 5).toAdr.toB256)
    (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons]; omega) ?_
  refine rx_caller (by simp only [List.length_cons]; omega) ?_
  refine rx_eq (v := 1) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [authorized]; exact ite_eq_left rfl
  refine rx_push (w := 0x0fb2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_succ (by decide : (1 : B256) ≠ 0) ?_
  exact initializeWrites_exactH hsg cost0 costS0 cost1 costS1 sentry0 sentry1 nonstatic room

/-- `initialize_decoder_exact` under historical rule facts. -/
theorem initialize_decoder_exactH {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (sentry0 : gCallStipend < G + initializeStore0ChargeH sevm b + initializeLoad1ChargeH sevm b +
      initializeStore1ChargeH sevm b + 39)
    (sentry1 : gCallStipend < G + initializeStore1ChargeH sevm b + 9)
    (nonstatic : sevm.isStatic = false) :
    SFunc.RunExact cert.prog sevm (St b [avail, 4, 0x0257, sel] M
      (G + initializeStorageChargeH sevm b + 151)) t_0434_c90
      (.halted (initializePublicPostH sevm b [sel] M G)) := by
  unfold t_0434_c90
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (v := (initializeToken0 sevm).toB256)
    (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_swap2 ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_add' (v := 36) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (v := (initializeToken1 sevm).toB256)
    (by rw [B256.and_comm]; exact addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0f2c) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  rw [show G + initializeStorageChargeH sevm b + 115 =
    ((G + 1) + initializeFactoryChargeH sevm b + initializeLoad0ChargeH sevm b +
      initializeStore0ChargeH sevm b + initializeLoad1ChargeH sevm b + initializeStore1ChargeH sevm b + 106) + 8
    from by unfold initializeStorageChargeH; omega]
  refine rx_callRet (g := t_0f2c_c45) rfl
    (initialize45_exactH hsg authorized rfl rfl rfl rfl rfl (by omega) (by omega) nonstatic
      (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact initializeStop_exact

/-- `initialize_entry_exact` under historical rule facts. -/
theorem initialize_entry_exactH {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (sentry0 : gCallStipend < G + initializeStore0ChargeH sevm b + initializeLoad1ChargeH sevm b +
      initializeStore1ChargeH sevm b + 39)
    (sentry1 : gCallStipend < G + initializeStore1ChargeH sevm b + 9)
    (nonstatic : sevm.isStatic = false) :
    SFunc.RunExact cert.prog sevm (St b [sel] M
      (G + initializeStorageChargeH sevm b + 191)) t_041e_c90
      (.halted (initializePublicPostH sevm b [sel] M G)) := by
  unfold t_041e_c90
  refine rx_dest ?_
  refine rx_push (w := 0x0257) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 4) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_sub' (v := sevm.data.length.toB256 - 4) rfl
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le guard)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0434) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  exact initialize_decoder_exactH hsg authorized sentry0 sentry1 nonstatic

/-- `initialize_pc0_exact` under historical rule facts. -/
theorem initialize_pc0_exactH {sevm : Sevm} {b : Devm} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none) (hshifts : sevm.benvStat.rules.op.shifts = true)
    (value : sevm.value = 0)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (sentry0 : gCallStipend < G + initializeStore0ChargeH sevm b + initializeLoad1ChargeH sevm b +
      initializeStore1ChargeH sevm b + 39)
    (sentry1 : gCallStipend < G + initializeStore1ChargeH sevm b + 9)
    (nonstatic : sevm.isStatic = false) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + initializeStorageChargeH sevm b + 377))
      (initializePublicPostH sevm b [0x485cc955] getterInitMemory G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  rw [show G + initializeStorageChargeH sevm b + 377 =
    (G + initializeStorageChargeH sevm b + 191) + 186 from by omega]
  exact initialize_dispatch_exact (h_shifts := hshifts) value size selector
    (initialize_entry_exactH hsg guard authorized sentry0 sentry1 nonstatic)

/-- **`initialize`, live, under historical rule facts.**  As `initialize_bytecode_live_raw`,
from `rules.stateGas = none` and the shifts, at the closed gas
`G + initializeStorageChargeH + 377`, ending at `initializePublicPostH`. -/
theorem initialize_bytecode_live_rawH {sevm : Sevm} {b : Devm} {G : Nat}
    (codeEq : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hshifts : sevm.benvStat.rules.op.shifts = true)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (sentry0 : gCallStipend < G + initializeStore0ChargeH sevm b + initializeLoad1ChargeH sevm b +
      initializeStore1ChargeH sevm b + 39)
    (sentry1 : gCallStipend < G + initializeStore1ChargeH sevm b + 9)
    (nonstatic : sevm.isStatic = false) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty (G + initializeStorageChargeH sevm b + 377))
      (.ok (initializePublicPostH sevm b [0x485cc955] getterInitMemory G))) :=
  lift_exact_noStateGas cert_check jumps_ok codeEq hsg
    (initialize_pc0_exactH hsg hshifts value size selector guard authorized sentry0 sentry1
      nonstatic)

end Blanc.Lift.UniswapV2Pair
