import Blanc.Lift.WithdrawalRequest.SystemLoop
import Blanc.Lift.WalkSteps
import Blanc.Lift.Deploy

/-! Actual sequential word-state bookkeeping. Pointer and excess arithmetic
remain modulo 256 bits; no queue no-alias or Nat excess premise is introduced. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

def systemAdvancedHead (head count : B256) : B256 := head + count

def systemPointerBase (sevm : Sevm) (base : Devm) (head tail count : B256) : Devm :=
  if systemAdvancedHead head count = tail then
    afterSstore sevm (afterSstore sevm base 2 0) 3 0
  else afterSstore sevm base 2 (systemAdvancedHead head count)

def systemPointerGas (sevm : Sevm) (base : Devm) (head tail count : B256) : Nat :=
  29 + if systemAdvancedHead head count = tail then
    16 + sstoreCost sevm base 2 0 + sstoreCost sevm (afterSstore sevm base 2 0) 3 0
  else 17 + sstoreCost sevm base 2 (systemAdvancedHead head count)

def systemOldExcess (sevm : Sevm) (base : Devm) : B256 :=
  base.getStorVal sevm.currentTarget 0

def systemEffectiveExcess (sevm : Sevm) (base : Devm) : B256 :=
  if systemOldExcess sevm base = B256.max then 0 else systemOldExcess sevm base

def systemExcessRead (sevm : Sevm) (base : Devm) : Devm := afterSload sevm base 0

def systemExcessReadGas (sevm : Sevm) (base : Devm) : Nat :=
  28 + sloadCost sevm base 0 + if systemOldExcess sevm base = B256.max then 4 else 0

def systemPendingCount (sevm : Sevm) (base : Devm) : B256 :=
  (systemExcessRead sevm base).getStorVal sevm.currentTarget 1

def systemCountRead (sevm : Sevm) (base : Devm) : Devm :=
  afterSload sevm (systemExcessRead sevm base) 1

def systemExcessSum (sevm : Sevm) (base : Devm) : B256 :=
  systemPendingCount sevm base + systemEffectiveExcess sevm base

def systemNewExcess (sevm : Sevm) (base : Devm) : B256 :=
  if (2 : B256) < systemExcessSum sevm base then systemExcessSum sevm base - 2 else 0

def systemCountReadGas (sevm : Sevm) (base : Devm) : Nat :=
  32 + sloadCost sevm (systemExcessRead sevm base) 1 +
    if (2 : B256) < systemExcessSum sevm base then 13 else 17

def systemExcessStore (sevm : Sevm) (base : Devm) : Devm :=
  afterSstore sevm (systemCountRead sevm base) 0 (systemNewExcess sevm base)

def systemBookkeepingBase (sevm : Sevm) (base : Devm) : Devm :=
  afterSstore sevm (systemExcessStore sevm base) 1 0

def systemReturnSize (count : B256) : B256 := 76 * count

theorem systemReturnSize_toNat {count : B256} (cap : count.toNat ≤ 16) :
    (systemReturnSize count).toNat = 76 * count.toNat := by
  have width : (76 * 16 : Nat) < 2 ^ 256 := by decide
  unfold systemReturnSize
  rw [B256.toNat_mul, show (76 : B256).toNat = 76 by decide, Nat.lo_eq_of_lt (by omega)]

def systemReturnGas (memory : Mem) (count : B256) : Nat :=
  calculateMemoryGasCost (memExtSize memory.size 0 (systemReturnSize count).toNat) -
    calculateMemoryGasCost memory.size

def systemBookkeepingPost (sevm : Sevm) (base : Devm) (memory : Mem) (count : B256)
    (gas : Nat) : Devm :=
  returnPost (St (systemBookkeepingBase sevm base) [0, systemReturnSize count] memory gas)
    0 (systemReturnSize count) []

def systemFinalStoresGas (sevm : Sevm) (base : Devm) (memory : Mem) (count : B256) : Nat :=
  18 + sstoreCost sevm (systemCountRead sevm base) 0 (systemNewExcess sevm base) +
    sstoreCost sevm (systemExcessStore sevm base) 1 0 + systemReturnGas memory count

def systemBookkeepingGas (sevm : Sevm) (base : Devm) (memory : Mem)
    (head tail count : B256) : Nat :=
  let pointers := systemPointerBase sevm base head tail count
  systemPointerGas sevm base head tail count + systemExcessReadGas sevm pointers +
    systemCountReadGas sevm pointers + systemFinalStoresGas sevm pointers memory count

end Blanc.Lift.WithdrawalRequest
