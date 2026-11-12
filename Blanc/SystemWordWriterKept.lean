import Blanc.Lift.SystemWordWriter

/-! The original CALL spawned by the shared privileged word writer. This is a
single-step producer: child entry, execution, settlement and retention remain
obligations of the consumer. -/

namespace Blanc.Lift.SystemWordWriter

open Jaune

/-- The writer's exact zero-value CALL spawns its actual message and resume.
No child execution or successful settlement is assumed. -/
theorem call_spawn {sevm : Sevm} {base : Devm} {target : Adr} {word : B256}
    {gas : Nat} {childCode : ByteArray}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (gasLt : gas < 2 ^ 256) (affordable : accessCost target base.accessedAddresses ≤ gas)
    (installed : base.getCode target = childCode)
    (nondelegated : getDelegatedCodeAddress childCode = none) :
    Xinst.step sevm
      (base.setMach ⟨[gas.toB256, target.toBytes.toB256, 0, 0, 32, 0, 0], wordMemory word,
        gas, base.stateGas⟩) .call =
      .spawn (Frame.ofCall (childMsg sevm base target word gas childCode))
        (.call (parent base target word gas) 0 0) := by
  let bare := base.setMach ⟨[], wordMemory word, gas, base.stateGas⟩
  have delegation : accessDelegation (addAccessedAddress bare target) target =
      (false, target, childCode, 0, addAccessedAddress bare target) := by
    unfold accessDelegation
    change (match getDelegatedCodeAddress (base.getCode target) with
      | some a => (true, a, base.getCode a, accessCost a (addAccessedAddress bare target).accessedAddresses,
          addAccessedAddress (addAccessedAddress bare target) a)
      | none => (false, target, base.getCode target, 0, addAccessedAddress bare target)) = _
    rw [installed, nondelegated]
  have splitGas : calculateMsgCallGas 0 gas.toB256.toNat gas 0 (accessCost target base.accessedAddresses) =
      (forwardedGas base target gas + accessCost target base.accessedAddresses,
        forwardedGas base target gas) := by
    rw [calculateMsgCallGas_zero (by omega), B256.toNat_toB256_of_lt gasLt]
    simp only [Nat.sub_zero]
    have bound : forwardedGas base target gas ≤ gas := by
      unfold forwardedGas except64th
      omega
    unfold forwardedGas at bound
    rw [Nat.min_eq_right bound]
    rfl
  have spawned := Xinst.step_call_zero_value_spawn
    (sevm := sevm)
    (devm := base.setMach ⟨[gas.toB256, target.toBytes.toB256, 0, 0, 32, 0, 0], wordMemory word,
      gas, base.stateGas⟩)
    (gw := gas.toB256) (cw := target.toBytes.toB256)
    (iiw := 0) (isw := 32) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := target) (code := childCode) (dgc := 0)
    (d1 := addAccessedAddress bare target) (ext := 0)
    (acc := accessCost target base.accessedAddresses)
    (mcs := forwardedGas base target gas)
    (mcc := forwardedGas base target gas + accessCost target base.accessedAddresses)
    (fork.callEra false) rfl ?_ ?_ ?_ splitGas ?_ depth
  · simpa only [childMsg, parent, bare, target_word, Nat.add_zero,
      B256.toNat_zero, show (32 : B256).toNat = 32 from rfl] using spawned
  · apply Devm.extCost_covered
    change memExtsSize (wordMemory word).size [(0, 32), (0, 0)] = (wordMemory word).size
    rw [show (wordMemory word).size = 32 from Mem.size_write_word]
    rfl
  · rw [target_word]
    exact delegation
  · rw [target_word]
    rfl
  · change forwardedGas base target gas + accessCost target base.accessedAddresses + 0 ≤ gas
    unfold forwardedGas except64th
    omega

end Blanc.Lift.SystemWordWriter
