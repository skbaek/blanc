import Blanc.Lift.Usdc.RefineTransfer

/-!
# FiatTokenV2_2: what a successful move does to the balance bits

U0's write table speaks of whole packed words, so no V2_2 row carries `nonInc`.  The frame laws
`frame_transfer` and `frame_transferFrom` settle it at the frame level: every written balance word
carries a clear flag, the source's bits fall by the value, the recipient's rise by it, and no other
slot's balance bits move.  Blacklist words keep their bits by `balanceBits_blacklistWord` and
`balanceBits_unBlacklistWord`.  Slot apartness is the consumer's hash premise.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

theorem bits_toB256_of_le {n : Nat} (h : n ≤ 2 ^ 255 - 1) : balanceBits (Nat.toB256 n) = n :=
  balanceBits_toB256 (by omega)

/-- A word with a clear flag is its balance bits. -/
theorem word_eq_bits {w : B256} (hf : frozenBit w = false) : w.toNat = balanceBits w := by
  unfold frozenBit at hf
  unfold balanceBits
  rw [decide_eq_false_iff_not, Nat.not_le] at hf
  exact (Nat.mod_eq_of_lt hf).symm

/-- **A move does not lower the balance bits of any slot but its source's.** -/
theorem move_bits_ge {σ : Stor} {a d : Adr} {v : Nat} {k : B256} (hk : k ≠ balSlot a)
    (hb : balanceBits ((debitStor σ a v).get (balSlot d)) + v ≤ 2 ^ 255 - 1) :
    balanceBits (σ.get k) ≤ balanceBits ((creditStor (debitStor σ a v) d v).get k) := by
  have h1 : (debitStor σ a v).get k = σ.get k := Stor.get_set_ne _ (Ne.symm hk) _
  unfold creditStor
  by_cases hkd : k = balSlot d
  · subst hkd
    rw [Stor.get_set_self, bits_toB256_of_le hb, ← h1]
    omega
  · rw [Stor.get_set_ne _ (Ne.symm hkd), h1]

/-- **The source's bits fall by the value**, apart from a self-move, and its word carries no flag. -/
theorem move_bits_source {σ : Stor} {a d : Adr} {v : Nat} (hne : balSlot a ≠ balSlot d)
    (hv : v ≤ balanceBits (σ.get (balSlot a))) :
    balanceBits ((creditStor (debitStor σ a v) d v).get (balSlot a)) + v =
      balanceBits (σ.get (balSlot a)) := by
  have lt : balanceBits (σ.get (balSlot a)) < 2 ^ 255 :=
    Nat.mod_lt _ (Nat.two_pow_pos 255)
  unfold creditStor debitStor
  rw [Stor.get_set_ne _ hne.symm, Stor.get_set_self, balanceBits_toB256 (by omega)]
  omega

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {post : Devm}

/-- **A `transfer` frame lowers no balance bits but its caller's.** -/
theorem frame_transfer_bits_ge (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm = 0xa9059cbb)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) {k : B256}
    (hk : k ≠ balSlot sevm.caller) :
    balanceBits ((Devm.getStor b sevm.currentTarget).get k) ≤
      balanceBits ((Devm.getStor post sevm.currentTarget).get k) := by
  obtain ⟨-, -, -, -, -, -, -, hb, sp⟩ := frame_transfer fork sel run
  rw [sp]
  exact move_bits_ge hk hb

/-- **A `transferFrom` frame lowers no balance bits but its source's** (the allowance slot, apart
from every balance slot by the consumer's premise, is written too). -/
theorem frame_transferFrom_bits_ge (fork : CoveredFork sevm.benvStat.fork)
    (sel : Sevm.selector sevm = 0x23b872dd)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) {k : B256}
    (hk : k ≠ balSlot (Sevm.dataWord sevm 4).toAdr)
    (ha : k ≠ allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) :
    balanceBits ((Devm.getStor b sevm.currentTarget).get k) ≤
      balanceBits ((Devm.getStor post sevm.currentTarget).get k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hb, -, sp⟩ := frame_transferFrom fork sel run
  rw [sp, Stor.get_set_ne _ (Ne.symm ha)]
  exact move_bits_ge hk hb

end Blanc.Lift.Usdc
