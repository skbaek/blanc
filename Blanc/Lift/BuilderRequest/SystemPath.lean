import Blanc.Lift.RequestSystem.Path

/-!
# The EIP-8282 builder contracts' excess arm

The builder runtimes branch on the calldata first: nonempty calldata stores the inhibitor (the latch). On
empty calldata they read the excess and the count, and the inhibitor takes the no-excess arm, so it
resets the excess to zero whatever the count. `latchShape` is this arm as a `SysShape`.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestFee (PushWord)
open RequestSystem

/-- The pushed words of the builder contracts' excess arm. -/
structure LatchWords where
  /-- Destination of the calldata latch. -/
  latch : PushWord
  /-- Destination taken when no excess carries over. -/
  noCarry : PushWord
  /-- Destination taken when some excess carries over. -/
  carry : PushWord
  /-- Destination of the final stores. -/
  final : PushWord
  /-- Requests per block the excess is measured against. -/
  target : PushWord
  /-- Bytes per returned record. -/
  len : PushWord

section Trees

variable (p : LatchWords)

/-- No excess: drop both words and store zero. -/
def sysNoCarry : SFunc :=
  (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [] (by decide))
  (.next (.push (p.final.head :: p.final.tail) p.final.le) (.jump 5))))))

/-- Some excess: `count + excess - target`. -/
def sysCarry : SFunc :=
  (.dest (.next (.reg .add) (.next (.push (p.target.head :: p.target.tail) p.target.le)
  (.next (.reg (.swap 0)) (.next (.reg .sub)
  (.next (.push (p.final.head :: p.final.tail) p.final.le) (.jump 5)))))))

/-- `count + excess > target`? -/
def sysOver : SFunc :=
  (.next (.push (p.target.head :: p.target.tail) p.target.le) (.next (.reg (.dup 2))
  (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .gt)
  (.next (.push (p.carry.head :: p.carry.tail) p.carry.le)
  (.branch (sysNoCarry p) (sysCarry p))))))))

/-- Read excess and count; the inhibitor takes the no-excess arm. -/
def sysRead : SFunc :=
  (.next (.push [] (by decide)) (.next (.reg .sload) (.next (.push [0x01] (by decide))
  (.next (.reg .sload) (.next (.reg (.dup 1))
  (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff] (by decide)) (.next (.reg .eq)
  (.next (.push (p.noCarry.head :: p.noCarry.tail) p.noCarry.le)
  (.branchTo (sysOver p) 4)))))))))

/-- Nonempty calldata stores the inhibitor: the calldata latch. -/
def sysLatch : SFunc :=
  (.dest (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff] (by decide)) (sysFinal p.len)))

/-- The excess update's entry: branch on the calldata. -/
def sysExcess : SFunc :=
  (.dest (.next (.reg .calldatasize) (.next (.push (p.latch.head :: p.latch.tail) p.latch.le)
  (.branch (sysRead p) (sysLatch p)))))

end Trees

/-! ## The excess -/

/-- The excess the code stores: the inhibitor resets to zero, otherwise `count + excess - target` in
words when that sum exceeds the target, else zero. -/
def excessNext (target excess count : B256) : B256 :=
  if B256.max = excess then 0
  else if count + excess > target then (count + excess) - target else 0

/-- The fixed charge of the excess update on empty calldata. -/
def excessFixed (target excess count : B256) : Nat :=
  if B256.max = excess then 61
  else if count + excess > target then 95 else 89

section Walks

variable (p : LatchWords) {fs : List SFunc} {sevm : Sevm}

theorem noCarry_run {d : Devm} {x y c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hpush0 : sevm.benvStat.rules.op.push0 = true) (h5 : fs[5]? = some (sysFinal p.len))
    (next : SFunc.RunExact fs sevm (St d [0, c] M G) (sysFinal p.len) oc) :
    SFunc.RunExact fs sevm (St d [x, y, c] M (G + 8 + 3 + 2 + 2 + 2 + 1)) (sysNoCarry p) oc := by
  unfold sysNoCarry
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  exact rx_jump h5 next

theorem carry_run {d : Devm} {x y c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (h5 : fs[5]? = some (sysFinal p.len))
    (next : SFunc.RunExact fs sevm (St d [(x + y) - p.target.word, c] M G) (sysFinal p.len) oc) :
    SFunc.RunExact fs sevm (St d [x, y, c] M (G + 8 + 3 + 3 + 3 + 3 + 3 + 1)) (sysCarry p) oc := by
  unfold sysCarry
  refine rx_dest ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_push (w := p.target.word) rfl (by rroom) ?_
  refine rx_swap1 ?_
  refine rx_sub' rfl (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  exact rx_jump h5 next

/-- The excess update on empty calldata, every arm. -/
theorem excess_run {d : Devm} {c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hdata : sevm.data = []) (h4 : fs[4]? = some (sysNoCarry p)) (h5 : fs[5]? = some (sysFinal p.len))
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm (afterSloadA sevm d 0) 1)
        [excessNext p.target.word (d.getStorVal sevm.currentTarget 0)
          (d.getStorVal sevm.currentTarget 1), c] M G) (sysFinal p.len) oc) :
    SFunc.RunExact fs sevm (St d [c] M (G + excessGas (excessFixed p.target.word) sevm d)) (sysExcess p) oc := by
  have hz : sevm.data.length.toB256 = 0 := by rw [hdata]; rfl
  generalize he : d.getStorVal sevm.currentTarget 0 = e at next
  generalize hn : d.getStorVal sevm.currentTarget 1 = n at next
  have hn' : (afterSloadA sevm d 0).getStorVal sevm.currentTarget 1 = n := by
    rw [afterSloadA_getStorVal, hn]
  have hgas : ∀ F, excessFixed p.target.word e n = F →
      G + excessGas (excessFixed p.target.word) sevm d =
        G + F + sloadCost sevm d 0 + sloadCost sevm (afterSloadA sevm d 0) 1 := by
    intro F hF
    simp only [excessGas, he, hn, hF]
    omega
  by_cases hinh : B256.max = e
  · have hflag : B256.eqCheck B256.max e = 1 := by simp only [B256.eqCheck, hinh, ite_true]
    have hnext : excessNext p.target.word e n = 0 := by simp only [excessNext, hinh, ite_true]
    rw [hnext] at next
    have nx := noCarry_run p (x := n) (y := e) hpush0 h5 next
    have e' : G + excessGas (excessFixed p.target.word) sevm d =
        G + 8 + 3 + 2 + 2 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSloadA sevm d 0) 1 + 3
          + sloadCost sevm d 0 + 2 + 10 + 3 + 2 + 1 := by
      rw [hgas 61 (by simp only [excessFixed, hinh, ite_true])]
      omega
    rw [e']
    unfold sysExcess sysRead
    refine rx_dest ?_
    refine rx_calldatasize (by rroom) ?_
    rw [hz]
    refine rx_push rfl (by rroom) ?_
    refine rx_branch_zero ?_
    refine rx_push0 hpush0 (by rroom) ?_
    refine rx_sloadV hacc (by rroom) he ?_
    refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadV hacc (by rroom) hn' ?_
    refine rx_dup2 (by rroom) ?_
    refine rx_push inhibitor_push (by rroom) ?_
    refine rx_eq hflag (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branchTo_succ (by decide) h4 ?_
    exact nx
  · have hflag : B256.eqCheck B256.max e = 0 := by simp only [B256.eqCheck, hinh, ite_false]
    by_cases hgt : n + e > p.target.word
    · have hcap : B256.gtCheck (n + e) p.target.word = 1 := by
        simp only [B256.gtCheck, hgt, ite_true]
      have hnext : excessNext p.target.word e n = (n + e) - p.target.word := by
        simp only [excessNext, hinh, hgt, ite_true, ite_false]
      rw [hnext] at next
      have nx := carry_run p (x := n) (y := e) h5 next
      have e' : G + excessGas (excessFixed p.target.word) sevm d =
          G + 8 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 3 + 3
            + sloadCost sevm (afterSloadA sevm d 0) 1 + 3 + sloadCost sevm d 0 + 2 + 10 + 3 + 2 + 1 := by
        rw [hgas 95 (by simp only [excessFixed, hinh, hgt, ite_true, ite_false])]
        omega
      rw [e']
      unfold sysExcess sysRead sysOver
      refine rx_dest ?_
      refine rx_calldatasize (by rroom) ?_
      rw [hz]
      refine rx_push rfl (by rroom) ?_
      refine rx_branch_zero ?_
      refine rx_push0 hpush0 (by rroom) ?_
      refine rx_sloadV hacc (by rroom) he ?_
      refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
      refine rx_sloadV hacc (by rroom) hn' ?_
      refine rx_dup2 (by rroom) ?_
      refine rx_push inhibitor_push (by rroom) ?_
      refine rx_eq hflag (by rroom) ?_
      refine rx_push rfl (by rroom) ?_
      refine rx_branchTo_zero ?_
      refine rx_push (w := p.target.word) rfl (by rroom) ?_
      refine rx_dup3 (by rroom) ?_
      refine rx_dup3 (by rroom) ?_
      refine rx_add' rfl (by rroom) ?_
      refine rx_gt hcap (by rroom) ?_
      refine rx_push rfl (by rroom) ?_
      refine rx_branch_succ (by decide) ?_
      exact nx
    · have hcap : B256.gtCheck (n + e) p.target.word = 0 := by
        simp only [B256.gtCheck, hgt, ite_false]
      have hnext : excessNext p.target.word e n = 0 := by
        simp only [excessNext, hinh, hgt, ite_false]
      rw [hnext] at next
      have nx := noCarry_run p (x := n) (y := e) hpush0 h5 next
      have e' : G + excessGas (excessFixed p.target.word) sevm d =
          G + 8 + 3 + 2 + 2 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 3 + 3
            + sloadCost sevm (afterSloadA sevm d 0) 1 + 3 + sloadCost sevm d 0 + 2 + 10 + 3 + 2 + 1 := by
        rw [hgas 89 (by simp only [excessFixed, hinh, hgt, ite_false])]
        omega
      rw [e']
      unfold sysExcess sysRead sysOver
      refine rx_dest ?_
      refine rx_calldatasize (by rroom) ?_
      rw [hz]
      refine rx_push rfl (by rroom) ?_
      refine rx_branch_zero ?_
      refine rx_push0 hpush0 (by rroom) ?_
      refine rx_sloadV hacc (by rroom) he ?_
      refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
      refine rx_sloadV hacc (by rroom) hn' ?_
      refine rx_dup2 (by rroom) ?_
      refine rx_push inhibitor_push (by rroom) ?_
      refine rx_eq hflag (by rroom) ?_
      refine rx_push rfl (by rroom) ?_
      refine rx_branchTo_zero ?_
      refine rx_push (w := p.target.word) rfl (by rroom) ?_
      refine rx_dup3 (by rroom) ?_
      refine rx_dup3 (by rroom) ?_
      refine rx_add' rfl (by rroom) ?_
      refine rx_gt hcap (by rroom) ?_
      refine rx_push rfl (by rroom) ?_
      refine rx_branch_zero ?_
      exact nx

end Walks

/-- The builder arm's charge is at most 95 beyond its reads. -/
theorem excessFixed_le (target e n : B256) : excessFixed target e n ≤ 95 := by
  simp only [excessFixed]
  split
  · decide
  · split <;> decide

/-- A builder runtime's shape: the loop's entry and the excess update at certificate indices 2 and 3. -/
def latchShape (p : LatchWords) (under cap post emptied excess : PushWord) : SysShape where
  under := under
  cap := cap
  post := post
  emptied := emptied
  excess := excess
  target := p.target
  len := p.len
  entryIdx := 2
  excessIdx := 3
  excessTree := sysExcess p
  next := excessNext p.target.word
  fixed := excessFixed p.target.word
  fixed_le := excessFixed_le _

end Blanc.Lift.BuilderRequest
