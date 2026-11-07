import Blanc.Lift.RequestSystem.Path

/-!
# The excess arm of the EIP-7002 and EIP-7251 runtimes

These runtimes have no calldata latch. They read slot 0, take the inhibitor as an excess of zero, read
the count, and store `count + excess - target` in words when that sum exceeds the target, else zero. So
unlike the EIP-8282 arm, an inhibitor with a count above the target leaves the count's own excess.
`plainShape` is this arm as a `SysShape`, with no premise on storage.
-/

namespace Blanc.Lift.RequestSystem

open Jaune
open RequestFee (PushWord)

/-- The pushed words and certificate indices of this excess arm. -/
structure PlainWords where
  /-- Destination taken when slot 0 is not the inhibitor. -/
  over : PushWord
  /-- Destination taken when some excess carries over. -/
  carry : PushWord
  /-- Destination of the final stores. -/
  final : PushWord
  /-- Requests per block the excess is measured against. -/
  target : PushWord
  /-- Bytes per returned record. -/
  len : PushWord
  /-- The certificate index of the comparison. -/
  overIdx : Nat
  /-- The certificate index of the final stores. -/
  finalIdx : Nat

section Trees

variable (p : PlainWords)

/-- No excess: drop both words and store zero. -/
def plainNoCarry : SFunc :=
  (.next (.reg .pop) (.next (.reg .pop) (.next (.push [] (by decide))
  (.next (.push (p.final.head :: p.final.tail) p.final.le) (.jump p.finalIdx)))))

/-- Some excess: `count + excess - target`, into the final stores. -/
def plainCarry : SFunc :=
  (.dest (.next (.reg .add) (.next (.push (p.target.head :: p.target.tail) p.target.le)
  (.next (.reg (.swap 0)) (.next (.reg .sub) (sysFinal p.len))))))

/-- Read the count; `count + excess > target`? -/
def plainOver : SFunc :=
  (.dest (.next (.push [0x01] (by decide)) (.next (.reg .sload)
  (.next (.push (p.target.head :: p.target.tail) p.target.le) (.next (.reg (.dup 2))
  (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .gt)
  (.next (.push (p.carry.head :: p.carry.tail) p.carry.le)
  (.branch (plainNoCarry p) (plainCarry p)))))))))))

/-- Read the excess; the inhibitor counts as zero. -/
def plainExcess : SFunc :=
  (.dest (.next (.push [] (by decide)) (.next (.reg .sload) (.next (.reg (.dup 0))
  (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff] (by decide)) (.next (.reg .eq) (.next (.reg .iszero)
  (.next (.push (p.over.head :: p.over.tail) p.over.le)
  (.branchTo (.next (.reg .pop) (.next (.push [] (by decide)) (plainOver p))) p.overIdx)))))))))

end Trees

/-- The excess this arm compares: the inhibitor counts as zero. -/
def plainBase (excess : B256) : B256 := if B256.max = excess then 0 else excess

/-- The excess this arm stores. -/
def plainNext (target excess count : B256) : B256 :=
  if count + plainBase excess > target then (count + plainBase excess) - target else 0

/-- The arm's charge beyond its two reads. -/
def plainFixed (target excess count : B256) : Nat :=
  (if B256.max = excess then 4 else 0) +
    (if count + plainBase excess > target then 73 else 77)

theorem plainFixed_le (target e n : B256) : plainFixed target e n ≤ 95 := by
  simp only [plainFixed]
  split <;> split <;> decide

section Walks

variable (p : PlainWords) {fs : List SFunc} {sevm : Sevm}

/-- The comparison on `[excess, count below]`, either way. -/
theorem over_run {d : Devm} {e c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hfinal : fs[p.finalIdx]? = some (sysFinal p.len))
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm d 1)
        [if d.getStorVal sevm.currentTarget 1 + e > p.target.word then
            (d.getStorVal sevm.currentTarget 1 + e) - p.target.word else 0, c] M G)
      (sysFinal p.len) oc) :
    SFunc.RunExact fs sevm
      (St d [e, c] M (G + (if d.getStorVal sevm.currentTarget 1 + e > p.target.word then 45 else 49)
        + sloadCost sevm d 1))
      (plainOver p) oc := by
  generalize hn : d.getStorVal sevm.currentTarget 1 = n at next ⊢
  by_cases hgt : n + e > p.target.word
  · have hflag : B256.gtCheck (n + e) p.target.word = 1 := by
      simp only [B256.gtCheck, hgt, ite_true]
    simp only [hgt, ite_true] at next ⊢
    have e' : G + 45 + sloadCost sevm d 1 =
        G + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm d 1 + 3 + 1 := by omega
    rw [e']
    unfold plainOver plainCarry
    refine rx_dest ?_
    refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadV hacc (by rroom) hn ?_
    refine rx_push (w := p.target.word) rfl (by rroom) ?_
    refine rx_dup3 (by rroom) ?_
    refine rx_dup3 (by rroom) ?_
    refine rx_add' rfl (by rroom) ?_
    refine rx_gt hflag (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branch_succ (by decide) ?_
    refine rx_dest ?_
    refine rx_add' rfl (by rroom) ?_
    refine rx_push (w := p.target.word) rfl (by rroom) ?_
    refine rx_swap1 ?_
    refine rx_sub' rfl (by rroom) ?_
    exact next
  · have hflag : B256.gtCheck (n + e) p.target.word = 0 := by
      simp only [B256.gtCheck, hgt, ite_false]
    simp only [hgt, ite_false] at next ⊢
    have e' : G + 49 + sloadCost sevm d 1 =
        G + 8 + 3 + 2 + 2 + 2 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm d 1 + 3 + 1 := by omega
    rw [e']
    unfold plainOver plainNoCarry
    refine rx_dest ?_
    refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadV hacc (by rroom) hn ?_
    refine rx_push (w := p.target.word) rfl (by rroom) ?_
    refine rx_dup3 (by rroom) ?_
    refine rx_dup3 (by rroom) ?_
    refine rx_add' rfl (by rroom) ?_
    refine rx_gt hflag (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branch_zero ?_
    refine rx_pop ?_
    refine rx_pop ?_
    refine rx_push0 hpush0 (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    exact rx_jump hfinal next

/-- The excess update, every arm, from any storage. -/
theorem plain_excess_run {d : Devm} {c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hover : fs[p.overIdx]? = some (plainOver p)) (hfinal : fs[p.finalIdx]? = some (sysFinal p.len))
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm (afterSloadA sevm d 0) 1)
        [plainNext p.target.word (d.getStorVal sevm.currentTarget 0)
          (d.getStorVal sevm.currentTarget 1), c] M G) (sysFinal p.len) oc) :
    SFunc.RunExact fs sevm (St d [c] M (G + excessGas (plainFixed p.target.word) sevm d))
      (plainExcess p) oc := by
  generalize he : d.getStorVal sevm.currentTarget 0 = e at next
  generalize hn : d.getStorVal sevm.currentTarget 1 = n at next
  have hn' : (afterSloadA sevm d 0).getStorVal sevm.currentTarget 1 = n := by
    rw [afterSloadA_getStorVal, hn]
  have step := over_run p (d := afterSloadA sevm d 0) (e := plainBase e) (c := c) (M := M) (G := G)
    hacc hpush0 hfinal (by rw [hn']; simpa only [plainNext] using next)
  rw [hn'] at step
  by_cases hinh : B256.max = e
  · have hflag : B256.eqCheck B256.max e = 1 := by simp only [B256.eqCheck, hinh, ite_true]
    have hbase : plainBase e = 0 := by simp only [plainBase, hinh, ite_true]
    rw [hbase] at step
    have e' : G + excessGas (plainFixed p.target.word) sevm d =
        G + (if n + 0 > p.target.word then 45 else 49) + sloadCost sevm (afterSloadA sevm d 0) 1 +
          2 + 2 + 10 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm d 0 + 2 + 1 := by
      simp only [excessGas, plainFixed, he, hn, hbase, hinh, ite_true]
      split <;> omega
    rw [e']
    unfold plainExcess
    refine rx_dest ?_
    refine rx_push0 hpush0 (by rroom) ?_
    refine rx_sloadV hacc (by rroom) he ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_push inhibitor_push (by rroom) ?_
    refine rx_eq hflag (by rroom) ?_
    refine rx_iszero (v := 0) (by decide) (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branchTo_zero ?_
    refine rx_pop ?_
    refine rx_push0 hpush0 (by rroom) ?_
    exact step
  · have hflag : B256.eqCheck B256.max e = 0 := by simp only [B256.eqCheck, hinh, ite_false]
    have hbase : plainBase e = e := by simp only [plainBase, hinh, ite_false]
    rw [hbase] at step
    have e' : G + excessGas (plainFixed p.target.word) sevm d =
        G + (if n + e > p.target.word then 45 else 49) + sloadCost sevm (afterSloadA sevm d 0) 1 +
          10 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm d 0 + 2 + 1 := by
      simp only [excessGas, plainFixed, he, hn, hbase, hinh, ite_false]
      split <;> omega
    rw [e']
    unfold plainExcess
    refine rx_dest ?_
    refine rx_push0 hpush0 (by rroom) ?_
    refine rx_sloadV hacc (by rroom) he ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_push inhibitor_push (by rroom) ?_
    refine rx_eq hflag (by rroom) ?_
    refine rx_iszero (v := 1) (by decide) (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branchTo_succ (by decide) hover ?_
    exact step

end Walks

/-- A plain-arm runtime's shape. -/
def plainShape (p : PlainWords) (under cap post emptied excess : PushWord) (entryIdx excessIdx : Nat) :
    SysShape where
  under := under
  cap := cap
  post := post
  emptied := emptied
  excess := excess
  target := p.target
  len := p.len
  entryIdx := entryIdx
  excessIdx := excessIdx
  excessTree := plainExcess p
  next := plainNext p.target.word
  fixed := plainFixed p.target.word
  fixed_le := plainFixed_le _

end Blanc.Lift.RequestSystem
