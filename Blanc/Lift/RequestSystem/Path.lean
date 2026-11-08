import Blanc.Lift.RequestSystem.Dispatch
import Blanc.Lift.RequestSystem.Stores
import Blanc.Lift.SystemCallAmsterdam
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.CreationOps
import Blanc.MemoryStageGas

/-!
# A request contract's system path, under Amsterdam

All four request contracts of Amsterdam (EIP-7002, EIP-7251, EIP-8282's deposit and exit) share one
system path: read tail and head, cap the count, drain the records, move the pointers, update the excess
from slots 0 and 1, clear the count, and return. The runtimes differ by pushed words, certificate
indices, the record body and its memory writes, and the excess update's arm (`SysShape.excessTree`),
so a generated tree is an instance of `sysSetup` by `rfl`.

`SysPath` packages a runtime with its loop body's walk and its excess arm's walk. `SysPath.frame_run` is
its whole frame, from any storage and with no storage premise, as an exact run from
`St b [] .empty (G + frameCost)` to an explicit post frame. Nothing here says which storage is
reachable. The rule record is read, not its prices: a repricing moves `frameCost`, not this structure.
-/

namespace Blanc.Lift.RequestSystem

open Jaune
open RequestFee (PushWord)

/-- Amsterdam's state-gas record. -/
local notation "A" => amsterdamStateGasRules

/-! ## The trees -/

/-- What a request contract's system path differs by, beyond its record body. -/
structure SysShape where
  /-- Destination taken when the queue holds fewer records than the cap. -/
  under : PushWord
  /-- Records drained per call at most. -/
  cap : PushWord
  /-- Destination leaving the drain loop. -/
  post : PushWord
  /-- Destination taken when the drain emptied the queue. -/
  emptied : PushWord
  /-- Destination of the excess update. -/
  excess : PushWord
  /-- Requests per block the excess is measured against. -/
  target : PushWord
  /-- Bytes per returned record. -/
  len : PushWord
  /-- The certificate index of the loop's entry. -/
  entryIdx : Nat
  /-- The certificate index of the excess update. -/
  excessIdx : Nat
  /-- The excess update's tree. -/
  excessTree : SFunc
  /-- The excess stored, from slots 0 and 1. -/
  next : B256 → B256 → B256
  /-- The excess update's charge beyond its two reads, from slots 0 and 1. -/
  fixed : B256 → B256 → Nat
  fixed_le : ∀ e n, fixed e n ≤ 95

/-- `t_final`: store the excess, clear the count, return the records. -/
def sysFinal (len : PushWord) : SFunc :=
  (.dest (.next (.push [] (by decide)) (.next (.reg .sstore) (.next (.push [] (by decide))
  (.next (.push [0x01] (by decide)) (.next (.reg .sstore)
  (.next (.push (len.head :: len.tail) len.le) (.next (.reg .mul)
  (.next (.push [] (by decide)) (.last .return_))))))))))

section Trees

variable (p : SysShape)

/-- The queue emptied: clear both pointers. -/
def sysEmptied : SFunc :=
  (.dest (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [] (by decide))
  (.next (.push [0x02] (by decide)) (.next (.reg .sstore) (.next (.push [] (by decide))
  (.next (.push [0x03] (by decide)) (.next (.reg .sstore) p.excessTree)))))))))

/-- Records remain: advance the head. -/
def sysAdvance : SFunc :=
  (.next (.reg (.swap 0)) (.next (.push [0x02] (by decide)) (.next (.reg .sstore)
  (.next (.push (p.excess.head :: p.excess.tail) p.excess.le) (.jump p.excessIdx)))))

/-- After the loop: did the drain reach the tail? -/
def sysBook : SFunc :=
  (.dest (.next (.reg (.swap 1)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.swap 2))
  (.next (.reg .eq) (.next (.push (p.emptied.head :: p.emptied.tail) p.emptied.le)
  (.branch (sysAdvance p) (sysEmptied p)))))))))

/-- The loop header. -/
def sysHeader (body : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 1)) (.next (.reg (.dup 1)) (.next (.reg .eq)
  (.next (.push (p.post.head :: p.post.tail) p.post.le) (.branch body (sysBook p)))))))

/-- Into the loop, index 0. -/
def sysEntry (body : SFunc) : SFunc :=
  (.dest (.next (.push [] (by decide)) (sysHeader p body)))

/-- The system arm: read tail and head, cap the count. -/
def sysSetup (body : SFunc) : SFunc :=
  (.dest (.next (.push [0x03] (by decide)) (.next (.reg .sload) (.next (.push [0x02] (by decide))
  (.next (.reg .sload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub)
  (.next (.reg (.dup 0)) (.next (.push (p.cap.head :: p.cap.tail) p.cap.le) (.next (.reg .gt)
  (.next (.push (p.under.head :: p.under.tail) p.under.le)
  (.branchTo (.next (.reg .pop) (.next (.push (p.cap.head :: p.cap.tail) p.cap.le)
    (sysEntry p body))) p.entryIdx)))))))))))))

end Trees

/-- The base after the final stores, on a fork's stores. -/
def finalBaseOn {sevm : Sevm} (w : SysStores sevm) (d : Devm) (e : B256) : Devm :=
  w.afterWrite (w.afterWrite d 0 e) 1 0

/-- The charge of `sysFinal` on a fork's stores, without its `RETURN`'s expansion. -/
def finalGasOn {sevm : Sevm} (w : SysStores sevm) (d : Devm) (e : B256) : Nat :=
  2 + 5 + 3 + w.writeCost (w.afterWrite d 0 e) 1 0 + 3 + 2 + w.writeCost d 0 e + 2 + 1

/-- The base after the final stores. -/
def finalBase (sevm : Sevm) (d : Devm) (e : B256) : Devm := finalBaseOn (amsterdamStores sevm) d e

/-- The charge of `sysFinal`, without its `RETURN`'s expansion. -/
def finalGas (sevm : Sevm) (d : Devm) (e : B256) : Nat := finalGasOn (amsterdamStores sevm) d e

/-- The selected charge of the excess update on empty calldata. -/
def excessGas (fixed : B256 → B256 → Nat) (sevm : Sevm) (d : Devm) : Nat :=
  fixed (d.getStorVal sevm.currentTarget 0) (d.getStorVal sevm.currentTarget 1) +
    sloadCost sevm d 0 + sloadCost sevm (afterSloadA sevm d 0) 1

section Walks

variable {fs : List SFunc} {sevm : Sevm}

/-- `t_final` on a fork's stores. -/
theorem final_runOn (len : PushWord) (w : SysStores sevm) (runs : w.Runs) (laws : w.Laws) {d : Devm}
    {e c : B256} {ks : List B256} {M : Mem} {G : Nat}
    (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hG : gCallStipend < G)
    (r : w.Ready d ((0 : B256) :: (1 : B256) :: ks)) (h01 : (0 : B256) ∉ (1 : B256) :: ks) :
    SFunc.RunExact fs sevm
      (St d [e, c] M (G + chargedRetExt M 0 (len.word * c) + finalGasOn w d e))
      (sysFinal len) (.halted (chargedRetPost (finalBaseOn w d e) [] M G 0 (len.word * c))) := by
  have r1 := laws.write r h01 e
  have hgas : G + chargedRetExt M 0 (len.word * c) + finalGasOn w d e =
      G + chargedRetExt M 0 (len.word * c) + 2 + 5 + 3 +
        w.writeCost (w.afterWrite d 0 e) 1 0 + 3 + 2 +
        w.writeCost d 0 e + 2 + 1 := by
    simp only [finalGasOn]
    omega
  rw [hgas]
  unfold sysFinal
  refine rx_dest ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine runs r hstatic (by omega) ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
  refine runs r1 hstatic (by omega) ?_
  refine rx_push (w := len.word) rfl (by rroom) ?_
  refine rx_mul rfl (by rroom) ?_
  refine rx_push0 hpush0 (by rroom) ?_
  exact rx_return_charged

theorem final_run (len : PushWord) {d : Devm} {e c : B256} {ks : List B256} {M : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = some A) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hG : gCallStipend < G)
    (r : Ready sevm d ((0 : B256) :: (1 : B256) :: ks)) (h01 : (0 : B256) ∉ (1 : B256) :: ks) :
    SFunc.RunExact fs sevm
      (St d [e, c] M (G + chargedRetExt M 0 (len.word * c) + finalGas sevm d e))
      (sysFinal len) (.halted (chargedRetPost (finalBase sevm d e) [] M G 0 (len.word * c))) :=
  final_runOn len (amsterdamStores sevm) (amsterdamStores_runs hsg) (amsterdamStores_laws sevm) hpush0
    hstatic hG r h01

/-- The base after the pointer stores, on a fork's stores. -/
def bookBaseOn (w : SysStores sevm) (q : Devm) (h c t : B256) : Devm :=
  if h + c = t then w.afterWrite (w.afterWrite q 2 0) 3 0
  else w.afterWrite q 2 (h + c)

/-- The charge of the bookkeeping, on a fork's stores. -/
def bookGasOn (w : SysStores sevm) (q : Devm) (h c t : B256) : Nat :=
  if h + c = t then
    45 + w.writeCost (w.afterWrite q 2 0) 3 0 + w.writeCost q 2 0
  else 46 + w.writeCost q 2 (h + c)

/-- The base after the pointer stores. -/
def bookBase (sevm : Sevm) (q : Devm) (h c t : B256) : Devm := bookBaseOn (amsterdamStores sevm) q h c t

/-- The charge of the bookkeeping. -/
def bookGas (sevm : Sevm) (q : Devm) (h c t : B256) : Nat := bookGasOn (amsterdamStores sevm) q h c t

/-- The bookkeeping, either way, on a fork's stores. -/
theorem book_runOn (p : SysShape) (w : SysStores sevm) (runs : w.Runs) (laws : w.Laws) {q : Devm}
    {c h t : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hG : gCallStipend < G)
    (r : w.Ready q [2, 3, 0, 1]) (h3 : fs[p.excessIdx]? = some p.excessTree)
    (next : SFunc.RunExact fs sevm (St (bookBaseOn w q h c t) [c] M G) p.excessTree oc) :
    SFunc.RunExact fs sevm (St q [c, c, h, t] M (G + bookGasOn w q h c t)) (sysBook p) oc := by
  by_cases hemptied : h + c = t
  · have r1 := laws.write r (by decide) (0 : B256)
    have hflag : B256.eqCheck t (h + c) = 1 := by
      rw [hemptied]
      simp only [B256.eqCheck, ite_true]
    simp only [bookBaseOn, hemptied, ite_true] at next
    have e' : G + bookGasOn w q h c t =
        G + w.writeCost (w.afterWrite q 2 0) 3 0 + 3 + 2 + w.writeCost q 2 0
          + 3 + 2 + 2 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 := by
      simp only [bookGasOn, hemptied, ite_true]
      omega
    rw [e']
    unfold sysBook sysEmptied
    refine rx_dest ?_
    refine rx_swap2 ?_
    refine rx_add' rfl (by rroom) ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_swap3 ?_
    refine rx_eq hflag (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branch_succ (by decide) ?_
    refine rx_dest ?_
    refine rx_swap1 ?_
    refine rx_pop ?_
    refine rx_push0 hpush0 (by rroom) ?_
    refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
    refine runs r hstatic (by omega) ?_
    refine rx_push0 hpush0 (by rroom) ?_
    refine rx_push (w := (3 : B256)) (by decide) (by rroom) ?_
    refine runs r1 hstatic (by omega) ?_
    exact next
  · have hflag : B256.eqCheck t (h + c) = 0 := by
      have hne : t ≠ h + c := fun e => hemptied e.symm
      simp only [B256.eqCheck, hne, ite_false]
    simp only [bookBaseOn, hemptied, ite_false] at next
    have e' : G + bookGasOn w q h c t =
        G + 8 + 3 + w.writeCost q 2 (h + c) + 3 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 := by
      simp only [bookGasOn, hemptied, ite_false]
      omega
    rw [e']
    unfold sysBook sysAdvance
    refine rx_dest ?_
    refine rx_swap2 ?_
    refine rx_add' rfl (by rroom) ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_swap3 ?_
    refine rx_eq hflag (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branch_zero ?_
    refine rx_swap1 ?_
    refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
    refine runs (laws.skip r) hstatic (by omega) ?_
    refine rx_push rfl (by rroom) ?_
    exact rx_jump h3 next

/-- The bookkeeping, either way. -/
theorem book_run (p : SysShape) {q : Devm} {c h t : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hsg : sevm.benvStat.rules.stateGas = some A) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hG : gCallStipend < G)
    (r : Ready sevm q [2, 3, 0, 1]) (h3 : fs[p.excessIdx]? = some p.excessTree)
    (next : SFunc.RunExact fs sevm (St (bookBase sevm q h c t) [c] M G) p.excessTree oc) :
    SFunc.RunExact fs sevm (St q [c, c, h, t] M (G + bookGas sevm q h c t)) (sysBook p) oc :=
  book_runOn p (amsterdamStores sevm) (amsterdamStores_runs hsg) (amsterdamStores_laws sevm) hpush0
    hstatic hG r h3 next

theorem ready_bookOn {w : SysStores sevm} (laws : w.Laws) {q : Devm} (r : w.Ready q [2, 3, 0, 1])
    (h c t : B256) : w.Ready (bookBaseOn w q h c t) [0, 1] := by
  unfold bookBaseOn
  split
  · exact laws.write (laws.write r (by decide) _) (by decide) _
  · exact laws.write (laws.skip r) (by decide) _

theorem ready_book {sevm : Sevm} {q : Devm} (r : Ready sevm q [2, 3, 0, 1]) (h c t : B256) :
    Ready sevm (bookBase sevm q h c t) [0, 1] :=
  ready_bookOn (amsterdamStores_laws sevm) r h c t

/-- `JUMPDEST DUP2 DUP2 EQ PUSH JUMPI`, either way. -/
theorem header_run (p : SysShape) {body : SFunc} {d : Devm} {M : Mem} {gas : Nat} {i c h t : B256} {oc : Outcome}
    (next : SFunc.RunExact fs sevm (St d [i, c, h, t] M gas) (if i = c then sysBook p else body) oc) :
    SFunc.RunExact fs sevm (St d [i, c, h, t] M (gas + 23)) (sysHeader p body) oc := by
  have e : gas + 23 = gas + 10 + 3 + 3 + 3 + 3 + 1 := by omega
  rw [e]
  unfold sysHeader
  refine rx_dest ?_
  refine rx_dup2 (by rroom) ?_
  refine rx_dup2 (by rroom) ?_
  refine rx_eq rfl (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  by_cases same : i = c
  · simp only [B256.eqCheck, ite_eq_left same] at next ⊢
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) next
  · simp only [B256.eqCheck, ite_eq_right same] at next ⊢
    exact rx_branch_zero next

/-- The base after tail and head are read. -/
def setupBase (sevm : Sevm) (b : Devm) : Devm := afterSloadA sevm (afterSloadA sevm b 3) 2

/-- Records to drain: the difference of the pointers, in words, up to the cap. -/
def drainCount (cap head tail : B256) : B256 :=
  if cap > tail - head then tail - head else cap

/-- The charge of the setup. -/
def setupGas (cap : B256) (sevm : Sevm) (b : Devm) : Nat :=
  (if cap > b.getStorVal sevm.currentTarget 3 - b.getStorVal sevm.currentTarget 2 then 41 else 46) +
    sloadCost sevm b 3 + sloadCost sevm (afterSloadA sevm b 3) 2

/-- The system arm's setup, into the loop header. -/
theorem setup_run (p : SysShape) {body : SFunc} {b : Devm} {G : Nat} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (h2 : fs[p.entryIdx]? = some (sysEntry p body))
    (next : SFunc.RunExact fs sevm
      (St (setupBase sevm b)
        [0, drainCount p.cap.word (b.getStorVal sevm.currentTarget 2)
            (b.getStorVal sevm.currentTarget 3),
          b.getStorVal sevm.currentTarget 2, b.getStorVal sevm.currentTarget 3] .empty G)
      (sysHeader p body) oc) :
    SFunc.RunExact fs sevm (St b [] .empty (G + setupGas p.cap.word sevm b)) (sysSetup p body) oc := by
  generalize ht : b.getStorVal sevm.currentTarget 3 = t at next
  generalize hh : b.getStorVal sevm.currentTarget 2 = h at next
  have hh' : (afterSloadA sevm b 3).getStorVal sevm.currentTarget 2 = h := by
    rw [afterSloadA_getStorVal, hh]
  by_cases hunder : p.cap.word > t - h
  · have hflag : B256.gtCheck p.cap.word (t - h) ≠ 0 := by
      simp only [B256.gtCheck, hunder, ite_true]
      decide
    simp only [drainCount, hunder, ite_true] at next
    have e' : G + setupGas p.cap.word sevm b =
        G + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSloadA sevm b 3) 2 + 3
          + sloadCost sevm b 3 + 3 + 1 := by
      simp only [setupGas, ht, hh, hunder, ite_true]
      omega
    rw [e']
    unfold sysSetup
    refine rx_dest ?_
    refine rx_push (w := (3 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadV hacc (by rroom) ht ?_
    refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadV hacc (by rroom) hh' ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_dup3 (by rroom) ?_
    refine rx_sub' rfl (by rroom) ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_push (w := p.cap.word) rfl (by rroom) ?_
    refine rx_gt rfl (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branchTo_succ hflag h2 ?_
    unfold sysEntry
    refine rx_dest ?_
    refine rx_push0 hpush0 (by rroom) ?_
    exact next
  · have hflag : B256.gtCheck p.cap.word (t - h) = 0 := by
      simp only [B256.gtCheck, hunder, ite_false]
    simp only [drainCount, hunder, ite_false] at next
    have e' : G + setupGas p.cap.word sevm b =
        G + 2 + 1 + 3 + 2 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (afterSloadA sevm b 3) 2
          + 3 + sloadCost sevm b 3 + 3 + 1 := by
      simp only [setupGas, ht, hh, hunder, ite_false]
      omega
    rw [e']
    unfold sysSetup sysEntry
    refine rx_dest ?_
    refine rx_push (w := (3 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadV hacc (by rroom) ht ?_
    refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadV hacc (by rroom) hh' ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_dup3 (by rroom) ?_
    refine rx_sub' rfl (by rroom) ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_push (w := p.cap.word) rfl (by rroom) ?_
    refine rx_gt hflag (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branchTo_zero ?_
    refine rx_pop ?_
    refine rx_push (w := p.cap.word) rfl (by rroom) ?_
    refine rx_dest ?_
    refine rx_push0 hpush0 (by rroom) ?_
    exact next

end Walks

/-! ## A runtime's system path -/

/-- What the loop leaves. -/
structure DrainPost where
  base : Devm
  memory : Mem
  charges : Nat

/-- A request runtime with its system path: the shape, the record body, and the walks of that body and of the excess arm. -/
structure SysPath where
  /-- The runtime bytes. -/
  code : ByteArray
  /-- Its certificate. -/
  cert : Cert
  check : Cert.check code cert = true
  jumps : Cert.jumpsOk code cert = true
  noExec : ProgNoExec cert.prog
  /-- The pushed words. -/
  shape : SysShape
  /-- Destination of the system arm. -/
  systemDest : PushWord
  /-- The user arm of caller dispatch, unread here. -/
  user : SFunc
  /-- The record body. -/
  body : SFunc
  /-- Maximum records per call, as a number. -/
  capN : Nat
  cap_word : shape.cap.word.toNat = capN
  /-- Slots read per record. -/
  slots : Nat
  /-- Memory writes per record. -/
  writes : Nat
  /-- A body's fixed charge. -/
  bodyFixed : Nat
  /-- The storage keys a record's body reads, in order, from head and index. -/
  keys : B256 → B256 → List B256
  keys_length : ∀ h i, (keys h i).length = slots
  /-- A record's memory writes, in order, from the storage read. -/
  stage : (B256 → B256) → B256 → B256 → MemoryStage
  stage_length : ∀ rd h i, (stage rd h i).length = writes
  root : cert.prog[0]? = some (dispatchTree systemDest user (sysSetup shape body))
  entry : cert.prog[shape.entryIdx]? = some (sysEntry shape body)
  excessEntry : cert.prog[shape.excessIdx]? = some shape.excessTree
  /-- The excess update on empty calldata, every arm. -/
  excess_run : ∀ {sevm : Sevm} {d : Devm} {c : B256} {M : Mem} {G : Nat} {oc : Outcome},
    sevm.benvStat.rules.access = .eip2929 → sevm.benvStat.rules.op.push0 = true → sevm.data = [] →
    SFunc.RunExact cert.prog sevm
      (St (afterSloadA sevm (afterSloadA sevm d 0) 1)
        [shape.next (d.getStorVal sevm.currentTarget 0) (d.getStorVal sevm.currentTarget 1), c] M G)
      (sysFinal shape.len) oc →
    SFunc.RunExact cert.prog sevm (St d [c] M (G + excessGas shape.fixed sevm d)) shape.excessTree oc
  /-- One record's body, ending on the loop's back-edge. -/
  body_run : ∀ {sevm : Sevm} {b : Devm} {M : Mem} {gas : Nat} {i c h t : B256} {oc : Outcome},
    sevm.benvStat.rules.access = .eip2929 → sevm.benvStat.rules.op.shifts = true →
    SFunc.RunExact cert.prog sevm
      (St (readsBase sevm b (keys h i)) [(1 : B256) + i, c, h, t]
        ((stage (b.getStorVal sevm.currentTarget) h i).applyMemory M) gas)
      (sysHeader shape body) oc →
    SFunc.RunExact cert.prog sevm
      (St b [i, c, h, t] M (gas + bodyFixed + readsGas sevm b (keys h i) +
        MemoryStage.selectedGas (stage (b.getStorVal sevm.currentTarget) h i) M)) body oc

namespace SysPath

variable (k : SysPath)

/-- The actual sequence of body effects: base, memory, and every charge of the loop but its final
header. -/
def fold (sevm : Sevm) (h : B256) (index : Nat) : Nat → Devm → Mem → DrainPost
  | 0, b, M => ⟨b, M, 0⟩
  | n + 1, b, M =>
    let i := index.toB256
    let rd := b.getStorVal sevm.currentTarget
    let post := fold sevm h (index + 1) n (readsBase sevm b (k.keys h i))
      ((k.stage rd h i).applyMemory M)
    ⟨post.base, post.memory,
      23 + k.bodyFixed + readsGas sevm b (k.keys h i) + MemoryStage.selectedGas (k.stage rd h i) M +
        post.charges⟩

theorem fold_readyOn {sevm : Sevm} {w : SysStores sevm} (laws : w.Laws) {h : B256} {ks : List B256}
    (index n : Nat) {b : Devm} {M : Mem}
    (r : w.Ready b ks) : w.Ready (k.fold sevm h index n b M).base ks := by
  induction n generalizing index b M with
  | zero => exact r
  | succ n ih => exact ih (index + 1) (laws.reads r _)

theorem fold_ready {sevm : Sevm} {h : B256} {ks : List B256} (index n : Nat) {b : Devm} {M : Mem}
    (r : Ready sevm b ks) : Ready sevm (k.fold sevm h index n b M).base ks :=
  k.fold_readyOn (amsterdamStores_laws sevm) index n r

theorem fold_state {sevm : Sevm} {h : B256} (index n : Nat) (b : Devm) (M : Mem) :
    (k.fold sevm h index n b M).base.state = b.state := by
  induction n generalizing index b M with
  | zero => rfl
  | succ n ih =>
    show (k.fold sevm h (index + 1) n _ _).base.state = _
    rw [ih, readsBase_state]

/-- **The bounded loop**, by induction on the remaining count, from any storage and memory, ending in
the bookkeeping. -/
theorem loop_run {sevm : Sevm} {h t c : B256}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hsh : sevm.benvStat.rules.op.shifts = true)
    (remaining : Nat) {index : Nat} {b : Devm} {M : Mem} {gas : Nat} {oc : Outcome}
    (bound : index + remaining = c.toNat)
    (next : SFunc.RunExact k.cert.prog sevm
      (St (k.fold sevm h index remaining b M).base [c, c, h, t]
        (k.fold sevm h index remaining b M).memory gas) (sysBook k.shape) oc) :
    SFunc.RunExact k.cert.prog sevm (St b [index.toB256, c, h, t] M
      (gas + (k.fold sevm h index remaining b M).charges + 23)) (sysHeader k.shape k.body) oc := by
  induction remaining generalizing index b M with
  | zero =>
    have same : index.toB256 = c := by
      rw [show index = c.toNat by omega, toB256_toNat]
    simp only [fold] at next ⊢
    apply header_run
    rw [ite_eq_left same, same]
    exact next
  | succ remaining ih =>
    have different : index.toB256 ≠ c := by
      intro eq
      have eqNat := congrArg B256.toNat eq
      rw [B256.toNat_toB256_of_lt (by have := B256.toNat_lt c; omega)] at eqNat
      omega
    simp only [fold] at next ⊢
    have suffix := ih (index := index + 1) (by omega) next
    rw [← one_add_toB256 (by have := B256.toNat_lt c; omega)] at suffix
    rw [show Bytes.toB256 [0x01] = (1 : B256) by decide] at suffix
    have body := k.body_run hacc hsh suffix
    have header := header_run k.shape (i := index.toB256) (c := c) (h := h) (t := t) (d := b) (M := M)
      (fs := k.cert.prog) (sevm := sevm) (body := k.body)
      (by simpa only [ite_eq_right different] using body)
    have gasEq : ∀ X Y Z W : Nat, gas + (23 + X + Y + Z + W) + 23 =
        gas + W + 23 + X + Y + Z + 23 := fun _ _ _ _ => by omega
    rw [gasEq]
    exact header

section Frame

variable (sevm : Sevm) (b : Devm)

/-- Storage as this frame reads it. -/
abbrev rd : B256 → B256 := b.getStorVal sevm.currentTarget

/-- The records this frame drains. -/
def count : B256 := drainCount k.shape.cap.word (rd sevm b 2) (rd sevm b 3)

/-- The frame's loop. -/
def drain : DrainPost :=
  k.fold sevm (rd sevm b 2) 0 (k.count sevm b).toNat (setupBase sevm b) .empty

/-- The bytes `RETURN` reads its window over. -/
def outLen : B256 := k.shape.len.word * k.count sevm b

variable {sevm} (w : SysStores sevm)

/-- After the pointer stores, on a fork's stores. -/
def bookedOn : Devm :=
  bookBaseOn w (k.drain sevm b).base (rd sevm b 2) (k.count sevm b) (rd sevm b 3)

/-- After excess and count are read, on a fork's stores. -/
def excessReadOn : Devm := afterSloadA sevm (afterSloadA sevm (k.bookedOn b w) 0) 1

/-- The excess this frame stores, on a fork's stores. -/
def excessStoredOn : B256 :=
  k.shape.next ((k.bookedOn b w).getStorVal sevm.currentTarget 0)
    ((k.bookedOn b w).getStorVal sevm.currentTarget 1)

/-- The frame's exact charge, on a fork's stores. -/
def frameCostOn : Nat :=
  chargedRetExt (k.drain sevm b).memory 0 (k.outLen sevm b) +
    finalGasOn w (k.excessReadOn b w) (k.excessStoredOn b w) +
    excessGas k.shape.fixed sevm (k.bookedOn b w) +
    bookGasOn w (k.drain sevm b).base (rd sevm b 2) (k.count sevm b) (rd sevm b 3) +
    (k.drain sevm b).charges + 23 + setupGas k.shape.cap.word sevm b + dispatchGas

/-- The frame's post state at `G` of remaining gas, on a fork's stores. -/
def framePostOn (G : Nat) : Devm :=
  chargedRetPost (finalBaseOn w (k.excessReadOn b w) (k.excessStoredOn b w)) [] (k.drain sevm b).memory
    G 0 (k.outLen sevm b)

variable (sevm)

/-- After the pointer stores. -/
def booked : Devm := k.bookedOn b (amsterdamStores sevm)

/-- After excess and count are read. -/
def excessRead : Devm := k.excessReadOn b (amsterdamStores sevm)

/-- The excess this frame stores. -/
def excessStored : B256 := k.excessStoredOn b (amsterdamStores sevm)

/-- The frame's exact charge. -/
def frameCost : Nat := k.frameCostOn b (amsterdamStores sevm)

/-- The frame's post state at `G` of remaining gas. -/
def framePost (G : Nat) : Devm := k.framePostOn b (amsterdamStores sevm) G

variable {sevm b w}

/-- The frame up to the excess update, on any calldata, on a fork's stores. -/
theorem frame_prefixOn (runs : w.Runs) (laws : w.Laws) (hacc : sevm.benvStat.rules.access = .eip2929)
    (hpush0 : sevm.benvStat.rules.op.push0 = true) (hsh : sevm.benvStat.rules.op.shifts = true)
    (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress) (r : w.Ready b [2, 3, 0, 1]) {G : Nat}
    (hG : gCallStipend < G) {oc : Outcome}
    (next : SFunc.RunExact k.cert.prog sevm
      (St (k.bookedOn b w) [k.count sevm b] (k.drain sevm b).memory G) k.shape.excessTree oc) :
    SFunc.RunExact k.cert.prog sevm
      (St b [] .empty (G + bookGasOn w (k.drain sevm b).base (rd sevm b 2) (k.count sevm b)
          (rd sevm b 3) + (k.drain sevm b).charges + 23 + setupGas k.shape.cap.word sevm b +
        dispatchGas))
      (dispatchTree k.systemDest k.user (sysSetup k.shape k.body)) oc := by
  have rSetup : w.Ready (setupBase sevm b) [2, 3, 0, 1] := laws.read (laws.read r 3) 2
  have rDrain := k.fold_readyOn laws (h := rd sevm b 2) 0 (k.count sevm b).toNat (M := .empty) rSetup
  have s3 := book_runOn k.shape w runs laws (q := (k.drain sevm b).base) (h := rd sevm b 2)
    (t := rd sevm b 3) hpush0 hstatic hG rDrain k.excessEntry next
  have s4 := k.loop_run (h := rd sevm b 2) (t := rd sevm b 3) (c := k.count sevm b)
    hacc hsh (k.count sevm b).toNat (index := 0) (b := setupBase sevm b) (M := .empty) (by omega) s3
  have s5 := setup_run k.shape (b := b) (body := k.body) hacc hpush0 k.entry s4
  exact dispatch_exact (dest := k.systemDest) (user := k.user)
    (system := sysSetup k.shape k.body) (fs := k.cert.prog) (sevm := sevm) (b := b) (M := .empty)
    (by rw [dispatchArm, ite_eq_left hcaller]; exact s5)

/-- **The whole system frame**, from any storage, on empty calldata, on a fork's stores. -/
theorem frame_runOn (runs : w.Runs) (laws : w.Laws) (hacc : sevm.benvStat.rules.access = .eip2929)
    (hpush0 : sevm.benvStat.rules.op.push0 = true) (hsh : sevm.benvStat.rules.op.shifts = true)
    (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (r : w.Ready b [2, 3, 0, 1]) {G : Nat} (hG : gCallStipend < G) :
    SFunc.RunExact k.cert.prog sevm (St b [] .empty (G + k.frameCostOn b w))
      (dispatchTree k.systemDest k.user (sysSetup k.shape k.body)) (.halted (k.framePostOn b w G)) := by
  have rSetup : w.Ready (setupBase sevm b) [2, 3, 0, 1] := laws.read (laws.read r 3) 2
  have rDrain := k.fold_readyOn laws (h := rd sevm b 2) 0 (k.count sevm b).toNat (M := .empty) rSetup
  have rBooked := ready_bookOn laws rDrain (rd sevm b 2) (k.count sevm b) (rd sevm b 3)
  have rRead : w.Ready (k.excessReadOn b w) [0, 1] := laws.read (laws.read rBooked 0) 1
  have s1 := final_runOn k.shape.len w runs laws (fs := k.cert.prog) (d := k.excessReadOn b w)
    (e := k.excessStoredOn b w) (c := k.count sevm b) (M := (k.drain sevm b).memory) hpush0
    hstatic hG rRead (by decide)
  have s2 := k.excess_run (d := k.bookedOn b w) (c := k.count sevm b) hacc hpush0 hdata s1
  have s3 := k.frame_prefixOn runs laws hacc hpush0 hsh hstatic hcaller r (by omega) s2
  have e : G + k.frameCostOn b w =
      G + chargedRetExt (k.drain sevm b).memory 0 (k.outLen sevm b) +
        finalGasOn w (k.excessReadOn b w) (k.excessStoredOn b w) +
        excessGas k.shape.fixed sevm (k.bookedOn b w) +
        bookGasOn w (k.drain sevm b).base (rd sevm b 2) (k.count sevm b) (rd sevm b 3) +
        (k.drain sevm b).charges + 23 + setupGas k.shape.cap.word sevm b + dispatchGas := by
    simp only [frameCostOn]
    omega
  rw [e]
  exact s3

/-- The frame up to the excess update, on any calldata. -/
theorem frame_prefix (hfork : sevm.benvStat.fork = .amsterdam) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress) (r : Ready sevm b [2, 3, 0, 1]) {G : Nat}
    (hG : gCallStipend < G) {oc : Outcome}
    (next : SFunc.RunExact k.cert.prog sevm
      (St (k.booked sevm b) [k.count sevm b] (k.drain sevm b).memory G) k.shape.excessTree oc) :
    SFunc.RunExact k.cert.prog sevm
      (St b [] .empty (G + bookGas sevm (k.drain sevm b).base (rd sevm b 2) (k.count sevm b)
          (rd sevm b 3) + (k.drain sevm b).charges + 23 + setupGas k.shape.cap.word sevm b +
        dispatchGas))
      (dispatchTree k.systemDest k.user (sysSetup k.shape k.body)) oc :=
  k.frame_prefixOn (amsterdamStores_runs (amsterdam_stateGas (s := sevm.benvStat) hfork))
    (amsterdamStores_laws sevm) (amsterdam_access (s := sevm.benvStat) hfork)
    (amsterdam_push0 (s := sevm.benvStat) hfork) (amsterdam_shifts (s := sevm.benvStat) hfork)
    hstatic hcaller r hG next

/-- **The whole system frame**, from any storage, on empty calldata. -/
theorem frame_run (hfork : sevm.benvStat.fork = .amsterdam) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (r : Ready sevm b [2, 3, 0, 1]) {G : Nat} (hG : gCallStipend < G) :
    SFunc.RunExact k.cert.prog sevm (St b [] .empty (G + k.frameCost sevm b))
      (dispatchTree k.systemDest k.user (sysSetup k.shape k.body)) (.halted (k.framePost sevm b G)) :=
  k.frame_runOn (amsterdamStores_runs (amsterdam_stateGas (s := sevm.benvStat) hfork))
    (amsterdamStores_laws sevm) (amsterdam_access (s := sevm.benvStat) hfork)
    (amsterdam_push0 (s := sevm.benvStat) hfork) (amsterdam_shifts (s := sevm.benvStat) hfork)
    hstatic hcaller hdata r hG

end Frame

end SysPath

end Blanc.Lift.RequestSystem
