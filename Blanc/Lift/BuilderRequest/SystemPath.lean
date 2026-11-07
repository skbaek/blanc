import Blanc.Lift.BuilderRequest.FeePath
import Blanc.Lift.SystemCallAmsterdam
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.CreationOps
import Blanc.MemoryStageGas
import Blanc.StorageAccessGas

/-!
# The EIP-8282 builder contracts' system path, under Amsterdam

Both runtimes share one system path: read tail and head, cap the count, drain the records, move the
pointers, fold the count into the excess, clear the count, and return. Only the pushed words, the
record body and its memory writes differ, so a generated tree is an instance of `sysSetup` by `rfl`.

`SysPath` packages a runtime with its loop body's walk. `SysPath.frame_run` is its whole frame, from any
storage and with no storage premise, as an exact run from `St b [] .empty (G + frameCost)` to an
explicit post frame. Nothing here says which storage is reachable. The rule record is read, not
its prices: a repricing moves `frameCost`, not this structure.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestFee (PushWord)

/-- Amsterdam's state-gas record. -/
local notation "A" => amsterdamStateGasRules

/-! ## The trees -/

/-- The pushed words a builder contract's system path differs by. -/
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

variable (p : SysShape)

/-- `t_final`: store the excess, clear the count, return the records. -/
def sysFinal : SFunc :=
  (.dest (.next (.push [] (by decide)) (.next (.reg .sstore) (.next (.push [] (by decide))
  (.next (.push [0x01] (by decide)) (.next (.reg .sstore)
  (.next (.push (p.len.head :: p.len.tail) p.len.le) (.next (.reg .mul)
  (.next (.push [] (by decide)) (.last .return_))))))))))

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
    0xff, 0xff, 0xff] (by decide)) (sysFinal p)))

/-- The excess update's entry: branch on the calldata. -/
def sysExcess : SFunc :=
  (.dest (.next (.reg .calldatasize) (.next (.push (p.latch.head :: p.latch.tail) p.latch.le)
  (.branch (sysRead p) (sysLatch p)))))

/-- The queue emptied: clear both pointers. -/
def sysEmptied : SFunc :=
  (.dest (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [] (by decide))
  (.next (.push [0x02] (by decide)) (.next (.reg .sstore) (.next (.push [] (by decide))
  (.next (.push [0x03] (by decide)) (.next (.reg .sstore) (sysExcess p))))))))))

/-- Records remain: advance the head. -/
def sysAdvance : SFunc :=
  (.next (.reg (.swap 0)) (.next (.push [0x02] (by decide)) (.next (.reg .sstore)
  (.next (.push (p.excess.head :: p.excess.tail) p.excess.le) (.jump 3)))))

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
    (sysEntry p body))) 2)))))))))))))

end Trees

/-! ## Reads leave the state alone -/

theorem afterSloadA_getStorVal (sevm : Sevm) (d : Devm) (k : B256) (a : Adr) (k' : B256) :
    (afterSloadA sevm d k).getStorVal a k' = d.getStorVal a k' := by
  unfold Devm.getStorVal Devm.getAcct
  rw [afterSloadA_state]

/-- `SLOAD` with the value it reads named. -/
theorem rx_sloadV {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {oc : Outcome}
    {S : List B256} {M : Mem} {G : Nat} {k' v : B256}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hroom : S.length < 1024)
    (hv : b.getStorVal sevm.currentTarget k' = v)
    (k : SFunc.RunExact fs sevm (St (afterSloadA sevm b k') (v :: S) M G) f oc) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + sloadCost sevm b k')) (.next (.reg .sload) f) oc :=
  rx_sloadA hacc hroom (hv ▸ k)

/-- The base after a list of reads, in order. -/
def readsBase (sevm : Sevm) (b : Devm) (keys : List B256) : Devm :=
  keys.foldl (afterSloadA sevm) b

/-- The selected charge of a list of reads, each against its actual incoming base. -/
def readsGas (sevm : Sevm) : Devm → List B256 → Nat
  | _, [] => 0
  | b, k :: ks => sloadCost sevm b k + readsGas sevm (afterSloadA sevm b k) ks

theorem readsGas_le (sevm : Sevm) (b : Devm) (keys : List B256) :
    readsGas sevm b keys ≤ keys.length * gasColdSload := by
  induction keys generalizing b with
  | nil => exact Nat.zero_le _
  | cons k ks ih =>
    have h1 := sloadCost_le sevm b k
    have h2 := ih (afterSloadA sevm b k)
    simp only [readsGas, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-! ## What a frame must keep to reach its stores -/

/-- A slot not yet changed in this transaction: its current value is its original one, or its
original one is zero. -/
def SlotClean (sevm : Sevm) (d : Devm) (k : B256) : Prop :=
  d.getOrigStorVal sevm sevm.currentTarget k = d.getStorVal sevm.currentTarget k ∨
    d.getOrigStorVal sevm sevm.currentTarget k = 0

/-- What the frame carries to its remaining `SSTORE`s at `keys`. -/
structure Ready (sevm : Sevm) (d : Devm) (keys : List B256) : Prop where
  error : d.error = none
  refund : 0 ≤ d.refundCounter
  spill : d.stateGas.spilled = 0
  reservoir : keys.length * amsterdamStateGasRules.storageSet ≤ d.stateGas.left
  clean : ∀ k ∈ keys, SlotClean sevm d k

theorem afterSloadA_createdAccounts (sevm : Sevm) (d : Devm) (k : B256) :
    (afterSloadA sevm d k).createdAccounts = d.createdAccounts := by
  unfold afterSloadA Devm.balReadStorage afterSload
  split <;> split <;> rfl

theorem afterSloadA_getOrig (sevm : Sevm) (d : Devm) (k : B256) (a : Adr) (k' : B256) :
    (afterSloadA sevm d k).getOrigStorVal sevm a k' = d.getOrigStorVal sevm a k' := by
  unfold Devm.getOrigStorVal
  rw [afterSloadA_createdAccounts]

theorem Ready.sload {sevm : Sevm} {d : Devm} {keys : List B256} (r : Ready sevm d keys) (k : B256) :
    Ready sevm (afterSloadA sevm d k) keys where
  error := (afterSloadA_error sevm d k).trans r.error
  refund := by rw [afterSloadA_refundCounter]; exact r.refund
  spill := by rw [afterSloadA_stateGas]; exact r.spill
  reservoir := by rw [afterSloadA_stateGas]; exact r.reservoir
  clean := fun k' hk' => by
    unfold SlotClean
    rw [afterSloadA_getOrig, afterSloadA_getStorVal]
    exact r.clean k' hk'

theorem Ready.reads {sevm : Sevm} {d : Devm} {ks : List B256} (r : Ready sevm d ks)
    (keys : List B256) : Ready sevm (readsBase sevm d keys) ks := by
  induction keys generalizing d with
  | nil => exact r
  | cons k rest ih => exact ih (r.sload k)

theorem readsBase_state (sevm : Sevm) (d : Devm) (keys : List B256) :
    (readsBase sevm d keys).state = d.state := by
  induction keys generalizing d with
  | nil => rfl
  | cons k rest ih =>
    show (readsBase sevm (afterSloadA sevm d k) rest).state = _
    rw [ih, afterSloadA_state]

theorem afterSstoreA_createdAccounts (sevm : Sevm) (d : Devm) (k v : B256) :
    (afterSstoreA A sevm d k v).createdAccounts = d.createdAccounts := by
  unfold afterSstoreA Devm.balReadAccount Devm.balReadStorage
  dsimp only
  split <;> split <;> rfl

theorem afterSstoreA_getStorVal_ne (sevm : Sevm) (d : Devm) {k k' : B256} (v : B256)
    (h : k ≠ k') :
    (afterSstoreA A sevm d k v).getStorVal sevm.currentTarget k' =
      d.getStorVal sevm.currentTarget k' := by
  unfold Devm.getStorVal Devm.getAcct
  rw [afterSstoreA_state]
  show ((d.state.setStorVal sevm.currentTarget k v).getStor sevm.currentTarget).get k' =
    (d.state.getStor sevm.currentTarget).get k'
  rw [State.getStor_setStorVal_self, Stor.get_set_ne _ h]

theorem Ready.sstore {sevm : Sevm} {d : Devm} {k : B256} {ks : List B256} (r : Ready sevm d (k :: ks))
    (fresh : k ∉ ks) (v : B256) : Ready sevm (afterSstoreA A sevm d k v) ks where
  error := (afterSstoreA_error A sevm d k v).trans r.error
  refund := by
    rw [afterSstoreA_refundCounter]
    have hc : d.getOrigStorVal sevm sevm.currentTarget k = d.getStorVal sevm.currentTarget k ∨
        d.getOrigStorVal sevm sevm.currentTarget k = 0 := r.clean k List.mem_cons_self
    exact Int.le_trans r.refund (sstoreAmsterdamRefund_ge _ A hc)
  spill := (afterSstoreA_meter A (n := 0) r.spill (by
    have := r.reservoir
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at this
    omega)).1
  reservoir := (afterSstoreA_meter A (n := ks.length * amsterdamStateGasRules.storageSet) r.spill (by
    have := r.reservoir
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at this
    omega)).2
  clean := fun k' hk' => by
    have hne : k ≠ k' := fun e => fresh (e ▸ hk')
    unfold SlotClean Devm.getOrigStorVal
    rw [afterSstoreA_createdAccounts, afterSstoreA_getStorVal_ne sevm d v hne]
    exact r.clean k' (List.mem_cons_of_mem _ hk')

/-- `Ready` keeps for fewer stores. -/
theorem Ready.skip {sevm : Sevm} {d : Devm} {k k' : B256} {ks : List B256}
    (r : Ready sevm d (k :: k' :: ks)) : Ready sevm d (k :: ks) where
  error := r.error
  refund := r.refund
  spill := r.spill
  reservoir := by
    have := r.reservoir
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at this ⊢
    omega
  clean := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact r.clean _ List.mem_cons_self
    · exact r.clean _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

/-- `SSTORE` from a `Ready` frame. -/
theorem rx_sstoreR {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {o : Outcome} {S : List B256}
    {M : Mem} {G : Nat} {k' v : B256} {ks : List B256}
    (hsg : sevm.benvStat.rules.stateGas = some A) (hstatic : sevm.isStatic = false)
    (r : Ready sevm b (k' :: ks)) (hsentry : gCallStipend < G + sstoreCostA A sevm b k' v)
    (k : SFunc.RunExact fs sevm (St (afterSstoreA A sevm b k' v) S M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: v :: S) M (G + sstoreCostA A sevm b k' v))
      (.next (.reg .sstore) f) o := by
  refine rx_sstoreA hsg hsentry hstatic r.spill ?_ k
  have hc := sstoreChargeA_le A sevm b k' v
  have hr := r.reservoir
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hr
  omega

/-! ## The excess -/

/-- The excess the code stores: the inhibitor resets to zero, otherwise `count + excess - target` in
words when that sum exceeds the target, else zero. -/
def excessNext (target excess count : B256) : B256 :=
  if B256.max = excess then 0
  else if count + excess > target then (count + excess) - target else 0

/-- The base after the final stores. -/
def finalBase (sevm : Sevm) (d : Devm) (e : B256) : Devm :=
  afterSstoreA A sevm (afterSstoreA A sevm d 0 e) 1 0

/-- The charge of `sysFinal`, without its `RETURN`'s expansion. -/
def finalGas (sevm : Sevm) (d : Devm) (e : B256) : Nat :=
  2 + 5 + 3 + sstoreCostA A sevm (afterSstoreA A sevm d 0 e) 1 0 + 3 + 2 +
    sstoreCostA A sevm d 0 e + 2 + 1

/-- The fixed charge of the excess update on empty calldata. -/
def excessFixed (target excess count : B256) : Nat :=
  if B256.max = excess then 61
  else if count + excess > target then 95 else 89

/-- The selected charge of the excess update on empty calldata. -/
def excessGas (target : B256) (sevm : Sevm) (d : Devm) : Nat :=
  excessFixed target (d.getStorVal sevm.currentTarget 0) (d.getStorVal sevm.currentTarget 1) +
    sloadCost sevm d 0 + sloadCost sevm (afterSloadA sevm d 0) 1

section Walks

variable (p : SysShape) {fs : List SFunc} {sevm : Sevm}

theorem final_run {d : Devm} {e c : B256} {ks : List B256} {M : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = some A) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hG : gCallStipend < G)
    (r : Ready sevm d ((0 : B256) :: (1 : B256) :: ks)) (h01 : (0 : B256) ∉ (1 : B256) :: ks) :
    SFunc.RunExact fs sevm
      (St d [e, c] M (G + retExt M 0 (p.len.word * c) + finalGas sevm d e))
      (sysFinal p) (.halted (retPost (finalBase sevm d e) [] M G 0 (p.len.word * c))) := by
  have r1 := r.sstore h01 e
  have hgas : G + retExt M 0 (p.len.word * c) + finalGas sevm d e =
      G + retExt M 0 (p.len.word * c) + 2 + 5 + 3 +
        sstoreCostA A sevm (afterSstoreA A sevm d 0 e) 1 0 + 3 + 2 +
        sstoreCostA A sevm d 0 e + 2 + 1 := by
    simp only [finalGas]
    omega
  rw [hgas]
  unfold sysFinal
  refine rx_dest ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_sstoreR hsg hstatic r (by omega) ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
  refine rx_sstoreR hsg hstatic r1 (by omega) ?_
  refine rx_push (w := p.len.word) rfl (by rroom) ?_
  refine rx_mul rfl (by rroom) ?_
  refine rx_push0 hpush0 (by rroom) ?_
  exact rx_return_charged

theorem noCarry_run {d : Devm} {x y c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hpush0 : sevm.benvStat.rules.op.push0 = true) (h5 : fs[5]? = some (sysFinal p))
    (next : SFunc.RunExact fs sevm (St d [0, c] M G) (sysFinal p) oc) :
    SFunc.RunExact fs sevm (St d [x, y, c] M (G + 8 + 3 + 2 + 2 + 2 + 1)) (sysNoCarry p) oc := by
  unfold sysNoCarry
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  exact rx_jump h5 next

theorem carry_run {d : Devm} {x y c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (h5 : fs[5]? = some (sysFinal p))
    (next : SFunc.RunExact fs sevm (St d [(x + y) - p.target.word, c] M G) (sysFinal p) oc) :
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
    (hdata : sevm.data = []) (h4 : fs[4]? = some (sysNoCarry p)) (h5 : fs[5]? = some (sysFinal p))
    (next : SFunc.RunExact fs sevm
      (St (afterSloadA sevm (afterSloadA sevm d 0) 1)
        [excessNext p.target.word (d.getStorVal sevm.currentTarget 0)
          (d.getStorVal sevm.currentTarget 1), c] M G) (sysFinal p) oc) :
    SFunc.RunExact fs sevm (St d [c] M (G + excessGas p.target.word sevm d)) (sysExcess p) oc := by
  have hz : sevm.data.length.toB256 = 0 := by rw [hdata]; rfl
  generalize he : d.getStorVal sevm.currentTarget 0 = e at next
  generalize hn : d.getStorVal sevm.currentTarget 1 = n at next
  have hn' : (afterSloadA sevm d 0).getStorVal sevm.currentTarget 1 = n := by
    rw [afterSloadA_getStorVal, hn]
  have hgas : ∀ F, excessFixed p.target.word e n = F →
      G + excessGas p.target.word sevm d =
        G + F + sloadCost sevm d 0 + sloadCost sevm (afterSloadA sevm d 0) 1 := by
    intro F hF
    simp only [excessGas, he, hn, hF]
    omega
  by_cases hinh : B256.max = e
  · have hflag : B256.eqCheck B256.max e = 1 := by simp only [B256.eqCheck, hinh, ite_true]
    have hnext : excessNext p.target.word e n = 0 := by simp only [excessNext, hinh, ite_true]
    rw [hnext] at next
    have nx := noCarry_run p (x := n) (y := e) hpush0 h5 next
    have e' : G + excessGas p.target.word sevm d =
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
      have e' : G + excessGas p.target.word sevm d =
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
      have e' : G + excessGas p.target.word sevm d =
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

/-- The base after the pointer stores. -/
def bookBase (sevm : Sevm) (q : Devm) (h c t : B256) : Devm :=
  if h + c = t then afterSstoreA A sevm (afterSstoreA A sevm q 2 0) 3 0
  else afterSstoreA A sevm q 2 (h + c)

/-- The charge of the bookkeeping. -/
def bookGas (sevm : Sevm) (q : Devm) (h c t : B256) : Nat :=
  if h + c = t then
    45 + sstoreCostA A sevm (afterSstoreA A sevm q 2 0) 3 0 + sstoreCostA A sevm q 2 0
  else 46 + sstoreCostA A sevm q 2 (h + c)

/-- The bookkeeping, either way. -/
theorem book_run {q : Devm} {c h t : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hsg : sevm.benvStat.rules.stateGas = some A) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hG : gCallStipend < G)
    (r : Ready sevm q [2, 3, 0, 1]) (h3 : fs[3]? = some (sysExcess p))
    (next : SFunc.RunExact fs sevm (St (bookBase sevm q h c t) [c] M G) (sysExcess p) oc) :
    SFunc.RunExact fs sevm (St q [c, c, h, t] M (G + bookGas sevm q h c t)) (sysBook p) oc := by
  by_cases hemptied : h + c = t
  · have r1 := r.sstore (by decide) (0 : B256)
    have hflag : B256.eqCheck t (h + c) = 1 := by
      rw [hemptied]
      simp only [B256.eqCheck, ite_true]
    simp only [bookBase, hemptied, ite_true] at next
    have e' : G + bookGas sevm q h c t =
        G + sstoreCostA A sevm (afterSstoreA A sevm q 2 0) 3 0 + 3 + 2 + sstoreCostA A sevm q 2 0
          + 3 + 2 + 2 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 := by
      simp only [bookGas, hemptied, ite_true]
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
    refine rx_sstoreR hsg hstatic r (by omega) ?_
    refine rx_push0 hpush0 (by rroom) ?_
    refine rx_push (w := (3 : B256)) (by decide) (by rroom) ?_
    refine rx_sstoreR hsg hstatic r1 (by omega) ?_
    exact next
  · have hflag : B256.eqCheck t (h + c) = 0 := by
      have hne : t ≠ h + c := fun e => hemptied e.symm
      simp only [B256.eqCheck, hne, ite_false]
    simp only [bookBase, hemptied, ite_false] at next
    have e' : G + bookGas sevm q h c t =
        G + 8 + 3 + sstoreCostA A sevm q 2 (h + c) + 3 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 := by
      simp only [bookGas, hemptied, ite_false]
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
    refine rx_sstoreR hsg hstatic r.skip (by omega) ?_
    refine rx_push rfl (by rroom) ?_
    exact rx_jump h3 next

theorem Ready.book {sevm : Sevm} {q : Devm} (r : Ready sevm q [2, 3, 0, 1]) (h c t : B256) :
    Ready sevm (bookBase sevm q h c t) [0, 1] := by
  unfold bookBase
  split
  · exact (r.sstore (by decide) _).sstore (by decide) _
  · exact r.skip.sstore (by decide) _

/-- `JUMPDEST DUP2 DUP2 EQ PUSH JUMPI`, either way. -/
theorem header_run {body : SFunc} {d : Devm} {M : Mem} {gas : Nat} {i c h t : B256} {oc : Outcome}
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
theorem setup_run {body : SFunc} {b : Devm} {G : Nat} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (h2 : fs[2]? = some (sysEntry p body))
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

/-- A builder runtime with its system path: the shape, the record body and that body's walk. -/
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
  entry2 : cert.prog[2]? = some (sysEntry shape body)
  entry3 : cert.prog[3]? = some (sysExcess shape)
  entry4 : cert.prog[4]? = some (sysNoCarry shape)
  entry5 : cert.prog[5]? = some (sysFinal shape)
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

theorem fold_ready {sevm : Sevm} {h : B256} {ks : List B256} (index n : Nat) {b : Devm} {M : Mem}
    (r : Ready sevm b ks) : Ready sevm (k.fold sevm h index n b M).base ks := by
  induction n generalizing index b M with
  | zero => exact r
  | succ n ih => exact ih (index + 1) (r.reads _)

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

/-- After the pointer stores. -/
def booked : Devm :=
  bookBase sevm (k.drain sevm b).base (rd sevm b 2) (k.count sevm b) (rd sevm b 3)

/-- After excess and count are read. -/
def excessRead : Devm := afterSloadA sevm (afterSloadA sevm (k.booked sevm b) 0) 1

/-- The excess this frame stores. -/
def excessStored : B256 :=
  excessNext k.shape.target.word ((k.booked sevm b).getStorVal sevm.currentTarget 0)
    ((k.booked sevm b).getStorVal sevm.currentTarget 1)

/-- The bytes `RETURN` reads its window over. -/
def outLen : B256 := k.shape.len.word * k.count sevm b

/-- The frame's exact charge. -/
def frameCost : Nat :=
  retExt (k.drain sevm b).memory 0 (k.outLen sevm b) +
    finalGas sevm (k.excessRead sevm b) (k.excessStored sevm b) +
    excessGas k.shape.target.word sevm (k.booked sevm b) +
    bookGas sevm (k.drain sevm b).base (rd sevm b 2) (k.count sevm b) (rd sevm b 3) +
    (k.drain sevm b).charges + 23 + setupGas k.shape.cap.word sevm b + dispatchGas

/-- The frame's post state at `G` of remaining gas. -/
def framePost (G : Nat) : Devm :=
  retPost (finalBase sevm (k.excessRead sevm b) (k.excessStored sevm b)) [] (k.drain sevm b).memory
    G 0 (k.outLen sevm b)

variable {sevm b}

/-- **The whole system frame**, from any storage, on empty calldata. -/
theorem frame_run (hfork : sevm.benvStat.fork = .amsterdam) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (r : Ready sevm b [2, 3, 0, 1]) {G : Nat} (hG : gCallStipend < G) :
    SFunc.RunExact k.cert.prog sevm (St b [] .empty (G + k.frameCost sevm b))
      (dispatchTree k.systemDest k.user (sysSetup k.shape k.body)) (.halted (k.framePost sevm b G)) := by
  have hsg := amsterdam_stateGas (s := sevm.benvStat) hfork
  have hacc := amsterdam_access (s := sevm.benvStat) hfork
  have hpush0 := amsterdam_push0 (s := sevm.benvStat) hfork
  have hsh := amsterdam_shifts (s := sevm.benvStat) hfork
  have rSetup : Ready sevm (setupBase sevm b) [2, 3, 0, 1] := (r.sload 3).sload 2
  have rDrain := k.fold_ready (h := rd sevm b 2) 0 (k.count sevm b).toNat (M := .empty) rSetup
  have rBooked := rDrain.book (rd sevm b 2) (k.count sevm b) (rd sevm b 3)
  have rRead : Ready sevm (k.excessRead sevm b) [0, 1] := (rBooked.sload 0).sload 1
  have s1 := final_run k.shape (fs := k.cert.prog) (d := k.excessRead sevm b)
    (e := k.excessStored sevm b) (c := k.count sevm b) (M := (k.drain sevm b).memory) hsg hpush0
    hstatic hG rRead (by decide)
  have s2 := excess_run k.shape (d := k.booked sevm b) (c := k.count sevm b) hacc hpush0 hdata
    k.entry4 k.entry5 s1
  have s3 := book_run k.shape (q := (k.drain sevm b).base) (h := rd sevm b 2) (t := rd sevm b 3)
    hsg hpush0 hstatic (by omega) rDrain k.entry3 s2
  have s4 := k.loop_run (h := rd sevm b 2) (t := rd sevm b 3) (c := k.count sevm b)
    hacc hsh (k.count sevm b).toNat (index := 0) (b := setupBase sevm b) (M := .empty) (by omega) s3
  have s5 := setup_run k.shape (b := b) (body := k.body) hacc hpush0 k.entry2 s4
  have s6 := dispatch_exact (dest := k.systemDest) (user := k.user)
    (system := sysSetup k.shape k.body) (fs := k.cert.prog) (sevm := sevm) (b := b) (M := .empty)
    (by simpa only [dispatchArm, ite_eq_left hcaller] using s5)
  have e : G + k.frameCost sevm b =
      G + retExt (k.drain sevm b).memory 0 (k.outLen sevm b) +
        finalGas sevm (k.excessRead sevm b) (k.excessStored sevm b) +
        excessGas k.shape.target.word sevm (k.booked sevm b) +
        bookGas sevm (k.drain sevm b).base (rd sevm b 2) (k.count sevm b) (rd sevm b 3) +
        (k.drain sevm b).charges + 23 + setupGas k.shape.cap.word sevm b + dispatchGas := by
    simp only [frameCost]
    omega
  rw [e]
  exact s6

end Frame

end SysPath

end Blanc.Lift.BuilderRequest
