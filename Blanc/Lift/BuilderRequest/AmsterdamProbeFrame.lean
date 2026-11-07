import Blanc.Lift.BuilderRequest.AmsterdamProbeDrain
import Blanc.Lift.BuilderRequest.AmsterdamProbeLift
import Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbeWalk
import Blanc.Lift.Deploy

/-!
# W1b probe: the whole system frame of the deposit builder under Amsterdam

Probe only; does not land. From the root of the certificate to `RETURN`, through every branch the
request phase can take, then through the lift, on any storage. The frame runs on empty calldata
(`runRequestContracts` passes `[]`). The cost is existential here: no gas bound is stated.
-/

namespace Blanc.Lift.BuilderRequest.AmsterdamProbe

open Jaune
open Blanc.Lift
open Blanc.Lift.BuilderRequest.Deposit
open Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe
open Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbeExact

/-- `.amsterdam` resolves to `amsterdamRules` in the record the machine reads. -/
theorem amsterdam_rules {s : BenvStat} (h : s.fork = .amsterdam) : s.rules = amsterdamRules := by
  show Fork.ruleSet s.fork = _
  rw [h]
  rfl

/-- The expansion charge of a return window. -/
def retExt (M : Mem) (i sz : B256) : Nat :=
  calculateMemoryGasCost (memExtSize M.size i.toNat sz.toNat) - calculateMemoryGasCost M.size

/-- The halted frame of `RETURN`. -/
def retPost (b : Devm) (S : List B256) (M : Mem) (G : Nat) (i sz : B256) : Devm :=
  ((St b S M G).memRead i.toNat sz.toNat).2.withOutput (M.read i.toNat sz.toNat).1

/-- `RETURN` of any window, with its expansion charged. Hoist debt: generalizes `rx_return`. -/
theorem rx_return_charged {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {i sz : B256} :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) M (G + retExt M i sz)) (.last .return_)
      (.halted (retPost b S M G i sz)) := by
  have hext : (St b (i :: sz :: S) M (G + retExt M i sz)).extCost [⟨i.toNat, sz.toNat⟩] =
      retExt M i sz := by
    have := Devm.extCost_add_of_size (devm := b) (S := i :: sz :: S) (N := M)
      (G := G + retExt M i sz) (i := i.toNat) (sz := sz.toNat) (a := 0) (e := retExt M i sz) rfl
      (Nat.zero_add _)
    rwa [Nat.zero_add] at this
  refine .last ?_
  show Linst.run sevm _ .return_ = _
  refine Linst.run_return_eq_ok (out := (M.read i.toNat sz.toNat).1) rfl
    (by rw [hext]; exact Nat.le_add_left _ _) ?_
  rw [hext]
  have hg : (St b (i :: sz :: S) M (G + retExt M i sz)).gasLeft - retExt M i sz = G :=
    Nat.add_sub_cancel _ _
  rw [hg]
  rfl

theorem afterSstoreA_meter {sevm : Sevm} {b : Devm} {k v : B256} {n : Nat}
    (hs : b.stateGas.spilled = 0) (hl : n + A.storageSet ≤ b.stateGas.left) :
    (afterSstoreA A sevm b k v).stateGas.spilled = 0 ∧
      n ≤ (afterSstoreA A sevm b k v).stateGas.left := by
  have hc := sstoreChargeA_le A sevm b k v
  rw [afterSstoreA_stateGas]
  refine ⟨hs, ?_⟩
  show n ≤ b.stateGas.left + _ - sstoreChargeA A sevm b k v
  omega

theorem dB6_stateGas (sevm : Sevm) (b : Devm) (h i : B256) :
    (dB6 sevm b h i).stateGas = b.stateGas := by
  simp only [dB6, dB5, dB4, dB3, dB2, dB1, afterSloadA_stateGas]

theorem drainFold_stateGas (sevm : Sevm) (h : B256) (n : Nat) (i : Nat) (b : Devm) (M : Mem) :
    (drainFold sevm h i n b M).base.stateGas = b.stateGas := by
  induction n generalizing i b M with
  | zero => rfl
  | succ n ih =>
    simp only [drainFold]
    rw [ih, dB6_stateGas]

section frame

variable {sevm : Sevm}

/-- The frame after the excess and count stores. -/
def fS1 (sevm : Sevm) (b : Devm) (e : B256) : Devm := afterSstoreA A sevm b 0 e
def fS2 (sevm : Sevm) (b : Devm) (e : B256) : Devm := afterSstoreA A sevm (fS1 sevm b e) 1 0

/-- `t_0264`: store the excess, clear the count, return the records. -/
theorem final_run {b : Devm} {e c : B256} {M : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = some A) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hG : gCallStipend < G)
    (hspill : b.stateGas.spilled = 0) (hres : 2 * A.storageSet ≤ b.stateGas.left) :
    SFunc.RunExact cert.prog sevm
      (St b [e, c] M (G + retExt M 0 ((184 : B256) * c) + 2 + 5 + 3
        + sstoreCostA A sevm (fS1 sevm b e) 1 0 + 3 + 2 + sstoreCostA A sevm b 0 e + 2 + 1))
      t_0264_c5 (.halted (retPost (fS2 sevm b e) [] M G 0 ((184 : B256) * c))) := by
  have hm := afterSstoreA_meter (sevm := sevm) (k := 0) (v := e) (n := A.storageSet) hspill
    (by omega)
  dsimp only [t_0264_c5]
  refine rx_dest ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_sstoreA hsg (by omega) hstatic hspill
    (le_trans (sstoreChargeA_le A sevm b 0 e) (by omega)) ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
  refine rx_sstoreA hsg (by omega) hstatic hm.1
    (le_trans (sstoreChargeA_le A sevm _ 1 0) (le_trans hm.2 (Nat.le_add_right _ _))) ?_
  refine rx_push (w := (184 : B256)) (by decide) (by rroom) ?_
  refine rx_mul rfl (by rroom) ?_
  refine rx_push0 hpush0 (by rroom) ?_
  exact rx_return_charged

/-- `t_0230`, no excess: down to `[0, c]`, jump to `t_0264`. -/
theorem noExcess_run {b : Devm} {x y c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (next : SFunc.RunExact cert.prog sevm (St b [0, c] M G) t_0264_c5 oc) :
    SFunc.RunExact cert.prog sevm (St b [x, y, c] M (G + 8 + 3 + 2 + 2 + 2 + 1)) t_0230_c4 oc := by
  dsimp only [t_0230_c4]
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  exact rx_jump rfl next

/-- The base after reading excess and count. -/
def fL0 (sevm : Sevm) (b : Devm) : Devm := afterSloadA sevm b 0
def fL1 (sevm : Sevm) (b : Devm) : Devm := afterSloadA sevm (fL0 sevm b) 1
def fExcess (sevm : Sevm) (b : Devm) : B256 := b.getStorVal sevm.currentTarget 0
def fCount (sevm : Sevm) (b : Devm) : B256 := (fL0 sevm b).getStorVal sevm.currentTarget 1
def fMax : B256 := Bytes.toB256 (List.replicate 32 0xff)

/-- `t_01f4`, then `t_01fa` and `t_0226`: empty calldata, not inhibited, no excess. -/
theorem excess_run {b : Devm} {c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929)
    (hpush0 : sevm.benvStat.rules.op.push0 = true) (hdata : sevm.data = [])
    (hinh : B256.eqCheck fMax (fExcess sevm b) = 0)
    (hcap : B256.gtCheck (fCount sevm b + fExcess sevm b) 8 = 0)
    (next : SFunc.RunExact cert.prog sevm
      (St (fL1 sevm b) [fCount sevm b, fExcess sevm b, c] M G) t_0230_c4 oc) :
    SFunc.RunExact cert.prog sevm
      (St b [c] M (G + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 3 + 3
        + sloadCost sevm (fL0 sevm b) 1 + 3 + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1))
      t_01f4_c3 oc := by
  have hz : sevm.data.length.toB256 = 0 := by rw [hdata]; rfl
  dsimp only [t_01f4_c3, t_01fa_c3, t_0226_c3]
  refine rx_dest ?_
  refine rx_calldatasize (by rroom) ?_
  rw [hz]
  refine rx_push rfl (by rroom) ?_
  refine rx_branch_zero ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_sloadA hacc (by rroom) ?_
  refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
  refine rx_sloadA hacc (by rroom) ?_
  refine rx_dup2 (by rroom) ?_
  refine rx_push (w := fMax) rfl (by rroom) ?_
  refine rx_eq hinh (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  refine rx_branchTo_zero ?_
  refine rx_push (w := (8 : B256)) (by decide) (by rroom) ?_
  refine rx_dup3 (by rroom) ?_
  refine rx_dup3 (by rroom) ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_gt hcap (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  refine rx_branch_zero ?_
  exact next

/-- The base after the queue's pointers are cleared. -/
def fR1 (sevm : Sevm) (b : Devm) : Devm := afterSstoreA A sevm b 2 0
def fR2 (sevm : Sevm) (b : Devm) : Devm := afterSstoreA A sevm (fR1 sevm b) 3 0

/-- `t_01d7` and `t_01e9`: the queue emptied, so head and tail go back to zero. -/
theorem bookkeeping_run {b : Devm} {c h t : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (hsg : sevm.benvStat.rules.stateGas = some A) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hG : gCallStipend < G)
    (hspill : b.stateGas.spilled = 0) (hres : 2 * A.storageSet ≤ b.stateGas.left)
    (hemptied : h + c = t)
    (next : SFunc.RunExact cert.prog sevm (St (fR2 sevm b) [c] M G) t_01f4_c3 oc) :
    SFunc.RunExact cert.prog sevm
      (St b [c, c, h, t] M (G + sstoreCostA A sevm (fR1 sevm b) 3 0 + 3 + 2
        + sstoreCostA A sevm b 2 0 + 3 + 2 + 2 + 3 + 1
        + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1))
      t_01d7_c2 oc := by
  have hm := afterSstoreA_meter (sevm := sevm) (k := 2) (v := 0) (n := A.storageSet) hspill
    (by omega)
  dsimp only [t_01d7_c2, t_01e9_c2]
  refine rx_dest ?_
  refine rx_swap2 ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_dup1 (by rroom) ?_
  refine rx_swap3 ?_
  refine rx_eq (v := 1) (by rw [hemptied]; simp only [B256.eqCheck, ite_true]) (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
  refine rx_sstoreA hsg (by omega) hstatic hspill
    (le_trans (sstoreChargeA_le A sevm b 2 0) (by omega)) ?_
  refine rx_push0 hpush0 (by rroom) ?_
  refine rx_push (w := (3 : B256)) (by decide) (by rroom) ?_
  refine rx_sstoreA hsg (by omega) hstatic hm.1
    (le_trans (sstoreChargeA_le A sevm _ 3 0) (le_trans hm.2 (Nat.le_add_right _ _))) ?_
  exact next

/-- The base after reading tail and head. -/
def fT0 (sevm : Sevm) (b : Devm) : Devm := afterSloadA sevm b 3
def fH0 (sevm : Sevm) (b : Devm) : Devm := afterSloadA sevm (fT0 sevm b) 2
def fTail (sevm : Sevm) (b : Devm) : B256 := b.getStorVal sevm.currentTarget 3
def fHead (sevm : Sevm) (b : Devm) : B256 := (fT0 sevm b).getStorVal sevm.currentTarget 2
def fCnt (sevm : Sevm) (b : Devm) : B256 := fTail sevm b - fHead sevm b

/-- `t_0000`, the system dispatch, and `t_011c`, the count under the cap, into the loop. -/
theorem setup_run {b : Devm} {G : Nat} {oc : Outcome}
    (hacc : sevm.benvStat.rules.access = .eip2929)
    (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hcaller : sevm.caller = systemAddress)
    (hunder : B256.gtCheck 64 (fCnt sevm b) ≠ 0)
    (next : SFunc.RunExact cert.prog sevm
      (St (fH0 sevm b) [0, fCnt sevm b, fHead sevm b, fTail sevm b] .empty G) t_0133_c7 oc) :
    SFunc.RunExact cert.prog sevm
      (St b [] .empty (G + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3
        + sloadCost sevm (fT0 sevm b) 2 + 3 + sloadCost sevm b 3 + 3 + 1
        + 10 + 3 + 3 + 3 + 2))
      t_0000_c0 oc := by
  dsimp only [t_0000_c0, t_011c_c0]
  refine rx_caller (by rroom) ?_
  refine rx_push (w := systemAddress.toB256) rfl (by rroom) ?_
  refine rx_eq (v := 1) (by rw [hcaller]; simp only [B256.eqCheck, ite_true]) (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  refine rx_branch_succ (by decide) ?_
  refine rx_dest ?_
  refine rx_push (w := (3 : B256)) (by decide) (by rroom) ?_
  refine rx_sloadA hacc (by rroom) ?_
  refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
  refine rx_sloadA hacc (by rroom) ?_
  refine rx_dup1 (by rroom) ?_
  refine rx_dup3 (by rroom) ?_
  refine rx_sub' rfl (by rroom) ?_
  refine rx_dup1 (by rroom) ?_
  refine rx_push (w := (64 : B256)) (by decide) (by rroom) ?_
  refine rx_gt rfl (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  refine rx_branchTo_succ hunder rfl ?_
  dsimp only [t_0131_c2]
  refine rx_dest ?_
  refine rx_push0 hpush0 (by rroom) ?_
  exact next

/-- The system frame halts from this point, whatever gas above the sentry remains after `cost`. -/
def Halts (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (f : SFunc) : Prop :=
  ∃ (cost : Nat) (post : Nat → Devm), ∀ G, gCallStipend < G →
    SFunc.RunExact cert.prog sevm (St b S M (G + cost)) f (.halted (post G))

theorem Halts.prefix {b' b : Devm} {S' S : List B256} {M' M : Mem} {f' f : SFunc} (p : Nat)
    (hp : ∀ G oc, gCallStipend < G → SFunc.RunExact cert.prog sevm (St b' S' M' G) f' oc →
      SFunc.RunExact cert.prog sevm (St b S M (G + p)) f oc)
    (next : Halts sevm b' S' M' f') : Halts sevm b S M f := by
  obtain ⟨c, post, h⟩ := next
  refine ⟨c + p, post, fun G hG => ?_⟩
  rw [← Nat.add_assoc]
  exact hp (G + c) _ (by omega) (h G hG)

/-- `t_0238`: some excess carries over. -/
theorem carry_run {b : Devm} {x y c : B256} {M : Mem} {G : Nat} {oc : Outcome}
    (next : SFunc.RunExact cert.prog sevm (St b [(x + y) - 8, c] M G) t_0264_c5 oc) :
    SFunc.RunExact cert.prog sevm (St b [x, y, c] M (G + 8 + 3 + 3 + 3 + 3 + 3 + 1)) t_0238_c3 oc := by
  dsimp only [t_0238_c3]
  refine rx_dest ?_
  refine rx_add' rfl (by rroom) ?_
  refine rx_push (w := (8 : B256)) (by decide) (by rroom) ?_
  refine rx_swap1 ?_
  refine rx_sub' rfl (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  exact rx_jump rfl next

theorem final_halts {b : Devm} {e c : B256} {M : Mem}
    (hsg : sevm.benvStat.rules.stateGas = some A) (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false)
    (hspill : b.stateGas.spilled = 0) (hres : 2 * A.storageSet ≤ b.stateGas.left) :
    Halts sevm b [e, c] M t_0264_c5 := by
  refine ⟨retExt M 0 ((184 : B256) * c) + 2 + 5 + 3
        + sstoreCostA A sevm (fS1 sevm b e) 1 0 + 3 + 2 + sstoreCostA A sevm b 0 e + 2 + 1,
    fun G => retPost (fS2 sevm b e) [] M G 0 ((184 : B256) * c), fun G hG => ?_⟩
  have r := final_run (e := e) (c := c) (M := M) hsg hpush0 hstatic hG hspill hres
  have e' : G + (retExt M 0 ((184 : B256) * c) + 2 + 5 + 3
        + sstoreCostA A sevm (fS1 sevm b e) 1 0 + 3 + 2 + sstoreCostA A sevm b 0 e + 2 + 1) =
      G + retExt M 0 ((184 : B256) * c) + 2 + 5 + 3
        + sstoreCostA A sevm (fS1 sevm b e) 1 0 + 3 + 2 + sstoreCostA A sevm b 0 e + 2 + 1 := by
    omega
  rw [e']
  exact r

/-- From `t_01f4`, on empty calldata: every branch of the excess and inhibitor logic. -/
theorem excess_halts {b : Devm} {c : B256} {M : Mem}
    (hsg : sevm.benvStat.rules.stateGas = some A)
    (hacc : sevm.benvStat.rules.access = .eip2929)
    (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hdata : sevm.data = [])
    (hspill : b.stateGas.spilled = 0) (hres : 2 * A.storageSet ≤ b.stateGas.left) :
    Halts sevm b [c] M t_01f4_c3 := by
  have hsg1 : (fL1 sevm b).stateGas = b.stateGas := by
    simp only [fL1, fL0, afterSloadA_stateGas]
  have hfin {e : B256} : Halts sevm (fL1 sevm b) [e, c] M t_0264_c5 :=
    final_halts hsg hpush0 hstatic (by rw [hsg1]; exact hspill) (by rw [hsg1]; exact hres)
  have hz : sevm.data.length.toB256 = 0 := by rw [hdata]; rfl
  by_cases hinh : fMax = fExcess sevm b
  · -- Inhibited: the excess stays at the inhibitor's branch, and is reset to zero.
    refine Halts.prefix (b' := fL1 sevm b) (S' := [0, c]) (M' := M) (f' := t_0264_c5)
      (8 + 3 + 2 + 2 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + sloadCost sevm (fL0 sevm b) 1 + 3
        + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1) (fun G oc _ r => ?_) hfin
    have nx := noExcess_run (x := fCount sevm b) (y := fExcess sevm b) hpush0 r
    have e' : ∀ X, G + (8 + 3 + 2 + 2 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + X + 3
        + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1) =
        G + 8 + 3 + 2 + 2 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + X + 3
        + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1 := fun _ => by omega
    rw [e']
    dsimp only [t_01f4_c3, t_01fa_c3]
    refine rx_dest ?_
    refine rx_calldatasize (by rroom) ?_
    rw [hz]
    refine rx_push rfl (by rroom) ?_
    refine rx_branch_zero ?_
    refine rx_push0 hpush0 (by rroom) ?_
    refine rx_sloadA hacc (by rroom) ?_
    refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadA hacc (by rroom) ?_
    refine rx_dup2 (by rroom) ?_
    refine rx_push (w := fMax) rfl (by rroom) ?_
    refine rx_eq (v := 1) (by simp only [B256.eqCheck, hinh, fExcess, ite_true]) (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branchTo_succ (by decide) rfl ?_
    exact nx
  · have hne : B256.eqCheck fMax (fExcess sevm b) = 0 := by
      simp only [B256.eqCheck, hinh, ite_false]
    by_cases hgt : fCount sevm b + fExcess sevm b > 8
    · have hcap : B256.gtCheck (fCount sevm b + fExcess sevm b) 8 = 1 := by
        simp only [B256.gtCheck, hgt, ite_true]
      refine Halts.prefix (b' := fL1 sevm b)
        (S' := [(fCount sevm b + fExcess sevm b) - 8, c]) (M' := M) (f' := t_0264_c5)
        (8 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 3 + 3
          + sloadCost sevm (fL0 sevm b) 1 + 3 + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1)
        (fun G oc _ r => ?_) hfin
      have nx := carry_run r
      have e' : ∀ X, G + (8 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 3 + 3
          + X + 3 + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1) =
          G + 8 + 3 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 3 + 3
          + X + 3 + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1 := fun _ => by omega
      rw [e']
      dsimp only [t_01f4_c3, t_01fa_c3, t_0226_c3]
      refine rx_dest ?_
      refine rx_calldatasize (by rroom) ?_
      rw [hz]
      refine rx_push rfl (by rroom) ?_
      refine rx_branch_zero ?_
      refine rx_push0 hpush0 (by rroom) ?_
      refine rx_sloadA hacc (by rroom) ?_
      refine rx_push (w := (1 : B256)) (by decide) (by rroom) ?_
      refine rx_sloadA hacc (by rroom) ?_
      refine rx_dup2 (by rroom) ?_
      refine rx_push (w := fMax) rfl (by rroom) ?_
      refine rx_eq hne (by rroom) ?_
      refine rx_push rfl (by rroom) ?_
      refine rx_branchTo_zero ?_
      refine rx_push (w := (8 : B256)) (by decide) (by rroom) ?_
      refine rx_dup3 (by rroom) ?_
      refine rx_dup3 (by rroom) ?_
      refine rx_add' rfl (by rroom) ?_
      refine rx_gt hcap (by rroom) ?_
      refine rx_push rfl (by rroom) ?_
      refine rx_branch_succ (by decide) ?_
      exact nx
    · have hcap : B256.gtCheck (fCount sevm b + fExcess sevm b) 8 = 0 := by
        simp only [B256.gtCheck, hgt, ite_false]
      refine Halts.prefix (b' := fL1 sevm b) (S' := [0, c]) (M' := M) (f' := t_0264_c5)
        (8 + 3 + 2 + 2 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 3 + 3
          + sloadCost sevm (fL0 sevm b) 1 + 3 + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1)
        (fun G oc _ r => ?_) hfin
      have nx := excess_run (c := c) (M := M) hacc hpush0 hdata hne hcap
        (noExcess_run (x := fCount sevm b) (y := fExcess sevm b) hpush0 r)
      have e' : ∀ X, G + (8 + 3 + 2 + 2 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 3 + 3
          + X + 3 + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1) =
          G + 8 + 3 + 2 + 2 + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 3 + 3
          + X + 3 + sloadCost sevm b 0 + 2 + 10 + 3 + 2 + 1 := fun _ => by omega
      rw [e']
      exact nx

/-- From `t_01d7`: the queue either emptied or did not. -/
theorem bookkeeping_halts {b : Devm} {c h t : B256} {M : Mem}
    (hsg : sevm.benvStat.rules.stateGas = some A)
    (hacc : sevm.benvStat.rules.access = .eip2929)
    (hpush0 : sevm.benvStat.rules.op.push0 = true)
    (hstatic : sevm.isStatic = false) (hdata : sevm.data = [])
    (hspill : b.stateGas.spilled = 0) (hres : 4 * A.storageSet ≤ b.stateGas.left) :
    Halts sevm b [c, c, h, t] M t_01d7_c2 := by
  by_cases hemptied : h + c = t
  · have hm1 := afterSstoreA_meter (sevm := sevm) (b := b) (k := 2) (v := 0)
      (n := 3 * A.storageSet) hspill (by omega)
    have hm2 := afterSstoreA_meter (sevm := sevm) (b := fR1 sevm b) (k := 3) (v := 0)
      (n := 2 * A.storageSet) hm1.1 (by unfold fR1 at *; omega)
    refine Halts.prefix (b' := fR2 sevm b) (S' := [c]) (M' := M) (f' := t_01f4_c3)
      (sstoreCostA A sevm (fR1 sevm b) 3 0 + 3 + 2 + sstoreCostA A sevm b 2 0 + 3 + 2 + 2 + 3 + 1
        + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1) (fun G oc hG r => ?_)
      (excess_halts hsg hacc hpush0 hstatic hdata hm2.1 hm2.2)
    have nx := bookkeeping_run (h := h) (t := t) hsg hpush0 hstatic hG hspill (by omega) hemptied r
    have e' : G + (sstoreCostA A sevm (fR1 sevm b) 3 0 + 3 + 2 + sstoreCostA A sevm b 2 0 + 3 + 2
        + 2 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1) =
        G + sstoreCostA A sevm (fR1 sevm b) 3 0 + 3 + 2 + sstoreCostA A sevm b 2 0 + 3 + 2 + 2 + 3
        + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 := by omega
    rw [e']
    exact nx
  · have hne : B256.eqCheck t (h + c) = 0 := by
      have : t ≠ h + c := fun e => hemptied e.symm
      simp only [B256.eqCheck, this, ite_false]
    have hm1 := afterSstoreA_meter (sevm := sevm) (b := b) (k := 2) (v := h + c)
      (n := 2 * A.storageSet) hspill (by omega)
    refine Halts.prefix (b' := afterSstoreA A sevm b 2 (h + c)) (S' := [c]) (M' := M)
      (f' := t_01f4_c3)
      (8 + 3 + sstoreCostA A sevm b 2 (h + c) + 3 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1)
      (fun G oc hG r => ?_) (excess_halts hsg hacc hpush0 hstatic hdata hm1.1 hm1.2)
    have e' : G + (8 + 3 + sstoreCostA A sevm b 2 (h + c) + 3 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1) =
        G + 8 + 3 + sstoreCostA A sevm b 2 (h + c) + 3 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 := by
      omega
    rw [e']
    dsimp only [t_01d7_c2, t_01e1_c2]
    refine rx_dest ?_
    refine rx_swap2 ?_
    refine rx_add' rfl (by rroom) ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_swap3 ?_
    refine rx_eq hne (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branch_zero ?_
    refine rx_swap1 ?_
    refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
    refine rx_sstoreA hsg (by omega) hstatic hspill
      (le_trans (sstoreChargeA_le A sevm b 2 (h + c)) (by omega)) ?_
    refine rx_push rfl (by rroom) ?_
    exact rx_jump rfl r

/-- Into the loop, for either count. -/
theorem loop_halts {b : Devm} {c h t : B256} {M : Mem}
    (hfork : sevm.benvStat.fork = .amsterdam) (hdata : sevm.data = [])
    (hstatic : sevm.isStatic = false) (cap : c.toNat ≤ 64)
    (hspill : b.stateGas.spilled = 0) (hres : 4 * A.storageSet ≤ b.stateGas.left) :
    Halts sevm b [0, c, h, t] M t_0133_c7 := by
  have hsgA := amsterdam_stateGas (s := sevm.benvStat) hfork
  have hacc := amsterdam_access (s := sevm.benvStat) hfork
  have hpush0 := amsterdam_push0 (s := sevm.benvStat) hfork
  have hsame := drainFold_stateGas sevm h c.toNat 0 b M
  refine Halts.prefix (b' := (drainFold sevm h 0 c.toNat b M).base) (S' := [c, c, h, t])
    (M' := (drainFold sevm h 0 c.toNat b M).memory) (f' := t_01d7_c2)
    ((drainFold sevm h 0 c.toNat b M).charges + 23) (fun G oc _ r => ?_)
    (bookkeeping_halts hsgA hacc hpush0 hstatic hdata (by rw [hsame]; exact hspill)
      (by rw [hsame]; exact hres))
  have l := drainLoop_exact_from (h := h) (t := t) (c := c) (b := b) (M := M) (gas := G) (oc := oc)
    hfork cap c.toNat (index := 0) (by omega) r
  have e' : G + ((drainFold sevm h 0 c.toNat b M).charges + 23) =
      G + (drainFold sevm h 0 c.toNat b M).charges + 23 := by omega
  rw [e']
  exact l

/-- **Every system frame of the deposit builder halts under Amsterdam, from any storage.** -/
theorem frame_halts {b : Devm}
    (hfork : sevm.benvStat.fork = .amsterdam) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (hspill : b.stateGas.spilled = 0) (hres : 4 * A.storageSet ≤ b.stateGas.left) :
    Halts sevm b [] .empty t_0000_c0 := by
  have hacc := amsterdam_access (s := sevm.benvStat) hfork
  have hpush0 := amsterdam_push0 (s := sevm.benvStat) hfork
  have hsg1 : (fH0 sevm b).stateGas = b.stateGas := by
    simp only [fH0, fT0, afterSloadA_stateGas]
  by_cases hunder : (64 : B256) > fCnt sevm b
  · have hflag : B256.gtCheck 64 (fCnt sevm b) ≠ 0 := by
      simp only [B256.gtCheck, hunder, ite_true]
      decide
    have cap : (fCnt sevm b).toNat ≤ 64 := by
      have := B256.toNat_lt_toNat hunder
      have h64 : (64 : B256).toNat = 64 := by decide
      omega
    refine Halts.prefix (b' := fH0 sevm b) (S' := [0, fCnt sevm b, fHead sevm b, fTail sevm b])
      (M' := .empty) (f' := t_0133_c7)
      (2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (fT0 sevm b) 2 + 3
        + sloadCost sevm b 3 + 3 + 1 + 10 + 3 + 3 + 3 + 2) (fun G oc _ r => ?_)
      (loop_halts hfork hdata hstatic cap (by rw [hsg1]; exact hspill) (by rw [hsg1]; exact hres))
    have s := setup_run hacc hpush0 hcaller hflag r
    have e' : G + (2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (fT0 sevm b) 2 + 3
        + sloadCost sevm b 3 + 3 + 1 + 10 + 3 + 3 + 3 + 2) =
        G + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (fT0 sevm b) 2 + 3
        + sloadCost sevm b 3 + 3 + 1 + 10 + 3 + 3 + 3 + 2 := by omega
    rw [e']
    exact s
  · have hflag : B256.gtCheck 64 (fCnt sevm b) = 0 := by
      simp only [B256.gtCheck, hunder, ite_false]
    refine Halts.prefix (b' := fH0 sevm b) (S' := [0, 64, fHead sevm b, fTail sevm b])
      (M' := .empty) (f' := t_0133_c7)
      (2 + 1 + 3 + 2 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (fT0 sevm b) 2 + 3
        + sloadCost sevm b 3 + 3 + 1 + 10 + 3 + 3 + 3 + 2) (fun G oc _ r => ?_)
      (loop_halts hfork hdata hstatic (by decide) (by rw [hsg1]; exact hspill)
        (by rw [hsg1]; exact hres))
    have e' : G + (2 + 1 + 3 + 2 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (fT0 sevm b) 2 + 3
        + sloadCost sevm b 3 + 3 + 1 + 10 + 3 + 3 + 3 + 2) =
        G + 2 + 1 + 3 + 2 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (fT0 sevm b) 2 + 3
        + sloadCost sevm b 3 + 3 + 1 + 10 + 3 + 3 + 3 + 2 := by omega
    rw [e']
    dsimp only [t_0000_c0, t_011c_c0, t_012e_c0, t_0131_c2]
    refine rx_caller (by rroom) ?_
    refine rx_push (w := systemAddress.toB256) rfl (by rroom) ?_
    refine rx_eq (v := 1) (by rw [hcaller]; simp only [B256.eqCheck, ite_true]) (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branch_succ (by decide) ?_
    refine rx_dest ?_
    refine rx_push (w := (3 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadA hacc (by rroom) ?_
    refine rx_push (w := (2 : B256)) (by decide) (by rroom) ?_
    refine rx_sloadA hacc (by rroom) ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_dup3 (by rroom) ?_
    refine rx_sub' rfl (by rroom) ?_
    refine rx_dup1 (by rroom) ?_
    refine rx_push (w := (64 : B256)) (by decide) (by rroom) ?_
    refine rx_gt hflag (by rroom) ?_
    refine rx_push rfl (by rroom) ?_
    refine rx_branchTo_zero ?_
    refine rx_pop ?_
    refine rx_push (w := (64 : B256)) (by decide) (by rroom) ?_
    refine rx_dest ?_
    refine rx_push0 hpush0 (by rroom) ?_
    exact r

/-- **The deposit builder's system frame, through the lift to the compiled `Exec`:** under
Amsterdam, from any storage, on empty calldata, the frame runs to a successful halt. -/
theorem deposit_exec_any_storage {b : Devm}
    (hcode : sevm.code = Deposit.code)
    (hfork : sevm.benvStat.fork = .amsterdam) (hstatic : sevm.isStatic = false)
    (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (hspill : b.stateGas.spilled = 0) (hres : 4 * A.storageSet ≤ b.stateGas.left) :
    ∃ (cost : Nat) (post : Nat → Devm), ∀ G, gCallStipend < G →
      Nonempty (Exec 0 sevm (St b [] .empty (G + cost)) (.ok (post G))) := by
  obtain ⟨cost, post, h⟩ := frame_halts hfork hstatic hcaller hdata hspill hres
  exact ⟨cost, post, fun G hG => deposit_lift hcode ⟨t_0000_c0, rfl, h G hG⟩⟩

end frame

end Blanc.Lift.BuilderRequest.AmsterdamProbe
