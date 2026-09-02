-- ProrataWithdraw.lean : exact successful PRORATA withdrawal settlement.

import Blanc.ProrataFunctional

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Prorata

private instance : Rinst.Hinv Devm.logs Rinst.selfbalance := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

private instance : Rinst.Hinv Devm.logs Rinst.sub := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

private instance : Rinst.Hinv Devm.logs Rinst.mul := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

private instance : Rinst.Hinv Devm.logs Rinst.div := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

private instance : Rinst.Hinv Devm.logs Rinst.shr := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

private instance : Rinst.Hinv Devm.output Rinst.selfbalance := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output⟩

private instance : Rinst.Hinv Devm.output Rinst.sub := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.output

private instance : Rinst.Hinv Devm.output Rinst.mul := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.output

private instance : Rinst.Hinv Devm.output Rinst.div := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.output

private instance : Rinst.Hinv Devm.output Rinst.shr := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.output

private instance : Rinst.Hinv Devm.memory Rinst.mul := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.memory

private instance : Rinst.Hinv Devm.memory Rinst.div := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.memory

/-- The settled outer state and literal operands immediately before the
outbound withdrawal `CALL`.  The call result is deliberately outside this
carrier: a callee may re-enter and change callback-final state. -/
def WithdrawPreCallEffect (sevm : Sevm) (pre callPre : Devm) : Prop :=
  let s := Sevm.argWord sevm 0
  let stor := Devm.getStor pre sevm.currentTarget
  let B := Devm.getBal pre sevm.currentTarget
  let C := stor.get sevm.caller.toB256
  let S := stor.get supplySlot
  let p := s * (B + 1) / (S + offset)
  s ≤ C ∧
    B ≤ maxBalance ∧
    Devm.getStor callPre sevm.currentTarget =
      (stor.set sevm.caller.toB256 (C - s)).set supplySlot (S - s) ∧
    Devm.getBal callPre = Devm.getBal pre ∧
    Devm.getCode callPre = Devm.getCode pre ∧
    callPre.logs = pre.logs ∧
    callPre.output = pre.output ∧
    callPre.memory = pre.memory ∧
    ∃ gasWord,
      gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: p :: S ::
        (S + offset) :: s :: supplySlot :: [] <<+ callPre.stack

private theorem sendToCaller_frame
    {sevm : Sevm} {pre callPost : Devm} {p : B256} {xs : Stack}
    (hp : p :: xs <<+ pre.stack)
    (run : Line.Run sevm pre sendToCaller callPost) :
    ∃ callPre gasWord,
      gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs <<+
        callPre.stack ∧
      Ninst.Run sevm callPre call callPost ∧
      Devm.getStor callPre = Devm.getStor pre ∧
      Devm.getBal callPre = Devm.getBal pre ∧
      Devm.getCode callPre = Devm.getCode pre ∧
      callPre.logs = pre.logs ∧
      callPre.output = pre.output ∧
      callPre.memory = pre.memory := by
  unfold sendToCaller at run
  let callPrefix : Line := pushList [0, 0, 0, 0] ++ [swap 3, caller, gas]
  rcases of_run_append callPrefix run with ⟨callPre, hprefix, hcall⟩
  have hstorPrefix : Devm.getStor pre = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by unfold callPrefix; line_inv) hprefix
  have hbalPrefix : Devm.getBal pre = Devm.getBal callPre :=
    Line.of_inv Devm.getBal (by unfold callPrefix; line_inv) hprefix
  have hcodePrefix : Devm.getCode pre = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by unfold callPrefix; line_inv) hprefix
  have hlogsPrefix : pre.logs = callPre.logs :=
    Line.of_inv Devm.logs (by unfold callPrefix; line_inv) hprefix
  have houtPrefix : pre.output = callPre.output :=
    Line.of_inv Devm.output (by unfold callPrefix; line_inv) hprefix
  have hmemPrefix : pre.memory = callPre.memory :=
    Line.of_inv Devm.memory (by unfold callPrefix; line_inv) hprefix
  rcases Line.of_run_cons hcall with ⟨callPost', qcall, hnil⟩
  cases hnil
  unfold callPrefix pushList at hprefix
  simp only [List.map] at hprefix
  rcases Line.of_run_cons hprefix with ⟨s1, q1, hprefix⟩
  have p1 : (0 : B256) :: p :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons hprefix with ⟨s2, q2, hprefix⟩
  have p2 : (0 : B256) :: 0 :: p :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 q2) p1
  rcases Line.of_run_cons hprefix with ⟨s3, q3, hprefix⟩
  have p3 : (0 : B256) :: 0 :: 0 :: p :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 q3) p2
  rcases Line.of_run_cons hprefix with ⟨s4, q4, hprefix⟩
  have p4 : (0 : B256) :: 0 :: 0 :: 0 :: p :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 q4) p3
  rcases Line.of_run_cons hprefix with ⟨s5, qswap, hprefix⟩
  have hswap : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: p :: xs)
      (p :: 0 :: 0 :: 0 :: 0 :: xs) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have p5 : p :: 0 :: 0 :: 0 :: 0 :: xs <<+ s5.stack :=
    Stack.prefix_of_swap hswap (of_run_swap qswap) p4
  rcases Line.of_run_cons hprefix with ⟨s6, qcaller, hprefix⟩
  have p6 : sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs <<+ s6.stack :=
    prefix_of_push (of_run_caller qcaller) p5
  rcases Line.of_run_cons hprefix with ⟨s7, qgas, hnil⟩
  cases hnil
  rcases of_run_gas qgas with ⟨gasWord, hgas⟩
  refine ⟨callPre, gasWord, ?_, qcall,
    hstorPrefix.symm, hbalPrefix.symm, hcodePrefix.symm, hlogsPrefix.symm,
    houtPrefix.symm, hmemPrefix.symm⟩
  simpa only [List.cons_append, List.nil_append] using prefix_of_push hgas p6

private def withdrawAfterCall : Func :=
  (mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert

/-- A successful raw withdrawal has settled both ledger writes before reaching
the outbound `CALL`; callback-final state is intentionally not characterized. -/
theorem withdraw_settles_before_call
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre withdraw post) :
    ∃ callPre callPost,
      WithdrawPreCallEffect sevm pre callPre ∧
      Ninst.Run sevm callPre call callPost ∧
      Func.Run fs sevm callPost withdrawAfterCall post := by
  simp only [withdraw] at run
  rcases of_run_prepend pushMaxWord _ run with ⟨u0, hcache, hrest⟩
  have hcacheInv := hcache
  rcases of_run_prepend (arg 0) _ hrest with ⟨u1, qarg, hrest⟩
  rcases of_run_prepend [dup 0, caller, sload, dup 1, dup 1, lt] _ hrest with
    ⟨u7, hcoverLine, hcoverBranch⟩
  have hcoverInv := hcoverLine
  unfold pushMaxWord at hcache
  rcases Line.of_run_cons hcache with ⟨c1, q0, hcache⟩
  rcases Line.of_run_cons hcache with ⟨u0', qnot, hnil⟩
  cases hnil
  have hU : ~~~(0 : B256) = B256.max := by decide +kernel
  have cp0 : (0 : B256) :: [] <<+ c1.stack :=
    prefix_of_push (of_run_pushB256 q0) nil_pref
  have cp1 : supplySlot :: [] <<+ u0.stack := by
    change B256.max :: [] <<+ u0.stack
    rw [← hU]
    exact prefix_of_not qnot cp0
  rcases Line.of_run_cons hcoverLine with ⟨u2, qdupS, hcoverLine⟩
  rcases Line.of_run_cons hcoverLine with ⟨u3, qcaller, hcoverLine⟩
  rcases Line.of_run_cons hcoverLine with ⟨u4, qsloadC, hcoverLine⟩
  rcases Line.of_run_cons hcoverLine with ⟨u5, qdupS', hcoverLine⟩
  rcases Line.of_run_cons hcoverLine with ⟨u6, qdupC, hcoverLine⟩
  rcases Line.of_run_cons hcoverLine with ⟨u7', qltC, hnil⟩
  cases hnil
  have p1 : Sevm.argWord sevm 0 :: supplySlot :: [] <<+ u1.stack :=
    prefix_of_arg cp1 qarg
  have p2 : Sevm.argWord sevm 0 :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      u2.stack := prefix_of_dup_val qdupS (by show_nth) p1
  have p3 : sevm.caller.toB256 :: Sevm.argWord sevm 0 :: Sevm.argWord sevm 0 ::
      supplySlot :: [] <<+ u3.stack :=
    prefix_of_push (of_run_caller qcaller) p2
  rcases prefix_of_sload qsloadC p3 with ⟨callerShares, p4, hcallerLoad⟩
  have hstor3 : Devm.getStor pre = Devm.getStor u3 := by
    calc
      Devm.getStor pre = Devm.getStor u0 :=
        Line.of_inv Devm.getStor (by line_inv) hcacheInv
      _ = Devm.getStor u1 :=
        Line.of_inv Devm.getStor (by unfold arg cdl; line_inv) qarg
      _ = Devm.getStor u2 := Ninst.Hinv.inv qdupS
      _ = Devm.getStor u3 := Ninst.Hinv.inv qcaller
  have hcallerShares : callerShares =
      (Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 := by
    rw [hcallerLoad]
    change (Devm.getStor u3 sevm.currentTarget).get sevm.caller.toB256 = _
    rw [← hstor3]
  rw [hcallerShares] at p4
  have p5 : Sevm.argWord sevm 0 ::
      (Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 ::
      Sevm.argWord sevm 0 :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      u5.stack := prefix_of_dup_val qdupS' (by show_nth) p4
  have p6 : (Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 ::
      Sevm.argWord sevm 0 ::
      (Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 ::
      Sevm.argWord sevm 0 :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      u6.stack := prefix_of_dup_val qdupC (by show_nth) p5
  have p7 : ((Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 <?
      Sevm.argWord sevm 0) ::
      (Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 ::
      Sevm.argWord sevm 0 :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      u7.stack := prefix_of_lt qltC p6
  rcases of_run_branch_revert hcoverBranch with ⟨u8, hcoverPop, hcoverSuccess⟩
  have hcoverFlag : (Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 <?
      Sevm.argWord sevm 0 = 0 := (popBurn_pref hcoverPop p7).1.symm
  have hcover : Sevm.argWord sevm 0 ≤
      (Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 := by
    apply B256.not_lt.mp
    intro hlt
    have hone : (Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 <?
        Sevm.argWord sevm 0 = 1 := by simp [B256.ltCheck, hlt]
    exact B256.zero_ne_one (hone.symm.trans hcoverFlag).symm
  have p8 : (Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 ::
      Sevm.argWord sevm 0 :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      u8.stack := (popBurn_pref hcoverPop p7).2
  rcases of_run_prepend [sub, caller, sstore] _ hcoverSuccess with
    ⟨u11, hcallerStoreLine, hrest⟩
  have hcallerStoreInv := hcallerStoreLine
  rcases Line.of_run_cons hcallerStoreLine with ⟨u9, qsub, hcallerStoreLine⟩
  rcases Line.of_run_cons hcallerStoreLine with ⟨u10, qcaller', hcallerStoreLine⟩
  rcases Line.of_run_cons hcallerStoreLine with ⟨u11', qstoreC, hnil⟩
  cases hnil
  have p9 : ((Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 -
      Sevm.argWord sevm 0) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      u9.stack := prefix_of_sub qsub p8
  have p10 : sevm.caller.toB256 ::
      ((Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 -
        Sevm.argWord sevm 0) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      u10.stack := prefix_of_push (of_run_caller qcaller') p9
  have hstoreC := sstore_getStor_set qstoreC p10
  have p11 : Sevm.argWord sevm 0 :: supplySlot :: [] <<+ u11.stack :=
    prefix_of_sstore qstoreC p10
  rcases of_run_prepend [selfbalance, dup 0, dup 3, pushB256 130, shr, lt] _ hrest with
    ⟨v6, hbalanceLine, hbalanceBranch⟩
  have hbalanceInv := hbalanceLine
  rcases Line.of_run_cons hbalanceLine with ⟨v1, qbalance, hbalanceLine⟩
  rcases Line.of_run_cons hbalanceLine with ⟨v2, qdupB, hbalanceLine⟩
  rcases Line.of_run_cons hbalanceLine with ⟨v3, qdupU, hbalanceLine⟩
  rcases Line.of_run_cons hbalanceLine with ⟨v4, q130, hbalanceLine⟩
  rcases Line.of_run_cons hbalanceLine with ⟨v5, qshr, hbalanceLine⟩
  rcases Line.of_run_cons hbalanceLine with ⟨v6', qltB, hnil⟩
  cases hnil
  have hbal11 : Devm.getBal pre = Devm.getBal u11 := by
    calc
      Devm.getBal pre = Devm.getBal u0 :=
        Line.of_inv Devm.getBal (by line_inv) hcacheInv
      _ = Devm.getBal u1 :=
        Line.of_inv Devm.getBal (by unfold arg cdl; line_inv) qarg
      _ = Devm.getBal u7 := Line.of_inv Devm.getBal (by line_inv) hcoverInv
      _ = Devm.getBal u8 := PopBurn.Inv.inv hcoverPop
      _ = Devm.getBal u11 := Line.of_inv Devm.getBal (by line_inv) hcallerStoreInv
  have r1 : Devm.getBal pre sevm.currentTarget :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      v1.stack := by
    have hpush := prefix_of_push (of_run_selfbalance qbalance) p11
    rw [← congrFun hbal11 sevm.currentTarget] at hpush
    exact hpush
  have r2 : Devm.getBal pre sevm.currentTarget :: Devm.getBal pre sevm.currentTarget ::
      Sevm.argWord sevm 0 :: supplySlot :: [] <<+ v2.stack :=
    prefix_of_dup_val qdupB (by show_nth) r1
  have r3 : supplySlot :: Devm.getBal pre sevm.currentTarget ::
      Devm.getBal pre sevm.currentTarget :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      v3.stack := prefix_of_dup_val qdupU (by show_nth) r2
  have r4 : (130 : B256) :: supplySlot :: Devm.getBal pre sevm.currentTarget ::
      Devm.getBal pre sevm.currentTarget :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      v4.stack := prefix_of_push (of_run_pushB256 q130) r3
  have h130 : supplySlot >>> (130 : B256).toNat = B256.shiftRight B256.max 130 := by
    rfl
  have r5 : B256.shiftRight B256.max 130 :: Devm.getBal pre sevm.currentTarget ::
      Devm.getBal pre sevm.currentTarget :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      v5.stack := by
    simpa only [h130] using prefix_of_shr qshr r4
  have r6 : (B256.shiftRight B256.max 130 <? Devm.getBal pre sevm.currentTarget) ::
      Devm.getBal pre sevm.currentTarget :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      v6.stack := prefix_of_lt qltB r5
  rcases of_run_branch_revert hbalanceBranch with ⟨v7, hbalancePop, hbalanceSuccess⟩
  have hBraw : B256.shiftRight B256.max 130 <? Devm.getBal pre sevm.currentTarget = 0 :=
    (popBurn_pref hbalancePop r6).1.symm
  have hBcap : B256.shiftRight B256.max 130 = maxBalance := by decide +kernel
  have hbalance : Devm.getBal pre sevm.currentTarget ≤ maxBalance := by
    apply B256.not_lt.mp
    intro hlt
    have hone : B256.shiftRight B256.max 130 <? Devm.getBal pre sevm.currentTarget = 1 := by
      rw [hBcap]
      simp [B256.ltCheck, hlt]
    exact B256.zero_ne_one (hone.symm.trans hBraw).symm
  have r7 : Devm.getBal pre sevm.currentTarget :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      v7.stack := by
    rw [hBcap] at r6
    have hzero : maxBalance <? Devm.getBal pre sevm.currentTarget = 0 := by
      simpa only [hBcap] using hBraw
    rw [hzero] at r6
    exact (popBurn_pref hbalancePop r6).2
  rcases of_run_prepend [pushB256 1, add, dup 1, mul, dup 2, sload,
    dup 0, pushB256 offset, add, swap 1, dup 2, swap 0, div,
    dup 3, dup 2, sub] _ hbalanceSuccess with ⟨w16, hmathLine, hrest⟩
  have hmathInv := hmathLine
  rcases Line.of_run_cons hmathLine with ⟨w1, a1, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w2, a2, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w3, a3, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w4, a4, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w5, a5, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w6, a6, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w7, a7, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w8, a8, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w9, a9, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w10, a10, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w11, a11, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w12, a12, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w13, a13, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w14, a14, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w15, a15, hmathLine⟩
  rcases Line.of_run_cons hmathLine with ⟨w16', a16, hnil⟩
  cases hnil
  let B := Devm.getBal pre sevm.currentTarget
  let stor := Devm.getStor pre sevm.currentTarget
  let S := stor.get supplySlot
  let p := Sevm.argWord sevm 0 * (B + 1) / (S + offset)
  have m1 : (1 : B256) :: B :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w1.stack := by
    simpa only [B, List.cons_append, List.nil_append] using
      prefix_of_push (of_run_pushB256 a1) r7
  have m2 : (B + 1) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w2.stack := by
    have hadd : (1 : B256) + B = B + 1 := B256.add_comm
    rw [← hadd]
    exact prefix_of_add a2 m1
  have m3 : Sevm.argWord sevm 0 :: (B + 1) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      w3.stack := prefix_of_dup_val a3 (by show_nth) m2
  have m4 : (Sevm.argWord sevm 0 * (B + 1)) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      w4.stack := prefix_of_mul a4 m3
  have m5 : supplySlot :: (Sevm.argWord sevm 0 * (B + 1)) :: Sevm.argWord sevm 0 ::
      supplySlot :: [] <<+ w5.stack := prefix_of_dup_val a5 (by show_nth) m4
  rcases prefix_of_sload a6 m5 with ⟨supply, m6, hsupplyLoad⟩
  have hstorW5 : Devm.getStor u11 = Devm.getStor w5 := by
    calc
      Devm.getStor u11 = Devm.getStor v6 :=
        Line.of_inv Devm.getStor (by line_inv) hbalanceInv
      _ = Devm.getStor v7 := PopBurn.Inv.inv hbalancePop
      _ = Devm.getStor w1 := Ninst.Hinv.inv a1
      _ = Devm.getStor w2 := Ninst.Hinv.inv a2
      _ = Devm.getStor w3 := Ninst.Hinv.inv a3
      _ = Devm.getStor w4 := Ninst.Hinv.inv a4
      _ = Devm.getStor w5 := Ninst.Hinv.inv a5
  have hstorPreU10 : Devm.getStor pre = Devm.getStor u10 := by
    calc
      Devm.getStor pre = Devm.getStor u0 :=
        Line.of_inv Devm.getStor (by line_inv) hcacheInv
      _ = Devm.getStor u1 :=
        Line.of_inv Devm.getStor (by unfold arg cdl; line_inv) qarg
      _ = Devm.getStor u7 := Line.of_inv Devm.getStor (by line_inv) hcoverInv
      _ = Devm.getStor u8 := PopBurn.Inv.inv hcoverPop
      _ = Devm.getStor u9 := Ninst.Hinv.inv qsub
      _ = Devm.getStor u10 := Ninst.Hinv.inv qcaller'
  have hsupply : supply = S := by
    rw [hsupplyLoad]
    change (Devm.getStor w5 sevm.currentTarget).get supplySlot = S
    rw [← hstorW5, hstoreC]
    rw [Stor.get_set_ne _ (caller_ne_supplySlot sevm.caller)]
    rw [← congrFun hstorPreU10 sevm.currentTarget]
  rw [hsupply] at m6
  have m7 : S :: S :: (Sevm.argWord sevm 0 * (B + 1)) :: Sevm.argWord sevm 0 ::
      supplySlot :: [] <<+ w7.stack := prefix_of_dup_val a7 (by show_nth) m6
  have m8 : offset :: S :: S :: (Sevm.argWord sevm 0 * (B + 1)) ::
      Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w8.stack :=
    prefix_of_push (of_run_pushB256 a8) m7
  have m9 : (S + offset) :: S :: (Sevm.argWord sevm 0 * (B + 1)) ::
      Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w9.stack := by
    have hoff : offset + S = S + offset := B256.add_comm
    rw [← hoff]
    exact prefix_of_add a9 m8
  have m10 : (Sevm.argWord sevm 0 * (B + 1)) :: S :: (S + offset) ::
      Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w10.stack := by
    have hswap : Stack.Swap (1 : Fin 16).val
        ((S + offset) :: S :: (Sevm.argWord sevm 0 * (B + 1)) ::
          Sevm.argWord sevm 0 :: supplySlot :: [])
        ((Sevm.argWord sevm 0 * (B + 1)) :: S :: (S + offset) ::
          Sevm.argWord sevm 0 :: supplySlot :: []) := by
      apply Stack.swapCore_succ
      apply Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap a10) m9
  have m11 : (S + offset) :: (Sevm.argWord sevm 0 * (B + 1)) :: S ::
      (S + offset) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w11.stack :=
    prefix_of_dup_val a11 (by show_nth) m10
  have m12 : (Sevm.argWord sevm 0 * (B + 1)) :: (S + offset) :: S ::
      (S + offset) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w12.stack := by
    have hswap : Stack.Swap (0 : Fin 16).val
        ((S + offset) :: (Sevm.argWord sevm 0 * (B + 1)) :: S ::
          (S + offset) :: Sevm.argWord sevm 0 :: supplySlot :: [])
        ((Sevm.argWord sevm 0 * (B + 1)) :: (S + offset) :: S ::
          (S + offset) :: Sevm.argWord sevm 0 :: supplySlot :: []) := by
      apply Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap a12) m11
  have m13 : p :: S :: (S + offset) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      w13.stack := by
    simpa only [p] using prefix_of_div a13 m12
  have m14 : Sevm.argWord sevm 0 :: p :: S :: (S + offset) ::
      Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w14.stack :=
    prefix_of_dup_val a14 (by show_nth) m13
  have m15 : S :: Sevm.argWord sevm 0 :: p :: S :: (S + offset) ::
      Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w15.stack :=
    prefix_of_dup_val a15 (by show_nth) m14
  have m16 : (S - Sevm.argWord sevm 0) :: p :: S :: (S + offset) ::
      Sevm.argWord sevm 0 :: supplySlot :: [] <<+ w16.stack :=
    prefix_of_sub a16 m15
  rcases of_run_prepend [dup 5, sstore, dup 0] _ hrest with ⟨z3, hsupplyStoreLine, hrest⟩
  have hsupplyStoreInv := hsupplyStoreLine
  rcases Line.of_run_cons hsupplyStoreLine with ⟨z1, b1, hsupplyStoreLine⟩
  rcases Line.of_run_cons hsupplyStoreLine with ⟨z2, b2, hsupplyStoreLine⟩
  rcases Line.of_run_cons hsupplyStoreLine with ⟨z3', b3, hnil⟩
  cases hnil
  have n1 : supplySlot :: (S - Sevm.argWord sevm 0) :: p :: S :: (S + offset) ::
      Sevm.argWord sevm 0 :: supplySlot :: [] <<+ z1.stack :=
    prefix_of_dup_val b1 (by show_nth) m16
  have hstoreS := sstore_getStor_set b2 n1
  have n2 : p :: S :: (S + offset) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      z2.stack := prefix_of_sstore b2 n1
  have n3 : p :: p :: S :: (S + offset) :: Sevm.argWord sevm 0 :: supplySlot :: [] <<+
      z3.stack := prefix_of_dup_val b3 (by show_nth) n2
  rcases of_run_prepend sendToCaller _ hrest with ⟨callPost, hsend, htail⟩
  rcases sendToCaller_frame n3 hsend with
    ⟨callPre, gasWord, hstack, hcall, hstorSend, hbalSend, hcodeSend,
      hlogsSend, houtSend, hmemSend⟩
  have hstorU11W16 : Devm.getStor u11 = Devm.getStor w16 := by
    calc
      Devm.getStor u11 = Devm.getStor v6 :=
        Line.of_inv Devm.getStor (by line_inv) hbalanceInv
      _ = Devm.getStor v7 := PopBurn.Inv.inv hbalancePop
      _ = Devm.getStor w16 := Line.of_inv Devm.getStor (by line_inv) hmathInv
  have hbalPreZ3 : Devm.getBal pre = Devm.getBal z3 := by
    calc
      Devm.getBal pre = Devm.getBal u0 := Line.of_inv Devm.getBal (by line_inv) hcacheInv
      _ = Devm.getBal u1 := Line.of_inv Devm.getBal (by unfold arg cdl; line_inv) qarg
      _ = Devm.getBal u7 := Line.of_inv Devm.getBal (by line_inv) hcoverInv
      _ = Devm.getBal u8 := PopBurn.Inv.inv hcoverPop
      _ = Devm.getBal u11 := Line.of_inv Devm.getBal (by line_inv) hcallerStoreInv
      _ = Devm.getBal v6 := Line.of_inv Devm.getBal (by line_inv) hbalanceInv
      _ = Devm.getBal v7 := PopBurn.Inv.inv hbalancePop
      _ = Devm.getBal w16 := Line.of_inv Devm.getBal (by line_inv) hmathInv
      _ = Devm.getBal z3 := Line.of_inv Devm.getBal (by line_inv) hsupplyStoreInv
  have hcodePreZ3 : Devm.getCode pre = Devm.getCode z3 := by
    calc
      Devm.getCode pre = Devm.getCode u0 := Line.of_inv Devm.getCode (by line_inv) hcacheInv
      _ = Devm.getCode u1 := Line.of_inv Devm.getCode (by unfold arg cdl; line_inv) qarg
      _ = Devm.getCode u7 := Line.of_inv Devm.getCode (by line_inv) hcoverInv
      _ = Devm.getCode u8 := by funext a; exact getCode_eq_of_state_eq hcoverPop.state a
      _ = Devm.getCode u11 := Line.of_inv Devm.getCode (by line_inv) hcallerStoreInv
      _ = Devm.getCode v6 := Line.of_inv Devm.getCode (by line_inv) hbalanceInv
      _ = Devm.getCode v7 := by funext a; exact getCode_eq_of_state_eq hbalancePop.state a
      _ = Devm.getCode w16 := Line.of_inv Devm.getCode (by line_inv) hmathInv
      _ = Devm.getCode z3 := Line.of_inv Devm.getCode (by line_inv) hsupplyStoreInv
  have hlogsPreZ3 : pre.logs = z3.logs := by
    calc
      pre.logs = u0.logs := Line.of_inv Devm.logs (by line_inv) hcacheInv
      _ = u1.logs := Line.of_inv Devm.logs (by unfold arg cdl; line_inv) qarg
      _ = u7.logs := Line.of_inv Devm.logs (by line_inv) hcoverInv
      _ = u8.logs := hcoverPop.logs
      _ = u11.logs := Line.of_inv Devm.logs (by line_inv) hcallerStoreInv
      _ = v6.logs := Line.of_inv Devm.logs (by line_inv) hbalanceInv
      _ = v7.logs := hbalancePop.logs
      _ = w16.logs := Line.of_inv Devm.logs (by line_inv) hmathInv
      _ = z3.logs := Line.of_inv Devm.logs (by line_inv) hsupplyStoreInv
  have houtPreZ3 : pre.output = z3.output := by
    calc
      pre.output = u0.output := Line.of_inv Devm.output (by line_inv) hcacheInv
      _ = u1.output := Line.of_inv Devm.output (by unfold arg cdl; line_inv) qarg
      _ = u7.output := Line.of_inv Devm.output (by line_inv) hcoverInv
      _ = u8.output := hcoverPop.output
      _ = u11.output := Line.of_inv Devm.output (by line_inv) hcallerStoreInv
      _ = v6.output := Line.of_inv Devm.output (by line_inv) hbalanceInv
      _ = v7.output := hbalancePop.output
      _ = w16.output := Line.of_inv Devm.output (by line_inv) hmathInv
      _ = z3.output := Line.of_inv Devm.output (by line_inv) hsupplyStoreInv
  have hmemPreZ3 : pre.memory = z3.memory := by
    calc
      pre.memory = u0.memory := Line.of_inv Devm.memory (by line_inv) hcacheInv
      _ = u1.memory := Line.of_inv Devm.memory (by unfold arg cdl; line_inv) qarg
      _ = u7.memory := Line.of_inv Devm.memory (by line_inv) hcoverInv
      _ = u8.memory := hcoverPop.memory
      _ = u11.memory := Line.of_inv Devm.memory (by line_inv) hcallerStoreInv
      _ = v6.memory := Line.of_inv Devm.memory (by line_inv) hbalanceInv
      _ = v7.memory := hbalancePop.memory
      _ = w16.memory := Line.of_inv Devm.memory (by line_inv) hmathInv
      _ = z3.memory := Line.of_inv Devm.memory (by line_inv) hsupplyStoreInv
  refine ⟨callPre, callPost, ?_, hcall, ?_⟩
  · unfold WithdrawPreCallEffect
    dsimp
    refine ⟨hcover, hbalance, ?_, hbalSend.trans hbalPreZ3.symm,
      hcodeSend.trans hcodePreZ3.symm, hlogsSend.trans hlogsPreZ3.symm,
      houtSend.trans houtPreZ3.symm, hmemSend.trans hmemPreZ3.symm, ?_⟩
    · calc
        Devm.getStor callPre sevm.currentTarget = Devm.getStor z3 sevm.currentTarget :=
          congrFun hstorSend sevm.currentTarget
        _ = Devm.getStor z2 sevm.currentTarget :=
          (congrFun (Ninst.Hinv.inv (f := Devm.getStor) b3) sevm.currentTarget).symm
        _ = (Devm.getStor z1 sevm.currentTarget).set supplySlot
            (S - Sevm.argWord sevm 0) := hstoreS
        _ = (Devm.getStor w16 sevm.currentTarget).set supplySlot
            (S - Sevm.argWord sevm 0) := by
          rw [Ninst.Hinv.inv (f := Devm.getStor) b1]
        _ = (Devm.getStor u11 sevm.currentTarget).set supplySlot
            (S - Sevm.argWord sevm 0) := by
          rw [hstorU11W16]
        _ = ((Devm.getStor u10 sevm.currentTarget).set sevm.caller.toB256
              ((Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 -
                Sevm.argWord sevm 0)).set supplySlot (S - Sevm.argWord sevm 0) := by
          rw [hstoreC]
        _ = ((Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
              ((Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 -
                Sevm.argWord sevm 0)).set supplySlot
              ((Devm.getStor pre sevm.currentTarget).get supplySlot - Sevm.argWord sevm 0) := by
          rw [← congrFun hstorPreU10 sevm.currentTarget]
    · exact ⟨gasWord, hstack⟩
  · simpa only [withdrawAfterCall] using htail

/-- An entered, successful value-CALL whose success word has been consumed
before the caller's return suffix.  The carrier records the entered child
boundary without imposing a simple callback-final storage delta. -/
def AcceptedPayout (sevm : Sevm) (p : B256)
    (callPre callPost guardPost returnPre : Devm) : Prop :=
  ∃ (gasWord : B256) (xs : Stack) (parent child : Devm) (xl : Xlot)
    (delegated : Bool) (nextAddress : Adr) (code : ByteArray) (avail pc : Nat),
    (gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs) <<+
      callPre.stack ∧
    Ninst.Run sevm callPre call callPost ∧
    Devm.PopBurn [1] callPost guardPost ∧
    Devm.Burn guardPost returnPre ∧
    Ninst.StepRun pc sevm callPre call xl (.ok callPost) ∧
    0 < sevm.depth ∧
    callPre.stack = gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 ::
      parent.stack ∧
    parent.state = callPre.state ∧
    parent.memory = callPre.memory.extends [(0, 0), (0, 0)] ∧
    parent.logs = callPre.logs ∧
    parent.output = callPre.output ∧
    ((getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) = none ∧
        nextAddress = sevm.caller.toB256.toAdr ∧
        code = callPre.getCode sevm.caller.toB256.toAdr ∧ delegated = false) ∨
      (∃ d, getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) = some d ∧
        nextAddress = d ∧ code = callPre.getCode d ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg sevm parent
        (min gasWord.toNat (except64th avail) +
          (if p.toNat = 0 then 0 else gCallStipend))
        p sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
        ((callPre.memory.read 0 0).1) code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    (Resume.call parent 0 0).run (.ok child) = .ok callPost ∧
    callPost.state = child.state ∧
    callPost.returnData = child.output ∧
    callPost.memory = parent.memory.write 0 (child.output.take 0) ∧
    callPost.stack = (1 : B256) :: parent.stack

/-- Full successful withdrawal evidence: settled outer pre-CALL state, an
accepted payout CALL, and the exact returned payout word. -/
def WithdrawPaysExactly (sevm : Sevm) (pre post : Devm) : Prop :=
  let s := Sevm.argWord sevm 0
  let B := Devm.getBal pre sevm.currentTarget
  let S := (Devm.getStor pre sevm.currentTarget).get supplySlot
  let p := s * (B + 1) / (S + offset)
  ∃ callPre callPost guardPost returnPre,
    WithdrawPreCallEffect sevm pre callPre ∧
    AcceptedPayout sevm p callPre callPost guardPost returnPre ∧
    Devm.getStor post = Devm.getStor callPost ∧
    Devm.getBal post = Devm.getBal callPost ∧
    ReturnsWord p post

theorem withdraw_pays_exactly
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre withdraw post) :
    WithdrawPaysExactly sevm pre post := by
  unfold WithdrawPaysExactly
  dsimp
  let B := Devm.getBal pre sevm.currentTarget
  let S := (Devm.getStor pre sevm.currentTarget).get supplySlot
  let p := Sevm.argWord sevm 0 * (B + 1) / (S + offset)
  change ∃ callPre callPost guardPost returnPre,
    WithdrawPreCallEffect sevm pre callPre ∧
    AcceptedPayout sevm p callPre callPost guardPost returnPre ∧
    Devm.getStor post = Devm.getStor callPost ∧
    Devm.getBal post = Devm.getBal callPost ∧
    ReturnsWord p post
  rcases withdraw_settles_before_call run with
    ⟨callPre, callPost, hpreRaw, hcall, htail⟩
  simp only [withdrawAfterCall] at htail
  have hstorTail : Devm.getStor callPost = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) htail
  have hbalTail : Devm.getBal callPost = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) htail
  rcases of_run_branch htail with
    ⟨_, hzero, hrev⟩ | ⟨w, guardPost, returnPre, hw, hpop, hburn, hreturn⟩
  · exact (not_run_revert hrev).elim
  have hpre := hpreRaw
  unfold WithdrawPreCallEffect at hpre
  dsimp at hpre
  rcases hpre with ⟨hcover, hbalance, hstor, hbal, hcode, hlogs, hout, hmem,
    gasWord, hstack⟩
  have hstack' :
      (gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 ::
        p :: S :: (S + offset) :: Sevm.argWord sevm 0 :: supplySlot :: []) <<+
        callPre.stack := by
    simpa only [p, B, S] using hstack
  rcases of_run_call_val_with_depth_frame hstack' hcall with hfailed | hentered
  · exact (hw (popBurn_pref hpop hfailed.1).1).elim
  rcases hentered with
    ⟨parent, child, xl, delegated, nextAddress, code, avail, pc, hstep, hdepth,
      hstackEq, hparentState, hparentMemory, hparentLogs, hparentOutput,
      hdelegated, hfilled, hmessage, hclean, hresume, hpostState,
      hpostReturnData, hpostMemory, hpostStack⟩
  have hpostPrefix : (1 : B256) :: p :: S :: (S + offset) ::
      Sevm.argWord sevm 0 :: supplySlot :: [] <<+ callPost.stack := by
    rw [hpostStack]
    apply pref_cons
    rw [hstackEq] at hstack'
    exact cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
      (cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
        (cons_pref_cons_inv hstack'))))))
  have hpop1 : Devm.PopBurn [1] callPost guardPost := by
    have hwone : w = 1 := (popBurn_pref hpop hpostPrefix).1
    subst w
    exact hpop
  have hguardPrefix : p :: S :: (S + offset) :: Sevm.argWord sevm 0 ::
      supplySlot :: [] <<+ guardPost.stack :=
    (popBurn_pref hpop1 hpostPrefix).2
  have hreturnPrefix : p :: S :: (S + offset) :: Sevm.argWord sevm 0 ::
      supplySlot :: [] <<+ returnPre.stack := by
    rw [← hburn.stack]
    exact hguardPrefix
  refine ⟨callPre, callPost, guardPost, returnPre, hpreRaw, ?_, ?_, ?_, ?_⟩
  · unfold AcceptedPayout
    exact ⟨gasWord, p :: S :: (S + offset) :: Sevm.argWord sevm 0 :: supplySlot :: [],
      parent, child, xl, delegated, nextAddress, code, avail, pc,
      hstack', hcall, hpop1, hburn, hstep, hdepth, hstackEq, hparentState,
      hparentMemory, hparentLogs, hparentOutput, hdelegated, hfilled, hmessage,
      hclean, hresume, hpostState, hpostReturnData, hpostMemory, hpostStack⟩
  · exact hstorTail.symm
  · exact hbalTail.symm
  · exact (returnsWord_of_storeReturn hreturnPrefix hreturn).1

end Prorata

end Blanc
