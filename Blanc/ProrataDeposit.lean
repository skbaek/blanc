-- ProrataDeposit.lean : exact successful PRORATA deposit effects.

import Blanc.ProrataArithmetic
import Blanc.ProrataFunctional

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Prorata

private instance : Rinst.Hinv Devm.logs Rinst.callvalue := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

private instance : Rinst.Hinv Devm.logs Rinst.selfbalance := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

private instance : Rinst.Hinv Devm.logs Rinst.shr := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

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

/-- Exact frame-local effect of a successful selected `deposit` body. -/
def DepositEffect (sevm : Sevm) (pre post : Devm) : Prop :=
  let stor := Devm.getStor pre sevm.currentTarget
  let bIn := Devm.getBal pre sevm.currentTarget
  let B0 := bIn - sevm.value
  let S := stor.get supplySlot
  let m := sevm.value * (S + offset) / (B0 + 1)
  sevm.value ≤ maxValue ∧
    B0 ≤ maxBalance ∧
    S + m ≤ maxSupply ∧
    Devm.getStor post sevm.currentTarget =
      (stor.set supplySlot (S + m)).set sevm.caller.toB256
        (stor.get sevm.caller.toB256 + m) ∧
    Devm.getBal post = Devm.getBal pre ∧
    Devm.getCode post = Devm.getCode pre ∧
    post.logs = pre.logs ∧
    ReturnsWord m post

private def depositTail : Func :=
  pushB256 1 ::: add :::
  dup 3 ::: sload :::
  dup 0 ::: pushB256 offset ::: add :::
  callvalue ::: mul :::
  dup 2 ::: swap 0 ::: div :::
  dup 1 ::: dup 1 ::: add :::
  dup 0 ::: dup 6 ::: lt :::
  .revert <?>
  dup 6 ::: sstore :::
  dup 0 ::: caller ::: sload ::: add :::
  caller ::: sstore :::
  mstoreAt 0 +++ returnMemoryRange 0 32

private theorem deposit_guard_prefix
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre deposit post) :
    ∃ after,
      sevm.value ≤ maxValue ∧
      Devm.getBal pre sevm.currentTarget - sevm.value ≤ maxBalance ∧
      (Devm.getBal pre sevm.currentTarget - sevm.value) :: 0 ::
        maxBalance :: supplySlot :: [] <<+ after.stack ∧
      Devm.getStor pre = Devm.getStor after ∧
      Devm.getBal pre = Devm.getBal after ∧
      Devm.getCode pre = Devm.getCode after ∧
      pre.logs = after.logs ∧
      Func.Run fs sevm after depositTail post := by
  simp only [deposit] at run
  rcases of_run_prepend pushMaxAndCap _ run with ⟨s0, hcache, hrest⟩
  rcases of_run_prepend [callvalue, dup 1, pushB256 30, shr, lt,
    callvalue, selfbalance, sub, dup 0, dup 3, lt, dup 2, add] _ hrest with
    ⟨s13, hline, hbranch⟩
  have hcacheInv := hcache
  have hlineInv := hline
  have hbal0 : Devm.getBal s0 = Devm.getBal pre :=
    (Line.of_inv Devm.getBal (by line_inv) hcache).symm
  unfold pushMaxAndCap at hcache
  rcases Line.of_run_cons hcache with ⟨c1, q0, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c2, qnot, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c3, qdup, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c4, q130, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c5, qshr, hnil⟩
  cases hnil
  have hU : ~~~(0 : B256) = B256.max := by decide +kernel
  have h130 : B256.max >>> (130 : B256).toNat = B256.shiftRight B256.max 130 := by
    rfl
  have h30 : B256.shiftRight B256.max 130 >>> (30 : B256).toNat =
      B256.shiftRight (B256.shiftRight B256.max 130) 30 := by
    rfl
  have cp0 : (0 : B256) :: [] <<+ c1.stack :=
    prefix_of_push (of_run_pushB256 q0) nil_pref
  have cp1 : B256.max :: [] <<+ c2.stack := by
    rw [← hU]
    exact prefix_of_not qnot cp0
  have cp2 : B256.max :: B256.max :: [] <<+ c3.stack :=
    prefix_of_dup_val qdup (by show_nth) cp1
  have cp3 : (130 : B256) :: B256.max :: B256.max :: [] <<+ c4.stack :=
    prefix_of_push (of_run_pushB256 q130) cp2
  have cp4 : B256.shiftRight B256.max 130 :: B256.max :: [] <<+ s0.stack := by
    simpa only [h130] using prefix_of_shr qshr cp3
  rcases Line.of_run_cons hline with ⟨d1, qvalue1, hline⟩
  rcases Line.of_run_cons hline with ⟨d2, qdupM, hline⟩
  rcases Line.of_run_cons hline with ⟨d3, q30, hline⟩
  rcases Line.of_run_cons hline with ⟨d4, qshrM, hline⟩
  rcases Line.of_run_cons hline with ⟨d5, qltA, hline⟩
  rcases Line.of_run_cons hline with ⟨d6, qvalue2, hline⟩
  rcases Line.of_run_cons hline with ⟨d7, qbalance, hline⟩
  rcases Line.of_run_cons hline with ⟨d8, qsub, hline⟩
  rcases Line.of_run_cons hline with ⟨d9, qdupB, hline⟩
  rcases Line.of_run_cons hline with ⟨d10, qdupCap, hline⟩
  rcases Line.of_run_cons hline with ⟨d11, qltB, hline⟩
  rcases Line.of_run_cons hline with ⟨d12, qdupA, hline⟩
  rcases Line.of_run_cons hline with ⟨d13, qadd, hnil⟩
  cases hnil
  have hd1 : Devm.getBal s0 = Devm.getBal d1 := Ninst.Hinv.inv qvalue1
  have hd2 : Devm.getBal d1 = Devm.getBal d2 := Ninst.Hinv.inv qdupM
  have hd3 : Devm.getBal d2 = Devm.getBal d3 := Ninst.Hinv.inv q30
  have hd4 : Devm.getBal d3 = Devm.getBal d4 := Ninst.Hinv.inv qshrM
  have hd5 : Devm.getBal d4 = Devm.getBal d5 := Ninst.Hinv.inv qltA
  have hd6 : Devm.getBal d5 = Devm.getBal d6 := Ninst.Hinv.inv qvalue2
  have hbal6 : Devm.getBal d6 = Devm.getBal pre :=
    hd6.symm.trans (hd5.symm.trans (hd4.symm.trans
      (hd3.symm.trans (hd2.symm.trans (hd1.symm.trans hbal0)))))
  have p1 : sevm.value :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+
      d1.stack :=
    prefix_of_push (of_run_callvalue qvalue1) cp4
  have p2 : B256.shiftRight B256.max 130 :: sevm.value ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d2.stack :=
    prefix_of_dup_val qdupM (by show_nth) p1
  have p3 : (30 : B256) :: B256.shiftRight B256.max 130 :: sevm.value ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d3.stack :=
    prefix_of_push (of_run_pushB256 q30) p2
  have p4 : B256.shiftRight (B256.shiftRight B256.max 130) 30 :: sevm.value ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d4.stack := by
    simpa only [h30] using prefix_of_shr qshrM p3
  have p5 : (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d5.stack :=
    prefix_of_lt qltA p4
  have p6 : sevm.value :: (B256.shiftRight (B256.shiftRight B256.max 130) 30 <?
      sevm.value) :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d6.stack :=
    prefix_of_push (of_run_callvalue qvalue2) p5
  have p7 : Devm.getBal pre sevm.currentTarget :: sevm.value ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d7.stack := by
    rw [← hbal6]
    exact prefix_of_push (of_run_selfbalance qbalance) p6
  have p8 : (Devm.getBal pre sevm.currentTarget - sevm.value) ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d8.stack :=
    prefix_of_sub qsub p7
  have p9 : (Devm.getBal pre sevm.currentTarget - sevm.value) ::
      (Devm.getBal pre sevm.currentTarget - sevm.value) ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d9.stack :=
    prefix_of_dup_val qdupB (by show_nth) p8
  have p10 : B256.shiftRight B256.max 130 ::
      (Devm.getBal pre sevm.currentTarget - sevm.value) ::
      (Devm.getBal pre sevm.currentTarget - sevm.value) ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d10.stack :=
    prefix_of_dup_val qdupCap (by show_nth) p9
  have p11 : (B256.shiftRight B256.max 130 <?
      (Devm.getBal pre sevm.currentTarget - sevm.value)) ::
      (Devm.getBal pre sevm.currentTarget - sevm.value) ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d11.stack :=
    prefix_of_lt qltB p10
  have p12 : (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) ::
      (B256.shiftRight B256.max 130 <?
        (Devm.getBal pre sevm.currentTarget - sevm.value)) ::
      (Devm.getBal pre sevm.currentTarget - sevm.value) ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d12.stack :=
    prefix_of_dup_val qdupA (by show_nth) p11
  have p13 :
      ((B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) +
        (B256.shiftRight B256.max 130 <?
          (Devm.getBal pre sevm.currentTarget - sevm.value))) ::
      (Devm.getBal pre sevm.currentTarget - sevm.value) ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? sevm.value) ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ s13.stack :=
    prefix_of_add qadd p12
  rcases of_run_branch_revert hbranch with ⟨after, hpop, hsuccess⟩
  have hzero := (popBurn_pref hpop p13).1.symm
  have hM : B256.shiftRight B256.max 130 = maxBalance := by decide +kernel
  have hV : B256.shiftRight maxBalance 30 = maxValue := by decide +kernel
  rw [hM, hV] at hzero
  have ha : ¬ maxValue < sevm.value := by
    intro ha
    by_cases hb : maxBalance < Devm.getBal pre sevm.currentTarget - sevm.value
    · have hz : (1 : B256) + 1 = 0 := by
        simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (1 : B256) + 1 ≠ 0) hz
    · have hz : (1 : B256) + 0 = 0 := by
        simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (1 : B256) + 0 ≠ 0) hz
  have hb : ¬ maxBalance < Devm.getBal pre sevm.currentTarget - sevm.value := by
    intro hb
    by_cases ha : maxValue < sevm.value
    · have hz : (1 : B256) + 1 = 0 := by
        simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (1 : B256) + 1 ≠ 0) hz
    · have hz : (0 : B256) + 1 = 0 := by
        simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (0 : B256) + 1 ≠ 0) hz
  have hfa : (maxValue <? sevm.value) = 0 := by
    simp only [B256.ltCheck]
    exact if_neg ha
  have hpAfter :
      (Devm.getBal pre sevm.currentTarget - sevm.value) :: 0 ::
        maxBalance :: supplySlot :: [] <<+ after.stack := by
    simpa only [hM, hV, hfa, supplySlot] using (popBurn_pref hpop p13).2
  refine ⟨after, B256.not_lt.mp ha, B256.not_lt.mp hb, hpAfter, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact (Line.of_inv Devm.getStor (by line_inv) hcacheInv).trans
      ((Line.of_inv Devm.getStor (by line_inv) hlineInv).trans (PopBurn.Inv.inv hpop))
  · exact (Line.of_inv Devm.getBal (by line_inv) hcacheInv).trans
      ((Line.of_inv Devm.getBal (by line_inv) hlineInv).trans (PopBurn.Inv.inv hpop))
  · have hcodePop : Devm.getCode s13 = Devm.getCode after := by
      funext a
      simp [Devm.getCode, Devm.getAcct]
      rw [hpop.state]
    exact (Line.of_inv Devm.getCode (by line_inv) hcacheInv).trans
      ((Line.of_inv Devm.getCode (by line_inv) hlineInv).trans hcodePop)
  · exact (Line.of_inv Devm.logs (by line_inv) hcacheInv).trans
      ((Line.of_inv Devm.logs (by line_inv) hlineInv).trans hpop.logs)
  · simpa only [depositTail] using hsuccess

private theorem deposit_pre_guards
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre deposit post) :
    sevm.value ≤ maxValue ∧
      Devm.getBal pre sevm.currentTarget - sevm.value ≤ maxBalance := by
  rcases deposit_guard_prefix run with ⟨-, ha, hb, -⟩
  exact ⟨ha, hb⟩

private theorem deposit_value_guard
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre deposit post) :
    sevm.value ≤ maxValue :=
  (deposit_pre_guards run).1

/-- Exact successful `deposit` body effect. -/
theorem deposit_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre deposit post) :
    DepositEffect sevm pre post := by
  unfold DepositEffect
  rcases deposit_guard_prefix run with
    ⟨s0, hvalue, hbalance, hp0, hstor0, hbal0, hcode0, hlogs0, htail⟩
  let B0 := Devm.getBal pre sevm.currentTarget - sevm.value
  let S := (Devm.getStor pre sevm.currentTarget).get supplySlot
  let m := sevm.value * (S + offset) / (B0 + 1)
  change sevm.value ≤ maxValue ∧ B0 ≤ maxBalance ∧ S + m ≤ maxSupply ∧
    Devm.getStor post sevm.currentTarget =
      ((Devm.getStor pre sevm.currentTarget).set supplySlot (S + m)).set
        sevm.caller.toB256 ((Devm.getStor pre sevm.currentTarget).get
          sevm.caller.toB256 + m) ∧
    Devm.getBal post = Devm.getBal pre ∧ Devm.getCode post = Devm.getCode pre ∧
    post.logs = pre.logs ∧ ReturnsWord m post
  simp only [depositTail] at htail
  rcases of_run_prepend [pushB256 1, add, dup 3] _ htail with
    ⟨s3, hfirst, hrest⟩
  have hfirstInv := hfirst
  rcases of_run_prepend [sload, dup 0, pushB256 offset, add, callvalue, mul,
    dup 2, swap 0, div, dup 1, dup 1, add, dup 0, dup 6, lt] _ hrest with
    ⟨s18, hline, hbranch⟩
  have hlineInv := hline
  rcases Line.of_run_cons hfirst with ⟨s1, q1, hfirst⟩
  rcases Line.of_run_cons hfirst with ⟨s2, q2, hfirst⟩
  rcases Line.of_run_cons hfirst with ⟨s3', q3, hnil⟩
  cases hnil
  have p1 : (1 : B256) :: B0 :: 0 :: maxBalance :: supplySlot :: [] <<+
      s1.stack := by
    simpa only [B0, List.cons_append, List.nil_append] using
      prefix_of_push (of_run_pushB256 q1) hp0
  have p2 : (1 + B0) :: 0 :: maxBalance :: supplySlot :: [] <<+ s2.stack :=
    prefix_of_add q2 p1
  have hadd : (1 : B256) + B0 = B0 + 1 := B256.add_comm
  have p3 : supplySlot :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s3.stack := by
    rw [← hadd]
    exact prefix_of_dup_val q3 (by show_nth) p2
  have hstor3 : Devm.getStor s0 = Devm.getStor s3 :=
    Line.of_inv Devm.getStor (by line_inv) hfirstInv
  rcases Line.of_run_cons hline with ⟨s4, q4, hline⟩
  rcases Line.of_run_cons hline with ⟨s5, q5, hline⟩
  rcases Line.of_run_cons hline with ⟨s6, q6, hline⟩
  rcases Line.of_run_cons hline with ⟨s7, q7, hline⟩
  rcases Line.of_run_cons hline with ⟨s8, q8, hline⟩
  rcases Line.of_run_cons hline with ⟨s9, q9, hline⟩
  rcases Line.of_run_cons hline with ⟨s10, q10, hline⟩
  rcases Line.of_run_cons hline with ⟨s11, q11, hline⟩
  rcases Line.of_run_cons hline with ⟨s12, q12, hline⟩
  rcases Line.of_run_cons hline with ⟨s13, q13, hline⟩
  rcases Line.of_run_cons hline with ⟨s14, q14, hline⟩
  rcases Line.of_run_cons hline with ⟨s15, q15, hline⟩
  rcases Line.of_run_cons hline with ⟨s16, q16, hline⟩
  rcases Line.of_run_cons hline with ⟨s17, q17, hline⟩
  rcases Line.of_run_cons hline with ⟨s18', q18, hnil⟩
  cases hnil
  rcases prefix_of_sload q4 p3 with ⟨supply, p4, hsupply⟩
  have hsupply' : supply = S := by
    rw [hsupply]
    change (Devm.getStor s3 sevm.currentTarget).get supplySlot = S
    rw [← hstor3, ← hstor0]
  rw [hsupply'] at p4
  have p5 : S :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s5.stack := prefix_of_dup_val q5 (by show_nth) p4
  have p6 : offset :: S :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s6.stack := prefix_of_push (of_run_pushB256 q6) p5
  have p7 : (S + offset) :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s7.stack := by
    have hoff : offset + S = S + offset := B256.add_comm
    rw [← hoff]
    exact prefix_of_add q7 p6
  have p8 : sevm.value :: (S + offset) :: S :: (B0 + 1) :: 0 :: maxBalance ::
      supplySlot :: [] <<+ s8.stack :=
    prefix_of_push (of_run_callvalue q8) p7
  have p9 : (sevm.value * (S + offset)) :: S :: (B0 + 1) :: 0 :: maxBalance ::
      supplySlot :: [] <<+ s9.stack := prefix_of_mul q9 p8
  have p10 : (B0 + 1) :: (sevm.value * (S + offset)) :: S :: (B0 + 1) :: 0 ::
      maxBalance :: supplySlot :: [] <<+ s10.stack :=
    prefix_of_dup_val q10 (by show_nth) p9
  have p11 : (sevm.value * (S + offset)) :: (B0 + 1) :: S :: (B0 + 1) :: 0 ::
      maxBalance :: supplySlot :: [] <<+ s11.stack := by
    have hswap : Stack.Swap (0 : Fin 16).val
        ((B0 + 1) :: (sevm.value * (S + offset)) :: S :: (B0 + 1) :: 0 ::
          maxBalance :: supplySlot :: [])
        ((sevm.value * (S + offset)) :: (B0 + 1) :: S :: (B0 + 1) :: 0 ::
          maxBalance :: supplySlot :: []) := by
      apply Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap q11) p10
  have p12 : m :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s12.stack := by
    simpa only [m] using prefix_of_div q12 p11
  have p13 : S :: m :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s13.stack := prefix_of_dup_val q13 (by show_nth) p12
  have p14 : m :: S :: m :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s14.stack := prefix_of_dup_val q14 (by show_nth) p13
  have p15 : (S + m) :: m :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s15.stack := by
        have hadd' : m + S = S + m := B256.add_comm
        rw [← hadd']
        exact prefix_of_add q15 p14
  have p16 : (S + m) :: (S + m) :: m :: S :: (B0 + 1) :: 0 :: maxBalance ::
      supplySlot :: [] <<+ s16.stack := prefix_of_dup_val q16 (by show_nth) p15
  have p17 : maxBalance :: (S + m) :: (S + m) :: m :: S :: (B0 + 1) :: 0 ::
      maxBalance :: supplySlot :: [] <<+ s17.stack :=
    prefix_of_dup_val q17 (by show_nth) p16
  have p18 : (maxBalance <? (S + m)) :: (S + m) :: m :: S :: (B0 + 1) :: 0 ::
      maxBalance :: supplySlot :: [] <<+ s18.stack := prefix_of_lt q18 p17
  rcases of_run_branch_revert hbranch with ⟨s19, hpop, hsuccess⟩
  have hflag : maxBalance <? (S + m) = 0 := (popBurn_pref hpop p18).1.symm
  have hsum : S + m ≤ maxSupply := by
    apply B256.not_lt.mp
    intro hlt
    have hcap : maxBalance = maxSupply := by decide +kernel
    have hlt' : maxBalance < S + m := by rwa [hcap]
    have hone : maxBalance <? (S + m) = 1 := by
      simp only [B256.ltCheck, if_pos hlt']
    exact B256.zero_ne_one (hone.symm.trans hflag).symm
  have p19 : (S + m) :: m :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s19.stack := (popBurn_pref hpop p18).2
  have hstor19 : Devm.getStor s0 = Devm.getStor s19 :=
    hstor3.trans ((Line.of_inv Devm.getStor (by line_inv) hlineInv).trans
      (PopBurn.Inv.inv hpop))
  rcases of_run_prepend [dup 6, sstore] _ hsuccess with ⟨s21, hsupplyStore, hrest⟩
  rcases Line.of_run_cons hsupplyStore with ⟨s20, q20, hsupplyStore⟩
  rcases Line.of_run_cons hsupplyStore with ⟨s21', q21, hnil⟩
  cases hnil
  have p20 : supplySlot :: (S + m) :: m :: S :: (B0 + 1) :: 0 :: maxBalance ::
      supplySlot :: [] <<+ s20.stack := prefix_of_dup_val q20 (by show_nth) p19
  have hstore1 := sstore_getStor_set q21 p20
  have p21 : m :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s21.stack := prefix_of_sstore q21 p20
  have hstor20 : Devm.getStor pre = Devm.getStor s20 :=
    hstor0.trans (hstor19.trans (Ninst.Hinv.inv q20))
  rcases of_run_prepend [dup 0, caller] _ hrest with ⟨s23, hcallerPre, hrest⟩
  have hcallerPreInv := hcallerPre
  rcases of_run_prepend [sload, add, caller, sstore] _ hrest with
    ⟨s27, hcallerStore, hret⟩
  rcases Line.of_run_cons hcallerPre with ⟨s22, q22, hcallerPre⟩
  rcases Line.of_run_cons hcallerPre with ⟨s23', q23, hnil⟩
  cases hnil
  have p22 : m :: m :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s22.stack := prefix_of_dup_val q22 (by show_nth) p21
  have p23 : sevm.caller.toB256 :: m :: m :: S :: (B0 + 1) :: 0 :: maxBalance ::
      supplySlot :: [] <<+ s23.stack :=
    prefix_of_push (of_run_caller q23) p22
  have hstor23 : Devm.getStor s21 = Devm.getStor s23 :=
    Line.of_inv Devm.getStor (by line_inv) hcallerPreInv
  rcases Line.of_run_cons hcallerStore with ⟨s24, q24, hcallerStore⟩
  rcases Line.of_run_cons hcallerStore with ⟨s25, q25, hcallerStore⟩
  rcases Line.of_run_cons hcallerStore with ⟨s26, q26, hcallerStore⟩
  rcases Line.of_run_cons hcallerStore with ⟨s27', q27, hnil⟩
  cases hnil
  rcases prefix_of_sload q24 p23 with ⟨balance, p24, hbalanceLoad⟩
  have hbalance' : balance = (Devm.getStor pre sevm.currentTarget).get
      sevm.caller.toB256 := by
    rw [hbalanceLoad]
    change (Devm.getStor s23 sevm.currentTarget).get sevm.caller.toB256 = _
    rw [← hstor23, hstore1, ← congrFun hstor20 sevm.currentTarget,
      Stor.get_set_ne _ (caller_ne_supplySlot sevm.caller).symm _]
  rw [hbalance'] at p24
  have p25 : ((Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 + m) ::
      m :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+ s25.stack :=
    prefix_of_add q25 p24
  have p26 : sevm.caller.toB256 ::
      ((Devm.getStor pre sevm.currentTarget).get sevm.caller.toB256 + m) :: m :: S ::
      (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+ s26.stack :=
    prefix_of_push (of_run_caller q26) p25
  have hstore2 := sstore_getStor_set q27 p26
  have p27 : m :: S :: (B0 + 1) :: 0 :: maxBalance :: supplySlot :: [] <<+
      s27.stack := prefix_of_sstore q27 p26
  have hstor26 : Devm.getStor s23 = Devm.getStor s26 :=
    (Ninst.Hinv.inv q24).trans ((Ninst.Hinv.inv q25).trans (Ninst.Hinv.inv q26))
  have hcode19 : Devm.getCode s0 = Devm.getCode s19 := by
    have hcode18 : Devm.getCode s0 = Devm.getCode s18 :=
      hcode0.symm.trans (hcode0.trans ((Line.of_inv Devm.getCode (by line_inv)
        hfirstInv).trans (Line.of_inv Devm.getCode (by line_inv) hlineInv)))
    have hcodePop : Devm.getCode s18 = Devm.getCode s19 := by
      funext a
      simp [Devm.getCode, Devm.getAcct]
      rw [hpop.state]
    exact hcode18.trans hcodePop
  have hlogs19 : s0.logs = s19.logs :=
    (Line.of_inv Devm.logs (by line_inv) hfirstInv).trans
      ((Line.of_inv Devm.logs (by line_inv) hlineInv).trans hpop.logs)
  have hcode19to27 : Devm.getCode s19 = Devm.getCode s27 :=
    (Ninst.Hinv.inv q20).trans ((Ninst.Hinv.inv q21).trans
      ((Line.of_inv Devm.getCode (by line_inv) hcallerPreInv).trans
        ((Ninst.Hinv.inv q24).trans ((Ninst.Hinv.inv q25).trans
          ((Ninst.Hinv.inv q26).trans (Ninst.Hinv.inv q27))))))
  have hreturn := returnsWord_of_storeReturn p27 hret
  refine ⟨hvalue, hbalance, hsum, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Func.of_inv Devm.getStor Devm.getStor (by func_inv) hret, hstore2,
      ← congrFun hstor26 sevm.currentTarget, ← congrFun hstor23 sevm.currentTarget, hstore1,
      ← congrFun hstor20 sevm.currentTarget]
  · exact (Func.of_inv Devm.getBal Devm.getBal (by func_inv) htail).symm.trans hbal0.symm
  · exact hreturn.2.symm.trans
      (hcode19to27.symm.trans (hcode19.symm.trans hcode0.symm))
  · exact (Func.of_inv Devm.logs Devm.logs (by func_inv) hsuccess).symm.trans
      (hlogs19.symm.trans hlogs0.symm)
  · exact hreturn.1

end Prorata

end Blanc
