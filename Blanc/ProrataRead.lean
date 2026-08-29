-- ProrataRead.lean : exact read-only observations for PRORATA conversion views.

import Blanc.ProrataFunctional

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Prorata

/-- `SHR` is a silent binary operation; the generic log-invariance catalogue
does not register it. -/
private theorem shr_logs_hinv : Rinst.Hinv Devm.logs Rinst.shr := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

private theorem mul_logs_hinv : Rinst.Hinv Devm.logs Rinst.mul := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

private theorem div_logs_hinv : Rinst.Hinv Devm.logs Rinst.div := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs

private theorem selfbalance_logs_hinv : Rinst.Hinv Devm.logs Rinst.selfbalance := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

private theorem rev_logs_hinv : Linst.Hinv Devm.logs Devm.logs Linst.rev := by
  constructor
  intro e s r run
  simp only [Linst.Run, Linst.run] at run
  rcases Except.bind_eq_ok run with ⟨v1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
  contradiction

private instance : PopBurn.Inv Devm.logs := ⟨fun h => h.logs⟩
private instance : Burn.Inv Devm.logs := ⟨fun h => h.logs⟩
private instance : PopBurn.Inv Devm.getCode := ⟨fun h => by
  funext a
  exact getCode_eq_of_state_eq h.state a⟩
private instance : Burn.Inv Devm.getCode := ⟨fun h => by
  funext a
  exact getCode_eq_of_state_eq h.state a⟩

/-- The shares conversion view does not change persistent storage. -/
theorem convertToShares_stor_inv :
    Func.Inv Devm.getStor Devm.getStor convertToShares := by
  func_inv

/-- The shares conversion view does not change account balances. -/
theorem convertToShares_bal_inv :
    Func.Inv Devm.getBal Devm.getBal convertToShares := by
  func_inv

/-- The shares conversion view emits no logs. -/
theorem convertToShares_logs_inv :
    Func.Inv Devm.logs Devm.logs convertToShares := by
  letI : Rinst.Hinv Devm.logs Rinst.shr := shr_logs_hinv
  letI : Rinst.Hinv Devm.logs Rinst.mul := mul_logs_hinv
  letI : Rinst.Hinv Devm.logs Rinst.div := div_logs_hinv
  letI : Rinst.Hinv Devm.logs Rinst.selfbalance := selfbalance_logs_hinv
  letI : Linst.Hinv Devm.logs Devm.logs Linst.rev := rev_logs_hinv
  func_inv




/-- The assets conversion view does not change persistent storage. -/
theorem convertToAssets_stor_inv :
    Func.Inv Devm.getStor Devm.getStor convertToAssets := by
  func_inv

/-- The assets conversion view does not change account balances. -/
theorem convertToAssets_bal_inv :
    Func.Inv Devm.getBal Devm.getBal convertToAssets := by
  func_inv

/-- The assets conversion view emits no logs. -/
theorem convertToAssets_logs_inv :
    Func.Inv Devm.logs Devm.logs convertToAssets := by
  letI : Rinst.Hinv Devm.logs Rinst.shr := shr_logs_hinv
  letI : Rinst.Hinv Devm.logs Rinst.mul := mul_logs_hinv
  letI : Rinst.Hinv Devm.logs Rinst.div := div_logs_hinv
  letI : Rinst.Hinv Devm.logs Rinst.selfbalance := selfbalance_logs_hinv
  letI : Linst.Hinv Devm.logs Devm.logs Linst.rev := rev_logs_hinv
  func_inv

/-- Exact successful-body observations for `convertToShares`.  The arithmetic
is deliberately stated at the EVM-word altitude: the accompanying guards,
rather than an external no-wrap hypothesis, license its uses. -/
def SharesViewEffect (sevm : Sevm) (pre post : Devm) : Prop :=
  let a := Sevm.argWord sevm 0
  let B := Devm.getBal pre sevm.currentTarget
  let S := (Devm.getStor pre sevm.currentTarget).get supplySlot
  let m := a * (S + offset) / (B + 1)
  a ≤ maxValue ∧ B ≤ maxBalance ∧ S + m ≤ maxSupply ∧
    ReturnsWord m post ∧
    Devm.getStor post = Devm.getStor pre ∧
    Devm.getBal post = Devm.getBal pre ∧
    Devm.getCode post = Devm.getCode pre ∧
    post.logs = pre.logs

private def convertToSharesTail : Func :=
  pushB256 1 ::: add ::: dup 4 ::: sload ::: dup 0 ::: pushB256 offset ::: add :::
    dup 4 ::: mul ::: dup 2 ::: swap 0 ::: div ::: dup 1 ::: dup 1 ::: add :::
    dup 6 ::: lt ::: .rev <?>
      (mstoreAt 0 +++ returnMemoryRange 0 32)



/-- A successful shares-preview body has passed its input and balance
magnitude guards.  The third (hypothetical-mint) guard is discharged by the
subsequent arithmetic suffix. -/
private theorem convertToShares_guardPrefix_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre convertToShares post) :
    Sevm.argWord sevm 0 ≤ maxValue ∧
      Devm.getBal pre sevm.currentTarget ≤ maxBalance ∧
    ∃ mid, Func.Run fs sevm mid convertToSharesTail post ∧
      Devm.getBal pre sevm.currentTarget :: (0 : B256) :: Sevm.argWord sevm 0 ::
        maxBalance :: supplySlot :: [] <<+ mid.stack ∧
      pre.memory = mid.memory ∧ Devm.getCode pre = Devm.getCode mid := by
  simp only [convertToShares] at run
  rcases of_run_prepend pushMaxAndCap _ run with ⟨s0, hcache, hrest⟩
  rcases of_run_prepend (arg 0) _ hrest with ⟨d1, qarg, hrest⟩
  rcases of_run_prepend [dup 0, dup 2, pushB256 30, shr, lt,
    selfbalance, dup 0, dup 4, lt, dup 2, add] _ hrest with
    ⟨s12, hline, hbranch⟩
  have hbal0 : Devm.getBal s0 = Devm.getBal pre :=
    (Line.of_inv Devm.getBal (by line_inv) hcache).symm
  unfold pushMaxAndCap at hcache
  rcases Line.of_run_cons hcache with ⟨c1, q0, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c2, qnot, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c3, qdup, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c4, q130, hcache⟩
  rcases Line.of_run_cons hcache with ⟨s0', qshr, hnil⟩
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
  rcases Line.of_run_cons hline with ⟨d2, qdupA, hline⟩
  rcases Line.of_run_cons hline with ⟨d3, qdupM, hline⟩
  rcases Line.of_run_cons hline with ⟨d4, q30, hline⟩
  rcases Line.of_run_cons hline with ⟨d5, qshrM, hline⟩
  rcases Line.of_run_cons hline with ⟨d6, qltA, hline⟩
  rcases Line.of_run_cons hline with ⟨d7, qbalance, hline⟩
  rcases Line.of_run_cons hline with ⟨d8, qdupB, hline⟩
  rcases Line.of_run_cons hline with ⟨d9, qdupCap, hline⟩
  rcases Line.of_run_cons hline with ⟨d10, qltB, hline⟩
  rcases Line.of_run_cons hline with ⟨d11, qdupFlag, hline⟩
  rcases Line.of_run_cons hline with ⟨s12', qadd, hnil⟩
  cases hnil
  have hbal6 : Devm.getBal d6 = Devm.getBal pre := by
    calc
      Devm.getBal d6 = Devm.getBal d5 := (Ninst.Hinv.inv qltA).symm
      _ = Devm.getBal d4 := (Ninst.Hinv.inv qshrM).symm
      _ = Devm.getBal d3 := (Ninst.Hinv.inv q30).symm
      _ = Devm.getBal d2 := (Ninst.Hinv.inv qdupM).symm
      _ = Devm.getBal d1 := (Ninst.Hinv.inv qdupA).symm
      _ = Devm.getBal s0 := (Line.of_inv Devm.getBal (by unfold arg cdl; line_inv) qarg).symm
      _ = Devm.getBal pre := hbal0
  have p1 : Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+
      d1.stack := prefix_of_arg cp4 qarg
  have p2 : Sevm.argWord sevm 0 :: Sevm.argWord sevm 0 ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d2.stack :=
    prefix_of_dup_val qdupA (by show_nth) p1
  have p3 : B256.shiftRight B256.max 130 :: Sevm.argWord sevm 0 ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+
      d3.stack := prefix_of_dup_val qdupM (by show_nth) p2
  have p4 : (30 : B256) :: B256.shiftRight B256.max 130 :: Sevm.argWord sevm 0 ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d4.stack :=
    prefix_of_push (of_run_pushB256 q30) p3
  have p5 : B256.shiftRight (B256.shiftRight B256.max 130) 30 ::
      Sevm.argWord sevm 0 :: Sevm.argWord sevm 0 ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+
      d5.stack := by simpa only [h30] using prefix_of_shr qshrM p4
  have p6 : (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+
      d6.stack := prefix_of_lt qltA p5
  have p7 : Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d7.stack := by
    rw [← hbal6]
    exact prefix_of_push (of_run_selfbalance qbalance) p6
  have p8 : Devm.getBal pre sevm.currentTarget :: Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d8.stack :=
    prefix_of_dup_val qdupB (by show_nth) p7
  have p9 : B256.shiftRight B256.max 130 :: Devm.getBal pre sevm.currentTarget ::
      Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d9.stack :=
    prefix_of_dup_val qdupCap (by show_nth) p8
  have p10 : (B256.shiftRight B256.max 130 <? Devm.getBal pre sevm.currentTarget) ::
      Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d10.stack :=
    prefix_of_lt qltB p9
  have p11 : (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? Sevm.argWord sevm 0) ::
      (B256.shiftRight B256.max 130 <? Devm.getBal pre sevm.currentTarget) ::
      Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d11.stack :=
    prefix_of_dup_val qdupFlag (by show_nth) p10
  have p12 :
      ((B256.shiftRight (B256.shiftRight B256.max 130) 30 <? Sevm.argWord sevm 0) +
        (B256.shiftRight B256.max 130 <? Devm.getBal pre sevm.currentTarget)) ::
      Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ s12.stack :=
    prefix_of_add qadd p11
  rcases of_run_branch_rev hbranch with ⟨after, hpop, hsuccess⟩
  have hzero := (popBurn_pref hpop p12).1.symm
  have hM : B256.shiftRight B256.max 130 = maxBalance := by decide +kernel
  have hV : B256.shiftRight maxBalance 30 = maxValue := by decide +kernel
  rw [hM, hV] at hzero
  have ha : ¬ maxValue < Sevm.argWord sevm 0 := by
    intro ha
    by_cases hb : maxBalance < Devm.getBal pre sevm.currentTarget
    · have hz : (1 : B256) + 1 = 0 := by simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (1 : B256) + 1 ≠ 0) hz
    · have hz : (1 : B256) + 0 = 0 := by simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (1 : B256) + 0 ≠ 0) hz
  have hb : ¬ maxBalance < Devm.getBal pre sevm.currentTarget := by
    intro hb
    by_cases ha : maxValue < Sevm.argWord sevm 0
    · have hz : (1 : B256) + 1 = 0 := by simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (1 : B256) + 1 ≠ 0) hz
    · have hz : (0 : B256) + 1 = 0 := by simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (0 : B256) + 1 ≠ 0) hz
  have hfA : maxBalance.shiftRight 30 <? Sevm.argWord sevm 0 = 0 := by
    rw [hV]
    simp [B256.ltCheck, ha]
  have hfAraw :
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <?
        Sevm.argWord sevm 0) = 0 := by
    rw [hM]
    exact hfA
  have hp : Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight (B256.shiftRight B256.max 130) 30 <?
        Sevm.argWord sevm 0) :: Sevm.argWord sevm 0 ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ after.stack :=
    (popBurn_pref hpop p12).2
  have hp' : Devm.getBal pre sevm.currentTarget :: (0 : B256) ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ after.stack := by
    simpa only [hM, hfA, supplySlot] using hp
  have hmem : pre.memory = after.memory := by
    calc
      pre.memory = c1.memory := Ninst.Hinv.inv q0
      _ = c2.memory := Ninst.Hinv.inv qnot
      _ = c3.memory := Ninst.Hinv.inv qdup
      _ = c4.memory := Ninst.Hinv.inv q130
      _ = s0.memory := Ninst.Hinv.inv qshr
      _ = d1.memory := (Line.of_inv Devm.memory (by unfold arg cdl; line_inv) qarg)
      _ = d2.memory := Ninst.Hinv.inv qdupA
      _ = d3.memory := Ninst.Hinv.inv qdupM
      _ = d4.memory := Ninst.Hinv.inv q30
      _ = d5.memory := Ninst.Hinv.inv qshrM
      _ = d6.memory := Ninst.Hinv.inv qltA
      _ = d7.memory := Ninst.Hinv.inv qbalance
      _ = d8.memory := Ninst.Hinv.inv qdupB
      _ = d9.memory := Ninst.Hinv.inv qdupCap
      _ = d10.memory := Ninst.Hinv.inv qltB
      _ = d11.memory := Ninst.Hinv.inv qdupFlag
      _ = s12.memory := Ninst.Hinv.inv qadd
      _ = after.memory := hpop.memory
  have hcode : Devm.getCode pre = Devm.getCode after := by
    calc
      Devm.getCode pre = Devm.getCode c1 := Ninst.Hinv.inv q0
      _ = Devm.getCode c2 := Ninst.Hinv.inv qnot
      _ = Devm.getCode c3 := Ninst.Hinv.inv qdup
      _ = Devm.getCode c4 := Ninst.Hinv.inv q130
      _ = Devm.getCode s0 := Ninst.Hinv.inv qshr
      _ = Devm.getCode d1 :=
        (Line.of_inv Devm.getCode (by unfold arg cdl; line_inv) qarg)
      _ = Devm.getCode d2 := Ninst.Hinv.inv qdupA
      _ = Devm.getCode d3 := Ninst.Hinv.inv qdupM
      _ = Devm.getCode d4 := Ninst.Hinv.inv q30
      _ = Devm.getCode d5 := Ninst.Hinv.inv qshrM
      _ = Devm.getCode d6 := Ninst.Hinv.inv qltA
      _ = Devm.getCode d7 := Ninst.Hinv.inv qbalance
      _ = Devm.getCode d8 := Ninst.Hinv.inv qdupB
      _ = Devm.getCode d9 := Ninst.Hinv.inv qdupCap
      _ = Devm.getCode d10 := Ninst.Hinv.inv qltB
      _ = Devm.getCode d11 := Ninst.Hinv.inv qdupFlag
      _ = Devm.getCode s12 := Ninst.Hinv.inv qadd
      _ = Devm.getCode after := by
        funext a
        exact getCode_eq_of_state_eq hpop.state a
  refine ⟨B256.not_lt.mp ha, B256.not_lt.mp hb, after, ?_, hp', hmem, hcode⟩
  simpa only [convertToSharesTail] using hsuccess

private theorem convertToShares_tail_effect
    {fs : List Func} {sevm : Sevm} {mid post : Devm}
    (hp : Devm.getBal mid sevm.currentTarget :: (0 : B256) ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ mid.stack)
    (run : Func.Run fs sevm mid convertToSharesTail post) :
    let B := Devm.getBal mid sevm.currentTarget
    let S := (Devm.getStor mid sevm.currentTarget).get supplySlot
    let m := Sevm.argWord sevm 0 * (S + offset) / (B + 1)
    S + m ≤ maxSupply ∧ ReturnsWord m post ∧ Devm.getCode mid = Devm.getCode post := by
  dsimp
  let B := Devm.getBal mid sevm.currentTarget
  let S := (Devm.getStor mid sevm.currentTarget).get supplySlot
  let m := Sevm.argWord sevm 0 * (S + offset) / (B + 1)
  simp only [convertToSharesTail] at run
  rcases of_run_prepend [pushB256 1, add, dup 4] _ run with ⟨s3, hfirst, hrest⟩
  have hfirstInv := hfirst
  rcases of_run_prepend [sload, dup 0, pushB256 offset, add, dup 4, mul,
    dup 2, swap 0, div, dup 1, dup 1, add, dup 6, lt] _ hrest with
    ⟨s17, hline, hbranch⟩
  have hlineInv := hline
  rcases Line.of_run_cons hfirst with ⟨s1, q1, hfirst⟩
  rcases Line.of_run_cons hfirst with ⟨s2, q2, hfirst⟩
  rcases Line.of_run_cons hfirst with ⟨s3', q3, hnil⟩
  cases hnil
  have p1 : (1 : B256) :: B :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s1.stack := by
    simpa only [B, List.cons_append, List.nil_append] using
      prefix_of_push (of_run_pushB256 q1) hp
  have p2 : (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s2.stack := by
    have hadd : (1 : B256) + B = B + 1 := B256.add_comm
    rw [← hadd]
    exact prefix_of_add q2 p1
  have p3 : supplySlot :: (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s3.stack := prefix_of_dup_val q3 (by show_nth) p2
  have hstor3 : Devm.getStor mid = Devm.getStor s3 :=
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
  rcases Line.of_run_cons hline with ⟨s17', q17, hnil⟩
  cases hnil
  rcases prefix_of_sload q4 p3 with ⟨supply, p4, hsupply⟩
  have hsupply' : supply = S := by
    rw [hsupply]
    change (Devm.getStor s3 sevm.currentTarget).get supplySlot = S
    rw [← hstor3]
  rw [hsupply'] at p4
  have p5 : S :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s5.stack := prefix_of_dup_val q5 (by show_nth) p4
  have p6 : offset :: S :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s6.stack := prefix_of_push (of_run_pushB256 q6) p5
  have p7 : (S + offset) :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s7.stack := by
    have hoff : offset + S = S + offset := B256.add_comm
    rw [← hoff]
    exact prefix_of_add q7 p6
  have p8 : Sevm.argWord sevm 0 :: (S + offset) :: S :: (B + 1) :: 0 ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ s8.stack :=
    prefix_of_dup_val q8 (by show_nth) p7
  have p9 : (Sevm.argWord sevm 0 * (S + offset)) :: S :: (B + 1) :: 0 ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ s9.stack :=
    prefix_of_mul q9 p8
  have p10 : (B + 1) :: (Sevm.argWord sevm 0 * (S + offset)) :: S :: (B + 1) :: 0 ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ s10.stack :=
    prefix_of_dup_val q10 (by show_nth) p9
  have p11 : (Sevm.argWord sevm 0 * (S + offset)) :: (B + 1) :: S :: (B + 1) :: 0 ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ s11.stack := by
    have hswap : Stack.Swap (0 : Fin 16).val
        ((B + 1) :: (Sevm.argWord sevm 0 * (S + offset)) :: S :: (B + 1) :: 0 ::
          Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [])
        ((Sevm.argWord sevm 0 * (S + offset)) :: (B + 1) :: S :: (B + 1) :: 0 ::
          Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: []) := by
      apply Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap q11) p10
  have p12 : m :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s12.stack := by
    simpa only [m] using prefix_of_div q12 p11
  have p13 : S :: m :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s13.stack := prefix_of_dup_val q13 (by show_nth) p12
  have p14 : m :: S :: m :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s14.stack := prefix_of_dup_val q14 (by show_nth) p13
  have p15 : (S + m) :: m :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s15.stack := by
    have hadd : m + S = S + m := B256.add_comm
    rw [← hadd]
    exact prefix_of_add q15 p14
  have p16 : maxBalance :: (S + m) :: m :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 ::
      maxBalance :: supplySlot :: [] <<+ s16.stack :=
    prefix_of_dup_val q16 (by show_nth) p15
  have p17 : (maxBalance <? (S + m)) :: m :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 ::
      maxBalance :: supplySlot :: [] <<+ s17.stack := prefix_of_lt q17 p16
  rcases of_run_branch_rev hbranch with ⟨after, hpop, hreturn⟩
  have hflag : maxBalance <? (S + m) = 0 := (popBurn_pref hpop p17).1.symm
  have hsum : S + m ≤ maxSupply := by
    apply B256.not_lt.mp
    intro hlt
    have hcap : maxBalance = maxSupply := by decide +kernel
    have hlt' : maxBalance < S + m := by rwa [hcap]
    have hone : maxBalance <? (S + m) = 1 := by
      simp only [B256.ltCheck, if_pos hlt']
    exact B256.zero_ne_one (hone.symm.trans hflag).symm
  have pafter : m :: S :: (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      after.stack := (popBurn_pref hpop p17).2
  have hword := returnsWord_of_storeReturn pafter hreturn
  exact ⟨hsum, hword.1, (Line.of_inv Devm.getCode (by line_inv) hfirstInv).trans
    ((Line.of_inv Devm.getCode (by line_inv) hlineInv).trans
      ((funext fun a => getCode_eq_of_state_eq hpop.state a).trans hword.2))⟩

/-- Compatibility projection of the shares guard-prefix certificate. -/
theorem convertToShares_pre_guards
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre convertToShares post) :
    Sevm.argWord sevm 0 ≤ maxValue ∧
      Devm.getBal pre sevm.currentTarget ≤ maxBalance := by
  exact ⟨(convertToShares_guardPrefix_effect run).1,
    (convertToShares_guardPrefix_effect run).2.1⟩

/-- Exact successful-body effect of `convertToShares(uint256)`. -/
theorem convertToShares_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre convertToShares post) :
    SharesViewEffect sevm pre post := by
  unfold SharesViewEffect
  dsimp
  rcases convertToShares_guardPrefix_effect run with
    ⟨hamount, hbalance, mid, htail, hp, hmem, hcode⟩
  have hstorWhole : Devm.getStor pre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor convertToShares_stor_inv run
  have hbalWhole : Devm.getBal pre = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal convertToShares_bal_inv run
  have hlogsWhole : pre.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs convertToShares_logs_inv run
  have hstorTail : Devm.getStor mid = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) htail
  have hbalTail : Devm.getBal mid = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) htail
  have hstorMid : Devm.getStor pre = Devm.getStor mid :=
    hstorWhole.trans hstorTail.symm
  have hbalMid : Devm.getBal pre = Devm.getBal mid :=
    hbalWhole.trans hbalTail.symm
  have hpMid : Devm.getBal mid sevm.currentTarget :: (0 : B256) ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ mid.stack := by
    rw [← hbalMid]
    exact hp
  rcases convertToShares_tail_effect hpMid htail with ⟨hsum, hword, hcodeTail⟩
  rw [← hstorMid, ← hbalMid] at hsum hword
  exact ⟨hamount, hbalance, hsum, hword, hstorWhole.symm, hbalWhole.symm,
    (hcode.trans hcodeTail).symm, hlogsWhole.symm⟩

/-- Exact successful-body effect of `convertToAssets(uint256)`. -/
def AssetsViewEffect (sevm : Sevm) (pre post : Devm) : Prop :=
  let s := Sevm.argWord sevm 0
  let B := Devm.getBal pre sevm.currentTarget
  let S := (Devm.getStor pre sevm.currentTarget).get supplySlot
  let p := s * (B + 1) / (S + offset)
  s ≤ maxSupply ∧ B ≤ maxBalance ∧ ReturnsWord p post ∧
    Devm.getStor post = Devm.getStor pre ∧
    Devm.getBal post = Devm.getBal pre ∧
    Devm.getCode post = Devm.getCode pre ∧
    post.logs = pre.logs

private def convertToAssetsTail : Func :=
  pushB256 1 ::: add ::: dup 2 ::: mul ::: dup 4 ::: sload :::
    pushB256 offset ::: add ::: swap 0 ::: div :::
    mstoreAt 0 +++ returnMemoryRange 0 32

/-- A successful assets-preview body has passed its share-count and balance
magnitude guards, and reaches its arithmetic suffix from the exact guard stack. -/
private theorem convertToAssets_guardPrefix_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre convertToAssets post) :
    Sevm.argWord sevm 0 ≤ maxSupply ∧
      Devm.getBal pre sevm.currentTarget ≤ maxBalance ∧
    ∃ mid, Func.Run fs sevm mid convertToAssetsTail post ∧
      Devm.getBal pre sevm.currentTarget :: (0 : B256) :: Sevm.argWord sevm 0 ::
        maxBalance :: supplySlot :: [] <<+ mid.stack ∧
      pre.memory = mid.memory ∧ Devm.getCode pre = Devm.getCode mid := by
  simp only [convertToAssets] at run
  rcases of_run_prepend pushMaxAndCap _ run with ⟨s0, hcache, hrest⟩
  rcases of_run_prepend (arg 0) _ hrest with ⟨d1, qarg, hrest⟩
  rcases of_run_prepend [dup 0, dup 2, lt, selfbalance, dup 0, dup 4, lt,
    dup 2, add] _ hrest with ⟨s9, hline, hbranch⟩
  have hcacheInv := hcache
  have hlineInv := hline
  have hbal0 : Devm.getBal s0 = Devm.getBal pre :=
    (Line.of_inv Devm.getBal (by line_inv) hcache).symm
  unfold pushMaxAndCap at hcache
  rcases Line.of_run_cons hcache with ⟨c1, q0, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c2, qnot, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c3, qdup, hcache⟩
  rcases Line.of_run_cons hcache with ⟨c4, q130, hcache⟩
  rcases Line.of_run_cons hcache with ⟨s0', qshr, hnil⟩
  cases hnil
  have hU : ~~~(0 : B256) = B256.max := by decide +kernel
  have h130 : B256.max >>> (130 : B256).toNat = B256.shiftRight B256.max 130 := by
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
  rcases Line.of_run_cons hline with ⟨d2, qdupA, hline⟩
  rcases Line.of_run_cons hline with ⟨d3, qdupM, hline⟩
  rcases Line.of_run_cons hline with ⟨d4, qltA, hline⟩
  rcases Line.of_run_cons hline with ⟨d5, qbalance, hline⟩
  rcases Line.of_run_cons hline with ⟨d6, qdupB, hline⟩
  rcases Line.of_run_cons hline with ⟨d7, qdupCap, hline⟩
  rcases Line.of_run_cons hline with ⟨d8, qltB, hline⟩
  rcases Line.of_run_cons hline with ⟨d9', qdupFlag, hline⟩
  rcases Line.of_run_cons hline with ⟨s9', qadd, hnil⟩
  cases hnil
  have hbal4 : Devm.getBal d4 = Devm.getBal pre := by
    calc
      Devm.getBal d4 = Devm.getBal d3 := (Ninst.Hinv.inv qltA).symm
      _ = Devm.getBal d2 := (Ninst.Hinv.inv qdupM).symm
      _ = Devm.getBal d1 := (Ninst.Hinv.inv qdupA).symm
      _ = Devm.getBal s0 := (Line.of_inv Devm.getBal (by unfold arg cdl; line_inv) qarg).symm
      _ = Devm.getBal pre := hbal0
  have p1 : Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+
      d1.stack := prefix_of_arg cp4 qarg
  have p2 : Sevm.argWord sevm 0 :: Sevm.argWord sevm 0 ::
      B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d2.stack :=
    prefix_of_dup_val qdupA (by show_nth) p1
  have p3 : B256.shiftRight B256.max 130 :: Sevm.argWord sevm 0 ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d3.stack :=
    prefix_of_dup_val qdupM (by show_nth) p2
  have p4 : (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d4.stack :=
    prefix_of_lt qltA p3
  have p5 : Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d5.stack := by
    rw [← hbal4]
    exact prefix_of_push (of_run_selfbalance qbalance) p4
  have p6 : Devm.getBal pre sevm.currentTarget :: Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d6.stack :=
    prefix_of_dup_val qdupB (by show_nth) p5
  have p7 : B256.shiftRight B256.max 130 :: Devm.getBal pre sevm.currentTarget ::
      Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d7.stack :=
    prefix_of_dup_val qdupCap (by show_nth) p6
  have p8 : (B256.shiftRight B256.max 130 <? Devm.getBal pre sevm.currentTarget) ::
      Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d8.stack :=
    prefix_of_lt qltB p7
  have p9 : (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) ::
      (B256.shiftRight B256.max 130 <? Devm.getBal pre sevm.currentTarget) ::
      Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ d9'.stack :=
    prefix_of_dup_val qdupFlag (by show_nth) p8
  have p10 :
      ((B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) +
        (B256.shiftRight B256.max 130 <? Devm.getBal pre sevm.currentTarget)) ::
      Devm.getBal pre sevm.currentTarget ::
      (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) ::
      Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+ s9.stack :=
    prefix_of_add qadd p9
  rcases of_run_branch_rev hbranch with ⟨after, hpop, hsuccess⟩
  have hzero := (popBurn_pref hpop p10).1.symm
  have hS : B256.shiftRight B256.max 130 = maxSupply := by decide +kernel
  have hB : B256.shiftRight B256.max 130 = maxBalance := by decide +kernel
  nth_rw 1 [hS] at hzero
  rw [hB] at hzero
  have ha : ¬ maxSupply < Sevm.argWord sevm 0 := by
    intro ha
    by_cases hb : maxBalance < Devm.getBal pre sevm.currentTarget
    · have hz : (1 : B256) + 1 = 0 := by simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (1 : B256) + 1 ≠ 0) hz
    · have hz : (1 : B256) + 0 = 0 := by simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (1 : B256) + 0 ≠ 0) hz
  have hb : ¬ maxBalance < Devm.getBal pre sevm.currentTarget := by
    intro hb
    by_cases ha : maxSupply < Sevm.argWord sevm 0
    · have hz : (1 : B256) + 1 = 0 := by simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (1 : B256) + 1 ≠ 0) hz
    · have hz : (0 : B256) + 1 = 0 := by simpa [B256.ltCheck, ha, hb] using hzero
      exact (by decide +kernel : (0 : B256) + 1 ≠ 0) hz
  have hfA : maxSupply <? Sevm.argWord sevm 0 = 0 := by
    simp [B256.ltCheck, ha]
  have hfAraw :
      (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) = 0 := by
    rw [hS]
    exact hfA
  have hp :
      Devm.getBal pre sevm.currentTarget ::
        (B256.shiftRight B256.max 130 <? Sevm.argWord sevm 0) ::
        Sevm.argWord sevm 0 :: B256.shiftRight B256.max 130 :: B256.max :: [] <<+
          after.stack :=
    (popBurn_pref hpop p10).2
  have hp' :
      Devm.getBal pre sevm.currentTarget :: (0 : B256) :: Sevm.argWord sevm 0 ::
        maxBalance :: supplySlot :: [] <<+ after.stack := by
    change Devm.getBal pre sevm.currentTarget :: (0 : B256) :: Sevm.argWord sevm 0 ::
      maxBalance :: B256.max :: [] <<+ after.stack
    rw [hfAraw, hB] at hp
    exact hp
  have hmem : pre.memory = after.memory := by
    calc
      pre.memory = s0.memory := Line.of_inv Devm.memory (by line_inv) hcacheInv
      _ = d1.memory := Line.of_inv Devm.memory (by unfold arg cdl; line_inv) qarg
      _ = s9.memory := Line.of_inv Devm.memory (by line_inv) hlineInv
      _ = after.memory := hpop.memory
  have hcode : Devm.getCode pre = Devm.getCode after := by
    calc
      Devm.getCode pre = Devm.getCode s0 :=
        Line.of_inv Devm.getCode (by line_inv) hcacheInv
      _ = Devm.getCode d1 :=
        Line.of_inv Devm.getCode (by unfold arg cdl; line_inv) qarg
      _ = Devm.getCode s9 := Line.of_inv Devm.getCode (by line_inv) hlineInv
      _ = Devm.getCode after := by
        funext a
        exact getCode_eq_of_state_eq hpop.state a
  refine ⟨B256.not_lt.mp ha, B256.not_lt.mp hb, after, ?_, hp', hmem, hcode⟩
  simpa only [convertToAssetsTail] using hsuccess

/-- A successful `convertToAssets` body has both of its pre-arithmetic guards. -/
theorem convertToAssets_pre_guards
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre convertToAssets post) :
    Sevm.argWord sevm 0 ≤ maxSupply ∧
      Devm.getBal pre sevm.currentTarget ≤ maxBalance := by
  exact ⟨(convertToAssets_guardPrefix_effect run).1,
    (convertToAssets_guardPrefix_effect run).2.1⟩

private theorem convertToAssets_tail_effect
    {fs : List Func} {sevm : Sevm} {mid post : Devm}
    (hp : Devm.getBal mid sevm.currentTarget :: (0 : B256) ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ mid.stack)
    (run : Func.Run fs sevm mid convertToAssetsTail post) :
    let B := Devm.getBal mid sevm.currentTarget
    let S := (Devm.getStor mid sevm.currentTarget).get supplySlot
    let p := Sevm.argWord sevm 0 * (B + 1) / (S + offset)
    ReturnsWord p post ∧ Devm.getCode mid = Devm.getCode post := by
  dsimp
  let B := Devm.getBal mid sevm.currentTarget
  let S := (Devm.getStor mid sevm.currentTarget).get supplySlot
  let p := Sevm.argWord sevm 0 * (B + 1) / (S + offset)
  simp only [convertToAssetsTail] at run
  rcases of_run_prepend [pushB256 1, add, dup 2, mul, dup 4] _ run with
    ⟨s5, hfirst, hrest⟩
  have hfirstInv := hfirst
  rcases of_run_prepend [sload, pushB256 offset, add, swap 0, div] _ hrest with
    ⟨s10, hline, hreturn⟩
  have hlineInv := hline
  rcases Line.of_run_cons hfirst with ⟨s1, q1, hfirst⟩
  rcases Line.of_run_cons hfirst with ⟨s2, q2, hfirst⟩
  rcases Line.of_run_cons hfirst with ⟨s3, q3, hfirst⟩
  rcases Line.of_run_cons hfirst with ⟨s4, q4, hfirst⟩
  rcases Line.of_run_cons hfirst with ⟨s5', q5, hnil⟩
  cases hnil
  have p1 : (1 : B256) :: B :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s1.stack := by
    simpa only [B, List.cons_append, List.nil_append] using
      prefix_of_push (of_run_pushB256 q1) hp
  have p2 : (B + 1) :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s2.stack := by
    have hadd : (1 : B256) + B = B + 1 := B256.add_comm
    rw [← hadd]
    exact prefix_of_add q2 p1
  have p3 : Sevm.argWord sevm 0 :: (B + 1) :: 0 :: Sevm.argWord sevm 0 ::
      maxBalance :: supplySlot :: [] <<+ s3.stack :=
    prefix_of_dup_val q3 (by show_nth) p2
  have p4 : (Sevm.argWord sevm 0 * (B + 1)) :: 0 :: Sevm.argWord sevm 0 ::
      maxBalance :: supplySlot :: [] <<+ s4.stack :=
    prefix_of_mul q4 p3
  have p5 : supplySlot :: (Sevm.argWord sevm 0 * (B + 1)) :: 0 ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ s5.stack :=
    prefix_of_dup_val q5 (by show_nth) p4
  have hstor5 : Devm.getStor mid = Devm.getStor s5 :=
    Line.of_inv Devm.getStor (by line_inv) hfirstInv
  rcases Line.of_run_cons hline with ⟨s6, q6, hline⟩
  rcases Line.of_run_cons hline with ⟨s7, q7, hline⟩
  rcases Line.of_run_cons hline with ⟨s8, q8, hline⟩
  rcases Line.of_run_cons hline with ⟨s9, q9, hline⟩
  rcases Line.of_run_cons hline with ⟨s10', q10, hnil⟩
  cases hnil
  rcases prefix_of_sload q6 p5 with ⟨supply, p6, hsupply⟩
  have hsupply' : supply = S := by
    rw [hsupply]
    change (Devm.getStor s5 sevm.currentTarget).get supplySlot = S
    rw [← hstor5]
  rw [hsupply'] at p6
  have p7 : offset :: S :: (Sevm.argWord sevm 0 * (B + 1)) :: 0 ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ s7.stack :=
    prefix_of_push (of_run_pushB256 q7) p6
  have p8 : (S + offset) :: (Sevm.argWord sevm 0 * (B + 1)) :: 0 ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ s8.stack := by
    have hoff : offset + S = S + offset := B256.add_comm
    rw [← hoff]
    exact prefix_of_add q8 p7
  have p9 : (Sevm.argWord sevm 0 * (B + 1)) :: (S + offset) :: 0 ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ s9.stack := by
    have hswap : Stack.Swap (0 : Fin 16).val
        ((S + offset) :: (Sevm.argWord sevm 0 * (B + 1)) :: 0 ::
          Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [])
        ((Sevm.argWord sevm 0 * (B + 1)) :: (S + offset) :: 0 ::
          Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: []) := by
      apply Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap q9) p8
  have p10 : p :: 0 :: Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+
      s10.stack := by
    simpa only [p] using prefix_of_div q10 p9
  have hword := returnsWord_of_storeReturn p10 hreturn
  exact ⟨hword.1, (Line.of_inv Devm.getCode (by line_inv) hfirstInv).trans
    ((Line.of_inv Devm.getCode (by line_inv) hlineInv).trans hword.2)⟩

/-- Exact successful-body effect of `convertToAssets(uint256)`. -/
theorem convertToAssets_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre convertToAssets post) :
    AssetsViewEffect sevm pre post := by
  unfold AssetsViewEffect
  dsimp
  rcases convertToAssets_guardPrefix_effect run with
    ⟨hshares, hbalance, mid, htail, hp, hmem, hcode⟩
  have hstorWhole : Devm.getStor pre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor convertToAssets_stor_inv run
  have hbalWhole : Devm.getBal pre = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal convertToAssets_bal_inv run
  have hlogsWhole : pre.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs convertToAssets_logs_inv run
  have hstorTail : Devm.getStor mid = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) htail
  have hbalTail : Devm.getBal mid = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) htail
  have hstorMid : Devm.getStor pre = Devm.getStor mid :=
    hstorWhole.trans hstorTail.symm
  have hbalMid : Devm.getBal pre = Devm.getBal mid :=
    hbalWhole.trans hbalTail.symm
  have hpMid : Devm.getBal mid sevm.currentTarget :: (0 : B256) ::
      Sevm.argWord sevm 0 :: maxBalance :: supplySlot :: [] <<+ mid.stack := by
    rw [← hbalMid]
    exact hp
  rcases convertToAssets_tail_effect hpMid htail with ⟨hword, hcodeTail⟩
  rw [← hstorMid, ← hbalMid] at hword
  exact ⟨hshares, hbalance, hword, hstorWhole.symm, hbalWhole.symm,
    (hcode.trans hcodeTail).symm, hlogsWhole.symm⟩


end Prorata

end Blanc
