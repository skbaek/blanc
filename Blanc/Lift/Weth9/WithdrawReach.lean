import Blanc.Lift.Weth9.Effects
import Blanc.Lift.ReachChain

/-!
# Reaching the `CALL` of WETH9's `withdraw`

`Withdraw.lean` walks entry 8 as a big-step run.  A chain node of a frame that decodes an external
instruction is placed by `reach_of_parentPrefix` as a *reach* from the frame's start, not as a run, so
the same walk is needed in reach form: from the frame's start, the only external instruction reachable
is the `CALL` of entry 8 (the ETH send), reached through the `withdraw` wrapper (entry 24) and the
`require` and debit of entry 8, and at that configuration

* the calldata is `withdraw(wad)` with `wad = calldata[4:36]`;
* the `require` holds: `wad ≤ balanceOf[caller]`;
* the storage is the debited storage;
* what is pending after the `CALL` is the silent `afterCall` and the silent return `t_0264_c24`.

The line-level facts are `Weth9.withdraw_prefix` (shared with the big-step walk).
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift

/-! ## Reach helpers -/

theorem chain_append (xs ys : List Ninst) (g : SFunc) : chain (xs ++ ys) g = chain xs (chain ys g) := by
  induction xs with
  | nil => rfl
  | cons n ns ih => exact congrArg (SFunc.next n) ih

/-- Split a reach through a straight line of non-external instructions at a prefix. -/
theorem Reach.chain_split {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc}
    {sevm : Sevm} (xs ys : List Ninst) (hn : ∀ n ∈ xs, ∀ x, n ≠ .exec x) {d : Devm} {g : SFunc}
    {K : List SFunc} {T : Conf} (run : Reach P fs sevm ⟨d, chain (xs ++ ys) g, K⟩ T)
    (hT : AtExec T) :
    ∃ d' : Devm, LineP P sevm d xs d' ∧ Reach P fs sevm ⟨d', chain ys g, K⟩ T := by
  rw [chain_append] at run
  exact Reach.chain_prefix xs hn run hT

/-- A test that an instruction is not external, decidable on concrete lines. -/
def isExecB : Ninst → Bool
  | .exec _ => true
  | _ => false

theorem nonexec_of_all {xs : List Ninst} (h : xs.all (fun n => !isExecB n) = true) :
    ∀ n ∈ xs, ∀ x, n ≠ .exec x := by
  intro n hn x hx
  have := List.all_eq_true.mp h n hn
  subst hx
  simp [isExecB] at this

/-- A revert tail is never left. -/
theorem not_reach_revert_tail {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc}
    {sevm : Sevm} {d : Devm} {K : List SFunc} {T : Conf}
    (run : Reach P fs sevm ⟨d, .next (.push [0x00] (by decide))
      (.next (.reg (.dup 0)) (.last .revert)), K⟩ T) (hT : AtExec T) : False := by
  obtain ⟨d1, -, run⟩ := Reach.next (by intro x h; cases h) run hT
  obtain ⟨d2, -, run⟩ := Reach.next (by intro x h; cases h) run hT
  exact Reach.not_last run hT

/-- The word popped by a jump leaves the rest of a stack prefix. -/
theorem prefix_of_popBurn1 {s s' : Devm} {a d : B256} {xs : Stack}
    (hp : a :: xs <<+ s.stack) (h : Devm.PopBurn [d] s s') : xs <<+ s'.stack := by
  have hs : s.stack = d :: s'.stack := h.stack
  rcases hp with ⟨t, ht⟩
  have ht' : s.stack = a :: (xs ++ t) := ht
  rw [hs] at ht'
  injection ht' with h1 ht'
  exact ⟨t, ht'⟩

/-! ## The argument decode of the wrapper -/

/-- Entry 24's decode of `withdraw`'s argument: the return address, the offset `4`, `calldataload(4)`,
and the jump destination of entry 8. -/
def wdLine : List Ninst :=
  [.push [0x02, 0x64] (by decide), .push [0x04] (by decide), .reg (.dup 0), .reg (.dup 0),
   .reg .calldataload, .reg (.swap 0), .push [0x20] (by decide), .reg .add, .reg (.swap 0),
   .reg (.swap 1), .reg (.swap 0), .reg .pop, .reg .pop, .push [0x09, 0xd9] (by decide)]

/-- The line leaves storage and balances alone and pushes `wad = calldata[4:36]`, a return address and
the jump destination. -/
theorem wdLine_walk {sevm : Sevm} {s s' : Devm} (run : Line.Run sevm s wdLine s') :
    Same s s' ∧ ∃ t r : B256, [t, Sevm.dataWord sevm 4, r] <<+ s'.stack := by
  have hsame : Same s s' := ⟨Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run⟩
  refine ⟨hsame, ?_⟩
  unfold wdLine at run
  obtain ⟨s1, h1, run⟩ := Line.of_run_cons run
  obtain ⟨s2, h2, run⟩ := Line.of_run_cons run
  obtain ⟨s3, h3, run⟩ := Line.of_run_cons run
  obtain ⟨s4, h4, run⟩ := Line.of_run_cons run
  obtain ⟨s5, h5, run⟩ := Line.of_run_cons run
  obtain ⟨s6, h6, run⟩ := Line.of_run_cons run
  obtain ⟨s7, h7, run⟩ := Line.of_run_cons run
  obtain ⟨s8, h8, run⟩ := Line.of_run_cons run
  obtain ⟨s9, h9, run⟩ := Line.of_run_cons run
  obtain ⟨s10, h10, run⟩ := Line.of_run_cons run
  obtain ⟨s11, h11, run⟩ := Line.of_run_cons run
  obtain ⟨s12, h12, run⟩ := Line.of_run_cons run
  obtain ⟨s13, h13, run⟩ := Line.of_run_cons run
  obtain ⟨s14, h14, run⟩ := Line.of_run_cons run
  cases run
  obtain ⟨r, hp1⟩ : ∃ r : B256, [r] <<+ s1.stack :=
    ⟨_, prefix_of_push (of_run_push h1) nil_pref⟩
  have hp2 : [(4 : B256), r] <<+ s2.stack := by
    have := prefix_of_push (of_run_push h2) hp1
    rwa [w04_eq] at this
  have hp3 : [(4 : B256), 4, r] <<+ s3.stack := prefix_of_dup_val h3 (by show_nth) hp2
  have hp4 : [(4 : B256), 4, 4, r] <<+ s4.stack := prefix_of_dup_val h4 (by show_nth) hp3
  have hp5 := prefix_of_calldataload_val h5 hp4
  generalize Sevm.dataWord sevm 4 = v at hp5 ⊢
  have hp6 : [(4 : B256), v, 4, r] <<+ s6.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h6) hp5
  have hp7 : [(32 : B256), 4, v, 4, r] <<+ s7.stack := by
    have := prefix_of_push (of_run_push h7) hp6
    rwa [w20_eq] at this
  have hp8 : [(32 : B256) + 4, v, 4, r] <<+ s8.stack := prefix_of_add h8 hp7
  have hp9 : [v, (32 : B256) + 4, 4, r] <<+ s9.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h9) hp8
  have hp10 : [(4 : B256), (32 : B256) + 4, v, r] <<+ s10.stack :=
    Stack.prefix_of_swap (n := 1) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h10) hp9
  have hp11 : [(32 : B256) + 4, 4, v, r] <<+ s11.stack :=
    Stack.prefix_of_swap (n := 0) (by simp [Stack.Swap, Stack.SwapCore])
      (of_run_swap h11) hp10
  have hp13 := prefix_of_pop (of_run_pop h13) (prefix_of_pop (of_run_pop h12) hp11)
  exact ⟨_, r, prefix_of_push (of_run_push h14) hp13⟩

/-! ## The reach to the `CALL` -/

theorem callvalueLine_nonexec :
    ∀ n ∈ ([.reg .callvalue, .reg .iszero, .push [0x02, 0x4e] (by decide)] : List Ninst),
      ∀ x, n ≠ .exec x :=
  nonexec_of_all (by decide)

theorem wdLine_nonexec : ∀ n ∈ wdLine, ∀ x, n ≠ .exec x :=
  nonexec_of_all (by decide)

theorem slotLine_nonexec : ∀ n ∈ slotLine, ∀ x, n ≠ .exec x :=
  nonexec_of_all (by decide)

theorem checkTail_nonexec : ∀ n ∈ checkTail, ∀ x, n ≠ .exec x :=
  nonexec_of_all (by decide)

theorem updLine_sub_nonexec : ∀ n ∈ updLine (.reg .sub), ∀ x, n ≠ .exec x :=
  nonexec_of_all (by decide)

theorem sendLine_nonexec : ∀ n ∈ sendLine, ∀ x, n ≠ .exec x :=
  nonexec_of_all (by decide)

theorem afterCall_execFree : afterCall.execFreeIn [] = true := by decide

/-- **The reach from the frame's start to an external instruction is the `withdraw` `CALL`.**  A reach
from entry `0` to a configuration about to run an external instruction is a reach to the `CALL` of
entry 8 reached through `withdraw`'s wrapper: the calldata is at least four bytes and selects
`withdraw`, the `require` `wad ≤ balanceOf[caller]` holds (for `wad = calldata[4:36]`), the storage is
the debited storage, and the pending trees are the silent `afterCall` and the silent return of the
wrapper. -/
theorem weth9_withdraw_reach {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sevm : Sevm} {pre : Devm} {T : Conf}
    (run : Reach P prog sevm ⟨pre, t_0000_c0, []⟩ T) (hT : AtExec T) :
    ¬ shortCall sevm ∧ Sevm.selector sevm = Bytes.toB256 [0x2e, 0x1a, 0x7d, 0x4d] ∧
      ∃ (d10 : Devm) (gw cw : B256) (ys : Stack),
        T = ⟨d10, .next (.exec .call) afterCall, [t_0264_c24]⟩ ∧
        Sevm.dataWord sevm 4 ≤
          (Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) ∧
        Devm.getStor d10 sevm.currentTarget =
          (Devm.getStor pre sevm.currentTarget).set (balSlot sevm.caller)
            ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) -
              Sevm.dataWord sevm 4) ∧
        gw :: cw :: Sevm.dataWord sevm 4 :: ys <<+ d10.stack := by
  obtain ⟨hshort, hsel, d', hs, run⟩ := weth9_reach_route hP run hT
  refine ⟨hshort, hsel, ?_⟩
  have h24 : t_0243_c24 = .dest (chain [.reg .callvalue, .reg .iszero,
      .push [0x02, 0x4e] (by decide)] (.branch t_024a_c24 t_024e_c24)) := rfl
  have h24e : t_024e_c24 = .dest (chain wdLine (.callNext 8 t_0264_c24)) := rfl
  rw [h24] at run
  obtain ⟨d1, burn, run⟩ := Reach.dest run hT
  obtain ⟨d2, hl, run⟩ := Reach.chain_prefix [.reg .callvalue, .reg .iszero,
    .push [0x02, 0x4e] (by decide)] callvalueLine_nonexec run hT
  change Reach P prog sevm ⟨d2, .branch t_024a_c24 t_024e_c24, []⟩ T at run
  rcases Reach.branch run hT with ⟨t, d3, pop, run⟩ | ⟨t, w, d3, hw, pop, run⟩
  · exact (not_reach_revert_tail run hT).elim
  rw [h24e] at run
  obtain ⟨d4, burn', run⟩ := Reach.dest run hT
  obtain ⟨d5, hl2, run⟩ := Reach.chain_prefix wdLine wdLine_nonexec run hT
  obtain ⟨s45, t9, r9, hp5⟩ := wdLine_walk (hl2.toRun hP)
  change Reach P prog sevm ⟨d5, .callNext 8 t_0264_c24, []⟩ T at run
  obtain ⟨tj, g, d6, hg, pop2, hcases⟩ := Reach.call run hT
  have s12 : Same d' d3 :=
    ((Same.of_state burn.state).trans
      ⟨Line.of_inv Devm.getStor (by line_inv) (hl.toRun hP),
        Line.of_inv Devm.getBal (by line_inv) (hl.toRun hP)⟩).trans (Same.of_state pop.state)
  have s35 : Same d3 d5 := (Same.of_state burn'.state).trans s45
  have s56 : Same d5 d6 := Same.of_state pop2.state
  have sAll : Same pre d6 := hs.trans (s12.trans (s35.trans s56))
  have hp6 : [Sevm.dataWord sevm 4, r9] <<+ d6.stack := by
    have := prefix_of_popBurn1 (a := t9) (by simpa using hp5) pop2
    simpa using this
  rcases hcases with ⟨T', reach', rfl⟩ | ⟨d7, hret, run'⟩
  · have hT' : AtExec T' := AtExec.below.mp hT
    have hg' : g = t_09d9_c8 := by simpa [prog, Cert.prog, cert] using hg.symm
    subst hg'
    rw [withdraw_tree_eq] at reach'
    obtain ⟨e0, burn0, reach⟩ := Reach.dest reach' hT'
    obtain ⟨e1, hdup, reach⟩ := Reach.chain_split [.reg (.dup 0)] (slotLine ++ checkTail)
      (nonexec_of_all (by decide)) reach hT'
    obtain ⟨e2, hslot, reach⟩ := Reach.chain_split slotLine checkTail slotLine_nonexec reach hT'
    obtain ⟨e3, hcheck, reach⟩ := Reach.chain_split checkTail [] checkTail_nonexec reach hT'
    change Reach P prog sevm ⟨e3, .branch t_0a23_c8 t_0a27_c8, []⟩ T' at reach
    rcases Reach.branch reach hT' with ⟨tq, e4, popq, reach⟩ | ⟨dw, w', e4, hwnz, popq, reach⟩
    · exact (not_reach_revert_tail reach hT').elim
    rw [debit_tree_eq] at reach
    obtain ⟨e5, burn1, reach⟩ := Reach.dest reach hT'
    obtain ⟨e6, hdup', reach⟩ := Reach.chain_split [.reg (.dup 0)]
      (slotLine ++ updLine (.reg .sub) ++ [Ninst.sstore] ++ sendLine ++ [.exec .call])
      (nonexec_of_all (by decide)) reach hT'
    obtain ⟨e7, hslot', reach⟩ := Reach.chain_split slotLine
      (updLine (.reg .sub) ++ [Ninst.sstore] ++ sendLine ++ [.exec .call])
      slotLine_nonexec reach hT'
    obtain ⟨e8, hdebit, reach⟩ := Reach.chain_split (updLine (.reg .sub))
      ([Ninst.sstore] ++ sendLine ++ [.exec .call]) updLine_sub_nonexec reach hT'
    obtain ⟨e9, hsstore, reach⟩ := Reach.chain_split [Ninst.sstore]
      (sendLine ++ [.exec .call]) (nonexec_of_all (by decide)) reach hT'
    obtain ⟨e10, hsend, reach⟩ := Reach.chain_split sendLine [.exec .call] sendLine_nonexec
      reach hT'
    change Reach P prog sevm ⟨e10, .next (.exec .call) afterCall, []⟩ T' at reach
    obtain ⟨wad, rest, gw, cw, ys, hstk, hle, hstor, -, -, hp10⟩ :=
      Weth9.withdraw_prefix burn0 (hdup.toRun hP) (hslot.toRun hP) (hcheck.toRun hP) hwnz popq
        burn1 (hdup'.toRun hP) (hslot'.toRun hP) (hdebit.toRun hP) (hsstore.toRun hP)
        (hsend.toRun hP)
    have hwad : wad = Sevm.dataWord sevm 4 := by
      obtain ⟨tl, htl⟩ := hp6
      have h1 : d6.stack = Sevm.dataWord sevm 4 :: r9 :: tl := htl
      rw [h1] at hstk
      exact (List.cons.inj hstk).1.symm
    subst hwad
    rw [← sAll.stor] at hle hstor
    have hT'eq : T' = ⟨e10, .next (.exec .call) afterCall, []⟩ := by
      rcases Reach.exec reach with h | ⟨d', hstep, reach2⟩
      · exact h
      · exact (Reach.false_of_execFree (E := []) rfl reach2 hT' afterCall_execFree
          (by simp)).elim
    refine ⟨e10, gw, cw, ys, ?_, hle, hstor, hp10⟩
    rw [hT'eq]
    rfl
  · exfalso
    have hret' : t_0264_c24 = .dest (.last .stop) := rfl
    rw [hret'] at run'
    obtain ⟨d8, -, run''⟩ := Reach.dest run' hT
    exact Reach.not_last run'' hT

end Blanc.Lift.Weth9
