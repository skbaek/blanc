import Blanc.Lift.Weth9.CommittedSpawn
import Blanc.Lift.Weth9.WithdrawReach
import Blanc.Lift.CursorCuts
import Blanc.Lift.CallSiteChildren
import Blanc.CallSpawnExact

/-!
# The `withdraw` `CALL` node of a WETH9 frame, and its child's entry precondition

`weth9_exec_node` (`Blanc/Lift/Weth9/CommittedSpawn.lean`) places every chain node of a successful WETH9
frame that decodes an external instruction at the `withdraw` debit.  The per-frame history facts of the
token core also need, at that node, the instruction itself (`CALL`), the balances (unchanged since the
frame's entry) and the amount on the stack (the debited `wad`), so that the child the `CALL` enters
starts in the footprint precondition (`withdraw_child_pre`): the debit lowered the booked total by
exactly the ETH the `CALL` sends out of the contract.
-/

namespace Blanc.Composition.Weth9TokenFrames

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.ExecutionTrace

/-- `weth9_withdraw_reach` with the balances at the `CALL` node: the walk from the frame's start to
the node moves no ETH. -/
theorem weth9_withdraw_reach_bal {P : Sevm → Devm → Ninst → Devm → Prop}
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
        d10.getBal = pre.getBal ∧
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
  have s12 : SameCode d' d3 :=
    ((SameCode.of_state burn.state).trans
      ⟨Line.of_inv Devm.getStor (by line_inv) (hl.toRun hP),
        Line.of_inv Devm.getBal (by line_inv) (hl.toRun hP),
        Line.of_inv Devm.getCode (by line_inv) (hl.toRun hP)⟩).trans
      (SameCode.of_state pop.state)
  have s35 : SameCode d3 d5 := (SameCode.of_state burn'.state).trans s45
  have s56 : SameCode d5 d6 := SameCode.of_state pop2.state
  have sAll : SameCode pre d6 := hs.trans (s12.trans (s35.trans s56))
  have hp6 : [Sevm.dataWord sevm 4, r9] <<+ d6.stack := by
    have := prefix_of_popBurn1 (a := t9) (by simpa only using hp5) pop2
    simpa only using this
  rcases hcases with ⟨T', reach', rfl⟩ | ⟨d7, hret, run'⟩
  · have hT' : AtExec T' := AtExec.below.mp hT
    have hg' : g = t_09d9_c8 := by simpa only [prog, Cert.prog, cert, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos,
      List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq] using hg.symm
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
    obtain ⟨wad, rest, gw, cw, ys, hstk, hle, hstor, hbal10, -, hp10⟩ :=
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
          (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true])).elim
    refine ⟨e10, gw, cw, ys, ?_, hle, hstor, hbal10.trans sAll.bal.symm, hp10⟩
    rw [hT'eq]
    rfl
  · exfalso
    have hret' : t_0264_c24 = .dest (.last .stop) := rfl
    rw [hret'] at run'
    obtain ⟨d8, -, run''⟩ := Reach.dest run' hT
    exact Reach.not_last run'' hT

/-- **The external node of a WETH9 frame is the `withdraw` `CALL`**, reached with the entry balances
and with the debited amount as the `CALL`'s value operand. -/
theorem weth9_exec_node_call {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    {N : Exec.Deriv} (hN : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N)
    (hat : ∃ x, Ninst.At N.sevm.code N.pc (.exec x)) :
    Ninst.At N.sevm.code N.pc (.exec .call) ∧ N.devm.getBal = pre.getBal ∧
      ∃ gw cw ys, gw :: cw :: Sevm.dataWord sevm 4 :: ys <<+ N.devm.stack := by
  obtain ⟨x, hx⟩ := hat
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl hcode fork hN
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hx
  have hT : AtExec (κ.conf N.devm) := ⟨x, g, hf⟩
  change Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) prog sevm ⟨pre, t_0000_c0, []⟩
    (κ.conf N.devm) at reach
  obtain ⟨-, -, d10, gw, cw, ys, hTeq, -, -, hbal, hstk⟩ :=
    weth9_withdraw_reach_bal StepIn.toRun reach hT
  have hNd : N.devm = d10 := congrArg Conf.d hTeq
  have hκf : κ.f = .next (.exec .call) afterCall := congrArg Conf.f hTeq
  exact ⟨ok.ninstAt_of_next hκf, by rw [hNd]; exact hbal, gw, cw, ys, by rw [hNd]; exact hstk⟩

/-- **The entry precondition of the child of `withdraw`'s `CALL`.**  At the `CALL` node of a WETH9
frame entered in the footprint precondition (storage debited by `wad`, balances as at the entry, `wad`
the value operand), the child the `CALL` enters starts in the footprint precondition. -/
theorem withdraw_child_pre {ca : Adr} {U : Key → Prop} (hinj : KeyInj U) {sevm : Sevm}
    {pre s : Devm} {pc pc' : Nat} {f : Frame} {rsm : Resume} {cevm : Evm} {gw cw : B256}
    {ys : Stack} (target : sevm.currentTarget = ca) (fork : CoveredFork sevm.benvStat.fork)
    (hcaller : U (.bal sevm.caller)) (hpre : (footSpec U).Pre ca sevm pre)
    (hle : Sevm.dataWord sevm 4 ≤ (Devm.getStor pre ca).get (balSlot sevm.caller))
    (hstor : Devm.getStor s ca = (Devm.getStor pre ca).set (balSlot sevm.caller)
      ((Devm.getStor pre ca).get (balSlot sevm.caller) - Sevm.dataWord sevm 4))
    (hbal : s.getBal = pre.getBal) (hcode : s.getCode ca = pre.getCode ca)
    (hat : Ninst.At sevm.code pc (.exec .call))
    (hstk : gw :: cw :: Sevm.dataWord sevm 4 :: ys <<+ s.stack)
    (step : Evm.step ⟨pc, sevm, s⟩ = .spawn f rsm pc') (enter : f.enter = .run cevm) :
    (footSpec U).Pre ca cevm.sta cevm.dyna := by
  rw [Evm.step_next hat] at step
  have hx : Xinst.step sevm s .call = .spawn f rsm :=
    XStep.toStep_spawn (by simpa only [Ninst.step_exec] using step)
  obtain ⟨g, c, v, ii, is, oi, os, rest, hs7⟩ := Xinst.step_call_spawn_stack fork hx
  have hv : v = Sevm.dataWord sevm 4 := by
    obtain ⟨tl, htl⟩ := hstk
    have h1 : s.stack = gw :: cw :: Sevm.dataWord sevm 4 :: (ys ++ tl) := htl
    rw [h1] at hs7
    simp only [List.cons.injEq] at hs7
    exact hs7.2.2.1.symm
  subst hv
  obtain ⟨parent, dp, na, code', avail, -, -, hparent, -, -, hframe, -⟩ :=
    Ninst.step_call_spawn_exact (by simpa only [Ninst.call] using step) hs7 fork
  obtain ⟨benv, transfer, rfl⟩ := Frame.enter_run_inv enter
  subst hframe
  subst target
  have hinv := foot_withdraw_step hinj hcaller (hpre.inv.left rfl) hle
  have hcodeS : some (s.state.getCode sevm.currentTarget).toList = (footSpec U).sem.image := by
    show some (s.getCode sevm.currentTarget).toList = _
    rw [hcode]
    exact hpre.code
  have hsideS : (footSpec U).Side s.state.bal := by
    show (footSpec U).Side s.getBal
    rw [hbal]
    exact hpre.side
  have hstorS : s.state.getStor sevm.currentTarget = Devm.getStor s sevm.currentTarget := rfl
  have hbalS : s.state.bal sevm.currentTarget = pre.getBal sevm.currentTarget := by
    show s.getBal sevm.currentTarget = _
    rw [hbal]
  by_cases hz : Sevm.dataWord sevm 4 = 0
  · have hbenv := benvAfterTransfer_eq_of_not_transfer (fun h => h.2 hz) transfer
    refine ContractSpecSem.Pre.of_inv_eqs ?_ (fun _ => hz)
    show (footSpec U).StateInv sevm.currentTarget benv.state
    rw [hbenv]
    show (footSpec U).StateInv sevm.currentTarget parent.state
    rw [hparent]
    refine ⟨hcodeS, hsideS, ?_⟩
    rw [hstorS, hstor, hbalS]
    have h2 := hinv.2
    rw [hz] at h2 ⊢
    simpa only [B256.sub_zero] using h2
  · obtain ⟨st_mid, h_sub, hB⟩ := of_benvAfterTransfer rfl hz transfer
    refine ContractSpecSem.Pre.child_of_outbound_transfer (st := s.state) (st_mid := st_mid)
      (target := c.toAdr) (value := Sevm.dataWord sevm 4) hcodeS hsideS ?_ ?_ ?_ rfl rfl
    · rw [hstorS, hstor, hbalS]
      exact hinv.2
    · rw [← hparent]
      exact h_sub
    · show benv.state = _
      rw [hB]
      rfl

end Blanc.Composition.Weth9TokenFrames
