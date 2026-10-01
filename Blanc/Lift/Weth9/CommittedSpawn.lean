import Blanc.Lift.Weth9.CommittedReplay

/-!
# The spawn obligations of a WETH9 frame

`Exec.CoreAccounting.SpawnReplay` (`Blanc/ExecutionModelAccounting.lean`) asks a contract for its own
steps `own` of a successful non-static target frame, and where they sit against the frame's chain nodes that
decode an external instruction.  For WETH9:

* `own` is the frame's invocation when it decodes as a writer, nothing for a view;
* every writer but `withdraw` runs no external instruction: its frame effect is the model step
  (`weth9_frame_effect`, `Call.stor_ledger`);
* `withdraw` debits *before* its ETH send: at the chain node that decodes the `CALL`, `own` has been taken
  (`weth9_exec_node`: the reach from the frame's start to that node is `weth9_withdraw_reach`), and after it
  the frame runs only the silent `afterCall` and the silent return, keeping storage (`getStor_post_of_silent`)
  and making no further external call (`noExec_after_of_cursor`);
* a `withdraw` frame with no chain node decoding an external instruction has no child, so its `CALL` step
  keeps storage (`StepIn.exec_getStor_eq_of_noDescendants`) and its post storage is the debited storage.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- The storage-level effect of `withdraw` from the run's facts: the `require` held and the storage is the
debit. -/
theorem withdraw_stor_of_debit {s s' : Stor} {who : Adr} {w : B256}
    (hle : w ≤ s.get (balSlot who)) (h : s' = s.set (balSlot who) (s.get (balSlot who) - w)) :
    Call.stor s (.withdraw who w) = some s' := by
  have hnlt : ¬ s.get (balSlot who) < w := B256.not_lt.mpr hle
  simp only [Call.stor, hnlt, ↓reduceIte]
  rw [h]

/-- **A chain node that decodes an external instruction is the `withdraw` `CALL`.**  In a successful frame,
at any node of its chain that decodes an external instruction, the calldata selects `withdraw`, its
`require` holds, the storage is the debited storage, and every node right after it has the frame's post
storage and is followed by no further external instruction. -/
theorem weth9_exec_node {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    {N : Exec.Deriv} (hN : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N)
    (hat : ∃ x, Ninst.At N.sevm.code N.pc (.exec x)) :
    decodeCall sevm = some (.withdraw sevm.caller (Sevm.dataWord sevm 4)) ∧
    Sevm.dataWord sevm 4 ≤ (Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) ∧
    Devm.getStor N.devm sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set (balSlot sevm.caller)
        ((Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
    ∀ N', Exec.Deriv.ParentStep N' N →
      Devm.getStor post = Devm.getStor N'.devm ∧
      ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) := by
  obtain ⟨x, hx⟩ := hat
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl hcode fork hN
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hx
  have hT : AtExec (κ.conf N.devm) := ⟨x, g, hf⟩
  change Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) prog sevm ⟨pre, t_0000_c0, []⟩
    (κ.conf N.devm) at reach
  obtain ⟨hshort, hsel, d10, gw, cw, ys, hTeq, hle, hstor, -⟩ :=
    weth9_withdraw_reach StepIn.toRun reach hT
  have hdec := decode_of_withdraw_selector hshort hsel
  have hNd : N.devm = d10 := congrArg Conf.d hTeq
  have hκf : κ.f = .next (.exec .call) afterCall := congrArg Conf.f hTeq
  have hκK : κ.K.map Cont.f = [t_0264_c24] := congrArg Conf.K hTeq
  refine ⟨hdec, hle, by rw [hNd]; exact hstor, ?_⟩
  intro N' edge
  have hsevmN : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hN
  have hforkN : CoveredFork N.sevm.benvStat.fork := by rw [hsevmN]; exact fork
  obtain ⟨κ₁, hs, -, ok₁⟩ := cursor_stepS cert_check ok edge hforkN
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hκf hκK
  subst hκf
  cases hs with
  | next habs =>
    have hchain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N' := hN.snoc edge
    have hfsil : afterCall.silentTree regSilent = true := by decide
    have hKsil : ∀ s ∈ K.map Cont.f, s.silentTree regSilent = true := by
      rw [hκK]
      intro s hs
      rw [List.mem_singleton] at hs
      subst hs
      decide
    refine ⟨?_, ?_⟩
    · exact getStor_post_of_silent cert_check (R := ⟨0, sevm, pre, .ok post, run⟩) (post := post)
        rfl hchain fork ok₁ (ok' := regSilent)
        (fun hn hs => Ninst.Run.state_of_regSilent hn (StepIn.toRun hs)) hfsil hKsil
    · intro M hM y
      exact noExec_after_of_cursor cert_check hchain hM fork ok₁ (E := []) rfl
        (by exact afterCall_execFree)
        (by
          simp only [hκK, List.map_cons, List.mem_singleton, forall_eq]
          decide) y

/-- WETH9 frames spawn only by `CALL`/`STATICCALL` (the certificate cursor). -/
theorem weth9_spawnKinds (ca : Adr) : SpawnKinds ca weth9Sem := by
  intro sevm pre post run hrun _ fork _ node chain x hat
  obtain ⟨κ, -, ok⟩ := cursor_of_parentPrefix cert_check
    (F := ⟨0, sevm, pre, .ok post, run⟩) rfl hrun.1 fork chain
  exact ok.exec_call_or_staticcall hat

/-- One decoded call's storage effect is the replay of its invocation, at the tracked keys. -/
theorem replay_one {U : Key → Prop} (hinj : KeyInj U) {sevm : Sevm} {pre post : Devm} {c : Call}
    (hkeys : ∀ k ∈ frameKeys sevm, U k) (hc : decodeCall sevm = some c) {s s' : Stor}
    (h : c.stor s = some s') :
    LedgerReplay (ledger U s) [⟨sevm, pre, post⟩] (ledger U s') := by
  have hstep := Call.stor_ledger hinj (fun k hk => hkeys k (decodeCall_keys hc k hk)) h
  unfold LedgerReplay replayCalls
  simp only [List.filterMap_cons, hc, List.filterMap_nil, Ledger.run_cons, hstep, Option.bind_some,
    Ledger.run_nil]

/-- **The replay of a successful non-static WETH9 target frame**: its own step and, when it sends ETH after
its debit, the position of that step against the chain node of the send. -/
theorem weth9_spawnReplay (ca : Adr) {U : Key → Prop} (hinj : KeyInj U) :
    Exec.CoreAccounting.SpawnReplay ca (footSpec U).sem (footEntry U) (wethCarrier ca U)
      (wethObservation ca U) := by
  intro sevm pre post run committed hrun target fork installed admitted bound hstatic
  have hkeys : ∀ k ∈ frameKeys sevm, U k := admitted.root target
  have hin := lift_sound_in cert_check hrun.1 fork run
  have self : committedFrameInvocations ca (Exec.Frame.ofRun run committed) =
      if (decodeCall sevm).isSome = true then [⟨sevm, pre, post⟩] else [] := by
    show (if sevm.currentTarget = ca ∧ sevm.isStatic = false ∧ (decodeCall sevm).isSome = true then
        [frameInvocation (Exec.Frame.ofRun run committed)] else []) = _
    by_cases h : (decodeCall sevm).isSome = true
    · simp only [target, hstatic, h, and_self, ↓reduceIte]
      rfl
    · have h' : (decodeCall sevm).isSome = false := by simpa only [Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none, Bool.not_eq_true] using h
      simp only [h', Bool.false_eq_true, and_false, ↓reduceIte]
  refine ⟨if (decodeCall sevm).isSome = true then [⟨sevm, pre, post⟩] else [], ?_, ?_, ?_⟩
  · show _ = committedFrameInvocations ca (Exec.Frame.ofRun run committed)
    rw [self]
    rfl
  · intro hnone
    subst target
    show LedgerReplay (ledger U (Devm.getStor pre sevm.currentTarget))
      (if (decodeCall sevm).isSome = true then [⟨sevm, pre, post⟩] else [])
      (ledger U (Devm.getStor post sevm.currentTarget))
    rcases weth9_frame_effect StepIn.toRun fork hin with ⟨hd, hst⟩ | ⟨c, hd, hnw, hstor⟩ |
        ⟨who, w, hd, -⟩
    · simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [hst]
      exact LedgerReplay.nil _
    · simp only [hd, Option.isSome_some, ↓reduceIte]
      exact replay_one hinj hkeys hd hstor
    · obtain ⟨d10, sf, hstorc, hstep, hstate⟩ :=
        weth9_withdraw_frame StepIn.toRun hin ⟨who, w, hd⟩
      have hdesc : Exec.rawFrameDescendants run = [] :=
        Exec.rawFrameDescendants_eq_nil_of_noExec run hnone
      have hsf : Devm.getStor sf = Devm.getStor d10 :=
        StepIn.exec_getStor_eq_of_noDescendants (R := ⟨0, sevm, pre, .ok post, run⟩) hdesc hstep
      have hpost : Devm.getStor post sevm.currentTarget = Devm.getStor d10 sevm.currentTarget :=
        (getStor_eq_of_state_eq hstate sevm.currentTarget).trans
          (congrFun hsf sevm.currentTarget)
      obtain ⟨rfl, rfl⟩ := decodeCall_withdraw_inv hd
      simp only [hd, Option.isSome_some, ↓reduceIte]
      rw [hpost]
      exact replay_one hinj hkeys hd hstorc
  · subst target
    intro N hN x hx
    obtain ⟨hdec, hle, hstor, hafter⟩ := weth9_exec_node run hrun.1 fork hN ⟨x, hx⟩
    refine ⟨?_, fun N' edge => ?_⟩
    · show LedgerReplay (ledger U (Devm.getStor pre sevm.currentTarget))
        (if (decodeCall sevm).isSome = true then [⟨sevm, pre, post⟩] else [])
        (ledger U (Devm.getStor N.devm sevm.currentTarget))
      simp only [hdec, Option.isSome_some, ↓reduceIte]
      exact replay_one hinj hkeys hdec (withdraw_stor_of_debit hle hstor)
    · obtain ⟨hpost, hnoexec⟩ := hafter N' edge
      refine ⟨?_, hnoexec⟩
      show LedgerReplay (ledger U (Devm.getStor N'.devm sevm.currentTarget)) []
        (ledger U (Devm.getStor post sevm.currentTarget))
      rw [hpost]
      exact LedgerReplay.nil _

end Blanc.Lift.Weth9
