import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.ReturnDataBound
import Blanc.ExecutionModelAccounting
import Blanc.Lift.CursorCuts

/-!
# A successful non-admin proxy frame ends in its child's output and world (C2)

`proxy_forwards_ok`: a pc-0 non-admin proxy frame that succeeds has a committed child whose output and
world the frame ends with.  The lifted run (`lift_sound_in`, `proxy_halt`) passes `_delegate`'s
`DELEGATECALL` with a nonzero flag, so that step filled its child slot with an entered child among
the frame's raw roots, one level deeper: the frame's chain spawns (`proxy_spawn_exists`).  At that
chain node (the `DELEGATECALL`, `proxy_node`) the actual successful suffix resumes with the child's
settled run (`Resume.call_run_inv`), and the delegate tail returns the returndata at that world
(`dl_tail_halted`).
-/

namespace Blanc

open Jaune

/-- Every raw descendant root of a chain suffix was entered at a spawning node of the chain. -/
theorem Exec.spawn_of_mem_rawFrameDescendants {root : Exec.Deriv} :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ r ∈ Exec.rawFrameDescendants run, ∃ (N : Exec.Deriv) (f : Frame) (rsm : Resume) (pc' : Nat),
        Exec.Deriv.ParentPrefix root N ∧ Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc' := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ r member
      simp only [Exec.rawFrameDescendants, List.not_mem_nil] at member
  | cont step next ih =>
      intro chain r member
      exact ih (chain.snoc (.cont step next)) r (by simpa only [Exec.rawFrameDescendants] using member)
  | doneErr _ _ _ =>
      intro _ r member
      simp only [Exec.rawFrameDescendants, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro chain r member
      exact ih (chain.snoc (.doneOk step enter resume next)) r
        (by simpa only [Exec.rawFrameDescendants] using member)
  | runErr step _ _ _ =>
      intro chain _ _
      exact ⟨_, _, _, _, chain, step⟩
  | runOk step _ _ _ _ _ _ =>
      intro chain _ _
      exact ⟨_, _, _, _, chain, step⟩

/-- A direct child of a later node of the chain is a direct child of the chain's root. -/
theorem Exec.Deriv.ParentPrefix.childFrames_subset {root N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix root N) :
    ∀ c ∈ Exec.childFrames N.exc, c ∈ Exec.childFrames root.exc := by
  induction chain with
  | refl => exact fun _ h => h
  | step head _ ih =>
      intro c member
      have h := ih c member
      cases head with
      | cont step next => simpa only [Exec.childFrames] using h
      | doneOk step enter resume next => simpa only [Exec.childFrames] using h
      | runOk step enter child resume next =>
          simp only [Exec.childFrames, List.mem_append]
          exact .inr h

end Blanc

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.Proxy

/-- The proxy's `DELEGATECALL` to an undelegated non-precompile `I` enters a code frame. -/
theorem dc_enter_run {sevm : Sevm} {devm : Devm} {f : Frame} {rsm : Resume} {I : Adr} {g : B256}
    {S : List B256} (hfork : CoveredFork sevm.benvStat.fork)
    (spawn : Xinst.step sevm devm .delegatecall = .spawn f rsm)
    (hstack : devm.stack = g :: I.toB256 :: S)
    (undelegated : getDelegatedCodeAddress (devm.getCode I) = none)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp I) :
    f.enter = .run (initEvm (f.inner.withBenv f.inner.benv)) := by
  obtain ⟨-, hA, -⟩ := Xinst.step_delegatecall_spawn_exact hfork spawn hstack
    (by rw [toAdr_toB256]; exact undelegated)
  rw [toAdr_toB256] at hA
  obtain ⟨-, -, -, hstv, hstat, -⟩ := Xinst.step_delegatecall_spawn_meta hfork spawn
  have hbt : f.inner.benvAfterTransfer = .ok f.inner.benv := by
    unfold Msg.benvAfterTransfer
    simp only [hstv, Bool.false_eq_true, false_and, ↓reduceIte]
  exact Frame.enter_run_of_nonprecompile hbt hA (by
    show f.inner.benv.stat.rules.isPrecomp I = false
    rw [hstat]
    exact propext ⟨fun h => absurd h notPrecompile, fun h => absurd h Bool.false_ne_true⟩)

/-- **A successful non-admin proxy frame spawns on its chain.** -/
theorem proxy_spawn_exists {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork)
    {I : Adr} (slot : (pre.state.getStor sevm.currentTarget).get implSlot = I.toB256)
    (notAdmin : sevm.caller ≠ adminOf pre.state sevm.currentTarget)
    (undelegated : getDelegatedCodeAddress (pre.state.getCode I) = none)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp I) :
    ∃ (N : Exec.Deriv) (f : Frame) (rsm : Resume) (pc' : Nat),
      Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N ∧
        Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc' := by
  obtain ⟨f0, hf0, hrun⟩ := lift_sound_in cert_check codeEq fork run
  obtain rfl : f0 = t_0000_c0 := Option.some.inj (hf0.symm.trans rfl)
  generalize hR : (⟨0, sevm, pre, .ok post, run⟩ : Exec.Deriv) = R at hrun
  rw [St.self' pre] at hrun
  rcases proxy_halt (P := StepIn R) (fun h => StepIn.toRun h) fork hrun with
    ⟨-, b', g, S, M, G, d1, hb', step, tail⟩ | ⟨hadm, -⟩
  swap
  · exact (notAdmin (by rw [adminOf_eq]; exact hadm)).elim
  obtain ⟨⟨w, st, hst, hw⟩, -, -⟩ := dl_tail_halted (fun h => StepIn.toRun h) tail
  have hv : pre.getStorVal sevm.currentTarget implSlot = I.toB256 := slot
  rw [hv] at step
  obtain ⟨xl, filled, pc, steprun⟩ := step
  have xrun : Xinst.Run sevm (St b' (g :: I.toB256 :: 0 :: sevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G) .delegatecall xl
      (.ok d1) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using steprun
  have hcode : (St b' (g :: I.toB256 :: 0 :: sevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G).getCode I =
      pre.state.getCode I := by
    rw [getCode_St, getCode_of_state hb']; rfl
  unfold Xinst.Run at xrun
  cases hs : Xinst.step sevm (St b' (g :: I.toB256 :: 0 :: sevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G) .delegatecall with
  | done ex =>
      rw [hs] at xrun
      obtain ⟨-, hex⟩ := xrun
      obtain ⟨s', hs'⟩ := Xinst.step_delegatecall_done_flag fork (hs.trans (by rw [← hex]))
      rw [hs'] at hst
      simp only [List.cons.injEq] at hst
      exact (hw hst.1.symm).elim
  | spawn f rsm =>
      have henter := dc_enter_run fork hs rfl (by rw [hcode]; exact undelegated) notPrecompile
      rw [hs] at xrun
      obtain ⟨r, hframe, -⟩ := xrun
      unfold RunFrame at hframe
      rw [henter] at hframe
      obtain ⟨raw, rfl, -⟩ := hframe
      obtain ⟨e, he⟩ := filled
      have hroot := he _ List.mem_cons_self
      subst hR
      rcases List.mem_cons.mp hroot with heq | hmem
      · exfalso
        obtain ⟨hd0, hdepth, -⟩ := Xinst.step_delegatecall_spawn_meta fork hs
        have hsevm := congrArg Exec.Deriv.sevm heq
        have hd := congrArg Sevm.depth hsevm
        change f.inner.depth = sevm.depth at hd
        omega
      · exact Exec.spawn_of_mem_rawFrameDescendants run (.refl _) _ hmem

/-- A clean successful raw run of a call frame settles to itself. -/
theorem Frame.settle_ok_clean {f : Frame} {x : Devm} (hf : f.isCreate = false)
    (hsg : f.inner.benv.stat.rules.stateGas = none) (hx : x.error = none) :
    f.settle (.ok x) = .ok x := by
  unfold Frame.settle Frame.settleMsg
  rw [hsg, hf]
  simp only [executeCode.handleErrorWith, executeCode.handleError, processMessage.settle, bind,
    Except.bind, hx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

/-- Every `DELEGATECALL` node of the proxy certificate is followed by `dlTail`. -/
def tailCheck (n : Ninst) (f : SFunc) : Bool := n != .exec .delegatecall || f == dlTail

theorem tail_checked : ∀ f ∈ Proxy.cert.prog, f.nodesSatisfy tailCheck = true := by decide

/-- **A successful non-admin proxy frame ends in its child's output and state.** -/
theorem proxy_forwards_ok {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork)
    {I : Adr} (slot : (pre.state.getStor sevm.currentTarget).get implSlot = I.toB256)
    (notAdmin : sevm.caller ≠ adminOf pre.state sevm.currentTarget)
    (undelegated : getDelegatedCodeAddress (pre.state.getCode I) = none)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp I) :
    ∀ post, out = .ok post → ∃ c ∈ Exec.childFrames run,
      post.output = c.post.output ∧ post.state = c.post.state := by
  intro post hout
  subst hout
  obtain ⟨N, f, rsm, pc', chain, step⟩ :=
    proxy_spawn_exists run codeEq fork slot notAdmin undelegated notPrecompile
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeFork : CoveredFork N.sevm.benvStat.fork := by rw [sevmEq]; exact fork
  have hexn : N.exn = .ok post := Exec.Deriv.ParentPrefix.exn_eq chain
  obtain ⟨g, K, ⟨rfl, hd⟩ | ⟨-, hs, -⟩⟩ := proxy_node run codeEq fork chain hat
  swap
  · exact (notAdmin (by rw [adminOf_eq]; exact hs.1)).elim
  obtain ⟨-, b', w0, S0, M0, G0, rest0, hstate0, -, hdev⟩ := hd
  change N.devm = _ at hdev
  have hv : pre.getStorVal sevm.currentTarget implSlot = I.toB256 := slot
  rw [hv] at hdev
  have hstackN : N.devm.stack = w0 :: I.toB256 :: (0 :: sevm.data.length.toB256 :: 0 :: 0 :: S0) := by
    rw [hdev]; rfl
  have hcodeN : N.devm.getCode I = pre.state.getCode I := by
    rw [hdev, getCode_St, getCode_of_state hstate0]; rfl
  have henterN := dc_enter_run nodeFork hx hstackN (by rw [hcodeN]; exact undelegated)
    (by rw [sevmEq]; exact notPrecompile)
  obtain ⟨-, -, hcreate, -, hstat, parent, oi, os, hrsm⟩ :=
    Xinst.step_delegatecall_spawn_meta nodeFork hx
  have hsg : f.inner.benv.stat.rules.stateGas = none := by
    rw [hstat]; exact nodeFork.rules_stateGas_none
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl codeEq fork chain
  obtain ⟨gt, hf, hgt⟩ := ok.nodesSatisfy_exec (Reach.nodesSatisfy tail_checked reach).1 hat
  have hgt' : gt = dlTail := by
    simp only [tailCheck, bne_self_eq_false, Bool.false_or, beq_iff_eq] at hgt
    exact hgt
  subst hgt'
  obtain ⟨N1, κ1, edge, -, -, synthetic, -, ok1⟩ := cursor_next_forward cert_check ok hf hexn nodeFork
  have htree : κ1.f = dlTail := by
    clear reach ok
    rcases κ with ⟨f0, pc0, a0, m0, K0⟩
    dsimp only at hf
    subst hf
    cases synthetic
    rfl
  have hexn1 : N1.exn = .ok post := by
    rw [← hexn]
    cases edge <;> rfl
  have sevm1 : N1.sevm = N.sevm := Cursor.parentStep_sevm edge
  -- the tail from the resumed node
  have tailRun : SFunc.RunP (StepIn N1) Proxy.cert.prog N1.sevm N1.devm dlTail (.halted post) := by
    obtain ⟨S1, base, stack, frame, -⟩ := ok1.stack
    have check : checkNodeM Proxy.code Proxy.cert.entries [] false κ1.m N1.pc κ1.a [] κ1.f = true := by
      rw [ok1.pc_eq, ← checkNode_eq_checkNodeM]
      exact ok1.check
    have source := node_soundM (Cert.checkedM_of_check cert_check) N1 N1
      (fun r member => List.mem_cons_of_mem _ member) post hexn1 ok1.code_eq
      (by rw [sevm1]; exact nodeFork) κ1.m κ1.a κ1.f (Cont.tagOf κ1.K) S1 base [] check stack frame
      (memMatches_nil _ _)
    rw [htree] at source
    rcases source with halted | ⟨_, returned, _, _, _, run1, _, _⟩
    · exact halted
    · exact (SFunc.RunP.not_returned_of_haltsOnly run1 (by decide)).elim
  obtain ⟨⟨w, st, hst, hw⟩, hout, hstate⟩ :=
    dl_tail_halted (fun h => StepIn.toRun h) tailRun
  clear tailRun ok1 htree hexn1 sevm1
  cases edge with
  | cont hstep next => cases hstep.symm.trans step
  | doneOk hstep henter hresume next =>
      obtain ⟨hf1, -, -⟩ := Step.spawn.inj (step.symm.trans hstep)
      subst hf1
      rw [henterN] at henter
      cases henter
  | runOk hstep henter child hresume next =>
      obtain ⟨hf1, hr1, hp1⟩ := Step.spawn.inj (step.symm.trans hstep)
      subst hf1 hr1 hp1
      subst hrsm
      rcases Resume.call_run_inv hcreate hsg hresume with ⟨xr, rfl, hxe, -, hstS, hrd⟩ | ⟨s0, hs0⟩
      swap
      · rw [hs0] at hst
        simp only [List.cons.injEq] at hst
        exact (hw hst.1.symm).elim
      have hcommit : Frame.settlementCommits f (.ok xr) = true := by
        unfold Frame.settlementCommits
        rw [Frame.settle_ok_clean hcreate hsg hxe]
        simp only [hxe, Option.isNone_none]
      refine ⟨Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits hcommit), ?_, ?_, ?_⟩
      · apply Exec.Deriv.ParentPrefix.childFrames_subset chain
        simp only [Exec.childFrames, hcommit, ↓reduceDIte, List.mem_append, List.mem_singleton, true_or]
      · show post.output = xr.output
        have hce : _ = _ := FrameEntry.run.inj (henter.symm.trans henterN)
        subst hce
        have hrel := ReturnDataBound.exec_output child hsg
        have hprov : ReturnDataBound.OutputProvenance _ xr := hrel
        have hlen : xr.output.length < 2 ^ 256 := by
          rcases hprov with h | h
          · rw [← h]
            show ([] : Bytes).length < 2 ^ 256
            decide
          · exact h
        rw [hout, hrd, B256.toNat_toB256_of_lt hlen, sliceD_zero_length]
      · exact hstate.trans hstS

/-- **C2, the proxy frame theorem** (non-admin branch), for calldata shorter than `2 ^ 256` bytes.
`proxy_forwards` as frozen, with the one added premise `dataBound`: `CALLDATASIZE` pushes the length
modulo `2 ^ 256`, so without it the child receives only that many bytes of the calldata. -/
theorem proxy_forwards_bounded {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (fork : CoveredFork sevm.benvStat.fork)
    {I : Adr} (slot : (pre.state.getStor sevm.currentTarget).get implSlot = I.toB256)
    (notAdmin : sevm.caller ≠ adminOf pre.state sevm.currentTarget)
    (undelegated : getDelegatedCodeAddress (pre.state.getCode I) = none)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp I)
    (dataBound : sevm.data.length < 2 ^ 256) :
    (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall) ∧
    (∀ c ∈ Exec.childFrames run, c.sevm.currentTarget = sevm.currentTarget ∧
      c.sevm.codeAddress = some I ∧ c.sevm.caller = sevm.caller ∧ c.sevm.value = sevm.value ∧
      c.sevm.data = sevm.data ∧ c.sevm.isStatic = sevm.isStatic ∧
      c.sevm.code = pre.state.getCode I) ∧
    (∀ post, out = .ok post → ∃ c ∈ Exec.childFrames run,
      post.output = c.post.output ∧ post.state = c.post.state) := by
  refine ⟨fun N chain x hat => ?_, fun c member => ?_,
    proxy_forwards_ok run codeEq fork slot notAdmin undelegated notPrecompile⟩
  · obtain ⟨g, K, ⟨hx, -⟩ | ⟨-, hs, -⟩⟩ := proxy_node run codeEq fork chain hat
    · exact hx
    · exact (notAdmin (by rw [adminOf_eq]; exact hs.1)).elim
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := proxy_child run codeEq fork slot notAdmin undelegated c member
    refine ⟨h1, h2, h3, h4, ?_, h6, h7⟩
    rw [h5, B256.toNat_toB256_of_lt dataBound, sliceD_zero_length]

end Blanc.Lift.Usdc
