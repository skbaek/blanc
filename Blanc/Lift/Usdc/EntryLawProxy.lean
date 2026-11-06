import Blanc.Lift.Usdc.EntryLawProxyHalt
import Blanc.Lift.Usdc.ProxyOk
import Blanc.Lift.Usdc.ImplSpawns
import Blanc.Lift.HistSpawnExact
import Blanc.LockExclusion
import Blanc.Lift.BalanceLocality

/-!
# A committed non-admin proxy frame is its implementation's frame

`proxy_entry_child`: on a historical fork, a committed proxy frame whose caller is not the admin word ran
`_delegate`, and the child committed: a frame of the implementation's code at the proxy's storage, with the proxy's
caller, value, static flag and calldata, entered at the proxy's storage and leaving the proxy's post storage. So a frame
law of the implementation is a frame law of the proxy.

`proxy_forwards_ok` is this on `CoveredFork`, with the child's place among the frame's children, which a frame law
does not read.
-/

namespace Blanc

open Jaune

/-- `Xinst.step_delegatecall_spawn_meta` from `rules.stateGas = none`. -/
theorem Xinst.step_delegatecall_spawn_meta_noStateGas {sevm : Sevm} {devm : Devm} {f : Frame} {rsm : Resume}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (spawn : Xinst.step sevm devm .delegatecall = .spawn f rsm) :
    f.isCreate = false ∧ f.inner.shouldTransferValue = false ∧ f.inner.benv.stat = sevm.benvStat ∧
      ∃ (parent : Devm) (oi os : Nat), rsm = .call parent oi os := by
  have hx := spawn
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [hsg] at hx
  dsimp only at hx
  repeat' split at hx
  all_goals simp only [XStep.ofExcept, reduceCtorEq, Pure.pure, Except.pure] at hx
  all_goals first
    | cases hx
    | (obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact hx
       exact ⟨rfl, rfl, rfl, _, _, _, rfl⟩)

/-- `Xinst.step_delegatecall_done_flag` from `rules.stateGas = none`. -/
theorem Xinst.step_delegatecall_done_flag_noStateGas {sevm : Sevm} {devm d : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (done : Xinst.step sevm devm .delegatecall = .done (.ok d)) :
    ∃ s, d.stack = 0 :: s := by
  have hx := done
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [hsg] at hx
  dsimp only at hx
  repeat' split at hx
  all_goals simp only [XStep.ofExcept, Pure.pure, Except.pure] at hx
  all_goals first
    | cases hx
    | (simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at hx
       repeat' split at hx
       all_goals simp only [XStep.ofExcept, reduceCtorEq, XStep.done.injEq, Except.ok.injEq] at hx
       all_goals subst hx
       rename_i pushed pushEq
       exact ⟨_, (Devm.push_of_push pushEq).stack⟩)

/-- A `DELEGATECALL`'s entered child starts from the parent's storage at each protected owner. -/
theorem Xinst.step_delegatecall_enter_getStor {sevm : Sevm} {pre : Devm} {frame : Jaune.Frame} {resume : Resume}
    {child : Evm} (hsg : sevm.benvStat.rules.stateGas = none)
    (spawn : Xinst.step sevm pre .delegatecall = .spawn frame resume)
    (enter : frame.enter = .run child) (owner : Adr) (protection : State.Protected pre.state owner) :
    Devm.getStor child.dyna owner = Devm.getStor pre owner := by
  have messageFacts : frame.inner.benv.state.getStor owner = pre.getStor owner ∧
      State.Protected frame.inner.benv.state owner := by
    rcases Xinst.step_shapeNoStateGas sevm pre .delegatecall hsg with
      ⟨execution, shape, -⟩ |
      ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
      ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
      rw [shape] at spawn
    · cases spawn
    · have create := (Xinst.step_delegatecall_spawn_meta_noStateGas hsg (by rw [shape]; exact spawn)).1
      rcases genericCreate_step_spawn_exact spawn with ⟨rfl, -⟩
      cases create
    · rcases genericCall_step_spawn_exact spawn with ⟨rfl, -⟩
      refine ⟨(hprefix.getStor owner).symm, ?_⟩
      change State.Protected d.state owner
      rw [← hprefix.state]
      exact protection
  rcases Frame.enter_run_inv enter with ⟨benv, transfer, rfl⟩
  exact (benvAfterTransfer_ok_getStor transfer owner (Or.inr messageFacts.2)).trans messageFacts.1

end Blanc

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.Proxy Blanc.Lift.WriteSite

/-- What a proxy frame's committed implementation child shares with it. -/
structure EntryChild (sevm : Sevm) (pre post : Devm) (C : ByteArray) (G : Exec.Frame) : Prop where
  pc : G.pc = 0
  code : G.sevm.code = C
  target : G.sevm.currentTarget = sevm.currentTarget
  caller : G.sevm.caller = sevm.caller
  data : G.sevm.data = sevm.data
  stat : G.sevm.benvStat = sevm.benvStat
  hasCode : (G.pre.getCode sevm.currentTarget).toList ≠ []
  codeLib : ∀ a, (pre.getCode a).toList ≠ [] → G.pre.getCode a = pre.getCode a
  preStor : Devm.getStor G.pre sevm.currentTarget = Devm.getStor pre sevm.currentTarget
  postStor : Devm.getStor post sevm.currentTarget = Devm.getStor G.post sevm.currentTarget
  wf : Mem.Wf G.pre.memory

theorem EntryChild.env {sevm : Sevm} {pre post : Devm} {C : ByteArray} {G : Exec.Frame}
    (h : EntryChild sevm pre post C G) : Env.root G.sevm = Env.root sevm := by
  unfold Env.root
  rw [h.caller, h.target, h.data]

/-- **A committed proxy frame off the five admin selectors has a caller other than the admin word**: the fallback
reverts for the admin. -/
theorem proxy_notAdmin {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) (sel : Blanc.Sevm.selector sevm ∉ adminSelectors) :
    sevm.caller ≠ adminOf pre.state sevm.currentTarget := by
  obtain ⟨f0, hf0, hrun⟩ := lift_sound_in_noStateGas cert_check codeEq hsg run
  obtain rfl : f0 = t_0000_c0 := Option.some.inj (hf0.symm.trans rfl)
  generalize hR : (⟨0, sevm, pre, .ok post, run⟩ : Exec.Deriv) = R at hrun
  rw [St.self' pre] at hrun
  rcases proxy_haltH_sel (P := StepIn R) (fun h => StepIn.toRun h) bal hrun with step | hadm
  · rw [adminOf_eq]
    exact step.1
  · exact (sel hadm.2).elim

/-- **A committed non-admin proxy frame is its implementation's frame.** -/
theorem proxy_entry_child {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (hasCode : (pre.getCode sevm.currentTarget).toList ≠ [])
    (notAdmin : sevm.caller ≠ adminOf pre.state sevm.currentTarget)
    (notDelegation : ¬ isValidDelegation (pre.getCode (pre.getStorVal sevm.currentTarget implSlot).toAdr))
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp (pre.getStorVal sevm.currentTarget implSlot).toAdr)
    (hsize : sevm.data.length < 2 ^ 256) :
    ∃ G : Exec.Frame, EntryChild sevm pre post
      (pre.getCode (pre.getStorVal sevm.currentTarget implSlot).toAdr) G := by
  obtain ⟨f0, hf0, hrun⟩ := lift_sound_in_noStateGas cert_check codeEq hsg run
  obtain rfl : f0 = t_0000_c0 := Option.some.inj (hf0.symm.trans rfl)
  generalize hR : (⟨0, sevm, pre, .ok post, run⟩ : Exec.Deriv) = R at hrun
  rw [St.self' pre] at hrun
  rcases proxy_haltH (P := StepIn R) (fun h => StepIn.toRun h) bal hrun with
    ⟨-, b', g, S, M, G, d1, hb', step, tail⟩ | hadm
  swap
  · exact (notAdmin (by rw [adminOf_eq]; exact hadm)).elim
  obtain ⟨⟨w, st, hst, hw⟩, -, hstate⟩ := dl_tail_halted (fun h => StepIn.toRun h) tail
  generalize hword : pre.getStorVal sevm.currentTarget implSlot = word at *
  obtain ⟨xl, filled, pc, steprun⟩ := step
  have xrun : Xinst.Run sevm (St b' (g :: word :: 0 :: sevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G) .delegatecall xl
      (.ok d1) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using steprun
  have codeSame : ∀ a, (St b' (g :: word :: 0 :: sevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G).getCode a = pre.getCode a := by
    intro a
    rw [St_getCode, getCode_of_state hb']
  have storSame : ∀ a, Devm.getStor (St b' (g :: word :: 0 :: sevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G) a = Devm.getStor pre a := by
    intro a
    simp only [Devm.getStor, Devm.getAcct]
    rw [show (St b' (g :: word :: 0 :: sevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G).state = pre.state from hb']
  unfold Xinst.Run at xrun
  cases hs : Xinst.step sevm (St b' (g :: word :: 0 :: sevm.data.length.toB256 :: 0 :: 0 :: S)
      (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G) .delegatecall with
  | done ex =>
    rw [hs] at xrun
    obtain ⟨-, hex⟩ := xrun
    obtain ⟨s', hs'⟩ := Xinst.step_delegatecall_done_flag_noStateGas hsg (hs.trans (by rw [← hex]))
    rw [hs'] at hst
    simp only [List.cons.injEq] at hst
    exact (hw hst.1.symm).elim
  | spawn f rsm =>
    obtain ⟨hcreate, hstv, hstat, parent, oi, os, hrsm⟩ := Xinst.step_delegatecall_spawn_meta_noStateGas hsg hs
    have undelegated : getDelegatedCodeAddress (pre.getCode word.toAdr) = none := by
      unfold getDelegatedCodeAddress
      simp only [notDelegation, ↓reduceIte]
    obtain ⟨hT, hA, hC, -, -, hK⟩ := step_delegatecall_spawn_shapeH hsg hs rfl
      (by rw [codeSame]; exact undelegated)
    obtain ⟨-, -, -, -, hdata⟩ := Xinst.step_delegatecall_spawn_St_noStateGas hsg hs
    have hbt : f.inner.benvAfterTransfer = .ok f.inner.benv := by
      unfold Msg.benvAfterTransfer
      simp only [hstv, Bool.false_eq_true, false_and, ↓reduceIte]
    have henter : f.enter = .run (initEvm (f.inner.withBenv f.inner.benv)) :=
      Frame.enter_run_of_nonprecompile hbt hA (by
        show f.inner.benv.stat.rules.isPrecomp word.toAdr = false
        rw [hstat]
        exact propext ⟨fun h => absurd h notPrecompile, fun h => absurd h Bool.false_ne_true⟩)
    rw [hs] at xrun
    obtain ⟨r, hframe, hresume⟩ := xrun
    unfold RunFrame at hframe
    rw [henter] at hframe
    obtain ⟨raw, rfl, rfl⟩ := hframe
    obtain ⟨child, roots⟩ := filled
    have hsgf : f.inner.benv.stat.rules.stateGas = none := by
      rw [hstat]
      exact hsg
    subst hrsm
    rcases Resume.call_run_inv hcreate hsgf hresume.symm with ⟨xr, rfl, hxe, -, hstS, -⟩ | ⟨s0, hs0⟩
    swap
    · rw [hs0] at hst
      simp only [List.cons.injEq] at hst
      exact (hw hst.1.symm).elim
    have committed : Execution.commits (.ok xr) = true := by
      simp only [Execution.commits, hxe, Option.isNone_none]
    have hdataEq : f.inner.data = sevm.data := by
      rw [hdata]
      have key := Mem.read_write_zero' M (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)
      rw [List.length_sliceD] at key
      rw [show (0 : B256).toNat = 0 from rfl]
      refine key.trans ?_
      rw [B256.toNat_toB256_of_lt hsize, sliceD_zero_length]
    have protection : State.Protected pre.state sevm.currentTarget := State.Protected.of_code_ne_nil hasCode
    have rootCode : ∀ a, (pre.getCode a).toList ≠ [] →
        (initEvm (f.inner.withBenv f.inner.benv)).dyna.getCode a = pre.getCode a := by
      intro a ne
      have mem := roots _ List.mem_cons_self
      subst hR
      exact Exec.rawFrameRoots_codePreserve run a ne _ mem
    refine ⟨Exec.Frame.ofRun child committed, ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rootCode, ?_, ?_, ?_⟩⟩
    · show f.inner.code = _
      rw [hK, codeSame]
    · exact hT
    · exact hC
    · exact hdataEq
    · exact hstat
    · show ((initEvm (f.inner.withBenv f.inner.benv)).dyna.getCode sevm.currentTarget).toList ≠ []
      rw [rootCode _ hasCode]
      exact hasCode
    · have := Xinst.step_delegatecall_enter_getStor hsg hs henter sevm.currentTarget (by
        change State.Protected _ _
        have e : (St b' (g :: word :: 0 :: sevm.data.length.toB256 :: 0 :: 0 :: S)
          (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G).state = pre.state := by
          exact hb'
        rw [e]
        exact protection)
      exact this.trans (storSame _)
    · show Devm.getStor post sevm.currentTarget = Devm.getStor xr sevm.currentTarget
      simp only [Devm.getStor, Devm.getAcct, hstate, hstS]
    · exact Nat.le_refl _

end Blanc.Lift.Usdc
