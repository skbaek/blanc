import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.World

/-!
# A setup root call through the clone settles

A root call `callMsg` from `creator` enters the clone's forwarder, which `DELEGATECALL`s the
implementation.  `forwarder_root` turns the kernel facts of such a run, evaluated at Prague over
a closed input world `W`, into the settled message result of the actual call on any covered
fork:

* the walks transport with `walk_transport` (`Blanc/Lift/NodeWalkFork.lean`);
* the implementation frame is supplied as `hchild` (what every derivation of it does);
* the clean raw result settles to itself (`frame_settle_ok`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach
open Jaune.Exec.Deriv (ParentStep ParentPrefix)

/-- What the kernel facts need of a frame's static machine: a covered fork and no excess blob
gas. -/
def KOK (s : Sevm) : Prop := CoveredFork s.benvStat.fork ∧ s.benvStat.excessBlobGas = 0

theorem KOK.of_stat {s t : Sevm} (h : t.benvStat = s.benvStat) (hs : KOK s) : KOK t := by
  rw [KOK, h]; exact hs

/-- **A walk transports** from the kernel's machine to any covered fork. -/
theorem walk_transport {s : Sevm} {g : Fork} (hs : KOK s) (hg : CoveredFork g)
    (pol : HashPol) {code : ByteArray} {dd : Nat} (T : CodeTries code dd) (ok : Nat → Bool)
    (n : Nat) (c : PCfg) : pwalkH pol T (s.withFork g) ok n c = pwalkH pol T s ok n c :=
  pwalkH_withFork hs.1 hg hs.2 pol T ok n c

theorem mem_emptyWithCapacity_keys (x : Adr × B256) :
    x ∈ (Std.HashSet.emptyWithCapacity : Std.HashSet (Adr × B256)) ↔
      x ∈ ([] : List (Adr × B256)) := by
  simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]

theorem mem_emptyWithCapacity_adrs (a : Adr) :
    a ∈ (Std.HashSet.emptyWithCapacity : AdrSet) ↔ a ∈ ([] : List Adr) := by
  simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]

/-- **A setup root call through the clone settles cleanly.**  From the kernel facts of the
forwarder frame (its walk to the `DELEGATECALL`, the prepared implementation frame, its walk
after the child, its `RETURN`) and what every derivation of the implementation frame does
(`hchild`), the actual message `callMsg g W data gas` (= `(callMsg .prague W data gas).withFork g`) settles to the forwarder's halted machine, which the final shadows describe. -/
theorem forwarder_root {g : Fork} (hg : CoveredFork g) {W : State} {acs : AcctShadow}
    {stor : StorShadow} {data : Bytes} {gas : Nat} {e eB : Evm} {c1 cl c3 : PCfg}
    {cp : CallPrep} {dB d2 dT : Devm}
    (hW : WorldIs W acs stor)
    (he : frameEnterS (Frame.ofCall (callMsg .prague W data gas)) acs = .run e)
    (hst : (e.pc, e.sta.currentTarget, e.sta.code, e.sta.benvStat.fork,
      e.sta.benvStat.excessBlobGas) =
      (0, proxyAddr, Blanc.forwarderCode Blanc.curvePlainImpl847e, .prague, 0))
    (w1 : pwalkH .refuse fwdTries e.sta okAny 11
      (childCfg e (Frame.ofCall (callMsg .prague W data gas)) [] [] stor acs) = .cont c1)
    (p1 : c1.pc = 31) (d1 : decodeT 6 fwdTries.bytes 31 = some (.next (.exec .delegatecall)))
    (hp : dcallPrep e.sta c1.devm c1.adrs c1.acs = some cp)
    (heB : frameEnterS cp.f c1.acs = .run eB) (hca : cp.f.inner.codeAddress = some implAddr)
    (hchild : KOK eB.sta → PAgree (childCfg eB cp.f c1.keys cp.adrs c1.stor c1.acs) →
      ∀ x, NodeAt (eB.sta.withFork g)
        (childCfg eB cp.f c1.keys cp.adrs c1.stor c1.acs) x →
        x.exn = .ok dB ∧ ChildAgree dB cl.keys cl.adrs cl.stor cl.acs)
    (hdB : dB.error = none) (hr : resumeCallB cp.p cp.oi cp.os (.ok dB) = some d2)
    (w3 : pwalkH .refuse fwdTries e.sta okAny 10
      ⟨c1.pc + 1, d2, c1.keys ++ cl.keys, cp.adrs ++ cl.adrs, cl.stor, cl.acs⟩ = .cont c3)
    (w4 : pwalkH .refuse fwdTries e.sta okAny 1 c3 = .halt (.ok dT)) (hdT : dT.error = none) :
    processMessage (callMsg g W data gas) = .ok dT ∧
      ChildAgree dT c3.keys c3.adrs c3.stor c3.acs := by
  obtain ⟨hpc, -, hcode, hfork, hx⟩ :
      e.pc = 0 ∧ e.sta.currentTarget = proxyAddr ∧
        e.sta.code = Blanc.forwarderCode Blanc.curvePlainImpl847e ∧
        e.sta.benvStat.fork = .prague ∧ e.sta.benvStat.excessBlobGas = 0 := by
    simp only [Prod.mk.injEq] at hst; exact hst
  have hs : KOK e.sta := ⟨by rw [hfork]; exact .prague, hx⟩
  have hsB : KOK eB.sta :=
    KOK.of_stat ((frameEnterS_stat heB).trans (dcallPrep_stat hp).2) hs
  -- the actual entry
  have hp0 : (Frame.ofCall (callMsg .prague W data gas)).PrecompNeutral :=
    Frame.precompNeutral_of_codeAddress (a := proxyAddr) rfl (by decide) (by decide)
  have hentK : (Frame.ofCall (callMsg .prague W data gas)).enter = .run e := by
    rw [frame_enter_eq_B, frameEnterB_eq_S hW.1]; exact he
  have hent : (Frame.ofCall (callMsg g W data gas)).enter = .run (e.withFork g) := by
    rw [callMsg_withFork g W data gas]
    show ((Frame.ofCall (callMsg .prague W data gas)).withFork g).enter = _
    rw [frame_enter_withFork (f := Frame.ofCall (callMsg .prague W data gas))
      CoveredFork.prague CoveredFork.prague hg hp0, hentK]
    rfl
  rw [MessageExecution.processMessage_eq_settle_exec_of_enter _ _ hent]
  -- every derivation of the forwarder frame succeeds with `dT`
  have hcT : (e.sta.withFork g).code =
      Blanc.forwarderCode Blanc.curvePlainImpl847e := hcode
  have hag0 : PAgree (childCfg e (Frame.ofCall (callMsg .prague W data gas)) [] [] stor acs) :=
    frameStart_agree .undefined he mem_emptyWithCapacity_keys mem_emptyWithCapacity_adrs
      hW.2 hW.1
  have w1' := (walk_transport hs hg .refuse fwdTries okAny 11 _).trans w1
  have w3' := (walk_transport hs hg .refuse fwdTries okAny 10 _).trans w3
  have w4' := (walk_transport hs hg .refuse fwdTries okAny 1 _).trans w4
  obtain ⟨hag1, h1⟩ := pwalkH_cont .refuse fwdTries hcT okAny 11 _ c1 hag0 w1'
  have hat1 : Ninst.At (e.sta.withFork g).code c1.pc (.exec .delegatecall) := by
    rw [hcT, p1]; exact decodeT_sound fwdTries d1
  obtain ⟨sB, nB⟩ := dcallSpawn_withFork hs.1 hg hp
    (Frame.precompNeutral_of_codeAddress hca (by decide) (by decide)) heB
  obtain ⟨stepT, entB, -, hagB0, hFT⟩ := delegatecall_node hag1 hat1 sB nB
  have hout : ∀ (out : Execution)
      (R : Exec 0 (e.sta.withFork g) e.dyna out), out = .ok dT ∧
      ChildAgree dT c3.keys c3.adrs c3.stor c3.acs := by
    intro out R
    have hP0 : NodeAt (e.sta.withFork g)
        (childCfg e (Frame.ofCall (callMsg .prague W data gas)) [] [] stor acs)
        ⟨0, e.sta.withFork g, e.dyna, out, R⟩ := ⟨hpc.symm, rfl, rfl⟩
    obtain ⟨x1, hx1, -, ex01, -, -⟩ := h1 _ hP0
    obtain ⟨-, x2, -, -, -, hx2, ex2, -, hag2⟩ :=
      spawn_resume_ok (cl := cl) hx1 hag1 hFT stepT entB hdB hr
        (fun ch hch => hchild hsB hagB0 ch hch)
    obtain ⟨hag3, h3⟩ := pwalkH_cont .refuse fwdTries hcT okAny 10 _ c3 hag2 w3'
    obtain ⟨x3, hx3, -, ex3, -, -⟩ := h3 x2 hx2
    obtain ⟨ex4, -, -⟩ := pwalkH_halt .refuse fwdTries hcT okAny 1 c3 _ hag3 w4' x3 hx3
    refine ⟨?_, halt1_childAgree fwdTries hag3 w4'⟩
    show (⟨0, e.sta.withFork g, e.dyna, out, R⟩ : Exec.Deriv).exn = _
    rw [← ex01, ← ex2, ← ex3]; exact ex4
  obtain ⟨R⟩ := (exec_iff_exec_eq 0 (e.sta.withFork g) e.dyna _).mpr rfl
  obtain ⟨hex, hca3⟩ := hout _ R
  have hexec : exec (e.withFork g) = .ok dT := by
    have h0 : e.withFork g = ⟨0, e.sta.withFork g, e.dyna⟩ := by
      show (⟨e.pc, e.sta.withFork g, e.dyna⟩ : Evm) = _
      rw [hpc]
    rw [h0]; exact hex
  rw [hexec]
  exact ⟨frame_settle_ok rfl (CoveredFork.rules_stateGas_none (s := (callBenv g W).stat) hg) hdT,
    hca3⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
