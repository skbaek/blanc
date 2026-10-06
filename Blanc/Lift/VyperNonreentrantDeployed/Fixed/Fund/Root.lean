import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.World
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.Proxy

/-!
# A funding root call settles, from Prague kernel facts under a cheap original state

`forwarder_root_re` is V2's `Init.forwarder_root` for `rootCall` (any target code, any value)
whose kernel facts are evaluated over `kCall W O …` (Prague, original state `O`): given that `O`
and the real input world `W` hold the same storage (`OrigAgree W O`), the actual message
`rootCall g W …` (original state `W`) settles to the same halted machine on any covered fork
(`Blanc/Lift/NodeWalkOrig.lean`, `walk_re`, `dcallSpawn_re`, `frame_enter_re`).
`leaf_root_re` is the same for a root frame that spawns nothing (the token's `approve`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Jaune.Exec.Deriv (ParentStep ParentPrefix)

/-- The kernel facts' entry machine has the kernel message's block environment. -/
theorem reOK_root {W O : State} {t : Adr} {cd : ByteArray} {data : Bytes} {gas : Nat} {v : B256}
    {acs : AcctShadow} {e : Evm} (hO : OrigAgree W O)
    (he : frameEnterS (Frame.ofCall (kCall W O t cd data gas v)) acs = .run e)
    (hx : e.sta.benvStat.excessBlobGas = 0) (hf : e.sta.benvStat.fork = .prague) :
    ReOK W e.sta := by
  have hs := frameEnterS_stat he
  refine ⟨by rw [hf]; exact .prague, hx, ?_⟩
  rw [hs]; exact hO

/-- The actual root call enters with the transported kernel machine. -/
theorem root_enter_re {g : Fork} (hg : CoveredFork g) {W O : State} {t : Adr} {cd : ByteArray}
    {data : Bytes} {gas : Nat} {v : B256} {acs : AcctShadow} {e : Evm}
    (hW : AcctAgree W acs) (ht : t ≠ 5 ∧ t ≠ 0x100)
    (he : frameEnterS (Frame.ofCall (kCall W O t cd data gas v)) acs = .run e) :
    (Frame.ofCall (rootCall g W t cd data gas v)).enter = .run (e.re g W) := by
  have hp0 : (Frame.ofCall (kCall W O t cd data gas v)).PrecompNeutral :=
    Frame.precompNeutral_of_codeAddress (a := t) rfl ht.1 ht.2
  have hentK : (Frame.ofCall (kCall W O t cd data gas v)).enter = .run e := by
    rw [frame_enter_eq_B, frameEnterB_eq_S hW]; exact he
  rw [rootCall_re g W O]
  exact frame_enter_re CoveredFork.prague CoveredFork.prague hg hp0 hentK

/-- **A forwarder root call settles cleanly** (`Init.forwarder_root` for `rootCall`, with the
kernel facts under the original state `O`). -/
theorem forwarder_root_re {g : Fork} (hg : CoveredFork g) {W O : State} {acs : AcctShadow}
    {stor : StorShadow} {data : Bytes} {gas : Nat} {v : B256} {e eB : Evm} {c1 cl c3 : PCfg}
    {cp : CallPrep} {dB d2 dT : Devm}
    (hW : WorldIs W acs stor) (hO : OrigAgree W O)
    (he : frameEnterS (Frame.ofCall (kCall W O proxyAddr fwd data gas v)) acs = .run e)
    (hst : (e.pc, e.sta.currentTarget, e.sta.code, e.sta.benvStat.fork,
      e.sta.benvStat.excessBlobGas) = (0, proxyAddr, fwd, .prague, 0))
    (w1 : pwalkH .refuse fwdTries e.sta okAny 11
      (childCfg e (Frame.ofCall (kCall W O proxyAddr fwd data gas v)) [] [] stor acs) = .cont c1)
    (p1 : c1.pc = 31) (d1 : decodeT 6 fwdTries.bytes 31 = some (.next (.exec .delegatecall)))
    (hp : dcallPrep e.sta c1.devm c1.adrs c1.acs = some cp)
    (heB : frameEnterS cp.f c1.acs = .run eB) (hca : cp.f.inner.codeAddress = some implAddr)
    (hchild : ReOK W eB.sta → PAgree (childCfg eB cp.f c1.keys cp.adrs c1.stor c1.acs) →
      ∀ x, NodeAt ((eB.sta.withFork g).withOrig W)
        (childCfg eB cp.f c1.keys cp.adrs c1.stor c1.acs) x →
        x.exn = .ok dB ∧ ChildAgree dB cl.keys cl.adrs cl.stor cl.acs)
    (hdB : dB.error = none) (hr : resumeCallB cp.p cp.oi cp.os (.ok dB) = some d2)
    (w3 : pwalkH .refuse fwdTries e.sta okAny 10
      ⟨c1.pc + 1, d2, c1.keys ++ cl.keys, cp.adrs ++ cl.adrs, cl.stor, cl.acs⟩ = .cont c3)
    (w4 : pwalkH .refuse fwdTries e.sta okAny 1 c3 = .halt (.ok dT)) (hdT : dT.error = none) :
    processMessage (rootCall g W proxyAddr fwd data gas v) = .ok dT ∧
      ChildAgree dT c3.keys c3.adrs c3.stor c3.acs := by
  obtain ⟨hpc, -, hcode, hfork, hx⟩ :
      e.pc = 0 ∧ e.sta.currentTarget = proxyAddr ∧ e.sta.code = fwd ∧
        e.sta.benvStat.fork = .prague ∧ e.sta.benvStat.excessBlobGas = 0 := by
    simp only [Prod.mk.injEq] at hst; exact hst
  have hs : ReOK W e.sta := reOK_root hO he hx hfork
  have hsB : ReOK W eB.sta :=
    ReOK.of_stat ((frameEnterS_stat heB).trans (dcallPrep_stat hp).2) hs
  have hent := root_enter_re hg hW.1 (by decide) he
  rw [MessageExecution.processMessage_eq_settle_exec_of_enter _ _ hent]
  have hcT : ((e.sta.withFork g).withOrig W).code = fwd := hcode
  have hag0 : PAgree (childCfg e (Frame.ofCall (kCall W O proxyAddr fwd data gas v)) [] [] stor acs) :=
    frameStart_agree .undefined he mem_emptyWithCapacity_keys mem_emptyWithCapacity_adrs
      hW.2 hW.1
  have w1' := (walk_re hs hg .refuse fwdTries okAny 11 _).trans w1
  have w3' := (walk_re hs hg .refuse fwdTries okAny 10 _).trans w3
  have w4' := (walk_re hs hg .refuse fwdTries okAny 1 _).trans w4
  obtain ⟨hag1, h1⟩ := pwalkH_cont .refuse fwdTries hcT okAny 11 _ c1 hag0 w1'
  have hat1 : Ninst.At ((e.sta.withFork g).withOrig W).code c1.pc (.exec .delegatecall) := by
    rw [hcT, p1]; exact decodeT_sound fwdTries d1
  obtain ⟨sB, nB⟩ := dcallSpawn_re hs hg hp
    (Frame.precompNeutral_of_codeAddress hca (by decide) (by decide)) heB
  obtain ⟨stepT, entB, -, hagB0, hFT⟩ := delegatecall_node hag1 hat1 sB nB
  have hout : ∀ (out : Execution)
      (R : Exec 0 ((e.sta.withFork g).withOrig W) e.dyna out), out = .ok dT ∧
      ChildAgree dT c3.keys c3.adrs c3.stor c3.acs := by
    intro out R
    have hP0 : NodeAt ((e.sta.withFork g).withOrig W)
        (childCfg e (Frame.ofCall (kCall W O proxyAddr fwd data gas v)) [] [] stor acs)
        ⟨0, (e.sta.withFork g).withOrig W, e.dyna, out, R⟩ := ⟨hpc.symm, rfl, rfl⟩
    obtain ⟨x1, hx1, -, ex01, -, -⟩ := h1 _ hP0
    obtain ⟨-, x2, -, -, -, hx2, ex2, -, hag2⟩ :=
      spawn_resume_ok (cl := cl) hx1 hag1 hFT stepT entB hdB hr
        (fun ch hch => hchild hsB hagB0 ch hch)
    obtain ⟨hag3, h3⟩ := pwalkH_cont .refuse fwdTries hcT okAny 10 _ c3 hag2 w3'
    obtain ⟨x3, hx3, -, ex3, -, -⟩ := h3 x2 hx2
    obtain ⟨ex4, -, -⟩ := pwalkH_halt .refuse fwdTries hcT okAny 1 c3 _ hag3 w4' x3 hx3
    refine ⟨?_, halt1_childAgree fwdTries hag3 w4'⟩
    show (⟨0, (e.sta.withFork g).withOrig W, e.dyna, out, R⟩ : Exec.Deriv).exn = _
    rw [← ex01, ← ex2, ← ex3]; exact ex4
  obtain ⟨R⟩ := (exec_iff_exec_eq 0 ((e.sta.withFork g).withOrig W) e.dyna _).mpr rfl
  obtain ⟨hex, hca3⟩ := hout _ R
  have hexec : exec (e.re g W) = .ok dT := by
    have h0 : e.re g W = ⟨0, (e.sta.withFork g).withOrig W, e.dyna⟩ := by
      show (⟨e.pc, (e.sta.withFork g).withOrig W, e.dyna⟩ : Evm) = _
      rw [hpc]
    rw [h0]; exact hex
  rw [hexec]
  exact ⟨frame_settle_ok rfl
    (CoveredFork.rules_stateGas_none (s := (rootCall g W proxyAddr fwd data gas v).benv.stat) hg)
    hdT, hca3⟩

/-- **A leaf root call settles cleanly**: a root frame whose walk halts without spawning. -/
theorem leaf_root_re {g : Fork} (hg : CoveredFork g) {W O : State} {acs : AcctShadow}
    {stor : StorShadow} {t : Adr} {cd : ByteArray} {data : Bytes} {gas : Nat} {v : B256}
    {dd : Nat} (T : CodeTries cd dd) (pol : HashPol) {n : Nat} {e : Evm} {c1 : PCfg} {dT : Devm}
    (ht : t ≠ 5 ∧ t ≠ 0x100) (hW : WorldIs W acs stor) (hO : OrigAgree W O)
    (he : frameEnterS (Frame.ofCall (kCall W O t cd data gas v)) acs = .run e)
    (hst : (e.pc, e.sta.code, e.sta.benvStat.fork, e.sta.benvStat.excessBlobGas) =
      (0, cd, .prague, 0))
    (w1 : pwalkH pol T e.sta okAny n
      (childCfg e (Frame.ofCall (kCall W O t cd data gas v)) [] [] stor acs) = .cont c1)
    (w2 : pwalkH pol T e.sta okAny 1 c1 = .halt (.ok dT)) (hdT : dT.error = none) :
    processMessage (rootCall g W t cd data gas v) = .ok dT ∧
      ChildAgree dT c1.keys c1.adrs c1.stor c1.acs := by
  obtain ⟨hpc, hcode, hfork, hx⟩ :
      e.pc = 0 ∧ e.sta.code = cd ∧ e.sta.benvStat.fork = .prague ∧
        e.sta.benvStat.excessBlobGas = 0 := by
    simp only [Prod.mk.injEq] at hst; exact hst
  have hs : ReOK W e.sta := reOK_root hO he hx hfork
  have hent := root_enter_re hg hW.1 ht he
  rw [MessageExecution.processMessage_eq_settle_exec_of_enter _ _ hent]
  have hcT : ((e.sta.withFork g).withOrig W).code = cd := hcode
  have hag0 : PAgree (childCfg e (Frame.ofCall (kCall W O t cd data gas v)) [] [] stor acs) :=
    frameStart_agree .undefined he mem_emptyWithCapacity_keys mem_emptyWithCapacity_adrs
      hW.2 hW.1
  have w1' := (walk_re hs hg pol T okAny n _).trans w1
  have w2' := (walk_re hs hg pol T okAny 1 _).trans w2
  obtain ⟨hca, hall⟩ := leaf_frame_ok pol T hcT okAny hag0 w1' w2'
  obtain ⟨R⟩ := (exec_iff_exec_eq 0 ((e.sta.withFork g).withOrig W) e.dyna _).mpr rfl
  have hP0 : NodeAt ((e.sta.withFork g).withOrig W)
      (childCfg e (Frame.ofCall (kCall W O t cd data gas v)) [] [] stor acs)
      ⟨0, (e.sta.withFork g).withOrig W, e.dyna, _, R⟩ := ⟨hpc.symm, rfl, rfl⟩
  have hex := (hall _ hP0).1
  have hexec : exec (e.re g W) = .ok dT := by
    have h0 : e.re g W = ⟨0, (e.sta.withFork g).withOrig W, e.dyna⟩ := by
      show (⟨e.pc, (e.sta.withFork g).withOrig W, e.dyna⟩ : Evm) = _
      rw [hpc]
    rw [h0]; exact hex
  rw [hexec]
  exact ⟨frame_settle_ok rfl
    (CoveredFork.rules_stateGas_none (s := (rootCall g W t cd data gas v).benv.stat) hg) hdT, hca⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
