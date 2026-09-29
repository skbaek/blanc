import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.RunRest
import Blanc.Lift.NodeWalkFork

/-!
# V+ nonvacuity: an active guarded body that spawns a child, executed

`vplus_witness` exhibits, for the deployed comparator runtime at its own address
(`vplus_exclusion_impl`, `P = I`), an actual Jaune execution `R` of the top-level message
`msg0` (from the explicit Prague pre-state of `Witness/Setup.lean`) together with nodes of
`R` that inhabit the antecedent of `vplus_exclusion` exactly as `Fixed/Exclusion.lean`
states it — `F ∈ Exec.rawFrameRoots R`, `ActiveRel I F h`, `Spawns h c` — and discharges its
premises for this `R`: the covered fork, the code at `I`, the root, and `HashAvoidIn`
(no frame of `I` in `R` executes `KECCAK256` at all).  Then it applies `vplus_exclusion_impl`
to the reentrant frame `G` the child opens: `G` is a frame of `I` running the comparator,
entered by `get_virtual_price()` (a guarded view: read-only reentry) while `F` holds the
lock; the theorem states that `G` reverts and that no node of `G` is at a guarded body start
(the kernel walk passes through the lock check, but the pcs it visits are not exported here;
`vplus_witness2` does export them).

Every node is a node of `R` itself: the walks of `Blanc/Lift/NodeWalk.lean` apply to any
derivation from the concrete machines, so no particular derivation is constructed.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion Blanc.ForkUniform
open Jaune.Exec.Deriv (ParentPrefix ParentStep)

attribute [local irreducible] e0 cB cH cpH eT cTs cpT eG dG childG dT1 cT2 dF1 dF

theorem e0_pc : e0.pc = 0 := (Prod.mk.inj e0_facts).1
theorem e0_target : e0.sta.currentTarget = poolAddress :=
  (Prod.mk.inj (Prod.mk.inj e0_facts).2).1
theorem hcodeF : e0.sta.code = code := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj e0_facts).2).2).1
theorem e0_fork : e0.sta.benvStat.fork = .prague := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj e0_facts).2).2).2
theorem eT_target : eT.sta.currentTarget = readerAddress := (Prod.mk.inj (Prod.mk.inj eT_facts).2).1
theorem hcodeT : eT.sta.code = Reader.code := (Prod.mk.inj (Prod.mk.inj eT_facts).2).2
theorem eG_pc : eG.pc = 0 := (Prod.mk.inj eG_facts).1
theorem eG_target : eG.sta.currentTarget = poolAddress := (Prod.mk.inj (Prod.mk.inj eG_facts).2).1
theorem hcodeG : eG.sta.code = code := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eG_facts).2).2).1
theorem eG_data : eG.sta.data = [0xbb, 0x7b, 0x8b, 0x80] :=
  (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eG_facts).2).2).2

/-- The pool frame's entry holds the comparator at the pool. -/
theorem e0_getCode : e0.dyna.getCode poolAddress = code := by
  have h : acctView (e0.dyna.state.get poolAddress) = lookupA c0.acs poolAddress :=
    c0_agree.2.2.2 poolAddress
  show (e0.dyna.state.get poolAddress).code = code
  rw [← c0_pool_code, ← h]
  rfl

theorem e0_withFork_prague : e0.sta.withFork .prague = e0.sta := by
  have h := Sevm.withFork_self e0.sta
  rw [e0_fork] at h
  exact h

theorem e0_covered : CoveredFork e0.sta.benvStat.fork := by rw [e0_fork]; exact CoveredFork.prague

theorem e0_excess : e0.sta.benvStat.excessBlobGas = 0 := by
  rw [frameEnterS_stat e0_eq]; rfl

/-- The reader's and the reentrant frame's machines carry the pool frame's block environment. -/
theorem eT_stat : eT.sta.benvStat = e0.sta.benvStat :=
  (frameEnterS_stat enterT).trans (scallPrep_stat scallH).2

theorem eG_stat : eG.sta.benvStat = e0.sta.benvStat :=
  ((frameEnterS_stat enterG).trans (scallPrep_stat scallT).2).trans eT_stat

theorem cpH_neutral : cpH.f.PrecompNeutral := by
  refine Or.inr fun a ha => ?_
  have : cpH.f.inner.codeAddress = some readerAddress := by kernel_rfl
  rw [this] at ha
  cases ha
  decide

theorem cpT_neutral : cpT.f.PrecompNeutral := by
  refine Or.inr fun a ha => ?_
  have : cpT.f.inner.codeAddress = some poolAddress := by kernel_rfl
  rw [this] at ha
  cases ha
  decide

/-- **The run, on every derivation, under any covered fork.**  Whatever derivation `R` of the
pool frame's machine is taken, with its fork changed to any covered fork, it reverts, and it
has the nodes the V+ antecedent names.  The kernel facts of the Prague walk are transported
(`Blanc/Lift/NodeWalkFork.lean`); nothing is re-evaluated. -/
theorem vplus_run_at {S : Sevm} (hS : ∃ g, CoveredFork g ∧ S = e0.sta.withFork g)
    {out : Execution} (R : Exec 0 S e0.dyna out) :
    out = .error (.revert, dF) ∧
    ∃ h c G : Exec.Deriv,
      ActiveRel poolAddress ⟨0, S, e0.dyna, out, R⟩ h ∧ Spawns h c ∧
      lockL.HashAvoidIn poolAddress R ∧
      h.pc = 0x337a ∧ Ninst.At h.sevm.code h.pc (.exec .staticcall) ∧
      c.sevm.currentTarget = readerAddress ∧ c.sevm.code = Reader.code ∧
      G ∈ Exec.rawFrameRoots c.exc ∧ CPFrame poolAddress code G ∧
      G.sevm.data = [0xbb, 0x7b, 0x8b, 0x80] ∧ G.exn = .error (.revert, dG) ∧
      (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) := by
  obtain ⟨g, hg, rfl⟩ := hS
  have hf0 := e0_covered
  have hx0 := e0_excess
  have hfT : CoveredFork eT.sta.benvStat.fork := eT_stat ▸ hf0
  have hxT : eT.sta.benvStat.excessBlobGas = 0 := eT_stat ▸ hx0
  have hfG : CoveredFork eG.sta.benvStat.fork := eG_stat ▸ hf0
  have hxG : eG.sta.benvStat.excessBlobGas = 0 := eG_stat ▸ hx0
  obtain ⟨hoH, hiH⟩ := scallPrep_stat scallH
  obtain ⟨hoT, hiT⟩ := scallPrep_stat scallT
  have hoH' : CoveredFork cpH.f.outer.benv.stat.fork := hoH ▸ hf0
  have hiH' : CoveredFork cpH.f.inner.benv.stat.fork := hiH ▸ hf0
  have hoT' : CoveredFork cpT.f.outer.benv.stat.fork := hoT ▸ hfT
  have hiT' : CoveredFork cpT.f.inner.benv.stat.fork := hiT ▸ hfT
  -- the Prague kernel facts, transported
  have wB := (pwalk_withFork hf0 hg hx0 codeTries okAll 174 c0).trans walkB
  have wH := (pwalk_withFork hf0 hg hx0 codeTries okRel 57 cB).trans walkH
  have sH : scallPrep (e0.sta.withFork g) cH.devm cH.adrs cH.acs = some (cpH.withFork g) := by
    rw [scallPrep_withFork hf0 hg, scallH]; rfl
  have nT : frameEnterS (cpH.withFork g).f cH.acs = .run (eT.withFork g) := by
    show frameEnterS (cpH.f.withFork g) cH.acs = _
    rw [frameEnterS_withFork hoH' hiH' hg cpH_neutral, enterT]; rfl
  have wTs := (pwalk_withFork hfT hg hxT readerTries okAll 9 cT0).trans walkTs
  have sT : scallPrep (eT.sta.withFork g) cTs.devm cTs.adrs cTs.acs = some (cpT.withFork g) := by
    rw [scallPrep_withFork hfT hg, scallT]; rfl
  have nG : frameEnterS (cpT.withFork g).f cTs.acs = .run (eG.withFork g) := by
    show frameEnterS (cpT.f.withFork g) cTs.acs = _
    rw [frameEnterS_withFork hoT' hiT' hg cpT_neutral, enterG]; rfl
  have wG := (pwalk_withFork hfG hg hxG codeTries okBody 141 cG0).trans walkG
  have wT2 := (pwalk_withFork hfT hg hxT readerTries okAll 1 cT1).trans walkT2
  have wT3 := (pwalk_withFork hfT hg hxT readerTries okAll 1 cT2).trans walkT3
  have wF := (pwalk_withFork hf0 hg hx0 codeTries okAll 12 cF1).trans walkF
  have stG : (cpT.withFork g).f.settle (.error (.revert, dG)) = .ok childG :=
    (settle_withFork hoT' hiT' hg _).trans settleG
  have hcF : (e0.sta.withFork g).code = code := hcodeF
  have hcT : (eT.withFork g).sta.code = Reader.code := hcodeT
  have hcG : (eG.withFork g).sta.code = code := hcodeG
  set F : Exec.Deriv := ⟨0, e0.sta.withFork g, e0.dyna, out, R⟩ with hFdef
  have hF0 : NodeAt (e0.sta.withFork g) c0 F := ⟨e0_pc.symm, rfl, rfl⟩
  -- the pool frame to its body start and to its `STATICCALL`
  obtain ⟨hagB, hB⟩ := pwalk_cont codeTries hcF okAll 174 c0 cB c0_agree wB
  obtain ⟨xB, hxB, hFB, exB, dsB, betB⟩ := hB F hF0
  obtain ⟨hagH, hH⟩ := pwalk_cont codeTries hcF okRel 57 cB cH hagB wH
  obtain ⟨xH, hxH, hBH, exH, dsH, betH⟩ := hH xB hxB
  -- the `STATICCALL` spawns the reader frame `c`
  have hatH : Ninst.At (e0.sta.withFork g).code cH.pc (.exec .staticcall) := by
    show Ninst.At e0.sta.code cH.pc _
    rw [hcodeF, cH_pc]; exact decodeT_sound codeTries decodeH
  obtain ⟨stepH, entH, -, hagT0⟩ := staticcall_node hagH hatH sH nT
  obtain ⟨c, spH, hcpc, hcs, hcd, okH, -⟩ :=
    Exec.Deriv.step_spawn ((step_eq_of_nodeAt hxH).trans stepH) entH
  have hc0 : NodeAt (eT.withFork g).sta cT0 c := ⟨hcpc, hcs, hcd⟩
  -- the reader frame to its `STATICCALL`, which spawns `G`
  obtain ⟨hagTs, hTs⟩ := pwalk_cont readerTries hcT okAll 9 cT0 cTs hagT0 wTs
  obtain ⟨xTs, hxTs, hcTs, exTs, dsTs, -⟩ := hTs c hc0
  have hatT : Ninst.At (eT.withFork g).sta.code cTs.pc (.exec .staticcall) := by
    show Ninst.At eT.sta.code cTs.pc _
    rw [hcodeT, cTs_pc]; exact decodeT_sound readerTries decodeTs
  obtain ⟨stepT, entT, -, hagG0⟩ := staticcall_node hagTs hatT sT nG
  obtain ⟨G, spT, hgpc, hgs, hgd, okT, -⟩ :=
    Exec.Deriv.step_spawn ((step_eq_of_nodeAt hxTs).trans stepT) entT
  have hg0 : NodeAt (eG.withFork g).sta cG0 G := ⟨hgpc, hgs, hgd⟩
  -- `G` reverts
  obtain ⟨exG, dsG, allG⟩ := pwalk_halt codeTries hcG okBody 141 cG0 _ hagG0 wG G hg0
  -- the reader resumes from the failed child and stops
  obtain ⟨chG, hsG, hceG, hstG⟩ := frame_settle_error (f := cpT.f) (d := dG)
    (Prod.mk.inj cpT_facts).1 (Prod.mk.inj cpT_facts).2 (.inl rfl)
  have hchG : chG = childG := by
    have := hsG.symm.trans settleG; cases this; rfl
  subst hchG
  obtain ⟨xT1, eT1, hxT1pc, hxT1s, hxT1d, exT1, dsT1⟩ :=
    okT dT1 (by rw [exG, stG]; exact resumeCallB_sound resumeT)
  have hagT1 : PAgree cT1 := resume_agree_error (cp := cpT.withFork g) hagTs sT hceG hstG resumeT
  have hxT1 : NodeAt (eT.withFork g).sta cT1 xT1 := ⟨hxT1pc, hxT1s.trans hxTs.2.1, hxT1d⟩
  obtain ⟨hagT2, hT2⟩ := pwalk_cont readerTries hcT okAll 1 cT1 cT2 hagT1 wT2
  obtain ⟨xT2, hxT2, hT12, exT2, dsT2, -⟩ := hT2 xT1 hxT1
  obtain ⟨exT3, dsT3, -⟩ := pwalk_halt readerTries hcT okAll 1 cT2 _ hagT2 wT3 xT2 hxT2
  have exc : c.exn = .ok cT2.devm := by
    rw [← exTs, ← exT1, ← exT2, exT3]
  -- the pool frame resumes from the reader and reverts
  obtain ⟨xF1, eF1, hxF1pc, hxF1s, hxF1d, exF1, dsF1⟩ :=
    okH dF1 (by
      rw [exc, show (cpH.withFork g).f = cpH.f.withFork g from rfl, settle_withFork hoH' hiH' hg,
        frame_settle_ok (Prod.mk.inj cpH_facts).1 (Prod.mk.inj cpH_facts).2 cT2_err]
      exact resumeCallB_sound resumeF)
  have hagF1 : PAgree cF1 :=
    resume_agree_ok (cp := cpH.withFork g) hagH sH (by rw [cT2_err]; rfl) (childAgree_of_pagree hagT2) resumeF
  have hxF1 : NodeAt (e0.sta.withFork g) cF1 xF1 := ⟨hxF1pc, hxF1s.trans hxH.2.1, hxF1d⟩
  obtain ⟨exF, dsF, allF⟩ := pwalk_halt codeTries hcF okAll 12 cF1 _ hagF1 wF xF1 hxF1
  -- the pool frame executes no `KECCAK256`
  have nkH : NoKeccakAt code xH.pc := by
    intro hk
    have hd := decodeT_sound codeTries decodeH
    unfold Ninst.At at hk
    rw [hxH.1, cH_pc, hd] at hk
    cases hk
  have hBneH : xB ≠ xH := fun h => by
    have := congrArg Exec.Deriv.pc h
    rw [hxB.1, hxH.1, cB_pc, cH_pc] at this
    exact absurd this (by decide)
  have nkF : ∀ x, ParentPrefix F x → NoKeccakAt code x.pc := by
    intro x hx
    rcases parentPrefix_total hx hFB with hxb | hbx
    · by_cases hxe : x = xB
      · subst hxe; exact (betH x (.refl _) hBH hBneH).2
      · exact (betB x hx hxb hxe).2
    · rcases parentPrefix_total hbx hBH with hxh | hhx
      · by_cases hxe : x = xH
        · subst hxe; exact nkH
        · exact (betH x hbx hxh hxe).2
      · cases hhx with
        | refl => exact nkH
        | step head rest =>
          have := Jaune.Exec.Deriv.ParentStep.unique head eF1
          subst this
          exact (allF x rest).2
  -- the frame roots of `R`: `F`, the reader `c`, and `G`
  have hroots : ∀ G', G' ∈ Exec.rawFrameRoots R → G' = F ∨ G' = c ∨ G' = G := by
    intro G' hG'
    have hdesc : Exec.rawFrameDescendants R = [c, G] := by
      show Exec.rawFrameDescendants F.exc = _
      rw [← dsB, ← dsH, dsF1, ← dsTs, dsT1, dsG, dsF, ← dsT2, dsT3]
      rfl
    simp only [Exec.rawFrameRoots, hdesc, List.mem_cons, List.not_mem_nil, or_false] at hG'
    exact hG'
  have hcne : c.sevm.currentTarget ≠ poolAddress := by
    rw [hcs]; show eT.sta.currentTarget ≠ _; rw [eT_target]; decide
  refine ⟨?_, xH, c, G, ⟨⟨rfl, e0_target, hcodeF⟩, hFB.trans hBH, xB, hFB, hBH, ?_, ?_⟩, spH,
    ?_, hxH.1.trans cH_pc, ?_, hcs ▸ eT_target, hcs ▸ hcodeT, ?_,
    ⟨hgpc.trans eG_pc, hgs ▸ eG_target, hgs ▸ hcodeG⟩, hgs ▸ eG_data, exG, ?_⟩
  · show F.exn = _
    rw [← exB, ← exH, ← exF1, exF]
  · rw [hxB.1, cB_pc]; decide
  · intro x hbx hxh hne
    have := (betH x hbx hxh hne).1
    simpa [okRel] using this
  · intro G' hG' hcp
    rcases hroots G' hG' with rfl | rfl | rfl
    · exact hashAvoid_of_noKeccak hcodeF nkF
    · exact absurd hcp.2.1 hcne
    · exact hashAvoid_of_noKeccak (hgs ▸ hcodeG) (fun x hx => (allG x hx).2)
  · rw [hxH.2.1, hxH.1]; exact hatH
  · show G ∈ _ :: Exec.rawFrameDescendants c.exc
    rw [← dsTs, dsT1]
    simp
  · intro x hx
    have := (allG x hx).1
    simpa [okBody] using this


/-- **V+ nonvacuity under every covered fork.**  `vplus_witness` with the block environment's
fork changed to any covered fork `g` (Prague, Osaka, BPO1, BPO2): the top-level message
`msg0.withFork g` enters with `e0.withFork g`; every execution of that machine reverts, one
exists, and it carries the V+ antecedent, the premises of `vplus_exclusion_impl`, the spawn
and the refused reentry exactly as at Prague.  Obtained from the Prague kernel facts by
`Blanc/Lift/NodeWalkFork.lean` (the run executes no `CLZ`, the block has no excess blob gas,
and no frame enters `MODEXP` or `P256VERIFY`); nothing is re-evaluated. -/
theorem vplus_witness_covered (g : Fork) (hg : CoveredFork g) :
    (msg0.withFork g).benv.stat.fork = g ∧ (f0.withFork g).enter = .run (e0.withFork g) ∧
    (e0.withFork g).pc = 0 ∧
    (∀ out, Exec 0 (e0.withFork g).sta (e0.withFork g).dyna out → out = .error (.revert, dF)) ∧
    ∃ (out : Execution) (R : Exec 0 (e0.withFork g).sta (e0.withFork g).dyna out)
      (h c G : Exec.Deriv),
      -- the antecedent of `vplus_exclusion`, for `F` the root of `R`
      (⟨0, (e0.withFork g).sta, (e0.withFork g).dyna, out, R⟩ : Exec.Deriv) ∈
        Exec.rawFrameRoots R ∧
      ActiveRel curvePlainImpl847e ⟨0, (e0.withFork g).sta, (e0.withFork g).dyna, out, R⟩ h ∧
      Spawns h c ∧
      -- the premises of `vplus_exclusion_impl`, for this `R`
      CoveredFork (e0.withFork g).sta.benvStat.fork ∧
      (e0.withFork g).dyna.getCode curvePlainImpl847e = code ∧
      ((e0.withFork g).sta.currentTarget = curvePlainImpl847e →
        (e0.withFork g).sta.code = (e0.withFork g).dyna.getCode curvePlainImpl847e) ∧
      lockL.HashAvoidIn curvePlainImpl847e R ∧
      -- the spawn: `remove_liquidity`'s `STATICCALL` of the coin `R`
      h.pc = 0x337a ∧ Ninst.At h.sevm.code h.pc (.exec .staticcall) ∧
      c.sevm.currentTarget = readerAddress ∧ c.sevm.code = Reader.code ∧
      -- the reentry into `get_virtual_price()`, refused
      G ∈ Exec.rawFrameRoots c.exc ∧ CPFrame curvePlainImpl847e code G ∧
      G.sevm.data = [0xbb, 0x7b, 0x8b, 0x80] ∧ G.exn = .error (.revert, dG) ∧
      (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
      ¬ lockL.Enters curvePlainImpl847e G := by
  have hS : ∃ g', CoveredFork g' ∧ (e0.withFork g).sta = e0.sta.withFork g' := ⟨g, hg, rfl⟩
  obtain ⟨R⟩ := (exec_iff_exec_eq 0 (e0.withFork g).sta (e0.withFork g).dyna _).mpr rfl
  obtain ⟨-, h, c, G, act, sp, hash, hpc, hat, hct, hcc, hG, cpG, hdG, exG, nb⟩ :=
    vplus_run_at hS R
  have hfork : CoveredFork (e0.withFork g).sta.benvStat.fork := hg
  have hroot : (e0.withFork g).sta.currentTarget = curvePlainImpl847e →
      (e0.withFork g).sta.code = (e0.withFork g).dyna.getCode curvePlainImpl847e := fun _ => by
    show e0.sta.code = e0.dyna.getCode curvePlainImpl847e
    rw [hcodeF, e0_getCode]
  have hent : (f0.withFork g).enter = .run (e0.withFork g) := by
    have h0 : f0.enter = .run e0 := by
      rw [frame_enter_eq_B, frameEnterB_eq_S acctAgree0]; exact e0_eq
    have hp : f0.PrecompNeutral := Or.inr fun a ha => by
      obtain rfl := Option.some.inj ha
      decide
    rw [frame_enter_withFork CoveredFork.prague CoveredFork.prague hg hp, h0]
    rfl
  refine ⟨rfl, hent, e0_pc, fun _ R' => (vplus_run_at hS R').1, _, R, h, c, G,
    Exec.mem_rawFrameRoots_self R, act, sp, hfork, e0_getCode, hroot, hash, hpc, hat, hct, hcc,
    hG, cpG, hdG, exG, nb, ?_⟩
  exact vplus_exclusion_impl R hfork e0_getCode hroot hash (Exec.mem_rawFrameRoots_self R)
    act sp hG

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness
