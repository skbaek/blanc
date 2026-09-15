-- DripRealizedHistory.lean : actual occurrence bridges for DRIP accounting.
--
-- This module connects the pure `Drip.RealizedChain` algebra to retained
-- execution evidence.  A finite coalition is only the accounting projection:
-- later realization constructors retain their full source and target states,
-- and therefore the complete `pie` row map, alongside each projected segment.

import Blanc.DripHistory
import Blanc.DripAccounting

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Drip

/-- Normalized units held by a finite coalition in the actual target storage. -/
noncomputable def coalitionUnits (coalition : Finset Adr) (ca : Adr) (state : State) : Nat :=
  (coalition.toList.map fun holder => pieN (state.getStor ca) holder).sum

/-- The accounting projection of one actual world state at the DRIP target. -/
noncomputable def snapshot (coalition : Finset Adr) (ca : Adr) (state : State) : Snapshot where
  chi := chiN (state.getStor ca)
  rho := rhoN (state.getStor ca)
  coalitionUnits := coalitionUnits coalition ca state
  totalUnits := totalN (state.getStor ca)
  balance := (state.bal ca).toNat

/-- The actual source `drip` path never moves ETH.  The fresh-index machine
retains its full entry world in its `Frame`; after selecting `afterDrip`, the
remaining local return path is balance-invariant by the existing instruction
invariance calculus. -/
private theorem of_run_drip_balance_eq {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.drip r) :
    Devm.getBal r = Devm.getBal entry := by
  unfold Drip.drip Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 routeDrip] ?_ run
  intro s1 hline1 run
  have hpushLogs : Line.Inv Devm.logs [pushB256 routeDrip] := by
    intro e s s1 hline
    rcases Line.of_run_cons hline with ⟨_, hpush, hnil⟩
    cases hnil
    exact (of_run_pushB256 hpush).logs
  have frame1 := frame.line (by line_inv) (by line_inv) hpushLogs hline1
  have hp1 : routeDrip :: tail <<+ s1.stack := by
    rcases Line.of_run_cons hline1 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.mstoreAt hp1 hline2
  obtain ⟨t3, image3, hlower, hupper, hclock, helapsed, hguards, hnofm, hcap,
    hfresh, hnow, hmachine, frame3, hp3, run⟩ :=
    of_run_freshStart hlookup frame2 hp2 run
  have htag : scratch image3 routeWord = routeDrip := by
    rw [hmachine.1, scratch_setScratch_self]
  obtain ⟨t4, frame4, hp4, hroute⟩ := of_run_freshRoute hlookup frame3 hp3 run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact absurd (htag.symm.trans htagA) (by decide +kernel)
  · exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · exact absurd (htag.symm.trans htagU) (by decide +kernel)
  · have htail : Devm.getBal t4 = Devm.getBal r :=
      Func.of_inv Devm.getBal Devm.getBal (by func_inv) run
    funext a
    exact (congrFun htail a).symm.trans
      (getBal_eq_of_state_eq frame4.state a).symm
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

/-- The deployed `drip()` effect preserves the target balance.  This is not
inferred from the storage effect: it is reconstructed from the actual entry
and its selected source route. -/
theorem drip_exec_balance_eq {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = dripSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    Devm.getBal post sevm.currentTarget = Devm.getBal pre sevm.currentTarget := by
  rcases exec_enters_drip exc hcode hsel hnonempty with
    ⟨-, -, entry, hstate, hmemory, -, -, hrun⟩
  have hentryMemory : entry.memory = Mem.empty := hmemory.symm.trans hcanon
  have hwf : Mem.Wf entry.memory := by
    rw [hentryMemory]
    exact Mem.wf_empty
  let image := entry.memory.data.toList
  have hreads : Mem.Reads entry.memory image := by
    intro i
    simp [image]
  let hframe : Frame image entry entry := ⟨hwf, hreads, rfl, rfl⟩
  have hsource := of_run_drip_balance_eq auxLookup_runtime hframe nil_pref hrun
  exact (congrFun hsource sevm.currentTarget).trans
    (getBal_eq_of_state_eq hstate.symm sevm.currentTarget)

/-- One successful deployed `drip()` execution realizes the accounting
`drip` segment.  The segment is derived from the executed storage writes and
the reconstructed balance-preserving source route; its configuration premises
remain explicit for the later classified-occurrence bridge. -/
theorem drip_exec_realized_effect (coalition : Finset Adr) {sevm : Sevm}
    {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = dripSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    Effect scale.toNat freshNat
      (snapshot coalition sevm.currentTarget pre.state)
      (.drip (sevm.benvStat.time -
        Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat)
      (snapshot coalition sevm.currentTarget post.state) := by
  obtain ⟨hlower, hupper, hclock, hcap, hguards, hnofm, hfreshCap, hstor, hreturn⟩ :=
    drip_exec_effect exc hcode hsel hnonempty hcanon
  let elapsed := (sevm.benvStat.time -
    Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat
  have htimele : Devm.getStorVal pre sevm.currentTarget rhoSlot ≤ sevm.benvStat.time :=
    le_of_not_gt hclock
  have htime : rhoN (Devm.getStor pre sevm.currentTarget) + elapsed =
      sevm.benvStat.time.toNat := by
    change (Devm.getStor pre sevm.currentTarget).get rhoSlot ≤ sevm.benvStat.time at htimele
    unfold rhoN elapsed
    change ((Devm.getStor pre sevm.currentTarget).get rhoSlot).toNat +
      (sevm.benvStat.time -
        (Devm.getStor pre sevm.currentTarget).get rhoSlot).toNat =
        sevm.benvStat.time.toNat
    have htimeleNat := B256.toNat_le_toNat htimele
    rw [B256.toNat_sub_eq_of_le _ _ htimele]
    omega
  have hfresh :
      ((B256.rpow scale half rate elapsed *
          Devm.getStorVal pre sevm.currentTarget chiSlot) / scale).toNat =
        freshNat (chiN (Devm.getStor pre sevm.currentTarget)) elapsed := by
    unfold chiN
    exact freshChi_toNat _ _ hguards hnofm
  have hchi : chiN (Devm.getStor post sevm.currentTarget) =
      freshNat (chiN (Devm.getStor pre sevm.currentTarget)) elapsed := by
    unfold chiN
    rw [hstor, Stor.get_set_ne _ scalarSlots_distinct.1.symm _, Stor.get_set_self]
    exact hfresh
  have hrho : rhoN (Devm.getStor post sevm.currentTarget) =
      rhoN (Devm.getStor pre sevm.currentTarget) + elapsed := by
    unfold rhoN
    rw [hstor, Stor.get_set_self]
    exact htime.symm
  have htotal : totalN (Devm.getStor post sevm.currentTarget) =
      totalN (Devm.getStor pre sevm.currentTarget) := by
    unfold totalN
    rw [hstor, Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
      Stor.get_set_ne _ scalarSlots_distinct.2.1 _]
  have hpie : ∀ holder, pieN (Devm.getStor post sevm.currentTarget) holder =
      pieN (Devm.getStor pre sevm.currentTarget) holder := by
    intro holder
    unfold pieN
    rw [hstor, Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder).symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder).symm _]
  have hcoal : coalitionUnits coalition sevm.currentTarget post.state =
      coalitionUnits coalition sevm.currentTarget pre.state := by
    unfold coalitionUnits
    change (coalition.toList.map fun holder =>
      pieN (Devm.getStor post sevm.currentTarget) holder).sum =
      (coalition.toList.map fun holder =>
        pieN (Devm.getStor pre sevm.currentTarget) holder).sum
    simp_rw [hpie]
  have hbalance := drip_exec_balance_eq exc hcode hsel hnonempty hcanon
  change Effect scale.toNat freshNat
    ⟨chiN (Devm.getStor pre sevm.currentTarget),
      rhoN (Devm.getStor pre sevm.currentTarget),
      coalitionUnits coalition sevm.currentTarget pre.state,
      totalN (Devm.getStor pre sevm.currentTarget),
      (Devm.getBal pre sevm.currentTarget).toNat⟩
    (.drip elapsed)
    ⟨chiN (Devm.getStor post sevm.currentTarget),
      rhoN (Devm.getStor post sevm.currentTarget),
      coalitionUnits coalition sevm.currentTarget post.state,
      totalN (Devm.getStor post sevm.currentTarget),
      (Devm.getBal post sevm.currentTarget).toNat⟩
  rw [hchi, hrho, hcoal, htotal, hbalance]
  exact .drip _ _ _ _ _ _

end Drip

end Blanc
