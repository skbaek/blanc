-- DripEndpoints.lean : source-level tails for DRIP's five fresh-index endpoints.
--
-- The machine substrate lives in DripMachine. This module owns endpoint
-- commits, return words, and exit's settlement-before-callback boundary.

import Blanc.DripMachine

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Drip

/-! ## The `drip()` tail

`afterDrip` is the smallest of the five endpoint tails and the one that makes
the machine's output visible: commit the fresh index and the timestamp to
their frozen scalar slots, in that order, and return the new index. -/

private theorem getStor_of_state {s t : Devm} (h : s.state = t.state) :
    Devm.getStor s = Devm.getStor t := by
  funext a
  unfold Devm.getStor Devm.getAcct
  rw [h]

theorem of_run_afterDrip {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterDrip r) :
    Devm.getStor r e.currentTarget =
        ((Devm.getStor entry e.currentTarget).set chiSlot
          (scratch image freshChiWord)).set rhoSlot (scratch image nowWord) ∧
      ReturnsWord (scratch image freshChiWord) r := by
  unfold Drip.afterDrip Drip.commitFresh at run
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, hwf1, hreads1, hst1⟩ :=
    of_run_loadWordAt_image (word := freshChiWord)
      (value := scratch image freshChiWord) hp frame.wf frame.reads rfl hline1
  refine run_prepend_elim _ [pushB256 chiSlot, sstore] ?_ run
  intro s2 hline2 run
  rcases Line.of_run_cons hline2 with ⟨u1, hpush1, hrest⟩
  rcases Line.of_run_cons hrest with ⟨u2, hstore1, hnil⟩
  cases hnil
  have hpu1 : chiSlot :: scratch image freshChiWord :: tail <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp1
  have hstor2 : Devm.getStor s2 e.currentTarget =
      (Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord) := by
    rw [sstore_getStor_set hstore1 hpu1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush1).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst1) e.currentTarget,
      ← congrFun (getStor_of_state frame.state) e.currentTarget]
  have hp2 : tail <<+ s2.stack := prefix_of_sstore hstore1 hpu1
  have hmem2 : s1.memory = s2.memory :=
    Line.of_inv Devm.memory (by line_inv) hline2
  have hwf2 : Mem.Wf s2.memory := by rw [← hmem2]; exact hwf1
  have hreads2 : Mem.Reads s2.memory image := by rw [← hmem2]; exact hreads1
  refine run_prepend_elim _ (loadWord nowWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, hwf3, hreads3, hst3⟩ :=
    of_run_loadWordAt_image (word := nowWord)
      (value := scratch image nowWord) hp2 hwf2 hreads2 rfl hline3
  refine run_prepend_elim _ [pushB256 rhoSlot, sstore] ?_ run
  intro s4 hline4 run
  rcases Line.of_run_cons hline4 with ⟨v1, hpush2, hrest⟩
  rcases Line.of_run_cons hrest with ⟨v2, hstore2, hnil⟩
  cases hnil
  have hpv1 : rhoSlot :: scratch image nowWord :: tail <<+ v1.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp3
  have hstor4 : Devm.getStor s4 e.currentTarget =
      ((Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord)).set rhoSlot (scratch image nowWord) := by
    rw [sstore_getStor_set hstore2 hpv1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush2).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst3) e.currentTarget, hstor2]
  have hp4 : tail <<+ s4.stack := prefix_of_sstore hstore2 hpv1
  have hmem4 : s3.memory = s4.memory :=
    Line.of_inv Devm.memory (by line_inv) hline4
  have hwf4 : Mem.Wf s4.memory := by rw [← hmem4]; exact hwf3
  have hreads4 : Mem.Reads s4.memory image := by rw [← hmem4]; exact hreads3
  -- the return tail leaves storage alone and returns the fresh index
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, hwf5, hreads5, hst5⟩ :=
    of_run_loadWordAt_image (word := freshChiWord)
      (value := scratch image freshChiWord) hp4 hwf4 hreads4 rfl hline5
  refine ⟨?_, (returnsWord_of_storeReturn hp5 run).1⟩
  rw [← congrFun
      (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run) e.currentTarget,
    ← congrFun (getStor_of_state hst5) e.currentTarget, hstor4]

/-! ## `drip()`, end to end at source level

The first complete DRIP endpoint: a successful permissionless `drip()` crosses
the four frozen guards, computes the exact Jaune-certified factor under
Jaune's own word-safety bundle, writes the composed index and the block
timestamp to their frozen scalar slots in that order, and returns the new
index. -/

theorem of_run_drip {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.drip r) :
    ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      B256.Nofm (Devm.getStorVal entry e.currentTarget chiSlot)
        (B256.rpow scale half rate
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat) ∧
      ¬ maxChi <
        (B256.rpow scale half rate
              (e.benvStat.time -
                Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
      Devm.getStor r e.currentTarget =
        ((Devm.getStor entry e.currentTarget).set chiSlot
            ((B256.rpow scale half rate
                  (e.benvStat.time -
                    Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
                Devm.getStorVal entry e.currentTarget chiSlot) / scale)).set
          rhoSlot e.benvStat.time ∧
      ReturnsWord
        ((B256.rpow scale half rate
              (e.benvStat.time -
                Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale) r := by
  unfold Drip.drip Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 routeDrip] ?_ run
  intro s1 hline1 run
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
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
  · obtain ⟨hstor, hret⟩ := of_run_afterDrip frame4 hp4 run
    rw [hfresh, hnow] at hstor
    rw [hfresh] at hret
    exact ⟨hlower, hupper, hclock, helapsed, hguards, hnofm, hcap, hstor, hret⟩
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

/-! ## The two conversion views

Both views are arithmetic-only previews at the same realized index a mutation
would use.  They perform the machine's whole guard route and then one exact
surface floor; neither writes storage, so a successful view leaves the
contract's rows exactly as it found them. -/

theorem of_run_afterConvertToAssets {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterConvertToAssets r) :
    Devm.getStor s = Devm.getStor r ∧
      ReturnsWord
        ((scratch image freshChiWord * scratch image argumentWord) / scale) r := by
  refine ⟨Func.of_inv Devm.getStor Devm.getStor (by func_inv) run, ?_⟩
  unfold Drip.afterConvertToAssets at run
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.loadWord hp1 hline2
  refine run_prepend_elim _ [mul, pushB256 scale, swap 0, div] ?_ run
  intro s3 hline3 run
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : ((scratch image freshChiWord * scratch image argumentWord) /
      scale) :: tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u1, hmul, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u4, hdiv, hnil⟩
    cases hnil
    have h1 := prefix_of_mul hmul hp2
    have h2 := prefix_of_push (of_run_pushB256 hpush) h1
    have h3 : (scratch image freshChiWord * scratch image argumentWord) ::
        scale :: tail <<+ u3.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scale :: (scratch image freshChiWord *
              scratch image argumentWord) :: tail)
            ((scratch image freshChiWord * scratch image argumentWord) ::
              scale :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) h2
    exact prefix_of_div hdiv h3
  refine run_prepend_elim _ (mstoreAt resultWord) ?_ run
  intro s4 hline4 run
  obtain ⟨hp4, frame4⟩ := frame3.mstoreAt hp3 hline4
  refine run_prepend_elim _ (loadWord resultWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, frame5⟩ := frame4.loadWord hp4 hline5
  rw [scratch_setScratch_self] at hp5
  exact (returnsWord_of_storeReturn hp5 run).1

theorem of_run_afterConvertToUnits {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterConvertToUnits r) :
    Devm.getStor s = Devm.getStor r ∧
      ReturnsWord
        ((scale * scratch image argumentWord) /
          scratch image freshChiWord) r := by
  refine ⟨Func.of_inv Devm.getStor Devm.getStor (by func_inv) run, ?_⟩
  unfold Drip.afterConvertToUnits at run
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
  refine run_prepend_elim _ [pushB256 scale, mul] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : (scale * scratch image argumentWord) :: tail <<+ s2.stack := by
    rcases Line.of_run_cons hline2 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hmul, hnil⟩
    cases hnil
    exact prefix_of_mul hmul (prefix_of_push (of_run_pushB256 hpush) hp1)
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.loadWord hp2 hline3
  refine run_prepend_elim _ [swap 0, div] ?_ run
  intro s4 hline4 run
  have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
  have hp4 : ((scale * scratch image argumentWord) /
      scratch image freshChiWord) :: tail <<+ s4.stack := by
    rcases Line.of_run_cons hline4 with ⟨u1, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdiv, hnil⟩
    cases hnil
    have h1 : (scale * scratch image argumentWord) ::
        scratch image freshChiWord :: tail <<+ u1.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scratch image freshChiWord ::
              (scale * scratch image argumentWord) :: tail)
            ((scale * scratch image argumentWord) ::
              scratch image freshChiWord :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) hp3
    exact prefix_of_div hdiv h1
  refine run_prepend_elim _ (mstoreAt resultWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, frame5⟩ := frame4.mstoreAt hp4 hline5
  refine run_prepend_elim _ (loadWord resultWord) ?_ run
  intro s6 hline6 run
  obtain ⟨hp6, frame6⟩ := frame5.loadWord hp5 hline6
  rw [scratch_setScratch_self] at hp6
  exact (returnsWord_of_storeReturn hp6 run).1

/-! ## The two views, end to end at source level -/

private theorem of_run_viewEntry {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    {cap route : B256}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s
      (arg 0 +++ dup 0 ::: mstoreAt argumentWord +++ pushB256 cap ::: lt :::
        (.revert <?> (stageRoute route +++ Func.call freshStartSlot))) r) :
    ∃ t image',
      ¬ cap < Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      scratch image' routeWord = route ∧
      scratch image' argumentWord = Sevm.dataWord e (32 * 0 + 4) ∧
      scratch image' freshChiWord =
        (B256.rpow scale half rate
              (e.benvStat.time -
                Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
      Frame image' entry t ∧ (tail <<+ t.stack) ∧
      Func.Run fs e t (.call freshRouteSlot) r := by
  refine run_prepend_elim _ (arg 0) ?_ run
  intro s1 hline1 run
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : Sevm.dataWord e (32 * 0 + 4) :: tail <<+ s1.stack :=
    prefix_of_cdl_val hp hline1
  refine run_prepend_elim _ [dup 0] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : Sevm.dataWord e (32 * 0 + 4) :: Sevm.dataWord e (32 * 0 + 4) ::
      tail <<+ s2.stack :=
    prefix_of_dup_val (of_run_singleton hline2) (by show_nth) hp1
  refine run_prepend_elim _ (mstoreAt argumentWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.mstoreAt hp2 hline3
  refine run_prepend_elim _ [pushB256 cap, lt] ?_ run
  intro s4 hline4 run
  have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
  have hp4 : (cap <? Sevm.dataWord e (32 * 0 + 4)) :: tail <<+ s4.stack := by
    rcases Line.of_run_cons hline4 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp3)
  obtain ⟨hflagCap, s5, hp5, hpop5, run⟩ := of_run_guard hp4 run
  have frame5 := frame4.of_popBurn hpop5
  have hcap := B256.not_lt_of_ltCheck_eq_zero hflagCap
  unfold Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 route] ?_ run
  intro s6 hline6 run
  have frame6 := frame5.line (by line_inv) (by line_inv) (by line_inv) hline6
  have hp6 : route :: tail <<+ s6.stack := by
    rcases Line.of_run_cons hline6 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp5
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s7 hline7 run
  obtain ⟨hp7, frame7⟩ := frame6.mstoreAt hp6 hline7
  obtain ⟨t8, image8, hlower, hupper, hclock, helapsed, hguards, hnofm, hcapChi,
    hfresh, hnow, hmachine, frame8, hp8, run⟩ :=
    of_run_freshStart hlookup frame7 hp7 run
  refine ⟨t8, image8, hcap, hlower, hupper, hclock, helapsed, hguards, ?_, ?_,
    hfresh, frame8, hp8, run⟩
  · rw [hmachine.1, scratch_setScratch_self]
  · rw [hmachine.2.1,
      scratch_setScratch_of_disjoint _ _ argument_route,
      scratch_setScratch_self]

theorem of_run_convertToAssets {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.convertToAssets r) :
    ¬ maxUnits < Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      Devm.getStor entry = Devm.getStor r ∧
      ReturnsWord
        (((B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale) *
          Sevm.dataWord e (32 * 0 + 4) / scale) r := by
  unfold Drip.convertToAssets at run
  obtain ⟨t, image', hcap, hlower, hupper, hclock, helapsed, hguards, htag,
    harg, hfresh, framet, hpt, run⟩ := of_run_viewEntry hlookup frame hp run
  obtain ⟨t2, frame2, hp2, hroute⟩ := of_run_freshRoute hlookup framet hpt run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · obtain ⟨hstor, hret⟩ := of_run_afterConvertToAssets frame2 hp2 run
    rw [hfresh, harg] at hret
    exact ⟨hcap, hlower, hupper, hclock, helapsed, hguards,
      (getStor_of_state frame2.state).trans hstor, hret⟩
  · exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · exact absurd (htag.symm.trans htagU) (by decide +kernel)
  · exact absurd (htag.symm.trans htagD) (by decide +kernel)
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

theorem of_run_convertToUnits {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.convertToUnits r) :
    ¬ maxAsset < Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      Devm.getStor entry = Devm.getStor r ∧
      ReturnsWord
        (scale * Sevm.dataWord e (32 * 0 + 4) /
          ((B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale)) r := by
  unfold Drip.convertToUnits at run
  obtain ⟨t, image', hcap, hlower, hupper, hclock, helapsed, hguards, htag,
    harg, hfresh, framet, hpt, run⟩ := of_run_viewEntry hlookup frame hp run
  obtain ⟨t2, frame2, hp2, hroute⟩ := of_run_freshRoute hlookup framet hpt run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact absurd (htag.symm.trans htagA) (by decide +kernel)
  · exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · obtain ⟨hstor, hret⟩ := of_run_afterConvertToUnits frame2 hp2 run
    rw [hfresh, harg] at hret
    exact ⟨hcap, hlower, hupper, hclock, helapsed, hguards,
      (getStor_of_state frame2.state).trans hstor, hret⟩
  · exact absurd (htag.symm.trans htagD) (by decide +kernel)
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

/-! ## The `join()` tail

`afterJoin` credits `⌊a·S / chi⁺⌋` normalized units, checks the caller row and
the total against their frozen caps *before* any persistent write, and then
writes in the frozen order: the fresh index, the timestamp, the caller's row,
and the total.  The caller's row is keyed by the raw address word, which
`Blanc/DripCore.lean` separately proves cannot alias a scalar slot. -/

theorem of_run_afterJoin {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterJoin r) :
    ¬ maxUnits < scratch image rowWord +
        (scale * scratch image argumentWord / scratch image freshChiWord) ∧
      ¬ maxPie <
        (scale * scratch image argumentWord / scratch image freshChiWord) +
          scratch image totalWord ∧
      Devm.getStor r e.currentTarget =
        ((((Devm.getStor entry e.currentTarget).set chiSlot
              (scratch image freshChiWord)).set rhoSlot
            (scratch image nowWord)).set e.caller.toB256
            (scratch image rowWord +
              (scale * scratch image argumentWord /
                scratch image freshChiWord))).set totalUnitsSlot
          ((scale * scratch image argumentWord / scratch image freshChiWord) +
            scratch image totalWord) ∧
      ReturnsWord
        (scale * scratch image argumentWord / scratch image freshChiWord) r := by
  unfold Drip.afterJoin at run
  -- the credited unit count
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
  refine run_prepend_elim _ [pushB256 scale, mul] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : (scale * scratch image argumentWord) :: tail <<+ s2.stack := by
    rcases Line.of_run_cons hline2 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hmul, hnil⟩
    cases hnil
    exact prefix_of_mul hmul (prefix_of_push (of_run_pushB256 hpush) hp1)
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.loadWord hp2 hline3
  refine run_prepend_elim _ [swap 0, div, dup 0] ?_ run
  intro s4 hline4 run
  have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
  have hp4 : (scale * scratch image argumentWord /
        scratch image freshChiWord) ::
      (scale * scratch image argumentWord / scratch image freshChiWord) ::
      tail <<+ s4.stack := by
    rcases Line.of_run_cons hline4 with ⟨u1, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdiv, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    have h1 : (scale * scratch image argumentWord) ::
        scratch image freshChiWord :: tail <<+ u1.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scratch image freshChiWord ::
              (scale * scratch image argumentWord) :: tail)
            ((scale * scratch image argumentWord) ::
              scratch image freshChiWord :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) hp3
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_div hdiv h1)
  refine run_prepend_elim _ (mstoreAt resultWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, frame5⟩ := frame4.mstoreAt hp4 hline5
  -- the caller row cap
  refine run_prepend_elim _ (loadWord rowWord) ?_ run
  intro s6 hline6 run
  obtain ⟨hp6, frame6⟩ := frame5.loadWord hp5 hline6
  rw [scratch_setScratch_of_disjoint _ _ row_result] at hp6
  refine run_prepend_elim _ [add, dup 0] ?_ run
  intro s7 hline7 run
  have frame7 := frame6.line (by line_inv) (by line_inv) (by line_inv) hline7
  have hp7 : (scratch image rowWord +
        (scale * scratch image argumentWord / scratch image freshChiWord)) ::
      (scratch image rowWord +
        (scale * scratch image argumentWord / scratch image freshChiWord)) ::
      tail <<+ s7.stack := by
    rcases Line.of_run_cons hline7 with ⟨u1, hadd, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_add hadd hp6)
  refine run_prepend_elim _ (mstoreAt newRowWord) ?_ run
  intro s8 hline8 run
  obtain ⟨hp8, frame8⟩ := frame7.mstoreAt hp7 hline8
  refine run_prepend_elim _ [pushB256 maxUnits, lt] ?_ run
  intro s9 hline9 run
  have frame9 := frame8.line (by line_inv) (by line_inv) (by line_inv) hline9
  have hp9 : (maxUnits <? (scratch image rowWord +
      (scale * scratch image argumentWord / scratch image freshChiWord))) ::
      tail <<+ s9.stack := by
    rcases Line.of_run_cons hline9 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp8)
  obtain ⟨hflagRow, s10, hp10, hpop10, run⟩ := of_run_guard hp9 run
  have frame10 := frame9.of_popBurn hpop10
  have hrowCap := B256.not_lt_of_ltCheck_eq_zero hflagRow
  -- the total cap
  refine run_prepend_elim _ (loadWord totalWord) ?_ run
  intro s11 hline11 run
  obtain ⟨hp11, frame11⟩ := frame10.loadWord hp10 hline11
  rw [scratch_setScratch_of_disjoint _ _ total_newRow,
    scratch_setScratch_of_disjoint _ _ total_result] at hp11
  refine run_prepend_elim _ (loadWord resultWord) ?_ run
  intro s12 hline12 run
  obtain ⟨hp12, frame12⟩ := frame11.loadWord hp11 hline12
  rw [scratch_setScratch_of_disjoint _ _ result_newRow,
    scratch_setScratch_self] at hp12
  refine run_prepend_elim _ [add, dup 0] ?_ run
  intro s13 hline13 run
  have frame13 := frame12.line (by line_inv) (by line_inv) (by line_inv) hline13
  have hp13 : ((scale * scratch image argumentWord /
        scratch image freshChiWord) + scratch image totalWord) ::
      ((scale * scratch image argumentWord / scratch image freshChiWord) +
        scratch image totalWord) :: tail <<+ s13.stack := by
    rcases Line.of_run_cons hline13 with ⟨u1, hadd, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth) (prefix_of_add hadd hp12)
  refine run_prepend_elim _ (mstoreAt newTotalWord) ?_ run
  intro s14 hline14 run
  obtain ⟨hp14, frame14⟩ := frame13.mstoreAt hp13 hline14
  refine run_prepend_elim _ [pushB256 maxPie, lt] ?_ run
  intro s15 hline15 run
  have frame15 := frame14.line (by line_inv) (by line_inv) (by line_inv) hline15
  have hp15 : (maxPie <? ((scale * scratch image argumentWord /
      scratch image freshChiWord) + scratch image totalWord)) ::
      tail <<+ s15.stack := by
    rcases Line.of_run_cons hline15 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp14)
  obtain ⟨hflagTotal, s16, hp16, hpop16, run⟩ := of_run_guard hp15 run
  have frame16 := frame15.of_popBurn hpop16
  have htotalCap := B256.not_lt_of_ltCheck_eq_zero hflagTotal
  -- the frozen write order: index, clock, caller row, total
  unfold Drip.commitFresh at run
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s17 hline17 run
  obtain ⟨hp17, hwf17, hreads17, hst17⟩ :=
    of_run_loadWordAt_image (word := freshChiWord)
      (value := scratch image freshChiWord) hp16 frame16.wf frame16.reads
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ freshChi_newTotal,
            scratch_setScratch_of_disjoint _ _ freshChi_newRow,
            scratch_setScratch_of_disjoint _ _ freshChi_result]) hline17
  refine run_prepend_elim _ [pushB256 chiSlot, sstore] ?_ run
  intro s18 hline18 run
  rcases Line.of_run_cons hline18 with ⟨u1, hpush1, hrest⟩
  rcases Line.of_run_cons hrest with ⟨u2, hstore1, hnil⟩
  cases hnil
  have hpu1 : chiSlot :: scratch image freshChiWord :: tail <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp17
  have hstor18 : Devm.getStor s18 e.currentTarget =
      (Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord) := by
    rw [sstore_getStor_set hstore1 hpu1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush1).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst17) e.currentTarget,
      ← congrFun (getStor_of_state frame16.state) e.currentTarget]
  have hp18 : tail <<+ s18.stack := prefix_of_sstore hstore1 hpu1
  have hmem18 : s17.memory = s18.memory :=
    Line.of_inv Devm.memory (by line_inv) hline18
  refine run_prepend_elim _ (loadWord nowWord) ?_ run
  intro s19 hline19 run
  obtain ⟨hp19, hwf19, hreads19, hst19⟩ :=
    of_run_loadWordAt_image (word := nowWord)
      (value := scratch image nowWord) hp18 (hmem18 ▸ hwf17) (hmem18 ▸ hreads17)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ now_newTotal,
            scratch_setScratch_of_disjoint _ _ now_newRow,
            scratch_setScratch_of_disjoint _ _ now_result]) hline19
  refine run_prepend_elim _ [pushB256 rhoSlot, sstore] ?_ run
  intro s20 hline20 run
  rcases Line.of_run_cons hline20 with ⟨v1, hpush2, hrest⟩
  rcases Line.of_run_cons hrest with ⟨v2, hstore2, hnil⟩
  cases hnil
  have hpv1 : rhoSlot :: scratch image nowWord :: tail <<+ v1.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp19
  have hstor20 : Devm.getStor s20 e.currentTarget =
      ((Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord)).set rhoSlot (scratch image nowWord) := by
    rw [sstore_getStor_set hstore2 hpv1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush2).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst19) e.currentTarget, hstor18]
  have hp20 : tail <<+ s20.stack := prefix_of_sstore hstore2 hpv1
  have hmem20 : s19.memory = s20.memory :=
    Line.of_inv Devm.memory (by line_inv) hline20
  refine run_prepend_elim _ (loadWord newRowWord) ?_ run
  intro s21 hline21 run
  obtain ⟨hp21, hwf21, hreads21, hst21⟩ :=
    of_run_loadWordAt_image (word := newRowWord)
      (value := scratch image rowWord +
        (scale * scratch image argumentWord / scratch image freshChiWord))
      hp20 (hmem20 ▸ hwf19) (hmem20 ▸ hreads19)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ newRow_newTotal,
            scratch_setScratch_self]) hline21
  refine run_prepend_elim _ [caller, sstore] ?_ run
  intro s22 hline22 run
  rcases Line.of_run_cons hline22 with ⟨w1, hcaller, hrest⟩
  rcases Line.of_run_cons hrest with ⟨w2, hstore3, hnil⟩
  cases hnil
  have hpw1 : e.caller.toB256 :: (scratch image rowWord +
      (scale * scratch image argumentWord / scratch image freshChiWord)) ::
      tail <<+ w1.stack := prefix_of_push (of_run_caller hcaller) hp21
  have hstor22 : Devm.getStor s22 e.currentTarget =
      (((Devm.getStor entry e.currentTarget).set chiSlot
          (scratch image freshChiWord)).set rhoSlot
        (scratch image nowWord)).set e.caller.toB256
        (scratch image rowWord +
          (scale * scratch image argumentWord /
            scratch image freshChiWord)) := by
    rw [sstore_getStor_set hstore3 hpw1,
      ← congrFun (getStor_of_state (of_run_caller hcaller).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst21) e.currentTarget, hstor20]
  have hp22 : tail <<+ s22.stack := prefix_of_sstore hstore3 hpw1
  have hmem22 : s21.memory = s22.memory :=
    Line.of_inv Devm.memory (by line_inv) hline22
  refine run_prepend_elim _ (loadWord newTotalWord) ?_ run
  intro s23 hline23 run
  obtain ⟨hp23, hwf23, hreads23, hst23⟩ :=
    of_run_loadWordAt_image (word := newTotalWord)
      (value := (scale * scratch image argumentWord /
        scratch image freshChiWord) + scratch image totalWord)
      hp22 (hmem22 ▸ hwf21) (hmem22 ▸ hreads21)
      (by show scratch _ _ = _
          rw [scratch_setScratch_self]) hline23
  refine run_prepend_elim _ [pushB256 totalUnitsSlot, sstore] ?_ run
  intro s24 hline24 run
  rcases Line.of_run_cons hline24 with ⟨x1, hpush4, hrest⟩
  rcases Line.of_run_cons hrest with ⟨x2, hstore4, hnil⟩
  cases hnil
  have hpx1 : totalUnitsSlot :: ((scale * scratch image argumentWord /
      scratch image freshChiWord) + scratch image totalWord) :: tail <<+
      x1.stack := prefix_of_push (of_run_pushB256 hpush4) hp23
  have hstor24 : Devm.getStor s24 e.currentTarget =
      ((((Devm.getStor entry e.currentTarget).set chiSlot
            (scratch image freshChiWord)).set rhoSlot
          (scratch image nowWord)).set e.caller.toB256
          (scratch image rowWord +
            (scale * scratch image argumentWord /
              scratch image freshChiWord))).set totalUnitsSlot
        ((scale * scratch image argumentWord / scratch image freshChiWord) +
          scratch image totalWord) := by
    rw [sstore_getStor_set hstore4 hpx1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush4).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst23) e.currentTarget, hstor22]
  have hp24 : tail <<+ s24.stack := prefix_of_sstore hstore4 hpx1
  have hmem24 : s23.memory = s24.memory :=
    Line.of_inv Devm.memory (by line_inv) hline24
  refine run_prepend_elim _ (loadWord resultWord) ?_ run
  intro s25 hline25 run
  obtain ⟨hp25, hwf25, hreads25, hst25⟩ :=
    of_run_loadWordAt_image (word := resultWord)
      (value := scale * scratch image argumentWord / scratch image freshChiWord)
      hp24 (hmem24 ▸ hwf23) (hmem24 ▸ hreads23)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ result_newTotal,
            scratch_setScratch_of_disjoint _ _ result_newRow,
            scratch_setScratch_self]) hline25
  refine ⟨hrowCap, htotalCap, ?_, (returnsWord_of_storeReturn hp25 run).1⟩
  rw [← congrFun
      (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run) e.currentTarget,
    ← congrFun (getStor_of_state hst25) e.currentTarget, hstor24]

/-! ## `join()`, end to end at source level -/

theorem of_run_join {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.join r) :
    ¬ maxAsset < e.value ∧
      ¬ maxUnits < Devm.getStorVal entry e.currentTarget e.caller.toB256 ∧
      ¬ maxPie < Devm.getStorVal entry e.currentTarget totalUnitsSlot ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      ∃ freshChi units,
        freshChi =
          (B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
        units = scale * e.value / freshChi ∧
        ¬ maxUnits <
          Devm.getStorVal entry e.currentTarget e.caller.toB256 + units ∧
        ¬ maxPie <
          units + Devm.getStorVal entry e.currentTarget totalUnitsSlot ∧
        Devm.getStor r e.currentTarget =
          ((((Devm.getStor entry e.currentTarget).set chiSlot freshChi).set
              rhoSlot e.benvStat.time).set e.caller.toB256
              (Devm.getStorVal entry e.currentTarget e.caller.toB256 +
                units)).set totalUnitsSlot
            (units + Devm.getStorVal entry e.currentTarget totalUnitsSlot) ∧
        ReturnsWord units r := by
  unfold Drip.join at run
  -- the call value's surface cap
  refine run_prepend_elim _ [callvalue, dup 0] ?_ run
  intro s1 hline1 run
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : e.value :: e.value :: tail <<+ s1.stack := by
    rcases Line.of_run_cons hline1 with ⟨u1, hcv, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hdup, hnil⟩
    cases hnil
    exact prefix_of_dup_val hdup (by show_nth)
      (prefix_of_push (of_run_callvalue hcv) hp)
  refine run_prepend_elim _ (mstoreAt argumentWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.mstoreAt hp1 hline2
  refine run_prepend_elim _ [pushB256 maxAsset, lt] ?_ run
  intro s3 hline3 run
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : (maxAsset <? e.value) :: tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp2)
  obtain ⟨hflagAsset, s4, hp4, hpop4, run⟩ := of_run_guard hp3 run
  have frame4 := frame3.of_popBurn hpop4
  have hassetCap := B256.not_lt_of_ltCheck_eq_zero hflagAsset
  -- the caller row's surface cap
  refine run_prepend_elim _ [caller, sload, dup 0] ?_ run
  intro s5 hline5 run
  have frame5 := frame4.line (by line_inv) (by line_inv) (by line_inv) hline5
  have hp5 : Devm.getStorVal entry e.currentTarget e.caller.toB256 ::
      Devm.getStorVal entry e.currentTarget e.caller.toB256 ::
      tail <<+ s5.stack := by
    rcases Line.of_run_cons hline5 with ⟨u1, hcaller, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_caller hcaller) hp4)
    rw [hyval,
      Devm.getStorVal_of_state
        (frame4.state.trans (of_run_caller hcaller).state).symm] at hy
    exact prefix_of_dup_val hdup (by show_nth) hy
  refine run_prepend_elim _ (mstoreAt rowWord) ?_ run
  intro s6 hline6 run
  obtain ⟨hp6, frame6⟩ := frame5.mstoreAt hp5 hline6
  refine run_prepend_elim _ [pushB256 maxUnits, lt] ?_ run
  intro s7 hline7 run
  have frame7 := frame6.line (by line_inv) (by line_inv) (by line_inv) hline7
  have hp7 : (maxUnits <?
      Devm.getStorVal entry e.currentTarget e.caller.toB256) ::
      tail <<+ s7.stack := by
    rcases Line.of_run_cons hline7 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp6)
  obtain ⟨hflagRow, s8, hp8, hpop8, run⟩ := of_run_guard hp7 run
  have frame8 := frame7.of_popBurn hpop8
  have hrowCapPre := B256.not_lt_of_ltCheck_eq_zero hflagRow
  -- the total's surface cap
  refine run_prepend_elim _ [pushB256 totalUnitsSlot, sload, dup 0] ?_ run
  intro s9 hline9 run
  have frame9 := frame8.line (by line_inv) (by line_inv) (by line_inv) hline9
  have hp9 : Devm.getStorVal entry e.currentTarget totalUnitsSlot ::
      Devm.getStorVal entry e.currentTarget totalUnitsSlot ::
      tail <<+ s9.stack := by
    rcases Line.of_run_cons hline9 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) hp8)
    rw [hyval,
      Devm.getStorVal_of_state
        (frame8.state.trans (of_run_pushB256 hpush).state).symm] at hy
    exact prefix_of_dup_val hdup (by show_nth) hy
  refine run_prepend_elim _ (mstoreAt totalWord) ?_ run
  intro s10 hline10 run
  obtain ⟨hp10, frame10⟩ := frame9.mstoreAt hp9 hline10
  refine run_prepend_elim _ [pushB256 maxPie, lt] ?_ run
  intro s11 hline11 run
  have frame11 := frame10.line (by line_inv) (by line_inv) (by line_inv) hline11
  have hp11 : (maxPie <?
      Devm.getStorVal entry e.currentTarget totalUnitsSlot) ::
      tail <<+ s11.stack := by
    rcases Line.of_run_cons hline11 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp10)
  obtain ⟨hflagTotal, s12, hp12, hpop12, run⟩ := of_run_guard hp11 run
  have frame12 := frame11.of_popBurn hpop12
  have htotalCapPre := B256.not_lt_of_ltCheck_eq_zero hflagTotal
  -- stage the route and enter the machine
  unfold Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 routeJoin] ?_ run
  intro s13 hline13 run
  have frame13 := frame12.line (by line_inv) (by line_inv) (by line_inv) hline13
  have hp13 : routeJoin :: tail <<+ s13.stack := by
    rcases Line.of_run_cons hline13 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp12
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s14 hline14 run
  obtain ⟨hp14, frame14⟩ := frame13.mstoreAt hp13 hline14
  obtain ⟨t15, image15, hlower, hupper, hclock, helapsed, hguards, hnofm,
    hcapChi, hfresh, hnow, hmachine, frame15, hp15, run⟩ :=
    of_run_freshStart hlookup frame14 hp14 run
  have htag : scratch image15 routeWord = routeJoin := by
    rw [hmachine.1, scratch_setScratch_self]
  have harg : scratch image15 argumentWord = e.value := by
    rw [hmachine.2.1,
      scratch_setScratch_of_disjoint _ _ argument_route,
      scratch_setScratch_of_disjoint _ _ argument_total,
      scratch_setScratch_of_disjoint _ _ argument_row,
      scratch_setScratch_self]
  have hrow : scratch image15 rowWord =
      Devm.getStorVal entry e.currentTarget e.caller.toB256 := by
    rw [hmachine.2.2.1,
      scratch_setScratch_of_disjoint _ _ row_route,
      scratch_setScratch_of_disjoint _ _ row_total,
      scratch_setScratch_self]
  have htotal : scratch image15 totalWord =
      Devm.getStorVal entry e.currentTarget totalUnitsSlot := by
    rw [hmachine.2.2.2,
      scratch_setScratch_of_disjoint _ _ total_route,
      scratch_setScratch_self]
  obtain ⟨t16, frame16, hp16, hroute⟩ := of_run_freshRoute hlookup frame15 hp15 run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact absurd (htag.symm.trans htagA) (by decide +kernel)
  · exact absurd (htag.symm.trans htagE) (by decide +kernel)
  · exact absurd (htag.symm.trans htagU) (by decide +kernel)
  · exact absurd (htag.symm.trans htagD) (by decide +kernel)
  · obtain ⟨hrowCap, htotalCap, hstor, hret⟩ :=
      of_run_afterJoin frame16 hp16 run
    simp only [harg, hrow, htotal, hfresh, hnow] at hrowCap htotalCap hstor hret
    refine ⟨hassetCap, hrowCapPre, htotalCapPre, hlower, hupper, hclock,
      helapsed, hguards, _, _, rfl, rfl, hrowCap, htotalCap, hstor, hret⟩

/-! ## `exit`'s checks-effects-interactions boundary

Every successful `exit` has *already* committed all four ledger writes — the
fresh index, the clock, the caller's debited row and the debited total — before
it reaches the outbound `CALL`.  That is the frozen memo's
checks-effects-interactions requirement, stated as a property of the walk
rather than assumed of the code. -/

theorem of_run_afterExit_settles {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s afterExit r) :
    ∃ t,
      Devm.getStor t e.currentTarget =
        ((((Devm.getStor entry e.currentTarget).set chiSlot
              (scratch image freshChiWord)).set rhoSlot
            (scratch image nowWord)).set e.caller.toB256
            (scratch image rowWord - scratch image argumentWord)).set
          totalUnitsSlot
          (scratch image totalWord - scratch image argumentWord) ∧
      (tail <<+ t.stack) ∧
      Mem.Wf t.memory ∧
      Mem.Reads t.memory
        (setScratch image resultWord
          ((scratch image freshChiWord * scratch image argumentWord) /
            scale)) ∧
      Func.Run fs e t
        (loadWord resultWord +++ sendToCaller +++
          (returnScratch resultWord <?> Func.revert)) r := by
  unfold Drip.afterExit Drip.commitFresh at run
  -- the payout
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s1 hline1 run
  obtain ⟨hp1, frame1⟩ := frame.loadWord hp hline1
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s2 hline2 run
  obtain ⟨hp2, frame2⟩ := frame1.loadWord hp1 hline2
  refine run_prepend_elim _ [mul, pushB256 scale, swap 0, div] ?_ run
  intro s3 hline3 run
  have frame3 := frame2.line (by line_inv) (by line_inv) (by line_inv) hline3
  have hp3 : ((scratch image freshChiWord * scratch image argumentWord) /
      scale) :: tail <<+ s3.stack := by
    rcases Line.of_run_cons hline3 with ⟨u1, hmul, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hswap, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u4, hdiv, hnil⟩
    cases hnil
    have h1 := prefix_of_mul hmul hp2
    have h2 := prefix_of_push (of_run_pushB256 hpush) h1
    have h3 : (scratch image freshChiWord * scratch image argumentWord) ::
        scale :: tail <<+ u3.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap 0
            (scale :: (scratch image freshChiWord *
              scratch image argumentWord) :: tail)
            ((scratch image freshChiWord * scratch image argumentWord) ::
              scale :: tail)
          from Stack.swapCore_zero)
        (of_run_swap hswap) h2
    exact prefix_of_div hdiv h3
  refine run_prepend_elim _ (mstoreAt resultWord) ?_ run
  intro s4 hline4 run
  obtain ⟨hp4, frame4⟩ := frame3.mstoreAt hp3 hline4
  -- the four ordered writes
  refine run_prepend_elim _ (loadWord freshChiWord) ?_ run
  intro s5 hline5 run
  obtain ⟨hp5, hwf5, hreads5, hst5⟩ :=
    of_run_loadWordAt_image (word := freshChiWord)
      (value := scratch image freshChiWord) hp4 frame4.wf frame4.reads
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ freshChi_result]) hline5
  refine run_prepend_elim _ [pushB256 chiSlot, sstore] ?_ run
  intro s6 hline6 run
  rcases Line.of_run_cons hline6 with ⟨u1, hpush1, hrest⟩
  rcases Line.of_run_cons hrest with ⟨u2, hstore1, hnil⟩
  cases hnil
  have hpu1 : chiSlot :: scratch image freshChiWord :: tail <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp5
  have hstor6 : Devm.getStor s6 e.currentTarget =
      (Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord) := by
    rw [sstore_getStor_set hstore1 hpu1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush1).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst5) e.currentTarget,
      ← congrFun (getStor_of_state frame4.state) e.currentTarget]
  have hp6 : tail <<+ s6.stack := prefix_of_sstore hstore1 hpu1
  have hmem6 : s5.memory = s6.memory :=
    Line.of_inv Devm.memory (by line_inv) hline6
  refine run_prepend_elim _ (loadWord nowWord) ?_ run
  intro s7 hline7 run
  obtain ⟨hp7, hwf7, hreads7, hst7⟩ :=
    of_run_loadWordAt_image (word := nowWord)
      (value := scratch image nowWord) hp6 (hmem6 ▸ hwf5) (hmem6 ▸ hreads5)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ now_result]) hline7
  refine run_prepend_elim _ [pushB256 rhoSlot, sstore] ?_ run
  intro s8 hline8 run
  rcases Line.of_run_cons hline8 with ⟨v1, hpush2, hrest⟩
  rcases Line.of_run_cons hrest with ⟨v2, hstore2, hnil⟩
  cases hnil
  have hpv1 : rhoSlot :: scratch image nowWord :: tail <<+ v1.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp7
  have hstor8 : Devm.getStor s8 e.currentTarget =
      ((Devm.getStor entry e.currentTarget).set chiSlot
        (scratch image freshChiWord)).set rhoSlot (scratch image nowWord) := by
    rw [sstore_getStor_set hstore2 hpv1,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush2).state)
        e.currentTarget,
      ← congrFun (getStor_of_state hst7) e.currentTarget, hstor6]
  have hp8 : tail <<+ s8.stack := prefix_of_sstore hstore2 hpv1
  have hmem8 : s7.memory = s8.memory :=
    Line.of_inv Devm.memory (by line_inv) hline8
  -- debit the caller's row
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s9 hline9 run
  obtain ⟨hp9, hwf9, hreads9, hst9⟩ :=
    of_run_loadWordAt_image (word := argumentWord)
      (value := scratch image argumentWord) hp8 (hmem8 ▸ hwf7) (hmem8 ▸ hreads7)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ argument_result]) hline9
  refine run_prepend_elim _ (loadWord rowWord) ?_ run
  intro s10 hline10 run
  obtain ⟨hp10, hwf10, hreads10, hst10⟩ :=
    of_run_loadWordAt_image (word := rowWord)
      (value := scratch image rowWord) hp9 hwf9 hreads9
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ row_result]) hline10
  refine run_prepend_elim _ [sub, caller, sstore] ?_ run
  intro s11 hline11 run
  rcases Line.of_run_cons hline11 with ⟨w1, hsub, hrest⟩
  rcases Line.of_run_cons hrest with ⟨w2, hcaller, hrest⟩
  rcases Line.of_run_cons hrest with ⟨w3, hstore3, hnil⟩
  cases hnil
  have hpw2 : e.caller.toB256 ::
      (scratch image rowWord - scratch image argumentWord) :: tail <<+
      w2.stack :=
    prefix_of_push (of_run_caller hcaller) (prefix_of_sub hsub hp10)
  have hstor11 : Devm.getStor s11 e.currentTarget =
      (((Devm.getStor entry e.currentTarget).set chiSlot
          (scratch image freshChiWord)).set rhoSlot
        (scratch image nowWord)).set e.caller.toB256
        (scratch image rowWord - scratch image argumentWord) := by
    rw [sstore_getStor_set hstore3 hpw2,
      ← congrFun (getStor_of_state (of_run_caller hcaller).state)
        e.currentTarget,
      ← congrFun (getStor_of_state
        (Line.of_inv Devm.state (by line_inv)
          (Line.Run.cons hsub Line.Run.nil))) e.currentTarget,
      ← congrFun (getStor_of_state hst10) e.currentTarget,
      ← congrFun (getStor_of_state hst9) e.currentTarget, hstor8]
  have hp11 : tail <<+ s11.stack := prefix_of_sstore hstore3 hpw2
  have hmem11 : s10.memory = s11.memory :=
    Line.of_inv Devm.memory (by line_inv) hline11
  -- debit the total
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s12 hline12 run
  obtain ⟨hp12, hwf12, hreads12, hst12⟩ :=
    of_run_loadWordAt_image (word := argumentWord)
      (value := scratch image argumentWord) hp11 (hmem11 ▸ hwf10)
      (hmem11 ▸ hreads10)
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ argument_result]) hline12
  refine run_prepend_elim _ (loadWord totalWord) ?_ run
  intro s13 hline13 run
  obtain ⟨hp13, hwf13, hreads13, hst13⟩ :=
    of_run_loadWordAt_image (word := totalWord)
      (value := scratch image totalWord) hp12 hwf12 hreads12
      (by show scratch _ _ = _
          rw [scratch_setScratch_of_disjoint _ _ total_result]) hline13
  refine run_prepend_elim _ [sub, pushB256 totalUnitsSlot, sstore] ?_ run
  intro s14 hline14 run
  rcases Line.of_run_cons hline14 with ⟨x1, hsub2, hrest⟩
  rcases Line.of_run_cons hrest with ⟨x2, hpush4, hrest⟩
  rcases Line.of_run_cons hrest with ⟨x3, hstore4, hnil⟩
  cases hnil
  have hpx2 : totalUnitsSlot ::
      (scratch image totalWord - scratch image argumentWord) :: tail <<+
      x2.stack :=
    prefix_of_push (of_run_pushB256 hpush4) (prefix_of_sub hsub2 hp13)
  have hstor14 : Devm.getStor s14 e.currentTarget =
      ((((Devm.getStor entry e.currentTarget).set chiSlot
            (scratch image freshChiWord)).set rhoSlot
          (scratch image nowWord)).set e.caller.toB256
          (scratch image rowWord - scratch image argumentWord)).set
        totalUnitsSlot
        (scratch image totalWord - scratch image argumentWord) := by
    rw [sstore_getStor_set hstore4 hpx2,
      ← congrFun (getStor_of_state (of_run_pushB256 hpush4).state)
        e.currentTarget,
      ← congrFun (getStor_of_state
        (Line.of_inv Devm.state (by line_inv)
          (Line.Run.cons hsub2 Line.Run.nil))) e.currentTarget,
      ← congrFun (getStor_of_state hst13) e.currentTarget,
      ← congrFun (getStor_of_state hst12) e.currentTarget, hstor11]
  have hp14 : tail <<+ s14.stack := prefix_of_sstore hstore4 hpx2
  have hmem14 : s13.memory = s14.memory :=
    Line.of_inv Devm.memory (by line_inv) hline14
  exact ⟨s14, hstor14, hp14, hmem14 ▸ hwf13, hmem14 ▸ hreads13, run⟩

/-! ## `exit(units)`, end to end at source level up to the outbound call

Every successful `exit` checks its caps *and* that the caller and the total
actually hold the units, computes the payout at the freshly accrued index, and
commits all four ledger writes before the outbound `CALL` is reached.  The
child crossing and the whole-frame rollback on a failed child are the one
remaining piece of the endpoint. -/

theorem of_run_exit_settles {fs : List Func} (hlookup : AuxLookup fs)
    {e : Sevm} {entry s r : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s Drip.exit r) :
    ¬ maxUnits < Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ maxUnits < Devm.getStorVal entry e.currentTarget e.caller.toB256 ∧
      ¬ maxPie < Devm.getStorVal entry e.currentTarget totalUnitsSlot ∧
      ¬ Devm.getStorVal entry e.currentTarget e.caller.toB256 <
        Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget totalUnitsSlot <
        Sevm.dataWord e (32 * 0 + 4) ∧
      ¬ Devm.getStorVal entry e.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal entry e.currentTarget chiSlot ∧
      ¬ e.benvStat.time < Devm.getStorVal entry e.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      ∃ t freshChi settledImage,
        freshChi =
          (B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale ∧
        scratch settledImage resultWord =
          (freshChi * Sevm.dataWord e (32 * 0 + 4)) / scale ∧
        tail <<+ t.stack ∧
        Mem.Wf t.memory ∧
        Mem.Reads t.memory settledImage ∧
        Devm.getStor t e.currentTarget =
          ((((Devm.getStor entry e.currentTarget).set chiSlot freshChi).set
              rhoSlot e.benvStat.time).set e.caller.toB256
              (Devm.getStorVal entry e.currentTarget e.caller.toB256 -
                Sevm.dataWord e (32 * 0 + 4))).set totalUnitsSlot
            (Devm.getStorVal entry e.currentTarget totalUnitsSlot -
              Sevm.dataWord e (32 * 0 + 4)) ∧
        Func.Run fs e t
          (loadWord resultWord +++ sendToCaller +++
            (returnScratch resultWord <?> Func.revert)) r := by
  unfold Drip.exit at run
  -- the argument's surface cap
  refine run_prepend_elim _ (arg 0) ?_ run
  intro s1 hline1 run
  have frame1 := frame.line (by line_inv) (by line_inv) (by line_inv) hline1
  have hp1 : Sevm.dataWord e (32 * 0 + 4) :: tail <<+ s1.stack :=
    prefix_of_cdl_val hp hline1
  refine run_prepend_elim _ [dup 0] ?_ run
  intro s2 hline2 run
  have frame2 := frame1.line (by line_inv) (by line_inv) (by line_inv) hline2
  have hp2 : Sevm.dataWord e (32 * 0 + 4) :: Sevm.dataWord e (32 * 0 + 4) ::
      tail <<+ s2.stack :=
    prefix_of_dup_val (of_run_singleton hline2) (by show_nth) hp1
  refine run_prepend_elim _ (mstoreAt argumentWord) ?_ run
  intro s3 hline3 run
  obtain ⟨hp3, frame3⟩ := frame2.mstoreAt hp2 hline3
  refine run_prepend_elim _ [pushB256 maxUnits, lt] ?_ run
  intro s4 hline4 run
  have frame4 := frame3.line (by line_inv) (by line_inv) (by line_inv) hline4
  have hp4 : (maxUnits <? Sevm.dataWord e (32 * 0 + 4)) :: tail <<+ s4.stack := by
    rcases Line.of_run_cons hline4 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp3)
  obtain ⟨hflagArg, s5, hp5, hpop5, run⟩ := of_run_guard hp4 run
  have frame5 := frame4.of_popBurn hpop5
  have hargCap := B256.not_lt_of_ltCheck_eq_zero hflagArg
  -- the caller row's surface cap
  refine run_prepend_elim _ [caller, sload, dup 0] ?_ run
  intro s6 hline6 run
  have frame6 := frame5.line (by line_inv) (by line_inv) (by line_inv) hline6
  have hp6 : Devm.getStorVal entry e.currentTarget e.caller.toB256 ::
      Devm.getStorVal entry e.currentTarget e.caller.toB256 ::
      tail <<+ s6.stack := by
    rcases Line.of_run_cons hline6 with ⟨u1, hcaller, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_caller hcaller) hp5)
    rw [hyval,
      Devm.getStorVal_of_state
        (frame5.state.trans (of_run_caller hcaller).state).symm] at hy
    exact prefix_of_dup_val hdup (by show_nth) hy
  refine run_prepend_elim _ (mstoreAt rowWord) ?_ run
  intro s7 hline7 run
  obtain ⟨hp7, frame7⟩ := frame6.mstoreAt hp6 hline7
  refine run_prepend_elim _ [pushB256 maxUnits, lt] ?_ run
  intro s8 hline8 run
  have frame8 := frame7.line (by line_inv) (by line_inv) (by line_inv) hline8
  have hp8 : (maxUnits <?
      Devm.getStorVal entry e.currentTarget e.caller.toB256) ::
      tail <<+ s8.stack := by
    rcases Line.of_run_cons hline8 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp7)
  obtain ⟨hflagRow, s9, hp9, hpop9, run⟩ := of_run_guard hp8 run
  have frame9 := frame8.of_popBurn hpop9
  have hrowCap := B256.not_lt_of_ltCheck_eq_zero hflagRow
  -- the total's surface cap
  refine run_prepend_elim _ [pushB256 totalUnitsSlot, sload, dup 0] ?_ run
  intro s10 hline10 run
  have frame10 := frame9.line (by line_inv) (by line_inv) (by line_inv) hline10
  have hp10 : Devm.getStorVal entry e.currentTarget totalUnitsSlot ::
      Devm.getStorVal entry e.currentTarget totalUnitsSlot ::
      tail <<+ s10.stack := by
    rcases Line.of_run_cons hline10 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hsload, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u3, hdup, hnil⟩
    cases hnil
    obtain ⟨y, hy, hyval⟩ :=
      prefix_of_sload hsload (prefix_of_push (of_run_pushB256 hpush) hp9)
    rw [hyval,
      Devm.getStorVal_of_state
        (frame9.state.trans (of_run_pushB256 hpush).state).symm] at hy
    exact prefix_of_dup_val hdup (by show_nth) hy
  refine run_prepend_elim _ (mstoreAt totalWord) ?_ run
  intro s11 hline11 run
  obtain ⟨hp11, frame11⟩ := frame10.mstoreAt hp10 hline11
  refine run_prepend_elim _ [pushB256 maxPie, lt] ?_ run
  intro s12 hline12 run
  have frame12 := frame11.line (by line_inv) (by line_inv) (by line_inv) hline12
  have hp12 : (maxPie <?
      Devm.getStorVal entry e.currentTarget totalUnitsSlot) ::
      tail <<+ s12.stack := by
    rcases Line.of_run_cons hline12 with ⟨u1, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨u2, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt (prefix_of_push (of_run_pushB256 hpush) hp11)
  obtain ⟨hflagTotal, s13, hp13, hpop13, run⟩ := of_run_guard hp12 run
  have frame13 := frame12.of_popBurn hpop13
  have htotalCap := B256.not_lt_of_ltCheck_eq_zero hflagTotal
  -- the caller actually holds the units
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s14 hline14 run
  obtain ⟨hp14, frame14⟩ := frame13.loadWord hp13 hline14
  rw [scratch_setScratch_of_disjoint _ _ argument_total,
    scratch_setScratch_of_disjoint _ _ argument_row,
    scratch_setScratch_self] at hp14
  refine run_prepend_elim _ (loadWord rowWord) ?_ run
  intro s15 hline15 run
  obtain ⟨hp15, frame15⟩ := frame14.loadWord hp14 hline15
  rw [scratch_setScratch_of_disjoint _ _ row_total,
    scratch_setScratch_self] at hp15
  refine run_prepend_elim _ [lt] ?_ run
  intro s16 hline16 run
  have frame16 := frame15.line (by line_inv) (by line_inv) (by line_inv) hline16
  have hp16 : (Devm.getStorVal entry e.currentTarget e.caller.toB256 <?
      Sevm.dataWord e (32 * 0 + 4)) :: tail <<+ s16.stack :=
    prefix_of_lt (of_run_singleton hline16) hp15
  obtain ⟨hflagOwn, s17, hp17, hpop17, run⟩ := of_run_guard hp16 run
  have frame17 := frame16.of_popBurn hpop17
  have hown := B256.not_lt_of_ltCheck_eq_zero hflagOwn
  -- the total actually holds the units
  refine run_prepend_elim _ (loadWord argumentWord) ?_ run
  intro s18 hline18 run
  obtain ⟨hp18, frame18⟩ := frame17.loadWord hp17 hline18
  rw [scratch_setScratch_of_disjoint _ _ argument_total,
    scratch_setScratch_of_disjoint _ _ argument_row,
    scratch_setScratch_self] at hp18
  refine run_prepend_elim _ (loadWord totalWord) ?_ run
  intro s19 hline19 run
  obtain ⟨hp19, frame19⟩ := frame18.loadWord hp18 hline19
  rw [scratch_setScratch_self] at hp19
  refine run_prepend_elim _ [lt] ?_ run
  intro s20 hline20 run
  have frame20 := frame19.line (by line_inv) (by line_inv) (by line_inv) hline20
  have hp20 : (Devm.getStorVal entry e.currentTarget totalUnitsSlot <?
      Sevm.dataWord e (32 * 0 + 4)) :: tail <<+ s20.stack :=
    prefix_of_lt (of_run_singleton hline20) hp19
  obtain ⟨hflagFund, s21, hp21, hpop21, run⟩ := of_run_guard hp20 run
  have frame21 := frame20.of_popBurn hpop21
  have hfund := B256.not_lt_of_ltCheck_eq_zero hflagFund
  -- stage the route and enter the machine
  unfold Drip.stageRoute at run
  refine run_prepend_elim _ [pushB256 routeExit] ?_ run
  intro s22 hline22 run
  have frame22 := frame21.line (by line_inv) (by line_inv) (by line_inv) hline22
  have hp22 : routeExit :: tail <<+ s22.stack := by
    rcases Line.of_run_cons hline22 with ⟨u, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) hp21
  refine run_prepend_elim _ (mstoreAt routeWord) ?_ run
  intro s23 hline23 run
  obtain ⟨hp23, frame23⟩ := frame22.mstoreAt hp22 hline23
  obtain ⟨t24, image24, hlower, hupper, hclock, helapsed, hguards, hnofm,
    hcapChi, hfresh, hnow, hmachine, frame24, hp24, run⟩ :=
    of_run_freshStart hlookup frame23 hp23 run
  have htag : scratch image24 routeWord = routeExit := by
    rw [hmachine.1, scratch_setScratch_self]
  have harg : scratch image24 argumentWord = Sevm.dataWord e (32 * 0 + 4) := by
    rw [hmachine.2.1,
      scratch_setScratch_of_disjoint _ _ argument_route,
      scratch_setScratch_of_disjoint _ _ argument_total,
      scratch_setScratch_of_disjoint _ _ argument_row,
      scratch_setScratch_self]
  have hrow : scratch image24 rowWord =
      Devm.getStorVal entry e.currentTarget e.caller.toB256 := by
    rw [hmachine.2.2.1,
      scratch_setScratch_of_disjoint _ _ row_route,
      scratch_setScratch_of_disjoint _ _ row_total,
      scratch_setScratch_self]
  have htotal : scratch image24 totalWord =
      Devm.getStorVal entry e.currentTarget totalUnitsSlot := by
    rw [hmachine.2.2.2,
      scratch_setScratch_of_disjoint _ _ total_route,
      scratch_setScratch_self]
  obtain ⟨t25, frame25, hp25, hroute⟩ :=
    of_run_freshRoute hlookup frame24 hp24 run
  rcases hroute with ⟨htagA, run⟩ | ⟨htagE, run⟩ | ⟨htagU, run⟩ |
    ⟨htagD, run⟩ | ⟨htagJ, run⟩
  · exact absurd (htag.symm.trans htagA) (by decide +kernel)
  · obtain ⟨t26, hstor, hp26, hwf26, hreads26, run⟩ :=
      of_run_afterExit_settles frame25 hp25 run
    simp only [harg, hrow, htotal, hfresh, hnow] at hstor hreads26
    exact ⟨hargCap, hrowCap, htotalCap, hown, hfund, hlower, hupper, hclock,
      helapsed, hguards, t26, _,
      setScratch image24 resultWord
        (((B256.rpow scale half rate
                (e.benvStat.time -
                  Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry e.currentTarget chiSlot) / scale *
            Sevm.dataWord e (32 * 0 + 4)) / scale),
      rfl, scratch_setScratch_self _ _ _, hp26, hwf26, hreads26, hstor, run⟩
  · exact absurd (htag.symm.trans htagU) (by decide +kernel)
  · exact absurd (htag.symm.trans htagD) (by decide +kernel)
  · exact absurd (htag.symm.trans htagJ) (by decide +kernel)

/-! ## `exit`'s entered child and exact return

The settlement theorem above stops just before the payout word is loaded for
the outbound call.  The remaining walk matters: the call uses the recipient,
value and two empty memory windows frozen by the statement memo; a zero status
word selects `Func.revert`; and only an entered, clean child can reach the
one-word return.  The raw parent/child equalities below retain the whole-frame
rollback boundary supplied by `of_run_call_val_with_depth_frame` instead of
summarizing the call as an unexplained success flag. -/

private theorem exit_sendToCaller_frame
    {sevm : Sevm} {pre callPost : Devm} {p : B256} {xs : Stack}
    (hp : p :: xs <<+ pre.stack)
    (run : Line.Run sevm pre sendToCaller callPost) :
    ∃ callPre gasWord,
      gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs <<+
        callPre.stack ∧
      Ninst.Run sevm callPre call callPost ∧
      Devm.getStor callPre = Devm.getStor pre ∧
      Devm.getBal callPre = Devm.getBal pre ∧
      Devm.getCode callPre = Devm.getCode pre ∧
      callPre.logs = pre.logs ∧
      callPre.output = pre.output ∧
      callPre.memory = pre.memory := by
  unfold sendToCaller at run
  let callPrefix : Line := pushList [0, 0, 0, 0] ++ [swap 3, caller, gas]
  rcases of_run_append callPrefix run with ⟨callPre, hprefix, hcall⟩
  have hstorPrefix : Devm.getStor pre = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by unfold callPrefix; line_inv) hprefix
  have hbalPrefix : Devm.getBal pre = Devm.getBal callPre :=
    Line.of_inv Devm.getBal (by unfold callPrefix; line_inv) hprefix
  have hcodePrefix : Devm.getCode pre = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by unfold callPrefix; line_inv) hprefix
  have hlogsPrefix : pre.logs = callPre.logs :=
    Line.of_inv Devm.logs (by unfold callPrefix; line_inv) hprefix
  have houtPrefix : pre.output = callPre.output :=
    Line.of_inv Devm.output (by unfold callPrefix; line_inv) hprefix
  have hmemPrefix : pre.memory = callPre.memory :=
    Line.of_inv Devm.memory (by unfold callPrefix; line_inv) hprefix
  rcases Line.of_run_cons hcall with ⟨callPost', qcall, hnil⟩
  cases hnil
  unfold callPrefix pushList at hprefix
  simp only [List.map] at hprefix
  rcases Line.of_run_cons hprefix with ⟨s1, q1, hprefix⟩
  have p1 : (0 : B256) :: p :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons hprefix with ⟨s2, q2, hprefix⟩
  have p2 : (0 : B256) :: 0 :: p :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 q2) p1
  rcases Line.of_run_cons hprefix with ⟨s3, q3, hprefix⟩
  have p3 : (0 : B256) :: 0 :: 0 :: p :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 q3) p2
  rcases Line.of_run_cons hprefix with ⟨s4, q4, hprefix⟩
  have p4 : (0 : B256) :: 0 :: 0 :: 0 :: p :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 q4) p3
  rcases Line.of_run_cons hprefix with ⟨s5, qswap, hprefix⟩
  have hswap : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: p :: xs)
      (p :: 0 :: 0 :: 0 :: 0 :: xs) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have p5 : p :: 0 :: 0 :: 0 :: 0 :: xs <<+ s5.stack :=
    Stack.prefix_of_swap hswap (of_run_swap qswap) p4
  rcases Line.of_run_cons hprefix with ⟨s6, qcaller, hprefix⟩
  have p6 : sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs <<+
      s6.stack :=
    prefix_of_push (of_run_caller qcaller) p5
  rcases Line.of_run_cons hprefix with ⟨s7, qgas, hnil⟩
  cases hnil
  rcases of_run_gas qgas with ⟨gasWord, hgas⟩
  refine ⟨callPre, gasWord, ?_, qcall,
    hstorPrefix.symm, hbalPrefix.symm, hcodePrefix.symm, hlogsPrefix.symm,
    houtPrefix.symm, hmemPrefix.symm⟩
  simpa only [List.cons_append, List.nil_append] using prefix_of_push hgas p6

/-- An `exit` payout whose status word is consumed by the success guard.  The
carrier retains the exact EIP-150 child message, delegation choice, empty
calldata/output windows, successful child settlement and caller resumption.
The first disjunct of `of_run_call_val_with_depth_frame` is absent precisely
because its zero flag selects the outer `Func.revert`; that inversion still
supplies `Devm.WorldEq` for the rejected child-failure arm. -/
def AcceptedPayout (sevm : Sevm) (p : B256)
    (callPre callPost guardPost returnPre : Devm) : Prop :=
  ∃ (gasWord : B256) (xs : Stack) (parent child : Devm) (xl : Xlot)
    (delegated : Bool) (nextAddress : Adr) (code : ByteArray) (avail pc : Nat),
    (gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs) <<+
      callPre.stack ∧
    Ninst.Run sevm callPre call callPost ∧
    Devm.PopBurn [1] callPost guardPost ∧
    Devm.Burn guardPost returnPre ∧
    Ninst.StepRun pc sevm callPre call xl (.ok callPost) ∧
    0 < sevm.depth ∧
    callPre.stack = gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 ::
      parent.stack ∧
    parent.state = callPre.state ∧
    parent.memory = callPre.memory.extends [(0, 0), (0, 0)] ∧
    parent.logs = callPre.logs ∧
    parent.output = callPre.output ∧
    ((getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) =
          none ∧
        nextAddress = sevm.caller.toB256.toAdr ∧
        code = callPre.getCode sevm.caller.toB256.toAdr ∧
        delegated = false) ∨
      (∃ d,
        getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) =
            some d ∧
          nextAddress = d ∧ code = callPre.getCode d ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg sevm parent
        (min gasWord.toNat (except64th avail) +
          (if p.toNat = 0 then 0 else gCallStipend))
        p sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
        ((callPre.memory.read 0 0).1) code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    (Resume.call parent 0 0).run (.ok child) = .ok callPost ∧
    callPost.state = child.state ∧
    callPost.returnData = child.output ∧
    callPost.memory = parent.memory.write 0 (child.output.take 0) ∧
    callPost.stack = (1 : B256) :: parent.stack

/-- The complete successful source-level `exit`: all guards hold, the four
ledger writes are already present at the call boundary, the exact value call
entered and settled cleanly, and the outer frame returns the payout word.
Callback-final storage and balance are related to the resumed child rather
than falsely summarized as a callback-free delta. -/
def ExitPaysExactly (sevm : Sevm) (entry post : Devm) : Prop :=
  let units := Sevm.dataWord sevm (32 * 0 + 4)
  let oldRow := Devm.getStorVal entry sevm.currentTarget sevm.caller.toB256
  let oldTotal := Devm.getStorVal entry sevm.currentTarget totalUnitsSlot
  let oldChi := Devm.getStorVal entry sevm.currentTarget chiSlot
  let oldRho := Devm.getStorVal entry sevm.currentTarget rhoSlot
  let elapsed := sevm.benvStat.time - oldRho
  let freshChi :=
    (B256.rpow scale half rate elapsed.toNat * oldChi) / scale
  let payout := (freshChi * units) / scale
  ¬ maxUnits < units ∧
    ¬ maxUnits < oldRow ∧
    ¬ maxPie < oldTotal ∧
    ¬ oldRow < units ∧
    ¬ oldTotal < units ∧
    ¬ oldChi < scale ∧
    ¬ maxChi < oldChi ∧
    ¬ sevm.benvStat.time < oldRho ∧
    ¬ maxElapsed < elapsed ∧
    B256.RPowGuards scale half rate elapsed.toNat ∧
    ∃ callPre callPost guardPost returnPre,
      Devm.getStor callPre sevm.currentTarget =
        ((((Devm.getStor entry sevm.currentTarget).set chiSlot freshChi).set
              rhoSlot sevm.benvStat.time).set sevm.caller.toB256
              (oldRow - units)).set totalUnitsSlot (oldTotal - units) ∧
      AcceptedPayout sevm payout callPre callPost guardPost returnPre ∧
      Devm.getStor post = Devm.getStor callPost ∧
      Devm.getBal post = Devm.getBal callPost ∧
      ReturnsWord payout post

theorem exit_pays_exactly {fs : List Func} (hlookup : AuxLookup fs)
    {sevm : Sevm} {entry s post : Devm} {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs sevm s Drip.exit post) :
    ExitPaysExactly sevm entry post := by
  unfold ExitPaysExactly
  dsimp only
  rcases of_run_exit_settles hlookup frame hp run with
    ⟨hargCap, hrowCap, htotalCap, hown, hfund, hlower, hupper, hclock,
      helapsed, hguards, callStart, freshChi, settledImage, hfresh,
      hresult, hpStart, hwfStart, hreadsStart, hstorStart, suffix⟩
  subst freshChi
  refine ⟨hargCap, hrowCap, htotalCap, hown, hfund, hlower, hupper,
    hclock, helapsed, hguards, ?_⟩
  rcases of_run_prepend (loadWord resultWord) _ suffix with
    ⟨sendPre, hload, suffix⟩
  obtain ⟨hpSend, hwfSend, hreadsSend, hstateSend⟩ :=
    of_run_loadWordAt_image (word := resultWord)
      (value :=
        ((B256.rpow scale half rate
              (sevm.benvStat.time -
                Devm.getStorVal entry sevm.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry sevm.currentTarget chiSlot) / scale *
          Sevm.dataWord sevm (32 * 0 + 4)) / scale)
      hpStart hwfStart hreadsStart hresult hload
  rcases of_run_prepend sendToCaller _ suffix with
    ⟨callPost, hsend, hbranch⟩
  rcases exit_sendToCaller_frame hpSend hsend with
    ⟨callPre, gasWord, hstack, hcall, hstorSend, hbalSend, hcodeSend,
      hlogsSend, houtSend, hmemSend⟩
  have hstorTail : Devm.getStor callPost = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hbranch
  have hbalTail : Devm.getBal callPost = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hbranch
  rcases of_run_branch hbranch with
    ⟨_, hzero, hrev⟩ |
      ⟨w, guardPost, returnPre, hw, hpop, hburn, hreturn⟩
  · exact (not_run_revert hrev).elim
  rcases of_run_call_val_with_depth_frame hstack hcall with
      hfailed | hentered
  · exact (hw (popBurn_pref hpop hfailed.1).1).elim
  rcases hentered with
    ⟨parent, child, xl, delegated, nextAddress, code, avail, pc, hstep,
      hdepth, hstackEq, hparentState, hparentMemory, hparentLogs,
      hparentOutput, hdelegated, hfilled, hmessage, hclean, hresume,
      hpostState, hpostReturnData, hpostMemory, hpostStack⟩
  have hpostPrefix : (1 : B256) :: tail <<+ callPost.stack := by
    rw [hpostStack]
    apply pref_cons
    rw [hstackEq] at hstack
    exact cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
      (cons_pref_cons_inv (cons_pref_cons_inv (cons_pref_cons_inv
        (cons_pref_cons_inv hstack))))))
  have hpop1 : Devm.PopBurn [1] callPost guardPost := by
    have hwone : w = 1 := (popBurn_pref hpop hpostPrefix).1
    subst w
    exact hpop
  have hguardPrefix : tail <<+ guardPost.stack :=
    (popBurn_pref hpop1 hpostPrefix).2
  have hreturnPrefix : tail <<+ returnPre.stack := by
    rw [← hburn.stack]
    exact hguardPrefix
  have hstorCallPre :
      Devm.getStor callPre sevm.currentTarget =
        ((((Devm.getStor entry sevm.currentTarget).set chiSlot
                ((B256.rpow scale half rate
                      (sevm.benvStat.time -
                        Devm.getStorVal entry sevm.currentTarget rhoSlot).toNat *
                    Devm.getStorVal entry sevm.currentTarget chiSlot) /
                  scale)).set rhoSlot sevm.benvStat.time).set
            sevm.caller.toB256
            (Devm.getStorVal entry sevm.currentTarget sevm.caller.toB256 -
              Sevm.dataWord sevm (32 * 0 + 4))).set totalUnitsSlot
          (Devm.getStorVal entry sevm.currentTarget totalUnitsSlot -
            Sevm.dataWord sevm (32 * 0 + 4)) := by
    rw [hstorSend,
      ← congrFun (getStor_of_state hstateSend) sevm.currentTarget,
      hstorStart]
  refine ⟨callPre, callPost, guardPost, returnPre, hstorCallPre, ?_,
    hstorTail.symm, hbalTail.symm, ?_⟩
  · unfold AcceptedPayout
    exact ⟨gasWord, tail, parent, child, xl, delegated, nextAddress, code,
      avail, pc, hstack, hcall, hpop1, hburn, hstep, hdepth, hstackEq,
      hparentState, hparentMemory, hparentLogs, hparentOutput, hdelegated,
      hfilled, hmessage, hclean, hresume, hpostState, hpostReturnData,
      hpostMemory, hpostStack⟩
  · have hcallMemory : callPost.memory = callPre.memory := by
      rw [hpostMemory, hparentMemory]
      rfl
    have hwfCallPre : Mem.Wf callPre.memory := by
      rw [hmemSend]
      exact hwfSend
    have hreadsCallPre : Mem.Reads callPre.memory settledImage := by
      rw [hmemSend]
      exact hreadsSend
    have hwfCallPost : Mem.Wf callPost.memory := by
      rw [hcallMemory]
      exact hwfCallPre
    have hreadsCallPost : Mem.Reads callPost.memory settledImage := by
      rw [hcallMemory]
      exact hreadsCallPre
    have hmemoryReturn : callPost.memory = returnPre.memory :=
      hpop1.memory.trans hburn.memory
    have hwfReturn : Mem.Wf returnPre.memory := by
      rw [← hmemoryReturn]
      exact hwfCallPost
    have hreadsReturn : Mem.Reads returnPre.memory settledImage := by
      rw [← hmemoryReturn]
      exact hreadsCallPost
    unfold returnScratch at hreturn
    rcases of_run_prepend (loadWord resultWord) _ hreturn with
      ⟨returnWordPre, hloadReturn, hstoreReturn⟩
    obtain ⟨hpReturn, _, _, _⟩ :=
      of_run_loadWordAt_image (word := resultWord)
        (value :=
          ((B256.rpow scale half rate
                (sevm.benvStat.time -
                  Devm.getStorVal entry sevm.currentTarget rhoSlot).toNat *
              Devm.getStorVal entry sevm.currentTarget chiSlot) / scale *
            Sevm.dataWord sevm (32 * 0 + 4)) / scale)
        hreturnPrefix hwfReturn hreadsReturn hresult hloadReturn
    exact (returnsWord_of_storeReturn hpReturn hstoreReturn).1

end Drip

end Blanc
