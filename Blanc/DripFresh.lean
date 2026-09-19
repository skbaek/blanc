-- Compatibility import for DRIP's source-level fresh-index proofs.
-- Public declarations retain their Blanc.Drip names in the two owners below.
-- G3 appends the compiled-bridge headlines: the fresh machine instantiated at
-- the deployed runtime literal, plus guard-free Nat images.

import Blanc.DripEndpoints
import Blanc.DripPreservation
import Blanc.DripFunctional
import Blanc.DripAccounting

namespace Blanc

open Jaune

namespace Drip

/-- A successful guarded half-up multiply is exactly `B256.mulr` under the two
no-overflow facts discharged by the runtime's own checks. -/
theorem drip_compiled_guardedMul_is_mulr {fs : List Func} {e : Sevm}
    {entry s r : Devm} {image : Bytes} {tail : Stack}
    {leftWord rightWord outputWord : B256} {next : Func}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run fs e s
      (guardedRoundedMul leftWord rightWord outputWord next) r) :
    ∃ t,
      B256.Nofm (scratch image leftWord) (scratch image rightWord) ∧
      B256.Nof (scratch image rightWord * scratch image leftWord) half ∧
      (half + scratch image rightWord * scratch image leftWord) / scale =
        B256.mulr scale half (scratch image leftWord)
          (scratch image rightWord) ∧
      Func.Run fs e t next r := by
  obtain ⟨t, hnofm, hnof, hpt, hframe, hrun⟩ :=
    of_run_guardedRoundedMul frame hp run
  refine ⟨t, hnofm, hnof, ?_, hrun⟩
  unfold B256.mulr
  rw [B256.mul_comm (scratch image leftWord) (scratch image rightWord),
    B256.add_comm]

/-- At exponent zero the compiled loop is the identity on the accumulator. -/
theorem drip_compiled_rpowLoop_zero {e : Sevm} {entry r : Devm}
    {s : Devm} {image : Bytes} {tail : Stack}
    (hexp : (scratch image exponentWord).toNat = 0)
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run (runtime.main :: runtime.aux) e s
      (.call rpowLoopSlot) r) :
    ∃ t image',
      scratch image' accumulatorWord = scratch image accumulatorWord ∧
        LoopOnly image image' ∧
        Frame image' entry t ∧ (tail <<+ t.stack) ∧
        Func.Run (runtime.main :: runtime.aux) e t
          (.call composeFreshSlot) r := by
  obtain ⟨t, image', hguards, hacc, hloop, hframe, hpt, hrun⟩ :=
    of_run_rpowLoop auxLookup_runtime (n := 0) hexp frame hp run
  refine ⟨t, image', ?_, hloop, hframe, hpt, hrun⟩
  rw [B256.rpowLoop, dif_pos rfl] at hacc
  exact hacc

/-- The compiled fresh machine: a successful run of the deployed `freshStart`
auxiliary crosses the four frozen guards, realizes `B256.rpow` under Jaune's
own guard bundle, floor-composes under the exact no-overflow check and index
cap, and stages the fresh index for its route continuation. -/
theorem drip_compiled_freshStart {e : Sevm} {entry s r : Devm} {image : Bytes}
    {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run (runtime.main :: runtime.aux) e s
      (.call freshStartSlot) r) :
    ∃ t image',
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
      scratch image' accumulatorWord =
        B256.rpow scale half rate
          (e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot).toNat ∧
      scratch image' nowWord = e.benvStat.time ∧
      MachineOnly image image' ∧
      Frame image' entry t ∧
      (((B256.rpow scale half rate
          (e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
          Devm.getStorVal entry e.currentTarget chiSlot) / scale) :: tail <<+ t.stack) ∧
      Func.Run (runtime.main :: runtime.aux) e t
        (.call freshRouteSlot) r := by
  exact of_run_freshStart auxLookup_runtime frame hp run

/-- The word guard, derived from a successful compiled run at the frozen
constants: loop guards, composition no-overflow, and the post cap. -/
theorem drip_compiled_guards_of_run {e : Sevm} {entry s r : Devm}
    {image : Bytes} {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run (runtime.main :: runtime.aux) e s
      (.call freshStartSlot) r) :
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
            Devm.getStorVal entry e.currentTarget chiSlot) / scale := by
  obtain ⟨t, image', hchiLo, hchiHi, hclock, helapsed, hguards, hnofm, hcap,
    hacc, hnow, hmach, hframe, hstack, hrun⟩ :=
    drip_compiled_freshStart frame hp run
  exact ⟨hguards, hnofm, hcap⟩

/-- Guard-free Nat image of the realized factor at the frozen constants. -/
theorem drip_compiled_factorNat {e : Sevm} {entry s r : Devm} {image : Bytes}
    {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run (runtime.main :: runtime.aux) e s
      (.call freshStartSlot) r) :
    (B256.rpow scale half rate
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat).toNat =
      Jaune.rpow scale.toNat half.toNat rate.toNat
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat := by
  obtain ⟨hguards, hnofm, hcap⟩ := drip_compiled_guards_of_run frame hp run
  have hscale : scale ≠ 0 := by decide +kernel
  exact B256.toNat_rpow hscale _ hguards

/-- Guard-free Nat image of the floor composition: the staged fresh word reads
as the exact `chi * f / S` quotient. -/
theorem drip_compiled_freshNat {e : Sevm} {entry s r : Devm} {image : Bytes}
    {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run (runtime.main :: runtime.aux) e s
      (.call freshStartSlot) r) :
    ((B256.rpow scale half rate
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
        Devm.getStorVal entry e.currentTarget chiSlot) / scale).toNat =
      (Devm.getStorVal entry e.currentTarget chiSlot).toNat *
        Jaune.rpow scale.toNat half.toNat rate.toNat
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat /
        scale.toNat := by
  obtain ⟨hguards, hnofm, hcap⟩ := drip_compiled_guards_of_run frame hp run
  have hscale : scale ≠ 0 := by decide +kernel
  have hbridge := B256.toNat_rpow hscale _ hguards
  rw [B256.mul_comm, B256.toNat_div hscale,
    B256.toNat_mul_eq_of_nofm hnofm, hbridge]

/-! ## G5: compiled freshness and same-block agreement -/

/-- A successful compiled `join` uses the fresh index for its conversion and
writes the fresh index, clock, caller row, and total in the endpoint's order. -/
theorem drip_compiled_join {e : Sevm} {entry s r : Devm} {image : Bytes}
    {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run (runtime.main :: runtime.aux) e s Drip.join r) :
    ∃ postChi units,
      Devm.getStor r e.currentTarget =
        ((((Devm.getStor entry e.currentTarget).set chiSlot postChi).set
        rhoSlot e.benvStat.time).set e.caller.toB256
          (Devm.getStorVal entry e.currentTarget e.caller.toB256 + units)).set
          totalUnitsSlot
          (units + Devm.getStorVal entry e.currentTarget totalUnitsSlot) ∧
      postChi.toNat =
        (Devm.getStorVal entry e.currentTarget chiSlot).toNat *
          Jaune.rpow scale.toNat half.toNat rate.toNat
            (e.benvStat.time -
              Devm.getStorVal entry e.currentTarget rhoSlot).toNat /
          scale.toNat ∧
      units.toNat = joinUnitsOf scale.toNat e.value.toNat postChi.toNat ∧
      ReturnsWord units r := by
  obtain ⟨hasset, hrow, htotal, hlower, hupper, hclock, helapsed,
    hguards, hnofm, hcap, freshChi, units, hfresh, hunits, hrowPost,
    htotalPost, hstor, hret⟩ :=
    of_run_join_full auxLookup_runtime frame hp run
  have hscale : scale ≠ 0 := by decide +kernel
  have hscaleValueNof : B256.Nofm scale e.value :=
    join_scale_value_nofm hasset
  have hfreshLower : scale.toNat ≤ freshChi.toNat := by
    rw [hfresh, freshChi_toNat _ _ hguards hnofm]
    exact (B256.toNat_le_toNat (le_of_not_gt hlower)).trans
      (freshNat_mono _ _)
  have hfreshNe : freshChi ≠ 0 := by
    intro hz
    have hpos : 0 < scale.toNat := by
      rw [scale_literal]
      decide +kernel
    apply (Nat.ne_of_gt hpos)
    apply Nat.eq_zero_of_le_zero
    rw [hz, B256.toNat_zero] at hfreshLower
    exact hfreshLower
  have _hunitLeValue : units.toNat ≤ e.value.toNat :=
    join_units_le_value hunits hfreshLower hscaleValueNof
  have hfreshNat0 : freshChi.toNat = freshNat
      (Devm.getStorVal entry e.currentTarget chiSlot).toNat
      (e.benvStat.time -
        Devm.getStorVal entry e.currentTarget rhoSlot).toNat := by
    rw [hfresh]
    exact freshChi_toNat _ _ hguards hnofm
  refine ⟨freshChi, units, hstor, ?_, ?_, hret⟩
  · have hfreshNat := freshChi_toNat
        (Devm.getStorVal entry e.currentTarget chiSlot)
        (e.benvStat.time -
          Devm.getStorVal entry e.currentTarget rhoSlot).toNat
        hguards hnofm
    calc
      freshChi.toNat =
          ((B256.rpow scale half rate
            (e.benvStat.time -
              Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
            Devm.getStorVal entry e.currentTarget chiSlot) / scale).toNat :=
        congrArg B256.toNat hfresh
      _ = freshNat
          (Devm.getStorVal entry e.currentTarget chiSlot).toNat
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat := hfreshNat
      _ = _ := by rfl
  · rw [hunits, B256.toNat_div hfreshNe,
      B256.toNat_mul_eq_of_nofm hscaleValueNof,
      hfreshNat0]
    simp only [joinUnitsOf, Nat.mul_comm]

/-- A successful compiled `exit` settles its fresh index and debit before the
value-transfer call, and the payout is the exact fresh-index floor.  The
`ExitPaysExactlyFull` carrier retains the call-boundary witnesses. -/
theorem drip_compiled_exit {e : Sevm} {entry s r : Devm} {image : Bytes}
    {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run (runtime.main :: runtime.aux) e s Drip.exit r) :
    ∃ (postChi payout : B256),
      postChi.toNat =
        (Devm.getStorVal entry e.currentTarget chiSlot).toNat *
          Jaune.rpow scale.toNat half.toNat rate.toNat
            (e.benvStat.time -
              Devm.getStorVal entry e.currentTarget rhoSlot).toNat /
          scale.toNat ∧
      payout.toNat =
        exitPayoutOf scale.toNat (Sevm.dataWord e (32 * 0 + 4)).toNat
          postChi.toNat ∧
      ExitPaysExactlyFull e entry r := by
  have hfull : ExitPaysExactlyFull e entry r :=
    exit_pays_exactly_full auxLookup_runtime frame hp run
  have hfullKeep := hfull
  unfold ExitPaysExactlyFull at hfull
  dsimp only at hfull
  rcases hfull with
    ⟨hargCap, hrowCap, htotalCap, hown, hfund, hlower, hupper, hclock,
      helapsed, hguards, hnofm, hcapChi, callPre, callPost, guardPost,
      returnPre, hstor, hcode, -, haccepted, hpost, hbal, hret⟩
  let postChi :=
    (B256.rpow scale half rate
      (e.benvStat.time - Devm.getStorVal entry e.currentTarget rhoSlot).toNat *
      Devm.getStorVal entry e.currentTarget chiSlot) / scale
  let payout := postChi * Sevm.dataWord e (32 * 0 + 4) / scale
  have hscale : scale ≠ 0 := by decide +kernel
  have hpostNat : postChi.toNat =
      (Devm.getStorVal entry e.currentTarget chiSlot).toNat *
        Jaune.rpow scale.toNat half.toNat rate.toNat
          (e.benvStat.time -
            Devm.getStorVal entry e.currentTarget rhoSlot).toNat /
        scale.toNat := by
    unfold postChi
    rw [B256.mul_comm, B256.toNat_div hscale,
      B256.toNat_mul_eq_of_nofm hnofm]
    exact congrArg (fun x =>
      (Devm.getStorVal entry e.currentTarget chiSlot).toNat * x /
        scale.toNat) (B256.toNat_rpow hscale _ hguards)
  have hpayoutNat : payout.toNat =
      exitPayoutOf scale.toNat (Sevm.dataWord e (32 * 0 + 4)).toNat
        postChi.toNat := by
    unfold payout exitPayoutOf
    have hnofPayout : B256.Nofm postChi
        (Sevm.dataWord e (32 * 0 + 4)) := by
      unfold B256.Nofm
      exact lt_of_le_of_lt
        (Nat.mul_le_mul
          (B256.toNat_le_toNat (le_of_not_gt hcapChi))
          (B256.toNat_le_toNat (le_of_not_gt hargCap))) (by
            rw [maxChi_literal, maxUnits_literal]
            decide +kernel)
    rw [B256.toNat_div hscale,
      B256.toNat_mul_eq_of_nofm hnofPayout]
    simp only [Nat.mul_comm]
  refine ⟨postChi, payout, hpostNat, hpayoutNat, ?_⟩
  exact hfullKeep

/-- End-to-end compiled `drip`: the stored and returned fresh index read as the
exact Nat quotient. -/
theorem drip_compiled_drip {e : Sevm} {entry s r : Devm} {image : Bytes}
    {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run (runtime.main :: runtime.aux) e s Drip.drip r) :
    ∃ postChi ret,
      Devm.getStor r e.currentTarget =
        ((Devm.getStor entry e.currentTarget).set chiSlot postChi).set rhoSlot
          e.benvStat.time ∧
      postChi.toNat =
        (Devm.getStorVal entry e.currentTarget chiSlot).toNat *
          Jaune.rpow scale.toNat half.toNat rate.toNat
            (e.benvStat.time -
              Devm.getStorVal entry e.currentTarget rhoSlot).toNat /
          scale.toNat ∧
      ReturnsWord ret r ∧ ret = postChi := by
  obtain ⟨hchiLo, hchiHi, hclock, helapsed, hguards, hnofm, hcap, hstor, hret⟩ :=
    of_run_drip auxLookup_runtime frame hp run
  have hscale : scale ≠ 0 := by decide +kernel
  have hbridge := B256.toNat_rpow hscale _ hguards
  refine ⟨_, _, hstor, ?_, hret, rfl⟩
  rw [B256.mul_comm, B256.toNat_div hscale,
    B256.toNat_mul_eq_of_nofm hnofm, hbridge]

/-! ### F3: the no-stale-index success route

The design's F3 (`no_stale_index_success`, section 3.2 of the G4/G5 design)
asks for one statement over the three mutating selectors.  **Two of its three
arms are below; the `exit` arm is not closable from this tree.**  `exit`
settles its ledger *before* the payout call, so its post-state is the resumed
child's, and the design's own risk R3 names the transport.  R3's mitigation is
not sufficient: `MonoInv` (U1) transports `rho0 ≤ rhoN` *upwards* through a
child, which gives `time ≤ rhoN post`, whereas F3's equation also needs
`rhoN post ≤ time`.  No `ContractSpec` can supply that bound, because
`ContractSpec.Inv : Stor -> B256 -> B256 -> Prop` never sees the block
environment while `Sound`/`Preserves` quantify over every `Sevm`, so an
instance at a fixed timestamp is false.  The fact is true — `callMsg` copies
`sevm.benvStat` into the child, so every nested frame writes the *same* `now`
— but using it needs a block-indexed frame ladder (a `lift_inv`
instantiation whose `sigma`/`rho` are `Sevm`-indexed), which lives in the
shared ladder, not here.  `no_stale_index_settlement_exit` carries the exit
arm exactly as far as the current machinery reaches. -/

/-- F3 for the two callback-free mutating selectors.  A successful deployed
`drip()` or `join()` call cannot have run at a stale index: the stored clock
was at or before the block timestamp on entry, it is exactly the block
timestamp afterwards, and the stored index is the exact fresh index for the
elapsed interval. -/
theorem no_stale_index_success_callback_free {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (hsel : Sevm.selector sevm = dripSelector ∨
      Sevm.selector sevm = joinSelector) :
    Devm.getStorVal pre sevm.currentTarget rhoSlot ≤ sevm.benvStat.time ∧
      Devm.getStorVal post sevm.currentTarget rhoSlot = sevm.benvStat.time ∧
      (Devm.getStorVal post sevm.currentTarget chiSlot).toNat =
        freshNat (Devm.getStorVal pre sevm.currentTarget chiSlot).toNat
          (sevm.benvStat.time -
            Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat := by
  rcases hsel with hsel | hsel
  · obtain ⟨hlower, hupper, hclock, helapsed, hguards, hnofm, hcap, hstor,
      hret⟩ := drip_exec_effect exc hcode hsel hnonempty hcanon
    refine ⟨le_of_not_gt hclock, ?_, ?_⟩
    · show (Devm.getStor post sevm.currentTarget).get rhoSlot = _
      rw [hstor, Stor.get_set_self]
    · show ((Devm.getStor post sevm.currentTarget).get chiSlot).toNat = _
      rw [hstor, Stor.get_set_ne _ (by decide +kernel : rhoSlot ≠ chiSlot),
        Stor.get_set_self]
      exact freshChi_toNat _ _ hguards hnofm
  · rcases exec_enters_join exc hcode hsel hnonempty with
      ⟨-, entry, hst, hmm, -, -, hbody⟩
    have hmem : entry.memory = Mem.empty := by rw [← hmm, hcanon]
    have hframe : Frame [] entry entry :=
      ⟨by rw [hmem]; exact Mem.wf_empty,
        by rw [hmem]; exact Mem.reads_empty, rfl, rfl⟩
    have heffect := of_run_join_full auxLookup_runtime hframe nil_pref hbody
    have hgv : ∀ k, Devm.getStorVal entry sevm.currentTarget k =
        Devm.getStorVal pre sevm.currentTarget k :=
      fun k => Devm.getStorVal_of_state hst.symm sevm.currentTarget k
    have hg : Devm.getStor entry sevm.currentTarget =
        Devm.getStor pre sevm.currentTarget :=
      getStor_eq_of_state_eq hst.symm sevm.currentTarget
    simp only [hgv, hg] at heffect
    obtain ⟨hasset, hrow, htotal, hlower, hupper, hclock, helapsed,
      hguards, hnofm, hcap, freshChi, units, hfresh, hunits, hrowPost,
      htotalPost, hstor, hret⟩ := heffect
    refine ⟨le_of_not_gt hclock, ?_, ?_⟩
    · show (Devm.getStor post sevm.currentTarget).get rhoSlot = _
      rw [hstor,
        Stor.get_set_ne _ (by decide +kernel : totalUnitsSlot ≠ rhoSlot),
        Stor.get_set_ne _
          (show sevm.caller.toB256 ≠ rhoSlot from pieSlot_ne_rhoSlot sevm.caller),
        Stor.get_set_self]
    · show ((Devm.getStor post sevm.currentTarget).get chiSlot).toNat = _
      rw [hstor,
        Stor.get_set_ne _ (by decide +kernel : totalUnitsSlot ≠ chiSlot),
        Stor.get_set_ne _
          (show sevm.caller.toB256 ≠ chiSlot from pieSlot_ne_chiSlot sevm.caller),
        Stor.get_set_ne _ (by decide +kernel : rhoSlot ≠ chiSlot),
        Stor.get_set_self, hfresh]
      exact freshChi_toNat _ _ hguards hnofm

/-- F3's `exit` arm, as far as the tree's machinery reaches.  The two
no-stale-index equations hold **at the settlement boundary** `callPre`, the
state immediately before the payout call, and the whole remaining distance to
`post` is the exhibited `AcceptedPayout` plus `Devm.getStor post =
Devm.getStor callPost`.  Lifting the two equations across that child is the
missing step described above the previous theorem; it is not weakened here,
it is left visible. -/
theorem no_stale_index_settlement_exit {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = exitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    Devm.getStorVal pre sevm.currentTarget rhoSlot ≤ sevm.benvStat.time ∧
      ∃ callPre callPost guardPost returnPre,
        (Devm.getStor callPre sevm.currentTarget).get rhoSlot =
            sevm.benvStat.time ∧
          ((Devm.getStor callPre sevm.currentTarget).get chiSlot).toNat =
            freshNat (Devm.getStorVal pre sevm.currentTarget chiSlot).toNat
              (sevm.benvStat.time -
                Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat ∧
          AcceptedPayout sevm
            ((B256.rpow scale half rate
                  (sevm.benvStat.time -
                    Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
                Devm.getStorVal pre sevm.currentTarget chiSlot / scale) *
              Sevm.dataWord sevm (32 * 0 + 4) / scale)
            callPre callPost guardPost returnPre ∧
          Devm.getStor post = Devm.getStor callPost := by
  have hfull := exit_exec_effect_full exc hcode hsel hnonempty hcanon
  unfold ExitPaysExactlyFull at hfull
  dsimp only at hfull
  rcases hfull with
    ⟨hargCap, hrowCap, htotalCap, hown, hfund, hlower, hupper, hclock,
      helapsed, hguards, hnofm, hcapChi, callPre, callPost, guardPost,
      returnPre, hstorCallPre, hcodeCallPre, -, haccepted, hstorFinal,
      hbalFinal, hretFinal⟩
  refine ⟨le_of_not_gt hclock, callPre, callPost, guardPost, returnPre,
    ?_, ?_, haccepted, hstorFinal⟩
  · rw [hstorCallPre,
      Stor.get_set_ne _ (by decide +kernel : totalUnitsSlot ≠ rhoSlot),
      Stor.get_set_ne _
        (show sevm.caller.toB256 ≠ rhoSlot from pieSlot_ne_rhoSlot sevm.caller),
      Stor.get_set_self]
  · rw [hstorCallPre,
      Stor.get_set_ne _ (by decide +kernel : totalUnitsSlot ≠ chiSlot),
      Stor.get_set_ne _
        (show sevm.caller.toB256 ≠ chiSlot from pieSlot_ne_chiSlot sevm.caller),
      Stor.get_set_ne _ (by decide +kernel : rhoSlot ≠ chiSlot),
      Stor.get_set_self]
    exact freshChi_toNat _ _ hguards hnofm

/-- F4.  Same-timestamp view/mutation agreement: at one block timestamp and
one pre-state, the `convertToUnits(assets)` preview returns exactly the units
that a `join()` carrying the same `assets` as callvalue actually mints.  The
preview is therefore not a stale-index quote, and a caller cannot arbitrage
the two entry points inside a block. -/
theorem view_eq_same_timestamp_join {view mint : Sevm}
    {pre viewPost mintPost : Devm}
    (excView : Exec 0 view pre (.ok viewPost))
    (excMint : Exec 0 mint pre (.ok mintPost))
    (hcodeView : view.code.toList = code)
    (hcodeMint : mint.code.toList = code)
    (hselView : Sevm.selector view = convertToUnitsSelector)
    (hselMint : Sevm.selector mint = joinSelector)
    (hneView : view.data.length.toB256 ≠ 0)
    (hneMint : mint.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (htarget : view.currentTarget = mint.currentTarget)
    (htime : view.benvStat.time = mint.benvStat.time)
    (hvalue : Sevm.dataWord view (32 * 0 + 4) = mint.value) :
    ReturnsWord
        (scale * mint.value /
          ((B256.rpow scale half rate
                (mint.benvStat.time -
                  Devm.getStorVal pre mint.currentTarget rhoSlot).toNat *
              Devm.getStorVal pre mint.currentTarget chiSlot) / scale))
        viewPost ∧
      ReturnsWord
        (scale * mint.value /
          ((B256.rpow scale half rate
                (mint.benvStat.time -
                  Devm.getStorVal pre mint.currentTarget rhoSlot).toNat *
              Devm.getStorVal pre mint.currentTarget chiSlot) / scale))
        mintPost := by
  obtain ⟨-, -, -, -, -, -, -, hviewRet⟩ :=
    convertToUnits_exec_effect excView hcodeView hselView hneView hcanon
  obtain ⟨-, -, -, -, -, -, -, -, freshChi, units, hfresh, hunits, -, -, -,
    hmintRet⟩ :=
    join_exec_effect excMint hcodeMint hselMint hneMint hcanon
  rw [htarget, htime, hvalue] at hviewRet
  refine ⟨hviewRet, ?_⟩
  rwa [hunits, hfresh] at hmintRet

end Drip

end Blanc
