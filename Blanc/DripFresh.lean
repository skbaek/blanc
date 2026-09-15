-- Compatibility import for DRIP's source-level fresh-index proofs.
-- Public declarations retain their Blanc.Drip names in the two owners below.
-- G3 appends the compiled-bridge headlines: the fresh machine instantiated at
-- the deployed runtime literal, plus guard-free Nat images.

import Blanc.DripEndpoints

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

end Drip

end Blanc
