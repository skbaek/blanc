-- DripClock.lean : DRIP's accrual clock bounded by an admitted block time.

import Blanc.DripMonotone
import Blanc.ContractAdmission
import Blanc.ExecutionFrameTime

/-!
# C1: timestamp validity in DRIP's family invariant

`ClockInv chi0 rho0 T` strengthens `MonoInv` by the timestamp-validity bound
`rho ≤ T`.  It is not step-closed in the unconditional sense of `StepClosed`:
every accruing endpoint writes `rho := now`, and nothing in the contract bounds
`now`.  What bounds it is the frame's block environment, so the invariant is
proved open-contract sound only relative to a trace-local admission — every
actually entered DRIP frame runs at a block time `≤ T` (`ClockEntry T`).

`StepClosedAt Q P` is `StepClosed P` with `Q now` offered to each accrual
obligation, and `soundAdmitted_of_stepClosedAt` is the twin of
`sound_of_stepClosed` that supplies it: `now` is the frame's own
`benvStat.time`, `Q now` comes from the frame's admission, and the child call
inside `exit` is transported by `ContractSpec.ofStorageOnly_of_call_sameBenv`,
whose deeper-frame hypothesis the admitted one discharges because every frame
the child enters inherits the caller's block statics
(`Exec.frameAdmitted_benvStat`).

`sound_of_stepClosed` is kept rather than re-derived from the twin:
`ContractSpec.Sound` supplies no concrete `Exec` witness for the admission,
and this module sits above `DripSound`.
-/

namespace Blanc

open Jaune

namespace Drip

/-- DRIP's monotone invariant together with timestamp validity: the accrual
clock is at most `T`. -/
def ClockInv (chi0 rho0 T : Nat) (s : Stor) : Prop :=
  MonoInv chi0 rho0 s ∧ rhoN s ≤ T

/-- DRIP's storage-only adapter for the clock-paired invariant. -/
def dripClockSpec (chi0 rho0 T : Nat) : ContractSpec :=
  ContractSpec.ofStorageOnly runtime (ClockInv chi0 rho0 T)

/-- Admission: the frame runs at time `T` or earlier. -/
def ClockEntry (T : Nat) : Sevm → Devm → Prop :=
  fun sevm _ => sevm.benvStat.time.toNat ≤ T

/-- `StepClosed` (DripSound.lean:25) with every accrual field also given
`Q now`. -/
structure StepClosedAt (Q : B256 → Prop) (P : Stor → Prop) : Prop where
  /-- `drip()`: the accrual write of the fresh index and the block timestamp. -/
  drip : ∀ {s : Stor} {fresh now : B256} {elapsed : Nat},
    P s →
    Q now →
    ¬ now < s.get rhoSlot →
    B256.RPowGuards scale half rate elapsed →
    B256.Nofm (s.get chiSlot) (B256.rpow scale half rate elapsed) →
    fresh = (B256.rpow scale half rate elapsed * s.get chiSlot) / scale →
    ¬ maxChi < fresh →
    P ((s.set chiSlot fresh).set rhoSlot now)
  /-- `join()`: the accrual write followed by the paired row/total mint. -/
  join : ∀ {s : Stor} {holder : Adr} {value fresh units now : B256}
      {elapsed : Nat},
    P s →
    Q now →
    ¬ now < s.get rhoSlot →
    B256.RPowGuards scale half rate elapsed →
    B256.Nofm (s.get chiSlot) (B256.rpow scale half rate elapsed) →
    fresh = (B256.rpow scale half rate elapsed * s.get chiSlot) / scale →
    ¬ maxChi < fresh →
    ¬ maxAsset < value →
    units = scale * value / fresh →
    ¬ maxUnits < s.get (pieSlot holder) + units →
    ¬ maxPie < units + s.get totalUnitsSlot →
    P ((((s.set chiSlot fresh).set rhoSlot now).set (pieSlot holder)
        (s.get (pieSlot holder) + units)).set totalUnitsSlot
      (units + s.get totalUnitsSlot))
  /-- `exit()`: the accrual write followed by the paired row/total burn, at the
  settlement boundary immediately before the payout call. -/
  exit : ∀ {s : Stor} {holder : Adr} {fresh units now : B256} {elapsed : Nat},
    P s →
    Q now →
    ¬ now < s.get rhoSlot →
    B256.RPowGuards scale half rate elapsed →
    B256.Nofm (s.get chiSlot) (B256.rpow scale half rate elapsed) →
    fresh = (B256.rpow scale half rate elapsed * s.get chiSlot) / scale →
    ¬ maxChi < fresh →
    ¬ s.get (pieSlot holder) < units →
    ¬ s.get totalUnitsSlot < units →
    P ((((s.set chiSlot fresh).set rhoSlot now).set (pieSlot holder)
        (s.get (pieSlot holder) - units)).set totalUnitsSlot
      (s.get totalUnitsSlot - units))

/-- The per-endpoint obligation of the admitted twin: `FuncSound` with the
frame's `Q now` and a deeper-frame hypothesis restricted to frames at the
caller's block statics. -/
private def FuncSoundAt (Q : B256 → Prop) (P : Stor → Prop) (ca : Adr)
    (body : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    sevm.currentTarget = ca →
    Q sevm.benvStat.time →
    (ContractSpec.ofStorageOnly runtime P).Pre ca sevm s →
    Mem.Wf s.memory →
    Exec.InvDepth sevm.depth ca runtime
      (fun sevm' pre' => sevm'.benvStat = sevm.benvStat ∧
        (ContractSpec.ofStorageOnly runtime P).PreWf ca sevm' pre')
      ((ContractSpec.ofStorageOnly runtime P).Post ca) →
    Func.Run (runtime.main :: runtime.aux) sevm s body r →
    (ContractSpec.ofStorageOnly runtime P).Post ca sevm r

/-- Peeling a successful nonpayable exact-calldata wrapper. -/
private theorem nonpayable_exactCalldata_funcSoundAt {Q : B256 → Prop}
    {P : Stor → Prop} {ca : Adr} {size : B256} {body : Func}
    (hbody : FuncSoundAt Q P ca body) :
    FuncSoundAt Q P ca (nonpayable (exactCalldata size body)) := by
  intro sevm s r htarget hQ hpre hwf hih hrun
  rcases of_run_nonpayable_exactCalldata hrun with
    ⟨mid, -, -, hstate, hmemory, -, -, hbodyRun⟩
  exact hbody htarget hQ (hpre.state_eq hstate.symm)
    (by rw [← hmemory]; exact hwf) hih hbodyRun

/-- Peeling a successful payable exact-calldata wrapper. -/
private theorem exactCalldata_funcSoundAt {Q : B256 → Prop}
    {P : Stor → Prop} {ca : Adr} {size : B256} {body : Func}
    (hbody : FuncSoundAt Q P ca body) :
    FuncSoundAt Q P ca (exactCalldata size body) := by
  intro sevm s r htarget hQ hpre hwf hih hrun
  rcases of_run_exactCalldata hrun with
    ⟨mid, -, hstate, hmemory, -, -, hbodyRun⟩
  exact hbody htarget hQ (hpre.state_eq hstate.symm)
    (by rw [← hmemory]; exact hwf) hih hbodyRun

/-- The entry frame image every raw endpoint walk starts from. -/
private theorem entryFrame {s : Devm} (hwf : Mem.Wf s.memory) :
    Frame s.memory.data.toList s s :=
  ⟨hwf, fun i => by simp, rfl, rfl⟩

private theorem drip_funcSoundAt {Q : B256 → Prop} {P : Stor → Prop}
    (hP : StepClosedAt Q P) (ca : Adr) : FuncSoundAt Q P ca drip := by
  intro sevm s r htarget hQ hpre hwf _ hrun
  subst ca
  rcases of_run_drip auxLookup_runtime (entryFrame hwf) nil_pref hrun with
    ⟨-, -, hclock, -, hguards, hnof, hcap, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [hstor]
  exact hP.drip (hpre.inv.1 rfl) hQ hclock hguards hnof rfl hcap

private theorem join_funcSoundAt {Q : B256 → Prop} {P : Stor → Prop}
    (hP : StepClosedAt Q P) (ca : Adr) : FuncSoundAt Q P ca join := by
  intro sevm s r htarget hQ hpre hwf _ hrun
  subst ca
  rcases of_run_join_full auxLookup_runtime (entryFrame hwf) nil_pref hrun with
    ⟨hasset, -, -, -, -, hclock, -, hguards, hnof, hcap,
      fresh, units, hfresh, hunits, hrowCap, htotalCap, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [hstor]
  exact hP.join (hpre.inv.1 rfl) hQ hclock hguards hnof hfresh
    (by rw [hfresh]; exact hcap) hasset hunits hrowCap htotalCap

private theorem convertToAssets_funcSoundAt {Q : B256 → Prop} {P : Stor → Prop}
    (ca : Adr) : FuncSoundAt Q P ca convertToAssets := by
  intro sevm s r htarget _ hpre hwf _ hrun
  subst ca
  rcases of_run_convertToAssets auxLookup_runtime (entryFrame hwf) nil_pref hrun with
    ⟨-, -, -, -, -, -, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [← congrFun hstor sevm.currentTarget]
  exact hpre.inv.1 rfl

private theorem convertToUnits_funcSoundAt {Q : B256 → Prop} {P : Stor → Prop}
    (ca : Adr) : FuncSoundAt Q P ca convertToUnits := by
  intro sevm s r htarget _ hpre hwf _ hrun
  subst ca
  rcases of_run_convertToUnits auxLookup_runtime (entryFrame hwf) nil_pref hrun with
    ⟨-, -, -, -, -, -, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [← congrFun hstor sevm.currentTarget]
  exact hpre.inv.1 rfl

/-- A successful raw `exit()`: the settlement write takes `Q now`; the payout
call is transported under the same-block deeper-frame hypothesis. -/
private theorem exit_funcSoundAt {Q : B256 → Prop} {P : Stor → Prop}
    (hP : StepClosedAt Q P) (ca : Adr) : FuncSoundAt Q P ca exit := by
  intro sevm s r htarget hQ hpre hwf hih hrun
  subst ca
  rcases exit_pays_exactly_full auxLookup_runtime (entryFrame hwf) nil_pref hrun with
    ⟨-, -, -, hrowCover, htotalCover, -, -, hclock, -, hguards, hnof, hcap,
      callPre, callPost, guardPost, returnPre, hstorCallPre, hcodeCallPre,
      -, haccepted, hstorFinal, -, -⟩
  have hsettled : P (Devm.getStor callPre sevm.currentTarget) := by
    rw [hstorCallPre]
    exact hP.exit (hpre.inv.1 rfl) hQ hclock hguards hnof rfl hcap hrowCover
      htotalCover
  unfold AcceptedPayout at haccepted
  rcases haccepted with
    ⟨gasWord, xs, parent, child, xl, delegated, nextAddress, code, avail, pc,
      hstack, hcall, _⟩
  have hcode :
      some (callPre.getCode sevm.currentTarget).toList = Prog.compile runtime := by
    rw [hcodeCallPre]
    exact hpre.code
  have hchild : P (Devm.getStor callPost sevm.currentTarget) :=
    (ContractSpec.ofStorageOnly_of_call_sameBenv hih hstack hcode hsettled hcall).1
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [congrFun hstorFinal sevm.currentTarget]
  exact hchild

/-- **The admitted DRIP dispatcher.**  Every successful DRIP source run whose
actually entered DRIP frames run at a block time satisfying `Q` preserves any
predicate step-closed under `Q`.  The twin of `sound_of_stepClosed`
(DripSound.lean:215) with `now := sevm.benvStat.time`. -/
theorem soundAdmitted_of_stepClosedAt {Q : B256 → Prop} {P : Stor → Prop}
    (hP : StepClosedAt Q P) (ca : Adr) :
    (ContractSpec.ofStorageOnly runtime P).SoundAdmitted ca
      (fun sevm _ => Q sevm.benvStat.time) := by
  intro sevm pre post execution hrun hca admitted ih hwf hpre
  have hQ : Q sevm.benvStat.time := admitted.root hca
  have hih : Exec.InvDepth sevm.depth ca runtime
      (fun sevm' pre' => sevm'.benvStat = sevm.benvStat ∧
        (ContractSpec.ofStorageOnly runtime P).PreWf ca sevm' pre')
      ((ContractSpec.ofStorageOnly runtime P).Post ca) := by
    intro pc' sevm' devm' exn' child hdepth hat hσ
    cases exn' with
    | error => simp only [ifOk]
    | ok post' =>
        refine ih pc' sevm' devm' post' child hdepth hat ?_ hσ.2
        intro root member target
        rw [Exec.frameAdmitted_benvStat child ca root member target, hσ.1]
        exact hQ
  dsimp only [Prog.Run] at hrun
  cases hrun
  rename (_ = _) => hentry
  rename (Func.Run _ _ _ _ _) => hmain
  rename (Devm.Burn _ _) => hburn
  rename Devm => entry
  cases hentry
  have hpreEntry : (ContractSpec.ofStorageOnly runtime P).Pre ca sevm entry :=
    hpre.state_eq hburn.state.symm
  have hwfEntry : Mem.Wf entry.memory := by
    rw [← hburn.memory]
    exact hwf
  change Func.Run (runtime.main :: runtime.aux) sevm entry main post at hmain
  by_cases hempty : sevm.data.length.toB256 = 0
  · rcases main_receive hmain hempty with ⟨hstate, -, -, -⟩
    exact (ContractSpec.ofStorageOnly runtime P).post_of_pre
      (hpreEntry.state_eq hstate.symm)
  · have hselector := main_selector_mem hmain hempty
    simp only [selectors, List.mem_cons, List.not_mem_nil, or_false] at hselector
    rcases hselector with hselector | hselector | hselector | hselector | hselector
    · rcases main_body (f := nonpayable (exactCalldata 36 convertToAssets))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact nonpayable_exactCalldata_funcSoundAt (convertToAssets_funcSoundAt ca)
        hca hQ (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := nonpayable (exactCalldata 36 exit))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact nonpayable_exactCalldata_funcSoundAt (exit_funcSoundAt hP ca)
        hca hQ (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := nonpayable (exactCalldata 36 convertToUnits))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact nonpayable_exactCalldata_funcSoundAt (convertToUnits_funcSoundAt ca)
        hca hQ (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := nonpayable (exactCalldata 4 drip))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact nonpayable_exactCalldata_funcSoundAt (drip_funcSoundAt hP ca)
        hca hQ (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := exactCalldata 4 join)
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact exactCalldata_funcSoundAt (join_funcSoundAt hP ca)
        hca hQ (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody

/-- The clock bound after an accrual write: the clock becomes `now`, and the
admitted `now ≤ T`. -/
private theorem rhoN_accrual_le {T : Nat} {s : Stor} {fresh now : B256}
    (hnow : now.toNat ≤ T) :
    rhoN ((s.set chiSlot fresh).set rhoSlot now) ≤ T := by
  unfold rhoN
  rw [Stor.get_set_self]
  exact hnow

/-- A paired row/total write after the accrual leaves the clock alone. -/
private theorem rhoN_ledger_write (s : Stor) (holder : Adr) (row total : B256) :
    rhoN ((s.set (pieSlot holder) row).set totalUnitsSlot total) = rhoN s := by
  unfold rhoN
  rw [Stor.get_set_ne _ scalarSlots_distinct.2.2.symm _,
    Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder) _]

/-- `ClockInv` is step-closed under an admitted clock: the `MonoInv` part is
`monoInv_stepClosed`, and the clock part is `rho' = now ≤ T`. -/
theorem clockInv_stepClosedAt (chi0 rho0 T : Nat) :
    StepClosedAt (fun now => now.toNat ≤ T) (ClockInv chi0 rho0 T) where
  drip := by
    intro s fresh now elapsed h hnow hclock hguards hnof hfresh hcap
    exact ⟨(monoInv_stepClosed chi0 rho0).drip h.1 hclock hguards hnof hfresh hcap,
      rhoN_accrual_le hnow⟩
  join := by
    intro s holder value fresh units now elapsed h hnow hclock hguards hnof hfresh
      hcap hasset hunits hrowCap htotalCap
    refine ⟨(monoInv_stepClosed chi0 rho0).join h.1 hclock hguards hnof hfresh
      hcap hasset hunits hrowCap htotalCap, ?_⟩
    rw [rhoN_ledger_write]
    exact rhoN_accrual_le hnow
  exit := by
    intro s holder fresh units now elapsed h hnow hclock hguards hnof hfresh hcap
      hrowCover htotalCover
    refine ⟨(monoInv_stepClosed chi0 rho0).exit h.1 hclock hguards hnof hfresh
      hcap hrowCover htotalCover, ?_⟩
    rw [rhoN_ledger_write]
    exact rhoN_accrual_le hnow

/-- Every successful DRIP source run whose entered DRIP frames run at a block
time `≤ T` preserves `ClockInv chi0 rho0 T`. -/
theorem dripClockSpec_soundAdmitted (chi0 rho0 T : Nat) (ca : Adr) :
    (dripClockSpec chi0 rho0 T).SoundAdmitted ca (ClockEntry T) :=
  soundAdmitted_of_stepClosedAt (clockInv_stepClosedAt chi0 rho0 T) ca

/-- The frame-level admitted preservation form of `ClockInv`, consumed by the
retained execution ladder. -/
theorem dripClockSpec_preservesAdmitted (chi0 rho0 T : Nat) (ca : Adr) :
    (dripClockSpec chi0 rho0 T).PreservesAdmitted ca (ClockEntry T) :=
  (dripClockSpec chi0 rho0 T).preserves_inv_admitted ca (ClockEntry T)
    (dripClockSpec_soundAdmitted chi0 rho0 T ca)

end Drip

end Blanc
