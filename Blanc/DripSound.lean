-- DripSound.lean : open-contract soundness for DRIP's realized ledger.

import Blanc.DripPreservation
import Blanc.DripFunctional

namespace Blanc

open Jaune

namespace Drip

/-- Peeling a successful nonpayable exact-calldata wrapper transports the
precondition and memory well-formedness to the raw endpoint body. -/
private theorem nonpayable_exactCalldata_funcSound
    (ca : Adr) {size : B256} {body : Func}
    (hbody : dripSpec.FuncSound ca runtime.aux body) :
    dripSpec.FuncSound ca runtime.aux (nonpayable (exactCalldata size body)) := by
  intro sevm s r htarget hpre hwf hih hrun
  rcases of_run_nonpayable_exactCalldata hrun with
    ⟨mid, -, -, hstate, hmemory, -, -, hbodyRun⟩
  exact hbody htarget (hpre.state_eq hstate.symm)
    (by rw [← hmemory]; exact hwf) hih hbodyRun

/-- Peeling a successful payable exact-calldata wrapper transports the same
entry facts to its raw endpoint. -/
private theorem exactCalldata_funcSound
    (ca : Adr) {size : B256} {body : Func}
    (hbody : dripSpec.FuncSound ca runtime.aux body) :
    dripSpec.FuncSound ca runtime.aux (exactCalldata size body) := by
  intro sevm s r htarget hpre hwf hih hrun
  rcases of_run_exactCalldata hrun with
    ⟨mid, -, hstate, hmemory, -, -, hbodyRun⟩
  exact hbody htarget (hpre.state_eq hstate.symm)
    (by rw [← hmemory]; exact hwf) hih hbodyRun

/-- The raw `drip()` body preserves the storage-only specification from an
arbitrary well-formed entry memory. -/
private theorem drip_funcSound (ca : Adr) :
    dripSpec.FuncSound ca runtime.aux drip := by
  intro sevm s r htarget hpre hwf _ hrun
  subst ca
  have hinv : AccountingInv (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases of_run_drip auxLookup_runtime frame nil_pref hrun with
    ⟨-, -, -, -, hguards, hnof, hcap, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change AccountingInv (Devm.getStor r sevm.currentTarget)
  rw [hstor]
  exact hinv.drip_write
    (hinv.fresh_lower _ hguards hnof)
    (B256.toNat_le_toNat (le_of_not_gt hcap))

/-- A raw payable `join()` uses the endpoint's multiplication no-wrap and
fresh-index cap facts to derive its two checked additions before preserving the
full-address ledger. -/
private theorem join_funcSound (ca : Adr) :
    dripSpec.FuncSound ca runtime.aux join := by
  intro sevm s r htarget hpre hwf _ hrun
  subst ca
  have hinv : AccountingInv (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases of_run_join_full auxLookup_runtime frame nil_pref hrun with
    ⟨hasset, -, -, -, -, -, -, hguards, hnof, hcap,
      fresh, units, hfresh, hunits, hrowCap, htotalCap, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change AccountingInv (Devm.getStor r sevm.currentTarget)
  rw [hstor]
  apply hinv.join_write_of_effect hasset hguards hnof
  · rw [hfresh]
    exact hcap
  · exact hfresh
  · exact hunits
  · exact hrowCap
  · exact htotalCap

/-- The conversion previews leave the full storage invariant unchanged. -/
private theorem convertToAssets_funcSound (ca : Adr) :
    dripSpec.FuncSound ca runtime.aux convertToAssets := by
  intro sevm s r htarget hpre hwf _ hrun
  subst ca
  have hinv : AccountingInv (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases of_run_convertToAssets auxLookup_runtime frame nil_pref hrun with
    ⟨-, -, -, -, -, -, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change AccountingInv (Devm.getStor r sevm.currentTarget)
  rw [← congrFun hstor sevm.currentTarget]
  exact hinv

/-- The other conversion preview leaves the full storage invariant unchanged. -/
private theorem convertToUnits_funcSound (ca : Adr) :
    dripSpec.FuncSound ca runtime.aux convertToUnits := by
  intro sevm s r htarget hpre hwf _ hrun
  subst ca
  have hinv : AccountingInv (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases of_run_convertToUnits auxLookup_runtime frame nil_pref hrun with
    ⟨-, -, -, -, -, -, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change AccountingInv (Devm.getStor r sevm.currentTarget)
  rw [← congrFun hstor sevm.currentTarget]
  exact hinv

/-- A successful raw `exit()` settles the debit before the real child call.
The storage-only call adapter applies the retained deeper-frame hypothesis to
that actual call; final storage is then transported through the resumed parent. -/
private theorem exit_funcSound (ca : Adr) :
    dripSpec.FuncSound ca runtime.aux exit := by
  intro sevm s r htarget hpre hwf hih hrun
  subst ca
  have hinv : AccountingInv (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases exit_pays_exactly_full auxLookup_runtime frame nil_pref hrun with
    ⟨-, -, -, hrowCover, htotalCover, -, -, -, -, hguards, hnof, hcap,
      callPre, callPost, guardPost, returnPre, hstorCallPre, hcodeCallPre,
      haccepted, hstorFinal, -, -⟩
  have hsettled : AccountingInv (Devm.getStor callPre sevm.currentTarget) := by
    let fresh :=
      (B256.rpow scale half rate
        (sevm.benvStat.time - s.getStorVal sevm.currentTarget rhoSlot).toNat *
        s.getStorVal sevm.currentTarget chiSlot) / scale
    let units := Sevm.dataWord sevm (32 * 0 + 4)
    let accrued :=
      ((Devm.getStor s sevm.currentTarget).set chiSlot fresh).set
        rhoSlot sevm.benvStat.time
    have hfreshLower : scale.toNat ≤ fresh.toNat := by
      dsimp only [fresh]
      exact hinv.fresh_lower _ hguards hnof
    have hfreshUpper : fresh.toNat ≤ maxChi.toNat := by
      dsimp only [fresh]
      exact B256.toNat_le_toNat (le_of_not_gt hcap)
    have haccrued : AccountingInv accrued := by
      dsimp only [accrued]
      exact hinv.drip_write hfreshLower hfreshUpper
    have hrowCoverAccrued : units ≤ accrued.get (pieSlot sevm.caller) := by
      dsimp only [units, accrued]
      rw [Stor.get_set_ne _ (pieSlot_ne_rhoSlot sevm.caller).symm _,
        Stor.get_set_ne _ (pieSlot_ne_chiSlot sevm.caller).symm _]
      exact le_of_not_gt hrowCover
    have htotalCoverAccrued : units ≤ accrued.get totalUnitsSlot := by
      dsimp only [units, accrued]
      rw [Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
        Stor.get_set_ne _ scalarSlots_distinct.2.1 _]
      exact le_of_not_gt htotalCover
    have hsettledRaw : AccountingInv
        ((accrued.set (pieSlot sevm.caller)
          (accrued.get (pieSlot sevm.caller) - units)).set totalUnitsSlot
          (accrued.get totalUnitsSlot - units)) :=
      haccrued.exit_ledger_write hrowCoverAccrued htotalCoverAccrued
    have hcallPre : Devm.getStor callPre sevm.currentTarget =
        ((accrued.set (pieSlot sevm.caller)
          (accrued.get (pieSlot sevm.caller) - units)).set totalUnitsSlot
      (accrued.get totalUnitsSlot - units)) := by
      rw [hstorCallPre]
      dsimp only [accrued, fresh, units]
      rw [Stor.get_set_ne _ (pieSlot_ne_rhoSlot sevm.caller).symm _,
        Stor.get_set_ne _ (pieSlot_ne_chiSlot sevm.caller).symm _,
        Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
        Stor.get_set_ne _ scalarSlots_distinct.2.1 _]
      simp only [pieSlot, Devm.getStorVal, Devm.getStor]
    rw [hcallPre]
    exact hsettledRaw
  unfold AcceptedPayout at haccepted
  rcases haccepted with
    ⟨gasWord, xs, parent, child, xl, delegated, nextAddress, code, avail, pc,
      hstack, hcall, _⟩
  have hcode :
      some (callPre.getCode sevm.currentTarget).toList = Prog.compile runtime := by
    rw [hcodeCallPre]
    exact hpre.code
  have hchild : AccountingInv (Devm.getStor callPost sevm.currentTarget) :=
    (ContractSpec.ofStorageOnly_of_call hih hstack hcode hsettled hcall).1
  refine ⟨trivial, ?_⟩
  change AccountingInv (Devm.getStor r sevm.currentTarget)
  rw [congrFun hstorFinal sevm.currentTarget]
  exact hchild

/-- Every successful DRIP source run preserves `AccountingInv`.  The actual
top-level branch is classified before a raw endpoint proof is selected, so
the receive and each frozen wrapper retain their distinct runtime evidence. -/
theorem dripSpec_sound (ca : Adr) : dripSpec.Sound ca := by
  intro sevm pre post hrun hca ih hwf hpre
  have hih : Exec.InvDepth sevm.depth ca dripSpec.prog
      (dripSpec.PreWf ca) (dripSpec.Post ca) := by
    intro pc' sevm' devm' exn'
    cases exn'
    · simp only [ifOk, implies_true]
    · apply ih
  dsimp only [Prog.Run] at hrun
  cases hrun
  rename (_ = _) => hentry
  rename (Func.Run _ _ _ _ _) => hmain
  rename (Devm.Burn _ _) => hburn
  rename Devm => entry
  cases hentry
  have hpreEntry : dripSpec.Pre ca sevm entry :=
    hpre.state_eq hburn.state.symm
  have hwfEntry : Mem.Wf entry.memory := by
    rw [← hburn.memory]
    exact hwf
  change Func.Run (runtime.main :: runtime.aux) sevm entry main post at hmain
  by_cases hempty : sevm.data.length.toB256 = 0
  · rcases main_receive hmain hempty with ⟨hstate, -, -, -⟩
    exact dripSpec.post_of_pre (hpreEntry.state_eq hstate.symm)
  · have hselector := main_selector_mem hmain hempty
    simp only [selectors, List.mem_cons, List.not_mem_nil, or_false] at hselector
    rcases hselector with hselector | hselector | hselector | hselector | hselector
    · rcases main_body (f := nonpayable (exactCalldata 36 convertToAssets))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact (nonpayable_exactCalldata_funcSound ca (convertToAssets_funcSound ca))
        hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := nonpayable (exactCalldata 36 exit))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact (nonpayable_exactCalldata_funcSound ca (exit_funcSound ca))
        hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := nonpayable (exactCalldata 36 convertToUnits))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact (nonpayable_exactCalldata_funcSound ca (convertToUnits_funcSound ca))
        hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := nonpayable (exactCalldata 4 drip))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact (nonpayable_exactCalldata_funcSound ca (drip_funcSound ca))
        hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := exactCalldata 4 join)
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact (exactCalldata_funcSound ca (join_funcSound ca))
        hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody

/-- The frame-level preservation form consumed by the retained execution
ladder. -/
theorem dripSpec_preserves (ca : Adr) : dripSpec.Preserves ca :=
  dripSpec.preserves_inv ca (dripSpec_sound ca)

end Drip

end Blanc
