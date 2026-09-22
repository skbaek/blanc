-- DripSound.lean : open-contract soundness for DRIP's realized ledger.

import Blanc.DripPreservation
import Blanc.DripFunctional

namespace Blanc

open Jaune

namespace Drip

/-- The storage obligations of DRIP's three writing endpoints, stated over an
arbitrary storage predicate `P`.  `sound_of_stepClosed` is the one dispatcher
proof that turns a step-closed predicate into open-contract soundness of
`ContractSpec.ofStorageOnly runtime P`; `AccountingInv` and `MonoInv` are its
instances.

Each field's premises are exactly the facts the endpoint's source walk
returns at its entry storage `s`: the runtime clock guard `¬ now < rho`, Jaune's
word-safety bundle for the elapsed exponent, the fresh-index equation and cap,
and the endpoint's own ledger guards.  None is an assumption about a post-state
or about the index being fresh.  The two conversion previews and the receive
leave storage unchanged, so they need no field; the child call inside `exit` is
transported by the generic `ContractSpec.ofStorageOnly_of_call`. -/
structure StepClosed (P : Stor → Prop) : Prop where
  /-- `drip()`: the accrual write of the fresh index and the block timestamp. -/
  drip : ∀ {s : Stor} {fresh now : B256} {elapsed : Nat},
    P s →
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

/-- Peeling a successful nonpayable exact-calldata wrapper transports the
precondition and memory well-formedness to the raw endpoint body. -/
private theorem nonpayable_exactCalldata_funcSound {P : Stor → Prop}
    (ca : Adr) {size : B256} {body : Func}
    (hbody : (ContractSpec.ofStorageOnly runtime P).FuncSound ca runtime.aux body) :
    (ContractSpec.ofStorageOnly runtime P).FuncSound ca runtime.aux
      (nonpayable (exactCalldata size body)) := by
  intro sevm s r hfork htarget hpre hwf hih hrun
  rcases of_run_nonpayable_exactCalldata hrun with
    ⟨mid, -, -, hstate, hmemory, -, -, hbodyRun⟩
  exact hbody hfork htarget (hpre.state_eq hstate.symm)
    (by rw [← hmemory]; exact hwf) hih hbodyRun

/-- Peeling a successful payable exact-calldata wrapper transports the same
entry facts to its raw endpoint. -/
private theorem exactCalldata_funcSound {P : Stor → Prop}
    (ca : Adr) {size : B256} {body : Func}
    (hbody : (ContractSpec.ofStorageOnly runtime P).FuncSound ca runtime.aux body) :
    (ContractSpec.ofStorageOnly runtime P).FuncSound ca runtime.aux
      (exactCalldata size body) := by
  intro sevm s r hfork htarget hpre hwf hih hrun
  rcases of_run_exactCalldata hrun with
    ⟨mid, -, hstate, hmemory, -, -, hbodyRun⟩
  exact hbody hfork htarget (hpre.state_eq hstate.symm)
    (by rw [← hmemory]; exact hwf) hih hbodyRun

/-- The raw `drip()` body preserves a step-closed storage predicate from an
arbitrary well-formed entry memory. -/
private theorem drip_funcSound {P : Stor → Prop} (hP : StepClosed P) (ca : Adr) :
    (ContractSpec.ofStorageOnly runtime P).FuncSound ca runtime.aux drip := by
  intro sevm s r _ htarget hpre hwf _ hrun
  subst ca
  have hinv : P (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases of_run_drip auxLookup_runtime frame nil_pref hrun with
    ⟨-, -, hclock, -, hguards, hnof, hcap, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [hstor]
  exact hP.drip hinv hclock hguards hnof rfl hcap

/-- A raw payable `join()` hands its guards, fresh-index and ledger facts to the
predicate's `join` obligation. -/
private theorem join_funcSound {P : Stor → Prop} (hP : StepClosed P) (ca : Adr) :
    (ContractSpec.ofStorageOnly runtime P).FuncSound ca runtime.aux join := by
  intro sevm s r _ htarget hpre hwf _ hrun
  subst ca
  have hinv : P (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases of_run_join_full auxLookup_runtime frame nil_pref hrun with
    ⟨hasset, -, -, -, -, hclock, -, hguards, hnof, hcap,
      fresh, units, hfresh, hunits, hrowCap, htotalCap, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [hstor]
  exact hP.join hinv hclock hguards hnof hfresh (by rw [hfresh]; exact hcap)
    hasset hunits hrowCap htotalCap

/-- The conversion previews leave any storage predicate unchanged. -/
private theorem convertToAssets_funcSound {P : Stor → Prop} (ca : Adr) :
    (ContractSpec.ofStorageOnly runtime P).FuncSound ca runtime.aux
      convertToAssets := by
  intro sevm s r _ htarget hpre hwf _ hrun
  subst ca
  have hinv : P (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases of_run_convertToAssets auxLookup_runtime frame nil_pref hrun with
    ⟨-, -, -, -, -, -, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [← congrFun hstor sevm.currentTarget]
  exact hinv

/-- The other conversion preview leaves any storage predicate unchanged. -/
private theorem convertToUnits_funcSound {P : Stor → Prop} (ca : Adr) :
    (ContractSpec.ofStorageOnly runtime P).FuncSound ca runtime.aux
      convertToUnits := by
  intro sevm s r _ htarget hpre hwf _ hrun
  subst ca
  have hinv : P (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases of_run_convertToUnits auxLookup_runtime frame nil_pref hrun with
    ⟨-, -, -, -, -, -, hstor, -⟩
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [← congrFun hstor sevm.currentTarget]
  exact hinv

/-- A successful raw `exit()` settles the debit before the real child call.
The predicate's `exit` obligation covers the settlement write; the storage-only
call adapter applies the retained deeper-frame hypothesis to that actual call;
final storage is then transported through the resumed parent. -/
private theorem exit_funcSound {P : Stor → Prop} (hP : StepClosed P) (ca : Adr) :
    (ContractSpec.ofStorageOnly runtime P).FuncSound ca runtime.aux exit := by
  intro sevm s r hfork htarget hpre hwf hih hrun
  subst ca
  have hinv : P (Devm.getStor s sevm.currentTarget) :=
    hpre.inv.1 rfl
  let image := s.memory.data.toList
  have hreads : Mem.Reads s.memory image := by
    intro i
    simp [image]
  let frame : Frame image s s := ⟨hwf, hreads, rfl, rfl⟩
  rcases exit_pays_exactly_full auxLookup_runtime frame nil_pref hrun hfork with
    ⟨-, -, -, hrowCover, htotalCover, -, -, hclock, -, hguards, hnof, hcap,
      callPre, callPost, guardPost, returnPre, hstorCallPre, hcodeCallPre,
      -, haccepted, hstorFinal, -, -⟩
  have hsettled : P (Devm.getStor callPre sevm.currentTarget) := by
    rw [hstorCallPre]
    exact hP.exit hinv hclock hguards hnof rfl hcap hrowCover htotalCover
  unfold AcceptedPayout at haccepted
  rcases haccepted with
    ⟨gasWord, xs, parent, child, xl, delegated, nextAddress, code, avail, pc,
      hstack, hcall, _⟩
  have hcode :
      some (callPre.getCode sevm.currentTarget).toList = Prog.compile runtime := by
    rw [hcodeCallPre]
    exact hpre.code
  have hchild : P (Devm.getStor callPost sevm.currentTarget) :=
    (ContractSpec.ofStorageOnly_of_call hih hfork hstack hcode hsettled hcall).1
  refine ⟨trivial, ?_⟩
  change P (Devm.getStor r sevm.currentTarget)
  rw [congrFun hstorFinal sevm.currentTarget]
  exact hchild

/-- **The one DRIP dispatcher.**  Every successful DRIP source run preserves
any step-closed storage predicate.  The actual top-level branch is classified
before a raw endpoint proof is selected, so the receive and each frozen wrapper
retain their distinct runtime evidence. -/
theorem sound_of_stepClosed {P : Stor → Prop} (hP : StepClosed P) (ca : Adr) :
    (ContractSpec.ofStorageOnly runtime P).Sound ca := by
  intro sevm pre post hfork hrun hca ih hwf hpre
  have hih : Exec.InvDepth sevm.depth ca (ContractSpec.ofStorageOnly runtime P).prog
      ((ContractSpec.ofStorageOnly runtime P).PreWf ca)
      ((ContractSpec.ofStorageOnly runtime P).Post ca) := by
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
      exact (nonpayable_exactCalldata_funcSound ca (convertToAssets_funcSound ca))
        hfork hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := nonpayable (exactCalldata 36 exit))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact (nonpayable_exactCalldata_funcSound ca (exit_funcSound hP ca))
        hfork hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := nonpayable (exactCalldata 36 convertToUnits))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact (nonpayable_exactCalldata_funcSound ca (convertToUnits_funcSound ca))
        hfork hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := nonpayable (exactCalldata 4 drip))
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact (nonpayable_exactCalldata_funcSound ca (drip_funcSound hP ca))
        hfork hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody
    · rcases main_body (f := exactCalldata 4 join)
        hmain hempty hselector (by simp [funcs]) with
        ⟨mid, hstate, hmemory, -, -, hbody⟩
      exact (exactCalldata_funcSound ca (join_funcSound hP ca))
        hfork hca (hpreEntry.state_eq hstate.symm)
        (by rw [← hmemory]; exact hwfEntry) hih hbody

/-- `AccountingInv` is step-closed: the accrual write, the join mint and the
exit burn each preserve full-address accounting. -/
theorem accountingInv_stepClosed : StepClosed AccountingInv where
  drip := by
    intro s fresh now elapsed h _ hguards hnof hfresh hcap
    subst hfresh
    exact h.drip_write (h.fresh_lower elapsed hguards hnof)
      (B256.toNat_le_toNat (le_of_not_gt hcap))
  join := by
    intro s holder value fresh units now elapsed h _ hguards hnof hfresh hcap
      hasset hunits hrowCap htotalCap
    exact h.join_write_of_effect hasset hguards hnof hcap hfresh hunits
      hrowCap htotalCap
  exit := by
    intro s holder fresh units now elapsed h _ hguards hnof hfresh hcap
      hrowCover htotalCover
    subst hfresh
    have haccrued : AccountingInv
        ((s.set chiSlot ((B256.rpow scale half rate elapsed * s.get chiSlot) /
          scale)).set rhoSlot now) :=
      h.drip_write (h.fresh_lower elapsed hguards hnof)
        (B256.toNat_le_toNat (le_of_not_gt hcap))
    have hrow :
        ((s.set chiSlot ((B256.rpow scale half rate elapsed * s.get chiSlot) /
          scale)).set rhoSlot now).get (pieSlot holder) = s.get (pieSlot holder) := by
      rw [Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder).symm _,
        Stor.get_set_ne _ (pieSlot_ne_chiSlot holder).symm _]
    have htotal :
        ((s.set chiSlot ((B256.rpow scale half rate elapsed * s.get chiSlot) /
          scale)).set rhoSlot now).get totalUnitsSlot = s.get totalUnitsSlot := by
      rw [Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
        Stor.get_set_ne _ scalarSlots_distinct.2.1 _]
    have hsettled := haccrued.exit_ledger_write (holder := holder) (units := units)
      (by rw [hrow]; exact le_of_not_gt hrowCover)
      (by rw [htotal]; exact le_of_not_gt htotalCover)
    rw [hrow, htotal] at hsettled
    exact hsettled

/-- Every successful DRIP source run preserves `AccountingInv`.  The actual
top-level branch is classified before a raw endpoint proof is selected, so
the receive and each frozen wrapper retain their distinct runtime evidence. -/
theorem dripSpec_sound (ca : Adr) : dripSpec.Sound ca :=
  sound_of_stepClosed accountingInv_stepClosed ca

/-- The frame-level preservation form consumed by the retained execution
ladder. -/
theorem dripSpec_preserves (ca : Adr) : dripSpec.Preserves ca :=
  dripSpec.preserves_inv ca (dripSpec_sound ca)

end Drip

end Blanc
