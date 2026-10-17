import Blanc.Lift.Usdc.RefineAdminRun
import Blanc.Lift.Usdc.RefineAdminReach
import Blanc.Lift.Usdc.RefineAdminLedger
import Blanc.Lift.Usdc.RefineShape
import Blanc.Lift.Usdc.Families
import Blanc.Lift.Usdc.RefineTransferDecode
import Blanc.Lift.Sound

/-!
# U6f: the refinement law of USDC's admin family

`implStepLaw_famAdmin : ImplStepLaw famAdmin` — a successful non-static implementation frame whose
message decodes to `mint`, `burn`, `configureMinter`, `removeMinter`, `updateMasterMinter`, `pause`,
`unpause`, `updatePauser`, `updateBlacklister`, `updateRescuer`, `transferOwnership`, `blacklist` or
`unBlacklist` commits the book's step, keeps the proxy's two slots and decodes no external
instruction.  Assembled from the decoded call (`decode_*`), the lifted run (`impl_lifted`), the
certificate walks (`*_run`, `reach_*`) and the ledger readings (`*_out`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.Impl

/-! ## Reading the decoded admin calls -/

theorem decode_pause {e : Sevm} (h : decodeCall e = some .pause) :
    Blanc.Sevm.selector e = 0x8456cb59 := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact hsel.symm

theorem decode_unpause {e : Sevm} (h : decodeCall e = some .unpause) :
    Blanc.Sevm.selector e = 0x3f4ba83a := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact hsel.symm

theorem decode_updatePauser {e : Sevm} {a : _} (h : decodeCall e = some (.updatePauser a)) :
    Blanc.Sevm.selector e = 0x554bab3c ∧ a = (Sevm.dataWord e 4).toAdr := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.updatePauser.inj hread).symm⟩

theorem decode_updateMasterMinter {e : Sevm} {a : _} (h : decodeCall e = some (.updateMasterMinter a)) :
    Blanc.Sevm.selector e = 0xaa20e1e4 ∧ a = (Sevm.dataWord e 4).toAdr := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.updateMasterMinter.inj hread).symm⟩

theorem decode_updateBlacklister {e : Sevm} {a : _} (h : decodeCall e = some (.updateBlacklister a)) :
    Blanc.Sevm.selector e = 0xad38bf22 ∧ a = (Sevm.dataWord e 4).toAdr := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.updateBlacklister.inj hread).symm⟩

theorem decode_updateRescuer {e : Sevm} {a : _} (h : decodeCall e = some (.updateRescuer a)) :
    Blanc.Sevm.selector e = 0x2ab60045 ∧ a = (Sevm.dataWord e 4).toAdr := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.updateRescuer.inj hread).symm⟩

theorem decode_transferOwnership {e : Sevm} {a : _} (h : decodeCall e = some (.transferOwnership a)) :
    Blanc.Sevm.selector e = 0xf2fde38b ∧ a = (Sevm.dataWord e 4).toAdr := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.transferOwnership.inj hread).symm⟩

theorem decode_removeMinter {e : Sevm} {a : _} (h : decodeCall e = some (.removeMinter a)) :
    Blanc.Sevm.selector e = 0x3092afd5 ∧ a = (Sevm.dataWord e 4).toAdr := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.removeMinter.inj hread).symm⟩

theorem decode_configureMinter {e : Sevm} {a v : _} (h : decodeCall e = some (.configureMinter a v)) :
    Blanc.Sevm.selector e = 0x4e44d956 ∧ a = (Sevm.dataWord e 4).toAdr ∧ v = (Sevm.dataWord e 36).toNat := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.configureMinter.inj hread).1.symm, (Call.configureMinter.inj hread).2.symm⟩

theorem decode_unBlacklist {e : Sevm} {a : _} (h : decodeCall e = some (.unBlacklist a)) :
    Blanc.Sevm.selector e = 0x1a895266 ∧ a = (Sevm.dataWord e 4).toAdr := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.unBlacklist.inj hread).symm⟩

theorem decode_blacklist {e : Sevm} {a : _} (h : decodeCall e = some (.blacklist a)) :
    Blanc.Sevm.selector e = 0xf9f92be4 ∧ a = (Sevm.dataWord e 4).toAdr := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.blacklist.inj hread).symm⟩

theorem decode_mint {e : Sevm} {a v : _} (h : decodeCall e = some (.mint a v)) :
    Blanc.Sevm.selector e = 0x40c10f19 ∧ a = (Sevm.dataWord e 4).toAdr ∧ v = (Sevm.dataWord e 36).toNat := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.mint.inj hread).1.symm, (Call.mint.inj hread).2.symm⟩

theorem decode_burn {e : Sevm} {v : _} (h : decodeCall e = some (.burn v)) :
    Blanc.Sevm.selector e = 0x42966c68 ∧ v = (Sevm.dataWord e 4).toNat := by
  obtain ⟨-, r, hr, hsel, hread⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Call.noConfusion hread | exact ⟨hsel.symm, (Call.burn.inj hread).symm⟩

open Classical in
/-- The book's step on a message from a caller other than the admin word is the decoded call's. -/
theorem book_step_of {P : Adr} {U : Key → Prop} {s : Stor} {e : Sevm} {c : Call}
    (notAdmin : e.caller ≠ (s.get adminSlot).toAdr) (dec : decodeCall e = some c) :
    (usdcBookS P).step (ledger U s) e = (ledger U s).step P e.caller c := by
  show (if e.caller = (ledger U s).admin then (if adminGetter e then some (ledger U s) else none)
    else match decodeCall e with
      | none => none
      | some c => (ledger U s).step P e.caller c) = _
  rw [ite_eq_right (show e.caller ≠ (ledger U s).admin from notAdmin), dec]

/-- An implementation frame whose selector reaches only exec-free code decodes no external
instruction along its own chain. -/
theorem impl_noExec {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (reach : ∀ {P : Sevm → Devm → Ninst → Devm → Prop}, (∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') →
      ∀ T : Conf, Reach P cert.prog sevm ⟨St pre pre.stack pre.memory pre.gasLeft, t_0000_c0, []⟩ T →
        AtExec T → False) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  intro N hp x hat
  obtain ⟨κ, hr, ok⟩ := reach_of_parentPrefix cert_check (R := ⟨0, sevm, pre, .ok post, run⟩) rfl codeEq fork hp
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hat
  have hr' : Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) cert.prog sevm
      ⟨St pre pre.stack pre.memory pre.gasLeft, t_0000_c0, []⟩ (κ.conf N.devm) := by
    rw [← St.self rfl rfl]
    exact hr
  exact reach StepIn.toRun _ hr' ⟨x, g, hf⟩

/-- The implementation frame's lifted run from entry `0`, over the walk state. -/
theorem impl_lifted {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) :
    SFunc.RunCut cert.prog sevm [] (St pre pre.stack pre.memory pre.gasLeft) t_0000_c0
      (.done (.halted post)) := by
  obtain ⟨f, hf, frun⟩ := lift_sound cert_check codeEq fork run
  obtain rfl : f = t_0000_c0 := Option.some.inj (hf.symm.trans rfl)
  rw [← St.self rfl rfl]
  exact SFunc.runP_iff_runCutP_nil.mp frun

/-- **U6f: the whole-frame step law of the admin family** (roles, minting, burning, pausing,
blacklisting).  Certificate-driven: the dispatcher sends the frame to the call's wrapper
(`RefineAdminDispatch.lean`), the wrapper's and body's walks give the guards it passed and its
writes (`RefineAdminRun.lean`), the writes read back as the model's step (`RefineAdminLedger.lean`);
no admin call reaches an external instruction (`RefineAdminReach.lean`), so the node clause holds
vacuously. -/
theorem implStepLaw_famAdmin : ImplStepLaw famAdmin := by
  intro P U sevm pre post run codeEq target codeAddr fork nonstatic inj apart keys libCode notAdmin c dec
    fam
  subst target
  have hrun := impl_lifted run codeEq fork
  have hk : ∀ k ∈ c.keys sevm.caller, U k := fun k hk => keys k (keys_sub_frameKeys dec k hk)
  suffices H : AdminOut sevm.currentTarget U (pre.state.getStor sevm.currentTarget)
      (post.state.getStor sevm.currentTarget) sevm.caller c ∧
      ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) by
    obtain ⟨⟨hstep, himpl, hadmin⟩, hno⟩ := H
    exact ⟨(book_step_of notAdmin dec).trans hstep, himpl, hadmin,
      fun N hp x hat => (hno N hp x hat).elim⟩
  cases c <;> simp only [famAdmin] at fam
  case pause  =>
    have hsel := decode_pause dec
    exact ⟨pause_out apart (pause_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_pause hP hsel r hT⟩
  case unpause  =>
    have hsel := decode_unpause dec
    exact ⟨unpause_out apart (unpause_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_unpause hP hsel r hT⟩
  case updatePauser a =>
    obtain ⟨hsel, rfl⟩ := decode_updatePauser dec
    exact ⟨updatePauser_out apart (updatePauser_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_updatePauser hP hsel r hT⟩
  case updateMasterMinter a =>
    obtain ⟨hsel, rfl⟩ := decode_updateMasterMinter dec
    exact ⟨updateMasterMinter_out apart (updateMasterMinter_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_updateMasterMinter hP hsel r hT⟩
  case updateBlacklister a =>
    obtain ⟨hsel, rfl⟩ := decode_updateBlacklister dec
    exact ⟨updateBlacklister_out apart (updateBlacklister_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_updateBlacklister hP hsel r hT⟩
  case updateRescuer a =>
    obtain ⟨hsel, rfl⟩ := decode_updateRescuer dec
    exact ⟨updateRescuer_out apart (updateRescuer_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_updateRescuer hP hsel r hT⟩
  case transferOwnership a =>
    obtain ⟨hsel, rfl⟩ := decode_transferOwnership dec
    exact ⟨transferOwnership_out apart (transferOwnership_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_transferOwnership hP hsel r hT⟩
  case removeMinter a =>
    obtain ⟨hsel, rfl⟩ := decode_removeMinter dec
    exact ⟨removeMinter_out inj apart (hk _ (by simp only [Call.keys, List.mem_cons, true_or])) (hk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])) (removeMinter_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_removeMinter hP hsel r hT⟩
  case configureMinter a v =>
    obtain ⟨hsel, rfl, rfl⟩ := decode_configureMinter dec
    exact ⟨configureMinter_out inj apart (hk _ (by simp only [Call.keys, List.mem_cons, true_or])) (hk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])) (configureMinter_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_configureMinter hP hsel r hT⟩
  case unBlacklist a =>
    obtain ⟨hsel, rfl⟩ := decode_unBlacklist dec
    exact ⟨unBlacklist_out inj apart (hk _ (by simp only [Call.keys, List.mem_cons, true_or])) (unBlacklist_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_unBlacklist hP hsel r hT⟩
  case blacklist a =>
    obtain ⟨hsel, rfl⟩ := decode_blacklist dec
    exact ⟨blacklist_out inj apart (hk _ (by simp only [Call.keys, List.mem_cons, true_or])) (blacklist_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_blacklist hP hsel r hT⟩
  case mint a v =>
    obtain ⟨hsel, rfl, rfl⟩ := decode_mint dec
    exact ⟨mint_out inj apart (hk _ (by simp only [Call.keys, List.mem_cons, true_or])) (hk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])) (hk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])) (hk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])) (mint_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_mint hP hsel r hT⟩
  case burn v =>
    obtain ⟨hsel, rfl⟩ := decode_burn dec
    exact ⟨burn_out inj apart (hk _ (by simp only [Call.keys, List.mem_cons, true_or])) (hk _ (by simp only [Call.keys, List.mem_cons, true_or, or_true])) (burn_run fork hsel hrun),
      impl_noExec run codeEq fork fun hP _ r hT => reach_burn hP hsel r hT⟩

end Blanc.Lift.Usdc
