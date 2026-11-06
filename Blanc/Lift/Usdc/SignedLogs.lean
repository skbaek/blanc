import Blanc.Lift.Usdc.EntryLawV22
import Blanc.Lift.Usdc.EntryChainSettled
import Blanc.Lift.CurveCoins.ApprovalLogsUsdcV2
import Blanc.Lift.CurveCoins.ApprovalLogsUsdcV2_1
import Blanc.Lift.CurveCoins.PremisesOfLogs

/-!
# USDC's `noSignature` from receipt logs

Each of `SignedAs`'s nine selectors, at a committed frame of each version, either has no route through the dispatcher, so
reverts, or logs: the three moves' forms log `AuthorizationUsed` with `from`, and `permit`'s forms and the three
`*AllowanceWithAuthorization` log `Approval` with the owner. `SignedLogged` collects both; `usdc_signed_logged` lifts it to the
proxy frame; `usdc_noSignature_of_receipts` turns it to what a reader's two log filters say. What a signature recovers is not
read.

| selector | V2 | V2_1 | V2_2 |
|---|---|---|---|
| `permit(…, v, r, s)` | `Approval` | `Approval` | `Approval` |
| `permit(…, bytes)` | absent | absent | `Approval` |
| `approve…`, `increase…`, `decreaseAllowanceWithAuthorization` | `Approval` | absent | absent |
| `transferWithAuthorization(…, v, r, s)` | `AuthorizationUsed` | same | same |
| `transferWithAuthorization(…, bytes)` | absent | absent | `AuthorizationUsed` |
| `receiveWithAuthorization(…, v, r, s)` | absent | `AuthorizationUsed` | same |
| `receiveWithAuthorization(…, bytes)` | absent | absent | `AuthorizationUsed` |
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- A state holding `AuthorizationUsed` or `Approval` of the frame's own coin, naming `a`. -/
def SignedLogged (sevm : Sevm) (d : Devm) (a : Adr) : Prop :=
  AuthLogged sevm d a ∨ ApprovalLogged sevm d a

/-- A selector with no route through the dispatcher of a word version does not commit. -/
macro "uabsent " run:ident s:ident : tactic => `(tactic|
  (have h := SFunc.Run.cut $run
   clear $run
   uhead h $s
   repeat ustep h
   exact (SFunc.RunCutP.false_of_noOk h (by decide)).elim))

/-- **FiatTokenV2.** -/
theorem v2_signed_logged {G : Exec.Frame} (pc : G.pc = 0) (hcode : G.sevm.code = ImplV2.code)
    (fork : HistFork G.sevm.benvStat.fork) (wf : Mem.Wf G.pre.memory)
    (sel : Blanc.Sevm.selector G.sevm ∈ signedSelectors) :
    SignedLogged G.sevm G.post (Sevm.dataWord G.sevm 4).toAdr := by
  have run := run_of_frame ImplV2.cert_check rfl pc hcode fork.stateGas_none
  simp only [signedSelectors, List.mem_cons, List.not_mem_nil, or_false] at sel
  rcases sel with s | s | s | s | s | s | s | s | s
  · exact .inr (CurveCoins.UsdcV2.frame_permit_logs fork s run)
  · uabsent run s
  · exact .inr (CurveCoins.UsdcV2.frame_approveWithAuthorization_logs fork s run)
  · exact .inr (CurveCoins.UsdcV2.frame_increaseAllowanceWithAuthorization_logs fork s run)
  · exact .inr (CurveCoins.UsdcV2.frame_decreaseAllowanceWithAuthorization_logs fork s run)
  · exact .inl (ImplV2.frame_twa_logged fork wf s run).2
  · uabsent run s
  · uabsent run s
  · uabsent run s

/-- **FiatTokenV2_1.** -/
theorem v2_1_signed_logged {G : Exec.Frame} (pc : G.pc = 0) (hcode : G.sevm.code = ImplV2_1.code)
    (fork : HistFork G.sevm.benvStat.fork) (wf : Mem.Wf G.pre.memory)
    (sel : Blanc.Sevm.selector G.sevm ∈ signedSelectors) :
    SignedLogged G.sevm G.post (Sevm.dataWord G.sevm 4).toAdr := by
  have run := run_of_frame ImplV2_1.cert_check rfl pc hcode fork.stateGas_none
  simp only [signedSelectors, List.mem_cons, List.not_mem_nil, or_false] at sel
  rcases sel with s | s | s | s | s | s | s | s | s
  · exact .inr (CurveCoins.UsdcV2_1.frame_permit_logs fork s run)
  · uabsent run s
  · uabsent run s
  · uabsent run s
  · uabsent run s
  · exact .inl (ImplV2_1.frame_twa_logged fork wf s run).2
  · uabsent run s
  · exact .inl (ImplV2_1.frame_rwa_logged fork wf s run).2
  · uabsent run s

/-- V2_2's dispatcher has no route for this selector. -/
macro "uabsent22 " run:ident s:ident : tactic => `(tactic|
  (have h := SFunc.Run.cut $run
   clear $run
   repeat istep h
   ibranch h c1
   repeat istep h
   ibranch h c2
   iterate 4 istep h
   rw [selector_word, $s:ident] at h
   repeat idisp h
   repeat ustep h
   exact (SFunc.RunCutP.false_of_noOk h (by decide)).elim))

/-- **FiatTokenV2_2.** -/
theorem v22_signed_logged {G : Exec.Frame} (pc : G.pc = 0) (hcode : G.sevm.code = Impl.code)
    (fork : HistFork G.sevm.benvStat.fork) (lib : G.pre.getCode usdcLib = Lib.code)
    (sel : Blanc.Sevm.selector G.sevm ∈ signedSelectors) :
    SignedLogged G.sevm G.post (Sevm.dataWord G.sevm 4).toAdr := by
  have frun := run_of_frame Impl.cert_check rfl pc hcode fork.stateGas_none
  simp only [signedSelectors, List.mem_cons, List.not_mem_nil, or_false] at sel
  obtain ⟨fpc, sevm, pre, out, run, committed⟩ := G
  dsimp only at pc hcode fork lib sel frun ⊢
  subst pc
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    rcases sel with s | s | s | s | s | s | s | s | s
    · exact .inr (frame_permitVrs fork lib s frun).2.2.2.2
    · exact .inr (frame_permitBytes fork lib s frun).2.2.2.2
    · uabsent22 frun s
    · uabsent22 frun s
    · uabsent22 frun s
    · exact .inl (frame_twa_vrs run hcode fork lib s).2
    · exact .inl (frame_twa_bytes run hcode fork lib s).2
    · exact .inl (frame_rwa_vrs run hcode fork lib s).2.2
    · exact .inl (frame_rwa_bytes run hcode fork lib s).2.2

/-- **A committed non-admin proxy frame whose message claims `h`'s signature logs a filter's hit naming `h`**, whichever
version the implementation word finds. -/
theorem usdc_signed_logged {T h : Adr} {F : Exec.Frame} (pc : F.pc = 0) (hcode : F.sevm.code = Proxy.code)
    (fork : HistFork F.sevm.benvStat.fork) (target : F.sevm.currentTarget = T)
    (hasCode : (F.pre.getCode T).toList ≠ []) (notAdmin : F.sevm.caller ≠ adminOf F.pre.state T)
    (certified : UsdcCertified F.pre T) (hsize : F.sevm.data.length < 2 ^ 256) (signed : SignedAs h F.sevm) :
    SignedLogged F.sevm F.post h := by
  obtain ⟨sel, named⟩ := signed
  obtain ⟨version, lib, np⟩ := certified
  obtain ⟨fpc, sevm, pre, out, run, committed⟩ := F
  dsimp only at pc hcode fork target hasCode notAdmin sel named version lib np hsize ⊢
  subst pc
  subst target
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    obtain ⟨G, child⟩ := proxy_entry_child run hcode fork.stateGas_none fork.bal_none hasCode notAdmin
      (CurveCoins.UsdcVersion.not_delegation version) (np sevm.benvStat.fork) hsize
    have same : SameMessage ⟨0, sevm, pre, .ok post, run, committed⟩ G := ⟨child.caller, child.data⟩
    have forkG : HistFork G.sevm.benvStat.fork := by rw [child.stat]; exact fork
    have selG : Blanc.Sevm.selector G.sevm ∈ signedSelectors := by rw [same.sel]; exact sel
    have word : (Sevm.dataWord G.sevm 4).toAdr = (Sevm.dataWord sevm 4).toAdr := by rw [same.word]
    have base : SignedLogged G.sevm G.post (Sevm.dataWord G.sevm 4).toAdr := by
      rcases version with c | c | c
      · exact v2_signed_logged child.pc (child.code.trans c) forkG child.wf selG
      · exact v2_1_signed_logged child.pc (child.code.trans c) forkG child.wf selG
      · exact v22_signed_logged child.pc (child.code.trans c) forkG
          ((child.codeLib usdcLib (by rw [lib c]; exact lib_toList_ne_nil)).trans (lib c)) selG
    rw [word, named] at base
    rcases base with ⟨l, m, a, t⟩ | ⟨l, m, a, t⟩
    · exact .inl ⟨l, child.logs l m, a.trans child.target, t⟩
    · exact .inr ⟨l, child.logs l m, a.trans child.target, t⟩

/-- What a reader's filter for `AuthorizationUsed` at `T` matches, with authorizer `h`. -/
def AuthorizationUsedLog (T h : Adr) (l : Log) : Prop :=
  l.address = T ∧ l.topics.take 2 = [0x98de503528ee59b575ef0c0a2576a82497bfc029a5685b209e9ec333479b10a5, h.toB256]

variable {T h : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}

/-- **USDC's `noSignature` from no `AuthorizationUsed(h, _)` and no `Approval(h, _)` receipt log**: no settled proxy frame
at `T` with a non-admin caller is a message claiming `h`'s signature. The proxy admin's power is `certified`; receipts do not
speak for system stages, hence `sysNe`. -/
theorem usdc_noSignature_of_receipts (trace : MidHistoryTraceIn HistFork cfg start future)
    (capabilities : BodyStageCapabilities HistFork) (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames)
    (auth : trace.NoLogInReceipts (AuthorizationUsedLog T h))
    (approval : trace.NoLogInReceipts (CurveCoins.ApprovalLog T h))
    (sysNe : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ T) :
    ∀ F ∈ coinFrames T (EntryObs T) trace.settledFrames, ¬ SignedAs h F.sevm := by
  intro F hF signed
  obtain ⟨member, target, stat, obs⟩ := mem_coinFrames.mp hF
  have notRescue : Blanc.Sevm.selector F.sevm ≠ rescueSelector := fun e => by
    have := signed.1
    rw [e] at this
    exact absurd this (by decide)
  obtain ⟨pc, code, fork, has⟩ := (usdc_viewChain_certified trace capabilities installed certified).1.good F
    (mem_coinFrames.mpr ⟨member, target, stat, obs, notRescue⟩)
  rcases usdc_signed_logged pc code fork target has obs.2 (certified F member target obs.1 obs.2)
    (settled_data_bound trace capabilities F member) signed with ⟨l, m, a, t⟩ | ⟨l, m, a, t⟩
  · exact trace.no_log_at HistFork.stateGas_none _ auth sysNe F member target l m ⟨a.trans target, t⟩
  · exact trace.no_log_at HistFork.stateGas_none _ approval sysNe F member target l m ⟨a.trans target, t⟩

/-- The same, at the chain's links. -/
theorem usdc_noSignature_chain (trace : MidHistoryTraceIn HistFork cfg start future)
    (capabilities : BodyStageCapabilities HistFork) (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames)
    (auth : trace.NoLogInReceipts (AuthorizationUsedLog T h))
    (approval : trace.NoLogInReceipts (CurveCoins.ApprovalLog T h))
    (sysNe : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ T) :
    ∀ F ∈ coinFrames T (ChainObs T) trace.settledFrames, ¬ SignedAs h F.sevm := fun F hF => by
  obtain ⟨member, target, stat, obs⟩ := mem_coinFrames.mp hF
  exact usdc_noSignature_of_receipts trace capabilities installed certified auth approval sysNe F
    (mem_coinFrames.mpr ⟨member, target, stat, obs.1⟩)

end Blanc.Lift.Usdc
