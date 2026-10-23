import Blanc.ExecutionDeletionSafety
import Blanc.ExecutionDirectCode
import Blanc.ExecutionOccurrence
import Blanc.ExecutionNoninterference
import Blanc.Lift.CallRestriction

/-!
# Producing raw terminal safety from an installed checked runtime

`Exec.inv_noDel_of_raw_terminal_safe` (`Blanc/ExecutionDeletionSafety.lean`) needs decoded
SELFDESTRUCT exclusion at every reached raw node whose storage context is the protected account
`wa`. This module produces that certificate from actual facts only: the protected account's
installed code `C` (nonempty, no EIP-7702 designator) is checked by a certificate `c` that has no
SELFDESTRUCT terminal (`Cert.noSelfdestruct`) and spawns only by `CALL`/`STATICCALL`
(`Cert.callOnly`), with selected state-gas absence and no fork premise.

The cross-frame argument (`Exec.protectedDescendants`) is an all-outcome induction over the raw
frame tree: every entered frame owning `wa`'s storage starts at pc `0` and runs `C`. Such a frame
arises from

* a `CALL`/`STATICCALL` by an owner-`wa` frame (the only spawns its certificate admits), whose
  child at `wa` runs `wa`'s own code;
* any spawn by a frame at another account, whose child at `wa` runs `wa`'s own code
  (`Evm.step_spawn_child`: a `DELEGATECALL`/`CALLCODE` keeps the caller's account, and
  `CREATE`/`CREATE2` cannot enter an account with code);

and `wa`'s code stays `C` along every reached node (`Exec.Deriv.ParentStep.codePreserve`,
`Evm.step_spawn_child`). Each owner-`wa` node then lies on a same-frame prefix of such a frame,
where the certificate cursor excludes SELFDESTRUCT.
-/

namespace Blanc

open Jaune

/-- A node owning `wa`'s storage lies on a same-frame prefix of a frame entered at pc `0` of `C`. -/
private def ProtectedAt (C : ByteArray) (wa : Adr) (n : Exec.Deriv) : Prop :=
  n.sevm.currentTarget = wa →
    ∃ R : Exec.Deriv, R.pc = 0 ∧ R.sevm.code = C ∧ Exec.Deriv.ParentPrefix R n

private theorem ne_empty_of_toList_ne_nil {C : ByteArray} (h : C.toList ≠ []) :
    C ≠ .empty := by
  rintro rfl
  exact h ByteArray.toList_empty

/-- Every raw descendant frame root starts at pc `0` with state-gas absence and `wa` holding `C`,
and runs `C` when it owns `wa`'s storage. -/
private theorem Exec.protectedDescendants {wa : Adr} {C : ByteArray} {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      sevm.benvStat.rules.stateGas = none →
      pre.getCode wa = C →
      ProtectedAt C wa ⟨pc, sevm, pre, out, run⟩ →
      ∀ G ∈ Exec.rawFrameDescendants run,
        G.pc = 0 ∧ G.sevm.benvStat.rules.stateGas = none ∧ G.devm.getCode wa = C ∧
          (G.sevm.currentTarget = wa → G.sevm.code = C) := by
  have hCempty := ne_empty_of_toList_ne_nil hCne
  -- The entered child's root facts.
  have childRoot : ∀ {pc pc' : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {f : Frame}
      {rsm : Resume} {cevm : Evm}, Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc' →
      f.enter = .run cevm →
      sevm.benvStat.rules.stateGas = none → pre.getCode wa = C →
      (sevm.currentTarget = wa →
        ∃ R : Exec.Deriv, R.pc = 0 ∧ R.sevm.code = C ∧
          ∃ run : Exec pc sevm pre out, Exec.Deriv.ParentPrefix R ⟨pc, sevm, pre, out, run⟩) →
      cevm.pc = 0 ∧ cevm.sta.benvStat.rules.stateGas = none ∧ cevm.dyna.getCode wa = C ∧
        (cevm.sta.currentTarget = wa → cevm.sta.code = C) := by
    intro pc pc' sevm pre out f rsm cevm hstep henter hsg hP prot
    obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hstep henter
    refine ⟨hpc0, by rw [Evm.step_spawn_child_benvStat hstep henter]; exact hsg,
      by rw [hgc]; exact hP, fun htgt => ?_⟩
    by_cases hparent : sevm.currentTarget = wa
    · obtain ⟨R, hRpc, hRcode, run, chain⟩ := prot hparent
      obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv hstep
      have hRsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
      have hkind : x = .call ∨ x = .staticcall :=
        Lift.call_or_staticcall_of_parentPrefix_noStateGas hc callOnly hRpc hRcode
          (by rw [← hRsevm]; exact hsg) chain hat
      rw [Frame.enter_run_currentTarget henter] at htgt
      rw [Frame.enter_run_code henter,
        Xinst.step_directCall_spawn_code hkind hx (by rw [htgt, hP]; exact hCdel), htgt, hP]
    · rw [hsrc (by rw [htgt]; exact hparent) (by rw [htgt, hP]; exact hCempty)
        (by rw [htgt, hP]; exact hCdel), htgt, hP]
  intro pc sevm pre out run
  induction run with
  | halt => intro _ _ _ G hG; simp only [Exec.rawFrameDescendants, List.not_mem_nil] at hG
  | doneErr => intro _ _ _ G hG; simp only [Exec.rawFrameDescendants, List.not_mem_nil] at hG
  | cont hstep next ih =>
      intro hsg hP prot G hG
      simp only [Exec.rawFrameDescendants] at hG
      have edge := Exec.Deriv.ParentStep.cont hstep next
      refine ih hsg ?_ ?_ G hG
      · rw [Exec.Deriv.ParentStep.codePreserve edge wa (by rw [hP]; exact hCne)]; exact hP
      · intro htgt
        obtain ⟨R, hRpc, hRcode, chain⟩ := prot htgt
        exact ⟨R, hRpc, hRcode, chain.snoc edge⟩
  | doneOk hstep henter hresume next ih =>
      intro hsg hP prot G hG
      simp only [Exec.rawFrameDescendants] at hG
      have edge := Exec.Deriv.ParentStep.doneOk hstep henter hresume next
      refine ih hsg ?_ ?_ G hG
      · rw [Exec.Deriv.ParentStep.codePreserve edge wa (by rw [hP]; exact hCne)]; exact hP
      · intro htgt
        obtain ⟨R, hRpc, hRcode, chain⟩ := prot htgt
        exact ⟨R, hRpc, hRcode, chain.snoc edge⟩
  | runErr hstep henter child hresume ih =>
      intro hsg hP prot G hG
      have root := childRoot hstep henter hsg hP
        (fun h => (prot h).imp fun R hR => ⟨hR.1, hR.2.1, _, hR.2.2⟩)
      simp only [Exec.rawFrameDescendants, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact root
      · refine ih root.2.1 root.2.2.1 (fun htgt => ⟨_, root.1, root.2.2.2 htgt, .refl _⟩) G hG
  | runOk hstep henter child hresume next childIh nextIh =>
      intro hsg hP prot G hG
      have root := childRoot hstep henter hsg hP
        (fun h => (prot h).imp fun R hR => ⟨hR.1, hR.2.1, _, hR.2.2⟩)
      have edge := Exec.Deriv.ParentStep.runOk hstep henter child hresume next
      simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at hG
      rcases hG with rfl | hG | hG
      · exact root
      · exact childIh root.2.1 root.2.2.1
          (fun htgt => ⟨_, root.1, root.2.2.2 htgt, .refl _⟩) G hG
      · refine nextIh hsg ?_ ?_ G hG
        · rw [Exec.Deriv.ParentStep.codePreserve edge wa (by rw [hP]; exact hCne)]; exact hP
        · intro htgt
          obtain ⟨R, hRpc, hRcode, chain⟩ := prot htgt
          exact ⟨R, hRpc, hRcode, chain.snoc edge⟩

/-- **Raw terminal safety from an installed checked runtime.** If `wa` holds a nonempty,
undesignated code `C` checked by a certificate without SELFDESTRUCT terminals that spawns only by
`CALL`/`STATICCALL`, then under state-gas absence every reached raw node owning `wa`'s storage
excludes decoded SELFDESTRUCT, provided the root, when it owns `wa`'s storage, enters `C` at pc
`0`. Every outcome is covered; no fork, success, routing or deletion premise is used. -/
theorem Exec.safe_of_installedCert {wa : Adr} {C : ByteArray} {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (installed : pre.getCode wa = C) (hCne : C.toList ≠ [])
    (root : sevm.currentTarget = wa → pc = 0 ∧ sevm.code = C) :
    ∀ node ∈ Exec.rawNodes run, node.sevm.currentTarget = wa →
      ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
  intro node hnode htgt
  obtain ⟨F, hF, chain⟩ := (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run node).mp hnode
  have hsevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [hsevm] at htgt
  have entry : F.pc = 0 ∧ F.sevm.benvStat.rules.stateGas = none ∧ F.sevm.code = C := by
    simp only [Exec.rawFrameRoots, List.mem_cons] at hF
    rcases hF with rfl | hF
    · exact ⟨(root htgt).1, hsg, (root htgt).2⟩
    · obtain ⟨hpc0, hsgF, -, hcode⟩ :=
        Exec.protectedDescendants hc callOnly hCne hCdel run hsg installed
          (fun h => ⟨_, (root h).1, (root h).2, .refl _⟩) F hF
      exact ⟨hpc0, hsgF, hcode htgt⟩
  exact Lift.not_selfdestruct_of_parentPrefix_noStateGas hc noSelfdestruct entry.1 entry.2.2
    entry.2.1 chain

/-- **No-deletion of a protected account holding an installed checked runtime**, for every
outcome of a complete execution under state-gas absence, from the input `Devm.NoDel`. The `safe`
premise of `Exec.inv_noDel_of_raw_terminal_safe` is produced by `Exec.safe_of_installedCert`. -/
theorem Exec.inv_noDel_of_installedCert {wa : Adr} {C : ByteArray} {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (installed : pre.getCode wa = C)
    (root : sevm.currentTarget = wa → pc = 0 ∧ sevm.code = C)
    (initial : Devm.NoDel wa pre) : Execution.NoDel wa out :=
  Exec.inv_noDel_of_raw_terminal_safe run hsg
    (Exec.safe_of_installedCert hc callOnly noSelfdestruct hCdel run hsg installed
      (installed ▸ initial.code) root)
    initial

end Blanc
