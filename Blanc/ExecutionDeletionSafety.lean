import Blanc.LadderBase
import Jaune.ExecChronology

/-!
Raw-terminal-safe no-deletion ownership over Jaune's existing driver.

`Exec.inv_noDel_of_raw_terminal_safe` concludes `Execution.NoDel` for a
complete `Exec` derivation from the input `Devm.NoDel`, absence of state gas,
and a decoded terminal exclusion at every actual reached driver node in the
executing storage context. The certificate is indexed by the selected run's
own `Exec.rawNodes`, never by retained or committed nodes. The concrete
protected-runtime or routing producer of the `safe` certificate is separate
mandatory work, out of scope here.
-/

namespace Blanc

open Jaune

/-- One actual driver step preserves no-deletion under the current node's
decoded terminal exclusion and the selected slot's preservation obligation. -/
private theorem Exec.step_noDel_of_safe {wa : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {slot : Xlot} {out : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (h : Devm.NoDel wa pre)
    (safeNode : sevm.currentTarget = wa → ¬ Linst.At sevm.code pc .selfdestruct)
    (inv : Xlot.InvNoDel wa slot)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, pre⟩) slot out) :
    Execution.NoDel wa out := by
  rcases hgi : (Evm.getInst ⟨pc, sevm, pre⟩) with _ | i
  · rw [Evm.step_invOp hgi] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact h
  · cases i with
    | next n =>
      rw [Evm.step_next (n := n) hgi] at hrun
      exact Ninst.inv_noDel_noStateGas hsg inv hrun h
    | jump j =>
      rw [Evm.step_jump (j := j) hgi] at hrun
      obtain ⟨-, hcase⟩ := Step.run_ofJump hrun
      have hjr := Jinst.noDelCode_effect wa j (evm := ⟨pc, sevm, pre⟩)
        (out := j.run ⟨pc, sevm, pre⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;>
        rw [hje] at hjr <;> exact hjr h
    | last l =>
      rw [Evm.step_last (l := l) hgi] at hrun
      obtain ⟨-, rfl⟩ := hrun
      refine Linst.run_noDel_of_safe rfl h ?_
      by_cases heq : sevm.currentTarget = wa
      · refine Or.inr fun hcon => safeNode heq ?_
        subst hcon
        exact hgi
      · exact Or.inl heq

/-- Public step interface for terminal-safe no-deletion, with the actual
selected recursive child obligation kept explicit. -/
theorem Exec.noDel_step_of_safe {wa : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {slot : Xlot} {out : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (h : Devm.NoDel wa pre)
    (safeNode : sevm.currentTarget = wa → ¬ Linst.At sevm.code pc .selfdestruct)
    (inv : Xlot.InvNoDel wa slot)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, pre⟩) slot out) :
    Execution.NoDel wa out :=
  Exec.step_noDel_of_safe hsg h safeNode inv hrun

/-- Six-constructor induction over the driver tree. The motive carries the
state-gas absence, the run-indexed raw-node safety and the input no-deletion
as arguments, so each child induction hypothesis has exactly the conditional
`Xlot.InvNoDel` shape for its filled slot. -/
private theorem Exec.invNoDel_of_rawNodes {wa : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out) :
    sevm.benvStat.rules.stateGas = none →
    (∀ node ∈ Exec.rawNodes run,
      node.sevm.currentTarget = wa →
      ¬ Linst.At node.sevm.code node.pc .selfdestruct) →
    Devm.NoDel wa pre → Execution.NoDel wa out := by
  induction run with
  | halt hstep =>
    intro hsg safe h
    have safeNode := safe _ (Exec.mem_rawNodes_self _)
    exact Exec.step_noDel_of_safe (slot := .none) hsg h safeNode trivial
      (by rw [hstep]; exact ⟨rfl, rfl⟩)
  | cont hstep next ih =>
    intro hsg safe h
    have safeNode := safe _ (Exec.mem_rawNodes_self _)
    have hmid : Execution.NoDel wa _ :=
      Exec.step_noDel_of_safe (slot := .none) hsg h safeNode trivial
        (by rw [hstep]; exact ⟨rfl, rfl⟩)
    have safeT : ∀ node ∈ Exec.rawNodes next,
        node.sevm.currentTarget = wa →
        ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
      intro node hm
      exact safe node (by
        show node ∈ Exec.rawNodes (Exec.cont hstep next)
        simp only [Exec.rawNodes]
        exact List.mem_cons_of_mem _ hm)
    exact ih hsg safeT hmid
  | doneErr hstep henter hr =>
    intro hsg safe h
    have safeNode := safe _ (Exec.mem_rawNodes_self _)
    exact Exec.step_noDel_of_safe (slot := .none) hsg h safeNode trivial
      (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
  | doneOk hstep henter hr next ih =>
    intro hsg safe h
    have safeNode := safe _ (Exec.mem_rawNodes_self _)
    have hmid : Execution.NoDel wa _ :=
      Exec.step_noDel_of_safe (slot := .none) hsg h safeNode trivial
        (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
    have safeT : ∀ node ∈ Exec.rawNodes next,
        node.sevm.currentTarget = wa →
        ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
      intro node hm
      exact safe node (by
        show node ∈ Exec.rawNodes (Exec.doneOk hstep henter hr next)
        simp only [Exec.rawNodes]
        exact List.mem_cons_of_mem _ hm)
    exact ih hsg safeT hmid
  | runErr hstep henter child hr ihc =>
    intro hsg safe h
    have safeNode := safe _ (Exec.mem_rawNodes_self _)
    have hbenv := Evm.step_spawn_child_benvStat hstep henter
    have hsgC := hbenv.symm ▸ hsg
    have safeC : ∀ node ∈ Exec.rawNodes child,
        node.sevm.currentTarget = wa →
        ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
      intro node hm
      exact safe node (by
        show node ∈ Exec.rawNodes (Exec.runErr hstep henter child hr)
        simp only [Exec.rawNodes]
        exact List.mem_cons_of_mem _ hm)
    exact Exec.step_noDel_of_safe (slot := .some ⟨_, _⟩) hsg h safeNode
      (fun hnd => ihc hsgC safeC hnd)
      (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
  | runOk hstep henter child hr next ihc ih =>
    intro hsg safe h
    have safeNode := safe _ (Exec.mem_rawNodes_self _)
    have hbenv := Evm.step_spawn_child_benvStat hstep henter
    have hsgC := hbenv.symm ▸ hsg
    have safeC : ∀ node ∈ Exec.rawNodes child,
        node.sevm.currentTarget = wa →
        ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
      intro node hm
      exact safe node (by
        show node ∈ Exec.rawNodes (Exec.runOk hstep henter child hr next)
        simp only [Exec.rawNodes]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ hm))
    have hmid : Execution.NoDel wa _ :=
      Exec.step_noDel_of_safe (slot := .some ⟨_, _⟩) hsg h safeNode
        (fun hnd => ihc hsgC safeC hnd)
        (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
    have safeT : ∀ node ∈ Exec.rawNodes next,
        node.sevm.currentTarget = wa →
        ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
      intro node hm
      exact safe node (by
        show node ∈ Exec.rawNodes (Exec.runOk hstep henter child hr next)
        simp only [Exec.rawNodes]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hm))
    exact ih hsg safeT hmid

/-- A complete driver execution preserves no-deletion when every actual
reached node in the executing storage context excludes decoded SELFDESTRUCT.
The certificate is a code/trace fact over `Exec.rawNodes`; its concrete
protected-runtime or routing producer remains separate work. -/
theorem Exec.inv_noDel_of_raw_terminal_safe {wa : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (safe : ∀ node ∈ Exec.rawNodes run,
      node.sevm.currentTarget = wa →
      ¬ Linst.At node.sevm.code node.pc .selfdestruct)
    (initial : Devm.NoDel wa pre) : Execution.NoDel wa out :=
  Exec.invNoDel_of_rawNodes run hsg safe initial

end Blanc
