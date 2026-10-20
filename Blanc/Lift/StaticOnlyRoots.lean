import Blanc.Lift.StaticOnlyFrames
import Blanc.ExecutionTraceCallOnly

/-!
# Static frames are never CREATE frames

A CREATE-family child is spawned only from a dynamic frame (`assertDynamic`), and its message is
dynamic (`createMsg` sets `isStatic := false`), so every frame a static frame enters, at any
depth, is a static call frame with a code address.  Two consequences, raw (every entered frame,
committed or not):

* `Xinst.step_spawn_codeAddress_of_static`: a spawned static frame has a code address;
* `Exec.static_rawFrameRoots`: every frame a static execution enters is static and has a code
  address;
* `Exec.staticOnly_rawFrameDescendants`: every frame entered below a frame of certified code that
  executes no external instruction but `STATICCALL` has a code address, so such an execution is
  creation-free (`Exec.codeAt_avoid`'s premise holds for every address).

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

theorem genericCreate.step_spawn_inner_isStatic
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress mi ms = .spawn f rsm) :
    f.inner.isStatic = false := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rfl

/-- **A spawned static frame has a code address**: it is not a CREATE frame. -/
theorem Xinst.step_spawn_codeAddress_of_static {sevm : Sevm} {devm : Devm} {x : Xinst}
    (hfork : CoveredFork sevm.benvStat.fork) {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm) (hst : f.inner.isStatic = true) :
    f.inner.codeAddress ≠ none := by
  rcases Xinst.step_shapeCovered sevm devm x hfork with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · rw [genericCreate.step_spawn_inner_isStatic hs] at hst
    cases hst
  · rw [genericCall.step_spawn_codeAddress hs]
    exact Option.some_ne_none _

/-- **Every frame a static execution enters is static and has a code address.** -/
theorem Exec.static_rawFrameRoots {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = true) (hca : sevm.codeAddress ≠ none) :
    ∀ root ∈ Exec.rawFrameRoots run, root.sevm.isStatic = true ∧ root.sevm.codeAddress ≠ none := by
  induction run with
  | halt hstep =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact ⟨hstatic, hca⟩
  | cont hstep next ih =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨hstatic, hca⟩
      · exact ih hfork hstatic hca root (List.mem_cons_of_mem _ member)
  | doneErr hstep henter hresume =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact ⟨hstatic, hca⟩
  | doneOk hstep henter hresume next ih =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨hstatic, hca⟩
      · exact ih hfork hstatic hca root (List.mem_cons_of_mem _ member)
  | @runErr p e d f rsm p' cevm raw er hstep henter child hresume ih =>
      obtain ⟨x, -, hxs, -⟩ := Evm.step_spawn_inv hstep
      have hfst := Xinst.step_spawn_isStatic hxs hstatic
      have hcst := Evm.step_run_isStatic hstep henter hstatic
      have hcac : f.inner.codeAddress ≠ none := Xinst.step_spawn_codeAddress_of_static hfork hxs hfst
      obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv henter
      have hcac' : cevm.sta.codeAddress ≠ none := by rw [hcev]; exact hcac
      have hroots := ih (Evm.step_spawn_child_fork hstep henter hfork) hcst hcac'
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨hstatic, hca⟩
      · rcases member with rfl | member
        · exact hroots _ (List.mem_cons_self ..)
        · exact hroots root (List.mem_cons_of_mem _ member)
  | @runOk p e d f rsm p' cevm raw d' ex hstep henter child hresume next ihChild ihNext =>
      obtain ⟨x, -, hxs, -⟩ := Evm.step_spawn_inv hstep
      have hfst := Xinst.step_spawn_isStatic hxs hstatic
      have hcst := Evm.step_run_isStatic hstep henter hstatic
      have hcac : f.inner.codeAddress ≠ none := Xinst.step_spawn_codeAddress_of_static hfork hxs hfst
      obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv henter
      have hcac' : cevm.sta.codeAddress ≠ none := by rw [hcev]; exact hcac
      have hrootsChild := ihChild (Evm.step_spawn_child_fork hstep henter hfork) hcst hcac'
      have hrootsNext := ihNext hfork hstatic hca
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | member | member | member
      · exact ⟨hstatic, hca⟩
      · exact hrootsChild root (by rw [member]; exact List.mem_cons_self ..)
      · exact hrootsChild root (List.mem_cons_of_mem _ member)
      · exact hrootsNext root (List.mem_cons_of_mem _ member)

/-- **Below a frame of certified code that executes only `STATICCALL`, every entered frame has a
code address**: the certified frame's children are `STATICCALL` frames and every frame below
those is static. -/
theorem Exec.staticOnly_rawFrameDescendants {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    {root : Exec.Deriv} (pc0 : root.pc = 0) (installed : root.sevm.code = code)
    (rootFork : CoveredFork root.sevm.benvStat.fork) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ D ∈ Exec.rawFrameDescendants run, D.sevm.codeAddress ≠ none := by
  intro pc sevm pre out run
  induction run with
  | halt step => simp only [Exec.rawFrameDescendants, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true]
  | cont step next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.cont step next))
  | doneErr step enter resume => simp only [Exec.rawFrameDescendants, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | doneOk step enter resume next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.doneOk step enter resume next))
  | @runErr nodePc nodeSevm nodePre frame rsm nextPc cevm raw e step enter child resume ih =>
    intro chain D member
    have sevmEq : nodeSevm = root.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
    have fork : CoveredFork nodeSevm.benvStat.fork := by rw [sevmEq]; exact rootFork
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall :=
      parentPrefix_exec_staticcall_of_cert checked only pc0 installed rootFork chain instruction
    subst x
    have fst := Xinst.step_staticcall_spawn_isStatic spawn
    have childStatic : cevm.sta.isStatic = true := (Frame.enter_run_isStatic enter).trans fst
    obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv enter
    have cca : cevm.sta.codeAddress ≠ none := by
      rw [hcev]; exact Xinst.step_spawn_codeAddress_of_static fork spawn fst
    have roots := Exec.static_rawFrameRoots child (Evm.step_spawn_child_fork step enter fork) childStatic
      cca
    simp only [Exec.rawFrameDescendants, List.mem_cons] at member
    rcases member with rfl | member
    · exact cca
    · exact (roots D (List.mem_cons_of_mem _ member)).2
  | @runOk nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final step enter child resume
      next childIH nextIH =>
    intro chain D member
    have sevmEq : nodeSevm = root.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
    have fork : CoveredFork nodeSevm.benvStat.fork := by rw [sevmEq]; exact rootFork
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall :=
      parentPrefix_exec_staticcall_of_cert checked only pc0 installed rootFork chain instruction
    subst x
    have fst := Xinst.step_staticcall_spawn_isStatic spawn
    have childStatic : cevm.sta.isStatic = true := (Frame.enter_run_isStatic enter).trans fst
    obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv enter
    have cca : cevm.sta.codeAddress ≠ none := by
      rw [hcev]; exact Xinst.step_spawn_codeAddress_of_static fork spawn fst
    have roots := Exec.static_rawFrameRoots child (Evm.step_spawn_child_fork step enter fork) childStatic
      cca
    have nextNodes := nextIH (chain.snoc (.runOk step enter child resume next))
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · exact cca
    · exact (roots D (List.mem_cons_of_mem _ member)).2
    · exact nextNodes D member

end Blanc.Lift
