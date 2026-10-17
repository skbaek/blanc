import Blanc.Lift.Usdc.Lib.Check
import Blanc.Lift.Usdc.Constants
import Blanc.Lift.StaticOnlyFrames
import Blanc.Lift.CallSiteChildren
import Blanc.Lift.CallChildren
import Blanc.Lift.ReachWalk
import Blanc.StaticStorage

/-!
# What the linked `SignatureChecker` library spawns (C2b, nested level)

`lib_children`: a frame running the library runtime `Lib.code` from pc `0` spawns only static
children called by its storage owner (the certificate executes no external instruction but
`STATICCALL`, `parentPrefix_exec_staticcall_of_cert`), and a successful frame leaves its storage
owner's storage unchanged: every instruction of the certificate is state-silent or a
`STATICCALL` (`SFunc.quiet`), and a successful `STATICCALL` keeps every storage map
(`Ninst.staticcall_getStor_eq`), so the lifted run keeps them (`SFunc.RunP.getStor_of_quiet`).

`SFunc.quiet`, `QuietSet` and `SFunc.RunP.getStor_of_quiet` are contract-neutral (hoist candidates
for `Blanc/Lift/Silent.lean`).
-/

namespace Blanc.Lift

open Jaune

/-- A tree whose instructions are state-silent or `STATICCALL`, with no `SELFDESTRUCT` terminal. -/
def SFunc.quiet : SFunc → Bool
  | .branch f g => f.quiet && g.quiet
  | .branchTo f _ => f.quiet
  | .last l => if l = .selfdestruct then false else true
  | .next n f => (regSilent n || n == .exec .staticcall) && f.quiet
  | .dest f => f.quiet
  | .jump _ => true
  | .callNext _ f => f.quiet
  | .ret => true
  | .pcAt _ f => f.quiet
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, each quiet. -/
def QuietSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.quiet && g.refs.all (· ∈ S)
    | none => false

private theorem ninst_getStor_of_quiet {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hn : (regSilent n || n == .exec .staticcall) = true) (run : Ninst.Run sevm pre n post) :
    Devm.getStor post = Devm.getStor pre := by
  rcases Bool.or_eq_true _ _ ▸ hn with silent | static
  · have hstate : post.state = pre.state := Ninst.Run.state_of_regSilent silent run
    funext a
    simp only [Devm.getStor, Devm.getAcct, hstate]
  · have : n = .exec .staticcall := beq_iff_eq.mp static
    subst this
    exact (Ninst.staticcall_getStor_eq hfork run).symm

private theorem getStor_of_state {d d' : Devm} (h : d'.state = d.state) :
    Devm.getStor d' = Devm.getStor d := by
  funext a
  simp only [Devm.getStor, Devm.getAcct, h]

/-- **A quiet lifted run keeps every storage map.** -/
theorem SFunc.RunP.getStor_of_quiet {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc} {S : List Nat}
    (hS : QuietSet fs S = true) {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (hf : f.quiet = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.RunP P fs sevm devm f o) :
    Devm.getStor (Outcome.devm o) = Devm.getStor devm := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.quiet = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  induction run with
  | zero d pop run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact (ih hf.1 hrefs.1).trans (getStor_of_state pop.state.symm)
  | succ d w hnz pop run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact (ih hf.2 hrefs.2).trans (getStor_of_state pop.state.symm)
  | toZero d pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      exact (ih hf hrefs.2).trans (getStor_of_state pop.state.symm)
  | toSucc d w hnz lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have htarget := closed (of_decide_eq_true hrefs.1) lookup
      exact (ih htarget.1 htarget.2).trans (getStor_of_state pop.state.symm)
  | @last d d' l hrun =>
      have hnot : l ≠ .selfdestruct := by
        intro h
        subst h
        simp only [SFunc.quiet, ite_true, Bool.false_eq_true] at hf
      have hframe := Linst.run_instructionFrame sevm d l hnot
      rw [hrun] at hframe
      exact getStor_of_state hframe.state.symm
  | next hrun run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      exact (ih hf.2 hrefs).trans (ninst_getStor_of_quiet hfork hf.1 (hP hrun))
  | dest burn run ih =>
      exact (ih hf hrefs).trans (getStor_of_state burn.state.symm)
  | jump d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have htarget := closed (of_decide_eq_true hrefs.1) lookup
      exact (ih htarget.1 htarget.2).trans (getStor_of_state pop.state.symm)
  | ret d pop => exact getStor_of_state pop.state.symm
  | callHalt d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have htarget := closed (of_decide_eq_true hrefs.1) lookup
      exact (ih htarget.1 htarget.2).trans (getStor_of_state pop.state.symm)
  | callRet d lookup pop run tail ihRun ihTail =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have htarget := closed (of_decide_eq_true hrefs.1) lookup
      simp only [SFunc.quiet] at hf
      exact (ihTail hf hrefs.2).trans ((ihRun htarget.1 htarget.2).trans
        (getStor_of_state pop.state.symm))
  | pcAt hrun _ run ih =>
      simp only [SFunc.quiet] at hf
      simp only [SFunc.refs] at hrefs
      exact (ih hf hrefs).trans (ninst_getStor_of_quiet (n := .reg .pc) hfork rfl (hP hrun))

end Blanc.Lift

namespace Blanc.Lift.Usdc

open Jaune Blanc

theorem lib_staticOnly : ∀ f ∈ Lib.cert.prog, f.execsSatisfy Xinst.isStaticcall = true := by
  decide +kernel

theorem lib_quiet : QuietSet Lib.cert.prog (List.range Lib.cert.length) = true := by
  decide +kernel

/-- The library calls out only by `STATICCALL` and leaves its storage owner's storage unchanged. -/
theorem lib_children {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Lib.code) (fork : CoveredFork sevm.benvStat.fork) :
    (∀ c ∈ Exec.childFrames run, c.sevm.isStatic = true ∧ c.sevm.caller = sevm.currentTarget) ∧
    ∀ post, out = .ok post →
      post.state.getStor sevm.currentTarget = pre.state.getStor sevm.currentTarget := by
  refine ⟨fun c member => ?_, fun post hout => ?_⟩
  · obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
      Exec.childFrames_spawnedAt run (.refl _) c member
    obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
    have hsx : x = .staticcall := parentPrefix_exec_staticcall_of_cert Lib.cert_check lib_staticOnly
      (root := ⟨0, sevm, pre, out, run⟩) rfl codeEq fork chain hat
    subst hsx
    have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
    have hcaller : cevm.sta.caller = f.inner.caller := by
      obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv enter
      rfl
    rw [childEq]
    exact ⟨(Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic hx),
      hcaller.trans ((Xinst.step_staticcall_spawn_caller hx).trans (by rw [sevmEq]))⟩
  · subst hout
    obtain ⟨f, hf0, hrun⟩ := lift_sound Lib.cert_check codeEq fork run
    have hmem : (0 : Nat) ∈ List.range Lib.cert.length := by decide
    have hq := (List.all_eq_true.mp lib_quiet) 0 hmem
    rw [hf0] at hq
    simp only [Bool.and_eq_true] at hq
    have := SFunc.RunP.getStor_of_quiet id lib_quiet fork hq.1 hq.2 hrun
    exact congrFun this sevm.currentTarget

end Blanc.Lift.Usdc
