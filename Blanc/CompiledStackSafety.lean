import Blanc.ExecutionOccurrence
import Blanc.ForwardCall

/-!
Local stack certificates for actual decoded execution, including arbitrary
terminal outcomes and parent resumption. The certificate proves local step
obligations; its invariant is then transported over the existing same-frame
chronology. No parallel execution relation or successful-run premise is used.
-/

namespace Blanc.CompiledStackSafety

open Jaune

/-- Operand-stack faults, distinct from the CALL-depth limit. -/
def StackFault : EvmError → Prop
  | .halt (.stackUnderflow _) => True
  | .halt (.stackOverflow _) => True
  | _ => False

/-- An immediate execution outcome contains no operand-stack fault. -/
def NoStackFault (out : Execution) : Prop :=
  ∀ err post, out = .error (err, post) → ¬ StackFault err

/-- A stack fault returned by a resumption came from the supplied child
settlement, rather than a failing push on the parent's operand stack. -/
def InheritedStackFault
    (settled : Except (EvmError × State × AdrSet × Tra) Devm)
    (err : EvmError) : Prop :=
  ∃ state addresses transient, settled = .error (err, state, addresses, transient)

/-- Local parent continuation obligations for every child settlement. -/
def ResumeSafe (invariant : Nat → Devm → Prop) (pc : Nat) (resume : Resume) : Prop :=
  ∀ settled,
    (∀ post, resume.run settled = .ok post → invariant pc post) ∧
    (∀ err post, resume.run settled = .error (err, post) →
      StackFault err → InheritedStackFault settled err)

/-- The checked property of one actual decoded step. Spawned child code is
arbitrary; only the original parent's continuation is covered here. -/
def StepSafe (invariant : Nat → Devm → Prop) : Step → Prop
  | .halt out => NoStackFault out
  | .cont pc post => invariant pc post
  | .spawn _ resume pc => ResumeSafe invariant pc resume

/-- Parent headroom makes either ordinary child outcome resume with exactly
one status word. This constructs the successful resume instead of assuming it. -/
theorem call_resumes_of_room (parent child : Devm) (oi os : Nat)
    (room : parent.stack.length < 1024) :
    ∃ post, (Resume.call parent oi os).run (.ok child) = .ok post ∧
      post.stack = (if child.error.isSome then (0 : B256) else 1) :: parent.stack := by
  have resumes : ∃ post, (Resume.call parent oi os).run (.ok child) = .ok post := by
    cases herror : child.error.isSome with
    | false => exact ⟨_, Resume.run_call_ok herror room⟩
    | true => exact ⟨_, Resume.run_call_err herror room⟩
  obtain ⟨post, run⟩ := resumes
  exact ⟨post, run, Resume.call_stack_flag run⟩

/-- The actual CALL resumer cannot generate a new operand-stack failure
when the parent has headroom. Fatal child errors retain their provenance. -/
theorem resume_call_safe
    {invariant : Nat → Devm → Prop} {pc : Nat}
    (parent : Devm) (oi os : Nat)
    (room : parent.stack.length < 1024)
    (continuation : ∀ post flag, (flag = 0 ∨ flag = 1) →
      post.stack = flag :: parent.stack → invariant pc post) :
    ResumeSafe invariant pc (.call parent oi os) := by
  intro settled
  cases settled with
  | error error =>
      rcases error with ⟨err, state, addresses, transient⟩
      constructor
      · intro post run
        exact False.elim (Resume.call_run_error run)
      · intro otherErr post run fault
        rw [Resume.run_call_fatal] at run
        cases run
        exact ⟨state, addresses, transient, rfl⟩
  | ok child =>
      obtain ⟨post, run, stack⟩ := call_resumes_of_room parent child oi os room
      constructor
      · intro actual result
        rw [run] at result
        cases result
        apply continuation _ _ _ stack
        split <;> simp
      · intro err actual result fault
        rw [run] at result
        cases result

/-- A proof-carrying collection of local obligations for fixed actual code.
Consumers must prove `step` from the decoder and the instruction semantics;
merely assigning heights to counters does not construct this certificate. -/
structure Certificate (sevm : Sevm) (invariant : Nat → Devm → Prop)
    (maximum : Nat) : Prop where
  height : ∀ pc pre, invariant pc pre → pre.stack.length ≤ maximum
  step : ∀ pc pre, invariant pc pre → StepSafe invariant (Evm.step ⟨pc, sevm, pre⟩)

/-- Transport one local certificate over an actual same-frame continuation. -/
theorem Certificate.parentStep
    {sevm : Sevm} {invariant : Nat → Devm → Prop} {maximum : Nat}
    (certificate : Certificate sevm invariant maximum)
    {root next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root)
    (codeFrame : root.sevm = sevm)
    (entry : invariant root.pc root.devm) :
    next.sevm = sevm ∧ invariant next.pc next.devm := by
  cases edge with
  | cont hstep continuation =>
      dsimp only at codeFrame entry ⊢
      subst codeFrame
      have safe := certificate.step _ _ entry
      rw [hstep] at safe
      exact ⟨rfl, safe⟩
  | doneOk hstep henter hresume continuation =>
      dsimp only at codeFrame entry ⊢
      subst codeFrame
      have safe := certificate.step _ _ entry
      rw [hstep] at safe
      exact ⟨rfl, (safe _).1 _ hresume⟩
  | runOk hstep henter child hresume continuation =>
      dsimp only at codeFrame entry ⊢
      subst codeFrame
      have safe := certificate.step _ _ entry
      rw [hstep] at safe
      exact ⟨rfl, (safe _).1 _ hresume⟩

/-- Every reached same-frame boundary satisfies the checked invariant,
regardless of the root's raw outcome or the number of loop iterations. -/
theorem Certificate.parentPrefix
    {sevm : Sevm} {invariant : Nat → Devm → Prop} {maximum : Nat}
    (certificate : Certificate sevm invariant maximum)
    {root node : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root node)
    (codeFrame : root.sevm = sevm)
    (entry : invariant root.pc root.devm) :
    node.sevm = sevm ∧ invariant node.pc node.devm := by
  induction hprefix with
  | refl => exact ⟨codeFrame, entry⟩
  | step edge rest ih =>
      obtain ⟨nextFrame, nextEntry⟩ := certificate.parentStep edge codeFrame entry
      exact ih nextFrame nextEntry

/-- The local error and height facts hold at each actual same-frame node.
This conclusion includes failing terminal nodes, not just successful walks. -/
theorem Certificate.at_parentPrefix
    {sevm : Sevm} {invariant : Nat → Devm → Prop} {maximum : Nat}
    (certificate : Certificate sevm invariant maximum)
    {root node : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root node)
    (codeFrame : root.sevm = sevm)
    (entry : invariant root.pc root.devm) :
    node.devm.stack.length ≤ maximum ∧
      StepSafe invariant (Evm.step ⟨node.pc, node.sevm, node.devm⟩) := by
  obtain ⟨frame, valid⟩ := certificate.parentPrefix hprefix codeFrame entry
  refine ⟨certificate.height _ _ valid, ?_⟩
  rw [frame]
  exact certificate.step _ _ valid

end Blanc.CompiledStackSafety
