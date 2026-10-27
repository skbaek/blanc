import Blanc.Lift.CommittedLogs

/-!
# Images of actual successful LOG instructions

The decoded instruction, its actual operand stack and its symbolic memory
read determine the same parent's LOG observation. No memory image is unfolded.
-/
namespace Blanc

open Jaune

/-- Identify an actual successful LOG from its decoded opcode, complete operand
prefix and memory-read payload. This proves no enclosing retention or receipt
identity; those are supplied by the separate parent-log attribution bridge. -/
theorem Exec.Deriv.successfulLog?_eq
    {node : Exec.Deriv} {post : Devm} {n : Fin 5}
    {mi size : B256} {rest : Stack} {data : Bytes}
    (success : node.exn = .ok post)
    (decoded : Ninst.At node.sevm.code node.pc (.reg (.log n)))
    (stack : node.devm.stack = mi :: size :: rest)
    (payload : (node.devm.memory.read mi.toNat size.toNat).1 = data) :
    Exec.Deriv.successfulLog? node = some ⟨node.sevm.currentTarget, rest.take n.val, data⟩ := by
  rcases node with ⟨pc, sevm, pre, out, run⟩
  dsimp only at success stack decoded payload
  subst out
  have hstep : Evm.step ⟨pc, sevm, pre⟩ =
      Step.ofExecution (pc + 1) (Rinst.run ⟨pc, sevm, pre⟩ (.log n)) :=
    Evm.step_next decoded
  cases run with
  | halt step => exact (Step.ofExecution_ne_halt_ok (hstep.symm.trans step)).elim
  | cont step next =>
      change Exec.logAt? pc sevm pre = some ⟨sevm.currentTarget, rest.take n.val, data⟩
      have instruction : Evm.getInst ⟨pc, sevm, pre⟩ = some (.next (.reg (.log n))) := decoded
      rw [Exec.logAt?, instruction, stack]
      change some (⟨sevm.currentTarget, rest.take n.val,
        (pre.memory.read mi.toNat size.toNat).1⟩ : Log) = _
      rw [payload]
  | doneOk step entered resumed next =>
      exact (Step.ofExecution_ne_spawn (hstep.symm.trans step)).elim
  | runOk step entered child resumed next =>
      exact (Step.ofExecution_ne_spawn (hstep.symm.trans step)).elim

end Blanc
