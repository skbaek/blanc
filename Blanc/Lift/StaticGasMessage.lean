import Blanc.Lift.StaticGasTransport
import Blanc.Lift.ExactWalk

/-!
# A frame theorem at message entry, across the message's gas

A frame theorem is stated at an arbitrary static machine `sevm` and an entry
`St pre [] Mem.empty G`. A message `msg` entered with the execution grant `G` (`msg.withGas G`)
is exactly that frame at `sevm := {initSevm msg with gas := G}` and `pre := initDevm msg`
(`initSevm_withGas`, `initDevm_withGas`): only the static initial-gas coordinate and the dynamic
gas depend on `G`. So a cost fixed at the base message's `(initSevm msg, initDevm msg)` stays the
same at every grant once the frame theorem's premises and cost are transported across
`Sevm.gas` (`StaticGasTransport`), and the frame's execution is the message's
(`exec_withGas_of_frame`).

`initDevm_gasMeasure`: a message's frame state measures exactly its execution gas (nothing is
spilled at entry).
-/

namespace Blanc.Lift

open Jaune

/-- The message with its execution grant replaced. -/
def _root_.Jaune.Msg.withGas (msg : Msg) (G : Nat) : Msg := {msg with gas := G}

/-- A message's static machine at a new grant is the base one with that initial gas. -/
theorem initSevm_withGas (msg : Msg) (G : Nat) :
    initSevm (msg.withGas G) = {initSevm msg with gas := G} := rfl

/-- A message's entry at a new grant is the base entry's frame state at that gas. -/
theorem initDevm_withGas (msg : Msg) (G : Nat) :
    initDevm (msg.withGas G) = St (initDevm msg) [] Mem.empty G := rfl

/-- A message's frame state at gas `G` measures `G`: nothing is spilled at entry. -/
theorem initDevm_gasMeasure (msg : Msg) (G : Nat) :
    (St (initDevm msg) [] Mem.empty G).gasMeasure = G := rfl

/-- **A frame execution at the message's grant is the message's execution.** -/
theorem exec_withGas_of_frame {msg : Msg} {G : Nat} {post : Devm}
    (exc : Exec 0 {initSevm msg with gas := G} (St (initDevm msg) [] Mem.empty G) (.ok post)) :
    exec (initEvm (msg.withGas G)) = .ok post :=
  (exec_iff_exec_eq 0 _ _ _).mp ⟨exc⟩

end Blanc.Lift
