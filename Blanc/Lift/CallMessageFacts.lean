import Blanc.Lift.ExactWalkCallChild

/-!
Initial value-call message projections, memory observations and the zero-value
child-message identity. These facts mention no concrete caller or callee code.
-/

namespace Blanc.Lift

open Jaune Blanc

section Msg

variable (sevm : Sevm) (P : Devm) (f : Nat) (v : B256) (c d : Adr) (ii is : Nat) (code : ByteArray)
  (dp : Bool)

theorem vcsm_benvStat : (initSevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).benvStat =
    sevm.benvStat := rfl
theorem vcsm_caller : (initSevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).caller =
    sevm.currentTarget := rfl
theorem vcsm_currentTarget :
    (initSevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).currentTarget = c := rfl
theorem vcsm_value : (initSevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).value = v := rfl
theorem vcsm_isStatic : (initSevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).isStatic =
    (false || sevm.isStatic) := rfl
theorem vcsm_code : (initSevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).code = code := rfl
theorem vcsm_state : (initDevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).state = P.state :=
  rfl
theorem vcsm_gasLeft : (initDevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).gasLeft = f :=
  rfl
theorem vcsm_stack : (initDevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).stack = [] := rfl
theorem vcsm_memory : (initDevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).memory =
    Mem.empty := rfl
theorem vcsm_error : (initDevm (valueCallSpawnMsg sevm P f v c d ii is code dp)).error = none :=
  rfl

theorem scsm_state : (initDevm (staticcallSpawnMsg sevm P f c d ii is code dp)).state = P.state :=
  rfl

end Msg

theorem callSpawnParent_memory_data (d : Devm) (c ii is oi os : Nat) :
    (callSpawnParent d c ii is oi os).memory.data = d.memory.data := rfl

theorem addAccessedAddress_setMach_memory (W : Devm) (m : Mach) (a : Adr) :
    (addAccessedAddress (W.setMach m) a).memory = m.memory := rfl

theorem mem_read_fst (μ : Mem) (i n : Nat) : (μ.read i n).1 = μ.data.sliceD i n 0 := rfl

end Blanc.Lift
