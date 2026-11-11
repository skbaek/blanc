import Blanc.Lift.RequestSystem.Call

/-!
# Whole-storage extraction for request system calls

The pure storage transformer and its equality with the system call post-state retain their legacy
names and namespace. Metadata updates use words; every other storage slot keeps its input value.
-/

namespace Blanc.Lift.BuilderRequest.Delivery

open Jaune
open RequestSystem

/-- The storage a builder system call on empty calldata leaves, as a function of the storage before it. -/
def drainStor (p : SysShape) (s : Stor) : Stor :=
  let c := drainCount p.cap.word (s.get 2) (s.get 3)
  let s1 := if s.get 2 + c = s.get 3 then (s.set 2 0).set 3 0 else s.set 2 (s.get 2 + c)
  (s1.set 0 (p.next (s.get 0) (s.get 1))).set 1 0

theorem sysState_getStor (p : SysShape) (σ : State) (a : Adr) :
    (sysState p σ a).getStor a = drainStor p (σ.getStor a) := by
  simp only [sysState, drainStor]
  split <;> simp only [State.getStor_setStorVal_self]

end Blanc.Lift.BuilderRequest.Delivery
