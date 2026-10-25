import Blanc.Lift.CursorSourceRun
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.StaticCallGuard

/-! Actual checked return-width guards and physical word decoding. -/

namespace Blanc.Lift
open Jaune

def returnWordGuardLine (destination : Bytes) (le : destination.length ≤ 32) : List Ninst :=
  [.reg .pop, .reg .pop, .reg .pop, .reg .pop] ++
    returnWidthCompareLine ++ [.push destination le]

def callFlagGuardLine (destination : Bytes) (le : destination.length ≤ 32) : List Ninst :=
  [.reg .iszero, .reg (.dup 0), .reg .iszero, .push destination le]

end Blanc.Lift
