import Blanc.Lift.UniswapV2Pair.BurnForward

/-! Literal states and source trees used by actual Burn cursor cuts. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Literal original-bytecode reserve-helper line before its return. -/
def burnReserveLine : List Ninst := [
  .push [8] (by decide), .reg .sload,
  .push [255,255,255,255,255,255,255,255,255,255,255,255,255,255] (by decide),
  .reg (.dup 0), .reg (.dup 2), .reg .and, .reg (.swap 2),
  .push [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide),
  .reg (.dup 3), .reg .div, .reg (.swap 0), .reg (.swap 1), .reg .and,
  .reg (.swap 1),
  .push [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] (by decide),
  .reg (.swap 0), .reg .div, .push [255,255,255,255] (by decide),
  .reg .and, .reg (.swap 0)]

/-- The continuation immediately after the first initial STATICCALL. -/
def burnFirstAfterCallTree : SFunc :=
  match t_14fb_c37 with
  | .dest (.next _ (.next _ (.next _ f))) => f
  | _ => .undefined

/-- The initial request state, computed from cached storage and ABI input. -/
def burnFirstCallInput (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (G : Nat) (r1 r0 toWord extρ : B256) : Devm :=
  let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
  let t0 := mask &&& b.getStorVal sevm.currentTarget 6
  let t1 := mask &&& (afterSload sevm b 6).getStorVal sevm.currentTarget 7
  St (temporalAccountAccessBase (burnTokensWorld sevm b) t0.toAdr)
    (G.toB256 :: t0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
      t0 :: 0 :: t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
    (balanceRequestMemory M sevm.currentTarget) G

end Blanc.Lift.UniswapV2Pair
