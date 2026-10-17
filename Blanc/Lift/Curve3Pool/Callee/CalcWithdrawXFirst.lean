import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXSpec

/-!
# `_calc_withdraw_one_coin`'s first `get_y_D` call, as the walk saw it

`xa_cw` exposes the first `get_y_D` call of `_calc_withdraw_one_coin` with its actual stack words
(`amp`, `xp`, `D1`) and the word `y` the callee returned (`getYD_spec`).  `CwFirstGetYD` is that
fact without the program point, in the shape the entry walks carry up to the frame: at the frame's
time `t`, for `_token_amount` `a`, coin `i` and the 3Crv supply `T` the frame read, the model's
checked prefix produces the words `amp`, `xp`, `D1` the bytecode passed, and `get_y_D` on them
returns the word `y` the bytecode received.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **The first `get_y_D` call of `_calc_withdraw_one_coin`**, as the words the bytecode passed and
received (`xa_cw`). -/
def CwFirstGetYD (s : State) (t a : Nat) (i : Fin 3) (T : Nat) : Prop :=
  ∃ (A x0 x1 x2 D0 D1 y : B256),
    aChk s t = some A.toNat ∧
    xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
    getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get A.toNat 1 = some D0.toNat ∧
    ((chkMul a D0.toNat).bind fun m => (chkDiv m T).bind fun q => chkSub D0.toNat q) =
      some D1.toNat ∧
    getYDChk A.toNat i (V3.mk x0.toNat x1.toNat x2.toNat).get D1.toNat = some y.toNat

end Blanc.Lift.Curve3Pool
