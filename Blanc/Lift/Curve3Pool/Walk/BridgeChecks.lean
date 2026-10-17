import Blanc.Lift.Curve3Pool.Bridge
import Blanc.Lift.Curve3Pool.Walk.ViewsA
import Blanc.Lift.Curve3Pool.Walk.ViewsGvpRaw
import Blanc.Lift.Curve3Pool.Walk.RampStop
import Blanc.Lift.Curve3Pool.Walk.RampA
import Blanc.Lift.Curve3Pool.Walk.ViewsDyRaw
import Blanc.Lift.Curve3Pool.Walk.ViewsDyuRaw
import Blanc.Lift.Curve3Pool.Walk.ViewsCtaRaw
import Blanc.Lift.Curve3Pool.Walk.ViewsCwo

/-!
# The views and ramp entries' raw effects, with the certificate checked

The walk files take the certificate's checkedness `Cert.CheckedM code cert mems true` as a premise
(so that they need not import `Check.lean`); here it is discharged by `checkedM` (Bridge.lean,
from `cert_checkM`), giving each entry's `*_raw`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **Safety of `A()`.** A successful frame of the pool's runtime on the `A()` selector, entered
at a `Checkpoint` with empty stack and memory, computed the model's step on the decoded call in
the quiet environment, with the raw effect Spec states. -/
theorem a_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selA)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  a_raw_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck

/-- **Safety of `get_virtual_price()`**: as `a_raw`, the environment's supply the
`totalSupply()` reply (the token not a precompile). -/
theorem gvp_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetVirtualPrice)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  gvp_raw_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck htok

/-- **Safety of `stop_ramp_A()`.** The successful pc-zero frame refines the model,
including its four ramp-slot writes and exact `StopRampA` log. -/
theorem stopRampA_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selStopRampA)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  stopRampA_raw_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck

/-- **Safety of `get_dy()`.** The successful pc-zero frame computes the exact model
quote, including every checked arithmetic operation, preserving storage and logs. -/
theorem dy_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetDy)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  dy_raw_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck

/-- **Safety of `ramp_A(_future_A, _future_time)`.** The successful pc-zero frame refines the
model: owner, both checked `MIN_RAMP_TIME` deadlines against the frame's own block timestamp,
`0 < _future_A < MAX_A`, the checked `MAX_A_CHANGE` bound against the bridged `_A()`, the four
ramp-slot writes and the exact `RampA` log. -/
theorem rampA_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRampA)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  rampA_raw_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck

/-- **Safety of `get_dy_underlying()`.** The successful pc-zero frame computes the exact
model quote over `PRECISION_MUL`, with every checked arithmetic operation, preserving storage
and logs. -/
theorem dyu_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetDyUnderlying)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  dyu_raw_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck

/-- **Safety of `calc_token_amount(amounts, deposit)`.** The successful pc-zero frame computes
the model's checked quote: `D0` and `D1` by bridged `get_D_mem`, each balance checked by the
deposit flag, the supply the `totalSupply()` reply of the frame's only (static) child, and the
checked `diff * supply / D0`; storage kept, logs only the child's. -/
theorem cta_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcTokenAmount)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  cta_raw_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck htok

/-- **Safety of `calc_withdraw_one_coin(_token_amount, i)`.** The successful pc-zero frame
returns the model's `calcWithdrawOne` amount: `_calc_withdraw_one_coin` walked child-aware on
the derivation (bridged `_A`, `_xp`, `get_D`, both `get_y_D` calls), the supply the
`totalSupply()` reply of the frame's only (static) child; storage kept, logs only the
child's. -/
theorem cwo_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcWithdrawOneCoin)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o :=
  cwo_raw_of checkedM exc hcode hfork hlen hcd hsel hstack hmem hgas hck htok

end Blanc.Lift.Curve3Pool
