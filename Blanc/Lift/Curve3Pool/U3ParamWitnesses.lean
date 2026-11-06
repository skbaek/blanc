import Blanc.Lift.Curve3Pool.U3Observable

/-!
# The returned virtual price falls at further parameter settings

The witnesses here state only parameters and calls. A `Fixture` history builds the pool with `A = 720`,
fee 0 and admin fee 0, deposits `10^6` of each coin, then commits the fee `10^7` with admin fee 0 and
applies it three days later: `feeFixture` is that sequence.

* the `Fixture` witnesses start from that exact deposit;
* the `First` witnesses make a different first deposit, then apply the same fee change;
* the `Params` witnesses use the constructor triple `A = 100`, fee `4000000`, admin fee 0.

No witness uses a `gift`. There is no ramp in any history, and `VpObsFalls` states that `_A()` is the
same before and after the call. Each `…_check` reports `(D, T, D', T')`, so the size of the fall in
the returned word is `D * 10^18 / T - D' * 10^18 / T'`.
-/

namespace Blanc.Lift.Curve3Pool

/-- Three days after `t0`, when the committed fee may be applied. -/
def feeT1 : Nat := t0 + 3 * 86400

/-- The fee change `set_fees(10^7, 0)`: commit at `t0`, apply three days later. -/
def feeChange : List Act :=
  [.call t0 (.commitNewFee 10000000 0), .call feeT1 .applyNewFee]

/-- The setup from a constructor with `A = 720`, fee 0, admin fee 0: a deposit of `10^6` of
each coin, then `set_fees(10^7, 0)`. -/
def feeFixture : List Act :=
  .call t0 (.addLiquidity ⟨10 ^ 24, 10 ^ 12, 10 ^ 12⟩ 0) :: feeChange

/-- The fixture's state: fee `10^7`, admin fee 0, `_A() = 720`, supply `3 * 10^24`, and a returned
price of exactly `10^18`. -/
theorem feeFixture_state :
    ((reach 720 0 0 feeFixture).bind fun w =>
      (worldRun w feeT1 1 .getVirtualPrice).map fun r =>
        (w.pool.fee, w.pool.adminFee, aChk w.pool feeT1, w.supply, r.2)) =
      some (10000000, 0, some 720, 3 * 10 ^ 24, some (10 ^ 18)) := by
  decide +kernel

/-- History for `vp_falls_fixture_oneCoin`. -/
def fixtureOneCoinPre : List Act :=
  feeFixture ++
    [.call feeT1 (.exchange 1 2 4976217494367 0)]

theorem vp_falls_fixture_oneCoin_check :
    obsCheck (reach 720 0 0 fixtureOneCoinPre) feeT1
        (.removeLiquidityOneCoin 56 0 0) =
      some (5118657716727494049000000, 3000000000000000000000000,
        5118657716727494048999904, 2999999999999999999999944) := by
  decide +kernel

/-- **The returned price falls** at `A = 720`, fee `10000000`, admin fee `0`: sell 4976217.494367 of coin 1 for coin 2, then burn 56 wei of LP for coin 0. The price goes from
`1706219238909164683` to `1706219238909164682`, a fall of 1. Largest/smallest scaled balance 5.65e+03. -/
theorem vp_falls_fixture_oneCoin :
    ∃ w w' r, reach 720 0 0 fixtureOneCoinPre = some w ∧
      worldRun w feeT1 1 (.removeLiquidityOneCoin 56 0 0) = some (w', r) ∧
      VpObsFalls w w' feeT1 :=
  obsCheck_falls vp_falls_fixture_oneCoin_check (by decide +kernel)

/-- History for `vp_falls_fixture_exchange`. -/
def fixtureExchangePre : List Act :=
  feeFixture ++
    [.call feeT1 (.removeLiquidity 2992784635095000000000000 ⟨0, 0, 0⟩),
     .call feeT1 (.exchange 0 1 70190276605463913836706 0)]

theorem vp_falls_fixture_exchange_check :
    obsCheck (reach 720 0 0 fixtureExchangePre) feeT1
        (.exchange 0 1 3 0) =
      some (32042834914245078430866, 7215364905000000000000,
        32042834914245078430865, 7215364905000000000000) := by
  decide +kernel

/-- **The returned price falls** at `A = 720`, fee `10000000`, admin fee `0`: remove most liquidity, sell coin 0 for coin 1, then sell 3 wei of coin 0. The price goes from
`4440916756966857580` to `4440916756966857579`, a fall of 1. Largest/smallest scaled balance 3.01e+04. -/
theorem vp_falls_fixture_exchange :
    ∃ w w' r, reach 720 0 0 fixtureExchangePre = some w ∧
      worldRun w feeT1 1 (.exchange 0 1 3 0) = some (w', r) ∧
      VpObsFalls w w' feeT1 :=
  obsCheck_falls vp_falls_fixture_exchange_check (by decide +kernel)

/-- History for `vp_falls_fixture_imbalance`. -/
def fixtureImbalancePre : List Act :=
  feeFixture ++
    [.call feeT1 (.removeLiquidity 2999285193030000000000000 ⟨0, 0, 0⟩),
     .call feeT1 (.exchange 0 1 170324120054259561364322 0)]

theorem vp_falls_fixture_imbalance_check :
    obsCheck (reach 720 0 0 fixtureImbalancePre) feeT1
        (.removeLiquidityImbalance ⟨65536, 0, 0⟩ (2 ^ 256 - 1)) =
      some (17162862332049128748773, 714806970000000000000,
        17162862332049128745383, 714806969999999999859) := by
  decide +kernel

/-- **The returned price falls** at `A = 720`, fee `10000000`, admin fee `0`: remove most liquidity, sell coin 0 for coin 1, then withdraw 65536 wei of coin 0. The price goes from
`24010485421048886455` to `24010485421048886454`, a fall of 1. Largest/smallest scaled balance 7.16e+05. -/
theorem vp_falls_fixture_imbalance :
    ∃ w w' r, reach 720 0 0 fixtureImbalancePre = some w ∧
      worldRun w feeT1 1 (.removeLiquidityImbalance ⟨65536, 0, 0⟩ (2 ^ 256 - 1)) = some (w', r) ∧
      VpObsFalls w w' feeT1 :=
  obsCheck_falls vp_falls_fixture_imbalance_check (by decide +kernel)

/-- History for `vp_falls_fixture_addLiquidity`. -/
def fixtureAddLiquidityPre : List Act :=
  feeFixture ++
    [.call feeT1 (.removeLiquidity 2999722546593000000000000 ⟨0, 0, 0⟩),
     .call feeT1 (.exchange 0 1 80393446285769737921703 0)]

theorem vp_falls_fixture_addLiquidity_check :
    obsCheck (reach 720 0 0 fixtureAddLiquidityPre) feeT1
        (.addLiquidity ⟨16384, 0, 0⟩ 0) =
      some (7363337763065607888522, 277453407000000000000,
        7363337763065607889291, 277453407000000000029) := by
  decide +kernel

/-- **The returned price falls** at `A = 720`, fee `10000000`, admin fee `0`: remove most liquidity, sell coin 0 for coin 1, then deposit 16384 wei of coin 0. The price goes from
`26539006468446818851` to `26539006468446818850`, a fall of 1. Largest/smallest scaled balance 8.7e+05. -/
theorem vp_falls_fixture_addLiquidity :
    ∃ w w' r, reach 720 0 0 fixtureAddLiquidityPre = some w ∧
      worldRun w feeT1 1 (.addLiquidity ⟨16384, 0, 0⟩ 0) = some (w', r) ∧
      VpObsFalls w w' feeT1 :=
  obsCheck_falls vp_falls_fixture_addLiquidity_check (by decide +kernel)

/-- History for `vp_falls_firstOneCoin`. -/
def feeFirstOneCoinPre : List Act :=
  .call t0 (.addLiquidity ⟨273649849671877804221219, 5731967991231, 1860267404235⟩ 0) :: feeChange

theorem vp_falls_firstOneCoin_check :
    obsCheck (reach 720 0 0 feeFirstOneCoinPre) feeT1
        (.removeLiquidityOneCoin 4 0 0) =
      some (7847235165455366898263767, 7847235165455366898263767,
        7847235165455366898263762, 7847235165455366898263763) := by
  decide +kernel

/-- **The returned price falls** at `A = 720`, fee `10000000`, admin fee `0`: burn 4 wei of LP for coin 0. The price goes from
`1000000000000000000` to `999999999999999999`, a fall of 1. Largest/smallest scaled balance 20.9. -/
theorem vp_falls_firstOneCoin :
    ∃ w w' r, reach 720 0 0 feeFirstOneCoinPre = some w ∧
      worldRun w feeT1 1 (.removeLiquidityOneCoin 4 0 0) = some (w', r) ∧
      VpObsFalls w w' feeT1 :=
  obsCheck_falls vp_falls_firstOneCoin_check (by decide +kernel)

/-- History for `vp_falls_firstRemove`. -/
def feeFirstRemovePre : List Act :=
  .call t0 (.addLiquidity ⟨46661521199324962226176, 14141770, 28582711⟩ 0) :: feeChange

theorem vp_falls_firstRemove_check :
    obsCheck (reach 720 0 0 feeFirstRemovePre) feeT1
        (.removeLiquidity 1 ⟨0, 0, 0⟩) =
      some (13794273849656543103505, 13794273849656543103505,
        13794273849656543103503, 13794273849656543103504) := by
  decide +kernel

/-- **The returned price falls** at `A = 720`, fee `10000000`, admin fee `0`: burn 1 wei of LP. The price goes from
`1000000000000000000` to `999999999999999999`, a fall of 1. Largest/smallest scaled balance 3.3e+03. -/
theorem vp_falls_firstRemove :
    ∃ w w' r, reach 720 0 0 feeFirstRemovePre = some w ∧
      worldRun w feeT1 1 (.removeLiquidity 1 ⟨0, 0, 0⟩) = some (w', r) ∧
      VpObsFalls w w' feeT1 :=
  obsCheck_falls vp_falls_firstRemove_check (by decide +kernel)

/-- History for `vp_falls_firstTinyOneCoin`. -/
def feeFirstTinyOneCoinPre : List Act :=
  .call t0 (.addLiquidity ⟨18054159784617, 587, 10⟩ 0) :: feeChange

theorem vp_falls_firstTinyOneCoin_check :
    obsCheck (reach 720 0 0 feeFirstTinyOneCoinPre) feeT1
        (.removeLiquidityOneCoin 7 0 0) =
      some (595045042696193, 595045042696193,
        595045042696185, 595045042696186) := by
  decide +kernel

/-- **The returned price falls** at `A = 720`, fee `10000000`, admin fee `0`: burn 7 wei of LP for coin 0; the pool is about 6e14 wei of LP, so one wei of `D` is many word units. The price goes from
`1000000000000000000` to `999999999999998319`, a fall of 1681. Largest/smallest scaled balance 58.7. -/
theorem vp_falls_firstTinyOneCoin :
    ∃ w w' r, reach 720 0 0 feeFirstTinyOneCoinPre = some w ∧
      worldRun w feeT1 1 (.removeLiquidityOneCoin 7 0 0) = some (w', r) ∧
      VpObsFalls w w' feeT1 :=
  obsCheck_falls vp_falls_firstTinyOneCoin_check (by decide +kernel)

/-- History for `vp_falls_params_OneCoin`. -/
def paramsOneCoinPre : List Act :=
  [.call t0 (.addLiquidity ⟨540712138941758899472585, 1160326029455, 1949013540497⟩ 0)]

theorem vp_falls_params_OneCoin_check :
    obsCheck (reach 100 4000000 0 paramsOneCoinPre) t0
        (.removeLiquidityOneCoin 8 0 0) =
      some (3644390107035349516613408, 3644390107035349516613408,
        3644390107035349516613399, 3644390107035349516613400) := by
  decide +kernel

/-- **The returned price falls** at `A = 100`, fee `4000000`, admin fee `0`: a first deposit, then a dust call. The price goes from
`1000000000000000000` to `999999999999999999`, a fall of 1. Largest/smallest scaled balance 3.6. -/
theorem vp_falls_params_OneCoin :
    ∃ w w' r, reach 100 4000000 0 paramsOneCoinPre = some w ∧
      worldRun w t0 1 (.removeLiquidityOneCoin 8 0 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls vp_falls_params_OneCoin_check (by decide +kernel)

/-- History for `vp_falls_params_Remove`. -/
def paramsRemovePre : List Act :=
  [.call t0 (.addLiquidity ⟨1303417805940886450571649, 12781455751, 12846024632⟩ 0)]

theorem vp_falls_params_Remove_check :
    obsCheck (reach 100 4000000 0 paramsRemovePre) t0
        (.removeLiquidity 1 ⟨0, 0, 0⟩) =
      some (919585373726591909207611, 919585373726591909207611,
        919585373726591909207609, 919585373726591909207610) := by
  decide +kernel

/-- **The returned price falls** at `A = 100`, fee `4000000`, admin fee `0`: a first deposit, then a dust call. The price goes from
`1000000000000000000` to `999999999999999999`, a fall of 1. Largest/smallest scaled balance 102. -/
theorem vp_falls_params_Remove :
    ∃ w w' r, reach 100 4000000 0 paramsRemovePre = some w ∧
      worldRun w t0 1 (.removeLiquidity 1 ⟨0, 0, 0⟩) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls vp_falls_params_Remove_check (by decide +kernel)

/-- History for `vp_falls_params_Exchange`. -/
def paramsExchangePre : List Act :=
  [.call t0 (.addLiquidity ⟨78247025325370577131128266, 141398014545043, 1631954253508⟩ 0)]

theorem vp_falls_params_Exchange_check :
    obsCheck (reach 100 4000000 0 paramsExchangePre) t0
        (.exchange 1 0 0 0) =
      some (208941867103925582560820412, 208941867103925582560820412,
        208941867103925582560820411, 208941867103925582560820412) := by
  decide +kernel

/-- **The returned price falls** at `A = 100`, fee `4000000`, admin fee `0`: a first deposit, then a dust call. The price goes from
`1000000000000000000` to `999999999999999999`, a fall of 1. Largest/smallest scaled balance 86.6. -/
theorem vp_falls_params_Exchange :
    ∃ w w' r, reach 100 4000000 0 paramsExchangePre = some w ∧
      worldRun w t0 1 (.exchange 1 0 0 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls vp_falls_params_Exchange_check (by decide +kernel)

/-- History for `vp_falls_params_AddLiquidity`. -/
def paramsAddLiquidityPre : List Act :=
  [.call t0 (.addLiquidity ⟨15184672904375984597356, 261120540, 73192913⟩ 0)]

theorem vp_falls_params_AddLiquidity_check :
    obsCheck (reach 100 4000000 0 paramsAddLiquidityPre) t0
        (.addLiquidity ⟨32768, 0, 0⟩ 0) =
      some (10460478779553119267883, 10460478779553119267883,
        10460478779553119282745, 10460478779553119282746) := by
  decide +kernel

/-- **The returned price falls** at `A = 100`, fee `4000000`, admin fee `0`: a first deposit, then a dust call. The price goes from
`1000000000000000000` to `999999999999999999`, a fall of 1. Largest/smallest scaled balance 207. -/
theorem vp_falls_params_AddLiquidity :
    ∃ w w' r, reach 100 4000000 0 paramsAddLiquidityPre = some w ∧
      worldRun w t0 1 (.addLiquidity ⟨32768, 0, 0⟩ 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls vp_falls_params_AddLiquidity_check (by decide +kernel)

/-- History for `vp_falls_params_Imbalance`. -/
def paramsImbalancePre : List Act :=
  [.call t0 (.addLiquidity ⟨21978104843719882076419961, 19852361353, 27217888314⟩ 0)]

theorem vp_falls_params_Imbalance_check :
    obsCheck (reach 100 4000000 0 paramsImbalancePre) t0
        (.removeLiquidityImbalance ⟨32768, 0, 0⟩ (2 ^ 256 - 1)) =
      some (6244006612382564453332677, 6244006612382564453332677,
        6244006612382564453327609, 6244006612382564453327610) := by
  decide +kernel

/-- **The returned price falls** at `A = 100`, fee `4000000`, admin fee `0`: a first deposit, then a dust call. The price goes from
`1000000000000000000` to `999999999999999999`, a fall of 1. Largest/smallest scaled balance 1.11e+03. -/
theorem vp_falls_params_Imbalance :
    ∃ w w' r, reach 100 4000000 0 paramsImbalancePre = some w ∧
      worldRun w t0 1 (.removeLiquidityImbalance ⟨32768, 0, 0⟩ (2 ^ 256 - 1)) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls vp_falls_params_Imbalance_check (by decide +kernel)

end Blanc.Lift.Curve3Pool
