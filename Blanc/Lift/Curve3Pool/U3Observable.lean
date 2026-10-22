import Blanc.Lift.Curve3Pool.U3Refute

/-!
# U3 refuted on the observable: `get_virtual_price` falls at fixed `A`

Goal `curve-3pool-stableswap-v1` §11. `U3Refute.lean` shows the exact ratio `D/T` falls; the
contract returns `get_virtual_price() = D * 10^18 / T` floored (source lines 227–238), and three of
those histories leave that returned word unchanged. The witnesses here show the **returned value**
falls, at deployed-like parameters (`A ∈ {100, 2000}`, fee `1e6` or `1.5e6`, admin fee 50 % or
100 %), each after one first deposit and one operation from the constructor.

`VpObsFalls` is stated on the model's own `get_virtual_price` call (`Call.getVirtualPrice`, run
by `worldRun` against the honest world), which returns `D * 10^18 / T` with `D = get_D(_xp(),
_A())` (`vDChk`) and `T` the 3Crv supply, before and after, at an unchanged `_A()`.

Right after the first deposit the supply is the minted `D` itself, so the price is exactly
`10^18` and any fall of `D/T` is a fall of the returned word. The six `…Deployed` witnesses use
the deployed 3pool's parameters (`A = 2000`, fee `1e6`, admin fee 50 %), one per operation; their
pools are imbalanced (largest/smallest scaled balance 40 to 27197). At admin fee 100 % the
returned price falls at moderate imbalance: `exchange` at 36, `remove_liquidity_one_coin` at 1.3.
The `…_live` witnesses use the live pool's current parameters (`A = 4000`, fee `1.5e6`, admin
fee 100 %) for four of the six operations.
-/

namespace Blanc.Lift.Curve3Pool

/-! ## The observable violation -/

/-- **The returned virtual price falls at fixed `A`** from `w` to `w'` at timestamp `t`: `_A()`
is the same before and after, `get_virtual_price()` succeeds on both worlds without changing
them and returns `D * 10^18 / T` resp. `D' * 10^18 / T'` (`D`, `D'` the `get_D(_xp(), _A())` of
`vDChk`, `T`, `T'` the 3Crv supplies), and the second is strictly smaller. -/
def VpObsFalls (w w' : World) (t : Nat) : Prop :=
  aChk w.pool t = aChk w'.pool t ∧
    ∃ D D', vDChk w.pool t = some D ∧ vDChk w'.pool t = some D' ∧
      worldRun w t 1 .getVirtualPrice = some (w, some (D * 10 ^ 18 / w.supply)) ∧
      worldRun w' t 1 .getVirtualPrice = some (w', some (D' * 10 ^ 18 / w'.supply)) ∧
      D' * 10 ^ 18 / w'.supply < D * 10 ^ 18 / w.supply

/-- The kernel-evaluable form: run `c` from `pre`, check `_A()` is unchanged and that
`get_virtual_price()` returns the floored ratio on both worlds, and report `(D, T, D', T')`. -/
def obsCheck (pre : Option World) (t : Nat) (c : Call) : Option (Nat × Nat × Nat × Nat) := do
  let w ← pre
  let (w', _) ← worldRun w t 1 c
  req (aChk w.pool t = aChk w'.pool t)
  let D ← vDChk w.pool t
  let D' ← vDChk w'.pool t
  req (worldRun w t 1 .getVirtualPrice = some (w, some (D * 10 ^ 18 / w.supply)))
  req (worldRun w' t 1 .getVirtualPrice = some (w', some (D' * 10 ^ 18 / w'.supply)))
  some (D, w.supply, D', w'.supply)

/-- Reading a falling returned price off `obsCheck`. -/
theorem obsCheck_falls {pre : Option World} {t : Nat} {c : Call} {D T D' T' : Nat}
    (h : obsCheck pre t c = some (D, T, D', T')) (hlt : D' * 10 ^ 18 / T' < D * 10 ^ 18 / T) :
    ∃ w w' r, pre = some w ∧ worldRun w t 1 c = some (w', r) ∧ VpObsFalls w w' t := by
  unfold obsCheck req at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_some_none_eq_some,
    Option.some.injEq, Prod.mk.injEq, and_true] at h
  obtain ⟨w, hw, ⟨w', r⟩, hr, -, hA, D0, hD, D1, hD', -, h0, -, h1, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨w, w', r, hw, hr, hA, _, _, hD, hD', h0, h1, hlt⟩

/-! ## The witnesses -/

/-- History: `A = 2000`, fee `1e6`, admin fee 100 %; the first deposit makes a balanced pool
(largest/smallest scaled balance 1.3) of about $4.85M. -/
def obsOneCoinBalancedPre : List Act :=
  [.call t0 (.addLiquidity ⟨1380078919950686522179584, 1637414595665, 1828441235168⟩ 0)]

theorem u3_obs_one_coin_balanced_check :
    obsCheck (reach 2000 1000000 10000000000 obsOneCoinBalancedPre) t0
        (.removeLiquidityOneCoin 58535416512045677281280 0 0) =
      some (4845918558245766047145464, 4845918558245766047145464,
        4787383141733720369864183, 4787383141733720369864184) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `remove_liquidity_one_coin`**: `A = 2000`, fee `1e6`,
admin fee 100 %; a balanced pool (largest/smallest scaled balance 1.3) of about $4.85M; withdraw
58535.4 3Crv in DAI. The returned price goes from `1000000000000000000` to `999999999999999999`:
kernel-checked replay from the constructor. -/
theorem u3_obs_one_coin_balanced :
    ∃ w w' r, reach 2000 1000000 10000000000 obsOneCoinBalancedPre = some w ∧
      worldRun w t0 1 (.removeLiquidityOneCoin 58535416512045677281280 0 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_one_coin_balanced_check (by decide +kernel)

/-- History: `A = 100`, fee `1.5e6`, admin fee 100 %; the first deposit makes a pool of about $1.12M
(largest/smallest scaled balance 36). -/
def obsExchangeModeratePre : List Act :=
  [.call t0 (.addLiquidity ⟨29122060253244361277440, 1055864975667, 37461564924⟩ 0)]

theorem u3_obs_exchange_moderate_check :
    obsCheck (reach 100 1500000 10000000000 obsExchangeModeratePre) t0
        (.exchange 1 0 8714565446 0) =
      some (1012976581485211932107755, 1012976581485211932107755,
        1012976581485211932107754, 1012976581485211932107755) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `exchange`**: `A = 100`, fee `1.5e6`, admin fee 100
%; a pool of about $1.12M (largest/smallest scaled balance 36); sell 8714.565446 USDC for DAI. The
returned price goes from `1000000000000000000` to `999999999999999999`: kernel-checked replay from
the constructor. -/
theorem u3_obs_exchange_moderate :
    ∃ w w' r, reach 100 1500000 10000000000 obsExchangeModeratePre = some w ∧
      worldRun w t0 1 (.exchange 1 0 8714565446 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_exchange_moderate_check (by decide +kernel)

/-- History: `A = 2000`, fee `1e6`, admin fee 50 %; the first deposit makes a pool of about $248
(largest/smallest scaled balance 1382). -/
def obsExchangeDeployedPre : List Act :=
  [.call t0 (.addLiquidity ⟨247429698943369084928, 179001, 838654⟩ 0)]

theorem u3_obs_exchange_deployed_check :
    obsCheck (reach 2000 1000000 5000000000 obsExchangeDeployedPre) t0
        (.exchange 0 1 1 0) =
      some (154291691462711088960, 154291691462711088960,
        154291691462711088959, 154291691462711088960) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `exchange`**: `A = 2000`, fee `1e6`, admin fee 50 %;
a pool of about $248 (largest/smallest scaled balance 1382); sell 1 wei of DAI for USDC. The
returned price goes from `1000000000000000000` to `999999999999999999`: kernel-checked replay from
the constructor. -/
theorem u3_obs_exchange_deployed :
    ∃ w w' r, reach 2000 1000000 5000000000 obsExchangeDeployedPre = some w ∧
      worldRun w t0 1 (.exchange 0 1 1 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_exchange_deployed_check (by decide +kernel)

/-- History: `A = 2000`, fee `1e6`, admin fee 50 %; the first deposit makes a pool of about $59
(largest/smallest scaled balance 40). -/
def obsOneCoinDeployedPre : List Act :=
  [.call t0 (.addLiquidity ⟨1439988294486095104, 56552164, 1407079⟩ 0)]

theorem u3_obs_one_coin_deployed_check :
    obsCheck (reach 2000 1000000 5000000000 obsOneCoinDeployedPre) t0
        (.removeLiquidityOneCoin 2 0 0) =
      some (58766518278623454017, 58766518278623454017,
        58766518278623454014, 58766518278623454015) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `remove_liquidity_one_coin`**: `A = 2000`, fee `1e6`,
admin fee 50 %; a pool of about $59 (largest/smallest scaled balance 40); withdraw 2 wei of 3Crv in
DAI. The returned price goes from `1000000000000000000` to `999999999999999999`: kernel-checked
replay from the constructor. -/
theorem u3_obs_one_coin_deployed :
    ∃ w w' r, reach 2000 1000000 5000000000 obsOneCoinDeployedPre = some w ∧
      worldRun w t0 1 (.removeLiquidityOneCoin 2 0 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_one_coin_deployed_check (by decide +kernel)

/-- History: `A = 2000`, fee `1e6`, admin fee 50 %; the first deposit makes a pool of about $8.95M
(largest/smallest scaled balance 1178). -/
def obsRemoveLiquidityDeployedPre : List Act :=
  [.call t0 (.addLiquidity ⟨8936571955745363429687296, 8850874779, 7586945359⟩ 0)]

theorem u3_obs_remove_liquidity_deployed_check :
    obsCheck (reach 2000 1000000 5000000000 obsRemoveLiquidityDeployedPre) t0
        (.removeLiquidity 1 ⟨0, 0, 0⟩) =
      some (4548996690390763282791385, 4548996690390763282791385,
        4548996690390763282791383, 4548996690390763282791384) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `remove_liquidity`**: `A = 2000`, fee `1e6`, admin
fee 50 %; a pool of about $8.95M (largest/smallest scaled balance 1178); burn 1 wei of 3Crv. The
returned price goes from `1000000000000000000` to `999999999999999999`: kernel-checked replay from
the constructor. -/
theorem u3_obs_remove_liquidity_deployed :
    ∃ w w' r, reach 2000 1000000 5000000000 obsRemoveLiquidityDeployedPre = some w ∧
      worldRun w t0 1 (.removeLiquidity 1 ⟨0, 0, 0⟩) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_remove_liquidity_deployed_check (by decide +kernel)

/-- History: `A = 2000`, fee `1e6`, admin fee 50 %; the first deposit makes a pool of about $51.8k
(largest/smallest scaled balance 1533). -/
def obsDonateDeployedPre : List Act :=
  [.call t0 (.addLiquidity ⟨51680021722449003413504, 33705804, 38207687⟩ 0),
   .gift 0 1]

theorem u3_obs_donate_deployed_check :
    obsCheck (reach 2000 1000000 5000000000 obsDonateDeployedPre) t0
        (.donateAdminFees) =
      some (23494737737286998521085, 23494737737286998521085,
        23494737737286998521084, 23494737737286998521085) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `donate_admin_fees`**: `A = 2000`, fee `1e6`, admin
fee 50 %; a pool of about $51.8k (largest/smallest scaled balance 1533); a 1-wei DAI gift, then
`donate_admin_fees()`. The returned price goes from `1000000000000000000` to `999999999999999999`:
kernel-checked replay from the constructor. -/
theorem u3_obs_donate_deployed :
    ∃ w w' r, reach 2000 1000000 5000000000 obsDonateDeployedPre = some w ∧
      worldRun w t0 1 (.donateAdminFees) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_donate_deployed_check (by decide +kernel)

/-- History: `A = 2000`, fee `1e6`, admin fee 50 %; the first deposit makes a pool of about $15.5k
(largest/smallest scaled balance 2429). -/
def obsAddLiquidityDeployedPre : List Act :=
  [.call t0 (.addLiquidity ⟨15493753495647829360640, 6379735, 9364260⟩ 0)]

theorem u3_obs_add_liquidity_deployed_check :
    obsCheck (reach 2000 1000000 5000000000 obsAddLiquidityDeployedPre) t0
        (.addLiquidity ⟨189165, 0, 0⟩ 0) =
      some (6124944372909509920393, 6124944372909509920393,
        6124944372909509962999, 6124944372909509963000) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `add_liquidity`**: `A = 2000`, fee `1e6`, admin fee
50 %; a pool of about $15.5k (largest/smallest scaled balance 2429); deposit 189165 wei of DAI. The
returned price goes from `1000000000000000000` to `999999999999999999`: kernel-checked replay from
the constructor. -/
theorem u3_obs_add_liquidity_deployed :
    ∃ w w' r, reach 2000 1000000 5000000000 obsAddLiquidityDeployedPre = some w ∧
      worldRun w t0 1 (.addLiquidity ⟨189165, 0, 0⟩ 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_add_liquidity_deployed_check (by decide +kernel)

/-- History: `A = 2000`, fee `1e6`, admin fee 50 %; the first deposit makes a pool of about $687
(largest/smallest scaled balance 27197). -/
def obsImbalanceDeployedPre : List Act :=
  [.call t0 (.addLiquidity ⟨686552434005090107392, 25244, 29973⟩ 0)]

theorem u3_obs_imbalance_deployed_check :
    obsCheck (reach 2000 1000000 5000000000 obsImbalanceDeployedPre) t0
        (.removeLiquidityImbalance ⟨611990, 0, 0⟩ (2 ^ 256 - 1)) =
      some (84374831357328535750, 84374831357328535750,
        84374831357328496873, 84374831357328496876) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `remove_liquidity_imbalance`**: `A = 2000`, fee
`1e6`, admin fee 50 %; a pool of about $687 (largest/smallest scaled balance 27197); withdraw 611990
wei of DAI. The returned price goes from `1000000000000000000` to `999999999999999999`: kernel-
checked replay from the constructor. -/
theorem u3_obs_imbalance_deployed :
    ∃ w w' r, reach 2000 1000000 5000000000 obsImbalanceDeployedPre = some w ∧
      worldRun w t0 1 (.removeLiquidityImbalance ⟨611990, 0, 0⟩ (2 ^ 256 - 1)) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_imbalance_deployed_check (by decide +kernel)

/-! ## At the live pool's current parameters

`A = 4000` (after a completed ramp; here set by the constructor), fee `1.5e6`, admin fee 100 %.
A bounded search found no deposit-plus-one-operation witness for `add_liquidity` or
`remove_liquidity_imbalance` at these parameters. -/

/-- History: `A = 4000`, fee `1.5e6`, admin fee 100 %; the first deposit makes a balanced pool
(largest/smallest scaled balance 1.12) of about $9.38M. -/
def obsOneCoinLivePre : List Act :=
  [.call t0 (.addLiquidity ⟨2974631569767724407062528, 3067641799049, 3335167505283⟩ 0)]

theorem u3_obs_remove_liquidity_one_coin_live_check :
    obsCheck (reach 4000 1500000 10000000000 obsOneCoinLivePre) t0
        (.removeLiquidityOneCoin 36651579986742719021056 0 0) =
      some (9377438110125531686177228, 9377438110125531686177228,
        9340786530138788967156171, 9340786530138788967156172) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `remove_liquidity_one_coin`**: `A = 4000`, fee
`1.5e6`, admin fee 100 %; a balanced pool (largest/smallest scaled balance 1.12) of about $9.38M;
withdraw 36651.58 3Crv in DAI. The returned price goes from `1000000000000000000` to
`999999999999999999`: kernel-checked replay from the constructor. -/
theorem u3_obs_remove_liquidity_one_coin_live :
    ∃ w w' r, reach 4000 1500000 10000000000 obsOneCoinLivePre = some w ∧
      worldRun w t0 1 (.removeLiquidityOneCoin 36651579986742719021056 0 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_remove_liquidity_one_coin_live_check (by decide +kernel)

/-- History: `A = 4000`, fee `1.5e6`, admin fee 100 %; the first deposit makes a pool of about $142k
(largest/smallest scaled balance 304). -/
def obsExchangeLivePre : List Act :=
  [.call t0 (.addLiquidity ⟨2055108991192043880448, 139791719638, 460381297⟩ 0)]

theorem u3_obs_exchange_live_check :
    obsCheck (reach 4000 1500000 10000000000 obsExchangeLivePre) t0
        (.exchange 1 0 1524159651 0) =
      some (134647987133102189808804, 134647987133102189808804,
        134647987133102189808803, 134647987133102189808804) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `exchange`**: `A = 4000`, fee `1.5e6`, admin fee 100
%; a pool of about $142k (largest/smallest scaled balance 304); sell 1524.159651 USDC for DAI. The
returned price goes from `1000000000000000000` to `999999999999999999`: kernel-checked replay from
the constructor. -/
theorem u3_obs_exchange_live :
    ∃ w w' r, reach 4000 1500000 10000000000 obsExchangeLivePre = some w ∧
      worldRun w t0 1 (.exchange 1 0 1524159651 0) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_exchange_live_check (by decide +kernel)

/-- History: `A = 4000`, fee `1.5e6`, admin fee 100 %; the first deposit makes a pool of about
$4.05M (largest/smallest scaled balance 2854). -/
def obsRemoveLiquidityLivePre : List Act :=
  [.call t0 (.addLiquidity ⟨4051742419832531182419968, 1419942278, 1775788842⟩ 0)]

theorem u3_obs_remove_liquidity_live_check :
    obsCheck (reach 4000 1500000 10000000000 obsRemoveLiquidityLivePre) t0
        (.removeLiquidity 1 ⟨0, 0, 0⟩) =
      some (1675312218210541108061495, 1675312218210541108061495,
        1675312218210541108061493, 1675312218210541108061494) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `remove_liquidity`**: `A = 4000`, fee `1.5e6`, admin
fee 100 %; a pool of about $4.05M (largest/smallest scaled balance 2854); burn 1 wei of 3Crv. The
returned price goes from `1000000000000000000` to `999999999999999999`: kernel-checked replay from
the constructor. -/
theorem u3_obs_remove_liquidity_live :
    ∃ w w' r, reach 4000 1500000 10000000000 obsRemoveLiquidityLivePre = some w ∧
      worldRun w t0 1 (.removeLiquidity 1 ⟨0, 0, 0⟩) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_remove_liquidity_live_check (by decide +kernel)

/-- History: `A = 4000`, fee `1.5e6`, admin fee 100 %; the first deposit makes a pool of about
$1.47M (largest/smallest scaled balance 2275). -/
def obsDonateAdminFeesLivePre : List Act :=
  [.call t0 (.addLiquidity ⟨1468238121078321441669120, 966802920, 645285056⟩ 0),
   .gift 0 1]

theorem u3_obs_donate_admin_fees_live_check :
    obsCheck (reach 4000 1500000 10000000000 obsDonateAdminFeesLivePre) t0
        (.donateAdminFees) =
      some (692956845791878889794565, 692956845791878889794565,
        692956845791878889794564, 692956845791878889794565) := by
  decide +kernel

/-- **Observable `get_virtual_price` falls for `donate_admin_fees`**: `A = 4000`, fee `1.5e6`, admin
fee 100 %; a pool of about $1.47M (largest/smallest scaled balance 2275); a 1-wei DAI gift, then
`donate_admin_fees()`. The returned price goes from `1000000000000000000` to `999999999999999999`:
kernel-checked replay from the constructor. -/
theorem u3_obs_donate_admin_fees_live :
    ∃ w w' r, reach 4000 1500000 10000000000 obsDonateAdminFeesLivePre = some w ∧
      worldRun w t0 1 (.donateAdminFees) = some (w', r) ∧
      VpObsFalls w w' t0 :=
  obsCheck_falls u3_obs_donate_admin_fees_live_check (by decide +kernel)

end Blanc.Lift.Curve3Pool
