import Blanc.Lift.Curve3Pool.Model

/-!
# U3 refuted: virtual price falls at fixed `A`, at states reachable from the constructor

Goal `curve-3pool-stableswap-v1` §11 (user decision `curve3pool-u3-refutation-20261017`): U3's
headline is a kernel-checked counterexample, for each of the six liquidity operations, at a state
reached from the constructor.

The histories run the model `step` against the honest synthetic coins and 3Crv of
`Model.lean` (`World`, `worldRun`, `gift`, `deploy`).

Each counterexample states, at a fixed `A` (no ramp: `futureATime = 0`, so `_A()` is
`future_A`), `vD s * T' > vD s' * T`, where `vD` is the bytecode's `get_D(_xp(), _A())` at the
stored balances (`vDChk`) and `T`, `T'` the 3Crv supply before and after. The histories are the
spec phase's (`evidence/curve-3pool-stableswap-v1/spec/data/counterexamples.json`).
-/

namespace Blanc.Lift.Curve3Pool

open Blanc.StableSwapNewton

/-! ## Histories and the violation -/

/-- One history entry: a call by the owner-deployer `1` at timestamp `t`, or an outsider's gift. -/
inductive Act
  | call (t : Nat) (c : Call)
  | gift (i : Fin 3) (v : Nat)

/-- Run a history against the honest world; `none` if any call reverts. -/
def runActs : World → List Act → Option World
  | w, [] => some w
  | w, .gift i v :: as => runActs (gift w i v) as
  | w, .call t c :: as => do
    let (w', _) ← worldRun w t 1 c
    runActs w' as

/-- The timestamp of every counterexample (`10^9`; there is no ramp, so `_A()` is `future_A`). -/
def t0 : Nat := 10 ^ 9

/-- The world a history from the constructor (`A`, fee, admin fee at `t0`) reaches. -/
def reach (amp fee adminFee : Nat) (h : List Act) : Option World :=
  (deploy amp fee adminFee t0).bind (runActs · h)

/-- **Virtual price falls at fixed `A`** from `w` to `w'` at timestamp `t`: the incoming supply is
positive, `_A()` is the same before and after, both `get_D(_xp(), _A())` succeed, and
`D' · T < D · T'`, i.e. `D'/T' < D/T`. -/
def VpFalls (w w' : World) (t : Nat) : Prop :=
  0 < w.supply ∧ aChk w.pool t = aChk w'.pool t ∧
    ∃ D D', vDChk w.pool t = some D ∧ vDChk w'.pool t = some D' ∧ D' * w.supply < D * w'.supply

/-- The kernel-evaluable form: run `c` from `pre`, check `_A()` is unchanged, and report
`(D, T, D', T')`. -/
def u3Check (pre : Option World) (t : Nat) (c : Call) : Option (Nat × Nat × Nat × Nat) := do
  let w ← pre
  let (w', _) ← worldRun w t 1 c
  req (aChk w.pool t = aChk w'.pool t)
  some (← vDChk w.pool t, w.supply, ← vDChk w'.pool t, w'.supply)

/-- Reading a falling virtual price off `u3Check`. -/
theorem u3Check_falls {pre : Option World} {t : Nat} {c : Call} {D T D' T' : Nat}
    (h : u3Check pre t c = some (D, T, D', T')) (hT : 0 < T) (hlt : D' * T < D * T') :
    ∃ w w' r, pre = some w ∧ worldRun w t 1 c = some (w', r) ∧ VpFalls w w' t := by
  unfold u3Check req at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_some_none_eq_some,
    Option.some.injEq, Prod.mk.injEq, and_true] at h
  obtain ⟨w, hw, ⟨w', r⟩, hr, -, hA, D0, hD, D1, hD', rfl, rfl, rfl, rfl⟩ := h
  exact ⟨w, w', r, hw, hr, hT, hA, _, _, hD, hD', hlt⟩

/-! ## The counterexamples -/

/-- History of the spec's #4: `A = 1`, fee `1e6`, admin fee 100 %; one deposit, then
`exchange(1, 0, 1512569520375)`; `D` falls by 1 wei at an unchanged supply. -/
def exchangePre : List Act :=
  [.call t0 (.addLiquidity ⟨1124218867948297019864249647, 2530836089977235, 1551801547276687⟩ 0)]

theorem u3_refuted_exchange_check :
    u3Check (reach 1 1000000 10000000000 exchangePre) t0
        (.exchange 1 0 1512569520375 0) =
      some (5060240259595919566956961728, 5060240259595919566956961728,
        5060240259595919566956961727, 5060240259595919566956961728) := by
  decide +kernel

/-- **U3 refuted for `exchange`**, the spec's #4: `A = 1`, fee `1e6`, admin fee 100 %; one
deposit, then `exchange(1, 0, 1512569520375)`; `D` falls by 1 wei at an unchanged supply:
kernel-checked replay from the constructor. -/
theorem u3_refuted_exchange :
    ∃ w w' r, reach 1 1000000 10000000000 exchangePre = some w ∧
      worldRun w t0 1 (.exchange 1 0 1512569520375 0) = some (w', r) ∧
      VpFalls w w' t0 :=
  u3Check_falls u3_refuted_exchange_check (by decide +kernel) (by decide +kernel)

/-- History of the spec's #5, deployed-like parameters (`A = 100`, fee `1e6` = 0.01 %, admin fee
50 %): ten calls, the last `exchange(1, 0, 0)`; `D` falls by 1 wei at an unchanged supply. -/
def exchangeDeployedPre : List Act :=
  [.call t0 (.addLiquidity ⟨10386427208602076250, 43955467, 47360591⟩ 0),
   .call t0 (.removeLiquidity 0 ⟨0, 0, 0⟩),
   .call t0 (.removeLiquidity 44066402188341630146 ⟨0, 0, 0⟩),
   .call t0 (.exchange 2 0 27 0),
   .call t0 (.removeLiquidity 48863180089630627 ⟨0, 0, 0⟩),
   .call t0 (.removeLiquidity 34152170435459 ⟨0, 0, 0⟩),
   .call t0 (.removeLiquidityOneCoin 41198453762578996145 2 0),
   .call t0 (.exchange 2 0 0 0),
   .call t0 (.removeLiquidity 5451493160704 ⟨0, 0, 0⟩)]

theorem u3_refuted_exchange_deployed_check :
    u3Check (reach 100 1000000 5000000000 exchangeDeployedPre) t0
        (.exchange 1 0 0 0) =
      some (16235335065924332735, 16122356713875852576,
        16235335065924332734, 16122356713875852576) := by
  decide +kernel

/-- **U3 refuted for `exchange`**, the spec's #5, deployed-like parameters (`A = 100`, fee `1e6`
= 0.01 %, admin fee 50 %): ten calls, the last `exchange(1, 0, 0)`; `D` falls by 1 wei at an
unchanged supply: kernel-checked replay from the constructor. -/
theorem u3_refuted_exchange_deployed :
    ∃ w w' r, reach 100 1000000 5000000000 exchangeDeployedPre = some w ∧
      worldRun w t0 1 (.exchange 1 0 0 0) = some (w', r) ∧
      VpFalls w w' t0 :=
  u3Check_falls u3_refuted_exchange_deployed_check (by decide +kernel) (by decide +kernel)

/-- History of the spec's #0: `A = 1`, fee `544575293`, admin fee 0; deposit, gift, then
`add_liquidity([3, 0, 0])`. -/
def addLiquidityPre : List Act :=
  [.call t0 (.addLiquidity ⟨16199401639002750582784, 10000000000, 31487⟩ 0),
   .gift 0 8521418270090248808,
   .gift 2 7]

theorem u3_refuted_add_liquidity_check :
    u3Check (reach 1 544575293 0 addLiquidityPre) t0
        (.addLiquidity ⟨3, 0, 0⟩ 0) =
      some (1792801470092182589289, 1792801470092182589289,
        1792801470092182589354, 1792801470092182589386) := by
  decide +kernel

/-- **U3 refuted for `add_liquidity`**, the spec's #0: `A = 1`, fee `544575293`, admin fee 0;
deposit, gift, then `add_liquidity([3, 0, 0])`: kernel-checked replay from the constructor. -/
theorem u3_refuted_add_liquidity :
    ∃ w w' r, reach 1 544575293 0 addLiquidityPre = some w ∧
      worldRun w t0 1 (.addLiquidity ⟨3, 0, 0⟩ 0) = some (w', r) ∧
      VpFalls w w' t0 :=
  u3Check_falls u3_refuted_add_liquidity_check (by decide +kernel) (by decide +kernel)

/-- History of the spec's #7: `A = 10`, fee 0, admin fee 100 %; deposit, gift, then
`remove_liquidity(2)`. -/
def removeLiquidityPre : List Act :=
  [.call t0 (.addLiquidity ⟨920405497560991399936, 1000000000, 640423⟩ 0),
   .gift 1 2445800,
   .gift 2 65037027576640]

theorem u3_refuted_remove_liquidity_check :
    u3Check (reach 10 0 10000000000 removeLiquidityPre) t0
        (.removeLiquidity 2 ⟨0, 0, 0⟩) =
      some (850991089228750062043, 850991089228750062043,
        850991089228750062040, 850991089228750062041) := by
  decide +kernel

/-- **U3 refuted for `remove_liquidity`**, the spec's #7: `A = 10`, fee 0, admin fee 100 %;
deposit, gift, then `remove_liquidity(2)`: kernel-checked replay from the constructor. -/
theorem u3_refuted_remove_liquidity :
    ∃ w w' r, reach 10 0 10000000000 removeLiquidityPre = some w ∧
      worldRun w t0 1 (.removeLiquidity 2 ⟨0, 0, 0⟩) = some (w', r) ∧
      VpFalls w w' t0 :=
  u3Check_falls u3_refuted_remove_liquidity_check (by decide +kernel) (by decide +kernel)

/-- History of the spec's #8, deployed-like parameters (`A = 2000`, fee `1e6`, admin fee 50 %):
nine calls, the last `remove_liquidity(1)`. -/
def removeLiquidityDeployedPre : List Act :=
  [.call t0 (.addLiquidity ⟨10976570749861736362, 9622914, 6866438⟩ 0),
   .gift 1 41735562,
   .call t0 (.donateAdminFees),
   .call t0 (.exchange 0 2 10000000000 0),
   .call t0 (.exchange 2 1 10857725 0),
   .call t0 (.removeLiquidityOneCoin 2129363596438300 0 0),
   .call t0 (.exchange 1 2 1000 0),
   .call t0 (.exchange 0 2 7441752863826290890 0),
   .call t0 (.addLiquidity ⟨1000000000000000000000000, 0, 0⟩ 0)]

theorem u3_refuted_remove_liquidity_deployed_check :
    u3Check (reach 2000 1000000 5000000000 removeLiquidityDeployedPre) t0
        (.removeLiquidity 1 ⟨0, 0, 0⟩) =
      some (87501516583596187431954, 34321026977092401285908,
        87501516583596187431951, 34321026977092401285907) := by
  decide +kernel

/-- **U3 refuted for `remove_liquidity`**, the spec's #8, deployed-like parameters (`A = 2000`,
fee `1e6`, admin fee 50 %): nine calls, the last `remove_liquidity(1)`: kernel-checked replay
from the constructor. -/
theorem u3_refuted_remove_liquidity_deployed :
    ∃ w w' r, reach 2000 1000000 5000000000 removeLiquidityDeployedPre = some w ∧
      worldRun w t0 1 (.removeLiquidity 1 ⟨0, 0, 0⟩) = some (w', r) ∧
      VpFalls w w' t0 :=
  u3Check_falls u3_refuted_remove_liquidity_deployed_check (by decide +kernel) (by decide +kernel)

/-- History of the spec's #10: `A = 1`, fee `402788378`, admin fee 0; deposit, then
`remove_liquidity_imbalance([100000, 0, 0])`. -/
def removeLiquidityImbalancePre : List Act :=
  [.call t0 (.addLiquidity ⟨1000000000000000000000, 566336054, 1358⟩ 0)]

theorem u3_refuted_remove_liquidity_imbalance_check :
    u3Check (reach 1 402788378 0 removeLiquidityImbalancePre) t0
        (.removeLiquidityImbalance ⟨100000, 0, 0⟩ (2 ^ 256 - 1)) =
      some (98331850909307643445, 98331850909307643445,
        98331850909307639315, 98331850909307639357) := by
  decide +kernel

/-- **U3 refuted for `remove_liquidity_imbalance`**, the spec's #10: `A = 1`, fee `402788378`,
admin fee 0; deposit, then `remove_liquidity_imbalance([100000, 0, 0])`: kernel-checked replay
from the constructor. -/
theorem u3_refuted_remove_liquidity_imbalance :
    ∃ w w' r, reach 1 402788378 0 removeLiquidityImbalancePre = some w ∧
      worldRun w t0 1 (.removeLiquidityImbalance ⟨100000, 0, 0⟩ (2 ^ 256 - 1)) = some (w', r) ∧
      VpFalls w w' t0 :=
  u3Check_falls u3_refuted_remove_liquidity_imbalance_check (by decide +kernel) (by decide +kernel)

/-- History of the spec's #13, deployed-like parameters (`A = 200`, fee `1e6`, admin fee 50 %):
deposit, `exchange(1, 2, 1e11)`, two one-coin withdrawals of 1000, the last in coin 0. -/
def removeLiquidityOneCoinDeployedPre : List Act :=
  [.call t0 (.addLiquidity ⟨10921537914467434328, 43893245, 31052797⟩ 0),
   .call t0 (.exchange 1 2 100000000000 0),
   .call t0 (.removeLiquidityOneCoin 1000 2 0)]

theorem u3_refuted_remove_liquidity_one_coin_deployed_check :
    u3Check (reach 200 1000000 5000000000 removeLiquidityOneCoinDeployedPre) t0
        (.removeLiquidityOneCoin 1000 0 0) =
      some (1283866191955004512337, 85785978133942998729,
        1283866191955004497366, 85785978133942997729) := by
  decide +kernel

/-- **U3 refuted for `remove_liquidity_one_coin`**, the spec's #13, deployed-like parameters (`A
= 200`, fee `1e6`, admin fee 50 %): deposit, `exchange(1, 2, 1e11)`, two one-coin withdrawals of
1000, the last in coin 0: kernel-checked replay from the constructor. -/
theorem u3_refuted_remove_liquidity_one_coin_deployed :
    ∃ w w' r, reach 200 1000000 5000000000 removeLiquidityOneCoinDeployedPre = some w ∧
      worldRun w t0 1 (.removeLiquidityOneCoin 1000 0 0) = some (w', r) ∧
      VpFalls w w' t0 :=
  u3Check_falls u3_refuted_remove_liquidity_one_coin_deployed_check (by decide +kernel)
    (by decide +kernel)

/-- History of the spec's #2: `A = 1`, fee `5e9`, admin fee 100 %; deposit, a 1-wei DAI gift,
then `donate_admin_fees()`; `D` falls by 1 wei at an unchanged supply. -/
def donateAdminFeesPre : List Act :=
  [.call t0 (.addLiquidity ⟨220465013637442144357580800, 180845591198, 100000000000000⟩ 0),
   .gift 0 1]

theorem u3_refuted_donate_admin_fees_check :
    u3Check (reach 1 5000000000 10000000000 donateAdminFeesPre) t0
        (.donateAdminFees) =
      some (95449129847100691141508666, 95449129847100691141508666,
        95449129847100691141508665, 95449129847100691141508666) := by
  decide +kernel

/-- **U3 refuted for `donate_admin_fees`**, the spec's #2: `A = 1`, fee `5e9`, admin fee 100 %;
deposit, a 1-wei DAI gift, then `donate_admin_fees()`; `D` falls by 1 wei at an unchanged
supply: kernel-checked replay from the constructor. -/
theorem u3_refuted_donate_admin_fees :
    ∃ w w' r, reach 1 5000000000 10000000000 donateAdminFeesPre = some w ∧
      worldRun w t0 1 (.donateAdminFees) = some (w', r) ∧
      VpFalls w w' t0 :=
  u3Check_falls u3_refuted_donate_admin_fees_check (by decide +kernel) (by decide +kernel)


end Blanc.Lift.Curve3Pool
