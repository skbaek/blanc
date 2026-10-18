import Blanc.Composition.Curve3Pool3CrvTxFrame
import Blanc.Composition.Curve3Pool3CrvBlock

/-!
# U9(b): worlds agreeing with `P0` on the touched accounts

`AgreesP0 st`: `st` and `P0` hold the same account at the trader, the pool, 3Crv, the three coins,
the identity precompile `4`, the coinbase `0` and the four system addresses.  Every world-level
premise of the closed block is read off these accounts:

* `exTxContext_of_agrees`: the exchange transaction's context on the closed block's environment;
* `systemCodes_of_agrees`: the system fixture before the block;
* `joint_of_agrees`: the joint pool–3Crv checkpoint, transported through U9(a)'s checker (it reads
  only the pool's and 3Crv's storage);
* `poolInstalled_of_agrees`, `c3crvInstalled_of_agrees`: the CODE premises.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Composition.Curve3Pool3CrvJoint
open Blanc.Lift.Weth9.ClosedInstance (systemAddresses SystemCodes systemCode input)

/-- The accounts the closed block touches or whose content its premises read. -/
def touchedAccounts : List Adr :=
  [trader, poolAddr, c3crvAddr, coin0Addr, coin1Addr, coin2Addr, 4, 0] ++ systemAddresses

/-- `st` agrees with `P0` on the touched accounts. -/
def AgreesP0 (st : Jaune.State) : Prop := ∀ a ∈ touchedAccounts, st.get a = P0.get a

theorem p0_agrees : AgreesP0 P0 := fun _ _ => rfl

theorem p0_code4 : P0.getCode 4 = .empty := by decide +kernel

theorem p0_system (a : Adr) (ha : a ∈ systemAddresses) : P0.getCode a = systemCode := by
  revert a
  decide +kernel

section Agrees

variable {st : Jaune.State} (ag : AgreesP0 st)

include ag

theorem agrees_trader : st.get trader = P0.get trader := ag _ (by decide +kernel)
theorem agrees_pool : st.get poolAddr = P0.get poolAddr := ag _ (by decide +kernel)
theorem agrees_c3crv : st.get c3crvAddr = P0.get c3crvAddr := ag _ (by decide +kernel)
theorem agrees_coin0 : st.get coin0Addr = P0.get coin0Addr := ag _ (by decide +kernel)
theorem agrees_coin1 : st.get coin1Addr = P0.get coin1Addr := ag _ (by decide +kernel)
theorem agrees_coin2 : st.get coin2Addr = P0.get coin2Addr := ag _ (by decide +kernel)
theorem agrees_4 : st.get 4 = P0.get 4 := ag _ (by decide +kernel)
theorem agrees_system {a : Adr} (ha : a ∈ systemAddresses) : st.get a = P0.get a :=
  ag a (List.mem_append_right _ ha)

theorem agrees_getCode {a : Adr} (h : st.get a = P0.get a) : st.getCode a = P0.getCode a := by
  change (st.get a).code = (P0.get a).code
  rw [h]

theorem agrees_getStor {a : Adr} (h : st.get a = P0.get a) : st.getStor a = P0.getStor a := by
  change (st.get a).stor = (P0.get a).stor
  rw [h]

/-- **The exchange transaction's context** on the closed block's environment. -/
theorem exTxContext_of_agrees : ExTxContext (input st) where
  fork := rfl
  chain := rfl
  baseFee := rfl
  coinbase := rfl
  time := rfl
  room := by change 900000 ≤ 1000000; decide
  nonce := by change (st.get trader).nonce = 0; rw [agrees_trader ag, p0_trader]; rfl
  balance := by change (st.get trader).bal = traderEther; rw [agrees_trader ag, p0_trader]; rfl
  noCode := by change (st.get trader).code.size = 0; rw [agrees_trader ag, p0_trader]; rfl
  poolCode := by change (st.get poolAddr).code = _; rw [agrees_pool ag, p0_pool]; rfl
  poolStor := by change (st.get poolAddr).stor = _; rw [agrees_pool ag, p0_pool]; rfl
  coin0Code := by change (st.get coin0Addr).code = _; rw [agrees_coin0 ag, p0_coin0]; rfl
  coin1Code := by change (st.get coin1Addr).code = _; rw [agrees_coin1 ag, p0_coin1]; rfl
  coin2Code := by change (st.get coin2Addr).code = _; rw [agrees_coin2 ag, p0_coin2]; rfl
  c3crvCode := by change (st.get c3crvAddr).code = _; rw [agrees_c3crv ag, p0_c3crv]; rfl
  coin0Stor := by change (st.get coin0Addr).stor = _; rw [agrees_coin0 ag, p0_coin0]; rfl
  coin1Stor := by change (st.get coin1Addr).stor = _; rw [agrees_coin1 ag, p0_coin1]; rfl
  code4 := by change st.getCode 4 = _; rw [agrees_getCode ag (agrees_4 ag)]; exact p0_code4
  createdPool := Std.HashSet.not_mem_emptyWithCapacity
  createdCoin0 := Std.HashSet.not_mem_emptyWithCapacity
  createdCoin1 := Std.HashSet.not_mem_emptyWithCapacity

/-- The system fixture before the block. -/
theorem systemCodes_of_agrees : SystemCodes st := fun a ha => by
  rw [agrees_getCode ag (agrees_system ag ha)]
  exact p0_system a ha

/-- The identity precompile's account holds no code. -/
theorem code4_of_agrees : st.getCode 4 = .empty := by
  rw [agrees_getCode ag (agrees_4 ag)]
  exact p0_code4

/-- **The joint pool–3Crv checkpoint** at `st`, by U9(a)'s checker: it reads only the pool's and
3Crv's storage. -/
theorem joint_of_agrees :
    JointCheckpoint poolAddr c3crvAddr poolState (rowsState c3Base c3Rows) (c3Keys c3Rows) st := by
  apply checkJoint_sound
  unfold checkJoint
  rw [agrees_getStor ag (agrees_pool ag), agrees_getStor ag (agrees_c3crv ag)]
  exact p0_checkJoint

theorem poolInstalled_of_agrees :
    some (st.getCode poolAddr).toList = Curve3Pool.poolSem.image := by
  rw [agrees_getCode ag (agrees_pool ag)]
  exact p0_poolInstalled

theorem c3crvInstalled_of_agrees :
    some (st.getCode c3crvAddr).toList = Curve3Crv.c3crvSem.image := by
  rw [agrees_getCode ag (agrees_c3crv ag)]
  exact p0_c3crvInstalled

end Agrees

end Blanc.Composition.Curve3Pool3CrvInstance
