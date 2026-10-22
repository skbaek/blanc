import Blanc.Composition.Curve3Pool3CrvCheckpoint
import Blanc.Lift.Curve3Pool.Ladder
import Blanc.Lift.Curve3Crv.Ladder
import Blanc.Lift.Weth9.ClosedWorld
import Blanc.Lift.VyperNonreentrantDeployed.Token20.Check
import Blanc.LadderBase

/-!
# U9(b): the synthetic world `P0` of the closed exchange instance

`P0` is U9(a)'s synthetic world (`Curve3Pool3CrvJoint.world`: the pool's and 3Crv's storage at the
joint checkpoint) with the code installed: the certified 3pool runtime at `poolAddr`, the certified
3Crv runtime at `c3crvAddr`, the synthetic token `Token20` (`VyperNonreentrantDeployed.Token20`) at
the three coins standing in for DAI, USDC and USDT, the STOP fixture at the four system addresses
(`Weth9.ClosedInstance.systemWorld`), and the funded code-free trader (the published secp256k1 test
key `1`'s address) that signs the exchange.

The coins' ledgers back the pool's stored balances (`1000`, `2000`, `3000`); the trader holds
`1000` of coin 0 and has approved the pool for `100` of it (`exchangeDx`), the amount the closed
block's `exchange(0, 1, 100, 0)` pulls.

* `p0_checkJoint`, `p0_joint`: U9(a)'s checker accepts `P0` (kernel evaluation) and its soundness
  gives the joint checkpoint;
* `p0_poolInstalled`, `p0_c3crvInstalled`: the installed-code facts the composed headlines take;
* `p0_canonical`, `p0_sumNof`: the global facts a configured history needs.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The trader: the address of the published secp256k1 test key `1`. -/
def trader : Adr := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf

/-- The amount of coin 0 the closed block's `exchange` pulls. -/
def exchangeDx : Nat := 100

/-- The trader's ether: enough for the exchange's maximal fee. -/
def traderEther : B256 := 10000000

/-- Coin 0's ledger: the trader's and the pool's balances and the trader's allowance to the
pool. -/
def coin0Stor : Stor := Stor.ofList
  [(VyperNonreentrantDeployed.Token20.balSlot trader, 1000),
    (VyperNonreentrantDeployed.Token20.balSlot poolAddr, 1000),
    (VyperNonreentrantDeployed.Token20.allowSlot trader poolAddr, Nat.toB256 exchangeDx)]

/-- Coin 1's ledger: the pool's balance. -/
def coin1Stor : Stor := Stor.ofList
  [(VyperNonreentrantDeployed.Token20.balSlot poolAddr, 2000)]

/-- Coin 2's ledger: the pool's balance. -/
def coin2Stor : Stor := Stor.ofList
  [(VyperNonreentrantDeployed.Token20.balSlot poolAddr, 3000)]

/-- The pool's account: the certified runtime over U9(a)'s storage. -/
def poolAcct : Acct := { nonce := 1, bal := 0, stor := poolStor, code := Curve3Pool.code }

/-- 3Crv's account: the certified runtime over U9(a)'s storage. -/
def c3crvAcct : Acct := { nonce := 1, bal := 0, stor := c3Stor, code := Curve3Crv.code }

/-- A coin's account: the synthetic token's runtime over its ledger. -/
def coinAcct (σ : Stor) : Acct :=
  { nonce := 1, bal := 0, stor := σ, code := VyperNonreentrantDeployed.Token20.code }

/-- The trader's account: code-free, nonce `0`, funded. -/
def traderAcct : Acct := { Acct.nil with bal := traderEther }

/-- **The synthetic world `P0`.** -/
def P0 : Jaune.State :=
  ((((((Weth9.ClosedInstance.systemWorld.set poolAddr poolAcct).set c3crvAddr
    c3crvAcct).set coin0Addr (coinAcct coin0Stor)).set coin1Addr
    (coinAcct coin1Stor)).set coin2Addr (coinAcct coin2Stor)).set trader traderAcct)

/-- **U9(a)'s checker accepts `P0`** (kernel evaluation). -/
theorem p0_checkJoint : checkJoint poolAddr c3crvAddr poolState c3Rows c3Base P0 = true := by
  decide +kernel

/-- **`P0` satisfies the joint pool–3Crv checkpoint.** -/
theorem p0_joint :
    JointCheckpoint poolAddr c3crvAddr poolState (rowsState c3Base c3Rows) (c3Keys c3Rows) P0 :=
  checkJoint_sound p0_checkJoint

theorem p0_trader : P0.get trader = traderAcct := State.get_set_self _ _ _

theorem p0_pool : P0.get poolAddr = poolAcct := by
  unfold P0
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_ne _ (by decide +kernel), State.get_set_self]

theorem p0_c3crv : P0.get c3crvAddr = c3crvAcct := by
  unfold P0
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_self]

theorem p0_coin0 : P0.get coin0Addr = coinAcct coin0Stor := by
  unfold P0
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_ne _ (by decide +kernel), State.get_set_self]

theorem p0_coin1 : P0.get coin1Addr = coinAcct coin1Stor := by
  unfold P0
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_self]

theorem p0_coin2 : P0.get coin2Addr = coinAcct coin2Stor := by
  unfold P0
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_self]

/-- **The certified 3pool runtime is installed at the pool** (the CODE premise). -/
theorem p0_poolInstalled : some (P0.getCode poolAddr).toList = Curve3Pool.poolSem.image := by
  change some (P0.get poolAddr).code.toList = _
  rw [p0_pool]
  rfl

/-- **The certified 3Crv runtime is installed at 3Crv** (the CODE premise). -/
theorem p0_c3crvInstalled : some (P0.getCode c3crvAddr).toList = Curve3Crv.c3crvSem.image := by
  change some (P0.get c3crvAddr).code.toList = _
  rw [p0_c3crv]
  rfl

/-- `P0` is canonical (kernel evaluation). -/
theorem p0_canonical : P0.Canonical := by
  decide +kernel

theorem p0_get_set (w : Jaune.State) (a b : Adr) (ac : Acct) :
    State.get (w.set a ac) b = if a = b then ac else w.get b := by
  by_cases h : a = b
  · subst b
    rw [State.get_set_self, ite_eq_left rfl]
  · rw [State.get_set_ne _ h, ite_eq_right h]

/-- `P0`'s ether: only the trader holds any. -/
theorem p0_bal (a : Adr) : P0.bal a = if a = trader then traderEther else 0 := by
  change (P0.get a).bal = _
  unfold P0
  simp only [p0_get_set]
  by_cases ht : a = trader
  · subst a
    simp only [ite_true]
    rfl
  · rw [ite_eq_right (Ne.symm ht), ite_eq_right ht]
    split_ifs <;> first | rfl | exact Weth9.ClosedInstance.systemWorld_bal a

/-- **`P0`'s total ether is representable.** -/
theorem p0_sumNof : SumNof P0.bal := by
  have total := sum_eq_add_of_row_add (f := fun _ => (0 : B256)) (g := P0.bal) (x := trader)
    (m := traderEther.toNat)
    (by rw [p0_bal, ite_eq_left rfl]; decide +kernel)
    (fun a ha => by rw [p0_bal, ite_eq_right ha])
  have zero : sum (fun _ => (0 : B256)) = 0 := sumBelow_zero _
  rw [zero, Nat.zero_add] at total
  unfold SumNof
  rw [total]
  decide +kernel

end Blanc.Composition.Curve3Pool3CrvInstance
