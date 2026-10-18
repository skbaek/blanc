import Blanc.Composition.UniswapV2PairWeth9CapstoneW0Slots
import Blanc.Composition.UniswapV2PairWeth9Block
import Blanc.Composition.UniswapV2PairWeth9Tx1Effects
import Blanc.Composition.UniswapV2PairWeth9Tx2
import Blanc.Composition.UniswapV2PairWeth9Joint

/-!
# Worlds agreeing with `W0` on the touched accounts

`AgreesW0 st`: `st` and `W0` hold the same account at the trader, `X`, the Pair, WETH9, the factory,
the coinbase `0` and the four system addresses.  From it (and nothing else of `st`): both
transactions' block-environment contexts, the system fixture before and after the block, the joint
checkpoint (given `SumNof st.bal`, the only global fact it carries) and the factory premises.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.Composition.UniswapV2PairWeth9Instance
  Blanc.Composition.UniswapV2PairWeth9Joint
open Blanc.Lift.Weth9.ClosedInstance (systemAddresses SystemCodes systemCode systemWorld input
  checkpoint)

/-- The accounts the closed instance's block touches. -/
def touchedAccounts : List Adr := [trader, tokenX, pair, weth, factory, 0] ++ systemAddresses

/-- `st` agrees with `W0` on every touched account. -/
def AgreesW0 (st : Jaune.State) : Prop := ∀ a ∈ touchedAccounts, st.get a = W0.get a

theorem get_insert_self (w : Jaune.State) (a : Adr) (ac : Acct) :
    State.get (w.insert a ac) a = ac := by
  unfold State.get
  exact Std.TreeMap.getD_insert_self

theorem get_insert_ne (w : Jaune.State) {a b : Adr} (h : a ≠ b) (ac : Acct) :
    State.get (w.insert a ac) b = w.get b := by
  unfold State.get
  rw [Std.TreeMap.getD_insert]
  exact ite_eq_right_iff.mpr (fun e => absurd (Std.LawfulEqCmp.eq_of_compare e) h)

theorem W0_trader : W0.get trader = { Acct.nil with bal := 10000000 } := get_insert_self _ _ _

theorem W0_tokenX : W0.get tokenX =
    { nonce := 1, bal := 0, stor := w0TokenStor, code := VyperNonreentrantDeployed.Token20.code } := by
  unfold W0
  rw [get_insert_ne _ (by decide +kernel), get_insert_ne _ (by decide +kernel), get_insert_self]

theorem W0_weth : W0.get weth =
    { nonce := 1, bal := 1000000, stor := w0WethStor, code := Weth9.code } := by
  unfold W0
  rw [get_insert_ne _ (by decide +kernel), get_insert_ne _ (by decide +kernel),
    get_insert_ne _ (by decide +kernel), get_insert_self]

theorem W0_pair : W0.get pair =
    { nonce := 1, bal := 0, stor := w0PairStor, code := UniswapV2Pair.code } := by
  unfold W0
  rw [get_insert_ne _ (by decide +kernel), get_insert_ne _ (by decide +kernel),
    get_insert_ne _ (by decide +kernel), get_insert_ne _ (by decide +kernel), get_insert_self]

theorem W0_system {a : Adr} (ha : a ∈ systemAddresses) : (W0.get a).code = systemCode := by
  have hs : a = beaconRootsAddress ∨ a = historyStorageAddress ∨
      a = withdrawalRequestPredeployAddress ∨ a = consolidationRequestPredeployAddress := by
    simpa only [systemAddresses, List.mem_cons, List.not_mem_nil, or_false] using ha
  unfold W0
  rw [get_insert_ne _ (by rcases hs with rfl | rfl | rfl | rfl <;> decide +kernel),
    get_insert_ne _ (by rcases hs with rfl | rfl | rfl | rfl <;> decide +kernel),
    get_insert_ne _ (by rcases hs with rfl | rfl | rfl | rfl <;> decide +kernel),
    get_insert_ne _ (by rcases hs with rfl | rfl | rfl | rfl <;> decide +kernel),
    get_insert_ne _ (by rcases hs with rfl | rfl | rfl | rfl <;> decide +kernel)]
  exact UniswapV2PairWeth9Instance.systemWorld_code a ha

section Agree

variable {st : Jaune.State} (ag : AgreesW0 st)
include ag

theorem agrees_trader : st.get trader = W0.get trader := ag trader (by decide +kernel)
theorem agrees_tokenX : st.get tokenX = W0.get tokenX := ag tokenX (by decide +kernel)
theorem agrees_pair : st.get pair = W0.get pair := ag pair (by decide +kernel)
theorem agrees_weth : st.get weth = W0.get weth := ag weth (by decide +kernel)
theorem agrees_factory : st.get factory = W0.get factory := ag factory (by decide +kernel)
theorem agrees_system {a : Adr} (ha : a ∈ systemAddresses) : st.get a = W0.get a :=
  ag a (List.mem_append_right _ ha)

/-- **`tx1`'s context** on the closed block's environment. -/
theorem tx1Context_of_agrees : Tx1Context (input st) 100000 1000000 where
  fork := rfl
  chain := rfl
  baseFee := rfl
  coinbase := rfl
  room := by change 50000 ≤ 1000000; decide
  nonce := by change (st.get trader).nonce = 0; rw [agrees_trader ag, W0_trader]; rfl
  balance := by change (st.get trader).bal = 10000000; rw [agrees_trader ag, W0_trader]
  noCode := by change (st.get trader).code.size = 0; rw [agrees_trader ag, W0_trader]; rfl
  code := by change (st.get tokenX).code = _; rw [agrees_tokenX ag, W0_tokenX]
  created := Std.HashSet.not_mem_emptyWithCapacity
  slotTrader := by
    change (st.get tokenX).stor.get _ = _; rw [agrees_tokenX ag, W0_tokenX]; exact w0TokenStor_trader
  slotPair := by
    change (st.get tokenX).stor.get _ = _; rw [agrees_tokenX ag, W0_tokenX]; exact w0TokenStor_pair
  covers := by decide
  pairNonzero := by decide
  noWrap := by unfold B256.Nof; decide

/-- `tx1`'s settled world. -/
abbrev tx1World (st : Jaune.State) : Jaune.State := tx1SettledState st 100000 1000000

omit ag in
theorem tx1World_other {a : Adr} (ht : trader ≠ a) (hx : tokenX ≠ a) (h0 : (0 : Adr) ≠ a) :
    (tx1World st).get a = st.get a :=
  tx1_settled_get_other st 100000 1000000 ht hx h0

theorem tx1World_trader : (tx1World st).get trader = { W0.get trader with nonce := 1, bal := 9936486 } := by
  rw [tx1_settled_get_trader st 100000 1000000 (by rw [agrees_trader ag, W0_trader]; decide),
    agrees_trader ag, W0_trader]
  rfl

/-- **`tx2`'s context** on the closed block's environment after `tx1`. -/
theorem tx2Context_of_agrees : Tx2Context ((input st).withState (tx1World st)) where
  fork := rfl
  chain := rfl
  baseFee := rfl
  coinbase := rfl
  time := rfl
  room := by change 331757 ≤ 1000000; decide
  nonce := by change ((tx1World st).get trader).nonce = 1; rw [tx1World_trader ag]
  balance := by change ((tx1World st).get trader).bal = 9936486; rw [tx1World_trader ag]
  noCode := by
    change ((tx1World st).get trader).code.size = 0; rw [tx1World_trader ag, W0_trader]; rfl
  pairCode := by
    change ((tx1World st).get pair).code = _
    rw [tx1World_other (by decide +kernel) (by decide +kernel) (by decide +kernel),
      agrees_pair ag, W0_pair]
  pairStor := by
    change ((tx1World st).get pair).stor = _
    rw [tx1World_other (by decide +kernel) (by decide +kernel) (by decide +kernel),
      agrees_pair ag, W0_pair]
  wethCode := by
    change ((tx1World st).get weth).code = _
    rw [tx1World_other (by decide +kernel) (by decide +kernel) (by decide +kernel),
      agrees_weth ag, W0_weth]
  wethPair := by
    change ((tx1World st).get weth).stor.get _ = _
    rw [tx1World_other (by decide +kernel) (by decide +kernel) (by decide +kernel),
      agrees_weth ag, W0_weth]
    exact w0WethStor_pair
  wethTrader := by
    change ((tx1World st).get weth).stor.get _ = _
    rw [tx1World_other (by decide +kernel) (by decide +kernel) (by decide +kernel),
      agrees_weth ag, W0_weth]
    exact w0WethStor_trader
  xCode := by
    change ((tx1World st).get tokenX).code = _
    rw [tx1_settled_get_tokenX, agrees_tokenX ag, W0_tokenX]
  xPair := by
    change ((tx1World st).get tokenX).stor.get _ = _
    rw [tx1_settled_get_tokenX, Stor.get_set_self]
    decide
  createdPair := Std.HashSet.not_mem_emptyWithCapacity
  createdWeth := Std.HashSet.not_mem_emptyWithCapacity
  createdX := Std.HashSet.not_mem_emptyWithCapacity

/-- The system fixture before the block. -/
theorem systemCodes_of_agrees : SystemCodes st := fun a ha => by
  change (st.get a).code = systemCode
  rw [agrees_system ag ha]
  exact W0_system ha

/-- The system fixture after both transactions: neither touches a system address. -/
theorem systemCodes_after : SystemCodes (tx2SettledState (tx1World st)) := fun a ha => by
  have hs : a = beaconRootsAddress ∨ a = historyStorageAddress ∨
      a = withdrawalRequestPredeployAddress ∨ a = consolidationRequestPredeployAddress := by
    simpa only [systemAddresses, List.mem_cons, List.not_mem_nil, or_false] using ha
  have ne : ∀ b, b = trader ∨ b = pair ∨ b = weth ∨ b = tokenX ∨ b = 0 → b ≠ a := by
    intro b hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;>
      decide +kernel
  change ((tx2SettledState (tx1World st)).get a).code = systemCode
  rw [tx2_settled_get_other _ (ne _ (Or.inl rfl)) (ne _ (Or.inr (Or.inl rfl)))
      (ne _ (Or.inr (Or.inr (Or.inl rfl)))) (ne _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))),
    tx1World_other (ne _ (Or.inl rfl)) (ne _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (ne _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), agrees_system ag ha]
  exact W0_system ha

/-- **The joint checkpoint** at `st`, transported from `W0`'s (`w0_jointCheckpoint`): every field
reads only the Pair's and WETH9's accounts, except `SumNof`. -/
theorem jointCheckpoint_of_agrees (bound : SumNof st.bal) :
    JointCheckpoint pair weth (FiniteCheckpoint.rowKeys w0WethRows)
      (UniswapV2Pair.pairKeys w0PairRows) (UniswapV2Pair.rowsState w0Base w0PairRows) .one st := by
  have j := w0_jointCheckpoint
  have code : ∀ a, st.get a = W0.get a → st.getCode a = W0.getCode a := fun a h => by
    change (st.get a).code = (W0.get a).code; rw [h]
  have stor : ∀ a, st.get a = W0.get a → st.getStor a = W0.getStor a := fun a h => by
    change (st.get a).stor = (W0.get a).stor; rw [h]
  have bal : ∀ a, st.get a = W0.get a → st.bal a = W0.bal a := fun a h => by
    change (st.get a).bal = (W0.get a).bal; rw [h]
  exact {
    pairCode := by rw [code _ (agrees_pair ag)]; exact j.pairCode
    pairRep := by rw [stor _ (agrees_pair ag)]; exact j.pairRep
    token := j.token
    unlocked := j.unlocked
    wethCode := by rw [code _ (agrees_weth ag)]; exact j.wethCode
    wethFoot := by rw [stor _ (agrees_weth ag), bal _ (agrees_weth ag)]; exact j.wethFoot
    sumNof := bound
    tracked := j.tracked
    noAllowance := by rw [stor _ (agrees_weth ag)]; exact j.noAllowance
    reserve := by rw [stor _ (agrees_weth ag)]; exact j.reserve
    apart := j.apart
    distinct := j.distinct
    notSystem := j.notSystem
    pairNonzero := j.pairNonzero
    wethNotPrecompile := j.wethNotPrecompile }

/-- **The factory premises** at `st` (A4/A14). -/
theorem factory_of_agrees :
    some (st.getCode (UniswapV2Pair.rowsState w0Base w0PairRows).factory).toList =
        UniswapV2Factory.factorySem.image ∧
      (UniswapV2Pair.rowsState w0Base w0PairRows).factory ≠ systemAddress := by
  refine ⟨?_, by decide +kernel⟩
  have h : st.getCode factory = W0.getCode factory := by
    change (st.get factory).code = (W0.get factory).code; rw [agrees_factory ag]
  change some (st.getCode factory).toList = _
  rw [h, UniswapV2Factory.factorySem_image]
  exact w0_factoryInstalled

end Agree

end Blanc.Composition.UniswapV2PairWeth9Capstone
