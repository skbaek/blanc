import Blanc.Composition.Curve3Pool3CrvTxData
import Blanc.Composition.Curve3Pool3CrvExRoot
import Blanc.BlockForward
import Blanc.TransactionForward
import Blanc.CodeDelegation

/-!
# U9(b): the exchange transaction enters the pool's `exchange` frame

`ExTxContext benv`: what the exchange transaction needs of its block environment (BPO2, chain 1,
base fee 1, coinbase `0`, timestamp `1`, gas room; the trader's nonce `0`, ether `traderEther` and
no code; the pool's code and U9(a)'s storage; `Token20` at the three coins over their ledgers; no
code at the identity precompile's address; none of the pool and the coins created in this block).

`ExFrame sevm b`: what the pool's `exchange` frame sees at its entry machine.

* `ex_intrinsic`: intrinsic gas `21600`, calldata floor `22500`;
* `ex_prepared_frame`: the message the transaction prepares enters an `ExFrame` over the debited
  world `exDebitState`;
* `exFrame_root`: from an `ExFrame` entry, the facts the exchange-root theorems take
  (`exRoot_children`, `exRoot_raw`).
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint

theorem ex_rules_bpo2 {s : BenvStat} (h : s.fork = .bpo2) : s.rules = Fork.bpo2.ruleSet := by
  unfold BenvStat.rules
  rw [h]

/-- **What the exchange transaction needs of its block environment.** -/
structure ExTxContext (benv : Benv) : Prop where
  fork : benv.stat.fork = .bpo2
  chain : benv.stat.chainId = 1
  baseFee : benv.stat.baseFeePerGas = 1
  coinbase : benv.stat.coinbase = 0
  time : benv.stat.time = 1
  room : 900000 ≤ benv.stat.blockGasLimit
  nonce : (benv.state.get trader).nonce = 0
  balance : benv.state.bal trader = traderEther
  noCode : (benv.state.getCode trader).size = 0
  poolCode : benv.state.getCode poolAddr = Curve3Pool.code
  poolStor : benv.state.getStor poolAddr = poolStor
  coin0Code : benv.state.getCode coin0Addr = VyperNonreentrantDeployed.Token20.code
  coin1Code : benv.state.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code
  coin2Code : benv.state.getCode coin2Addr = VyperNonreentrantDeployed.Token20.code
  c3crvCode : benv.state.getCode c3crvAddr = Curve3Crv.code
  coin0Stor : benv.state.getStor coin0Addr = coin0Stor
  coin1Stor : benv.state.getStor coin1Addr = coin1Stor
  code4 : benv.state.getCode 4 = .empty
  createdPool : poolAddr ∉ benv.createdAccounts
  createdCoin0 : coin0Addr ∉ benv.createdAccounts
  createdCoin1 : coin1Addr ∉ benv.createdAccounts

/-- **What the pool's `exchange` frame sees at its entry.** -/
structure ExFrame (sevm : Sevm) (b : Devm) : Prop where
  code : sevm.code = Curve3Pool.code
  fork : sevm.benvStat.fork = .bpo2
  caller : sevm.caller = trader
  target : sevm.currentTarget = poolAddr
  static : sevm.isStatic = false
  data : sevm.data = exchangeData
  value : sevm.value = 0
  depth : sevm.depth = 1024
  time : sevm.benvStat.time = 1
  stack : b.stack = []
  memory : b.memory = Mem.empty
  gas : b.gasLeft = 878400
  poolStor : b.state.getStor poolAddr = poolStor
  poolCode : b.state.getCode poolAddr = Curve3Pool.code
  coin0Code : b.state.getCode coin0Addr = VyperNonreentrantDeployed.Token20.code
  coin1Code : b.state.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code
  coin2Code : b.state.getCode coin2Addr = VyperNonreentrantDeployed.Token20.code
  c3crvCode : b.state.getCode c3crvAddr = Curve3Crv.code
  coin0Stor : b.state.getStor coin0Addr = coin0Stor
  coin1Stor : b.state.getStor coin1Addr = coin1Stor
  code4 : b.state.getCode 4 = .empty
  warm4 : (4 : Adr) ∈ b.accessedAddresses
  createdPool : poolAddr ∉ b.createdAccounts
  createdCoin0 : coin0Addr ∉ b.createdAccounts
  createdCoin1 : coin1Addr ∉ b.createdAccounts
  spill : b.mach.stateGas.spilled = 0 ∧ b.mach.stateGas.committedSpill = 0
  error : b.error = none
  refund : b.refundCounter = 0
  origPool : (getOrigAcct sevm poolAddr).stor = Curve3Pool3CrvJoint.poolStor
  origCoin0 : (getOrigAcct sevm coin0Addr).stor = Curve3Pool3CrvInstance.coin0Stor
  origCoin1 : (getOrigAcct sevm coin1Addr).stor = Curve3Pool3CrvInstance.coin1Stor

/-- After admission: the trader's nonce bumped and the maximal fee `900000 × 2` taken. -/
def exDebitState (st : Jaune.State) : Jaune.State :=
  (st.incrNonce trader).setBal trader (traderEther - 1800000)

theorem ex_gas (v : Nat) (r s : Bytes) : (exchangeTx v r s).gas = 900000 := rfl

theorem ex_value (v : Nat) (r s : Bytes) : (exchangeTx v r s).value = 0 := rfl

theorem ex_intrinsic {rules : ForkRules} (v : Nat) (r s : Bytes)
    (hsg : rules.stateGas = none) (hbase : rules.gas.txBase = 21000)
    (hfloor : rules.gas.floorTokenCost = 10) :
    calculateIntrinsicCost rules (exchangeTx v r s) trader = (21600, 22500) := by
  rw [calculateIntrinsicCost_two_call hsg (by rfl)]
  simp only [exchangeTx, hbase, hfloor]
  decide +kernel

theorem exDebitState_get_ne (st : Jaune.State) {a : Adr} (ha : trader ≠ a) :
    ((exDebitState st).get a).stor = (st.get a).stor ∧
      ((exDebitState st).get a).code = (st.get a).code := by
  unfold exDebitState
  rw [State.setBal_get_ne ha, State.incrNonce_get_stor, ite_eq_right (fun h => ha h.1)]
  exact ⟨rfl, by rw [State.incrNonce_get_code]⟩

/-- The pool's runtime is no EIP-7702 delegation designator. -/
theorem getDelegatedCodeAddress_pool : getDelegatedCodeAddress Curve3Pool.code = none :=
  getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel)

theorem ex_warm4 :
    (4 : Adr) ∈ (Std.HashSet.ofList [(0 : Adr)]).insertMany
      (Fork.bpo2.ruleSet.precompiles ++ [trader, poolAddr]) := by
  rw [Std.HashSet.mem_insertMany_list]
  exact .inr (by decide +kernel)

/-- **The exchange's message enters the `exchange` frame** over the debited world. -/
theorem ex_prepared_frame {benv : Benv} (ctx : ExTxContext benv)
    (v : Nat) (r s : Bytes) (debit : Jaune.State) (msg : Msg) (after : Benv)
    (hdebit : (benv.state.incrNonce trader).subBal trader
      ((exchangeTx v r s).gas * (min 1 (8 - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas)).toB256 = some debit)
    (hprepare : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction (exchangeTx v r s) 0 trader
        (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        21600 []) (exchangeTx v r s) = .ok msg)
    (hentry : msg.benvAfterTransfer = .ok after) :
    ExFrame (initSevm (msg.withBenv after)) (initDevm (msg.withBenv after)) ∧
      (initDevm (msg.withBenv after)).state = exDebitState benv.state := by
  have debitEq : debit = exDebitState benv.state := by
    obtain ⟨_, equation⟩ := State.of_subBal hdebit
    rw [State.incrNonce_bal, ctx.balance, ctx.baseFee] at equation
    have fee : traderEther - Nat.toB256 ((exchangeTx v r s).gas * (min 1 (8 - 1) + 1)) =
        traderEther - 1800000 := by
      rw [ex_gas]
      decide +kernel
    rw [fee] at equation
    exact equation
  subst debit
  rw [prepareMessage_call (by rfl)] at hprepare
  have msgEq := (Except.ok.inj hprepare).symm
  subst msg
  rw [Msg.benvAfterTransfer_of_value_zero (by rfl)] at hentry
  have afterEq := (Except.ok.inj hentry).symm
  subst after
  have hP := exDebitState_get_ne benv.state (a := poolAddr) (by decide +kernel)
  have h0 := exDebitState_get_ne benv.state (a := coin0Addr) (by decide +kernel)
  have h1 := exDebitState_get_ne benv.state (a := coin1Addr) (by decide +kernel)
  have h2 := exDebitState_get_ne benv.state (a := coin2Addr) (by decide +kernel)
  have h4 := exDebitState_get_ne benv.state (a := 4) (by decide +kernel)
  have h3 := exDebitState_get_ne benv.state (a := c3crvAddr) (by decide +kernel)
  refine ⟨⟨?code, ctx.fork, rfl, rfl, rfl, rfl, rfl, rfl, ctx.time, rfl, rfl, ?gas, ?pstor,
    ?pcode, ?c0, ?c1, ?c2, ?c3, ?s0, ?s1, ?k4, ?w4, ctx.createdPool, ctx.createdCoin0,
    ctx.createdCoin1, ⟨rfl, rfl⟩, rfl, rfl, ?o0, ?o1, ?o2⟩, rfl⟩
  case o0 => exact ctx.poolStor
  case o1 => exact ctx.coin0Stor
  case o2 => exact ctx.coin1Stor
  case code =>
    change ((exDebitState benv.state).get poolAddr).code = _
    rw [hP.2]
    exact ctx.poolCode
  case gas =>
    rw [initDevm_gasLeft]
    change (exchangeTx v r s).gas - 21600 = 878400
    rw [ex_gas]
  case pstor =>
    change ((exDebitState benv.state).get poolAddr).stor = _
    rw [hP.1]
    exact ctx.poolStor
  case pcode =>
    change ((exDebitState benv.state).get poolAddr).code = _
    rw [hP.2]
    exact ctx.poolCode
  case c0 =>
    change ((exDebitState benv.state).get coin0Addr).code = _
    rw [h0.2]
    exact ctx.coin0Code
  case c1 =>
    change ((exDebitState benv.state).get coin1Addr).code = _
    rw [h1.2]
    exact ctx.coin1Code
  case c2 =>
    change ((exDebitState benv.state).get coin2Addr).code = _
    rw [h2.2]
    exact ctx.coin2Code
  case c3 =>
    change ((exDebitState benv.state).get c3crvAddr).code = _
    rw [h3.2]
    exact ctx.c3crvCode
  case s0 =>
    change ((exDebitState benv.state).get coin0Addr).stor = _
    rw [h0.1]
    exact ctx.coin0Stor
  case s1 =>
    change ((exDebitState benv.state).get coin1Addr).stor = _
    rw [h1.1]
    exact ctx.coin1Stor
  case k4 =>
    change ((exDebitState benv.state).get 4).code = _
    rw [h4.2]
    exact ctx.code4
  case w4 =>
    change (4 : Adr) ∈ (Std.HashSet.ofList [benv.stat.coinbase]).insertMany
      (benv.stat.rules.precompiles ++ [trader, poolAddr])
    rw [ctx.coinbase, ex_rules_bpo2 ctx.fork]
    exact ex_warm4

/-! ## From the frame's entry to the exchange-root theorems -/

theorem p0_checkPool : checkPool poolStor poolState = true := by
  decide +kernel

/-- The pool's coins as its storage names them. -/
def exCoinAdr : Fin 3 → Adr
  | 0 => coin0Addr
  | 1 => coin1Addr
  | 2 => coin2Addr

theorem poolStor_coin : ∀ k : Fin 3, (poolStor.get (coinSlot k)).toAdr = exCoinAdr k := by
  decide +kernel

theorem exCoinAdr_ne : ∀ k : Fin 3, exCoinAdr k ≠ poolAddr ∧ exCoinAdr k ≠ 4 := by
  decide +kernel

theorem exCoinAdr_notPrecomp : ∀ k : Fin 3, ¬ Fork.bpo2.ruleSet.isPrecomp (exCoinAdr k) := by
  decide +kernel

section Frame

variable {sevm : Sevm} {b : Devm} (h : ExFrame sevm b)
include h

theorem exFrame_coin (k : Fin 3) : exCoin sevm b k = exCoinAdr k := by
  unfold exCoin
  change ((b.state.getStor sevm.currentTarget).get (coinSlot k)).toAdr = _
  rw [h.target, h.poolStor]
  exact poolStor_coin k

theorem exFrame_fork : CoveredFork sevm.benvStat.fork := by rw [h.fork]; exact .bpo2

theorem exFrame_len : 4 ≤ sevm.data.length ∧ sevm.data.length < 2 ^ 256 := by
  rw [h.data]; decide +kernel

theorem exFrame_sel : Sevm.selector sevm = selExchange := by
  unfold Sevm.selector Sevm.dataWord
  rw [h.data]
  decide +kernel

theorem exFrame_abs : Abstracts (b.getStor sevm.currentTarget) poolState := by
  change Abstracts (b.state.getStor sevm.currentTarget) poolState
  rw [h.target, h.poolStor]
  exact (checkPool_sound p0_checkPool).abs

theorem exFrame_checkpoint : Checkpoint (b.getStor sevm.currentTarget) poolState := by
  change Checkpoint (b.state.getStor sevm.currentTarget) poolState
  rw [h.target, h.poolStor]
  exact checkPool_sound p0_checkPool

theorem exFrame_id : IdReady sevm b := by
  refine ⟨?_, h.warm4, ?_, exFrame_fork h⟩
  · change getDelegatedCodeAddress (b.state.getCode 4) = none
    rw [h.code4]
    decide +kernel
  · unfold BenvStat.rules
    rw [h.fork]
    decide +kernel

theorem exFrame_gas : b.gasMeasure < 2 ^ 256 := by
  rw [Devm.gasMeasure_def, h.gas, h.spill.1, h.spill.2]
  decide

theorem exFrame_coins (k : Fin 3) :
    b.getCode (exCoin sevm b k) = VyperNonreentrantDeployed.Token20.code ∧
      exCoin sevm b k ≠ sevm.currentTarget ∧ exCoin sevm b k ≠ 4 := by
  rw [exFrame_coin h, h.target]
  refine ⟨?_, (exCoinAdr_ne k).1, (exCoinAdr_ne k).2⟩
  change b.state.getCode (exCoinAdr k) = _
  match k with
  | 0 => exact h.coin0Code
  | 1 => exact h.coin1Code
  | 2 => exact h.coin2Code

theorem exFrame_poolCode : b.getCode sevm.currentTarget = Curve3Pool.code := by
  change b.state.getCode _ = _
  rw [h.target]
  exact h.poolCode

theorem exFrame_coinPre (k : Fin 3) : ¬ sevm.benvStat.rules.isPrecomp (exCoin sevm b k) := by
  rw [exFrame_coin h]
  unfold BenvStat.rules
  rw [h.fork]
  exact exCoinAdr_notPrecomp k

/-- **The exchange frame's children** (`exRoot_children` at an `ExFrame` entry): all at the coins,
keeping the pool's storage and the code at `4`. -/
theorem exFrame_children {post : Devm} (exc : Exec 0 sevm b (.ok post)) :
    (∀ c ∈ Exec.childFrames exc, ExCoinChild sevm b c) ∧
      PoolCallsKeep ⟨0, sevm, b, .ok post, exc⟩ ∧
      ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4 :=
  exRoot_children exc h.code (exFrame_fork h) (exFrame_len h).1 (exFrame_len h).2 (exFrame_sel h)
    (exFrame_abs h) (exFrame_coinPre h) (exFrame_poolCode h) (exFrame_id h) h.stack h.memory (exFrame_gas h) (exFrame_coins h)

/-- **The raw frames the exchange frame enters** (`exRoot_raw` at an `ExFrame` entry). -/
theorem exFrame_raw {post : Devm} (exc : Exec 0 sevm b (.ok post)) :
    ∀ r ∈ Exec.rawFrameDescendants exc, ∃ c ∈ Exec.childFrames exc, ExCoinChild sevm b c ∧
      r.sevm = c.sevm ∧ c.sevm.code = VyperNonreentrantDeployed.Token20.code ∧
      Exec.rawFrameDescendants r.exc = [] :=
  exRoot_raw exc h.code (exFrame_fork h) (exFrame_len h).1 (exFrame_len h).2 (exFrame_sel h)
    (exFrame_abs h) (exFrame_coinPre h) (exFrame_poolCode h) (exFrame_id h) h.stack h.memory (exFrame_gas h) (exFrame_coins h)

end Frame

end Blanc.Composition.Curve3Pool3CrvInstance
