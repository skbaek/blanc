import Blanc.Composition.Curve3PoolPublicPremises
import Blanc.TransactionForward
import Blanc.CommonProofs.NoDel
import Blanc.ExecutionTrace
import Blanc.Lift.Usdc.Footprint

/-!
# The Curve 3pool's public statements: a transaction at a point of history

`Moment` is a point of mainnet right after a recorded transaction, where the history's facts apply.
`TxAdmitted` is what makes a direct signed call to the pool admissible there. `CoinsOpen` is the named
liveness powers not in force. Shared by `lp_exit` and `swap`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- **A point of mainnet after the minter assignment**: right after transaction `i` of `block`. -/
structure Moment (d : Deployment) where
  pre : BlockChain
  post : BlockChain
  history : MainnetHistory d.minter.post pre
  block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post
  i : Nat
  cut : block.bodyTrace.transactions.TxSplit i

namespace Moment

variable {d : Deployment} (m : Moment d)

/-- The history through the moment's whole block. -/
noncomputable def through : MainnetHistory d.minter.post m.post := m.history.step m.block

/-- The block environment at the moment. -/
noncomputable def benv : Benv := m.cut.afterBenv

/-- The block's running output at the moment. -/
noncomputable def bout : BlockOutput := m.cut.txBout

/-- The world at the moment. -/
noncomputable def world : State := m.benv.state

/-- The position the next transaction takes in the block. -/
noncomputable def nextIndex : Nat := m.cut.index + 1

end Moment

/-- A signed type-2 direct call to `pool`, with no value and no access list, at these fees. -/
structure TxForm (benv : Benv) (tx : Tx) (prio maxFee : Nat) : Prop where
  type : tx.type = .two benv.stat.chainId prio maxFee (some pool) []
  value : tx.value = 0
  tip : prio ≤ maxFee
  base : benv.stat.baseFeePerGas ≤ maxFee

/-- `E` signed `tx`, is ready to send it, and can pay for its gas. -/
structure SignerReady (benv : Benv) (tx : Tx) (E : Adr) (maxFee : Nat) : Prop where
  signed : recoverSender benv.stat.chainId tx = .ok E
  nonce : (benv.state.get E).nonce = tx.nonce ∧ tx.nonce ≠ UInt64.max
  noCode : (benv.state.getCode E).size = 0
  funds : tx.gas * maxFee ≤ (benv.state.get E).bal.toNat
  named : E ≠ 0 ∧ benv.stat.rules.isPrecomp E = false

/-- The transaction's gas limit covers `need` and fits the protocol's cap and the block's room. -/
structure GasRoom (benv : Benv) (bout : BlockOutput) (tx : Tx) (need : Nat) : Prop where
  enough : need ≤ tx.gas
  cap : tx.gas ≤ 16777216
  block : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed

/-- The contracts the call touches. -/
def parties (w : State) : List Adr := [pool, c3, dai, usdc, usdt, usdcImplOf w]

/-- The block's fee recipient is apart from the parties, so none starts warm. -/
def CoinbaseApart (benv : Benv) (E : Adr) : Prop :=
  benv.stat.coinbase ≠ E ∧ benv.stat.coinbase ∉ parties benv.state

/-- **`tx`, signed by `E`, is admissible at `benv` with `need` gas.** -/
structure TxAdmitted (benv : Benv) (bout : BlockOutput) (tx : Tx) (E : Adr) (need : Nat) : Prop where
  fork : CoveredFork benv.stat.fork
  form : ∃ prio maxFee, TxForm benv tx prio maxFee ∧ SignerReady benv tx E maxFee
  room : GasRoom benv bout tx need
  block : CoinbaseApart benv E

/-! ## The liveness powers -/

/-- USDT's transfer fee on an amount: `min(v * basisPointsRate / 10000, maximumFee)`. -/
def usdtFee (w : State) (v : Nat) : Nat := min (v * word w usdt 3 / 10000) (word w usdt 4)

/-- What a recipient nets from a transfer of `v` in coin `k`. -/
def netOf (w : State) (k : Fin 3) (v : Nat) : Nat := if k = 2 then v - usdtFee w v else v

/-- USDC is not paused: the flag at byte 20 of its slot 1. -/
def UsdcOpen (w : State) : Prop := Usdc.flag20 ((w.getStor usdc).get 1) = false

/-- USDC has not blacklisted `a`: bit 255 of its word, under V2_2. -/
def UsdcUnlisted (w : State) (a : Adr) : Prop :=
  Usdc.frozenBit ((w.getStor usdc).get (Usdc.balSlot a)) = false

/-- USDT is not paused and has not blacklisted `a`. -/
def UsdtOpen (w : State) (a : Adr) : Prop :=
  Usdt.flag20 ((w.getStor usdt).get 0) = 0 ∧ Usdt.listedByte (w.getStor usdt) a = 0

/-- `a`'s raw word in coin `k` stays below `2^255` after a credit of `v`, in every version's reading. -/
def CreditFits (w : State) (a : Adr) (k : Fin 3) (v : Nat) : Prop :=
  word w (coinAt k) (coinEntry a k) + v < 2 ^ 255

/-- USDT's fee arithmetic fits a word, its owner's credit fits, and the fee is at most the amount, on an amount `v`. -/
def UsdtFeeFits (w : State) (v : Nat) : Prop :=
  v * word w usdt 3 < 2 ^ 256 ∧ CreditFits w (Usdt.ownerOf (w.getStor usdt)) 2 (usdtFee w v) ∧ usdtFee w v ≤ v

/-- **No named liveness power is in force against the pool or `E`.** -/
structure CoinsOpen (w : State) (E : Adr) : Prop where
  /-- USDC runs V2_2, as it has since well before `CoveredFork`'s first block. -/
  usdcV22 : UsdcPacked w
  /-- V2_2's code is at the address `usdcV22` names: one read. -/
  usdcImplCode : w.getCode Usdc.usdcImpl = Usdc.Impl.code
  usdtOpen : UsdtOpen w pool
  usdcOpen : UsdcOpen w
  usdcParties : UsdcUnlisted w pool ∧ UsdcUnlisted w E
  /-- The pool is not USDC's proxy admin, whose calls the proxy refuses to forward: Circle's power. -/
  usdcAdmin : pool ≠ ((w.getStor usdc).get Usdc.adminSlot).toAdr

end Blanc.Composition.Curve3PoolPublic
