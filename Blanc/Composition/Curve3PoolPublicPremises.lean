import Blanc.Composition.Curve3PoolPublicObservers
import Blanc.Lift.Curve3Pool.Creation.HistoricalTxTrace
import Blanc.Lift.Curve3Crv.HistCommittedHistory
import Blanc.Lift.Curve3Crv.SetMinterTx
import Blanc.Lift.Dai.Cert
import Blanc.Lift.Usdt.Cert
import Blanc.Lift.Usdc.Proxy.Cert
import Blanc.Lift.Usdc.ImplV2.Cert
import Blanc.Lift.Usdc.ImplV2_1.Cert
import Blanc.Lift.Usdc.Impl.Cert
import Blanc.Lift.Usdc.Constants
import Blanc.ExecutionHistoryInAppend
import Blanc.ExecutionHistoryInPreCancun
import Blanc.ExecutionHistoryInFrameEnv

/-!
# The Curve 3pool's public statements: what they assume

The deployment record, the code the pool relies on at creation, the operators' powers restrained by
name, and the history's hash and signature facts. `Assumes` collects them; every headline takes it.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- A configured mainnet history over the forks the kit covers. -/
abbrev MainnetHistory := ConfiguredHistoryTraceIn HistFork mainnetChainConfig
/-- One configured mainnet block over those forks. -/
abbrev MainnetBlock := ConfiguredBlockTraceIn HistFork mainnetChainConfig

/-- Block `b` is mainnet block `n` at time `t`; slot `i` decodes to `tx`, whose receipt succeeded. -/
structure RecordedTx {pre post : BlockChain} (b : MainnetBlock pre post) (n t i : Nat) (tx : Tx) where
  number : b.block.header.number = n
  time : b.block.header.timestamp = t
  entry : Bytes ⊕ Tx
  slot : b.block.txs[i]? = some entry
  decoded : decodeTx b.fork.ruleSet entry = .ok tx
  receipt : Fin 5 × Receipt
  lookup : b.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt
  succeeded : receipt.2.succeeded = true

/-- A mainnet block holding a recorded transaction. -/
structure RecordedBlock (n t i : Nat) (tx : Tx) where
  pre : BlockChain
  post : BlockChain
  trace : MainnetBlock pre post
  recorded : RecordedTx trace n t i tx

namespace RecordedBlock

variable {n t i : Nat} {tx : Tx}

/-- The block's transactions cut at the recorded one. -/
noncomputable def cut (r : RecordedBlock n t i tx) : r.trace.bodyTrace.transactions.TxSplit i :=
  r.trace.bodyTrace.txSplitOfSlot r.recorded.slot r.recorded.decoded

/-- What remains of the block after the recorded transaction. -/
noncomputable def rest (r : RecordedBlock n t i tx) :
    MidHistoryTraceIn HistFork mainnetChainConfig r.cut.afterBenv r.post :=
  MidHistoryTraceIn.tail r.trace r.cut

end RecordedBlock

/-- **3Crv's creation, the pool's creation and the minter assignment**, in one mainnet history. -/
structure Deployment where
  c3 : RecordedBlock 10809467 1599414946 76 Lift.Curve3Crv.Creation.HistoricalTx.tx
  pool : RecordedBlock 10809473 1599414978 53 Lift.Curve3Pool.Creation.HistoricalTx.tx
  minter : RecordedBlock 10809482 1599415164 135 Lift.Curve3Crv.SetMinter.tx
  toPool : MainnetHistory c3.post pool.pre
  toMinter : MainnetHistory pool.post minter.pre

namespace Deployment

variable (d : Deployment) {future : BlockChain} (h : MainnetHistory d.minter.post future)

/-- Mainnet from the end of 3Crv's creation block to `future`. -/
noncomputable def sinceC3Block : MainnetHistory d.c3.post future :=
  ((d.toPool.step d.pool.trace).append d.toMinter).step d.minter.trace |>.append h

/-- Mainnet from right after 3Crv's creation to `future`. -/
noncomputable def sinceCreation : MidHistoryTraceIn HistFork mainnetChainConfig d.c3.cut.afterBenv future :=
  d.c3.rest.append (d.sinceC3Block h)

/-- Mainnet from right after the minter assignment to `future`. -/
noncomputable def sinceMinter : MidHistoryTraceIn HistFork mainnetChainConfig d.minter.cut.afterBenv future :=
  d.minter.rest.append h

end Deployment

/-- **The code the pool relies on, right after 3Crv's creation block**: one `eth_getCode` each. -/
structure StartingCode (w : State) : Prop where
  daiCode : w.getCode dai = Lift.Dai.code
  usdcCode : w.getCode usdc = Lift.Usdc.Proxy.code
  usdtCode : w.getCode usdt = Lift.Usdt.code
  idEmpty : w.getCode 4 = ByteArray.empty

/-! ## The operators -/

/-- The first argument word of a frame's calldata. -/
def firstArg (f : Exec.Frame) : B256 := Sevm.dataWord f.sevm 4

/-- USDT's owner confiscates the pool's balance: a committed `destroyBlackFunds(pool)`. -/
def DestroysBlackFunds (f : Exec.Frame) : Prop :=
  f.sevm.currentTarget = usdt ∧ Sevm.selector f.sevm = 0xf3bdc228 ∧ firstArg f = pool.toB256

/-- DAI's and USDC's signature-authorized entries, whose first argument names the signer. -/
def signedSelectors : List B256 :=
  [0x8fcbaf0c, 0xd505accf, 0x9fd5a6cf, 0xe3ee160e, 0xcf092995, 0xef55bec6, 0x88b7ab63]

/-- A committed coin call authorized by a signature naming the pool as the signer. -/
def SignedAsPool (f : Exec.Frame) : Prop :=
  (f.sevm.currentTarget = dai ∨ f.sevm.currentTarget = usdc) ∧
    Sevm.selector f.sevm ∈ signedSelectors ∧ firstArg f = pool.toB256

/-- The address USDC's proxy delegates to, in a state. -/
def usdcImplOf (w : State) : Adr := ((w.getStor usdc).get Usdc.implSlot).toAdr

/-- USDC's implementation in `w` holds one of the three audited versions. -/
def UsdcCertified (w : State) : Prop :=
  w.getCode (usdcImplOf w) = Usdc.ImplV2.code ∨ w.getCode (usdcImplOf w) = Usdc.ImplV2_1.code ∨
    w.getCode (usdcImplOf w) = Usdc.Impl.code

/-- USDC's implementation in `w` is V2_2, which reads bit 255 of a balance word as a blacklist flag. -/
def UsdcPacked (w : State) : Prop := w.getCode (usdcImplOf w) = Usdc.Impl.code

/-- **The operators' powers over the pool's balance entries**, each restrained by name, over a
history's committed frames. -/
structure PowersRestrained (frames : List Exec.Frame) : Prop where
  /-- Tether's owner never destroys the pool's USDT. -/
  noConfiscation : ∀ f ∈ frames, ¬ DestroysBlackFunds f
  /-- Tether's owner never redirects USDT through `deprecate`. -/
  notDeprecated : ∀ f ∈ frames, f.sevm.currentTarget = usdt →
    Usdt.flag20 ((f.pre.getStor usdt).get 10) = 0
  /-- Circle's proxy admin only upgrades USDC to a certified version. -/
  usdcCertified : ∀ f ∈ frames, f.sevm.currentTarget = usdc → UsdcCertified f.pre.state
  /-- Circle's minters never take the pool's whole USDC word to `2^255` before V2_2 reads that bit. -/
  usdcBelowFlag : ∀ f ∈ frames, f.sevm.currentTarget = usdc → ¬ UsdcPacked f.post.state →
    word f.post.state usdc (Usdc.balSlot pool) < 2 ^ 255
  /-- Nobody produces a signature recovering to the pool for DAI's or USDC's signed entries. -/
  noPoolSignature : ∀ f ∈ frames, ¬ SignedAsPool f

/-! ## Hashes and signatures -/

/-- The addresses a coin frame can name as a balance key: its caller and its first two arguments. -/
def namedKeys (f : Exec.Frame) : List B256 :=
  [f.sevm.caller.toB256, firstArg f, Sevm.dataWord f.sevm 36]

/-- No address a coin frame names shares a balance entry with the pool. Shape to be settled by U3. -/
def CoinKeysFresh (frames : List Exec.Frame) : Prop :=
  ∀ f ∈ frames, ∀ k : Fin 3, f.sevm.currentTarget = coinAt k → ∀ a ∈ namedKeys f,
    a ≠ pool.toB256 → coinEntry a.toAdr k ≠ coinEntry pool k

/-- **The history's hashes do not collide on what the proofs compare.** -/
structure HashesFresh (d : Deployment) {future : BlockChain}
    (h : MainnetHistory d.minter.post future) : Prop where
  /-- 3Crv's storage keys are collision-free over the history (HASH-T). -/
  c3Keys : Curve3Crv.FreshKeys (fun _ => False) (Curve3Crv.midTouchedKeysIn c3 (d.sinceCreation h))
  /-- The pool's balance entries in the coins are collision-free over the history. -/
  coinKeys : CoinKeysFresh (d.sinceCreation h).settledFrames
  /-- No contract creation lands on the identity precompile's address. -/
  noCreateAt4 : ∀ r ∈ (d.sinceC3Block h).rawFrames, r.sevm.codeAddress = none → r.sevm.currentTarget ≠ 4

/-- **What every headline assumes about mainnet.** -/
structure Assumes (d : Deployment) {future : BlockChain}
    (h : MainnetHistory d.minter.post future) : Prop where
  /-- The coins are their deployed bytes, and address 4 holds no code. -/
  code : StartingCode d.c3.post.state
  /-- The operators' powers are restrained. -/
  powers : PowersRestrained (d.sinceCreation h).settledFrames
  /-- The history's hashes do not collide. -/
  hashes : HashesFresh d h
  /-- No EIP-7702 authorization recovers to address 4. -/
  idNoAuthority : (d.sinceC3Block h).PragueNoAuthorityAt 4
  /-- No system contract's frame runs at the pool. -/
  sysAvoidsPool : ∀ r ∈ (d.sinceC3Block h).systemRawFrames, r.sevm.currentTarget ≠ pool

end Blanc.Composition.Curve3PoolPublic
