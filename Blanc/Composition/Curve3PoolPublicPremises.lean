import Blanc.Composition.Curve3PoolPublicObservers
import Blanc.Composition.Curve3PoolBlockAnchor
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

The anchored deployment, the code the pool relies on at creation, the operators' powers restrained by
name, and the history's hash and signature facts. `Assumes` collects them; every headline takes it.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- A configured mainnet history over the forks the kit covers. -/
abbrev MainnetHistory := ConfiguredHistoryTraceIn HistFork mainnetChainConfig

/-- **3Crv's creation block, the pool's and the minter assignment's, each by its hash**, in one mainnet
history. -/
abbrev Deployment := Curve3PoolBlockAnchor.AnchoredDeployment

namespace Deployment

variable (d : Deployment) {future : BlockChain} (h : MainnetHistory d.minter.post future)

/-- 3Crv's creation block, cut at the creation transaction. -/
noncomputable def c3Cut := d.c3.trace.bodyTrace.txSplitOfSlot d.c3Recorded.slot rfl

/-- The minter assignment's block, cut at that transaction. -/
noncomputable def minterCut := d.minter.trace.bodyTrace.txSplitOfSlot d.minterRecorded.slot rfl

/-- Mainnet from the end of 3Crv's creation block to `future`. -/
noncomputable def sinceC3Block : MainnetHistory d.c3.post future :=
  ((d.toPool.step d.pool.trace).append d.toMinter).step d.minter.trace |>.append h

/-- Mainnet from right after 3Crv's creation to `future`. -/
noncomputable def sinceCreation : MidHistoryTraceIn HistFork mainnetChainConfig d.c3Cut.afterBenv future :=
  (MidHistoryTraceIn.tail d.c3.trace d.c3Cut).append (d.sinceC3Block h)

/-- The pool's creation block, cut at the creation transaction. -/
noncomputable def poolCut := d.pool.trace.bodyTrace.txSplitOfSlot d.poolRecorded.slot rfl

/-- Mainnet from right after the pool's creation to `future`. -/
noncomputable def sincePool : MidHistoryTraceIn HistFork mainnetChainConfig d.poolCut.afterBenv future :=
  (MidHistoryTraceIn.tail d.pool.trace d.poolCut).append
    ((d.toMinter.step d.minter.trace).append h)

/-- Mainnet from right after the minter assignment to `future`. -/
noncomputable def sinceMinter : MidHistoryTraceIn HistFork mainnetChainConfig d.minterCut.afterBenv future :=
  (MidHistoryTraceIn.tail d.minter.trace d.minterCut).append h

end Deployment

/-- **The code the pool relies on, right after 3Crv's creation block**: one `eth_getCode` each. USDC's
stays with Circle's powers, because its proxy delegates. -/
structure StartingCode (w : State) : Prop where
  daiCode : w.getCode dai = Lift.Dai.code
  usdtCode : w.getCode usdt = Lift.Usdt.code
  idEmpty : w.getCode 4 = ByteArray.empty

/-! ## The operators -/

/-- The first argument word of a frame's calldata. -/
def firstArg (f : Exec.Frame) : B256 := Sevm.dataWord f.sevm 4

/-- USDT's owner confiscates the pool's balance: a committed `destroyBlackFunds(pool)`. -/
def DestroysBlackFunds (f : Exec.Frame) : Prop :=
  f.sevm.currentTarget = usdt ∧ Sevm.selector f.sevm = 0xf3bdc228 ∧ firstArg f = pool.toB256

/-- The address USDC's proxy delegates to, in a state. -/
def usdcImplOf (w : State) : Adr := ((w.getStor usdc).get Usdc.implSlot).toAdr

/-- USDC's implementation in `w` holds one of the three audited versions. -/
def UsdcCertified (w : State) : Prop :=
  w.getCode (usdcImplOf w) = Usdc.ImplV2.code ∨ w.getCode (usdcImplOf w) = Usdc.ImplV2_1.code ∨
    w.getCode (usdcImplOf w) = Usdc.Impl.code

/-- USDC's implementation in `w` is V2_2, which reads bit 255 of a balance word as a blacklist flag. -/
def UsdcPacked (w : State) : Prop := w.getCode (usdcImplOf w) = Usdc.Impl.code

/-- USDC's initializer entries, each run once at an upgrade. -/
def usdcInitializers : List B256 := [0x3357162b, 0xd608ea64, 0x2fc81e09, 0x430239b4]

/-- **Tether's owner's powers over the pool's USDT entry**, restrained, over a history's frames. -/
structure TetherRestrained (settled : List Exec.Frame) (raw : List Exec.Deriv) : Prop where
  /-- The owner never destroys the pool's USDT. -/
  noConfiscation : ∀ f ∈ settled, ¬ DestroysBlackFunds f
  /-- The owner never redirects USDT through `deprecate`. -/
  notDeprecated : ∀ r ∈ raw, r.sevm.currentTarget = usdt →
    Usdt.flag20 ((r.devm.getStor usdt).get 10) = 0
  /-- The owner never hands ownership to the pool, whose balance `redeem` would then debit. -/
  ownerNotPool : ∀ f ∈ settled, f.sevm.currentTarget = usdt →
    Usdt.ownerOf (f.pre.getStor usdt) ≠ pool

/-- **Circle's powers over the pool's USDC entry**, restrained, over a history's frames. -/
structure CircleRestrained (settled : List Exec.Frame) (raw : List Exec.Deriv) : Prop where
  /-- USDC stays behind its proxy's code. -/
  proxyStays : ∀ r ∈ raw, r.devm.getCode usdc = Lift.Usdc.Proxy.code
  /-- The proxy admin only upgrades USDC to a certified version. -/
  usdcCertified : ∀ r ∈ raw, r.sevm.currentTarget = usdc → UsdcCertified r.devm.state
  /-- An initializer leaves the pool's USDC entry alone. Shape to be settled by U3. -/
  initializerBoundary : ∀ f ∈ settled, f.sevm.currentTarget = usdc →
    Sevm.selector f.sevm ∈ usdcInitializers → word f.post.state usdc (Usdc.balSlot pool) =
      word f.pre.state usdc (Usdc.balSlot pool)
  /-- The minters never take the pool's whole word to `2^255` before V2_2 reads that bit. -/
  belowFlag : ∀ f ∈ settled, f.sevm.currentTarget = usdc → ¬ UsdcPacked f.post.state →
    word f.post.state usdc (Usdc.balSlot pool) < 2 ^ 255

/-! ## Signatures -/

/-- The word `o`'s allowance to `s` sits at, in coin `k`. -/
def allowanceEntry (o s : Adr) : Fin 3 → B256
  | 0 => Dai.allowSlot o s
  | 1 => Usdc.allowSlot o s
  | 2 => Usdt.allowSlot o s

/-- DAI's and USDC's signature-authorized entries, whose first argument names the signer. -/
def signedSelectors : List B256 :=
  [0x8fcbaf0c, 0xd505accf, 0x9fd5a6cf, 0xe3ee160e, 0xcf092995, 0xef55bec6, 0x88b7ab63]

/-- A committed coin call authorized by a signature naming the pool as the signer. -/
def SignedAsPool (f : Exec.Frame) : Prop :=
  (f.sevm.currentTarget = dai ∨ f.sevm.currentTarget = usdc) ∧ f.sevm.isStatic = false ∧
    Sevm.selector f.sevm ∈ signedSelectors ∧ firstArg f = pool.toB256

/-- **Nobody holds a key for the pool's address or for address 4.** -/
structure NoKeyHolder (w : State) (settled : List Exec.Frame) (noAuthority : Prop) : Prop where
  /-- No signature recovers to the pool for a coin's signed entries. -/
  noSignature : ∀ f ∈ settled, ¬ SignedAsPool f
  /-- The pool's allowance rows are empty when it is created: before its code exists only its key could
  set one. A universal over spenders, checkable for any finite set, not one RPC read. -/
  rowsAtCut : ∀ k g, word w (coinAt k) (allowanceEntry pool g k) = 0
  /-- No EIP-7702 authorization recovers to address 4. -/
  idNoAuthority : noAuthority

/-! ## Hashes -/

/-- The addresses a coin frame can name as a balance key: its caller and its first two arguments. -/
def namedKeys (f : Exec.Frame) : List B256 :=
  [f.sevm.caller.toB256, firstArg f, Sevm.dataWord f.sevm 36]

/-- No address a coin frame names shares a balance entry with the pool. Shape to be settled by U3. -/
def CoinKeysFresh (frames : List Exec.Frame) : Prop :=
  ∀ f ∈ frames, ∀ k : Fin 3, f.sevm.currentTarget = coinAt k → ∀ a ∈ namedKeys f,
    a.toAdr ≠ pool → coinEntry a.toAdr k ≠ coinEntry pool k

/-- **The history's hashes do not collide on what the proofs compare.** -/
structure HashesFresh (d : Deployment) {future : BlockChain}
    (h : MainnetHistory d.minter.post future) : Prop where
  /-- 3Crv's storage keys are collision-free over the history (HASH-T). -/
  c3Keys : Curve3Crv.FreshKeys (fun _ => False) (Curve3Crv.midTouchedKeysIn c3 (d.sinceCreation h))
  /-- The pool's balance entries in the coins are collision-free over the history (HASH-T). -/
  coinKeys : CoinKeysFresh (d.sincePool h).settledFrames
  /-- No contract creation lands on the identity precompile's address. -/
  noCreateAt4 : ∀ r ∈ (d.sinceC3Block h).rawFrames, r.sevm.codeAddress = none → r.sevm.currentTarget ≠ 4

/-- **What every headline assumes about mainnet.** -/
structure Assumes (d : Deployment) {future : BlockChain}
    (h : MainnetHistory d.minter.post future) : Prop where
  /-- DAI and USDT are their deployed bytes, and address 4 holds no code. -/
  code : StartingCode d.c3.post.state
  /-- Tether's owner's powers are restrained. -/
  tether : TetherRestrained (d.sincePool h).settledFrames (d.sincePool h).rawFrames
  /-- Circle's powers are restrained. -/
  circle : CircleRestrained (d.sincePool h).settledFrames (d.sincePool h).rawFrames
  /-- Nobody holds a key for the pool's address or for address 4. -/
  keys : NoKeyHolder d.poolCut.afterBenv.state (d.sincePool h).settledFrames
    ((d.sinceC3Block h).PragueNoAuthorityAt 4)
  /-- The history's hashes do not collide. -/
  hashes : HashesFresh d h
  /-- No system contract's frame runs at the pool. -/
  sysAvoidsPool : ∀ r ∈ (d.sinceC3Block h).systemRawFrames, r.sevm.currentTarget ≠ pool

end Blanc.Composition.Curve3PoolPublic
