import Blanc.Composition.Curve3PoolPublicObservers
import Blanc.Composition.Curve3PoolBlockAnchor
import Blanc.ExecutionHistoryInSystemConfined
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
import Blanc.Lift.CurveCoins.DaiLocality
import Blanc.Lift.CurveCoins.UsdtLocality
import Blanc.Lift.Usdc.EntryChain
import Blanc.Lift.Usdc.ImplV2Ws.Ann
import Blanc.Lift.Usdc.ImplV2_1Ws.Ann
import Blanc.Lift.Usdc.ImplWs.Ann

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
noncomputable def c3Cut := d.c3.trace.bodyTrace.txSplitOfItem d.c3Recorded.slot

/-- The minter assignment's block, cut at that transaction. -/
noncomputable def minterCut := d.minter.trace.bodyTrace.txSplitOfItem d.minterRecorded.slot

/-- Mainnet from the end of 3Crv's creation block to `future`. -/
noncomputable def sinceC3Block : MainnetHistory d.c3.post future :=
  ((d.toPool.step d.pool.trace).append d.toMinter).step d.minter.trace |>.append h

/-- Mainnet from right after 3Crv's creation to `future`. -/
noncomputable def sinceCreation : MidHistoryTraceIn HistFork mainnetChainConfig d.c3Cut.afterBenv future :=
  (MidHistoryTraceIn.tail d.c3.trace d.c3Cut).append (d.sinceC3Block h)

/-- The pool's creation block, cut at the creation transaction. -/
noncomputable def poolCut := d.pool.trace.bodyTrace.txSplitOfItem d.poolRecorded.slot

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

/-- **Tether's owner's powers over the pool's USDT entry**, restrained, over a history's retained frames. -/
structure TetherRestrained (settled : List Exec.Frame) : Prop where
  /-- The owner never destroys the pool's USDT. -/
  noConfiscation : ∀ F ∈ coinFrames usdt (fun _ => True) settled, ¬ CurveCoins.Usdt.Confiscates pool F.sevm
  /-- The owner never redirects USDT through `deprecate`. -/
  notDeprecated : ∀ F ∈ coinFrames usdt (fun _ => True) settled, CurveCoins.Usdt.NotDeprecated usdt F

/-- **Circle's powers over the pool's USDC entry**, restrained, over a history's retained frames. -/
structure CircleRestrained (settled : List Exec.Frame) : Prop where
  /-- USDC stays behind its proxy's code. -/
  proxyStays : ∀ f ∈ settled, f.pre.getCode usdc = Lift.Usdc.Proxy.code
  /-- The proxy admin only upgrades USDC to one of the three versions, and V2_2 finds its library. -/
  usdcCertified : ∀ f ∈ settled, f.sevm.currentTarget = usdc → Usdc.UsdcCertified f.pre usdc
  /-- An initializer does not lower the pool's entry. -/
  initializers : Usdc.InitializerKeeps usdc pool settled
  /-- The rescuer's call does not re-enter USDC. -/
  rescueQuiet : Usdc.RescueQuiet usdc settled
  /-- The pool's whole word is below `2^255` where USDC moves to V2_2, which reads that bit. -/
  belowFlag : Usdc.BelowFlagAt usdc pool (coinFrames usdc (Usdc.EntryObs usdc) settled)

/-! ## Signatures -/

/-- The word `o`'s allowance to `s` sits at, in coin `k`. -/
def allowanceEntry (o s : Adr) : Fin 3 → B256
  | 0 => Dai.allowSlot o s
  | 1 => Usdc.allowSlot o s
  | 2 => Usdt.allowSlot o s

/-- USDC's signature-authorized entries, whose first argument names the signer. -/
def usdcSignedSelectors : List B256 := [0xd505accf, 0x9fd5a6cf, 0xe3ee160e, 0xcf092995, 0xef55bec6, 0x88b7ab63]

/-- A USDC message authorized by a signature naming `h` as the signer. -/
def UsdcSignedAs (h : Adr) (e : Sevm) : Prop :=
  Sevm.selector e ∈ usdcSignedSelectors ∧ (Sevm.dataWord e 4).toAdr = h

/-- **Nobody holds a key for the pool's address or for address 4.** -/
structure NoKeyHolder (w : State) (settled : List Exec.Frame) (noAuthority : Prop) : Prop where
  /-- DAI's `Approval` never names the pool as owner; a `permit` naming it would log that. -/
  daiNoApproval : ∀ F ∈ coinFrames dai (fun _ => True) settled, ¬ CurveCoins.Dai.LogsApprovalAs dai pool F
  /-- No signature recovers to the pool for USDC's signed entries. -/
  usdcNoSignature : ∀ F ∈ coinFrames usdc (fun _ => True) settled, ¬ UsdcSignedAs pool F.sevm
  /-- The pool's allowance rows are empty when it is created: before its code exists only its key could
  set one. A universal over spenders, checkable for any finite set, not one RPC read. -/
  rowsAtCut : ∀ k g, wordsAt (coinAt k) w (allowanceEntry pool g k) = 0
  /-- No EIP-7702 authorization recovers to address 4. -/
  idNoAuthority : noAuthority

/-! ## Hashes -/

/-- The sites USDC's three versions can write. -/
def usdcSites : List WriteSite.Site :=
  WriteSite.wsRoot Usdc.ImplV2Ws.implWsAnn ++ WriteSite.wsRoot Usdc.ImplV2_1Ws.implWsAnn ++
    WriteSite.wsRoot Usdc.ImplWs.implWsAnn

/-- **The pool's entries in each coin are collision-free over that coin's retained frames (HASH-T).** -/
structure CoinKeysHold (settled : List Exec.Frame) : Prop where
  dai : CoinKeysFresh (WriteSite.wsRoot DaiWs.implWsAnn) 2 3 pool (coinFrames dai (fun _ => True) settled)
  usdc : CoinKeysFresh usdcSites 9 10 pool (coinFrames usdc (fun _ => True) settled)
  usdt : CurveCoins.Usdt.UsdtKeysFresh pool (coinFrames usdt (fun _ => True) settled)

/-- **The history's hashes do not collide on what the proofs compare.** -/
structure HashesFresh (d : Deployment) {future : BlockChain}
    (h : MainnetHistory d.minter.post future) : Prop where
  /-- 3Crv's storage keys are collision-free over the history (HASH-T). -/
  c3Keys : Curve3Crv.FreshKeys (fun _ => False) (Curve3Crv.midTouchedKeysIn c3 (d.sinceCreation h))
  /-- The pool's entries in the coins are collision-free (HASH-T). -/
  coinKeys : CoinKeysHold (d.sincePool h).settledFrames
  /-- No contract creation lands on the identity precompile's address. -/
  noCreateAt4 : ∀ r ∈ (d.sinceC3Block h).rawFrames, r.sevm.codeAddress = none → r.sevm.currentTarget ≠ 4

/-- **What every headline assumes about mainnet.** -/
structure Assumes (d : Deployment) {future : BlockChain}
    (h : MainnetHistory d.minter.post future) : Prop where
  /-- DAI and USDT are their deployed bytes, and address 4 holds no code. -/
  code : StartingCode d.c3.post.state
  /-- Tether's owner's powers are restrained. -/
  tether : TetherRestrained (d.sincePool h).settledFrames
  /-- Circle's powers are restrained. -/
  circle : CircleRestrained (d.sincePool h).settledFrames
  /-- Nobody holds a key for the pool's address or for address 4. -/
  keys : NoKeyHolder d.poolCut.afterBenv.state (d.sincePool h).settledFrames
    ((d.sinceC3Block h).PragueNoAuthorityAt 4)
  /-- The history's hashes do not collide. -/
  hashes : HashesFresh d h
  /-- Each system contract has its code when its fork activates it, and nobody holds its key. -/
  system : h.SystemConfined

end Blanc.Composition.Curve3PoolPublic
