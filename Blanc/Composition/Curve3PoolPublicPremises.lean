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
import Blanc.Lift.Usdc.EntryJoin
import Blanc.Lift.Usdc.SignedLogs

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
is read at the pool's creation (`CircleRestrained.usdcCode`), since from there Circle's powers are restrained. -/
structure StartingCode (w : State) : Prop where
  /-- DAI is its deployed bytes. -/
  daiCode : w.getCode dai = Lift.Dai.code
  /-- USDT is its deployed bytes. -/
  usdtCode : w.getCode usdt = Lift.Usdt.code
  /-- Address 4 holds no code. -/
  idEmpty : w.getCode 4 = ByteArray.empty

/-! ## The operators -/

/-- **Tether's owner's powers over the pool's USDT entry**, restrained, over a history's retained frames. -/
structure TetherRestrained (w : State) (settled : List Exec.Frame) : Prop where
  /-- The owner never destroys the pool's USDT. -/
  noConfiscation : ∀ F ∈ coinFrames usdt (fun _ => True) settled, ¬ CurveCoins.Usdt.Confiscates pool F.sevm
  /-- USDT is not redirected when the pool is created. -/
  notRedirected : Usdt.flag20 ((w.getStor usdt).get 10) = 0
  /-- The owner never redirects USDT through `deprecate`. -/
  noDeprecate : ∀ F ∈ coinFrames usdt (fun _ => True) settled, Blanc.Sevm.selector F.sevm ≠ 0x0753c30c

/-- **USDC moves to V2_2 once, with the pool's whole word below the flag until then.** V2_2 reads that word's low 255 bits,
the earlier versions the whole word. -/
structure UsdcMovesOnce (w : State) (settled : List Exec.Frame) : Prop where
  /-- Once a frame reading USDC's ledger runs V2_2, every later one does. -/
  onward : ∀ before F after, settled = before ++ F :: after → F.sevm.currentTarget = usdc → Usdc.ChainObs usdc F →
    Usdc.V22At usdc F → ∀ G ∈ after, G.sevm.currentTarget = usdc → Usdc.ChainObs usdc G → Usdc.V22At usdc G
  /-- The pool's whole word is below the flag when it is created, and after every frame running the earlier versions. -/
  below : ((w.getStor usdc).get (Usdc.balSlot pool)).toNat < 2 ^ 255 ∧
    ∀ F ∈ coinFrames usdc (Usdc.ChainObs usdc) settled, ¬ Usdc.V22At usdc F →
      ((F.post.getStor usdc).get (Usdc.balSlot pool)).toNat < 2 ^ 255

/-- **Circle's powers over the pool's USDC entry**, restrained, from the pool's creation over a history's retained frames. -/
structure CircleRestrained (w : State) (settled : List Exec.Frame) : Prop where
  /-- USDC is behind its proxy's code when the pool is created. -/
  usdcCode : w.getCode usdc = Lift.Usdc.Proxy.code
  /-- The proxy admin only upgrades USDC to one of the three versions, and V2_2 finds its library. -/
  usdcCertified : Usdc.CertifiedSettled usdc settled
  /-- USDC moves to V2_2 once, with the pool's whole word below the bit that version reads as a flag. -/
  movesOnce : UsdcMovesOnce w settled

/-! ## Signatures -/

/-- The word `o`'s allowance to `s` sits at, in coin `k`. -/
def allowanceEntry (o s : Adr) : Fin 3 → B256
  | 0 => Dai.allowSlot o s
  | 1 => Usdc.allowSlot o s
  | 2 => Usdt.allowSlot o s

/-- **Nobody holds a key for the pool's address or for address 4.** -/
structure NoKeyHolder (w : State) (settled : List Exec.Frame) (noAuthority : Prop) : Prop where
  /-- DAI's `Approval` never names the pool as owner; a `permit` naming it would log that. -/
  daiNoApproval : ∀ F ∈ coinFrames dai (fun _ => True) settled, ¬ CurveCoins.Dai.LogsApprovalAs dai pool F
  /-- USDC's `AuthorizationUsed` never names the pool; a signed move from it would log that. -/
  usdcNoAuthorizationUsed : ∀ F ∈ coinFrames usdc (fun _ => True) settled, ∀ l ∈ F.post.logs,
    ¬ Usdc.AuthorizationUsedLog usdc pool l
  /-- USDC's `Approval` never names the pool as owner; a `permit` naming it would log that. -/
  usdcNoApproval : ∀ F ∈ coinFrames usdc (fun _ => True) settled, ¬ CurveCoins.FrameLogsApproval usdc pool F
  /-- The pool's allowance rows are empty when it is created: before its code exists only its key could
  set one. A universal over spenders, checkable for any finite set, not one RPC read. -/
  rowsAtCut : ∀ k g, wordsAt (coinAt k) w (allowanceEntry pool g k) = 0
  /-- No EIP-7702 authorization recovers to address 4. -/
  idNoAuthority : noAuthority

/-! ## Hashes -/

/-- **The pool's entries in each coin are collision-free over that coin's retained frames (HASH-T).** -/
structure CoinKeysHold (settled : List Exec.Frame) : Prop where
  /-- The pool's DAI entry is collision-free over DAI's retained frames. -/
  dai : CoinKeysFresh (WriteSite.wsRoot DaiWs.implWsAnn) 2 3 pool (coinFrames dai (fun _ => True) settled)
  /-- The pool's USDC entry is collision-free over USDC's retained frames. -/
  usdc : Usdc.UsdcKeysFreshInit usdc pool (Usdc.usdcFrames usdc settled)
  /-- The pool's USDT entry is collision-free over USDT's retained frames. -/
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
  tether : TetherRestrained d.poolCut.afterBenv.state (d.sincePool h).settledFrames
  /-- Circle's powers are restrained. -/
  circle : CircleRestrained d.poolCut.afterBenv.state (d.sincePool h).settledFrames
  /-- Nobody holds a key for the pool's address or for address 4. -/
  keys : NoKeyHolder d.poolCut.afterBenv.state (d.sincePool h).settledFrames
    ((d.sinceC3Block h).PragueNoAuthorityAt 4)
  /-- The history's hashes do not collide. -/
  hashes : HashesFresh d h
  /-- Each system contract has its code when its fork activates it, and nobody holds its key. -/
  system : h.SystemConfined

end Blanc.Composition.Curve3PoolPublic
