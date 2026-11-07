import Blanc.Composition.Curve3PoolJointRoot
import Blanc.Lift.Curve3Crv.Creation.Block.Slot
import Blanc.Lift.Curve3Crv.Creation.BlockMinter.Slot
import Blanc.Lift.Curve3Pool.Creation.Block.Slot
import Blanc.ExecutionHistoryInSystemConfined

/-!
# The joint deployment anchored at three block hashes

`AnchoredDeployment` is `JointDeployment`'s history with each of the three blocks given by its hash:
3Crv's creation block 10,809,467, the pool's 10,809,473 and the minter assignment's 10,809,482. Each
block's number and time, its body slot and its receipt are theorems (`Slot`'s `recorded`). The
generated records hold no trusted data: the kernel checks that each header hashes to its block hash
and that each pair of entry lists produces that header's roots.

| premise | content | class |
|---|---|---|
| `AnchoredBlock.bound.hash` | the block's hash, three times | A: the only fetched fact about the blocks |
| `AnchoredBlock.bound` HASH-B | no collision on the two values each binding compares | finite, trace-local |
| `AnchoredBlock.trace`, `toPool`, `toMinter` | configured `HistFork` traces | C |
| `Facts` | `JointDeployment`'s four remaining facts about the history | as there |

`AnchoredDeployment.toJoint` gives `JointDeployment`, so every theorem from it holds from the hashes.
-/

namespace Blanc.Composition.Curve3PoolBlockAnchor

open Jaune Blanc Blanc.ExecutionTrace Blanc.BlockHashBinding
open Blanc.Composition.Curve3PoolJointRoot

local notation "c3Adr" => Lift.Curve3Crv.Creation.tokenAddress
local notation "poolAdr" => Lift.Curve3Pool.Creation.poolAddress

/-- A retained `HistFork` mainnet block from `pre` that is the recorded block `r`. -/
structure AnchoredBlock (pre : BlockChain) (r : BlockRecord) where
  /-- The chain after the block. -/
  post : BlockChain
  /-- The block's configured trace from the chain before to the chain after. -/
  trace : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post
  /-- The block has the recorded hash, under HASH-B. -/
  bound : HashBound trace r

/-- **The anchored deployment.** 3Crv's creation block, the pool's and the minter assignment's, each
by its hash, in one mainnet history. -/
structure AnchoredDeployment where
  /-- The chain before 3Crv's creation block. -/
  c3Pre : BlockChain
  /-- 3Crv's creation block, by its hash. -/
  c3 : AnchoredBlock c3Pre Lift.Curve3Crv.Creation.Block.record
  /-- The chain before the pool's creation block. -/
  poolPre : BlockChain
  /-- The mainnet history from 3Crv's creation to the chain before the pool's creation. -/
  toPool : ConfiguredHistoryTraceIn HistFork mainnetChainConfig c3.post poolPre
  /-- The pool's creation block, by its hash. -/
  pool : AnchoredBlock poolPre Lift.Curve3Pool.Creation.Block.record
  /-- The chain before the minter assignment's block. -/
  minterPre : BlockChain
  /-- The mainnet history from the pool's creation to the chain before the minter assignment. -/
  toMinter : ConfiguredHistoryTraceIn HistFork mainnetChainConfig pool.post minterPre
  /-- The minter assignment's block, by its hash. -/
  minter : AnchoredBlock minterPre Lift.Curve3Crv.Creation.BlockMinter.record

namespace AnchoredDeployment

variable (d : AnchoredDeployment)

/-- 3Crv's creation block, as recorded. -/
theorem c3Recorded : Recorded d.c3.trace 10809467 1599414946 76
    Lift.Curve3Crv.Creation.HistoricalTx.tx Lift.Curve3Crv.Creation.Block.slotReceipt :=
  Lift.Curve3Crv.Creation.Block.recorded d.c3.bound

/-- The pool's creation block, as recorded. -/
theorem poolRecorded : Recorded d.pool.trace 10809473 1599414978 53
    Lift.Curve3Pool.Creation.HistoricalTx.tx Lift.Curve3Pool.Creation.Block.slotReceipt :=
  Lift.Curve3Pool.Creation.Block.recorded d.pool.bound

/-- The minter assignment's block, as recorded. -/
theorem minterRecorded : Recorded d.minter.trace 10809482 1599415164 135
    Lift.Curve3Crv.SetMinter.tx Lift.Curve3Crv.Creation.BlockMinter.slotReceipt :=
  Lift.Curve3Crv.Creation.BlockMinter.recorded d.minter.bound

/-- `JointDeployment`'s facts about the history, which no block hash decides. -/
structure Facts : Prop where
  /-- HASH-T for 3Crv over the whole history. -/
  fresh : Lift.Curve3Crv.FreshKeys (fun _ => False)
    (Lift.Curve3Crv.midTouchedKeysIn c3Adr
      ((MidHistoryTraceIn.tail d.c3.trace
        (d.c3.trace.bodyTrace.txSplitOfItem d.c3Recorded.slot)).append
        (((d.toPool.step d.pool.trace).append d.toMinter).step d.minter.trace)))
  /-- The coins are their deployed bytes and the operators' two powers are restrained. -/
  coins : Curve3PoolCoinKeep.CoinsHold (((MidHistoryTraceIn.tail d.pool.trace
      (d.pool.trace.bodyTrace.txSplitOfItem d.poolRecorded.slot)).append d.toMinter).step
      d.minter.trace)
    (Lift.Curve3Pool.adrOf (Lift.Curve3Pool.Creation.coinsN.get 0))
    (Lift.Curve3Pool.adrOf (Lift.Curve3Pool.Creation.coinsN.get 1))
    (Lift.Curve3Pool.adrOf (Lift.Curve3Pool.Creation.coinsN.get 2))
  /-- The identity precompile's account holds no code just after 3Crv's creation block. -/
  idEmpty : d.c3.post.state.getCode 4 = ByteArray.empty
  /-- No CREATE frame of the history lands at the identity precompile's address. -/
  idNoFrame : ∀ root ∈ (((d.toPool.step d.pool.trace).append d.toMinter).step d.minter.trace).rawFrames,
    root.sevm.codeAddress = none → root.sevm.currentTarget ≠ 4

variable {d}

/-- **The anchored deployment gives the joint deployment record.** -/
noncomputable def toJoint (facts : d.Facts) : JointDeployment where
  c3Pre := d.c3Pre
  c3Completed := d.c3.post
  c3Block := d.c3.trace
  c3Number := d.c3Recorded.number
  c3Time := d.c3Recorded.time
  c3Slot := d.c3Recorded.slot
  c3Receipt := _
  c3Lookup := d.c3Recorded.lookup
  c3Succeeded := d.c3Recorded.succeeded
  poolPre := d.poolPre
  toPool := d.toPool
  poolCompleted := d.pool.post
  poolBlock := d.pool.trace
  poolNumber := d.poolRecorded.number
  poolTime := d.poolRecorded.time
  poolSlot := d.poolRecorded.slot
  poolReceipt := _
  poolLookup := d.poolRecorded.lookup
  poolSucceeded := d.poolRecorded.succeeded
  minterPre := d.minterPre
  toMinter := d.toMinter
  minterCompleted := d.minter.post
  minterBlock := d.minter.trace
  minterNumber := d.minterRecorded.number
  minterTime := d.minterRecorded.time
  minterSlot := d.minterRecorded.slot
  minterReceipt := _
  minterLookup := d.minterRecorded.lookup
  minterSucceeded := d.minterRecorded.succeeded
  fresh := facts.fresh
  coins := facts.coins
  idEmpty := facts.idEmpty
  idNoFrame := facts.idNoFrame

/-! ## System stages -/

/-- The whole history after 3Crv's creation block, to the end of the minter block. -/
noncomputable def toMinterEnd (d : AnchoredDeployment) :
    ConfiguredHistoryTraceIn HistFork mainnetChainConfig d.c3.post d.minter.post :=
  ((d.toPool.step d.pool.trace).append d.toMinter).step d.minter.trace

/-- Everything up to the minter assignment is before Cancun. -/
theorem forks (d : AnchoredDeployment) : d.toMinterEnd.ForksSatisfy PreCancun := by
  have last : d.minter.post.blocks.getLast? = some d.minter.trace.block :=
    (congrArg (fun chain : BlockChain => chain.blocks.getLast?) d.minter.trace.postEq).trans
      (appendBlock_getLast? _ _)
  exact d.toMinterEnd.forksPreCancun_of_mainnet_tip last
    (by rw [d.minterRecorded.time]; decide)

/-- The pool is outside the system addresses. -/
theorem pool_not_system : poolAdr ∉ systemTargets := by decide +kernel

/-- **No system frame from 3Crv's creation block on targets an account outside the system addresses**,
from the confinement of the history after the minter assignment; before it there is no system frame.
For the pool (`pool_not_system`) and the coins (`Lift.CurveCoins.coins_not_system`), this one premise
gives what each asked separately. -/
theorem system_ne (d : AnchoredDeployment) {future : BlockChain}
    {h : ConfiguredHistoryTraceIn HistFork mainnetChainConfig d.minter.post future}
    (confined : h.SystemConfined) {T : Adr} (notSystem : T ∉ systemTargets) :
    ∀ r ∈ (d.toMinterEnd.append h).systemRawFrames, r.sevm.currentTarget ≠ T := by
  rw [ConfiguredHistoryTraceIn.systemRawFrames_append,
    d.toMinterEnd.systemRawFrames_nil_of_preCancun d.forks, List.nil_append]
  exact confined.system_ne notSystem

/-- **The mid history from just after the pool's creation is confined**, the form the coins' receipt
laws take through `MidHistoryTraceIn.system_ne`. -/
theorem sincePool_confined (d : AnchoredDeployment) {future : BlockChain}
    {h : ConfiguredHistoryTraceIn HistFork mainnetChainConfig d.minter.post future}
    (confined : h.SystemConfined) :
    ((MidHistoryTraceIn.tail d.pool.trace
      (d.pool.trace.bodyTrace.txSplitOfItem d.poolRecorded.slot)).append
        ((d.toMinter.step d.minter.trace).append h)).SystemConfined := by
  have forks := d.forks
  have poolForks := ((ConfiguredHistoryTraceIn.ForksSatisfy_append _ _ _).mp forks.1)
  have rest : (d.toMinter.step d.minter.trace).ForksSatisfy PreCancun := ⟨poolForks.2, forks.2⟩
  refine MidHistoryTraceIn.systemConfined_append
    (.tail d.pool.trace (d.pool.trace.bodyTrace.txSplitOfItem d.poolRecorded.slot))
    (d.pool.trace.systemConfined_of_preCancun poolForks.1.2) _ ?_ ?_
  · exact (ConfiguredHistoryTraceIn.SystemCodeAtOpenings_append _ _).mpr
      ⟨ConfiguredHistoryTraceIn.systemCodeAtOpenings_of_preCancun _ rest, confined.openings⟩
  · intro p hp
    exact (ConfiguredHistoryTraceIn.PragueNoAuthorityAt_append _ _ _).mpr
      ⟨ConfiguredHistoryTraceIn.pragueNoAuthorityAt_of_prePrague _
        (rest.mono fun _ hf => hf.toPrePrague) _, confined.noAuthority p hp⟩

/-- **The joint deployment root, from three block hashes.** `joint_root` at the anchored deployment:
no block's number, time, slot or receipt is an input. -/
theorem joint_root_anchored (facts : d.Facts) :
    some ((toJoint facts).cutState.getCode poolAdr).toList = Lift.Curve3Pool.poolSem.image ∧
    some ((toJoint facts).cutState.getCode c3Adr).toList = Lift.Curve3Crv.c3crvSem.image ∧
    ∃ ps cs, Lift.Curve3Crv.InvRunBy Lift.Curve3Crv.OwnerAnswerH
        (Lift.Curve3Crv.Creation.curveDeployedState Lift.Curve3Crv.Creation.deployer)
        (toJoint facts).c3Invocations cs ∧
      Curve3Pool3CrvJoint.JointCheckpoint poolAdr c3Adr ps cs (toJoint facts).c3Keys
        (toJoint facts).cutState :=
  joint_root (toJoint facts)

end AnchoredDeployment

end Blanc.Composition.Curve3PoolBlockAnchor
