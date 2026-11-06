import Blanc.Composition.Curve3PoolJointRoot
import Blanc.Lift.Curve3Crv.Creation.Block.Slot
import Blanc.Lift.Curve3Crv.Creation.BlockMinter.Slot
import Blanc.Lift.Curve3Pool.Creation.Block.Slot

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
| `AnchoredBlock.wire` | the retained block is in Jaune's wire decoder's form | C |
| `Facts` | `JointDeployment`'s four remaining facts about the history | as there |

`wire` is here because `JointDeployment` asks for the exact `Tx` at each slot, and the roots fix a
slot only up to leading zero bytes of its signature scalars.

`AnchoredDeployment.toJoint` gives `JointDeployment`, so every theorem from it holds from the hashes.
-/

namespace Blanc.Composition.Curve3PoolBlockAnchor

open Jaune Blanc Blanc.ExecutionTrace Blanc.BlockHashBinding
open Blanc.Composition.Curve3PoolJointRoot

local notation "c3Adr" => Lift.Curve3Crv.Creation.tokenAddress
local notation "poolAdr" => Lift.Curve3Pool.Creation.poolAddress

/-- A retained `HistFork` mainnet block from `pre` that is the recorded block `r`. -/
structure AnchoredBlock (pre : BlockChain) (r : BlockRecord) where
  post : BlockChain
  trace : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post
  /-- The block has the recorded hash, under HASH-B. -/
  bound : HashBound trace r
  /-- The retained block is in the wire decoder's form. -/
  wire : trace.block.RlpCanonical

/-- **The anchored deployment.** 3Crv's creation block, the pool's and the minter assignment's, each
by its hash, in one mainnet history. -/
structure AnchoredDeployment where
  c3Pre : BlockChain
  c3 : AnchoredBlock c3Pre Lift.Curve3Crv.Creation.Block.record
  poolPre : BlockChain
  toPool : ConfiguredHistoryTraceIn HistFork mainnetChainConfig c3.post poolPre
  pool : AnchoredBlock poolPre Lift.Curve3Pool.Creation.Block.record
  minterPre : BlockChain
  toMinter : ConfiguredHistoryTraceIn HistFork mainnetChainConfig pool.post minterPre
  minter : AnchoredBlock minterPre Lift.Curve3Crv.Creation.BlockMinter.record

namespace AnchoredDeployment

variable (d : AnchoredDeployment)

/-- 3Crv's creation block, as recorded. -/
theorem c3Recorded : Recorded d.c3.trace 10809467 1599414946 76
    Lift.Curve3Crv.Creation.HistoricalTx.tx Lift.Curve3Crv.Creation.Block.slotReceipt :=
  Lift.Curve3Crv.Creation.Block.recorded d.c3.bound d.c3.wire

/-- The pool's creation block, as recorded. -/
theorem poolRecorded : Recorded d.pool.trace 10809473 1599414978 53
    Lift.Curve3Pool.Creation.HistoricalTx.tx Lift.Curve3Pool.Creation.Block.slotReceipt :=
  Lift.Curve3Pool.Creation.Block.recorded d.pool.bound d.pool.wire

/-- The minter assignment's block, as recorded. -/
theorem minterRecorded : Recorded d.minter.trace 10809482 1599415164 135
    Lift.Curve3Crv.SetMinter.tx Lift.Curve3Crv.Creation.BlockMinter.slotReceipt :=
  Lift.Curve3Crv.Creation.BlockMinter.recorded d.minter.bound d.minter.wire

/-- `JointDeployment`'s facts about the history, which no block hash decides. -/
structure Facts : Prop where
  /-- HASH-T for 3Crv over the whole history. -/
  fresh : Lift.Curve3Crv.FreshKeys (fun _ => False)
    (Lift.Curve3Crv.midTouchedKeysIn c3Adr
      ((MidHistoryTraceIn.tail d.c3.trace
        (d.c3.trace.bodyTrace.txSplitOfSlot d.c3Recorded.slot rfl)).append
        (((d.toPool.step d.pool.trace).append d.toMinter).step d.minter.trace)))
  /-- Every child of a pool frame keeps the pool's storage; every coin child keeps 3Crv's. -/
  callbacks : (((MidHistoryTraceIn.tail d.pool.trace
      (d.pool.trace.bodyTrace.txSplitOfSlot d.poolRecorded.slot rfl)).append d.toMinter).step
      d.minter.trace).FrameAdmitted poolAdr (Exec.derivEntry fun D =>
        Lift.Curve3Pool.PoolCallsKeep D ∧ Lift.Curve3Pool.PoolCoinCallsKeepToken D)
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
  c3Entry := .inr _
  c3Slot := d.c3Recorded.slot
  c3Decoded := rfl
  c3Receipt := _
  c3Lookup := d.c3Recorded.lookup
  c3Succeeded := d.c3Recorded.succeeded
  poolPre := d.poolPre
  toPool := d.toPool
  poolCompleted := d.pool.post
  poolBlock := d.pool.trace
  poolNumber := d.poolRecorded.number
  poolTime := d.poolRecorded.time
  poolEntry := .inr _
  poolSlot := d.poolRecorded.slot
  poolDecoded := rfl
  poolReceipt := _
  poolLookup := d.poolRecorded.lookup
  poolSucceeded := d.poolRecorded.succeeded
  minterPre := d.minterPre
  toMinter := d.toMinter
  minterCompleted := d.minter.post
  minterBlock := d.minter.trace
  minterNumber := d.minterRecorded.number
  minterTime := d.minterRecorded.time
  minterEntry := .inr _
  minterSlot := d.minterRecorded.slot
  minterDecoded := rfl
  minterReceipt := _
  minterLookup := d.minterRecorded.lookup
  minterSucceeded := d.minterRecorded.succeeded
  fresh := facts.fresh
  callbacks := facts.callbacks
  idEmpty := facts.idEmpty
  idNoFrame := facts.idNoFrame

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
