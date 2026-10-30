import Blanc.Lift.BeaconDeposit.HistDepositLogs
import Blanc.Lift.BeaconDeposit.HistoricalSeam
import Blanc.ExecutionRewardCredits

/-!
# The Beacon deposit contract from its actual deployment block

`BeaconDeploymentTo B` is the single deployment premise for the Beacon deposit contract at a
later modern block `B`. It joins the two halves that were previously separate:

* the deployment half, `actual_muir_deployment_to_D_of_receipt`: the retained Muir block
  11,052,984 whose body slot 2 decodes to the recorded signed creation transaction, its
  successful receipt at key 2, and its empty target logs;
* the history half, `historicalSeam_wholeSpan_solInv`: the configured historical history from
  the end of that block through the adopted Shanghai/Cancun/Prague seam anchors to `P`, then
  the unchanged modern history to `B`.

The installed code and the empty-history invariant at the deployment boundary `D`, which the
seam theorems take as premises, are theorems here, and so are the reward-credit budgets of the
historical span; the historical span needs no authority exclusion because it is pre-Prague.
What remains explicit is listed field by field below: one-block observations, the
configured-history traces, the `0x02` frame exclusions and the modern authority exclusions.
No frame can CREATE at an installed system contract: its present code collides.

Derived API: `.trace` / `.deposits` (the committed deposit nodes, in order, over the whole
retained span from `D` to `B`), `.solInv`, `.count` and `.root`.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace

/-- **The Beacon deposit deployment record**: the actual Muir creation block, the configured
history from it through the adopted seam anchors to a later modern block `B`, and the
remaining explicit exclusions of the seam. -/
structure BeaconDeploymentTo (B : BlockChain) where
  /-- The chain before the deployment block. -/
  pre : BlockChain
  /-- The chain ending with the deployment block (the seam's `D`). -/
  D : BlockChain
  /-- The seam's last Shanghai checkpoint. -/
  C : BlockChain
  /-- The chain ending with the first Cancun block. -/
  C1 : BlockChain
  /-- The seam's last Cancun checkpoint. -/
  P : BlockChain
  /-- C: the retained deployment block. -/
  block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D
  /-- A: body slot 2 of the deployment block decodes to the recorded creation transaction. -/
  atTwo : block.bodyTrace.decodedTxs[2]? = some Creation.HistoricalTx.tx
  /-- A: the receipt at key 2 of the deployment block. -/
  receipt : Fin 5 × Receipt
  lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (2 : Nat).toBytes)]? = some receipt
  succeeded : receipt.2.succeeded = true
  /-- A: the deployment block has no log at the deposit address. -/
  emptyLogs : block.blockOutput.blockLogs.filter
    (fun log => log.address == Creation.depositAddress) = []
  /-- C: the configured histories `D → C`, the first Cancun block, `C1 → P`, and `P → B`. -/
  dc : ConfiguredHistoryTraceIn HistFork mainnetChainConfig D C
  first : ConfiguredBlockTraceIn HistFork mainnetChainConfig C C1
  tail : ConfiguredHistoryTraceIn HistFork mainnetChainConfig C1 P
  modern : ConfiguredHistoryTrace mainnetChainConfig P B
  /-- A: the adopted seam anchors. Their `D` tip also pins the deployment block's number and
  timestamp, so the record carries no separate number/timestamp fields. -/
  anchors : HistoricalSeamAnchors D C P first.block
  /-- A (not yet in an adopted packet): `eth_getCode(0x02)` is empty after block 11,052,984. -/
  checkpointEmpty : D.state.getCode 2 = ByteArray.empty
  /-- D: no frame of the historical span without a code address, at any depth, targets
  `0x02` (a CREATE there needs a keccak preimage). The installed system contracts need no such
  field: CREATE collides with their present code. -/
  historicalNoFrame : ∀ root ∈ ((dc.step first).append tail).rawFrames,
    root.sevm.codeAddress = none → root.sevm.currentTarget ≠ (2 : Adr)
  /-- D: over the modern span `P → B`, no authorization recovers to a system contract or
  `0x02`, and no frame without a code address, at any depth, targets `0x02`. -/
  modernSystemNoAuthority : ∀ p ∈ systemContracts, modern.NoAuthorityAt p.1
  modernNoAuthority : modern.NoAuthorityAt 2
  modernNoFrame : ∀ root ∈ modern.rawFrames, root.sevm.codeAddress = none →
    root.sevm.currentTarget ≠ (2 : Adr)

namespace BeaconDeploymentTo

variable {B : BlockChain} (d : BeaconDeploymentTo B)

/-- The creation transaction's cut of the deployment block, from its decoded slot. -/
noncomputable def cut : d.block.bodyTrace.transactions.TxSplit 2 :=
  d.block.bodyTrace.transactions.splitAt 2 (by
    rw [indexedTransactions_length]
    exact (List.getElem?_eq_some_iff.mp d.atTwo).1)

/-- The whole retained span from the end of the deployment block to `B`. -/
def trace : ConfiguredHistoryTraceIn HistFork mainnetChainConfig d.D B :=
  ((d.dc.step d.first).append d.tail).append d.modern.toHistForkIn

/-- The committed deposit nodes of that span, in chronological order. -/
noncomputable def deposits : List B256 :=
  committedNodesIn Creation.depositAddress d.trace

/-- The adopted `D` anchor is the deployment block's own header. -/
theorem header : d.block.block.header.number = 11052984 ∧
    d.block.block.header.timestamp = 1602667372 := by
  obtain ⟨tip, last, number, timestamp, -, -⟩ := d.anchors.dTip
  have own : d.D.blocks.getLast? = some d.block.block :=
    (congrArg (fun chain : BlockChain => chain.blocks.getLast?) d.block.postEq).trans
      (appendBlock_getLast? _ _)
  obtain rfl := Option.some.inj (last.symm.trans own)
  exact ⟨number, timestamp⟩

/-- **The deployment boundary**: right after the actual deployment block the deposit
contract holds the certified runtime with the empty-history invariant. -/
theorem deployed : d.D.state.getCode Creation.depositAddress = code ∧
    SolInv (d.D.state.getStor Creation.depositAddress) [] :=
  (actual_muir_deployment_to_D_of_receipt d.block d.cut d.header.1 d.header.2 d.atTwo
    d.receipt d.lookup d.succeeded d.emptyLogs).2

/-- **The Beacon invariant from the actual deployment block**: at the later modern block `B`
the deposit contract's storage satisfies `SolInv` for exactly the deposits committed over the
whole retained span from the deployment block. -/
theorem solInv : SolInv (B.state.getStor Creation.depositAddress) d.deposits := by
  have rewards := ((d.dc.step d.first).append d.tail).rewardCreditsFunded
    BodyStageCapabilities.historical
  have whole := historicalSeam_wholeSpan_solInv (initialHistory := []) d.dc d.first d.tail
    d.modern d.anchors d.checkpointEmpty d.historicalNoFrame rewards
    d.modernSystemNoAuthority
    d.modernNoAuthority d.modernNoFrame d.deployed.1 d.deployed.2
  rw [List.nil_append] at whole
  exact whole

/-- **The deposit count word from the actual deployment block**: at `B` it is the number of
deposits committed since deployment, which stays below `2 ^ 32`. -/
theorem count : (B.state.getStor Creation.depositAddress).get solCountSlot =
    Nat.toB256 d.deposits.length ∧ d.deposits.length < 2 ^ 32 :=
  solCount_eq_of_solInv d.solInv

/-- **The stored deposit root from the actual deployment block**: at `B` the stored
accumulator's mixed root is the mixed root of exactly the deposits committed since deployment. -/
theorem root : BeaconDeposit.Acc.root Bytes.sha256
    (solAcc (B.state.getStor Creation.depositAddress)) =
      BeaconDeposit.mixedRootOf Bytes.sha256 d.deposits :=
  BeaconDeposit.root_correct _ _ _ d.solInv.2

end BeaconDeploymentTo

end Blanc.Lift.BeaconDeposit
