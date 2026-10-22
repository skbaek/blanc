import Blanc.BlockForward
import Blanc.Lift.Weth9.ClosedSigningData

/-!
The concrete chain envelope for the synthetic WETH9 applicability witness.
The checkpoint carries its supplied state unchanged and commits to its root.
The successor's commitments will be filled from the proved body result.
-/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.BlockForward Blanc.ExecutionTrace

def config : ChainConfig := ChainConfig.single 1 .bpo2

theorem config_valid : config.Valid := ChainConfig.single_valid 1 .bpo2

theorem config_forkAt (number t : Nat) : config.forkAt number t = .ok .bpo2 :=
  ChainConfig.single_forkAt 1 .bpo2 number t

theorem config_covered (number t : Nat) (fork : Fork)
    (h : config.forkAt number t = .ok fork) : CoveredFork fork := by
  rw [config_forkAt] at h
  cases h
  decide +kernel

def checkpointHeader (st : Jaune.State) : Header :=
  { parentHash := 0
    ommersHash := emptyOmmerHash
    coinbase := 0
    stateRoot := st.root
    txsRoot := getTransactionsRoot BlockOutput.init
    receiptRoot := getReceiptRoot BlockOutput.init
    bloom := List.replicate 256 0
    difficulty := 0
    number := 0
    gasLimit := 1000000
    gasUsed := 500000
    timestamp := 0
    extraData := []
    prevRandao := 0
    nonce := 0
    baseFeePerGas := some 1
    withdrawalsRoot := some (getWithdrawalsRoot BlockOutput.init)
    blobGasUsed := some 0
    excessBlobGas := some 0
    parentBeaconBlockRoot := some 0
    requestsHash := none
    blockAccessListHash := none
    slotNumber := none }

def checkpointBlock (st : Jaune.State) : Block :=
  { header := checkpointHeader st, txs := [], wds := [], ommers := [] }

def checkpoint (st : Jaune.State) : BlockChain :=
  { blocks := [checkpointBlock st], state := st, chainId := 1 }

def executionHeader (st : Jaune.State) : Header :=
  { checkpointHeader st with
    parentHash := (checkpointHeader st).hash
    number := 1
    gasUsed := 0
    timestamp := 1 }

def input (st : Jaune.State) : Benv :=
  initBenv .bpo2 (checkpoint st) (executionHeader st)

def depositBlock (st post : Jaune.State) (bout : BlockOutput) : Block :=
  { header := commitHeader Fork.bpo2.ruleSet (checkpointBlock st)
      (executionHeader st) post bout
    txs := [Sum.inr depositTx]
    wds := []
    ommers := [] }

theorem checkpoint_validContext {st : Jaune.State} (hcanon : st.Canonical) :
    (checkpoint st).ValidContext := by
  refine ⟨?_, hcanon, ?_, ?_⟩
  · simp only [checkpoint, ne_eq, List.cons_ne_self, not_false_eq_true]
  · simp only [BlockChain.RetainedHistoryValid, checkpoint, List.isChain_singleton,
      List.mem_singleton, forall_eq, List.length_singleton, List.head?_cons,
      Option.mem_some_iff, checkpointBlock, checkpointHeader, true_and]
    constructor
    · change (List.replicate 256 (0 : UInt8)).length = 256 ∧
        0 < 2 ^ 256 ∧ 0 < 2 ^ 256 ∧ 1000000 < 2 ^ 256 ∧
        500000 < 2 ^ 256 ∧ 0 < 2 ^ 256 ∧ (∀ b ∈ some 1, b < 2 ^ 256) ∧
        (∀ b ∈ some 0, b < 2 ^ 64) ∧ (∀ b ∈ some 0, b < 2 ^ 64)
      decide +kernel
    · refine Or.inr ?_
      intro b hb
      cases hb
      rfl
  · intro tip htip
    have ht : tip = checkpointBlock st := by
      simpa only [checkpoint, List.getLast?_singleton, Option.mem_def,
        Option.some.injEq] using htip.symm
    subst tip
    rfl

theorem depositBlock_input (st post : Jaune.State) (bout : BlockOutput) :
    initBenv .bpo2 (checkpoint st) (depositBlock st post bout).header = input st := by
  rfl

end Blanc.Lift.Weth9.ClosedInstance
