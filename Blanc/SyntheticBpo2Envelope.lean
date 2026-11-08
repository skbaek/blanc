import Blanc.BlockForward

/-!
Fixed synthetic BPO2-from-genesis chain envelope.

The chain ID is 1 and the gas limit is 1,000,000. The checkpoint retains its
supplied state and commits to that root; its successor header is independent
of transaction bodies. This fixture makes no mainnet or arbitrary-fork claim.
-/

namespace Blanc.SyntheticBpo2Envelope

open Jaune Blanc Blanc.BlockForward Blanc.ExecutionTrace

def config : ChainConfig := ChainConfig.single 1 .bpo2

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

/-- Fill the fixed successor header with the supplied body commitments. -/
def committedHeader (st post : Jaune.State) (bout : BlockOutput) : Header :=
  commitHeader Fork.bpo2.ruleSet (checkpointBlock st) (executionHeader st) post bout

end Blanc.SyntheticBpo2Envelope
