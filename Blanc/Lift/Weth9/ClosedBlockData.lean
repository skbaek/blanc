import Blanc.SyntheticBpo2Envelope
import Blanc.Lift.Weth9.ClosedSigningData

/-!
The concrete chain envelope for the synthetic WETH9 applicability witness.
The neutral fixed BPO2 fixture owns the header/input scaffold. This module
keeps its compatibility names and the WETH deposit transaction instance.
-/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.BlockForward Blanc.ExecutionTrace

def config : ChainConfig :=
  SyntheticBpo2Envelope.config

theorem config_valid : config.Valid :=
  SyntheticBpo2Envelope.config_valid

theorem config_forkAt (number t : Nat) : config.forkAt number t = .ok .bpo2 :=
  SyntheticBpo2Envelope.config_forkAt number t

theorem config_covered (number t : Nat) (fork : Fork)
    (h : config.forkAt number t = .ok fork) : CoveredFork fork :=
  SyntheticBpo2Envelope.config_covered number t fork h

def checkpointHeader (st : Jaune.State) : Header :=
  SyntheticBpo2Envelope.checkpointHeader st

def checkpointBlock (st : Jaune.State) : Block :=
  SyntheticBpo2Envelope.checkpointBlock st

def checkpoint (st : Jaune.State) : BlockChain :=
  SyntheticBpo2Envelope.checkpoint st

def executionHeader (st : Jaune.State) : Header :=
  SyntheticBpo2Envelope.executionHeader st

def input (st : Jaune.State) : Benv :=
  SyntheticBpo2Envelope.input st

def depositBlock (st post : Jaune.State) (bout : BlockOutput) : Block :=
  { header := SyntheticBpo2Envelope.committedHeader st post bout
    txs := [Sum.inr depositTx]
    wds := []
    ommers := [] }

theorem checkpoint_validContext {st : Jaune.State} (hcanon : st.Canonical) :
    (checkpoint st).ValidContext :=
  SyntheticBpo2Envelope.checkpoint_validContext hcanon

theorem depositBlock_input (st post : Jaune.State) (bout : BlockOutput) :
    initBenv .bpo2 (checkpoint st) (depositBlock st post bout).header = input st :=
  SyntheticBpo2Envelope.committedHeader_input st post bout

end Blanc.Lift.Weth9.ClosedInstance
