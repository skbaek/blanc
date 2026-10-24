import Blanc.Lift.UniswapV2Pair.MintPositionalFacts
import Blanc.Lift.UniswapV2Pair.MintPositionalReturn
import Blanc.Lift.UniswapV2Pair.MintPositionalFinite

/-! Finite Mint finish from one certificate's original replies and suffixes. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintPositionalFeeBase {root : Exec.Deriv} {b : Devm} (r : MintRootCallPositions root b) : Devm :=
  feeKLastWorld root.sevm r.fee.occurrence.call.returned.devm

def mintPositionalFeeBaseH {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm} (r : MintRootCallPositionsH root b W1 A2 F) : Devm :=
  feeKLastWorldH root.sevm r.fee.occurrence.call.returned.devm

theorem mintPositionalFeeBaseH_of_covered {root : Exec.Deriv} {b : Devm} {r : MintRootCallPositions root b}
    (fork : CoveredFork root.sevm.benvStat.fork) :
    mintPositionalFeeBaseH (r.toH fork) = mintPositionalFeeBase r := by
  unfold mintPositionalFeeBaseH mintPositionalFeeBase
  exact feeKLastWorldH_of_covered fork

def mintPositionalFeeMemory {root : Exec.Deriv} {b : Devm} (r : MintRootCallPositions root b) : Mem :=
  feeReplyMemory (balanceReplyMemory
    (balanceReplyMemory getterInitMemory root.sevm.currentTarget r.out0)
    r.first.call.returned.sevm.currentTarget r.out1) r.fee.out

def mintPositionalFeeMemoryH {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm} (r : MintRootCallPositionsH root b W1 A2 F) : Mem :=
  feeReplyMemory (balanceReplyMemory
    (balanceReplyMemory getterInitMemory root.sevm.currentTarget r.out0)
    r.first.call.returned.sevm.currentTarget r.out1) r.fee.out

theorem mintPositionalFeeMemoryH_of_covered {root : Exec.Deriv} {b : Devm} {r : MintRootCallPositions root b}
    (fork : CoveredFork root.sevm.benvStat.fork) :
    mintPositionalFeeMemoryH (r.toH fork) = mintPositionalFeeMemory r := by
  rfl

def mintPositionalFeeWord {root : Exec.Deriv} {b : Devm} (r : MintRootCallPositions root b) : B256 :=
  Bytes.toB256 (r.fee.out.take 32)

def mintPositionalFeeWordH {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm} (r : MintRootCallPositionsH root b W1 A2 F) : B256 :=
  Bytes.toB256 (r.fee.out.take 32)

theorem mintPositionalFeeWordH_of_covered {root : Exec.Deriv} {b : Devm} {r : MintRootCallPositions root b}
    (fork : CoveredFork root.sevm.benvStat.fork) :
    mintPositionalFeeWordH (r.toH fork) = mintPositionalFeeWord r := by
  rfl

def mintPositionalLocals {root : Exec.Deriv} {b : Devm} (r : MintRootCallPositions root b) : List B256 :=
  mintFeeLocals (Bytes.toB256 (r.out1.take 32) - mintRootReserve1 root b)
    (Bytes.toB256 (r.out0.take 32) - mintRootReserve0 root b)
    (Bytes.toB256 (r.out1.take 32)) (Bytes.toB256 (r.out0.take 32))
    (mintRootReserve1 root b) (mintRootReserve0 root b)
    (Sevm.dataWord root.sevm 4).toAdr.toB256 0x039b [0x6a627842]

def mintPositionalLocalsH {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm} (r : MintRootCallPositionsH root b W1 A2 F) : List B256 :=
  mintFeeLocals (Bytes.toB256 (r.out1.take 32) - mintRootReserve1 root b)
    (Bytes.toB256 (r.out0.take 32) - mintRootReserve0 root b)
    (Bytes.toB256 (r.out1.take 32)) (Bytes.toB256 (r.out0.take 32))
    (mintRootReserve1 root b) (mintRootReserve0 root b)
    (Sevm.dataWord root.sevm 4).toAdr.toB256 0x039b [0x6a627842]

theorem mintPositionalLocalsH_of_covered {root : Exec.Deriv} {b : Devm} {r : MintRootCallPositions root b}
    (fork : CoveredFork root.sevm.benvStat.fork) :
    mintPositionalLocalsH (r.toH fork) = mintPositionalLocals r := by
  rfl

def mintPositionalFeeKeys {root : Exec.Deriv} {b : Devm} (K : WriterKey → Prop)
    (current : Checkpoint) (r : MintRootCallPositions root b) : WriterKey → Prop :=
  feeBranchSourceKeys K { current.state with unlocked := 0 } root.sevm
    (mintPositionalFeeBase r) (mintPositionalFeeWord r) (mintRootReserve0 root b) (mintRootReserve1 root b)

def mintPositionalFeeKeysH {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm} (K : WriterKey → Prop)
    (current : Checkpoint) (r : MintRootCallPositionsH root b W1 A2 F) : WriterKey → Prop :=
  feeBranchSourceKeys K { current.state with unlocked := 0 } root.sevm
    (mintPositionalFeeBaseH r) (mintPositionalFeeWordH r) (mintRootReserve0 root b) (mintRootReserve1 root b)

theorem mintPositionalFeeKeysH_of_covered {root : Exec.Deriv} {b : Devm} {K : WriterKey → Prop} {current : Checkpoint} {r : MintRootCallPositions root b}
    (fork : CoveredFork root.sevm.benvStat.fork) :
    mintPositionalFeeKeysH K current (r.toH fork) = mintPositionalFeeKeys K current r := by
  unfold mintPositionalFeeKeysH mintPositionalFeeKeys
  rw [mintPositionalFeeBaseH_of_covered fork, mintPositionalFeeWordH_of_covered fork]

def mintPositionalFeeResult {root : Exec.Deriv} {b : Devm}
    (current : Checkpoint) (r : MintRootCallPositions root b) : FeeResult :=
  feeBranchSourceFee { current.state with unlocked := 0 } root.sevm
    (mintPositionalFeeBase r) (mintPositionalFeeWord r) (mintRootReserve0 root b) (mintRootReserve1 root b)

def mintPositionalFeeResultH {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm}
    (current : Checkpoint) (r : MintRootCallPositionsH root b W1 A2 F) : FeeResult :=
  feeBranchSourceFee { current.state with unlocked := 0 } root.sevm
    (mintPositionalFeeBaseH r) (mintPositionalFeeWordH r) (mintRootReserve0 root b) (mintRootReserve1 root b)

theorem mintPositionalFeeResultH_of_covered {root : Exec.Deriv} {b : Devm} {current : Checkpoint} {r : MintRootCallPositions root b}
    (fork : CoveredFork root.sevm.benvStat.fork) :
    mintPositionalFeeResultH current (r.toH fork) = mintPositionalFeeResult current r := by
  unfold mintPositionalFeeResultH mintPositionalFeeResult
  rw [mintPositionalFeeBaseH_of_covered fork, mintPositionalFeeWordH_of_covered fork]

def MintPositionalSourceFinishH {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm} (K : WriterKey → Prop)
    (current : Checkpoint) (invocation : List Nat) (post : Devm)
    (r : MintRootCallPositionsH root b W1 A2 F) : Prop :=
  ∃ (feeN : Exec.Deriv) (feeGas : Nat),
    Exec.Deriv.ExecFreeUntil r.fee.occurrence.call.returned feeN ∧
    FeeMintSourceResultH K { current.state with unlocked := 0 } root.sevm
      (mintPositionalFeeBaseH r) (mintPositionalLocalsH r) (mintPositionalFeeMemoryH r)
      (mintPositionalFeeWordH r) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas ∧
    feeN.devm = feeBranchPostH root.sevm (mintPositionalFeeBaseH r)
      (mintPositionalLocalsH r) (mintPositionalFeeMemoryH r) current.state.kLast
      (mintPositionalFeeWordH r) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas ∧
    MintPublicFrameResult (mintPositionalFeeKeysH K current r)
      (mintSourceAfterFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
      (mintBalanceObserved current.state (Sevm.dataWord root.sevm 4).toAdr
        (Bytes.toB256 (r.out0.take 32)) (Bytes.toB256 (r.out1.take 32)))
      (mintPositionalFeeResultH current r) root.sevm feeN.devm
      (Bytes.toB256 (r.out1.take 32) - mintRootReserve1 root b)
      (Bytes.toB256 (r.out0.take 32) - mintRootReserve0 root b)
      (Bytes.toB256 (r.out1.take 32)) (Bytes.toB256 (r.out0.take 32))
      (Sevm.dataWord root.sevm 4).toAdr.toB256 (.halted post)

theorem MintRootCallPositionsH.sourceFinish {root : Exec.Deriv} {b post : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : MintRootCallPositionsH root b W1 A2 F)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (success : root.exn = .ok post)
    (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none)
    (freshFee : FeeMintFresh K { current.state with unlocked := 0 } root.sevm
      (mintPositionalFeeBaseH r) (mintPositionalFeeWordH r)
      (mintRootReserve0 root b) (mintRootReserve1 root b))
    (freshMint : MintAfterFeeFresh (mintPositionalFeeKeysH K current r)
      (mintPositionalFeeResultH current r).state (Sevm.dataWord root.sevm 4).toAdr.toB256) :
    MintPositionalSourceFinishH K current invocation post r := by
  obtain ⟨feeN, mintN, feeCursor, mintCursor, feeGas, spanFee, envFee, outcomeFee,
    placedFee, treeFee, contsFee, guards, stateFee, spanMint, envMint, outcomeMint,
    placedMint, treeMint, contsMint, sourceMint, sourceABI⟩ := r.suffixes success stateGas bal
  have env1 := r.second.returned_sevm.trans r.first.returned_sevm
  have actualReply := r.fee.reply
  simp only [env1] at actualReply
  rw [r.worlds.2.2 _ _ rfl] at actualReply
  have postRep := (r.fee_entry_rep rep).fee_factory_postH actualReply
  rcases postRep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, last, _⟩
  have rawLast : feeKLastWord root.sevm r.fee.occurrence.call.returned.devm =
      current.state.kLast := by
    simp only [feeKLastWorldH, afterSloadH_getStor] at last
    simpa only [feeKLastWord, Devm.getStorVal, Devm.getStor] using last
  obtain ⟨cache0, cache1, _, _, _⟩ := r.cache_targets rep
  have nat0 : (mintRootReserve0 root b).toNat = current.state.reserve0.val := by
    rw [cache0, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have nat1 : (mintRootReserve1 root b).toNat = current.state.reserve1.val := by
    rw [cache1, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have bound0 : (mintRootReserve0 root b).toNat < 2 ^ 112 := nat0 ▸ current.state.reserve0.isLt
  have bound1 : (mintRootReserve1 root b).toNat < 2 ^ 112 := nat1 ▸ current.state.reserve1.isLt
  have sourceGuards : feeBranchAcceptsH root.sevm (mintPositionalFeeBaseH r)
      current.state.kLast (mintPositionalFeeWordH r) (mintRootReserve0 root b)
      (mintRootReserve1 root b) := by
    simpa only [mintPositionalFeeBaseH, mintPositionalFeeWordH, rawLast] using guards
  have sourceFee : FeeMintSourceResultH K { current.state with unlocked := 0 } root.sevm
      (mintPositionalFeeBaseH r) (mintPositionalLocalsH r) (mintPositionalFeeMemoryH r)
      (mintPositionalFeeWordH r) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas :=
    feeBranch_source_resultH postRep bound0 bound1 sourceGuards freshFee
  have stateFee' : feeN.devm = feeBranchPostH root.sevm (mintPositionalFeeBaseH r)
      (mintPositionalLocalsH r) (mintPositionalFeeMemoryH r) current.state.kLast
      (mintPositionalFeeWordH r) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas := by
    simpa only [mintPositionalFeeBaseH, mintPositionalLocalsH, mintPositionalFeeMemoryH,
      mintPositionalFeeWordH, rawLast] using stateFee
  have mem0 := balanceRequestMemory_ptr getterInitMemory_ptr root.sevm.currentTarget
  have mem1 := balanceReplyMemory_ptr r.out0 mem0
  have mem2 := balanceRequestMemory_ptr mem1 r.first.call.returned.sevm.currentTarget
  have mem3 := balanceReplyMemory_ptr r.out1 mem2
  have mem := feeReplyMemory_ptr r.fee.out (feeRequestMemory_ptr mem3)
  have payload := mint_balance_observed_eq (st := current.state)
    (recipient := (Sevm.dataWord root.sevm 4).toAdr)
    (b0 := Bytes.toB256 (r.out0.take 32)) (b1 := Bytes.toB256 (r.out1.take 32))
    bound0 bound1 cache0 cache1 nat0 nat1
  have cache : MintAfterFeeCache
      (mintBalanceObserved current.state (Sevm.dataWord root.sevm 4).toAdr
        (Bytes.toB256 (r.out0.take 32)) (Bytes.toB256 (r.out1.take 32)))
      (mintPositionalFeeResultH current r) (feeOnWord (mintPositionalFeeWordH r))
      (Bytes.toB256 (r.out1.take 32) - mintRootReserve1 root b)
      (Bytes.toB256 (r.out0.take 32) - mintRootReserve0 root b)
      (Bytes.toB256 (r.out1.take 32)) (Bytes.toB256 (r.out0.take 32))
      (mintRootReserve1 root b) (mintRootReserve0 root b)
      (Sevm.dataWord root.sevm 4).toAdr.toB256 := by
    rw [← payload]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, mintFeePost_flag⟩
  refine ⟨feeN, feeGas, spanFee, sourceFee, stateFee', ?_⟩
  exact mint_fixed_fee_public_frameH stateGas bal mem bound0 bound1 sourceFee stateFee'
    freshMint cache rfl rfl rfl sourceMint sourceABI


end Blanc.Lift.UniswapV2Pair
