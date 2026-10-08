import Blanc.Lift.UniswapV2Pair.MintPositionalFacts
import Blanc.Lift.UniswapV2Pair.MintPositionalReturn
import Blanc.Lift.UniswapV2Pair.MintPositionalFinite

/-! Finite Mint finish from one certificate's original replies and suffixes. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintPositionalFeeBase {root : Exec.Deriv} {b : Devm} (r : MintRootCallPositions root b) : Devm :=
  feeKLastWorld root.sevm r.fee.occurrence.call.returned.devm

def mintPositionalFeeMemory {root : Exec.Deriv} {b : Devm} (r : MintRootCallPositions root b) : Mem :=
  feeReplyMemory (balanceReplyMemory
    (balanceReplyMemory getterInitMemory root.sevm.currentTarget r.out0)
    r.first.call.returned.sevm.currentTarget r.out1) r.fee.out

def mintPositionalFeeWord {root : Exec.Deriv} {b : Devm} (r : MintRootCallPositions root b) : B256 :=
  Bytes.toB256 (r.fee.out.take 32)

def mintPositionalLocals {root : Exec.Deriv} {b : Devm} (r : MintRootCallPositions root b) : List B256 :=
  mintFeeLocals (Bytes.toB256 (r.out1.take 32) - mintRootReserve1 root b)
    (Bytes.toB256 (r.out0.take 32) - mintRootReserve0 root b)
    (Bytes.toB256 (r.out1.take 32)) (Bytes.toB256 (r.out0.take 32))
    (mintRootReserve1 root b) (mintRootReserve0 root b)
    (Sevm.dataWord root.sevm 4).toAdr.toB256 0x039b [0x6a627842]

def mintPositionalFeeKeys {root : Exec.Deriv} {b : Devm} (K : WriterKey → Prop)
    (current : Checkpoint) (r : MintRootCallPositions root b) : WriterKey → Prop :=
  feeBranchSourceKeys K { current.state with unlocked := 0 } root.sevm
    (mintPositionalFeeBase r) (mintPositionalFeeWord r) (mintRootReserve0 root b) (mintRootReserve1 root b)

def mintPositionalFeeResult {root : Exec.Deriv} {b : Devm}
    (current : Checkpoint) (r : MintRootCallPositions root b) : FeeResult :=
  feeBranchSourceFee { current.state with unlocked := 0 } root.sevm
    (mintPositionalFeeBase r) (mintPositionalFeeWord r) (mintRootReserve0 root b) (mintRootReserve1 root b)

/-- The source finish keeps the original incoming checkpoint and the full actual fee state. -/
def MintPositionalSourceFinish {root : Exec.Deriv} {b : Devm} (K : WriterKey → Prop)
    (current : Checkpoint) (invocation : List Nat) (post : Devm)
    (r : MintRootCallPositions root b) : Prop :=
  ∃ (feeN : Exec.Deriv) (feeGas : Nat),
    Exec.Deriv.ExecFreeUntil r.fee.occurrence.call.returned feeN ∧
    FeeMintSourceResult K { current.state with unlocked := 0 } root.sevm
      (mintPositionalFeeBase r) (mintPositionalLocals r) (mintPositionalFeeMemory r)
      (mintPositionalFeeWord r) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas ∧
    feeN.devm = feeBranchPost root.sevm (mintPositionalFeeBase r)
      (mintPositionalLocals r) (mintPositionalFeeMemory r) current.state.kLast
      (mintPositionalFeeWord r) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas ∧
    MintPublicFrameResult (mintPositionalFeeKeys K current r)
      (mintSourceAfterFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
      (mintBalanceObserved current.state (Sevm.dataWord root.sevm 4).toAdr
        (Bytes.toB256 (r.out0.take 32)) (Bytes.toB256 (r.out1.take 32)))
      (mintPositionalFeeResult current r) root.sevm feeN.devm
      (Bytes.toB256 (r.out1.take 32) - mintRootReserve1 root b)
      (Bytes.toB256 (r.out0.take 32) - mintRootReserve0 root b)
      (Bytes.toB256 (r.out1.take 32)) (Bytes.toB256 (r.out0.take 32))
      (Sevm.dataWord root.sevm 4).toAdr.toB256 (.halted post)

/-- Fixed-reply finite accounting starts at the actual fee return and consumes
its original Mint and ABI continuations. The incoming checkpoint is unchanged. -/
theorem MintRootCallPositions.sourceFinish {root : Exec.Deriv} {b post : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : MintRootCallPositions root b)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat) (success : root.exn = .ok post)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (freshFee : FeeMintFresh K { current.state with unlocked := 0 } root.sevm
      (mintPositionalFeeBase r) (mintPositionalFeeWord r)
      (mintRootReserve0 root b) (mintRootReserve1 root b))
    (freshMint : MintAfterFeeFresh (mintPositionalFeeKeys K current r)
      (mintPositionalFeeResult current r).state (Sevm.dataWord root.sevm 4).toAdr.toB256) :
    MintPositionalSourceFinish K current invocation post r := by
  obtain ⟨feeN, mintN, feeCursor, mintCursor, feeGas, spanFee, envFee, outcomeFee,
    placedFee, treeFee, contsFee, guards, stateFee, spanMint, envMint, outcomeMint,
    placedMint, treeMint, contsMint, sourceMint, sourceABI⟩ := r.suffixes success fork
  have env1 := r.second.returned_sevm.trans r.first.returned_sevm
  have actualReply := r.fee.reply
  simp only [env1] at actualReply
  have postRep := (r.fee_entry_rep rep).fee_factory_post actualReply
  rcases postRep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, last, _⟩
  have rawLast : feeKLastWord root.sevm r.fee.occurrence.call.returned.devm =
      current.state.kLast := by
    simp only [feeKLastWorld, afterSload_getStor] at last
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
  have sourceGuards : feeBranchAccepts root.sevm (mintPositionalFeeBase r)
      current.state.kLast (mintPositionalFeeWord r) (mintRootReserve0 root b)
      (mintRootReserve1 root b) := by
    simpa only [mintPositionalFeeBase, mintPositionalFeeWord, rawLast] using guards
  have sourceFee : FeeMintSourceResult K { current.state with unlocked := 0 } root.sevm
      (mintPositionalFeeBase r) (mintPositionalLocals r) (mintPositionalFeeMemory r)
      (mintPositionalFeeWord r) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas :=
    feeBranch_source_result postRep bound0 bound1 sourceGuards freshFee
  have stateFee' : feeN.devm = feeBranchPost root.sevm (mintPositionalFeeBase r)
      (mintPositionalLocals r) (mintPositionalFeeMemory r) current.state.kLast
      (mintPositionalFeeWord r) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas := by
    simpa only [mintPositionalFeeBase, mintPositionalLocals, mintPositionalFeeMemory,
      mintPositionalFeeWord, rawLast] using stateFee
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
      (mintPositionalFeeResult current r) (feeOnWord (mintPositionalFeeWord r))
      (Bytes.toB256 (r.out1.take 32) - mintRootReserve1 root b)
      (Bytes.toB256 (r.out0.take 32) - mintRootReserve0 root b)
      (Bytes.toB256 (r.out1.take 32)) (Bytes.toB256 (r.out0.take 32))
      (mintRootReserve1 root b) (mintRootReserve0 root b)
      (Sevm.dataWord root.sevm 4).toAdr.toB256 := by
    rw [← payload]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, mintFeePost_flag⟩
  refine ⟨feeN, feeGas, spanFee, sourceFee, stateFee', ?_⟩
  exact mint_fixed_fee_public_frame fork mem bound0 bound1 sourceFee stateFee'
    freshMint cache rfl rfl rfl sourceMint sourceABI

end Blanc.Lift.UniswapV2Pair
