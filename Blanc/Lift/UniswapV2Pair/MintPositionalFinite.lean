import Blanc.Lift.UniswapV2Pair.MintPrefixWalk

/-! Source finish over a fixed actual fee return and its original Mint suffix. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Fixed fee-output source accounting consumes the supplied actual pricing and
ABI suffixes. No factory observation is selected again by this adapter. -/
theorem mint_fixed_fee_public_frame {K : WriterKey → Prop} {st : State}
    {frame : Frame} {observed : MintObserved} {sevm : Sevm}
    {feeBase feePost calleePost post : Devm} {R : List B256} {M : Mem}
    {w amount1 amount0 b1 b0 r1 r0 toWord ρ : B256} {feeGas : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (sourceFee : FeeMintSourceResult K st sevm feeBase
      (mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R) M w r0 r1 feeGas)
    (stateFee : feePost = feeBranchPost sevm feeBase
      (mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R) M st.kLast w r0 r1 feeGas)
    (fresh : MintAfterFeeFresh (feeBranchSourceKeys K st sevm feeBase w r0 r1)
      (feeBranchSourceFee st sevm feeBase w r0 r1).state toWord)
    (cache : MintAfterFeeCache observed (feeBranchSourceFee st sevm feeBase w r0 r1)
      (feeOnWord w) amount1 amount0 b1 b0 r1 r0 toWord)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (pair : frame.context.pair = sevm.currentTarget) (sender : frame.context.sender = sevm.caller)
    (sourceMint : SFunc.Run cert.prog sevm feePost t_1233_c41 (.returned calleePost))
    (sourceABI : SFunc.Run cert.prog sevm calleePost t_039b_c86 (.halted post)) :
    MintPublicFrameResult (feeBranchSourceKeys K st sevm feeBase w r0 r1)
      frame observed (feeBranchSourceFee st sevm feeBase w r0 r1)
      sevm feePost amount1 amount0 b1 b0 toWord (.halted post) := by
  have machine := pairFeePost_machine (sevm := sevm) (b := feeBase)
    (R := mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R)
    (K := st.kLast) (w := w) (r0 := r0) (r1 := r1) (G := feeGas) mem
  rw [← stateFee] at machine
  have rep : WriterRep (feeBranchSourceKeys K st sevm feeBase w r0 r1)
      (feePost.getStor sevm.currentTarget) (feeBranchSourceFee st sevm feeBase w r0 r1).state := by
    rw [stateFee]
    exact sourceFee.2.1
  have self := St.self (d := feePost) machine.1 rfl
  have raw : SFunc.Run cert.prog sevm
      (St feePost (feeOnWord w :: 0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
        0 :: toWord :: ρ :: R) feePost.memory feePost.gasLeft)
      t_1233_c41 (.returned calleePost) := by
    have transported := (congrArg (fun world : Devm =>
      SFunc.Run cert.prog sevm world t_1233_c41 (.returned calleePost)) self).mp sourceMint
    simpa only [mintFeeLocals] using transported
  have finite := mintAfterFee_frame_inv fork machine.2 rep fresh cache time pair sender
    bound0 bound1 raw
  have priced := mintAfterFee_inv fork machine.2 bound0 bound1 raw
  obtain ⟨liquidity, returned, result, stack, pointer⟩ :=
    mintAfterFeeResult_return_machine machine.2 priced
  have same := Outcome.returned.inj result
  have actualPointer : PtrMem 128 192 calleePost.memory := same.symm ▸ pointer
  exact mintFrameResult_public_return_inv actualPointer finite sourceABI

end Blanc.Lift.UniswapV2Pair
