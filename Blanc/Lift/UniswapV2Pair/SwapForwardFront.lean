import Blanc.Lift.UniswapV2Pair.SwapForwardCallback
import Blanc.Lift.UniswapV2Pair.SwapCut

/-! The forward (gas-exact) front half of the swap body, from the body entry `t_0683_c54` to
the post-callback join `t_09c3_c5` with the cut stack: the lock prefix
(`swapBody_prefix_exact`), both optional transfers (`swapFwdTransfers_exact`) and the
conditional callback (`swapFwdCallback_call`/`_skip`). The callee frames (both token
transfers and the callback) are forward-environment premises; the moved-pointer `_safeTransfer`
helper and the reply-length bound are cross-host hypotheses. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The world at the callback branch: after the optional transfers. -/
def swapFrontTransferWorld (sevm : Sevm) (b d0 d1 : Devm) : Devm :=
  swapOptWorld (swapAmount1Out sevm) (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm b) d0) d1

/-- The memory at the callback branch. -/
def swapFrontTransferMem (sevm : Sevm) (d0 d1 : Devm) : Mem :=
  swapOptMem (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
    (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) (swapRecipientWord sevm) d1

/-- The free pointer at the callback branch (and at the join). -/
def swapFrontPtr (sevm : Sevm) (d0 d1 : Devm) : B256 :=
  swapOptPtr (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) d1

/-- The world at the join. -/
def swapFrontCutWorld (sevm : Sevm) (b d0 d1 dC : Devm) : Devm :=
  if swapDataLength sevm = 0 then swapFrontTransferWorld sevm b d0 d1 else dC

/-- The memory at the join. -/
def swapFrontCutMem (sevm : Sevm) (d0 d1 dC : Devm) : Mem :=
  if swapDataLength sevm = 0 then swapFrontTransferMem sevm d0 d1 else dC.memory

/-- The gas at the callback branch, given the join gas `Gc`. -/
def swapFrontCallbackGas (sevm : Sevm) (b d0 d1 : Devm) (cgC Gc : Nat) : Nat :=
  if swapDataLength sevm = 0 then Gc + 20 else
    cgC + swapCallbackGas (swapFrontTransferWorld sevm b d0 d1)
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& swapRecipientWord sevm).toAdr
      (swapFrontTransferMem sevm d0 d1).size (swapFrontPtr sevm d0 d1).toNat
      (swapDataLength sevm).toNat

/-- The gas at the optimistic-transfer branch. -/
def swapFrontTransferGas (pre : Nat → B256 → Nat) (sevm : Sevm) (b d0 d1 : Devm)
    (cg0 cg1 cgC Gc : Nat) : Nat :=
  swapOptGas pre getterInitMemory 128 (swapAmount0Out sevm) cg0
    (swapOptGas pre (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
      (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) cg1
      (swapFrontCallbackGas sevm b d0 d1 cgC Gc))

/-- **Forward environment of the swap front half**, over the callee results `d0`, `d1`, `dC`
and the `CALL` states' gas `cg0`, `cg1`, `cgC`: each taken token transfer's primitive `CALL`
data (`SwapTransferCallForward`) and reply bound, the callback's primitive `CALL` data
(`SwapCallbackCallForward`), and the lock-store stipend check. Each call's residual gas
is tied to the next segment's need, ending at the join gas `Gc`. No successful suffix run is
assumed.
CROSS-HOST: conditional on `SwapForwardReplyShort`. -/
structure SwapFrontForwardEnv (pre : Nat → B256 → Nat) (post : Nat → B256 → Bytes → Nat)
    (sevm : Sevm) (b : Devm) (st : State) (d0 d1 dC : Devm) (cg0 cg1 cgC Gc : Nat) : Prop where
  transfer0 : swapAmount0Out sevm ≠ 0 → SwapTransferCallForward post sevm (swapPrefixWorld sevm b)
    (swapLocalsStack sevm st) getterInitMemory getterInitMemory.size 128 (swapAmount0Out sevm)
    (swapRecipientWord sevm) st.token0.toB256 0x8d0 cg0
    (swapOptGas pre (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
      (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) cg1
      (swapFrontCallbackGas sevm b d0 d1 cgC Gc)) d0
  short0 : swapAmount0Out sevm ≠ 0 → SwapForwardReplyShort d0
  transfer1 : swapAmount1Out sevm ≠ 0 → SwapTransferCallForward post sevm
    (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm b) d0) (swapLocalsStack sevm st)
    (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
    (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0).size
    (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) (swapRecipientWord sevm)
    st.token1.toB256 0x8e1 cg1 (swapFrontCallbackGas sevm b d0 d1 cgC Gc) d1
  short1 : swapAmount1Out sevm ≠ 0 → SwapForwardReplyShort d1
  callback : swapDataLength sevm ≠ 0 → SwapCallbackCallForward sevm
    (swapFrontTransferWorld sevm b d0 d1) (swapLocalsStack sevm st)
    (swapFrontTransferMem sevm d0 d1) (swapFrontPtr sevm d0 d1) (swapRecipientWord sevm)
    (swapAmount0Out sevm) (swapAmount1Out sevm) (swapDataLength sevm) (swapDataStart sevm) cgC Gc dC
  sentry : gCallStipend < swapFrontTransferGas pre sevm b d0 d1 cg0 cg1 cgC Gc +
    sstoreCost sevm (afterSload sevm b 12) 12 0

/-- **Forward swap front half.** Under the finite entry storage, the source guards of
`startTyped`, the guards of the ABI wrapper's `data` view and the front environment, the body
runs from its entry with the closed charge `swapPrefixGas` over the transfer-branch gas to the
join, with the source-named locals (`swapLocalsStack`, the cut stack
`swapCutStack (swapCutWords sevm st) 0x257 [0x022c0d9f]`). At the join
the free-pointer carrier holds at `swapFrontPtr` with `128 ≤ p` and `p + 260 < 2^256`, and the
output buffer is the entry one.
CROSS-HOST: conditional on `SwapSafeTransferForward`, `SwapForwardReplyShort`. -/
theorem swapBody_front_exact {K : WriterKey → Prop} {st : State}
    {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b d0 d1 dC : Devm} {cg0 cg1 cgC Gc : Nat}
    (helper : SwapSafeTransferForward pre post)
    (fork : CoveredFork sevm.benvStat.fork)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (unlocked : st.unlocked = 1) (nonstatic : sevm.isStatic = false)
    (output : swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0)
    (liquidity0 : (swapAmount0Out sevm).toNat < st.reserve0.val)
    (liquidity1 : (swapAmount1Out sevm).toNat < st.reserve1.val)
    (to0 : swapRecipient sevm ≠ st.token0) (to1 : swapRecipient sevm ≠ st.token1)
    (guards : SwapAbiGuards sevm)
    (env : SwapFrontForwardEnv pre post sevm b st d0 d1 dC cg0 cg1 cgC Gc) :
    let cutMem := swapFrontCutMem sevm d0 d1 dC
    let p := swapFrontPtr sevm d0 d1
    PtrMem p cutMem.size cutMem ∧ 128 ≤ p.toNat ∧ p.toNat + 260 < 2 ^ 256 ∧
    (swapFrontCutWorld sevm b d0 d1 dC).output = b.output ∧
    ∀ o, SFunc.RunExact cert.prog sevm
        (St (swapFrontCutWorld sevm b d0 d1 dC) (swapLocalsStack sevm st)
          cutMem Gc) t_09c3_c5 o →
      SFunc.RunExact cert.prog sevm
        (St b (swapBodyStack sevm) getterInitMemory
          (swapFrontTransferGas pre sevm b d0 d1 cg0 cg1 cgC Gc + swapPrefixGas sevm b (swapAmount0Out sevm)))
        t_0683_c54 o := by
  intro cutMem p
  have sentinel : memWord getterInitMemory 96 = 0 := by
    have zero : memWord Mem.empty 96 = 0 := by decide
    rw [← zero]
    refine memWord_congr (fun j hj => ?_)
    rw [getterInitMemory, Mem.Reads.write Mem.wf_empty (Mem.reads_data Mem.empty) 64 _ (96 + j),
      Bytes.getD_writeAt]
    split
    · exfalso
      rw [B256.length_toBytes] at *
      omega
    · rw [← Mem.reads_data Mem.empty (96 + j)]
  obtain ⟨⟨⟨n2, mem2⟩, lower2, upper2, out2⟩, transfers⟩ :=
    swapFwdTransfers_exact (sevm := sevm) (b0 := swapPrefixWorld sevm b) (d0 := d0) (d1 := d1)
      (R := [0x022c0d9f]) (cg0 := cg0) (cg1 := cg1)
      (G := swapFrontCallbackGas sevm b d0 d1 cgC Gc) (t1 := st.token1.toB256)
      (t0 := st.token0.toB256) (r1 := Nat.toB256 st.reserve1.val) (r0 := Nat.toB256 st.reserve0.val)
      (len := swapDataLength sevm) (start := swapDataStart sevm) (toWord := swapRecipientWord sevm)
      (a1 := swapAmount1Out sevm) (a0 := swapAmount0Out sevm) (ρ := 0x257)
      helper fork (by decide) getterInitMemory_ptr sentinel (by decide) (by decide)
      env.transfer0 env.short0 env.transfer1 env.short1
  have width2 : p.toNat + 260 < 2 ^ 256 := by
    have : 2 ^ 163 + 260 < 2 ^ 256 := by decide
    simp only [p, swapFrontPtr]
    omega
  have mem2' : PtrMem (swapFrontPtr sevm d0 d1) (swapFrontTransferMem sevm d0 d1).size
      (swapFrontTransferMem sevm d0 d1) := by
    unfold swapFrontPtr swapFrontTransferMem
    rw [mem2.size]
    exact mem2
  have short : (swapDataLength sevm).toNat ≤ 2 ^ 32 := guards.length
  have callback : ((∃ n', PtrMem p n' cutMem) ∧ (swapFrontCutWorld sevm b d0 d1 dC).output =
        (swapFrontTransferWorld sevm b d0 d1).output) ∧
      ∀ o, SFunc.RunExact cert.prog sevm
          (St (swapFrontCutWorld sevm b d0 d1 dC) (swapLocalsStack sevm st) cutMem Gc) t_09c3_c5 o →
        SFunc.RunExact cert.prog sevm
          (St (swapFrontTransferWorld sevm b d0 d1) (swapLocalsStack sevm st)
            (swapFrontTransferMem sevm d0 d1) (swapFrontCallbackGas sevm b d0 d1 cgC Gc))
          t_08e1_c4 o := by
    by_cases zero : swapDataLength sevm = 0
    · simp only [cutMem, swapFrontCutMem, swapFrontCutWorld, swapFrontCallbackGas, zero, ↓reduceIte]
      exact ⟨⟨⟨_, mem2'⟩, trivial⟩, fun o cont => swapFwdCallback_skip (by decide) zero cont⟩
    · simp only [cutMem, swapFrontCutMem, swapFrontCutWorld, swapFrontCallbackGas, zero, ↓reduceIte]
      have e := env.callback zero
      exact ⟨e.post fork mem2' lower2, fun o cont =>
        swapFwdCallback_call fork (by decide) mem2' lower2 upper2 short zero e cont⟩
  obtain ⟨⟨⟨n3, mem3⟩, out3⟩, run3⟩ := callback
  refine ⟨by rw [mem3.size]; exact mem3, lower2, width2, out3.trans (out2.trans ?_), fun o cont => ?_⟩
  · unfold swapPrefixWorld mintLockedWorld
    rw [afterSload_output, afterSload_output, afterSload_output, afterSstore_output,
      afterSload_output]
  exact swapBody_prefix_exact fork rep unlocked nonstatic output liquidity0 liquidity1 to0 to1
    env.sentry (transfers o (run3 o cont))

end Blanc.Lift.UniswapV2Pair
