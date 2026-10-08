import Blanc.Lift.UniswapV2Pair.SwapPositionalBalance
import Blanc.Lift.UniswapV2Pair.SwapCanonical
import Blanc.Lift.CursorSourceRunReturn

/-! The original checked balance suffix reaches the actual final Swap image. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def swapRawReserve0 (sevm : Sevm) (b : Devm) : B256 :=
  reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)

def swapRawReserve1 (sevm : Sevm) (b : Devm) : B256 :=
  reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)

def SwapBalances.balance0 {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) : B256 := Bytes.toB256 (r.first.out.take 32)

def SwapBalances.balance1 {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) : B256 := Bytes.toB256 (r.second.out.take 32)

def SwapBalances.input0 {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) : B256 :=
  swapInWord r.balance0 (swapRawReserve0 root.sevm b) (swapAmount0Out root.sevm)

def SwapBalances.input1 {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) : B256 :=
  swapInWord r.balance1 (swapRawReserve1 root.sevm b) (swapAmount1Out root.sevm)

def SwapBalances.finalMemory {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) : Mem :=
  swapBalanceReply
    (swapBalanceReply r.optional.callback.memory r.optional.transfers.second.ptr
      r.optional.callback.next.sevm.currentTarget r.first.out)
    r.optional.transfers.second.ptr r.first.step.returned.sevm.currentTarget r.second.out

def SwapBalances.finalWorld {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) : Devm :=
  afterSstore root.sevm
    ((updateWorld root.sevm r.second.step.returned.devm
      (swapRawReserve0 root.sevm b) (swapRawReserve1 root.sevm b) r.balance0 r.balance1).addLog
      (swapEventLog root.sevm r.input0 r.input1 (swapAmount0Out root.sevm)
        (swapAmount1Out root.sevm) (swapRecipientWord root.sevm))) 12 1

/-- Every acceptance and range fact belongs to these same two decoded replies. -/
structure SwapSuffixFacts {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) : Prop where
  input : 0 < r.input0 ∨ 0 < r.input1
  pricing : SwapKFacts r.balance0 r.balance1 r.input0 r.input1
    (swapRawReserve0 root.sevm b) (swapRawReserve1 root.sevm b)
  bound0 : r.balance0.toNat < 2 ^ 112
  bound1 : r.balance1.toNat < 2 ^ 112
  nonstatic : root.sevm.isStatic = false

/-- Existing input, pricing and update inverses consume this same actual
second decoder. No other balance call or returned world is selected. -/
theorem SwapBalances.decoded_tail_inv {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) {G : Nat} {o : Outcome}
    (fork : CoveredFork root.sevm.benvStat.fork)
    (run : SFunc.Run cert.prog root.sevm
      (St r.second.step.returned.devm (r.balance1 :: swapBalance1LocalsStack root.sevm b r.first.out)
        r.finalMemory G) (swapBalanceDecodedTail true) o) :
    SwapSuffixFacts r ∧ ∃ M gas, o = .returned (St r.finalWorld [0x022c0d9f] M gas) := by
  have plain := run.cut
  dsimp only [swapBalance1LocalsStack, swapRawLocalsStack, swapBodyStack, List.set] at plain
  obtain ⟨input, _, plain⟩ := swapInputsDecoded_inv plain
  obtain ⟨pricing, _, plain⟩ := swapK_inv plain
  have width : r.optional.transfers.second.ptr.toNat + 260 < 2 ^ 256 := by
    have upper := r.optional.transfers.secondUpper
    omega
  obtain ⟨bound0, bound1, nonstatic, M, gas, returned⟩ := swapTail_inv fork
    r.second.pointer r.optional.transfers.secondLower width plain
  exact ⟨⟨input, pricing, bound0, bound1, nonstatic⟩, M, gas, returned⟩

/-- The checked actual body return and its actual pending wrapper STOP derive
this root's final machine image and acceptance facts. -/
theorem SwapBalances.post_image {root : Exec.Deriv} {b post : Devm}
    (r : SwapBalances root root.sevm b) (success : root.exn = .ok post)
    (fork : CoveredFork root.sevm.benvStat.fork) :
    SwapSuffixFacts r ∧ ∃ M gas, post = St r.finalWorld [0x022c0d9f] M gas := by
  let cut := r.second.tail
  have reached := r.second.step.sameFrame.snoc r.second.step.edge
  have env : cut.node.sevm = root.sevm := cut.sevm_eq.trans
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached)
  have outcome : cut.node.exn = .ok post := cut.exn_eq.trans
    ((Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success)
  obtain ⟨gas, state⟩ := cut.state
  rcases cut.placed.sourceRunReturn cert_check outcome (by rw [env]; exact fork) with halted | returned
  · rw [cut.tree, state, env] at halted
    obtain ⟨facts, M, G, impossible⟩ := r.decoded_tail_inv fork (halted.mono StepIn.toRun)
    cases impossible
  · obtain ⟨continuation, tail, d, actual, stack, live, smaller, body, placed⟩ := returned
    rw [cut.tree, state, env] at body
    obtain ⟨facts, M, G, image⟩ := r.decoded_tail_inv fork (body.mono StepIn.toRun)
    have image' : d = St r.finalWorld [0x022c0d9f] M G := Outcome.returned.inj image
    have conts := cut.continuations
    rw [stack, List.map_cons] at conts
    have head : continuation.f = t_0257_c99 := (List.cons.inj conts).1
    have empty : tail = [] := by
      have h := (List.cons.inj conts).2
      cases tail with
      | nil => rfl
      | cons a rest => cases h
    subst tail
    rcases placed.sourceRunReturn cert_check rfl (by change CoveredFork cut.node.sevm.benvStat.fork; rw [env]; exact fork) with stopped | returnedAgain
    · have stopped' : SFunc.RunP (StepIn ⟨_, cut.node.sevm, d, .ok post, actual⟩)
          cert.prog cut.node.sevm (St r.finalWorld [0x022c0d9f] M G) t_0257_c99
          (.halted post) := by
        rw [← image']
        conv => arg 5; rw [← head]
        exact stopped
      obtain ⟨G', result⟩ := swap_stop_inv (SFunc.runP_iff_runCutP_nil.mp stopped')
      exact ⟨facts, M, G', result⟩
    · obtain ⟨next, rest, d', actual', noContinuation, _⟩ := returnedAgain
      cases noContinuation

/-- Both transfer branches preserve the actual incoming output buffer. -/
theorem SwapOptionalTransfer.output_eq {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {p amount toWord token rho : B256}
    {caller : SFunc} {K : List SFunc}
    (r : SwapOptionalTransfer root start b L M p amount toWord token rho caller K) :
    r.world.output = b.output := by
  rcases r.choice with ⟨_, _, world, _⟩ | ⟨actual, _, _, world, _⟩
  · rw [world]
  · rw [world]; exact actual.output

/-- The optional callback preserves its own incoming output buffer. -/
theorem SwapOptionalCallback.output_eq {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {q toWord a0 a1 len dataStart : B256} {K : List SFunc}
    (r : SwapOptionalCallback root start b L M q toWord a0 a1 len dataStart K) :
    r.world.output = b.output := by
  rcases r.choice with ⟨_, _, world, _⟩ | ⟨actual, _, _, world, _⟩
  · rw [world]
  · rw [world]; exact actual.output

/-- The same physical endpoint retains the original input output buffer. -/
theorem SwapBalances.output_eq {root : Exec.Deriv} {b post : Devm}
    (r : SwapBalances root root.sevm b) (success : root.exn = .ok post)
    (fork : CoveredFork root.sevm.benvStat.fork) : post.output = b.output := by
  obtain ⟨_, M, gas, image⟩ := r.post_image success fork
  rw [image, St, Devm.setMach_output, SwapBalances.finalWorld, afterSstore_output]
  generalize world : updateWorld root.sevm r.second.step.returned.devm
    (swapRawReserve0 root.sevm b) (swapRawReserve1 root.sevm b) r.balance0 r.balance1 = w
  change w.output = b.output
  rw [← world, updateWorld_output, r.second.reply.output rfl, temporalAccountAccessBase_output,
    r.first.reply.output rfl, temporalAccountAccessBase_output, r.optional.callback.output_eq,
    r.optional.transfers.second.output_eq, r.optional.transfers.first.output_eq,
    swapPrefixWorld, afterSload_output, afterSload_output, afterSload_output,
    mintLockedWorld, afterSstore_output, afterSload_output]

/-- One complete physical Swap chain, including its actual suffix endpoint. -/
structure SwapPhysicalResult (root : Exec.Deriv) (b post : Devm) where
  balances : SwapBalances root root.sevm b
  facts : SwapSuffixFacts balances
  image : ∃ M gas, post = St balances.finalWorld [0x022c0d9f] M gas
  output : post.output = b.output

/-- Only the original code, fork, selector and successful root execution are
required for the complete optional-call chain and the same actual endpoint. -/
theorem swap_physical_result {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (SwapPhysicalResult ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) := by
  obtain ⟨r⟩ := swap_balances_cursor_state codeEq fork selector run
  obtain ⟨facts, image⟩ := r.post_image rfl fork
  exact ⟨⟨r, facts, image, r.output_eq rfl fork⟩⟩

end Blanc.Lift.UniswapV2Pair
