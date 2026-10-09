import Blanc.Lift.UniswapV2Pair.MintPositionalQueues
import Blanc.Lift.UniswapV2Pair.MintPositionalConsume

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def MintPositionalQueues.transcript {root : Exec.Deriv} {b : Devm}
    {current : Checkpoint} {invocation : List Nat} {r : MintRootCallPositions root b}
    (q : MintPositionalQueues current invocation r) : Transcript :=
  .next (feeObservedResult r.out0) (staticViewTranscript q.views0 .done)
    (.next (feeObservedResult r.out1) (staticViewTranscript q.views1 .done)
      (.next (feeObservedResult r.fee.out) (staticViewTranscript q.viewsF .done) .done))

def MintPositionalQueues.childReturns {root : Exec.Deriv} {b : Devm}
    {current : Checkpoint} {invocation : List Nat} {r : MintRootCallPositions root b}
    (q : MintPositionalQueues current invocation r) : List ChildReturn :=
  staticViewChildReturns
    (mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
    (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)) 0 q.views0 ++
  (staticViewChildReturns
    ((mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr).beginResume
      (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)))
    (requestFor .mintBalance1 current.state.token1 (.balanceOf root.sevm.currentTarget)) 0 q.views1 ++
  (staticViewChildReturns
    (mintSourceFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
    (requestFor .mintFeeTo current.state.factory .feeTo) 0 q.viewsF ++ []))

/-- The canonical source and finite result are correlated with the three
original Mint calls, their full slot queues, and the supplied incoming state. -/
structure MintPositionalCanonicalResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (root : Exec.Deriv) (b post : Devm) where
  positions : MintRootCallPositions root b
  queues : MintPositionalQueues current invocation positions
  value : root.sevm.value = 0
  nonstatic : root.sevm.isStatic = false
  feeNode : Exec.Deriv
  feeGas : Nat
  feeFree : Exec.Deriv.ExecFreeUntil positions.fee.occurrence.call.returned feeNode
  sourceFee : FeeMintSourceResult K {current.state with unlocked := 0} root.sevm
    (mintPositionalFeeBase positions) (mintPositionalLocals positions) (mintPositionalFeeMemory positions)
    (mintPositionalFeeWord positions) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas
  feeState : feeNode.devm = feeBranchPost root.sevm (mintPositionalFeeBase positions)
    (mintPositionalLocals positions) (mintPositionalFeeMemory positions) current.state.kLast
    (mintPositionalFeeWord positions) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas
  final : Frame
  liquidity : Nat
  keys : WriterKey → Prop
  footprint : keys = (if (mintPositionalFeeResult current positions).state.totalSupply = 0 then
    WriterExtend (WriterExtend (mintPositionalFeeKeys K current positions) (lpMintTouched (0 : B256).toAdr))
      (lpMintTouched (Sevm.dataWord root.sevm 4).toAdr)
    else WriterExtend (mintPositionalFeeKeys K current positions) (lpMintTouched (Sevm.dataWord root.sevm 4).toAdr))
  typedFinished :
    (mintSourceAfterFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr).mintAfterFee
      (mintBalanceObserved current.state (Sevm.dataWord root.sevm 4).toAdr
        (Bytes.toB256 (positions.out0.take 32)) (Bytes.toB256 (positions.out1.take 32)))
      (mintPositionalFeeResult current positions) = .finished final (encodeWords [liquidity.toB256])
  positional : PositionalConsumes root root 0
    (startTyped current (writerContext root.sevm invocation) (.mint (Sevm.dataWord root.sevm 4).toAdr))
    queues.transcript
    {status := .success (encodeWords [liquidity.toB256]), frame := final,
      remaining := .done, childReturns := queues.childReturns}
  admission : ∀ Auth : Exec.Deriv → Entry → Transcript → Prop,
    SourceAdmission Auth positional
  checkpoint : final.checkpoint = current
  context : final.context = writerContext root.sevm invocation
  unlocked : final.current.state.unlocked = 1
  grown : ∀ k, keys k → WriterExtend K (mintTraceKeys root) k
  storage : WriterRep keys (post.getStor root.sevm.currentTarget) final.current.state
  output : post.output = encodeWords [liquidity.toB256]
  logs : post.logs = feeNode.devm.logs ++
    (if (mintPositionalFeeResult current positions).state.totalSupply = 0 then
      [lpMintRawLog root.sevm.currentTarget (0 : B256).toAdr 1000] else []) ++
    [lpMintRawLog root.sevm.currentTarget (Sevm.dataWord root.sevm 4).toAdr liquidity.toB256,
      ⟨root.sevm.currentTarget, [updateSyncTopic],
        encodeWords [Bytes.toB256 (positions.out0.take 32), Bytes.toB256 (positions.out1.take 32)]⟩,
      ⟨root.sevm.currentTarget, [mintEventTopic, root.sevm.caller.toB256],
        (Bytes.toB256 (positions.out0.take 32) - mintRootReserve0 root b).toBytes ++
        (Bytes.toB256 (positions.out1.take 32) - mintRootReserve1 root b).toBytes⟩]

/-- Every successful original Mint root supplies one correlated canonical
result. Its requests, full reply queues, finite state and output are all those
of the same actual three-call certificate at the supplied incoming checkpoint. -/
theorem mint_positional_canonical {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (inj : WriterInj
      (WriterExtend K (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (apart : WriterApart
      (WriterExtend K (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (MintPositionalCanonicalResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨r⟩ := mint_three_occurrences_of_success codeEq fork selector run
  have fresh : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys K (staticViewDecodedKeys F.sevm) := by
    intro F member target
    exact Blanc.SlotFootprint.FreshKeys.of_universe inj apart
      (fun _ tracked => Or.inl tracked)
      (fun k touched => Or.inr (mintTraceKeys_frame member target k touched))
  obtain ⟨q⟩ := mint_positional_queues run r rep invocation sem image installed fork fresh
  obtain ⟨value, nonstatic, handlers⟩ :=
    mint_positional_balance_handlers run r rep invocation codeEq fork selector
  obtain ⟨feeN, feeGas, free, sourceFee, feeState, frameResult⟩ :=
    mint_positional_source_finish run r rep invocation fork inj apart
  obtain ⟨liquidity, keys, final, d, footprint, typedFinished, storage,
    halted, output, logs⟩ := frameResult
  have dPost : post = d := Outcome.halted.inj halted
  subst dPost
  have feeFinished := (r.feeResume rep invocation sourceFee).trans typedFinished
  have positional := q.positionalConsumes fork handlers feeFinished
  obtain ⟨checkpoint, context, unlocked⟩ := mintAfterFee_finished_shape typedFinished
  have sub : ∀ k, K k → WriterExtend K (mintTraceKeys root) k := fun _ tracked => Or.inl tracked
  have feeRow : WriterExtend K (mintTraceKeys root)
      (.balance (mintPositionalFeeWord r).toAdr) := Or.inr (r.feeReplyKey fork)
  have feeKeys : ∀ k, mintPositionalFeeKeys K current r k → WriterExtend K (mintTraceKeys root) k :=
    mint_feeKeys_sub sub feeRow {current.state with unlocked := 0} sevm
      (mintPositionalFeeBase r) (mintRootReserve0 root b) (mintRootReserve1 root b)
  have zeroRows : ∀ k ∈ lpMintTouched (0 : B256).toAdr,
      WriterExtend K (mintTraceKeys root) k := by
    intro k member
    simp only [lpMintTouched, List.mem_cons, List.not_mem_nil, or_false] at member
    rw [member]
    exact Or.inr (mintTraceKeys_rows root).1
  have recipientRows : ∀ k ∈ lpMintTouched (Sevm.dataWord sevm 4).toAdr,
      WriterExtend K (mintTraceKeys root) k := by
    intro k member
    simp only [lpMintTouched, List.mem_cons, List.not_mem_nil, or_false] at member
    rw [member]
    exact Or.inr (mintTraceKeys_rows root).2
  have grown : ∀ k, keys k → WriterExtend K (mintTraceKeys root) k := by
    rw [footprint]
    intro k tracked
    split at tracked
    · rcases tracked with (old | zeroRow) | recipientRow
      · exact feeKeys k old
      · exact zeroRows k zeroRow
      · rw [toAdr_toB256] at recipientRow
        exact recipientRows k recipientRow
    · rcases tracked with old | recipientRow
      · exact feeKeys k old
      · rw [toAdr_toB256] at recipientRow
        exact recipientRows k recipientRow
  have framePair : (mintSourceAfterFeeFrame current (writerContext sevm invocation)
      (Sevm.dataWord sevm 4).toAdr).context.pair = sevm.currentTarget := rfl
  have frameSender : (mintSourceAfterFeeFrame current (writerContext sevm invocation)
      (Sevm.dataWord sevm 4).toAdr).context.sender = sevm.caller := rfl
  refine ⟨{
    positions := r, queues := q, value := value, nonstatic := nonstatic,
    feeNode := feeN, feeGas := feeGas, feeFree := free, sourceFee := sourceFee,
    feeState := feeState, final := final, liquidity := liquidity, keys := keys,
    footprint := ?_, typedFinished := typedFinished, positional := positional,
    admission := fun Auth => (q.admittedConsumes (Auth := Auth) fork handlers feeFinished).choose_spec,
    checkpoint := checkpoint, context := context, unlocked := unlocked,
    grown := grown, storage := storage, output := output, logs := ?_}⟩
  · simpa only [toAdr_toB256] using footprint
  · simpa only [toAdr_toB256, framePair, frameSender] using logs

/-- Erasure retains the same transcript, final model frame and successful bytes. -/
theorem MintPositionalCanonicalResult.exactConsumes {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (result : MintPositionalCanonicalResult K current invocation root b post) :
    ExactConsumes
      (startTyped current (writerContext root.sevm invocation) (.mint (Sevm.dataWord root.sevm 4).toAdr))
      result.queues.transcript
      {status := .success (encodeWords [result.liquidity.toB256]), frame := result.final,
        remaining := .done, childReturns := result.queues.childReturns} :=
  result.positional.forget

end Blanc.Lift.UniswapV2Pair
