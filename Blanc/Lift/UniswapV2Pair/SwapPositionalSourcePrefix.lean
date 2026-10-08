import Blanc.Lift.UniswapV2Pair.SwapPositionalMutableTransfer

/-! The original typed Swap prefix composes its same admitted optional transfers. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The source lock, guards and cached words derive from the original run. -/
structure SwapSourcePrefix (U : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (sevm : Sevm) (b : Devm) : Prop where
  value : sevm.value = 0
  nonstatic : sevm.isStatic = false
  token0 : swapInitialToken0 sevm b = current.state.token0.toB256
  token1 : swapInitialToken1 sevm b = current.state.token1.toB256
  reserve0 : swapRawReserve0 sevm b = Nat.toB256 current.state.reserve0.val
  reserve1 : swapRawReserve1 sevm b = Nat.toB256 current.state.reserve1.val
  started : startTyped current (writerContext sevm invocation) (swapDecodedEntry sevm) =
    swapTransferPhaseStart false
      (swapLockedFrame current (writerContext sevm invocation) (swapDecodedEntry sevm))
      (swapFrontLocals sevm current.state)
  invariant : SwapFrontState U sevm.currentTarget (writerContext sevm invocation) current b
    (swapLockedFrame current (writerContext sevm invocation) (swapDecodedEntry sevm))
    (swapPrefixWorld sevm b)

/-- Initial finite storage fixes the four raw cached Swap words. -/
theorem swap_source_cached_words {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state) :
    swapInitialToken0 sevm b = current.state.token0.toB256 ∧
    swapInitialToken1 sevm b = current.state.token1.toB256 ∧
    swapRawReserve0 sevm b = Nat.toB256 current.state.reserve0.val ∧
    swapRawReserve1 sevm b = Nat.toB256 current.state.reserve1.val := by
  have fixed := (rep.mint_locked_world (sevm := sevm) (b := b)).fixed
  obtain ⟨_, _, _, token0, token1, reserve0, reserve1, _⟩ := fixed
  have storage (k : B256) :
      (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget k =
        (mintLockedWorld sevm b).getStorVal sevm.currentTarget k := by
    change ((afterSload sevm (mintLockedWorld sevm b) 8).getStor sevm.currentTarget).get k = _
    rw [afterSload_getStor]
    rfl
  have maskWord : ∀ x : B256, (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& x =
      x.toAdr.toB256 := fun x => ff20_and_word x
  refine ⟨?_, ?_, reserve0, reserve1⟩
  · rw [swapInitialToken0, maskWord, storage]
    exact congrArg Adr.toB256 token0
  · rw [swapInitialToken1, maskWord, storage]
    exact congrArg Adr.toB256 token1

/-- Existing inverses derive only the original source guards and starting segment. -/
theorem swap_source_start_of_success {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat) (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ sevm.isStatic = false ∧
    startTyped current (writerContext sevm invocation) (swapDecodedEntry sevm) =
      swapTransferPhaseStart false
        (swapLockedFrame current (writerContext sevm invocation) (swapDecodedEntry sevm))
        (swapFrontLocals sevm current.state) := by
  obtain ⟨f, entry, derived⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, _, _, _, _, body, _⟩ := swapPc0_inv selector derived
  obtain ⟨unlocked, nonstatic, output, lt0, lt1, ne0, ne1, _, _⟩ :=
    swapBody_prefix_inv fork rep (SFunc.runP_iff_runCutP_nil.mp body)
  have started := swap_startTyped (current := current) (ctx := writerContext sevm invocation)
    (data := swapData sevm) value nonstatic unlocked (output.imp swap_pos_of_ne swap_pos_of_ne)
    lt0 lt1 ne0 ne1
  refine ⟨value, nonstatic, ?_⟩
  simpa only [swapTransferPhaseStart, swapTransferPhaseRequest, swapFrontLocals,
    swapSourceLocals, swapDecodedEntry, Frame.suspend, Bool.false_eq_true, ite_false]
    using started

/-- No optional-call or model witness is selected from the legacy inverses. -/
theorem swap_source_prefix_of_success {K U : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat) (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sub : ∀ k, K k → U k)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    SwapSourcePrefix U current invocation sevm b := by
  obtain ⟨token0, token1, reserve0, reserve1⟩ := swap_source_cached_words rep
  obtain ⟨value, nonstatic, started⟩ := swap_source_start_of_success invocation rep codeEq fork selector run
  exact ⟨value, nonstatic, token0, token1, reserve0, reserve1, started,
    swap_prefix_source_invariant rep sub⟩

/-- Both admitted transfer phases start at the original decoded Swap entry,
sharing this physical chain's actual nodes and the same evolving source frame. -/
theorem swap_source_transfers {root : Exec.Deriv} {b : Devm}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (r : SwapTransfers root root.sevm b)
    (entryFacts : SwapSourcePrefix U current invocation root.sevm b)
    (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode root.sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → LockedGood U F) :
    let locals := swapFrontLocals root.sevm current.state
    let count0 := if swapAmount0Out root.sevm = 0 then 0 else 1
    let count1 := if swapAmount1Out root.sevm = 0 then 0 else 1
    ∃ (frame : Frame) (T : Transcript → Transcript) (rets : List ChildReturn),
      SwapFrontState U root.sevm.currentTarget (writerContext root.sevm invocation)
        current b frame r.second.world ∧
      ∀ tail out,
        AdmittedSourceConsumes LockedAuth root r.second.next (count0 + count1)
          (frame.afterSwapTransfer1 locals) tail out →
        AdmittedSourceConsumes LockedAuth root root 0
          (startTyped current (writerContext root.sevm invocation) (swapDecodedEntry root.sevm))
          (T tail) {out with childReturns := rets ++ out.childReturns} := by
  intro locals count0 count1
  have token0 : (swapInitialToken0 root.sevm b).toAdr = current.state.token0 := by
    rw [entryFacts.token0, toAdr_toB256]
  have token1 : (swapInitialToken1 root.sevm b).toAdr = current.state.token1 := by
    rw [entryFacts.token1, toAdr_toB256]
  have recipient : (swapRecipientWord root.sevm).toAdr = swapRecipient root.sevm := by
    rw [swapRecipientWord_eq, toAdr_toB256]
  obtain ⟨F0, T0, R0, inv0, reach0⟩ := swap_optional_transfer_admitted (locals := locals) false r.first
    token0 recipient 0 inj apart sem image installed entryFacts.invariant rfl rfl entryFacts.nonstatic
    entryFacts.nonstatic fork good
  obtain ⟨F1, T1, R1, inv1, reach1⟩ := swap_optional_transfer_admitted (locals := locals) true r.second
    token1 recipient count0 inj apart sem image installed inv0 rfl rfl entryFacts.nonstatic
    entryFacts.nonstatic fork good
  refine ⟨F1, fun tail => T0 (T1 tail), R0 ++ R1, inv1, ?_⟩
  intro tail out rest
  simp only [Bool.false_eq_true, ite_false, Nat.zero_add, swapTransferPhaseEnd,
    show locals.amount0Out = swapAmount0Out root.sevm from rfl] at reach0
  simp only [ite_true, swapTransferPhaseEnd, swapTransferPhaseStart,
    show locals.amount1Out = swapAmount1Out root.sevm from rfl] at reach1
  have second := reach1 tail out rest
  have first := reach0 (T1 tail) _ second
  exact Eq.mpr (congrArg (fun segment =>
    AdmittedSourceConsumes LockedAuth root root 0 segment (T0 (T1 tail))
      {out with childReturns := (R0 ++ R1) ++ out.childReturns}) entryFacts.started)
    (by simpa only [List.append_assoc] using first)

end Blanc.Lift.UniswapV2Pair
