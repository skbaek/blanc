import Blanc.Lift.UniswapV2Pair.BurnPositionalCuts
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.InvWalkGas
import Blanc.Lift.UniswapV2Pair.BurnPositionalInv

/-! Actual Burn call positions in the checked original-bytecode execution. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnFirstRequestCost (sevm : Sevm) (b : Devm) : Nat :=
  5 + sloadCost sevm b 6 + sloadCost sevm (afterSload sevm b 6) 7 +
    temporalAccountAccessCost (burnTokensWorld sevm b)
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        b.getStorVal sevm.currentTarget 6).toAdr + 184

def burnFirstEntryGas (sevm : Sevm) (b : Devm) (G : Nat) : Nat :=
  let locked := burnLockedWorld sevm b
  let reserves := afterSload sevm locked 8
  G + burnFirstRequestCost sevm reserves + sloadCost sevm locked 8 + 78 +
    sstoreCost sevm (afterSload sevm b 12) 12 0 + sloadCost sevm b 12 + 51

/-- A gas-scheduled source entry produces the actual first Burn call.
The request, node, filled slot and returned parent all belong to the supplied
execution; no endpoint or selected call is a premise. -/
theorem burn_first_occurrence_scheduled {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abiSize : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (nonstatic : sevm.isStatic = false)
    (sentry : gCallStipend <
      G + burnFirstRequestCost sevm (afterSload sevm (burnLockedWorld sevm b) 8) +
        sloadCost sevm (burnLockedWorld sevm b) 8 + 78 + 9 +
        sstoreCost sevm (afterSload sevm b 12) 12 0)
    (nonzero : ((burnTokensWorld sevm (afterSload sevm (burnLockedWorld sevm b) 8)).getCode
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
        (afterSload sevm (burnLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6).toAdr).size.toB256 ≠ 0)
    (run : Exec 0 sevm (St b [] Mem.empty (burnFirstEntryGas sevm b G + 249)) (.ok post)) :
    let root : Exec.Deriv :=
      ⟨0, sevm, St b [] Mem.empty (burnFirstEntryGas sevm b G + 249), .ok post, run⟩
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor),
      Exec.Deriv.ExecFreeUntil root step.occurrence.node ∧
      step.occurrence.node.sevm = sevm ∧
      step.occurrence.node.exn = .ok post ∧
      step.occurrence.node.devm = burnFirstCallInput sevm
        (afterSload sevm (burnLockedWorld sevm b) 8) [0x89afcb44] getterInitMemory G
        (reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (Sevm.dataWord sevm 4).toAdr.toB256 0x053d ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor := by
  let root : Exec.Deriv :=
    ⟨0, sevm, St b [] Mem.empty (burnFirstEntryGas sevm b G + 249), .ok post, run⟩
  let locked := burnLockedWorld sevm b
  let reserves := afterSload sevm locked 8
  let requestGas := G + burnFirstRequestCost sevm reserves
  let reserveGas := requestGas + sloadCost sevm locked 8 + 78
  let entryGas := burnFirstEntryGas sevm b G
  let toWord := (Sevm.dataWord sevm 4).toAdr.toB256
  obtain ⟨abi, κabi, gapAbi, envAbi, outcomeAbi, okAbi, treeAbi, stateAbi⟩ :=
    burn_dispatch_positional_cut codeEq fork value size abiSize selector run
  have popAbi : Devm.PopBurnBy [0x13f5] gMid abi.devm
      (St b [toWord, 0x053d, 0x89afcb44] getterInitMemory entryGas) := by
    rw [stateAbi]
    exact popBurnBy_St1
  obtain ⟨entry, κentry, gapEntry, envEntry, outcomeEntry, okEntry, treeEntry, stateEntry⟩ :=
    cursor_callNext_exact cert_check okAbi treeAbi outcomeAbi
      (by rw [envAbi]; exact fork) popAbi
  have envEntryRoot : entry.sevm = sevm := envEntry.trans envAbi
  have successEntry : entry.exn = .ok post := outcomeEntry.trans outcomeAbi
  have treeEntry' : κentry.f = t_13f5_c37 := by
    change some t_13f5_c37 = some κentry.f at treeEntry
    exact (Option.some.inj treeEntry).symm
  have stateEntry' : entry.devm = St b (toWord :: 0x053d :: [0x89afcb44]) getterInitMemory
      (reserveGas + sstoreCost entry.sevm (afterSload entry.sevm b 12) 12 0 +
        sloadCost entry.sevm b 12 + 51) := by
    rw [envEntryRoot]
    exact stateEntry
  obtain ⟨callReserve, κcall, gapLock, envLock, outcomeLock, okCall, treeCall, stateCall⟩ :=
    burn_reserve_positional_cut okEntry treeEntry' successEntry
      (by rw [envEntryRoot]; exact fork) stateEntry' (by decide)
      (by rw [envEntryRoot]; exact unlocked) (by rw [envEntryRoot]; exact nonstatic)
      (by rw [envEntryRoot]; exact sentry)
  have envCall : callReserve.sevm = sevm := envLock.trans envEntryRoot
  have successCall : callReserve.exn = .ok post := outcomeLock.trans successEntry
  have popCall : Devm.PopBurnBy [0x0d90] gMid callReserve.devm
      (St locked (0x1479 :: 0 :: 0 :: 0 :: 0 :: toWord :: 0x053d :: [0x89afcb44])
        getterInitMemory (requestGas + sloadCost sevm locked 8 + 70)) := by
    rw [stateCall, envEntryRoot]
    change Devm.PopBurnBy [0x0d90] gMid
      (St locked _ getterInitMemory (requestGas + sloadCost sevm locked 8 + 78)) _
    rw [show requestGas + sloadCost sevm locked 8 + 78 =
      (requestGas + sloadCost sevm locked 8 + 70) + gMid by unfold gMid; omega]
    exact popBurnBy_St1
  obtain ⟨callee, κcallee, cont, gapCall, envCallee, outcomeCallee, okCallee,
      lookupCallee, stateCallee, KCallee, bodyCont⟩ :=
    cursor_callNext_exact_cont cert_check okCall treeCall successCall
      (by rw [envCall]; exact fork) popCall
  have envCalleeRoot : callee.sevm = sevm := envCallee.trans envCall
  have successCallee : callee.exn = .ok post := outcomeCallee.trans successCall
  have treeCallee : κcallee.f = t_0d90_c56 := by
    change some t_0d90_c56 = some κcallee.f at lookupCallee
    exact (Option.some.inj lookupCallee).symm
  obtain ⟨ret, κret, gapReserves, envRet, outcomeRet, okRet, treeRet, stateRet, KRet⟩ :=
    burn_reserve_return_positional_cut okCallee treeCallee successCallee
      (by rw [envCalleeRoot]; exact fork)
      (by rw [envCalleeRoot]; exact stateCallee)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have envRetRoot : ret.sevm = sevm := envRet.trans envCalleeRoot
  have successRet : ret.exn = .ok post := outcomeRet.trans successCallee
  have popRet : Devm.PopBurnBy [0x1479] gMid ret.devm
      (St reserves
        (reserveTimestampRead (locked.getStorVal sevm.currentTarget 8) ::
          reserve1Read (locked.getStorVal sevm.currentTarget 8) ::
          reserve0Read (locked.getStorVal sevm.currentTarget 8) ::
          0 :: 0 :: 0 :: 0 :: toWord :: 0x053d :: [0x89afcb44]) getterInitMemory requestGas) := by
    rw [stateRet, envCalleeRoot]
    exact popBurnBy_St1
  obtain ⟨request, κrequest, gapRet, envRequest, outcomeRequest, okRequest,
      treeRequest, stateRequest, _⟩ :=
    cursor_ret_exact_cont cert_check okRet treeRet (KRet.trans KCallee)
      successRet (by rw [envRetRoot]; exact fork) popRet
  have envRequestRoot : request.sevm = sevm := envRequest.trans envRetRoot
  have successRequest : request.exn = .ok post := outcomeRequest.trans successRet
  obtain ⟨call, κcall, gapRequest, envFirst, outcomeFirst, okFirst, treeFirst, stateFirst⟩ :=
    burn_first_request_positional_cut (b := reserves) (R := [0x89afcb44]) (G := G)
      okRequest (treeRequest.trans bodyCont) successRequest
      (by rw [envRequestRoot]; exact fork)
      (by rw [envRequestRoot]; simpa only [requestGas, burnFirstRequestCost, Nat.add_assoc] using stateRequest)
      getterInitMemory_ptr (by decide) (by rw [envRequestRoot]; exact nonzero)
  have gap : Exec.Deriv.ExecFreeUntil root call :=
    gapAbi.trans (gapEntry.trans (gapLock.trans (gapCall.trans
      (gapReserves.trans (gapRet.trans gapRequest)))))
  have envFirstRoot : call.sevm = sevm := envFirst.trans envRequestRoot
  have successFirst : call.exn = .ok post := outcomeFirst.trans successRequest
  obtain ⟨step, cursor, nodeEq, _, primitive, _, _, placed⟩ :=
    cursor_next_call_occurrence_forward cert_check gap.1 okFirst treeFirst successFirst
      (by rw [envFirstRoot]; exact fork)
  refine ⟨step, cursor, ?_, ?_, ?_, ?_, ?_, placed⟩
  · rw [nodeEq]; exact gap
  · rw [nodeEq]; exact envFirstRoot
  · rw [nodeEq]; exact successFirst
  · rw [nodeEq, stateFirst, envRequestRoot]
  · simpa only [nodeEq, envFirstRoot] using primitive

/-- GAS and the first STATICCALL use the supplied actual request cursor.
The word supplied as call gas equals the actual successor's remaining gas. -/
theorem burn_first_call_of_request_cursor {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {r1 r0 toWord extρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_14fb_c37
      (temporalAccountAccessBase (burnTokensWorld root.sevm b)
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal root.sevm.currentTarget 6).toAdr)
      (0 :: ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal root.sevm.currentTarget 6) :: 128 :: 36 :: 128 :: 32 :: 164 ::
        0x70a08231 :: ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal root.sevm.currentTarget 6) :: 0 ::
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          (afterSload root.sevm b 6).getStorVal root.sevm.currentTarget 7) ::
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal root.sevm.currentTarget 6) ::
        r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M root.sevm.currentTarget) K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil root step.occurrence.node ∧
      step.occurrence.node.sevm = root.sevm ∧
      step.occurrence.node.exn = root.exn ∧
      step.occurrence.node.devm = burnFirstCallInput root.sevm b R M gas r1 r0 toWord extρ ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) root.sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧
      cursor.f = burnFirstAfterCallTree ∧ cursor.K.map Cont.f = K := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨beforeGas⟩ := opened.line cert_check success fork [.reg .pop] (by rfl)
    (by intro n member x equal; simp only [List.mem_singleton, equal, reduceCtorEq] at member)
    (by
      intro g d line
      obtain ⟨_, pop, tail⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_pop pop
      cases tail
      exact ⟨g', state⟩)
  obtain ⟨call, κ, _, _, sameSevm, sameExn, placed, tree, line, sameK, free⟩ :=
    cursor_nexts_line_cont_free_forward cert_check beforeGas.placed [.reg .gas]
      (.next (.exec .staticcall) burnFirstAfterCallTree)
      (beforeGas.tree.trans (by rfl)) (beforeGas.exn_eq.trans success)
      (by rw [beforeGas.sevm_eq]; exact fork)
  obtain ⟨g, state⟩ := beforeGas.state
  rw [beforeGas.sevm_eq, state] at line
  obtain ⟨_, primitive, tail⟩ := Line.of_run_cons line
  cases tail
  obtain ⟨gas, callState⟩ := ri_gas_remaining primitive
  have gap := beforeGas.free.trans (free (by
    intro n member x equal
    simp only [List.mem_singleton, equal, reduceCtorEq] at member))
  have env := sameSevm.trans beforeGas.sevm_eq
  have outcome := sameExn.trans beforeGas.exn_eq
  obtain ⟨step, cursor, nodeEq, _, primitiveCall, synthetic, _, returned⟩ :=
    cursor_next_call_occurrence_forward cert_check gap.1 placed tree
      (outcome.trans success) (by rw [env]; exact fork)
  have nextShape : cursor.f = burnFirstAfterCallTree ∧ cursor.K = κ.K := by
    rcases κ with ⟨f, pc, a, m, pending⟩
    dsimp only at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  refine ⟨step, cursor, gas, ?_, ?_, ?_, ?_, ?_, returned, nextShape.1, ?_⟩
  · rw [nodeEq]; exact gap
  · rw [nodeEq]; exact env
  · rw [nodeEq]; exact outcome
  · rw [nodeEq]
    exact callState
  · simpa only [nodeEq, env] using primitiveCall
  · rw [nextShape.2, sameK]; exact beforeGas.continuations

/-- A successful public Burn execution produces its first original-bytecode
balance STATICCALL, exact request, filled actual slot and returned cursor.
All prefix guards and residual gas are derived from this supplied execution. -/
theorem burn_first_occurrence_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil root step.occurrence.node ∧
      step.occurrence.node.sevm = sevm ∧
      step.occurrence.node.exn = .ok post ∧
      step.occurrence.node.devm = burnFirstCallInput sevm
        (afterSload sevm (burnLockedWorld sevm b) 8) [0x89afcb44] getterInitMemory gas
        (reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (Sevm.dataWord sevm 4).toAdr.toB256 0x053d ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧
      cursor.f = burnFirstAfterCallTree ∧ cursor.K.map Cont.f = [t_053d_c83] := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨_, _, abiSize, unlocked, _, nonzero⟩ :=
    burn_prefix_guards_of_success codeEq fork selector run
  obtain ⟨publicEntry⟩ := burn_public_cursor_state codeEq fork selector run
  obtain ⟨entry⟩ := burn_abi_cursor_state publicEntry rfl fork abiSize
  obtain ⟨reserveEntry⟩ := burn_lock_cursor_state entry rfl fork unlocked
  obtain ⟨requestEntry⟩ := burn_reserves_cursor_state reserveEntry rfl fork
  obtain ⟨request⟩ := burn_first_guard_cursor_state requestEntry rfl fork
    getterInitMemory_ptr nonzero
  exact burn_first_call_of_request_cursor request rfl fork

end Blanc.Lift.UniswapV2Pair
