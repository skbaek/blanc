import Blanc.Lift.UniswapV2Pair.PairHistoryLive
import Blanc.Lift.UniswapV2Pair.PermitEntries
import Blanc.Lift.UniswapV2Pair.InitializeEntries

/-!
# Gas-exact liveness of `permit` and `initialize` after any configured history

The remaining state-changing entries of U6/M6: `pair_history_permit_live` (the `ECRECOVER` precompile's
answer is the callee input, as in `permit_bytecode_live_raw`) and `pair_history_initialize_live`, each
one `pair_live_outcome` call over the pc-zero run, with model acceptance at the history's state
`finish` bridged by `runTyped_permit_conditions` / `runTyped_initialize_conditions`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc.ExecutionTrace

/-! ## Model acceptance gives the guards -/

/-- A successful `initialize` in the model is non-payable, from the factory, and non-static. -/
theorem runTyped_initialize_conditions {st : State} {ctx : Context} {token0 token1 : Adr}
    {transcript : Transcript} {returndata : Bytes}
    (successful : (runTyped st ctx (.initialize token0 token1) transcript).status =
      .success returndata) :
    ctx.value = 0 ∧ ctx.sender = st.factory ∧ ctx.isStatic = false := by
  let current : Checkpoint := { state := st, logs := [], updates := [] }
  change (drive (transcript.work + 2) (startTyped current ctx (.initialize token0 token1))
    transcript).status = .success returndata at successful
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ .emptyRevert transcript returndata successful)
  have authCurrent : ∀ h : ctx.sender = current.state.factory, ctx.sender = st.factory := id
  by_cases auth : ctx.sender = current.state.factory
  swap
  · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, ite_eq_right auth,
      Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ (.sourceGuard "UniswapV2: FORBIDDEN")
      transcript returndata successful)
  by_cases staticContext : ctx.isStatic = true
  · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, ite_eq_left auth,
      staticContext, ite_true, Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ .staticWrite transcript returndata successful)
  refine ⟨by by_contra h; exact paid h, authCurrent auth, ?_⟩
  cases h : ctx.isStatic
  · rfl
  · exact absurd h staticContext

/-- The `ECRECOVER` answer the model reads: the first transcript entry's recovery output. -/
def Transcript.firstRecovered : Transcript → Adr
  | .next result _ _ => result.recoveryOutput.toAdr
  | _ => 0

/-- A successful `permit` in the model is non-payable, non-static, before its deadline, and its
recovered signer is the nonzero owner. -/
theorem runTyped_permit_conditions {st : State} {ctx : Context} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    {transcript : Transcript} {returndata : Bytes}
    (successful : (runTyped st ctx (.permit owner spender value deadline v r s) transcript).status =
      .success returndata) :
    ctx.value = 0 ∧ ctx.isStatic = false ∧ ctx.timestamp ≤ deadline ∧
      transcript.firstRecovered ≠ 0 ∧ transcript.firstRecovered = owner := by
  let current : Checkpoint := { state := st, logs := [], updates := [] }
  change (drive (transcript.work + 2)
    (startTyped current ctx (.permit owner spender value deadline v r s)) transcript).status =
      .success returndata at successful
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ .emptyRevert transcript returndata successful)
  by_cases timely : ctx.timestamp ≤ deadline
  swap
  · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, ite_eq_right timely,
      Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ (.sourceGuard "UniswapV2: EXPIRED")
      transcript returndata successful)
  by_cases staticContext : ctx.isStatic = true
  · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, ite_eq_left timely,
      staticContext, ite_true, Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ .staticWrite transcript returndata successful)
  have nonstatic : ctx.isStatic = false := by
    cases h : ctx.isStatic
    · rfl
    · exact absurd h staticContext
  simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, ite_eq_left timely,
    nonstatic, Frame.suspend] at successful
  generalize transcript.work + 2 = fuel at successful
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
      drive_suspended_success successful
    cases decoded : decodeExternal (requestFor .permitRecovery 1 (.recover (permitDigest
        current.state owner spender value (current.state.nonces owner) deadline) v r s)) result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | word w =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | address recovered =>
        have recoveredEq : recovered = result.recoveryOutput.toAdr := by
          by_cases ok : result.success = true
          · simp only [decodeExternal, requestFor, ok, Bool.false_and, Bool.false_eq_true,
              ite_false, ite_true, Except.ok.injEq, DecodedResult.address.injEq] at decoded
            exact decoded.symm
          · simp only [decodeExternal, requestFor, ok, Bool.false_and, Bool.false_eq_true,
              ite_false] at decoded
            cases decoded
        have firstEq : transcript.firstRecovered = recovered := by
          rw [shape, Transcript.firstRecovered, recoveredEq]
        simp only [resumeSegment, decoded] at resumedSuccess
        by_cases good : recovered ≠ 0 ∧ recovered = owner
        · refine ⟨by by_contra h; exact paid h, nonstatic, timely, ?_, ?_⟩
          · rw [firstEq]; exact good.1
          · rw [firstEq]; exact good.2
        · rw [ite_eq_right good, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "UniswapV2: INVALID_SIGNATURE") tail returndata resumedSuccess)

/-! ## The liveness instances -/

/-- **`initialize` after any configured history.**  When the model accepts the decoded
`initialize(token0, token1)` at the history's state `finish` (the call is non-payable and non-static
and comes from the factory), a pc-zero run exists at the closed gas
`G + initializeStorageCharge sevm pre + 377` ending at gas `G`; under HASH-T freshness of its own rows
its post storage represents the model's next state.  Premises: the history's; the new frame's
environment and calldata length guard; the two store sentries; model acceptance at `finish`
(`runTyped_initialize_conditions`). -/
theorem pair_history_initialize_live {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (sentry0 : gCallStipend < G + initializeStore0Charge sevm pre + initializeLoad1Charge sevm pre +
      initializeStore1Charge sevm pre + 39)
    (sentry1 : gCallStipend < G + initializeStore1Charge sevm pre + 9) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        (runTyped finish (writerContext sevm [])
          (.initialize (initializeToken0 sevm) (initializeToken1 sevm)) transcript).status =
            .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty (G + initializeStorageCharge sevm pre + 377))
            (.ok (initializePublicPost sevm pre [0x485cc955] getterInitMemory G)),
          (initializePublicPost sevm pre [0x485cc955] getterInitMemory G).gasLeft = G ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (G + initializeStorageCharge sevm pre + 377),
                .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (G + initializeStorageCharge sevm pre + 377), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (G + initializeStorageCharge sevm pre + 377), .ok _, run⟩
              (initializePublicPost sevm pre [0x485cc955] getterInitMemory G)) := by
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed trace installed initial fresh
  refine ⟨finish, K', replayed, fun transcript returndata accepted => ?_⟩
  obtain ⟨value, sender, nonstatic⟩ := runTyped_initialize_conditions accepted
  obtain ⟨rep, _⟩ := replayed.at_frame target state
  have authorized : sevm.caller = (pre.getStorVal sevm.currentTarget 5).toAdr :=
    sender.trans rep.fixed.2.2.1.symm
  obtain ⟨run⟩ := initialize_bytecode_live_raw codeEq fork value size selector guard authorized
    sentry0 sentry1 nonstatic
  exact ⟨run, rfl, fun newFresh => pair_live_outcome initial fresh futureCode replayed run target
    state codeEq fork output representable newFresh⟩

/-- **`permit` after any configured history.**  Given the frame's actual `ECRECOVER` precompile result
(the compiled `STATICCALL` from its staged state, its success and returned gas: the callee input, as in
`permit_bytecode_live_raw`) and the residual sentries, whenever the model accepts the decoded `permit`
at the history's state `finish` over a transcript whose recovered address is that result's, a pc-zero
run exists at the closed gas `callGas + permitNonceStoreCharge sevm pre + permitNonceCharge sevm pre +
1137` ending at gas `G`; under HASH-T freshness of its own rows its post storage represents the model's
next state.  Model acceptance enters through `runTyped_permit_conditions` (non-payable, non-static, before
the deadline, the recovered signer is the nonzero owner). -/
theorem pair_history_permit_live {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre d : Devm} {G callGas : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (guard : (224 : B256) ≤ sevm.data.length.toB256 - 4)
    (sentry3 : gCallStipend < callGas + 641 + permitNonceStoreCharge sevm pre)
    (call : Ninst.RunCompiled sevm (St (permitNonceWorld sevm pre (permitOwner sevm))
      (callGas.toB256 :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack sevm pre 0xd505accf)
      (permitPublicCallMemory sevm pre) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: permitPublicCallStack sevm pre 0xd505accf)
    (returnedGas : d.gasLeft = G + permitApproveCharge sevm d + 2165)
    (sentry : gCallStipend < G + permitApproveCharge sevm d + 1846) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstRecovered = (permitRecoveredWord d.returnData).toAdr →
        (runTyped finish (writerContext sevm []) (permitDecodedEntry sevm) transcript).status =
          .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty
            (callGas + permitNonceStoreCharge sevm pre + permitNonceCharge sevm pre + 1137))
            (.ok (permitPublicPost sevm pre d d.returnData 0xd505accf G)),
          (permitPublicPost sevm pre d d.returnData 0xd505accf G).gasLeft = G ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                (callGas + permitNonceStoreCharge sevm pre + permitNonceCharge sevm pre + 1137),
                .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (callGas + permitNonceStoreCharge sevm pre + permitNonceCharge sevm pre + 1137),
                  .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty
                (callGas + permitNonceStoreCharge sevm pre + permitNonceCharge sevm pre + 1137),
                .ok _, run⟩
              (permitPublicPost sevm pre d d.returnData 0xd505accf G)) := by
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed trace installed initial fresh
  refine ⟨finish, K', replayed, fun transcript returndata answer accepted => ?_⟩
  obtain ⟨value, nonstatic, timely, recovered, signer⟩ := runTyped_permit_conditions accepted
  rw [answer] at recovered signer
  obtain ⟨run⟩ := permit_bytecode_live_raw codeEq fork value size selector guard nonstatic timely
    sentry3 call success returnedGas recovered signer sentry
  exact ⟨run, rfl, fun newFresh => pair_live_outcome initial fresh futureCode replayed run target
    state codeEq fork output representable newFresh⟩

end Blanc.Lift.UniswapV2Pair
