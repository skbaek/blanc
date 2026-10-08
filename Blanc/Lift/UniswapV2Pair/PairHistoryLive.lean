import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.UniswapV2Pair.ReplayWriterGas
import Blanc.Lift.UniswapV2Pair.SwapForwardAccept
import Blanc.Lift.UniswapV2Pair.MintForwardAccept
import Blanc.Lift.UniswapV2Pair.BurnForwardAccept
import Blanc.Lift.UniswapV2Pair.SkimForwardKeep
import Blanc.SlotFootprintRestrict

/-!
# Gas-exact liveness of the Pair after any configured history (U6)

`pair_history_committed` places the Pair's future storage over a replayed model state `finish`.  This
module composes it with the frame forward theorems: at a new frame whose pre-state is the history's
future state, a call the model accepts at `finish` executes from pc zero with a closed cost over the
residual `G`, and its post storage represents the model's next state.

* `pairHistoryUniverse`, `PairHistoryReplayed`, `pair_history_replayed` — the history's facts at
  `finish`, packaged once;
* `pair_live_outcome` — the shared glue: any successful pc-zero run of a new Pair frame at the future
  state, under HASH-T freshness of its own rows against the history universe, is one authenticated
  source invocation from `finish` that succeeds in the model (`PairStepOutcome`);
* `pair_history_writer_live` (transfer, approve, transferFrom), `pair_history_sync_live`,
  `pair_history_mint_live`, `pair_history_swap_live` — one instance per entry.

Premise classes: the history's (CODE, INIT, HASH-T); the new frame's environment; the callee
behaviour the frame forward theorem names (ENV); model acceptance at `finish`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc.ExecutionTrace

/-- The history's tracked universe: the initial rows and every row the trace's Pair frames select. -/
abbrev pairHistoryUniverse {cfg : ChainConfig} {checkpoint future : BlockChain} (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (K₀ : WriterKey → Prop) :
    WriterKey → Prop :=
  WriterExtend K₀ (pairHistoryTouchedKeys pair trace)

def PairHistoryReplayedWith
    (Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop)
    (Auth : Exec.Deriv → Entry → Transcript → Prop)
    {cfg : ChainConfig} {checkpoint future : BlockChain} (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (K₀ : WriterKey → Prop) (st₀ : State)
    (finish : State) (K' : WriterKey → Prop) : Prop :=
  ∃ steps : List PairStep,
    steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
    (∀ s ∈ steps, s.AuthenticWith Auth pair) ∧
    PairObservedReplayWith Consumes st₀ steps finish ∧
    runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
    (∀ k, K₀ k → K' k) ∧ (∀ k, K' k → pairHistoryUniverse pair trace K₀ k) ∧
    WriterRep K' (future.state.getStor pair) finish

theorem pair_history_replayed_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    future.state.getCode pair = code ∧
      ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayedWith Consumes Auth pair trace K₀ st₀ finish K' := by
  obtain ⟨installedFuture, steps, observed, auth, finish, K', matched, _, realized, grows, inside, rep⟩ :=
    pair_history_committed_with supplies weaken trace installed initial fresh
  exact ⟨code_eq_of_toList installedFuture, finish, K',
    steps, observed, auth, matched, realized, grows, inside, rep⟩

theorem PairHistoryReplayedWith.at_frame
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ finish : State}
    {K' : WriterKey → Prop} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (replayed : PairHistoryReplayedWith Consumes Auth pair trace K₀ st₀ finish K') {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state) :
    WriterRep K' (pre.getStor sevm.currentTarget) finish ∧
      (∀ k, K' k → pairHistoryUniverse pair trace K₀ k) := by
  obtain ⟨_, _, _, _, _, _, inside, rep⟩ := replayed
  refine ⟨?_, inside⟩
  have same : pre.getStor sevm.currentTarget = future.state.getStor pair := by
    rw [target]
    exact congrArg (fun world : Jaune.State => world.getStor pair) state
  rw [same]
  exact rep

theorem pair_live_outcome_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ finish : State} {K' : WriterKey → Prop}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (futureCode : future.state.getCode pair = code)
    (replayed : PairHistoryReplayedWith Consumes Auth pair trace K₀ st₀ finish K')
    {sevm : Sevm} {pre post : Devm} {g : Nat}
    (run : Exec 0 sevm (St pre [] Mem.empty g) (.ok post))
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (newFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀)
      (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty g, .ok post, run⟩)) :
    PairStepOutcomeWith Consumes Auth
      (WriterExtend (pairHistoryUniverse pair trace K₀)
        (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty g, .ok post, run⟩))
      { state := finish, logs := [], updates := [] } [] K'
      ⟨0, sevm, St pre [] Mem.empty g, .ok post, run⟩ post := by
  have hist : WriterRep (pairHistoryUniverse pair trace K₀) (checkpoint.state.getStor pair) st₀ :=
    initial.extend fresh
  obtain ⟨rep, inside⟩ := replayed.at_frame target state
  have installedCode : pre.getCode sevm.currentTarget = code := by
    rw [target]
    change pre.state.getCode pair = code
    rw [state]
    exact futureCode
  exact supplies _ (hist.inj.extend newFresh) (hist.apart.extend newFresh) { state := finish, logs := [], updates := [] } [] run codeEq installedCode fork
    output representable trivial (pairGood_of_keys fun _ row => Or.inr row)
    (fun k tracked => Or.inl (inside k tracked)) rep

/-- The history's facts at its replayed model state `finish` over the tracked rows `K'`
(`pair_history_committed`'s existential). -/
def PairHistoryReplayed {cfg : ChainConfig} {checkpoint future : BlockChain} (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (K₀ : WriterKey → Prop) (st₀ : State)
    (finish : State) (K' : WriterKey → Prop) : Prop :=
  PairHistoryReplayedWith (fun _ => ExactConsumes) PairFrameAuth pair trace K₀ st₀ finish K'

theorem pair_history_replayed {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    future.state.getCode pair = code ∧
      ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' :=
  pair_history_replayed_with (fun _ inj apart => pairSupply inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed) trace installed initial fresh

/-- The history's facts at a new frame whose world is the history's future world. -/
theorem PairHistoryReplayed.at_frame {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ finish : State}
    {K' : WriterKey → Prop} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (replayed : PairHistoryReplayed pair trace K₀ st₀ finish K') {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state) :
    WriterRep K' (pre.getStor sevm.currentTarget) finish ∧
      (∀ k, K' k → pairHistoryUniverse pair trace K₀ k) :=
  PairHistoryReplayedWith.at_frame replayed target state

/-- **The shared liveness glue.**  A successful pc-zero run of a new Pair frame at the history's future
world, under HASH-T freshness of the rows its own derivation selects against the history universe, is
one authenticated source invocation from the history's model state `finish` that succeeds in the model,
and its post storage represents the model's next state. -/
theorem pair_live_outcome {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ finish : State} {K' : WriterKey → Prop}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (futureCode : future.state.getCode pair = code)
    (replayed : PairHistoryReplayed pair trace K₀ st₀ finish K')
    {sevm : Sevm} {pre post : Devm} {g : Nat}
    (run : Exec 0 sevm (St pre [] Mem.empty g) (.ok post))
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (newFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀)
      (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty g, .ok post, run⟩)) :
    PairStepOutcome PairFrameAuth
      (WriterExtend (pairHistoryUniverse pair trace K₀)
        (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty g, .ok post, run⟩))
      { state := finish, logs := [], updates := [] } [] K'
      ⟨0, sevm, St pre [] Mem.empty g, .ok post, run⟩ post :=
  pair_live_outcome_with (fun _ inj apart => pairSupply inj apart pairSem pairSem_image)
    initial fresh futureCode replayed run target state codeEq fork output representable newFresh

/-! ## Instances -/

theorem pair_history_writer_live_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (writer : LedgerWriter) {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (representable : sevm.data.length < 2 ^ 256)
    (length : writer.calldataSize ≤ sevm.data.length)
    (selector : Blanc.Sevm.selector sevm = writer.selector)
    (callFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀) (writer.keys sevm)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayedWith Consumes Auth pair trace K₀ st₀ finish K' ∧
      ∀ (G : Nat) (sourceFrame : Frame) (returndata : Bytes),
        startImmediate { state := finish, logs := [], updates := [] } (writerContext sevm [])
          (writer.entry sevm) = some (.finished sourceFrame returndata) →
        gCallStipend < G →
        Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + writer.cost sevm pre))
          (.ok (writer.post sevm pre G))) ∧
        (writer.post sevm pre G).gasLeft = G ∧
        writer.Result K' { state := finish, logs := [], updates := [] } [] sevm pre
          (writer.post sevm pre G) G := by
  obtain ⟨_, finish, K', replayed⟩ := pair_history_replayed_with supplies weaken trace installed initial fresh
  refine ⟨finish, K', replayed, fun G sourceFrame returndata accepted residual => ?_⟩
  have hist : WriterRep (pairHistoryUniverse pair trace K₀) (checkpoint.state.getStor pair) st₀ :=
    initial.extend fresh
  obtain ⟨rep, inside⟩ := replayed.at_frame target state
  obtain ⟨_, run, result⟩ := writer.source_live rep
    (Blanc.SlotFootprint.FreshKeys.restrict hist.inj hist.apart inside callFresh) representable length
    codeEq fork selector residual accepted
  refine ⟨run, ?_, result⟩
  cases writer <;> rfl

/-- **LP writers after any configured history (transfer, approve, transferFrom).**  A writer call
the model accepts at the history's state `finish` executes from pc zero at gas
`G + writer.cost sevm pre` (the closed charge over the actual warm/cold slots: `sstoreCost` of the
written rows plus constants) and ends at gas `G`, its post storage representing the model's next state
over the history's rows extended by the call's own rows (`writer.Result`: exact storage, logs and
return word).  Premises: the history's; the new frame's environment; HASH-T freshness of the call's
rows against the history universe; model acceptance at `finish`; a residual above the stipend. -/
theorem pair_history_writer_live {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (writer : LedgerWriter) {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (representable : sevm.data.length < 2 ^ 256)
    (length : writer.calldataSize ≤ sevm.data.length)
    (selector : Blanc.Sevm.selector sevm = writer.selector)
    (callFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀) (writer.keys sevm)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (G : Nat) (sourceFrame : Frame) (returndata : Bytes),
        startImmediate { state := finish, logs := [], updates := [] } (writerContext sevm [])
          (writer.entry sevm) = some (.finished sourceFrame returndata) →
        gCallStipend < G →
        Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + writer.cost sevm pre))
          (.ok (writer.post sevm pre G))) ∧
        (writer.post sevm pre G).gasLeft = G ∧
        writer.Result K' { state := finish, logs := [], updates := [] } [] sevm pre
          (writer.post sevm pre G) G :=
  pair_history_writer_live_with (fun _ inj apart => pairSupply inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed)
    trace installed initial fresh writer target state codeEq fork representable length selector
    callFresh

theorem pair_history_sync_live_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre d0 d1 : Devm} {callGas0 callGas1 G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) (static : sevm.isStatic = false)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm pre)
        (syncFirstToken sevm pre).toAdr) + sloadCost sevm (syncLockedWorld sevm pre) 6 + 119 +
      sstoreCost sevm (afterSload sevm pre 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm pre).getCode (syncFirstToken sevm pre).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm pre) (syncFirstToken sevm pre).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm pre) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 ::
      [0xfff6cae9])
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (returnedGas1 : d1.gasLeft = (syncUpdateUnlockClosedGas sevm d1
      (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 (G + 1)) + 70)
    (long1 : 32 ≤ d1.returnData.length) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayedWith Consumes Auth pair trace K₀ st₀ finish K' ∧
      (finish.unlocked = 1 →
        (∃ result, finish.update (writerContext sevm []) (Bytes.toB256 (d0.returnData.take 32))
          (Bytes.toB256 (d1.returnData.take 32)) finish.reserve0.val finish.reserve1.val =
            .ok result) →
        let balance0 := (Bytes.toB256 (d0.returnData.take 32))
        let balance1 := (Bytes.toB256 (d1.returnData.take 32))
        let u := afterSload sevm d1 8
        let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
        let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
        let finalGas := (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 + 7
        let h := afterSload sevm u 8
        let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
        let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
        let v := updateOracleWorld sevm u old0 old1
        let store9 := sstoreCost sevm (afterSload sevm h 9) 9
          (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
            (updatePriceWord old0 old1) delta)
        let load10 := sloadCost sevm w9 10
        let store10 := sstoreCost sevm (afterSload sevm w9 10) 10
          (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
            (updatePriceWord old1 old0) delta)
        let load8 := sloadCost sevm v 8
        let store8 := sstoreCost sevm (afterSload sevm v 8) 8
          (updateFinalPackedWord sevm u old0 old1 balance0 balance1)
        gCallStipend < finalGas + updateSyncGas 192 + store8 →
        (updateOracleActive sevm u old0 old1 →
          gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 + store10) →
        (updateOracleActive sevm u old0 old1 →
          gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 +
            load10 + store10 + 42 + 149 + store9) →
        gCallStipend < (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 →
        ∃ (post : Devm)
          (run : Exec 0 sevm (St pre [] Mem.empty (syncCalleePrefixGas sevm pre callGas0 + 15 + 229))
            (.ok post)),
          post.gasLeft = G ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                (syncCalleePrefixGas sevm pre callGas0 + 15 + 229), .ok post, run⟩) →
            PairStepOutcomeWith Consumes Auth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (syncCalleePrefixGas sevm pre callGas0 + 15 + 229), .ok post, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (syncCalleePrefixGas sevm pre callGas0 + 15 + 229),
                .ok post, run⟩ post)) := by
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed_with supplies weaken trace installed initial fresh
  refine ⟨finish, K', replayed, fun unlockedModel accepted => ?_⟩
  obtain ⟨rep, _⟩ := replayed.at_frame target state
  obtain ⟨_, updated⟩ := accepted
  obtain ⟨bound0, bound1⟩ := State.update_bounds updated
  have installedPre : some (pre.getCode sevm.currentTarget).toList = pairSem.image := by
    rw [target]
    change some (pre.state.getCode pair).toList = pairSem.image
    rw [state, futureCode]
    rfl
  intro balance0 balance1 u old0 old1 finalGas h delta w9 v store9 load10 store10 load8 store8
    sentry8 sentry10 sentry9 unlockSentry
  obtain ⟨post, run, gas, _⟩ := syncPc0_canonical_live
      (current := { state := finish, logs := [], updates := [] }) [] rep pairSem pairSem_image installedPre codeEq fork value size selector
    static (rep.unlocked_word.trans unlockedModel) sentry nonzero0 call0 success0 returnedGas0
    long0 nonzero1 call1 success1 returnedGas1 long1 bound0 bound1 sentry8 sentry10 sentry9
    unlockSentry
  exact ⟨post, run, gas, fun newFresh => pair_live_outcome_with supplies initial fresh futureCode replayed run
    target state codeEq fork output representable newFresh⟩

/-- **`sync` after any configured history.**  When the model accepts `sync` at the history's state
`finish` — the lock is open and its reserve update accepts the two actual `balanceOf(pair)` answers —
a pc-zero run exists at gas `syncCalleePrefixGas sevm pre callGas0 + 15 + 229` (the lock, cache and
request charges over the gas `callGas0` forwarded to the first token; the callees' consumption is
fixed by their `returnedGas` premises) ending at gas `G`; under HASH-T freshness of its own rows its
post storage represents the model's next state (`PairStepOutcome`).  Premises: the history's; the new
frame's environment; the two token `STATICCALL`s with their replies and returned gas (ENV); the
residual sentries; model acceptance at `finish`. -/
theorem pair_history_sync_live {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre d0 d1 : Devm} {callGas0 callGas1 G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) (static : sevm.isStatic = false)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm pre)
        (syncFirstToken sevm pre).toAdr) + sloadCost sevm (syncLockedWorld sevm pre) 6 + 119 +
      sstoreCost sevm (afterSload sevm pre 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm pre).getCode (syncFirstToken sevm pre).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm pre) (syncFirstToken sevm pre).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm pre) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 ::
      [0xfff6cae9])
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (returnedGas1 : d1.gasLeft = (syncUpdateUnlockClosedGas sevm d1
      (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 (G + 1)) + 70)
    (long1 : 32 ≤ d1.returnData.length) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      (finish.unlocked = 1 →
        (∃ result, finish.update (writerContext sevm []) (Bytes.toB256 (d0.returnData.take 32))
          (Bytes.toB256 (d1.returnData.take 32)) finish.reserve0.val finish.reserve1.val =
            .ok result) →
        let balance0 := (Bytes.toB256 (d0.returnData.take 32))
        let balance1 := (Bytes.toB256 (d1.returnData.take 32))
        let u := afterSload sevm d1 8
        let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
        let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
        let finalGas := (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 + 7
        let h := afterSload sevm u 8
        let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
        let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
        let v := updateOracleWorld sevm u old0 old1
        let store9 := sstoreCost sevm (afterSload sevm h 9) 9
          (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
            (updatePriceWord old0 old1) delta)
        let load10 := sloadCost sevm w9 10
        let store10 := sstoreCost sevm (afterSload sevm w9 10) 10
          (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
            (updatePriceWord old1 old0) delta)
        let load8 := sloadCost sevm v 8
        let store8 := sstoreCost sevm (afterSload sevm v 8) 8
          (updateFinalPackedWord sevm u old0 old1 balance0 balance1)
        gCallStipend < finalGas + updateSyncGas 192 + store8 →
        (updateOracleActive sevm u old0 old1 →
          gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 + store10) →
        (updateOracleActive sevm u old0 old1 →
          gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 +
            load10 + store10 + 42 + 149 + store9) →
        gCallStipend < (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 →
        ∃ (post : Devm)
          (run : Exec 0 sevm (St pre [] Mem.empty (syncCalleePrefixGas sevm pre callGas0 + 15 + 229))
            (.ok post)),
          post.gasLeft = G ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                (syncCalleePrefixGas sevm pre callGas0 + 15 + 229), .ok post, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (syncCalleePrefixGas sevm pre callGas0 + 15 + 229), .ok post, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (syncCalleePrefixGas sevm pre callGas0 + 15 + 229),
                .ok post, run⟩ post)) :=
  pair_history_sync_live_with (fun _ inj apart => pairSupply inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed)
    trace installed initial fresh target state codeEq fork output representable value size
    selector static sentry nonzero0 call0 success0 returnedGas0 long0 nonzero1 call1 success1
    returnedGas1 long1

theorem pair_history_mint_live_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (callee : MintPrefixCallee sevm pre [0x6a627842] getterInitMemory
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43))
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀)
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
        lpMintTouched callee.feeTo)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayedWith Consumes Auth pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        (runTyped finish (writerContext sevm []) (.mint (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ (liquidity : B256)
          (run : Exec 0 sevm (St pre [] Mem.empty (callee.gas + 228))
            (.ok (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G))),
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).gasLeft = G ∧
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).output =
            liquidity.toBytes ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩) →
            PairStepOutcomeWith Consumes Auth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩
              (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G)) := by
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed_with supplies weaken trace installed initial fresh
  refine ⟨finish, K', replayed, fun transcript returndata answer0 answer1 answerFee accepted => ?_⟩
  have conditions := runTyped_mint_conditions accepted
  rw [answer0, answer1, answerFee] at conditions
  have hist : WriterRep (pairHistoryUniverse pair trace K₀) (checkpoint.state.getStor pair) st₀ :=
    initial.extend fresh
  obtain ⟨rep, inside⟩ := replayed.at_frame target state
  have rowIn : ∀ k ∈ lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
      lpMintTouched callee.feeTo,
      WriterExtend (pairHistoryUniverse pair trace K₀)
        (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
          lpMintTouched callee.feeTo) k := fun k member => Or.inr member
  obtain ⟨env, envGas, envPost⟩ := callee.accepted fork rep (hist.inj.extend rowsFresh)
    (hist.apart.extend rowsFresh) (fun k tracked => Or.inl (inside k tracked))
    (rowIn _ (by simp only [lpMintTouched, List.mem_append, List.mem_singleton, or_true]))
    (rowIn _ (by simp only [lpMintTouched, List.mem_append, List.mem_singleton, true_or]))
    (rowIn _ (by simp only [lpMintTouched, List.mem_append, List.mem_singleton, true_or, or_true]))
    conditions
  obtain ⟨liquidity, ⟨run⟩, returned⟩ :=
    mintBytecode_exact codeEq fork value size guard selector env
  rw [envGas, envPost] at run
  rw [envPost] at returned
  exact ⟨liquidity, run, rfl, returned, fun newFresh =>
    pair_live_outcome_with supplies initial fresh futureCode replayed run target state codeEq fork output
      representable newFresh⟩

/-- **`mint` after any configured history.**  When the model accepts the mint at the history's state
`finish` on a transcript whose three answers are the frame's actual answers (the two token
`balanceOf(pair)` replies and the factory's `feeTo` reply), then given the callee-only environment at
the future world (`MintPrefixCallee`: the three `STATICCALL`s with their replies and returned gas, and
the charge equations and residual sentries) and HASH-T freshness of the LP rows of address zero, the
recipient and the `feeTo` answer against the history universe, a pc-zero run exists at gas
`callee.gas + 228` (`callee.gas`: the gas `callGas0` forwarded to token0 plus the closed lock, cache and
request charges) ending at gas `G` and returning the liquidity word; under HASH-T freshness of its own
rows its post storage represents the model's next state from `finish`.  Model acceptance enters through
`runTyped_mint_conditions` (every accepted mint passes `MintModelConditions` at its answers). -/
theorem pair_history_mint_live {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (callee : MintPrefixCallee sevm pre [0x6a627842] getterInitMemory
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43))
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀)
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
        lpMintTouched callee.feeTo)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        (runTyped finish (writerContext sevm []) (.mint (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ (liquidity : B256)
          (run : Exec 0 sevm (St pre [] Mem.empty (callee.gas + 228))
            (.ok (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G))),
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).gasLeft = G ∧
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).output =
            liquidity.toBytes ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩
              (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G)) :=
  pair_history_mint_live_with (fun _ inj apart => pairSupply inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed)
    trace installed initial fresh target state codeEq fork output representable value size guard
    selector callee rowsFresh

theorem pair_history_swap_live_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayedWith Consumes Auth pair trace K₀ st₀ finish K' ∧
      ∀ {d0 d1 dC : Devm} {cg0 cg1 cgC g : Nat}
        (callee : SwapBackCalleeEnv sevm (swapFrontCutWorld sevm pre d0 d1 dC)
          (swapFrontCutMem sevm d0 d1 dC) (swapFrontCutMem sevm d0 d1 dC).size
          (swapFrontPtr sevm d0 d1) (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1))
        (_front : SwapFrontForwardEnv sevm pre finish d0 d1 dC cg0 cg1 cgC
          callee.gas),
        SwapContextConditions (writerContext sevm []) →
        SwapModelConditions finish (swapAmount0Out sevm) (swapAmount1Out sevm) (swapRecipient sevm)
          (swapBalanceWord callee.d0.returnData) (swapBalanceWord callee.d1.returnData) →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty
            (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
              swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166))
            (.ok (St callee.post [0x022c0d9f] callee.memory g)),
          (St callee.post [0x022c0d9f] callee.memory g).gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
                  swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166), .ok _, run⟩) →
            PairStepOutcomeWith Consumes Auth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
                    swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty
                (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
                  swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166), .ok _, run⟩
              (St callee.post [0x022c0d9f] callee.memory g)) := by
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed_with supplies weaken trace installed initial fresh
  refine ⟨finish, K', replayed, fun {d0 d1 dC cg0 cg1 cgC g} callee front context conditions => ?_⟩
  obtain ⟨rep, _⟩ := replayed.at_frame target state
  have nonstatic : sevm.isStatic = false := context.2
  obtain ⟨back, backGas, backPost, backMemory⟩ := callee.accepted conditions nonstatic
  obtain ⟨unlocked, positive, liquidity0, liquidity1, to0, to1, _⟩ := conditions
  have installedPre : some (pre.getCode sevm.currentTarget).toList = pairSem.image := by
    rw [target]
    change some (pre.state.getCode pair).toList = pairSem.image
    rw [state, futureCode]
    rfl
  have nonzero : swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0 := by
    rcases positive with h | h
    · exact Or.inl (ne_of_gt h)
    · exact Or.inr (ne_of_gt h)
  rw [← backGas] at front ⊢
  rw [← backPost, ← backMemory]
  obtain ⟨run, _⟩ := swap_bytecode_forward_consumes
    (current := { state := finish, logs := [], updates := [] }) [] rep pairSem pairSem_image
    installedPre output codeEq fork value size selector guards unlocked nonstatic nonzero
    liquidity0 liquidity1 to0 to1 back front
  exact ⟨run, rfl, fun newFresh => pair_live_outcome_with supplies initial fresh futureCode replayed run target
    state codeEq fork output representable newFresh⟩

/-- **`swap` after any configured history, with or without the flash callback.**  When the model
accepts the decoded swap at the history's state `finish` with the frame's actual post-callback
`balanceOf(pair)` answers (`SwapContextConditions` and `SwapModelConditions`: the lock is open, some
output is positive, both outputs are below the reserves, `to` is neither token, the answers fit
`uint112`, some input is positive and the fee-adjusted `K` check holds; by
`runTyped_swap_canonical_success` this is the model run succeeding on those answers, and
`runTyped_swap_success_reserves` gives it back from any successful run), then given the callee-only
environments at the future world (`front`: the optional transfer `CALL`s and the callback `CALL`,
present iff their amount or the data is nonzero; `callee`: the two `balanceOf(pair)` `STATICCALL`s with
their returned gas), with the `_safeTransfer` helper discharged by `safeTransfer_dynamic_forward`, a pc-zero run exists at gas
`swapFrontTransferGas … callee.gas + swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166` ending at
gas `g`; under HASH-T freshness of its own rows its post storage represents the model's next state. -/
theorem pair_history_swap_live {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ {d0 d1 dC : Devm} {cg0 cg1 cgC g : Nat}
        (callee : SwapBackCalleeEnv sevm (swapFrontCutWorld sevm pre d0 d1 dC)
          (swapFrontCutMem sevm d0 d1 dC) (swapFrontCutMem sevm d0 d1 dC).size
          (swapFrontPtr sevm d0 d1) (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1))
        (_front : SwapFrontForwardEnv sevm pre finish d0 d1 dC cg0 cg1 cgC
          callee.gas),
        SwapContextConditions (writerContext sevm []) →
        SwapModelConditions finish (swapAmount0Out sevm) (swapAmount1Out sevm) (swapRecipient sevm)
          (swapBalanceWord callee.d0.returnData) (swapBalanceWord callee.d1.returnData) →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty
            (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
              swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166))
            (.ok (St callee.post [0x022c0d9f] callee.memory g)),
          (St callee.post [0x022c0d9f] callee.memory g).gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
                  swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166), .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
                    swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty
                (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
                  swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166), .ok _, run⟩
              (St callee.post [0x022c0d9f] callee.memory g)) :=
  pair_history_swap_live_with (fun _ inj apart => pairSupply inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed)
    trace installed initial fresh target state codeEq fork output representable value size
    selector guards

theorem pair_history_burn_live_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (callee : BurnForwardEnv sevm pre g)
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀)
      (lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayedWith Consumes Auth pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final0 →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final1 →
        (runTyped finish (writerContext sevm []) (.burn (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairStepOutcomeWith Consumes Auth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) := by
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed_with supplies weaken trace installed initial fresh
  refine ⟨finish, K', replayed,
    fun transcript returndata answer0 answer1 answerFee final0 final1 accepted => ?_⟩
  have conditions := runTyped_burn_conditions accepted
  rw [answer0, answer1, answerFee, final0, final1] at conditions
  have hist : WriterRep (pairHistoryUniverse pair trace K₀) (checkpoint.state.getStor pair) st₀ :=
    initial.extend fresh
  obtain ⟨rep, inside⟩ := replayed.at_frame target state
  let rows := lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo
  have inj := hist.inj.extend rowsFresh
  have apart := hist.apart.extend rowsFresh
  have rowIn : ∀ k ∈ rows, WriterExtend (pairHistoryUniverse pair trace K₀) rows k :=
    fun k member => Or.inr member
  have ownRow : WriterExtend (pairHistoryUniverse pair trace K₀) rows
      (.balance sevm.currentTarget) :=
    rowIn _ (by simp only [rows, lpMintTouched, List.mem_append, List.mem_singleton, true_or])
  have feeRow : WriterExtend (pairHistoryUniverse pair trace K₀) rows (.balance callee.feeTo) :=
    rowIn _ (by simp only [rows, lpMintTouched, List.mem_append, List.mem_singleton, or_true])
  have subK : ∀ k, K' k → WriterExtend (pairHistoryUniverse pair trace K₀) rows k :=
    fun k tracked => Or.inl (inside k tracked)
  have ownFresh : WriterFreshKeys K' (lpMintTouched sevm.currentTarget) :=
    Blanc.SlotFootprint.FreshKeys.of_universe inj apart subK
      (fun k member => by rw [List.mem_singleton.mp member]; exact ownRow)
  have repOwn := rep.extend ownFresh
  have subOwn : ∀ k, WriterExtend K' (lpMintTouched sevm.currentTarget) k →
      WriterExtend (pairHistoryUniverse pair trace K₀) rows k := by
    intro k member
    rcases member with old | row
    · exact subK k old
    · rw [List.mem_singleton.mp row]; exact ownRow
  have tracked : WriterExtend K' (lpMintTouched sevm.currentTarget) (.balance sevm.currentTarget) :=
    Or.inr (List.mem_singleton_self _)
  have guards := callee.guards_of_model repOwn inj apart subOwn feeRow conditions
  have installedPre : some (pre.getCode sevm.currentTarget).toList = pairSem.image := by
    rw [target]
    change some (pre.state.getCode pair).toList = pairSem.image
    rw [state, futureCode]
    rfl
  obtain ⟨run, _⟩ := burn_bytecode_forward_consumes
    (current := { state := finish, logs := [], updates := [] }) [] codeEq fork value size
    guard selector repOwn tracked pairSem pairSem_image installedPre callee guards
  exact ⟨run, rfl, fun newFresh => pair_live_outcome_with supplies initial fresh futureCode replayed run target
    state codeEq fork output representable newFresh⟩

/-- **`burn` after any configured history.**  Given the callee-only Burn environment at the future
world (`BurnForwardEnv`: both initial `balanceOf(pair)` `STATICCALL`s, the factory `feeTo`
`STATICCALL`, both transfer `CALL`s and both final `balanceOf(pair)` `STATICCALL`s with their replies
and returned gas, and the charge equations and sentries; the `_safeTransfer` helper is
`safeTransfer_dynamic_forward`), and HASH-T freshness of the Pair's
own LP row and the `feeTo` answer's LP row against the history universe: whenever the model accepts
the decoded Burn at the history's state `finish` over a transcript whose answers are the callees'
actual ones, a pc-zero run exists at gas `callee.gas` halting with both amounts returned at residual
`g`; under HASH-T freshness of its own rows its post storage represents the model's next state.
Model acceptance enters through `runTyped_burn_conditions`. -/
theorem pair_history_burn_live {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (callee : BurnForwardEnv sevm pre g)
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀)
      (lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final0 →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final1 →
        (runTyped finish (writerContext sevm []) (.burn (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) :=
  pair_history_burn_live_with (fun _ inj apart => pairSupply inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed)
    trace installed initial fresh target state codeEq fork output representable value size guard
    selector callee rowsFresh

theorem pair_history_skim_live_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWith Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (callee : SkimForwardEnv sevm pre g)
    (firstFresh : callee.FirstCallFresh (pairHistoryUniverse pair trace K₀)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayedWith Consumes Auth pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 →
        transcript.ownTail.ownTail.firstWord = callee.balance1 →
        (runTyped finish (writerContext sevm []) (.skim (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairStepOutcomeWith Consumes Auth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) := by
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed_with supplies weaken trace installed initial fresh
  refine ⟨finish, K', replayed, fun transcript returndata answer0 answer1 accepted => ?_⟩
  have conditions := runTyped_skim_conditions accepted
  rw [answer0, answer1] at conditions
  have hist : WriterRep (pairHistoryUniverse pair trace K₀) (checkpoint.state.getStor pair) st₀ :=
    initial.extend fresh
  obtain ⟨rep, inside⟩ := replayed.at_frame target state
  have installedPre : some (pre.getCode sevm.currentTarget).toList = pairSem.image := by
    rw [target]
    change some (pre.state.getCode pair).toList = pairSem.image
    rw [state, futureCode]
    rfl
  obtain ⟨run⟩ := callee.run_of_model (current := { state := finish, logs := [], updates := [] })
    [] rep hist.inj hist.apart inside pairSem pairSem_image installedPre output codeEq fork value
    size selector abi firstFresh conditions
  exact ⟨run, rfl, fun newFresh => pair_live_outcome_with supplies initial fresh futureCode replayed run target
    state codeEq fork output representable newFresh⟩

/-- **`skim` after any configured history.**  Given the callee-only skim environment at the future
world (`SkimForwardEnv`: both `balanceOf(pair)` `STATICCALL`s and both transfer `CALL`s with their
replies and returned gas, the code checks, the lock and unlock sentries) and trace-local HASH-T for
the first transfer's Pair frames (`FirstCallFresh`; that `CALL` keeps reserve1 by the derived
`firstCall_keeps`, no callee clause): whenever the model accepts the decoded skim at the history's
state `finish` over a transcript whose balance answers are the callees' actual ones, a pc-zero run
exists at gas `callee.gas` halting at residual `g`; under HASH-T freshness of its own rows its post
storage represents the model's next state.  Model acceptance enters via `runTyped_skim_conditions`. -/
theorem pair_history_skim_live {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (callee : SkimForwardEnv sevm pre g)
    (firstFresh : callee.FirstCallFresh (pairHistoryUniverse pair trace K₀)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 →
        transcript.ownTail.ownTail.firstWord = callee.balance1 →
        (runTyped finish (writerContext sevm []) (.skim (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) :=
  pair_history_skim_live_with (fun _ inj apart => pairSupply inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed)
    trace installed initial fresh target state codeEq fork output representable value size abi
    selector callee firstFresh

end Blanc.Lift.UniswapV2Pair
