import Blanc.Lift.UniswapV2Pair.InitializeEntries
import Blanc.Lift.UniswapV2Pair.ApproveSource
import Blanc.Lift.CalldataGuards

/-! Repeated factory initialization consumes the existing typed source handler. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def initializeSourceState (st : State) (token0 token1 : Adr) : State :=
  { st with token0 := token0, token1 := token1 }

def initializeDecodedEntry (sevm : Sevm) : Entry :=
  .initialize (initializeToken0 sevm) (initializeToken1 sevm)

def initializeSourceFrame (current : Checkpoint) (ctx : Context)
    (token0 token1 : Adr) : Frame :=
  (Frame.enter current ctx (.initialize token0 token1)).withEvents
    (initializeSourceState current.state token0 token1) []

def initializeSourceDone (current : Checkpoint) (ctx : Context)
    (token0 token1 : Adr) : RunResult :=
  { status := .success [], frame := initializeSourceFrame current ctx token0 token1,
    remaining := .done, childReturns := [] }

theorem initializeSourceState_value (st : State) (token0 token1 : Adr) (k : WriterKey) :
    k.value (initializeSourceState st token0 token1) = k.value st := by
  cases k <;> rfl

theorem WriterRep.initialize_public_post {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state) :
    WriterRep K
      ((initializePublicPost sevm b [0x485cc955] getterInitMemory G).getStor sevm.currentTarget)
      (initializeSourceState current.state (initializeToken0 sevm) (initializeToken1 sevm)) := by
  have step := initializePublicPost_storstep (sevm := sevm) (b := b)
    (R := [0x485cc955]) (M := getterInitMemory) (G := G)
  rw [step.self]
  have packed := initializePublicStorage_packed (sevm := sevm) (b := b)
  have unchanged (n : B256) (off6 : (6 : B256) ≠ n) (off7 : (7 : B256) ≠ n) :
      (initializePublicStorage sevm b).get n = (b.getStor sevm.currentTarget).get n := by
    unfold initializePublicStorage
    rw [Stor.get_set_ne _ off7, Stor.get_set_ne _ off6]
  refine ⟨rep.finite, ?_, ?_, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches, initializeSourceState]
    rw [unchanged 0 (by decide) (by decide), unchanged 3 (by decide) (by decide),
      unchanged 5 (by decide) (by decide), packed.1, packed.2.1,
      unchanged 8 (by decide) (by decide), unchanged 9 (by decide) (by decide),
      unchanged 10 (by decide) (by decide), unchanged 11 (by decide) (by decide),
      unchanged 12 (by decide) (by decide)]
    exact ⟨rep.fixed.1, rep.fixed.2.1, rep.fixed.2.2.1, rfl, rfl, rep.fixed.2.2.2.2.2⟩
  · intro n nonzero
    by_cases slot6 : n = 6
    · exact .inl (slot6.symm ▸ (by decide : (6 : B256) ∈ writerFixedSlots))
    · by_cases slot7 : n = 7
      · exact .inl (slot7.symm ▸ (by decide : (7 : B256) ∈ writerFixedSlots))
      · rw [unchanged n (Ne.symm slot6) (Ne.symm slot7)] at nonzero
        exact rep.support n nonzero
  · intro k tracked
    have apart := rep.apart k tracked
    have off6 : (6 : B256) ≠ k.slot :=
      fun eq => apart (eq ▸ (by decide : (6 : B256) ∈ writerFixedSlots))
    have off7 : (7 : B256) ≠ k.slot :=
      fun eq => apart (eq ▸ (by decide : (7 : B256) ∈ writerFixedSlots))
    rw [unchanged k.slot off6 off7, initializeSourceState_value]
    exact rep.selected k tracked
  · intro k outside
    rw [initializeSourceState_value]
    exact rep.logicalZero k outside

theorem initialize_startImmediate_done {current : Checkpoint} {ctx : Context}
    {token0 token1 : Adr} (value : ctx.value = 0)
    (authorized : ctx.sender = current.state.factory) (nonstatic : ctx.isStatic = false) :
    startImmediate current ctx (.initialize token0 token1) =
      some (.finished (initializeSourceFrame current ctx token0 token1) []) := by
  simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value),
    getterResult, ite_eq_left authorized, nonstatic, Bool.false_eq_true, ite_false]
  rfl

theorem initialize_drive_done {current : Checkpoint} {ctx : Context}
    {token0 token1 : Adr} (value : ctx.value = 0)
    (authorized : ctx.sender = current.state.factory) (nonstatic : ctx.isStatic = false) :
    drive 2 (startTyped current ctx (.initialize token0 token1)) .done =
      initializeSourceDone current ctx token0 token1 := by
  rw [startTyped, initialize_startImmediate_done value authorized nonstatic]
  rfl

theorem initializeSourceFrame_prefix (current : Checkpoint) (ctx : Context) (token0 token1 : Adr) :
    (initializeSourceFrame current ctx token0 token1).context = ctx ∧
    (initializeSourceFrame current ctx token0 token1).entry = .initialize token0 token1 ∧
    (initializeSourceFrame current ctx token0 token1).checkpoint = current ∧
    (initializeSourceFrame current ctx token0 token1).current =
      { current with state := initializeSourceState current.state token0 token1 } ∧
    (initializeSourceFrame current ctx token0 token1).segment = 0 ∧
    (initializeSourceFrame current ctx token0 token1).afterCall = none := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl⟩
  simp only [initializeSourceFrame, Frame.withEvents, Frame.enter, List.map_nil, List.append_nil]

/-- No hashed row is touched by the two fixed writes. -/
theorem initializePublicStorage_unchanged {sevm : Sevm} {b : Devm} {n : B256}
    (off6 : n ≠ 6) (off7 : n ≠ 7) :
    (initializePublicStorage sevm b).get n = b.getStorVal sevm.currentTarget n := by
  unfold initializePublicStorage
  rw [Stor.get_set_ne _ (Ne.symm off7), Stor.get_set_ne _ (Ne.symm off6)]
  rfl

/-- The representation and incoming output belong to the real frame producer. -/
structure InitializeSourceResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (sevm : Sevm) (b post : Devm) (residual : Nat) : Prop where
  rawPost : post = initializePublicPost sevm b [0x485cc955] getterInitMemory residual
  representation : WriterRep K (post.getStor sevm.currentTarget)
    (initializeSourceState current.state (initializeToken0 sevm) (initializeToken1 sevm))
  sourceImmediate : startImmediate current (writerContext sevm invocation) (initializeDecodedEntry sevm) =
    some (.finished (initializeSourceFrame current (writerContext sevm invocation)
      (initializeToken0 sevm) (initializeToken1 sevm)) [])
  sourceDone : drive 2 (startTyped current (writerContext sevm invocation) (initializeDecodedEntry sevm)) .done =
    initializeSourceDone current (writerContext sevm invocation) (initializeToken0 sevm) (initializeToken1 sevm)
  context : (initializeSourceFrame current (writerContext sevm invocation)
    (initializeToken0 sevm) (initializeToken1 sevm)).context = writerContext sevm invocation
  entry : (initializeSourceFrame current (writerContext sevm invocation)
    (initializeToken0 sevm) (initializeToken1 sevm)).entry = initializeDecodedEntry sevm
  checkpoint : (initializeSourceFrame current (writerContext sevm invocation)
    (initializeToken0 sevm) (initializeToken1 sevm)).checkpoint = current
  sourceCurrent : (initializeSourceFrame current (writerContext sevm invocation)
    (initializeToken0 sevm) (initializeToken1 sevm)).current =
      { current with state := initializeSourceState current.state (initializeToken0 sevm) (initializeToken1 sevm) }
  segment : (initializeSourceFrame current (writerContext sevm invocation)
    (initializeToken0 sevm) (initializeToken1 sevm)).segment = 0
  afterCall : (initializeSourceFrame current (writerContext sevm invocation)
    (initializeToken0 sevm) (initializeToken1 sevm)).afterCall = none
  output : post.output = []
  storage : post.getStor sevm.currentTarget = initializePublicStorage sevm b
  logs : post.logs = b.logs
  foreignStorage : ∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a
  unchangedSlots : ∀ n, n ≠ 6 → n ≠ 7 → post.getStorVal sevm.currentTarget n = b.getStorVal sevm.currentTarget n
  token0 : (post.getStorVal sevm.currentTarget 6).toAdr = initializeToken0 sevm
  token1 : (post.getStorVal sevm.currentTarget 7).toAdr = initializeToken1 sevm
  upper0 : addressMask &&& post.getStorVal sevm.currentTarget 6 = addressMask &&& b.getStorVal sevm.currentTarget 6
  upper1 : addressMask &&& post.getStorVal sevm.currentTarget 7 = addressMask &&& b.getStorVal sevm.currentTarget 7
  gas : post.gasLeft = residual

theorem initialize_public_source_result {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (freshOutput : b.output = []) (value : sevm.value = 0)
    (authorized : sevm.caller = current.state.factory) (nonstatic : sevm.isStatic = false) :
    InitializeSourceResult K current invocation sevm b
      (initializePublicPost sevm b [0x485cc955] getterInitMemory G) G := by
  have sourceFacts := initializeSourceFrame_prefix current (writerContext sevm invocation)
    (initializeToken0 sevm) (initializeToken1 sevm)
  have step := initializePublicPost_storstep (sevm := sevm) (b := b)
    (R := [0x485cc955]) (M := getterInitMemory) (G := G)
  have packed := initializePublicStorage_packed (sevm := sevm) (b := b)
  refine ⟨rfl, rep.initialize_public_post, initialize_startImmediate_done value authorized nonstatic,
    initialize_drive_done value authorized nonstatic, sourceFacts.1, sourceFacts.2.1, sourceFacts.2.2.1,
    sourceFacts.2.2.2.1, sourceFacts.2.2.2.2.1, sourceFacts.2.2.2.2.2, ?_, step.self, step.logs,
    step.other, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [initializePublicPost_output, freshOutput]
  · intro n off6 off7
    rw [step.getStorVal n]
    exact initializePublicStorage_unchanged off6 off7
  · rw [step.getStorVal 6]
    exact packed.1
  · rw [step.getStorVal 7]
    exact packed.2.1
  · rw [step.getStorVal 6]
    exact packed.2.2.1
  · rw [step.getStorVal 7]
    exact packed.2.2.2
  · rfl

/-- A successful literal pc-zero run derives the existing handler's accepted result. -/
theorem initialize_bytecode_refines_source {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (representable : sevm.data.length < 2 ^ 256) (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 68 ≤ sevm.data.length ∧ sevm.caller = current.state.factory ∧
      sevm.isStatic = false ∧ ∃ residual, InitializeSourceResult K current invocation sevm b post residual := by
  obtain ⟨value, size, guard, rawAuthorized, nonstatic, residual, result⟩ :=
    initialize_bytecode_refines_raw codeEq fork selector run
  have authorized : sevm.caller = current.state.factory := rawAuthorized.trans rep.fixed.2.2.1
  have length := (word_calldata_guards_iff (n := 64) representable (by decide)).mp ⟨size, guard⟩
  refine ⟨value, length, authorized, nonstatic, residual, ?_⟩
  rw [result]
  exact initialize_public_source_result rep freshOutput value authorized nonstatic

/-- Successful raw pc0 execution derives exact consumption for the typed initialize entry. -/
theorem initialize_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (representable : sevm.data.length < 2 ^ 256) (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 68 ≤ sevm.data.length ∧ sevm.caller = current.state.factory ∧
      sevm.isStatic = false ∧ ∃ residual, InitializeSourceResult K current invocation sevm b post residual ∧
        ExactConsumes (startTyped current (writerContext sevm invocation) (initializeDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := initializeSourceFrame current (writerContext sevm invocation)
              (initializeToken0 sevm) (initializeToken1 sevm),
            remaining := .done, childReturns := [] } := by
  obtain ⟨value, length, authorized, nonstatic, residual, result⟩ :=
    initialize_bytecode_refines_source rep representable freshOutput codeEq fork selector run
  have typed : startTyped current (writerContext sevm invocation) (initializeDecodedEntry sevm) =
      .finished (initializeSourceFrame current (writerContext sevm invocation)
        (initializeToken0 sevm) (initializeToken1 sevm)) post.output := by
    unfold startTyped
    rw [result.sourceImmediate]
    dsimp only []
    rw [← result.output]
  refine ⟨value, length, authorized, nonstatic, residual, result, ?_⟩
  rw [typed]
  exact ExactConsumes.finished (initializeSourceFrame current (writerContext sevm invocation)
    (initializeToken0 sevm) (initializeToken1 sevm)) post.output

end Blanc.Lift.UniswapV2Pair
