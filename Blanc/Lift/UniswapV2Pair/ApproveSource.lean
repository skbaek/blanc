import Blanc.Lift.UniswapV2Pair.WriterStorage
import Blanc.Lift.UniswapV2Pair.WriterEntries
import Blanc.Lift.UniswapV2Pair.Consumption

/-! The actual approval writer consumes the existing immediate source handler. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Public entry context is read from the actual EVM frame; only its history path is supplied. -/
def writerContext (sevm : Sevm) (invocation : List Nat) : Context :=
  { pair := sevm.currentTarget, sender := sevm.caller, value := sevm.value,
    timestamp := sevm.benvStat.time, isStatic := sevm.isStatic, invocation := invocation }

def approveDecodedEntry (sevm : Sevm) : Entry :=
  .approve (approveSpender sevm) (approveAmount sevm)

def writerEntryOrigin (ctx : Context) : ReceiptOrigin :=
  { invocation := ctx.invocation, segment := 0, afterCall := none }

def approvalRawLog (pair owner spender : Adr) (amount : B256) : Jaune.Log :=
  ⟨pair, [approvalTopic, owner.toB256, spender.toB256], amount.toBytes⟩

def approveSourceFrame (current : Checkpoint) (ctx : Context)
    (spender : Adr) (amount : B256) : Frame :=
  (Frame.enter current ctx (.approve spender amount)).withEvents
    (approveSourceState current.state ctx.sender spender amount)
    [.approval ctx.sender spender amount]

def approveSourceDone (current : Checkpoint) (ctx : Context)
    (spender : Adr) (amount : B256) : RunResult :=
  { status := .success (encodeWords [1]),
    frame := approveSourceFrame current ctx spender amount,
    remaining := .done, childReturns := [] }


theorem approveLP_accept {st : State} {ctx : Context} {owner spender : Adr}
    {amount : B256} (nonstatic : ctx.isStatic = false) :
    st.approveLP ctx owner spender amount =
      .ok (approveSourceState st owner spender amount, [.approval owner spender amount]) := by
  rw [State.approveLP, nonstatic]
  rfl

theorem approve_startImmediate_done {current : Checkpoint} {ctx : Context}
    {spender : Adr} {amount : B256}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false) :
    startImmediate current ctx (.approve spender amount) =
      some (.finished (approveSourceFrame current ctx spender amount) (encodeWords [1])) := by
  simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
    approveLP_accept nonstatic, Frame.finishLP]
  rfl

theorem approve_drive_done {current : Checkpoint} {ctx : Context}
    {spender : Adr} {amount : B256}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false) :
    drive 2 (startTyped current ctx (.approve spender amount)) .done =
      approveSourceDone current ctx spender amount := by
  rw [startTyped, approve_startImmediate_done value nonstatic]
  rfl

theorem approve_runTyped_done {st : State} {ctx : Context} {spender : Adr} {amount : B256}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false) :
    runTyped st ctx (.approve spender amount) .done =
      approveSourceDone { state := st, logs := [], updates := [] } ctx spender amount := by
  exact approve_drive_done value nonstatic

theorem approveSourceFrame_prefix (current : Checkpoint) (ctx : Context)
    (spender : Adr) (amount : B256) :
    (approveSourceFrame current ctx spender amount).context = ctx ∧
    (approveSourceFrame current ctx spender amount).checkpoint = current ∧
    (approveSourceFrame current ctx spender amount).current.logs =
      current.logs ++ [.owned (writerEntryOrigin ctx) (.approval ctx.sender spender amount)] ∧
    (approveSourceFrame current ctx spender amount).current.updates = current.updates ∧
    (approveSourceFrame current ctx spender amount).segment = 0 ∧
    (approveSourceFrame current ctx spender amount).afterCall = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- The Nat ABI guard needs actual calldata representability, not modular identification. -/
theorem approve_word_guards_iff {sevm : Sevm}
    (representable : sevm.data.length < 2 ^ 256) :
    ((4 : B256) ≤ sevm.data.length.toB256 ∧
      (64 : B256) ≤ sevm.data.length.toB256 - 4) ↔ 68 ≤ sevm.data.length := by
  constructor
  · rintro ⟨size, guard⟩
    have natGuard := B256.toNat_le_toNat guard
    rw [B256.toNat_sub_eq_of_le _ _ size, B256.toNat_toB256_of_lt representable] at natGuard
    change 64 ≤ sevm.data.length - 4 at natGuard
    omega
  · intro length
    have size : (4 : B256) ≤ sevm.data.length.toB256 := by
      apply B256.le_of_toNat_le_toNat
      rw [B256.toNat_toB256_of_lt representable]
      change 4 ≤ sevm.data.length
      omega
    refine ⟨size, ?_⟩
    apply B256.le_of_toNat_le_toNat
    rw [B256.toNat_sub_eq_of_le _ _ size, B256.toNat_toB256_of_lt representable]
    change 64 ≤ sevm.data.length - 4
    omega

theorem WriterRep.approve_public_post {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (approveTouched sevm.caller (approveSpender sevm))) :
    WriterRep (WriterExtend K (approveTouched sevm.caller (approveSpender sevm)))
      ((approvePublicPost sevm b [0x095ea7b3] getterInitMemory G).getStor sevm.currentTarget)
      (approveSourceState st sevm.caller (approveSpender sevm) (approveAmount sevm)) := by
  change WriterRep (WriterExtend K (approveTouched sevm.caller (approveSpender sevm)))
    ((approveCoreBase sevm b sevm.caller (approveSpender sevm) (approveAmount sevm)).getStor
      sevm.currentTarget)
    (approveSourceState st sevm.caller (approveSpender sevm) (approveAmount sevm))
  rw [approveCoreBase, Devm.addLog_getStor, afterSstore_getStor_self]
  exact rep.approve_store fresh


/-- Project the checked post symbolically; never evaluate the concrete memory write chain. -/
theorem approvePublicPost_facts {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} (mem : PtrMem 128 96 M) :
    (approvePublicPost sevm b R M G).output = encodeWords [1] ∧
    (approvePublicPost sevm b R M G).logs = b.logs ++
      [approvalRawLog sevm.currentTarget sevm.caller (approveSpender sevm) (approveAmount sevm)] ∧
    (approvePublicPost sevm b R M G).getStor sevm.currentTarget =
      (b.getStor sevm.currentTarget).set (approveSlot sevm) (approveAmount sevm) ∧
    (∀ a, a ≠ sevm.currentTarget → (approvePublicPost sevm b R M G).getStor a = b.getStor a) ∧
    (approvePublicPost sevm b R M G).gasLeft = G := by
  unfold approvePublicPost
  have memory := getterWordMemory_ptr
    (approveScratch_ptr mem sevm.caller.toB256 (approveSpender sevm).toB256)
    (approveAmount sevm)
  have facts := getterWordPost_facts
    (b := approveCoreBase sevm b sevm.caller (approveSpender sevm) (approveAmount sevm))
    (R := R) (v := 1) (G := G) memory.wf
  refine ⟨?_, ?_, ?_, ?_, facts.2.2.2⟩
  · simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil] using facts.1
  · rw [facts.2.2.1]
    change (afterSstore sevm b (approveSlot sevm) (approveAmount sevm)).logs ++
      [approvalRawLog sevm.currentTarget sevm.caller (approveSpender sevm) (approveAmount sevm)] = _
    rw [afterSstore_logs]
  · rw [facts.2.1 sevm.currentTarget, approveCoreBase, Devm.addLog_getStor,
      afterSstore_getStor_self]
    rfl
  · intro a different
    rw [facts.2.1 a, approveCoreBase, Devm.addLog_getStor,
      afterSstore_getStor_ne _ _ _ _ _ different.symm]

theorem approve_startImmediate_inv {current : Checkpoint} {ctx : Context}
    {spender : Adr} {amount : B256} {sourceFrame : Frame} {returndata : Bytes}
    (accepted : startImmediate current ctx (.approve spender amount) =
      some (.finished sourceFrame returndata)) :
    ctx.value = 0 ∧ ctx.isStatic = false ∧
      sourceFrame = approveSourceFrame current ctx spender amount ∧ returndata = encodeWords [1] := by
  have value : ctx.value = 0 := by
    by_contra paid
    simp only [startImmediate, ite_eq_left paid, Frame.fail, Option.some.injEq] at accepted
    cases accepted
  have nonstatic : ctx.isStatic = false := by
    cases static : ctx.isStatic with
    | false => rfl
    | true =>
      simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value),
        getterResult, State.approveLP, static, ite_true, Frame.finishLP,
        Frame.fail, Option.some.injEq] at accepted
      cases accepted
  rw [approve_startImmediate_done value nonstatic] at accepted
  have fields := SegmentResult.finished.inj (Option.some.inj accepted)
  exact ⟨value, nonstatic, fields.1.symm, fields.2.symm⟩

/-- Local frame facts; chronology still supplies the incoming checkpoint and invocation. -/
def ApproveSourceResult (K : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat)
    (sevm : Sevm) (b post : Devm) (residual : Nat) : Prop :=
  post = approvePublicPost sevm b [0x095ea7b3] getterInitMemory residual ∧
  WriterRep (WriterExtend K (approveTouched sevm.caller (approveSpender sevm)))
    (post.getStor sevm.currentTarget)
    (approveSourceState current.state sevm.caller (approveSpender sevm) (approveAmount sevm)) ∧
  startImmediate current (writerContext sevm invocation) (approveDecodedEntry sevm) =
    some (.finished (approveSourceFrame current (writerContext sevm invocation)
      (approveSpender sevm) (approveAmount sevm)) (encodeWords [1])) ∧
  drive 2 (startTyped current (writerContext sevm invocation) (approveDecodedEntry sevm)) .done =
    approveSourceDone current (writerContext sevm invocation) (approveSpender sevm) (approveAmount sevm) ∧
  (approveSourceFrame current (writerContext sevm invocation)
    (approveSpender sevm) (approveAmount sevm)).context = writerContext sevm invocation ∧
  (approveSourceFrame current (writerContext sevm invocation)
    (approveSpender sevm) (approveAmount sevm)).checkpoint = current ∧
  (approveSourceFrame current (writerContext sevm invocation)
    (approveSpender sevm) (approveAmount sevm)).current.logs = current.logs ++
      [.owned (writerEntryOrigin (writerContext sevm invocation))
        (.approval sevm.caller (approveSpender sevm) (approveAmount sevm))] ∧
  (approveSourceFrame current (writerContext sevm invocation)
    (approveSpender sevm) (approveAmount sevm)).current.updates = current.updates ∧
  post.output = encodeWords [1] ∧
  post.logs = b.logs ++ [approvalRawLog sevm.currentTarget sevm.caller
    (approveSpender sevm) (approveAmount sevm)] ∧
  post.getStor sevm.currentTarget =
    (b.getStor sevm.currentTarget).set (approveSlot sevm) (approveAmount sevm) ∧
  (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) ∧
  post.gasLeft = residual

theorem approve_public_source_result {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (approveTouched sevm.caller (approveSpender sevm)))
    (value : sevm.value = 0) (nonstatic : sevm.isStatic = false) :
    ApproveSourceResult K current invocation sevm b
      (approvePublicPost sevm b [0x095ea7b3] getterInitMemory G) G := by
  have sourceFacts := approveSourceFrame_prefix current (writerContext sevm invocation)
    (approveSpender sevm) (approveAmount sevm)
  have facts := approvePublicPost_facts (sevm := sevm) (b := b)
    (R := [0x095ea7b3]) (G := G) getterInitMemory_ptr
  exact ⟨rfl, rep.approve_public_post fresh, approve_startImmediate_done value nonstatic,
    approve_drive_done value nonstatic, sourceFacts.1, sourceFacts.2.1, sourceFacts.2.2.1,
    sourceFacts.2.2.2.1, facts⟩

/-- Successful literal bytecode derives source acceptance; no source endpoint is a premise. -/
theorem approve_bytecode_refines_source {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (approveTouched sevm.caller (approveSpender sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 68 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      ∃ residual, ApproveSourceResult K current invocation sevm b post residual := by
  obtain ⟨value, size, guard, nonstatic, residual, eq⟩ :=
    approve_bytecode_refines_raw codeEq fork selector run
  refine ⟨value, (approve_word_guards_iff representable).mp ⟨size, guard⟩,
    nonstatic, residual, ?_⟩
  rw [eq]
  exact approve_public_source_result rep fresh value nonstatic

/-- Existing handler acceptance yields exact raw gas with the actual selected-store sentry. -/
theorem approve_source_bytecode_exact {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b : Devm} {G c : Nat}
    {sourceFrame : Frame} {returndata : Bytes}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (approveTouched sevm.caller (approveSpender sevm)))
    (representable : sevm.data.length < 2 ^ 256) (length : 68 ≤ sevm.data.length)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (cost : c = sstoreCost sevm b (approveSlot sevm) (approveAmount sevm))
    (sentry : gCallStipend < G + c + 1898)
    (accepted : startImmediate current (writerContext sevm invocation) (approveDecodedEntry sevm) =
      some (.finished sourceFrame returndata)) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + c + 2342))
      (approvePublicPost sevm b [0x095ea7b3] getterInitMemory G) ∧
    Nonempty (Exec 0 sevm (St b [] Mem.empty (G + c + 2342))
      (.ok (approvePublicPost sevm b [0x095ea7b3] getterInitMemory G))) ∧
    sourceFrame = approveSourceFrame current (writerContext sevm invocation)
      (approveSpender sevm) (approveAmount sevm) ∧
    returndata = encodeWords [1] ∧
    ApproveSourceResult K current invocation sevm b
      (approvePublicPost sevm b [0x095ea7b3] getterInitMemory G) G := by
  obtain ⟨value, nonstatic, frameEq, dataEq⟩ := approve_startImmediate_inv accepted
  obtain ⟨size, guard⟩ := (approve_word_guards_iff representable).mpr length
  exact ⟨approve_pc0_exact fork value size selector guard cost sentry nonstatic,
    approve_bytecode_live_raw codeEq fork value size selector guard cost sentry nonstatic,
    frameEq, dataEq, approve_public_source_result rep fresh value nonstatic⟩

/-- Successful raw pc0 execution derives exact consumption for the typed approve entry. -/
theorem approve_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (approveTouched sevm.caller (approveSpender sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 68 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      ∃ residual, ApproveSourceResult K current invocation sevm b post residual ∧
        ExactConsumes (startTyped current (writerContext sevm invocation) (approveDecodedEntry sevm)) .done
          { status := .success post.output,
            frame := approveSourceFrame current (writerContext sevm invocation)
              (approveSpender sevm) (approveAmount sevm),
            remaining := .done, childReturns := [] } := by
  obtain ⟨value, size, nonstatic, residual, result⟩ :=
    approve_bytecode_refines_source rep fresh representable codeEq fork selector run
  have accepted := result.2.2.1
  have output := result.2.2.2.2.2.2.2.2.1
  have typed : startTyped current (writerContext sevm invocation) (approveDecodedEntry sevm) =
      .finished (approveSourceFrame current (writerContext sevm invocation)
        (approveSpender sevm) (approveAmount sevm)) post.output := by
    unfold startTyped
    rw [accepted]
    dsimp only []
    rw [← output]
  refine ⟨value, size, nonstatic, residual, result, ?_⟩
  rw [typed]
  exact ExactConsumes.finished (approveSourceFrame current (writerContext sevm invocation)
    (approveSpender sevm) (approveAmount sevm)) post.output

end Blanc.Lift.UniswapV2Pair
