import Blanc.Lift.UniswapV2Pair.PermitTurns

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The source recovery request and copied reply are those of the same original
instruction, processed slot, and returned machine state. -/
theorem PermitCallOccurrence.sourceCall {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (actual : PermitCallOccurrence root b) (settled : PermitRecoverySettlement actual)
    (source : PermitSourceResult K current invocation root.sevm b post
      actual.call.returned.devm actual.out settled.entered post.gasLeft) :
    ∃ observed : SourceCallAt root (permitPublicSuspended current invocation root.sevm)
        (permitPublicRequest current root.sevm) (permitExternalResult actual.out settled.entered) 0,
      observed.call = actual.call ∧ observed.paths = settled.paths := by
  have calldata := source.2.2.2.1
  have target := source.2.2.2.2.1
  refine ⟨{
    call := actual.call
    message := settled.message
    resume := Resume.call settled.parent 450 32
    nextPc := actual.call.occurrence.node.pc + 1
    child := settled.child
    outputOffset := 450
    outputSize := 32
    parent := settled.parent
    spawned := settled.spawned
    target := by rw [settled.messageEq]; exact congrArg some target.symm
    caller := by rw [settled.messageEq]; rfl
    value := by rw [settled.messageEq]; rfl
    calldata := by rw [settled.messageEq]; exact calldata.symm
    static := by
      rw [settled.messageEq]
      simp [callMsg, externalStatic, permitPublicRequest, permitRequest, requestFor]
    response := settled.process
    resumeEq := rfl
    resumed := settled.resumed
    replyAt := by
      apply SourceReplyAt.recovery (by rfl)
      · rw [settled.clean]; rfl
      · exact settled.output.symm
      · exact actual.recovered_image.symm
    guarded := by intro impossible; cases impossible
    unguardedEntry := by intro _; exact settled.enteredEq
    paths := settled.paths
    queue := settled.queue
    childFrames := settled.childFrames
    partition := settled.partition
  }, rfl, rfl⟩

/-- The exact same source result consumes the original recovery occurrence and
then the actual returned frame's closed suffix. -/
theorem PermitCallOccurrence.positionalConsumes {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (actual : PermitCallOccurrence root b) (settled : PermitRecoverySettlement actual)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (source : PermitSourceResult K current invocation root.sevm b post
      actual.call.returned.devm actual.out settled.entered post.gasLeft)
    {views : List StaticViewTurn} (mapped : views.map Prod.fst = settled.paths)
    (authentic : ∀ picked ∈ views,
      picked.Authentic (permitPublicSuspended current invocation root.sevm))
    (during : ExactTurns (permitPublicSuspended current invocation root.sevm)
      (permitPublicRequest current root.sevm) 0 (staticViewTranscript views .done)
      {complete := true, frame := permitPublicSuspended current invocation root.sevm,
        childReturns := staticViewChildReturns (permitPublicSuspended current invocation root.sevm)
          (permitPublicRequest current root.sevm) 0 views}) :
    PositionalConsumes root root 0
      (startTyped current (writerContext root.sevm invocation) (permitDecodedEntry root.sevm))
      (.next (permitExternalResult actual.out settled.entered) (staticViewTranscript views .done) .done)
      (permitPublicDone current invocation root.sevm
        (staticViewChildReturns (permitPublicSuspended current invocation root.sevm)
          (permitPublicRequest current root.sevm) 0 views)) := by
  obtain ⟨observed, sameCall, samePaths⟩ := actual.sourceCall settled source
  obtain ⟨recovered, signer, nonstatic, _⟩ := actual.post_image success fork
  have noCode : settled.entered = false → views = [] := by
    intro missing
    have slot : actual.call.occurrence.slot = .none := by
      cases eq : actual.call.occurrence.slot with
      | none => rfl
      | some pair =>
        have entered := settled.enteredEq
        rw [eq] at entered
        exact Bool.noConfusion (missing.symm.trans entered)
    have empty := settled.queue.paths_unique (Or.inl ⟨slot, rfl⟩)
    exact List.eq_nil_of_map_eq_nil (mapped.trans empty)
  have annotated : PositionalTurns (permitPublicSuspended current invocation root.sevm)
      (permitPublicRequest current root.sevm) observed.paths
      (staticViewTranscript views .done)
      {complete := true, frame := permitPublicSuspended current invocation root.sevm,
        childReturns := staticViewChildReturns (permitPublicSuspended current invocation root.sevm)
          (permitPublicRequest current root.sevm) 0 views} := by
    rw [samePaths]
    exact .staticViews views mapped authentic during
  have resumed := permit_resume_finished (current := current)
    (ctx := writerContext root.sevm invocation) (owner := permitOwner root.sevm)
    (spender := permitSpender root.sevm) (value := permitValue root.sevm)
    (deadline := permitDeadline root.sevm) (v := permitV root.sevm)
    (r := permitR root.sevm) (s := permitS root.sevm) (codeExists := settled.entered)
    nonstatic recovered signer
  have terminal : PositionalConsumes root actual.call.returned 1
      (.finished (permitSourceFrame current (writerContext root.sevm invocation)
        (permitOwner root.sevm) (permitSpender root.sevm) (permitValue root.sevm)
        (permitDeadline root.sevm) (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)) [])
      .done (permitSourceDone current (writerContext root.sevm invocation)
        (permitOwner root.sevm) (permitSpender root.sevm) (permitValue root.sevm)
        (permitDeadline root.sevm) (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)) :=
    .finished _ [] (actual.noExecSuffix fork)
  rw [← resumed] at terminal
  have consumed := PositionalConsumes.nextCall (start := root)
    (continuation := .permitRecovery (permitOwner root.sevm) (permitSpender root.sevm)
      (permitValue root.sevm)) observed
    (by rw [sameCall]; exact actual.gap) (by rfl)
    (by intro missing; rw [noCode missing]; rfl) annotated (by
      simpa only [sameCall, permitExternalResult, ite_true, permitPublicSuspended,
        permitPublicRequest] using terminal)
  rw [source.2.2.1]
  simpa only [permitPublicDone, permitSourceDone, List.append_nil,
    permitPublicSuspended, permitPublicRequest] using consumed

/-- Original raw-success premises produce one recovery witness, its source
result, positional transcript, and exact erasure of that same transcript. -/
theorem permit_bytecode_positional_consumes {U K : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    {current : Checkpoint} {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (touched : ∀ k ∈ permitTouched (permitOwner sevm) (permitSpender sevm), U k)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf) (freshOutput : b.output = [])
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (good : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    sevm.value = 0 ∧ 228 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      sevm.benvStat.time ≤ permitDeadline sevm ∧
      ∃ (actual : PermitCallOccurrence ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b)
        (settled : PermitRecoverySettlement actual) (views : List StaticViewTurn),
        PermitSourceResult K current invocation sevm b post actual.call.returned.devm
          actual.out settled.entered post.gasLeft ∧
        PermitRecoveryAuth ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
          actual.out settled.entered views ∧
        PositionalConsumes ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
          ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ 0
          (startTyped current (writerContext sevm invocation) (permitDecodedEntry sevm))
          (.next (permitExternalResult actual.out settled.entered) (staticViewTranscript views .done) .done)
          (permitPublicDone current invocation sevm
            (staticViewChildReturns (permitPublicSuspended current invocation sevm)
              (permitPublicRequest current sevm) 0 views)) ∧
        ExactConsumes (startTyped current (writerContext sevm invocation) (permitDecodedEntry sevm))
          (.next (permitExternalResult actual.out settled.entered) (staticViewTranscript views .done) .done)
          (permitPublicDone current invocation sevm
            (staticViewChildReturns (permitPublicSuspended current invocation sevm)
              (permitPublicRequest current sevm) 0 views)) ∧
        views.map Prod.fst = settled.paths ∧
        (∀ picked ∈ views, picked.Authentic (permitPublicSuspended current invocation sevm)) := by
  obtain ⟨paid, length, nonstatic, timely, actual, settled, views, source, mapped,
    authentic, during⟩ := permit_bytecode_actual_turns (invocation := invocation)
      inj apart sub sem image rep touched installed representable codeEq fork selector
        freshOutput run good
  have annotated := actual.positionalConsumes settled rfl fork source mapped authentic during
  exact ⟨paid, length, nonstatic, timely, actual, settled, views, source,
    ⟨b, G, actual, settled, rfl, rfl, rfl, rfl, mapped⟩,
    annotated, annotated.forget, mapped, authentic⟩

end Blanc.Lift.UniswapV2Pair
