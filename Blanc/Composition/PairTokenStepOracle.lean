import Blanc.Composition.PairTokenStepFrames

/-!
# The per-continuation token oracle of a Pair step (C3, consumed by U6c2)

At one observed call (`SourceCallAt`) of a settled Pair frame, inside the positional consumption
of that frame, the Pair's retained frames from the current node on split as the call's committed
subtree `mid` followed by the frames retained after the call returns.  Across `mid` the booked
token ledger moves from `l` to `l'`, and `StepOracle` records what the model side needs:

* the Pair keeps a zero allowance;
* a static request leaves the ledger unchanged;
* an entered successful `balanceOf(pair)` read of the token replies the word of `bal l pair`,
  which reads back as the balance (A9);
* a mutable `transfer` request to the token of `v` leaves the Pair at least `bal l pair - v`;
* a mutable request elsewhere leaves the Pair at least `bal l pair`.

`entered` is the call's child slot being filled: a successful call with an empty slot ran an
enabled precompile, about which no token fact speaks.
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair

/-- **Per-continuation token oracle** (consumed by U6c2).  Across one observed call of a Pair
frame: `l` is the booked ledger before the call's retained subtree, `l'` the ledger after it. -/
structure StepOracle (B : Book) (T pair : Adr) (frame : UniswapV2Pair.Frame) (request : Request)
    (reply : ExternalResult) (entered : Prop) (l l' : B.Ledger) : Prop where
  zero : ∀ g, B.allow l' pair g = 0
  static : externalStatic frame request = true → l' = l
  read : request.target = T → request.calldata = (ExternalOperation.balanceOf pair).encode →
    reply.success = true → entered →
      reply.returndata = (Nat.toB256 (B.bal l pair)).toBytes ∧
        (Bytes.toB256 (reply.returndata.take 32)).toNat = B.bal l pair
  transfer : ∀ {recipient : Adr} {value : B256}, request.target = T →
    request.calldata = (ExternalOperation.transfer recipient value).encode →
    externalStatic frame request = false → B.bal l pair ≤ B.bal l' pair + value.toNat
  other : request.target ≠ T → externalStatic frame request = false →
    B.bal l pair ≤ B.bal l' pair

/-- A call that retains no frame leaves the ledger alone; the oracle holds when the read clause is
vacuous. -/
theorem StepOracle.unchanged {B : Book} {T pair : Adr} {frame : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {entered : Prop} {l : B.Ledger}
    (zero : ∀ g, B.allow l pair g = 0)
    (noRead : request.target = T → request.calldata = (ExternalOperation.balanceOf pair).encode →
      reply.success = true → entered → False) :
    StepOracle B T pair frame request reply entered l l where
  zero := zero
  static _ := rfl
  read target data success enteredH := (noRead target data success enteredH).elim
  transfer _ _ _ := Nat.le_add_right _ _
  other _ _ := Nat.le_refl _

/-! ## Frame facts at a spawning node -/

/-- A continuation's direct children are direct children of the node. -/
theorem parentStep_childFrames_subset {N returned : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep returned N) :
    ∀ c ∈ Exec.childFrames returned.exc, c ∈ Exec.childFrames N.exc := by
  intro c member
  cases edge with
  | cont hstep next => simpa only [Exec.childFrames] using member
  | doneOk hstep henter hresume next => simpa only [Exec.childFrames] using member
  | runOk hstep henter child hresume next =>
      simp only [Exec.childFrames, List.mem_append]
      exact Or.inr member

/-- A same-frame node's direct children are direct children of the frame. -/
theorem parentPrefix_childFrames_subset {root node : Exec.Deriv}
    (reached : Exec.Deriv.ParentPrefix root node) :
    ∀ c ∈ Exec.childFrames node.exc, c ∈ Exec.childFrames root.exc := by
  induction reached with
  | refl => exact fun _ member => member
  | step head _ ih => exact fun c member => parentStep_childFrames_subset head c (ih c member)

/-- At a node that ran a child, the retained frames are the child's subtree (when its settlement
commits) followed by the continuation's. -/
theorem parentStep_descendantFrames_runOk_eq {N returned : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep returned N) {frame : Jaune.Frame} {resume : Resume}
    {nextPc : Nat} {childEvm : Evm} {raw : Execution} {post : Devm}
    {spawn : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn frame resume nextPc}
    {enter : frame.enter = .run childEvm}
    {childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw}
    {resumed : resume.run (frame.settle raw) = .ok post}
    {next : Exec nextPc N.sevm post N.exn}
    (nodeExc : N.exc = .runOk spawn enter childRun resumed next) :
    Exec.descendantFrames N.exc =
      (if settles : Jaune.Frame.settlementCommits frame raw = true then
        Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles) ::
          Exec.descendantFrames childRun
      else []) ++ Exec.descendantFrames returned.exc := by
  have nextEdge : Exec.Deriv.ParentStep ⟨nextPc, N.sevm, post, N.exn, next⟩ N := by
    have shaped : Exec.Deriv.ParentStep ⟨nextPc, N.sevm, post, N.exn, next⟩
        ⟨N.pc, N.sevm, N.devm, N.exn, .runOk spawn enter childRun resumed next⟩ :=
      .runOk _ _ _ _ _
    have same : (⟨N.pc, N.sevm, N.devm, N.exn, .runOk spawn enter childRun resumed next⟩ :
        Exec.Deriv) = N := by
      rw [← nodeExc]
    rw [same] at shaped
    exact shaped
  cases nextEdge.unique edge
  rw [nodeExc]
  by_cases settles : Jaune.Frame.settlementCommits frame raw = true
  · rw [Exec.descendantFrames_runOk_of_settlementCommits spawn enter childRun resumed next settles,
      dite_eq_left_of_eq_true (eq_true settles)]
  · rw [Exec.descendantFrames_runOk_of_not_settlementCommits spawn enter childRun resumed next
      settles, dite_eq_right_of_eq_false (eq_false settles), List.nil_append]

/-- A committed call frame's settlement is its committed post-machine. -/
theorem ofCall_settle_committed {msg : Msg} {raw : Execution}
    (committed : Execution.commits raw = true) :
    (Jaune.Frame.ofCall msg).settle raw = .ok (Execution.committedPost raw committed) := by
  cases raw with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    cases errorEq : post.error with
    | none =>
      simp only [Jaune.Frame.settle, Jaune.Frame.settleMsg, Jaune.Frame.ofCall,
        executeCode.handleErrorWith_ok, processMessage.settle, Bind.bind, Except.bind, errorEq,
        Option.isSome_none, Bool.false_eq_true, ite_false, Execution.committedPost]
    | some error =>
      simp only [Execution.commits, errorEq, Option.isNone_some, Bool.false_eq_true] at committed

/-- What the observed reply is, in terms of the processed child. -/
theorem sourceCallAt_reply_facts {root : Exec.Deriv} {frame : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {index : Nat}
    (observed : SourceCallAt root frame request reply index) :
    reply.success = !observed.child.error.isSome ∧ reply.returndata = observed.child.output := by
  cases observed.replyAt with
  | bytes _ success returndata => exact ⟨success, returndata⟩
  | recovery _ success returndata _ => exact ⟨success, returndata⟩

/-! ## The oracle -/

/-- **The per-continuation token oracle.** -/
theorem pair_token_stepOracle {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
    (abi : Erc20Abi B) (self : SelfCaller C) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (hist : C.Hist trace)
    (apart : pair ≠ T) (answerable : C.Answerable trace pair)
    {P : Exec.Frame} (settledP : P ∈ trace.settledFrames) (atPair : P.sevm.currentTarget = pair)
    {start : Exec.Deriv} {frame : UniswapV2Pair.Frame} {request : Request} {reply : ExternalResult}
    {index : Nat}
    (observed : SourceCallAt (Blanc.Exec.Frame.rootDeriv P) frame request reply index)
    (gap : Exec.Deriv.ExecFreeUntil start observed.call.occurrence.node)
    (locked : LockedBelow pair (Exec.descendantFrames start.exc))
    (toT : request.target = T → externalStatic frame request = false →
      ∃ recipient value, request.calldata = (ExternalOperation.transfer recipient value).encode)
    {pre post : List Exec.Frame}
    (split : trace.settledFrames = pre ++ Exec.descendantFrames start.exc ++ post)
    {l : B.Ledger} (atPre : B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l)
    (zero : ∀ g, B.allow l pair g = 0) :
    ∃ (mid : List Exec.Frame) (l' : B.Ledger),
      Exec.descendantFrames start.exc = mid ++ Exec.descendantFrames observed.call.returned.exc ∧
      B.run l (entryAsks T mid) = some l' ∧
      StepOracle B T pair frame request reply (observed.call.occurrence.slot.isSome = true) l l' :=
    by
  rw [gap.descendantFrames_eq] at split locked ⊢
  have replyFacts := sourceCallAt_reply_facts observed
  rcases observed.queue with ⟨slotNone, -⟩ |
    ⟨childEvm, raw, callee, resume, pc', childRun, next, spawn, enter, resumed, slotSome, nodeExc,
      -⟩
  · -- empty slot: no retained frame
    have notRun : ∀ childEvm, (Jaune.Frame.ofCall observed.message).enter ≠ .run childEvm := by
      intro childEvm run
      have response := observed.response
      rw [slotNone] at response
      unfold ProcessMessage RunFrame at response
      rw [run] at response
      obtain ⟨_, impossible, _⟩ := response
      cases impossible
    refine ⟨[], l, ?_, rfl, StepOracle.unchanged zero ?_⟩
    · rw [Blanc.Exec.Deriv.ParentStep.descendantFrames_spawn_done observed.call.edge
        observed.spawned notRun, List.nil_append]
    · intro _ _ _ entered
      rw [slotNone] at entered
      cases entered
  · have same := spawn.symm.trans observed.spawned
    simp only [Step.spawn.injEq] at same
    obtain ⟨rfl, -, -⟩ := same
    have eq := parentStep_descendantFrames_runOk_eq observed.call.edge nodeExc
    have response := observed.response
    rw [slotSome] at response
    obtain ⟨-, settleEq⟩ := RunFrame.some_inv response
    by_cases settles :
        Jaune.Frame.settlementCommits (Jaune.Frame.ofCall observed.message) raw = true
    · rw [dite_eq_left_of_eq_true (eq_true settles)] at eq
      let c := Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles)
      have cFrames : Exec.committedFrames c.run = c :: Exec.descendantFrames childRun :=
        committedFrames_frame c
      obtain ⟨target, caller, data, static⟩ := observed.child_facts (c := c) enter rfl
      have inNode : c ∈ Exec.childFrames observed.call.occurrence.node.exc := by
        rw [nodeExc]
        simp only [Exec.childFrames, dite_eq_left_of_eq_true (eq_true settles),
          List.singleton_append]
        exact List.mem_cons_self
      have child : c ∈ Exec.childFrames P.run :=
        parentPrefix_childFrames_subset observed.call.sameFrame c inNode
      have lockedC : LockedBelow pair (Exec.committedFrames c.run) := by
        intro D member
        apply locked D
        rw [eq, ← cFrames]
        exact List.mem_append_left _ member
      have splitC : trace.settledFrames =
          pre ++ Exec.committedFrames c.run ++ (Exec.descendantFrames observed.call.returned.exc ++
            post) := by
        rw [split, eq, cFrames, List.append_assoc, List.append_assoc, List.append_assoc]
      obtain ⟨l', step, zero', staticFact, readFact, transferFact, otherFact⟩ :=
        pair_token_child_frames C laws abi self trace hist apart answerable settledP atPair child
          (caller.trans atPair)
          lockedC (fun atT mutable => by
            rw [data]
            exact toT (target.symm.trans atT) (static.symm.trans mutable)) splitC atPre zero
      refine ⟨Exec.committedFrames c.run, l', by rw [eq, cFrames], step, zero',
        fun h => staticFact (static.trans h), ?_, ?_, ?_⟩
      · intro atT readData _ _
        obtain ⟨output, lt⟩ := readFact (target.trans atT) (data.trans readData)
        have childEq : observed.child = c.post := by
          have settled := settleEq.trans
            (ofCall_settle_committed (Jaune.Frame.raw_commits_of_settlementCommits settles))
          exact Except.ok.inj settled
        have returned : reply.returndata = (Nat.toB256 (B.bal l pair)).toBytes := by
          rw [replyFacts.2, childEq, output]
        refine ⟨returned, ?_⟩
        rw [returned, List.take_of_length_le (Nat.le_of_eq (B256.length_toBytes _)),
          B256.toB256_toBytes, B256.toNat_toB256_of_lt lt]
      · intro recipient value atT transferData mutable
        exact transferFact (target.trans atT) (static.trans mutable) (data.trans transferData)
      · intro elsewhere _
        exact otherFact (fun h => elsewhere (target.symm.trans h))
    · rw [dite_eq_right_of_eq_false (eq_false settles), List.nil_append] at eq
      refine ⟨[], l, by rw [eq, List.nil_append], rfl, StepOracle.unchanged zero ?_⟩
      intro _ _ success _
      have clean : observed.child.error.isSome = false := by
        rw [replyFacts.1] at success
        cases h : observed.child.error.isSome
        · rfl
        · rw [h] at success; cases success
      exact settles (ProcessMessage.settlementCommits_of_some_ok_clean response clean)

end Blanc.Composition.PairTokenJoint
