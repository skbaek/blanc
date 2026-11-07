import Batteries.Tactic.OpenPrivate
import Blanc.ExecutionKeptFacts
import Blanc.ExecutionKeptTop
import Blanc.ExecutionHistory
import Blanc.ExecutionInCellProvenance
import Blanc.LadderReached

/-!
# Kept frames along a transaction, a body and a history

The levels above `MessageRoots`. Everything is stated over a rule fact, `KeptRules`, and so holds on both lanes of the
rule record. Settlement is only passed over: no statement here names a gas amount, and no statement names a frame that
did not commit.

A transaction's environment differs from its block's in `origState` alone, so the entry statements of a stage read
`{stat with origState := orig}`.
-/

namespace Blanc

open Jaune ExecutionTrace

open private runPreparedTopFrame from Jaune.Transaction

open private TopRun TopRun.shape TopRun.frame TopRun.prepared TopRun.settled TopRun.state_eq TopRun.create_ne
  TopRun.entry_getCode TopRun.commits_eq MessageRoots.cases message_top settle_ofCall_committed
  settle_ofCreate_committed settle_error_rollback precomp_post Prepared.away Prepared.codeAddress
  Prepared.currentTarget runFrame_cases prepare_spec settleMsg_error from Blanc.ExecutionKeptTop

/-! ## The rule fact -/

/-- The rule facts the levels above a message read: EIP-6780 selfdestruct, no touched sweep, no block rewards. -/
structure KeptRules (r : ForkRules) : Prop where
  selfdestruct : r.settle.selfdestructOnlyCreated = true
  noSweep : r.settle.touchedSweep = false
  noRewards : r.pow = none
  /-- A byte of calldata costs at least four gas, zero or not. -/
  dataCost : 4 ≤ r.txr.dataNonZero

/-- The forks these levels speak about: the covered ones and Amsterdam. -/
def KeptFork (f : Fork) : Prop := CoveredFork f ∨ f = .amsterdam

theorem KeptFork.rules {f : Fork} (h : KeptFork f) : KeptRules f.ruleSet := by
  rcases h with covered | rfl
  · exact covered.cases (motive := fun f => KeptRules f.ruleSet) ⟨rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, rfl, by decide⟩
      ⟨rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, rfl, by decide⟩
  · exact ⟨rfl, rfl, rfl, by decide⟩

/-! ## What a root keeps -/

/-- All the frames a root keeps: nothing if its settlement does not commit, else its run's committed frames. -/
def Root.frames (r : Root) : List Exec.Frame :=
  if Frame.settlementCommits r.frame r.raw = true then Exec.committedFrames r.run else []

/-- All the frames some roots keep, for premises over them. -/
def keptAll (rs : List Root) : List Exec.Frame := rs.flatMap Root.frames

/-- `rs` create nothing at `S`: no frame they keep without a code address runs at `S`. -/
def NoCreateAt (S : Adr) (rs : List Root) : Prop :=
  ∀ f ∈ keptAll rs, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ S

/-- A message that reads its code from its own target, or a creation with no code address. -/
def RoutedMessage (msg : Msg) : Prop :=
  (msg.target.isNone = false → msg.codeAddress = some msg.currentTarget ∧
      msg.code = msg.benv.state.getCode msg.currentTarget) ∧
    (msg.target.isNone = true → msg.codeAddress = none)

/-- The environment of frames below a stage: the stage's, but for the state a transaction opened on. -/
def Exec.Frame.EntryIn (a : Adr) (C : ByteArray) (stat : BenvStat) (f : Exec.Frame) : Prop :=
  ∃ orig, Exec.Frame.EntryAt a C {stat with origState := orig} f

/-! ## The message level, beyond `ExecutionKeptTop` -/

/-- A top-level create never targets an account with code that is no delegation. -/
theorem MessageRoots.create_ne {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {r : Root} (hr : r ∈ rs) {x : Adr}
    (hc : (msg.benv.state.getCode x).toList ≠ []) (hd : ¬ isValidDelegation (msg.benv.state.getCode x))
    (create : msg.target.isNone = true) : msg.currentTarget ≠ x := by
  rcases MessageRoots.cases h with ⟨rfl, -⟩ | ⟨r', m, benv, s, rfl, t⟩
  · cases hr
  · rcases TopRun.frame t with ⟨hn, -⟩ | ⟨-, hf, -⟩
    · rw [create] at hn; cases hn
    · exact TopRun.create_ne t hc hd (by rw [hf]; rfl)

/-- **Not deleted.** Under EIP-6780 a message reports no deletion of a code-bearing account that it neither inherited
as deleted nor found created. -/
theorem MessageRoots.not_deleted {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {a : Adr} (hc : (msg.benv.state.getCode a).toList ≠ [])
    (hd : ¬ isValidDelegation (msg.benv.state.getCode a)) (inherited : a ∉ msg.inheritedDeletions)
    (created : a ∉ msg.benv.createdAccounts) (flag : msg.benv.stat.rules.settle.selfdestructOnlyCreated = true) :
    a ∉ out.accountsToDelete := by
  intro member
  rcases h.deletions member with old | ⟨r, hr, settles, hk⟩
  · exact inherited old
  · obtain ⟨hcode, -⟩ := h.entry_kept hr hc hd
    obtain ⟨hdel, hcreated⟩ := h.entry_sets hr
    have hstat := (h.entry_routing hr).2.2.1
    refine (Exec.keptAccount r.run (Frame.raw_commits_of_settlementCommits settles)
      (by rw [hcode]; exact hc) ?_ (by rw [hdel]; exact inherited) (by rw [hstat]; exact flag)).2 hk
    intro inCreated
    rcases hcreated a inCreated with old | ⟨create, same⟩
    · exact created old
    · exact h.create_ne hr hc hd create same.symm

/-! ## A create that ran no root -/

private theorem enteredFrame_ne_none {f : Frame} {benv : Benv} (ht : f.inner.benvAfterTransfer = .ok benv)
    (ca : f.inner.codeAddress = none) : enteredFrame f ≠ none := by
  have enter : executeCode.enter (f.inner.withBenv benv) = .inl (initEvm (f.inner.withBenv benv)) := by
    unfold executeCode.enter
    dsimp only [Msg.withBenv]
    rw [ca]
  unfold enteredFrame Frame.enter
  rw [ht]
  dsimp only
  rw [enter]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]

private theorem preparedEntry_ne_none {f : Frame} {d : Devm} {benv : Benv} (ht : f.inner.benvAfterTransfer = .ok benv)
    (ca : f.inner.codeAddress = none) : preparedEntry f d ≠ none := by
  have enter : executeCode.enter (f.inner.withBenv benv) = .inl (initEvm (f.inner.withBenv benv)) := by
    unfold executeCode.enter
    dsimp only [Msg.withBenv]
    rw [ca]
  unfold preparedEntry
  rw [ht]
  dsimp only
  rw [enter]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- A create with no code address that enters no machine rolled back before any frame: it collided, or its preparation
failed. -/
private theorem create_no_entry {msg : Msg} {state : State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok (state, out)) (create : msg.target.isNone = true)
    (ca : msg.codeAddress = none) (none : messageEntry msg = none) : state = msg.benv.state := by
  unfold messageEntry at none
  have body := h
  unfold processMessageCall at body
  simp only [create, ↓reduceIte] at body
  unfold processMessageCall.create at body
  cases hsg : msg.benv.stat.rules.stateGas with
  | none =>
      rw [hsg] at none body
      dsimp only at none
      unfold legacyEntry at none
      simp only [create, ↓reduceIte] at none
      cases collision : messageCreateCollision msg with
      | true => exact (processMessageCall_createCollision_out_noStateGas hsg create collision h).1
      | false =>
          simp only [collision, Bool.false_eq_true, ↓reduceIte] at none
          unfold messageCreateCollision at collision
          simp only [collision, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at body
          obtain ⟨evm, hevm, -⟩ := Except.bind_eq_ok body
          have core : runFrame (Frame.ofCreate msg) = .ok evm := Except.bimap_id_eq_ok hevm
          obtain ⟨benv, ht, -⟩ := runFrame_cases core
          exact (enteredFrame_ne_none ht ca none).elim
  | some st =>
      rw [hsg] at none body
      dsimp only at none body
      unfold amsterdamEntry at none
      unfold processTopLevelAmsterdam at body
      cases hp : prepareTopLevelAmsterdam st msg with
      | error p =>
          rw [hp] at body
          rcases p with ⟨err, d⟩
          dsimp only at body
          unfold settleTopLevelPreparationFailure at body
          split at body
          · simp only [Except.ok.injEq, Prod.mk.injEq] at body
            exact body.1.symm
          all_goals cases body
      | ok p =>
          rcases p with ⟨m, d⟩
          rw [hp] at body none
          dsimp only at body none
          simp only [create, ↓reduceIte] at none
          obtain ⟨evm, hevm, -⟩ := Except.bind_eq_ok body
          have hrun : runPreparedTopFrame (Frame.ofCreate m) d = .ok evm := Except.bimap_id_eq_ok hevm
          obtain ⟨prep, -, -⟩ := prepare_spec hp
          have hca : (Frame.ofCreate m).inner.codeAddress = Option.none :=
            (Prepared.codeAddress prep create).trans ca
          cases ht : (Frame.ofCreate m).inner.benvAfterTransfer with
          | error e =>
              unfold runPreparedTopFrame at hrun
              rw [ht] at hrun
              exact (settleMsg_error hrun).elim
          | ok benv => exact (preparedEntry_ne_none ht hca none).elim

/-! ## What a root's frames premise gives -/

private theorem Root.mem_frames {r : Root} (settles : Frame.settlementCommits r.frame r.raw = true) :
    Exec.Frame.ofRun r.run (Frame.raw_commits_of_settlementCommits settles) ∈ r.frames ∧
      ∀ f ∈ Exec.descendantFrames r.run, f ∈ r.frames := by
  have c := Frame.raw_commits_of_settlementCommits settles
  unfold Root.frames
  rw [ite_eq_left settles, Exec.committedFrames, dite_eq_left c]
  exact ⟨List.mem_cons_self, fun f hf => List.mem_cons_of_mem _ hf⟩

private theorem NoCreateAt.of_mem {S : Adr} {rs : List Root} (avoid : NoCreateAt S rs) {r : Root} (hr : r ∈ rs) :
    ∀ f ∈ r.frames, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ S :=
  fun f hf => avoid f (List.mem_flatMap.mpr ⟨r, hr, hf⟩)

/-- A root at `S` that commits and creates nothing there runs empty code, when it starts with none at `S`. -/
private theorem MessageRoots.target_code {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) (routed : RoutedMessage msg) {S : Adr}
    (empty : msg.benv.state.getCode S = ByteArray.empty)
    (away : ∀ auth ∈ msg.tenv.stat.auths, recoverAuthority auth ≠ .ok S) (avoid : NoCreateAt S rs) {r : Root} (hr : r
        ∈ rs)
    (settles : Frame.settlementCommits r.frame r.raw = true) :
    r.evm.sta.currentTarget = S → r.evm.sta.code = ByteArray.empty := by
  intro here
  have same : msg.currentTarget = S := (h.entry_routing hr).2.1.symm.trans here
  cases call : msg.target.isNone with
  | false =>
      obtain ⟨hca, hcode⟩ := routed.1 call
      subst same
      exact (h.entry_call_code hr call hca hcode).2 empty away
  | true =>
      have ca : r.evm.sta.codeAddress = none := (h.entry_create hr call).trans (routed.2 call)
      exact (avoid.of_mem hr _ (Root.mem_frames settles).1 ca here).elim

private theorem committedPost_codeAt {S : Adr} {pre : Devm} {raw : Execution} (rel : Execution.Rel (Devm.CodeAt S) pre
    raw)
    (c : Execution.commits raw = true) : (Execution.committedPost raw c).getCode S = pre.getCode S := by
  cases raw with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at c
  | ok final => exact rel

/-- **A code-free account stays code-free across a message**, committing or not, when no authorization recovers to it
and no frame the message keeps creates there. -/
theorem MessageRoots.empty_stays {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) (routed : RoutedMessage msg) {S : Adr}
    (empty : msg.benv.state.getCode S = ByteArray.empty)
    (away : ∀ auth ∈ msg.tenv.stat.auths, recoverAuthority auth ≠ .ok S) (avoid : NoCreateAt S rs) :
    state.getCode S = ByteArray.empty := by
  have congrCode : ∀ {x y : State}, x = y → x.getCode S = y.getCode S := fun e => by rw [e]
  rcases MessageRoots.cases h with ⟨rfl, -⟩ | ⟨r, m, benv, s, rfl, t⟩
  · rcases message_top h.1 with ⟨-, hst, -⟩ | ⟨hnone, m, f, benv, e, adr, s, t⟩ | ⟨m, f, benv, e, s, hsome, t⟩
    · rw [hst]
      exact empty
    · have prepared := (Prepared.away (TopRun.prepared t) S away).trans empty
      rcases TopRun.frame t with ⟨-, hf⟩ | ⟨create, -, -⟩
      · subst hf
        by_cases clean : s.error.isNone = true
        · have c := Frame.raw_commits_of_settlementCommits ((TopRun.commits_eq t).trans clean)
          rw [TopRun.state_eq t, congrCode (settle_ofCall_committed (TopRun.settled t) c).1,
            congrCode (precomp_post e adr c).1]
          exact (TopRun.entry_getCode t S).trans prepared
        · have dirty : s.error.isSome = true := by
            cases he : s.error
            · simp only [he, Option.isNone_none, not_true_eq_false] at clean
            · rfl
          rw [TopRun.state_eq t, congrCode (settle_error_rollback (.inl rfl) (TopRun.settled t) dirty)]
          exact prepared
      · rw [create_no_entry h.1 create (routed.2 create) hnone]
        exact empty
    · have hmap := h.2
      rw [hsome] at hmap
      cases hmap
  · have hr : r ∈ [r] := List.mem_singleton.mpr rfl
    have prepared := (Prepared.away (TopRun.prepared t) S away).trans empty
    by_cases clean : s.error.isNone = true
    · have settles : Frame.settlementCommits r.frame r.raw = true := (TopRun.commits_eq t).trans clean
      have c := Frame.raw_commits_of_settlementCommits settles
      have rel := Exec.codeAt_retained_neutral r.run c (fun f hf => avoid.of_mem hr f ((Root.mem_frames settles).2 f
          hf))
      have post : (Execution.committedPost r.raw c).getCode S = ByteArray.empty :=
        (committedPost_codeAt rel c).trans ((TopRun.entry_getCode t S).trans prepared)
      rcases TopRun.shape t with hf | hf
      · rw [TopRun.state_eq t, congrCode (settle_ofCall_committed (hf ▸ TopRun.settled t) c).1]
        exact post
      · have ne : m.currentTarget ≠ S := by
          rw [Prepared.currentTarget (TopRun.prepared t), ← (h.entry_routing hr).2.1]
          intro here
          have create : msg.target.isNone = true := by
            rcases TopRun.frame t with ⟨-, call⟩ | ⟨create, -, -⟩
            · rw [hf] at call
              have := congrArg Frame.isCreate call
              simp only [Frame.ofCreate, Frame.ofCall, Bool.true_eq_false] at this
            · exact create
          exact avoid.of_mem hr _ (Root.mem_frames settles).1
            ((h.entry_create hr create).trans (routed.2 create)) here
        rw [TopRun.state_eq t]
        exact ((settle_ofCreate_committed (hf ▸ TopRun.settled t) c clean).1 S ne).1.trans post
    · have dirty : s.error.isSome = true := by
        cases he : s.error
        · simp only [he, Option.isNone_none, not_true_eq_false] at clean
        · rfl
      rw [TopRun.state_eq t, congrCode (settle_error_rollback (TopRun.shape t) (TopRun.settled t) dirty)]
      exact prepared

/-! ## Caller exclusion for roots whose caller may be `S` -/

/-- One entered child, at a parent that runs empty code at `S`: it runs empty code if it is at `S`. -/
private theorem Evm.step_spawn_targetCode_neutral {S : Adr} {pc nextPc : Nat} {sevm : Sevm} {pre : Devm} {frame : Frame}
    {resume : Resume} {child : Evm} (spawn : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc)
    (enter : frame.enter = .run child) (targetCode : sevm.currentTarget = S → sevm.code = ByteArray.empty)
    (childEmpty : child.dyna.getCode S = ByteArray.empty)
    (avoid : child.sta.codeAddress = none → child.sta.currentTarget ≠ S) :
    child.sta.currentTarget = S → child.sta.code = ByteArray.empty := by
  intro target
  have parentTarget : sevm.currentTarget ≠ S := fun eq => Evm.step_empty_code_not_spawn (targetCode eq) spawn
  obtain ⟨x, _, instruction, _⟩ := Evm.step_spawn_inv spawn
  have emptyAt : pre.getCode S = ByteArray.empty := by
    rw [← (Evm.step_spawn_child spawn enter).2.1 S]
    exact childEmpty
  have frameTarget : frame.inner.currentTarget = S := (Frame.enter_run_currentTarget enter).symm.trans target
  cases x with
  | create =>
    exact False.elim (avoid (by
      rw [Frame.enter_run_codeAddress enter]
      exact Xinst.step_create_spawn_codeAddress_neutral (Or.inl rfl) instruction) target)
  | create2 =>
    exact False.elim (avoid (by
      rw [Frame.enter_run_codeAddress enter]
      exact Xinst.step_create_spawn_codeAddress_neutral (Or.inr rfl) instruction) target)
  | call =>
    rw [Frame.enter_run_code enter,
      Xinst.step_directCall_spawn_code (Or.inl rfl) instruction (by
        rw [frameTarget, emptyAt]
        decide), frameTarget, emptyAt]
  | staticcall =>
    rw [Frame.enter_run_code enter,
      Xinst.step_directCall_spawn_code (Or.inr rfl) instruction (by
        rw [frameTarget, emptyAt]
        decide), frameTarget, emptyAt]
  | callcode =>
    exact False.elim (parentTarget ((Xinst.step_spawn_context_target (Or.inl rfl) instruction).symm.trans frameTarget))
  | delegatecall =>
    exact False.elim (parentTarget ((Xinst.step_spawn_context_target (Or.inr rfl) instruction).symm.trans frameTarget))

/-- **Caller exclusion at `a`, whatever the run's own caller.** The frames a committing run of a frame not at `a` keeps
at `a` are the outermost there: a parent is not at `a`, so it is their caller or shares their target; and a parent at
`S` runs empty code, so it spawns nothing. -/
theorem Exec.keptAt_caller_ne {a S : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) (target : sevm.currentTarget ≠ a)
    (targetCode : sevm.currentTarget = S → sevm.code = ByteArray.empty) (empty : pre.getCode S = ByteArray.empty)
    (avoid : ∀ f ∈ Exec.descendantFrames run, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ S) :
    ∀ f ∈ Exec.keptAt a run, f.sevm.caller ≠ S := by
  revert target targetCode empty avoid
  refine Exec.retained_induction
    (P := fun _ sevm pre _ run => sevm.currentTarget ≠ a → (sevm.currentTarget = S → sevm.code = ByteArray.empty) →
      pre.getCode S = ByteArray.empty →
      (∀ f ∈ Exec.descendantFrames run, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ S) →
      ∀ f ∈ Exec.keptAt a run, f.sevm.caller ≠ S)
    ?_ ?_ ?_ ?_ ?_ run committed
  · intro pc sevm pre out step _ _ _ _ f member
    simp only [Exec.keptAt, List.not_mem_nil] at member
  · intro pc sevm pre pc' post out step next ih target targetCode empty avoid
    have here : Devm.CodeAt S _ _ := Evm.step_codeAt_neutral (xl := .none) (out := .ok _)
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [step] at h; cases h))
      trivial (by rw [step]; exact ⟨rfl, rfl⟩)
    rw [Exec.descendantFrames] at avoid
    rw [Exec.keptAt]
    exact ih target targetCode (here.trans empty) avoid
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih target targetCode empty avoid
    have here : Devm.CodeAt S _ _ := Evm.step_codeAt_neutral (xl := .none) (out := .ok _)
      (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
        rw [step] at h
        cases h
        rw [enter] at hen
        cases hen))
      trivial (by rw [step]; exact ⟨_, RunFrame.of_done enter, resumed.symm⟩)
    rw [Exec.descendantFrames] at avoid
    rw [Exec.keptAt]
    exact ih target targetCode (here.trans empty) avoid
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH
      target targetCode empty avoid
    rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resumed next settles] at avoid
    have childAvoid : ∀ f ∈ Exec.descendantFrames child, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ S :=
      fun f member => avoid f (List.mem_append_left _ (List.mem_cons_of_mem _ member))
    have rootAvoid := avoid _ (List.mem_append_left _ List.mem_cons_self)
    have childEmpty : childEvm.dyna.getCode S = ByteArray.empty := ((Evm.step_spawn_child step enter).2.1 S).trans empty
    have stepped := Evm.step_spawn_settled_codeAt_neutral step enter
      (Exec.codeAt_retained_neutral child (Frame.raw_commits_of_settlementCommits settles) childAvoid) resumed rootAvoid
    rw [Exec.keptAt, dite_eq_left settles]
    intro f member
    rcases List.mem_append.mp member with member | member
    · by_cases at_a : childEvm.sta.currentTarget = a
      · rw [ite_eq_left at_a, List.mem_singleton] at member
        subst member
        change childEvm.sta.caller ≠ S
        obtain ⟨x, -, instruction, -⟩ := Evm.step_spawn_inv step
        rw [Frame.enter_run_caller enter]
        rcases Xinst.step_spawn_caller_eq_parent_or_target_eq_parent instruction with parent | shared
        · rw [parent]
          exact fun eq => Evm.step_empty_code_not_spawn (targetCode eq) step
        · exact (target (shared.symm.trans ((Frame.enter_run_currentTarget enter).symm.trans at_a))).elim
      · rw [ite_eq_right at_a] at member
        exact childIH at_a (Evm.step_spawn_targetCode_neutral step enter targetCode childEmpty rootAvoid) childEmpty
          childAvoid f member
    · exact nextIH target targetCode (stepped.trans empty) (fun f hf => avoid f (List.mem_append_right _ hf)) f member
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH
      target targetCode empty avoid
    rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resumed next rolled] at avoid
    rw [Exec.keptAt, dite_eq_right rolled, List.nil_append]
    exact nextIH target targetCode ((Evm.step_spawn_rolled_codeAt_neutral step enter resumed rolled).trans empty) avoid

/-- **Caller exclusion over a message.** A frame its root keeps at `a` has a caller other than `S`, unless the root
itself runs at `a` for caller `S`. -/
theorem MessageRoots.caller_ne {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) (routed : RoutedMessage msg) {a S : Adr}
    (empty : msg.benv.state.getCode S = ByteArray.empty)
    (away : ∀ auth ∈ msg.tenv.stat.auths, recoverAuthority auth ≠ .ok S) (avoid : NoCreateAt S rs)
    (outer : msg.caller ≠ S ∨ msg.currentTarget ≠ a) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), f.sevm.caller ≠ S := by
  intro f member
  obtain ⟨r, hr, kept⟩ := List.mem_flatMap.mp member
  obtain ⟨hcaller, htarget, -, -⟩ := h.entry_routing hr
  by_cases settles : Frame.settlementCommits r.frame r.raw = true
  · rw [Root.keptAt, dite_eq_left settles] at kept
    by_cases here : r.evm.sta.currentTarget = a
    · rw [ite_eq_left here, List.mem_singleton] at kept
      subst kept
      change r.evm.sta.caller ≠ S
      rw [hcaller]
      rcases outer with ne | ne
      · exact ne
      · exact (ne (htarget.symm.trans here)).elim
    · rw [ite_eq_right here] at kept
      exact Exec.keptAt_caller_ne r.run (Frame.raw_commits_of_settlementCommits settles) here
        (h.target_code routed empty away avoid hr settles) (h.entry_empty hr empty away)
        (fun g hg => avoid.of_mem hr g ((Root.mem_frames settles).2 g hg)) f kept
  · rw [Root.keptAt, dite_eq_right settles] at kept
    cases kept

/-- **Entry facts over a message.** Every frame its root keeps at `a`, where `a` holds nondelegating code `C`, runs `C`
from its start on fresh machine state, under the message's own environment. -/
theorem MessageRoots.entry_at {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) (routed : RoutedMessage msg) {a : Adr} {C : ByteArray}
    (code : msg.benv.state.getCode a = C) (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (data : msg.data.length < 2 ^ 256) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), Exec.Frame.EntryAt a C msg.benv.stat f := by
  intro f member
  obtain ⟨r, hr, kept⟩ := List.mem_flatMap.mp member
  obtain ⟨-, htarget, hstat, hdata⟩ := h.entry_routing hr
  have hc : (msg.benv.state.getCode a).toList ≠ [] := by rw [code]; exact nonempty
  have hd : ¬ isValidDelegation (msg.benv.state.getCode a) := by rw [code]; exact nondelegating
  by_cases settles : Frame.settlementCommits r.frame r.raw = true
  · have c := Frame.raw_commits_of_settlementCommits settles
    rw [Root.keptAt, dite_eq_left settles] at kept
    by_cases here : r.evm.sta.currentTarget = a
    · rw [ite_eq_left here, List.mem_singleton] at kept
      subst kept
      obtain ⟨hpc, hstack, hmem, hwf, hsize⟩ := h.entry_machine hr
      have same : msg.currentTarget = a := htarget.symm.trans here
      refine ⟨hpc, here, ?_, hstack, hsize, hwf, hstat, by change r.evm.sta.data.length < _; rw [hdata]; exact data⟩
      cases call : msg.target.isNone with
      | false =>
          obtain ⟨hca, hcode⟩ := routed.1 call
          subst same
          exact ((h.entry_call_code hr call hca hcode).1 hc hd).trans code
      | true => exact (h.create_ne hr hc hd call same).elim
    · rw [ite_eq_right here] at kept
      have below := Exec.keptAt_entry r.run c here ((h.entry_kept hr hc hd).1.trans code) nonempty nondelegating f kept
      rw [hstat] at below
      exact below
  · rw [Root.keptAt, dite_eq_right settles] at kept
    cases kept

/-! ## The transaction level -/

/-- The transaction environment `processTransaction` builds for `sender`, on either lane. -/
def transactionTenvAt (active : Benv) (tx : Tx) (index : Nat) (sender : Adr) (price intrinsic : Nat)
    (hashes : List B256) : Tenv :=
  let base := transactionTenv active tx index sender price intrinsic hashes
  let allocation := allocateEvmGas active.stat.rules tx.gas intrinsic
  {base with stat := {base.stat with gas := allocation.executionGas, stateGasReservoir := allocation.stateGasReservoir}}

/-- The prefix of `processTransaction`: the sender `checkTransaction` returned and the message it prepared. -/
def transactionMessage (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) :
    Except TransitionError (Adr × Msg) := do
  let active := benv.beginTransaction
  let validationSender ← recoverValidationSender active tx
  let ⟨intrinsic, _⟩ ← Except.mapError .transaction (validateTransaction active.stat.rules tx validationSender)
  let ⟨sender, price, hashes, _⟩ ← checkTransaction active (transactionPreludeBout bout tx index) tx
  let debit ← ((active.state.incrNonce sender).subBal sender (tx.gas * price + transactionBlobGasFee active
      tx).toB256).toExcept
    (TransitionError.internal (.invariant (.text "balance underflow")))
  let msg ← prepareMessage {active with state := debit} (transactionTenvAt active tx index sender price intrinsic
      hashes) tx
  .ok (sender, msg)

/-- `processTransaction` returned `(state, bout')`, and `rs` are the roots of the message it prepared for `sender`. -/
def TransactionRoots (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) (state : State) (bout' : BlockOutput)
    (sender : Adr) (rs : List Root) : Prop :=
  processTransaction benv bout tx index = .ok (state, bout') ∧
    ∃ msg messageState messageOut, transactionMessage benv bout tx index = .ok (sender, msg) ∧
      MessageRoots msg messageState messageOut rs

/-- The whole of `processTransaction`, passing over the settlement amounts. -/
private theorem processTransaction_form {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} (h : processTransaction benv bout tx index = .ok (state, bout')) :
    ∃ sender msg messageState messageOut, ∃ refund tip : B256,
      transactionMessage benv bout tx index = .ok (sender, msg) ∧
      processMessageCall msg = .ok (messageState, messageOut) ∧
      state = sweepTouchedAccounts benv.stat.rules messageOut.touchedAccounts.toList
        (settleSelfdestructs benv.stat.rules messageOut.accountsToDelete.toList
          ((messageState.addBal sender refund).addBal benv.stat.coinbase tip)) ∧
      bout'.requests = bout.requests := by
  unfold processTransaction at h
  dsimp only at h
  obtain ⟨prelude, hprelude, h⟩ := Except.bind_eq_ok h
  cases hprelude
  obtain ⟨validationSender, hrec, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨intrinsic, floor⟩, hvalid, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨sender, price, hashes, blob⟩, hchecked, h⟩ := Except.bind_eq_ok h
  obtain ⟨debit, hdebit, h⟩ := Except.bind_eq_ok h
  obtain ⟨msg, hprepared, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨messageState, messageOut⟩, hmessage, h⟩ := Except.bind_eq_ok h
  rw [Except.mapError_eq_ok_iff] at hmessage
  obtain ⟨counter, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨bout₂, hbout₂, h⟩ := Except.bind_eq_ok h
  obtain ⟨bout₃, hbout₃, h⟩ := Except.bind_eq_ok h
  cases hbout₂
  cases hbout₃
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  refine ⟨sender, msg, messageState, messageOut, _, _, ?_, hmessage, h.1.symm, ?_⟩
  · unfold transactionMessage
    dsimp only
    simp only [bind, Except.bind]
    rw [hrec]
    dsimp only
    rw [hvalid]
    dsimp only
    rw [show checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx = _ from hchecked]
    dsimp only
    rw [show ((benv.beginTransaction.state.incrNonce sender).subBal sender
      (tx.gas * price + transactionBlobGasFee benv.beginTransaction tx).toB256).toExcept _ = _ from hdebit]
    dsimp only
    rw [show prepareMessage _ (transactionTenvAt benv.beginTransaction tx index sender price intrinsic hashes) tx = _
      from hprepared]
  · rw [← h.2]
    rfl

/-- What the prepared message of a transaction is. -/
private structure PreparedTx (benv : Benv) (tx : Tx) (sender : Adr) (msg : Msg) : Prop where
  caller : msg.caller = sender
  auths : msg.tenv.stat.auths = tx.auths
  routed : RoutedMessage msg
  deletions : msg.inheritedDeletions = .emptyWithCapacity
  stat : msg.benv.stat = benv.beginTransaction.stat
  created : msg.benv.createdAccounts = benv.createdAccounts
  data : msg.data = tx.data ∨ msg.data = []
  debit : ∃ v, (benv.state.incrNonce sender).subBal sender v = some msg.benv.state

private theorem prepareMessage_shape {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h : prepareMessage benv tenv tx = .ok msg) :
    msg.caller = tenv.stat.origin ∧ msg.inheritedDeletions = .emptyWithCapacity := by
  unfold prepareMessage at h
  split at h
  all_goals
    dsimp only at h
    obtain rfl := Except.ok.inj h
    exact ⟨rfl, rfl⟩

private theorem transactionMessage_facts {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {sender : Adr}
    {msg : Msg} (h : transactionMessage benv bout tx index = .ok (sender, msg)) : PreparedTx benv tx sender msg := by
  unfold transactionMessage at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨intrinsic, floor⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨sender', price, hashes, blob⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨debit, hdebit, h⟩ := Except.bind_eq_ok h
  obtain ⟨msg', hprepared, h⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hbenv := prepareMessage_benv hprepared
  have hfields := prepareMessage_fields hprepared
  have hshape := prepareMessage_shape hprepared
  refine ⟨hshape.1, by rw [hfields.1]; rfl, ⟨prepareMessage_callCode hprepared, hfields.2⟩, hshape.2,
    by rw [hbenv], by rw [hbenv]; rfl, prepareMessage_data hprepared,
    (tx.gas * price + transactionBlobGasFee benv.beginTransaction tx).toB256, ?_⟩
  rw [hbenv]
  exact Option.toExcept_eq_ok hdebit

/-- The transaction, read off its roots: the prepared message, the roots of it, and what settlement does to the world.
    -/
private theorem TransactionRoots.spine {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} {sender : Adr} {rs : List Root} (h : TransactionRoots benv bout tx index state bout' sender
        rs) :
    ∃ msg messageState messageOut, ∃ refund tip : B256, PreparedTx benv tx sender msg ∧
      MessageRoots msg messageState messageOut rs ∧
      state = sweepTouchedAccounts benv.stat.rules messageOut.touchedAccounts.toList
        (settleSelfdestructs benv.stat.rules messageOut.accountsToDelete.toList
          ((messageState.addBal sender refund).addBal benv.stat.coinbase tip)) ∧
      bout'.requests = bout.requests := by
  obtain ⟨result, msg₀, state₀, out₀, hm₀, roots⟩ := h
  obtain ⟨sender', msg, state₁, out₁, refund, tip, hm, hmessage, final, requests⟩ := processTransaction_form result
  have same := Except.ok.inj (hm₀.symm.trans hm)
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  have sameOut := Except.ok.inj (roots.1.symm.trans hmessage)
  simp only [Prod.mk.injEq] at sameOut
  obtain ⟨rfl, rfl⟩ := sameOut
  exact ⟨msg₀, state₀, out₀, refund, tip, transactionMessage_facts hm₀, roots, final, requests⟩

/-- **Every successful transaction has its roots.** -/
theorem exists_transactionRoots {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} (h : processTransaction benv bout tx index = .ok (state, bout')) :
    ∃ sender rs, TransactionRoots benv bout tx index state bout' sender rs := by
  obtain ⟨sender, msg, messageState, messageOut, -, -, hm, hmessage, -⟩ := processTransaction_form h
  obtain ⟨rs, roots⟩ := exists_messageRoots hmessage
  exact ⟨sender, rs, h, msg, messageState, messageOut, hm, roots⟩

/-! ## What settlement keeps -/

private theorem debit_getCode {st d : State} {s : Adr} {v : B256} (h : (st.incrNonce s).subBal s v = some d) (x : Adr) :
    d.getCode x = st.getCode x := by
  rw [State.subBal_getCode h]
  unfold State.getCode
  rw [State.incrNonce_get_code]

private theorem debit_getStor {st d : State} {s x : Adr} {v : B256} (h : (st.incrNonce s).subBal s v = some d)
    (hc : (st.getCode x).toList ≠ []) : d.getStor x = st.getStor x := by
  obtain ⟨-, rfl⟩ := State.of_subBal h
  change (((st.incrNonce s).setBal s _).get x).stor = (st.get x).stor
  rw [State.setBal_get_stor, ite_eq_right ?_, State.incrNonce_get_stor, ite_eq_right ?_]
  · rintro ⟨rfl, empty⟩
    exact ne_wa_of_code_size_zero hc empty.1 rfl
  · rintro ⟨rfl, empty⟩
    have zero : (st.get s).code.size = 0 := by
      rw [← State.incrNonce_get_code (adr := s)]
      exact empty.1
    exact ne_wa_of_code_size_zero hc zero rfl

private theorem foldl_clear_get_eq {a : Adr} {addresses : List Adr} (hne : ∀ x ∈ addresses, x ≠ a) (st : State) :
    (addresses.foldl clearAccountPreservingBalance st).get a = st.get a := by
  induction addresses generalizing st with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, ih (fun y hy => hne y (List.mem_cons_of_mem _ hy))]
      exact State.get_set_ne _ (hne x List.mem_cons_self) _

private theorem settleSelfdestructs_get {a : Adr} {addresses : List Adr} (hne : ∀ x ∈ addresses, x ≠ a) (r : ForkRules)
    (st : State) : (settleSelfdestructs r addresses st).get a = st.get a := by
  unfold settleSelfdestructs
  split
  · exact foldl_destroyAccount_get_eq hne
  · exact foldl_clear_get_eq hne st

private theorem settleSelfdestructs_getCode_empty {S : Adr} (addresses : List Adr) (r : ForkRules) {st : State}
    (h : st.getCode S = ByteArray.empty) : (settleSelfdestructs r addresses st).getCode S = ByteArray.empty := by
  unfold settleSelfdestructs
  split
  · exact foldl_destroyAccount_getCode_empty _ h
  · induction addresses generalizing st with
    | nil => exact h
    | cons x xs ih =>
        rw [List.foldl_cons]
        refine ih ?_
        unfold clearAccountPreservingBalance State.getCode
        dsimp only
        by_cases same : x = S
        · subst same
          rw [State.get_set_self]
        · rw [State.get_set_ne _ same]
          exact h

/-! ## The chain, callers and entry of a transaction -/

/-- **The chain of a transaction.** At an account with code that is no delegation and not created in the block, the
frames kept by the transaction's roots run from the storage it found to the storage it left, and the code stays. -/
theorem TransactionRoots.chain {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} {sender : Adr} {rs : List Root} (h : TransactionRoots benv bout tx index state bout' sender
        rs)
    (rules : KeptRules benv.stat.rules) {a : Adr} (hc : (benv.state.getCode a).toList ≠ [])
    (hd : ¬ isValidDelegation (benv.state.getCode a)) (created : a ∉ benv.createdAccounts) :
    KeptChain a (benv.state.getStor a) (rs.flatMap (Root.keptAt a)) (state.getStor a) ∧
      state.getCode a = benv.state.getCode a := by
  obtain ⟨msg, messageState, messageOut, refund, tip, facts, roots, final, -⟩ := TransactionRoots.spine h
  obtain ⟨v, hdebit⟩ := facts.debit
  have hcode := debit_getCode hdebit a
  have hstor := debit_getStor hdebit hc
  have hc' : (msg.benv.state.getCode a).toList ≠ [] := by rw [hcode]; exact hc
  have hd' : ¬ isValidDelegation (msg.benv.state.getCode a) := by rw [hcode]; exact hd
  obtain ⟨chain, messageCode⟩ := roots.chain hc' hd'
  have notDeleted := roots.not_deleted hc' hd' (by rw [facts.deletions]; exact AdrSet.not_mem_empty)
    (by rw [facts.created]; exact created) (by rw [facts.stat]; exact rules.selfdestruct)
  have notList : ∀ x ∈ messageOut.accountsToDelete.toList, x ≠ a :=
    fun x member same => notDeleted (same ▸ Std.HashSet.mem_toList.mp member)
  rw [sweepTouchedAccounts_of_not_touchedSweep rules.noSweep] at final
  have hget := settleSelfdestructs_get notList benv.stat.rules
    ((messageState.addBal sender refund).addBal benv.stat.coinbase tip)
  have messageNonempty : (messageState.getCode a).toList ≠ [] := by rw [messageCode]; exact hc'
  have finalStor : state.getStor a = messageState.getStor a := by
    rw [final]
    unfold State.getStor
    rw [hget]
    change ((messageState.addBal sender refund).addBal benv.stat.coinbase tip).getStor a = _
    rw [addBal_getStor_of_codenonempty (by rw [State.addBal_getCode]; exact messageNonempty),
      addBal_getStor_of_codenonempty messageNonempty]
    rfl
  have finalCode : state.getCode a = messageState.getCode a := by
    rw [final]
    unfold State.getCode
    rw [hget]
    change ((messageState.addBal sender refund).addBal benv.stat.coinbase tip).getCode a = _
    rw [State.addBal_getCode, State.addBal_getCode]
    rfl
  rw [hstor, ← finalStor] at chain
  exact ⟨chain, finalCode.trans (messageCode.trans hcode)⟩

/-- A code-free account stays code-free across a transaction when none of its authorizations recovers to it and no frame
it keeps creates there. -/
theorem TransactionRoots.empty_stays {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} {sender : Adr} {rs : List Root} (h : TransactionRoots benv bout tx index state bout' sender
        rs)
    {S : Adr} (empty : benv.state.getCode S = ByteArray.empty)
    (away : ∀ auth ∈ tx.auths, recoverAuthority auth ≠ .ok S) (avoid : NoCreateAt S rs) :
    state.getCode S = ByteArray.empty := by
  obtain ⟨msg, messageState, messageOut, refund, tip, facts, roots, final, -⟩ := TransactionRoots.spine h
  obtain ⟨v, hdebit⟩ := facts.debit
  have message := roots.empty_stays facts.routed ((debit_getCode hdebit S).trans empty)
    (by rw [facts.auths]; exact away) avoid
  rw [final]
  refine sweepTouchedAccounts_getCode_empty _ _ (settleSelfdestructs_getCode_empty _ _ ?_)
  rw [State.addBal_getCode, State.addBal_getCode]
  exact message

/-- A transaction whose sender is not `S` keeps no frame with caller `S`, at any account. -/
theorem TransactionRoots.caller_ne {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} {sender : Adr} {rs : List Root} (h : TransactionRoots benv bout tx index state bout' sender
        rs)
    {a S : Adr} (notSender : sender ≠ S) (empty : benv.state.getCode S = ByteArray.empty)
    (away : ∀ auth ∈ tx.auths, recoverAuthority auth ≠ .ok S) (avoid : NoCreateAt S rs) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), f.sevm.caller ≠ S := by
  obtain ⟨msg, messageState, messageOut, refund, tip, facts, roots, -, -⟩ := TransactionRoots.spine h
  obtain ⟨v, hdebit⟩ := facts.debit
  exact roots.caller_ne facts.routed ((debit_getCode hdebit S).trans empty) (by rw [facts.auths]; exact away) avoid
    (.inl (by rw [facts.caller]; exact notSender))

/-- Every frame a transaction keeps at `a`, where `a` holds nondelegating code `C`, runs `C` from its start on fresh
machine state, under the block's environment with the transaction's opening state. -/
theorem TransactionRoots.entry_at {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} {sender : Adr} {rs : List Root} (h : TransactionRoots benv bout tx index state bout' sender
        rs)
    {a : Adr} {C : ByteArray} (code : benv.state.getCode a = C) (nonempty : C.toList ≠ [])
    (nondelegating : ¬ isValidDelegation C) (data : tx.data.length < 2 ^ 256) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), Exec.Frame.EntryAt a C benv.beginTransaction.stat f := by
  obtain ⟨msg, messageState, messageOut, refund, tip, facts, roots, -, -⟩ := TransactionRoots.spine h
  obtain ⟨v, hdebit⟩ := facts.debit
  rw [← facts.stat]
  refine roots.entry_at facts.routed ((debit_getCode hdebit a).trans code) nonempty nondelegating ?_
  rcases facts.data with same | same
  · rw [same]; exact data
  · rw [same]; decide

/-! ## The calldata a transaction can have -/

/-- Four gas per byte is at most the calldata cost, when a nonzero byte costs at least four. -/
private theorem length_mul4_le_dataCost {n : Nat} (hn : 4 ≤ n) (l : Bytes) :
    l.length * 4 ≤ l.foldl (fun acc x => acc + (if x = 0 then standardCallDataTokenCost else n)) 0 := by
  have aux : ∀ (d : Nat) (l : Bytes), l.length * 4 + d ≤
      l.foldl (fun acc x => acc + (if x = 0 then standardCallDataTokenCost else n)) d := by
    intro d l
    induction l generalizing d with
    | nil => exact Nat.le_of_eq (by simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, List.foldl_nil])
    | cons x xs ih =>
        have h := ih (d + if x = 0 then standardCallDataTokenCost else n)
        have step : 4 ≤ if x = 0 then standardCallDataTokenCost else n := by
          split
          · exact Nat.le_refl _
          · exact hn
        simp only [List.length_cons, List.foldl_cons]
        omega
  exact aux 0 l

/-- On either lane the intrinsic cost holds the calldata cost, so four gas per byte. -/
theorem length_mul4_le_intrinsic {rules : ForkRules} (hn : 4 ≤ rules.txr.dataNonZero) (tx : Tx) (sender : Adr) :
    tx.data.length * 4 ≤ (calculateIntrinsicCost rules tx sender).1 := by
  have h := length_mul4_le_dataCost hn tx.data
  simp only [calculateIntrinsicCost]
  omega

/-- On either lane, a validated transaction's gas covers its intrinsic cost. -/
theorem validated_intrinsic_le_gas_lanes {rules : ForkRules} {tx : Tx} {sender : Adr} {p : Nat × Nat}
    (h : validateTransaction rules tx sender = .ok p) : (calculateIntrinsicCost rules tx sender).1 ≤ tx.gas := by
  cases hsg : rules.stateGas with
  | none => exact validated_intrinsic_le_gas hsg h
  | some state =>
      simp only [validateTransaction, hsg] at h
      by_cases hn : tx.nonce = UInt64.max
      · rw [if_pos hn] at h
        obtain ⟨_, hcontra, -⟩ := Except.bind_eq_ok h
        cases hcontra
      rw [if_neg hn] at h
      obtain ⟨_, -, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, -, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, -, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, -, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, -, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, -, h⟩ := Except.bind_eq_ok h
      by_cases hc : (calculateIntrinsicCost rules tx sender).1 > tx.gas
      · rw [if_pos hc] at h
        obtain ⟨_, hcontra, -⟩ := Except.bind_eq_ok h
        cases hcontra
      · exact Nat.le_of_not_gt hc

/-- On either lane, a checked transaction's gas fits in the block gas limit. -/
theorem checked_gas_le_blockGasLimit {benv : Benv} {bout : BlockOutput} {tx : Tx} {q : Adr × Nat × List B256 × Nat}
    (h : checkTransaction benv bout tx = .ok q) : tx.gas ≤ benv.stat.blockGasLimit := by
  cases hsg : benv.stat.rules.stateGas with
  | none => exact tx_gas_le_blockGasLimit_of_checked hsg h
  | some state =>
      simp only [checkTransaction] at h
      obtain ⟨_, hlim, -⟩ := Except.bind_eq_ok h
      rw [Except.mapError_eq_ok_iff] at hlim
      simp only [checkTransactionGasLimits, hsg] at hlim
      by_cases hc : tx.gas > benv.stat.blockGasLimit - bout.blockStateGasUsed
      · split at hlim
        · cases hlim
        · cases hlim
      · omega

/-- **A transaction's calldata is word-sized**, from what `processTransaction` checked: four gas per byte, gas within
the block's limit, the limit below `2 ^ 63`. -/
theorem TransactionRoots.data_fits {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} {sender : Adr} {rs : List Root} (h : TransactionRoots benv bout tx index state bout' sender
        rs)
    (rules : KeptRules benv.stat.rules) (limit : benv.stat.blockGasLimit < 2 ^ 63) : tx.data.length < 2 ^ 256 := by
  obtain ⟨-, msg, -, -, hmsg, -⟩ := h
  unfold transactionMessage at hmsg
  obtain ⟨validationSender, _, hmsg⟩ := Except.bind_eq_ok hmsg
  obtain ⟨_, hvalid, hmsg⟩ := Except.bind_eq_ok hmsg
  obtain ⟨_, hchecked, -⟩ := Except.bind_eq_ok hmsg
  have hv := validated_intrinsic_le_gas_lanes (Except.mapError_eq_ok_iff.mp hvalid)
  have hg : tx.gas ≤ benv.stat.blockGasLimit := checked_gas_le_blockGasLimit hchecked
  have hd := length_mul4_le_intrinsic (rules := benv.beginTransaction.stat.rules) rules.dataCost tx validationSender
  have big : (2 : Nat) ^ 63 < 2 ^ 256 := by decide
  omega

/-! ## The transaction list -/

/-- No listed transaction was sent by `S`. -/
def NoSenderAt (S : Adr) (txs : List (Adr × Tx)) : Prop := ∀ p ∈ txs, p.1 ≠ S

/-- No authorization of a listed transaction recovers to `S`, whether or not its message ran. -/
def NoAuthorityAt (S : Adr) (txs : List (Adr × Tx)) : Prop :=
  ∀ p ∈ txs, ∀ auth ∈ p.2.auths, recoverAuthority auth ≠ .ok S

/-- The calldata of every listed transaction is word-sized. -/
def DataFits (txs : List (Adr × Tx)) : Prop := ∀ p ∈ txs, p.2.data.length < 2 ^ 256

/-- The roots along `applyTransactions`, with each transaction's sender and the transaction. -/
inductive TransactionsRoots : List (Nat × Tx) → Benv → BlockOutput → Benv → BlockOutput → List (Adr × Tx) → List Root →
    Prop where
  | nil (benv : Benv) (bout : BlockOutput) : TransactionsRoots [] benv bout benv bout [] []
  | cons {i : Nat} {tx : Tx} {rest : List (Nat × Tx)} {benv final : Benv} {bout bout' finalOut : BlockOutput}
      {st : State} {sender : Adr} {rs later : List Root} {txs : List (Adr × Tx)} :
      TransactionRoots benv bout tx i st bout' sender rs →
      TransactionsRoots rest (benv.withState st) bout' final finalOut txs later →
      TransactionsRoots ((i, tx) :: rest) benv bout final finalOut ((sender, tx) :: txs) (rs ++ later)

/-- **Every successful transaction list has its roots.** -/
theorem exists_transactionsRoots {txis : List (Nat × Tx)} {benv final : Benv} {bout finalOut : BlockOutput}
    (h : applyTransactions txis benv bout = .ok (final, finalOut)) :
    ∃ txs rs, TransactionsRoots txis benv bout final finalOut txs rs := by
  induction txis generalizing benv bout with
  | nil =>
      unfold applyTransactions at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], [], .nil _ _⟩
  | cons txi rest ih =>
      obtain ⟨i, tx⟩ := txi
      unfold applyTransactions at h
      obtain ⟨⟨st, bout'⟩, hq, h⟩ := Except.bind_eq_ok h
      obtain ⟨sender, rs, head⟩ := exists_transactionRoots hq
      obtain ⟨txs, later, tail⟩ := ih h
      exact ⟨_, _, .cons head tail⟩

theorem NoCreateAt.left {S : Adr} {xs ys : List Root} (h : NoCreateAt S (xs ++ ys)) : NoCreateAt S xs :=
  fun f hf => h f (by unfold keptAll at hf ⊢; rw [List.flatMap_append]; exact List.mem_append_left _ hf)

theorem NoCreateAt.right {S : Adr} {xs ys : List Root} (h : NoCreateAt S (xs ++ ys)) : NoCreateAt S ys :=
  fun f hf => h f (by unfold keptAll at hf ⊢; rw [List.flatMap_append]; exact List.mem_append_right _ hf)

namespace TransactionsRoots

variable {txis : List (Nat × Tx)} {benv final : Benv} {bout finalOut : BlockOutput} {txs : List (Adr × Tx)}
  {rs : List Root}

/-- The roots determine the list's run. -/
theorem run (h : TransactionsRoots txis benv bout final finalOut txs rs) :
    applyTransactions txis benv bout = .ok (final, finalOut) := by
  induction h with
  | nil benv bout => rfl
  | cons head tail ih =>
      unfold applyTransactions
      rw [head.1]
      exact ih

/-- The list leaves the environment, but for its state. -/
theorem final_eq (h : TransactionsRoots txis benv bout final finalOut txs rs) : final = benv.withState final.state := by
  induction h with
  | nil benv bout => rfl
  | cons head tail ih => exact ih

/-- The list leaves the request bytes. -/
theorem requests_eq (h : TransactionsRoots txis benv bout final finalOut txs rs) : finalOut.requests = bout.requests
    := by
  induction h with
  | nil benv bout => rfl
  | @cons i tx rest benv final bout bout' finalOut st sender rs later txs head tail ih =>
      obtain ⟨-, -, -, -, -, -, -, -, requests⟩ := TransactionRoots.spine head
      exact ih.trans requests

/-- **The chain of a transaction list.** -/
theorem chain (h : TransactionsRoots txis benv bout final finalOut txs rs) (rules : KeptRules benv.stat.rules) {a : Adr}
    (hc : (benv.state.getCode a).toList ≠ []) (hd : ¬ isValidDelegation (benv.state.getCode a))
    (created : a ∉ benv.createdAccounts) :
    KeptChain a (benv.state.getStor a) (rs.flatMap (Root.keptAt a)) (final.state.getStor a) ∧
      final.state.getCode a = benv.state.getCode a := by
  induction h with
  | nil benv bout => exact ⟨.nil _, rfl⟩
  | cons head tail ih =>
      obtain ⟨chain₁, code₁⟩ := head.chain rules hc hd created
      obtain ⟨chain₂, code₂⟩ := ih rules (by simpa only [Benv.withState, code₁] using hc)
        (by simpa only [Benv.withState, code₁] using hd) created
      rw [List.flatMap_append]
      exact ⟨chain₁.append chain₂, code₂.trans code₁⟩

/-- A code-free account stays code-free across the list. -/
theorem empty_stays (h : TransactionsRoots txis benv bout final finalOut txs rs) {S : Adr}
    (empty : benv.state.getCode S = ByteArray.empty) (authorities : NoAuthorityAt S txs) (avoid : NoCreateAt S rs) :
    final.state.getCode S = ByteArray.empty := by
  induction h with
  | nil benv bout => exact empty
  | cons head tail ih =>
      refine ih (head.empty_stays empty (authorities _ List.mem_cons_self) (NoCreateAt.left avoid))
        (fun p hp => authorities p (List.mem_cons_of_mem _ hp)) (NoCreateAt.right avoid)

/-- With no sender and no authority at `S`, no frame the list keeps at any account has caller `S`. -/
theorem caller_ne (h : TransactionsRoots txis benv bout final finalOut txs rs) {a S : Adr}
    (empty : benv.state.getCode S = ByteArray.empty) (senders : NoSenderAt S txs) (authorities : NoAuthorityAt S txs)
    (avoid : NoCreateAt S rs) : ∀ f ∈ rs.flatMap (Root.keptAt a), f.sevm.caller ≠ S := by
  induction h with
  | nil benv bout =>
      intro f hf
      cases hf
  | cons head tail ih =>
      intro f hf
      rw [List.flatMap_append, List.mem_append] at hf
      rcases hf with hf | hf
      · exact head.caller_ne (senders _ List.mem_cons_self) empty (authorities _ List.mem_cons_self)
          (NoCreateAt.left avoid) f hf
      · exact ih (head.empty_stays empty (authorities _ List.mem_cons_self) (NoCreateAt.left avoid))
          (fun p hp => senders p (List.mem_cons_of_mem _ hp)) (fun p hp => authorities p (List.mem_cons_of_mem _ hp))
          (NoCreateAt.right avoid) f hf

/-- Every frame the list keeps at `a`, where `a` holds nondelegating code `C`, runs `C` from its start on fresh machine
state, under the block's environment with its transaction's opening state. -/
theorem entry_in (h : TransactionsRoots txis benv bout final finalOut txs rs) (rules : KeptRules benv.stat.rules) {a :
    Adr}
    {C : ByteArray} (code : benv.state.getCode a = C) (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (created : a ∉ benv.createdAccounts) (data : DataFits txs) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), Exec.Frame.EntryIn a C benv.stat f := by
  induction h with
  | nil benv bout =>
      intro f hf
      cases hf
  | cons head tail ih =>
      intro f hf
      rw [List.flatMap_append, List.mem_append] at hf
      rcases hf with hf | hf
      · exact ⟨_, head.entry_at code nonempty nondelegating (data _ List.mem_cons_self) f hf⟩
      · have hc : (_ : State).getCode a = _ := (head.chain rules (by rw [code]; exact nonempty)
          (by rw [code]; exact nondelegating) created).2
        exact ih rules (hc.trans code) created (fun p hp => data p (List.mem_cons_of_mem _ hp)) f hf

/-- **The calldata of every listed transaction is word-sized**, under a header's gas limit. -/
theorem data_fits (h : TransactionsRoots txis benv bout final finalOut txs rs) (rules : KeptRules benv.stat.rules)
    (limit : benv.stat.blockGasLimit < 2 ^ 63) : DataFits txs := by
  induction h with
  | nil benv bout => exact fun _ hp => absurd hp List.not_mem_nil
  | cons head tail ih =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact head.data_fits rules limit
      · exact ih rules limit p hp

end TransactionsRoots

/-! ## System messages -/

section System

variable {benv : Benv} {target : Adr} {data : Bytes} {post : State} {out : MsgCallOutput} {rs : List Root}

private theorem systemMessage_routed : RoutedMessage (systemTransactionMessage benv target data) :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun h => by cases h⟩

/-- The chain across one system message: the world it runs on is the stage's. -/
private theorem systemMessage_chain (h : MessageRoots (systemTransactionMessage benv target data) post out rs) {a : Adr}
    (hc : (benv.state.getCode a).toList ≠ []) (hd : ¬ isValidDelegation (benv.state.getCode a)) :
    KeptChain a (benv.state.getStor a) (rs.flatMap (Root.keptAt a)) (post.getStor a) ∧
      post.getCode a = benv.state.getCode a :=
  MessageRoots.chain h hc hd

private theorem systemMessage_empty (h : MessageRoots (systemTransactionMessage benv target data) post out rs) {S : Adr}
    (empty : benv.state.getCode S = ByteArray.empty) (avoid : NoCreateAt S rs) : post.getCode S = ByteArray.empty :=
  h.empty_stays systemMessage_routed empty (fun _ hauth => by cases hauth) avoid

private theorem systemMessage_caller (h : MessageRoots (systemTransactionMessage benv target data) post out rs) {a S :
    Adr}
    (empty : benv.state.getCode S = ByteArray.empty) (avoid : NoCreateAt S rs) (elsewhere : target ≠ a) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), f.sevm.caller ≠ S :=
  h.caller_ne systemMessage_routed empty (fun _ hauth => by cases hauth) avoid (.inr elsewhere)

private theorem systemMessage_entry (h : MessageRoots (systemTransactionMessage benv target data) post out rs) {a : Adr}
    {C : ByteArray} (code : benv.state.getCode a = C) (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (fits : data.length < 2 ^ 256) : ∀ f ∈ rs.flatMap (Root.keptAt a), Exec.Frame.EntryIn a C benv.stat f :=
  fun f hf => ⟨_, h.entry_at systemMessage_routed code nonempty nondelegating fits f hf⟩

end System

/-! ## The request fold -/

/-- One checked request call: its contract's type byte and address, its post-state and output, and its roots. -/
structure RequestStep where
  type : UInt8
  target : Adr
  post : State
  output : MsgCallOutput
  roots : List Root

/-- The bytes one request call contributes to the block: its type byte first, and only when its return data is
    nonempty. -/
def RequestStep.bytes (s : RequestStep) : List Bytes :=
  if s.output.returnData.length > 0 then [[s.type] ++ s.output.returnData] else []

/-- What one request call does to the block access list; it carries no root. -/
def requestBal (idx : Nat) (benv : Benv) (bal : BalBuilder) (target : Adr) (post : State) (out : MsgCallOutput) :
    BalBuilder :=
  match benv.stat.rules.bal with
  | none => bal
  | some _ => bal.incorporate idx benv.state post (target :: out.accountReads.toList) out.storageReads.toList
      out.storageWrites.toList

/-- The roots along `runRequestContracts idx`, one step per contract. -/
inductive RequestRoots (idx : Nat) : List (UInt8 × Adr) → Benv → List Bytes → BalBuilder → State → List Bytes →
    BalBuilder → List RequestStep → Prop where
  | nil (benv : Benv) (acc : List Bytes) (bal : BalBuilder) : RequestRoots idx [] benv acc bal benv.state acc bal []
  | cons {type : UInt8} {target : Adr} {rest : List (UInt8 × Adr)} {benv : Benv} {acc acc' : List Bytes}
      {bal bal' : BalBuilder} {post final : State} {out : MsgCallOutput} {rs : List Root} {steps : List RequestStep} :
      processCheckedSystemTransaction benv target [] = .ok (post, out) →
      MessageRoots (systemTransactionMessage benv target []) post out rs →
      RequestRoots idx rest (benv.withState post) (acc ++ (RequestStep.mk type target post out rs).bytes)
        (requestBal idx benv bal target post out) final acc' bal' steps →
      RequestRoots idx ((type, target) :: rest) benv acc bal final acc' bal' (⟨type, target, post, out, rs⟩ :: steps)

/-- All the roots of some request calls, in call order. -/
def requestRootsOf (steps : List RequestStep) : List Root := steps.flatMap RequestStep.roots

/-- **Every successful request fold has its roots.** -/
theorem exists_requestRoots {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv} {acc acc' : List Bytes}
    {bal bal' : BalBuilder} {final : State} (h : runRequestContracts idx contracts benv acc bal = .ok (final, acc',
        bal')) :
    ∃ steps, RequestRoots idx contracts benv acc bal final acc' bal' steps := by
  induction contracts generalizing benv acc bal with
  | nil =>
      unfold runRequestContracts at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], .nil _ _ _⟩
  | cons contract rest ih =>
      obtain ⟨type, target⟩ := contract
      unfold runRequestContracts at h
      obtain ⟨⟨post, out⟩, hcall, h⟩ := Except.bind_eq_ok h
      obtain ⟨-, rs, roots⟩ := exists_systemRoots hcall
      have hacc : (if out.returnData.length > 0 then acc ++ [[type] ++ out.returnData] else acc) =
          acc ++ (RequestStep.mk type target post out rs).bytes := by
        unfold RequestStep.bytes
        dsimp only
        split <;> simp only [List.append_nil]
      dsimp only at h
      rw [hacc] at h
      obtain ⟨steps, tail⟩ := ih h
      exact ⟨_, .cons hcall roots tail⟩

namespace RequestRoots

variable {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv} {acc acc' : List Bytes} {bal bal' : BalBuilder}
  {final : State} {steps : List RequestStep}

/-- The roots determine the fold's run. -/
theorem run (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) :
    runRequestContracts idx contracts benv acc bal = .ok (final, acc', bal') := by
  induction h with
  | nil benv acc bal => rfl
  | @cons type target rest benv acc acc' bal bal' post final out rs steps hcall roots tail ih =>
      unfold runRequestContracts
      rw [hcall]
      have hacc : (if out.returnData.length > 0 then acc ++ [[type] ++ out.returnData] else acc) =
          acc ++ (RequestStep.mk type target post out rs).bytes := by
        unfold RequestStep.bytes
        dsimp only
        split <;> simp only [List.append_nil]
      change runRequestContracts idx rest (benv.withState post)
        (if out.returnData.length > 0 then acc ++ [[type] ++ out.returnData] else acc)
        (requestBal idx benv bal target post out) = _
      rw [hacc]
      exact ih

/-- **The request bytes.** The fold appends each call's bytes, in call order. -/
theorem acc_eq (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) :
    acc' = acc ++ steps.flatMap RequestStep.bytes := by
  induction h with
  | nil benv acc bal => simp only [List.flatMap_nil, List.append_nil]
  | cons hcall roots tail ih =>
      rw [ih, List.flatMap_cons, List.append_assoc]

/-- The fold's contracts, in call order, are its steps' types and targets. -/
theorem contracts_eq (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) :
    contracts = steps.map (fun s => (s.type, s.target)) := by
  induction h with
  | nil benv acc bal => rfl
  | cons hcall roots tail ih =>
      rw [ih]
      rfl

/-- Each step is a checked system call at its target, on the block's environment but for the state. -/
theorem step_roots (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) :
    ∀ s ∈ steps, ∃ b : Benv, b.stat = benv.stat ∧ processCheckedSystemTransaction b s.target [] = .ok (s.post,
        s.output) ∧
      MessageRoots (systemTransactionMessage b s.target []) s.post s.output s.roots := by
  induction h with
  | nil benv acc bal =>
      intro s hs
      cases hs
  | cons hcall roots tail ih =>
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨_, rfl, hcall, roots⟩
      · exact ih s hs

/-- **Telling a request step apart.** Every root of a step runs at the step's target for the system caller. -/
theorem root_routing (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) :
    ∀ s ∈ steps, ∀ r ∈ s.roots, r.evm.sta.currentTarget = s.target ∧ r.evm.sta.caller = systemAddress := by
  intro s hs r hr
  obtain ⟨b, -, -, roots⟩ := h.step_roots s hs
  obtain ⟨hcaller, htarget, -, -⟩ := roots.entry_routing hr
  exact ⟨htarget, hcaller⟩

/-- **The chain of the request fold.** -/
theorem chain (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) {a : Adr}
    (hc : (benv.state.getCode a).toList ≠ []) (hd : ¬ isValidDelegation (benv.state.getCode a)) :
    KeptChain a (benv.state.getStor a) ((requestRootsOf steps).flatMap (Root.keptAt a)) (final.getStor a) ∧
      final.getCode a = benv.state.getCode a := by
  induction h with
  | nil benv acc bal => exact ⟨.nil _, rfl⟩
  | cons hcall roots tail ih =>
      obtain ⟨chain₁, code₁⟩ := systemMessage_chain roots hc hd
      obtain ⟨chain₂, code₂⟩ := ih (by simpa only [Benv.withState, code₁] using hc)
        (by simpa only [Benv.withState, code₁] using hd)
      unfold requestRootsOf at chain₂ ⊢
      rw [List.flatMap_cons, List.flatMap_append]
      exact ⟨chain₁.append chain₂, code₂.trans code₁⟩

/-- A code-free account stays code-free across the fold. -/
theorem empty_stays (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) {S : Adr}
    (empty : benv.state.getCode S = ByteArray.empty) (avoid : NoCreateAt S (requestRootsOf steps)) :
    final.getCode S = ByteArray.empty := by
  induction h with
  | nil benv acc bal => exact empty
  | cons hcall roots tail ih =>
      have parts : NoCreateAt S (_ ++ requestRootsOf _) := avoid
      exact ih (systemMessage_empty roots empty (NoCreateAt.left parts)) (NoCreateAt.right parts)

/-- A request step not at `a` keeps no frame with caller `S` at `a`, the system caller or not. -/
theorem caller_ne (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) {a S : Adr}
    (empty : benv.state.getCode S = ByteArray.empty) (avoid : NoCreateAt S (requestRootsOf steps)) :
    ∀ s ∈ steps, s.target ≠ a → ∀ f ∈ s.roots.flatMap (Root.keptAt a), f.sevm.caller ≠ S := by
  induction h with
  | nil benv acc bal =>
      intro s hs
      cases hs
  | cons hcall roots tail ih =>
      have parts : NoCreateAt S (_ ++ requestRootsOf _) := avoid
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact fun elsewhere => systemMessage_caller roots empty (NoCreateAt.left parts) elsewhere
      · exact ih (systemMessage_empty roots empty (NoCreateAt.left parts)) (NoCreateAt.right parts) s hs

/-- Every frame the fold keeps at `a`, where `a` holds nondelegating code `C`, runs `C` from its start on fresh machine
state, under the block's environment with its call's opening state. -/
theorem entry_in (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) {a : Adr} {C : ByteArray}
    (code : benv.state.getCode a = C) (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C) :
    ∀ f ∈ (requestRootsOf steps).flatMap (Root.keptAt a), Exec.Frame.EntryIn a C benv.stat f := by
  induction h with
  | nil benv acc bal =>
      intro f hf
      cases hf
  | cons hcall roots tail ih =>
      intro f hf
      unfold requestRootsOf at hf ih
      rw [List.flatMap_cons, List.flatMap_append, List.mem_append] at hf
      rcases hf with hf | hf
      · exact systemMessage_entry roots code nonempty nondelegating (by decide) f hf
      · have hc : (_ : State).getCode a = _ := (systemMessage_chain roots (by rw [code]; exact nonempty)
          (by rw [code]; exact nondelegating)).2
        exact ih (hc.trans code) f hf

end RequestRoots

/-! ## The body -/

/-- The bytes the history call passes: the last block hash, the only data that call can succeed on. -/
def historyData (benv : Benv) : Bytes :=
  match benv.stat.blockHashes.getLast? with
  | some hash => hash.toBytes
  | none => []

/-- One pre-execution system call: enabled, `rs` are the roots of its message; disabled, nothing happens and no root. -/
def PreCall (on : Bool) (benv : Benv) (target : Adr) (data : Bytes) (st : State) (rs : List Root) : Prop :=
  if on = true then ∃ out, MessageRoots (systemTransactionMessage benv target data) st out rs
  else st = benv.state ∧ rs = []

/-- The beacon then history calls of a body, ending on `st` and `bal` with the roots `rs`. -/
def PreRoots (benv : Benv) (st : State) (bal : BalBuilder) (rs : List Root) : Prop :=
  ∃ beacon beaconBal beaconRoots historyRoots,
    beaconRootsCall benv.stat.rules benv = .ok (beacon, beaconBal) ∧
    PreCall benv.stat.rules.sys.beaconRoots benv beaconRootsAddress benv.stat.parentBeaconBlockRoot.toBytes beacon
      beaconRoots ∧
    historyStorageCall benv.stat.rules (benv.withState beacon) beaconBal = .ok (st, bal) ∧
    PreCall benv.stat.rules.sys.historyStorage (benv.withState beacon) historyStorageAddress (historyData benv) st
      historyRoots ∧
    rs = beaconRoots ++ historyRoots

/-- The requests a deposit parse seeds the fold with: the deposit type byte first, and only when nonempty. -/
def seedRequests (bout : BlockOutput) (deposits : Bytes) : List Bytes :=
  if deposits.length > 0 then bout.requests ++ [depositRequestType ++ deposits] else bout.requests

/-- The request pass: enabled, the deposit parse then the fold's steps build `out`; disabled, nothing happens. -/
def RequestPass (benv : Benv) (bout : BlockOutput) (st : State) (out : BlockOutput) (steps : List RequestStep) : Prop :=
  if benv.stat.rules.header.requestsHash = true then
    ∃ deposits acc bal, parseDepositRequests bout = .ok deposits ∧
      RequestRoots (bout.receiptKeys.length + 1) benv.stat.rules.requests benv (seedRequests bout deposits) bout.bal
        st acc bal steps ∧
      out = {bout with requests := acc, bal := bal}
  else st = benv.state ∧ out = bout ∧ steps = []

/-- The stages of one body: what the pre-execution calls and the transactions end on, with the roots of each stage. -/
structure BodyRun where
  preState : State
  preBal : BalBuilder
  preRoots : List Root
  txEnv : Benv
  txOut : BlockOutput
  senders : List (Adr × Tx)
  txRoots : List Root
  requests : List RequestStep

/-- All the roots of a body, in execution order. -/
def BodyRun.roots (run : BodyRun) : List Root := run.preRoots ++ run.txRoots ++ requestRootsOf run.requests

/-- The frames at `a` a body keeps outside its request fold. -/
def BodyRun.outsideRequests (a : Adr) (run : BodyRun) : List Exec.Frame :=
  (run.preRoots ++ run.txRoots).flatMap (Root.keptAt a)

/-- `applyBody` returned `(state, bout)`, along the stages of `run`. Withdrawals and the block access list carry no
root. -/
structure BodyRoots (benv : Benv) (txs : List (Bytes ⊕ Tx)) (ommers : List Header) (wds : List Withdrawal) (state :
    State)
    (bout : BlockOutput) (run : BodyRun) : Prop where
  applied : applyBody benv txs ommers wds = .ok (state, bout)
  pre : PreRoots benv run.preState run.preBal run.preRoots
  transactions : ∃ decoded, txs.mapM (decodeTx benv.stat.rules) = .ok decoded ∧
    TransactionsRoots decoded.putIndex (benv.withState run.preState) {BlockOutput.init with bal := run.preBal} run.txEnv
      run.txOut run.senders run.txRoots
  requests : ∃ st out, RequestPass (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut wds).1)
    (withdrawalsPass benv.stat.rules run.txEnv run.txOut wds).2 st out run.requests

/-! ### The pre-execution calls -/

theorem exists_beaconRoots {benv : Benv} {st : State} {bal : BalBuilder}
    (h : beaconRootsCall benv.stat.rules benv = .ok (st, bal)) :
    ∃ rs, PreCall benv.stat.rules.sys.beaconRoots benv beaconRootsAddress benv.stat.parentBeaconBlockRoot.toBytes st
        rs := by
  unfold beaconRootsCall at h
  unfold PreCall
  by_cases on : benv.stat.rules.sys.beaconRoots = true
  · rw [ite_eq_left on] at h
    simp only [ite_eq_left on]
    obtain ⟨⟨st', out⟩, hunchecked, h⟩ := Except.bind_eq_ok h
    rw [Except.mapError_eq_ok_iff] at hunchecked
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨rs, roots⟩ := exists_messageRoots (msg := systemTransactionMessage benv beaconRootsAddress _) hunchecked
    exact ⟨rs, out, roots⟩
  · rw [ite_eq_right on] at h
    simp only [ite_eq_right on]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨[], h.1.symm, rfl⟩

theorem exists_historyRoots {benv : Benv} {st : State} {bal bal' : BalBuilder} (data : Bytes)
    (hdata : historyData benv = data)
    (h : historyStorageCall benv.stat.rules benv bal = .ok (st, bal')) :
    ∃ rs, PreCall benv.stat.rules.sys.historyStorage benv historyStorageAddress data st rs := by
  unfold historyStorageCall at h
  unfold PreCall
  by_cases on : benv.stat.rules.sys.historyStorage = true
  · rw [ite_eq_left on] at h
    simp only [ite_eq_left on]
    obtain ⟨last, hlast, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨st', out⟩, hunchecked, h⟩ := Except.bind_eq_ok h
    rw [Except.mapError_eq_ok_iff] at hunchecked
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have some := Option.toExcept_eq_ok hlast
    have same : data = last.toBytes := by
      rw [← hdata]
      unfold historyData
      rw [some]
    subst same
    obtain ⟨rs, roots⟩ := exists_messageRoots (msg := systemTransactionMessage benv historyStorageAddress _) hunchecked
    exact ⟨rs, out, roots⟩
  · rw [ite_eq_right on] at h
    simp only [ite_eq_right on]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨[], h.1.symm, rfl⟩

namespace PreCall

variable {on : Bool} {benv : Benv} {target : Adr} {data : Bytes} {st : State} {rs : List Root}

theorem chain (h : PreCall on benv target data st rs) {a : Adr} (hc : (benv.state.getCode a).toList ≠ [])
    (hd : ¬ isValidDelegation (benv.state.getCode a)) :
    KeptChain a (benv.state.getStor a) (rs.flatMap (Root.keptAt a)) (st.getStor a) ∧
      st.getCode a = benv.state.getCode a := by
  unfold PreCall at h
  split at h
  · obtain ⟨out, roots⟩ := h
    exact systemMessage_chain roots hc hd
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨.nil _, rfl⟩

theorem empty_stays (h : PreCall on benv target data st rs) {S : Adr} (empty : benv.state.getCode S = ByteArray.empty)
    (avoid : NoCreateAt S rs) : st.getCode S = ByteArray.empty := by
  unfold PreCall at h
  split at h
  · obtain ⟨out, roots⟩ := h
    exact systemMessage_empty roots empty avoid
  · obtain ⟨rfl, rfl⟩ := h
    exact empty

theorem caller_ne (h : PreCall on benv target data st rs) {a S : Adr} (empty : benv.state.getCode S = ByteArray.empty)
    (avoid : NoCreateAt S rs) (elsewhere : target ≠ a) : ∀ f ∈ rs.flatMap (Root.keptAt a), f.sevm.caller ≠ S := by
  unfold PreCall at h
  split at h
  · obtain ⟨out, roots⟩ := h
    exact systemMessage_caller roots empty avoid elsewhere
  · obtain ⟨rfl, rfl⟩ := h
    intro f hf
    cases hf

theorem entry_in (h : PreCall on benv target data st rs) {a : Adr} {C : ByteArray} (code : benv.state.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C) (fits : data.length < 2 ^ 256) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), Exec.Frame.EntryIn a C benv.stat f := by
  unfold PreCall at h
  split at h
  · obtain ⟨out, roots⟩ := h
    exact systemMessage_entry roots code nonempty nondelegating fits
  · obtain ⟨rfl, rfl⟩ := h
    intro f hf
    cases hf

end PreCall

private theorem historyData_fits (benv : Benv) : (historyData benv).length < 2 ^ 256 := by
  unfold historyData
  split
  · rw [B256.length_toBytes]
    decide
  · decide

namespace PreRoots

variable {benv : Benv} {st : State} {bal : BalBuilder} {rs : List Root}

theorem chain (h : PreRoots benv st bal rs) {a : Adr} (hc : (benv.state.getCode a).toList ≠ [])
    (hd : ¬ isValidDelegation (benv.state.getCode a)) :
    KeptChain a (benv.state.getStor a) (rs.flatMap (Root.keptAt a)) (st.getStor a) ∧
      st.getCode a = benv.state.getCode a := by
  obtain ⟨beacon, -, beaconRoots, historyRoots, -, first, -, second, rfl⟩ := h
  obtain ⟨chain₁, code₁⟩ := first.chain hc hd
  obtain ⟨chain₂, code₂⟩ := second.chain (a := a) (by simpa only [Benv.withState, code₁] using hc)
    (by simpa only [Benv.withState, code₁] using hd)
  rw [List.flatMap_append]
  exact ⟨chain₁.append chain₂, code₂.trans code₁⟩

theorem empty_stays (h : PreRoots benv st bal rs) {S : Adr} (empty : benv.state.getCode S = ByteArray.empty)
    (avoid : NoCreateAt S rs) : st.getCode S = ByteArray.empty := by
  obtain ⟨beacon, -, beaconRoots, historyRoots, -, first, -, second, rfl⟩ := h
  exact second.empty_stays (first.empty_stays empty avoid.left) avoid.right

theorem caller_ne (h : PreRoots benv st bal rs) {a S : Adr} (empty : benv.state.getCode S = ByteArray.empty)
    (avoid : NoCreateAt S rs) (notBeacon : beaconRootsAddress ≠ a) (notHistory : historyStorageAddress ≠ a) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), f.sevm.caller ≠ S := by
  obtain ⟨beacon, -, beaconRoots, historyRoots, -, first, -, second, rfl⟩ := h
  intro f hf
  rw [List.flatMap_append, List.mem_append] at hf
  rcases hf with hf | hf
  · exact first.caller_ne empty avoid.left notBeacon f hf
  · exact second.caller_ne (first.empty_stays empty avoid.left) avoid.right notHistory f hf

theorem entry_in (h : PreRoots benv st bal rs) {a : Adr} {C : ByteArray} (code : benv.state.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), Exec.Frame.EntryIn a C benv.stat f := by
  obtain ⟨beacon, -, beaconRoots, historyRoots, -, first, -, second, rfl⟩ := h
  intro f hf
  rw [List.flatMap_append, List.mem_append] at hf
  rcases hf with hf | hf
  · exact first.entry_in code nonempty nondelegating (by rw [B256.length_toBytes]; decide) f hf
  · have code₁ := (first.chain (by rw [code]; exact nonempty) (by rw [code]; exact nondelegating)).2
    exact second.entry_in (code₁.trans code) nonempty nondelegating (historyData_fits benv) f hf

end PreRoots

/-! ### Withdrawals -/

private theorem withdrawalsPass_getCode (rules : ForkRules) (benv : Benv) (bout : BlockOutput) (wds : List Withdrawal)
    (x : Adr) : (withdrawalsPass rules benv bout wds).1.getCode x = benv.state.getCode x := by
  unfold withdrawalsPass
  split
  · exact processWithdrawalsState_getCode _ _ _
  · rfl

private theorem processWithdrawalsState_getStor {st : State} {x : Adr} (wds : List Withdrawal)
    (hc : (st.getCode x).toList ≠ []) : (processWithdrawalsState st wds).getStor x = st.getStor x := by
  unfold processWithdrawalsState
  induction wds generalizing st with
  | nil => rfl
  | cons wd wds ih =>
      rw [List.foldl_cons, ih (by rw [State.addBal_getCode]; exact hc)]
      exact addBal_getStor_of_codenonempty hc

private theorem withdrawalsPass_getStor (rules : ForkRules) (benv : Benv) (bout : BlockOutput) (wds : List Withdrawal)
    {x : Adr} (hc : (benv.state.getCode x).toList ≠ []) :
    (withdrawalsPass rules benv bout wds).1.getStor x = benv.state.getStor x := by
  unfold withdrawalsPass
  split
  · exact processWithdrawalsState_getStor wds hc
  · rfl

private theorem withdrawalsPass_requests (rules : ForkRules) (benv : Benv) (bout : BlockOutput) (wds : List
    Withdrawal) :
    (withdrawalsPass rules benv bout wds).2.requests = bout.requests := by
  unfold withdrawalsPass
  split <;> rfl

/-! ### The request pass -/

namespace RequestPass

variable {benv : Benv} {bout out : BlockOutput} {st : State} {steps : List RequestStep}

/-- The stage's roots determine `requestsPass`. -/
theorem run (h : RequestPass benv bout st out steps) : requestsPass benv.stat.rules benv bout = .ok (st, out) := by
  unfold RequestPass at h
  unfold requestsPass
  split at h
  · rename_i on
    rw [ite_eq_left on]
    obtain ⟨deposits, acc, bal, hparse, roots, rfl⟩ := h
    unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt
    rw [hparse]
    change (runRequestContracts _ _ benv (seedRequests bout deposits) bout.bal >>= _) = _
    rw [roots.run]
    rfl
  · rename_i off
    rw [ite_eq_right off]
    obtain ⟨rfl, rfl, -⟩ := h
    rfl

theorem exists_of_run (h : requestsPass benv.stat.rules benv bout = .ok (st, out)) :
    ∃ steps, RequestPass benv bout st out steps := by
  unfold requestsPass at h
  unfold RequestPass
  by_cases on : benv.stat.rules.header.requestsHash = true
  · rw [ite_eq_left on] at h
    simp only [ite_eq_left on]
    unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at h
    obtain ⟨deposits, hparse, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨st', acc, bal⟩, hrun, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨steps, roots⟩ := exists_requestRoots hrun
    exact ⟨steps, deposits, acc, bal, hparse, roots, rfl⟩
  · rw [ite_eq_right on] at h
    simp only [ite_eq_right on]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨[], h.1.symm, h.2.symm, rfl⟩

theorem chain (h : RequestPass benv bout st out steps) {a : Adr} (hc : (benv.state.getCode a).toList ≠ [])
    (hd : ¬ isValidDelegation (benv.state.getCode a)) :
    KeptChain a (benv.state.getStor a) ((requestRootsOf steps).flatMap (Root.keptAt a)) (st.getStor a) ∧
      st.getCode a = benv.state.getCode a := by
  unfold RequestPass at h
  split at h
  · obtain ⟨deposits, acc, bal, -, roots, -⟩ := h
    exact roots.chain hc hd
  · obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨.nil _, rfl⟩

theorem empty_stays (h : RequestPass benv bout st out steps) {S : Adr} (empty : benv.state.getCode S = ByteArray.empty)
    (avoid : NoCreateAt S (requestRootsOf steps)) : st.getCode S = ByteArray.empty := by
  unfold RequestPass at h
  split at h
  · obtain ⟨deposits, acc, bal, -, roots, -⟩ := h
    exact roots.empty_stays empty avoid
  · obtain ⟨rfl, -, rfl⟩ := h
    exact empty

theorem caller_ne (h : RequestPass benv bout st out steps) {a S : Adr} (empty : benv.state.getCode S = ByteArray.empty)
    (avoid : NoCreateAt S (requestRootsOf steps)) :
    ∀ s ∈ steps, s.target ≠ a → ∀ f ∈ s.roots.flatMap (Root.keptAt a), f.sevm.caller ≠ S := by
  unfold RequestPass at h
  split at h
  · obtain ⟨deposits, acc, bal, -, roots, -⟩ := h
    exact roots.caller_ne empty avoid
  · obtain ⟨rfl, -, rfl⟩ := h
    intro s hs
    cases hs

theorem entry_in (h : RequestPass benv bout st out steps) {a : Adr} {C : ByteArray} (code : benv.state.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C) :
    ∀ f ∈ (requestRootsOf steps).flatMap (Root.keptAt a), Exec.Frame.EntryIn a C benv.stat f := by
  unfold RequestPass at h
  split at h
  · obtain ⟨deposits, acc, bal, -, roots, -⟩ := h
    exact roots.entry_in code nonempty nondelegating
  · obtain ⟨rfl, -, rfl⟩ := h
    intro f hf
    cases hf

/-- **Telling a request step apart.** Every root of a step runs at the step's target for the system caller. -/
theorem root_routing (h : RequestPass benv bout st out steps) :
    ∀ s ∈ steps, ∀ r ∈ s.roots, r.evm.sta.currentTarget = s.target ∧ r.evm.sta.caller = systemAddress := by
  unfold RequestPass at h
  split at h
  · obtain ⟨deposits, acc, bal, -, roots, -⟩ := h
    exact roots.root_routing
  · obtain ⟨-, -, rfl⟩ := h
    intro s hs
    cases hs

end RequestPass

/-! ### The body's levels -/

/-- The whole of `applyBody`, passing over the block access list. -/
private theorem applyBody_form {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput} (h : applyBody benv txs ommers wds = .ok (state, bout)) :
    ∃ beacon beaconBal preState preBal decoded txEnv txOut st out,
      beaconRootsCall benv.stat.rules benv = .ok (beacon, beaconBal) ∧
      historyStorageCall benv.stat.rules (benv.withState beacon) beaconBal = .ok (preState, preBal) ∧
      txs.mapM (decodeTx benv.stat.rules) = .ok decoded ∧
      applyTransactions decoded.putIndex (benv.withState preState) {BlockOutput.init with bal := preBal} = .ok (txEnv,
          txOut) ∧
      requestsPass benv.stat.rules (txEnv.withState (withdrawalsPass benv.stat.rules txEnv txOut wds).1)
        (withdrawalsPass benv.stat.rules txEnv txOut wds).2 = .ok (st, out) ∧
      (benv.stat.rules.pow = none → state = st) ∧ bout.requests = out.requests := by
  unfold applyBody at h
  dsimp only at h
  obtain ⟨⟨beacon, beaconBal⟩, hbeacon, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨preState, preBal⟩, hhistory, h⟩ := Except.bind_eq_ok h
  obtain ⟨decoded, hdecoded, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨txEnv, txOut⟩, htxs, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  rcases hw : withdrawalsPass benv.stat.rules txEnv txOut wds with ⟨withdrawn, withdrawnOut⟩
  simp only [hw] at h
  obtain ⟨⟨st, out⟩, hreq, h⟩ := Except.bind_eq_ok h
  obtain ⟨-, -, h⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  refine ⟨beacon, beaconBal, preState, preBal, decoded, txEnv, txOut, st, out, hbeacon, hhistory, hdecoded, htxs,
    by rw [hw]; exact hreq, fun none => ?_, ?_⟩
  · rw [← h.1, none]
  · rw [← h.2]

/-- **Every successful body has its roots.** -/
theorem exists_bodyRoots {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput} (h : applyBody benv txs ommers wds = .ok (state, bout)) :
    ∃ run, BodyRoots benv txs ommers wds state bout run := by
  obtain ⟨beacon, beaconBal, preState, preBal, decoded, txEnv, txOut, st, out, hbeacon, hhistory, hdecoded, htxs,
      hreq, -, -⟩ :=
    applyBody_form h
  obtain ⟨beaconRoots, first⟩ := exists_beaconRoots hbeacon
  obtain ⟨historyRoots, second⟩ := exists_historyRoots (benv := benv.withState beacon) (historyData benv) rfl hhistory
  obtain ⟨senders, txRoots, roots⟩ := exists_transactionsRoots htxs
  have hstat : txEnv.stat = benv.stat := by
    have same := congrArg Benv.stat roots.final_eq
    exact same
  obtain ⟨steps, pass⟩ := RequestPass.exists_of_run
    (benv := txEnv.withState (withdrawalsPass benv.stat.rules txEnv txOut wds).1)
    (bout := (withdrawalsPass benv.stat.rules txEnv txOut wds).2) (st := st) (out := out)
    (by change requestsPass txEnv.stat.rules _ _ = _; rw [hstat]; exact hreq)
  exact ⟨⟨preState, preBal, beaconRoots ++ historyRoots, txEnv, txOut, senders, txRoots, steps⟩, h,
    ⟨beacon, beaconBal, beaconRoots, historyRoots, hbeacon, first, hhistory, second, rfl⟩, ⟨decoded, hdecoded, roots⟩,
    ⟨st, out, pass⟩⟩

namespace BodyRoots

variable {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal} {state : State}
  {bout : BlockOutput} {run : BodyRun}

/-- Transactions leave the block's environment. -/
theorem txEnv_stat (h : BodyRoots benv txs ommers wds state bout run) : run.txEnv.stat = benv.stat := by
  obtain ⟨decoded, -, roots⟩ := h.transactions
  have same := congrArg Benv.stat roots.final_eq
  exact same

/-- A body, read off its roots: the request pass ends the world, and builds the request bytes. -/
theorem stages (h : BodyRoots benv txs ommers wds state bout run) :
    ∃ st out, RequestPass (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut wds).1)
        (withdrawalsPass benv.stat.rules run.txEnv run.txOut wds).2 st out run.requests ∧
      (benv.stat.rules.pow = none → state = st) ∧ bout.requests = out.requests := by
  obtain ⟨beacon, beaconBal, preState, preBal, decoded, txEnv, txOut, st, out, hbeacon, hhistory, hdecoded, htxs,
      hreq, final,
    requests⟩ := applyBody_form h.applied
  obtain ⟨beacon', beaconBal', -, -, hbeacon', -, hhistory', -, -⟩ := h.pre
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hbeacon.symm.trans hbeacon'))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hhistory.symm.trans hhistory'))
  obtain ⟨decoded', hdecoded', roots⟩ := h.transactions
  obtain rfl := Except.ok.inj (hdecoded.symm.trans hdecoded')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (htxs.symm.trans roots.run))
  obtain ⟨st', out', pass⟩ := h.requests
  have hrun := pass.run
  change requestsPass run.txEnv.stat.rules _ _ = _ at hrun
  rw [h.txEnv_stat] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hreq.symm.trans hrun))
  exact ⟨st, out, pass, final, requests⟩

/-- **The chain of a body.** At an account with code that is no delegation and not created in the block, the frames the
body keeps run from the storage it found to the storage it left, and the code stays. -/
theorem chain (h : BodyRoots benv txs ommers wds state bout run) (rules : KeptRules benv.stat.rules) {a : Adr}
    (hc : (benv.state.getCode a).toList ≠ []) (hd : ¬ isValidDelegation (benv.state.getCode a))
    (created : a ∉ benv.createdAccounts) :
    KeptChain a (benv.state.getStor a) (run.roots.flatMap (Root.keptAt a)) (state.getStor a) ∧
      state.getCode a = benv.state.getCode a := by
  obtain ⟨st, out, pass, final, -⟩ := h.stages
  obtain ⟨decoded, -, roots⟩ := h.transactions
  obtain ⟨chain₁, code₁⟩ := h.pre.chain hc hd
  obtain ⟨chain₂, code₂⟩ := roots.chain rules (a := a) (by simpa only [Benv.withState, code₁] using hc)
    (by simpa only [Benv.withState, code₁] using hd) created
  have codeT : run.txEnv.state.getCode a = benv.state.getCode a := code₂.trans code₁
  have hcT : (run.txEnv.state.getCode a).toList ≠ [] := by rw [codeT]; exact hc
  have hcode := withdrawalsPass_getCode benv.stat.rules run.txEnv run.txOut wds a
  obtain ⟨chain₃, code₃⟩ := pass.chain (a := a) (by simpa only [Benv.withState, hcode] using hcT)
    (by simpa only [Benv.withState, hcode, codeT] using hd)
  have hstor := withdrawalsPass_getStor benv.stat.rules run.txEnv run.txOut wds hcT
  simp only [Benv.withState] at chain₂ chain₃ code₃
  rw [hstor] at chain₃
  rw [hcode] at code₃
  rw [final rules.noRewards]
  unfold BodyRun.roots
  rw [List.flatMap_append, List.flatMap_append]
  exact ⟨(chain₁.append chain₂).append chain₃, code₃.trans codeT⟩

/-- **Caller exclusion over a body.** With no sender, authority or created frame at `S`, and `a` neither pre-execution
contract: no frame kept at `a` outside the request fold has caller `S`, nor does one of a request step at another
    target,
and `S` stays code-free. -/
theorem caller_ne (h : BodyRoots benv txs ommers wds state bout run) (rules : KeptRules benv.stat.rules) {a S : Adr}
    (empty : benv.state.getCode S = ByteArray.empty) (notBeacon : beaconRootsAddress ≠ a)
    (notHistory : historyStorageAddress ≠ a) (senders : NoSenderAt S run.senders) (authorities : NoAuthorityAt S
        run.senders)
    (avoid : NoCreateAt S run.roots) :
    (∀ f ∈ run.outsideRequests a, f.sevm.caller ≠ S) ∧
      (∀ s ∈ run.requests, s.target ≠ a → ∀ f ∈ s.roots.flatMap (Root.keptAt a), f.sevm.caller ≠ S) ∧
      state.getCode S = ByteArray.empty := by
  obtain ⟨st, out, pass, final, -⟩ := h.stages
  obtain ⟨decoded, -, roots⟩ := h.transactions
  have avoidPre : NoCreateAt S run.preRoots := avoid.left.left
  have avoidTxs : NoCreateAt S run.txRoots := avoid.left.right
  have avoidReq : NoCreateAt S (requestRootsOf run.requests) := avoid.right
  have empty₁ := h.pre.empty_stays empty avoidPre
  have empty₂ := roots.empty_stays empty₁ authorities avoidTxs
  have empty₃ : (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut wds).1).state.getCode S =
      ByteArray.empty := (withdrawalsPass_getCode _ _ _ _ S).trans empty₂
  refine ⟨fun f hf => ?_, pass.caller_ne empty₃ avoidReq, ?_⟩
  · unfold BodyRun.outsideRequests at hf
    rw [List.flatMap_append, List.mem_append] at hf
    rcases hf with hf | hf
    · exact h.pre.caller_ne empty avoidPre notBeacon notHistory f hf
    · exact roots.caller_ne empty₁ senders authorities avoidTxs f hf
  · rw [final rules.noRewards]
    exact pass.empty_stays empty₃ avoidReq

/-- **Entry facts over a body.** Every frame it keeps at `a`, where `a` holds nondelegating code `C`, runs `C` from its
start on fresh machine state, under the block's environment with its message's opening state. -/
theorem entry_in (h : BodyRoots benv txs ommers wds state bout run) (rules : KeptRules benv.stat.rules) {a : Adr}
    {C : ByteArray} (code : benv.state.getCode a = C) (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (created : a ∉ benv.createdAccounts) (data : DataFits run.senders) :
    ∀ f ∈ run.roots.flatMap (Root.keptAt a), Exec.Frame.EntryIn a C benv.stat f := by
  obtain ⟨st, out, pass, -, -⟩ := h.stages
  obtain ⟨decoded, -, roots⟩ := h.transactions
  have hc : (benv.state.getCode a).toList ≠ [] := by rw [code]; exact nonempty
  have hd : ¬ isValidDelegation (benv.state.getCode a) := by rw [code]; exact nondelegating
  have code₁ := (h.pre.chain hc hd).2
  have code₂ := (roots.chain rules (a := a) (by simpa only [Benv.withState, code₁] using hc)
    (by simpa only [Benv.withState, code₁] using hd) created).2
  intro f hf
  unfold BodyRun.roots at hf
  rw [List.flatMap_append, List.flatMap_append, List.mem_append, List.mem_append] at hf
  rcases hf with (hf | hf) | hf
  · exact h.pre.entry_in code nonempty nondelegating f hf
  · exact roots.entry_in rules (code₁.trans code) nonempty nondelegating created data f hf
  · have below : Exec.Frame.EntryIn a C run.txEnv.stat f :=
      pass.entry_in ((withdrawalsPass_getCode _ _ _ _ a).trans (code₂.trans (code₁.trans code))) nonempty
          nondelegating f hf
    rw [h.txEnv_stat] at below
    exact below

/-- **The request bytes of a body.** Where the rules have the request pass, the block's requests are the deposit
requests, type byte first and only when nonempty, then each call's bytes in call order. -/
theorem requests_eq (h : BodyRoots benv txs ommers wds state bout run) (on : benv.stat.rules.header.requestsHash =
    true) :
    ∃ deposits, parseDepositRequests (withdrawalsPass benv.stat.rules run.txEnv run.txOut wds).2 = .ok deposits ∧
      bout.requests = (if deposits.length > 0 then [depositRequestType ++ deposits] else []) ++
        run.requests.flatMap RequestStep.bytes := by
  obtain ⟨st, out, pass, -, requests⟩ := h.stages
  obtain ⟨decoded, -, roots⟩ := h.transactions
  have on' : (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut
      wds).1).stat.rules.header.requestsHash
      = true := by
    change run.txEnv.stat.rules.header.requestsHash = true
    rw [h.txEnv_stat]
    exact on
  unfold RequestPass at pass
  rw [ite_eq_left on'] at pass
  obtain ⟨deposits, acc, bal, hparse, fold, rfl⟩ := pass
  refine ⟨deposits, hparse, ?_⟩
  have seeded : (withdrawalsPass benv.stat.rules run.txEnv run.txOut wds).2.requests = [] :=
    (withdrawalsPass_requests _ _ _ _).trans roots.requests_eq
  rw [requests, fold.acc_eq]
  unfold seedRequests
  rw [seeded]
  simp only [List.nil_append]

/-- Where the rules have no request pass, a body has no request step. -/
theorem requests_off (h : BodyRoots benv txs ommers wds state bout run) (off : ¬ benv.stat.rules.header.requestsHash =
    true) :
    run.requests = [] := by
  obtain ⟨st, out, pass, -, -⟩ := h.stages
  have off' : ¬ (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut
      wds).1).stat.rules.header.requestsHash
      = true := by
    change ¬ run.txEnv.stat.rules.header.requestsHash = true
    rw [h.txEnv_stat]
    exact off
  unfold RequestPass at pass
  rw [ite_eq_right off'] at pass
  exact pass.2.2

/-- Where the rules have the request pass, the request steps are the rules' contracts, in order. -/
theorem contracts_eq (h : BodyRoots benv txs ommers wds state bout run) (on : benv.stat.rules.header.requestsHash =
    true) :
    benv.stat.rules.requests = run.requests.map (fun s => (s.type, s.target)) := by
  obtain ⟨st, out, pass, -, -⟩ := h.stages
  have on' : (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut
      wds).1).stat.rules.header.requestsHash
      = true := by
    change run.txEnv.stat.rules.header.requestsHash = true
    rw [h.txEnv_stat]
    exact on
  unfold RequestPass at pass
  rw [ite_eq_left on'] at pass
  obtain ⟨deposits, acc, bal, -, fold, -⟩ := pass
  have same := fold.contracts_eq
  change run.txEnv.stat.rules.requests = _ at same
  rw [h.txEnv_stat] at same
  exact same

/-- **Telling a request step apart.** Every root of a request step runs at the step's target for the system caller. -/
theorem request_routing (h : BodyRoots benv txs ommers wds state bout run) :
    ∀ s ∈ run.requests, ∀ r ∈ s.roots, r.evm.sta.currentTarget = s.target ∧ r.evm.sta.caller = systemAddress := by
  obtain ⟨st, out, pass, -, -⟩ := h.stages
  exact pass.root_routing

/-- **A body's calldata is word-sized**, under its header's gas limit. -/
theorem data_fits (h : BodyRoots benv txs ommers wds state bout run) (rules : KeptRules benv.stat.rules)
    (limit : benv.stat.blockGasLimit < 2 ^ 63) : DataFits run.senders := by
  obtain ⟨decoded, -, roots⟩ := h.transactions
  exact roots.data_fits rules limit

end BodyRoots

/-! ## The history -/

/-- One block of a kept history: the chain before it, the block, its fork, its output and its stages. -/
structure KeptBlock where
  parent : BlockChain
  block : Block
  fork : Fork
  output : BlockOutput
  run : BodyRun

/-- The environment a kept block's body opened on. -/
def KeptBlock.benv (b : KeptBlock) : Benv := initBenv b.fork b.parent b.block.header

/-- What a kept block keeps at `a`. -/
def KeptBlock.keptAt (a : Adr) (b : KeptBlock) : List Exec.Frame := b.run.roots.flatMap (Root.keptAt a)

/-- One step of a kept history: a successful transition, at a kept fork, ending on the state of its body's roots. -/
structure KeptStep (cfg : ChainConfig) (b : KeptBlock) (post : BlockChain) : Prop where
  transition : stateTransitionUsing cfg b.parent b.block = .ok post
  forkAt : cfg.forkAt b.block.header.number b.block.header.timestamp = .ok b.fork
  kept : KeptFork b.fork
  body : BodyRoots b.benv b.block.txs b.block.ommers b.block.wds post.state b.output b.run

/-- The roots of every block from one chain to another, at kept forks. -/
inductive KeptHistory (cfg : ChainConfig) (start : BlockChain) : List KeptBlock → BlockChain → Prop where
  | refl : KeptHistory cfg start [] start
  | step {blocks : List KeptBlock} {b : KeptBlock} {post : BlockChain} :
      KeptHistory cfg start blocks b.parent → KeptStep cfg b post → KeptHistory cfg start (blocks ++ [b]) post

/-- Chains joined by successful transitions, each selecting a kept fork. -/
inductive KeptReach (cfg : ChainConfig) (start : BlockChain) : BlockChain → Prop where
  | refl : KeptReach cfg start start
  | step {current post : BlockChain} {block : Block} : KeptReach cfg start current →
      stateTransitionUsing cfg current block = .ok post →
      (∀ fork, cfg.forkAt block.header.number block.header.timestamp = .ok fork → KeptFork fork) →
      KeptReach cfg start post

/-- **A configured reach is a kept reach, from a timestamp on.** Every block a chain accepts is strictly later than the
tip it extends, so a schedule that selects only kept forks at or after `T` is enough, from a chain whose tip is at or
past `T`. Mainnet's schedule, for instance, selects historical forks only before Prague. -/
theorem KeptReach.of_reachUsing {cfg : ChainConfig} {start post : BlockChain} (h : BlockChain.ReachUsing cfg start post)
    (T : Nat) (kept : ∀ number timestamp f, T ≤ timestamp → cfg.forkAt number timestamp = .ok f → KeptFork f)
    (floor : ∃ parent, start.blocks.getLast? = some parent ∧ T ≤ parent.header.timestamp) : KeptReach cfg start post := by
  induction h with
  | refl => exact .refl
  | step prior _ transition ih =>
      refine .step ih transition fun fork hf => kept _ _ fork ?_ hf
      obtain ⟨_, _, _, ⟨parent, hlast, hlt⟩, _⟩ := stateTransitionUsing_reachedStep transition
      obtain ⟨tip, htip, hfloor⟩ := prior.tip_floor floor
      rw [htip] at hlast
      cases hlast
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt hfloor hlt)

/-- **A schedule of kept forks only**: every configured reach is a kept reach. -/
theorem KeptReach.of_schedule {cfg : ChainConfig} {start post : BlockChain} (h : BlockChain.ReachUsing cfg start post)
    (kept : ∀ a ∈ cfg.activations, KeptFork a.fork) : KeptReach cfg start post := by
  induction h with
  | refl => exact .refl
  | step _ _ transition ih =>
      refine .step ih transition fun fork hf => ?_
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (ChainConfig.forkAt_mem hf)
      exact kept a ha

/-- From Prague on, mainnet's schedule selects only kept forks. It names no Amsterdam activation yet. -/
theorem KeptReach.of_mainnet {start post : BlockChain} (h : BlockChain.ReachUsing mainnetChainConfig start post)
    (floor : ∃ parent, start.blocks.getLast? = some parent ∧ mainnetPragueTimestamp ≤ parent.header.timestamp) :
    KeptReach mainnetChainConfig start post :=
  .of_reachUsing h mainnetPragueTimestamp (fun n t f ht hf => .inl (mainnetChainConfig_covered n t f ht hf)) floor

/-- A chain of one fork from genesis on, at Amsterdam: Amsterdam alone is a kept schedule. -/
theorem KeptReach.of_amsterdamOnly {chainId : UInt64} {start post : BlockChain}
    (h : BlockChain.ReachUsing (ChainConfig.single chainId .amsterdam) start post) :
    KeptReach (ChainConfig.single chainId .amsterdam) start post := by
  refine .of_schedule h fun a ha => ?_
  simp only [ChainConfig.single, List.mem_singleton] at ha
  subst ha
  exact .inr rfl

/-- A timestamp activation of Amsterdam on top of BPO2, the schedule of Jaune's `BPO2ToAmsterdamAtTime` fixtures. -/
theorem KeptReach.of_bpo2ToAmsterdam {chainId : UInt64} {T : Nat} {start post : BlockChain}
    (h : BlockChain.ReachUsing (ForkTransition.chainConfig chainId ⟨.bpo2, .amsterdam, .byTimestamp T⟩) start post) :
    KeptReach (ForkTransition.chainConfig chainId ⟨.bpo2, .amsterdam, .byTimestamp T⟩) start post := by
  refine .of_schedule h fun a ha => ?_
  rcases List.mem_cons.mp ha with same | ha
  · rw [same]
    exact .inl (show CoveredFork .bpo2 by decide)
  · rw [List.mem_singleton.mp ha]
    exact .inr rfl

/-- Each kept fork commits to requests. -/
theorem KeptFork.requestsHash {f : Fork} (h : KeptFork f) : f.ruleSet.header.requestsHash = true := by
  rcases h with covered | rfl
  · exact covered.cases (motive := fun f => f.ruleSet.header.requestsHash = true) rfl rfl rfl rfl
  · rfl

/-- The last of the block's output checks: the requests hash it computed is the header's. -/
theorem stateTransitionChecks_requestsHash {bout : BlockOutput} {header : Header}
    {transactionsRoot blockStateRoot receiptRoot withdrawalsRoot : B256} {blockLogsBloom : Bytes}
    {requestsHash : Option B256}
    (h : stateTransitionChecks bout header transactionsRoot blockStateRoot receiptRoot blockLogsBloom withdrawalsRoot
      requestsHash = .ok ()) : requestsHash = header.requestsHash := by
  have pass : ∀ {c : Prop} [Decidable c] {α ε : Type} {e : ε} {k : Unit → Except ε α} {r : Except ε α} {x : α},
      (if c then Except.bind (.error e) k else r) = .ok x → r = .ok x := by
    intro c _ α ε e k r x hx
    by_cases hc : c
    · rw [if_pos hc] at hx
      cases hx
    · rw [if_neg hc] at hx
      exact hx
  unfold stateTransitionChecks at h
  dsimp only at h
  have h := pass (pass (pass (pass (pass (pass (pass h))))))
  by_contra hne
  rw [if_pos hne] at h
  cases h

/-- **Every successful transition at a kept fork has its roots.** -/
theorem exists_keptStep {cfg : ChainConfig} {pre post : BlockChain} {block : Block}
    (h : stateTransitionUsing cfg pre block = .ok post)
    (kept : ∀ fork, cfg.forkAt block.header.number block.header.timestamp = .ok fork → KeptFork fork) :
    ∃ b : KeptBlock, b.parent = pre ∧ b.block = block ∧ KeptStep cfg b post := by
  obtain ⟨fork, state, output, hfork, -, hbody, rfl⟩ := exists_configuredBody_of_transition h
  obtain ⟨run, roots⟩ := exists_bodyRoots hbody
  exact ⟨⟨pre, block, fork, output, run⟩, rfl, rfl, ⟨h, hfork, kept fork hfork, roots⟩⟩

/-- **Every reach through kept forks has its roots.** -/
theorem exists_keptHistory {cfg : ChainConfig} {start post : BlockChain} (h : KeptReach cfg start post) :
    ∃ blocks, KeptHistory cfg start blocks post := by
  induction h with
  | refl => exact ⟨[], .refl⟩
  | step _ transition kept ih =>
      obtain ⟨blocks, history⟩ := ih
      obtain ⟨b, rfl, rfl, step⟩ := exists_keptStep transition kept
      exact ⟨_, .step history step⟩

namespace KeptStep

variable {cfg : ChainConfig} {b : KeptBlock} {post : BlockChain}

private theorem rules (h : KeptStep cfg b post) : KeptRules b.benv.stat.rules := h.kept.rules

private theorem not_created (a : Adr) (b : KeptBlock) : a ∉ b.benv.createdAccounts := AdrSet.not_mem_empty

/-- **The header commits to the requests the body output.** A kept step's transition compared them: the header's hash is
`computeRequestsHash` of exactly the block's request bytes. -/
theorem requests_hash (h : KeptStep cfg b post) :
    b.block.header.requestsHash = some (computeRequestsHash b.output.requests) := by
  obtain ⟨fork, hFork, hScheduled⟩ := stateTransitionUsing_scheduled_ok h.transition
  obtain rfl : fork = b.fork := Except.ok.inj (hFork.symm.trans h.forkAt)
  have hCore := stateTransitionScheduledE_eq_ok_iff.mp hScheduled
  unfold stateTransitionCoreE at hCore
  obtain ⟨_, _, hCore⟩ := Except.bind_eq_ok hCore
  obtain ⟨_, _, hCore⟩ := Except.bind_eq_ok hCore
  obtain ⟨⟨bodyState, blockOutput⟩, hBody, hCore⟩ := Except.bind_eq_ok hCore
  have hBodyEq := Except.mapError_eq_ok_iff.mp hBody
  change applyBody b.benv b.block.txs b.block.ommers b.block.wds = _ at hBodyEq
  rw [h.body.applied] at hBodyEq
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hBodyEq)
  dsimp only at hCore
  obtain ⟨checked, hChecks, _⟩ := Except.bind_eq_ok hCore
  cases checked
  have same := stateTransitionChecks_requestsHash (Except.mapError_eq_ok_iff.mp hChecks)
  rw [← same, h.kept.requestsHash]
  rfl

/-- **A kept step's calldata is word-sized**: the transition validated the header's gas limit. -/
theorem data_fits (h : KeptStep cfg b post) : DataFits b.run.senders :=
  h.body.data_fits h.rules (ExecutionTrace.header_gasLimit_lt_of_transition h.transition)

end KeptStep

namespace KeptHistory

variable {cfg : ChainConfig} {start post : BlockChain} {blocks : List KeptBlock}

/-- **The chain of a history.** At an account with code that is no delegation, the frames kept along the history run
from the storage it found to the storage it left, and the code stays. -/
theorem chain (h : KeptHistory cfg start blocks post) {a : Adr} (hc : (start.state.getCode a).toList ≠ [])
    (hd : ¬ isValidDelegation (start.state.getCode a)) :
    KeptChain a (start.state.getStor a) (blocks.flatMap (KeptBlock.keptAt a)) (post.state.getStor a) ∧
      post.state.getCode a = start.state.getCode a := by
  induction h with
  | refl => exact ⟨.nil _, rfl⟩
  | @step blocks b post prior step ih =>
      obtain ⟨chain₁, code₁⟩ := ih
      obtain ⟨chain₂, code₂⟩ := step.body.chain step.rules (a := a)
        (by change (b.parent.state.getCode a).toList ≠ []; rw [code₁]; exact hc)
        (by change ¬ isValidDelegation (b.parent.state.getCode a); rw [code₁]; exact hd) (KeptStep.not_created a b)
      rw [List.flatMap_append, List.flatMap_singleton]
      exact ⟨chain₁.append chain₂, code₂.trans code₁⟩

/-- **Caller exclusion over a history.** With no sender, authority or created frame at `S` in any block, and `a` neither
pre-execution contract: no frame kept at `a` outside the request folds has caller `S`, nor does one of a request step at
another target, and `S` stays code-free. A request step at `a` itself is a root with the system caller, by
`BodyRoots.request_routing`. -/
theorem caller_ne (h : KeptHistory cfg start blocks post) {a S : Adr} (empty : start.state.getCode S = ByteArray.empty)
    (notBeacon : beaconRootsAddress ≠ a) (notHistory : historyStorageAddress ≠ a)
    (senders : ∀ b ∈ blocks, NoSenderAt S b.run.senders) (authorities : ∀ b ∈ blocks, NoAuthorityAt S b.run.senders)
    (avoid : ∀ b ∈ blocks, NoCreateAt S b.run.roots) :
    (∀ b ∈ blocks, ∀ f ∈ b.run.outsideRequests a, f.sevm.caller ≠ S) ∧
      (∀ b ∈ blocks, ∀ s ∈ b.run.requests, s.target ≠ a → ∀ f ∈ s.roots.flatMap (Root.keptAt a), f.sevm.caller ≠ S) ∧
      post.state.getCode S = ByteArray.empty := by
  induction h with
  | refl => exact ⟨fun _ hb => absurd hb List.not_mem_nil, fun _ hb => absurd hb List.not_mem_nil, empty⟩
  | @step blocks b post prior step ih =>
      obtain ⟨outside, requests, code⟩ := ih (fun x hx => senders x (List.mem_append_left _ hx))
        (fun x hx => authorities x (List.mem_append_left _ hx)) (fun x hx => avoid x (List.mem_append_left _ hx))
      have here : b ∈ blocks ++ [b] := List.mem_append_right _ List.mem_cons_self
      obtain ⟨outside', requests', code'⟩ := step.body.caller_ne step.rules (S := S) code notBeacon notHistory
        (senders b here) (authorities b here) (avoid b here)
      refine ⟨fun x hx => ?_, fun x hx => ?_, code'⟩
      · rcases List.mem_append.mp hx with hx | hx
        · exact outside x hx
        · rw [List.mem_singleton.mp hx]
          exact outside'
      · rcases List.mem_append.mp hx with hx | hx
        · exact requests x hx
        · rw [List.mem_singleton.mp hx]
          exact requests'

/-- **Entry facts over a history.** Every frame kept at `a`, where `a` holds nondelegating code `C`, runs `C` from its
start on fresh machine state, under its block's environment with its message's opening state. -/
theorem entry_in (h : KeptHistory cfg start blocks post) {a : Adr} {C : ByteArray} (code : start.state.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C) :
    ∀ b ∈ blocks, ∀ f ∈ b.keptAt a, Exec.Frame.EntryIn a C b.benv.stat f := by
  have hc : (start.state.getCode a).toList ≠ [] := by rw [code]; exact nonempty
  have hd : ¬ isValidDelegation (start.state.getCode a) := by rw [code]; exact nondelegating
  induction h with
  | refl => exact fun _ hb => absurd hb List.not_mem_nil
  | @step blocks b post prior step ih =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ih x hx
      · rw [List.mem_singleton.mp hx]
        exact step.body.entry_in step.rules ((chain prior hc hd).2.trans code) nonempty nondelegating
          (KeptStep.not_created a b) step.data_fits

/-- Every kept block is a step of the history, so its output and its stages can be read back. -/
theorem mem_step (h : KeptHistory cfg start blocks post) :
    ∀ b ∈ blocks, ∃ next, KeptStep cfg b next := by
  induction h with
  | refl => exact fun _ hb => absurd hb List.not_mem_nil
  | @step blocks b post prior step ih =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ih x hx
      · rw [List.mem_singleton.mp hx]
        exact ⟨post, step⟩

end KeptHistory

end Blanc
