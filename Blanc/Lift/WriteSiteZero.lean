import Blanc.Lift.WriteSiteLocality
import Blanc.Lift.Quiet
import Blanc.TerminalStorage
import Blanc.Lift.TargetLogEvents

/-!
# Zero preservation from checked write locality

An actual SSTORE satisfying `GuardObs K False` preserves zero on the demanded
slots. The general lifted-run fold exposes external-step and terminal laws;
the terminal law can be discharged by actual terminal semantics, including
SELFDESTRUCT. Locality alone says nothing about child effects.
These are storage induction tools, with no contract, hash or signature premise.
-/

namespace Blanc.Lift.WriteSite

open Jaune

/-- The demanded physical storage cells of account `a` read zero. -/
def ZeroSlots (K : B256 → Prop) (a : Adr) (d : Devm) : Prop :=
  ∀ x, K x → d.getStorVal a x = 0

/-- Exact storage equality transports a zero seed. -/
theorem ZeroSlots.of_getStor_eq {K : B256 → Prop} {a : Adr} {pre post : Devm}
    (zero : ZeroSlots K a pre) (storage : post.getStor a = pre.getStor a) :
    ZeroSlots K a post := by
  intro x tracked
  change (post.getStor a).get x = 0
  rw [storage]
  exact zero x tracked

/-- An actual non-increasing SSTORE preserves all demanded zero cells,
including those distinct from the written slot. No fork or hash law is needed. -/
theorem GuardObs.sstore_zero {K : B256 → Prop} {sevm : Sevm} {pre post : Devm}
    (obs : GuardObs K False sevm pre (.reg .sstore))
    (run : Ninst.Run sevm pre (.reg .sstore) post)
    (zero : ZeroSlots K sevm.currentTarget pre) : ZeroSlots K sevm.currentTarget post := by
  obtain ⟨key, value, popped⟩ := of_run_sstore run
  have stack : pre.stack = key :: value :: post.stack := popped
  have effect := sstore_getStor_set (xs := []) run ⟨post.stack, popped⟩
  intro probe tracked
  change (post.getStor sevm.currentTarget).get probe = 0
  rw [effect, Stor.get_set_ite]
  by_cases hit : key = probe
  · rw [ite_eq_left hit]
    have keyTracked : K key := by rw [hit]; exact tracked
    rcases obs rfl key value post.stack stack keyTracked with impossible | nonInc
    · exact impossible.elim
    · apply B256.toNat_inj
      rw [B256.toNat_zero]
      have bounded : value.toNat ≤ 0 := by
        simpa only [zero key keyTracked, B256.toNat_zero] using nonInc
      exact Nat.eq_zero_of_le_zero bounded
  · rw [ite_eq_right hit]
    exact zero probe tracked

/-- Zero across one actual instruction. The external arm consumes its exact
filled recursive slot and real `Xinst.Run`; locality does not prove its effect. -/
theorem GuardObs.step_zero {K : B256 → Prop} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (fork : CoveredFork sevm.benvStat.fork) (obs : GuardObs K False sevm pre n)
    (run : Ninst.Run sevm pre n post)
    (child : ∀ {x : Xinst} {xl : Xlot}, n = .exec x → xl.Filled →
      Xinst.Run sevm pre x xl (.ok post) →
      ZeroSlots K sevm.currentTarget pre → ZeroSlots K sevm.currentTarget post)
    (zero : ZeroSlots K sevm.currentTarget pre) : ZeroSlots K sevm.currentTarget post := by
  cases n with
  | exec x =>
      obtain ⟨xl, filled, pc, step⟩ := run
      simp only [Ninst.StepRun, Ninst.step_exec] at step
      exact child rfl filled (XStep.run_toStep.mp step) zero
  | reg r =>
      by_cases store : r = .sstore
      · subst r
        exact obs.sstore_zero run zero
      · obtain ⟨pc, regular⟩ := of_run_reg run
        exact zero.of_getStor_eq (congrFun (Rinst.preserves_stor store regular) _).symm
  | push bytes bound =>
      exact zero.of_getStor_eq (congrFun (Ninst.world_of_quiet fork rfl run).1 _)
  | dupn imm =>
      exact zero.of_getStor_eq (congrFun (Ninst.world_of_quiet fork rfl run).1 _)
  | swapn imm =>
      exact zero.of_getStor_eq (congrFun (Ninst.world_of_quiet fork rfl run).1 _)
  | exchange imm =>
      exact zero.of_getStor_eq (congrFun (Ninst.world_of_quiet fork rfl run).1 _)

/-- Compatibility form for non-SELFDESTRUCT terminals. `terminal_zero_all`
also handles SELFDESTRUCT's possible empty-account storage clearing. -/
theorem terminal_zero {K : B256 → Prop} {a : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (terminal : l ≠ .selfdestruct) (run : Linst.Run sevm pre l (.ok post))
    (zero : ZeroSlots K a pre) : ZeroSlots K a post :=
  zero.of_getStor_eq (congrFun (Linst.world_of_ok terminal run).1 a)

/-- Every successful terminal preserves demanded zero cells, including
SELFDESTRUCT: each storage map is unchanged or becomes empty. No fork or
account-protection premise is needed at this instruction boundary. -/
theorem terminal_zero_all {K : B256 → Prop} {a : Adr} {sevm : Sevm} {pre post : Devm}
    {l : Linst} (run : Linst.Run sevm pre l (.ok post))
    (zero : ZeroSlots K a pre) : ZeroSlots K a post := by
  intro slot tracked
  change (post.getStor a).get slot = 0
  rcases Blanc.Linst.run_getStor_eq_or_empty run a with same | empty
  · rw [same]
    exact zero slot tracked
  · rw [empty]
    rfl

/-- Fold zero preservation through the actual lifted derivation, including
callee returns and continuations, from any one-step zero law. Fork-free: the
step law and terminal law are the caller's. -/
theorem runP_zero_of_step {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm}
    (stepZero : ∀ {d n d'}, P sevm d n d' →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d')
    (terminals : ∀ {d d' l}, Linst.Run sevm d l (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d') :
    ∀ {d f out}, SFunc.RunP P fs sevm d f out → ZeroSlots K sevm.currentTarget d →
      ZeroSlots K sevm.currentTarget (Outcome.devm out) := by
  intro d f out run
  induction run with
  | zero _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | succ _ _ _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | toZero _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | toSucc _ _ _ _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | last run =>
      exact terminals run
  | next step _ ih =>
      intro seed
      exact ih (stepZero step seed)
  | dest burn _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (Blanc.Devm.Burn.getStor burn _))
  | jump _ _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | ret _ popped =>
      intro seed
      exact seed.of_getStor_eq (popped.getStor _)
  | callHalt _ _ popped _ ih =>
      intro seed
      exact ih (seed.of_getStor_eq (popped.getStor _))
  | callRet _ _ popped _ _ ihCall ihTail =>
      intro seed
      exact ihTail (ihCall (seed.of_getStor_eq (popped.getStor _)))
  | pcAt step _ _ ih =>
      intro seed
      exact ih (stepZero step seed)

/-- Fold zero preservation through the actual lifted derivation, including
callee returns and continuations. External and terminal laws concern their
real one-step executions; neither is a whole-run endpoint premise. They must
be discharged by the eventual runtime/history consumer. -/
theorem runP_zero {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} (fork : CoveredFork sevm.benvStat.fork)
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.Run sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (children : ∀ {d d' x xl}, P sevm d (.exec x) d' → xl.Filled →
      Xinst.Run sevm d x xl (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d')
    (terminals : ∀ {d d' l}, Linst.Run sevm d l (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d') :
    ∀ {d f out}, SFunc.RunP P fs sevm d f out → ZeroSlots K sevm.currentTarget d →
      ZeroSlots K sevm.currentTarget (Outcome.devm out) := by
  refine runP_zero_of_step ?_ terminals
  intro d n d' step zero
  refine (observations step).step_zero fork (steps step) ?_ zero
  intro x xl instruction filled run
  subst n
  exact children step filled run

/-- Zero across one actual non-external instruction, with no fork premise:
an SSTORE by `GuardObs.sstore_zero`, every other such instruction is
state-silent. -/
theorem GuardObs.step_zero_noExec {K : B256 → Prop} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (obs : GuardObs K False sevm pre n) (run : Ninst.Run sevm pre n post)
    (noExec : ∀ x, n ≠ .exec x)
    (zero : ZeroSlots K sevm.currentTarget pre) : ZeroSlots K sevm.currentTarget post := by
  by_cases store : n = .reg .sstore
  · subst store
    exact obs.sstore_zero run zero
  have silent : n.stateSilent = true := by
    cases n with
    | exec x => exact (noExec x rfl).elim
    | reg r =>
        cases r <;> first | rfl | exact (store rfl).elim
    | push => rfl
    | dupn => rfl
    | swapn => rfl
    | exchange => rfl
  have state : post.state = pre.state := by
    have whole : SFunc.RunP Ninst.Run ([] : List SFunc) sevm pre (.next n (.last .stop))
        (.halted post) := .next run (.last rfl)
    exact SFunc.RunP.state_of_silent id (S := []) rfl
      (by simp only [SFunc.silent, silent, Bool.true_and]; rfl) rfl whole
  exact zero.of_getStor_eq (by simp only [Devm.getStor, Devm.getAcct, state])

/-- Fork-free zero fold for a lifted run with no external instruction:
every step is observed non-increasing on `K` and not `.exec`; terminals use
their actual semantics. Only the initial seed remains explicit. -/
theorem runP_zero_noExec {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm}
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.Run sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (noExec : ∀ {d n d'}, P sevm d n d' → ∀ x, n ≠ .exec x) :
    ∀ {d f out}, SFunc.RunP P fs sevm d f out → ZeroSlots K sevm.currentTarget d →
      ZeroSlots K sevm.currentTarget (Outcome.devm out) :=
  runP_zero_of_step
    (fun step zero => (observations step).step_zero_noExec (steps step) (noExec step) zero)
    (fun run zero => terminal_zero_all run zero)

/-- Halted whole-program form of `runP_zero_noExec`. -/
theorem progRunP_zero_noExec {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.Run sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (noExec : ∀ {d n d'}, P sevm d n d' → ∀ x, n ≠ .exec x)
    (run : SProg.RunP P fs sevm pre post) (zero : ZeroSlots K sevm.currentTarget pre) :
    ZeroSlots K sevm.currentTarget post := by
  obtain ⟨f, _, actual⟩ := run
  exact runP_zero_noExec steps observations noExec actual zero

/-- Entry zero's whole-program form of `runP_zero`, for an actual halted run. -/
theorem progRunP_zero {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.Run sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (children : ∀ {d d' x xl}, P sevm d (.exec x) d' → xl.Filled →
      Xinst.Run sevm d x xl (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d')
    (terminals : ∀ {d d' l}, Linst.Run sevm d l (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d')
    (run : SProg.RunP P fs sevm pre post) (zero : ZeroSlots K sevm.currentTarget pre) :
    ZeroSlots K sevm.currentTarget post := by
  obtain ⟨f, _, actual⟩ := run
  exact runP_zero fork steps observations children terminals actual zero

/-- Actual terminals discharge the terminal premise of `runP_zero`. Only the
genuine local external-step law remains for the concrete child consumer. -/
theorem runP_zero_of_children {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} (fork : CoveredFork sevm.benvStat.fork)
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.Run sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (children : ∀ {d d' x xl}, P sevm d (.exec x) d' → xl.Filled →
      Xinst.Run sevm d x xl (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d') :
    ∀ {d f out}, SFunc.RunP P fs sevm d f out → ZeroSlots K sevm.currentTarget d →
      ZeroSlots K sevm.currentTarget (Outcome.devm out) :=
  runP_zero fork steps observations children (fun run zero => terminal_zero_all run zero)

/-- Whole-program zero preservation with actual terminal semantics discharged;
the initial seed and local actual child law remain explicit. -/
theorem progRunP_zero_of_children
    {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.Run sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (children : ∀ {d d' x xl}, P sevm d (.exec x) d' → xl.Filled →
      Xinst.Run sevm d x xl (.ok d') →
      ZeroSlots K sevm.currentTarget d → ZeroSlots K sevm.currentTarget d')
    (run : SProg.RunP P fs sevm pre post) (zero : ZeroSlots K sevm.currentTarget pre) :
    ZeroSlots K sevm.currentTarget post := by
  obtain ⟨f, _, actual⟩ := run
  exact runP_zero_of_children fork steps observations children actual zero

/-- Reduce an actual executable step to its committing, nonstatic recursive
child. Childless execution, STATICCALL and complete-settlement rollback use
existing semantic storage laws. The actual child derivation and its `Q`
provenance survive, and the seed is transported at the same observed owner,
which need not be the child's execution target. -/
theorem exec_zero_of_committed_child
    {Q : ∀ pc sevm d out, Exec pc sevm d out → Prop}
    {K : B256 → Prop} {a : Adr} {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (fork : CoveredFork sevm.benvStat.fork)
    (code : x ≠ .staticcall → pre.getCode a ≠ .empty)
    (run : Ninst.RunWith Q sevm pre (.exec x) post)
    (children : ∀ {frame : Jaune.Frame} {resume : Resume} {child : Evm} {raw : Execution},
      x ≠ .staticcall → (body : Exec child.pc child.sta child.dyna raw) →
      Q _ _ _ _ body → Xinst.step sevm pre x = .spawn frame resume →
      frame.enter = .run child → resume.run (frame.settle raw) = .ok post →
      ∀ settles : frame.settlementCommits raw = true,
      child.sta.depth < sevm.depth → CoveredFork child.sta.benvStat.fork →
      ZeroSlots K a child.dyna →
      ZeroSlots K a (Execution.committedPost raw
        (Frame.raw_commits_of_settlementCommits settles)))
    (zero : ZeroSlots K a pre) : ZeroSlots K a post := by
  by_cases static : x = .staticcall
  · subst x
    exact zero.of_getStor_eq
      (congrFun (Ninst.staticcall_inv_getStor_exact fork run.toRun).symm a)
  · obtain ⟨xl, filled, pc, step⟩ := run
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at step
    cases xl with
    | none =>
        have protection : State.Protected pre.state a := by
          right
          intro empty
          exact code static (ByteArray.eq_empty_of_size_eq_zero empty)
        exact zero.of_getStor_eq (Blanc.Xinst.none_getStor_eq step a protection)
    | some slot =>
        obtain ⟨child, raw⟩ := slot
        obtain ⟨body, provenance⟩ := filled
        obtain ⟨frame, resume, spawn, entered, resumed⟩ := XStep.Run.some_inv step
        obtain ⟨world, _, _, _, childFork, _⟩ :=
          Blanc.Xinst.spawn_child_world fork spawn entered
        have seam := Blanc.Xinst.spawn_run_getStor fork spawn entered body resumed.symm
          (code static)
        by_cases settles : frame.settlementCommits raw = true
        · have seed : ZeroSlots K a child.dyna := zero.of_getStor_eq (world a (code static))
          have childZero := children static body provenance spawn entered resumed.symm settles
            (Xinst.depth_lt step) childFork seed
          intro key tracked
          change (post.getStor a).get key = 0
          rw [seam.1 settles key]
          exact childZero key tracked
        · intro key tracked
          change (post.getStor a).get key = 0
          rw [seam.2 settles key]
          exact zero key tracked

/-- A lifted fold whose only recursive zero obligation concerns actual
nonstatic children that commit through complete settlement. `RunWith Q`
retains occurrence/root provenance for the recursive producer. -/
theorem runP_zero_of_committed_children
    {Q : ∀ pc sevm d out, Exec pc sevm d out → Prop}
    {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm}
    (fork : CoveredFork sevm.benvStat.fork)
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.RunWith Q sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (code : ∀ {d d' x}, P sevm d (.exec x) d' → x ≠ .staticcall →
      d.getCode sevm.currentTarget ≠ .empty)
    (children : ∀ {d d' x frame resume child raw}, P sevm d (.exec x) d' →
      x ≠ .staticcall → (body : Exec child.pc child.sta child.dyna raw) →
      Q _ _ _ _ body → Xinst.step sevm d x = .spawn frame resume →
      frame.enter = .run child → resume.run (frame.settle raw) = .ok d' →
      ∀ settles : frame.settlementCommits raw = true,
      child.sta.depth < sevm.depth → CoveredFork child.sta.benvStat.fork →
      ZeroSlots K sevm.currentTarget child.dyna →
      ZeroSlots K sevm.currentTarget (Execution.committedPost raw
        (Frame.raw_commits_of_settlementCommits settles))) :
    ∀ {d f out}, SFunc.RunP P fs sevm d f out → ZeroSlots K sevm.currentTarget d →
      ZeroSlots K sevm.currentTarget (Outcome.devm out) := by
  apply runP_zero_of_children fork (fun step => (steps step).toRun) observations
  intro d d' x xl step _ _ zero
  exact exec_zero_of_committed_child fork (code step) (steps step) (children step) zero

/-- Entry-zero, halted form of `runP_zero_of_committed_children`, with no
obligation for childless, static or discarded recursive execution. -/
theorem progRunP_zero_of_committed_children
    {Q : ∀ pc sevm d out, Exec pc sevm d out → Prop}
    {K : B256 → Prop} {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (steps : ∀ {d n d'}, P sevm d n d' → Ninst.RunWith Q sevm d n d')
    (observations : ∀ {d n d'}, P sevm d n d' → GuardObs K False sevm d n)
    (code : ∀ {d d' x}, P sevm d (.exec x) d' → x ≠ .staticcall →
      d.getCode sevm.currentTarget ≠ .empty)
    (children : ∀ {d d' x frame resume child raw}, P sevm d (.exec x) d' →
      x ≠ .staticcall → (body : Exec child.pc child.sta child.dyna raw) →
      Q _ _ _ _ body → Xinst.step sevm d x = .spawn frame resume →
      frame.enter = .run child → resume.run (frame.settle raw) = .ok d' →
      ∀ settles : frame.settlementCommits raw = true,
      child.sta.depth < sevm.depth → CoveredFork child.sta.benvStat.fork →
      ZeroSlots K sevm.currentTarget child.dyna →
      ZeroSlots K sevm.currentTarget (Execution.committedPost raw
        (Frame.raw_commits_of_settlementCommits settles)))
    (run : SProg.RunP P fs sevm pre post) (zero : ZeroSlots K sevm.currentTarget pre) :
    ZeroSlots K sevm.currentTarget post := by
  obtain ⟨f, _, actual⟩ := run
  exact runP_zero_of_committed_children fork steps observations code children actual zero

end Blanc.Lift.WriteSite
