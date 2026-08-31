-- ForwardCall.lean : crossing a `CALL`, forward.
--
-- `Blanc/Forward.lean` builds `Ninst.RunCompiled` derivations for every
-- instruction whose step is childless.  A `CALL` is not one of those: its step
-- outcome is a `.spawn`, its premise is genuinely existential in the child slot
-- (`Ninst.RunCompiled`'s `∃ xl, xl.Filled`), and the successor state is what
-- `Resume.run` makes of whatever the child settled at.  That is the one thing
-- the forward layer could not do, and this module is it.
--
-- Three things carry the weight, and each is small on its own.
--
-- * **The child comes from totality, never from a premise.**  Jaune's `exec` is
--   total and fuel-free (`Jaune/Sufficiency.lean`), `Blanc/Semantics.lean`'s
--   `exec_iff_exec_eq` is bidirectional for a general `Execution`, and
--   `Xlot.filled_exec` fills the slot for *any* machine.  So the slot obligation
--   an external call carries -- the one a proof about arbitrary callee bytecode
--   would normally have to assume away -- is discharged here by a theorem, at
--   `exec cevm`, with no premise about the callee at all.  Nothing below says
--   the child succeeds, terminates quickly, or behaves; it says only that its
--   derivation exists, which is what the caller then case-splits on.
-- * **The resume is characterised, not unfolded at the call site.**
--   `Resume.run (.call parent oi os)` has exactly three outcomes, and each is
--   one lemma: the settle propagated an error, the child settled with an error
--   set, the child settled clean.  The middle one is where the parent *keeps its
--   own warm sets* -- `incorporateChildOnError` copies state, transient storage,
--   created accounts, return data and gas and nothing else -- which is what
--   makes a post-`CALL` worst case deterministic rather than callee-controlled.
-- * **`value = 0` collapses the `.call` arm.**  Blanc's callbacks forward no
--   value, and at `value = 0` the new-account charge, the transfer charge and
--   the stipend are all zero, the static-context assertion passes on its right
--   disjunct, and the balance short-circuit `senderBal < 0` is unreachable.
--   What is left is one `min` and one `except64th`, which is the whole EIP-150
--   content at this altitude.  The nonzero-value case is not stated: no Blanc
--   contract needs it, and an unused generalisation of a lemma this shape is a
--   maintenance surface, not a capability.
--
-- Nothing here is contract-specific and nothing here mentions a `Func`: this is
-- the `Ninst`/`Xinst` altitude, and the walk that consumes it lives in a
-- contract-owned module.
--
-- The import is `Blanc/Reverts.lean` rather than `Blanc/Forward.lean` so that a
-- caller building a `Func.RunCompiledTo` walk has both layers from one import;
-- `Reverts.lean` imports `Forward.lean`, so nothing is duplicated.

import Blanc.Reverts

namespace Blanc

open Jaune

/-- A successful outcome-generalized walk is the ordinary successful walk.
This is the inverse needed by constructive callers after a prefix was phrased
uniformly over success and revert outcomes. -/
theorem Func.RunCompiled.of_runCompiledTo_ok {fs : List Func} {sevm : Sevm}
    {devm devm' : Devm} {f : Func}
    (h : Func.RunCompiledTo fs sevm devm f (.ok devm')) :
    Func.RunCompiled fs sevm devm f devm' := by
  generalize hx : Except.ok devm' = ex at h
  induction h with
  | zero h_room h_pop _ ih => exact .zero h_room h_pop (ih hx)
  | succ h_ne h_room h_pop _ ih => exact .succ h_ne h_room h_pop (ih hx)
  | last h_lin => cases hx; exact .last h_lin
  | next h_n _ ih => exact .next h_n (ih hx)
  | call h_get h_room h_burn _ ih => exact .call h_get h_room h_burn (ih hx)

/-! ## The spawn premise, discharged by totality

`Ninst.RunCompiled sevm devm (.exec x) devm'` unfolds to
`∃ xl, xl.Filled ∧ ∀ pc, Ninst.StepRun pc sevm devm (.exec x) xl (.ok devm')`.
For a childless instruction the slot is `.none` and `Filled` is `True`; for a
spawning one it is a real obligation, and these three lemmas are the three ways
to meet it. -/

/-- A spawning instruction whose frame **enters**: the slot is filled at
`exec cevm` by `Xlot.filled_exec`, and the successor is whatever `Resume.run`
makes of the settle.

This is the arc's crossing lemma.  Read the premises: `h_step` is about the
parent's own state, `h_enter` is about the message the parent built, and
`h_res` is about the resume.  **There is no premise about the child.**  Its
derivation is `exec cevm`, an opaque term the caller case-splits on. -/
lemma Ninst.runCompiled_exec_run {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {cevm : Evm} {devm' : Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .run cevm)
    (h_res : rsm.run (f.settle (exec cevm)) = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec x) devm' := by
  refine ⟨.some ⟨cevm, exec cevm⟩, Xlot.filled_exec cevm, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨_, RunFrame.of_run h_enter, h_res.symm⟩

/-- A successful compiled instruction step whose recursive execution slot is
definitionally empty.  This is stronger than `RunCompiled` and is the common
boundary needed by callers that reason about raw child-frame chronology. -/
def Ninst.ChildlessRunCompiled
    (sevm : Sevm) (pre : Devm) (instruction : Ninst) (post : Devm) : Prop :=
  ∀ pc, Ninst.StepRun pc sevm pre instruction .none (.ok post)

/-- Forgetting childlessness yields the ordinary compiled-step witness. -/
theorem Ninst.ChildlessRunCompiled.toRunCompiled
    {sevm : Sevm} {pre post : Devm} {instruction : Ninst}
    (run : Ninst.ChildlessRunCompiled sevm pre instruction post) :
    Ninst.RunCompiled sevm pre instruction post :=
  ⟨.none, trivial, run⟩

/-- A syntactically non-external compiled instruction necessarily uses the
empty recursive slot. -/
theorem Ninst.RunCompiled.childless_of_not_exec
    {sevm : Sevm} {pre post : Devm} {instruction : Ninst}
    (run : Ninst.RunCompiled sevm pre instruction post)
    (notExec : ∀ operation : Xinst, instruction ≠ .exec operation) :
    Ninst.ChildlessRunCompiled sevm pre instruction post := by
  rcases run with ⟨slot, filled, steps⟩
  cases instruction with
  | reg operation =>
      have stepRun := steps 0
      rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at stepRun
      rw [stepRun.1] at steps
      exact steps
  | push bytes length =>
      have stepRun := steps 0
      rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at stepRun
      rw [stepRun.1] at steps
      exact steps
  | exec operation => exact (notExec operation rfl).elim

/-- A spawning instruction whose frame resolves synchronously has a childless
compiled-step witness.  Enabled precompiles are the principal consumer. -/
theorem Ninst.childlessRunCompiled_exec_doneFrame
    {sevm : Sevm} {pre post : Devm} {operation : Xinst}
    {frame : Frame} {resume : Resume}
    {settled : Except (EvmError × State × AdrSet × Tra) Devm}
    (step : Xinst.step sevm pre operation = .spawn frame resume)
    (enter : frame.enter = .done settled)
    (resumeOk : resume.run settled = .ok post) :
    Ninst.ChildlessRunCompiled sevm pre (.exec operation) post := by
  intro pc
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm pre operation) _ _
  rw [step]
  exact ⟨settled, RunFrame.of_done enter, resumeOk.symm⟩

/-- A spawning instruction whose frame **does not enter** — the value transfer
failed, or the callee is a precompile.  No child machine exists, the slot is
`.none`, and `Filled` is `True`. -/
lemma Ninst.runCompiled_exec_doneFrame {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {devm' : Devm}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .done r) (h_res : rsm.run r = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec x) devm' := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨r, RunFrame.of_done h_enter, h_res.symm⟩

/-- Forward form of the precompile branch of `Frame.enter`: after a successful
value-transfer preparation, an enabled precompile answers synchronously and
there is no child execution slot. -/
lemma Frame.enter_eq_done_executePrecomp {f : Frame} {benv : Benv} {adr : Adr}
    (h_bt : f.inner.benvAfterTransfer = .ok benv)
    (h_ca : (f.inner.withBenv benv).codeAddress = some adr)
    (h_pre :
      (!((f.inner.withBenv benv).disablePrecompiles) &&
        decide ((f.inner.withBenv benv).benv.stat.rules.isPrecomp adr)) = true) :
    f.enter = .done
      (f.settle (executePrecomp (initEvm (f.inner.withBenv benv)) adr)) := by
  unfold Frame.enter
  rw [h_bt]
  unfold executeCode.enter
  simp only [h_ca, h_pre, if_true]

/-- A call-type instruction that never spawns at all: `Xinst.step` itself
returned `.done`.  The depth-1024 arm below is the case this exists for. -/
lemma Ninst.runCompiled_exec_done {sevm : Sevm} {devm : Devm} {x : Xinst}
    {devm' : Devm} (h_step : Xinst.step sevm devm x = .done (.ok devm')) :
    Ninst.RunCompiled sevm devm (.exec x) devm' := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨rfl, rfl⟩

/-- `Devm.popToAdr`, evaluated forward — the mirror of `Blanc/Forward.lean`'s
`Devm.popToNat_eq_ok`, needed because a `CALL`'s second operand is an address.
It lives here rather than there for **A4**'s reason: `Blanc/Forward.lean`'s
elaboration row is the one this arc may not raise. -/
lemma Devm.popToAdr_eq_ok {x : B256} {s : List B256} {devm : Devm}
    (h : devm.stack = x :: s) :
    devm.popToAdr =
      .ok ⟨x.toAdr, devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
  rw [Devm.popToAdr_def, Devm.pop_eq_ok h]
  rfl

/-! ## Reading storage without deciding warmth

`Blanc/Forward.lean` splits `SLOAD` into a cold rule and a warm rule, because
the cold one moves the base state (the key joins the accessed set) and the warm
one does not.  A walk that has to be *correct whichever way the frame came in*
therefore forks, and a trunk with two such reads forks four ways.

The rule below is the fork, taken once and packaged.  Its successor's base is a
**variable** pinned by an `if`, so one derivation covers both cases and the
consumer reads what it needs off `h_base` — which for a continuation is only
ever membership, `getStorVal`, and the machine fields the `setMach` names.
`h_cost` is the same `if`, so the charge is symbolic and the caller bounds it.

Contract-agnostic, and here rather than in `Blanc/Forward.lean` for **A4**'s
reason: that module's elaboration row is the one this arc may not raise. -/

/-- `SLOAD`, warmth left open.  The successor's base is whichever of the two
states the frame's own accessed set selects, and the charge is the matching
schedule constant; both are handed to the caller as equations.

Neither `if` is decided here, so nothing about the frame's accessed set is
assumed — which is what lets a single walk serve a statement with no warmth
premise. -/
lemma Ninst.runCompiled_sload_of {sevm : Sevm} {devm base : Devm} {k v : B256}
    {s : List B256} {c G : Nat} (h_stk : devm.stack = k :: s)
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base)
    (h_cost : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then gasWarmAccess else gasColdSload) = c)
    (h_val : devm.getStorVal sevm.currentTarget k = v)
    (h_gas : devm.gasLeft = G + c) (h_room : s.length < 1024) :
    Ninst.RunCompiled sevm devm (.reg .sload)
      (base.setMach ⟨v :: s, devm.memory, G⟩) := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base h_cost
    subst h_base; subst h_cost
    exact Ninst.runCompiled_sload_warm h_stk h h_val h_gas h_room
  · rw [if_neg h] at h_base h_cost
    subst h_base; subst h_cost
    exact Ninst.runCompiled_sload_cold h_stk h h_val h_gas h_room

/-- The key an `SLOAD` read is warm afterwards, whichever arm was taken. -/
lemma mem_accessedStorageKeys_sload_of {sevm : Sevm} {devm base : Devm}
    {k : B256}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base) :
    (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ base.accessedStorageKeys := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; exact h
  · rw [if_neg h] at h_base; subst h_base
    exact Std.HashSet.mem_insert_self

/-- A key already warm stays warm across an unrelated `SLOAD`. -/
lemma mem_accessedStorageKeys_sload_of_mem {sevm : Sevm} {devm base : Devm}
    {k k' : B256} {a : Adr}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base)
    (h_mem : (⟨a, k'⟩ : Adr × B256) ∈ devm.accessedStorageKeys) :
    (⟨a, k'⟩ : Adr × B256) ∈ base.accessedStorageKeys := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; exact h_mem
  · rw [if_neg h] at h_base; subst h_base
    exact Std.HashSet.mem_insert.mpr (Or.inr h_mem)

/-- The storage a `SLOAD` reads is the storage it leaves: the accessed set is
`meta`, the values are `world`. -/
lemma getStorVal_sload_of {sevm : Sevm} {devm base : Devm} {k : B256}
    {a : Adr} {k' : B256}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base) :
    base.getStorVal a k' = devm.getStorVal a k' := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; rfl
  · rw [if_neg h] at h_base; subst h_base; rfl

/-- …and so is the original storage the `SSTORE` pricing compares against. -/
lemma refundCounter_sload_of {sevm : Sevm} {devm base : Devm} {k : B256}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base) :
    base.refundCounter = devm.refundCounter := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; rfl
  · rw [if_neg h] at h_base; subst h_base; rfl

/-- A read emits no log. -/
lemma logs_sload_of {sevm : Sevm} {devm base : Devm} {k : B256}
    (h_base : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then devm else addAccessedStorageKey devm sevm.currentTarget k) = base) :
    base.logs = devm.logs := by
  by_cases h : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
  · rw [if_pos h] at h_base; subst h_base; rfl
  · rw [if_neg h] at h_base; subst h_base; rfl

/-- The charge is between the two schedule constants, whichever arm fires. -/
lemma le_sload_cost_of {sevm : Sevm} {devm : Devm} {k : B256} {c : Nat}
    (h_cost : (if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
      then gasWarmAccess else gasColdSload) = c) :
    gasWarmAccess ≤ c ∧ c ≤ gasColdSload := by
  subst h_cost; split <;> exact ⟨by decide, by decide⟩

/-- State-dependent charge selected by one `SLOAD`. -/
def sloadCost (sevm : Sevm) (base : Devm) (key : B256) : Nat :=
  if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      base.accessedStorageKeys then
    gasWarmAccess
  else
    gasColdSload

/-- Meta-state after one `SLOAD`, including a newly warmed key when needed. -/
def afterSload (sevm : Sevm) (base : Devm) (key : B256) : Devm :=
  if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      base.accessedStorageKeys then
    base
  else
    addAccessedStorageKey base sevm.currentTarget key

private lemma addAccessedStorageKey_setMach_setMach_selected
    {base : Devm} {target : Adr} {key : B256} {mach mach' : Mach} :
    (addAccessedStorageKey (base.setMach mach) target key).setMach mach' =
      (addAccessedStorageKey base target key).setMach mach' := rfl

/-- One exact `SLOAD` whose warm/cold choice stays inside neutral carrier
definitions.  Unlike the CPS rule below, this needs only the actually selected
charge and is therefore suitable for minimal-gas theorems. -/
theorem Ninst.runCompiled_sload_selected
    {sevm : Sevm} {base : Devm} {key value : B256}
    {stack : List B256} {memory : Mem} {G : Nat}
    (hvalue : base.getStorVal sevm.currentTarget key = value)
    (hroom : stack.length < 1024) :
    Ninst.RunCompiled sevm
      (base.setMach
        ⟨key :: stack, memory, G + sloadCost sevm base key⟩)
      sload
      ((afterSload sevm base key).setMach
        ⟨value :: stack, memory, G⟩) := by
  by_cases hwarm :
      (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
        base.accessedStorageKeys
  · rw [sloadCost, if_pos hwarm, afterSload, if_pos hwarm]
    exact Ninst.runCompiled_sload_warm
      (k := key) (v := value) (s := stack) (G := G)
      rfl hwarm hvalue
      (by simp only [Devm.gasLeft_setMach, gasWarmAccess])
      hroom
  · rw [sloadCost, if_neg hwarm, afterSload, if_neg hwarm]
    simpa only [addAccessedStorageKey_setMach_setMach_selected,
      Devm.memory_setMach] using
      (Ninst.runCompiled_sload_cold
        (sevm := sevm)
        (devm := base.setMach
          ⟨key :: stack, memory, G + gasColdSload⟩)
        (k := key) (v := value) (s := stack) (G := G)
        rfl hwarm
        (by simpa only [Devm.getStorVal_setMach] using hvalue)
        (by simp only [Devm.gasLeft_setMach, gasColdSload])
        hroom)

/-- Exact selected warm/cold charge of one `SSTORE`. -/
def sstoreCost (sevm : Sevm) (devm : Devm) (key value : B256) : Nat :=
  (if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      devm.accessedStorageKeys then 0 else gasColdSload) +
    sstoreValueCost (getOrigStorVal sevm sevm.currentTarget key)
      (devm.getStorVal sevm.currentTarget key) value

/-- Meta/world state after one selected warm/cold `SSTORE`. -/
def afterSstore (sevm : Sevm) (devm : Devm)
    (key value : B256) : Devm :=
  let accessed :=
    if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
        devm.accessedStorageKeys then devm
    else addAccessedStorageKey devm sevm.currentTarget key
  (accessed.withRefundCounter
      (sstoreNewRefundCounter value
        (getOrigStorVal sevm sevm.currentTarget key)
        (devm.getStorVal sevm.currentTarget key) devm.refundCounter)).setStorVal
    sevm.currentTarget key value

/-- One exact `SSTORE` whose warm/cold choice stays inside neutral carrier
definitions. The caller supplies the real EIP-2200 sentry and static-context
premises; the successor exposes the selected access-set and refund update. -/
theorem Ninst.runCompiled_sstore_selected
    {sevm : Sevm} {devm : Devm} {key value : B256}
    {stack : List B256} {G : Nat}
    (hstack : devm.stack = key :: value :: stack)
    (hsentry : gCallStipend < devm.gasLeft)
    (hstatic : sevm.isStatic = false)
    (hgas : devm.gasLeft = G + sstoreCost sevm devm key value) :
    Ninst.RunCompiled sevm devm sstore
      ((afterSstore sevm devm key value).setMach
        ⟨stack, devm.memory, G⟩) := by
  by_cases hwarm :
      (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
        devm.accessedStorageKeys
  · simp only [sstoreCost, if_pos hwarm, Nat.zero_add,
      afterSstore] at hgas ⊢
    exact Ninst.runCompiled_sstore_warm hstack hwarm hsentry hstatic
      rfl rfl hgas
  · simp only [sstoreCost, if_neg hwarm, afterSstore] at hgas ⊢
    exact Ninst.runCompiled_sstore_cold hstack hwarm hsentry hstatic
      rfl rfl hgas

@[simp] theorem sstoreCost_setMach
    {sevm : Sevm} {base : Devm} {mach : Mach} {key value : B256} :
    sstoreCost sevm (base.setMach mach) key value =
      sstoreCost sevm base key value := rfl

private lemma accessedStorageKeys_setMach_selected
    {base : Devm} {mach : Mach} :
    (base.setMach mach).accessedStorageKeys =
      base.accessedStorageKeys := rfl

private lemma afterSstore_setMach_setMach_selected
    {sevm : Sevm} {base : Devm} {mach mach' : Mach}
    {key value : B256} :
    (afterSstore sevm (base.setMach mach) key value).setMach mach' =
      (afterSstore sevm base key value).setMach mach' := by
  unfold afterSstore
  by_cases hwarm :
      (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
        base.accessedStorageKeys
  · simp only [accessedStorageKeys_setMach_selected,
      Devm.getStorVal_setMach, Devm.setMach_refundCounter,
      hwarm, if_pos]
    rfl
  · simp only [accessedStorageKeys_setMach_selected,
      Devm.getStorVal_setMach, Devm.setMach_refundCounter,
      hwarm]
    rfl

/-- The selected warm/cold `SSTORE` rule specialized to a caller-owned
machine image.  The selected cost and successor remain phrased over the
stable base state, so later instructions do not inherit a machine-register
term in either one. -/
theorem Ninst.runCompiled_sstore_selected_setMach
    {sevm : Sevm} {base : Devm} {key value : B256}
    {stack : List B256} {memory : Mem} {G : Nat}
    (hsentry : gCallStipend < G + sstoreCost sevm base key value)
    (hstatic : sevm.isStatic = false) :
    Ninst.RunCompiled sevm
      (base.setMach
        ⟨key :: value :: stack, memory,
          G + sstoreCost sevm base key value⟩)
      sstore
      ((afterSstore sevm base key value).setMach
        ⟨stack, memory, G⟩) := by
  simpa only [sstoreCost_setMach,
    afterSstore_setMach_setMach_selected, Devm.memory_setMach] using
    (Ninst.runCompiled_sstore_selected
      (sevm := sevm)
      (devm := base.setMach
        ⟨key :: value :: stack, memory,
          G + sstoreCost sevm base key value⟩)
      (key := key) (value := value) (stack := stack) (G := G)
      rfl
      (by simpa only [Devm.gasLeft_setMach] using hsentry)
      hstatic
      (by simp only [Devm.gasLeft_setMach, sstoreCost_setMach]))

/-! ### The two storage steps, in continuation-passing form

`Ninst.runCompiled_sload_of` above and `Blanc/Forward.lean`'s
`Ninst.runCompiled_sstore_warm` both hand the caller a successor whose base and
whose charge are *terms*, and a walk that meets several of them accumulates
those terms into a state nobody can write down.  The two rules below are the
same steps stated so that the successor's base, its charge and its gas account
arrive in the continuation as **variables with equations** — everything a later
instruction needs to know about them, and nothing else.

That is what makes a trunk with two warmth-unknown reads and two stores a
*single* walk instead of a four-way fork over unwritable states, and it is why
a caller never has to name a `Devm` that a rule produced.

Neither is exhaustive about the charge: both bound it by the schedule's worst
case, which is **A3**'s decision — a premise buying exactness would be a premise
about the frame's history, and the statements this serves have none. -/

/-- `SLOAD` as a walk step, with warmth, charge and successor handed to the
continuation.  `h_gas` is the worst case, so no warmth premise is needed to know
the frame can pay. -/
lemma Func.runCompiledTo_sload_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k v : B256} {s : List B256} {M : Mem} {rest : Func} {ex : Execution}
    (h_stk : devm.stack = k :: s) (h_room : s.length < 1024)
    (h_val : devm.getStorVal sevm.currentTarget k = v)
    (h_mem : devm.memory = M)
    (h_gas : gasColdSload ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ base.accessedStorageKeys →
      (∀ p : Adr × B256, p ∈ devm.accessedStorageKeys →
        p ∈ base.accessedStorageKeys) →
      (∀ (a : Adr) (k' : B256), base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.refundCounter = devm.refundCounter →
      base.logs = devm.logs →
      gasWarmAccess ≤ c → c ≤ gasColdSload →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (base.setMach ⟨v :: s, M, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next Ninst.sload rest) ex := by
  subst h_val; subst h_mem
  set base : Devm :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then devm else addAccessedStorageKey devm sevm.currentTarget k with h_base
  set c : Nat :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then gasWarmAccess else gasColdSload with h_c
  have h_lo : gasWarmAccess ≤ c := (le_sload_cost_of h_c.symm).1
  have h_hi : c ≤ gasColdSload := (le_sload_cost_of h_c.symm).2
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_sload_of (base := base) (c := c) (G := devm.gasLeft - c)
      h_stk h_base.symm h_c.symm rfl (by omega) h_room) ?_
  exact h_next base c (devm.gasLeft - c)
    (mem_accessedStorageKeys_sload_of h_base.symm)
    (fun _ hp => mem_accessedStorageKeys_sload_of_mem h_base.symm hp)
    (fun _ _ => getStorVal_sload_of h_base.symm)
    (fun _ => by rw [h_base]; split <;> rfl)
    (fun _ => by rw [h_base]; split <;> rfl)
    (refundCounter_sload_of h_base.symm) (logs_sload_of h_base.symm)
    h_lo h_hi (by omega)

/-- `SSTORE` on a **warm** key as a walk step.  The written value, the untouched
keys, the unmoved accessed set, the charge's bound and the gas account arrive in
the continuation; the base state itself never has to be named.

Warm only, deliberately: every store this serves is preceded by a read of the
same key in the same frame, so the cold arm is unreachable rather than
unhandled. -/
lemma Func.runCompiledTo_sstore_warm_step {fs : List Func} {sevm : Sevm}
    {devm : Devm} {k v : B256} {s : List B256} {M : Mem} {rest : Func}
    {ex : Execution}
    (h_stk : devm.stack = k :: v :: s)
    (h_warm : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys)
    (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_gas : gasStorageSet ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      base.getStorVal sevm.currentTarget k = v →
      (∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
        base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.logs = devm.logs →
      c ≤ gasStorageSet →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (base.setMach ⟨s, M, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next Ninst.sstore rest) ex := by
  subst h_mem
  have h_bound : sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v ≤ gasStorageSet := by
    rw [sstoreValueCost]; split_ifs <;> decide
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_sstore_warm (c := sstoreValueCost
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      (G := devm.gasLeft - sstoreValueCost
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      h_stk h_warm (by simp only [gCallStipend, gasStorageSet] at *; omega)
      h_static rfl rfl (by omega)) ?_
  refine h_next _ _ _ ?_ (fun a k' h_ne => ?_) (fun a => ?_)
    (fun a => ?_) rfl rfl h_bound (by omega)
  · show (Devm.getStor _ sevm.currentTarget).get k = v
    rw [setStorVal_getStor_self, Stor.get_set_self]
  · by_cases h_adr : sevm.currentTarget = a
    · subst h_adr
      have h_key : k ≠ k' := fun h => h_ne (by rw [h])
      show (Devm.getStor _ sevm.currentTarget).get k' = _
      rw [setStorVal_getStor_self, Stor.get_set_ne _ h_key]
      rfl
    · show (Devm.getStor _ a).get k' = _
      have h_off : Devm.getStor
          ((devm.withRefundCounter (sstoreNewRefundCounter v
            (getOrigStorVal sevm sevm.currentTarget k)
            (devm.getStorVal sevm.currentTarget k)
            devm.refundCounter)).setStorVal sevm.currentTarget k v) a
            = Devm.getStor devm a := by
        simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
          Devm.setWorld, State.setStorVal]
        simp only [Devm.state, State.get_set_ne _ h_adr]
        rfl
      rw [h_off]
      rfl
  · have hbc := State.setStorVal_balCodeEq devm.state sevm.currentTarget k v
    exact (congrArg Prod.fst (congrFun hbc a)).symm
  · have hbc := State.setStorVal_balCodeEq devm.state sevm.currentTarget k v
    exact (congrArg Prod.snd (congrFun hbc a)).symm

/-! ## The memory window, in the shapes a walk's obligations arrive in

`func_run` hands every memory-expansion charge straight back — the image is a
chain of writes the tactic has no arithmetic for.  The three lemmas below are
what a caller closes those obligations with: the size of an image after one
word-write, the extension charge as a function of that size, and the fact that
*reading* a window the image already covers leaves the image alone.

The last is what keeps a `LOG` from doubling the state: `Mem.read` returns
`⟨μ.data, memExtSize …⟩`, which is `μ` again exactly when the window fits, and
structure eta makes that an equation the walk can rewrite with rather than a new
image every reader has to carry. -/

/-- The size of an image after writing one word: unchanged when the window
already fits, and rounded up to the word above otherwise.

`Mem.write` matches on the payload being non-empty, and `B256.toBytes` is not a
literal, so this needs the same `rcases` that `Mem.size_write_word` does. -/
lemma Mem.size_write_word_at {N : Mem} {i : Nat} {w : B256} :
    (N.write i w.toBytes).size = if i + 32 ≤ N.size then N.size else ceil32 (i + 32) := by
  rcases hb : w.toBytes with _ | ⟨b, bs⟩
  · exact absurd (hb ▸ B256.length_toBytes w) (by simp)
  · have hlen : (b :: bs).length = 32 := hb ▸ B256.length_toBytes w
    simp only [Mem.write, hlen]
    split_ifs <;> rfl

/-- `Mem.size_write_word_at` for an arbitrary non-empty payload: the size after
a write is unchanged when the window already fits and rounds up otherwise. -/
lemma Mem.size_write_cons {N : Mem} {n : Nat} {x : UInt8} {xs : Bytes} :
    (N.write n (x :: xs)).size =
      if n + (x :: xs).length ≤ N.size then N.size
      else ceil32 (n + (x :: xs).length) := by
  simp only [Mem.write]
  split_ifs <;> rfl

/-- The extension charge for a window, as a function of the image's size alone.
Stated with the charge as a parameter, and applied with `exact` rather than
`rw`: a walk's window index arrives as `(k * 32 : B256).toNat` rather than a
literal, which unifies but does not *match*. -/
lemma Devm.extCost_of_size {devm : Devm} {S : List B256} {N : Mem} {G : Nat}
    {i sz n e : Nat} (h : N.size = n)
    (he : calculateMemoryGasCost (memExtSize n i sz)
      - calculateMemoryGasCost n = e) :
    (devm.setMach ⟨S, N, G⟩).extCost [⟨i, sz⟩] = e := by
  simp only [Devm.extCost, Devm.memory_setMach, memExtsSize, h, he]

/-- The same, summed with the instruction's fixed part — the shape every charge
premise outside `MSTORE` arrives in. -/
lemma Devm.extCost_add_of_size {devm : Devm} {S : List B256} {N : Mem} {G : Nat}
    {i sz n a e : Nat} (h : N.size = n)
    (he : a + (calculateMemoryGasCost (memExtSize n i sz)
      - calculateMemoryGasCost n) = e) :
    a + (devm.setMach ⟨S, N, G⟩).extCost [⟨i, sz⟩] = e := by
  simp only [Devm.extCost, Devm.memory_setMach, memExtsSize, h, he]

/-- Reading a window the image already covers returns the image unchanged. -/
lemma Mem.read_snd_eq_self {N : Mem} {i sz : Nat}
    (h : memExtSize N.size i sz = N.size) : (N.read i sz).2 = N := by
  show N.extend i sz = N
  simp only [Mem.extend, h]

/-- A window inside a word-aligned image extends nothing.  The alignment
premise is real: an access to an unaligned image is rounded up whether or not
the window is covered. -/
lemma memExtSize_of_le {n i sz : Nat} (h32 : n % 32 = 0) (hw : i + sz ≤ n) :
    memExtSize n i sz = n := by
  unfold memExtSize
  split_ifs with h
  · rfl
  · have h1 : ceilDiv (i + sz) 32 ≤ ceilDiv n 32 := by
      simp only [ceilDiv]
      rw [if_pos h32]
      split_ifs with h2 <;> omega
    rw [Nat.max_eq_left h1]
    simp only [ceilDiv]
    rw [if_pos h32]
    omega

/-- The window charge vanishes for a window a word-aligned image covers — the
symbolic-image sibling of `Devm.extCost_of_size`, for walks over a memory
*variable* whose size is only bounded, never computed. -/
lemma Devm.extCost_zero_of_le {devm : Devm} {S : List B256} {N : Mem} {G : Nat}
    {i sz : Nat} (h32 : N.size % 32 = 0) (hw : i + sz ≤ N.size) :
    (devm.setMach ⟨S, N, G⟩).extCost [⟨i, sz⟩] = 0 := by
  simp only [Devm.extCost, Devm.memory_setMach, memExtsSize,
    memExtSize_of_le h32 hw, Nat.sub_self]

/-- A write inside the image leaves the size alone. -/
lemma Mem.size_write_of_le {N : Mem} {n : Nat} {bs : Bytes}
    (h : n + bs.length ≤ N.size) : (N.write n bs).size = N.size := by
  rcases bs with _ | ⟨x, xs⟩
  · rfl
  · rw [Mem.size_write_cons,
      if_pos (by simp only [List.length_cons] at h ⊢; omega)]

/-- Reading a covered window of a word-aligned image leaves the size alone. -/
lemma Mem.size_read_snd_of_le {N : Mem} {i sz : Nat} (h32 : N.size % 32 = 0)
    (hw : i + sz ≤ N.size) : ((N.read i sz).2).size = N.size := by
  rw [Mem.read_snd_eq_self (memExtSize_of_le h32 hw)]

/-- The length of a `sliceD` is the width asked for, whatever the source: a
short source is padded with the default rather than truncating the result.
This is what lets a copy instruction's payload be keyed on its *length* when
its head cannot be matched. -/
lemma _root_.List.length_sliceD {ξ : Type u} (xs : List ξ) (m n : Nat) (d : ξ) :
    (xs.sliceD m n d).length = n := List.takeD_length _ _ _

/-- Expansion preserves word alignment: a window opened over an aligned image
leaves an aligned image.  The neighbouring lemmas all *consume* an
`N.size % 32 = 0` premise and none of them produces one, so a walk that crosses
two windows had no way to carry alignment past the first. -/
lemma memExtSize_mod_32 {n i sz : Nat} (h32 : n % 32 = 0) :
    memExtSize n i sz % 32 = 0 := by
  simp only [memExtSize]
  split_ifs with h
  · exact h32
  · omega

/-- The other half of `memExtSize_of_le`: a window that does not fit rounds the
image up to `ceil32` of its far edge — the very rounding `Mem.write` applies
when it grows.  Together with `memExtSize_of_le` this pins `memExtSize`
completely, and it is what lets a `Mem.write` size law be stated in the
`memExtSize` vocabulary the charge is computed in.

Alignment of `n` is deliberately *not* a premise: in the `sz ≠ 0` branch the
value is `32 * max (ceilDiv n 32) (ceilDiv (i + sz) 32)` and `ceilDiv · 32` is
monotone, so `n ≤ i + sz` alone forces the max.  `0 < sz` is not decoration: at
`sz = 0` the expansion is the identity whatever `i` is, so `n = 0, i = 1`
refutes the conclusion. -/
lemma memExtSize_eq_ceil32_of_le {n i sz : Nat}
    (hsz : 0 < sz) (h : n ≤ i + sz) : memExtSize n i sz = ceil32 (i + sz) := by
  have hne : ¬ sz = 0 := by omega
  simp only [memExtSize, if_neg hne]
  have hmax : max (ceilDiv n 32) (ceilDiv (i + sz) 32) = ceilDiv (i + sz) 32 := by
    refine Nat.max_eq_right ?_
    simp only [ceilDiv]
    split_ifs <;> omega
  rw [hmax]
  unfold ceil32 ceilDiv
  split <;> split <;> omega

/-- `Mem.size_write_cons` keyed on the payload's **length** rather than on its
head.  This is the member of the family a forwarding walk actually needs:
`Mem.size_write_word_at` fixes the payload at one word; `Mem.size_write_cons` is
variable-length but demands the payload be *syntactically* `x :: xs`, and a
payload arriving as `List.sliceD _ _ len _` has no head to match on;
`Mem.size_write_of_le` accepts any payload but answers only on the branch where
the window already fits. -/
lemma Mem.size_write_of_length {N : Mem} {n len : Nat} {bs : Bytes}
    (hlen : bs.length = len) (hpos : 0 < len) :
    (N.write n bs).size =
      if n + len ≤ N.size then N.size else ceil32 (n + len) := by
  rcases bs with _ | ⟨x, xs⟩
  · exact absurd hpos (by rw [← hlen]; simp)
  · subst hlen
    exact Mem.size_write_cons

/-- **The variable-length write size law**, in the vocabulary the *charge* is
computed in.

Keyed on the payload's length rather than its head, so a `sliceD` payload
applies; and keyed on the image's size as a *parameter* rather than as a
projection in the conclusion.  That second choice is this file's own idiom
(see `Devm.extCost_of_size`): a walk's window index arrives as
`(k * 32 : B256).toNat` rather than a literal, which unifies but does not
match, so a conclusion mentioning `N.size` would force the caller to rewrite a
projection out of a term it cannot name.  With `n` a parameter the caller
supplies `hN` however it likes and the conclusion is already in the charge's
vocabulary. -/
lemma Mem.size_write_of_size {N : Mem} {bs : Bytes} {i n len : Nat}
    (hN : N.size = n) (h32 : n % 32 = 0) (hlen : bs.length = len) :
    (N.write i bs).size = memExtSize n i len := by
  subst hN
  rcases bs with _ | ⟨x, xs⟩
  · have hzero : len = 0 := hlen.symm
    subst hzero
    rfl
  · have hpos : 0 < len := by rw [← hlen]; simp
    rw [Mem.size_write_of_length hlen hpos]
    by_cases hfit : i + len ≤ N.size
    · rw [if_pos hfit, memExtSize_of_le h32 hfit]
    · rw [if_neg hfit, memExtSize_eq_ceil32_of_le (by omega) (by omega)]

/-- **Control** — the memory-size premise the spike's proxy walk carried as a
*hypothesis* is now derivable.  This is the two-window shape: the image is
already the result of one window (`memExtSize 0 0 cds`) and a second copy writes
over it, so the conclusion nests.  Nesting is instantiation, not a new law —
`Mem.size_write_of_size` concludes `= memExtSize n i len` and `n` is
instantiated to the inner window.  What the walk could *not* previously supply
is the alignment of that inner image: every other member of this family
consumes a `% 32 = 0` premise and none produces one, which is why
`memExtSize_mod_32` is the ingredient that completes the family rather than
duplicating it. -/
theorem control_two_window_memory_premise_derivable
    {N : Mem} {cs : Bytes} {cds rds : Nat}
    (hN : N.size = memExtSize 0 0 cds) (hc : cs.length = rds) :
    (N.write 0 cs).size = memExtSize (memExtSize 0 0 cds) 0 rds :=
  Mem.size_write_of_size hN (memExtSize_mod_32 (Nat.zero_mod 32)) hc

/-- **Control** — a copy opcode's `sliceD` payload meets the law's length
hypothesis with no premise about the source at all, which is the whole point of
keying the law on the payload's length rather than on its head: a payload
arriving as `List.sliceD _ _ len _` has no head to `rcases` on. -/
theorem control_sliceD_payload_size {N : Mem} {src : Bytes} {i off len n : Nat}
    (hN : N.size = n) (h32 : n % 32 = 0) :
    (N.write i (src.sliceD off len 0)).size = memExtSize n i len :=
  Mem.size_write_of_size hN h32 (List.length_sliceD _ _ _ _)

/-- `setMach` moves no return data. -/
lemma Devm.returnData_setMach {devm : Devm} {m : Mach} :
    (devm.setMach m).returnData = devm.returnData := rfl

/-- `RETURN`, at the outcome relation's altitude — the `.ok` sibling of
`Func.runCompiledTo_rev_of`, with the read-back reduced to its *first*
component exactly as `Func.runCompiled_ret_word` does and for the same
reason. -/
lemma Func.runCompiledTo_ret_word {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i sz : B256} {s : List B256} {out : Bytes} {G e : Nat}
    (h_stk : devm.stack = i :: sz :: s)
    (h_ext : devm.extCost [⟨i.toNat, sz.toNat⟩] = e)
    (h_gas : devm.gasLeft = G + e)
    (h_out : ((devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat sz.toNat).1
      = out) :
    Func.RunCompiledTo fs sevm devm (.last .ret)
      (.ok ((((devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat
        sz.toNat).2).withOutput out)) := by
  subst h_ext
  have h_eq : devm.gasLeft - devm.extCost [⟨i.toNat, sz.toNat⟩] = G := by omega
  refine Func.RunCompiledTo.last ?_
  show Linst.run sevm devm .ret = _
  exact Linst.run_ret_eq_ok h_stk (by omega) (by rw [h_eq]; exact Prod.ext h_out rfl)

/-! ## The two remaining walk steps: `LOG` and `CALLDATACOPY`

Both are in the continuation-passing form the storage steps established, and
each is here for its own reason.

`LOG` moves the *base* — `Devm.addLog` — and its successor's memory image is a
projection out of the state it reads.  Handed to the walk as a term, both would
be carried inside every later state (**F8** of `~/plans/reports/
adversarial-progress-step2.md`); handed to a continuation, the base is a
variable and the image is whatever the caller names.

`CALLDATACOPY`'s charge is affine in the copied length, and `func_run` requires
every charge hint to be a **numeral** (**F10**).  A trunk that forwards a
caller-supplied `bytes` payload therefore cannot walk its copy with the tactic
at all; it applies this between two `func_run` segments, with the charge a
variable and one equation. -/

/-- `MSTORE` as a walk step, with the written image handed to the continuation
as a **variable**.

`func_run` has an `MSTORE` arm and it is the right one for a view: two or three
stores over `Mem.empty` and the image stays small.  It is the wrong one for a
frame that lays out a call's arguments.  There the image is a chain of eight
writes whose payloads are *concrete* — a selector that is a `keccak`, an
address, a length word — so every `whnf` the walk performs on a later state runs
that chain, and the cost per instruction grows with the number of stores before
it (measured: ≈ 0.1 s per node before the layout, ≈ 1.5 s after it).

Naming each image instead keeps every state one write deep, and the caller ends
up with the chain as a list of equations, which is also the shape a memory-image
characterisation wants. -/
lemma Func.runCompiledTo_mstore_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i v : B256} {s : List B256} {c : Nat} {M : Mem} {rest : Func}
    {ex : Execution}
    (h_stk : devm.stack = i :: v :: s)
    (h_mem : devm.memory = M)
    (h_cost : gVerylow + devm.extCost [⟨i.toNat, 32⟩] = c)
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (M' : Mem) (G : Nat), M.write i.toNat v.toBytes = M' →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (devm.setMach ⟨s, M', G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next Ninst.mstore rest) ex := by
  subst h_mem
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of (G := devm.gasLeft - c) (e := devm.extCost
      [⟨i.toNat, 32⟩]) h_stk rfl (by omega) rfl) ?_
  exact h_next _ _ rfl (by omega)

/-- `mstoreAt` over an abstract memory.  The written image remains behind the
continuation boundary instead of becoming a concrete write tower in every
later compiled state. -/
lemma Func.runCompiledTo_mstoreAt
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256} {value word : B256}
    {G pushGas extGas : Nat} {body : Func} {ex : Execution}
    (hpushCost : pushCost (word * 32).toBytes.sig = pushGas)
    (hroom : stack.length < 1023)
    (hext : ∀ (S : List B256) (G' : Nat),
      (base.setMach ⟨S, memory, G'⟩).extCost
        [⟨(word * 32).toNat, 32⟩] = extGas)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory.write (word * 32).toNat value.toBytes, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨value :: stack, memory, G + pushGas + gVerylow + extGas⟩)
      (mstoreAt word +++ body) ex := by
  unfold mstoreAt
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (G := G + gVerylow + extGas) hpushCost
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.runCompiledTo_mstore_step
    (M := memory) (c := gVerylow + extGas) rfl rfl ?_ ?_ ?_
  · rw [hext]
  · simp only [Devm.gasLeft_setMach]
    omega
  · intro memory' G' hmemory hgas
    simp only [Devm.gasLeft_setMach] at hgas
    subst memory'
    have hG' : G' = G := by omega
    subst G'
    simpa only [Devm.setMach_setMach, prepend] using hbody

/-- `LOG n` as a walk step.  The emitted entry, the untouched storage and
accessed set, and the gas account arrive in the continuation. -/
lemma Func.runCompiledTo_log_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {n : Fin 5} {i sz : B256} {topics s : List B256} {c : Nat} {M M' : Mem}
    {payload : Bytes} {rest : Func} {ex : Execution}
    (h_stk : devm.stack = i :: sz :: (topics ++ s))
    (h_len : topics.length = n.val) (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_cost : gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩] = c)
    (h_data : (M.read i.toNat sz.toNat).1 = payload)
    (h_img : (M.read i.toNat sz.toNat).2 = M')
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (G : Nat),
      base.logs = devm.logs ++ [⟨sevm.currentTarget, topics, payload⟩] →
      (∀ (a : Adr) (k : B256), base.getStorVal a k = devm.getStorVal a k) →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (base.setMach ⟨s, M', G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next (.reg (.log n)) rest) ex := by
  subst h_mem
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_log_of (G := devm.gasLeft - c) h_stk h_len h_static
      h_cost h_data h_img (by omega)) ?_
  exact h_next _ _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    rfl (by omega)

/-- `CALLDATACOPY` as a walk step, with the charge a variable.  The copied bytes
are `Sevm.data`'s slice — zero-filled past the end of calldata, which is why no
premise bounds the requested window. -/
lemma Func.runCompiledTo_calldatacopy_step {fs : List Func} {sevm : Sevm}
    {devm : Devm} {di si sz : B256} {s : List B256} {c : Nat} {M : Mem}
    {rest : Func} {ex : Execution}
    (h_stk : devm.stack = di :: si :: sz :: s)
    (h_mem : devm.memory = M)
    (h_cost : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] = c)
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (M' : Mem) (G : Nat),
      M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0) = M' →
      devm.gasLeft = G + c →
      Func.RunCompiledTo fs sevm (devm.setMach ⟨s, M', G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (Func.next (.reg .calldatacopy) rest) ex := by
  subst h_mem
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_calldatacopy_of (G := devm.gasLeft - c) h_stk h_cost
      rfl (by omega)) ?_
  exact h_next _ _ rfl (by omega)

/-! ## EIP-150, at `value = 0`

`calculateMsgCallGas` is where the 63/64 rule lives, and P4 of
`~/plans/adversarial-progress.md` settles that it is *frame-local*: the cap is
computed inside `Xinst.step`, and no transaction layer is touched.  At
`value = 0` the stipend vanishes and the pair collapses to one `min`. -/

/-- `calculateMsgCallGas` at `value = 0`, in the branch where the frame can
afford its own overhead.  The forwarded amount is `min` of what the operand
asked for and the 63/64 cap; the stipend is zero. -/
lemma calculateMsgCallGas_zero {gas gl ext acc : Nat} (h : acc + ext ≤ gl) :
    calculateMsgCallGas 0 gas gl ext acc =
      ⟨min gas (except64th (gl - ext - acc)) + acc,
        min gas (except64th (gl - ext - acc))⟩ := by
  rw [calculateMsgCallGas, if_pos (rfl : (0 : Nat) = 0), if_neg (by omega)]
  show (min gas (except64th (gl - ext - acc)) + acc,
    min gas (except64th (gl - ext - acc)) + 0) = _
  rw [Nat.add_zero]

/-- **The retained gas, bounded below.**  Whatever the operand asked for, the
frame keeps at least a sixty-fourth of what it had after its own overhead:
`except64th n = n - n / 64` leaves `n / 64` behind, and `min` can only leave
more.

This is what makes a post-`CALL` continuation provable against a *closed* bound
without any premise about the callee — the callee cannot take the last
sixty-fourth however it behaves. -/
lemma le_retained_of_calculateMsgCallGas_zero {gas gl ext acc mcc mcs : Nat}
    (h : acc + ext ≤ gl)
    (h_split : calculateMsgCallGas 0 gas gl ext acc = ⟨mcc, mcs⟩) :
    (gl - ext - acc) / 64 ≤ gl - (mcc + ext) := by
  rw [calculateMsgCallGas_zero h] at h_split
  injection h_split with h_cost _
  subst h_cost
  rw [show except64th (gl - ext - acc)
    = (gl - ext - acc) - (gl - ext - acc) / 64 from rfl]
  have h_div : (gl - ext - acc) / 64 ≤ gl - ext - acc := Nat.div_le_self _ _
  omega

/-- The `min` collapses when the operand asked for at least the cap — which is
what a frame that pushed its own `GAS` and forwarded it does, since the cap is
strictly below the account the push read. -/
lemma calculateMsgCallGas_zero_of_cap_le {gas gl ext acc : Nat}
    (h : acc + ext ≤ gl) (h_cap : except64th (gl - ext - acc) ≤ gas) :
    calculateMsgCallGas 0 gas gl ext acc =
      ⟨except64th (gl - ext - acc) + acc, except64th (gl - ext - acc)⟩ := by
  rw [calculateMsgCallGas_zero h, Nat.min_eq_right h_cap]

/-! ## `genericCall.step`

Two arms, and the depth test is the whole difference.  At `sevm.depth = 0` no
child is spawned at all: the frame pushes `0`, gets the forwarded gas back and
carries on — a *revert-path* case for a contract that checks the return value,
never a premise. -/

/-- The spawning arm: at nonzero depth, the message is built and the frame
suspends.  Nothing is evaluated here that the caller cannot read off the
conclusion. -/
lemma genericCall.step_spawn {sevm : Sevm} {devm : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_depth : sevm.depth ≠ 0) :
    genericCall.step sevm devm gas value caller target codeAddress stv isStatic
        ii is oi os code dp =
      .spawn
        (Frame.ofCall
          (callMsg sevm (devm.withReturnData []) gas value caller target
            codeAddress stv isStatic
            ((devm.withReturnData []).memory.data.sliceD ii is 0) code dp))
        (.call (devm.withReturnData []) oi os) := by
  rw [genericCall.step, if_neg h_depth]

/-- The depth-limit arm: `sevm.depth = 0` is Jaune's encoding of "no room for a
child", and the instruction answers `0` on the stack with the requested gas
handed straight back.

A contract that branches on the returned flag reverts here, which is why P2's
trichotomy needs this arm and not a premise excluding it. -/
lemma genericCall.step_zero_depth {sevm : Sevm} {devm : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_depth : sevm.depth = 0)
    (h_room : devm.stack.length < 1024) :
    genericCall.step sevm devm gas value caller target codeAddress stv isStatic
        ii is oi os code dp =
      .done (.ok ((devm.withReturnData []).setMach
        ⟨0 :: devm.stack, devm.memory, devm.gasLeft + gas⟩)) := by
  rw [genericCall.step, if_pos h_depth]
  show XStep.ofExcept
    (Devm.push 0
      (((devm.withReturnData []).withGasLeft
        ((devm.withReturnData []).gasLeft + gas))) >>= fun d =>
          Except.ok (XStep.done (.ok d))) = _
  rw [Devm.push_eq_ok
    (devm := (devm.withReturnData []).withGasLeft
      ((devm.withReturnData []).gasLeft + gas))
    (by show devm.stack.length < 1024; exact h_room)]
  rfl

/-! ## `Xinst.step`'s `.call` arm, at `value = 0`

Seven pops, one memory-expansion charge, one delegation resolution, the EIP-150
split, and then `genericCall.step`.  Every step of that is either arithmetic the
caller supplies as an equation or a projection of the popped state.

The two branches a nonzero value would open are *closed* here rather than
assumed away: the static-context assertion succeeds on `value = 0`, and the
balance short-circuit tests `senderBal < 0`, which no `B256` satisfies. -/

/-- The `.call` arm reduced to a `genericCall.step`, at `value = 0`.

The premises name what the arm computes and this layer does not: the
memory-expansion charge (`h_ext`), the delegation resolution (`h_del` — EIP-7702
can add a second cold-account charge, and `dgc` is it), the collected access
cost (`h_acc`), and the EIP-150 split (`h_split`).  `h_afford` is the branch
condition of `calculateMsgCallGas`, and `h_gas` is the frame's own ability to
pay. -/
lemma Xinst.step_call_zero_value {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) :
    Xinst.step sevm devm .call =
      genericCall.step sevm
        ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
          [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
        mcs 0 sevm.currentTarget cw.toAdr dadr true false
        iiw.toNat isw.toNat oiw.toNat osw.toNat code dp := by
  subst h_ext; subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨callee, d⟩ ← d.popToAdr
    let ⟨value, d⟩ ← d.pop
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost callee d.accessedAddresses
    let d := addAccessedAddress d callee
    let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d callee
    let accessCost := preAccessCost + delegatedAccessGasCost
    let createCost :=
      if (¬ (d.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount
    let transferCost := if value = 0 then 0 else gasCallValue
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas value.toNat gas.toNat d.gasLeft extendCost
        (accessCost + createCost + transferCost)
    let d ← chargeGas (msgCallCost + extendCost) d
    Except.assert (!sevm.isStatic ∨ value = 0)
      ⟨.halt (.writeInStaticContext .none), d⟩
    let d := d.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let senderBal := (d.getAcct sevm.currentTarget).bal
    if senderBal < value then
      let d ← d.push 0
      return .done
        (.ok ((d.withReturnData []).withGasLeft (d.gasLeft + msgCallStipend)))
    else
      return genericCall.step
        sevm d msgCallStipend value sevm.currentTarget callee
        newCodeAddress true false inputIndex inputSize outputIndex outputSize
        code disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach ⟨cw :: 0 :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨0 :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  -- `value = 0` closes the new-account and transfer charges, and the
  -- static-context assertion, on their right disjuncts.  `simp only` rather
  -- than `rw` for `h_del`: the new-account `if` carries a `Decidable` instance
  -- that depends on the term being rewritten.
  simp only [if_pos (Or.inr trivial), if_pos trivial, Nat.add_zero,
    show ((0 : B256).toNat) = 0 from rfl]
  simp only [h_del, h_split]
  rw [chargeGas_eq_ok (devm := d1) h_gas]
  simp only [Except.assert, if_pos (Or.inr trivial)]
  -- The balance short-circuit tests `senderBal < 0`, which no `B256` satisfies:
  -- at `value = 0` the branch is unreachable rather than excluded by a premise.
  rw [if_neg (by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _))]
  rfl

/-! ## `Xinst.step`'s `.call` arm, at nonzero value -/

/-- The nonzero-value `.call` arm reduced to `genericCall.step` after the
caller has paid the account/value overhead and the sender-affordability branch
has been discharged explicitly.  The account-creation charge remains a named
branch input so callers can cover empty and existing recipients separately. -/
lemma Xinst.step_call_nonzero {sevm : Sevm} {devm : Devm}
    {gw cw vw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc create mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: s)
    (h_value : vw ≠ 0)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_create :
      (if ¬ (d1.getAcct cw.toAdr).Empty then 0 else gNewAccount) = create)
    (h_split :
      calculateMsgCallGas vw.toNat gw.toNat d1.gasLeft ext
        (acc + create + gasCallValue) = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_dynamic : sevm.isStatic = false)
    (h_sender : ¬ (d1.getAcct sevm.currentTarget).bal < vw) :
    Xinst.step sevm devm .call =
      genericCall.step sevm
        ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
          [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
        mcs vw sevm.currentTarget cw.toAdr dadr true false
        iiw.toNat isw.toNat oiw.toNat osw.toNat code dp := by
  subst h_ext
  subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨callee, d⟩ ← d.popToAdr
    let ⟨value, d⟩ ← d.pop
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost callee d.accessedAddresses
    let d := addAccessedAddress d callee
    let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d callee
    let accessCost := preAccessCost + delegatedAccessGasCost
    let createCost :=
      if (¬ (d.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount
    let transferCost := if value = 0 then 0 else gasCallValue
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas value.toNat gas.toNat d.gasLeft extendCost
        (accessCost + createCost + transferCost)
    let d ← chargeGas (msgCallCost + extendCost) d
    Except.assert (!sevm.isStatic ∨ value = 0)
      ⟨.halt (.writeInStaticContext .none), d⟩
    let d := d.memExtends
      [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let senderBal := (d.getAcct sevm.currentTarget).bal
    if senderBal < value then
      let d ← d.push 0
      return .done
        (.ok ((d.withReturnData []).withGasLeft
          (d.gasLeft + msgCallStipend)))
    else
      return genericCall.step
        sevm d msgCallStipend value sevm.currentTarget callee
        newCodeAddress true false inputIndex inputSize outputIndex outputSize
        code disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach
      ⟨cw :: vw :: iiw :: isw :: oiw :: osw :: s,
        devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach
      ⟨vw :: iiw :: isw :: oiw :: osw :: s, devm.memory, devm.gasLeft⟩)
      rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach
      ⟨iiw :: isw :: oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach
      ⟨isw :: oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach
      ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach
      ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  simp only [h_del, h_value, or_false, if_false, h_create, h_split]
  rw [chargeGas_eq_ok (devm := d1) h_gas]
  simp only [Except.assert, h_dynamic, Bool.not_false, if_true]
  have h_sender' :
      ¬ (((d1.setMach
          ⟨d1.stack, d1.memory,
            d1.gasLeft -
              (mcc +
                (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
                  [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])⟩).memExtends
            [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).getAcct
          sevm.currentTarget).bal < vw := by
    change ¬ (d1.getAcct sevm.currentTarget).bal < vw
    exact h_sender
  rw [if_neg h_sender']
  rfl

private lemma accessDelegation_stack_state {devm d1 : Devm}
    {a dadr : Adr} {dp : Bool} {code : ByteArray} {dgc : Nat}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    d1.stack = devm.stack ∧ d1.state = devm.state := by
  unfold accessDelegation at h
  rcases hd : getDelegatedCodeAddress (devm.state.getCode a) with _ | adr <;>
    simp only [hd] at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h
    exact ⟨rfl, rfl⟩

/-- The distinct nonzero-value affordability short circuit.  The instruction
does not spawn a child: it pushes failure flag `0`, preserves the world, clears
return data, and refunds the calculated child stipend. -/
lemma Xinst.step_call_nonzero_insufficient {sevm : Sevm} {devm : Devm}
    {gw cw vw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc create mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: s)
    (h_value : vw ≠ 0)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_create :
      (if ¬ (d1.getAcct cw.toAdr).Empty then 0 else gNewAccount) = create)
    (h_split :
      calculateMsgCallGas vw.toNat gw.toNat d1.gasLeft ext
        (acc + create + gasCallValue) = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_dynamic : sevm.isStatic = false)
    (h_sender : (d1.getAcct sevm.currentTarget).bal < vw)
    (h_room : s.length < 1024) :
    ∃ post,
      Xinst.step sevm devm .call = .done (.ok post) ∧
      post.stack = 0 :: s ∧
      post.state = devm.state ∧
      post.returnData = [] ∧
      post.gasLeft = d1.gasLeft - (mcc + ext) + mcs := by
  subst h_ext
  subst h_acc
  change ∃ post, XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨callee, d⟩ ← d.popToAdr
    let ⟨value, d⟩ ← d.pop
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost callee d.accessedAddresses
    let d := addAccessedAddress d callee
    let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d callee
    let accessCost := preAccessCost + delegatedAccessGasCost
    let createCost :=
      if (¬ (d.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount
    let transferCost := if value = 0 then 0 else gasCallValue
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas value.toNat gas.toNat d.gasLeft extendCost
        (accessCost + createCost + transferCost)
    let d ← chargeGas (msgCallCost + extendCost) d
    Except.assert (!sevm.isStatic ∨ value = 0)
      ⟨.halt (.writeInStaticContext .none), d⟩
    let d := d.memExtends
      [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let senderBal := (d.getAcct sevm.currentTarget).bal
    if senderBal < value then
      let d ← d.push 0
      return .done
        (.ok ((d.withReturnData []).withGasLeft
          (d.gasLeft + msgCallStipend)))
    else
      return genericCall.step
        sevm d msgCallStipend value sevm.currentTarget callee
        newCodeAddress true false inputIndex inputSize outputIndex outputSize
        code disablePrecompiles) = .done (.ok post) ∧
      post.stack = 0 :: s ∧
      post.state = devm.state ∧
      post.returnData = [] ∧
      post.gasLeft = d1.gasLeft -
        (mcc +
          (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
            [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]) + mcs
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach
      ⟨cw :: vw :: iiw :: isw :: oiw :: osw :: s,
        devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach
      ⟨vw :: iiw :: isw :: oiw :: osw :: s, devm.memory, devm.gasLeft⟩)
      rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach
      ⟨iiw :: isw :: oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach
      ⟨isw :: oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach
      ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach
      ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  simp only [h_del, h_value, or_false, if_false, h_create, h_split]
  rw [chargeGas_eq_ok (devm := d1) h_gas]
  simp only [Except.assert, h_dynamic, Bool.not_false, if_true]
  have h_sender' :
      (((d1.setMach
          ⟨d1.stack, d1.memory,
            d1.gasLeft -
              (mcc +
                (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
                  [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])⟩).memExtends
            [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).getAcct
          sevm.currentTarget).bal < vw := by
    change (d1.getAcct sevm.currentTarget).bal < vw
    exact h_sender
  rw [if_pos h_sender']
  have hframe := accessDelegation_stack_state h_del
  have hd1stack : d1.stack = s := by
    have h := hframe.1
    change d1.stack = s at h
    exact h
  have hd1state : d1.state = devm.state := by
    have h := hframe.2
    change d1.state = devm.state at h
    exact h
  rw [Devm.push_eq_ok (by
    change d1.stack.length < 1024
    rw [hd1stack]
    exact h_room)]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · change 0 :: d1.stack = 0 :: s
    rw [hd1stack]
  · change d1.state = devm.state
    exact hd1state
  · rfl
  · rfl

/-! ## `Xinst.step`'s `.statcall` arm

`STATICCALL` has the same six stack operands as the value-zero part of `CALL`,
but fixes both the transferred value and the child value to zero and marks the
child message static.  Naming this reduction once is enough for callers that
resolve through interpreted code and for childless precompile answers alike. -/

/-- The `.statcall` arm reduced to `genericCall.step`, with its delegation,
access-charge, memory-extension, and EIP-150 computations named by equations. -/
lemma Xinst.step_statcall {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) :
    Xinst.step sevm devm .statcall =
      genericCall.step sevm
        ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
          [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
        mcs 0 sevm.currentTarget tw.toAdr dadr true true
        iiw.toNat isw.toNat oiw.toNat osw.toNat code dp := by
  subst h_ext
  subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨target, d⟩ ← d.popToAdr
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost target d.accessedAddresses
    let d := addAccessedAddress d target
    let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d target
    let accessCost := preAccessCost + delegatedAccessGasCost
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas 0 gas.toNat d.gasLeft extendCost accessCost
    let d ← chargeGas (msgCallCost + extendCost) d
    let d :=
      d.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    return genericCall.step
      sevm d msgCallStipend 0 sevm.currentTarget target newCodeAddress
      true true inputIndex inputSize outputIndex outputSize code
      disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach ⟨tw :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  simp only [h_del, h_split]
  rw [chargeGas_eq_ok (devm := d1) h_gas]
  rfl

/-! ## `Xinst.step`'s `.delcall` arm

`DELEGATECALL` pops the same six operands as `STATICCALL` and charges for them
the same way; the two arms differ only in the four arguments `genericCall.step`
is finally handed.  Those four arguments are what this section is about.  A
`DELEGATECALL` leaves the *running* account as the child's storage owner, gives
the resolved account the code role alone, and inherits the parent frame's own
`caller` and `value` instead of substituting the parent's address and zero.

Three roles are named separately throughout:

* **storage owner** — `Msg.currentTarget`, the account whose `SSTORE`/`SLOAD`
  and `TSTORE`/`TLOAD` are hit;
* **code address** — `Msg.codeAddress`, the account whose code runs;
* **caller** — `Msg.caller`, what `CALLER` observes inside the child.

`callSpawnMsg` and `statcallSpawnMsg` already take the first two as separate
parameters, because EIP-7702 delegation can separate them under a plain `CALL`
too.  What `DELEGATECALL` changes is *which* account fills the storage slot:
not the popped operand, but `sevm.currentTarget`. -/

/-- The `.delcall` arm reduced to `genericCall.step`, with its delegation,
access-charge, memory-extension, and EIP-150 computations named by equations.
An exact mirror of `Xinst.step_statcall` apart from those four arguments. -/
lemma Xinst.step_delcall {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) :
    Xinst.step sevm devm .delcall =
      genericCall.step sevm
        ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
          [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
        mcs sevm.value sevm.caller sevm.currentTarget dadr false false
        iiw.toNat isw.toNat oiw.toNat osw.toNat code dp := by
  subst h_ext
  subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨codeAddress, d⟩ ← d.popToAdr
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost codeAddress d.accessedAddresses
    let d := addAccessedAddress d codeAddress
    let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d codeAddress
    let accessCost := preAccessCost + delegatedAccessGasCost
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas 0 gas.toNat d.gasLeft extendCost accessCost
    let d ← chargeGas (msgCallCost + extendCost) d
    let d :=
      d.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    return genericCall.step
      sevm d msgCallStipend sevm.value sevm.caller sevm.currentTarget
      newCodeAddress false false
      inputIndex inputSize outputIndex outputSize code disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach ⟨cw :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  simp only [h_del, h_split]
  rw [chargeGas_eq_ok (devm := d1) h_gas]
  rfl

/-! ### The spawned frame, named

Step 2 of the arc has to state what the child starts from, and Step 4's success
form has to *quantify over it by name* rather than existentially (**A5**: an
∃-form boundary premise cannot compose forward, which the `fmint-restoration`
R4 finding established).  These two definitions are where that name comes from:
they are the spawn's two components, written as functions of the parent's own
state, so a statement about the callee is a statement about a term the caller
can build. -/

/-- The parent state a `CALL` suspends on: charged, window-extended and with
its return data cleared.  The term is shared by zero- and nonzero-value calls. -/
def callSpawnParent (d1 : Devm) (charge ii is oi os : Nat) : Devm :=
  ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - charge⟩).memExtends
    [⟨ii, is⟩, ⟨oi, os⟩]).withReturnData []

/-- The message a `value = 0` `CALL` builds: the callee owns the storage, the
separately supplied `cadr` is the account whose code runs, the value is zero,
and the calldata is the input window read out of the parent's own memory.

The two address roles are distinct parameters because EIP-7702 makes them
distinct facts: when the callee carries a delegation designator, the code that
runs is the delegation target's.  A caller with no delegation in play passes
the callee for both. -/
def callSpawnMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (callee cadr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callMsg sevm p mcs 0 sevm.currentTarget callee cadr true false
    (p.memory.data.sliceD ii is 0) code dp

/-- The message built by a nonzero-value `CALL`.  The stipend-bearing child gas
is the `mcs` produced by `calculateMsgCallGas`; it is not charged a second time
to the parent. -/
def valueCallSpawnMsg (sevm : Sevm) (p : Devm) (mcs : Nat)
    (value : B256) (callee cadr : Adr) (ii is : Nat)
    (code : ByteArray) (dp : Bool) : Msg :=
  callMsg sevm p mcs value sevm.currentTarget callee cadr true false
    (p.memory.data.sliceD ii is 0) code dp

/-- The message a `STATICCALL` builds.  It shares `callSpawnParent` with a
zero-value `CALL`, but the child message is static.  `target` owns the storage
and `cadr` is the account whose code runs; see `callSpawnMsg` on why they are
separate parameters. -/
def statcallSpawnMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (target cadr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callMsg sevm p mcs 0 sevm.currentTarget target cadr true true
    (p.memory.data.sliceD ii is 0) code dp

/-- The message a `DELEGATECALL` builds.  It shares `callSpawnParent` with a
zero-value `CALL`, but where `callSpawnMsg` and `statcallSpawnMsg` take the
storage owner as a parameter supplied from the popped operand, this constructor
fixes it to `sevm.currentTarget`: the account already running keeps its own
storage, and `codeAdr` — the account `accessDelegation` resolved — takes the
code role alone.  `caller` and `value` are inherited from the parent frame
rather than being set to the parent's own address and zero, and nothing is
transferred. -/
def delcallSpawnMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (codeAdr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callMsg sevm p mcs sevm.value sevm.caller sevm.currentTarget codeAdr
    false false (p.memory.data.sliceD ii is 0) code dp

/-- The affordable nonzero-value `.call` arm all the way to its spawned child
frame.  Sender affordability remains an explicit hypothesis at this reusable
boundary. -/
lemma Xinst.step_call_nonzero_spawn {sevm : Sevm} {devm : Devm}
    {gw cw vw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc create mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: s)
    (h_value : vw ≠ 0)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_create :
      (if ¬ (d1.getAcct cw.toAdr).Empty then 0 else gNewAccount) = create)
    (h_split :
      calculateMsgCallGas vw.toNat gw.toNat d1.gasLeft ext
        (acc + create + gasCallValue) = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_dynamic : sevm.isStatic = false)
    (h_sender : ¬ (d1.getAcct sevm.currentTarget).bal < vw)
    (h_depth : sevm.depth ≠ 0) :
    Xinst.step sevm devm .call =
      .spawn
        (Frame.ofCall (valueCallSpawnMsg sevm
          (callSpawnParent d1 (mcc + ext)
            iiw.toNat isw.toNat oiw.toNat osw.toNat)
          mcs vw cw.toAdr dadr iiw.toNat isw.toNat code dp))
        (.call (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat)
          oiw.toNat osw.toNat) := by
  rw [Xinst.step_call_nonzero h_stk h_value h_ext h_del h_acc h_create
    h_split h_gas h_dynamic h_sender, genericCall.step_spawn h_depth]
  rfl

/-- The `.call` arm all the way to its `.spawn`, at `value = 0` and nonzero
depth. -/
lemma Xinst.step_call_zero_value_spawn {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0) :
    Xinst.step sevm devm .call =
      .spawn
        (Frame.ofCall (callSpawnMsg sevm
          (callSpawnParent d1 (mcc + ext)
            iiw.toNat isw.toNat oiw.toNat osw.toNat)
          mcs cw.toAdr dadr iiw.toNat isw.toNat code dp))
        (.call (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat) := by
  rw [Xinst.step_call_zero_value h_stk h_ext h_del h_acc h_split h_gas,
    genericCall.step_spawn h_depth]
  rfl

/-- The `.statcall` arm all the way to its spawned static frame. -/
lemma Xinst.step_statcall_spawn {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0) :
    Xinst.step sevm devm .statcall =
      .spawn
        (Frame.ofCall (statcallSpawnMsg sevm
          (callSpawnParent d1 (mcc + ext)
            iiw.toNat isw.toNat oiw.toNat osw.toNat)
          mcs tw.toAdr dadr iiw.toNat isw.toNat code dp))
        (.call (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat) := by
  rw [Xinst.step_statcall h_stk h_ext h_del h_acc h_split h_gas,
    genericCall.step_spawn h_depth]
  rfl

/-- The `.delcall` arm all the way to its spawned child frame. -/
lemma Xinst.step_delcall_spawn {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0) :
    Xinst.step sevm devm .delcall =
      .spawn
        (Frame.ofCall (delcallSpawnMsg sevm
          (callSpawnParent d1 (mcc + ext)
            iiw.toNat isw.toNat oiw.toNat osw.toNat)
          mcs dadr iiw.toNat isw.toNat code dp))
        (.call (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat) := by
  rw [Xinst.step_delcall h_stk h_ext h_del h_acc h_split h_gas,
    genericCall.step_spawn h_depth]
  rfl

/-- **The crossing, assembled.**

A `value = 0` `CALL` whose frame enters, as one `Ninst.RunCompiled` premise: the
parent's arithmetic on the left, `Resume.run` on the right, and in between the
child's derivation supplied by `Xlot.filled_exec` at `exec cevm`.

Count the premises about the callee: there are none.  `h_enter` is about the
message the *parent* built and `h_res` is about the resume — and the term
`exec cevm` that stands where a behavioural assumption would go is exactly what
a caller case-splits on to get a trichotomy rather than a hypothesis. -/
lemma Ninst.runCompiled_call_zero_value {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {cevm : Evm} {devm' : Devm}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0)
    (h_enter : (Frame.ofCall (callSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs cw.toAdr dadr iiw.toNat isw.toNat code dp)).enter = .run cevm)
    (h_res : Resume.run
      (.call (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat)
      ((Frame.ofCall (callSpawnMsg sevm
        (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat)
        mcs cw.toAdr dadr iiw.toNat isw.toNat code dp)).settle (exec cevm))
        = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec .call) devm' :=
  Ninst.runCompiled_exec_run
    (Xinst.step_call_zero_value_spawn h_stk h_ext h_del h_acc h_split h_gas
      h_depth) h_enter h_res

/-- The corresponding compiled-instruction crossing for an affordable
nonzero-value `CALL`.  No successful child execution is a premise: the child
result is the total semantic term `exec cevm`, which the caller specializes by
proving frame entry and settlement for its admitted recipient class. -/
lemma Ninst.runCompiled_call_nonzero {sevm : Sevm} {devm : Devm}
    {gw cw vw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc create mcc mcs : Nat} {cevm : Evm} {devm' : Devm}
    (h_stk : devm.stack = gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: s)
    (h_value : vw ≠ 0)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_create :
      (if ¬ (d1.getAcct cw.toAdr).Empty then 0 else gNewAccount) = create)
    (h_split :
      calculateMsgCallGas vw.toNat gw.toNat d1.gasLeft ext
        (acc + create + gasCallValue) = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_dynamic : sevm.isStatic = false)
    (h_sender : ¬ (d1.getAcct sevm.currentTarget).bal < vw)
    (h_depth : sevm.depth ≠ 0)
    (h_enter : (Frame.ofCall (valueCallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs vw cw.toAdr dadr iiw.toNat isw.toNat code dp)).enter = .run cevm)
    (h_res : Resume.run
      (.call (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat)
      ((Frame.ofCall (valueCallSpawnMsg sevm
        (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat)
        mcs vw cw.toAdr dadr iiw.toNat isw.toNat code dp)).settle (exec cevm)) =
          .ok devm') :
    Ninst.RunCompiled sevm devm (.exec .call) devm' :=
  Ninst.runCompiled_exec_run
    (Xinst.step_call_nonzero_spawn h_stk h_value h_ext h_del h_acc h_create
      h_split h_gas h_dynamic h_sender h_depth) h_enter h_res

/-- **The crossing a forwarding proxy actually takes.**

The implementation's frame *enters* and runs, packaged as one
`Ninst.RunCompiled` premise.  Its `.done` counterpart is
`Ninst.runCompiled_delcall_doneFrame` below, which covers the arm where the
frame settles without entering — a precompile code address, or an entry
failure.

Count the premises about the code account: there are none.  The child's
derivation is the total term `exec cevm`, supplied by `Xlot.filled_exec`,
exactly as in `Ninst.runCompiled_call_zero_value`.  `h_enter` is a fact about
the message the *parent* built. -/
lemma Ninst.runCompiled_delcall {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {cevm : Evm} {devm' : Devm}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0)
    (h_enter : (Frame.ofCall (delcallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs dadr iiw.toNat isw.toNat code dp)).enter = .run cevm)
    (h_res : Resume.run
      (.call (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat)
      ((Frame.ofCall (delcallSpawnMsg sevm
        (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat)
        mcs dadr iiw.toNat isw.toNat code dp)).settle (exec cevm))
        = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec .delcall) devm' :=
  Ninst.runCompiled_exec_run
    (Xinst.step_delcall_spawn h_stk h_ext h_del h_acc h_split h_gas h_depth)
    h_enter h_res

/-- A code-free child halts successfully immediately: fetching beyond the
empty byte array produces the EVM's implicit `STOP`.  This is the reusable
callee-totality fact used by value transfers to admitted externally-owned
accounts; it contains no premise about child execution. -/
lemma exec_empty_code (evm : Evm) (h : evm.sta.code.size = 0) :
    exec evm = .ok evm.dyna := by
  rw [← exec_iff_exec_eq]
  refine ⟨Exec.halt ?_⟩
  simp [Evm.step, Evm.getInst, ByteArray.getInst, h, Linst.run]

/-- A value-transfer message whose sender can afford the value prepares the
debit/credit world successfully.  The intermediate debit state is produced by
the semantics rather than supplied as an envelope premise. -/
lemma Msg.benvAfterTransfer_of_affordable (msg : Msg)
    (h_transfer : msg.shouldTransferValue = true)
    (h_affordable : ¬ msg.benv.state.bal msg.caller < msg.value) :
    ∃ stmid,
      msg.benv.state.subBal msg.caller msg.value = some stmid ∧
      msg.benvAfterTransfer =
        .ok ((msg.benv.withState stmid).addBal msg.currentTarget msg.value) := by
  have hsub : msg.benv.state.subBal msg.caller msg.value =
      some (msg.benv.state.setBal msg.caller
        (msg.benv.state.bal msg.caller - msg.value)) := by
    simp [State.subBal, h_affordable]
  refine ⟨_, hsub, ?_⟩
  unfold Msg.benvAfterTransfer
  rw [h_transfer]
  simp only [if_true, Benv.subBal, hsub]
  rfl

/-- After transfer preparation, a non-precompile call enters the ordinary EVM
child.  The callee code is intentionally unconstrained here; the code-free
specialization composes this with `exec_empty_code`. -/
lemma Frame.enter_run_of_nonprecompile {f : Frame} {benv : Benv} {adr : Adr}
    (h_bt : f.inner.benvAfterTransfer = .ok benv)
    (h_ca : (f.inner.withBenv benv).codeAddress = some adr)
    (h_nonprecompile :
      (f.inner.withBenv benv).benv.stat.rules.isPrecomp adr = false) :
    f.enter = .run (initEvm (f.inner.withBenv benv)) := by
  unfold Frame.enter
  rw [h_bt]
  unfold executeCode.enter
  simp only [h_ca]
  rw [if_neg]
  intro h
  have hn : ¬ (f.inner.withBenv benv).benv.stat.rules.isPrecomp adr := by
    rw [h_nonprecompile]
    simp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact (hn h.2).elim

/-- A `STATICCALL` whose frame resolves without entering, preserving the
definitionally empty child slot.  Enabled precompiles are the principal
consumer. -/
lemma Ninst.childlessRunCompiled_statcall_doneFrame
    {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {devm' : Devm}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0)
    (h_enter : (Frame.ofCall (statcallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs tw.toAdr dadr iiw.toNat isw.toNat code dp)).enter = .done r)
    (h_res : Resume.run
      (.call (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat)
      r = .ok devm') :
    Ninst.ChildlessRunCompiled sevm devm (.exec .statcall) devm' :=
  Ninst.childlessRunCompiled_exec_doneFrame
    (Xinst.step_statcall_spawn h_stk h_ext h_del h_acc h_split h_gas h_depth)
    h_enter h_res

/-- A `STATICCALL` whose frame resolves without entering, packaged as one
`Ninst.RunCompiled` premise.  Enabled precompiles are the principal consumer:
their exact answer is already the `.done` result named by `h_enter`. -/
lemma Ninst.runCompiled_statcall_doneFrame {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {devm' : Devm}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0)
    (h_enter : (Frame.ofCall (statcallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs tw.toAdr dadr iiw.toNat isw.toNat code dp)).enter = .done r)
    (h_res : Resume.run
      (.call (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat)
      r = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec .statcall) devm' :=
  Ninst.runCompiled_exec_doneFrame
    (Xinst.step_statcall_spawn h_stk h_ext h_del h_acc h_split h_gas h_depth)
    h_enter h_res

/-- A `DELEGATECALL` whose frame resolves without entering, packaged as one
`Ninst.RunCompiled` premise.  A precompile code address is the principal
consumer: its exact answer is already the `.done` result named by `h_enter`.
As in `Ninst.runCompiled_delcall`, nothing here is a premise about the code
account. -/
lemma Ninst.runCompiled_delcall_doneFrame {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {devm' : Devm}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0)
    (h_enter : (Frame.ofCall (delcallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs dadr iiw.toNat isw.toNat code dp)).enter = .done r)
    (h_res : Resume.run
      (.call (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat)
      r = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec .delcall) devm' :=
  Ninst.runCompiled_exec_doneFrame
    (Xinst.step_delcall_spawn h_stk h_ext h_del h_acc h_split h_gas h_depth)
    h_enter h_res

/-- **The entered child's storage owner is the parent's own account.**

Between `Xinst.step … .delcall = .spawn …` and `exec (initEvm child)` sits
`Frame.enter`, and this discharges it — generically, for any parent frame,
rather than for one fixture.

Two things make that cheap under `DELEGATECALL`.  The value transfer is
provably the identity, because `shouldTransferValue = false` makes
`Msg.benvAfterTransfer` short-circuit; the `benv` the child enters with is the
one the parent handed it, so no affordability premise is needed.  What does
remain a premise is the precompile test, because `Frame.enter` consults
`benv.stat.rules.isPrecomp` at the *code* address — under `DELEGATECALL` the
implementation's account, not the storage owner's.

The second conjunct is the point of the whole family, stated about the frame
that actually runs rather than about the message that describes it. -/
theorem delcall_enters_with_parent_as_storage_owner {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile :
      sevm.benvStat.rules.isPrecomp dadr = false) :
    let parent := callSpawnParent d1 (mcc + ext)
      iiw.toNat isw.toNat oiw.toNat osw.toNat
    let child := delcallSpawnMsg sevm parent mcs dadr
      iiw.toNat isw.toNat code dp
    (Frame.ofCall child).enter = .run (initEvm child) ∧
      (initEvm child).sta.currentTarget = sevm.currentTarget ∧
      (initEvm child).sta.codeAddress = some dadr ∧
      (initEvm child).sta.caller = sevm.caller ∧
      (initEvm child).sta.value = sevm.value ∧
      ∀ devm', Resume.run
          (.call parent oiw.toNat osw.toNat)
          ((Frame.ofCall child).settle (exec (initEvm child))) = .ok devm' →
        Ninst.RunCompiled sevm devm (.exec .delcall) devm' := by
  dsimp only
  have h_bt : (delcallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs dadr iiw.toNat isw.toNat code dp).benvAfterTransfer
      = .ok (delcallSpawnMsg sevm
        (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat)
        mcs dadr iiw.toNat isw.toNat code dp).benv := rfl
  have h_enter := Frame.enter_run_of_nonprecompile
    (f := Frame.ofCall (delcallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs dadr iiw.toNat isw.toNat code dp))
    (adr := dadr) h_bt rfl h_nonprecompile
  refine ⟨h_enter, rfl, rfl, rfl, rfl, fun devm' h_res => ?_⟩
  exact Ninst.runCompiled_delcall h_stk h_ext h_del h_acc h_split h_gas h_depth
    h_enter h_res

/-! ### Anti-vacuity controls

A statement about `DELEGATECALL` ownership is worth nothing unless the same
shape under `CALL` comes out differently.  Since EIP-7702 the contrast is no
longer that one constructor fuses the two address roles and the other separates
them — `callSpawnMsg` and `statcallSpawnMsg` take both roles explicitly too.
The contrast is over *which account fills the storage slot*: a `CALL` puts the
popped callee there, for every code address the delegation resolver could
return, while a `DELEGATECALL` puts the running frame's own account there, for
every code address.  The controls below pin exactly that, and nothing weaker
would survive someone re-fusing either constructor's roles. -/

/-- The storage-owner control.  `hne` is what makes it bite: with
`sevm.currentTarget = cadr` the two constructors would agree and the separation
would be vacuously about one address.

What this pins: `delcallSpawnMsg`'s storage owner is `sevm.currentTarget` for
*every* code address, and `callSpawnMsg`'s is its `callee` parameter for every
code address, so neither slot can be re-wired to the other role without
breaking a `rfl` here.  What it does not pin: anything about the `.delcall` or
`.call` arms themselves — that is `Xinst.step_delcall` and
`Xinst.step_call_zero_value`, which is where the arms' choice of arguments is
proved.  Nor does it claim the two roles are *always* distinct under `CALL`:
the sixth and seventh clauses record only that at the undelegated
instantiation `cadr = callee`, which is the shape `Xinst.step_call_zero_value`
produces at an account carrying no delegation designator, they coincide. -/
theorem control_delcall_separates_call_fuses
    (sevm : Sevm) (p : Devm) (mcs : Nat) (callee cadr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool)
    (hne : sevm.currentTarget ≠ cadr) :
    -- `DELEGATECALL`: the storage owner is the running account, and the code
    -- account is a different one.
    (delcallSpawnMsg sevm p mcs cadr ii is code dp).currentTarget =
        sevm.currentTarget ∧
      (delcallSpawnMsg sevm p mcs cadr ii is code dp).codeAddress =
        some cadr ∧
      (delcallSpawnMsg sevm p mcs cadr ii is code dp).currentTarget ≠ cadr ∧
    -- `CALL`: the storage owner is the popped callee, for every code address
    -- the delegation resolver could have returned.
      (callSpawnMsg sevm p mcs callee cadr ii is code dp).currentTarget =
        callee ∧
      (callSpawnMsg sevm p mcs callee cadr ii is code dp).codeAddress =
        some cadr ∧
    -- Undelegated, the `.call` arm supplies the callee for both roles, and
    -- there — and only there — `CALL`'s two addresses coincide.
      (callSpawnMsg sevm p mcs cadr cadr ii is code dp).currentTarget = cadr ∧
      (callSpawnMsg sevm p mcs cadr cadr ii is code dp).codeAddress =
        some cadr ∧
    -- The separation itself: at the same code account, a `CALL` owns that
    -- account's storage and a `DELEGATECALL` owns the running account's.
      (delcallSpawnMsg sevm p mcs cadr ii is code dp).currentTarget ≠
        (callSpawnMsg sevm p mcs cadr cadr ii is code dp).currentTarget :=
  ⟨rfl, rfl, hne, rfl, rfl, rfl, rfl, hne⟩

/-- The caller and value clauses of the same control, unchanged in content by
EIP-7702 because neither opcode's `caller`, `value` or `shouldTransferValue`
argument mentions a code address.  Under `CALL` the child's `CALLER` is the
parent's own account and its `CALLVALUE` is the literal `0` supplied by the
opcode; under `DELEGATECALL` both are inherited from the parent frame, so a
forwarding proxy is transparent to `msg.sender` and `msg.value`. -/
theorem control_delcall_inherits_caller_and_value
    (sevm : Sevm) (p : Devm) (mcs : Nat) (callee cadr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) :
    (delcallSpawnMsg sevm p mcs cadr ii is code dp).caller = sevm.caller ∧
      (delcallSpawnMsg sevm p mcs cadr ii is code dp).value = sevm.value ∧
      (delcallSpawnMsg sevm p mcs cadr ii is code dp).shouldTransferValue
        = false ∧
      (callSpawnMsg sevm p mcs callee cadr ii is code dp).caller
        = sevm.currentTarget ∧
      (callSpawnMsg sevm p mcs callee cadr ii is code dp).value = 0 ∧
      (callSpawnMsg sevm p mcs callee cadr ii is code dp).shouldTransferValue
        = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What the child's own code *observes*, as opposed to what its `Msg` records.
`initSevm` carries `caller` and `value` into the child `Sevm`, and
`Rinst.runCore`'s `.caller` and `.callvalue` arms read them straight back out.
So a contract running behind a forwarding proxy sees the proxy's caller and the
proxy's value, not the proxy's address and zero — which is the property that
makes such a proxy transparent to `msg.sender` and `msg.value`.  The `CALL`
control is stated in the same theorem so the two cannot drift apart. -/
theorem delcall_child_observes_outer_caller_and_value
    (sevm : Sevm) (p : Devm) (mcs : Nat) (callee cadr : Adr) (ii is : Nat)
    (code : ByteArray) (dp : Bool) (d : Devm) (pc : Nat)
    (h_room : d.stack.length < 1024) (h_gas : gBase ≤ d.gasLeft) :
    ∃ dc dv cc cv,
      -- Under `DELEGATECALL` the child sees the outer frame's caller and value.
      Rinst.run
        ⟨pc, initSevm (delcallSpawnMsg sevm p mcs cadr ii is code dp), d⟩
        .caller = .ok dc ∧
      dc.stack = sevm.caller.toB256 :: d.stack ∧
      Rinst.run
        ⟨pc, initSevm (delcallSpawnMsg sevm p mcs cadr ii is code dp), d⟩
        .callvalue = .ok dv ∧
      dv.stack = sevm.value :: d.stack ∧
      -- Under `CALL` it sees the caller's own address and the opcode's zero.
      Rinst.run
        ⟨pc, initSevm (callSpawnMsg sevm p mcs callee cadr ii is code dp), d⟩
        .caller = .ok cc ∧
      cc.stack = sevm.currentTarget.toB256 :: d.stack ∧
      Rinst.run
        ⟨pc, initSevm (callSpawnMsg sevm p mcs callee cadr ii is code dp), d⟩
        .callvalue = .ok cv ∧
      cv.stack = (0 : B256) :: d.stack := by
  have step : ∀ (w : B256),
      ∃ d', pushItem w gBase d = .ok d' ∧ d'.stack = w :: d.stack := by
    intro w
    rw [pushItem_def, chargeGas_eq_ok h_gas]
    simp only [bind, Except.bind]
    rw [Devm.push_eq_ok
      (devm := d.setMach ⟨d.stack, d.memory, d.gasLeft - gBase⟩)
      (by show d.stack.length < 1024; exact h_room)]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨dc, hdc, hdcs⟩ := step sevm.caller.toB256
  obtain ⟨dv, hdv, hdvs⟩ := step sevm.value
  obtain ⟨cc, hcc, hccs⟩ := step sevm.currentTarget.toB256
  obtain ⟨cv, hcv, hcvs⟩ := step (0 : B256)
  exact ⟨dc, dv, cc, cv, hdc, hdcs, hdv, hdvs, hcc, hccs, hcv, hcvs⟩

/-! ## The resume, characterised

`Resume.run (.call parent oi os) r` is where the parent comes back.  Three
lemmas, one per outcome, and between them they are the whole post-`CALL` state.

What each says about the parent is the part worth reading twice.

* On a **fatal settle** (`.crypto`/`.internal`, the channel
  `executeCode.handleError` propagates rather than settles) the resume does not
  run at all: the error travels straight out, carrying the child's state.
* On a **settled child with an error** the parent keeps its **own** accessed
  addresses and storage keys, its own logs, its own refund counter and its own
  accounts-to-delete.  `incorporateChildOnError` copies gas, created accounts,
  return data, state and transient storage — and nothing else.  So a post-`CALL`
  worst case is fixed by the frame's own trunk, not by the callee.
* On a **clean child** the sets union, so warm stays warm.

None of the three is conditional on the callee doing anything. -/

/-- The fatal arm: the settle propagated a non-consensus error, so
`liftToExecution` re-raises it against the parent's world. -/
lemma Resume.run_call_fatal {parent : Devm} {oi os : Nat}
    {e : EvmError} {st : State} {ca : AdrSet} {tra : Tra} :
    Resume.run (.call parent oi os) (.error ⟨e, st, ca, tra⟩) =
      .error ⟨e, (parent.withCreatedAccounts ca).setWorld
        {parent.world with state := st, transientStorage := tra}⟩ := rfl

/-- The settled-with-error arm.  `h_err` is read off the child; `h_room` is the
parent's own headroom, which its trunk established. -/
lemma Resume.run_call_err {parent child : Devm} {oi os : Nat}
    (h_err : child.error.isSome = true)
    (h_room : parent.stack.length < 1024) :
    Resume.run (.call parent oi os) (.ok child) =
      .ok (((incorporateChildOnError parent child child.output).setMach
        ⟨0 :: parent.stack, parent.memory,
          parent.gasLeft + child.gasLeft⟩).memWrite oi
            (child.output.take os)) := by
  show (do
    let c ← liftToExecution parent (.ok child)
    let actualOutput := c.output.take os
    if c.error.isSome then
      let evm2 ← (incorporateChildOnError parent c c.output).push 0
      Except.ok (evm2.memWrite oi actualOutput)
    else
      let evm2 ← (incorporateChildOnSuccess parent c c.output).push 1
      Except.ok (evm2.memWrite oi actualOutput)) = _
  show (if child.error.isSome then
      (incorporateChildOnError parent child child.output).push 0 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))
    else
      (incorporateChildOnSuccess parent child child.output).push 1 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))) = _
  rw [if_pos h_err, Devm.push_eq_ok
    (devm := incorporateChildOnError parent child child.output)
    (by show parent.stack.length < 1024; exact h_room)]
  rfl

/-- The clean arm.  The pushed flag is `1`, and
`incorporateChildOnSuccess` unions the warm sets, the logs, the refund counter
and the accounts to delete. -/
lemma Resume.run_call_ok {parent child : Devm} {oi os : Nat}
    (h_ok : child.error.isSome = false)
    (h_room : parent.stack.length < 1024) :
    Resume.run (.call parent oi os) (.ok child) =
      .ok (((incorporateChildOnSuccess parent child child.output).setMach
        ⟨1 :: parent.stack, parent.memory,
          parent.gasLeft + child.gasLeft⟩).memWrite oi
            (child.output.take os)) := by
  show (do
    let c ← liftToExecution parent (.ok child)
    let actualOutput := c.output.take os
    if c.error.isSome then
      let evm2 ← (incorporateChildOnError parent c c.output).push 0
      Except.ok (evm2.memWrite oi actualOutput)
    else
      let evm2 ← (incorporateChildOnSuccess parent c c.output).push 1
      Except.ok (evm2.memWrite oi actualOutput)) = _
  show (if child.error.isSome then
      (incorporateChildOnError parent child child.output).push 0 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))
    else
      (incorporateChildOnSuccess parent child child.output).push 1 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))) = _
  rw [if_neg (by rw [h_ok]; exact Bool.false_ne_true), Devm.push_eq_ok
    (devm := incorporateChildOnSuccess parent child child.output)
    (by show parent.stack.length < 1024; exact h_room)]
  rfl

/-! ### Reading the resume state

The projections a continuation walk needs, so that it never has to unfold
`incorporateChild*` again. -/

/-- An empty return window writes nothing: `Mem.write` at an empty payload is
the identity, which is why fmint's `(0,0)` window costs the resume nothing. -/
lemma Devm.memWrite_nil {devm : Devm} {i : Nat} : devm.memWrite i [] = devm := rfl

/-- On the error path the parent's accessed storage keys are its own. -/
lemma incorporateChildOnError_accessedStorageKeys {parent child : Devm}
    {rd : Bytes} :
    (incorporateChildOnError parent child rd).accessedStorageKeys
      = parent.accessedStorageKeys := rfl

/-- And its accessed addresses. -/
lemma incorporateChildOnError_accessedAddresses {parent child : Devm}
    {rd : Bytes} :
    (incorporateChildOnError parent child rd).accessedAddresses
      = parent.accessedAddresses := rfl

/-- And its logs: a reverted child emits none the parent keeps. -/
lemma incorporateChildOnError_logs {parent child : Devm} {rd : Bytes} :
    (incorporateChildOnError parent child rd).logs = parent.logs := rfl

/-- The return data is the child's output on either path, which is what
`RETURNDATASIZE` then reads. -/
lemma incorporateChildOnError_returnData {parent child : Devm} {rd : Bytes} :
    (incorporateChildOnError parent child rd).returnData = rd := rfl

lemma incorporateChildOnSuccess_returnData {parent child : Devm} {rd : Bytes} :
    (incorporateChildOnSuccess parent child rd).returnData = rd := rfl

/-- On the success path the accessed sets union, so a key the parent warmed
stays warm across the call. -/
lemma incorporateChildOnSuccess_accessedStorageKeys {parent child : Devm}
    {rd : Bytes} :
    (incorporateChildOnSuccess parent child rd).accessedStorageKeys
      = parent.accessedStorageKeys.union child.accessedStorageKeys := rfl

/-! ## The non-consensus channel

`SettledHalt` is the storable half of `EvmError`: a frame settlement records an
exceptional halt or a revert, and a cryptographic or internal failure is
deliberately unrepresentable there, so it can only propagate on the error
channel.  `NonConsensus` names exactly that unrepresentability, which is what a
settlement trichotomy quarantines its third disjunct with. -/

/-- An error no settlement can store: it is outside `SettledHalt.toEvmError`'s
image, so it travels the error channel and never reads as a settled halt. -/
def NonConsensus (e : EvmError) : Prop := ∀ sh : SettledHalt, sh.toEvmError ≠ e

/-- A cryptographic failure is non-consensus. -/
lemma nonConsensus_crypto {r : CryptoError} : NonConsensus (.crypto r) := by
  intro sh; cases sh <;> simp [SettledHalt.toEvmError]

/-- An internal fault is non-consensus. -/
lemma nonConsensus_internal {r : InternalError} : NonConsensus (.internal r) := by
  intro sh; cases sh <;> simp [SettledHalt.toEvmError]

/-- The only errors `executeCode.handleError` re-raises are the two
non-consensus channels: a halt or a revert is *stored* and comes back `.ok`. -/
lemma handleError_error_inv {raw : Execution}
    {p : EvmError × State × AdrSet × Tra}
    (h : executeCode.handleError raw = .error p) : NonConsensus p.1 := by
  rcases raw with ⟨e, d⟩ | d
  · rcases e with r | _ | r | r <;>
      simp only [executeCode.handleError] at h
    · cases h
    · cases h
    · cases h; exact nonConsensus_crypto
    · cases h; exact nonConsensus_internal
  · cases h

/-- A call frame's settlement passes an error through untouched: the settle
step only inspects `.ok` results. -/
lemma Frame.settle_error_inv {f : Frame} {raw : Execution}
    {p : EvmError × State × AdrSet × Tra}
    (h_call : f.isCreate = false) (h : f.settle raw = .error p) :
    executeCode.handleError raw = .error p := by
  unfold Frame.settle Frame.settleMsg at h
  rw [h_call] at h
  simp only [Bool.false_eq_true, if_false] at h
  rcases hh : executeCode.handleError raw with q | evm <;> rw [hh] at h
  · simpa [processMessage.settle] using h
  · unfold processMessage.settle at h
    simp only [bind, Except.bind] at h
    split at h <;> cases h

/-- A value transfer can only fail on the non-consensus channel: the one error
`Msg.benvAfterTransfer` raises is an internal assertion. -/
lemma Msg.benvAfterTransfer_error_inv {msg : Msg}
    {p : EvmError × State × AdrSet × Tra}
    (h : msg.benvAfterTransfer = .error p) : NonConsensus p.1 := by
  unfold Msg.benvAfterTransfer at h
  split at h
  · rcases hs : (msg.benv.subBal msg.caller msg.value) with _ | benv <;>
      simp only [hs, Option.toExcept, bind, Except.bind] at h
    · cases h; exact nonConsensus_internal
    · cases h
  · cases h

/-- A call frame that resolves without entering — a precompile, or a failed
transfer — can only carry a non-consensus error in its `.done`. -/
lemma Frame.enter_done_error_inv {f : Frame}
    {p : EvmError × State × AdrSet × Tra}
    (h_call : f.isCreate = false) (h : f.enter = .done (.error p)) :
    NonConsensus p.1 := by
  unfold Frame.enter at h
  rcases hb : f.inner.benvAfterTransfer with e | benv <;> simp only [hb] at h
  · injection h with h_eq
    have h_pass : f.settleMsg (.error e) = .error e := by
      unfold Frame.settleMsg
      rw [h_call]
      simp [processMessage.settle]
    rw [h_pass] at h_eq
    cases h_eq
    exact Msg.benvAfterTransfer_error_inv hb
  · rcases he : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
      simp only [he] at h
    · cases h
    · injection h with h_eq
      exact handleError_error_inv (Frame.settle_error_inv h_call h_eq)

/-! ## `Func.ExecTo` — a walk, transported to derivation evidence

`Func.RunCompiledTo` cannot say "the frame dies *at* this instruction": its
`.next` rule requires the instruction to succeed, and only a `.last` carries an
arbitrary outcome.  A `CALL` whose child settles on the non-consensus channel
is exactly that — a `.next` node whose step outcome is an error — so the
composition of a trichotomy has to happen one level down, at the `Exec`
derivation the bridge produces.

`Func.ExecTo` is that level, packaged so the walk machinery still applies: it
is the *statement* of `Func.exec_of_runCompiledTo_core` abstracted over the
walk — at every pc where this `Func`'s code sits, the execution from this state
settles at `ex`.  It is a `Prop`-valued definition, not a new inductive: no new
relation is built, and a complete `Func.RunCompiledTo` derivation embeds by one
application of the landed core.

The four structural rules below are positional mirrors of
`Func.RunCompiledTo`'s wrappers, which is what lets `func_run` build this
too (`Forward.execSpec`).  On top of them sit the two things only this level
can say: a `.next` node whose instruction *fails* (`Func.execTo_next_error`),
and the top-level bridge to the total `exec` (`Prog.exec_of_execTo`). -/

/-- At every pc where `p`'s compiled code sits, execution from `devm` settles
at `ex`.  The quantified `f₀ :: fs'` split and the compile equation are the
core bridge's own premises, threaded so the internal `.call` rule can resolve
table entries. -/
def Func.ExecTo (fs : List Func) (sevm : Sevm) (devm : Devm) (p : Func)
    (ex : Execution) : Prop :=
  ∀ (f₀ : Func) (fs' : List Func), fs = f₀ :: fs' →
    some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩ →
    ∀ pc,
      subcode sevm.code.toList pc (Func.compile (table 0 (f₀ :: fs')) pc p) →
      noPushBefore sevm.code pc 32 = true →
      Nonempty (Exec pc sevm devm ex)

/-- A complete walk is `ExecTo` evidence: one application of the landed core. -/
lemma Func.ExecTo.of_runCompiledTo {fs : List Func} {sevm : Sevm} {devm : Devm}
    {p : Func} {ex : Execution} (h : Func.RunCompiledTo fs sevm devm p ex) :
    Func.ExecTo fs sevm devm p ex :=
  fun _ _ hFS h_eq pc sub hb => Func.exec_of_runCompiledTo_core h h_eq hFS pc sub hb

/-- The `.next` rule: one successful instruction, then the tail's evidence.
Positional mirror of `Func.RunCompiledTo.next`. -/
lemma Func.execTo_next {fs : List Func} {sevm : Sevm} {devm : Devm} {i : Ninst}
    {devm' : Devm} {f : Func} {ex : Execution}
    (h_n : Ninst.RunCompiled sevm devm i devm')
    (h_f : Func.ExecTo fs sevm devm' f ex) :
    Func.ExecTo fs sevm devm (.next i f) ex := by
  intro f₀ fs' hFS h_eq pc sub hb
  rcases Func.noPushBefore_next sub hb with ⟨hb', sub'⟩
  rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
  rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩
  simp [pure] at h_rw
  rw [← h_rw] at h_slice
  rcases h_n with ⟨xl, h_filled, h_step⟩
  exact Ninst.exec_of_stepRun (Ninst.at_of_slice (List.slice_prefix h_slice))
    h_filled (h_step pc) (h_f f₀ fs' hFS h_eq _ sub' hb')

/-- The fall-through arm of a `branch`.  Positional mirror of
`Func.runCompiledTo_branch_zero`. -/
lemma Func.execTo_branch_zero {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {s : List B256} {G : Nat}
    (h_stk : devm.stack = 0 :: s) (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh))
    (h_arm : Func.ExecTo fs sevm (devm.setMach ⟨s, devm.memory, G⟩) f ex) :
    Func.ExecTo fs sevm devm (.branch f g) ex := by
  intro f₀ fs' hFS h_eq pc sub hb
  rcases subcode_compile_branch_jumpable sub hb with
    ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp, h_subq, h_bq⟩
  rcases Evm.branch_zero_steps h_push h_jumpi h_loc h_room
    (Devm.popBurnBy_setMach h_stk h_gas) with ⟨h1, h2⟩
  obtain ⟨excf⟩ := h_arm f₀ fs' hFS h_eq (pc + 4) h_subp h_bp
  exact ⟨Exec.cont h1 (Exec.cont h2 excf)⟩

/-- The jumped arm of a `branch`.  Positional mirror of
`Func.runCompiledTo_branch_succ`. -/
lemma Func.execTo_branch_succ {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {w : B256} {s : List B256} {G : Nat}
    (h_ne : w ≠ 0) (h_stk : devm.stack = w :: s)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh + gJumpdest))
    (h_arm : Func.ExecTo fs sevm (devm.setMach ⟨s, devm.memory, G⟩) g ex) :
    Func.ExecTo fs sevm devm (.branch f g) ex := by
  intro f₀ fs' hFS h_eq pc sub hb
  rcases subcode_compile_branch_jumpable sub hb with
    ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp, h_subq, h_bq⟩
  rcases Evm.branch_succ_steps h_push h_jumpi h_jd h_jp h_loc h_ne h_room
    (Devm.popBurnBy_setMach h_stk h_gas) with ⟨h1, h2, h3⟩
  obtain ⟨excg⟩ := h_arm f₀ fs' hFS h_eq (loc + 1) h_subq h_bq
  exact ⟨Exec.cont h1 (Exec.cont h2 (Exec.cont h3 excg))⟩

/-- An internal `.call` into the flat table.  Positional mirror of
`Func.runCompiledTo_call'`. -/
lemma Func.execTo_call' {fs : List Func} {sevm : Sevm} {devm : Devm} {k : Nat}
    {f : Func} {ex : Execution} {G : Nat} (h_get : fs[k]? = some f)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gMid + gJumpdest))
    (h_body : Func.ExecTo fs sevm
      (devm.setMach ⟨devm.stack, devm.memory, G⟩) f ex) :
    Func.ExecTo fs sevm devm (.call k) ex := by
  intro f₀ fs' hFS h_eq pc sub hb
  subst hFS
  rcases subcode_compile_call sub with ⟨loc, p₁, h_get_tab, h_loc, h_pushAt, h_jump⟩
  have h_pf := (Prog.get?_table (m := 0)).symm.trans
    (congrArg (Prod.snd <$> ·) h_get_tab)
  rw [h_get] at h_pf
  simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at h_pf
  subst h_pf
  rcases subcode_of_get?_eq_some h_eq h_get_tab with ⟨h_jd, h_subf⟩
  have h_jpb := Prog.jumpable_of_get?_table h_eq h_get_tab
  rcases h_pushAt with ⟨le, h_push⟩
  rcases Evm.call_steps (le := le) h_push h_jump h_jd h_jpb.1 h_loc h_room
    (Devm.burnBy_setMach_gas h_gas) with ⟨h1, h2, h3⟩
  obtain ⟨excf⟩ := h_body f₀ fs' rfl h_eq (loc + 1) h_subf h_jpb.2
  exact ⟨Exec.cont h1 (Exec.cont h2 (Exec.cont h3 excf))⟩

/-- The error sibling of `Ninst.exec_of_stepRun`: an instruction whose step
outcome is an error ends the derivation right there, whichever of the three
step shapes produced it. -/
lemma Ninst.exec_of_stepRun_error {pc : Nat} {sevm : Sevm} {devm : Devm}
    {n : Ninst} {xl : Xlot} {e : EvmError × Devm}
    (h_at : Ninst.At sevm.code pc n)
    (h_filled : xl.Filled)
    (h_step : Ninst.StepRun pc sevm devm n xl (.error e)) :
    Nonempty (Exec pc sevm devm (.error e)) := by
  have hstep : Evm.step ⟨pc, sevm, devm⟩ = Ninst.step ⟨pc, sevm, devm⟩ n :=
    Evm.step_next h_at
  cases n with
  | reg r =>
    rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_step
    refine ⟨Exec.halt ?_⟩
    rw [hstep, Ninst.step_reg, ← h_step.2]
    rfl
  | push xs le =>
    rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_step
    refine ⟨Exec.halt ?_⟩
    rw [hstep, Ninst.step_push, ← h_step.2]
    rfl
  | exec x =>
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at h_step
    cases hx : Xinst.step sevm devm x with
    | done ex' =>
      rw [hx] at h_step
      simp only [XStep.Run] at h_step
      refine ⟨Exec.halt ?_⟩
      rw [hstep, Ninst.step_exec, hx, ← h_step.2]
      rfl
    | spawn fr rsm =>
      rw [hx] at h_step
      rcases h_step with ⟨r, hframe, hex⟩
      have hstep' : Evm.step ⟨pc, sevm, devm⟩ = .spawn fr rsm (pc + 1) := by
        rw [hstep, Ninst.step_exec, hx]
        rfl
      unfold RunFrame at hframe
      rcases henter : fr.enter with r' | cevm <;> simp only [henter] at hframe
      · exact ⟨Exec.doneErr hstep' henter (hframe.2 ▸ hex.symm)⟩
      · rcases hframe with ⟨raw, hxl, hr⟩
        subst hxl
        obtain ⟨excChild⟩ : Nonempty (Exec cevm.pc cevm.sta cevm.dyna raw) :=
          h_filled
        refine ⟨Exec.runErr hstep' henter excChild ?_⟩
        rw [← hr]
        exact hex.symm

/-- The terminal only this level has: a `.next` node whose instruction fails.
The whole frame settles at that error, whatever the rest of the `Func` was. -/
lemma Func.execTo_next_error {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i : Ninst} {rest : Func} {e : EvmError × Devm}
    (h : ∃ xl : Xlot, xl.Filled ∧
      ∀ pc, Ninst.StepRun pc sevm devm i xl (.error e)) :
    Func.ExecTo fs sevm devm (.next i rest) (.error e) := by
  intro f₀ fs' hFS h_eq pc sub hb
  rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
  rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩
  simp [pure] at h_rw
  rw [← h_rw] at h_slice
  rcases h with ⟨xl, h_filled, h_step⟩
  exact Ninst.exec_of_stepRun_error
    (Ninst.at_of_slice (List.slice_prefix h_slice)) h_filled (h_step pc)

/-- A spawning instruction whose entered child's settle propagates a fatal
error, as the step evidence `Func.execTo_next_error` consumes.  The mirror of
`Ninst.runCompiled_exec_run`, one constructor over: same premises, error side.
**There is still no premise about the child** — its derivation is
`exec cevm`. -/
lemma Ninst.stepRun_exec_run_error {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {cevm : Evm} {e : EvmError × Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .run cevm)
    (h_res : rsm.run (f.settle (exec cevm)) = .error e) :
    ∃ xl : Xlot, xl.Filled ∧
      ∀ pc, Ninst.StepRun pc sevm devm (.exec x) xl (.error e) := by
  refine ⟨.some ⟨cevm, exec cevm⟩, Xlot.filled_exec cevm, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨_, RunFrame.of_run h_enter, h_res.symm⟩

/-- The same for a frame that resolves without entering: no child exists, and
the resume of its `.done` result propagates the error. -/
lemma Ninst.stepRun_exec_doneFrame_error {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {e : EvmError × Devm}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .done r) (h_res : rsm.run r = .error e) :
    ∃ xl : Xlot, xl.Filled ∧
      ∀ pc, Ninst.StepRun pc sevm devm (.exec x) xl (.error e) := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨r, RunFrame.of_done h_enter, h_res.symm⟩

/-- The program altitude: entry `JUMPDEST`, then the main `Func`'s evidence. -/
def Prog.ExecTo (sevm : Sevm) (devm : Devm) (p : Prog) (ex : Execution) : Prop :=
  ∃ mid, Devm.BurnBy gJumpdest devm mid ∧
    Func.ExecTo (p.main :: p.aux) sevm mid p.main ex

/-- **The bridge.**  `ExecTo` evidence at a compiled program *is* the total
`exec`'s value at pc 0 — the mirror of `Prog.exec_of_runCompiledTo`, consumed
by statements whose outcome cannot stay inside `Func.RunCompiledTo` because a
spawning instruction may fail. -/
theorem Prog.exec_of_execTo {sevm : Sevm} {pre : Devm} {p : Prog}
    {ex : Execution}
    (h : Prog.ExecTo sevm pre p ex)
    (h_eq : some sevm.code.toList = p.compile) :
    exec ⟨0, sevm, pre⟩ = ex := by
  rcases h with ⟨mid, h_burn, h_run⟩
  have h_eq' : some sevm.code.toList = Prog.compile ⟨p.main, p.aux⟩ := h_eq
  have h_get : (table 0 (p.main :: p.aux))[0]? = some (0, p.main) := rfl
  rcases subcode_of_get?_eq_some h_eq' h_get with ⟨h_jd, h_sub⟩
  have h_npb : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table h_eq' h_get).2
  have h1 : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont h_jd h_burn
  obtain ⟨exc⟩ := h_run p.main p.aux rfl h_eq' 1 h_sub h_npb
  rw [← exec_iff_exec_eq]
  exact ⟨Exec.cont h1 exc⟩

/-! ## `ExecSat` — success carries the compiled walk

A statement like a settlement trichotomy does not know its outcome up front:
which disjunct holds is decided by a case analysis *inside* the walk, on facts
about states the walk itself introduces.  A relation whose outcome is a fixed
parameter cannot carry that — the continuation-passing steps universally
quantify their successor states, so no single outcome term can be named before
the case split.  `ExecSat` is the fix: the outcome is existential, constrained
only by a predicate, and every walk step threads the pair through.  Its witness
is deliberately asymmetric: a successful outcome retains the actual
`RunCompiled` walk required by the public code bridge; only a fatal outcome,
which `RunCompiled` cannot express, falls back to `ExecTo`. -/

/-- Evidence appropriate to an outcome: a real compiled walk on success, and
execution evidence only for the fatal terminal that the walk relation cannot
represent. -/
def Func.ExecWitness (fs : List Func) (sevm : Sevm) (devm : Devm) (f : Func) :
    Execution → Prop
  | .ok post => Func.RunCompiled fs sevm devm f post
  | .error err => Func.ExecTo fs sevm devm f (.error err)

/-- The program-altitude form of `Func.ExecWitness`. -/
def Prog.ExecWitness (sevm : Sevm) (devm : Devm) (p : Prog) : Execution → Prop
  | .ok post => Prog.RunCompiled sevm devm p post
  | .error err => Prog.ExecTo sevm devm p (.error err)

/-- Some outcome satisfying `P` is reachable: the existential the case tree
under a `CALL` needs. -/
def Func.ExecSat (fs : List Func) (sevm : Sevm) (devm : Devm) (f : Func)
    (P : Execution → Prop) : Prop :=
  ∃ ex, Func.ExecWitness fs sevm devm f ex ∧ P ex

/-- The program altitude of `Func.ExecSat`. -/
def Prog.ExecSat (sevm : Sevm) (devm : Devm) (p : Prog)
    (P : Execution → Prop) : Prop :=
  ∃ ex, Prog.ExecWitness sevm devm p ex ∧ P ex

/-- What `ExecSat` is for: the predicate holds of the total `exec`'s value. -/
theorem Prog.execSat_out {sevm : Sevm} {pre : Devm} {p : Prog}
    {P : Execution → Prop}
    (h : Prog.ExecSat sevm pre p P)
    (h_eq : some sevm.code.toList = p.compile) :
    P (exec ⟨0, sevm, pre⟩) := by
  rcases h with ⟨ex, hw, hp⟩
  cases ex with
  | ok post =>
      rw [Prog.exec_of_runCompiled hw h_eq]
      exact hp
  | error err =>
      rw [Prog.exec_of_execTo hw h_eq]
      exact hp

/-- The program entry, mirroring `Prog.runCompiledTo_intro`. -/
lemma Prog.execSat_intro {sevm : Sevm} {devm mid : Devm} {p : Prog}
    {P : Execution → Prop} {G : Nat}
    (h_gas : devm.gasLeft = G + gJumpdest)
    (h_mid : mid = devm.setMach ⟨devm.stack, devm.memory, G⟩)
    (h_main : Func.ExecSat (p.main :: p.aux) sevm mid p.main P) :
    Prog.ExecSat sevm devm p P := by
  rcases h_main with ⟨ex, hw, hp⟩
  subst h_mid
  refine ⟨ex, ?_, hp⟩
  cases ex <;> exact ⟨_, Devm.burnBy_setMach_gas h_gas, hw⟩

/-- A segment of ordinary instructions, threaded through the existential: the
transformer premise is a fixed-outcome witness implication, which is exactly
the shape the registered `ExecWitness` relation lets `func_run` prove directly:
walk the goal once, then close the residue with the hypothesis. -/
lemma Func.execSat_segment {fs : List Func} {sevm : Sevm} {devm devm' : Devm}
    {f f' : Func} {P : Execution → Prop}
    (h_seg : ∀ ex, Func.ExecWitness fs sevm devm' f' ex →
      Func.ExecWitness fs sevm devm f ex)
    (h : Func.ExecSat fs sevm devm' f' P) : Func.ExecSat fs sevm devm f P := by
  rcases h with ⟨ex, hw, hp⟩
  exact ⟨ex, h_seg ex hw, hp⟩

/-- One successful instruction preserves the outcome-appropriate witness. -/
lemma Func.ExecWitness.next {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i : Ninst} {devm' : Devm} {f : Func} {ex : Execution}
    (h_n : Ninst.RunCompiled sevm devm i devm')
    (h_f : Func.ExecWitness fs sevm devm' f ex) :
    Func.ExecWitness fs sevm devm (.next i f) ex := by
  cases ex with
  | ok post => exact Func.RunCompiled.next h_n h_f
  | error err => exact Func.execTo_next h_n h_f

/-- The zero branch preserves the outcome-aware witness.  These structural
rules register `ExecWitness` with the shared `func_run` walk without splitting
and re-elaborating every instruction prefix at each use site. -/
lemma Func.execWitness_branch_zero {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f g : Func} {ex : Execution} {s : List B256} {G : Nat}
    (h_stk : devm.stack = 0 :: s) (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh))
    (h_arm : Func.ExecWitness fs sevm
      (devm.setMach ⟨s, devm.memory, G⟩) f ex) :
    Func.ExecWitness fs sevm devm (.branch f g) ex := by
  cases ex with
  | ok post => exact Func.runCompiled_branch_zero h_stk h_room h_gas h_arm
  | error err => exact Func.execTo_branch_zero h_stk h_room h_gas h_arm

/-- The nonzero branch preserves the outcome-aware witness. -/
lemma Func.execWitness_branch_succ {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f g : Func} {ex : Execution} {w : B256} {s : List B256}
    {G : Nat} (h_ne : w ≠ 0) (h_stk : devm.stack = w :: s)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh + gJumpdest))
    (h_arm : Func.ExecWitness fs sevm
      (devm.setMach ⟨s, devm.memory, G⟩) g ex) :
    Func.ExecWitness fs sevm devm (.branch f g) ex := by
  cases ex with
  | ok post => exact Func.runCompiled_branch_succ h_ne h_stk h_room h_gas h_arm
  | error err => exact Func.execTo_branch_succ h_ne h_stk h_room h_gas h_arm

/-- An internal tail call preserves the outcome-aware witness. -/
lemma Func.execWitness_call' {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k : Nat} {f : Func} {ex : Execution} {G : Nat} (h_get : fs[k]? = some f)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gMid + gJumpdest))
    (h_body : Func.ExecWitness fs sevm
      (devm.setMach ⟨devm.stack, devm.memory, G⟩) f ex) :
    Func.ExecWitness fs sevm devm (.call k) ex := by
  cases ex with
  | ok post => exact Func.runCompiled_call' h_get h_room h_gas h_body
  | error err => exact Func.execTo_call' h_get h_room h_gas h_body

/-- One successful instruction, threaded through the existential. -/
lemma Func.execSat_next {fs : List Func} {sevm : Sevm} {devm devm' : Devm}
    {i : Ninst} {f : Func} {P : Execution → Prop}
    (h_n : Ninst.RunCompiled sevm devm i devm')
    (h_f : Func.ExecSat fs sevm devm' f P) :
    Func.ExecSat fs sevm devm (.next i f) P := by
  rcases h_f with ⟨ex, hw, hp⟩
  exact ⟨ex, Func.ExecWitness.next h_n hw, hp⟩

/-- A complete residual walk closes an `ExecSat` goal: the leaf terminal. -/
lemma Func.execSat_of_runCompiledTo {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f : Func} {ex : Execution} {P : Execution → Prop}
    (h : Func.RunCompiledTo fs sevm devm f ex) (hp : P ex) :
    Func.ExecSat fs sevm devm f P := by
  refine ⟨ex, ?_, hp⟩
  cases ex with
  | ok post => exact Func.RunCompiled.of_runCompiledTo_ok h
  | error err => exact Func.ExecTo.of_runCompiledTo h

/-- The fatal terminal: a spawning instruction fails, the frame settles at the
error right there, and the predicate is met on the error side. -/
lemma Func.execSat_next_error {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i : Ninst} {rest : Func} {e : EvmError × Devm} {P : Execution → Prop}
    (h : ∃ xl : Xlot, xl.Filled ∧
      ∀ pc, Ninst.StepRun pc sevm devm i xl (.error e))
    (hp : P (.error e)) :
    Func.ExecSat fs sevm devm (.next i rest) P :=
  ⟨.error e, Func.execTo_next_error h, hp⟩

/-! ### The continuation-passing steps, threaded through the existential

Positional siblings of the five `Func.runCompiledTo_*_step` lemmas above, for
walks whose outcome is decided by a case analysis further down.  Same premises,
same handed-back facts; only the relation differs, so each proof is its
sibling's with the pair threaded. -/

/-- `SLOAD` as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_sload_step`. -/
lemma Func.execSat_sload_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k v : B256} {s : List B256} {M : Mem} {rest : Func} {P : Execution → Prop}
    (h_stk : devm.stack = k :: s) (h_room : s.length < 1024)
    (h_val : devm.getStorVal sevm.currentTarget k = v)
    (h_mem : devm.memory = M)
    (h_gas : gasColdSload ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ base.accessedStorageKeys →
      (∀ p : Adr × B256, p ∈ devm.accessedStorageKeys →
        p ∈ base.accessedStorageKeys) →
      (∀ (a : Adr) (k' : B256), base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.refundCounter = devm.refundCounter →
      base.logs = devm.logs →
      base.output = devm.output →
      base.error = devm.error →
      base.accountsToDelete = devm.accountsToDelete →
      gasWarmAccess ≤ c → c ≤ gasColdSload →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (base.setMach ⟨v :: s, M, G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next Ninst.sload rest) P := by
  subst h_val; subst h_mem
  set base : Devm :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then devm else addAccessedStorageKey devm sevm.currentTarget k with h_base
  set c : Nat :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys
    then gasWarmAccess else gasColdSload with h_c
  have h_lo : gasWarmAccess ≤ c := (le_sload_cost_of h_c.symm).1
  have h_hi : c ≤ gasColdSload := (le_sload_cost_of h_c.symm).2
  rcases h_next base c (devm.gasLeft - c)
      (mem_accessedStorageKeys_sload_of h_base.symm)
      (fun _ hp => mem_accessedStorageKeys_sload_of_mem h_base.symm hp)
      (fun _ _ => getStorVal_sload_of h_base.symm)
      (fun _ => by rw [h_base]; split <;> rfl)
      (fun _ => by rw [h_base]; split <;> rfl)
      (refundCounter_sload_of h_base.symm) (logs_sload_of h_base.symm)
      (by rw [h_base]; split <;> rfl)
      (by rw [h_base]; split <;> rfl)
      (by rw [h_base]; split <;> rfl)
      h_lo h_hi (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.ExecWitness.next
    (Ninst.runCompiled_sload_of (base := base) (c := c) (G := devm.gasLeft - c)
      h_stk h_base.symm h_c.symm rfl (by omega) h_room) hto, hp⟩

/-- `SSTORE` on a warm key as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_sstore_warm_step`. -/
lemma Func.execSat_sstore_warm_step {fs : List Func} {sevm : Sevm}
    {devm : Devm} {k v : B256} {s : List B256} {M : Mem} {rest : Func}
    {P : Execution → Prop}
    (h_stk : devm.stack = k :: v :: s)
    (h_warm : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ devm.accessedStorageKeys)
    (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_gas : gasStorageSet ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (c G : Nat),
      base.getStorVal sevm.currentTarget k = v →
      (∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
      base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.logs = devm.logs →
      base.output = devm.output →
      base.error = devm.error →
      base.accountsToDelete = devm.accountsToDelete →
      base.refundCounter = sstoreNewRefundCounter v
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) devm.refundCounter →
      c ≤ gasStorageSet →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (base.setMach ⟨s, M, G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next Ninst.sstore rest) P := by
  subst h_mem
  have h_bound : sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v ≤ gasStorageSet := by
    rw [sstoreValueCost]; split_ifs <;> decide
  have h_key : ((devm.withRefundCounter (sstoreNewRefundCounter v
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k)
      devm.refundCounter)).setStorVal sevm.currentTarget k v).getStorVal
        sevm.currentTarget k = v := by
    show (Devm.getStor _ sevm.currentTarget).get k = v
    rw [setStorVal_getStor_self, Stor.get_set_self]
  have h_oth : ∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
      ((devm.withRefundCounter (sstoreNewRefundCounter v
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k)
        devm.refundCounter)).setStorVal sevm.currentTarget k v).getStorVal a k'
          = devm.getStorVal a k' := by
    intro a k' h_ne
    by_cases h_adr : sevm.currentTarget = a
    · subst h_adr
      have h_key' : k ≠ k' := fun h => h_ne (by rw [h])
      show (Devm.getStor _ sevm.currentTarget).get k' = _
      rw [setStorVal_getStor_self, Stor.get_set_ne _ h_key']
      rfl
    · show (Devm.getStor _ a).get k' = _
      have h_off : Devm.getStor
          ((devm.withRefundCounter (sstoreNewRefundCounter v
            (getOrigStorVal sevm sevm.currentTarget k)
            (devm.getStorVal sevm.currentTarget k)
            devm.refundCounter)).setStorVal sevm.currentTarget k v) a
            = Devm.getStor devm a := by
        simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
          Devm.setWorld, State.setStorVal]
        simp only [Devm.state, State.get_set_ne _ h_adr]
        rfl
      rw [h_off]
      rfl
  rcases h_next _ _ (devm.gasLeft - sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v)
      h_key h_oth
      (fun a => by
        have hbc := State.setStorVal_balCodeEq devm.state sevm.currentTarget k v
        exact (congrArg Prod.fst (congrFun hbc a)).symm)
      (fun a => by
        have hbc := State.setStorVal_balCodeEq devm.state sevm.currentTarget k v
        exact (congrArg Prod.snd (congrFun hbc a)).symm)
      rfl rfl rfl rfl rfl rfl h_bound (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.ExecWitness.next
    (Ninst.runCompiled_sstore_warm (c := sstoreValueCost
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      (G := devm.gasLeft - sstoreValueCost
        (getOrigStorVal sevm sevm.currentTarget k)
        (devm.getStorVal sevm.currentTarget k) v)
      h_stk h_warm (by simp only [gCallStipend, gasStorageSet] at *; omega)
      h_static rfl rfl (by omega)) hto, hp⟩

/-- `MSTORE` as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_mstore_step`. -/
lemma Func.execSat_mstore_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i v : B256} {s : List B256} {c : Nat} {M : Mem} {rest : Func}
    {P : Execution → Prop}
    (h_stk : devm.stack = i :: v :: s)
    (h_mem : devm.memory = M)
    (h_cost : gVerylow + devm.extCost [⟨i.toNat, 32⟩] = c)
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (M' : Mem) (G : Nat), M.write i.toNat v.toBytes = M' →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (devm.setMach ⟨s, M', G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next Ninst.mstore rest) P := by
  subst h_mem
  rcases h_next _ (devm.gasLeft - c) rfl (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.ExecWitness.next
    (Ninst.runCompiled_mstore_of (G := devm.gasLeft - c) (e := devm.extCost
      [⟨i.toNat, 32⟩]) h_stk rfl (by omega) rfl) hto, hp⟩

/-- `LOG n` as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_log_step`. -/
lemma Func.execSat_log_step {fs : List Func} {sevm : Sevm} {devm : Devm}
    {n : Fin 5} {i sz : B256} {topics s : List B256} {c : Nat} {M M' : Mem}
    {payload : Bytes} {rest : Func} {P : Execution → Prop}
    (h_stk : devm.stack = i :: sz :: (topics ++ s))
    (h_len : topics.length = n.val) (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_cost : gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩] = c)
    (h_data : (M.read i.toNat sz.toNat).1 = payload)
    (h_img : (M.read i.toNat sz.toNat).2 = M')
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (base : Devm) (G : Nat),
      base.logs = devm.logs ++ [⟨sevm.currentTarget, topics, payload⟩] →
      (∀ (a : Adr) (k : B256), base.getStorVal a k = devm.getStorVal a k) →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.refundCounter = devm.refundCounter →
      base.output = devm.output →
      base.error = devm.error →
      base.accountsToDelete = devm.accountsToDelete →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (base.setMach ⟨s, M', G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next (.reg (.log n)) rest) P := by
  subst h_mem
  rcases h_next (devm.addLog ⟨sevm.currentTarget, topics, payload⟩)
      (devm.gasLeft - c) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
      rfl rfl rfl rfl rfl (by omega)
    with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.ExecWitness.next
    (Ninst.runCompiled_log_of (G := devm.gasLeft - c) h_stk h_len h_static
      h_cost h_data h_img (by omega)) hto, hp⟩

/-- `CALLDATACOPY` as an `ExecSat` walk step.  Sibling of
`Func.runCompiledTo_calldatacopy_step`. -/
lemma Func.execSat_calldatacopy_step {fs : List Func} {sevm : Sevm}
    {devm : Devm} {di si sz : B256} {s : List B256} {c : Nat} {M : Mem}
    {rest : Func} {P : Execution → Prop}
    (h_stk : devm.stack = di :: si :: sz :: s)
    (h_mem : devm.memory = M)
    (h_cost : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + devm.extCost [⟨di.toNat, sz.toNat⟩] = c)
    (h_gas : c ≤ devm.gasLeft)
    (h_next : ∀ (M' : Mem) (G : Nat),
      M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0) = M' →
      devm.gasLeft = G + c →
      Func.ExecSat fs sevm (devm.setMach ⟨s, M', G⟩) rest P) :
    Func.ExecSat fs sevm devm (Func.next (.reg .calldatacopy) rest) P := by
  subst h_mem
  rcases h_next _ (devm.gasLeft - c) rfl (by omega) with ⟨ex, hto, hp⟩
  exact ⟨ex, Func.ExecWitness.next
    (Ninst.runCompiled_calldatacopy_of (G := devm.gasLeft - c) h_stk h_cost
      rfl (by omega)) hto, hp⟩

/-! ## The `.call` arm's remaining shapes, and its world-dependent inputs

The crossing lemma family above (`Xinst.step_call_zero_value*`) covers the
spawn; a settlement statement also meets the **depth-limit arm** — at
`sevm.depth = 0` no child is spawned and the instruction answers `0` — and has
to price the world-dependent inputs it cannot compute: the delegation
resolution and the access cost.  Neither is knowable from the frame, so both
are *bounded*, which is all a closed gas bound needs. -/

/-- The delegation resolution moves only the accessed-address set: the machine
fields a continuation walks with are untouched, and the extra charge is at most
one cold account access. -/
lemma accessDelegation_inv {devm d1 : Devm} {a dadr : Adr} {dp : Bool}
    {code : ByteArray} {dgc : Nat}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    d1.stack = devm.stack ∧ d1.memory = devm.memory ∧
      d1.gasLeft = devm.gasLeft ∧ dgc ≤ gasColdAccountAccess := by
  unfold accessDelegation at h
  rcases hd : getDelegatedCodeAddress (devm.state.getCode a) with _ | adr <;>
    simp only [hd] at h
  · cases h
    exact ⟨rfl, rfl, rfl, by decide⟩
  · cases h
    refine ⟨rfl, rfl, rfl, ?_⟩
    unfold accessCost
    split <;> decide

/-- And it leaves the settled-error field alone, which is how a frame-level
statement carries "this frame never stored a halt" across the `CALL`. -/
lemma accessDelegation_error {devm d1 : Devm} {a dadr : Adr} {dp : Bool}
    {code : ByteArray} {dgc : Nat}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    d1.error = devm.error := by
  unfold accessDelegation at h
  rcases hd : getDelegatedCodeAddress (devm.state.getCode a) with _ | adr <;>
    simp only [hd] at h
  · cases h; rfl
  · cases h; rfl

/-- Delegation resolution changes only access metadata; the world and the
frame-local result fields used by an enclosing successful call are unchanged. -/
lemma accessDelegation_frame {devm d1 : Devm} {a dadr : Adr} {dp : Bool}
    {code : ByteArray} {dgc : Nat}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    d1.state = devm.state ∧ d1.logs = devm.logs ∧
      d1.refundCounter = devm.refundCounter ∧
      d1.accountsToDelete = devm.accountsToDelete ∧
      d1.output = devm.output := by
  unfold accessDelegation at h
  rcases hd : getDelegatedCodeAddress (devm.state.getCode a) with _ | adr <;>
    simp only [hd] at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The account-access charge is at most the cold price. -/
lemma accessCost_le {x : Adr} {a : AdrSet} : accessCost x a ≤ gasColdAccountAccess := by
  unfold accessCost
  split <;> decide

/-- Once the caller can pay the fixed call overhead and memory expansion,
`calculateMsgCallGas`'s charged component is affordable.  The EIP-150 `min`
can only reduce the forwarded part. -/
lemma calculateMsgCallGas_cost_le {value gas gasLeft mem extra : Nat}
    (h : extra + mem ≤ gasLeft) :
    (calculateMsgCallGas value gas gasLeft mem extra).1 + mem ≤ gasLeft := by
  unfold calculateMsgCallGas
  rw [if_neg (not_lt_of_ge h)]
  dsimp only []
  have hmin : min gas (except64th (gasLeft - mem - extra)) ≤
      except64th (gasLeft - mem - extra) := Nat.min_le_right _ _
  have hexcept : except64th (gasLeft - mem - extra) ≤
      gasLeft - mem - extra := Nat.sub_le _ _
  omega

/-- An affordable value-bearing `CALL` to a code-free non-precompile account
constructs a clean child and resumes with success flag `1`.  Child success is
derived from the empty code here; it is not a premise.  The exposed machine
projections are exactly the facts a caller's post-`CALL` guard consumes. -/
lemma Ninst.runCompiled_call_nonzero_codeFree {sevm : Sevm} {devm : Devm}
    {gw cw vw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc create mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: vw :: iiw :: isw :: oiw :: osw :: s)
    (h_value : vw ≠ 0)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_create :
      (if ¬ (d1.getAcct cw.toAdr).Empty then 0 else gNewAccount) = create)
    (h_split :
      calculateMsgCallGas vw.toNat gw.toNat d1.gasLeft ext
        (acc + create + gasCallValue) = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_dynamic : sevm.isStatic = false)
    (h_sender : ¬ (d1.getAcct sevm.currentTarget).bal < vw)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_code : code.size = 0) (h_room : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .call) post ∧
      post.stack = 1 :: s ∧
      post.memory = devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] ∧
      post.gasLeft = d1.gasLeft - (mcc + ext) + mcs ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = [] ∧ post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget vw = some stmid ∧
        post.state = stmid.addBal cw.toAdr vw := by
  let p := callSpawnParent d1 (mcc + ext)
    iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := valueCallSpawnMsg sevm p mcs vw cw.toAdr dadr
    iiw.toNat isw.toNat code dp
  have h_afford : ¬ msg.benv.state.bal msg.caller < msg.value := by
    change ¬ (d1.getAcct sevm.currentTarget).bal < vw
    exact h_sender
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable msg rfl h_afford
  let benv' := (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  let child := initEvm (msg.withBenv benv')
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have h_child_code : child.sta.code.size = 0 := by
    change code.size = 0
    exact h_code
  have hexec : exec child = .ok child.dyna :=
    exec_empty_code child h_child_code
  have hsettle : (Frame.ofCall msg).settle (exec child) = .ok child.dyna := by
    rw [hexec]
    rfl
  have hdi := accessDelegation_inv h_del
  have hd1stack : d1.stack = s := by
    have h := hdi.1
    change d1.stack = s at h
    exact h
  have hd1mem : d1.memory = devm.memory := by
    have h := hdi.2.1
    change d1.memory = devm.memory at h
    exact h
  have hd1frame := accessDelegation_frame h_del
  have hd1error := accessDelegation_error h_del
  have hd1state : d1.state = devm.state := hd1frame.1
  have hd1logs : d1.logs = devm.logs := hd1frame.2.1
  have hd1refund : d1.refundCounter = devm.refundCounter := hd1frame.2.2.1
  have hd1delete : d1.accountsToDelete = devm.accountsToDelete :=
    hd1frame.2.2.2.1
  have hd1output : d1.output = devm.output := hd1frame.2.2.2.2
  have hd1error' : d1.error = devm.error := hd1error
  have hpstack : p.stack.length < 1024 := by
    change d1.stack.length < 1024
    rw [hd1stack]
    exact h_room
  let post := (((incorporateChildOnSuccess p child.dyna child.dyna.output).setMach
    ⟨1 :: p.stack, p.memory, p.gasLeft + child.dyna.gasLeft⟩).memWrite
      oiw.toNat (child.dyna.output.take osw.toNat))
  have hres : Resume.run (.call p oiw.toNat osw.toNat)
      ((Frame.ofCall msg).settle (exec child)) = .ok post := by
    rw [hsettle, Resume.run_call_ok (by rfl) hpstack]
  have hrun : Ninst.RunCompiled sevm devm (.exec .call) post :=
    Ninst.runCompiled_call_nonzero h_stk h_value h_ext h_del h_acc h_create
      h_split h_gas h_dynamic h_sender h_depth
        (by simpa [p, msg]) (by simpa [p, msg] using hres)
  have hout : child.dyna.output = [] := rfl
  have hpostError : post.error = p.error := by
    dsimp only [post]
    rw [hout, List.take_nil, Devm.memWrite_nil]
    rfl
  have hpostOutput : post.output = p.output := by
    dsimp only [post]
    rw [hout, List.take_nil, Devm.memWrite_nil]
    rfl
  have hpostReturnData : post.returnData = [] := by
    dsimp only [post]
    rw [hout, List.take_nil, Devm.memWrite_nil]
    rfl
  have hpostLogs : post.logs = p.logs := by
    dsimp only [post]
    rw [hout, List.take_nil, Devm.memWrite_nil]
    exact List.append_nil _
  have hpostRefund : post.refundCounter = p.refundCounter := by
    dsimp only [post, child, initEvm, initDevm]
    change p.refundCounter + 0 = p.refundCounter
    omega
  have hpostDelete :
      post.accountsToDelete.isEmpty = p.accountsToDelete.isEmpty := by
    dsimp only [post, child, initEvm, initDevm]
    change (p.accountsToDelete.union
      Std.HashSet.emptyWithCapacity).isEmpty = p.accountsToDelete.isEmpty
    simp
  have hpostState : post.state = stmid.addBal cw.toAdr vw := by
    dsimp only [post, child, benv', initEvm, initDevm]
    rfl
  have hfields :
      post.stack = 1 :: p.stack ∧ post.memory = p.memory ∧
        post.gasLeft = p.gasLeft + mcs := by
    dsimp only [post]
    have hchildgas : child.dyna.gasLeft = mcs := rfl
    simp only [hout, List.take_nil, Devm.memWrite_nil, Devm.stack_setMach,
      Devm.memory_setMach, Devm.gasLeft_setMach, hchildgas]
    exact ⟨trivial, trivial, trivial⟩
  refine ⟨post, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, stmid, ?_, ?_⟩
  · rw [hfields.1]
    exact congrArg (1 :: ·) hd1stack
  · rw [hfields.2.1]
    change d1.memory.extends [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = _
    rw [hd1mem]
  · simpa [p, callSpawnParent] using hfields.2.2
  · rw [hpostError]
    exact (show p.error = d1.error from rfl).trans hd1error'
  · rw [hpostOutput]
    exact (show p.output = d1.output from rfl).trans hd1output
  · exact hpostReturnData
  · rw [hpostLogs]
    exact (show p.logs = d1.logs from rfl).trans hd1logs
  · rw [hpostRefund]
    exact (show p.refundCounter = d1.refundCounter from rfl).trans hd1refund
  · rw [hpostDelete]
    change d1.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty
    rw [hd1delete]
  · rw [← hd1state]
    have hsub' : p.state.subBal sevm.currentTarget vw = some stmid := by
      simpa [msg, valueCallSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsub'
    exact hsub'
  · exact hpostState

/-- A zero-value `CALL` to a code-free non-precompile account likewise enters
an empty child and resumes with success flag `1`.  This packages the existing
zero-value crossing without assuming anything about a child result. -/
lemma Ninst.runCompiled_call_zero_value_codeFree {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_code : code.size = 0) (h_room : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .call) post ∧
      post.stack = 1 :: s ∧
      post.memory = devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] ∧
      post.gasLeft = d1.gasLeft - (mcc + ext) + mcs ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = [] ∧ post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal cw.toAdr 0 := by
  let p := callSpawnParent d1 (mcc + ext)
    iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := callSpawnMsg sevm p mcs cw.toAdr dadr
    iiw.toNat isw.toNat code dp
  have h_afford : ¬ msg.benv.state.bal msg.caller < msg.value := by
    change ¬ (d1.getAcct sevm.currentTarget).bal < 0
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _)
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable msg rfl h_afford
  let benv' := (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  let child := initEvm (msg.withBenv benv')
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have h_child_code : child.sta.code.size = 0 := by
    change code.size = 0
    exact h_code
  have hexec : exec child = .ok child.dyna :=
    exec_empty_code child h_child_code
  have hsettle : (Frame.ofCall msg).settle (exec child) = .ok child.dyna := by
    rw [hexec]
    rfl
  have hdi := accessDelegation_inv h_del
  have hd1stack : d1.stack = s := by
    have h := hdi.1
    change d1.stack = s at h
    exact h
  have hd1mem : d1.memory = devm.memory := by
    have h := hdi.2.1
    change d1.memory = devm.memory at h
    exact h
  have hd1frame := accessDelegation_frame h_del
  have hd1error := accessDelegation_error h_del
  have hd1state : d1.state = devm.state := hd1frame.1
  have hd1logs : d1.logs = devm.logs := hd1frame.2.1
  have hd1refund : d1.refundCounter = devm.refundCounter := hd1frame.2.2.1
  have hd1delete : d1.accountsToDelete = devm.accountsToDelete :=
    hd1frame.2.2.2.1
  have hd1output : d1.output = devm.output := hd1frame.2.2.2.2
  have hd1error' : d1.error = devm.error := hd1error
  have hpstack : p.stack.length < 1024 := by
    change d1.stack.length < 1024
    rw [hd1stack]
    exact h_room
  let post := (((incorporateChildOnSuccess p child.dyna child.dyna.output).setMach
    ⟨1 :: p.stack, p.memory, p.gasLeft + child.dyna.gasLeft⟩).memWrite
      oiw.toNat (child.dyna.output.take osw.toNat))
  have hres : Resume.run (.call p oiw.toNat osw.toNat)
      ((Frame.ofCall msg).settle (exec child)) = .ok post := by
    rw [hsettle, Resume.run_call_ok (by rfl) hpstack]
  have hrun : Ninst.RunCompiled sevm devm (.exec .call) post :=
    Ninst.runCompiled_call_zero_value h_stk h_ext h_del h_acc h_split h_gas
      h_depth (by simpa [p, msg]) (by simpa [p, msg] using hres)
  have hout : child.dyna.output = [] := rfl
  have hpostError : post.error = p.error := by
    dsimp only [post]
    rw [hout, List.take_nil, Devm.memWrite_nil]
    rfl
  have hpostOutput : post.output = p.output := by
    dsimp only [post]
    rw [hout, List.take_nil, Devm.memWrite_nil]
    rfl
  have hpostReturnData : post.returnData = [] := by
    dsimp only [post]
    rw [hout, List.take_nil, Devm.memWrite_nil]
    rfl
  have hpostLogs : post.logs = p.logs := by
    dsimp only [post]
    rw [hout, List.take_nil, Devm.memWrite_nil]
    exact List.append_nil _
  have hpostRefund : post.refundCounter = p.refundCounter := by
    dsimp only [post, child, initEvm, initDevm]
    change p.refundCounter + 0 = p.refundCounter
    omega
  have hpostDelete :
      post.accountsToDelete.isEmpty = p.accountsToDelete.isEmpty := by
    dsimp only [post, child, initEvm, initDevm]
    change (p.accountsToDelete.union
      Std.HashSet.emptyWithCapacity).isEmpty = p.accountsToDelete.isEmpty
    simp
  have hpostState : post.state = stmid.addBal cw.toAdr 0 := by
    dsimp only [post, child, benv', initEvm, initDevm]
    rfl
  have hfields :
      post.stack = 1 :: p.stack ∧ post.memory = p.memory ∧
        post.gasLeft = p.gasLeft + mcs := by
    dsimp only [post]
    have hchildgas : child.dyna.gasLeft = mcs := rfl
    simp only [hout, List.take_nil, Devm.memWrite_nil, Devm.stack_setMach,
      Devm.memory_setMach, Devm.gasLeft_setMach, hchildgas]
    exact ⟨trivial, trivial, trivial⟩
  refine ⟨post, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, stmid, ?_, ?_⟩
  · rw [hfields.1]
    exact congrArg (1 :: ·) hd1stack
  · rw [hfields.2.1]
    change d1.memory.extends [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = _
    rw [hd1mem]
  · simpa [p, callSpawnParent] using hfields.2.2
  · rw [hpostError]
    exact (show p.error = d1.error from rfl).trans hd1error'
  · rw [hpostOutput]
    exact (show p.output = d1.output from rfl).trans hd1output
  · exact hpostReturnData
  · rw [hpostLogs]
    exact (show p.logs = d1.logs from rfl).trans hd1logs
  · rw [hpostRefund]
    exact (show p.refundCounter = d1.refundCounter from rfl).trans hd1refund
  · rw [hpostDelete]
    change d1.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty
    rw [hd1delete]
  · rw [← hd1state]
    have hsub' : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, callSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsub'
    exact hsub'
  · exact hpostState

/-- The depth-limit arm, packaged as the step interface: at `sevm.depth = 0`
the `CALL` charges, extends, pushes `0`, and hands the forwarded gas straight
back.  This is a *revert-path* case for a contract that branches on the flag,
never a premise. -/
lemma Ninst.runCompiled_call_zero_value_zero_depth {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth = 0)
    (h_room : d1.stack.length < 1024) :
    Ninst.RunCompiled sevm devm (.exec .call)
      ((((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
          [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).withReturnData
            []).setMach
        ⟨0 :: d1.stack,
          (d1.memory.extends [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]),
          d1.gasLeft - (mcc + ext) + mcs⟩) := by
  refine Ninst.runCompiled_exec_done ?_
  rw [Xinst.step_call_zero_value h_stk h_ext h_del h_acc h_split h_gas,
    genericCall.step_zero_depth h_depth (by
      show ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).stack.length < 1024
      exact h_room)]
  rfl

/-- Extending to already-covered windows leaves the image alone: the
`memExtends` a `CALL` performs after its charge is the identity whenever the
frame wrote its argument window first. -/
lemma Mem.extends_covered {N : Mem} {ps : List (Nat × Nat)}
    (h : memExtsSize N.size ps = N.size) : N.extends ps = N := by
  show (⟨N.data, memExtsSize N.size ps⟩ : Mem) = N
  rw [h]

/-- An access window the image already covers costs nothing. -/
lemma Devm.extCost_covered {devm : Devm} {S : List B256} {N : Mem} {G : Nat}
    {ws : List (Nat × Nat)} (h : memExtsSize N.size ws = N.size) :
    (devm.setMach ⟨S, N, G⟩).extCost ws = 0 := by
  simp only [Devm.extCost, Devm.memory_setMach, h]
  omega

/-! ### Reading the suspended parent

The three machine fields of `callSpawnParent`, as the continuation reads them.
All three are projections through `memExtends` and `withReturnData`, which
touch `mach.memory` and `meta` respectively. -/

lemma callSpawnParent_stack {d1 : Devm} {c ii is oi os : Nat} :
    (callSpawnParent d1 c ii is oi os).stack = d1.stack := rfl

lemma callSpawnParent_memory {d1 : Devm} {c ii is oi os : Nat} :
    (callSpawnParent d1 c ii is oi os).memory
      = d1.memory.extends [⟨ii, is⟩, ⟨oi, os⟩] := rfl

lemma callSpawnParent_gasLeft {d1 : Devm} {c ii is oi os : Nat} :
    (callSpawnParent d1 c ii is oi os).gasLeft = d1.gasLeft - c := rfl

/-- And the settled-error field, which the suspension does not touch either:
`withReturnData` writes `meta.returnData`, not `meta.error`. -/
lemma callSpawnParent_error {d1 : Devm} {c ii is oi os : Nat} :
    (callSpawnParent d1 c ii is oi os).error = d1.error := rfl

end Blanc
