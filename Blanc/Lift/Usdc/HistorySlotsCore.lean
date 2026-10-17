import Blanc.Lift.Usdc.RefineTransfer
import Blanc.Lift.Usdc.RefineAdmin
import Blanc.Lift.Usdc.RefineDispatch
import Blanc.Lift.Usdc.ProxyOk
import Blanc.Lift.Usdc.ImplSpawns
import Blanc.Lift.Usdc.LibSpawns
import Blanc.Lift.StaticOnlyPrefix
import Blanc.ExecutionSpawnFrames
import Blanc.ExecutionModelAccounting
import Blanc.ExecutionCallerExclusion
import Blanc.ExecDeterminism
import Blanc.Lift.RetainedTargetCompleteness

/-!
# The proxy's slot invariant along one message run (U6b2)

The joint in-run induction behind `usdc_history_slots` and `usdc_history_settled_owner`.  The
carrier is the proxy's storage alone: `SlotInv U a₀ s` says that the implementation slot names the
implementation, the admin slot holds the checkpoint's admin word `a₀`, and the footprint ledger is
good.  `SlotsOk` is the motive of a depth induction through `lift_core_sem`, located by the proxy's
certified code (`proxySem`): a committed derivation entered with `SlotInv` ends with it, and every
committed descendant frame (`FrameQ`) is entered with it and, if it runs at the proxy, runs the
proxy (an entry), the implementation or the library.  The facts the history supplies about settled
frames (the three codes installed, governance F2) come in as `Avail` at every descendant.

* foreign nodes: same-frame steps keep the proxy's storage, a spawned child enters with it and
  hands back its committed storage or none (`Exec.spawn_seam`); a child at the proxy is an entry;
* the proxy frame (this file's `proxyFrame`, below in `HistorySlots.lean`): an admin caller has a
  getter (F2), no child and unchanged storage; any other caller forwards to the implementation;
* implementation frames (`implFrame`): the family laws (`ImplStepLaw`, `RescueLaw`, the
  initializers' revert at a good ledger) keep the slots and the ledger good, at the end and at
  every spawning node; children are library frames or entries;
* library frames (`libFrame`): no storage change along the chain, static entries only.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.Token

/-! ## The carrier and the frame facts -/

/-- The proxy's slot invariant: the implementation slot names the implementation, the admin slot
holds `a₀`, and the footprint ledger over `U` is good. -/
def SlotInv (U : Key → Prop) (a₀ : Adr) (s : Stor) : Prop :=
  s.get implSlot = usdcImpl.toB256 ∧ (s.get adminSlot).toAdr = a₀ ∧ (ledger U s).Good

theorem SlotInv.congr {U : Key → Prop} {a₀ : Adr} {s s' : Stor} (h : ∀ k, s'.get k = s.get k)
    (inv : SlotInv U a₀ s) : SlotInv U a₀ s' := by
  have hg : s'.get = s.get := funext h
  have ht : SlotFootprint.trackedWord Key.slot U s' = SlotFootprint.trackedWord Key.slot U s :=
    funext fun k => by simp only [SlotFootprint.trackedWord, h]
  have hl : ledger U s' = ledger U s := by
    simp only [ledger, ht, hg]
  obtain ⟨hi, ha, hgood⟩ := inv
  refine ⟨?_, ?_, ?_⟩
  · rw [h]; exact hi
  · rw [h]; exact ha
  · rw [hl]; exact hgood

/-- The three code kinds of a frame at the proxy, by code address. -/
def OwnerKind (P : Adr) (e : Sevm) : Prop :=
  (e.codeAddress = some P ∧ e.code = Proxy.code) ∨
    (e.codeAddress = some usdcImpl ∧ e.code = Impl.code) ∨
    (e.codeAddress = some usdcLib ∧ e.code = Lib.code)

/-- The three runtimes installed. -/
def Codes (P : Adr) (d : Devm) : Prop :=
  d.getCode P = Proxy.code ∧ d.getCode usdcImpl = Impl.code ∧ d.getCode usdcLib = Lib.code

/-- What the history supplies at a settled frame: the codes installed at its entry, and F2 for the
checkpoint's admin word `a₀`. -/
def Avail (P a₀ : Adr) (f : Exec.Frame) : Prop :=
  Codes P f.pre ∧ (IsEntry P f → f.sevm.caller = a₀ →
    Blanc.Sevm.selector f.sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970])

/-- What the induction delivers at a committed frame: the invariant at its entry and its end, and
its code kind if it runs at the proxy. -/
def FrameQ (P : Adr) (U : Key → Prop) (a₀ : Adr) (f : Exec.Frame) : Prop :=
  SlotInv U a₀ (f.pre.state.getStor P) ∧ SlotInv U a₀ (f.post.state.getStor P) ∧
    (f.sevm.currentTarget = P → OwnerKind P f.sevm)

/-- The admission at raw frames at the proxy: tracked keys and bounded calldata. -/
def slotEntry (U : Key → Prop) : Sevm → Devm → Prop := fun sevm _ =>
  (∀ k ∈ frameKeys sevm, U k) ∧ sevm.data.length < 2 ^ 256

/-- A frame entered at the proxy is an entry frame with the codes installed and F2. -/
def Here (P a₀ : Adr) (sevm : Sevm) (pre : Devm) : Prop :=
  sevm.currentTarget = P → sevm.codeAddress = some P ∧ Codes P pre ∧
    (sevm.caller = a₀ → Blanc.Sevm.selector sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970])

/-- **The induction motive.** -/
def SlotsOk (P : Adr) (U : Key → Prop) (a₀ : Adr) (pc : Nat) (sevm : Sevm) (pre : Devm)
    (out : Execution) : Prop :=
  ∀ run : Exec pc sevm pre out, out.commits = true → CoveredFork sevm.benvStat.fork →
    proxySem.At P pc sevm pre → Exec.FrameAdmitted P (slotEntry U) run → Here P a₀ sevm pre →
    (∀ f ∈ Exec.descendantFrames run, Avail P a₀ f) → SlotInv U a₀ (pre.state.getStor P) →
    (∀ post, out = .ok post → SlotInv U a₀ (post.state.getStor P)) ∧
      ∀ f ∈ Exec.descendantFrames run, FrameQ P U a₀ f

/-- The deeper-frame hypothesis of the induction. -/
abbrev Deeper (P : Adr) (U : Key → Prop) (a₀ : Adr) (k : Nat) : Prop :=
  ForallDeeperAtSem k P proxySem (fun pc s d e _ => SlotsOk P U a₀ pc s d e)

/-! ## Code facts -/

theorem proxy_nonempty : Proxy.code.toList ≠ [] := proxySem.ne_nil rfl

theorem proxy_undelegated : getDelegatedCodeAddress Proxy.code = none := by
  unfold getDelegatedCodeAddress
  simp only [proxySem.not_delegation (code := Proxy.code) rfl, ↓reduceIte]

theorem impl_undelegated : getDelegatedCodeAddress Impl.code = none := by
  unfold getDelegatedCodeAddress
  simp only [implSem.not_delegation (code := Impl.code) rfl, ↓reduceIte]

theorem impl_not_precompile {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) :
    ¬ sevm.benvStat.rules.isPrecomp usdcImpl :=
  hfork.cases (motive := fun f => ¬ (Fork.ruleSet f).isPrecomp usdcImpl)
    (by decide) (by decide) (by decide) (by decide)

theorem proxy_protected {d : Devm} {P : Adr} (h : d.getCode P = Proxy.code) :
    State.Protected d.state P :=
  State.Protected.of_code_ne_nil (by change (d.getCode P).toList ≠ []; rw [h]; exact proxy_nonempty)

theorem proxy_at_image {d : Devm} {P : Adr} (h : d.getCode P = Proxy.code) :
    some (d.getCode P).toList = proxySem.image := by
  rw [h]; rfl

theorem code_of_at {d : Devm} {P : Adr} (h : some (d.getCode P).toList = proxySem.image) :
    d.getCode P = Proxy.code :=
  bytes_eq_of_image h

theorem codes_keep {P : Adr} {d d' : Devm} (keep : ∀ a, (d.getCode a).toList ≠ [] →
    d'.getCode a = d.getCode a) (codes : Codes P d) : Codes P d' := by
  obtain ⟨hp, hi, hl⟩ := codes
  refine ⟨?_, ?_, ?_⟩
  · rw [keep P (by rw [hp]; exact proxy_nonempty), hp]
  · rw [keep usdcImpl (by rw [hi]; exact implSem.ne_nil rfl), hi]
  · rw [keep usdcLib (by rw [hl]; exact lib_toList_ne_nil), hl]

/-- A committed run's `post` conclusion at its committed post state. -/
theorem post_of_commits {S : Devm → Prop} {out : Execution} (h : out.commits = true)
    (post : ∀ p, out = .ok p → S p) : S (Execution.committedPost out h) := by
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at h
  | ok p => exact post p rfl

/-- An entry child: a `CALL`/`STATICCALL` from a node at the proxy back into the proxy runs the
proxy's code at code address `P`. -/
theorem entry_child {P : Adr} {sevm : Sevm} {d : Devm} {x : Xinst} {f : Frame} {rsm : Resume}
    {cevm : Evm} (kind : x = .call ∨ x = .staticcall)
    (spawn : Xinst.step sevm d x = .spawn f rsm) (enter : f.enter = .run cevm)
    (codeP : d.getCode P = Proxy.code) (target : cevm.sta.currentTarget = P) :
    cevm.sta.codeAddress = some P ∧
      (sevm.currentTarget = P → cevm.sta.code = Proxy.code) := by
  have innerTarget : f.inner.currentTarget = P := by
    rw [← Frame.enter_run_currentTarget enter, target]
  refine ⟨?_, fun same => ?_⟩
  · rw [Frame.enter_run_codeAddress enter, Xinst.step_callKind_spawn_codeAddress kind spawn
      (by rw [innerTarget, codeP]; exact proxy_undelegated), innerTarget]
  · have sameTarget : f.inner.currentTarget = sevm.currentTarget := by rw [innerTarget, same]
    have notDel : ¬ isValidDelegation (d.getCode f.inner.currentTarget) := by
      rw [innerTarget, codeP]; exact proxySem.not_delegation rfl
    rw [Frame.enter_run_code enter]
    rcases kind with rfl | rfl
    · rw [Xinst.step_call_sameTarget_code spawn sameTarget notDel, innerTarget, codeP]
    · rw [Xinst.step_staticcall_sameTarget_code spawn sameTarget notDel, innerTarget, codeP]

/-- **A child located by the proxy's code.**  Given the child's code and code address when it targets
the proxy, its entry facts and the motive at the child give its conclusion and its own `FrameQ`. -/
theorem child_slots {P : Adr} {U : Key → Prop} {a₀ : Adr} {cevm : Evm} {raw : Execution}
    (ih : proxySem.At P cevm.pc cevm.sta cevm.dyna → SlotsOk P U a₀ cevm.pc cevm.sta cevm.dyna raw)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (committed : raw.commits = true) (pcZero : cevm.pc = 0)
    (fork : CoveredFork cevm.sta.benvStat.fork) (codeP : cevm.dyna.getCode P = Proxy.code)
    (kind : cevm.sta.currentTarget = P → cevm.sta.codeAddress = some P ∧ cevm.sta.code = Proxy.code)
    (admitted : Exec.FrameAdmitted P (slotEntry U) child)
    (avail : Avail P a₀ (Exec.Frame.ofRun child committed))
    (below : ∀ f ∈ Exec.descendantFrames child, Avail P a₀ f)
    (inv : SlotInv U a₀ (cevm.dyna.state.getStor P)) :
    SlotInv U a₀ ((Execution.committedPost raw committed).state.getStor P) ∧
      FrameQ P U a₀ (Exec.Frame.ofRun child committed) ∧
      ∀ f ∈ Exec.descendantFrames child, FrameQ P U a₀ f := by
  have at_ : proxySem.At P cevm.pc cevm.sta cevm.dyna :=
    ⟨proxy_at_image codeP, fun t => ⟨by rw [(kind t).2]; rfl, pcZero⟩⟩
  have here : Here P a₀ cevm.sta cevm.dyna := fun t =>
    ⟨(kind t).1, avail.1, avail.2 ⟨t, (kind t).1⟩⟩
  obtain ⟨post, desc⟩ := ih at_ child committed fork at_ admitted here below inv
  have hpost := post_of_commits committed post
  exact ⟨hpost, ⟨inv, hpost, fun t => .inl (kind t)⟩, desc⟩

/-! ## Foreign nodes -/

section Foreign

variable {P : Adr} {U : Key → Prop} {a₀ : Adr}

theorem SlotsOk.error {pc : Nat} {sevm : Sevm} {pre : Devm} {e : EvmError × Devm} :
    SlotsOk P U a₀ pc sevm pre (.error e) := by
  intro _ committed
  simp only [Execution.commits, Bool.false_eq_true] at committed

theorem SlotsOk.nextNone {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst}
    {out : Execution} (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out) (targetNe : sevm.currentTarget ≠ P)
    (ih : SlotsOk P U a₀ (pc + n.size) sevm inter out) :
    SlotsOk P U a₀ pc sevm pre out := by
  intro run committed fork installed admitted _ avail inv
  rw [Exec.descendantFrames_eq_of_nextNone hat step run next] at avail ⊢
  have codeNe : (pre.getCode P).toList ≠ [] := fun empty =>
    (proxySem.ne_nil (installed.1.symm.trans (congrArg some empty))) rfl
  have codeEq := lift_core_sem.stepCode (xl := .none) trivial
    (by rw [Evm.step_next hat]; exact step) P codeNe
  have interAt : proxySem.At P (pc + n.size) sevm inter :=
    ⟨by rw [codeEq]; exact installed.1, fun t => (targetNe t).elim⟩
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have interAdmitted := admitted.of_descendants_of_ne targetNe
      (Exec.rawFrameDescendants_sub_of_stepNone hat step next run)
    have keep : inter.state.getStor P = pre.state.getStor P :=
      Ninst.foreignNone_getStor_eq fork step targetNe (State.Protected.of_image installed.1)
    exact ih next committed fork interAt interAdmitted (fun t => (targetNe t).elim) avail
      (by rw [keep]; exact inv)

theorem SlotsOk.jump {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {j : Jinst}
    {out : Execution} (hat : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out) (targetNe : sevm.currentTarget ≠ P)
    (ih : SlotsOk P U a₀ pc' sevm inter out) :
    SlotsOk P U a₀ pc sevm pre out := by
  intro run committed fork installed admitted _ avail inv
  rw [Exec.descendantFrames_eq_of_jump hat step run next] at avail ⊢
  have stateEq := Jinst.preserves_state step
  have interAt : proxySem.At P pc' sevm inter :=
    ⟨by simpa only [Devm.getCode, Devm.getAcct, stateEq] using installed.1,
      fun t => (targetNe t).elim⟩
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have interAdmitted := admitted.of_descendants_of_ne targetNe
      (Exec.rawFrameDescendants_sub_of_jump hat step next run)
    exact ih next committed fork interAt interAdmitted (fun t => (targetNe t).elim) avail
      (by rw [stateEq]; exact inv)

theorem SlotsOk.last {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst} {out : Execution}
    (hat : Linst.At sevm.code pc l) (step : Linst.Run sevm pre l out) :
    SlotsOk P U a₀ pc sevm pre out := by
  intro run _ _ installed _ _ _ inv
  rw [Exec.descendantFrames_eq_nil_of_last hat run]
  refine ⟨fun post hout => ?_, fun f member => (List.not_mem_nil member).elim⟩
  subst hout
  have keep : post.state.getStor P = pre.state.getStor P :=
    Linst.getStor_eq step P (State.Protected.of_image installed.1)
  rw [keep]; exact inv

/-- **Foreign spawn.**  The child enters with the proxy's storage, at the proxy's code if it
targets the proxy (a direct call child at its own code address); the parent resumes with the child's
committed storage or its own. -/
theorem SlotsOk.nextSome {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst}
    {cevm : Evm} {raw out : Execution} (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out) (targetNe : sevm.currentTarget ≠ P)
    (ihChild : SlotsOk P U a₀ cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : SlotsOk P U a₀ (pc + n.size) sevm inter out) :
    SlotsOk P U a₀ pc sevm pre out := by
  cases n with
  | reg r => cases (Step.run_ofExecution.mp step).1
  | push xs length => cases (Step.run_ofExecution.mp step).1
  | dupn imm => cases (Step.run_ofExecution.mp step).1
  | swapn imm => cases (Step.run_ofExecution.mp step).1
  | exchange imm => cases (Step.run_ofExecution.mp step).1
  | exec x =>
  intro run committed fork installed admitted _ avail inv
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
  obtain ⟨frame, resume, spawnX, enter, hres, hroot⟩ := Ninst.StepRun.spawnParts hat step
  have subsets := Exec.rawFrameDescendants_sub_of_stepSome hat step child next run
  have runEq : run = Exec.runOk hroot enter child hres next := Exec.unique _ _
  subst runEq
  have codeP : pre.getCode P = Proxy.code := code_of_at installed.1
  obtain ⟨pcZero, childFork, -, childCode, childStor⟩ := Evm.step_spawn_entry fork hroot enter
  have childCodeP : cevm.dyna.getCode P = Proxy.code := (childCode P).trans codeP
  have childInv : SlotInv U a₀ (cevm.dyna.state.getStor P) := by
    rw [childStor P (proxy_protected codeP)]; exact inv
  have childAdmitted : Exec.FrameAdmitted P (slotEntry U) child := admitted.mono fun root member =>
    List.mem_cons_of_mem _ (subsets.1 root member)
  have nextAdmitted := admitted.of_descendants_of_ne targetNe subsets.2
  have codeNe : pre.getCode P ≠ .empty := fun empty => proxy_nonempty (by
    rw [← codeP, empty]; simp only [ByteArray.toList_empty])
  obtain ⟨-, -, codeSource⟩ := Evm.step_spawn_child hroot enter
  have kind : cevm.sta.currentTarget = P →
      cevm.sta.codeAddress = some P ∧ cevm.sta.code = Proxy.code := by
    intro target
    have innerTarget : frame.inner.currentTarget = P := by
      rw [← Frame.enter_run_currentTarget enter, target]
    refine ⟨?_, ?_⟩
    · rw [Frame.enter_run_codeAddress enter,
        Xinst.step_spawn_codeAddress_eq_currentTarget spawnX (by rw [innerTarget]; exact targetNe)
          (by rw [innerTarget]; exact codeNe) (by rw [innerTarget, codeP]; exact proxy_undelegated),
        innerTarget]
    · rw [codeSource (by rw [target]; exact targetNe) (by rw [target]; exact codeNe)
        (by rw [target, codeP]; exact proxySem.not_delegation rfl), target, codeP]
  have nextAt : proxySem.At P (pc + 1) sevm inter := by
    obtain ⟨-, codeEq⟩ := Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode
      (.step (.runOk hroot enter child hres next) (.refl _))
    exact ⟨by rw [codeEq P (by rw [codeP]; exact proxy_nonempty)]; exact installed.1,
      fun t => (targetNe t).elim⟩
  obtain ⟨seamOk, seamNo⟩ := Exec.spawn_seam fork hroot enter child hres
  by_cases settles : Frame.settlementCommits frame raw = true
  · have hraw := Frame.raw_commits_of_settlementCommits settles
    rw [Exec.descendantFrames_runOk_of_settlementCommits hroot enter child hres next settles]
      at avail ⊢
    have childAvail := avail _ List.mem_cons_self
    obtain ⟨childPost, childQ, childDesc⟩ := child_slots (fun _ => ihChild) child hraw pcZero
      childFork childCodeP kind childAdmitted childAvail
      (fun f hf => avail f (List.mem_cons_of_mem _ (List.mem_append_left _ hf))) childInv
    have interInv : SlotInv U a₀ (inter.state.getStor P) :=
      SlotInv.congr (seamOk hraw settles P) childPost
    obtain ⟨nextPost, nextDesc⟩ := ihNext next committed fork nextAt nextAdmitted
      (fun t => (targetNe t).elim)
      (fun f hf => avail f (List.mem_cons_of_mem _ (List.mem_append_right _ hf))) interInv
    refine ⟨nextPost, fun f hf => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hf
    · exact childQ
    rcases List.mem_append.mp hf with hc | hn
    · exact childDesc f hc
    · exact nextDesc f hn
  · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hroot enter child hres next settles]
      at avail ⊢
    exact ihNext next committed fork nextAt nextAdmitted (fun t => (targetNe t).elim) avail
      (SlotInv.congr (seamNo settles P) inv)

end Foreign

end Blanc.Lift.Usdc
