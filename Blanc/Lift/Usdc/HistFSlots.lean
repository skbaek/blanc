import Blanc.Lift.Usdc.HistFCore
import Blanc.Lift.Usdc.HistorySlotsFrames
import Blanc.Lift.Usdc.HistorySlotsRescue
import Blanc.Lift.Usdc.RefineSignedPermit
import Blanc.ExecutionSettledCodeImage
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionTraceCalldata

/-!
# The proxy's support-free slot invariant along one message run (twin of U6b2)

The support-free twin of the slot induction (`HistorySlotsCore.lean`,
`HistorySlotsFrames.lean`, `HistorySlots.lean`).  `SlotInvF U a₀ s` is `SlotInv` without its
4th conjunct (`Support`); every step law's support clause is an implication
`Support pre → Support post` (`RefineShape.lean:47-56`, `HistorySlotsFrames.lean:86-121`),
so the twin re-threads the same induction projecting that conjunct away.  `Avail`, `Here`,
`Codes`, `OwnerKind` and `slotEntry` are support-free already and reused directly.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.Token
  Blanc.ExecutionAccountingReplay

/-! ## The carrier and the frame facts -/

/-- The proxy's support-free slot invariant: the implementation slot names the
implementation, the admin slot holds `a₀`, and the footprint ledger over `U` is good. -/
def SlotInvF (U : Key → Prop) (a₀ : Adr) (s : Stor) : Prop :=
  s.get implSlot = usdcImpl.toB256 ∧ (s.get adminSlot).toAdr = a₀ ∧ (ledger U s).Good

theorem SlotInvF.congr {U : Key → Prop} {a₀ : Adr} {s s' : Stor} (h : ∀ k, s'.get k = s.get k)
    (inv : SlotInvF U a₀ s) : SlotInvF U a₀ s' := by
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

/-- What the support-free induction delivers at a committed frame: the invariant at its entry
and its end, and its code kind if it runs at the proxy. -/
def FrameQF (P : Adr) (U : Key → Prop) (a₀ : Adr) (f : Exec.Frame) : Prop :=
  SlotInvF U a₀ (f.pre.state.getStor P) ∧ SlotInvF U a₀ (f.post.state.getStor P) ∧
    (f.sevm.currentTarget = P → OwnerKind P f.sevm)

/-- **The support-free induction motive.** -/
def SlotsOkF (P : Adr) (U : Key → Prop) (a₀ : Adr) (pc : Nat) (sevm : Sevm) (pre : Devm)
    (out : Execution) : Prop :=
  ∀ run : Exec pc sevm pre out, out.commits = true → CoveredFork sevm.benvStat.fork →
    proxySem.At P pc sevm pre → Exec.FrameAdmitted P (slotEntry U) run → Here P a₀ sevm pre →
    (∀ f ∈ Exec.descendantFrames run, Avail P a₀ f) → SlotInvF U a₀ (pre.state.getStor P) →
    (∀ post, out = .ok post → SlotInvF U a₀ (post.state.getStor P)) ∧
      ∀ f ∈ Exec.descendantFrames run, FrameQF P U a₀ f

/-- The deeper-frame hypothesis of the support-free induction. -/
abbrev DeeperF (P : Adr) (U : Key → Prop) (a₀ : Adr) (k : Nat) : Prop :=
  ForallDeeperAtSem k P proxySem (fun pc s d e _ => SlotsOkF P U a₀ pc s d e)

/-- **A child located by the proxy's code.**  The support-free twin of `child_slots`. -/
theorem child_slotsF {P : Adr} {U : Key → Prop} {a₀ : Adr} {cevm : Evm} {raw : Execution}
    (ih : proxySem.At P cevm.pc cevm.sta cevm.dyna → SlotsOkF P U a₀ cevm.pc cevm.sta cevm.dyna raw)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (committed : raw.commits = true) (pcZero : cevm.pc = 0)
    (fork : CoveredFork cevm.sta.benvStat.fork) (codeP : cevm.dyna.getCode P = Proxy.code)
    (kind : cevm.sta.currentTarget = P → cevm.sta.codeAddress = some P ∧ cevm.sta.code = Proxy.code)
    (admitted : Exec.FrameAdmitted P (slotEntry U) child)
    (avail : Avail P a₀ (Exec.Frame.ofRun child committed))
    (below : ∀ f ∈ Exec.descendantFrames child, Avail P a₀ f)
    (inv : SlotInvF U a₀ (cevm.dyna.state.getStor P)) :
    SlotInvF U a₀ ((Execution.committedPost raw committed).state.getStor P) ∧
      FrameQF P U a₀ (Exec.Frame.ofRun child committed) ∧
      ∀ f ∈ Exec.descendantFrames child, FrameQF P U a₀ f := by
  have at_ : proxySem.At P cevm.pc cevm.sta cevm.dyna :=
    ⟨proxy_at_image codeP, fun t => ⟨by rw [(kind t).2]; rfl, pcZero⟩⟩
  have here : Here P a₀ cevm.sta cevm.dyna := fun t =>
    ⟨(kind t).1, avail.1, avail.2 ⟨t, (kind t).1⟩⟩
  obtain ⟨post, desc⟩ := ih at_ child committed fork at_ admitted here below inv
  have hpost := post_of_commits committed post
  exact ⟨hpost, ⟨inv, hpost, fun t => .inl (kind t)⟩, desc⟩

/-! ## Foreign nodes -/

section ForeignF

variable {P : Adr} {U : Key → Prop} {a₀ : Adr}

theorem SlotsOkF.error {pc : Nat} {sevm : Sevm} {pre : Devm} {e : EvmError × Devm} :
    SlotsOkF P U a₀ pc sevm pre (.error e) := by
  intro _ committed
  simp only [Execution.commits, Bool.false_eq_true] at committed

theorem SlotsOkF.nextNone {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst}
    {out : Execution} (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out) (targetNe : sevm.currentTarget ≠ P)
    (ih : SlotsOkF P U a₀ (pc + n.size) sevm inter out) :
    SlotsOkF P U a₀ pc sevm pre out := by
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

theorem SlotsOkF.jump {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {j : Jinst}
    {out : Execution} (hat : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out) (targetNe : sevm.currentTarget ≠ P)
    (ih : SlotsOkF P U a₀ pc' sevm inter out) :
    SlotsOkF P U a₀ pc sevm pre out := by
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

theorem SlotsOkF.last {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst} {out : Execution}
    (hat : Linst.At sevm.code pc l) (step : Linst.Run sevm pre l out) :
    SlotsOkF P U a₀ pc sevm pre out := by
  intro run _ _ installed _ _ _ inv
  rw [Exec.descendantFrames_eq_nil_of_last hat run]
  refine ⟨fun post hout => ?_, fun f member => (List.not_mem_nil member).elim⟩
  subst hout
  have keep : post.state.getStor P = pre.state.getStor P :=
    Linst.getStor_eq step P (State.Protected.of_image installed.1)
  rw [keep]; exact inv

/-- **Foreign spawn.**  The support-free twin of `SlotsOk.nextSome`. -/
theorem SlotsOkF.nextSome {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst}
    {cevm : Evm} {raw out : Execution} (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out) (targetNe : sevm.currentTarget ≠ P)
    (ihChild : SlotsOkF P U a₀ cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : SlotsOkF P U a₀ (pc + n.size) sevm inter out) :
    SlotsOkF P U a₀ pc sevm pre out := by
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
  have childInv : SlotInvF U a₀ (cevm.dyna.state.getStor P) := by
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
    obtain ⟨childPost, childQ, childDesc⟩ := child_slotsF (fun _ => ihChild) child hraw pcZero
      childFork childCodeP kind childAdmitted childAvail
      (fun f hf => avail f (List.mem_cons_of_mem _ (List.mem_append_left _ hf))) childInv
    have interInv : SlotInvF U a₀ (inter.state.getStor P) :=
      SlotInvF.congr (seamOk hraw settles P) childPost
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
      (SlotInvF.congr (seamNo settles P) inv)

end ForeignF

/-! ## The frame handlers -/

section FramesF

variable {P : Adr} {U : Key → Prop} {a₀ : Adr}

/-- The whole-frame keeping of a successful implementation frame, support-free: the ledger
good and the proxy's slots kept, at its end and at every external node. -/
def ImplKeepsF (P : Adr) (U : Key → Prop) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) : Prop :=
  ((ledger U (post.state.getStor P)).Good ∧
      (post.state.getStor P).get implSlot = (pre.state.getStor P).get implSlot ∧
      (post.state.getStor P).get adminSlot = (pre.state.getStor P).get adminSlot) ∧
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        (ledger U (N.devm.state.getStor P)).Good ∧
        (N.devm.state.getStor P).get implSlot = (pre.state.getStor P).get implSlot ∧
        (N.devm.state.getStor P).get adminSlot = (pre.state.getStor P).get adminSlot

/-- **The family laws at a good ledger, support-free.**  The support-free twin of `impl_laws`:
the step laws' support clauses (`Support pre → Support post`) are simply not applied. -/
theorem impl_lawsF {P : Adr} {U : Key → Prop} (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) (signed : ImplStepLaw famSigned)
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Impl.code) (target : sevm.currentTarget = P)
    (codeAddr : sevm.codeAddress = some usdcImpl) (fork : CoveredFork sevm.benvStat.fork)
    (nonstatic : sevm.isStatic = false) (keys : ∀ k ∈ frameKeys sevm, U k)
    (lib : some (pre.state.getCode usdcLib).toList = libSem.image)
    (notAdmin : sevm.caller ≠ adminOf pre.state P) (good : (ledger U (pre.state.getStor P)).Good) :
    ImplKeepsF P U run ∨ Blanc.Sevm.selector sevm = rescueSelector := by
  obtain ⟨c, dec⟩ := impl_decodes run codeEq fork
  have whole : ∀ fam, ImplStepLaw fam → fam c →
      ImplKeepsF P U run ∨ Blanc.Sevm.selector sevm = rescueSelector := fun fam law hc => by
    obtain ⟨step, hi, ha, -, nodes⟩ :=
      law run codeEq target codeAddr fork nonstatic inj apart keys lib notAdmin c dec hc
    exact Or.inl ⟨⟨book_good step good, hi, ha⟩, fun N chain x hat =>
      let ⟨_, g, i, a, _⟩ := nodes N chain x hat
      ⟨g good, i, a⟩⟩
  rcases call_family_cases c with h | h | h | h | h | h | ⟨t, d, v, rfl⟩
  · exact whole _ implStepLaw_famTransfer h
  · exact whole _ signed h
  · exact whole _ implStepLaw_famAdmin h
  · exact whole _ impl_view_law (by cases c <;> first | rfl | exact h.elim)
  · exact (impl_initRevert run codeEq target codeAddr fork nonstatic inj apart keys lib notAdmin
      good c dec h).elim
  · exact (impl_initV2Revert run codeEq target codeAddr fork nonstatic inj apart keys lib notAdmin
      good c dec (by cases c <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩ | exact h.elim)).elim
  · exact .inr (decodeCall_rescue dec)

/-- A child at a node of a frame at the proxy that a `CALL`/`STATICCALL` spawned, support-free:
the twin of `entry_slots`. -/
theorem entry_slotsF {k : Nat} (deeper : DeeperF P U a₀ k) {root N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix root N) (fork : CoveredFork root.sevm.benvStat.fork)
    (codes : Codes P root.devm) (target : root.sevm.currentTarget = P)
    (depth : root.sevm.depth ≤ k) {x : Xinst} (kind : x = .call ∨ x = .staticcall) {f : Frame}
    {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
    (step : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc')
    (spawn : Xinst.step N.sevm N.devm x = .spawn f rsm) (enter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw) (h : raw.commits = true)
    (admitted : Exec.FrameAdmitted P (slotEntry U) root.exc)
    (desc : ∀ g ∈ Exec.Frame.ofRun child h :: Exec.descendantFrames child,
      g ∈ Exec.descendantFrames root.exc)
    (avail : ∀ g ∈ Exec.descendantFrames root.exc, Avail P a₀ g)
    (nodeInv : SlotInvF U a₀ (N.devm.state.getStor P)) :
    FrameQF P U a₀ (Exec.Frame.ofRun child h) ∧
      ∀ g ∈ Exec.descendantFrames child, FrameQF P U a₀ g := by
  obtain ⟨sevmEq, -, pcZero, cfork, cdepth, ncodes, ccodes, cstor⟩ :=
    node_child chain fork codes step enter
  have mem := desc _ List.mem_cons_self
  have kindAt : cevm.sta.currentTarget = P →
      cevm.sta.codeAddress = some P ∧ cevm.sta.code = Proxy.code := fun t =>
    let ⟨ca, cd⟩ := entry_child kind spawn enter ncodes.1 t
    ⟨ca, cd (by rw [sevmEq]; exact target)⟩
  obtain ⟨-, q, d⟩ := child_slotsF (fun at_ => deeper _ _ _ _ child (Nat.lt_of_lt_of_le cdepth depth) at_)
    child h pcZero cfork ccodes.1 kindAt (Exec.FrameAdmitted.of_mem_descendantFrames admitted mem)
    (avail _ mem) (fun g hg => avail g (desc g (List.mem_cons_of_mem _ hg)))
    (by rw [cstor]; exact nodeInv)
  exact ⟨q, d⟩

/-- **A library frame at the proxy, support-free.**  The twin of `libFrame`. -/
theorem libFrameF {k : Nat} (deeper : DeeperF P U a₀ k) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (depth : sevm.depth ≤ k) (codeEq : sevm.code = Lib.code)
    (target : sevm.currentTarget = P) (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted P (slotEntry U) run) (codes : Codes P pre)
    (avail : ∀ f ∈ Exec.descendantFrames run, Avail P a₀ f)
    (inv : SlotInvF U a₀ (pre.state.getStor P)) :
    SlotInvF U a₀ (post.state.getStor P) ∧ ∀ f ∈ Exec.descendantFrames run, FrameQF P U a₀ f := by
  let root : Exec.Deriv := ⟨0, sevm, pre, .ok post, run⟩
  have onlyStatic : ∀ {node : Exec.Deriv} {x : Xinst}, Exec.Deriv.ParentPrefix root node →
      Ninst.At node.sevm.code node.pc (.exec x) → x = .staticcall := fun chain hat =>
    parentPrefix_exec_staticcall_of_cert Lib.cert_check lib_staticOnly (root := root) rfl codeEq
      fork chain hat
  refine ⟨?_, Exec.descendantFrames_of_spawns (root := root) ?_ run (.refl _) (fun _ h => h)
    (fun _ h => h)⟩
  · have keep := (lib_children run codeEq fork).2 post rfl
    rw [target] at keep
    rw [keep]; exact inv
  · intro N f rsm pc' cevm raw child h chain step enter _ desc
    obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
    have hx : x = .staticcall := onlyStatic chain hat
    have keep := Exec.Deriv.ParentPrefix.getStor_of_quiet chain fork
      (fun _ hat' => lib_stor_free (by rw [← codeEq]; exact hat')) onlyStatic
    have nodeInv : SlotInvF U a₀ (N.devm.state.getStor P) := by
      rw [show N.devm.state.getStor P = pre.state.getStor P from congrFun keep P]; exact inv
    exact entry_slotsF deeper chain fork codes target depth (.inr hx) step (hx ▸ spawn) enter child
      h admitted desc avail nodeInv

/-- **An implementation frame's children, support-free.**  The twin of `impl_children_slots`. -/
theorem impl_children_slotsF {k : Nat} (deeper : DeeperF P U a₀ k) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (depth : sevm.depth ≤ k) (codeEq : sevm.code = Impl.code)
    (target : sevm.currentTarget = P) (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted P (slotEntry U) run) (codes : Codes P pre)
    (avail : ∀ f ∈ Exec.descendantFrames run, Avail P a₀ f)
    (entryInv : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
        (child : Exec cevm.pc cevm.sta cevm.dyna raw) (h : raw.commits = true),
        Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc' → f.enter = .run cevm →
        Exec.Frame.ofRun child h ∈ Exec.childFrames run →
        SlotInvF U a₀ (cevm.dyna.state.getStor P) ∧ SlotInvF U a₀ (N.devm.state.getStor P)) :
    ∀ f ∈ Exec.descendantFrames run, FrameQF P U a₀ f := by
  refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, .ok post, run⟩) ?_ run (.refl _)
    (fun _ h => h) (fun _ h => h)
  intro N f rsm pc' cevm raw child h chain step enter member desc
  obtain ⟨cinv, ninv⟩ := entryInv N chain child h step enter member
  obtain ⟨sevmEq, nfork, pcZero, cfork, cdepth, ncodes, ccodes, -⟩ :=
    node_child chain fork codes step enter
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  rcases impl_node run codeEq fork chain hat spawn with rfl | ⟨rfl, g, rest, stack⟩
  · exact entry_slotsF deeper chain fork codes target depth (.inl rfl) step spawn enter child h
      admitted desc avail ninv
  · have adr : usdcLib.toB256.toAdr = usdcLib := toAdr_toB256 _
    obtain ⟨hT, hA, -, -, -, hK, -⟩ := Xinst.step_delegatecall_spawn_exact nfork spawn stack
      (by rw [adr, ncodes.2.2]; exact lib_undelegated)
    rw [adr] at hA hK
    have ctarget : cevm.sta.currentTarget = P := by
      rw [Frame.enter_run_currentTarget enter, hT, sevmEq]; exact target
    have ccode : cevm.sta.code = Lib.code := by
      rw [Frame.enter_run_code enter, hK]; exact ncodes.2.2
    have cca : cevm.sta.codeAddress = some usdcLib := by
      rw [Frame.enter_run_codeAddress enter]; exact hA
    have mem := desc _ List.mem_cons_self
    have cadmitted := Exec.FrameAdmitted.of_mem_descendantFrames admitted mem
    cases raw with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at h
    | ok cpost =>
      obtain ⟨cevmPc, csevm, cdyna⟩ := cevm
      dsimp only at pcZero
      subst pcZero
      obtain ⟨lpost, ldesc⟩ := libFrameF deeper child (Nat.le_of_lt (Nat.lt_of_lt_of_le cdepth depth))
        ccode ctarget cfork cadmitted ccodes
        (fun g hg => avail g (desc g (List.mem_cons_of_mem _ hg))) cinv
      exact ⟨⟨cinv, lpost, fun _ => .inr (.inr ⟨cca, ccode⟩)⟩, ldesc⟩

/-- **An implementation frame at the proxy, support-free.**  The twin of `implFrame`. -/
theorem implFrameF (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) (signed : ImplStepLaw famSigned)
    (rescueEnd : RescueQuietEnd) {k : Nat} (deeper : DeeperF P U a₀ k) {sevm : Sevm}
    {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) (depth : sevm.depth ≤ k)
    (codeEq : sevm.code = Impl.code) (target : sevm.currentTarget = P)
    (codeAddr : sevm.codeAddress = some usdcImpl) (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted P (slotEntry U) run) (codes : Codes P pre)
    (notAdmin : sevm.caller ≠ adminOf pre.state P)
    (avail : ∀ f ∈ Exec.descendantFrames run, Avail P a₀ f)
    (inv : SlotInvF U a₀ (pre.state.getStor P)) :
    SlotInvF U a₀ (post.state.getStor P) ∧ ∀ f ∈ Exec.descendantFrames run, FrameQF P U a₀ f := by
  have keys : ∀ k ∈ frameKeys sevm, U k := (admitted.root target).1
  have lib : some (pre.state.getCode usdcLib).toList = libSem.image := by
    rw [show pre.state.getCode usdcLib = Lib.code from codes.2.2]; rfl
  have codeNe : (pre.getCode P).toList ≠ [] := by rw [codes.1]; exact proxy_nonempty
  have entryOfNode : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm},
        Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc' → f.enter = .run cevm →
        cevm.dyna.state.getStor P = N.devm.state.getStor P := by
    intro N chain f rsm pc' cevm step enter
    exact (node_child chain fork codes step enter).2.2.2.2.2.2.2
  cases hs : sevm.isStatic
  · rcases impl_lawsF inj apart signed run codeEq target codeAddr fork hs keys lib notAdmin
      inv.2.2 with ⟨⟨pg, pi, pa⟩, nodes⟩ | hsel
    · have nodeInv : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
          ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → SlotInvF U a₀ (N.devm.state.getStor P) :=
        fun N chain x hat =>
          let ⟨g, i, a⟩ := nodes N chain x hat
          ⟨i.trans inv.1, by rw [a]; exact inv.2.1, g⟩
      refine ⟨⟨pi.trans inv.1, by rw [pa]; exact inv.2.1, pg⟩, ?_⟩
      refine impl_children_slotsF deeper run depth codeEq target fork admitted codes avail ?_
      intro N chain f rsm pc' cevm raw child h step enter _
      obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
      have ni := nodeInv N chain x hat
      exact ⟨by rw [entryOfNode N chain step enter]; exact ni, ni⟩
    · obtain ⟨-, nodes⟩ := rescueLaw run codeEq target codeAddr fork hs keys hsel
      have desc : ∀ f ∈ Exec.descendantFrames run, FrameQF P U a₀ f := by
        refine impl_children_slotsF deeper run depth codeEq target fork admitted codes avail ?_
        intro N chain f rsm pc' cevm raw child h step enter _
        obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
        have nstor := (nodes N chain x hat).2.1
        exact ⟨by rw [entryOfNode N chain step enter, nstor]; exact inv, by rw [nstor]; exact inv⟩
      refine ⟨?_, desc⟩
      rcases Exec.Deriv.exists_firstExec_or_none run with none | ⟨Vn, hV⟩
      · rw [rescueEnd run codeEq target fork hs hsel (proxy_protected codes.1) none]; exact inv
      have hpV := hV.parentPrefix
      have dEq := hV.descendantFrames_eq
      obtain ⟨x, hx⟩ := hV.exec_at
      have hexn := Exec.Deriv.ParentPrefix.exn_eq hpV
      obtain ⟨-, nstor, after⟩ := nodes _ hpV x hx
      obtain ⟨vpc, vsevm, vd, vout, vrun⟩ := Vn
      dsimp only at hexn hx dEq nstor after hpV
      subst hexn
      have vfork : CoveredFork vsevm.benvStat.fork := by
        have e := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hpV
        dsimp only at e
        rw [e]; exact fork
      have vprot : State.Protected vd.state P :=
        proxy_protected (codes_keep (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode hpV).2 codes).1
      cases vrun with
      | halt step =>
          rw [Evm.step_next hx] at step
          exact (Ninst.step_ne_halt_ok step).elim
      | cont step next =>
          rename_i pc' post'
          have nstep : Ninst.step ⟨vpc, vsevm, vd⟩ (.exec x) = .cont pc' post' := by
            rw [← Evm.step_next hx]; exact step
          have nrun : Ninst.StepRun vpc vsevm vd (.exec x) .none (.ok post') := by
            unfold Ninst.StepRun; rw [nstep]; exact ⟨rfl, rfl⟩
          have hstor : post'.state.getStor P = vd.state.getStor P :=
            Ninst.none_getStor_eq_of_ne_sstore nrun (by intro h; cases h) P vprot
          rw [(after _ (.cont step next)).1]
          change SlotInvF U a₀ (post'.state.getStor P)
          rw [hstor, nstor]; exact inv
      | doneOk step enter resume next =>
          rename_i settled pc' post'
          have hstor : post'.state.getStor P = vd.state.getStor P :=
            Evm.step_doneOk_getStor_eq step enter resume P vprot
          rw [(after _ (.doneOk step enter resume next)).1]
          change SlotInvF U a₀ (post'.state.getStor P)
          rw [hstor, nstor]; exact inv
      | runOk step enter child resume next =>
          rename_i frame rsm pc' cevm raw inter
          rw [(after _ (.runOk step enter child resume next)).1]
          change SlotInvF U a₀ (inter.state.getStor P)
          obtain ⟨seamA, seamB⟩ := Exec.spawn_seam vfork step enter child resume
          by_cases settles : Frame.settlementCommits frame raw = true
          · have hcommit := Frame.raw_commits_of_settlementCommits settles
            have mem : Exec.Frame.ofRun child hcommit ∈ Exec.descendantFrames run := by
              rw [dEq, Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next
                settles]
              exact List.mem_cons_self
            exact SlotInvF.congr (seamA hcommit settles P) (desc _ mem).2.1
          · refine SlotInvF.congr (seamB settles P) ?_
            change SlotInvF U a₀ (vd.state.getStor P)
            rw [nstor]; exact inv
  · have keep := Exec.getStor_committedPost_eq_of_static run hs committed fork
      (Or.inl (by rw [target]; exact proxy_protected codes.1))
    refine ⟨?_, ?_⟩
    · rw [show post.state.getStor P = pre.state.getStor P from congrFun keep P]; exact inv
    refine impl_children_slotsF deeper run depth codeEq target fork admitted codes avail ?_
    intro N chain f rsm pc' cevm raw child h step enter member
    have mem := Exec.mem_descendantFrames_of_mem_childFrames run _ member
    have e : cevm.dyna.state.getStor P = pre.state.getStor P :=
      Blanc.Exec.descendantFrames_getStor_of_static run hs committed fork codeNe _ mem
    exact ⟨by rw [e]; exact inv, by rw [← entryOfNode N chain step enter, e]; exact inv⟩

/-- **A proxy frame, support-free** (the target handler).  The twin of `proxyFrame`. -/
theorem proxyFrameF (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) (signed : ImplStepLaw famSigned)
    (rescueEnd : RescueQuietEnd) {sevm : Sevm} {pre post : Devm}
    (codeEq : sevm.code = Proxy.code) (target : sevm.currentTarget = P)
    (deeper : DeeperF P U a₀ sevm.depth) : SlotsOkF P U a₀ 0 sevm pre (.ok post) := by
  intro run _ fork _ admitted here avail inv
  obtain ⟨-, codes, gov⟩ := here target
  by_cases admin : sevm.caller = adminOf pre.state P
  · have admin' : sevm.caller = adminOf pre.state sevm.currentTarget := by rw [target]; exact admin
    have hsel := gov (admin.trans inv.2.1)
    have noExec : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := fun N chain x hat =>
      hsel (by rw [(proxy_admin_exec run codeEq fork admin' N chain x hat).2.1]; decide)
    rw [Exec.descendantFrames_eq_nil_of_noExec run noExec]
    refine ⟨fun p hp => ?_, fun f hf => (List.not_mem_nil hf).elim⟩
    cases hp
    have keep := ((proxy_admin_rule run codeEq fork admin').2.2 hsel).2 post rfl
    rw [target] at keep
    rw [keep]; exact inv
  · have notAdmin' : sevm.caller ≠ adminOf pre.state sevm.currentTarget := by
      rw [target]; exact admin
    have slot : (pre.state.getStor sevm.currentTarget).get implSlot = usdcImpl.toB256 := by
      rw [target]; exact inv.1
    obtain ⟨-, kids, fin⟩ := proxy_forwards run codeEq fork slot notAdmin'
      (by rw [show pre.state.getCode usdcImpl = Impl.code from codes.2.1]; exact impl_undelegated)
      (impl_not_precompile fork) (admitted.root target).2
    have nodeState : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → N.devm.state = pre.state := by
      intro N chain x hat
      obtain ⟨g, K, ⟨-, hd⟩ | ⟨-, hs, -⟩⟩ := proxy_node run codeEq fork chain hat
      · obtain ⟨-, b', w, S, M, G, rest, hstate, -, hdev⟩ := hd
        change N.devm = _ at hdev
        rw [hdev]; exact hstate
      · exact (notAdmin' (by rw [adminOf_eq]; exact hs.1)).elim
    have desc : ∀ f ∈ Exec.descendantFrames run, FrameQF P U a₀ f := by
      refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, .ok post, run⟩) ?_ run
        (.refl _) (fun _ h => h) (fun _ h => h)
      intro N f rsm pc' cevm raw child h chain step enter member descm
      obtain ⟨hT, hA, hC, -, -, -, hK⟩ := kids _ member
      obtain ⟨-, -, pcZero, cfork, cdepth, -, ccodes, cstor⟩ :=
        node_child chain fork codes step enter
      obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
      have nstate := nodeState N chain x hat
      have cstor' : cevm.dyna.state.getStor P = pre.state.getStor P := by rw [cstor, nstate]
      have cinv : SlotInvF U a₀ (cevm.dyna.state.getStor P) := by rw [cstor']; exact inv
      have mem := descm _ List.mem_cons_self
      have ccode : cevm.sta.code = Impl.code := hK.trans codes.2.1
      cases raw with
      | error e => simp only [Execution.commits, Bool.false_eq_true] at h
      | ok cpost =>
        obtain ⟨cevmPc, csevm, cdyna⟩ := cevm
        dsimp only at pcZero
        subst pcZero
        have cnot : csevm.caller ≠ adminOf cdyna.state P := by
          change csevm.caller = sevm.caller at hC
          unfold adminOf
          rw [cstor', hC]; exact admin
        obtain ⟨ipost, idesc⟩ := implFrameF inj apart signed rescueEnd deeper child h
          (Nat.le_of_lt cdepth) ccode (hT.trans target) hA cfork
          (Exec.FrameAdmitted.of_mem_descendantFrames admitted mem) ccodes cnot
          (fun g hg => avail g (descm g (List.mem_cons_of_mem _ hg))) cinv
        exact ⟨⟨cinv, ipost, fun _ => .inr (.inl ⟨hA, ccode⟩)⟩, idesc⟩
    refine ⟨fun p hp => ?_, desc⟩
    cases hp
    obtain ⟨c, mem, -, hstate⟩ := fin post rfl
    rw [hstate]
    exact (desc c (Exec.mem_descendantFrames_of_mem_childFrames run c mem)).2.1

/-- **The support-free slot induction**, at every derivation located by the proxy's code. -/
theorem usdc_slotsOkF (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) (signed : ImplStepLaw famSigned)
    (rescueEnd : RescueQuietEnd) :
    Exec.Fa (Exec.WknSem P proxySem (fun pc s d e _ => SlotsOkF P U a₀ pc s d e)) :=
  lift_core_sem (fun pc s d e => SlotsOkF P U a₀ pc s d e)
    (fun s d p => SlotsOkF P U a₀ 0 s d (.ok p)) (fun h => h) P proxySem
    (fun hrun target deeper => proxyFrameF inj apart signed rescueEnd hrun target deeper)
    (fun _ => SlotsOkF.error) (fun _ _ => SlotsOkF.error) (fun _ _ _ => SlotsOkF.error)
    (fun _ _ _ _ _ => SlotsOkF.error)
    (fun hat step next targetNe ih => SlotsOkF.nextNone hat step next targetNe ih)
    (fun hat step child next targetNe ihChild ihNext =>
      SlotsOkF.nextSome hat step child next targetNe ihChild ihNext)
    (fun _ _ _ => SlotsOkF.error)
    (fun hat step next targetNe ih => SlotsOkF.jump hat step next targetNe ih)
    (fun hat step _ => SlotsOkF.last hat step)

end FramesF

/-! ## The history-level ladder -/

/-- The support-free slot carrier: the proxy's storage; a replay of frames, from a boundary in
the support-free invariant and with the history's facts at each frame, ends in the invariant
and delivers `FrameQF` at each frame. -/
def slotCarrierF (P : Adr) (U : Key → Prop) (a₀ : Adr) : ReplayCarrier P where
  Snap := Stor
  Step := Exec.Frame
  Tag := Unit
  Replay s fs s' := (∀ f ∈ fs, Avail P a₀ f) → SlotInvF U a₀ s →
    SlotInvF U a₀ s' ∧ ∀ f ∈ fs, FrameQF P U a₀ f
  ofState w := w.getStor P
  frameEntry _ w := w.getStor P
  nil _ := fun _ inv => ⟨inv, fun _ h => (List.not_mem_nil h).elim⟩
  readsStorage := true
  silent := fun storage _ => storage rfl
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], fun _ inv => ⟨?_, fun _ h => (List.not_mem_nil h).elim⟩⟩
    rw [storage]; exact inv
  entry_eq_ofState := by
    intro _ _ caller_ne _ transfer sum_nof
    exact benvAfterTransfer_getStor_eq_of_safe transfer sum_nof
      (fun transfers _ => Or.inl (caller_ne transfers))

/-- Every settled frame is observed, as itself (support-free carrier). -/
def slotObservationF (P : Adr) (U : Key → Prop) (a₀ : Adr) :
    ReplayObservation (slotCarrierF P U a₀) where
  O := Exec.Frame
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs f := [f]
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], fun _ inv => ⟨?_, fun _ h => (List.not_mem_nil h).elim⟩, rfl⟩
    change SlotInvF U a₀ (post.getStor P)
    rw [storage]; exact inv

/-- **The support-free slot ladder**: its root law is the support-free slot induction below a
message root. -/
noncomputable def slotLadderF (P : Adr) {U : Key → Prop} (a₀ : Adr)
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    (signed : ImplStepLaw famSigned) (rescueEnd : RescueQuietEnd) :
    AccountingLadderAdmitted (ContractSpecSem.ofStorageOnly proxySem (fun _ => True)) P
      (slotEntry U) where
  carrier := slotCarrierF P U a₀
  append := fun left right avail inv =>
    let ⟨mid, q₁⟩ := left (fun f hf => avail f (List.mem_append_left _ hf)) inv
    let ⟨fin, q₂⟩ := right (fun f hf => avail f (List.mem_append_right _ hf)) mid
    ⟨fin, fun f hf => (List.mem_append.mp hf).elim (q₁ f) (q₂ f)⟩
  tag _ _ := ()
  preserves := by
    intro sevm pre post fork run admitted image wf inv
    exact ⟨trivial, trivial⟩
  view := slotObservationF P U a₀
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork bound
    obtain ⟨installed, -⟩ := Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have pcEq := congrArg Evm.pc evmEq
    have sevmEq := congrArg Evm.sta evmEq
    dsimp only [initEvm] at pcEq sevmEq
    have rootCA : sevm.currentTarget = P → sevm.codeAddress = some P := by
      intro target
      rw [sevmEq] at target ⊢
      rcases ready.codeOrForeign with call | foreign
      · exact ready.ready.codeAddress call target
      · exact (foreign target).elim
    refine ⟨Exec.committedFrames run, fun avail inv => ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    have frames : Exec.committedFrames run = Exec.Frame.ofRun run committed ::
        Exec.descendantFrames run := by
      rw [Exec.committedFrames, dite_eq_left committed]
    rw [frames] at avail ⊢
    obtain ⟨codes, gov⟩ := avail _ List.mem_cons_self
    have here : Here P a₀ sevm pre := fun target =>
      ⟨rootCA target, codes, gov ⟨target, rootCA target⟩⟩
    obtain ⟨post, desc⟩ := usdc_slotsOkF inj apart signed rescueEnd _ _ _ _ run installed run
      committed fork installed admitted here (fun f hf => avail f (List.mem_cons_of_mem _ hf)) inv
    have hpost := post_of_commits committed post
    refine ⟨hpost, fun f hf => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hf
    · refine ⟨inv, hpost, fun target => .inl ⟨rootCA target, ?_⟩⟩
      exact bytes_eq_of_image (installed.2 target).1
    · exact desc f hf

/-- **The support-free slot facts at every settled frame and at the end** of a configured
history from a `UsdcHistF` checkpoint, over the history's key universe, given the signed
family's law.  The twin of `usdc_history_frames_of`: `FootCoreL.extend` replaces
`FootInv.extend`, and the replay starts from the support-free boundary. -/
theorem usdc_history_frames_ofF (signed : ImplStepLaw famSigned)
    {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) (hist : UsdcHistF P K₀ tr) :
    (∀ G ∈ tr.settledFrames,
      FrameQF P (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P) G) ∧
      SlotInvF (historyKeyUniverse P tr K₀) (adminOf checkpoint.state P)
        (future.state.getStor P) := by
  obtain ⟨installed, gov, foot, fresh⟩ := hist
  have ext := foot.extend fresh
  have admitted : tr.FrameAdmitted P (slotEntry (historyKeyUniverse P tr K₀)) := by
    apply (tr.frameAdmitted_iff_rawFrames P _).2
    intro root member target
    refine ⟨fun k hk => Or.inr (List.mem_flatMap.mpr ⟨root, member, ?_⟩),
      tr.calldata_bound root member⟩
    simpa only [target, ite_true] using hk
  obtain ⟨steps, replay, observed⟩ :=
    (slotLadderF P (adminOf checkpoint.state P) ext.inj ext.apart signed rescueQuietEnd).configuredHistory
      tr admitted ⟨installed.proxy, trivial, trivial⟩
  change steps = tr.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  subst observed
  have codeP := tr.settled_codeImage proxySem P installed.proxy
  have codeI := tr.settled_codeImage implSem usdcImpl installed.impl
  have codeL := tr.settled_codeImage libSem usdcLib installed.lib
  have avail : ∀ f ∈ tr.settledFrames, Avail P (adminOf checkpoint.state P) f := fun f hf =>
    ⟨⟨bytes_eq_of_image (codeP f hf), bytes_eq_of_image (codeI f hf),
      bytes_eq_of_image (codeL f hf)⟩, gov f hf⟩
  obtain ⟨fin, frames⟩ := replay avail ⟨installed.slot, rfl, ext.good⟩
  exact ⟨frames, fin⟩

/-- **`usdc_history_slotsF`, given the signed family's law.** -/
theorem usdc_history_slots_ofF (signed : ImplStepLaw famSigned)
    {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    (∀ G ∈ tr.settledFrames, (G.pre.state.getStor P).get implSlot = usdcImpl.toB256 ∧
      adminOf G.pre.state P = adminOf checkpoint.state P) ∧
    (future.state.getStor P).get implSlot = usdcImpl.toB256 ∧
      adminOf future.state P = adminOf checkpoint.state P := by
  obtain ⟨frames, fin⟩ := usdc_history_frames_ofF signed tr hist
  exact ⟨fun G hG => ⟨(frames G hG).1.1, (frames G hG).1.2.1⟩, fin.1, fin.2.1⟩

/-- **`usdc_history_settled_ownerF`, given the signed family's law.** -/
theorem usdc_history_settled_owner_ofF (signed : ImplStepLaw famSigned) {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ G ∈ tr.settledFrames, G.sevm.currentTarget = P →
      (G.sevm.codeAddress = some P ∧ G.sevm.code = Proxy.code) ∨
      (G.sevm.codeAddress = some usdcImpl ∧ G.sevm.code = Impl.code) ∨
      (G.sevm.codeAddress = some usdcLib ∧ G.sevm.code = Lib.code) :=
  fun G hG => ((usdc_history_frames_ofF signed tr hist).1 G hG).2.2

theorem usdc_history_slotsF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    (∀ G ∈ tr.settledFrames, (G.pre.state.getStor P).get implSlot = usdcImpl.toB256 ∧
      adminOf G.pre.state P = adminOf checkpoint.state P) ∧
    (future.state.getStor P).get implSlot = usdcImpl.toB256 ∧
      adminOf future.state P = adminOf checkpoint.state P :=
  usdc_history_slots_ofF impl_signed_law tr hist

theorem usdc_history_settled_ownerF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) :
    ∀ G ∈ tr.settledFrames, G.sevm.currentTarget = P →
      (G.sevm.codeAddress = some P ∧ G.sevm.code = Proxy.code) ∨
      (G.sevm.codeAddress = some usdcImpl ∧ G.sevm.code = Impl.code) ∨
      (G.sevm.codeAddress = some usdcLib ∧ G.sevm.code = Lib.code) :=
  usdc_history_settled_owner_ofF impl_signed_law tr hist

end Blanc.Lift.Usdc
