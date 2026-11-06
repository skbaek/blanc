import Blanc.Lift.Usdc.EntryQuiet
import Blanc.Lift.Usdc.EntryRescue

/-!
# The target handler at the proxy

`entryTarget`: the target handler of `Exec.coreAccountingIn` at the proxy, over the historical forks.

* a static proxy frame observes nothing and keeps the proxy's storage;
* a frame whose caller is the admin word observes only what is below it. It writes only the proxy's two slots, and
  its only external instruction is `upgradeToAndCall`'s `CALL` to the proxy, so the model replay over its child
  carries the view;
* a frame whose caller is not the admin word observes itself. Off `rescueERC20` it is a chain link and, when allowed,
  has nothing observed below it (`entryQuiet`). On `rescueERC20` it is marked out of the chain (`entryKeep`), and when
  allowed the view runs through its re-entrant frames: it delegates to a version, which runs one `CALL` and is silent
  around it (`version_rescue_nodes`, `version_rescue_end`), so two model replays carry the view to the frames below.

An uncertified frame's replay is vacuous, since it is among the steps. No `CoveredFork`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.Proxy Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

theorem proxy_toList_ne_nil : Proxy.code.toList ≠ [] :=
  entrySem.ne_nil (l := Proxy.code.toList) rfl

theorem proxy_not_delegation : ¬ isValidDelegation Proxy.code :=
  entrySem.not_delegation (code := Proxy.code) rfl

variable {T : Adr}

local notation "Ca" => viewCarrier T ledgerView (EntryGood T) (EntryAllowed T) entryKeep
local notation "Ob" => viewObservation T ledgerView (EntryObs T) (EntryGood T) (EntryAllowed T) entryKeep

/-- The accounting of every derivation at the proxy, below a depth. -/
local notation "Deep" D => ForallDeeperAtSem D T entrySem
  (fun pc s d e _ => Exec.CoreAccountingIn HistFork T entrySem (fun _ _ => True) Ca Ob pc s d e)

/-- **A version's frame on `rescueERC20`, at `T`, replays what is below its one `CALL`.** -/
theorem version_rescue_replay {D : Nat} (deeper : Deep D) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (committed : Execution.commits (.ok post) = true)
    (version : CurveCoins.UsdcVersion sevm.code) (fork : HistFork sevm.benvStat.fork)
    (target : sevm.currentTarget = T) (hsel : Blanc.Sevm.selector sevm = rescueSelector)
    (installed : pre.state.getCode T = Proxy.code) (depth : sevm.depth ≤ D)
    (bound : sum pre.state.bal < 2 ^ 256) :
    ∃ steps, (Ca).Replay ((Ca).frameEntry sevm pre.state) steps ((Ca).ofState post.state) ∧
      steps = (Exec.committedFrames run).flatMap (coinObs T (EntryObs T)) := by
  have hsg := fork.stateGas_none
  have rootNonempty : (pre.getCode T).toList ≠ [] := by
    change (pre.state.getCode T).toList ≠ []
    rw [installed]
    exact proxy_toList_ne_nil
  have rootObs : coinObs T (EntryObs T) (Exec.Frame.ofRun run committed) = [] :=
    ite_eq_right fun h => (version_ne_proxy version h.2.2.1).elim
  have frames : Exec.committedFrames run = Exec.Frame.ofRun run committed :: Exec.descendantFrames run := by
    simp only [Exec.committedFrames, dite_eq_left committed]
  have hlist : (Exec.committedFrames run).flatMap (coinObs T (EntryObs T)) =
      (Exec.descendantFrames run).flatMap (coinObs T (EntryObs T)) := by
    rw [frames, List.flatMap_cons, rootObs, List.nil_append]
  have c3 : (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
      (Ca).Replay ((Ca).frameEntry sevm pre.state) [] ((Ca).ofState post.state) := fun none _ =>
    congrArg (fun s => ledgerView (Stor.get s))
      (version_rescue_end run version hsg hsel (State.Protected.of_code_ne_nil rootNonempty) none)
  have c12 : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        (Ca).Replay ((Ca).frameEntry sevm pre.state) [] ((Ca).ofState N.devm.state) ∧
        ∀ N', Exec.Deriv.ParentStep N' N →
          (Ca).Replay ((Ca).ofState N'.devm.state) [] ((Ca).ofState post.state) ∧
          ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) :=
    fun N chain x hat => by
      obtain ⟨-, state, after⟩ := version_rescue_nodes run version hsg hsel chain hat
      refine ⟨fun _ => ?_, fun N' edge => ⟨fun _ => ?_, (after N' edge).2⟩⟩
      · exact congrArg (fun w => ledgerView (wordsAt T w)) state
      · exact congrArg (fun w => ledgerView (wordsAt T w)) (after N' edge).1
  obtain ⟨steps, replay, observed⟩ := Exec.CoreAccounting.modelFrameNoStateGas
    (C := Ca) (V := Ob) (ca := T) (fun _ _ => rfl) entry_ofStateGet viewCarrier_append run hsg rootNonempty bound
    (fun {nodePc nodeSevm nodePre out frame rsm nextPc cevm raw inter} step enter child resume next chain childCommitted childBound => by
      have sevmEq : nodeSevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
      obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
      obtain ⟨isCall, -, -⟩ := version_rescue_nodes run version hsg hsel chain instruction
      subst isCall
      have nodeCode : nodePre.getCode T = pre.getCode T :=
        (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 T rootNonempty
      have nodeImage : some (nodePre.getCode T).toList = entrySem.image := by
        rw [nodeCode]
        change some (pre.state.getCode T).toList = _
        rw [installed]
        rfl
      have childFork : HistFork cevm.sta.benvStat.fork :=
        Blanc.LockExclusion.Evm.step_spawn_child_forkIn step enter (by rw [sevmEq]; exact fork)
      have childDepth : cevm.sta.depth < D := by
        have : cevm.sta.depth < sevm.depth := by
          rw [Frame.enter_run_depth enter, ← sevmEq]
          exact Step.spawn_depth_lt step
        omega
      obtain ⟨pcZero, getCode, -⟩ := Blanc.Evm.step_spawn_child step enter
      have childAt : entrySem.At T cevm.pc cevm.sta cevm.dyna := by
        refine ⟨by rw [getCode T]; exact nodeImage, fun childTarget => ⟨?_, pcZero⟩⟩
        obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
        subst hcevm
        have frameTarget : frame.inner.currentTarget = T := childTarget
        have code := Xinst.step_call_spawn_code spawn (by
          rw [frameTarget]
          exact entrySem.not_delegation nodeImage)
        change some frame.inner.code.toList = _
        rw [code, frameTarget]
        exact nodeImage
      exact (deeper _ _ _ _ child childDepth childAt child childCommitted childFork childAt
        (fun _ _ _ => trivial)).2 childBound)
    [] c3 c12
  refine ⟨steps, replay, ?_⟩
  change steps = (Exec.committedFrames run).flatMap (coinObs T (EntryObs T))
  rw [hlist]
  exact observed

/-- **The target handler at the proxy.** -/
theorem entryTarget {sevm : Sevm} {pre post : Devm}
    (hrun : entrySem.Run sevm pre post) (target : sevm.currentTarget = T) (deeper : Deep sevm.depth) :
    Exec.CoreAccountingIn HistFork T entrySem (fun _ _ => True) Ca Ob 0 sevm pre (.ok post) := by
  intro run committed fork installed _
  have codeEq : sevm.code = Proxy.code := hrun
  have hsg : sevm.benvStat.rules.stateGas = none := fork.stateGas_none
  have bal : sevm.benvStat.rules.bal = none := fork.bal_none
  have rootNonempty : (pre.getCode T).toList ≠ [] := fun empty =>
    entrySem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  have frames : Exec.committedFrames run = Exec.Frame.ofRun run committed ::
      Exec.descendantFrames run := by
    simp only [Exec.committedFrames, dite_eq_left committed]
  by_cases hs : sevm.isStatic = true
  · have hobs : (Exec.committedFrames run).flatMap (coinObs T (EntryObs T)) = [] :=
      List.flatMap_eq_nil_iff.mpr fun D member =>
        ite_eq_right fun h => by
          rw [Exec.committedFrames_isStatic run hs D member] at h
          cases h.2.1
    refine ⟨fun _ => hobs, fun _ => ⟨[], fun _ => ?_, hobs.symm⟩⟩
    have hview := Exec.getStor_committedPost_eq_of_static_protected_noStateGas run hs committed
      hsg T (State.Protected.of_code_ne_nil rootNonempty)
    exact congrArg ledgerView (funext fun k => congrArg (fun stor => stor.get k) hview)
  have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
  refine ⟨fun h => absurd h hs, fun bound => ?_⟩
  have c3 : (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
      (Ca).Replay ((Ca).frameEntry sevm pre.state) [] ((Ca).ofState post.state) := fun none _ =>
    ledgerView_congr fun k hi ha =>
      proxy_cell_of_noExec run committed codeEq hsg bal rootNonempty none hi ha
  have c12 : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        (Ca).Replay ((Ca).frameEntry sevm pre.state) [] ((Ca).ofState N.devm.state) ∧
        ∀ N', Exec.Deriv.ParentStep N' N →
          (Ca).Replay ((Ca).ofState N'.devm.state) [] ((Ca).ofState post.state) ∧
          ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) :=
    fun N chain x hat =>
      ⟨fun _ => ledgerView_congr fun k hi ha =>
          proxy_cell_to_exec run codeEq target hsg bal rootNonempty hi ha chain (.refl _) ⟨x, hat⟩,
        fun N' edge =>
          ⟨fun _ => congrArg (fun w => ledgerView (wordsAt T w))
              (proxy_tailH run codeEq hsg chain hat N' edge).1,
            (proxy_tailH run codeEq hsg chain hat N' edge).2⟩⟩
  by_cases admin : sevm.caller = adminOf pre.state T
  · -- the admin word's frame observes only what is below it
    have rootObs : coinObs T (EntryObs T) (Exec.Frame.ofRun run committed) = [] :=
      ite_eq_right fun h => (h.2.2.2 admin).elim
    have hlist : (Exec.committedFrames run).flatMap (coinObs T (EntryObs T)) =
        (Exec.descendantFrames run).flatMap (coinObs T (EntryObs T)) := by
      rw [frames, List.flatMap_cons, rootObs, List.nil_append]
    have callOnly : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .call := by
      intro N chain x hat
      obtain ⟨g, K, ⟨-, hd⟩ | ⟨rfl, -⟩⟩ := proxy_nodeH run codeEq hsg bal chain hat
      · refine (hd.1 ?_).elim
        rw [admin, target]
        rfl
      · rfl
    obtain ⟨steps, replay, observed⟩ := Exec.CoreAccounting.modelFrameNoStateGas
      (C := Ca) (V := Ob) (ca := T) (fun _ _ => rfl) entry_ofStateGet viewCarrier_append run hsg rootNonempty bound
      (fun {nodePc nodeSevm nodePre out frame rsm nextPc cevm raw inter} step enter child resume next chain childCommitted childBound => by
        have sevmEq : nodeSevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
        obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
        have isCall := callOnly _ chain x instruction
        subst isCall
        have nodeCode : nodePre.getCode T = pre.getCode T :=
          (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 T rootNonempty
        have nodeImage : some (nodePre.getCode T).toList = entrySem.image := by
          rw [nodeCode]; exact installed.1
        have childFork : HistFork cevm.sta.benvStat.fork :=
          Blanc.LockExclusion.Evm.step_spawn_child_forkIn step enter (by rw [sevmEq]; exact fork)
        have childDepth : cevm.sta.depth < sevm.depth := by
          rw [Frame.enter_run_depth enter, ← sevmEq]
          exact Step.spawn_depth_lt step
        obtain ⟨pcZero, getCode, -⟩ := Blanc.Evm.step_spawn_child step enter
        have childAt : entrySem.At T cevm.pc cevm.sta cevm.dyna := by
          refine ⟨by rw [getCode T]; exact nodeImage, fun childTarget => ⟨?_, pcZero⟩⟩
          obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
          subst hcevm
          have frameTarget : frame.inner.currentTarget = T := childTarget
          have code := Xinst.step_call_spawn_code spawn (by
            rw [frameTarget]
            exact entrySem.not_delegation nodeImage)
          change some frame.inner.code.toList = _
          rw [code, frameTarget]
          exact nodeImage
        exact (deeper _ _ _ _ child childDepth childAt child childCommitted childFork childAt
          (fun _ _ _ => trivial)).2 childBound)
      [] c3 c12
    refine ⟨steps, replay, ?_⟩
    change steps = (Exec.committedFrames run).flatMap (coinObs T (EntryObs T))
    rw [hlist]
    exact observed
  · -- an entry frame observes itself
    have rootObs : coinObs T (EntryObs T) (Exec.Frame.ofRun run committed) =
        [Exec.Frame.ofRun run committed] := ite_eq_left ⟨target, hs', hrun, admin⟩
    refine ⟨(Exec.committedFrames run).flatMap (coinObs T (EntryObs T)), fun all => ?_, rfl⟩
    have hlist : (Exec.committedFrames run).flatMap (coinObs T (EntryObs T)) =
        Exec.Frame.ofRun run committed ::
          (Exec.descendantFrames run).flatMap (coinObs T (EntryObs T)) := by
      rw [frames, List.flatMap_cons, rootObs]
      rfl
    have all' : ∀ G ∈ (Exec.committedFrames run).flatMap (coinObs T (EntryObs T)), EntryAllowed T G := all
    change ViewChain T ledgerView (EntryGood T) (ledgerView (wordsAt T pre.state))
      (((Exec.committedFrames run).flatMap (coinObs T (EntryObs T))).filter entryKeep)
      (ledgerView (wordsAt T post.state))
    rw [hlist] at all' ⊢
    obtain ⟨certified, size⟩ := all' _ List.mem_cons_self
    by_cases sel : Blanc.Sevm.selector sevm = rescueSelector
    · -- a rescue frame is marked out, and the view runs through what is below it
      have marked : ¬ entryKeep (Exec.Frame.ofRun run committed) = true := fun keep =>
        of_decide_eq_true keep sel
      rw [List.filter_cons_of_neg marked]
      obtain ⟨steps, replay, observed⟩ := Exec.CoreAccounting.modelFrameNoStateGas
        (C := Ca) (V := Ob) (ca := T) (fun _ _ => rfl) entry_ofStateGet viewCarrier_append run hsg rootNonempty bound
        (fun {nodePc nodeSevm nodePre out frame rsm nextPc cevm raw inter} step enter child resume next chain childCommitted childBound => by
          have sevmEq : nodeSevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
          obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
          obtain ⟨rfl, ctarget, -, cdata, cstate, ccode⟩ :=
            proxy_delegate_child run codeEq hsg bal (by rw [target]; exact admin) size chain hat spawn
          have nodeGetCode : ∀ a, nodePre.getCode a = pre.getCode a := fun a => by
            simp only [Devm.getCode, Devm.getAcct, cstate]
          have version : CurveCoins.UsdcVersion (pre.getCode (pre.getStorVal T implSlot).toAdr) := certified.1
          have code : cevm.sta.code = pre.getCode (pre.getStorVal T implSlot).toAdr := by
            rw [Frame.enter_run_code enter, ccode (by rw [target, nodeGetCode]; exact version_undelegated version),
              target, nodeGetCode]
          have childVersion : CurveCoins.UsdcVersion cevm.sta.code := code ▸ version
          obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
          obtain ⟨pcZero, childCode, -⟩ := Blanc.Evm.step_spawn_child step enter
          have childData : cevm.sta.data = sevm.data := by rw [hcevm]; exact cdata
          have childSel : Blanc.Sevm.selector cevm.sta = Blanc.Sevm.selector sevm := by
            simp only [Blanc.Sevm.selector, Sevm.dataWord, childData]
          have childTarget : cevm.sta.currentTarget = T := by
            rw [hcevm]
            exact ctarget.trans target
          have childFork : HistFork cevm.sta.benvStat.fork :=
            Blanc.LockExclusion.Evm.step_spawn_child_forkIn step enter (by rw [sevmEq]; exact fork)
          have childDepth : cevm.sta.depth < sevm.depth := by
            rw [Frame.enter_run_depth enter, ← sevmEq]
            exact Step.spawn_depth_lt step
          have childInstalled : cevm.dyna.state.getCode T = Proxy.code := by
            change cevm.dyna.getCode T = _
            rw [childCode, nodeGetCode]
            exact bytes_eq_of_image installed.1
          obtain ⟨cpc, csevm, cdyna⟩ := cevm
          dsimp only at pcZero childVersion childSel childTarget childFork childDepth childInstalled child
          subst pcZero
          cases raw with
          | error e => cases childCommitted
          | ok cpost =>
            exact version_rescue_replay deeper child childCommitted childVersion childFork childTarget
              (childSel.trans sel) childInstalled (Nat.le_of_lt childDepth) childBound)
        [] c3 c12
      have observed' : steps = (Exec.descendantFrames run).flatMap (coinObs T (EntryObs T)) := observed
      subst observed'
      exact replay fun G hG => all' G (List.mem_cons_of_mem _ hG)
    · have kept : entryKeep (Exec.Frame.ofRun run committed) = true := decide_eq_true sel
      rw [entryQuiet run codeEq fork target admin sel certified size, List.filter_cons_of_pos kept]
      exact ⟨⟨rfl, hrun, fork, rootNonempty⟩, rfl, rfl⟩

end Blanc.Lift.Usdc
