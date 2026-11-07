import Blanc.Lift.Usdc.EntryChainRoots
import Blanc.Lift.Usdc.EntryChainSettled
import Blanc.Lift.RootStanding

/-!
# USDC's view at a frame below a rescue or an admin's upgrade

`usdc_viewChain_certified` reaches the entry of a settled frame no non-static frame at `T` encloses. A frame on
`rescueERC20`, and the admin's `upgradeToAndCall`, are non-static frames at `T` whose one external call can lead anywhere,
so a holder's frame can lie below them. The view runs through both, since each is silent around its call. Only the chain's
links stop it: `LinkFrame`. Below a link every frame is static or the library (`link_below`).

`usdc_viewAt_links`: the ledger view at the entry of any settled frame no earlier link encloses.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.Proxy Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

variable {T : Adr}

/-- **A link of the chain**: a non-static frame of the proxy at `T`, called by other than the admin, off `rescueERC20`. -/
def LinkFrame (T : Adr) (A : Exec.Frame) : Prop :=
  A.sevm.currentTarget = T ∧ A.sevm.isStatic = false ∧ ChainObs T A

local notation "Ca" => viewCarrier T ledgerView (EntryGood T) (EntryAllowed T) entryKeep
local notation "Ob" => viewObservation T ledgerView (EntryObs T) (EntryGood T) (EntryAllowed T) entryKeep

/-- The positional accounting of every derivation at the proxy, below a depth. -/
local notation "Deep" D => ForallDeeperAtSem D T entrySem
  (fun pc s d e _ => Exec.PositionalAccountingIn HistFork T entrySem (fun _ _ => True) Ca Ob (LinkFrame T) pc s d e)

/-- **A version's frame on `rescueERC20` at `T` is positional**: everything below it is below its one `CALL`. -/
theorem version_rescue_positional {D : Nat} (deeper : Deep D) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (committed : Execution.commits (.ok post) = true)
    (version : CurveCoins.UsdcVersion sevm.code) (fork : HistFork sevm.benvStat.fork)
    (hsel : Blanc.Sevm.selector sevm = rescueSelector)
    (installed : pre.state.getCode T = Proxy.code) (depth : sevm.depth ≤ D)
    (bound : sum pre.state.bal < 2 ^ 256) (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame)
    (split : Exec.committedFrames run = before ++ f :: after)
    (noOpaque : Exec.NoOpaqueAbove (LinkFrame T) before f) :
    ∃ steps, (Ca).Replay ((Ca).ofState pre.state) steps ((Ca).ofState f.pre.state) ∧
      (Ob).obs steps = before.flatMap (Ob).frameObs := by
  have hsg := fork.stateGas_none
  have rootNonempty : (pre.getCode T).toList ≠ [] := by
    change (pre.state.getCode T).toList ≠ []
    rw [installed]
    exact proxy_toList_ne_nil
  rw [Exec.committedFrames, dite_eq_left committed] at split
  cases before with
  | nil =>
    obtain ⟨rfl, -⟩ := List.cons.inj split
    exact ⟨[], (Ca).nil _, rfl⟩
  | cons P rest =>
  obtain ⟨hP, hdesc⟩ := List.cons.inj split
  have rootObs : (Ob).frameObs (Exec.Frame.ofRun run committed) = [] :=
    ite_eq_right fun h => (version_ne_proxy version h.2.2.1).elim
  refine Exec.PositionalAccounting.modelFrameAtNoStateGas (C := Ca) (V := Ob) (Opaque := LinkFrame T) entry_ofStateGet
    viewCarrier_append run committed hsg rootNonempty bound ?_ [] rootObs.symm ?_ P rest f after hP hdesc
    (Exec.NoOpaqueAbove.tail noOpaque)
  · intro nodePc nodeSevm nodePre out frame rsm nextPc cevm raw inter step enter child resume next chain childCommitted
      childBound
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
    exact deeper _ _ _ _ child childDepth childAt child childCommitted childFork childAt (fun _ _ _ => trivial) childBound
  · intro N chain x hat
    obtain ⟨-, state, after⟩ := version_rescue_nodes run version hsg hsel chain hat
    refine ⟨fun _ => ?_, fun N' edge => ⟨fun _ => ?_, (after N' edge).2⟩⟩
    · exact congrArg (fun w => ledgerView (wordsAt T w)) state
    · exact congrArg (fun w => ledgerView (wordsAt T w)) (after N' edge).1

/-- **The positional handler at the proxy**: only a link stops the descent. -/
theorem entryTargetLinks {sevm : Sevm} {pre post : Devm}
    (hrun : entrySem.Run sevm pre post) (target : sevm.currentTarget = T) (deeper : Deep sevm.depth) :
    Exec.PositionalAccountingIn HistFork T entrySem (fun _ _ => True) Ca Ob (LinkFrame T) 0 sevm pre (.ok post) := by
  by_cases hs : sevm.isStatic = true
  · exact Exec.PositionalAccounting.static (fun h => h.stateGas_none) entry_ofStateGet entry_core hs
  intro run committed fork installed admitted bound before f after split noOpaque
  have codeEq : sevm.code = Proxy.code := hrun
  have hsg : sevm.benvStat.rules.stateGas = none := fork.stateGas_none
  have bal : sevm.benvStat.rules.bal = none := fork.bal_none
  have rootNonempty : (pre.getCode T).toList ≠ [] := fun empty =>
    entrySem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
  rw [Exec.committedFrames, dite_eq_left committed] at split
  cases before with
  | nil =>
    obtain ⟨rfl, -⟩ := List.cons.inj split
    exact ⟨[], (Ca).nil _, rfl⟩
  | cons P rest =>
  obtain ⟨hP, hdesc⟩ := List.cons.inj split
  have noBelow := Exec.NoOpaqueAbove.tail noOpaque
  have nilRep : ∀ {a b : StorWords}, a = b → (Ca).Replay a [] b := fun h => by
    rw [h]
    exact (Ca).nil _
  have c3cell : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        ledgerView (wordsAt T pre.state) = ledgerView (wordsAt T N.devm.state) ∧
        ∀ N', Exec.Deriv.ParentStep N' N →
          ledgerView (wordsAt T N'.devm.state) = ledgerView (wordsAt T post.state) ∧
          ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) :=
    fun N chain x hat =>
      ⟨ledgerView_congr fun k hi ha =>
          (proxy_cell_to_exec run codeEq target hsg bal rootNonempty hi ha chain (.refl _) ⟨x, hat⟩).symm,
        fun N' edge =>
          ⟨congrArg (fun w => ledgerView (wordsAt T w))
              (proxy_tailH run codeEq hsg chain hat N' edge).1.symm,
            (proxy_tailH run codeEq hsg chain hat N' edge).2⟩⟩
  by_cases admin : sevm.caller = adminOf pre.state T
  · -- the admin word's frame: its one external instruction is `upgradeToAndCall`'s `CALL`
    have rootObs : (Ob).frameObs (Exec.Frame.ofRun run committed) = [] :=
      ite_eq_right fun h => (h.2.2.2 admin).elim
    have callOnly : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .call := by
      intro N chain x hat
      obtain ⟨g, K, ⟨-, hd⟩ | ⟨rfl, -⟩⟩ := proxy_nodeH run codeEq hsg bal chain hat
      · refine (hd.1 ?_).elim
        rw [admin, target]
        rfl
      · rfl
    refine Exec.PositionalAccounting.modelFrameAtNoStateGas (C := Ca) (V := Ob) (Opaque := LinkFrame T) entry_ofStateGet
      viewCarrier_append run committed hsg rootNonempty bound ?_ [] rootObs.symm
      (fun N chain x hat => ⟨nilRep (c3cell N chain x hat).1,
        fun N' edge => ⟨nilRep ((c3cell N chain x hat).2 N' edge).1, ((c3cell N chain x hat).2 N' edge).2⟩⟩)
      P rest f after hP hdesc noBelow
    intro nodePc nodeSevm nodePre out frame rsm nextPc cevm raw inter step enter child resume next chain childCommitted
      childBound
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
    exact deeper _ _ _ _ child childDepth childAt child childCommitted childFork childAt (fun _ _ _ => trivial) childBound
  · by_cases sel : Blanc.Sevm.selector sevm = rescueSelector
    · -- a rescue frame: the view runs through its delegate child
      have marked : ¬ entryKeep (Exec.Frame.ofRun run committed) = true := fun keep => of_decide_eq_true keep sel
      have rootObs : (Ob).frameObs (Exec.Frame.ofRun run committed) = [Exec.Frame.ofRun run committed] :=
        ite_eq_left ⟨target, hs', hrun, admin⟩
      refine ⟨(P :: rest).flatMap (Ob).frameObs, fun all => ?_, rfl⟩
      have all' : ∀ G ∈ (P :: rest).flatMap (Ob).frameObs, EntryAllowed T G := all
      have self : EntryAllowed T (Exec.Frame.ofRun run committed) := by
        refine all' _ ?_
        rw [List.flatMap_cons, ← hP, rootObs]
        exact List.mem_append_left _ List.mem_cons_self
      obtain ⟨certified, size⟩ := self
      obtain ⟨steps, replay, observed⟩ := Exec.PositionalAccounting.modelFrameAtNoStateGas (C := Ca) (V := Ob)
        (Opaque := LinkFrame T) entry_ofStateGet viewCarrier_append run committed hsg rootNonempty bound
        (fun {nodePc nodeSevm nodePre out frame rsm nextPc cevm raw inter} step enter child resume next chain childCommitted
            childBound before f after split noOpaque => by
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
          dsimp only at pcZero childVersion childSel childFork childDepth childInstalled child split
          subst pcZero
          cases raw with
          | error e => cases childCommitted
          | ok cpost =>
            exact version_rescue_positional deeper child childCommitted childVersion childFork (childSel.trans sel)
              childInstalled (Nat.le_of_lt childDepth) childBound before f after split noOpaque)
        [Exec.Frame.ofRun run committed] rootObs.symm
        (fun N chain x hat =>
          ⟨fun _ => by
              change ViewChain T ledgerView (EntryGood T) _ ([Exec.Frame.ofRun run committed].filter entryKeep) _
              rw [List.filter_cons_of_neg marked]
              exact nilRep (c3cell N chain x hat).1 fun _ h => absurd h List.not_mem_nil,
            fun N' edge => ⟨nilRep ((c3cell N chain x hat).2 N' edge).1, ((c3cell N chain x hat).2 N' edge).2⟩⟩)
        P rest f after hP hdesc noBelow
      have observed' : steps = (P :: rest).flatMap (Ob).frameObs := observed
      subst observed'
      exact replay all
    · -- a link stops the descent
      subst hP
      exact (noOpaque [] _ rest after rfl hdesc ⟨target, hs', ⟨hrun, admin⟩, sel⟩).elim

/-- Positional accounting of every derivation at the proxy, stopped only by links. -/
theorem entry_positional_links : Exec.Fa (Exec.WknSem T entrySem
    (fun pc s d e _ => Exec.PositionalAccountingIn HistFork T entrySem (fun _ _ => True) Ca Ob (LinkFrame T) pc s d e)) :=
  Exec.positionalAccountingIn HistFork.stateGas_none (fun _ _ => rfl) entry_ofStateGet
    (fun f hf => ite_eq_right fun h => hf h.1) viewCarrier_append (fun _ op => op.1) entry_core
    (fun hrun target deeper => entryTargetLinks hrun target deeper)

/-- **Below a link every frame is static, a version or the library.** -/
theorem link_below {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (fork : HistFork sevm.benvStat.fork) (target : sevm.currentTarget = T)
    (notAdmin : sevm.caller ≠ adminOf pre.state T) (sel : Blanc.Sevm.selector sevm ≠ rescueSelector)
    (certified : UsdcCertified pre T) (size : sevm.data.length < 2 ^ 256) :
    ∀ g ∈ Exec.descendantFrames run,
      g.sevm.isStatic = true ∨ g.sevm.code = Lib.code ∨ CurveCoins.UsdcVersion g.sevm.code := by
  have hsg : sevm.benvStat.rules.stateGas = none := fork.stateGas_none
  have bal : sevm.benvStat.rules.bal = none := fork.bal_none
  refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, .ok post, run⟩)
    (Q := fun g => g.sevm.isStatic = true ∨ g.sevm.code = Lib.code ∨ CurveCoins.UsdcVersion g.sevm.code) ?_ run (.refl _)
    (fun _ h => h) (fun _ h => h)
  intro N f rsm pc' cevm raw child h chain step enter _ _
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨rfl, ctarget, cstatic, cdata, cstate, ccode⟩ :=
    proxy_delegate_child run codeEq hsg bal (by rw [target]; exact notAdmin) size chain hat spawn
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeGetCode : ∀ a, N.devm.getCode a = pre.getCode a := fun a => by
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
  have csg : cevm.sta.benvStat.rules.stateGas = none := by
    rw [Blanc.Evm.step_spawn_child_benvStat step enter, sevmEq]
    exact hsg
  have libClause : cevm.sta.code = Impl.code → cevm.dyna.state.getCode usdcLib = Lib.code := fun hi => by
    have := certified.2.1 (code.symm.trans hi)
    change (cevm.dyna.getCode usdcLib) = _
    rw [childCode, nodeGetCode]
    exact this
  refine ⟨.inr (.inr childVersion), fun g hg => ?_⟩
  obtain ⟨cpc, csevm, cdyna⟩ := cevm
  dsimp only at pcZero childVersion childSel csg libClause child
  subst pcZero
  rcases version_below child childVersion csg (by rw [childSel]; exact sel) libClause g hg with s | c
  · exact .inl s
  · exact .inr (.inl c)

section Roots

local notation "Op" => LinkFrame T

/-- The view at a frame of a root chain, from each root's positional replay. -/
theorem viewAt_of_roots
    (core : ∀ R : Exec.Frame, RootReady HistFork T entrySem (fun _ _ => True) R → ∃ steps,
      (Ca).Replay (ledgerView (wordsAt T R.pre.state)) steps (ledgerView (wordsAt T R.post.state)) ∧
      steps = (Exec.committedFrames R.run).flatMap (coinObs T (EntryObs T)))
    (positional : ∀ R : Exec.Frame, RootReady HistFork T entrySem (fun _ _ => True) R →
      ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
        Exec.committedFrames R.run = before ++ f :: after → Exec.NoOpaqueAbove Op before f →
        ∃ steps, (Ca).Replay (ledgerView (wordsAt T R.pre.state)) steps (ledgerView (wordsAt T f.pre.state)) ∧
          steps = before.flatMap (coinObs T (EntryObs T))) :
    ∀ {a b : StorWords} {roots : List Exec.Frame}, RootChain T a roots b →
      (∀ R ∈ roots, RootReady HistFork T entrySem (fun _ _ => True) R) →
      ∀ {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame},
        roots.flatMap (fun R => Exec.committedFrames R.run) = before ++ f :: after →
        Exec.NoOpaqueAbove Op before f →
        (∀ F ∈ coinFrames T (EntryObs T) before, EntryAllowed T F) →
        ViewChain T ledgerView (EntryGood T) (ledgerView a) ((coinFrames T (EntryObs T) before).filter entryKeep)
          (ledgerView (wordsAt T f.pre.state)) := by
  intro a b roots
  induction roots generalizing a with
  | nil =>
    intro _ _ before f after split
    have empty : ([] : List Exec.Frame) = before ++ f :: after := split
    cases before <;> simp only [List.nil_append, List.cons_append, reduceCtorEq] at empty
  | cons R rest ih =>
    intro h ready before f after split noOpaque all
    obtain ⟨rfl, tail⟩ := h
    have here := ready R List.mem_cons_self
    rw [List.flatMap_cons] at split
    rcases List.split_append_cons split with ⟨m, hx, -⟩ | ⟨n, hb, hy⟩
    · obtain ⟨s, r, rfl⟩ := positional R here before f m hx noOpaque
      exact r all
    · subst hb
      obtain ⟨steps, replay, rfl⟩ := core R here
      rw [coinFrames_append] at all ⊢
      rw [List.filter_append]
      exact (replay fun G hG => all G (List.mem_append_left _ hG)).append
        (ih tail (fun G hG => ready G (List.mem_cons_of_mem _ hG)) hy (Exec.NoOpaqueAbove.drop noOpaque)
          fun G hG => all G (List.mem_append_right _ hG))

end Roots

/-- **The view at a settled frame no earlier link encloses.** -/
theorem usdc_viewAt_links {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (capabilities : BodyStageCapabilities HistFork)
    (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames) {before : List Exec.Frame} {f : Exec.Frame}
    {after : List Exec.Frame} (split : trace.settledFrames = before ++ f :: after)
    (noOpaque : Exec.NoOpaqueAbove (LinkFrame T) before f) :
    ViewChain T ledgerView (EntryGood T) (ledgerView (wordsAt T start.state))
      (coinFrames T (ChainObs T) before) (ledgerView (wordsAt T f.pre.state)) := by
  have notDeleted := (usdc_outputNotDeleted trace capabilities installed certified).1
  have split' := split
  rw [trace.settledFrames_eq] at split'
  rw [← filter_coinFrames]
  refine viewAt_of_roots (fun R ready => ?_) (fun R ready before f after split noOpaque => ?_)
    (Blanc.Lift.MidHistoryTraceIn.rootChain trace (fun _ h => HistFork.stateGas_none h) installed proxy_toList_ne_nil
      proxy_not_delegation notDeleted)
    (Blanc.Lift.MidHistoryTraceIn.rootsReady trace capabilities (C := Proxy.code) rfl installed proxy_toList_ne_nil
      proxy_not_delegation notDeleted) split' noOpaque fun F member => ?_
  · obtain ⟨fork, at_, admitted, bound, -⟩ := ready
    exact (entry_core R.pc R.sevm R.pre R.out R.run at_ R.run R.committed fork at_ admitted).2 bound
  · obtain ⟨fork, at_, admitted, bound, -⟩ := ready
    obtain ⟨steps, replay, observed⟩ := entry_positional_links R.pc R.sevm R.pre R.out R.run at_ R.run
      R.committed fork at_ admitted bound before f after split noOpaque
    exact ⟨steps, replay, observed⟩
  · obtain ⟨inFs, target, -, obs⟩ := mem_coinFrames.mp member
    have inAll : F ∈ trace.settledFrames := by
      rw [split]
      exact List.mem_append_left _ inFs
    exact ⟨certified F inAll target obs.1 obs.2, settled_data_bound trace capabilities F inAll⟩

/-- **A non-static frame running neither a version nor the library lies below no link** of a certified history. -/
theorem noLink_above {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (capabilities : BodyStageCapabilities HistFork)
    (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T trace.settledFrames) {before : List Exec.Frame} {f : Exec.Frame}
    (sub : ∀ F ∈ before, F ∈ trace.settledFrames) (mutable : f.sevm.isStatic = false)
    (notLib : f.sevm.code ≠ Lib.code) (notVersion : ¬ CurveCoins.UsdcVersion f.sevm.code) :
    Exec.NoOpaqueAbove (LinkFrame T) before f := by
  rintro b A m n split desc ⟨target, nonstatic, obs⟩
  have mem : A ∈ trace.settledFrames := sub _ (by rw [split]; exact List.mem_append_right _ List.mem_cons_self)
  obtain ⟨pc, code, fork, -⟩ := (usdc_viewChain_certified trace capabilities installed certified).1.good A
    (mem_coinFrames.mpr ⟨mem, target, nonstatic, obs⟩)
  have good := certified A mem target obs.1.1 obs.1.2
  have size := settled_data_bound trace capabilities A mem
  have inDesc : f ∈ Exec.descendantFrames A.run := by
    rw [desc]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨apc, sevm, pre, out, run, committed⟩ := A
  dsimp only at pc code fork target good size inDesc obs
  subst pc
  cases out with
  | error e => cases committed
  | ok post =>
    rcases link_below (T := T) run code fork target obs.1.2 obs.2 good size f inDesc with s | c | v
    · rw [mutable] at s
      cases s
    · exact notLib c
    · exact notVersion v

/-- **The proxy's code stands right after any transaction of a certified history's last block.** A delegating proxy has no
`InstalledCert`; each root keeps it out of the deletion set by `root_noDel`, so its code stays through the stages. -/
theorem usdc_code_at_cut {cfg : ChainConfig} {start : Benv} {pre post : BlockChain}
    (history : MidHistoryTraceIn HistFork cfg start pre) (block : ConfiguredBlockTraceIn HistFork cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (capabilities : BodyStageCapabilities HistFork)
    (installed : start.state.getCode T = Proxy.code)
    (certified : CertifiedSettled T (history.step block).settledFrames) :
    cut.afterBenv.state.getCode T = Proxy.code := by
  have prior := (usdc_outputNotDeleted history capabilities installed
    fun F m => certified F (List.mem_append_left _ m)).2
  refine (stagedBody_cut_live (F := HistFork) (wa := T) (sem := entrySem) (C := Proxy.code) (k := 0)
    (W := fun _ l => l = []) block.bodyTrace cut rfl (capabilities.stateGas_none block.forkIn) proxy_toList_ne_nil
    proxy_not_delegation (fun _ => AdrSet.not_mem_empty) block.forkIn block.withdrawalsBound
    (fun R member ready _ _ _ => ⟨root_noDel ready fun G hG => certified G ?_, [], rfl,
      fun _ hp => absurd hp List.not_mem_nil⟩)
    (fun _ _ _ e _ _ hp => by subst e; cases hp) ⟨prior, [], rfl, fun _ hp => absurd hp List.not_mem_nil⟩).1
  rw [(history.step block).settledFrames_eq]
  exact List.mem_flatMap.mpr ⟨R, List.mem_append_right _ member, hG⟩

end Blanc.Lift.Usdc
