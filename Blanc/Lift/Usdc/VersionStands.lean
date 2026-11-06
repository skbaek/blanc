import Blanc.Lift.RootStanding
import Blanc.Lift.Usdc.EntryChainScan

/-!
# A listed version, once standing, stands: the scan is a complete check

Every certificate of the three versions and the library has no `SELFDESTRUCT` (kernel decided, `*.cert_noSelfdestruct`).
V2, V2_1 and the library spawn no `DELEGATECALL`, so nothing else runs in their storage context; V2_2's only one runs the
library (`impl_committed`). So no settled root deletes one of these accounts while it holds its code, and a read at the
start of a mid history reaches every later settled root (`entry_ready`).

`certifiedSettled_of_scan`: the word's version stands at the start, and each `Upgraded` log names a version standing at
its root's entry; every settled proxy frame is certified. `MidHistoryTraceIn.live_of_roots` carries the named version
standing through the history, with `T`'s own deletion exclusion, so nothing is read between upgrades.
`scanRoot_of_cuts` reads the versions at one cut each: the log's root lies after that cut.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-! ## At one root -/

theorem v2_undelegatedCert : ∀ f ∈ ImplV2.cert.prog, f.execsSatisfy Xinst.notDelegatecall = true := by
  decide +kernel

theorem v2_1_undelegatedCert : ∀ f ∈ ImplV2_1.cert.prog, f.execsSatisfy Xinst.notDelegatecall = true := by
  decide +kernel

theorem lib_undelegatedCert : ∀ f ∈ Lib.cert.prog, f.execsSatisfy Xinst.notDelegatecall = true := by
  decide +kernel

theorem v2_safety : InstalledRuntimeSafety ImplV2.code :=
  .of_undelegatedCert ImplV2.cert_check v2_undelegatedCert ImplV2.cert_noSelfdestruct
    ImplV2.code_not_delegation (UsdcContextCode.ne_nil (.inr (.inr (.inl rfl))))

theorem v2_1_safety : InstalledRuntimeSafety ImplV2_1.code :=
  .of_undelegatedCert ImplV2_1.cert_check v2_1_undelegatedCert ImplV2_1.cert_noSelfdestruct
    ImplV2_1.code_not_delegation (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inl rfl)))))

theorem lib_safety : InstalledRuntimeSafety Lib.code :=
  .of_undelegatedCert Lib.cert_check lib_undelegatedCert Lib.cert_noSelfdestruct
    Lib.code_not_delegation (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inr rfl))))))

theorem v2_size : ImplV2.code.size ≠ 0 ∧ ImplV2.code.size ≠ eoaDelegatedCodeLength := by decide +kernel

theorem v2_1_size : ImplV2_1.code.size ≠ 0 ∧ ImplV2_1.code.size ≠ eoaDelegatedCodeLength := by decide +kernel

theorem impl_size : Impl.code.size ≠ 0 ∧ Impl.code.size ≠ eoaDelegatedCodeLength := by decide +kernel

theorem lib_size : Lib.code.size ≠ 0 ∧ Lib.code.size ≠ eoaDelegatedCodeLength := by decide +kernel

/-- A code at an account, under the code's own semantics. -/
def standingAt (b : Adr) (C : ByteArray) (size : C.size ≠ 0 ∧ C.size ≠ eoaDelegatedCodeLength) : StandingCode :=
  ⟨b, C, CodeSem.ofBytes C size.1 size.2, rfl⟩

variable {a : Adr}

/-- A spawn's child at `a`, which holds V2_2, runs V2_2 or the library. -/
theorem impl_child {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (fork : HistFork sevm.benvStat.fork) (code : pre.state.getCode a = Impl.code)
    (lib : pre.state.getCode usdcLib = Lib.code)
    (context : sevm.currentTarget = a → sevm.code = Impl.code ∨ sevm.code = Lib.code)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm}
    (step : Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc') (enter : f.enter = .run cevm)
    (childTarget : cevm.sta.currentTarget = a) : cevm.sta.code = Impl.code ∨ cevm.sta.code = Lib.code := by
  have hsg := fork.stateGas_none
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have implNe : Impl.code.toList ≠ [] := UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inl rfl)))))
  have nodeCode : N.devm.getCode a = Impl.code := by
    refine ((Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 a ?_).trans code
    change (pre.state.getCode a).toList ≠ []
    rw [code]
    exact implNe
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨-, -, actual⟩ := Blanc.Evm.step_spawn_child step enter
  obtain ⟨benv, -, hcevm⟩ := Frame.enter_run_inv enter
  have frameTarget : f.inner.currentTarget = a := by rw [hcevm] at childTarget; exact childTarget
  have frameCode : cevm.sta.code = f.inner.code := Frame.enter_run_code enter
  have direct : x = .call ∨ x = .staticcall → cevm.sta.code = Impl.code := fun d => by
    rw [frameCode, Xinst.step_directCall_spawn_code d spawn
      (by rw [frameTarget, nodeCode]; exact Impl.code_not_delegation), frameTarget, nodeCode]
  by_cases parent : sevm.currentTarget = a
  · rcases context parent with hc | hc
    · obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas certL_check
        (F := ⟨0, sevm, pre, out, run⟩) rfl hc hsg chain
      have kind := ok.execsSatisfy (Cursor.execsSatisfy_of_reachable impl_kinds reach) hat
      cases x with
      | call => exact .inl (direct (.inl rfl))
      | delegatecall => exact .inr (frameCode.trans (impl_delegate_lib run hc hsg lib chain hat spawn))
      | _ => simp only [implKinds, reduceCtorEq, beq_iff_eq, Bool.or_eq_true, or_self] at kind
    · obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas Lib.cert_check
        (F := ⟨0, sevm, pre, out, run⟩) rfl hc hsg chain
      exact .inl (direct (.inr (isStaticcall_eq
        (ok.execsSatisfy (Cursor.execsSatisfy_of_reachable lib_staticOnly reach) hat))))
  · have away : N.sevm.currentTarget ≠ cevm.sta.currentTarget := by
      rw [sevmEq, childTarget]
      exact parent
    have entered := actual away
      (by rw [childTarget, nodeCode]; exact fun e => implNe (by rw [e]; exact ByteArray.toList_empty))
      (by rw [childTarget, nodeCode]; exact Impl.code_not_delegation)
    rw [childTarget, nodeCode] at entered
    exact .inl entered

/-- **Every committed frame in the storage of an account holding V2_2 runs V2_2 or the library**, when the library
stands. -/
theorem impl_committed (n : Nat) : ∀ {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out), sevm.depth < n → HistFork sevm.benvStat.fork →
    pre.state.getCode a = Impl.code → pre.state.getCode usdcLib = Lib.code →
    (sevm.currentTarget = a → sevm.code = Impl.code ∨ sevm.code = Lib.code) →
    ∀ G ∈ Exec.committedFrames run, G.pc = 0 ∧ G.sevm.benvStat.rules.stateGas = none ∧
      (G.sevm.currentTarget = a → G.sevm.code = Impl.code ∨ G.sevm.code = Lib.code) := by
  induction n with
  | zero => exact fun _ h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro sevm pre out run depth fork code lib context G member
    unfold Exec.committedFrames at member
    split at member
    · rename_i committed
      rcases List.mem_cons.mp member with rfl | below
      · exact ⟨rfl, fork.stateGas_none, context⟩
      · refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, out, run⟩)
          (Q := fun G => G.pc = 0 ∧ G.sevm.benvStat.rules.stateGas = none ∧
            (G.sevm.currentTarget = a → G.sevm.code = Impl.code ∨ G.sevm.code = Lib.code))
          ?_ run (.refl _) (fun _ h => h) (fun _ h => h) G below
        intro N f rsm pc' cevm raw child h chain step enter _ into
        have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
        have childDepth : cevm.sta.depth < n := by
          have : cevm.sta.depth < sevm.depth := by
            rw [Frame.enter_run_depth enter, ← sevmEq]
            exact Step.spawn_depth_lt step
          omega
        have childFork : HistFork cevm.sta.benvStat.fork :=
          Blanc.LockExclusion.Evm.step_spawn_child_forkIn step enter (by rw [sevmEq]; exact fork)
        have childContext := impl_child run fork code lib context chain step enter
        obtain ⟨pcZero, getCode, -⟩ := Blanc.Evm.step_spawn_child step enter
        have keep : ∀ {b : Adr} {C : ByteArray}, C.toList ≠ [] → pre.state.getCode b = C →
            cevm.dyna.state.getCode b = C := fun {b C} ne hb => by
          change cevm.dyna.getCode b = _
          rw [getCode]
          refine ((Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 b ?_).trans hb
          change (pre.state.getCode b).toList ≠ []
          rw [hb]
          exact ne
        have childCode := keep (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inl rfl)))))) code
        have childLib := keep (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inr rfl)))))) lib
        obtain ⟨cpc, csevm, cdyna⟩ := cevm
        dsimp only at pcZero child childDepth childFork childContext childCode childLib
        subst pcZero
        have all := ih child childDepth childFork childCode childLib childContext
        have frames : Exec.committedFrames child = Exec.Frame.ofRun child h :: Exec.descendantFrames child := by
          simp only [Exec.committedFrames, dite_eq_left h]
        rw [frames] at all
        exact ⟨all _ List.mem_cons_self, fun g hg => all g (List.mem_cons_of_mem _ hg)⟩
    · exact absurd member List.not_mem_nil

/-- A root that finds V2_2 and the library keeps the account out of the deletion set. -/
theorem impl_root_noDel {s0 : Impl.code.size ≠ 0} {sd : Impl.code.size ≠ eoaDelegatedCodeLength} {R : Exec.Frame}
    (ready : RootReady HistFork a (CodeSem.ofBytes Impl.code s0 sd) (fun _ _ => True) R)
    (lib : R.pre.state.getCode usdcLib = Lib.code) (initial : Devm.NoDel a R.pre) : Devm.NoDel a R.post := by
  obtain ⟨fork, at_, -, -, pcZero⟩ := ready
  rcases R with ⟨pc, sevm, pre, out, run, committed⟩
  dsimp only at fork at_ lib initial pcZero
  subst pcZero
  have hsg := fork.stateGas_none
  have frames := impl_committed (a := a) (sevm.depth + 1) run (Nat.lt_succ_self _) fork
    (bytes_eq_of_image at_.1) lib (fun t => .inl (bytes_eq_of_image (at_.2 t).1))
  have safe : ∀ N ∈ Exec.retainedNodes run, N.sevm.currentTarget = a →
      ¬ Linst.At N.sevm.code N.pc .selfdestruct := by
    intro N retained target
    obtain ⟨frame, member, chain⟩ := (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix run N).mp retained
    obtain ⟨framePc, frameSg, classify⟩ := frames frame member
    have same : N.sevm = frame.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
    have family : UsdcContextCode N.sevm.code := by
      rcases classify (by rw [← same]; exact target) with c | c
      · rw [same]; exact .inr (.inr (.inr (.inr (.inl c))))
      · rw [same]; exact .inr (.inr (.inr (.inr (.inr c))))
    obtain ⟨certificate, checked, noSelfdestruct⟩ := usdcContextCode_certified _ family
    exact not_selfdestruct_of_parentPrefix_noStateGas checked noSelfdestruct framePc
      (by change frame.sevm.code = N.sevm.code; rw [← same]) frameSg chain
  have result := Exec.inv_noDel_of_retained_terminal_safe run committed hsg safe initial
  cases out with
  | error error => cases committed
  | ok post => exact result

/-! ## Along a mid history -/

section Mid

variable {cfg : ChainConfig} {start : Benv} {future : BlockChain}
  (trace : MidHistoryTraceIn HistFork cfg start future) (capabilities : BodyStageCapabilities HistFork)

include capabilities in
/-- **A listed version, with the library under V2_2, standing at the start of a mid history stands at every settled
root.** One read at the start. -/
theorem entry_ready {e : UsdcDeployedEntry} (version : CurveCoins.UsdcVersion e.code)
    (code : start.state.getCode e.adr = e.code)
    (lib : e.code = Impl.code → start.state.getCode usdcLib = Lib.code) :
    ∀ R ∈ trace.settledRoots, e.RuntimeReady R.pre := by
  obtain ⟨adr, C, base, before⟩ := e
  dsimp only at version code lib
  intro R member
  refine ⟨?_, fun hi => ?_⟩
  · rcases version with rfl | rfl | rfl
    · exact stands_of_safety capabilities trace v2_safety (standingAt adr _ v2_size).image code R member
    · exact stands_of_safety capabilities trace v2_1_safety (standingAt adr _ v2_1_size).image code R member
    · have libStands := stands_of_safety capabilities trace lib_safety (standingAt usdcLib _ lib_size).image
        (lib rfl)
      exact stands_of_law capabilities trace (sem := CodeSem.ofBytes Impl.code impl_size.1 impl_size.2) rfl
        (UsdcContextCode.ne_nil (.inr (.inr (.inr (.inr (.inl rfl)))))) Impl.code_not_delegation code
        (fun Q here ready => impl_root_noDel ready (libStands Q here)) R member
  · exact stands_of_safety capabilities trace lib_safety (standingAt usdcLib _ lib_size).image (lib hi) R member

end Mid

/-! ## The word's version, standing, as a state invariant -/

/-- What must stand for the word `v` to name a listed version. -/
def VersionWitness (Vs : List UsdcDeployedEntry) (v : B256) (l : List StandingCode) : Prop :=
  ∃ e ∈ Vs, v.toAdr = e.adr ∧
    ((e.code = ImplV2.code ∧ l = [standingAt e.adr _ v2_size]) ∨
     (e.code = ImplV2_1.code ∧ l = [standingAt e.adr _ v2_1_size]) ∨
     (e.code = Impl.code ∧ l = [standingAt e.adr _ impl_size, standingAt usdcLib _ lib_size]))

variable {T : Adr} {Vs : List UsdcDeployedEntry}

theorem namedReady_of_witness {w : State} {l : List StandingCode}
    (witness : VersionWitness Vs ((w.getStor T).get implSlot) l) (stands : Stands l w) : NamedReady T Vs w := by
  obtain ⟨e, he, word, cases⟩ := witness
  refine ⟨e, he, word, ?_⟩
  rcases cases with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact ⟨(stands _ List.mem_cons_self).trans c.symm,
      fun i => absurd (c.symm.trans i) (by decide +kernel)⟩
  · exact ⟨(stands _ List.mem_cons_self).trans c.symm,
      fun i => absurd (c.symm.trans i) (by decide +kernel)⟩
  · exact ⟨(stands _ List.mem_cons_self).trans c.symm,
      fun _ => stands _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem witness_of_ready {w : State} (list : VersionList Vs) {v : B256} {e : UsdcDeployedEntry} (he : e ∈ Vs)
    (word : v.toAdr = e.adr) (code : w.getCode e.adr = e.code)
    (lib : e.code = Impl.code → w.getCode usdcLib = Lib.code) :
    ∃ l, VersionWitness Vs v l ∧ Stands l w := by
  rcases list.codes e he with c | c | c
  · exact ⟨_, ⟨e, he, word, .inl ⟨c, rfl⟩⟩, by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact code.trans c⟩
  · exact ⟨_, ⟨e, he, word, .inr (.inl ⟨c, rfl⟩)⟩, by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact code.trans c⟩
  · refine ⟨_, ⟨e, he, word, .inr (.inr ⟨c, rfl⟩)⟩, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact code.trans c
    · rw [List.mem_singleton] at hp
      subst hp
      exact lib c

theorem version_stays : WitnessStays HistFork (VersionWitness Vs) := by
  intro R v l witness stands p hp ready initial
  obtain ⟨e, -, -, cases⟩ := witness
  rcases cases with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rw [List.mem_singleton] at hp
    subst hp
    exact root_noDel_of_safety BodyStageCapabilities.historical v2_safety rfl ready initial
  · rw [List.mem_singleton] at hp
    subst hp
    exact root_noDel_of_safety BodyStageCapabilities.historical v2_1_safety rfl ready initial
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact impl_root_noDel (s0 := impl_size.1) (sd := impl_size.2) ready
        (stands _ (List.mem_cons_of_mem _ List.mem_cons_self)) initial
    · rw [List.mem_singleton] at hp
      subst hp
      exact root_noDel_of_safety BodyStageCapabilities.historical lib_safety rfl ready initial

section Scan

variable {cfg : ChainConfig} {checkpoint future' : BlockChain}
  (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future')
  (capabilities : BodyStageCapabilities HistFork)
  {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn HistFork cfg start future)
  (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
  (list : VersionList Vs)
  (scan : ∀ R ∈ trace.settledRoots, ScanRoot T Vs R)
  (apart : KnownImplSlotApart T history.rawNodes)

include rootsIn apart in
/-- The slot exclusion at the retained nodes of one settled root. -/
theorem scan_apartAt {R : Exec.Frame} (here : R ∈ trace.settledRoots) :
    KnownImplSlotApart T (Exec.retainedNodes R.run) := fun m hm =>
  apart m (history.rawNodes_of_mem_rawFrames _
    (history.mem_rawFrames_of_mem_settledRoots R (rootsIn R here)) m
    ((Exec.retainedNodes_sublist_rawNodes R.run).subset hm))

include capabilities rootsIn list scan apart in
/-- **The scan alone excludes `T`'s deletion, keeps its code, and keeps the word's version standing.** -/
theorem scan_live (installed : start.state.getCode T = Proxy.code) (initial : NamedReady T Vs start.state) :
    trace.OutputNotDeleted T ∧ future.state.getCode T = Proxy.code ∧ NamedReady T Vs future.state ∧
      ∀ R ∈ trace.settledRoots, R.pre.state.getCode T = Proxy.code ∧ NamedReady T Vs R.pre.state := by
  have bal : ∀ {fork}, HistFork fork → fork.ruleSet.bal = none := fun h => h.bal_none
  have law : ∀ R ∈ trace.settledRoots, RootStep HistFork T entrySem implSlot (VersionWitness Vs) R := by
    intro R here ready l witness stands
    have proxy : R.pre.getCode T = Proxy.code := bytes_eq_of_image ready.2.1.1
    have live := namedReady_of_witness witness stands
    have apartR := scan_apartAt history trace rootsIn apart here
    obtain ⟨e, he, word, code⟩ :=
      scan_post history capabilities bal list (rootsIn R here) proxy live (scan R here) apartR
    refine ⟨root_noDel ready fun G hG _ _ _ => ?_, witness_of_ready list he word code.1 code.2⟩
    exact scan_frames history capabilities bal list (rootsIn R here) proxy live (scan R here) apartR G hG
  obtain ⟨e, he, word, code, lib⟩ := initial
  obtain ⟨nd, final, roots⟩ := Blanc.Lift.MidHistoryTraceIn.live_of_roots trace capabilities (sem := entrySem) rfl
    proxy_toList_ne_nil proxy_not_delegation law version_stays ⟨installed, witness_of_ready list he word code lib⟩
  obtain ⟨finalCode, l, witness, stands⟩ := final
  exact ⟨nd, finalCode, namedReady_of_witness witness stands, fun R here => by
    obtain ⟨rootCode, l, witness, stands⟩ := roots R here
    exact ⟨rootCode, namedReady_of_witness witness stands⟩⟩

include capabilities rootsIn list scan apart in
/-- **The scan is a complete check**: with the word's version standing at the start and the logs scanned, the settled
proxy frames are certified. Nothing is asked about deletion, nor about any root between upgrades. -/
theorem certifiedSettled_of_scan (installed : start.state.getCode T = Proxy.code)
    (initial : NamedReady T Vs start.state) : CertifiedSettled T trace.settledFrames := by
  have bal : ∀ {fork}, HistFork fork → fork.ruleSet.bal = none := fun h => h.bal_none
  obtain ⟨-, -, -, roots⟩ := scan_live history capabilities trace rootsIn list scan apart installed initial
  intro G member target _ _
  rw [trace.settledFrames_eq] at member
  obtain ⟨R, here, frame⟩ := List.mem_flatMap.mp member
  exact scan_frames history capabilities bal list (rootsIn R here) (roots R here).1 (roots R here).2 (scan R here)
    (scan_apartAt history trace rootsIn apart here) G frame

end Scan

/-- **A root's scan from one cut per version**: each `Upgraded` log names a listed version with a mid history from a cut,
at which it (and, under V2_2, the library) stands, holding this root. -/
theorem scanRoot_of_cuts {cfg : ChainConfig} {future : BlockChain} (capabilities : BodyStageCapabilities HistFork)
    {R : Exec.Frame}
    (logs : ∀ entry ∈ R.post.logs, UpgradedTargetSatisfies T (fun a => ∃ e ∈ Vs, a = e.adr ∧
      CurveCoins.UsdcVersion e.code ∧ ∃ (c : Benv) (suffix : MidHistoryTraceIn HistFork cfg c future),
        (c.state.getCode e.adr = e.code ∧ (e.code = Impl.code → c.state.getCode usdcLib = Lib.code)) ∧
        R ∈ suffix.settledRoots) entry) : ScanRoot T Vs R := fun entry present address topics => by
  obtain ⟨e, he, adr, version, c, suffix, ⟨code, lib⟩, here⟩ := logs entry present address topics
  exact ⟨e, he, adr, entry_ready suffix capabilities version code lib R here⟩

end Blanc.Lift.Usdc
