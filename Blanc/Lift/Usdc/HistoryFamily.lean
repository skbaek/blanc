import Blanc.Lift.Usdc.HistoryFamilyProxy
import Blanc.Lift.Token.FamilyReplay
import Blanc.Lift.Token.Holder
import Blanc.Lift.Usdc.RefineSigned
import Blanc.ExecutionOwnerFamilyPositional
import Blanc.Lift.Usdc.HistoryFamilyCodes

/-!
# USDC's code family ladder (U6h1)

The instance of the family ladder (`Blanc/ExecutionOwnerFamily.lean`,
`Blanc/ExecutionOwnerFamilyPositional.lean`) at the proxy `P`: the family is the implementation and
the library by code address (`usdcFamily`); the guarded book carrier (`usdcCarrier`) reads the
footprint ledger over a universe `U` with the guard `usdcGuard U A₀` (implementation slot, admin
word `A₀`, good ledger) and the allowed messages `usdcAllowed A₀` (the admin word asks only a
getter); observers are implementation frames and admin-word proxy frames (`usdcObs`), keyed on
the code a frame runs (decision usdc-u6h1-u2-amendments).

The family obligations:

* `usdc_spawnKinds`: a proxy frame decodes `_delegate`'s `DELEGATECALL` to the slot's
  implementation, or (admin) `CALL`; an implementation frame `CALL` or `DELEGATECALL` to the library;
  a library frame only `STATICCALL`;
* `usdc_spawnReplay`, per shape: proxy frames are model frames (`own = []`, or `own = [ask]` for the
  admin word, its getters keeping the storage), `rescueERC20` is a model frame with `own = [ask]`
  (`rescueLaw`), other implementation frames are whole frames (`impl_whole_law`, the library
  subtree observing nothing), and library frames are whole frames observing nothing (`lib_quiet`);
* the carrier side conditions, the admission's `installed`, and `usdcLadder`/`usdcPositionalLadder`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay Blanc.Lift.Token

/-- USDC's code family at the proxy: the implementation and the library by code address. -/
noncomputable def usdcFamily (P : Adr) : CodeFamily P proxySem :=
  ⟨[⟨usdcImpl, implSem⟩, ⟨usdcLib, libSem⟩]⟩

/-- The guard: the implementation slot names the implementation, the admin word is `A₀` (the
checkpoint's), and the footprint ledger over `U` is good. -/
def usdcGuard (U : Key → Prop) (A₀ : Adr) (s : Stor) : Prop :=
  s.get implSlot = usdcImpl.toB256 ∧ (s.get adminSlot).toAdr = A₀ ∧ (ledger U s).Good

/-- Allowed messages: `A₀` asks only a getter (F2 and `proxy_admin_selectors` at history level). -/
def usdcAllowed (A₀ : Adr) (e : Sevm) : Prop :=
  e.caller = A₀ → adminGetter e

/-- The observers: implementation frames, and proxy frames of the admin word (which run no
implementation). -/
def usdcObs (P : Adr) (f : Exec.Frame) : Prop :=
  f.sevm.code = Impl.code ∨ (f.sevm.code = Proxy.code ∧ f.sevm.caller = adminOf f.pre.state P)

/-- The whole frames: implementation frames other than `rescueERC20`, and library frames. -/
def usdcWhole (e : Sevm) : Prop :=
  (e.code = Impl.code ∧ Blanc.Sevm.selector e ≠ rescueSelector) ∨ e.code = Lib.code

/-- The related messages of an entry and its implementation frame. -/
def usdcRelated (a b : Sevm) : Prop :=
  a.caller = b.caller ∧ a.value = b.value ∧ a.data = b.data

/-- The specification the generic rungs carry: the proxy's code, no storage invariant (the guarded
carrier holds everything storage-dependent). -/
noncomputable def usdcSpec : ContractSpecSem := ContractSpecSem.ofStorageOnly proxySem (fun _ => True)

/-- The admission: the frame's keys are tracked, and the delegates are installed. -/
def usdcEntry (P : Adr) (U : Key → Prop) (sevm : Sevm) (devm : Devm) : Prop :=
  (∀ k ∈ frameKeys sevm, U k) ∧ (usdcFamily P).DelegatesInstalled devm.state

/-- The USDC carrier over a history's universe `U` and checkpoint admin `A₀`. -/
noncomputable def usdcCarrier (P : Adr) (U : Key → Prop) (A₀ : Adr) : ReplayCarrier P :=
  guardedBookCarrier P (usdcBookS P).toBook (ledger U) (usdcGuard U A₀) (usdcAllowed A₀)

/-- The USDC observer view over `usdcCarrier`. -/
noncomputable def usdcView (P : Adr) (U : Key → Prop) (A₀ : Adr) :
    ReplayObservation (usdcCarrier P U A₀) :=
  observerView P (usdcObs P) (B := (usdcBookS P).toBook) (read := ledger U)
    (Guard := usdcGuard U A₀) (Allowed := usdcAllowed A₀)

/-! ## The carrier -/

section Carrier

variable {P : Adr} {U : Key → Prop} {A₀ : Adr}

/-- A replay between two states' boundaries, from the guard and the allowed messages. -/
theorem usdcReplay_of {w w' : State} {xs : List Sevm}
    (h : usdcGuard U A₀ (w.getStor P) → (∀ e ∈ xs, usdcAllowed A₀ e) →
      (usdcBookS P).toBook.run (ledger U (w.getStor P)) xs = some (ledger U (w'.getStor P)) ∧
        usdcGuard U A₀ (w'.getStor P)) :
    (usdcCarrier P U A₀).Replay ((usdcCarrier P U A₀).ofState w) xs
      ((usdcCarrier P U A₀).ofState w') := by
  classical
  intro guarded allowed
  obtain ⟨run, guard'⟩ := h (of_decide_eq_true guarded) allowed
  exact ⟨run, decide_eq_true guard'⟩

/-- The empty replay between states agreeing on the proxy's storage. -/
theorem usdcReplay_nil {w w' : State} (storage : w'.getStor P = w.getStor P) :
    (usdcCarrier P U A₀).Replay ((usdcCarrier P U A₀).ofState w) []
      ((usdcCarrier P U A₀).ofState w') :=
  usdcReplay_of fun g _ => ⟨by rw [storage]; rfl, by rw [storage]; exact g⟩

/-- A one-message replay, from the book's step. -/
theorem usdcReplay_one {w w' : State} {e : Sevm}
    (h : usdcGuard U A₀ (w.getStor P) → usdcAllowed A₀ e →
      (usdcBookS P).step (ledger U (w.getStor P)) e = some (ledger U (w'.getStor P)) ∧
        usdcGuard U A₀ (w'.getStor P)) :
    (usdcCarrier P U A₀).Replay ((usdcCarrier P U A₀).ofState w) [e]
      ((usdcCarrier P U A₀).ofState w') :=
  usdcReplay_of fun g allowed => by
    obtain ⟨step, g'⟩ := h g (allowed e List.mem_cons_self)
    refine ⟨?_, g'⟩
    change ((usdcBookS P).step _ e).bind (fun l => some l) = _
    rw [step]
    rfl

theorem usdcCarrier_append {a b c : (usdcCarrier P U A₀).Snap} {xs ys : List Sevm}
    (left : (usdcCarrier P U A₀).Replay a xs b) (right : (usdcCarrier P U A₀).Replay b ys c) :
    (usdcCarrier P U A₀).Replay a (xs ++ ys) c := by
  intro guarded allowed
  obtain ⟨r₁, g₁⟩ := left guarded fun e he => allowed e (List.mem_append_left _ he)
  obtain ⟨r₂, g₂⟩ := right g₁ fun e he => allowed e (List.mem_append_right _ he)
  refine ⟨?_, g₂⟩
  rw [Book.run_append, show (usdcBookS P).toBook.run a.1 xs = some b.1 from r₁]
  exact r₂

theorem usdcCarrier_ofStateGet {s s' : State}
    (h : ∀ k, (s.getStor P).get k = (s'.getStor P).get k) :
    (usdcCarrier P U A₀).ofState s = (usdcCarrier P U A₀).ofState s' := by
  have hg : (s.getStor P).get = (s'.getStor P).get := funext h
  have ht : SlotFootprint.trackedWord Key.slot U (s.getStor P) =
      SlotFootprint.trackedWord Key.slot U (s'.getStor P) :=
    funext fun k => by simp only [SlotFootprint.trackedWord, h]
  have hl : ledger U (s.getStor P) = ledger U (s'.getStor P) := by
    simp only [ledger, ht, hg]
  have hguard : usdcGuard U A₀ (s.getStor P) = usdcGuard U A₀ (s'.getStor P) := by
    simp only [usdcGuard, hg, hl]
  show (ledger U (s.getStor P), _) = (ledger U (s'.getStor P), _)
  rw [hl]
  congr 1
  exact decide_eq_decide.mpr (by rw [hguard])

theorem usdcView_static (f : Exec.Frame) (h : f.sevm.isStatic = true) :
    (usdcView P U A₀).frameObs f = [] := by
  classical
  show (if f.sevm.currentTarget = P ∧ f.sevm.isStatic = false ∧ usdcObs P f then [f.sevm] else []) = []
  rw [ite_eq_right (fun c => by rw [h] at c; exact Bool.noConfusion c.2.1)]

theorem usdcView_foreign (f : Exec.Frame) (h : f.sevm.currentTarget ≠ P) :
    (usdcView P U A₀).frameObs f = [] := by
  classical
  show (if f.sevm.currentTarget = P ∧ f.sevm.isStatic = false ∧ usdcObs P f then [f.sevm] else []) = []
  rw [ite_eq_right (fun c => h c.1)]

theorem usdcView_obs (f : Exec.Frame) (target : f.sevm.currentTarget = P)
    (nonstatic : f.sevm.isStatic = false) (obs : usdcObs P f) :
    (usdcView P U A₀).frameObs f = [f.sevm] := by
  classical
  show (if f.sevm.currentTarget = P ∧ f.sevm.isStatic = false ∧ usdcObs P f then [f.sevm] else []) = _
  rw [ite_eq_left ⟨target, nonstatic, obs⟩]

theorem usdcView_not_obs (f : Exec.Frame) (obs : ¬ usdcObs P f) :
    (usdcView P U A₀).frameObs f = [] := by
  classical
  show (if f.sevm.currentTarget = P ∧ f.sevm.isStatic = false ∧ usdcObs P f then [f.sevm] else []) = []
  rw [ite_eq_right (fun c => obs c.2.2)]

end Carrier

/-! ## The family's frames -/

/-- A family frame at the proxy: the three codes installed, and it runs the proxy, the
implementation at its code address, or the library at its code address. -/
theorem usdc_runs {P : Adr} {sevm : Sevm} {pre : Devm} (runs : (usdcFamily P).Runs sevm pre) :
    sevm.currentTarget = P ∧ Codes P pre ∧
      (sevm.code = Proxy.code ∨ (sevm.code = Impl.code ∧ sevm.codeAddress = some usdcImpl) ∨
        (sevm.code = Lib.code ∧ sevm.codeAddress = some usdcLib)) := by
  obtain ⟨target, image, installed, kind⟩ := runs
  have hi := installed ⟨usdcImpl, implSem⟩ List.mem_cons_self
  have hl := installed ⟨usdcLib, libSem⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨target, ⟨bytes_eq_of_image image, bytes_eq_of_image hi, bytes_eq_of_image hl⟩, ?_⟩
  rcases kind with h | ⟨m, hm, ca, code⟩
  · exact .inl (bytes_eq_of_image h)
  · simp only [usdcFamily, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact .inr (.inl ⟨bytes_eq_of_image code, ca⟩)
    · exact .inr (.inr ⟨bytes_eq_of_image code, ca⟩)

/-- **The family's spawn kinds.** -/
theorem usdc_spawnKinds (P : Adr) (U : Key → Prop) (A₀ : Adr) :
    (usdcFamily P).SpawnKinds (usdcGuard U A₀) := by
  intro sevm pre post run runs fork guard node chain x hat
  obtain ⟨target, -, kind⟩ := usdc_runs runs
  rcases kind with codeEq | ⟨codeEq, -⟩ | ⟨codeEq, -⟩
  · obtain ⟨g, K, ⟨hx, hd⟩ | ⟨hx, -, -⟩⟩ := proxy_node run codeEq fork chain hat
    · refine .inr (.inr ⟨hx, fun g' a rest hs => ⟨⟨usdcImpl, implSem⟩, List.mem_cons_self, ?_⟩⟩)
      obtain ⟨-, b', w, S, M, G, rest0, -, -, hdev⟩ := hd
      change node.devm = _ at hdev
      rw [hdev, St.stack] at hs
      obtain ⟨-, ha⟩ := List.cons.inj hs
      obtain ⟨ha, -⟩ := List.cons.inj ha
      have slot : pre.getStorVal sevm.currentTarget implSlot = usdcImpl.toB256 := by
        rw [target]; exact guard.1
      rw [← ha, slot]
      exact toAdr_toB256 _
    · exact .inl hx
  · rcases impl_exec_kind run codeEq fork chain hat with hx | ⟨hx, word⟩
    · exact .inl hx
    · exact .inr (.inr ⟨hx, fun g a rest hs => ⟨⟨usdcLib, libSem⟩,
        List.mem_cons_of_mem _ List.mem_cons_self, by rw [word g a rest hs]; exact usdcLib_word⟩⟩)
  · exact .inr (.inl (parentPrefix_exec_staticcall_of_cert Lib.cert_check lib_staticOnly
      (root := ⟨0, sevm, pre, .ok post, run⟩) rfl codeEq fork chain hat))

/-! ## The replay shapes -/

section Shapes

variable {P : Adr} {U : Key → Prop} {A₀ : Adr}

/-- The model shape of `CodeFamily.SpawnReplay` over the USDC carrier. -/
def UsdcModel (P : Adr) (U : Key → Prop) (A₀ : Adr) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (committed : Execution.commits (.ok post) = true) : Prop :=
  ∃ own : List Sevm,
    (usdcView P U A₀).obs own = (usdcView P U A₀).frameObs (Exec.Frame.ofRun run committed) ∧
    ((∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
        ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) →
      (usdcCarrier P U A₀).Replay ((usdcCarrier P U A₀).ofState pre.state) own
        ((usdcCarrier P U A₀).ofState post.state)) ∧
    (∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        (usdcCarrier P U A₀).Replay ((usdcCarrier P U A₀).ofState pre.state) own
          ((usdcCarrier P U A₀).ofState N.devm.state) ∧
        ∀ N', Exec.Deriv.ParentStep N' N →
          (usdcCarrier P U A₀).Replay ((usdcCarrier P U A₀).ofState N'.devm.state) []
            ((usdcCarrier P U A₀).ofState post.state) ∧
          ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y))

theorem usdcRun_one (l : Ledger) (e : Sevm) :
    (usdcBookS P).toBook.run l [e] = (usdcBookS P).step l e := by
  change ((usdcBookS P).step l e).bind (fun l => some l) = _
  cases (usdcBookS P).step l e <;> rfl

/-- **A proxy frame is a model frame**: an admin-word frame observes itself, holds a getter when
allowed, and ends silently after `upgradeToAndCall`'s `CALL`; any other caller observes nothing,
keeps the storage up to `_delegate`'s `DELEGATECALL`, and ends in the resumed state. -/
theorem usdc_proxy_model {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) (codeEq : sevm.code = Proxy.code)
    (target : sevm.currentTarget = P) (codes : Codes P pre) (fork : CoveredFork sevm.benvStat.fork)
    (nonstatic : sevm.isStatic = false) (guard : usdcGuard U A₀ (pre.state.getStor P)) :
    UsdcModel P U A₀ run committed := by
  have tail := fun {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N)
      {x : Xinst} (hat : Ninst.At N.sevm.code N.pc (.exec x)) => proxy_tail run codeEq fork chain hat
  by_cases admin : sevm.caller = adminOf pre.state P
  · have admin' : sevm.caller = adminOf pre.state sevm.currentTarget := by rw [target]; exact admin
    refine ⟨[sevm], ?_, fun _ => ?_, fun N chain x hat => ⟨?_, fun N' edge => ?_⟩⟩
    · rw [usdcView_obs (Exec.Frame.ofRun run committed) target nonstatic (.inr ⟨codeEq, admin⟩)]
      rfl
    · refine usdcReplay_one fun g allowed => ?_
      have getter : adminGetter sevm := allowed (admin.trans g.2.1)
      have hsel : Blanc.Sevm.selector sevm ∉ [0x3659cfe6, 0x4f1ef286, 0x8f283970] := by
        rcases getter with h | h <;> rw [h] <;> decide
      have keep := ((proxy_admin_rule run codeEq fork admin').2.2 hsel).2 post rfl
      rw [target] at keep
      rw [keep]
      refine ⟨?_, g⟩
      have adminL : sevm.caller = (ledger U (pre.state.getStor P)).admin := admin
      simp only [usdcBookS, adminL, getter, ↓reduceIte]
    · have hsel := (proxy_admin_exec run codeEq fork admin' N chain x hat).2.1
      refine usdcReplay_one fun _ allowed => ?_
      have getter : adminGetter sevm := allowed (admin.trans guard.2.1)
      exfalso
      rcases getter with h | h <;> rw [hsel] at h <;> exact absurd h (by decide)
    · obtain ⟨st, noExec⟩ := tail chain hat N' edge
      exact ⟨usdcReplay_nil (congrArg (State.getStor · P) st), noExec⟩
  · have notAdmin' : sevm.caller ≠ adminOf pre.state sevm.currentTarget := by
      rw [target]; exact admin
    have slot : (pre.state.getStor sevm.currentTarget).get implSlot = usdcImpl.toB256 := by
      rw [target]; exact guard.1
    refine ⟨[], ?_, fun noExec => ?_, fun N chain x hat => ⟨?_, fun N' edge => ?_⟩⟩
    · rw [usdcView_not_obs]
      · rfl
      · rintro (h | ⟨-, h⟩)
        · exact proxy_ne_impl (codeEq.symm.trans h)
        · exact admin h
    · exfalso
      obtain ⟨N, f, rsm, pc', chain, step⟩ := proxy_spawn_exists run codeEq fork slot notAdmin'
        (by rw [show pre.state.getCode usdcImpl = Impl.code from codes.2.1]; exact impl_undelegated)
        (impl_not_precompile fork)
      obtain ⟨x, hat, -, -⟩ := Evm.step_spawn_inv step
      exact noExec N chain x hat
    · obtain ⟨g, K, ⟨-, hd⟩ | ⟨-, hs, -⟩⟩ := proxy_node run codeEq fork chain hat
      · obtain ⟨-, b', w, S, M, G, rest, hstate, -, hdev⟩ := hd
        change N.devm = _ at hdev
        have nstate : N.devm.state = pre.state := by rw [hdev]; exact hstate
        exact usdcReplay_nil (congrArg (State.getStor · P) nstate)
      · exact (notAdmin' (by rw [adminOf_eq]; exact hs.1)).elim
    · obtain ⟨st, noExec⟩ := tail chain hat N' edge
      exact ⟨usdcReplay_nil (congrArg (State.getStor · P) st), noExec⟩

/-- An admin-word message allowed at a frame whose selector is `rescueERC20`'s is not the admin
word's. -/
theorem rescue_notAdmin {sevm : Sevm} {w : State} (guard : usdcGuard U A₀ (w.getStor P))
    (hsel : Blanc.Sevm.selector sevm = rescueSelector) (allowed : usdcAllowed A₀ sevm) :
    sevm.caller ≠ adminOf w P := fun h => by
  have getter := allowed (h.trans guard.2.1)
  rcases getter with g | g <;> rw [hsel] at g <;> exact absurd g (by decide)

/-- **`rescueERC20` is a model frame** observing its own message (`rescueLaw`). -/
theorem usdc_rescue_model {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) (codeEq : sevm.code = Impl.code)
    (target : sevm.currentTarget = P) (codeAddr : sevm.codeAddress = some usdcImpl)
    (codes : Codes P pre) (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (keys : ∀ k ∈ frameKeys sevm, U k) (hsel : Blanc.Sevm.selector sevm = rescueSelector) :
    UsdcModel P U A₀ run committed := by
  obtain ⟨stepId, nodes⟩ := rescueLaw (U := U) run codeEq target codeAddr fork nonstatic keys hsel
  refine ⟨[sevm], ?_, fun noExec => ?_, fun N chain x hat => ⟨?_, fun N' edge => ?_⟩⟩
  · rw [usdcView_obs (Exec.Frame.ofRun run committed) target nonstatic (.inl codeEq)]
    rfl
  · refine usdcReplay_one fun g allowed => ?_
    have keep := rescueQuietEnd run codeEq target fork nonstatic hsel (proxy_protected codes.1) noExec
    rw [keep]
    exact ⟨stepId (rescue_notAdmin g hsel allowed), g⟩
  · obtain ⟨-, nstor, -⟩ := nodes N chain x hat
    refine usdcReplay_one fun g allowed => ?_
    rw [nstor]
    exact ⟨stepId (rescue_notAdmin g hsel allowed), g⟩
  · obtain ⟨-, -, after⟩ := nodes N chain x hat
    obtain ⟨pstor, noExec⟩ := after N' edge
    exact ⟨usdcReplay_nil pstor, noExec⟩

end Shapes

/-! ## Whole frames -/

section Whole

variable {P : Adr} {U : Key → Prop} {A₀ : Adr}

/-- The committed frames of a successful run: the run's own frame, then its descendants. -/
theorem committedFrames_ok {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) :
    Exec.committedFrames run = Exec.Frame.ofRun run committed :: Exec.descendantFrames run := by
  rw [Exec.committedFrames, dite_eq_left committed]

/-- **The library subtree of an implementation frame observes nothing**: an implementation frame
decoding only `DELEGATECALL`s spawns library frames, whose descendants are static. -/
theorem impl_descendants_quiet {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) (codes : Codes P pre)
    (nodes : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall) :
    ∀ f ∈ Exec.descendantFrames run, (usdcView P U A₀).frameObs f = [] := by
  refine Exec.descendantFrames_of_spawns (root := ⟨0, sevm, pre, .ok post, run⟩) ?_ run (.refl _)
    (fun _ h => h) (fun _ h => h)
  intro N f rsm pc' cevm raw child h chain step enter _ _
  obtain ⟨sevmEq, nfork, pcZero, cfork, -, ncodes, -, -⟩ := node_child chain fork codes step enter
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  have hx := nodes N chain x hat
  subst hx
  rcases impl_node run codeEq fork chain hat spawn with h | ⟨-, g, rest, stack⟩
  · cases h
  have adr : usdcLib.toB256.toAdr = usdcLib := toAdr_toB256 _
  obtain ⟨-, -, -, -, -, hK, -⟩ := Xinst.step_delegatecall_spawn_exact nfork spawn stack
    (by rw [adr, ncodes.2.2]; exact lib_undelegated)
  rw [adr] at hK
  have ccode : cevm.sta.code = Lib.code := by
    rw [Frame.enter_run_code enter, hK]; exact ncodes.2.2
  cases raw with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at h
  | ok cpost =>
    obtain ⟨cevmPc, csevm, cdyna⟩ := cevm
    dsimp only at pcZero
    subst pcZero
    refine ⟨usdcView_not_obs _ ?_, fun g hg => usdcView_static g ((lib_quiet child ccode cfork).2 g hg)⟩
    rintro (o | ⟨o, -⟩)
    · exact lib_ne_impl (ccode.symm.trans o)
    · exact lib_ne_proxy (ccode.symm.trans o)

/-- **An implementation frame other than `rescueERC20` is a whole frame**: from a guarded boundary,
over its allowed observations, the book runs its own message to its end. -/
theorem usdc_impl_whole (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (committed : Execution.commits (.ok post) = true)
    (codeEq : sevm.code = Impl.code) (target : sevm.currentTarget = P)
    (codeAddr : sevm.codeAddress = some usdcImpl) (codes : Codes P pre)
    (fork : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false)
    (keys : ∀ k ∈ frameKeys sevm, U k) (hsel : Blanc.Sevm.selector sevm ≠ rescueSelector) :
    ∃ steps : List Sevm,
      (usdcCarrier P U A₀).Replay ((usdcCarrier P U A₀).ofState pre.state) steps
        ((usdcCarrier P U A₀).ofState post.state) ∧
      (usdcView P U A₀).obs steps = (Exec.committedFrames run).flatMap (usdcView P U A₀).frameObs := by
  refine ⟨(Exec.committedFrames run).flatMap (usdcView P U A₀).frameObs, usdcReplay_of fun g allowed => ?_, rfl⟩
  have own : (usdcView P U A₀).frameObs (Exec.Frame.ofRun run committed) = [sevm] :=
    usdcView_obs (Exec.Frame.ofRun run committed) target nonstatic (.inl codeEq)
  have mem : sevm ∈ (Exec.committedFrames run).flatMap (usdcView P U A₀).frameObs :=
    List.mem_flatMap.mpr ⟨_, by rw [committedFrames_ok run committed]; exact List.mem_cons_self,
      by rw [own]; exact List.mem_singleton_self _⟩
  have notAdmin : sevm.caller ≠ adminOf pre.state P := fun h => by
    obtain ⟨c, dec⟩ := impl_decodes run codeEq fork
    exact decodeCall_not_getter dec (allowed sevm mem (h.trans g.2.1))
  have lib : some (pre.state.getCode usdcLib).toList = libSem.image := by
    rw [show pre.state.getCode usdcLib = Lib.code from codes.2.2]; rfl
  obtain ⟨step, hi, ha, nodes⟩ :=
    impl_whole_law inj apart run codeEq target codeAddr fork nonstatic keys lib notAdmin g.2.2 hsel
  have quiet : (Exec.descendantFrames run).flatMap (usdcView P U A₀).frameObs = [] :=
    List.flatMap_eq_nil_iff.mpr (impl_descendants_quiet run codeEq fork codes nodes)
  have hsteps : (Exec.committedFrames run).flatMap (usdcView P U A₀).frameObs = [sevm] := by
    rw [committedFrames_ok run committed, List.flatMap_cons, own, quiet]; rfl
  have key : (usdcBookS P).toBook.run (ledger U (pre.state.getStor P)) [sevm] =
      some (ledger U (post.state.getStor P)) := by rw [usdcRun_one, step]
  exact ⟨(congrArg ((usdcBookS P).toBook.run (ledger U (pre.state.getStor P))) hsteps).trans key, by rw [hi]; exact g.1, by rw [ha]; exact g.2.1, book_good step g.2.2⟩

/-- **A library frame is a whole frame observing nothing**: it keeps its storage owner's storage and
spawns only static frames. -/
theorem usdc_lib_whole {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) (codeEq : sevm.code = Lib.code)
    (target : sevm.currentTarget = P) (fork : CoveredFork sevm.benvStat.fork) :
    ∃ steps : List Sevm,
      (usdcCarrier P U A₀).Replay ((usdcCarrier P U A₀).ofState pre.state) steps
        ((usdcCarrier P U A₀).ofState post.state) ∧
      (usdcView P U A₀).obs steps = (Exec.committedFrames run).flatMap (usdcView P U A₀).frameObs := by
  refine ⟨[], ?_, ?_⟩
  · have keep := (lib_children run codeEq fork).2 post rfl
    rw [target] at keep
    exact usdcReplay_nil keep
  · rw [committedFrames_ok run committed, List.flatMap_cons,
      usdcView_not_obs (Exec.Frame.ofRun run committed) ?_,
      List.flatMap_eq_nil_iff.mpr fun g hg => usdcView_static g ((lib_quiet run codeEq fork).2 g hg)]
    · rfl
    · rintro (o | ⟨o, -⟩)
      · exact lib_ne_impl (codeEq.symm.trans o)
      · exact lib_ne_proxy (codeEq.symm.trans o)

end Whole

/-! ## The family obligations and the ladders -/

/-- **The family's replay obligation.** -/
theorem usdc_spawnReplay (P : Adr) {U : Key → Prop} (A₀ : Adr) (inj : SlotFootprint.Inj Key.slot U)
    (apart : SlotFootprint.Apart Key.slot fixedSlots U) :
    (usdcFamily P).SpawnReplay (usdcGuard U A₀) usdcWhole (usdcEntry P U) (usdcCarrier P U A₀)
      (usdcView P U A₀) := by
  intro sevm pre post run committed runs fork admitted _ nonstatic guard
  obtain ⟨target, codes, kind⟩ := usdc_runs runs
  have keys : ∀ k ∈ frameKeys sevm, U k := (admitted.root target).1
  rcases kind with codeEq | ⟨codeEq, codeAddr⟩ | ⟨codeEq, -⟩
  · refine ⟨fun whole => ?_, fun _ => usdc_proxy_model run committed codeEq target codes fork
      nonstatic guard⟩
    rcases whole with ⟨h, -⟩ | h
    · exact (proxy_ne_impl (codeEq.symm.trans h)).elim
    · exact (lib_ne_proxy (h.symm.trans codeEq)).elim
  · by_cases hsel : Blanc.Sevm.selector sevm = rescueSelector
    · refine ⟨fun whole => ?_, fun _ => usdc_rescue_model run committed codeEq target codeAddr codes
        fork nonstatic keys hsel⟩
      rcases whole with ⟨-, h⟩ | h
      · exact (h hsel).elim
      · exact (lib_ne_impl (h.symm.trans codeEq)).elim
    · exact ⟨fun _ => usdc_impl_whole inj apart run committed codeEq target codeAddr codes fork
        nonstatic keys hsel, fun whole => (whole (.inl ⟨codeEq, hsel⟩)).elim⟩
  · exact ⟨fun _ => usdc_lib_whole run committed codeEq target fork,
      fun whole => (whole (.inr codeEq)).elim⟩

/-- The admission installs the delegates. -/
theorem usdcEntry_installed (P : Adr) (U : Key → Prop) :
    ∀ (sevm : Sevm) (devm : Devm), sevm.currentTarget = P → usdcEntry P U sevm devm →
      (usdcFamily P).DelegatesInstalled devm.state :=
  fun _ _ _ entry => entry.2

theorem usdcSpec_preserves (P : Adr) (U : Key → Prop) :
    usdcSpec.PreservesAdmitted P (usdcEntry P U) := by
  intro sevm pre post fork run admitted image wf inv
  exact ⟨trivial, trivial⟩

/-- **USDC's family accounting ladder** over a universe `U` (injective and apart from the fixed
slots) and the checkpoint admin word `A₀`. -/
noncomputable def usdcLadder (P : Adr) {U : Key → Prop} (A₀ : Adr)
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U) :
    AccountingLadderAdmitted usdcSpec P (usdcEntry P U) :=
  (usdcFamily P).ladder (c := usdcSpec) (usdcGuard U A₀) usdcWhole (usdcCarrier P U A₀)
    (usdcView P U A₀) usdcCarrier_append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    usdcCarrier_ofStateGet usdcView_static usdcView_foreign
    (guardedBookCarrier_unguarded P (usdcObs P)) (usdcEntry_installed P U)
    (usdc_spawnKinds P U A₀) (usdc_spawnReplay P A₀ inj apart) (usdcSpec_preserves P U)

/-- **USDC's family positional ladder** (`Opaque` = non-static whole frames at the proxy). -/
noncomputable def usdcPositionalLadder (P : Adr) {U : Key → Prop} (A₀ : Adr)
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U) :
    PositionalLadder usdcSpec P (usdcEntry P U) :=
  (usdcFamily P).positionalLadder (c := usdcSpec) (usdcGuard U A₀) usdcWhole (usdcCarrier P U A₀)
    (usdcView P U A₀) usdcCarrier_append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    usdcCarrier_ofStateGet usdcView_static usdcView_foreign
    (guardedBookCarrier_unguarded P (usdcObs P)) (usdcEntry_installed P U)
    (usdc_spawnKinds P U A₀) (usdc_spawnReplay P A₀ inj apart) (usdcSpec_preserves P U)

/-- **The positional law over a configured history** (`CodeFamily.configuredHistory_at` at USDC's
instance): at the entry of every settled frame not enclosed by an earlier non-static whole frame at
the proxy, the boundary is the replay, from the checkpoint, of the earlier settled frames'
observations. -/
theorem usdc_configuredHistory_at (P : Adr) {U : Key → Prop} (A₀ : Adr)
    (inj : SlotFootprint.Inj Key.slot U) (apart : SlotFootprint.Apart Key.slot fixedSlots U)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : history.FrameAdmitted P (usdcEntry P U))
    (installed : some (checkpoint.state.getCode P).toList = proxySem.image) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      history.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ CodeFamily.Opaque P usdcWhole A) →
      ∃ steps, (usdcCarrier P U A₀).Replay ((usdcCarrier P U A₀).ofState checkpoint.state) steps
          ((usdcCarrier P U A₀).ofState f.pre.state) ∧
        (usdcView P U A₀).obs steps = before.flatMap (usdcView P U A₀).frameObs :=
  (usdcFamily P).configuredHistory_at (c := usdcSpec) (usdcGuard U A₀) usdcWhole (usdcCarrier P U A₀)
    (usdcView P U A₀) usdcCarrier_append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    usdcCarrier_ofStateGet usdcView_static usdcView_foreign
    (guardedBookCarrier_unguarded P (usdcObs P)) (usdcEntry_installed P U)
    (usdc_spawnKinds P U A₀) (usdc_spawnReplay P A₀ inj apart) (usdcSpec_preserves P U) history
    admitted ⟨installed, trivial, trivial⟩

/-- **The admission over a history's key universe**: every raw frame's keys are among the
history's touched keys, and the implementation and the library stay installed at every raw frame
(`ConfiguredHistoryTrace.rawFrames_codeImage_of_installed`). -/
theorem usdc_history_admitted {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : UsdcInstalled P checkpoint.state) :
    tr.FrameAdmitted P (usdcEntry P (historyKeyUniverse P tr K₀)) := by
  apply (tr.frameAdmitted_iff_rawFrames P _).2
  intro root member target
  refine ⟨fun k hk => Or.inr (List.mem_flatMap.mpr ⟨root, member, ?_⟩), fun m hm => ?_⟩
  · simpa only [target, ite_true] using hk
  · simp only [usdcFamily, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact tr.rawFrames_codeImage_of_installed implSem usdcImpl installed.impl root member
    · exact tr.rawFrames_codeImage_of_installed libSem usdcLib installed.lib root member

end Blanc.Lift.Usdc
