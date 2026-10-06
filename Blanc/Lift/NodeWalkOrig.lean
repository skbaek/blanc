import Blanc.Lift.NodeWalk
import Blanc.Lift.WitnessFork

/-!
# Node walks under a changed transaction-original state

A message that opens a transaction runs with its own input world as the block environment's
original state (`Benv.beginTransaction`: `origState := state`).  When that world is not a
closed term (it is the settled world of an earlier message), the kernel cannot evaluate the
`SSTORE` charge, which reads the original storage (`getOrigStorVal`).  This module transports
the kernel facts of the walk engine (`Blanc/Lift/NodeWalk.lean`), evaluated under a closed
original state `O`, to the same machine under any original state `O'` with the same storage
at every address (`OrigAgree`), with no new evaluation:

* `pwalkH_withOrig`: a pc-level walk is unchanged.  Only the `SSTORE` arm
  (`sstoreStep_withOrig`) reads the original state, and only its storage;
* `scallPrep_withOrig`, `dcallPrep_withOrig`: a `STATICCALL`/`DELEGATECALL` preparation
  spawns the same frame with its original state changed;
* `frameEnterS_withOrig`, `settle_withOrig`: entering and settling a frame commute with the
  change (no part of entry or settlement reads the original state);
* `scallSpawn_withOrig`, `dcallSpawn_withOrig`: whole spawns, as `NodeWalkFork.lean` does for
  the fork.

Jaune reads `origState` in message execution only through `getOrigAcct` (the `SSTORE`
original value).  Nothing here is contract-specific.
-/

namespace Jaune

/-- The block environment's static part with its original state replaced. -/
def BenvStat.withOrig (s : BenvStat) (O : State) : BenvStat := { s with origState := O }
def Benv.withOrig (b : Benv) (O : State) : Benv := { b with stat := b.stat.withOrig O }
def Sevm.withOrig (s : Sevm) (O : State) : Sevm := { s with benvStat := s.benvStat.withOrig O }
def Evm.withOrig (e : Evm) (O : State) : Evm := { e with sta := e.sta.withOrig O }
def Msg.withOrig (m : Msg) (O : State) : Msg := { m with benv := m.benv.withOrig O }
def Frame.withOrig (f : Frame) (O : State) : Frame :=
  ⟨f.outer.withOrig O, f.inner.withOrig O, f.isCreate⟩

def FrameEntry.withOrig (O : State) : FrameEntry → FrameEntry
  | .done r => .done r
  | .run e => .run (e.withOrig O)

theorem Sevm.withOrig_fork (s : Sevm) (O : State) :
    (s.withOrig O).benvStat.fork = s.benvStat.fork := rfl
theorem Sevm.withOrig_depth (s : Sevm) (O : State) : (s.withOrig O).depth = s.depth := rfl
theorem Sevm.withOrig_isStatic (s : Sevm) (O : State) :
    (s.withOrig O).isStatic = s.isStatic := rfl
theorem Sevm.withOrig_currentTarget (s : Sevm) (O : State) :
    (s.withOrig O).currentTarget = s.currentTarget := rfl

end Jaune

namespace Blanc.Lift.NodeWalk

open Jaune Blanc.Lift Blanc.Lift.Witness

/-- Two original states holding the same storage at every address. -/
def OrigAgree (O O' : State) : Prop := ∀ a k, (O.get a).stor.get k = (O'.get a).stor.get k

theorem OrigAgree.symm {O O' : State} (h : OrigAgree O O') : OrigAgree O' O :=
  fun a k => (h a k).symm

/-- A call preparation with its frame's original state changed. -/
def _root_.Blanc.Lift.Witness.CallPrep.withOrig (cp : CallPrep) (O : State) : CallPrep :=
  { cp with f := cp.f.withOrig O }

variable {s : Sevm} {O : State}

theorem Frame.ofCall_withOrig (m : Msg) : Frame.ofCall (m.withOrig O) = (Frame.ofCall m).withOrig O :=
  rfl

theorem sevm_withOrig_self (s : Sevm) : s.withOrig s.benvStat.origState = s := rfl

/-! ## One step -/

theorem sstoreStep_withOrig (hO : OrigAgree O s.benvStat.origState) (c : Cfg) (k : SFunc) :
    sstoreStep (s.withOrig O) c k = sstoreStep s c k := by
  have h : ∀ a key, getOrigStorVal (s.withOrig O) a key = getOrigStorVal s a key :=
    fun a key => hO a key
  unfold sstoreStep
  simp only [h]
  rfl

theorem ninst_step_reg_withOrig (pc : Nat) (d : Devm) {r : Rinst} (hr : r ≠ .sstore) :
    Ninst.step ⟨pc, s.withOrig O, d⟩ (.reg r) = Ninst.step ⟨pc, s, d⟩ (.reg r) := by
  cases r <;> first | exact absurd rfl hr | rfl

theorem linst_run_withOrig (d : Devm) (l : Linst) :
    Linst.run (s.withOrig O) d l = Linst.run s d l := by
  cases l <;> rfl

/-- One witness-engine step at a non-frame-entering instruction is unchanged. -/
theorem wstep_next_withOrig (hO : OrigAgree O s.benvStat.origState) (fs : List SFunc) (c : PCfg)
    (n : Ninst) (k : SFunc) (hn : ∀ x, n ≠ .exec x) :
    wstep fs (s.withOrig O) (c.cfg (.next n k)) = wstep fs s (c.cfg (.next n k)) := by
  cases n with
  | exec x => exact absurd rfl (hn x)
  | push xs h => rfl
  | dupn _ => rfl
  | swapn _ => rfl
  | exchange _ => rfl
  | reg r =>
    by_cases hs : r = .sstore
    · subst hs
      simp only [PCfg.cfg, wstep, sstoreStep_withOrig hO]
    · cases r <;> first
        | exact absurd rfl hs
        | rfl
        | simp only [PCfg.cfg, wstep, ninst_step_reg_withOrig _ _ hs]

/-- **One walk step is unchanged** when the original state keeps every original storage
value. -/
theorem pstepH_withOrig (hO : OrigAgree O s.benvStat.origState) (pol : HashPol) {code : ByteArray}
    {dd : Nat} (T : CodeTries code dd) (c : PCfg) :
    pstepH pol T (s.withOrig O) c = pstepH pol T s c := by
  unfold pstepH
  cases decodeT dd T.bytes c.pc with
  | none => rfl
  | some i =>
    cases i with
    | next n =>
      cases n with
      | exec x => rfl
      | reg r =>
        by_cases hsb : r = .selfbalance
        · subst hsb; rfl
        · by_cases hrd : r = .returndatacopy
          · subst hrd
            simp only [ninst_step_reg_withOrig _ _ (by decide : Rinst.returndatacopy ≠ .sstore)]
          · have hw := wstep_next_withOrig hO [] c (.reg r) (.last .stop) (by simp only [ne_eq,
              reduceCtorEq, not_false_eq_true, implies_true])
            cases r <;> first
              | exact absurd rfl hsb
              | exact absurd rfl hrd
              | simp only [hw]
      | push xs h =>
        simp only [wstep_next_withOrig hO [] c (.push xs h) (.last .stop) (by simp only [ne_eq,
          reduceCtorEq, not_false_eq_true, implies_true])]
      | dupn i => simp only [wstep_next_withOrig hO [] c (.dupn i) (.last .stop) (by simp only
        [ne_eq, reduceCtorEq, not_false_eq_true, implies_true])]
      | swapn i => simp only [wstep_next_withOrig hO [] c (.swapn i) (.last .stop) (by simp only
        [ne_eq, reduceCtorEq, not_false_eq_true, implies_true])]
      | exchange i =>
        simp only [wstep_next_withOrig hO [] c (.exchange i) (.last .stop) (by simp only [ne_eq,
          reduceCtorEq, not_false_eq_true, implies_true])]
    | jump j => rfl
    | last l =>
      cases l with
      | selfdestruct => rfl
      | _ => simp only [linst_run_withOrig]

/-- **A walk is unchanged under an original state with the same storage.** -/
theorem pwalkH_withOrig (hO : OrigAgree O s.benvStat.origState) (pol : HashPol)
    {code : ByteArray} {dd : Nat} (T : CodeTries code dd) (ok : Nat → Bool) :
    ∀ n c, pwalkH pol T (s.withOrig O) ok n c = pwalkH pol T s ok n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [pwalkH, pstepH_withOrig hO, pwalkH_withOrig hO pol T ok n]

/-! ## Spawns and entries -/

theorem scallPrep_withOrig (d : Devm) (adrs : List Adr) (acs : AcctShadow) :
    scallPrep (s.withOrig O) d adrs acs = (scallPrep s d adrs acs).map (·.withOrig O) := by
  unfold scallPrep
  generalize d.stack = st
  rcases st with _ | ⟨gw, _ | ⟨tw, _ | ⟨iiw, _ | ⟨isw, _ | ⟨oiw, _ | ⟨osw, rest⟩⟩⟩⟩⟩⟩ <;> try rfl
  simp only [Sevm.withOrig_fork, Sevm.withOrig_depth]
  by_cases hf : CoveredFork s.benvStat.fork
  · simp only [hf, decide_true, true_and]
    by_cases hd : s.depth = 0
    · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte, Option.map_none]
    · simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
      split
      · rfl
      · split
        · simp only [Option.map_some]
          rfl
        · rfl
  · simp only [hf, decide_false, Bool.false_eq_true, false_and, ↓reduceIte, Option.map_none]

theorem dcallPrep_withOrig (d : Devm) (adrs : List Adr) (acs : AcctShadow) :
    dcallPrep (s.withOrig O) d adrs acs = (dcallPrep s d adrs acs).map (·.withOrig O) := by
  unfold dcallPrep
  generalize d.stack = st
  rcases st with _ | ⟨gw, _ | ⟨cw, _ | ⟨iiw, _ | ⟨isw, _ | ⟨oiw, _ | ⟨osw, rest⟩⟩⟩⟩⟩⟩ <;> try rfl
  simp only [Sevm.withOrig_fork, Sevm.withOrig_depth]
  by_cases hf : CoveredFork s.benvStat.fork
  · simp only [hf, decide_true, true_and]
    by_cases hd : s.depth = 0
    · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte, Option.map_none]
    · simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
      split
      · rfl
      · split
        · simp only [Option.map_some]
          rfl
        · rfl
  · simp only [hf, decide_false, Bool.false_eq_true, false_and, ↓reduceIte, Option.map_none]

theorem benvAfterTransferS_withOrig (m : Msg) (acs : AcctShadow) :
    benvAfterTransferS (m.withOrig O) acs = (benvAfterTransferS m acs).map (·.withOrig O) := by
  unfold benvAfterTransferS
  by_cases h : m.shouldTransferValue = true
  · have h' : (m.withOrig O).shouldTransferValue = true := h
    simp only [h, h', ↓reduceIte]
    by_cases hb : (lookupA acs m.caller).bal < m.value
    · have hb' : (lookupA acs (m.withOrig O).caller).bal < (m.withOrig O).value := hb
      simp only [hb, hb', ↓reduceIte]
      rfl
    · have hb' : ¬ (lookupA acs (m.withOrig O).caller).bal < (m.withOrig O).value := hb
      simp only [hb, hb', ↓reduceIte]
      rfl
  · have h' : ¬ (m.withOrig O).shouldTransferValue = true := h
    simp only [h, h', ↓reduceIte]
    rfl

theorem executePrecomp_withOrig (e : Evm) (adr : Adr) :
    executePrecomp (e.withOrig O) adr = executePrecomp e adr := by
  have hrun : precompileRun (e.withOrig O) adr = precompileRun e adr := by
    unfold precompileRun
    split <;> rfl
  unfold executePrecomp
  rw [hrun]
  rfl

theorem settle_withOrig (f : Frame) (raw : Execution) : (f.withOrig O).settle raw = f.settle raw :=
  rfl

theorem initEvm_withOrig (m : Msg) : initEvm (m.withOrig O) = (initEvm m).withOrig O := rfl

theorem executeCode_enter_withOrig (m : Msg) :
    executeCode.enter (m.withOrig O) = (executeCode.enter m).map (·.withOrig O) id := by
  unfold executeCode.enter
  have hc : (m.withOrig O).codeAddress = m.codeAddress := rfl
  have hd : (m.withOrig O).disablePrecompiles = m.disablePrecompiles := rfl
  have hr : (m.withOrig O).benv.stat.rules = m.benv.stat.rules := rfl
  simp only [initEvm_withOrig, hc, hd, hr]
  cases m.codeAddress with
  | none => rfl
  | some adr =>
    by_cases hp : (!m.disablePrecompiles && decide (m.benv.stat.rules.isPrecomp adr)) = true
    · simp only [hp, ↓reduceIte, Sum.map_inr, id, executePrecomp_withOrig]
    · simp only [hp, ↓reduceIte, Bool.false_eq_true, Sum.map_inl]

/-- Frame entry through any value-transfer function that commutes with the original-state
change: the shape shared by `Frame.enter` and the witness engine's shadow entry. -/
theorem enterVia_withOrig {T : Msg → Except (EvmError × State × AdrSet × Tra) Benv} {f : Frame}
    (hT : T (f.inner.withOrig O) = (T f.inner).map (·.withOrig O)) :
    (match T (f.inner.withOrig O) with
      | .error e => FrameEntry.done ((f.withOrig O).settleMsg (.error e))
      | .ok benv =>
        match executeCode.enter ((f.inner.withOrig O).withBenv benv) with
        | .inl evm => .run evm
        | .inr raw => .done ((f.withOrig O).settle raw)) =
    (match T f.inner with
      | .error e => FrameEntry.done (f.settleMsg (.error e))
      | .ok benv =>
        match executeCode.enter (f.inner.withBenv benv) with
        | .inl evm => .run evm
        | .inr raw => .done (f.settle raw)).withOrig O := by
  rw [hT]
  cases T f.inner with
  | error e => rfl
  | ok benv =>
    show (match executeCode.enter ((f.inner.withBenv benv).withOrig O) with
      | .inl evm => FrameEntry.run evm
      | .inr raw => .done ((f.withOrig O).settle raw)) = _
    rw [executeCode_enter_withOrig]
    rcases he : executeCode.enter (f.inner.withBenv benv) with e | raw <;>
      simp only [he, Sum.map_inl, Sum.map_inr, id, FrameEntry.withOrig, settle_withOrig]

/-- **The shadow frame entry commutes with the original-state change.** -/
theorem frameEnterS_withOrig (f : Frame) (acs : AcctShadow) :
    frameEnterS (f.withOrig O) acs = (frameEnterS f acs).withOrig O :=
  enterVia_withOrig (T := (benvAfterTransferS · acs)) (benvAfterTransferS_withOrig _ _)

theorem benvAfterTransferB_withOrig (m : Msg) :
    benvAfterTransferB (m.withOrig O) = (benvAfterTransferB m).map (·.withOrig O) := by
  unfold benvAfterTransferB
  have h1 : (m.withOrig O).shouldTransferValue = m.shouldTransferValue := rfl
  have h2 : (m.withOrig O).benv.state = m.benv.state := rfl
  have h3 : (m.withOrig O).caller = m.caller := rfl
  have h4 : (m.withOrig O).value = m.value := rfl
  simp only [h1, h2, h3, h4]
  split
  · split <;> rfl
  · rfl

/-- **Root frame entry commutes with the original-state change.** -/
theorem frame_enter_withOrig (f : Frame) : (f.withOrig O).enter = f.enter.withOrig O := by
  rw [frame_enter_eq_B, frame_enter_eq_B]
  exact enterVia_withOrig (T := benvAfterTransferB) (benvAfterTransferB_withOrig _)

/-- **A `STATICCALL` spawn transports to a changed original state**: the preparation and the
entry of the prepared frame (run or synchronous). -/
theorem scallSpawn_withOrig {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep}
    {r : FrameEntry} (hp : scallPrep s d adrs acs = some cp) (he : frameEnterS cp.f acs = r) :
    scallPrep (s.withOrig O) d adrs acs = some (cp.withOrig O) ∧
      frameEnterS (cp.withOrig O).f acs = r.withOrig O := by
  refine ⟨by rw [scallPrep_withOrig, hp]; rfl, ?_⟩
  show frameEnterS (cp.f.withOrig O) acs = _
  rw [frameEnterS_withOrig, he]

/-- **A `DELEGATECALL` spawn transports to a changed original state.** -/
theorem dcallSpawn_withOrig {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep}
    {r : FrameEntry} (hp : dcallPrep s d adrs acs = some cp) (he : frameEnterS cp.f acs = r) :
    dcallPrep (s.withOrig O) d adrs acs = some (cp.withOrig O) ∧
      frameEnterS (cp.withOrig O).f acs = r.withOrig O := by
  refine ⟨by rw [dcallPrep_withOrig, hp]; rfl, ?_⟩
  show frameEnterS (cp.f.withOrig O) acs = _
  rw [frameEnterS_withOrig, he]

/-- A child's start configuration does not see the original state. -/
theorem childCfg_withOrig (cevm : Evm) (f : Frame) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow) :
    childCfg (cevm.withOrig O) (f.withOrig O) keys adrs stor acs =
      childCfg cevm f keys adrs stor acs := rfl

theorem callPrep_withOrig (c : Cfg) :
    callPrep (s.withOrig O) c = (callPrep s c).map (·.withOrig O) := by
  unfold callPrep
  generalize c.devm.stack = st
  rcases st with _ | ⟨gw, _ | ⟨cw, _ | ⟨vw, _ | ⟨iiw, _ | ⟨isw, _ | ⟨oiw, _ | ⟨osw, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    try rfl
  simp only [Sevm.withOrig_fork, Sevm.withOrig_depth, Sevm.withOrig_isStatic,
    Sevm.withOrig_currentTarget]
  by_cases hf : CoveredFork s.benvStat.fork
  · simp only [hf, decide_true, true_and]
    by_cases hd : s.depth = 0
    · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte, Option.map_none]
    · simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
      split
      · rfl
      · split
        · split
          · simp only [Option.map_some]
            rfl
          · rfl
        · simp only [apply_ite (Option.map (fun x : CallPrep => x.withOrig O)), Option.map_some,
            Option.map_none]
          exact if_congr Iff.rfl rfl rfl
  · simp only [hf, decide_false, Bool.false_eq_true, false_and, ↓reduceIte, Option.map_none]

end Blanc.Lift.NodeWalk

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift Blanc.Lift.NodeWalk

variable {s : Sevm} {O : State}

/-! ## The certificate interpreter -/

theorem callStep_withOrig (c : Cfg) (k : SFunc) : callStep (s.withOrig O) c k = callStep s c k := by
  unfold callStep
  rw [callPrep_withOrig]
  cases hp : callPrep s c with
  | none => rfl
  | some cp =>
    simp only [Option.map_some]
    have hfe : frameEnterS (cp.withOrig O).f c.acs = (frameEnterS cp.f c.acs).withOrig O :=
      frameEnterS_withOrig cp.f c.acs
    rw [hfe]
    cases frameEnterS cp.f c.acs with
    | run e => rfl
    | done r => rfl

theorem sstoreStep_withOrig' (hO : OrigAgree O s.benvStat.origState) (c : Cfg) (k : SFunc) :
    sstoreStep (s.withOrig O) c k = sstoreStep s c k :=
  sstoreStep_withOrig hO c k

/-- **One interpreter step is unchanged** under an original state with the same storage. -/
theorem wstep_withOrig (hO : OrigAgree O s.benvStat.origState) (fs : List SFunc) (c : Cfg) :
    wstep fs (s.withOrig O) c = wstep fs s c := by
  rcases c with ⟨d, f, K, keys, adrs, stor, acs⟩
  cases f with
  | dest _ => rfl
  | jump _ => rfl
  | branch _ _ => rfl
  | branchTo _ _ => rfl
  | callNext _ _ => rfl
  | ret => rfl
  | undefined => rfl
  | pcAt p k =>
    simp only [wstep, ninst_step_reg_withOrig p d (by decide : Rinst.pc ≠ .sstore)]
  | last l =>
    cases l <;> simp only [wstep, linst_run_withOrig]
  | next n k =>
    cases n with
    | push xs h => rfl
    | dupn _ => rfl
    | swapn _ => rfl
    | exchange _ => rfl
    | exec x =>
      cases x <;> simp only [wstep, callStep_withOrig, ninstAccKeeps, Bool.false_eq_true, ↓reduceIte]
    | reg r =>
      by_cases hs : r = .sstore
      · subst hs; simp only [wstep, sstoreStep_withOrig hO]
      · cases r <;> first
          | exact absurd rfl hs
          | rfl
          | simp only [wstep, ninst_step_reg_withOrig _ _ hs]

/-- **A certificate run is unchanged** under an original state with the same storage. -/
theorem wrun_withOrig (hO : OrigAgree O s.benvStat.origState) (fs : List SFunc) :
    ∀ (n : Nat) (c : Cfg), wrun fs (s.withOrig O) n c = wrun fs s n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [wrun, wstep_withOrig hO, wrun_withOrig hO fs n]

theorem childStart_withOrig (c : Cfg) (f0 : SFunc) :
    childStart (s.withOrig O) c f0 = (childStart s c f0).map (fun p => (p.1.withOrig O, p.2)) := by
  unfold childStart
  rw [callPrep_withOrig]
  cases hp : callPrep s c with
  | none => rfl
  | some cp =>
    simp only [Option.map_some]
    have hfe : frameEnterS (cp.withOrig O).f c.acs = (frameEnterS cp.f c.acs).withOrig O :=
      frameEnterS_withOrig cp.f c.acs
    rw [hfe]
    have hN' : frameEntryForkFree (cp.withOrig O).f = frameEntryForkFree cp.f := rfl
    cases frameEnterS cp.f c.acs with
    | run e =>
      simp only [FrameEntry.withOrig, hN']
      split <;> rfl
    | done r => rfl

/-- **A code child's run is unchanged** under an original state with the same storage (the
child inherits the caller's block environment). -/
theorem childRun_withOrig (hO : OrigAgree O s.benvStat.origState) (fs : List SFunc)
    (code : ByteArray) (n : Nat) (c : Cfg) :
    childRun fs code (s.withOrig O) n c = childRun fs code s n c := by
  unfold childRun
  cases fs[0]? with
  | none => rfl
  | some f0 =>
    dsimp only
    rw [childStart_withOrig]
    cases hcs : childStart s c f0 with
    | none => rfl
    | some p =>
      obtain ⟨e, cc⟩ := p
      have hst := childStart_stat hcs
      have hO' : OrigAgree O e.sta.benvStat.origState := by rw [hst]; exact hO
      simp only [Option.map_some]
      show (if decide (CoveredFork e.sta.benvStat.fork) ∧ e.sta.code.data.toList = code.data.toList then
          wrun fs (e.sta.withOrig O) n cc else .stuck) = _
      split
      · exact wrun_withOrig hO' fs n cc
      · rfl

/-- The configuration after a code-child `CALL` is unchanged under a changed original state. -/
theorem callResume_withOrig (c : Cfg) (child : Devm) (ck : List (Adr × B256)) (ca : List Adr)
    (cs : StorShadow) (cacc : AcctShadow) :
    callResume (s.withOrig O) c child ck ca cs cacc = callResume s c child ck ca cs cacc := by
  unfold callResume
  cases c.f with
  | next n k =>
    cases n with
    | exec x =>
      cases x with
      | call =>
        simp only
        rw [callPrep_withOrig]
        cases callPrep s c with
        | none => rfl
        | some cp =>
          simp only [Option.map_some]
          have hfe : frameEnterS (cp.withOrig O).f c.acs = (frameEnterS cp.f c.acs).withOrig O :=
            frameEnterS_withOrig cp.f c.acs
          rw [hfe]
          cases frameEnterS cp.f c.acs with
          | run e => rfl
          | done r => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

end Blanc.Lift.Witness
