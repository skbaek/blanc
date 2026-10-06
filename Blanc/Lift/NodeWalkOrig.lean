import Blanc.Lift.NodeWalk
import Blanc.Lift.NodeWalkFork

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

`callSpawn_withOrig` covers `CALL`.  The `*_re` lemmas compose the change with the fork change
of `Blanc/Lift/NodeWalkFork.lean`: kernel facts evaluated at Prague under a cheap closed original
state `O` (built from storage shadows) transport to the real machine under any covered fork and
under the real original state (a settled world whose evaluation would re-run earlier messages),
given only that the two agree on storage (`OrigAgree`, itself proved from shadow agreement, not
by evaluation).
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
  have e1 : (s.withOrig O).benvStat.fork = s.benvStat.fork := rfl
  have e2 : (s.withOrig O).depth = s.depth := rfl
  have e3 : (s.withOrig O).isStatic = s.isStatic := rfl
  have e4 : (s.withOrig O).currentTarget = s.currentTarget := rfl
  simp only [e1, e2, e3, e4]
  by_cases h : decide (CoveredFork s.benvStat.fork) = true ∧ s.depth ≠ 0
  · rw [if_pos h, if_pos h]
    split
    · rename_i heq; simp only [heq, Option.map_none]
    · split_ifs <;> rfl
  · rw [if_neg h, if_neg h]; rfl

theorem dcallPrep_withOrig (d : Devm) (adrs : List Adr) (acs : AcctShadow) :
    dcallPrep (s.withOrig O) d adrs acs = (dcallPrep s d adrs acs).map (·.withOrig O) := by
  unfold dcallPrep
  generalize d.stack = st
  rcases st with _ | ⟨gw, _ | ⟨tw, _ | ⟨iiw, _ | ⟨isw, _ | ⟨oiw, _ | ⟨osw, rest⟩⟩⟩⟩⟩⟩ <;> try rfl
  have e1 : (s.withOrig O).benvStat.fork = s.benvStat.fork := rfl
  have e2 : (s.withOrig O).depth = s.depth := rfl
  have e3 : (s.withOrig O).isStatic = s.isStatic := rfl
  have e4 : (s.withOrig O).currentTarget = s.currentTarget := rfl
  simp only [e1, e2, e3, e4]
  by_cases h : decide (CoveredFork s.benvStat.fork) = true ∧ s.depth ≠ 0
  · rw [if_pos h, if_pos h]
    split
    · rename_i heq; simp only [heq, Option.map_none]
    · split_ifs <;> rfl
  · rw [if_neg h, if_neg h]; rfl

theorem callPrep_withOrig (c : Cfg) :
    callPrep (s.withOrig O) c = (callPrep s c).map (·.withOrig O) := by
  unfold callPrep
  generalize c.devm.stack = st
  rcases st with _ | ⟨gw, _ | ⟨cw, _ | ⟨vw, _ | ⟨iiw, _ | ⟨isw, _ | ⟨oiw, _ | ⟨osw, rest⟩⟩⟩⟩⟩⟩⟩ <;> try rfl
  have e1 : (s.withOrig O).benvStat.fork = s.benvStat.fork := rfl
  have e2 : (s.withOrig O).depth = s.depth := rfl
  have e3 : (s.withOrig O).isStatic = s.isStatic := rfl
  have e4 : (s.withOrig O).currentTarget = s.currentTarget := rfl
  simp only [e1, e2, e3, e4]
  by_cases h : decide (CoveredFork s.benvStat.fork) = true ∧ s.depth ≠ 0
  · rw [if_pos h, if_pos h]
    split
    · rename_i heq; simp only [heq, Option.map_none]
    · split_ifs <;> rfl
  · rw [if_neg h, if_neg h]; rfl

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

theorem settle_withOrig (f : Frame) (raw : Execution) : (f.withOrig O).settle raw = f.settle raw :=
  rfl

/-- Entering code that is not a precompile commutes with the original-state change. -/
theorem executeCode_enter_withOrig {m : Msg} {e : Evm} (h : executeCode.enter m = .inl e) :
    executeCode.enter (m.withOrig O) = .inl (e.withOrig O) := by
  unfold executeCode.enter at h ⊢
  have hc : (m.withOrig O).codeAddress = m.codeAddress := rfl
  have hd : (m.withOrig O).disablePrecompiles = m.disablePrecompiles := rfl
  have hr : (m.withOrig O).benv.stat.rules = m.benv.stat.rules := rfl
  have hi : initEvm (m.withOrig O) = (initEvm m).withOrig O := rfl
  simp only [hc, hd, hr, hi]
  revert h
  cases m.codeAddress with
  | none => intro h; cases h; rfl
  | some adr =>
    dsimp only
    split
    · intro h; cases h
    · intro h; cases h; rfl

/-- **A shadow frame entry that runs code commutes with the original-state change.** -/
theorem frameEnterS_withOrig {f : Frame} {acs : AcctShadow} {e : Evm}
    (h : frameEnterS f acs = .run e) : frameEnterS (f.withOrig O) acs = .run (e.withOrig O) := by
  unfold frameEnterS at h ⊢
  have hT : benvAfterTransferS (f.withOrig O).inner acs =
      (benvAfterTransferS f.inner acs).map (·.withOrig O) := benvAfterTransferS_withOrig _ _
  rw [hT]
  revert h
  cases benvAfterTransferS f.inner acs with
  | error x => intro h; cases h
  | ok benv =>
    dsimp only [Except.map]
    have hm : (f.withOrig O).inner.withBenv (benv.withOrig O) =
        (f.inner.withBenv benv).withOrig O := rfl
    rw [hm]
    cases he : executeCode.enter (f.inner.withBenv benv) with
    | inl evm =>
      intro h; cases h
      rw [executeCode_enter_withOrig he]
    | inr raw => intro h; cases h

theorem benvAfterTransferB_withOrig (m : Msg) :
    benvAfterTransferB (m.withOrig O) = (benvAfterTransferB m).map (·.withOrig O) := by
  unfold benvAfterTransferB
  by_cases h : m.shouldTransferValue = true
  · have h' : (m.withOrig O).shouldTransferValue = true := h
    simp only [h, h', ↓reduceIte]
    by_cases hb : m.benv.state.bal m.caller < m.value
    · have hb' : (m.withOrig O).benv.state.bal (m.withOrig O).caller < (m.withOrig O).value := hb
      simp only [hb, hb', ↓reduceIte]
      rfl
    · have hb' : ¬ (m.withOrig O).benv.state.bal (m.withOrig O).caller < (m.withOrig O).value :=
        hb
      simp only [hb, hb', ↓reduceIte]
      rfl
  · have h' : ¬ (m.withOrig O).shouldTransferValue = true := h
    simp only [h, h', ↓reduceIte]
    rfl

/-- **A root frame entry that runs code commutes with the original-state change.** -/
theorem frame_enter_withOrig {f : Frame} {e : Evm} (h : f.enter = .run e) :
    (f.withOrig O).enter = .run (e.withOrig O) := by
  rw [frame_enter_eq_B] at h ⊢
  unfold frameEnterB at h ⊢
  have hT : benvAfterTransferB (f.withOrig O).inner =
      (benvAfterTransferB f.inner).map (·.withOrig O) := benvAfterTransferB_withOrig _
  rw [hT]
  revert h
  cases benvAfterTransferB f.inner with
  | error x => intro h; cases h
  | ok benv =>
    dsimp only [Except.map]
    have hm : (f.withOrig O).inner.withBenv (benv.withOrig O) =
        (f.inner.withBenv benv).withOrig O := rfl
    rw [hm]
    cases he : executeCode.enter (f.inner.withBenv benv) with
    | inl evm =>
      intro h; cases h
      rw [executeCode_enter_withOrig he]
    | inr raw => intro h; cases h

/-- **A `STATICCALL` spawn transports to a changed original state**: the preparation and the
entry of the prepared frame. -/
theorem scallSpawn_withOrig {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep}
    {e : Evm} (hp : scallPrep s d adrs acs = some cp) (he : frameEnterS cp.f acs = .run e) :
    scallPrep (s.withOrig O) d adrs acs = some (cp.withOrig O) ∧
      frameEnterS (cp.withOrig O).f acs = .run (e.withOrig O) :=
  ⟨by rw [scallPrep_withOrig, hp]; rfl, frameEnterS_withOrig he⟩

/-- **A `DELEGATECALL` spawn transports to a changed original state.** -/
theorem dcallSpawn_withOrig {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep}
    {e : Evm} (hp : dcallPrep s d adrs acs = some cp) (he : frameEnterS cp.f acs = .run e) :
    dcallPrep (s.withOrig O) d adrs acs = some (cp.withOrig O) ∧
      frameEnterS (cp.withOrig O).f acs = .run (e.withOrig O) :=
  ⟨by rw [dcallPrep_withOrig, hp]; rfl, frameEnterS_withOrig he⟩

/-- A child's start configuration does not see the original state. -/
theorem childCfg_withOrig (cevm : Evm) (f : Frame) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow) :
    childCfg (cevm.withOrig O) (f.withOrig O) keys adrs stor acs =
      childCfg cevm f keys adrs stor acs := rfl


theorem callPrepP_withOrig (c : PCfg) :
    callPrepP (s.withOrig O) c = (callPrepP s c).map (·.withOrig O) :=
  callPrep_withOrig _

/-- **A `CALL` spawn transports to a changed original state.** -/
theorem callSpawn_withOrig {c : PCfg} {cp : CallPrep} {e : Evm}
    (hp : callPrepP s c = some cp) (he : frameEnterS cp.f c.acs = .run e) :
    callPrepP (s.withOrig O) c = some (cp.withOrig O) ∧
      frameEnterS (cp.withOrig O).f c.acs = .run (e.withOrig O) :=
  ⟨by rw [callPrepP_withOrig, hp]; rfl, frameEnterS_withOrig he⟩

/-! ## A cheap closed original state with given storage -/

/-- The world holding exactly the storage `l` reads (newest write first) and nothing else: a
closed original state the kernel evaluates cheaply. -/
def origOf (l : StorShadow) : State := stateFoldStor default l.reverse

theorem foldl_cons_eq (l : StorShadow) :
    ∀ acc : StorShadow, l.foldl (fun s w => w :: s) acc = l.reverse ++ acc := by
  induction l with
  | nil => intro acc; rfl
  | cons e l ih => intro acc; simp only [List.foldl_cons, ih, List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append]

theorem storOf_origOf (l : StorShadow) (a : Adr) (k : B256) :
    storOf (origOf l) a k = lookupS l a k := by
  have h := storOf_stateFoldStor l.reverse (st := default) storOf_empty a k
  rw [origOf, h]
  unfold storShadowOf
  rw [foldl_cons_eq, List.reverse_reverse, List.append_nil]

/-- A world whose storage the shadow `l` describes agrees in storage with `origOf l`. -/
theorem origAgree_origOf {W : State} {l : StorShadow} (h : ∀ a k, storOf W a k = lookupS l a k) :
    OrigAgree W (origOf l) := fun a k => (h a k).trans (storOf_origOf l a k).symm

/-! ## Fork and original state together

`ReOK O s`: what transporting the kernel facts of a walk over the static machine `s` to
`(s.withFork g).withOrig O` needs: a covered fork, no excess blob gas (`pwalkH_withFork`), and
an original state `O` with `s`'s original storage. -/

open Blanc.ForkUniform

/-- The kernel machine `s` transports to any covered fork and to the original state `O`. -/
def ReOK (O : State) (s : Sevm) : Prop :=
  CoveredFork s.benvStat.fork ∧ s.benvStat.excessBlobGas = 0 ∧ OrigAgree O s.benvStat.origState

theorem ReOK.of_stat {O : State} {s t : Sevm} (h : t.benvStat = s.benvStat) (hs : ReOK O s) :
    ReOK O t := by
  rw [ReOK, h]; exact hs

/-- **A walk transports** to any covered fork and an agreeing original state. -/
theorem walk_re {g : Fork} (hs : ReOK O s) (hg : CoveredFork g) (pol : HashPol)
    {code : ByteArray} {dd : Nat} (T : CodeTries code dd) (ok : Nat → Bool) (n : Nat)
    (c : PCfg) : pwalkH pol T ((s.withFork g).withOrig O) ok n c = pwalkH pol T s ok n c :=
  (pwalkH_withOrig (s := s.withFork g) hs.2.2 pol T ok n c).trans
    (pwalkH_withFork hs.1 hg hs.2.1 pol T ok n c)

/-- A call preparation with its fork and original state changed. -/
def _root_.Blanc.Lift.Witness.CallPrep.re (cp : CallPrep) (g : Fork) (O : State) : CallPrep :=
  (cp.withFork g).withOrig O

/-- A machine with its fork and original state changed. -/
def _root_.Jaune.Evm.re (e : Evm) (g : Fork) (O : State) : Evm := (e.withFork g).withOrig O

/-- **A `STATICCALL` spawn transports** to any covered fork and an agreeing original state. -/
theorem scallSpawn_re {g : Fork} (hs : ReOK O s) (hg : CoveredFork g) {d : Devm}
    {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep} {e : Evm}
    (hp : scallPrep s d adrs acs = some cp) (hN : cp.f.PrecompNeutral)
    (he : frameEnterS cp.f acs = .run e) :
    scallPrep ((s.withFork g).withOrig O) d adrs acs = some (cp.re g O) ∧
      frameEnterS (cp.re g O).f acs = .run (e.re g O) := by
  obtain ⟨h1, h2⟩ := scallSpawn_withFork hs.1 hg hp hN he
  exact scallSpawn_withOrig h1 h2

/-- **A `CALL` spawn transports** to any covered fork and an agreeing original state. -/
theorem callSpawn_re {g : Fork} (hs : ReOK O s) (hg : CoveredFork g) {c : PCfg}
    {cp : CallPrep} {e : Evm} (hp : callPrepP s c = some cp) (hN : cp.f.PrecompNeutral)
    (he : frameEnterS cp.f c.acs = .run e) :
    callPrepP ((s.withFork g).withOrig O) c = some (cp.re g O) ∧
      frameEnterS (cp.re g O).f c.acs = .run (e.re g O) := by
  obtain ⟨h1, h2⟩ := callSpawn_withFork hs.1 hg hp hN he
  exact callSpawn_withOrig h1 h2

/-- **A `DELEGATECALL` spawn transports** to any covered fork and an agreeing original state. -/
theorem dcallSpawn_re {g : Fork} (hs : ReOK O s) (hg : CoveredFork g) {d : Devm}
    {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep} {e : Evm}
    (hp : dcallPrep s d adrs acs = some cp) (hN : cp.f.PrecompNeutral)
    (he : frameEnterS cp.f acs = .run e) :
    dcallPrep ((s.withFork g).withOrig O) d adrs acs = some (cp.re g O) ∧
      frameEnterS (cp.re g O).f acs = .run (e.re g O) := by
  obtain ⟨h1, h2⟩ := dcallSpawn_withFork hs.1 hg hp hN he
  exact dcallSpawn_withOrig h1 h2

/-- A spawned child's start configuration does not see the fork or the original state.  Rewrite
a transported spawn's agreement and nodes with `pagree_re`/`nodeAt_re` before handing them to
lemmas stated over the kernel configuration: otherwise the kernel compares a concrete machine
with its transported form by evaluating both. -/
theorem childCfg_re (e : Evm) (cp : CallPrep) (g : Fork) (O : State) (keys : List (Adr × B256))
    (stor : StorShadow) (acs : AcctShadow) :
    childCfg (e.re g O) (cp.re g O).f keys (cp.re g O).adrs stor acs =
      childCfg e cp.f keys cp.adrs stor acs := rfl

theorem pagree_re {e : Evm} {cp : CallPrep} {g : Fork} {keys : List (Adr × B256)}
    {stor : StorShadow} {acs : AcctShadow}
    (h : PAgree (childCfg (e.re g O) (cp.re g O).f keys (cp.re g O).adrs stor acs)) :
    PAgree (childCfg e cp.f keys cp.adrs stor acs) := h

theorem nodeAt_re {s' : Sevm} {e : Evm} {cp : CallPrep} {g : Fork} {keys : List (Adr × B256)}
    {stor : StorShadow} {acs : AcctShadow} {x : Exec.Deriv}
    (h : NodeAt s' (childCfg (e.re g O) (cp.re g O).f keys (cp.re g O).adrs stor acs) x) :
    NodeAt s' (childCfg e cp.f keys cp.adrs stor acs) x := h

/-- Settling a spawned frame ignores both changes. -/
theorem settle_re {g : Fork} (hs : ReOK O s) (hg : CoveredFork g) {cp : CallPrep}
    (hst : cp.f.outer.benv.stat = s.benvStat ∧ cp.f.inner.benv.stat = s.benvStat)
    (raw : Execution) : (cp.re g O).f.settle raw = cp.f.settle raw :=
  (settle_withOrig (cp.f.withFork g) raw).trans (settle_withFork_of_stat hs.1 hg hst raw)

/-- **A root frame entry transports** from the Prague kernel entry: the frame with its fork
changed to any covered fork and its original state changed enters with the transported
machine. -/
theorem frame_enter_re {f : Frame} {e : Evm} {g : Fork} (ho : CoveredFork f.outer.benv.stat.fork)
    (hi : CoveredFork f.inner.benv.stat.fork) (hg : CoveredFork g) (hp : f.PrecompNeutral)
    (he : f.enter = .run e) : ((f.withFork g).withOrig O).enter = .run (e.re g O) := by
  have h1 : (f.withFork g).enter = .run (e.withFork g) := by
    rw [frame_enter_withFork ho hi hg hp, he]; rfl
  exact frame_enter_withOrig h1

end Blanc.Lift.NodeWalk
