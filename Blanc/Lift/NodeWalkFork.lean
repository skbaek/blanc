import Blanc.Lift.NodeWalk
import Blanc.ForkUniform

/-!
# Node walks under any covered fork

The walk engine of `Blanc/Lift/NodeWalk.lean` evaluates concrete runs in the kernel from a
static machine that fixes one fork.  This module transports those kernel facts to the same
machine under any covered fork (`Blanc/ForkUniform.lean`), with no new evaluation:

* `pwalkH_withFork`: a pc-level walk is unchanged.  A walk never runs `CLZ` (it is not an
  `ninstAccKeeps` instruction, so every walk is stuck there under every fork) and never enters
  a frame; `BLOBBASEFEE` is unchanged when the block carries no excess blob gas;
* `scallPrep_withFork`, `callPrepP_withFork`, `dcallPrep_withFork`: a `STATICCALL`, `CALL` or
  `DELEGATECALL` preparation spawns the same frame with its fork changed
  (`*_stat`: the frame carries the caller's block environment);
* `frameEnterS_withFork`: the shadow frame entry commutes with the fork change for a frame
  that does not enter `MODEXP` or `P256VERIFY`;
* `scallSpawn_withFork`, `callSpawn_withFork`, `dcallSpawn_withFork`: a whole spawn (the
  preparation and the entry of its frame) transported from the Prague facts, given a kernel
  fact on the frame's `codeAddress` (`Frame.precompNeutral_of_codeAddress`);
  `settle_withFork_of_stat` is the child's settle;
* `childCfg_withFork`: a child's start configuration is unchanged.

A closed witness built from these facts therefore replays under any covered fork by
rewriting each kernel fact, provided its block has zero excess blob gas and its frames avoid
the two fork-sensitive precompiles.
-/

namespace Blanc.Lift.NodeWalk

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ForkUniform

variable {s : Sevm} {g : Fork}

theorem ninst_step_reg_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (hx : s.benvStat.excessBlobGas = 0) (pc : Nat) (d : Devm) {r : Rinst} (hr : r ≠ .clz) :
    Ninst.step ⟨pc, s.withFork g, d⟩ (.reg r) = Ninst.step ⟨pc, s, d⟩ (.reg r) := by
  show Step.ofExecution _ (Rinst.runCore pc d (s.withFork g) r) =
    Step.ofExecution _ (Rinst.runCore pc d s r)
  rw [rinst_runCore_withFork hf hg pc d r hr (fun _ => hx)]

theorem selfbalanceP_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (c : PCfg) : selfbalanceP (s.withFork g) c = selfbalanceP s c :=
  eq_of_prague (fun s => selfbalanceP s c) hf hg fun _ hg =>
    hg.cases (motive := fun g => selfbalanceP (s.withFork g) c =
      selfbalanceP (s.withFork .prague) c) rfl rfl rfl rfl

theorem sloadStep_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (c : Cfg) (k : SFunc) : sloadStep (s.withFork g) c k = sloadStep s c k :=
  eq_of_prague (fun s => sloadStep s c k) hf hg fun _ hg =>
    hg.cases (motive := fun g => sloadStep (s.withFork g) c k =
      sloadStep (s.withFork .prague) c k) rfl rfl rfl rfl

theorem sstoreStep_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (c : Cfg) (k : SFunc) : sstoreStep (s.withFork g) c k = sstoreStep s c k :=
  eq_of_prague (fun s => sstoreStep s c k) hf hg fun _ hg =>
    hg.cases (motive := fun g => sstoreStep (s.withFork g) c k =
      sstoreStep (s.withFork .prague) c k) rfl rfl rfl rfl

theorem calldatacopyStep_withFork (c : Cfg) (k : SFunc) :
    calldatacopyStep (s.withFork g) c k = calldatacopyStep s c k := rfl

theorem logStep_withFork (n : Fin 5) (c : Cfg) (k : SFunc) :
    logStep (s.withFork g) n c k = logStep s n c k := rfl

/-- One witness-engine step at a non-frame-entering instruction is unchanged. -/
theorem wstep_next_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (hx : s.benvStat.excessBlobGas = 0) (fs : List SFunc) (c : PCfg) (n : Ninst) (k : SFunc)
    (hn : ∀ x, n ≠ .exec x) :
    wstep fs (s.withFork g) (c.cfg (.next n k)) = wstep fs s (c.cfg (.next n k)) := by
  cases n with
  | exec x => exact absurd rfl (hn x)
  | push xs h => rfl
  | dupn _ => rfl
  | swapn _ => rfl
  | exchange _ => rfl
  | reg r =>
    by_cases hc : r = .clz
    · subst hc; rfl
    · cases r <;> first
        | exact absurd rfl hc
        | simp only [PCfg.cfg, wstep, sloadStep_withFork hf hg, sstoreStep_withFork hf hg,
            calldatacopyStep_withFork, logStep_withFork,
            ninst_step_reg_withFork hf hg hx _ _ hc]

/-- One walk step is unchanged. -/
theorem pstepH_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (hx : s.benvStat.excessBlobGas = 0) (pol : HashPol) {code : ByteArray} {dd : Nat}
    (T : CodeTries code dd) (c : PCfg) :
    pstepH pol T (s.withFork g) c = pstepH pol T s c := by
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
        · subst hsb
          simp only [selfbalanceP_withFork hf hg]
        · by_cases hrd : r = .returndatacopy
          · subst hrd
            simp only [ninst_step_reg_withFork hf hg hx _ _ (by decide : Rinst.returndatacopy ≠ .clz)]
          · have hw := wstep_next_withFork hf hg hx [] c (.reg r) (.last .stop) (by simp)
            cases r <;> first
              | exact absurd rfl hsb
              | exact absurd rfl hrd
              | simp only [hw]
      | push xs h =>
        simp only [wstep_next_withFork hf hg hx [] c (.push xs h) (.last .stop) (by simp)]
      | dupn i => simp only [wstep_next_withFork hf hg hx [] c (.dupn i) (.last .stop) (by simp)]
      | swapn i => simp only [wstep_next_withFork hf hg hx [] c (.swapn i) (.last .stop) (by simp)]
      | exchange i =>
        simp only [wstep_next_withFork hf hg hx [] c (.exchange i) (.last .stop) (by simp)]
    | jump j => rfl
    | last l =>
      cases l with
      | selfdestruct => rfl
      | _ => simp only [linst_run_withFork hf hg]

/-- **A walk is unchanged under any covered fork** when the block carries no excess blob gas. -/
theorem pwalkH_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (hx : s.benvStat.excessBlobGas = 0) (pol : HashPol) {code : ByteArray} {dd : Nat}
    (T : CodeTries code dd) (ok : Nat → Bool) :
    ∀ n c, pwalkH pol T (s.withFork g) ok n c = pwalkH pol T s ok n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [pwalkH, pstepH_withFork hf hg hx, pwalkH_withFork hf hg hx pol T ok n]

theorem pwalk_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (hx : s.benvStat.excessBlobGas = 0) {code : ByteArray} {dd : Nat}
    (T : CodeTries code dd) (ok : Nat → Bool) (n : Nat) (c : PCfg) :
    pwalk T (s.withFork g) ok n c = pwalk T s ok n c :=
  pwalkH_withFork hf hg hx .refuse T ok n c

/-! ## Spawns and entries -/

/-- A call preparation with its frame's fork changed. -/
def _root_.Blanc.Lift.Witness.CallPrep.withFork (cp : CallPrep) (g : Fork) : CallPrep := { cp with f := cp.f.withFork g }

theorem scallPrep_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (d : Devm) (adrs : List Adr) (acs : AcctShadow) :
    scallPrep (s.withFork g) d adrs acs = (scallPrep s d adrs acs).map (·.withFork g) := by
  unfold scallPrep
  generalize d.stack = st
  rcases st with _ | ⟨gw, _ | ⟨tw, _ | ⟨iiw, _ | ⟨isw, _ | ⟨oiw, _ | ⟨osw, rest⟩⟩⟩⟩⟩⟩ <;> try rfl
  simp only [Sevm.withFork_fork, Sevm.withFork_depth, hg, hf, decide_true, true_and]
  by_cases hd : s.depth = 0
  · simp [hd]
  · simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
    split
    · rfl
    · split
      · simp only [Option.map_some]
        rfl
      · rfl

/-- A `DELEGATECALL` preparation spawns the same frame with its fork changed. -/
theorem dcallPrep_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (d : Devm) (adrs : List Adr) (acs : AcctShadow) :
    dcallPrep (s.withFork g) d adrs acs = (dcallPrep s d adrs acs).map (·.withFork g) := by
  unfold dcallPrep
  generalize d.stack = st
  rcases st with _ | ⟨gw, _ | ⟨cw, _ | ⟨iiw, _ | ⟨isw, _ | ⟨oiw, _ | ⟨osw, rest⟩⟩⟩⟩⟩⟩ <;> try rfl
  simp only [Sevm.withFork_fork, Sevm.withFork_depth, hg, hf, decide_true, true_and]
  by_cases hd : s.depth = 0
  · simp [hd]
  · simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
    split
    · rfl
    · split
      · simp only [Option.map_some]
        rfl
      · rfl

/-- A `CALL` preparation (with or without value) spawns the same frame with its fork
changed. -/
theorem callPrep_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g) (c : Cfg) :
    callPrep (s.withFork g) c = (callPrep s c).map (·.withFork g) := by
  unfold callPrep
  generalize c.devm.stack = st
  rcases st with _ | ⟨gw, _ | ⟨cw, _ | ⟨vw, _ | ⟨iiw, _ | ⟨isw, _ | ⟨oiw, _ | ⟨osw, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    try rfl
  simp only [Sevm.withFork_fork, Sevm.withFork_depth, hg, hf, decide_true, true_and]
  by_cases hd : s.depth = 0
  · simp [hd]
  · simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
    split
    · rfl
    · split
      · split
        · simp only [Option.map_some]
          rfl
        · rfl
      · simp only [Sevm.withFork_isStatic, Sevm.withFork_currentTarget,
          apply_ite (Option.map (fun x : CallPrep => x.withFork g)), Option.map_some,
          Option.map_none]
        exact if_congr Iff.rfl rfl rfl

theorem callPrepP_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g) (c : PCfg) :
    callPrepP (s.withFork g) c = (callPrepP s c).map (·.withFork g) :=
  callPrep_withFork hf hg _

theorem benvAfterTransferS_withFork (m : Msg) (g : Fork) (acs : AcctShadow) :
    benvAfterTransferS (m.withFork g) acs = (benvAfterTransferS m acs).map (·.withFork g) := by
  unfold benvAfterTransferS
  simp only [Msg.withFork_shouldTransferValue, Msg.withFork_caller, Msg.withFork_value,
    Msg.withFork_currentTarget, Msg.withFork_benv_state]
  by_cases h : m.shouldTransferValue = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true]
  · by_cases hb : (lookupA acs m.caller).bal < m.value <;> simp only [hb, ↓reduceIte] <;> rfl
  · rfl

theorem benvAfterTransferS_stat {m : Msg} {acs : AcctShadow} {b : Benv}
    (h : benvAfterTransferS m acs = .ok b) : b.stat = m.benv.stat := by
  unfold benvAfterTransferS at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h; rfl

/-- **The shadow frame entry commutes with the fork change** between covered forks, for a
frame that does not enter `MODEXP` or `P256VERIFY`. -/
theorem frameEnterS_withFork {f : Frame} (ho : CoveredFork f.outer.benv.stat.fork)
    (hi : CoveredFork f.inner.benv.stat.fork) (hg : CoveredFork g) (hp : f.PrecompNeutral)
    (acs : AcctShadow) :
    frameEnterS (f.withFork g) acs = (frameEnterS f acs).withFork g :=
  enterVia_withFork (T := (benvAfterTransferS · acs)) (benvAfterTransferS_withFork _ _ _)
    (fun _ hb => benvAfterTransferS_stat hb) ho hi hg hp

/-- A child's start configuration does not see the fork. -/
theorem childCfg_withFork (cevm : Evm) (f : Frame) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow) :
    childCfg (cevm.withFork g) (f.withFork g) keys adrs stor acs =
      childCfg cevm f keys adrs stor acs := rfl

/-! ## What a spawned or entered machine inherits -/

/-- A `STATICCALL` preparation's frame carries the caller's block environment. -/
theorem scallPrep_stat {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep}
    (h : scallPrep s d adrs acs = some cp) :
    cp.f.outer.benv.stat = s.benvStat ∧ cp.f.inner.benv.stat = s.benvStat := by
  unfold scallPrep at h
  generalize d.stack = st at h
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only at h
    split at h
    · split at h
      · simp at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl⟩
        · simp at h
    · simp at h

/-- A `DELEGATECALL` preparation's frame carries the caller's block environment. -/
theorem dcallPrep_stat {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep}
    (h : dcallPrep s d adrs acs = some cp) :
    cp.f.outer.benv.stat = s.benvStat ∧ cp.f.inner.benv.stat = s.benvStat := by
  unfold dcallPrep at h
  generalize d.stack = st at h
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only at h
    split at h
    · split at h
      · simp at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl⟩
        · simp at h
    · simp at h

/-- A `CALL` preparation's frame carries the caller's block environment. -/
theorem callPrepP_stat {c : PCfg} {cp : CallPrep} (h : callPrepP s c = some cp) :
    cp.f.outer.benv.stat = s.benvStat ∧ cp.f.inner.benv.stat = s.benvStat := by
  unfold callPrepP callPrep at h
  generalize (c.cfg .undefined).devm.stack = st at h
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only at h
    split at h
    · split at h
      · simp at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            subst h
            exact ⟨rfl, rfl⟩
          · simp at h
        · split at h
          · simp only [Option.some.injEq] at h
            subst h
            exact ⟨rfl, rfl⟩
          · simp at h
    · simp at h

theorem executeCode_enter_stat {m : Msg} {e : Evm} (h : executeCode.enter m = .inl e) :
    e.sta.benvStat = m.benv.stat := by
  unfold executeCode.enter at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl

/-- An entered machine carries its frame's block environment. -/
theorem frameEnterS_stat {f : Frame} {acs : AcctShadow} {e : Evm}
    (h : frameEnterS f acs = .run e) : e.sta.benvStat = f.inner.benv.stat := by
  unfold frameEnterS at h
  split at h
  · cases h
  · rename_i benv hb
    split at h
    · rename_i evm he
      cases h
      exact (executeCode_enter_stat he).trans (benvAfterTransferS_stat hb)
    · cases h

/-! ## A spawn under any covered fork -/

/-- The shadow frame entry of a frame carrying the caller's block environment commutes with
the fork change. -/
theorem frameEnterS_withFork_of_stat {f : Frame} (hf : CoveredFork s.benvStat.fork)
    (hg : CoveredFork g) (hst : f.outer.benv.stat = s.benvStat ∧ f.inner.benv.stat = s.benvStat)
    (hp : f.PrecompNeutral) (acs : AcctShadow) :
    frameEnterS (f.withFork g) acs = (frameEnterS f acs).withFork g :=
  frameEnterS_withFork (by rw [hst.1]; exact hf) (by rw [hst.2]; exact hf) hg hp acs

/-- Settling a frame carrying the caller's block environment ignores the fork change. -/
theorem settle_withFork_of_stat {f : Frame} (hf : CoveredFork s.benvStat.fork)
    (hg : CoveredFork g) (hst : f.outer.benv.stat = s.benvStat ∧ f.inner.benv.stat = s.benvStat)
    (raw : Execution) : (f.withFork g).settle raw = f.settle raw :=
  settle_withFork (by rw [hst.1]; exact hf) (by rw [hst.2]; exact hf) hg raw

/-- **A `STATICCALL` spawn transports to any covered fork**: the preparation and the entry of
the prepared frame, with only the fork changed. -/
theorem scallSpawn_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep} {e : Evm}
    (hp : scallPrep s d adrs acs = some cp) (hN : cp.f.PrecompNeutral)
    (he : frameEnterS cp.f acs = .run e) :
    scallPrep (s.withFork g) d adrs acs = some (cp.withFork g) ∧
      frameEnterS (cp.withFork g).f acs = .run (e.withFork g) := by
  refine ⟨by rw [scallPrep_withFork hf hg, hp]; rfl, ?_⟩
  show frameEnterS (cp.f.withFork g) acs = _
  rw [frameEnterS_withFork_of_stat hf hg (scallPrep_stat hp) hN, he]; rfl

/-- **A `CALL` spawn transports to any covered fork** (`scallSpawn_withFork` for `callPrepP`). -/
theorem callSpawn_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    {c : PCfg} {cp : CallPrep} {e : Evm}
    (hp : callPrepP s c = some cp) (hN : cp.f.PrecompNeutral)
    (he : frameEnterS cp.f c.acs = .run e) :
    callPrepP (s.withFork g) c = some (cp.withFork g) ∧
      frameEnterS (cp.withFork g).f c.acs = .run (e.withFork g) := by
  refine ⟨by rw [callPrepP_withFork hf hg, hp]; rfl, ?_⟩
  show frameEnterS (cp.f.withFork g) c.acs = _
  rw [frameEnterS_withFork_of_stat hf hg (callPrepP_stat hp) hN, he]; rfl

/-- **A `DELEGATECALL` spawn transports to any covered fork**
(`scallSpawn_withFork` for `dcallPrep`). -/
theorem dcallSpawn_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep} {e : Evm}
    (hp : dcallPrep s d adrs acs = some cp) (hN : cp.f.PrecompNeutral)
    (he : frameEnterS cp.f acs = .run e) :
    dcallPrep (s.withFork g) d adrs acs = some (cp.withFork g) ∧
      frameEnterS (cp.withFork g).f acs = .run (e.withFork g) := by
  refine ⟨by rw [dcallPrep_withFork hf hg, hp]; rfl, ?_⟩
  show frameEnterS (cp.f.withFork g) acs = _
  rw [frameEnterS_withFork_of_stat hf hg (dcallPrep_stat hp) hN, he]; rfl

end Blanc.Lift.NodeWalk
