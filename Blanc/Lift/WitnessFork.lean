import Blanc.Lift.NodeWalkFork
import Blanc.Lift.WitnessBoundary
import Blanc.Lift.WitnessSpawn

/-!
# Frame-level witnesses under any covered fork

`Blanc/Lift/NodeWalkFork.lean` shows that a run of the certificate interpreter `wrun` is
unchanged by the fork (`wrun_withFork`).  This module carries the rest of the witness kit
across: the child machinery built on it (`childStart`, `childRun`, `callResume`, and the
two-call frame kit `callPairFrom` of `Blanc/Lift/WitnessBoundary.lean`) is unchanged by the
fork, so every kernel fact stated with them is the same fact for `s.withFork g`; and Jaune's
own driver (`stepN`) transports from a Prague machine, in which `CLZ` is invalid: a Prague
step that is not an error halt is at an instruction every covered fork runs the same.
Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift Blanc.ForkUniform Blanc.Lift.NodeWalk Blanc.ConcreteRun
  Blanc.Lift.Witness.Boundary

variable {s : Sevm} {g : Fork}

/-! ## The child machinery -/

/-- The machine a code child of `CALL` starts with carries the caller's block environment. -/
theorem childStart_stat {c cc : Cfg} {f0 : SFunc} {e : Evm}
    (h : childStart s c f0 = some (e, cc)) : e.sta.benvStat = s.benvStat := by
  unfold childStart at h
  split at h
  · rename_i cp hp
    split at h
    · rename_i cevm he
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact (frameEnterS_stat he).trans (callPrep_stat hp).2
      · cases h
    · cases h
  · cases h

/-- **A code child's start is unchanged by the fork**: the machine is the same machine with
its fork changed, the configuration is the same. -/
theorem childStart_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g) (c : Cfg)
    (f0 : SFunc) :
    childStart (s.withFork g) c f0 =
      (childStart s c f0).map (fun p => (p.1.withFork g, p.2)) := by
  unfold childStart
  rw [callPrep_withFork hf hg]
  cases hp : callPrep s c with
  | none => rfl
  | some cp =>
    simp only [Option.map_some]
    by_cases hN : frameEntryForkFree cp.f = true
    · have hfe : frameEnterS (cp.withFork g).f c.acs = (frameEnterS cp.f c.acs).withFork g :=
        frameEnterS_withFork_of_stat hf hg (callPrep_stat hp)
          (precompNeutral_of_frameEntryForkFree hN) _
      rw [hfe]
      have hN' : frameEntryForkFree (cp.withFork g).f = true := hN
      cases hr : frameEnterS cp.f c.acs with
      | run e => simp only [FrameEntry.withFork, hN, hN', ↓reduceIte, Option.map_some]; rfl
      | done r => rfl
    · have h1 : frameEntryForkFree cp.f = false := by simpa using hN
      have h2 : frameEntryForkFree (cp.withFork g).f = false := h1
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
      split <;> split <;> rfl

/-- **A code child's run is unchanged by the fork** (the block carries no excess blob gas). -/
theorem childRun_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (hx : s.benvStat.excessBlobGas = 0) (fs : List SFunc) (code : ByteArray) (n : Nat) (c : Cfg) :
    childRun fs code (s.withFork g) n c = childRun fs code s n c := by
  unfold childRun
  cases fs[0]? with
  | none => rfl
  | some f0 =>
    dsimp only
    rw [childStart_withFork hf hg]
    cases hcs : childStart s c f0 with
    | none => rfl
    | some p =>
      obtain ⟨e, cc⟩ := p
      have hst := childStart_stat hcs
      have hf' : CoveredFork e.sta.benvStat.fork := by rw [hst]; exact hf
      have hx' : e.sta.benvStat.excessBlobGas = 0 := by rw [hst]; exact hx
      simp only [Option.map_some]
      show (if decide (CoveredFork g) ∧ e.sta.code.data.toList = code.data.toList then
          wrun fs (e.sta.withFork g) n cc else .stuck) = _
      simp only [decide_eq_true hg, decide_eq_true hf', true_and]
      split
      · exact wrun_withFork hf' hg hx' fs n cc
      · rfl

/-- The configuration after a code-child `CALL` is unchanged by the fork. -/
theorem callResume_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g) (c : Cfg)
    (child : Devm) (ck : List (Adr × B256)) (ca : List Adr) (cs : StorShadow)
    (cacc : AcctShadow) :
    callResume (s.withFork g) c child ck ca cs cacc = callResume s c child ck ca cs cacc := by
  unfold callResume
  cases hf0 : c.f with
  | next n k =>
    cases n with
    | exec x =>
      cases x with
      | call =>
        simp only
        rw [callPrep_withFork hf hg]
        cases hp : callPrep s c with
        | none => rfl
        | some cp =>
          simp only [Option.map_some]
          by_cases hN : frameEntryForkFree cp.f = true
          · have hfe : frameEnterS (cp.withFork g).f c.acs = (frameEnterS cp.f c.acs).withFork g :=
              frameEnterS_withFork_of_stat hf hg (callPrep_stat hp)
                (precompNeutral_of_frameEntryForkFree hN) _
            rw [hfe]
            cases hr : frameEnterS cp.f c.acs with
            | run e => rfl
            | done r => rfl
          · have h1 : frameEntryForkFree cp.f = false := by simpa using hN
            have h2 : frameEntryForkFree (cp.withFork g).f = false := h1
            simp only [h1, h2, Bool.false_eq_true, and_false, ↓reduceIte]
            split <;> split <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-! ## The two-call frame kit -/

theorem callPairFrom_withFork (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (hx : s.benvStat.excessBlobGas = 0) (fs fsT : List SFunc) (tcode : ByteArray)
    (nA nT nB : Nat) (ck : List (Adr × B256)) (ca : List Adr) (cs : StorShadow)
    (cacc : AcctShadow) (r : Res) (d : Devm) :
    callPairFrom fs (s.withFork g) fsT tcode nA nT nB ck ca cs cacc r d =
      callPairFrom fs s fsT tcode nA nT nB ck ca cs cacc r d := by
  unfold callPairFrom
  simp only [wrun_withFork hf hg hx, childRun_withFork hf hg hx, callResume_withFork hf hg]

/-! ## Jaune's driver from a Prague machine -/

/-- A Prague step that is not an error halt runs an instruction that every covered fork runs
the same: it is not `CLZ` (an invalid opcode before Osaka), and the block carries no excess
blob gas. -/
theorem instNeutralAt_of_prague {e : Evm} (hp : e.sta.benvStat.fork = .prague)
    (hx : e.sta.benvStat.excessBlobGas = 0) (h : ∀ ee, Evm.step e ≠ .halt (.error ee)) :
    InstNeutralAt e.sta e.pc := by
  refine ⟨fun hc => ?_, fun _ => hx⟩
  refine h ⟨.halt (.invalidOpcode .none), e.dyna⟩ ?_
  unfold Evm.step
  have hi : e.getInst = some (.next (.reg .clz)) := hc
  rw [hi]
  show Step.ofExecution _ (Rinst.runCore e.pc e.dyna e.sta .clz) = _
  have hclz : e.sta.benvStat.rules.op.clz = false := by
    show (Fork.ruleSet e.sta.benvStat.fork).op.clz = false
    rw [hp]; rfl
  simp only [Rinst.runCore, hclz, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **One driver step from a Prague machine commutes with the fork change** when it is not an
error halt. -/
theorem evm_step_withFork_prague {e : Evm} (hp : e.sta.benvStat.fork = .prague)
    (hx : e.sta.benvStat.excessBlobGas = 0) (hg : CoveredFork g)
    (h : ∀ ee, Evm.step e ≠ .halt (.error ee)) :
    (e.withFork g).step = e.step.withFork g :=
  evm_step_withFork (by rw [hp]; exact CoveredFork.prague) hg (instNeutralAt_of_prague hp hx h)

/-- **`stepN` from a Prague machine commutes with the fork change.** -/
theorem stepN_withFork (hg : CoveredFork g) :
    ∀ {n : Nat} {e e' : Evm}, e.sta.benvStat.fork = .prague →
      e.sta.benvStat.excessBlobGas = 0 → stepN n e = some e' →
      stepN n (e.withFork g) = some (e'.withFork g)
  | 0, e, e', _, _, h => by
    simp only [stepN, Option.some.injEq] at h
    subst h
    rfl
  | n + 1, e, e', hp, hx, h => by
    simp only [stepN] at h
    split at h
    · rename_i pc devm hstep
      have hs := evm_step_withFork_prague hp hx hg (by rw [hstep]; intro ee; nofun)
      simp only [stepN]
      rw [hs, hstep]
      exact stepN_withFork hg (e := ⟨pc, e.sta, devm⟩) hp hx h
    · cases h

end Blanc.Lift.Witness
