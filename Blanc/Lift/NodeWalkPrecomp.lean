import Blanc.Lift.NodeWalkFrames
import Blanc.Lift.NodeWalkFork

/-!
# A synchronous precompile child of a node walk

A `STATICCALL` into a precompile is not a raw frame: its entry answers at once
(`Frame.enter = .done`), and the derivation continues through `Exec.doneOk`.  The walk engine
(`Blanc/Lift/NodeWalk.lean`) stops at every frame-entering instruction; this module supplies
the step across such a call on any derivation:

* `Exec.Deriv.step_done`: one driver step whose spawned frame answers synchronously pins the
  node's same-frame successor (outcome and raw frame descendants unchanged);
* `staticcall_done_node`: at an agreeing configuration whose code has a `STATICCALL` at its
  pc, a prepared call whose shadow entry answers successfully resumes at the configuration
  the shadows describe (the account shadow takes the call's value transfer);
* `scallDone_withFork`: the preparation and the synchronous entry transport to any covered
  fork, for a frame that avoids `MODEXP` and `P256VERIFY`.

Nothing here is contract-specific.
-/

namespace Blanc.Lift.NodeWalk

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ForkUniform
open Jaune.Exec.Deriv (ParentStep ParentPrefix)

/-- A spawning step whose frame answers synchronously and resumes: every derivation node has
the resumed machine as its same-frame successor, with the same outcome and the same raw frame
descendants. -/
theorem Exec.Deriv.step_done {x : Exec.Deriv} {f : Frame} {rsm : Resume} {pc' : Nat}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {post : Devm}
    (h : Evm.step ⟨x.pc, x.sevm, x.devm⟩ = .spawn f rsm pc') (henter : f.enter = .done r)
    (hr : rsm.run r = .ok post) :
    ∃ x', ParentStep x' x ∧ x'.pc = pc' ∧ x'.sevm = x.sevm ∧ x'.devm = post ∧
      x'.exn = x.exn ∧ Exec.rawFrameDescendants x'.exc = Exec.rawFrameDescendants x.exc := by
  obtain ⟨pc, sevm, devm, exn, exc⟩ := x
  cases exc with
  | halt h' => simp only at h; rw [h] at h'; cases h'
  | cont h' _ => simp only at h; rw [h] at h'; cases h'
  | doneErr h' he hr' =>
    simp only at h; rw [h] at h'; cases h'; rw [henter] at he; cases he
    rw [hr] at hr'; cases hr'
  | doneOk h' he hr' next =>
    simp only at h; rw [h] at h'; cases h'; rw [henter] at he; cases he
    rw [hr] at hr'; cases hr'
    exact ⟨_, .doneOk h henter hr next, rfl, rfl, rfl, rfl,
      by simp only [Exec.rawFrameDescendants]⟩
  | runErr h' he _ _ => simp only at h; rw [h] at h'; cases h'; rw [henter] at he; cases he
  | runOk h' he _ _ _ => simp only at h; rw [h] at h'; cases h'; rw [henter] at he; cases he

/-- **A `STATICCALL` into a precompile, on any derivation.**  At a node sitting at an agreeing
configuration whose code has a `STATICCALL` at its pc, if the prepared frame's shadow entry
answers with a successful machine and the parent resumes, the node's same-frame successor
sits at the resumed configuration, whose shadows agree; the outcome and the raw frame
descendants are unchanged. -/
theorem staticcall_done_node {sevm : Sevm} {c : PCfg} {cp : CallPrep} {child d : Devm}
    {x : Exec.Deriv} (hn : NodeAt sevm c x) (hag : PAgree c)
    (hat : Ninst.At sevm.code c.pc (.exec .staticcall))
    (hp : scallPrep sevm c.devm c.adrs c.acs = some cp)
    (he : frameEnterS cp.f c.acs = .done (.ok child)) (hce : child.error.isSome = false)
    (hr : resumeCallB cp.p cp.oi cp.os (.ok child) = some d) :
    ∃ x', ParentStep x' x ∧
      NodeAt sevm ⟨c.pc + 1, d, c.keys, cp.adrs, c.stor, acsTransfer cp.f.inner c.acs⟩ x' ∧
      x'.exn = x.exn ∧ Exec.rawFrameDescendants x'.exc = Exec.rawFrameDescendants x.exc ∧
      PAgree ⟨c.pc + 1, d, c.keys, cp.adrs, c.stor, acsTransfer cp.f.inner c.acs⟩ := by
  obtain ⟨hstep, hF⟩ := scallPrep_node_facts hag hp
  have hC : AcctAgree cp.f.inner.benv.state c.acs := by rw [hF.state]; exact hag.2.2.2
  have heB : frameEnterB cp.f = .done (.ok child) := by rw [frameEnterB_eq_S hC]; exact he
  have hent : cp.f.enter = .done (.ok child) := by rw [frame_enter_eq_B]; exact heB
  have hs : Evm.step ⟨c.pc, sevm, c.devm⟩ = .spawn cp.f (.call cp.p cp.oi cp.os) (c.pc + 1) := by
    rw [Evm.step_next hat]
    simp only [Ninst.step, hstep]
    rfl
  obtain ⟨x', e1, hp1, hs1, hd1, hex1, hdesc1⟩ :=
    Exec.Deriv.step_done ((step_eq_of_nodeAt hn).trans hs) hent (resumeCallB_sound hr)
  refine ⟨x', e1, ⟨hp1, hs1.trans hn.2.1, hd1⟩, hex1, hdesc1, ?_⟩
  obtain ⟨hda, hdk⟩ := resumeCallB_acc hr
  obtain ⟨hca, hck, -⟩ := frameEnterB_done_acc hF.create hF.stateGas heB
  obtain ⟨benv, hb, hcst⟩ := frameEnterB_done_ok_state hF.create hF.stateGas heB hce
  rw [benvAfterTransfer_eq_S hC] at hb
  refine ⟨fun y => ?_, fun a => ?_, fun a k => ?_, fun a => ?_⟩
  · show y ∈ d.accessedStorageKeys ↔ y ∈ c.keys
    rw [hdk y, hck, hF.entryKeys, hF.keys]
    exact ⟨fun h => (h.elim id (·.2)) |> (hag.1 y).mp, fun h => .inl ((hag.1 y).mpr h)⟩
  · show a ∈ d.accessedAddresses ↔ a ∈ cp.adrs
    rw [hda a, hca, hF.entryAdrs, hF.adrs a]
    exact ⟨fun h => h.elim id (·.2), .inl⟩
  · show storOf d.state a k = lookupS c.stor a k
    rw [resumeCallB_state hr, hcst]
    have hb' := hb
    unfold benvAfterTransferS at hb'
    split at hb'
    · split at hb'
      · cases hb'
      · cases hb'
        show storOf (State.setBal _ _ _) a k = _
        rw [storOf_setBal, storOf_setBal, hF.state]
        exact hag.2.2.1 a k
    · cases hb'
      rw [hF.state]
      exact hag.2.2.1 a k
  · show acctView (d.state.get a) = lookupA (acsTransfer cp.f.inner c.acs) a
    rw [resumeCallB_state hr, hcst]
    exact acctAgree_transfer hC hb a

/-- **A synchronous `STATICCALL` transports to any covered fork**: the preparation and the
shadow entry of the prepared frame, for a frame that avoids `MODEXP` and `P256VERIFY`. -/
theorem scallDone_withFork {s : Sevm} {g : Fork} (hf : CoveredFork s.benvStat.fork)
    (hg : CoveredFork g) {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (hp : scallPrep s d adrs acs = some cp) (hN : cp.f.PrecompNeutral)
    (he : frameEnterS cp.f acs = .done r) :
    scallPrep (s.withFork g) d adrs acs = some (cp.withFork g) ∧
      frameEnterS (cp.withFork g).f acs = .done r := by
  refine ⟨by rw [scallPrep_withFork hf hg, hp]; rfl, ?_⟩
  show frameEnterS (cp.f.withFork g) acs = _
  rw [frameEnterS_withFork_of_stat hf hg (scallPrep_stat hp) hN, he]
  rfl

end Blanc.Lift.NodeWalk
