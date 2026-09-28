import Blanc.Lift.Curve3Crv.Lift
import Blanc.Lift.Curve3Crv.SafeBodies
import Blanc.Lift.Curve3Crv.SafeViews
import Blanc.ExecutionFrameEntry

/-!
# The deployed 3Crv runtime refines the model (safety), composed from its segments

Every successful frame execution of the deployed bytes, from a frame start and the storage
abstraction `VyInv … s K`, with the frame-local `FreshKeys` premise for the keys the call touches:

* if the call writes (`set_minter`, `set_name`, `transfer`, `transferFrom`, `approve`, `mint`,
  `burnFrom`), it is exactly the model's `step` on the call `decodeCall` reads: the model
  accepts it (with, for `set_name`, the owner answer the frame's static call to the minter
  returned), the new storage abstracts the model's new state over the extended live keys, other
  accounts' storage is unchanged, the model's events are appended as `LOG3` entries, and the
  return data is the model's;
* otherwise (the six views; a selector miss or short calldata cannot succeed) every storage map
  and the log list are unchanged.

Route: `lift_sound`; the dispatcher (`safe_dispatch`) hands body `k` its entry state; views by
the kernel-decided quiet sets (`view_world`); writers by their inversion segments
(`SafeBodies.lean`) and the pure refinement (`refine_at`).

`c3crv_frame_refines_raw` keeps Jaune's exact `STOP` output preservation over
an arbitrary base. `c3crv_frame_refines` specializes to empty entry output;
`c3crv_entered_frame_refines` derives that freshness from actual frame entry.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Call)

/-- A writer's landing and correspondence give the frame's conclusion. -/
theorem writer_post {sevm : Sevm} {pre post : Devm} {K' : Key → Prop} {r : Raw}
    {o : Curve3Crv.Out} (hl : Lands sevm pre post r) (hc : Corr sevm K' r o) :
    VyInv (Devm.getStor post sevm.currentTarget) o.1 K' ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
      post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
      RetOutFrom pre.output post.output o.2.2 := by
  obtain ⟨hinv, hlogs, hret⟩ := hc
  refine ⟨hl.stor ▸ hinv, hl.other, hl.logs.trans (by rw [hlogs]), ?_⟩
  rcases h : r.2.2 with _ | out
  · rw [h] at hret
    simp only [RetMatch] at hret
    rw [hret]
    exact hl.stop_output h
  · rw [h] at hret
    rw [hl.output out h]
    cases hr : o.2.2 <;> simp only [hr, RetMatch, RetOutFrom] at hret ⊢
    · exact hret
    · exact hret
    · exact hret

/-- **Raw refinement of the deployed runtime**, retaining exact output over an arbitrary base. -/
theorem c3crv_frame_refines_raw {sevm : Sevm} {pre post : Devm} {s : Curve3Crv.State}
    {K : Key → Prop}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (exc : Exec 0 sevm pre (.ok post)) :
    (IsWriter (decodeCall sevm) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOutFrom pre.output post.output o.2.2) ∧
    (¬ IsWriter (decodeCall sevm) →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs) := by
  obtain ⟨f0, hf0, run⟩ := lift_sound cert_check hcode hfork exc
  rw [show (Cert.prog cert)[0]? = some t_0000_c0 from rfl] at hf0
  cases hf0
  rw [St.self hstack hmem] at run
  obtain ⟨k, f, sel, G', hk, hs, hsel, hlen, runB⟩ := safe_dispatch hcd run
  have hdec := decodeCall_at hs hsel hlen
  rw [hdec] at hfresh ⊢
  have hk13 : k < 13 := by
    have := (List.getElem?_eq_some_iff.mp hk).1
    simpa [bodies] using this
  set stor := Devm.getStor pre sevm.currentTarget with hstor
  -- a writer, from its landing
  have writer : ∀ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) →
      (∃ r, rawOf k sevm ow stor = some r ∧ Lands sevm pre post r) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (callAt sevm k) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (callAt sevm k))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOutFrom pre.output post.output o.2.2 := by
    intro ow how ⟨r, hr, hl⟩
    obtain ⟨o, ho, hc⟩ := (refine_at (ow := ow) hk13 hinv hfresh).1 r hr
    exact ⟨ow, how, o, ho, writer_post hl hc⟩
  -- a view, from quietness
  have view : k ∈ viewKs →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs := by
    intro hv
    have hw := view_world hfork hv hk runB
    exact ⟨fun a => congrFun hw.1 a, hw.2⟩
  have none_ok : ∀ w, (none : Option B256) = some w → OwnerAnswer sevm pre s.minter w :=
    fun _ h => absurd h (by simp)
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp only [bodies, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hk
  all_goals try subst hk
  · exact ⟨fun _ => writer none none_ok (safe_setMinter hfork G' post runB),
      fun h => absurd trivial h⟩
  · refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
    obtain ⟨w, hw, r, hr, hl⟩ := safe_setName hfork runB
    have hm : (stor.get vyMinterSlot).toAdr = s.minter := by
      rw [hinv.minter, toAdr_toB256]
    rw [hm] at hw
    exact writer (some w) (fun w' h => by cases h; exact hw) ⟨r, hr, hl⟩
  · exact ⟨fun h => False.elim h, fun _ => view (by simp [viewKs])⟩
  · exact ⟨fun h => False.elim h, fun _ => view (by simp [viewKs])⟩
  · exact ⟨fun _ => writer none none_ok (safe_transfer hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun _ => writer none none_ok (safe_transferFrom hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun _ => writer none none_ok (safe_approve hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun _ => writer none none_ok (safe_mint hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun _ => writer none none_ok (safe_burnFrom hfork G' post runB),
      fun h => absurd trivial h⟩
  · exact ⟨fun h => False.elim h, fun _ => view (by simp [viewKs])⟩
  · exact ⟨fun h => False.elim h, fun _ => view (by simp [viewKs])⟩
  · exact ⟨fun h => False.elim h, fun _ => view (by simp [viewKs])⟩
  · exact ⟨fun h => False.elim h, fun _ => view (by simp [viewKs])⟩

/-- Fresh entry makes the exact raw output relation the model's return bytes. -/
theorem c3crv_frame_refines {sevm : Sevm} {pre post : Devm} {s : Curve3Crv.State}
    {K : Key → Prop}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (houtput : pre.output = [])
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (exc : Exec 0 sevm pre (.ok post)) :
    (IsWriter (decodeCall sevm) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOut post.output o.2.2) ∧
    (¬ IsWriter (decodeCall sevm) →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs) := by
  have h := c3crv_frame_refines_raw hcode hfork hcd hstack hmem hinv hfresh exc
  refine ⟨?_, h.2⟩
  intro hw
  obtain ⟨ow, how, o, hok, hinv', hother, hlogs, hret⟩ := h.1 hw
  exact ⟨ow, how, o, hok, hinv', hother, hlogs, hret.of_empty houtput⟩

/-- Refinement from a genuinely entered frame; initialization supplies all
three freshness facts, including empty output, rather than assuming a final result. -/
theorem c3crv_entered_frame_refines {sevm : Sevm} {pre post : Devm} {s : Curve3Crv.State}
    {K : Key → Prop} {frame : Jaune.Frame}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (henter : frame.enter = .run ⟨0, sevm, pre⟩)
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (exc : Exec 0 sevm pre (.ok post)) :
    (IsWriter (decodeCall sevm) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOut post.output o.2.2) ∧
    (¬ IsWriter (decodeCall sevm) →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs) := by
  obtain ⟨hstack, hmem⟩ := Frame.enter_run_fresh henter
  exact c3crv_frame_refines hcode hfork hcd hstack hmem
    (Frame.enter_run_output_empty henter) hinv hfresh exc

end Blanc.Lift.Curve3Crv
