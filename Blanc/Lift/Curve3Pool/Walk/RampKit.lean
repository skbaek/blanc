import Blanc.Lift.Curve3Pool.Walk.ViewsKit
import Blanc.Lift.Curve3Pool.Walk.Quiet
import Blanc.Lift.Curve3Pool.Spec

/-!
# Kit for the ramp entries (`ramp_A`, `stop_ramp_A`)

* `rawEffect_noChild`: the raw effect of a childless frame in the quiet environment, from its
  storage effect, its logs (the model's events appended) and its output.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **A childless frame's raw effect** in the quiet environment. -/
theorem rawEffect_noChild {D : Exec.Deriv} {post : Devm} {o : Out}
    (hch : children D = [])
    (hstor : StorEffect (decodeCall D.sevm) (entryStor D) (post.getStor D.sevm.currentTarget)
      o.state)
    (hlogs : post.logs = D.devm.logs ++ o.events.map (eventLog D.sevm.currentTarget))
    (hout : post.output = retOut D.devm.output o.ret) (hcalls : o.calls = []) :
    RawEffect D post (quietEnv D.sevm) o := by
  refine ⟨envOf_quiet D, hstor, ?_, hout, fun _ => ?_⟩
  · rw [hlogs, hch]
    simp only [List.flatMap_nil, List.append_nil]
  · rw [CallsOf, hch, hcalls]
    rfl

/-- **The ramp entries' storage effect**: the four ramp slots set to `a, f, t0, t1`. -/
theorem ramp_storEffect {c : Call}
    (hfp : footprint c = [.initialA, .futureA, .initialATime, .futureATime]) {pre post : Stor}
    {s' : State} {a f t0 t1 : B256}
    (hpost : ∀ x, post.get x = ((((pre.set initialASlot a).set futureASlot f).set
      initialATimeSlot t0).set futureATimeSlot t1).get x)
    (ha : a.toNat = s'.initialA) (hf : f.toNat = s'.futureA) (h0 : t0.toNat = s'.initialATime)
    (h1 : t1.toNat = s'.futureATime) : StorEffect c pre post s' := by
  refine ⟨fun x hx => ?_, fun g hg => ?_⟩
  · rw [hfp] at hx
    have e0 : initialASlot ≠ x := hx .initialA (by decide)
    have e1 : futureASlot ≠ x := hx .futureA (by decide)
    have e2 : initialATimeSlot ≠ x := hx .initialATime (by decide)
    have e3 : futureATimeSlot ≠ x := hx .futureATime (by decide)
    rw [hpost, Stor.get_set_ne _ e3, Stor.get_set_ne _ e2, Stor.get_set_ne _ e1,
      Stor.get_set_ne _ e0]
  · rw [hfp] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · show (post.get initialASlot).toNat = _
      rw [hpost, Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide),
        Stor.get_set_ne _ (by decide), Stor.get_set_self, ha]
    · show (post.get futureASlot).toNat = _
      rw [hpost, Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide), Stor.get_set_self, hf]
    · show (post.get initialATimeSlot).toNat = _
      rw [hpost, Stor.get_set_ne _ (by decide), Stor.get_set_self, h0]
    · show (post.get futureATimeSlot).toNat = _
      rw [hpost, Stor.get_set_self, h1]

end Blanc.Lift.Curve3Pool
