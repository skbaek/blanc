import Blanc.Lift.Curve3Crv.Jumps
import Blanc.Lift.Curve3Crv.LiveBodies
import Blanc.Lift.Curve3Crv.Safe

/-!
# Model-accepted calls are real executions of the deployed 3Crv runtime (liveness)

The dispatcher (`live_dispatch`, `dispatchGas k`), a body (`live_at`, or `live_setName`), and the
kernel-checked converse bridge `exec_of_runExact` compose into a real Jaune execution of the
deployed bytes from a frame start:

* `c3crv_exec`: a raw effect that succeeds is executed, gas-exact, ending as it says;
* `c3crv_step_exec`: under `VyInv` and `FreshKeys`, a call the model accepts (every function but
  `set_name`) is executed, gas-exact, and ends in the model's new state, events and return data;
* `c3crv_setName_exec`: `set_name`, the model accepting with the owner answering the caller, is
  executed whenever the minter's `owner()` answers the caller (`OwnerCallOk`); its gas after the
  call is the callee's, so it is not exact.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune
open Blanc.Curve3Crv (Call)

/-- **A raw effect that succeeds is a real, gas-exact execution** of the deployed runtime (every
body but `set_name`). -/
theorem c3crv_exec {sevm : Sevm} {pre : Devm} {k : Nat} {ow : Option B256} {r : Raw}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hk1 : k ≠ 1)
    (hk : sels[k]? = some (Sevm.selector sevm)) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256)
    (hr : rawOf k sevm ow (Devm.getStor pre sevm.currentTarget) = some r) :
    ∃ c, ∀ G, gCallStipend < G → ∃ post,
      Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + c)) (.ok post)) ∧ post.gasLeft = G ∧
        Lands sevm pre post r := by
  obtain ⟨f, hf⟩ : ∃ f, bodies[k]? = some f := by
    have hlt : k < sels.length := (List.getElem?_eq_some_iff.mp hk).1
    exact ⟨_, List.getElem?_eq_getElem (by simpa [sels, bodies] using hlt)⟩
  obtain ⟨c, hc⟩ := live_at hfork hstatic hk1 hf hr
  refine ⟨c + dispatchGas k, fun G hG => ?_⟩
  obtain ⟨post, hrun, hg, hl⟩ := hc G hG
  have hd := live_dispatch hf hk rfl hlen hcd hrun
  rw [← Nat.add_assoc]
  exact ⟨post, exec_of_runExact hcode hfork ⟨_, rfl, hd⟩, hg, hl⟩

/-- **A call the model accepts is a real, gas-exact execution ending in the model's step**
(every function but `set_name`). -/
theorem c3crv_step_exec {sevm : Sevm} {pre : Devm} {s : Curve3Crv.State} {K : Key → Prop}
    {ow : Option B256} {o : Curve3Crv.Out} {k : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hk1 : k ≠ 1)
    (hk : sels[k]? = some (Sevm.selector sevm)) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256)
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (hok : Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o) :
    ∃ c, ∀ G, gCallStipend < G → ∃ post,
      Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + c)) (.ok post)) ∧ post.gasLeft = G ∧
        VyInv (Devm.getStor post sevm.currentTarget) o.1
          (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
        (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
        post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
        RetOut post.output o.2.2 := by
  have hdec := decodeCall_at hk rfl hlen
  rw [hdec] at hfresh hok ⊢
  have hk13 : k < 13 := by
    have := (List.getElem?_eq_some_iff.mp hk).1
    simpa [sels] using this
  obtain ⟨r, hr, hc⟩ := (refine_at (ow := ow) hk13 hinv hfresh).2 o hok
  obtain ⟨c, hx⟩ := c3crv_exec hcode hfork hstatic hk1 hk hlen hcd hr
  refine ⟨c, fun G hG => ?_⟩
  obtain ⟨post, he, hg, hl⟩ := hx G hG
  exact ⟨post, he, hg, writer_post hl hc⟩

/-- **`set_name` the model accepts is a real execution** whenever the minter's `owner()` answers
the caller: there are a gas amount `R` the body needs after the call and a prefix cost `P` such
that, if the call answers leaving `R` whenever made with at least `Gc`, every frame with at least
`Gc + P` gas (beyond the dispatcher's) succeeds and ends in the model's step. -/
theorem c3crv_setName_exec {sevm : Sevm} {pre : Devm} {s : Curve3Crv.State} {K : Key → Prop}
    {o : Curve3Crv.Out}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false)
    (hsel : Sevm.selector sevm = selSetName) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256)
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (hok : Curve3Crv.step (c3ctx sevm (some sevm.caller.toB256)) (decodeCall sevm) s = .ok o) :
    ∃ R P, ∀ Gc, OwnerCallOk sevm pre sevm.caller.toB256 R Gc → ∀ G, Gc + P ≤ G →
      G < 2 ^ 256 → ∃ post,
        Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + dispatchGas 1)) (.ok post)) ∧
        VyInv (Devm.getStor post sevm.currentTarget) o.1
          (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
        (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
        post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
        RetOut post.output o.2.2 := by
  have hs1 : sels[1]? = some selSetName := rfl
  have hdec := decodeCall_at hs1 hsel hlen
  rw [hdec] at hfresh hok ⊢
  obtain ⟨r, hr, hc⟩ := (refine_at (ow := some sevm.caller.toB256) (k := 1) (by decide) hinv
    hfresh).2 o hok
  obtain ⟨R, P, hx⟩ := live_setName (b := pre) hfork hstatic hr
  refine ⟨R, P, fun Gc hcall G hG hG' => ?_⟩
  obtain ⟨post, hrun, hl⟩ := hx Gc hcall G hG hG'
  have hd := live_dispatch (k := 1) rfl hs1 hsel hlen hcd hrun
  exact ⟨post, exec_of_runExact hcode hfork ⟨_, rfl, hd⟩, writer_post hl hc⟩

end Blanc.Lift.Curve3Crv
