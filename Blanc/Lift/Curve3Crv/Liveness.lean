import Blanc.Lift.Curve3Crv.CommittedHistory
import Blanc.Lift.Curve3Crv.Exec

/-!
# Liveness at every reachable state (3Crv)

`c3crv_history_committed` (`CommittedHistory.lean`) says the future storage of
a configured history abstracts the replayed model state `s` over the history's
live keys `K`. `c3crv_step_exec` and `c3crv_setName_exec` (`Exec.lean`) say a
call the model accepts at such a state executes with its exact cost and the
model's output. This module composes them: at any frame whose pre-state is the
future state of a configured history, every model-accepted call executes,
assuming freshness only for that new call's own keys.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionTrace

/-- **Liveness at every reachable state (every function but `set_name`).** After
any configured history, every call the model accepts at the replayed state
executes at the future storage with its exact cost and the model's output. -/
theorem c3crv_history_live {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (calldata : trace.FrameAdmitted ca (fun sevm _ => sevm.data.length < 2 ^ 256))
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace))
    (sevm : Sevm) (pre : Devm) (k : Nat)
    (target : sevm.currentTarget = ca)
    (state : pre.state = future.state)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hk1 : k ≠ 1)
    (hk : sels[k]? = some (Sevm.selector sevm)) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256) (houtput : pre.output = [])
    (hfresh : FreshKeys (Key.extend initialKeys (invocationKeys (committedInvocations ca trace)))
      (callKeys sevm.caller (decodeCall sevm))) :
    ∃ s, InvRun initial (committedInvocations ca trace) s ∧
      runInvocations initial (committedInvocations ca trace) = some s ∧
      VyInv (future.state.getStor ca) s
        (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) ∧
      ∀ (ow : Option B256) (o : Blanc.Curve3Crv.Out),
        Blanc.Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o →
        ∃ c, ∀ G, gCallStipend < G → ∃ post,
          Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + c)) (.ok post)) ∧ post.gasLeft = G ∧
            VyInv (Devm.getStor post sevm.currentTarget) o.1
              (Key.extend (Key.extend initialKeys (invocationKeys (committedInvocations ca trace)))
                (callKeys sevm.caller (decodeCall sevm))) ∧
            (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
            post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
            RetOut post.output o.2.2 := by
  obtain ⟨_, s, run, hrunEq, hfinal, _⟩ :=
    c3crv_history_committed trace installed invariant calldata fresh
  have hstor : Devm.getStor pre sevm.currentTarget = future.state.getStor ca := by
    rw [target]
    exact congrArg (fun world : State => world.getStor ca) state
  have hinv : VyInv (Devm.getStor pre sevm.currentTarget) s
      (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) := by
    rw [hstor]
    exact hfinal
  refine ⟨s, run, hrunEq, hfinal, fun ow o hok => ?_⟩
  obtain ⟨c, hx⟩ := c3crv_step_exec hcode hfork hstatic hk1 hk hlen hcd houtput hinv hfresh hok
  exact ⟨c, hx⟩

/-- **Liveness at every reachable state (`set_name`).** After any configured
history, a `set_name` the model accepts (with the owner answering the caller)
executes at the future storage and ends in the model's step. -/
theorem c3crv_history_setName_live {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (calldata : trace.FrameAdmitted ca (fun sevm _ => sevm.data.length < 2 ^ 256))
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace))
    (sevm : Sevm) (pre : Devm)
    (target : sevm.currentTarget = ca)
    (state : pre.state = future.state)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false)
    (hsel : Sevm.selector sevm = selSetName) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256) (houtput : pre.output = [])
    (hfresh : FreshKeys (Key.extend initialKeys (invocationKeys (committedInvocations ca trace)))
      (callKeys sevm.caller (decodeCall sevm))) :
    ∃ s, InvRun initial (committedInvocations ca trace) s ∧
      runInvocations initial (committedInvocations ca trace) = some s ∧
      VyInv (future.state.getStor ca) s
        (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) ∧
      ∀ (o : Blanc.Curve3Crv.Out),
        Blanc.Curve3Crv.step (c3ctx sevm (some sevm.caller.toB256)) (decodeCall sevm) s =
          .ok o →
        ∃ R P, ∀ Gc, OwnerCallOk sevm pre sevm.caller.toB256 R Gc → ∀ G, Gc + P ≤ G →
          G < 2 ^ 256 → ∃ post,
            Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + dispatchGas 1)) (.ok post)) ∧
              VyInv (Devm.getStor post sevm.currentTarget) o.1
                (Key.extend (Key.extend initialKeys
                  (invocationKeys (committedInvocations ca trace)))
                  (callKeys sevm.caller (decodeCall sevm))) ∧
              (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
              post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
              RetOut post.output o.2.2 := by
  obtain ⟨_, s, run, hrunEq, hfinal, _⟩ :=
    c3crv_history_committed trace installed invariant calldata fresh
  have hstor : Devm.getStor pre sevm.currentTarget = future.state.getStor ca := by
    rw [target]
    exact congrArg (fun world : State => world.getStor ca) state
  have hinv : VyInv (Devm.getStor pre sevm.currentTarget) s
      (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) := by
    rw [hstor]
    exact hfinal
  refine ⟨s, run, hrunEq, hfinal, fun o hok => ?_⟩
  obtain ⟨R, P, hx⟩ :=
    c3crv_setName_exec hcode hfork hstatic hsel hlen hcd houtput hinv hfresh hok
  exact ⟨R, P, hx⟩

end Blanc.Lift.Curve3Crv
