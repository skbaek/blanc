import Blanc.Lift.Exact
import Blanc.DeploymentMessage

/-!
# Deploying lifted creation code

The bridge from a gas-exact synthetic run of a lifted constructor (`SProg.RunExact` of a
checked certificate of the creation input, `Blanc/Lift/Exact.lean`) to Jaune's CREATE
settlement `processCreateMessage`: the run is a real Jaune execution (`lift_exact`), it
settles as the inner message's result (`processMessage_ok_of_exec`), the returned output is
charged as code (`processCreateMessage.chargeCodeGas`, legacy schedule) and installed at the
new address (`processCreateMessage_ok_of_processMessage_and_charge`).

`liftCreate_ok` is contract-neutral: a contract supplies its checked creation certificate and a
run from the creation frame's start state, and receives the settled post-state with the
constructor's output installed as the new account's code and the constructor's storage kept.
-/

namespace Blanc.Lift

open Jaune

/-- The creation frame of `msg` over the post-transfer environment `benv`. -/
abbrev createSeed (msg : Msg) (benv : Benv) : Msg := (processCreateMessage.msg msg).withBenv benv

/-- **Deploying lifted creation code.**  If the checked creation certificate's constructor
runs, gas-exactly, from the creation frame's start state to `raw` without error, and `raw`'s
output is admissible code (no `0xEF` prefix, affordable, within the size limit), then
`processCreateMessage msg` succeeds, installs `raw.output` at `msg.currentTarget`, and keeps
`raw`'s storage there. -/
theorem liftCreate_ok {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    (msg : Msg) (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hfork : CoveredFork msg.benv.stat.fork) {benv : Benv} {raw : Devm}
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hrun : SProg.RunExact c.prog (initSevm (createSeed msg benv))
      (initDevm (createSeed msg benv)) raw)
    (herror : raw.error = .none) (hprefix : raw.output.head? ≠ some 0xEF)
    (hgas : raw.output.length * gasCodeDeposit ≤ raw.gasLeft)
    (hmax : raw.output.length ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = raw.output ∧
      Devm.getStor post msg.currentTarget = Devm.getStor raw msg.currentTarget ∧
      post.error = .none := by
  have hstat : (initSevm (createSeed msg benv)).benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  obtain ⟨exc⟩ := lift_exact hc hj (sevm := initSevm (createSeed msg benv)) hcode
    (by rw [hstat]; exact hfork) hrun
  have hexec : exec (initEvm (createSeed msg benv)) = .ok raw :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
  have hprocess : processMessage (processCreateMessage.msg msg) = .ok raw :=
    processMessage_ok_of_exec htransfer hcodeAddress hexec herror
  have hcharge := processCreateMessage.chargeCodeGas_legacy_eq_ok
    (rules := msg.benv.stat.rules) (d := raw) hfork.rules_stateGas_none hprefix hgas hmax
  refine ⟨_, processCreateMessage_ok_of_processMessage_and_charge msg hprocess herror hcharge,
    ?_, ?_, ?_⟩
  · unfold Devm.getCode Devm.getAcct
    rw [Devm.setCode_state]
    unfold State.setCode
    rw [State.get_set_self]
    simp only [ByteArray.toList_eq_toList_data]
    rfl
  · rw [congrFun (Devm.setCode_getStor _ msg.currentTarget _) msg.currentTarget]
    rfl
  · rw [Devm.setCode_error]
    exact herror

end Blanc.Lift
