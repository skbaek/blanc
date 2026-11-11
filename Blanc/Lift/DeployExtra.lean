import Blanc.Lift.Exact
import Blanc.Lift.SolcStorageReturn
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.WalkSteps
import Blanc.DeploymentMessage
import Blanc.DeploymentTouch
import Blanc.Lift.WalkInvKit
import Blanc.Lift.Deploy
import Blanc.DeploymentMessageExtra

/-!
# Deploying lifted creation code

The bridge from a gas-exact synthetic run of a lifted constructor (`SProg.RunExact` of a
checked certificate of the creation input, `Blanc/Lift/Exact.lean`) to Jaune's CREATE
settlement `processCreateMessage`: the run is a real Jaune execution (`lift_exact`), it
settles as the inner message's result (`processMessage_ok_of_exec`), the returned output is
charged as code (`processCreateMessage.chargeCodeGas`, legacy schedule) and installed at the
new address (`processCreateMessage_ok_of_processMessage_and_charge`).

The walk steps a constructor needs beyond the shared kits (`SSTORE` and `CALLVALUE` in cut
runs, `RETURN` with its halting state named over a variable state, `returnPost`) are here too.

`liftCreate_ok` is contract-neutral: a contract supplies its checked creation certificate and a
run from the creation frame's start state, and receives the settled post-state with the
constructor's output installed as the new account's code and the exact normalized account storage.
-/

namespace Blanc.Lift

open Jaune

/-! ## Constructor walk steps

`SSTORE`, `CALLVALUE` and `RETURN` in cut runs, and `RETURN` of an arbitrary state in exact runs,
with the halting state named over a variable state (`returnPost`) so that nothing reduces a
concrete memory image. -/

section Steps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

end Steps

/-- **Deploying lifted creation code, exactly.**  If the checked creation certificate's
constructor runs, gas-exactly, from the creation frame's start state to `raw` without error,
and `raw`'s output is admissible code (no `0xEF` prefix, affordable, within the size limit),
then `processCreateMessage msg` succeeds with exactly `liftCreatePost msg.currentTarget raw`. -/
theorem liftCreate_post {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    (msg : Msg) (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hfork : CoveredFork msg.benv.stat.fork) {benv : Benv} {raw : Devm}
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hrun : SProg.RunExact c.prog (initSevm (createSeed msg benv))
      (initDevm (createSeed msg benv)) raw)
    (herror : raw.error = .none) (hprefix : raw.output.head? ≠ some 0xEF)
    (hgas : raw.output.length * gasCodeDeposit ≤ raw.gasLeft)
    (hmax : raw.output.length ≤ msg.benv.stat.rules.code.maxCodeSize) :
    processCreateMessage msg = .ok (liftCreatePost msg.currentTarget raw) := by
  have hstat : (initSevm (createSeed msg benv)).benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  obtain ⟨exc⟩ := lift_exact hc hj (sevm := initSevm (createSeed msg benv)) hcode
    (by rw [hstat]; exact hfork.shanghaiOnwards) hrun
  have hexec : exec (initEvm (createSeed msg benv)) = .ok raw :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
  have hprocess : processMessage (processCreateMessage.msg msg) = .ok raw :=
    processMessage_ok_of_exec htransfer hcodeAddress hexec herror
      (hfork.cases (motive := fun f => f.ruleSet.settle.touchedSweep = false) rfl rfl rfl rfl)
  have hcharge := processCreateMessage.chargeCodeGas_legacy_eq_ok
    (rules := msg.benv.stat.rules) (d := raw) hfork.rules_stateGas_none hprefix hgas hmax
  exact processCreateMessage_ok_of_processMessage_and_charge msg hprocess herror hcharge

/-- **Deploying lifted creation code.**  If the checked creation certificate's constructor
runs, gas-exactly, from the creation frame's start state to `raw` without error, and `raw`'s
output is admissible code (no `0xEF` prefix, affordable, within the size limit), then
`processCreateMessage msg` succeeds, installs `raw.output` at `msg.currentTarget`, and keeps
the exact normalized storage there. -/
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
      Devm.getStor post msg.currentTarget =
        ({ raw.state.get msg.currentTarget with code := ⟨⟨raw.output⟩⟩ } : Acct).clearIfEmpty.stor ∧
      post.error = .none := by
  refine ⟨_, liftCreate_post hc hj msg hcodeAddress hcode hfork htransfer hrun herror hprefix
    hgas hmax, ?_, ?_, ?_⟩
  · unfold Devm.getCode Devm.getAcct
    rw [(liftCreatePost_facts _ raw).2.2.1]
    simp only [Acct.clearIfEmpty_code, ByteArray.toList_eq_toList_data]
  · unfold Devm.getStor Devm.getAcct
    rw [(liftCreatePost_facts _ raw).2.2.1]
  · rw [(liftCreatePost_facts _ raw).1]
    exact herror

end Blanc.Lift
