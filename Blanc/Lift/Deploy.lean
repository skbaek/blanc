import Blanc.Lift.Exact
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.WalkSteps
import Blanc.DeploymentMessage

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
constructor's output installed as the new account's code and the constructor's storage kept.
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

/-- `SSTORE` at its selected cost, in a cut run. -/
theorem rxc_sstore {k' v : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hsentry : gCallStipend < G + sstoreCost sevm b k' v) (hstatic : sevm.isStatic = false)
    (k : SFunc.RunExactCut fs sevm C (St (afterSstore sevm b k' v) S M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (k' :: v :: S) M (G + sstoreCost sevm b k' v))
      (.next (.reg .sstore) f) r := by
  refine .next (Ninst.runCompiled_sstore_selected_setMach hfork hsentry hstatic) ?_
  rw [← afterSstore_stateGas (sevm := sevm) (devm := b) (key := k') (value := v)]
  exact k

/-- `CALLVALUE`, in a cut run. -/
theorem rxc_callvalue (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (sevm.value :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 2)) (.next (.reg .callvalue) f) r :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- `St` keeps the world's error and storage. -/
theorem St_error (b : Devm) (S : List B256) (M : Mem) (G : Nat) : (St b S M G).error = b.error :=
  rfl

theorem St_getStor (b : Devm) (S : List B256) (M : Mem) (G : Nat) (a : Adr) :
    Devm.getStor (St b S M G) a = Devm.getStor b a := rfl

/-- The state `RETURN` leaves (stated over a variable state, so nothing reduces a concrete
memory image). -/
def returnPost (d : Devm) (i sz : B256) (S : List B256) : Devm :=
  ((d.setMach ⟨S, d.memory, d.gasLeft, d.stateGas⟩).memRead i.toNat sz.toNat).2.withOutput
    (d.memory.read i.toNat sz.toNat).1

theorem returnPost_facts (d : Devm) (i sz : B256) (S : List B256) :
    (returnPost d i sz S).output = (d.memory.read i.toNat sz.toNat).1 ∧
      (returnPost d i sz S).error = d.error ∧
      (∀ a, Devm.getStor (returnPost d i sz S) a = Devm.getStor d a) ∧
      (returnPost d i sz S).gasLeft = d.gasLeft :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

/-- `RETURN` of a window that needs no expansion, in a cut run. -/
theorem rxc_return_any {fs : List SFunc} {sevm : Sevm} {C : List Nat} {d : Devm} {i sz : B256}
    {S : List B256} (hstk : d.stack = i :: sz :: S) (hext : d.extCost [⟨i.toNat, sz.toNat⟩] = 0) :
    SFunc.RunExactCut fs sevm C d (.last .return_) (.done (.halted (returnPost d i sz S))) := by
  refine .last ?_
  show Linst.run sevm _ .return_ = _
  exact Linst.run_return_eq_ok hstk (by rw [hext]; exact Nat.zero_le _)
    (by rw [hext, Nat.sub_zero]; rfl)

/-- `RETURN` of a window that needs no expansion, in an exact run. -/
theorem rx_return_any {fs : List SFunc} {sevm : Sevm} {d : Devm} {i sz : B256}
    {S : List B256} (hstk : d.stack = i :: sz :: S) (hext : d.extCost [⟨i.toNat, sz.toNat⟩] = 0) :
    SFunc.RunExact fs sevm d (.last .return_) (.halted (returnPost d i sz S)) := by
  refine .last ?_
  show Linst.run sevm _ .return_ = _
  exact Linst.run_return_eq_ok hstk (by rw [hext]; exact Nat.zero_le _)
    (by rw [hext, Nat.sub_zero]; rfl)

/-- `CODECOPY`, with the whole charge named, in an exact run. -/
theorem rx_codecopy {o : Outcome} {di si sz : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + gasCopy * ceilDiv sz.toNat 32 +
      (St b (di :: si :: sz :: S) M (G + c)).extCost [⟨di.toNat, sz.toNat⟩] = c)
    (hw : M.write di.toNat (sevm.code.sliceD si.toNat sz.toNat (Linst.toUInt8 .stop)) = M')
    (k : SFunc.RunExact fs sevm (St b S M' G) f o) :
    SFunc.RunExact fs sevm (St b (di :: si :: sz :: S) M (G + c)) (.next (.reg .codecopy) f) o :=
  .next (Ninst.runCompiled_codecopy_of (devm := St b (di :: si :: sz :: S) M (G + c)) rfl hc hw
    rfl) k

end Steps

/-- The creation frame of `msg` over the post-transfer environment `benv`. -/
abbrev createSeed (msg : Msg) (benv : Benv) : Msg := (processCreateMessage.msg msg).withBenv benv

/-- The settled world of a successful lifted CREATE: the constructor's final state charged
the code deposit, with its output installed at the new address. -/
def liftCreatePost (target : Adr) (raw : Devm) : Devm :=
  (raw.setMach ⟨raw.stack, raw.memory, raw.gasLeft - raw.output.length * gasCodeDeposit,
    raw.stateGas⟩).setCode target ⟨⟨raw.output⟩⟩

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
    (by rw [hstat]; exact hfork) hrun
  have hexec : exec (initEvm (createSeed msg benv)) = .ok raw :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
  have hprocess : processMessage (processCreateMessage.msg msg) = .ok raw :=
    processMessage_ok_of_exec htransfer hcodeAddress hexec herror
  have hcharge := processCreateMessage.chargeCodeGas_legacy_eq_ok
    (rules := msg.benv.stat.rules) (d := raw) hfork.rules_stateGas_none hprefix hgas hmax
  exact processCreateMessage_ok_of_processMessage_and_charge msg hprocess herror hcharge

/-- The settled world's projections: error, remaining gas, code and storage at the new
address, and every other account unchanged from the constructor's final state. -/
theorem liftCreatePost_facts (target : Adr) (raw : Devm) :
    (liftCreatePost target raw).error = raw.error ∧
    (liftCreatePost target raw).gasLeft = raw.gasLeft - raw.output.length * gasCodeDeposit ∧
    (liftCreatePost target raw).state.get target =
      { raw.state.get target with code := ⟨⟨raw.output⟩⟩ } ∧
    (∀ a, a ≠ target → (liftCreatePost target raw).state.get a = raw.state.get a) := by
  refine ⟨Devm.setCode_error _ _ _, rfl, ?_, fun a ha => ?_⟩
  · show (raw.state.setCode target _).get target = _
    unfold State.setCode
    rw [State.get_set_self]
  · show (raw.state.setCode target _).get a = _
    unfold State.setCode
    rw [State.get_set_ne _ (Ne.symm ha)]

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
  refine ⟨_, liftCreate_post hc hj msg hcodeAddress hcode hfork htransfer hrun herror hprefix
    hgas hmax, ?_, ?_, ?_⟩
  · unfold Devm.getCode Devm.getAcct
    rw [(liftCreatePost_facts _ raw).2.2.1]
    simp only [ByteArray.toList_eq_toList_data]
  · unfold Devm.getStor Devm.getAcct
    rw [(liftCreatePost_facts _ raw).2.2.1]
  · rw [(liftCreatePost_facts _ raw).1]
    exact herror

end Blanc.Lift
