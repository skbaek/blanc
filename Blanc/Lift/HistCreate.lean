import Blanc.Lift.HistAccessFacts
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.Create2Deploy
import Blanc.Lift.HistAccessWalkFacts

/-!
# Creation steps under historical rule facts

The forward (gas-exact) creation kit takes `CoveredFork`: its `SLOAD`/`SSTORE` steps charge the
EIP-2929 warm/cold schedule, its settlement assumes no EIP-161 touched sweep, and its `CREATE2`
step charges the EIP-3860 init-code words. This module states the same steps from the rule facts
they read.

* the `SLOAD`/`SSTORE` charges `sloadCostH`/`sstoreCostH` and forward steps (`rx_sload_selH`,
  `rx_sstoreH`, ...) are in `HistAccessWalk.lean`; here, their pricing facts
  (`sstoreCostH_congr`, `sloadCostH_muir_eq`, `sstoreCostH_muir_le`, `sloadCostH_le`,
  `sstoreCostH_le`);
* `processMessage_ok_of_execH`, `liftCreate_postH`, `liftCreate_okH` — the lifted creation
  settles under `rules.stateGas = none` alone; under the EIP-161 sweep the settled machine is the
  constructor's with the target's touch recorded (`Devm.recordTouch`), which moves no state;
* `create2ChargeH`, `Xinst.step_create2_spawnH`, `create2_runCompiledH` — `CREATE2` with the
  init-code word charge and size bound only where `creation.initCodeLimit` holds, from
  `rules.stateGas = none` and `rules.op.create2 = true`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## `SLOAD` and `SSTORE` pricing facts

The charges `sloadCostH`/`sstoreCostH` and their forward steps live in
`HistAccessWalk.lean`. -/

/-- Historical SSTORE pricing depends only on the selected price inputs. -/
theorem sstoreCostH_congr {sevm : Sevm} {d1 d2 : Devm} (key value : B256)
    (hkeys : d1.accessedStorageKeys = d2.accessedStorageKeys)
    (hstor : Devm.getStor d1 sevm.currentTarget = Devm.getStor d2 sevm.currentTarget)
    (hcreated : d1.createdAccounts = d2.createdAccounts) :
    sstoreCostH sevm d1 key value = sstoreCostH sevm d2 key value := by
  unfold sstoreCostH storageAccessCostH
  rw [hkeys]
  have horig : d1.getOrigStorVal sevm sevm.currentTarget key =
      d2.getOrigStorVal sevm sevm.currentTarget key := by
    unfold Devm.getOrigStorVal
    rw [hcreated]
  rw [horig]
  show sstoreRegimeGasCost _ _ _ _ _ ((Devm.getStor d1 sevm.currentTarget).get key) = _
  rw [hstor]
  rfl

/-- The actual flat Muir Glacier read charge. -/
theorem sloadCostH_muir_eq {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules)
    (base : Devm) (key : B256) : sloadCostH sevm base key = 800 := by
  unfold sloadCostH
  rw [hmuir]
  rfl

/-- The actual Muir Glacier net-metered write charge is at most 20,000. -/
theorem sstoreCostH_muir_le {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules)
    (base : Devm) (key value : B256) : sstoreCostH sevm base key value ≤ 20000 := by
  unfold sstoreCostH storageAccessCostH
  rw [hmuir]
  unfold sstoreRegimeGasCost
  change (if _ then if _ then 0 + 20000 else 0 + 5000 else 0 + 800) ≤ 20000
  split_ifs <;> decide

/-- Under a flat `SLOAD` price of at most 2100 (every historical schedule), one `SLOAD` costs at
most 2100. -/
theorem sloadCostH_le {sevm : Sevm} {base : Devm} {key : B256}
    (flat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 2100) :
    sloadCostH sevm base key ≤ 2100 := by
  unfold sloadCostH
  split
  · unfold sloadCost; split <;> decide
  · exact flat _ ‹_›

/-- Under the same fact, one `SSTORE` costs at most 22100. -/
theorem sstoreCostH_le {sevm : Sevm} {devm : Devm} {key value : B256}
    (flat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 2100) :
    sstoreCostH sevm devm key value ≤ 22100 := by
  unfold sstoreCostH storageAccessCostH sstoreRegimeGasCost
  cases hacc : sevm.benvStat.rules.access with
  | flat g =>
    have := flat g hacc
    split_ifs <;> (try simp only [gasStorageSet, gasStorageUpdate]) <;> omega
  | eip2929 =>
    split_ifs <;>
      (try simp only [gasStorageSet, gasStorageUpdate, gasColdSload, gasWarmAccess]) <;> omega

/-! ## Settling a lifted creation -/

/-- A successful raw `exec` with no frame error settles as the ordinary message result with the
current target's EIP-161 touch recorded (the identity when the rules do not sweep). No rule fact
is assumed. -/
theorem processMessage_ok_of_execH
    {msg : Msg} {benv : Benv} {post : Devm}
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hcodeAddress : msg.codeAddress = .none)
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post)
    (herror : post.error = .none) :
    processMessage msg = .ok (post.recordTouch msg.benv.stat.rules true msg.currentTarget) := by
  unfold processMessage runFrame Frame.enter Frame.ofCall
  rw [htransfer]
  unfold executeCode.enter
  simp only [Msg.withBenv, hcodeAddress]
  unfold Frame.settle Frame.settleMsg
  simp only [Msg.withBenv, hcodeAddress] at hexec
  rw [hexec]
  simp only [Bool.false_eq_true, ↓reduceIte, processMessage.settle, executeCode.handleErrorWith_ok,
    Except.bind_ok, herror, Option.isSome_none]

/-- Code deposit and installation preserve the constructor bookkeeping. -/
theorem liftCreatePost_meta (t : Adr) (raw : Devm) :
    (liftCreatePost t raw).accountsToDelete = raw.accountsToDelete ∧
    (liftCreatePost t raw).refundCounter = raw.refundCounter ∧
    (liftCreatePost t raw).createdAccounts = raw.createdAccounts := ⟨rfl, rfl, rfl⟩

/-- EIP-161 touch recording preserves deletion, refund, creation and gas projections. -/
theorem recordTouch_meta (rules : ForkRules) (cond : Bool) (adr : Adr) (d : Devm) :
    (d.recordTouch rules cond adr).accountsToDelete = d.accountsToDelete ∧
    (d.recordTouch rules cond adr).refundCounter = d.refundCounter ∧
    (d.recordTouch rules cond adr).createdAccounts = d.createdAccounts ∧
    (d.recordTouch rules cond adr).gasLeft = d.gasLeft := ⟨rfl, rfl, rfl, rfl⟩

/-- **Deploying lifted creation code, exactly, from `rules.stateGas = none`.**  As
`liftCreate_post`, with the settled machine `raw` with the new target's touch recorded: that
moves only `touchedAccounts`, and is the identity when the rules do not sweep. -/
theorem liftCreate_postH {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    (msg : Msg) (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hsg : msg.benv.stat.rules.stateGas = none) {benv : Benv} {raw : Devm}
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hrun : SProg.RunExact c.prog (initSevm (createSeed msg benv))
      (initDevm (createSeed msg benv)) raw)
    (herror : raw.error = .none) (hprefix : raw.output.head? ≠ some 0xEF)
    (hgas : raw.output.length * gasCodeDeposit ≤ raw.gasLeft)
    (hmax : raw.output.length ≤ msg.benv.stat.rules.code.maxCodeSize) :
    processCreateMessage msg = .ok (liftCreatePost msg.currentTarget
      (raw.recordTouch msg.benv.stat.rules true msg.currentTarget)) := by
  have hstat : (initSevm (createSeed msg benv)).benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  obtain ⟨exc⟩ := lift_exact_noStateGas hc hj (sevm := initSevm (createSeed msg benv)) hcode
    (by rw [hstat]; exact hsg) hrun
  have hexec : exec (initEvm (createSeed msg benv)) = .ok raw :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
  have hprocess : processMessage (processCreateMessage.msg msg) =
      .ok (raw.recordTouch msg.benv.stat.rules true msg.currentTarget) :=
    processMessage_ok_of_execH htransfer hcodeAddress hexec herror
  have hcharge := processCreateMessage.chargeCodeGas_legacy_eq_ok
    (rules := msg.benv.stat.rules) (d := raw.recordTouch msg.benv.stat.rules true msg.currentTarget)
    hsg hprefix hgas hmax
  exact processCreateMessage_ok_of_processMessage_and_charge msg hprocess herror hcharge

/-- **Deploying lifted creation code, from `rules.stateGas = none`.**  The conclusion of
`liftCreate_ok`: the creation succeeds, installs `raw.output` at `msg.currentTarget`, and keeps
the exact normalized storage there. -/
theorem liftCreate_okH {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    (msg : Msg) (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hsg : msg.benv.stat.rules.stateGas = none) {benv : Benv} {raw : Devm}
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
  let d := raw.recordTouch msg.benv.stat.rules true msg.currentTarget
  have facts := liftCreatePost_facts msg.currentTarget d
  refine ⟨_, liftCreate_postH hc hj msg hcodeAddress hcode hsg htransfer hrun herror hprefix
    hgas hmax, ?_, ?_, ?_⟩
  · unfold Devm.getCode Devm.getAcct
    rw [facts.2.2.1]
    simp only [Acct.clearIfEmpty_code, ByteArray.toList_eq_toList_data, d,
      Devm.recordTouch_output]
  · unfold Devm.getStor Devm.getAcct
    rw [facts.2.2.1]
    simp only [d, Devm.recordTouch_state, Devm.recordTouch_output]
  · rw [facts.1]
    exact herror

/-! ## `CREATE2` -/

/-- `CREATE2`'s own charge from memory `M` under the frame's rules: access, init-code hashing,
memory expansion, and the init-code word charge only where `creation.initCodeLimit` holds. -/
def create2ChargeH (sevm : Sevm) (M : Mem) (i sz : B256) : Nat :=
  sevm.benvStat.rules.gas.createAccess + gasKeccak256Word * ceilDiv sz.toNat 32 +
    (calculateMemoryGasCost (memExtsSize M.size [⟨i.toNat, sz.toNat⟩]) -
      calculateMemoryGasCost M.size) +
    (if sevm.benvStat.rules.creation.initCodeLimit then gasInitCodeWordCost * ceilDiv sz.toNat 32
      else 0)

theorem create2ChargeH_of_initCodeLimit {sevm : Sevm} {M : Mem} {i sz : B256}
    (h : sevm.benvStat.rules.creation.initCodeLimit = true) :
    create2ChargeH sevm M i sz = create2Charge sevm M i sz := by
  unfold create2ChargeH create2Charge
  rw [h]
  rfl

/-- An admitted CREATE2 spawn from the rule facts it reads: `rules.stateGas = none`, `CREATE2`
available, and the init-code size bound only where `creation.initCodeLimit` holds. -/
theorem Xinst.step_create2_spawnH_of_nonce_code {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {v i sz salt : B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hcreate2 : sevm.benvStat.rules.op.create2 = true)
    (hmax : sevm.benvStat.rules.creation.initCodeLimit = true →
      sz.toNat ≤ sevm.benvStat.rules.code.maxInitCodeSize)
    (hstatic : sevm.isStatic = false)
    (hbal : ¬ (b.state.get sevm.currentTarget).bal < v)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetNoCollision (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))) :
    Xinst.step sevm (St b (v :: i :: sz :: salt :: S) M
        (G + create2ChargeH sevm M i sz)) .create2 =
      .spawn (Frame.ofCreate (createMsg sevm
          (create2Prepared sevm b S M G i sz
            (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
          (except64th G) v
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))
          (create2InitCode M i sz)))
        (.create (create2Prepared sevm b S M G i sz
            (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))) := by
  have hc : chargeGas (create2ChargeH sevm M i sz) (St b S M (G + create2ChargeH sevm M i sz)) =
      .ok (St b S M G) := by
    rw [chargeGas_eq_ok (by simp only [St.gasLeft]; omega)]
    simp only [St.stack, St.memory, St.gasLeft, Nat.add_sub_cancel]
    rfl
  simp only [Xinst.step, hsg, hcreate2, ↓reduceIte]
  rw [show (St b (v :: i :: sz :: salt :: S) M (G + create2ChargeH sevm M i sz)).pop =
    .ok (v, St b (i :: sz :: salt :: S) M (G + create2ChargeH sevm M i sz)) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (i :: sz :: salt :: S) M (G + create2ChargeH sevm M i sz)).popToNat =
    .ok (i.toNat, St b (sz :: salt :: S) M (G + create2ChargeH sevm M i sz)) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (sz :: salt :: S) M (G + create2ChargeH sevm M i sz)).popToNat =
    .ok (sz.toNat, St b (salt :: S) M (G + create2ChargeH sevm M i sz)) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (salt :: S) M (G + create2ChargeH sevm M i sz)).pop =
    .ok (salt, St b S M (G + create2ChargeH sevm M i sz)) from rfl]
  simp only [Except.bind_ok]
  have hc' : chargeGas (sevm.benvStat.rules.gas.createAccess +
      gasKeccak256Word * ceilDiv sz.toNat 32 +
      (St b S M (G + create2ChargeH sevm M i sz)).extCost [(i.toNat, sz.toNat)] +
      (if sevm.benvStat.rules.creation.initCodeLimit = true then
        gasInitCodeWordCost * ceilDiv sz.toNat 32 else 0))
      (St b S M (G + create2ChargeH sevm M i sz)) =
      .ok (St b S M G) := hc
  rw [hc']
  simp only [Except.bind_ok]
  show genericCreate.step _ _ _ _ _ _ = _
  simp only [genericCreate.step, Except.assert, ite_eq_left hmax, assertDynamic, hstatic,
    Bool.not_false, ite_true, Except.bind_ok]
  rw [ite_eq_right, ite_eq_right]
  · rfl
  · exact fun h => by
      rcases h with h | h
      · exact h hfresh.1
      · exact h hfresh.2
  · exact fun h => by
      rcases h with h | h | h
      · exact hbal h
      · exact hnonce h
      · exact hdepth h

/-- Compatibility wrapper retaining the original nonce/code/storage target premise. -/
theorem Xinst.step_create2_spawnH {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {v i sz salt : B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hcreate2 : sevm.benvStat.rules.op.create2 = true)
    (hmax : sevm.benvStat.rules.creation.initCodeLimit = true →
      sz.toNat ≤ sevm.benvStat.rules.code.maxInitCodeSize)
    (hstatic : sevm.isStatic = false)
    (hbal : ¬ (b.state.get sevm.currentTarget).bal < v)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))) :
    Xinst.step sevm (St b (v :: i :: sz :: salt :: S) M
        (G + create2ChargeH sevm M i sz)) .create2 =
      .spawn (Frame.ofCreate (createMsg sevm
          (create2Prepared sevm b S M G i sz
            (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
          (except64th G) v
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))
          (create2InitCode M i sz)))
        (.create (create2Prepared sevm b S M G i sz
            (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))) := by
  exact Xinst.step_create2_spawnH_of_nonce_code hsg hcreate2 hmax hstatic hbal hnonce hdepth
    ⟨hfresh.1, hfresh.2.1⟩

/-- **`CREATE2`, closed, from rule facts and its actual nonce/code collision check.**
Charging `create2ChargeH`; no initial target-storage premise is needed. -/
theorem create2_runCompiledH_of_nonce_code {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {v i sz salt : B256} {child : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hcreate2 : sevm.benvStat.rules.op.create2 = true)
    (hmax : sevm.benvStat.rules.creation.initCodeLimit = true →
      sz.toNat ≤ sevm.benvStat.rules.code.maxInitCodeSize)
    (hstatic : sevm.isStatic = false)
    (hbal : ¬ (b.state.get sevm.currentTarget).bal < v)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetNoCollision (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
    (hchild : processCreateMessage (createMsg sevm
        (create2Prepared sevm b S M G i sz
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        (except64th G) v
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))
        (create2InitCode M i sz)) = .ok child)
    (herror : child.error = none) (hroom : S.length < 1024) :
    Ninst.RunCompiled sevm (St b (v :: i :: sz :: salt :: S) M
        (G + create2ChargeH sevm M i sz)) (.exec .create2)
      (create2Post (create2Prepared sevm b S M G i sz
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        child (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))) := by
  obtain ⟨xl, hfill, hrf⟩ := of_processCreateMessage _ _ hchild
  refine ⟨xl, hfill, fun pc => XStep.run_toStep.mpr ?_⟩
  show XStep.Run (Xinst.step _ _ _) xl _
  rw [Xinst.step_create2_spawnH_of_nonce_code hsg hcreate2 hmax hstatic hbal hnonce hdepth hfresh]
  refine ⟨_, hrf, ?_⟩
  simp only [Resume.run, liftToExecution, Except.bind_ok, herror, Option.isSome_none,
    Bool.false_eq_true, ite_false]
  rw [Devm.push_eq_ok (by exact hroom)]
  rfl

/-- Compatibility wrapper retaining the original nonce/code/storage target premise. -/
theorem create2_runCompiledH {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {v i sz salt : B256} {child : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hcreate2 : sevm.benvStat.rules.op.create2 = true)
    (hmax : sevm.benvStat.rules.creation.initCodeLimit = true →
      sz.toNat ≤ sevm.benvStat.rules.code.maxInitCodeSize)
    (hstatic : sevm.isStatic = false)
    (hbal : ¬ (b.state.get sevm.currentTarget).bal < v)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
    (hchild : processCreateMessage (createMsg sevm
        (create2Prepared sevm b S M G i sz
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        (except64th G) v
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))
        (create2InitCode M i sz)) = .ok child)
    (herror : child.error = none) (hroom : S.length < 1024) :
    Ninst.RunCompiled sevm (St b (v :: i :: sz :: salt :: S) M
        (G + create2ChargeH sevm M i sz)) (.exec .create2)
      (create2Post (create2Prepared sevm b S M G i sz
          (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
        child (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))) := by
  exact create2_runCompiledH_of_nonce_code hsg hcreate2 hmax hstatic hbal hnonce hdepth
    ⟨hfresh.1, hfresh.2.1⟩ hchild herror hroom

end Blanc.Lift
