import Blanc.Lift.HistAccessWalk
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.Create2Deploy
import Blanc.Lift.HistAccessWalkFacts

/-!
# Creation steps under historical rule facts

The forward (gas-exact) creation kit takes `CoveredFork`: its `SLOAD`/`SSTORE` steps charge the
EIP-2929 warm/cold schedule, its settlement assumes no EIP-161 touched sweep, and its `CREATE2`
step charges the EIP-3860 init-code words. This module states the same steps from the rule facts
they read.

* `sloadCostH`, `sstoreCostH` — the charges under the frame's actual access schedule and
  `SSTORE` regime (legacy, flat net-metered, EIP-2929), equal to `sloadCost`/`sstoreCost` under
  EIP-2929 (`sloadCostH_of_eip2929`);
* `Ninst.runCompiled_sload_selectedH`, `Ninst.runCompiled_sstore_selectedH`, `rx_sload_selH`,
  `rx_sstoreH` — forward steps over `afterSloadH`/`afterSstoreH`, from `rules.stateGas = none`
  (the `SSTORE` stipend sentry is required only where the rules have it);
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

/-! ## `SLOAD` and `SSTORE`, forward -/

/-- The charge of one `SLOAD` under the frame's actual access schedule. -/
def sloadCostH (sevm : Sevm) (base : Devm) (key : B256) : Nat :=
  match sevm.benvStat.rules.access with
  | .eip2929 => sloadCost sevm base key
  | .flat g => g.sload

theorem sloadCostH_of_eip2929 {sevm : Sevm} {base : Devm} {key : B256}
    (access : sevm.benvStat.rules.access = .eip2929) :
    sloadCostH sevm base key = sloadCost sevm base key := by
  unfold sloadCostH
  rw [access]

/-- The access part of one `SSTORE` charge: the cold surcharge under EIP-2929, nothing under
flat access. -/
def storageAccessCostH (sevm : Sevm) (devm : Devm) (key : B256) : Nat :=
  match sevm.benvStat.rules.access with
  | .flat _ => 0
  | .eip2929 =>
    if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ devm.accessedStorageKeys then 0
    else gasColdSload

/-- The charge of one `SSTORE` (`stateGas = none` lane) under the frame's actual access schedule
and `SSTORE` regime. -/
def sstoreCostH (sevm : Sevm) (devm : Devm) (key value : B256) : Nat :=
  sstoreRegimeGasCost sevm.benvStat.rules.sstore sevm.benvStat.rules.access
    (storageAccessCostH sevm devm key) value
    (devm.getOrigStorVal sevm sevm.currentTarget key) (devm.getStorVal sevm.currentTarget key)

theorem afterSloadH_state (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).state = base.state := by
  unfold afterSloadH afterSload
  split
  · split <;> rfl
  · rfl

theorem afterSstoreH_state (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).state =
      base.state.setStorVal sevm.currentTarget key value := by
  unfold afterSstoreH storageAccessH
  split
  · rfl
  · split <;> rfl

/-- One exact `SLOAD` under the frame's actual access schedule, from `rules.stateGas = none`. -/
theorem Ninst.runCompiled_sload_selectedH
    {sevm : Sevm} {base : Devm} {key value : B256}
    {stack : List B256} {memory : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hvalue : base.getStorVal sevm.currentTarget key = value)
    (hroom : stack.length < 1024) :
    Ninst.RunCompiled sevm
      (base.setMach ⟨key :: stack, memory, G + sloadCostH sevm base key, base.stateGas⟩)
      (.reg .sload)
      ((afterSloadH sevm base key).setMach ⟨value :: stack, memory, G, base.stateGas⟩) := by
  cases access : sevm.benvStat.rules.access with
  | eip2929 =>
    rw [sloadCostH_of_eip2929 access, afterSloadH_of_eip2929 access]
    by_cases hwarm : (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys
    · rw [sloadCost, ite_eq_left hwarm, afterSload, ite_eq_left hwarm]
      exact Ninst.runCompiled_sload_warm (k := key) (v := value) (s := stack) (G := G)
        hsg access rfl hwarm hvalue (by simp only [Devm.gasLeft_setMach, gasWarmAccess]) hroom
    · rw [sloadCost, ite_eq_right hwarm, afterSload, ite_eq_right hwarm]
      have hcomm : ∀ (m m' : Mach), (addAccessedStorageKey (base.setMach m) sevm.currentTarget
          key).setMach m' = (addAccessedStorageKey base sevm.currentTarget key).setMach m' :=
        fun _ _ => rfl
      simpa only [hcomm, Devm.memory_setMach, Devm.stateGas_setMach] using
        (Ninst.runCompiled_sload_cold
          (devm := base.setMach ⟨key :: stack, memory, G + gasColdSload, base.stateGas⟩)
          (k := key) (v := value) (s := stack) (G := G) hsg access rfl hwarm
          (by simpa only [Devm.getStorVal_setMach] using hvalue)
          (by simp only [Devm.gasLeft_setMach, gasColdSload]) hroom)
  | flat g =>
    subst hvalue
    have hbal := BenvStat.bal_none_of_stateGas_none hsg
    refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
    simp only [Rinst.runCore, access, Devm.balReadStorage_of_bal_none hbal, sloadCostH,
      afterSloadH]
    rw [Devm.pop_eq_ok rfl]
    simp only [bind, Except.bind]
    rw [chargeGas_eq_ok (by simp only [Devm.gasLeft_setMach]; omega)]
    simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.stack_setMach, Nat.add_sub_cancel]
    rw [Devm.push_eq_ok (by simpa only [Devm.stack_setMach] using hroom)]
    rfl

/-- One exact `SSTORE` under the frame's actual access schedule and `SSTORE` regime, from
`rules.stateGas = none`. The stipend sentry is required only under rules that have it. -/
theorem Ninst.runCompiled_sstore_selectedH
    {sevm : Sevm} {base : Devm} {key value : B256}
    {stack : List B256} {memory : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hsentry : sevm.benvStat.rules.sstore.stipendSentry = true →
      gCallStipend < G + sstoreCostH sevm base key value)
    (hstatic : sevm.isStatic = false) :
    Ninst.RunCompiled sevm
      (base.setMach ⟨key :: value :: stack, memory, G + sstoreCostH sevm base key value,
        base.stateGas⟩)
      (.reg .sstore)
      ((afterSstoreH sevm base key value).setMach ⟨stack, memory, G, base.stateGas⟩) := by
  have hbal := BenvStat.bal_none_of_stateGas_none hsg
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  have hO : ∀ m : Mach, (base.setMach m).getOrigStorVal sevm sevm.currentTarget key =
      base.getOrigStorVal sevm sevm.currentTarget key := fun _ => rfl
  have hC : ∀ m : Mach, (base.setMach m).getStorVal sevm.currentTarget key =
      base.getStorVal sevm.currentTarget key := fun _ => rfl
  have hK : ∀ m : Mach, (base.setMach m).accessedStorageKeys = base.accessedStorageKeys :=
    fun _ => rfl
  have hR : ∀ m : Mach, (base.setMach m).refundCounter = base.refundCounter := fun _ => rfl
  have hA : ∀ (m m' : Mach), (addAccessedStorageKey (base.setMach m) sevm.currentTarget
      key).setMach m' = (addAccessedStorageKey base sevm.currentTarget key).setMach m' :=
    fun _ _ => rfl
  have hG : ∀ (m : Mach) (rc : Int), ((base.setMach m).withRefundCounter rc).gasLeft =
      m.gasLeft := fun _ _ => rfl
  have hG' : ∀ (m : Mach) (rc : Int), ((addAccessedStorageKey (base.setMach m)
      sevm.currentTarget key).withRefundCounter rc).gasLeft = m.gasLeft := fun _ _ => rfl
  rcases hss : sevm.benvStat.rules.sstore with ⟨nm, ss⟩
  rw [hss] at hsentry
  unfold sstoreCostH storageAccessCostH at hsentry ⊢
  unfold afterSstoreH storageAccessH sstoreRefundH
  cases access : sevm.benvStat.rules.access <;> cases nm <;> cases ss <;>
  · simp only [Rinst.runCore, hsg, hss, access, Devm.balReadStorage_of_bal_none hbal,
      Devm.balReadAccount_of_bal_none hbal] at hsentry ⊢
    rw [Devm.pop_eq_ok rfl]
    simp only [bind, Except.bind]
    rw [Devm.pop_eq_ok rfl]
    simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, hO, hC, hK, hR]
    try (by_cases hw : (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys <;>
      simp only [hw, ite_true, ite_false, not_true_eq_false, not_false_eq_true] at hsentry ⊢)
    all_goals
      simp only [Except.assert, Bool.false_eq_true, false_implies, forall_const,
        ite_true] at hsentry ⊢
      try simp only [hsentry, ite_true]
      try simp only [sstoreRegimeGasCost, ↓reduceIte]
      rw [chargeGas_eq_ok (Nat.le_add_left _ _)]
      simp only [assertDynamic, Except.assert, hstatic, Bool.not_false, ↓reduceIte, hG, hG',
        Nat.add_sub_cancel]
      rfl

/-- `SLOAD` of any key in an exact run, under the frame's actual access schedule. -/
theorem rx_sload_selH {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {o : Outcome}
    {S : List B256} {M : Mem} {G : Nat} {k' : B256}
    (hsg : sevm.benvStat.rules.stateGas = none) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (afterSloadH sevm b k') (b.getStorVal sevm.currentTarget k' :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + sloadCostH sevm b k'))
      (.next (.reg .sload) f) o := by
  refine .next ?_ k
  have h := Ninst.runCompiled_sload_selectedH (sevm := sevm) (base := b) (key := k') (stack := S)
    (memory := M) (G := G) hsg rfl hroom
  simpa only [St, afterSloadH_stateGas] using h

/-- `SSTORE` in an exact run, under the frame's actual access schedule and `SSTORE` regime. -/
theorem rx_sstoreH {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {o : Outcome}
    {S : List B256} {M : Mem} {G : Nat} {k' v : B256}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hsentry : sevm.benvStat.rules.sstore.stipendSentry = true →
      gCallStipend < G + sstoreCostH sevm b k' v)
    (hstatic : sevm.isStatic = false)
    (k : SFunc.RunExact fs sevm (St (afterSstoreH sevm b k' v) S M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: v :: S) M (G + sstoreCostH sevm b k' v))
      (.next (.reg .sstore) f) o := by
  refine .next (Ninst.runCompiled_sstore_selectedH hsg hsentry hstatic) ?_
  rw [← afterSstoreH_stateGas sevm b k' v]
  exact k

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

/-- `Xinst.step_create2_spawn` from the rule facts it reads: `rules.stateGas = none`, `CREATE2`
available, and the init-code size bound only where `creation.initCodeLimit` holds. -/
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
      · exact h hfresh.2.1
  · exact fun h => by
      rcases h with h | h | h
      · exact hbal h
      · exact hnonce h
      · exact hdepth h

/-- **`CREATE2`, closed, from rule facts.**  As `create2_runCompiled`, charging
`create2ChargeH`. -/
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
  obtain ⟨xl, hfill, hrf⟩ := of_processCreateMessage _ _ hchild
  refine ⟨xl, hfill, fun pc => XStep.run_toStep.mpr ?_⟩
  show XStep.Run (Xinst.step _ _ _) xl _
  rw [Xinst.step_create2_spawnH hsg hcreate2 hmax hstatic hbal hnonce hdepth hfresh]
  refine ⟨_, hrf, ?_⟩
  simp only [Resume.run, liftToExecution, Except.bind_ok, herror, Option.isSome_none,
    Bool.false_eq_true, ite_false]
  rw [Devm.push_eq_ok (by exact hroom)]
  rfl

end Blanc.Lift
