import Blanc.Lift.UniswapV2Factory.CreatePairMemory
import Blanc.Lift.UniswapV2Pair.Creation.DeployInit
import Blanc.Lift.UniswapV2Pair.InitializeLiveH
import Blanc.Lift.HistCallFlat
import Blanc.Lift.HistSstoreRefund
import Blanc.Lift.HistAccessMeta

/-!
# The two spawns of `createPair`, under historical rule facts

* `pair_create_postH`: the Pair's creation message settles at the named machine: the constructor's
  final machine `UniswapV2Pair.Creation.ctorPostH` with the target's EIP-161 touch recorded, and the runtime installed
  (`liftCreatePost`). This is `pair_createH` with its post-state named.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune Blanc.Lift

/-- **The Pair's creation, with its settled machine named.**  As `pair_createH`, for a creation
message whose gas is `Gc + UniswapV2Pair.Creation.ctorCostH` over its own frame and whose leftover `Gc` pays the code
deposit: `processCreateMessage` returns `liftCreatePost` over the constructor's final machine with
the target's touch recorded. -/
theorem pair_create_postH (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = UniswapV2Pair.Creation.code)
    (hsg : msg.benv.stat.rules.stateGas = none) (hchain : msg.benv.stat.rules.op.chainId = true)
    (hshifts : msg.benv.stat.rules.op.shifts = true)
    (hstatic : msg.isStatic = false)
    (hmax : 11293 ≤ msg.benv.stat.rules.code.maxCodeSize) (Gc : Nat)
    (hgas : msg.gas = Gc + UniswapV2Pair.Creation.ctorCostH (initSevm (createSeed msg (processCreateMessage.msg msg).benv))
      (initDevm (createSeed msg (processCreateMessage.msg msg).benv)))
    (hdeposit : 11293 * gasCodeDeposit ≤ Gc) :
    processCreateMessage msg = .ok (liftCreatePost msg.currentTarget
      ((UniswapV2Pair.Creation.ctorPostH (initSevm (createSeed msg (processCreateMessage.msg msg).benv))
        (initDevm (createSeed msg (processCreateMessage.msg msg).benv)) Gc).recordTouch
        msg.benv.stat.rules true msg.currentTarget)) := by
  have htransfer : (processCreateMessage.msg msg).benvAfterTransfer =
      .ok (processCreateMessage.msg msg).benv := Msg.benvAfterTransfer_of_value_zero hvalue
  let benv := (processCreateMessage.msg msg).benv
  have hstat : (initSevm (createSeed msg benv)).benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have hempty : Devm.getStor (initDevm (createSeed msg benv))
      (initSevm (createSeed msg benv)).currentTarget = Stor.empty := by
    show benv.state.getStor msg.currentTarget = _
    rw [benvAfterTransfer_ok_getStor htransfer _ (Or.inl hvalue),
      processCreateMessage_msg_getStor_currentTarget]
  have hstor : ∀ x, (Devm.getStor (initDevm (createSeed msg benv))
      (initSevm (createSeed msg benv)).currentTarget).get x = 0 := fun x => by
    rw [hempty]
    rfl
  have hrun := UniswapV2Pair.Creation.ctor_run_postH (sevm := initSevm (createSeed msg benv)) (by rw [hstat]; exact hsg)
    (by rw [hstat]; exact hchain) (by rw [hstat]; exact hshifts) hstatic hcode hvalue hstor Gc
  have hpre : St (initDevm (createSeed msg benv)) [] Mem.empty
      (Gc + UniswapV2Pair.Creation.ctorCostH (initSevm (createSeed msg benv)) (initDevm (createSeed msg benv))) =
      initDevm (createSeed msg benv) :=
    pre_eq_St rfl rfl (by rw [← hgas]; rfl)
  rw [hpre] at hrun
  obtain ⟨hout, herr, -, hleft⟩ := UniswapV2Pair.Creation.ctorPostH_facts
    (initSevm (createSeed msg benv)) (initDevm (createSeed msg benv)) Gc
  have hwin : (UniswapV2Pair.Creation.ctorPostH (initSevm (createSeed msg benv)) (initDevm (createSeed msg benv))
      Gc).output = Blanc.Lift.UniswapV2Pair.code.toList := by
    rw [hout, UniswapV2Pair.Creation.runtimeWindow_eq]
  have hlen : (UniswapV2Pair.Creation.ctorPostH (initSevm (createSeed msg benv)) (initDevm (createSeed msg benv))
      Gc).output.length = 11293 := by
    rw [hout, UniswapV2Pair.Creation.runtimeWindow_length]
  exact liftCreate_postH UniswapV2Pair.Creation.cert_check UniswapV2Pair.Creation.jumps_ok msg
    hcodeAddress hcode hsg htransfer hrun (by rw [herr]; rfl)
    (by rw [hwin]; exact UniswapV2Pair.Creation.runtime_head)
    (by rw [hlen, hleft]; exact hdeposit) (by rw [hlen]; exact hmax)

/-! ## World facts of the two children -/

theorem liftCreatePost_meta (t : Adr) (raw : Devm) :
    (liftCreatePost t raw).accountsToDelete = raw.accountsToDelete ∧
    (liftCreatePost t raw).refundCounter = raw.refundCounter ∧
    (liftCreatePost t raw).createdAccounts = raw.createdAccounts := ⟨rfl, rfl, rfl⟩

theorem recordTouch_meta (rules : ForkRules) (cond : Bool) (adr : Adr) (d : Devm) :
    (d.recordTouch rules cond adr).accountsToDelete = d.accountsToDelete ∧
    (d.recordTouch rules cond adr).refundCounter = d.refundCounter ∧
    (d.recordTouch rules cond adr).createdAccounts = d.createdAccounts ∧
    (d.recordTouch rules cond adr).gasLeft = d.gasLeft := ⟨rfl, rfl, rfl, rfl⟩


theorem afterSloadH_createdAccounts (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).createdAccounts = base.createdAccounts := by
  unfold afterSloadH afterSload
  split
  · split <;> rfl
  · rfl

/-- A store at a created account never lowers the refund counter (its original storage is
zero). -/
theorem afterSstoreH_refund_ge_of_created {sevm : Sevm} {base : Devm} {key value : B256}
    (hflat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 5000)
    (hcreated : sevm.currentTarget ∈ base.createdAccounts) :
    base.refundCounter ≤ (afterSstoreH sevm base key value).refundCounter :=
  afterSstoreH_refundCounter_ge sevm base key value hflat
    (Or.inl (by unfold Devm.getOrigStorVal; simp only [hcreated, ↓reduceIte]))

/-- What the Pair constructor's final machine keeps of its frame's entry machine: the accounts to
delete, the created accounts, every other account, and (at a created account) a refund counter at
least the entry's. -/
theorem ctorPostH_meta (sevm : Sevm) (d : Devm) (G : Nat)
    (hflat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 5000)
    (hcreated : sevm.currentTarget ∈ d.createdAccounts) :
    (UniswapV2Pair.Creation.ctorPostH sevm d G).accountsToDelete = d.accountsToDelete ∧
    (UniswapV2Pair.Creation.ctorPostH sevm d G).createdAccounts = d.createdAccounts ∧
    (∀ a, a ≠ sevm.currentTarget → (UniswapV2Pair.Creation.ctorPostH sevm d G).state.get a = d.state.get a) ∧
    d.refundCounter ≤ (UniswapV2Pair.Creation.ctorPostH sevm d G).refundCounter := by
  have c1 : (UniswapV2Pair.Creation.w1H sevm d).createdAccounts = d.createdAccounts :=
    afterSstoreH_createdAccounts _ _ _ _
  have c2 : (UniswapV2Pair.Creation.w2H sevm d).createdAccounts = d.createdAccounts :=
    (afterSstoreH_createdAccounts _ _ _ _).trans c1
  have c3 : (UniswapV2Pair.Creation.w3H sevm d).createdAccounts = d.createdAccounts :=
    (afterSloadH_createdAccounts _ _ _).trans c2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (UniswapV2Pair.Creation.w4H sevm d).accountsToDelete = _
    simp only [UniswapV2Pair.Creation.w4H, UniswapV2Pair.Creation.w3H, UniswapV2Pair.Creation.w2H,
      UniswapV2Pair.Creation.w1H, afterSstoreH_accountsToDelete, afterSloadH_accountsToDelete]
  · show (UniswapV2Pair.Creation.w4H sevm d).createdAccounts = _
    exact (afterSstoreH_createdAccounts _ _ _ _).trans c3
  · intro a ha
    show (UniswapV2Pair.Creation.w4H sevm d).state.get a = _
    simp only [UniswapV2Pair.Creation.w4H, UniswapV2Pair.Creation.w3H, UniswapV2Pair.Creation.w2H,
      UniswapV2Pair.Creation.w1H, afterSstoreH_state, afterSloadH_state,
      State.setStorVal_get_ne _ (Ne.symm ha)]
  · show d.refundCounter ≤ (UniswapV2Pair.Creation.w4H sevm d).refundCounter
    have r1 := afterSstoreH_refund_ge_of_created (base := d) (key := 12) (value := 1) hflat hcreated
    have r2 := afterSstoreH_refund_ge_of_created (base := UniswapV2Pair.Creation.w1H sevm d)
      (key := 3) (value := UniswapV2Pair.Creation.domainSeparator sevm.benvStat.chainId.toB256
        sevm.currentTarget) hflat (by rw [c1]; exact hcreated)
    have r3 := afterSstoreH_refund_ge_of_created (base := UniswapV2Pair.Creation.w3H sevm d)
      (key := 5) (value := sevm.caller.toB256) hflat (by rw [c3]; exact hcreated)
    have r4 := afterSloadH_refundCounter sevm (UniswapV2Pair.Creation.w2H sevm d) 5
    simp only [UniswapV2Pair.Creation.w4H, UniswapV2Pair.Creation.w3H, UniswapV2Pair.Creation.w2H,
      UniswapV2Pair.Creation.w1H] at r1 r2 r3 r4 ⊢
    omega

/-- What `initialize`'s final machine keeps of its frame's entry machine: the accounts to delete,
the created accounts, every account's code, every other account, and (at a created account) a
refund counter at least the entry's. -/
theorem initializePublicPostH_meta (sevm : Sevm) (d : Devm) (R : List B256) (M : Mem) (G : Nat)
    (hflat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 5000)
    (hcreated : sevm.currentTarget ∈ d.createdAccounts) :
    (UniswapV2Pair.initializePublicPostH sevm d R M G).accountsToDelete = d.accountsToDelete ∧
    (UniswapV2Pair.initializePublicPostH sevm d R M G).createdAccounts = d.createdAccounts ∧
    (∀ a, (UniswapV2Pair.initializePublicPostH sevm d R M G).getCode a = d.getCode a) ∧
    (∀ a, a ≠ sevm.currentTarget →
      (UniswapV2Pair.initializePublicPostH sevm d R M G).state.get a = d.state.get a) ∧
    d.refundCounter ≤ (UniswapV2Pair.initializePublicPostH sevm d R M G).refundCounter := by
  let t0 := UniswapV2Pair.initializeToken0 sevm
  let t1 := UniswapV2Pair.initializeToken1 sevm
  let f := UniswapV2Pair.initializeFactoryBaseH sevm d
  let l0 := UniswapV2Pair.initializeLoaded0H sevm f
  let s0 := UniswapV2Pair.initializeStored0H sevm f t0
  let l1 := UniswapV2Pair.initializeLoaded1H sevm f t0
  have cf : f.createdAccounts = d.createdAccounts := afterSloadH_createdAccounts _ _ _
  have cl0 : l0.createdAccounts = d.createdAccounts := (afterSloadH_createdAccounts _ _ _).trans cf
  have cs0 : s0.createdAccounts = d.createdAccounts := (afterSstoreH_createdAccounts _ _ _ _).trans cl0
  have cl1 : l1.createdAccounts = d.createdAccounts := (afterSloadH_createdAccounts _ _ _).trans cs0
  have hpost : UniswapV2Pair.initializePublicPostH sevm d R M G =
      St (afterSstoreH sevm l1 7 (UniswapV2Pair.initializeWord1H sevm f t0 t1)) R M G := rfl
  have hs0 : s0 = afterSstoreH sevm l0 6 (UniswapV2Pair.initializeWord0 sevm f t0) := rfl
  have hl1 : l1 = afterSloadH sevm s0 7 := rfl
  have hl0 : l0 = afterSloadH sevm f 6 := rfl
  have hf : f = afterSloadH sevm d 5 := rfl
  rw [hpost]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (afterSstoreH sevm l1 7 _).accountsToDelete = _
    rw [afterSstoreH_accountsToDelete, hl1, afterSloadH_accountsToDelete, hs0,
      afterSstoreH_accountsToDelete, hl0, afterSloadH_accountsToDelete, hf,
      afterSloadH_accountsToDelete]
  · exact (afterSstoreH_createdAccounts _ _ _ _).trans cl1
  · intro a
    show (afterSstoreH sevm l1 7 _).getCode a = _
    rw [afterSstoreH_getCode, hl1, afterSloadH_getCode, hs0, afterSstoreH_getCode, hl0,
      afterSloadH_getCode, hf, afterSloadH_getCode]
  · intro a ha
    show (afterSstoreH sevm l1 7 _).state.get a = _
    rw [afterSstoreH_state, State.setStorVal_get_ne _ (Ne.symm ha), hl1, afterSloadH_state, hs0,
      afterSstoreH_state, State.setStorVal_get_ne _ (Ne.symm ha), hl0, afterSloadH_state, hf,
      afterSloadH_state]
  · show d.refundCounter ≤ (afterSstoreH sevm l1 7 _).refundCounter
    have r1 := afterSstoreH_refund_ge_of_created (base := l1) (key := 7)
      (value := UniswapV2Pair.initializeWord1H sevm f t0 t1) hflat (by rw [cl1]; exact hcreated)
    have r0 := afterSstoreH_refund_ge_of_created (base := l0) (key := 6)
      (value := UniswapV2Pair.initializeWord0 sevm f t0) hflat (by rw [cl0]; exact hcreated)
    rw [← hs0] at r0
    have e1 : l1.refundCounter = s0.refundCounter := by rw [hl1, afterSloadH_refundCounter]
    have e0 : l0.refundCounter = d.refundCounter := by
      rw [hl0, afterSloadH_refundCounter, hf, afterSloadH_refundCounter]
    omega

/-! ## The factory's `CREATE2` -/

/-- The creation message the factory's `CREATE2` builds from the world `b`, the stack below the
operands `S` and the gas `Y` left after the charge. -/
def pairCreateMsg (sevm : Sevm) (b : Devm) (S : List B256) (Y : Nat) : Msg :=
  createMsg sevm (create2Prepared sevm b S fm12 Y 0xa0 0x2d74 UniswapV2Pair.Creation.pairAddress)
    (except64th Y) 0 UniswapV2Pair.Creation.pairAddress UniswapV2Pair.Creation.code.toList

/-- The constructor frame of `pairCreateMsg`. -/
abbrev pairCtorSevm (sevm : Sevm) (b : Devm) (S : List B256) (Y : Nat) : Sevm :=
  initSevm (createSeed (pairCreateMsg sevm b S Y)
    (processCreateMessage.msg (pairCreateMsg sevm b S Y)).benv)

abbrev pairCtorDevm (sevm : Sevm) (b : Devm) (S : List B256) (Y : Nat) : Devm :=
  initDevm (createSeed (pairCreateMsg sevm b S Y)
    (processCreateMessage.msg (pairCreateMsg sevm b S Y)).benv)

/-- The constructor's charge in that frame. -/
def pairCtorCost (sevm : Sevm) (b : Devm) (S : List B256) (Y : Nat) : Nat :=
  UniswapV2Pair.Creation.ctorCostH (pairCtorSevm sevm b S Y) (pairCtorDevm sevm b S Y)

/-- The settled creation child. -/
def pairChild (sevm : Sevm) (b : Devm) (S : List B256) (Y : Nat) : Devm :=
  liftCreatePost UniswapV2Pair.Creation.pairAddress
    ((UniswapV2Pair.Creation.ctorPostH (pairCtorSevm sevm b S Y) (pairCtorDevm sevm b S Y)
      (except64th Y - pairCtorCost sevm b S Y)).recordTouch
      (pairCreateMsg sevm b S Y).benv.stat.rules true UniswapV2Pair.Creation.pairAddress)

/-- The factory frame after its `CREATE2`. -/
def pairCreate2Post (sevm : Sevm) (b : Devm) (S : List B256) (Y : Nat) : Devm :=
  create2Post (create2Prepared sevm b S fm12 Y 0xa0 0x2d74 UniswapV2Pair.Creation.pairAddress)
    (pairChild sevm b S Y) UniswapV2Pair.Creation.pairAddress

theorem muirRules {sevm : Sevm} (hfork : sevm.benvStat.fork = .muirGlacier) :
    sevm.benvStat.rules = Fork.ruleSet .muirGlacier := by
  rw [BenvStat.rules, hfork]

/-- The constructor costs at most 80,000 gas in the factory's creation frame at Muir Glacier. -/
theorem pairCtorCost_le {sevm : Sevm} (hfork : sevm.benvStat.fork = .muirGlacier) (b : Devm)
    (S : List B256) (Y : Nat) : pairCtorCost sevm b S Y ≤ 80000 :=
  UniswapV2Pair.Creation.ctorCostH_le _ _ (fun g h => by
    change sevm.benvStat.rules.access = _ at h
    rw [muirRules hfork, show (Fork.ruleSet .muirGlacier).access = .flat istanbulAccessGas from rfl]
      at h
    cases h
    decide)

/-- **The factory's `CREATE2` of the Pair, at Muir Glacier.**  From the factory frame (target
`factory`) with the creation code at `[0xa0, 0xa0 + 11636)` of `fm12` and the salt
`keccak(USDC ‖ WETH)`, a `CREATE2` with an empty target, enough gas for the constructor and the
code deposit, positive depth and a creator nonce below the maximum is a compiled step to
`pairCreate2Post`. -/
theorem pairCreate2_runCompiled {sevm : Sevm} {b : Devm} {S : List B256} {Y : Nat}
    (hfork : sevm.benvStat.fork = .muirGlacier) (hstatic : sevm.isStatic = false)
    (htarget : sevm.currentTarget = UniswapV2Pair.Creation.factory) (hdepth : sevm.depth ≠ 0)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S fm12 Y 0xa0 0x2d74
      UniswapV2Pair.Creation.pairAddress) UniswapV2Pair.Creation.pairAddress)
    (hgas : 2338600 ≤ except64th Y) (hroom : S.length < 1024) :
    Ninst.RunCompiled sevm (St b ((0 : B256) :: 0xa0 :: 0x2d74 :: fk3 :: S) fm12
      (Y + create2ChargeH sevm fm12 0xa0 0x2d74)) (.exec .create2) (pairCreate2Post sevm b S Y) := by
  have rules := muirRules hfork
  have haddr : create2NewAddress sevm.currentTarget fk3 (create2InitCode fm12 0xa0 0x2d74) =
      UniswapV2Pair.Creation.pairAddress := by
    rw [htarget, fm12_create2InitCode, fk3, ← UniswapV2Pair.Creation.pairAddress_eq]
  have hle := pairCtorCost_le hfork b S Y
  have hchild : processCreateMessage (pairCreateMsg sevm b S Y) = .ok (pairChild sevm b S Y) :=
    pair_create_postH (pairCreateMsg sevm b S Y) rfl rfl
      (by
        show ByteArray.mk ⟨UniswapV2Pair.Creation.code.toList⟩ = _
        rw [ByteArray.toList_eq_toList_data])
      (by show sevm.benvStat.rules.stateGas = none; rw [rules]; rfl)
      (by show sevm.benvStat.rules.op.chainId = true; rw [rules]; rfl)
      (by show sevm.benvStat.rules.op.shifts = true; rw [rules]; rfl) rfl
      (by show 11293 ≤ sevm.benvStat.rules.code.maxCodeSize; rw [rules]; decide)
      (except64th Y - pairCtorCost sevm b S Y)
      (by
        show except64th Y = except64th Y - pairCtorCost sevm b S Y + pairCtorCost sevm b S Y
        unfold pairCtorCost at hle ⊢; omega)
      (by unfold gasCodeDeposit; omega)
  have h := create2_runCompiledH (sevm := sevm) (b := b) (S := S) (M := fm12) (G := Y) (v := 0)
    (i := 0xa0) (sz := 0x2d74) (salt := fk3) (child := pairChild sevm b S Y)
    (by rw [rules]; rfl) (by rw [rules]; rfl) (fun h => by rw [rules] at h; cases h) hstatic
    (not_lt_of_ge (B256.zero_le _)) hnonce hdepth (by rw [haddr]; exact hfresh)
    (by rw [haddr, fm12_create2InitCode]; exact hchild) ?_ hroom
  · rw [haddr] at h
    exact h
  · rw [pairChild, (liftCreatePost_facts _ _).1, Devm.recordTouch_error,
      (UniswapV2Pair.Creation.ctorPostH_facts _ _ _).2.1]
    rfl

theorem state_setStor_get_ne (w : State) {a b : Adr} (h : a ≠ b) (st : Stor) :
    (w.setStor a st).get b = w.get b := by
  unfold State.setStor
  split
  · exact State.get_setPresent_ne _ h _
  · exact State.get_set_ne _ h _

/-- The Pair constructor's frame, as the factory's `CREATE2` builds it. -/
theorem pairCtor_facts (sevm : Sevm) (b : Devm) (S : List B256) (Y : Nat) :
    (pairCtorSevm sevm b S Y).currentTarget = UniswapV2Pair.Creation.pairAddress ∧
    (pairCtorSevm sevm b S Y).caller = sevm.currentTarget ∧
    (pairCtorSevm sevm b S Y).benvStat = sevm.benvStat ∧
    Devm.getStor (pairCtorDevm sevm b S Y) UniswapV2Pair.Creation.pairAddress = Stor.empty ∧
    UniswapV2Pair.Creation.pairAddress ∈ (pairCtorDevm sevm b S Y).createdAccounts ∧
    (pairCtorDevm sevm b S Y).refundCounter = 0 ∧
    (pairCtorDevm sevm b S Y).accountsToDelete =
      (if sevm.benvStat.rules.settle.selfdestructRefund = 0 then .emptyWithCapacity
        else b.accountsToDelete) ∧
    (∀ a, a ≠ UniswapV2Pair.Creation.pairAddress →
      (pairCtorDevm sevm b S Y).state.get a = (b.state.incrNonce sevm.currentTarget).get a) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · exact processCreateMessage_msg_getStor_currentTarget (pairCreateMsg sevm b S Y)
  · show UniswapV2Pair.Creation.pairAddress ∈
      ((b.createdAccounts).insert UniswapV2Pair.Creation.pairAddress)
    exact Std.HashSet.mem_insert_self
  · intro a ha
    show (((b.state.incrNonce sevm.currentTarget).setStor UniswapV2Pair.Creation.pairAddress
      .empty).incrNonce UniswapV2Pair.Creation.pairAddress).get a = _
    unfold State.incrNonce
    rw [State.setAccount_get_ne _ (Ne.symm ha), state_setStor_get_ne _ (Ne.symm ha)]

/-- What the factory's `CREATE2` child leaves: the Pair runtime and the constructor storage at the
Pair address, every other account as the creating world had it after the creator's nonce bump,
the inherited deletions, a non-negative refund counter (at Muir Glacier's flat `SLOAD` price) and
the Pair among the created accounts. -/
theorem pairChild_facts {sevm : Sevm} {b : Devm} {S : List B256} {Y : Nat}
    (hflat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 5000) :
    (pairChild sevm b S Y).state.getCode UniswapV2Pair.Creation.pairAddress =
      UniswapV2Pair.code ∧
    Devm.getStor (pairChild sevm b S Y) UniswapV2Pair.Creation.pairAddress =
      UniswapV2Pair.Creation.ctorStor sevm.benvStat.chainId.toB256
        UniswapV2Pair.Creation.pairAddress sevm.currentTarget Stor.empty ∧
    (∀ a, a ≠ UniswapV2Pair.Creation.pairAddress →
      (pairChild sevm b S Y).state.get a = (b.state.incrNonce sevm.currentTarget).get a) ∧
    (pairChild sevm b S Y).accountsToDelete = (pairCtorDevm sevm b S Y).accountsToDelete ∧
    0 ≤ (pairChild sevm b S Y).refundCounter ∧
    UniswapV2Pair.Creation.pairAddress ∈ (pairChild sevm b S Y).createdAccounts := by
  obtain ⟨ht, hc, hst, hempty, hcreated, hrc, -, hother⟩ := pairCtor_facts sevm b S Y
  obtain ⟨hout, -, hstor, -⟩ := UniswapV2Pair.Creation.ctorPostH_facts
    (pairCtorSevm sevm b S Y) (pairCtorDevm sevm b S Y) (except64th Y - pairCtorCost sevm b S Y)
  obtain ⟨hatd, hca, hkeep, hge⟩ := ctorPostH_meta (pairCtorSevm sevm b S Y)
    (pairCtorDevm sevm b S Y) (except64th Y - pairCtorCost sevm b S Y) (by rw [hst]; exact hflat)
    (by rw [ht]; exact hcreated)
  have facts := liftCreatePost_facts UniswapV2Pair.Creation.pairAddress
    ((UniswapV2Pair.Creation.ctorPostH (pairCtorSevm sevm b S Y) (pairCtorDevm sevm b S Y)
      (except64th Y - pairCtorCost sevm b S Y)).recordTouch
      (pairCreateMsg sevm b S Y).benv.stat.rules true UniswapV2Pair.Creation.pairAddress)
  have hwin : (UniswapV2Pair.Creation.ctorPostH (pairCtorSevm sevm b S Y) (pairCtorDevm sevm b S Y)
      (except64th Y - pairCtorCost sevm b S Y)).output = UniswapV2Pair.code.toList := by
    rw [hout, UniswapV2Pair.Creation.runtimeWindow_eq]
  have hne : ¬ ({ (UniswapV2Pair.Creation.ctorPostH (pairCtorSevm sevm b S Y) (pairCtorDevm sevm b S Y)
      (except64th Y - pairCtorCost sevm b S Y)).state.get UniswapV2Pair.Creation.pairAddress with
        code := ⟨⟨UniswapV2Pair.code.toList⟩⟩ } : Acct).Empty := by
    intro he
    have hsize : (⟨⟨UniswapV2Pair.code.toList⟩⟩ : ByteArray).size ≠ 0 := by
      rw [show (⟨⟨UniswapV2Pair.code.toList⟩⟩ : ByteArray).size =
        UniswapV2Pair.code.toList.length from rfl, ← UniswapV2Pair.Creation.runtimeWindow_eq,
        UniswapV2Pair.Creation.runtimeWindow_length]
      decide
    exact hsize he.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((pairChild sevm b S Y).state.get UniswapV2Pair.Creation.pairAddress).code = _
    rw [pairChild, facts.2.2.1]
    simp only [Devm.recordTouch_state, Devm.recordTouch_output, hwin, Acct.clearIfEmpty_code]
    rw [ByteArray.toList_eq_toList_data]
  · show ((pairChild sevm b S Y).state.get UniswapV2Pair.Creation.pairAddress).stor = _
    rw [pairChild, facts.2.2.1]
    simp only [Devm.recordTouch_state, Devm.recordTouch_output, hwin]
    rw [Acct.clearIfEmpty_stor]
    simp only [hne, ↓reduceIte]
    show Devm.getStor (UniswapV2Pair.Creation.ctorPostH (pairCtorSevm sevm b S Y) (pairCtorDevm sevm b S Y)
      (except64th Y - pairCtorCost sevm b S Y)) UniswapV2Pair.Creation.pairAddress = _
    rw [← ht, hstor, ht, hempty, hc, hst]
  · intro a ha
    rw [pairChild, facts.2.2.2 a ha]
    simp only [Devm.recordTouch_state]
    rw [hkeep a (by rw [ht]; exact ha), hother a ha]
  · rw [pairChild, (liftCreatePost_meta _ _).1, (recordTouch_meta _ _ _ _).1]
    exact hatd
  · rw [pairChild, (liftCreatePost_meta _ _).2.1, (recordTouch_meta _ _ _ _).2.1, ← hrc]
    exact hge
  · rw [pairChild, (liftCreatePost_meta _ _).2.2, (recordTouch_meta _ _ _ _).2.2.1, hca]
    exact hcreated

/-- `create2Post` field by field, over any parent and child. -/
theorem create2Post_fields (D child : Devm) (addr : Adr) :
    (create2Post D child addr).stack = addr.toB256 :: D.stack ∧
    (create2Post D child addr).memory = D.memory ∧
    (create2Post D child addr).gasLeft = D.gasLeft + child.gasLeft ∧
    (create2Post D child addr).error = D.error ∧
    (create2Post D child addr).state = child.state ∧
    (create2Post D child addr).accountsToDelete = D.accountsToDelete.union child.accountsToDelete ∧
    (create2Post D child addr).refundCounter = D.refundCounter + child.refundCounter ∧
    (create2Post D child addr).createdAccounts = child.createdAccounts :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `create2Prepared` field by field. -/
theorem create2Prepared_fields (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat)
    (i sz : B256) (addr : Adr) :
    (create2Prepared sevm b S M G i sz addr).stack = S ∧
    (create2Prepared sevm b S M G i sz addr).memory = M.extends [(i.toNat, sz.toNat)] ∧
    (create2Prepared sevm b S M G i sz addr).gasLeft = G - except64th G ∧
    (create2Prepared sevm b S M G i sz addr).error = b.error ∧
    (create2Prepared sevm b S M G i sz addr).accountsToDelete = b.accountsToDelete ∧
    (create2Prepared sevm b S M G i sz addr).refundCounter = b.refundCounter :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pairAddress_toB256 :
    UniswapV2Pair.Creation.pairAddress.toB256 = 0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc := by
  decide

/-- The factory frame after its `CREATE2`, field by field: the new address pushed over `S`, the
memory `fm12`, the gas left by the withheld child gas less the constructor and the code deposit,
the frame's error, and the child's world, deletions, refunds and created accounts merged. -/
theorem pairCreate2Post_facts (sevm : Sevm) (b : Devm) (S : List B256) (Y : Nat) :
    (pairCreate2Post sevm b S Y).stack = (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) :: S ∧
    (pairCreate2Post sevm b S Y).memory = fm12 ∧
    (pairCreate2Post sevm b S Y).gasLeft = (Y - except64th Y) +
      (except64th Y - pairCtorCost sevm b S Y - 11293 * gasCodeDeposit) ∧
    (pairCreate2Post sevm b S Y).error = b.error ∧
    (pairCreate2Post sevm b S Y).state = (pairChild sevm b S Y).state ∧
    (pairCreate2Post sevm b S Y).accountsToDelete =
      b.accountsToDelete.union (pairChild sevm b S Y).accountsToDelete ∧
    (pairCreate2Post sevm b S Y).refundCounter =
      b.refundCounter + (pairChild sevm b S Y).refundCounter ∧
    (pairCreate2Post sevm b S Y).createdAccounts = (pairChild sevm b S Y).createdAccounts := by
  obtain ⟨hout, -, -, hleft⟩ := UniswapV2Pair.Creation.ctorPostH_facts
    (pairCtorSevm sevm b S Y) (pairCtorDevm sevm b S Y) (except64th Y - pairCtorCost sevm b S Y)
  have hlen : (UniswapV2Pair.Creation.ctorPostH (pairCtorSevm sevm b S Y) (pairCtorDevm sevm b S Y)
      (except64th Y - pairCtorCost sevm b S Y)).output.length = 11293 := by
    rw [hout, UniswapV2Pair.Creation.runtimeWindow_length]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := create2Post_fields
    (create2Prepared sevm b S fm12 Y 0xa0 0x2d74 UniswapV2Pair.Creation.pairAddress)
    (pairChild sevm b S Y) UniswapV2Pair.Creation.pairAddress
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := create2Prepared_fields sevm b S fm12 Y 0xa0 0x2d74
    UniswapV2Pair.Creation.pairAddress
  unfold pairCreate2Post
  refine ⟨?_, ?_, ?_, c4.trans p4, c5, ?_, ?_, c8⟩
  · rw [c1, p1, pairAddress_toB256]
  · rw [c2, p2]
    exact Mem.extends_covered (by rw [fm12_size]; decide)
  · rw [c3, p3, pairChild, (liftCreatePost_facts _ _).2.1, (recordTouch_meta _ _ _ _).2.2.2,
      Devm.recordTouch_output, hleft, hlen]
  · rw [c6, p5]
  · rw [c7, p6]

/-! ## The factory's `initialize` call -/

/-- The factory frame suspended at its `initialize` `CALL` from the world `b`, the stack below the
operands `S` and the gas `X`: charged the flat call base 700 and the forwarded
`except64th (X - 700)`, with the windows already covered by `fm15`. -/
def initCallParent (b : Devm) (S : List B256) (X : Nat) : Devm :=
  callSpawnParent (St b S fm15 X) (except64th (X - 700) + 700 + 0) 11880 68 11880 0

/-- The `initialize` message. -/
def initCallMsg (sevm : Sevm) (b : Devm) (S : List B256) (X : Nat) : Msg :=
  callSpawnMsg sevm (initCallParent b S X) (except64th (X - 700))
    UniswapV2Pair.Creation.pairAddress UniswapV2Pair.Creation.pairAddress 11880 68
    (b.state.getCode UniswapV2Pair.Creation.pairAddress) false

/-- `initialize`'s storage charge in that frame. -/
def initCallCharge (sevm : Sevm) (b : Devm) (S : List B256) (X : Nat) : Nat :=
  UniswapV2Pair.initializeStorageChargeH (initSevm (initCallMsg sevm b S X))
    (initDevm (initCallMsg sevm b S X))

/-- The `initialize` frame's final machine. -/
def initChild (sevm : Sevm) (b : Devm) (S : List B256) (X : Nat) : Devm :=
  UniswapV2Pair.initializePublicPostH (initSevm (initCallMsg sevm b S X))
    (initDevm (initCallMsg sevm b S X)) [0x485cc955] UniswapV2Pair.getterInitMemory
    (except64th (X - 700) - initCallCharge sevm b S X - 377)

/-- The factory frame after the `initialize` call. -/
def initCallPost (sevm : Sevm) (b : Devm) (S : List B256) (X : Nat) : Devm :=
  callChildPost (initCallParent b S X)
    ((initChild sevm b S X).recordTouch sevm.benvStat.rules true UniswapV2Pair.Creation.pairAddress)
    11880 0

theorem callSpawnParent_memory (d1 : Devm) (charge ii is oi os : Nat) :
    (callSpawnParent d1 charge ii is oi os).memory = d1.memory.extends [(ii, is), (oi, os)] := rfl

theorem callSpawnMsg_data (sevm : Sevm) (p : Devm) (mcs : Nat) (callee cadr : Adr) (ii is : Nat)
    (code : ByteArray) (dp : Bool) :
    (callSpawnMsg sevm p mcs callee cadr ii is code dp).data = p.memory.data.sliceD ii is 0 := rfl

theorem initCallParent_memory (b : Devm) (S : List B256) (X : Nat) :
    (initCallParent b S X).memory = fm15 := by
  rw [initCallParent, callSpawnParent_memory, St.memory]
  exact Mem.extends_covered (by rw [fm15_size]; decide)

theorem initCallMsg_data (sevm : Sevm) (b : Devm) (S : List B256) (X : Nat) :
    (initCallMsg sevm b S X).data = initializeCalldata := by
  rw [initCallMsg, callSpawnMsg_data, initCallParent_memory, fm15_calldata]

theorem pairAddress_word_toAdr :
    (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256).toAdr =
      UniswapV2Pair.Creation.pairAddress := by decide

/-- **The `initialize` child runs.**  The message of the factory's `initialize` call, over a
world holding the Pair runtime with the constructor storage for the factory and with
`except64th (X - 700)` covering `initialize`'s closed charge and the store sentries, executes from
pc `0` to `initChild`. -/
theorem initChild_exec {sevm : Sevm} {b : Devm} {S : List B256} {X : Nat} {chainWord : B256}
    (hfork : sevm.benvStat.fork = .muirGlacier) (hstatic : sevm.isStatic = false)
    (htarget : sevm.currentTarget = UniswapV2Pair.Creation.factory)
    (hcode : b.state.getCode UniswapV2Pair.Creation.pairAddress = UniswapV2Pair.code)
    (hstor : b.getStor UniswapV2Pair.Creation.pairAddress =
      UniswapV2Pair.Creation.ctorStor chainWord UniswapV2Pair.Creation.pairAddress
        UniswapV2Pair.Creation.factory Stor.empty)
    (hgas : initCallCharge sevm b S X + 377 + 2400 ≤ except64th (X - 700)) :
    Nonempty (Exec 0 (initSevm (initCallMsg sevm b S X)) (initDevm (initCallMsg sevm b S X))
      (.ok (initChild sevm b S X))) := by
  have rules := muirRules hfork
  have hdata := initCallMsg_data sevm b S X
  have hstat : (initSevm (initCallMsg sevm b S X)).benvStat = sevm.benvStat := rfl
  have hpre : St (initDevm (initCallMsg sevm b S X)) [] Mem.empty
      ((except64th (X - 700) - initCallCharge sevm b S X - 377) +
        UniswapV2Pair.initializeStorageChargeH (initSevm (initCallMsg sevm b S X))
          (initDevm (initCallMsg sevm b S X)) + 377) = initDevm (initCallMsg sevm b S X) :=
    pre_eq_St rfl rfl (by show _ = except64th (X - 700); unfold initCallCharge at hgas ⊢; omega)
  have h := UniswapV2Pair.initialize_bytecode_live_rawH (sevm := initSevm (initCallMsg sevm b S X))
    (b := initDevm (initCallMsg sevm b S X))
    (G := except64th (X - 700) - initCallCharge sevm b S X - 377)
    (by show b.state.getCode _ = _; exact hcode)
    (by rw [hstat, rules]; rfl) (by rw [hstat, rules]; rfl) rfl
    (by show (4 : B256) ≤ (initCallMsg sevm b S X).data.length.toB256; rw [hdata]; decide)
    (by
      show Bytes.toB256 ((initCallMsg sevm b S X).data.sliceD (0 : B256).toNat 32 0) >>> 224 = _
      rw [hdata]; decide)
    (by show (64 : B256) ≤ (initCallMsg sevm b S X).data.length.toB256 - 4; rw [hdata]; decide)
    (by
      show sevm.currentTarget = ((Devm.getStor b UniswapV2Pair.Creation.pairAddress).get 5).toAdr
      rw [hstor, htarget, UniswapV2Pair.Creation.ctorStor, Stor.get_set_self, toAdr_toB256])
    (by unfold gCallStipend initCallCharge at *; omega)
    (by unfold gCallStipend initCallCharge at *; omega)
    (by show (false || sevm.isStatic) = false; rw [hstatic]; rfl)
  rw [hpre] at h
  exact h

/-- **The factory's `initialize` call, at Muir Glacier.**  From the world `b` holding the Pair
runtime at the new address with the constructor storage for the factory, a `GAS`-forwarding
zero-value `CALL` of `initialize(USDC, WETH)` at gas `X` (so that the forwarded
`except64th (X - 700)` covers `initialize`'s closed charge with room for the store sentries) is a
compiled step to `initCallPost`. -/
theorem pairInitCall_runCompiled {sevm : Sevm} {b : Devm} {S : List B256} {X : Nat}
    {chainWord : B256}
    (hfork : sevm.benvStat.fork = .muirGlacier) (hstatic : sevm.isStatic = false)
    (htarget : sevm.currentTarget = UniswapV2Pair.Creation.factory) (hdepth : sevm.depth ≠ 0)
    (hcode : b.state.getCode UniswapV2Pair.Creation.pairAddress = UniswapV2Pair.code)
    (hstor : b.getStor UniswapV2Pair.Creation.pairAddress =
      UniswapV2Pair.Creation.ctorStor chainWord UniswapV2Pair.Creation.pairAddress
        UniswapV2Pair.Creation.factory Stor.empty)
    (hX : X < 2 ^ 256) (h700 : 700 ≤ X)
    (hgas : initCallCharge sevm b S X + 377 + 2400 ≤ except64th (X - 700))
    (hroom : S.length < 1024) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 X ::
        (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) ::
        0 :: 0x2e68 :: 0x44 :: 0x2e68 :: 0 :: S) fm15 X) (.exec .call)
      (initCallPost sevm b S X) := by
  have rules := muirRules hfork
  obtain ⟨run⟩ := initChild_exec hfork hstatic htarget hcode hstor hgas
  have hexec : exec (initEvm (initCallMsg sevm b S X)) = .ok (initChild sevm b S X) :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨run⟩
  have herr : (initChild sevm b S X).error = none := by
    unfold initChild UniswapV2Pair.initializePublicPostH UniswapV2Pair.initializePublicBaseH
      UniswapV2Pair.initializeCoreBaseH UniswapV2Pair.initializeWritesBaseH
      UniswapV2Pair.initializeLoaded1H UniswapV2Pair.initializeStored0H
      UniswapV2Pair.initializeLoaded0H UniswapV2Pair.initializeFactoryBaseH
    rw [St_error]
    simp only [afterSstoreH_error, afterSloadH_error]
    rfl
  have h := Ninst.runCompiled_call_zero_child_flat (sevm := sevm) (b := b) (S := S) (M := fm15)
    (X := X) (g := Nat.toB256 X) (c := 0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc)
    (ii := 0x2e68) (is := 0x44) (oi := 0x2e68) (os := 0) (ext := 0)
    (mcc := except64th (X - 700) + 700) (mcs := except64th (X - 700))
    (fa := istanbulAccessGas) (cpost := initChild sevm b S X)
    (by rw [rules]; rfl) (by rw [rules]; rfl) (by rw [rules]; rfl)
    (Devm.extCost_covered (by rw [fm15_size]; decide))
    (by
      rw [B256.toNat_toB256_of_lt hX]
      unfold calculateMsgCallGas
      simp only [show istanbulAccessGas.call = 700 from rfl, Nat.sub_zero,
        show ¬ X < 700 + 0 by omega, ↓reduceIte]
      rw [Nat.min_eq_right (by unfold except64th; omega)]
      rfl)
    (by unfold except64th; omega) hdepth
    (by rw [pairAddress_word_toAdr, rules]; decide) hroom
    (by rw [pairAddress_word_toAdr]; exact hexec) herr
  rw [pairAddress_word_toAdr] at h
  exact h

/-- The factory frame after the `initialize` call, field by field: the success flag over `S`, the
memory `fm15`, the gas left by the call base and `initialize`'s closed charge, the frame's error,
and the child's world, deletions and refunds merged. -/
theorem initCallPost_facts (sevm : Sevm) (b : Devm) (S : List B256) (X : Nat) :
    (initCallPost sevm b S X).stack = (1 : B256) :: S ∧
    (initCallPost sevm b S X).memory = fm15 ∧
    (initCallPost sevm b S X).gasLeft =
      (X - (except64th (X - 700) + 700 + 0)) +
        (except64th (X - 700) - initCallCharge sevm b S X - 377) ∧
    (initCallPost sevm b S X).error = b.error ∧
    (initCallPost sevm b S X).state = (initChild sevm b S X).state ∧
    (initCallPost sevm b S X).accountsToDelete =
      b.accountsToDelete.union (initChild sevm b S X).accountsToDelete ∧
    (initCallPost sevm b S X).refundCounter =
      b.refundCounter + (initChild sevm b S X).refundCounter := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := callChildPost_facts_zero (initCallParent b S X)
    ((initChild sevm b S X).recordTouch sevm.benvStat.rules true UniswapV2Pair.Creation.pairAddress)
    11880 0 rfl
  refine ⟨h1, h2.trans (initCallParent_memory b S X), ?_, h5, ?_, ?_, ?_⟩
  · rw [initCallPost, h3]
    rfl
  · rw [initCallPost, h4]
    rfl
  · unfold initCallPost callChildPost
    rw [List.take_zero, Devm.memWrite_nil]
    rfl
  · unfold initCallPost callChildPost
    rw [List.take_zero, Devm.memWrite_nil]
    rfl

/-- What the `initialize` child leaves: every account's code and every account other than the
Pair's as the calling world had them, the inherited deletions, and (at Muir Glacier's flat
`SLOAD` price, with the Pair among the created accounts) a non-negative refund counter. -/
theorem initChild_facts {sevm : Sevm} {b : Devm} {S : List B256} {X : Nat}
    (hflat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 5000)
    (hcreated : UniswapV2Pair.Creation.pairAddress ∈ b.createdAccounts) :
    (∀ a, (initChild sevm b S X).getCode a = b.getCode a) ∧
    (∀ a, a ≠ UniswapV2Pair.Creation.pairAddress →
      (initChild sevm b S X).state.get a = b.state.get a) ∧
    (initChild sevm b S X).accountsToDelete =
      (if sevm.benvStat.rules.settle.selfdestructRefund = 0 then .emptyWithCapacity
        else b.accountsToDelete) ∧
    0 ≤ (initChild sevm b S X).refundCounter := by
  obtain ⟨hatd, -, hcode, hkeep, hge⟩ := initializePublicPostH_meta
    (initSevm (initCallMsg sevm b S X)) (initDevm (initCallMsg sevm b S X)) [0x485cc955]
    UniswapV2Pair.getterInitMemory (except64th (X - 700) - initCallCharge sevm b S X - 377)
    hflat hcreated
  exact ⟨hcode, hkeep, hatd, hge⟩

end Blanc.Lift.UniswapV2Factory
