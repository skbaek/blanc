import Blanc.Lift.SystemWordWriter
import Blanc.Lift.ConsolidationRequest.Delivery
import Blanc.Lift.ConsolidationRequest.SystemFrame
import Blanc.Lift.WithdrawalRequest.DrainTx
import Jaune.RlpEval

/-!
# Closed inputs and empty-calldata caller runtime for the C-S3 witness

1. Fixed type-2 transaction `txSub` (96-byte user submission to EIP-7251 with `value = 1`),
   with its recovered sender `subSender` checked distinct from `senderE`, coinbase `0`,
   `systemAddress`, and all four system contracts.
2. Empty-calldata 29-byte caller runtime `callerCode` (`PUSH0 × 5; PUSH20 0x…7251; GAS; CALL; STOP`),
   its single-step `CALL` spawn theorem `caller_call_spawn`, its exact EIP-7251 child
   execution theorem `consolidation_child_exec`, and `callerPost_facts`.
-/

namespace Blanc.Composition.ConsolidationRequestDrainInput

open Jaune Blanc Blanc.Lift
open Blanc.Lift.RequestSystem
open Blanc.Lift.WithdrawalRequest.FloodTx (senderE)

/-- The 96-byte consolidation request payload (`sourcePubkey ++ targetPubkey`). -/
def payload96 : Bytes := List.replicate 96 0x11

theorem payload96_length : payload96.length = 96 := by decide

/-- User submission transaction to `consolidationRequestPredeployAddress` paying 1 wei. -/
def txSub : Tx :=
  { nonce := 0, gas := 2 ^ 20, value := 1, data := payload96, v := 0
    r := (0x2ba550518ad1955936234bb6ad552eeab937deecff98751c7f495a48a9594055 : B256).toBytes
    s := (0x09a1f8f3576b0e2ffd997b9d4aa4c200a5085b1a60d67f00eb7b3e21adf274ee : B256).toBytes
    type := .two 1 1 8 (some consolidationRequestPredeployAddress) [] }

def txSubSigningPayload : Bytes :=
  [0x02, 0xf8, 0x81, 0x01, 0x80, 0x01, 0x08, 0x83, 0x10, 0x00, 0x00, 0x94,
   0x00, 0x00, 0xbb, 0xdd, 0xc7, 0xce, 0x48, 0x86, 0x42, 0xfb,
   0x57, 0x9f, 0x8b, 0x00, 0xf3, 0xa5, 0x90, 0x00, 0x72, 0x51,
   0x01, 0xb8, 0x60] ++ payload96 ++ [0xc0]

theorem txSub_signingEncoded : txSub.signingHash = some txSubSigningPayload.keccak := by
  simp only [Tx.signingHash, txSub, AccessList.toBLT, List.map_nil]
  congr 2
  rw [BLT.toBytes_eq_toBytesS]
  simp only [Nat.toBytes_eq_toBytesS]
  decide +kernel

/-- Recovered sender address for `txSub` on `chainId = 1`. -/
def subSender : Adr := 0x1ebdc0f3203a69534bbe8c661c96f18d6c44812a

theorem txSub_recoveredSender : recoverSender 1 txSub = .ok subSender := by
  rw [recoverSender, txSub_signingEncoded]
  decide +kernel

theorem subSender_distinct :
    subSender ≠ senderE ∧
    subSender ≠ 0 ∧
    subSender ≠ systemAddress ∧
    subSender ≠ beaconRootsAddress ∧
    subSender ≠ historyStorageAddress ∧
    subSender ≠ withdrawalRequestPredeployAddress ∧
    subSender ≠ consolidationRequestPredeployAddress := by
  decide

theorem txSub_intrinsic (E : Adr) :
    calculateIntrinsicCost pragueRules txSub E = (22536, 24840) := by
  rw [calculateIntrinsicCost_two_call (rules := pragueRules) rfl rfl rfl rfl]
  decide +kernel

/-! ## Empty-calldata caller runtime targeting EIP-7251 -/

/-- `PUSH0 × 5; PUSH20 consolidationRequestPredeployAddress; GAS; CALL; STOP` (29 bytes). -/
def callerCode : ByteArray :=
  ⟨([0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x73] ++
    consolidationRequestPredeployAddress.toBytes ++ [0x5a, 0xf1, 0x00]).toArray⟩

theorem callerCode_size : callerCode.size = 29 := by
  simp only [callerCode, ByteArray.size, List.size_toArray, List.length_append]
  decide

theorem callerCode_runtime :
    callerCode.toList ≠ [] ∧ ¬ isValidDelegation callerCode := by
  constructor
  · apply List.ne_nil_of_length_pos
    rw [← ByteArray.size_eq_length_toList, callerCode_size]
    decide
  · intro bad
    have size := bad.1
    rw [callerCode_size] at size
    contradiction

theorem callerCode_undelegated : getDelegatedCodeAddress callerCode = none := by
  unfold getDelegatedCodeAddress
  apply ite_eq_right
  intro bad
  have size := bad.1
  rw [callerCode_size] at size
  contradiction

def callerParent (base : Devm) (gas : Nat) : Devm :=
  callSpawnParent
    (addAccessedAddress (base.setMach ⟨[], .empty, gas, base.stateGas⟩) consolidationRequestPredeployAddress)
    (SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas +
      accessCost consolidationRequestPredeployAddress base.accessedAddresses) 0 0 0 0

def callerChildMsg (sevm : Sevm) (base : Devm) (gas : Nat)
    (childCode : ByteArray) : Msg :=
  callSpawnMsg sevm (callerParent base gas)
    (SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas)
    consolidationRequestPredeployAddress consolidationRequestPredeployAddress 0 0 childCode false

def callerPost (base : Devm) (gas : Nat) (child : Devm) : Devm :=
  callChildPost (callerParent base gas) child 0 0

theorem caller_call_spawn {sevm : Sevm} {base : Devm} {gas : Nat}
    {childCode : ByteArray}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (gasLt : gas < 2 ^ 256)
    (affordable : accessCost consolidationRequestPredeployAddress base.accessedAddresses ≤ gas)
    (installed : base.getCode consolidationRequestPredeployAddress = childCode)
    (nondelegated : getDelegatedCodeAddress childCode = none) :
    Xinst.step sevm
      (base.setMach ⟨[gas.toB256, consolidationRequestPredeployAddress.toBytes.toB256, 0, 0, 0, 0, 0],
        .empty, gas, base.stateGas⟩) .call =
      .spawn (Frame.ofCall (callerChildMsg sevm base gas childCode))
        (.call (callerParent base gas) 0 0) := by
  let bare := base.setMach ⟨[], .empty, gas, base.stateGas⟩
  have delegation : accessDelegation (addAccessedAddress bare consolidationRequestPredeployAddress) consolidationRequestPredeployAddress =
      (false, consolidationRequestPredeployAddress, childCode, 0, addAccessedAddress bare consolidationRequestPredeployAddress) := by
    unfold accessDelegation
    change (match getDelegatedCodeAddress (base.getCode consolidationRequestPredeployAddress) with
      | some a => (true, a, base.getCode a, accessCost a (addAccessedAddress bare consolidationRequestPredeployAddress).accessedAddresses,
          addAccessedAddress (addAccessedAddress bare consolidationRequestPredeployAddress) a)
      | none => (false, consolidationRequestPredeployAddress, base.getCode consolidationRequestPredeployAddress, 0, addAccessedAddress bare consolidationRequestPredeployAddress)) = _
    rw [installed, nondelegated]
  have splitGas : calculateMsgCallGas 0 gas.toB256.toNat gas 0
      (accessCost consolidationRequestPredeployAddress base.accessedAddresses) =
      (SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas + accessCost consolidationRequestPredeployAddress base.accessedAddresses,
        SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas) := by
    rw [calculateMsgCallGas_zero (by omega), B256.toNat_toB256_of_lt gasLt]
    simp only [Nat.sub_zero]
    have bound : SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas ≤ gas := by
      unfold SystemWordWriter.forwardedGas except64th
      omega
    unfold SystemWordWriter.forwardedGas at bound
    rw [Nat.min_eq_right bound]
    rfl
  have spawned := Xinst.step_call_zero_value_spawn
    (sevm := sevm)
    (devm := base.setMach ⟨[gas.toB256, consolidationRequestPredeployAddress.toBytes.toB256, 0, 0, 0, 0, 0], .empty,
      gas, base.stateGas⟩)
    (gw := gas.toB256) (cw := consolidationRequestPredeployAddress.toBytes.toB256)
    (iiw := 0) (isw := 0) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := consolidationRequestPredeployAddress) (code := childCode) (dgc := 0)
    (d1 := addAccessedAddress bare consolidationRequestPredeployAddress) (ext := 0)
    (acc := accessCost consolidationRequestPredeployAddress base.accessedAddresses)
    (mcs := SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas)
    (mcc := SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas + accessCost consolidationRequestPredeployAddress base.accessedAddresses)
    (fork.callEra false) rfl ?_ ?_ ?_ splitGas ?_ depth
  · simpa only [callerChildMsg, callerParent, bare, SystemWordWriter.target_word,
      Nat.add_zero, B256.toNat_zero] using spawned
  · simp only [Devm.extCost, B256.toNat_zero, memExtsSize, memExtSize, ite_true, Nat.sub_self]
  · rw [SystemWordWriter.target_word]
    exact delegation
  · rw [SystemWordWriter.target_word]
    rfl
  · change SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas +
      accessCost consolidationRequestPredeployAddress base.accessedAddresses + 0 ≤ gas
    unfold SystemWordWriter.forwardedGas except64th
    omega

abbrev cSysPath : SysPath := SystemExecution.ConsolidationRequest.Amsterdam.sysPath
abbrev cSysShape : SysShape := SystemExecution.ConsolidationRequest.Amsterdam.sysShape

def consolidationChildPost (msg : Msg) : Devm :=
  let s := initSevm msg
  let b := initDevm msg
  cSysPath.framePostOn b (coveredStores s) (msg.gas - cSysPath.frameCostOn b (coveredStores s))

theorem consolidation_child_exec {sevm : Sevm} {base : Devm} {gas : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (hsys : sevm.currentTarget = systemAddress)
    (hstatic : sevm.isStatic = false)
    (horig : ∀ k, getOrigStorVal sevm consolidationRequestPredeployAddress k =
      base.getStorVal consolidationRequestPredeployAddress k)
    (hgas : 120000 ≤ SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas) :
    let msg := callerChildMsg sevm base gas
      consolidationRequestCode
    let cpost := consolidationChildPost msg
    exec (initEvm msg) = .ok cpost ∧
      cpost.error = none ∧
      0 ≤ cpost.refundCounter ∧
      cpost.state = sysState cSysShape base.state consolidationRequestPredeployAddress ∧
      cpost.logs = [] := by
  intro msg cpost
  let s := initSevm msg
  let b := initDevm msg
  have fork' : CoveredFork s.benvStat.fork := fork
  have laws := coveredStores_laws s
  have hle : cSysPath.frameCostOn b (coveredStores s) ≤ 114177 := by
    have hb := SysPath.frameCost_leOn SystemExecution.ConsolidationRequest.Amsterdam.sysMemory laws b
    change _ ≤ cSysPath.frameBoundOn _ (gasColdSload + gasStorageSet) at hb
    rw [ConsolidationRequest.frameBound_eq] at hb
    exact hb
  have mtarget : s.currentTarget = consolidationRequestPredeployAddress := rfl
  have mcaller : s.caller = systemAddress := hsys
  have mstatic : s.isStatic = false := by
    show (false || sevm.isStatic) = false
    rw [hstatic]
    rfl
  have mdata : s.data = [] := by
    show ((callerParent base gas).memory.data.sliceD 0 0 0) = []
    rfl
  have hbState : b.state = base.state := by rfl
  have hbStorVal : ∀ k, b.getStorVal consolidationRequestPredeployAddress k =
      base.getStorVal consolidationRequestPredeployAddress k := by
    intro k
    change (b.state.get consolidationRequestPredeployAddress).stor.get k =
      (base.state.get consolidationRequestPredeployAddress).stor.get k
    rw [hbState]
  have r : CoveredReady s b [2, 3, 0, 1] := by
    refine ⟨rfl, (Int.le_refl 0 :), fun k _ => ?_⟩
    unfold SlotClean Devm.getOrigStorVal
    split
    · exact Or.inr rfl
    · refine Or.inl ?_
      rw [mtarget, hbStorVal k]
      exact horig k
  have mgas : b.gasLeft = msg.gas := initDevm_gasLeft msg
  have hmsgGas : msg.gas = SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress gas := rfl
  have hG : gCallStipend < msg.gas - cSysPath.frameCostOn b (coveredStores s) := by
    simp only [gCallStipend]
    omega
  have run := cSysPath.frame_runOn (sevm := s) (b := b) (w := coveredStores s)
    (coveredStores_runs fork') laws fork'.rules_access fork'.rules_push0 fork'.rules_shifts
    mstatic mcaller mdata r hG
  rw [show msg.gas - cSysPath.frameCostOn b (coveredStores s) + cSysPath.frameCostOn b (coveredStores s) =
      b.gasLeft by omega,
    show St b [] .empty b.gasLeft = b from St.self (d := b) rfl rfl] at run
  have hexec : Nonempty (Exec 0 s b (.ok cpost)) :=
    lift_exact_noExec cSysPath.check cSysPath.jumps rfl cSysPath.noExec ⟨_, cSysPath.root, run⟩
  have hrun : exec (initEvm msg) = .ok cpost := (exec_iff_exec_eq 0 s b (.ok cpost)).mp hexec
  have rSetup : CoveredReady s (setupBase s b) [2, 3, 0, 1] := laws.read (laws.read r 3) 2
  have rDrain := cSysPath.fold_readyOn laws (h := SysPath.rd s b 2) 0 (cSysPath.count s b).toNat
    (M := .empty) rSetup
  have rBooked := ready_bookOn laws rDrain (SysPath.rd s b 2) (cSysPath.count s b) (SysPath.rd s b 3)
  have rRead : CoveredReady s (cSysPath.excessReadOn b (coveredStores s)) [0, 1] :=
    laws.read (laws.read rBooked 0) 1
  have rEnd := laws.write (laws.write rRead (by decide) (cSysPath.excessStoredOn b (coveredStores s)))
    (by decide) (0 : B256)
  have herr : cpost.error = none := by
    dsimp only [cpost, consolidationChildPost]
    rw [SysPath.framePostOn, chargedRetPost_error]
    exact laws.error rEnd
  have href : 0 ≤ cpost.refundCounter := by
    dsimp only [cpost, consolidationChildPost]
    rw [SysPath.framePostOn, chargedRetPost_refundCounter]
    exact laws.refund rEnd
  have hstate : cpost.state = sysState cSysShape base.state consolidationRequestPredeployAddress := by
    have hs := SysPath.framePostOn_state (k := cSysPath) laws b (msg.gas - cSysPath.frameCostOn b (coveredStores s))
    rw [mtarget] at hs
    exact hs.trans (by rw [hbState]; rfl)
  have hlogs : cpost.logs = [] := by
    obtain ⟨execRun⟩ := hexec
    have hl := (ConsolidationRequest.exec_system_frame (sevm := s) (pre := b) (post := cpost)
      rfl fork' rfl (show Mem.Wf b.memory from Mem.wf_empty) mcaller execRun).2.2.2
    have hbLogs : b.logs = [] := by
      change (match s.benvStat.rules.stateGas with | none => [] | some _ => _) = []
      rw [CoveredFork.rules_stateGas_none fork']
    exact hl.trans hbLogs
  exact ⟨hrun, herr, href, hstate, hlogs⟩

theorem callerPost_facts (base : Devm) (gas : Nat) (child : Devm) :
    (callerPost base gas child).state = child.state ∧
    (callerPost base gas child).logs = base.logs ++ child.logs ∧
    (callerPost base gas child).refundCounter = base.refundCounter + child.refundCounter ∧
    (callerPost base gas child).error = base.error ∧
    (callerPost base gas child).output = base.output := by
  unfold callerPost callChildPost callerParent
  rw [List.take_zero, Devm.memWrite_nil]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Blanc.Composition.ConsolidationRequestDrainInput
