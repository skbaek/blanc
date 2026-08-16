import Blanc.LidoCircuitBreakerEnumeration
import Blanc.LidoCircuitBreakerSites

/-!
Exact access and temporal authority for the Lido CircuitBreaker runtime.

This owner builds on the completed Registry and observability layers.  The
small pure kernel below fixes the strict liveness and checked-extension
meanings used by the compiled endpoint and occurrence theorems that follow.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- Runtime liveness is strict and depends only on the timestamp and stored
expiry.  Registry membership is intentionally absent. -/
def IsPauserLiveAt (timestamp expiry : B256) : Prop :=
  timestamp < expiry

/-- Exact EVM word returned by `isPauserLive(address)`. -/
def pauserLiveWord (timestamp expiry : B256) : B256 :=
  B256.ltCheck timestamp expiry

theorem IsPauserLiveAt.irrefl (timestamp : B256) :
    ¬ IsPauserLiveAt timestamp timestamp := by
  simp [IsPauserLiveAt]

theorem pauserLiveWord_eq_zero_at_expiry (expiry : B256) :
    pauserLiveWord expiry expiry = 0 := by
  simp [pauserLiveWord, B256.ltCheck]

theorem pauserLiveWord_eq_zero_of_expired {timestamp expiry : B256}
    (expired : expiry ≤ timestamp) :
    pauserLiveWord timestamp expiry = 0 := by
  simp [pauserLiveWord, B256.ltCheck, B256.not_lt.mpr expired]

/-- Mathematical specification of the runtime's checked
`timestamp + heartbeatInterval` operation. -/
def CheckedHeartbeatExtension
    (timestamp interval expiry : B256) : Prop :=
  timestamp.toNat + interval.toNat < 2 ^ 256 ∧
    expiry = Nat.toB256 (timestamp.toNat + interval.toNat)

theorem CheckedHeartbeatExtension.strict_of_interval_pos
    {timestamp interval expiry : B256}
    (extension : CheckedHeartbeatExtension timestamp interval expiry)
    (positive : 0 < interval.toNat) :
    IsPauserLiveAt timestamp expiry := by
  rcases extension with ⟨bound, rfl⟩
  rw [IsPauserLiveAt, B256.lt_iff_toNat_lt_toNat,
    B256.toNat_toB256_of_lt bound]
  omega

theorem CheckedHeartbeatExtension.add_eq
    {timestamp interval expiry : B256}
    (extension : CheckedHeartbeatExtension timestamp interval expiry) :
    timestamp + interval = expiry := by
  rcases extension with ⟨bound, rfl⟩
  have hnof : timestamp.Nof interval := bound
  rw [← Jaune.toB256_toNat (timestamp + interval),
    Jaune.B256.toNat_add_eq_of_nof _ _ hnof]

def checkedHeartbeatExpiryGasWarm : Nat := 132

set_option maxRecDepth 4096 in
/-- The successful arm of the checked heartbeat addition is an exact compiled
walk.  Its result remains on the stack for the caller's store-and-log tail. -/
theorem checkedHeartbeatExpiry_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (timestamp interval expiry : B256) (G : Nat)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (extension : CheckedHeartbeatExtension timestamp interval expiry) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + checkedHeartbeatExpiryGasWarm⟩)
      (checkedHeartbeatExpiry Func.stop)
      (base.setMach ⟨[expiry], Mem.empty, G⟩) := by
  rcases extension with ⟨bound, hexpiry⟩
  have hsum : timestamp + interval = expiry :=
    CheckedHeartbeatExtension.add_eq ⟨bound, hexpiry⟩
  have hle : timestamp ≤ expiry := by
    rw [B256.le_iff_toNat_le_toNat, hexpiry,
      B256.toNat_toB256_of_lt bound]
    omega
  unfold checkedHeartbeatExpiry checkedHeartbeatExpiryGasWarm
  func_run [expiry, 0]
  case h_val =>
    simp only [Devm.getStorVal_setMach, hinterval, htime]
    rw [B256.add_comm]
    exact hsum
  case h_val =>
    rw [htime]
    simp only [B256.ltCheck, if_neg (not_lt_of_ge hle)]
  case h_arm =>
    exact Func.RunCompiled.last rfl

def heartbeatBodySuccessGasWarmUpdate : Nat := 4693

set_option maxRecDepth 8192 in
/-- A successful direct heartbeat-body execution in the warm, nonzero-to-
nonzero storage-update case.  The run fixes the checked sum, the exact expiry
write, and the single `HeartbeatUpdated` log emitted after that write. -/
theorem heartbeat_body_runCompiled_of_checkedExtension
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (count oldExpiry timestamp interval expiry : B256) (G : Nat)
    (htime : sevm.benvStat.time = timestamp)
    (hcount : Devm.getStorVal base sevm.currentTarget
      (countSlot sevm.caller.toB256) = count)
    (hcountNonzero : count ≠ 0)
    (holdExpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (horigExpiry : getOrigStorVal sevm sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (hinterval : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarmCount : (⟨sevm.currentTarget,
      countSlot sevm.caller.toB256⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hwarmInterval : (⟨sevm.currentTarget,
      heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (holdLive : timestamp < oldExpiry)
    (holdNonzero : oldExpiry ≠ 0)
    (hchanged : oldExpiry ≠ expiry)
    (extension : CheckedHeartbeatExtension timestamp interval expiry) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty,
          G + heartbeatBodySuccessGasWarmUpdate⟩)
        heartbeat post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        (expirySlot sevm.caller.toB256) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, sevm.caller.toB256], expiry.toBytes⟩] := by
  have hsum := CheckedHeartbeatExtension.add_eq extension
  rcases extension with ⟨bound, hexpiry⟩
  have hle : timestamp ≤ expiry := by
    rw [B256.le_iff_toNat_le_toNat, hexpiry,
      B256.toNat_toB256_of_lt bound]
    omega
  unfold heartbeat checkedHeartbeatExpiry storeHeartbeatExpiryFromStack
    tagTop mstoreAt logWith heartbeatBodySuccessGasWarmUpdate
  apply Exists.intro
  constructor
  · func_run [countSlot sevm.caller.toB256, 0,
      expirySlot sevm.caller.toB256, 1, expiry, 0,
      3, expirySlot sevm.caller.toB256, 2900, 1381]
    all_goals try {
      simp only [Devm.getStorVal_setMach, hcount]
      simp [B256.eqCheck, hcountNonzero] }
    all_goals try {
      simp only [Devm.getStorVal_setMach, holdExpiry, htime]
      simp [B256.ltCheck, holdLive] }
    all_goals try {
      simp only [Devm.getStorVal_setMach, hinterval, htime]
      rw [B256.add_comm]
      exact hsum }
    all_goals try {
      rw [htime]
      simp only [B256.ltCheck, if_neg (not_lt_of_ge hle)] }
    case h_ext =>
      change (base.setMach
        ⟨[0, expiry, expiry], Mem.empty, G + 4693 - 388⟩).extCost
          [⟨0, 32⟩] = 3
      simpa [gMemory] using
        (Devm.extCost_empty_word (devm := base) (S := [0, expiry, expiry])
          (G := G + 4693 - 388))
    all_goals try {
      rw [horigExpiry, Devm.getStorVal_setMach, holdExpiry]
      rw [sstoreValueCost, if_pos ⟨rfl, hchanged⟩,
        if_neg holdNonzero]
      norm_num [gasStorageUpdate, gasColdSload] }
    case h_cost =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((1 : B256) * 32).toNat = 32 by decide]
      rw [Devm.extCost_word_word Mem.size_write_word]
      norm_num [gLog, gLogdata, gLogtopic]
    case a => exact Func.RunCompiled.last rfl
  · refine ⟨?_, ?_, ?_⟩
    · simp only [Devm.gasLeft_setMach]
      omega
    · rw [Devm.getStorVal_setMach]
      have getStorVal_addLog (d : Devm) (log : Log)
          (a : Adr) (k : B256) :
          (d.addLog log).getStorVal a k = d.getStorVal a k := rfl
      rw [getStorVal_addLog, Devm.getStorVal_setMach]
      show (Devm.getStor _ sevm.currentTarget).get
        (expirySlot sevm.caller.toB256) = expiry
      rw [setStorVal_getStor_self, Stor.get_set_self]
    · have logs_setMach (d : Devm) (mach : Mach) :
          (d.setMach mach).logs = d.logs := rfl
      have logs_addLog (d : Devm) (log : Log) :
          (d.addLog log).logs = d.logs ++ [log] := rfl
      have logs_setStorVal (d : Devm) (a : Adr) (k v : B256) :
          (d.setStorVal a k v).logs = d.logs := rfl
      have logs_withRefundCounter (d : Devm) (rc : Int) :
          (d.withRefundCounter rc).logs = d.logs := rfl
      rw [logs_setMach, logs_addLog, logs_setMach, logs_setStorVal,
        logs_withRefundCounter, logs_setMach]
      rw [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((1 : B256) * 32).toNat = 32 by decide]
      rw [Mem.read_write_word]

/-! ## Representative strict-liveness compiled cut -/

private theorem temporalReturnWord_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (word : B256) (G : Nat) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[0, 32], Mem.empty.write 0 word.toBytes, G⟩)
        Func.ret post ∧
      Devm.output post = word.toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs := by
  let retPre := base.setMach
    ⟨[0, 32], Mem.empty.write 0 word.toBytes, G⟩
  let d := (retPre.setMach ⟨[], retPre.memory, G⟩).memRead 0 32
  let post := d.2.withOutput word.toBytes
  refine ⟨post, ?_, rfl, ?_, rfl⟩
  have hread :
      (retPre.setMach ⟨[], retPre.memory, G⟩).memRead 0 32 =
        ⟨word.toBytes, d.2⟩ := by
    exact Prod.ext
      (Devm.memRead_word_fst
        (by simp only [retPre, Devm.memory_setMach]))
      rfl
  exact Func.runCompiled_ret_of (devm := retPre) (G := G) (e := 0)
    (out := word.toBytes) (d' := d.2) rfl
    (Devm.extCost_word_word Mem.size_write_word) rfl hread
  · exact ⟨rfl, rfl⟩

def temporalLiveBodyGasWarm : Nat := 184

/-- The complete decoded body returns false when the stored expiry equals the
block timestamp.  The exact EVM walk includes the calldata bound, canonical
address check, warm expiry SLOAD, timestamp, strict LT, ABI store, and return. -/
theorem isPauserLive_body_runCompiled_at_expiry
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (pauser : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = sevm.benvStat.time)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty, G + temporalLiveBodyGasWarm⟩)
        isPauserLive post ∧
      Devm.output post = (0 : B256).toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs := by
  have hcanonical := canonicalAddress_mask_zero hpauser
  unfold isPauserLive requireStaticArgs canonicalAddressArg arg cdl
    checkNonAddress pushAddressMask tagTop returnWord mstoreAt
    returnMemoryRange pushList temporalLiveBodyGasWarm
  have hword0 : Sevm.dataWord sevm (32 * 0 + 4) = pauser := hword
  have hgasFinal : G + 184 - 184 = G := by omega
  rcases temporalReturnWord_runCompiled fs sevm base (0 : B256) G with
    ⟨post, hreturn, houtput⟩
  refine ⟨post, ?_, houtput⟩
  set_option maxRecDepth 4096 in
    func_run [0, ~~~(0 : B256), addressMask, 0, expirySlot pauser, 0, 3]
  all_goals try { rw [hword0]; exact hcanonical }
  all_goals try { rw [hword0]; rfl }
  case h_val =>
    change sevm.benvStat.time <? Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = 0
    rw [hexpiry]
    simp [B256.ltCheck]
  case h_ext =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word
  case a =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide,
      hgasFinal]
    exact hreturn

def isPauserLiveDispatchGas : Nat := 168

set_option maxRecDepth 4096 in
/-- Exact public-dispatch representative at the strict expiry boundary.  The
result fixes the deployed program/compiler identity in addition to the decoded
body semantics. -/
theorem isPauserLive_runCompiled_at_expiry
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (pauser : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "isPauserLive" [.address])
    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = sevm.benvStat.time)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + isPauserLiveDispatchGas + temporalLiveBodyGasWarm⟩)
        (runtime dp) post ∧
      Devm.output post = (0 : B256).toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdata]
    decide
  rcases isPauserLive_body_runCompiled_at_expiry
      (runtimeMain dp :: aux) sevm base pauser G
      hbodyData hword hpauser hexpiry hwarm with
    ⟨post, hbody, houtput, hworld, hlogs⟩
  refine ⟨post, ?_, houtput, hworld, hlogs, ?_⟩
  · refine Prog.runCompiled_intro
      (mid := base.setMach ⟨[], Mem.empty,
        G + 167 + temporalLiveBodyGasWarm⟩)
      (G := G + 167 + temporalLiveBodyGasWarm) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, isPauserLiveDispatchGas, gJumpdest]
      omega
    · rfl
    · have hvalueZero : B256.eqCheck sevm.value 0 = 1 := by
        simp [B256.eqCheck, hvalue]
      have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "isPauserLive" [.address] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (33) [0, 0, selector "isPauserLive" [.address],
        0, 0, 0, 0, 0, 1]
      have hboundary :
          G + 167 + temporalLiveBodyGasWarm - 167 =
            G + temporalLiveBodyGasWarm := by omega
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
        runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
        List.take, List.drop, List.head?, Option.map, Option.getD,
        linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

/-! ## Exact temporal views -/

theorem pauserLiveWord_eq_one_of_live {timestamp expiry : B256}
    (live : IsPauserLiveAt timestamp expiry) :
    pauserLiveWord timestamp expiry = 1 := by
  change timestamp < expiry at live
  have hnot : ¬ expiry ≤ timestamp := B256.not_le.mpr live
  simp [pauserLiveWord, B256.ltCheck, hnot]

/-- The decoded liveness body returns the exact strict-comparison word for an
arbitrary stored expiry. -/
theorem isPauserLive_body_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (pauser expiry : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = expiry)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty, G + temporalLiveBodyGasWarm⟩)
        isPauserLive post ∧
      Devm.output post =
        (pauserLiveWord sevm.benvStat.time expiry).toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs := by
  have hcanonical := canonicalAddress_mask_zero hpauser
  unfold isPauserLive requireStaticArgs canonicalAddressArg arg cdl
    checkNonAddress pushAddressMask tagTop returnWord mstoreAt
    returnMemoryRange pushList temporalLiveBodyGasWarm
  have hword0 : Sevm.dataWord sevm (32 * 0 + 4) = pauser := hword
  have hgasFinal : G + 184 - 184 = G := by omega
  rcases temporalReturnWord_runCompiled fs sevm base
      (pauserLiveWord sevm.benvStat.time expiry) G with
    ⟨post, hreturn, houtput⟩
  refine ⟨post, ?_, houtput⟩
  set_option maxRecDepth 4096 in
    func_run [0, ~~~(0 : B256), addressMask, 0, expirySlot pauser,
      pauserLiveWord sevm.benvStat.time expiry, 3]
  all_goals try { rw [hword0]; exact hcanonical }
  all_goals try { rw [hword0]; rfl }
  case h_val =>
    change sevm.benvStat.time <? Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = pauserLiveWord sevm.benvStat.time expiry
    rw [hexpiry]
    rfl
  case h_ext =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word
  case a =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide,
      hgasFinal]
    exact hreturn

set_option maxRecDepth 4096 in
/-- Exact direct public execution of `isPauserLive(address)` for an arbitrary
stored expiry. -/
theorem isPauserLive_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (pauser expiry : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "isPauserLive" [.address])
    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = expiry)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + isPauserLiveDispatchGas + temporalLiveBodyGasWarm⟩)
        (runtime dp) post ∧
      Devm.output post =
        (pauserLiveWord sevm.benvStat.time expiry).toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdata]
    decide
  rcases isPauserLive_body_runCompiled
      (runtimeMain dp :: aux) sevm base pauser expiry G
      hbodyData hword hpauser hexpiry hwarm with
    ⟨post, hbody, houtput, hworld, hlogs⟩
  refine ⟨post, ?_, houtput, hworld, hlogs, ?_⟩
  · refine Prog.runCompiled_intro
      (mid := base.setMach ⟨[], Mem.empty,
        G + 167 + temporalLiveBodyGasWarm⟩)
      (G := G + 167 + temporalLiveBodyGasWarm) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, isPauserLiveDispatchGas,
        gJumpdest]
      omega
    · rfl
    · have hvalueZero : B256.eqCheck sevm.value 0 = 1 := by
        simp [B256.eqCheck, hvalue]
      have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "isPauserLive" [.address] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (33) [0, 0, selector "isPauserLive" [.address],
        0, 0, 0, 0, 0, 1]
      have hboundary :
          G + 167 + temporalLiveBodyGasWarm - 167 =
            G + temporalLiveBodyGasWarm := by omega
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
        runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
        List.take, List.drop, List.head?, Option.map, Option.getD,
        linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

def heartbeatIntervalBodyGasWarm : Nat := 116
def heartbeatIntervalDispatchGas : Nat := 152

theorem heartbeatInterval_body_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (interval : B256) (G : Nat)
    (hinterval : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty, G + heartbeatIntervalBodyGasWarm⟩)
        heartbeatInterval post ∧
      Devm.output post = interval.toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs := by
  unfold heartbeatInterval returnWord mstoreAt returnMemoryRange pushList
    heartbeatIntervalBodyGasWarm
  have hgasFinal : G + 116 - 116 = G := by omega
  rcases temporalReturnWord_runCompiled fs sevm base interval G with
    ⟨post, hreturn, houtput⟩
  refine ⟨post, ?_, houtput⟩
  func_run [3]
  case h_ext =>
    exact Devm.extCost_empty_word
  case a =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide,
      Devm.getStorVal_setMach, hinterval, hgasFinal]
    exact hreturn

set_option maxRecDepth 4096 in
/-- Exact direct public execution of `heartbeatInterval()`. -/
theorem heartbeatInterval_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (interval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 4)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "heartbeatInterval" [])
    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hinterval : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + heartbeatIntervalDispatchGas + heartbeatIntervalBodyGasWarm⟩)
        (runtime dp) post ∧
      Devm.output post = interval.toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases heartbeatInterval_body_runCompiled
      (runtimeMain dp :: aux) sevm base interval G hinterval hwarm with
    ⟨post, hbody, houtput, hworld, hlogs⟩
  refine ⟨post, ?_, houtput, hworld, hlogs, ?_⟩
  · refine Prog.runCompiled_intro
      (mid := base.setMach ⟨[], Mem.empty,
        G + 151 + heartbeatIntervalBodyGasWarm⟩)
      (G := G + 151 + heartbeatIntervalBodyGasWarm) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, heartbeatIntervalDispatchGas,
        gJumpdest]
      omega
    · rfl
    · have hvalueZero : B256.eqCheck sevm.value 0 = 1 := by
        simp [B256.eqCheck, hvalue]
      have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "heartbeatInterval" [] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (31) [0, 0, selector "heartbeatInterval" [],
        1, 0, 0, 0, 1]
      have hboundary :
          G + 151 + heartbeatIntervalBodyGasWarm - 151 =
            G + heartbeatIntervalBodyGasWarm := by omega
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
        runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
        List.take, List.drop, List.head?, Option.map, Option.getD,
        linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

def heartbeatExpiryBodyGasWarm : Nat := 179
def heartbeatExpiryDispatchGas : Nat := 129

theorem heartbeatExpiry_body_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (pauser expiry : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = expiry)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty, G + heartbeatExpiryBodyGasWarm⟩)
        heartbeatExpiry post ∧
      Devm.output post = expiry.toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs := by
  have hcanonical := canonicalAddress_mask_zero hpauser
  unfold heartbeatExpiry requireStaticArgs canonicalAddressArg arg cdl
    checkNonAddress pushAddressMask tagTop returnWord mstoreAt
    returnMemoryRange pushList heartbeatExpiryBodyGasWarm
  have hword0 : Sevm.dataWord sevm (32 * 0 + 4) = pauser := hword
  have hgasFinal : G + 179 - 179 = G := by omega
  rcases temporalReturnWord_runCompiled fs sevm base expiry G with
    ⟨post, hreturn, houtput⟩
  refine ⟨post, ?_, houtput⟩
  set_option maxRecDepth 4096 in
    func_run [0, ~~~(0 : B256), addressMask, 0, expirySlot pauser, 3]
  all_goals try { rw [hword0]; exact hcanonical }
  all_goals try { rw [hword0]; rfl }
  case h_ext =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word
  case a =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide,
      Devm.getStorVal_setMach, hexpiry, hgasFinal]
    exact hreturn

set_option maxRecDepth 4096 in
/-- Exact direct public execution of canonical `heartbeatExpiry(address)`. -/
theorem heartbeatExpiry_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (pauser expiry : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "heartbeatExpiry" [.address])
    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = expiry)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + heartbeatExpiryDispatchGas + heartbeatExpiryBodyGasWarm⟩)
        (runtime dp) post ∧
      Devm.output post = expiry.toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdata]
    decide
  rcases heartbeatExpiry_body_runCompiled
      (runtimeMain dp :: aux) sevm base pauser expiry G
      hbodyData hword hpauser hexpiry hwarm with
    ⟨post, hbody, houtput, hworld, hlogs⟩
  refine ⟨post, ?_, houtput, hworld, hlogs, ?_⟩
  · refine Prog.runCompiled_intro
      (mid := base.setMach ⟨[], Mem.empty,
        G + 128 + heartbeatExpiryBodyGasWarm⟩)
      (G := G + 128 + heartbeatExpiryBodyGasWarm) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, heartbeatExpiryDispatchGas,
        gJumpdest]
      omega
    · rfl
    · have hvalueZero : B256.eqCheck sevm.value 0 = 1 := by
        simp [B256.eqCheck, hvalue]
      have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "heartbeatExpiry" [.address] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (27) [0, 0, selector "heartbeatExpiry" [.address],
        0, 0, 0, 1]
      have hboundary :
          G + 128 + heartbeatExpiryBodyGasWarm - 128 =
            G + heartbeatExpiryBodyGasWarm := by omega
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
        runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
        List.take, List.drop, List.head?, Option.map, Option.getD,
        linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

/-! ## Public strict-liveness corollaries -/

theorem isPauserLive_runCompiled_of_live
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (pauser expiry : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "isPauserLive" [.address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = expiry)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (live : IsPauserLiveAt sevm.benvStat.time expiry) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + isPauserLiveDispatchGas + temporalLiveBodyGasWarm⟩)
        (runtime dp) post ∧
      Devm.output post = (1 : B256).toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases isPauserLive_runCompiled dp sevm base pauser expiry G
      hdata hvalue hselector hcodeAddress hcode hword hpauser hexpiry hwarm with
    ⟨post, hrun, houtput, hworld, hlogs, hcompile⟩
  refine ⟨post, hrun, ?_, hworld, hlogs, hcompile⟩
  rw [houtput, pauserLiveWord_eq_one_of_live live]

theorem isPauserLive_runCompiled_of_later
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (pauser expiry : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "isPauserLive" [.address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = expiry)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (later : expiry < sevm.benvStat.time) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + isPauserLiveDispatchGas + temporalLiveBodyGasWarm⟩)
        (runtime dp) post ∧
      Devm.output post = (0 : B256).toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases isPauserLive_runCompiled dp sevm base pauser expiry G
      hdata hvalue hselector hcodeAddress hcode hword hpauser hexpiry hwarm with
    ⟨post, hrun, houtput, hworld, hlogs, hcompile⟩
  refine ⟨post, hrun, ?_, hworld, hlogs, hcompile⟩
  rw [houtput, pauserLiveWord_eq_zero_of_expired (B256.le_of_lt later)]

/-! ## Heartbeat-interval transition -/

/-- A canonical expiry key is disjoint from the heartbeat-interval
configuration key.  This is the storage-separation fact used by the exact
setter transition below. -/
theorem expirySlot_ne_heartbeatIntervalSlot
    (pauser : B256) (hpauser : canonicalAddress pauser) :
    expirySlot pauser ≠ heartbeatIntervalSlot := by
  have hpayload : pauser.toNat < 2 ^ 252 := by
    unfold canonicalAddress at hpauser
    exact lt_trans hpauser (by norm_num)
  simpa [expirySlot, heartbeatIntervalSlot] using
    slot_ne_of_region_ne
      (leftRegion := expiryRegion) (rightRegion := configRegion)
      (left := pauser) (right := (1 : B256))
      (by norm_num [expiryRegion]) (by norm_num [configRegion])
      hpayload
      (by
        change (1 : Nat) < 2 ^ 252
        norm_num)
      (by norm_num [expiryRegion, configRegion])

private def setHeartbeatIntervalStoreTail : Func :=
  arg 0 +++ Ninst.pushB256 heartbeatIntervalSlot :::
    Ninst.sstore ::: Func.stop

private def setHeartbeatIntervalStoreTailGasWarmUpdate : Nat := 2909

private def setHeartbeatIntervalStoreTailGasWarmSet : Nat := 20009

private def setHeartbeatIntervalEventTail : Func :=
  Ninst.pushB256 heartbeatIntervalUpdatedEvent :::
    logWith 0 0 2 +++ setHeartbeatIntervalStoreTail

private def setHeartbeatIntervalEventTailGasWarmUpdate : Nat := 4179

private def setHeartbeatIntervalEventTailGasWarmSet : Nat := 21279

private def setHeartbeatIntervalUpdateTail : Func :=
  Ninst.pushB256 heartbeatIntervalSlot ::: Ninst.sload :::
    mstoreAt 0 +++ arg 0 +++ mstoreAt 1 +++
      setHeartbeatIntervalEventTail

private def setHeartbeatIntervalUpdateTailGasWarmUpdate : Nat := 4305

private def setHeartbeatIntervalUpdateTailGasWarmSet : Nat := 21405

/-- Exact source-body charge for the warm nonzero-to-different-nonzero
successful setter path. -/
def setHeartbeatIntervalBodyGasWarmUpdate : Nat := 4398

/-- Exact source-body charge for a warm zero-to-nonzero setter path. -/
def setHeartbeatIntervalBodyGasWarmSet : Nat := 21498

def setHeartbeatIntervalDispatchGas : Nat := 169

/-- The two ABI words staged for `HeartbeatIntervalUpdated` read back as the
exact old/new event payload. -/
private theorem setHeartbeatIntervalEventData
    (old newInterval : B256) :
    (((Mem.empty.write 0 old.toBytes).write 32 newInterval.toBytes).read
      0 64).1 = old.toBytes ++ newInterval.toBytes := by
  have hfirst : Bytes.writeAt [] 0 old.toBytes = old.toBytes := by
    simp [Bytes.writeAt]
  have hsecond : Bytes.writeAt old.toBytes 32 newInterval.toBytes =
      old.toBytes ++ newInterval.toBytes :=
    Bytes.writeAt_of_length_eq (B256.length_toBytes old)
  have hreads₀ : Mem.Reads Mem.empty [] := Mem.reads_empty
  have hreads₁ := Mem.Reads.write Mem.wf_empty hreads₀ 0 old.toBytes
  rw [hfirst] at hreads₁
  have hwf₁ := Mem.Wf.write Mem.wf_empty 0 old.toBytes
  have hreads₂ := Mem.Reads.write hwf₁ hreads₁ 32
    newInterval.toBytes
  rw [hsecond] at hreads₂
  rw [Mem.Reads.read hreads₂]
  show List.takeD 64
      (List.drop 0 (old.toBytes ++ newInterval.toBytes)) 0 = _
  rw [List.drop_zero, List.takeD_eq_self 0 (by
    simp [B256.length_toBytes])]

set_option maxRecDepth 4096 in
/-- Exact final store suffix of the successful heartbeat-interval setter.
The suffix starts after the event has been emitted, so it preserves that log
list while changing only the named configuration key. -/
private theorem setHeartbeatIntervalStoreTail_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (memory : Mem)
    (old newInterval : B256) (G : Nat)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = old)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = old)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (holdNonzero : old ≠ 0)
    (hchanged : old ≠ newInterval) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], memory,
          G + setHeartbeatIntervalStoreTailGasWarmUpdate⟩)
        setHeartbeatIntervalStoreTail post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  have hsstoreCost : sstoreValueCost old old newInterval = 2900 := by
    rw [sstoreValueCost, if_pos ⟨rfl, hchanged⟩, if_neg holdNonzero]
    norm_num [gasStorageUpdate, gasColdSload]
  unfold setHeartbeatIntervalStoreTail
    setHeartbeatIntervalStoreTailGasWarmUpdate
  apply Exists.intro
  constructor
  · func_run [2900]
    case h_cost =>
      simpa only [Devm.getStorVal_setMach, horig, hold, harg] using
        hsstoreCost
    case a => exact Func.RunCompiled.last rfl
  · simp only [Devm.gasLeft_setMach]
    refine ⟨by omega, ?_, rfl, ?_⟩
    rw [Devm.getStorVal_setMach]
    show (Devm.getStor _ sevm.currentTarget).get heartbeatIntervalSlot =
      newInterval
    rw [setStorVal_getStor_self, Stor.get_set_self, harg]
    intro pauser hpauser
    rw [Devm.getStorVal_setMach]
    show (Devm.getStor _ sevm.currentTarget).get (expirySlot pauser) =
      Devm.getStorVal base sevm.currentTarget (expirySlot pauser)
    rw [setStorVal_getStor_self, Stor.get_set_ne _
      (expirySlot_ne_heartbeatIntervalSlot pauser hpauser).symm, harg]
    rfl

set_option maxRecDepth 4096 in
/-- Exact warm zero-to-nonzero storage-price companion. -/
private theorem setHeartbeatIntervalStoreTail_runCompiled_zero
    (fs : List Func) (sevm : Sevm) (base : Devm) (memory : Mem)
    (newInterval : B256) (G : Nat)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hnewNonzero : newInterval ≠ 0) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], memory,
          G + setHeartbeatIntervalStoreTailGasWarmSet⟩)
        setHeartbeatIntervalStoreTail post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  have hsstoreCost : sstoreValueCost 0 0 newInterval = 20000 := by
    rw [sstoreValueCost, if_pos ⟨rfl, hnewNonzero.symm⟩, if_pos rfl]
    norm_num [gasStorageSet]
  unfold setHeartbeatIntervalStoreTail
    setHeartbeatIntervalStoreTailGasWarmSet
  apply Exists.intro
  constructor
  · func_run [20000]
    case h_cost =>
      simpa only [Devm.getStorVal_setMach, horig, hold, harg] using
        hsstoreCost
    case a => exact Func.RunCompiled.last rfl
  · simp only [Devm.gasLeft_setMach]
    refine ⟨by omega, ?_, rfl, ?_⟩
    · rw [Devm.getStorVal_setMach]
      show (Devm.getStor _ sevm.currentTarget).get heartbeatIntervalSlot =
        newInterval
      rw [setStorVal_getStor_self, Stor.get_set_self, harg]
    · intro pauser hpauser
      rw [Devm.getStorVal_setMach]
      show (Devm.getStor _ sevm.currentTarget).get (expirySlot pauser) =
        Devm.getStorVal base sevm.currentTarget (expirySlot pauser)
      rw [setStorVal_getStor_self, Stor.get_set_ne _
        (expirySlot_ne_heartbeatIntervalSlot pauser hpauser).symm, harg]
      rfl

set_option maxRecDepth 4096 in
/-- No-op storage-price companion to the changed-value suffix.  The caller
supplies the same 2909-unit suffix budget, so the exact 109-unit warm no-op
store leaves 2800 additional gas. -/
private theorem setHeartbeatIntervalStoreTail_runCompiled_noop
    (fs : List Func) (sevm : Sevm) (base : Devm) (memory : Mem)
    (interval : B256) (G : Nat)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = interval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], memory,
          G + setHeartbeatIntervalStoreTailGasWarmUpdate⟩)
        setHeartbeatIntervalStoreTail post ∧
      post.gasLeft = G + 2800 ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = interval ∧
      post.logs = base.logs ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  have hsstoreCost : sstoreValueCost interval interval interval = 100 := by
    simp [sstoreValueCost, gasWarmAccess]
  unfold setHeartbeatIntervalStoreTail
    setHeartbeatIntervalStoreTailGasWarmUpdate
  apply Exists.intro
  constructor
  · func_run [100]
    case h_cost =>
      simpa only [Devm.getStorVal_setMach, horig, hold, harg] using
        hsstoreCost
    case a => exact Func.RunCompiled.last rfl
  · simp only [Devm.gasLeft_setMach]
    refine ⟨by omega, ?_, rfl, ?_⟩
    · rw [Devm.getStorVal_setMach]
      show (Devm.getStor _ sevm.currentTarget).get heartbeatIntervalSlot =
        interval
      rw [setStorVal_getStor_self, Stor.get_set_self, harg]
    · intro pauser hpauser
      rw [Devm.getStorVal_setMach]
      show (Devm.getStor _ sevm.currentTarget).get (expirySlot pauser) =
        Devm.getStorVal base sevm.currentTarget (expirySlot pauser)
      rw [setStorVal_getStor_self, Stor.get_set_ne _
        (expirySlot_ne_heartbeatIntervalSlot pauser hpauser).symm, harg]
      rfl

set_option maxRecDepth 16384 in
/-- The successful event suffix emits the exact old/new record and then runs
the named store suffix.  Thus the source chronology is represented directly:
the `LOG1` predecessor is constructed before the `SSTORE` continuation. -/
private theorem setHeartbeatIntervalEventTail_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (old newInterval : B256) (G : Nat)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = old)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = old)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (holdNonzero : old ≠ 0)
    (hchanged : old ≠ newInterval) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach
          ⟨[], (Mem.empty.write 0 old.toBytes).write 32 newInterval.toBytes,
            G + setHeartbeatIntervalEventTailGasWarmUpdate⟩)
        setHeartbeatIntervalEventTail post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          old.toBytes ++ newInterval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  let event : Log :=
    ⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
      old.toBytes ++ newInterval.toBytes⟩
  rcases setHeartbeatIntervalStoreTail_runCompiled fs sevm
      (base.addLog event)
      ((Mem.empty.write 0 old.toBytes).write 32 newInterval.toBytes)
      old newInterval G harg hold horig hwarm hstatic holdNonzero hchanged with
    ⟨post, htail, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, ?_, ?_⟩
  · unfold setHeartbeatIntervalEventTail
    unfold logWith
    func_run (4) [1262]
    all_goals try {
      simp only [Devm.gasLeft_setMach,
        setHeartbeatIntervalEventTailGasWarmUpdate]
      omega }
    case h_cost =>
      rw [show ((2 : B256) * 32).toNat = 64 by decide,
        show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_of_size (by
        rw [Mem.size_write_word_at, Mem.size_write_word]) rfl]
      decide
    case a =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((2 : B256) * 32).toNat = 64 by decide]
      rw [setHeartbeatIntervalEventData old newInterval,
        Mem.read_snd_eq_self (by
          rw [Mem.size_write_word_at, Mem.size_write_word]
          decide)]
      change Func.RunCompiled fs sevm
        ((base.addLog event).setMach
          ⟨[], (Mem.empty.write 0 old.toBytes).write 32 newInterval.toBytes,
            G + 2909⟩)
        setHeartbeatIntervalStoreTail post
      exact htail
  · rw [hlogs]
    rfl
  · intro pauser hpauser
    rw [hexpiries pauser hpauser]
    rfl

set_option maxRecDepth 16384 in
private theorem setHeartbeatIntervalEventTail_runCompiled_zero
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (newInterval : B256) (G : Nat)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hnewNonzero : newInterval ≠ 0) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach
          ⟨[], (Mem.empty.write 0 (0 : B256).toBytes).write 32
              newInterval.toBytes,
            G + setHeartbeatIntervalEventTailGasWarmSet⟩)
        setHeartbeatIntervalEventTail post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          (0 : B256).toBytes ++ newInterval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  let event : Log :=
    ⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
      (0 : B256).toBytes ++ newInterval.toBytes⟩
  rcases setHeartbeatIntervalStoreTail_runCompiled_zero fs sevm
      (base.addLog event)
      ((Mem.empty.write 0 (0 : B256).toBytes).write 32 newInterval.toBytes)
      newInterval G harg hold horig hwarm hstatic hnewNonzero with
    ⟨post, htail, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, ?_, ?_⟩
  · unfold setHeartbeatIntervalEventTail logWith
    func_run (4) [1262]
    all_goals try {
      simp only [Devm.gasLeft_setMach,
        setHeartbeatIntervalEventTailGasWarmSet]
      omega }
    case h_cost =>
      rw [show ((2 : B256) * 32).toNat = 64 by decide,
        show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_of_size (by
        rw [Mem.size_write_word_at, Mem.size_write_word]) rfl]
      decide
    case a =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((2 : B256) * 32).toNat = 64 by decide]
      rw [setHeartbeatIntervalEventData 0 newInterval,
        Mem.read_snd_eq_self (by
          rw [Mem.size_write_word_at, Mem.size_write_word]
          decide)]
      change Func.RunCompiled fs sevm
        ((base.addLog event).setMach
          ⟨[], (Mem.empty.write 0 (0 : B256).toBytes).write 32
              newInterval.toBytes,
            G + 20009⟩)
        setHeartbeatIntervalStoreTail post
      exact htail
  · rw [hlogs]
    rfl
  · intro pauser hpauser
    rw [hexpiries pauser hpauser]
    rfl

set_option maxRecDepth 16384 in
private theorem setHeartbeatIntervalEventTail_runCompiled_noop
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (interval : B256) (G : Nat)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = interval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach
          ⟨[], (Mem.empty.write 0 interval.toBytes).write 32 interval.toBytes,
            G + setHeartbeatIntervalEventTailGasWarmUpdate⟩)
        setHeartbeatIntervalEventTail post ∧
      post.gasLeft = G + 2800 ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = interval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          interval.toBytes ++ interval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  let event : Log :=
    ⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
      interval.toBytes ++ interval.toBytes⟩
  rcases setHeartbeatIntervalStoreTail_runCompiled_noop fs sevm
      (base.addLog event)
      ((Mem.empty.write 0 interval.toBytes).write 32 interval.toBytes)
      interval G harg hold horig hwarm hstatic with
    ⟨post, htail, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, ?_, ?_⟩
  · unfold setHeartbeatIntervalEventTail logWith
    func_run (4) [1262]
    all_goals try {
      simp only [Devm.gasLeft_setMach,
        setHeartbeatIntervalEventTailGasWarmUpdate]
      omega }
    case h_cost =>
      rw [show ((2 : B256) * 32).toNat = 64 by decide,
        show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_of_size (by
        rw [Mem.size_write_word_at, Mem.size_write_word]) rfl]
      decide
    case a =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((2 : B256) * 32).toNat = 64 by decide]
      rw [setHeartbeatIntervalEventData interval interval,
        Mem.read_snd_eq_self (by
          rw [Mem.size_write_word_at, Mem.size_write_word]
          decide)]
      change Func.RunCompiled fs sevm
        ((base.addLog event).setMach
          ⟨[], (Mem.empty.write 0 interval.toBytes).write 32 interval.toBytes,
            G + 2909⟩)
        setHeartbeatIntervalStoreTail post
      exact htail
  · rw [hlogs]
    rfl
  · intro pauser hpauser
    rw [hexpiries pauser hpauser]
    rfl

set_option maxRecDepth 8192 in
/-- The successful update tail reads the exact old word, stages old/new ABI
words, and enters the event-before-store suffix. -/
private theorem setHeartbeatIntervalUpdateTail_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (old newInterval : B256) (G : Nat)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = old)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = old)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (holdNonzero : old ≠ 0)
    (hchanged : old ≠ newInterval) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalUpdateTailGasWarmUpdate⟩)
        setHeartbeatIntervalUpdateTail post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          old.toBytes ++ newInterval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  rcases setHeartbeatIntervalEventTail_runCompiled fs sevm base
      old newInterval G harg hold horig hwarm hstatic holdNonzero hchanged with
    ⟨post, htail, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, hlogs, hexpiries⟩
  unfold setHeartbeatIntervalUpdateTail arg mstoreAt
  func_run (8) [3, 3]
  all_goals try {
    simp only [Devm.gasLeft_setMach,
      setHeartbeatIntervalUpdateTailGasWarmUpdate]
    norm_num [gasWarmAccess, gVerylow] <;> omega }
  case h_ext =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word
  case h_ext =>
    rw [show ((1 : B256) * 32).toNat = 32 by decide]
    exact Devm.extCost_of_size Mem.size_write_word (by decide)
  case a =>
    simp only [Devm.getStorVal_setMach, hold, harg]
    change Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], (Mem.empty.write 0 old.toBytes).write 32 newInterval.toBytes,
          G + setHeartbeatIntervalEventTailGasWarmUpdate⟩)
      setHeartbeatIntervalEventTail post
    exact htail

set_option maxRecDepth 8192 in
private theorem setHeartbeatIntervalUpdateTail_runCompiled_zero
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (newInterval : B256) (G : Nat)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hnewNonzero : newInterval ≠ 0) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalUpdateTailGasWarmSet⟩)
        setHeartbeatIntervalUpdateTail post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          (0 : B256).toBytes ++ newInterval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  rcases setHeartbeatIntervalEventTail_runCompiled_zero fs sevm base
      newInterval G harg hold horig hwarm hstatic hnewNonzero with
    ⟨post, htail, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, hlogs, hexpiries⟩
  unfold setHeartbeatIntervalUpdateTail arg mstoreAt
  func_run (8) [3, 3]
  all_goals try {
    simp only [Devm.gasLeft_setMach,
      setHeartbeatIntervalUpdateTailGasWarmSet]
    norm_num [gasWarmAccess, gVerylow] <;> omega }
  case h_ext =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word
  case h_ext =>
    rw [show ((1 : B256) * 32).toNat = 32 by decide]
    exact Devm.extCost_of_size Mem.size_write_word (by decide)
  case a =>
    simp only [Devm.getStorVal_setMach, hold, harg]
    change Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], (Mem.empty.write 0 (0 : B256).toBytes).write 32
            newInterval.toBytes,
          G + setHeartbeatIntervalEventTailGasWarmSet⟩)
      setHeartbeatIntervalEventTail post
    exact htail

set_option maxRecDepth 8192 in
private theorem setHeartbeatIntervalUpdateTail_runCompiled_noop
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (interval : B256) (G : Nat)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = interval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalUpdateTailGasWarmUpdate⟩)
        setHeartbeatIntervalUpdateTail post ∧
      post.gasLeft = G + 2800 ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = interval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          interval.toBytes ++ interval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  rcases setHeartbeatIntervalEventTail_runCompiled_noop fs sevm base
      interval G harg hold horig hwarm hstatic with
    ⟨post, htail, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, hlogs, hexpiries⟩
  unfold setHeartbeatIntervalUpdateTail arg mstoreAt
  func_run (8) [3, 3]
  all_goals try {
    simp only [Devm.gasLeft_setMach,
      setHeartbeatIntervalUpdateTailGasWarmUpdate]
    norm_num [gasWarmAccess, gVerylow] <;> omega }
  case h_ext =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word
  case h_ext =>
    rw [show ((1 : B256) * 32).toNat = 32 by decide]
    exact Devm.extCost_of_size Mem.size_write_word (by decide)
  case a =>
    simp only [Devm.getStorVal_setMach, hold, harg]
    change Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], (Mem.empty.write 0 interval.toBytes).write 32 interval.toBytes,
          G + setHeartbeatIntervalEventTailGasWarmUpdate⟩)
      setHeartbeatIntervalEventTail post
    exact htail

set_option maxRecDepth 8192 in
/-- Exact successful setter body.  Both configured bounds are inclusive, the
caller word must equal the immutable admin exactly, the old/new event is
emitted before the named interval store, and every canonical expiry slot is
preserved. -/
theorem setHeartbeatInterval_body_runCompiled_of_inclusive
    (fs : List Func) (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (old newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hmin : dp.minHeartbeatInterval ≤ newInterval)
    (hmax : newInterval ≤ dp.maxHeartbeatInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = old)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = old)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (holdNonzero : old ≠ 0)
    (hchanged : old ≠ newInterval) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalBodyGasWarmUpdate⟩)
        (setHeartbeatInterval dp) post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          old.toBytes ++ newInterval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  rcases setHeartbeatIntervalUpdateTail_runCompiled fs sevm base
      old newInterval G harg hold horig hwarm hstatic holdNonzero hchanged with
    ⟨post, htail, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, hlogs, hexpiries⟩
  unfold setHeartbeatInterval requireStaticArgs onlyAdmin arg cdl
  unfold pushDeployWord
  func_run (18) [0, 1, 0, 0]
  all_goals try {
    simp only [Devm.gasLeft_setMach,
      setHeartbeatIntervalBodyGasWarmUpdate]
    norm_num [gBase, gVerylow, gHigh, gJumpdest] <;> omega }
  all_goals try {
    simp only [hadmin]
    simp [B256.eqCheck] }
  all_goals try {
    rw [harg]
    simp [B256.ltCheck, B256.not_lt.mpr hmin] }
  all_goals try {
    rw [harg]
    simp [B256.gtCheck, B256.not_lt.mpr hmax] }
  case h_arm =>
    change Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty,
        G + setHeartbeatIntervalUpdateTailGasWarmUpdate⟩)
      setHeartbeatIntervalUpdateTail post
    exact htail

set_option maxRecDepth 8192 in
/-- Inclusive-bound successful zero-to-nonzero companion, with the exact warm
storage-set price and the same event-before-store chronology. -/
theorem setHeartbeatInterval_body_runCompiled_zero_of_inclusive
    (fs : List Func) (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hmin : dp.minHeartbeatInterval ≤ newInterval)
    (hmax : newInterval ≤ dp.maxHeartbeatInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hnewNonzero : newInterval ≠ 0) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalBodyGasWarmSet⟩)
        (setHeartbeatInterval dp) post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          (0 : B256).toBytes ++ newInterval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  rcases setHeartbeatIntervalUpdateTail_runCompiled_zero fs sevm base
      newInterval G harg hold horig hwarm hstatic hnewNonzero with
    ⟨post, htail, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, hlogs, hexpiries⟩
  unfold setHeartbeatInterval requireStaticArgs onlyAdmin arg cdl
  unfold pushDeployWord
  func_run (18) [0, 1, 0, 0]
  all_goals try {
    simp only [Devm.gasLeft_setMach,
      setHeartbeatIntervalBodyGasWarmSet]
    norm_num [gBase, gVerylow, gHigh, gJumpdest] <;> omega }
  all_goals try {
    simp only [hadmin]
    simp [B256.eqCheck] }
  all_goals try {
    rw [harg]
    simp [B256.ltCheck, B256.not_lt.mpr hmin] }
  all_goals try {
    rw [harg]
    simp [B256.gtCheck, B256.not_lt.mpr hmax] }
  case h_arm =>
    change Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty,
        G + setHeartbeatIntervalUpdateTailGasWarmSet⟩)
      setHeartbeatIntervalUpdateTail post
    exact htail

set_option maxRecDepth 8192 in
/-- Inclusive-bound successful no-op companion: setting the interval to its
current word still emits the exact old/new event and executes the named store,
with the EIP-2200 no-op price reflected in the remaining gas. -/
theorem setHeartbeatInterval_body_runCompiled_noop_of_inclusive
    (fs : List Func) (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (interval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = interval)
    (hmin : dp.minHeartbeatInterval ≤ interval)
    (hmax : interval ≤ dp.maxHeartbeatInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalBodyGasWarmUpdate⟩)
        (setHeartbeatInterval dp) post ∧
      post.gasLeft = G + 2800 ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = interval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          interval.toBytes ++ interval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser) := by
  rcases setHeartbeatIntervalUpdateTail_runCompiled_noop fs sevm base
      interval G harg hold horig hwarm hstatic with
    ⟨post, htail, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, hlogs, hexpiries⟩
  unfold setHeartbeatInterval requireStaticArgs onlyAdmin arg cdl
  unfold pushDeployWord
  func_run (18) [0, 1, 0, 0]
  all_goals try {
    simp only [Devm.gasLeft_setMach,
      setHeartbeatIntervalBodyGasWarmUpdate]
    norm_num [gBase, gVerylow, gHigh, gJumpdest] <;> omega }
  all_goals try {
    simp only [hadmin]
    simp [B256.eqCheck] }
  all_goals try {
    rw [harg]
    simp [B256.ltCheck, B256.not_lt.mpr hmin] }
  all_goals try {
    rw [harg]
    simp [B256.gtCheck, B256.not_lt.mpr hmax] }
  case h_arm =>
    change Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty,
        G + setHeartbeatIntervalUpdateTailGasWarmUpdate⟩)
      setHeartbeatIntervalUpdateTail post
    exact htail

set_option maxRecDepth 16384 in
/-- Exact public-dispatch success for `setHeartbeatInterval(uint256)` in the
warm nonzero-to-different-nonzero update case.  The result pins invocation
identity to the generated runtime/compiler image as well as the exact temporal
effects established by the body theorem. -/
theorem setHeartbeatInterval_runCompiled_of_inclusive
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (old newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "setHeartbeatInterval" [.uint256])
    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hmin : dp.minHeartbeatInterval ≤ newInterval)
    (hmax : newInterval ≤ dp.maxHeartbeatInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = old)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = old)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (holdNonzero : old ≠ 0)
    (hchanged : old ≠ newInterval) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalDispatchGas +
            setHeartbeatIntervalBodyGasWarmUpdate⟩)
        (runtime dp) post ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          old.toBytes ++ newInterval.toBytes⟩] ∧
      (∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdata]
    decide
  rcases setHeartbeatInterval_body_runCompiled_of_inclusive
      (runtimeMain dp :: aux) dp sevm base old newInterval G
      hbodyData hadmin harg hmin hmax hold horig hwarm hstatic
      holdNonzero hchanged with
    ⟨post, hbody, hgas, hstore, hlogs, hexpiries⟩
  refine ⟨post, ?_, hgas, hstore, hlogs, hexpiries, ?_⟩
  · refine Prog.runCompiled_intro
      (mid := base.setMach ⟨[], Mem.empty,
        G + 168 + setHeartbeatIntervalBodyGasWarmUpdate⟩)
      (G := G + 168 + setHeartbeatIntervalBodyGasWarmUpdate) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach,
        setHeartbeatIntervalDispatchGas, gJumpdest]
      omega
    · rfl
    · have hvalueZero : B256.eqCheck sevm.value 0 = 1 := by
        simp [B256.eqCheck, hvalue]
      have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "setHeartbeatInterval" [.uint256] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (33) [0, 0,
        selector "setHeartbeatInterval" [.uint256],
        1, 0, 0, 0, 0, 1]
      have hboundary :
          G + 168 + setHeartbeatIntervalBodyGasWarmUpdate - 168 =
            G + setHeartbeatIntervalBodyGasWarmUpdate := by omega
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
        runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
        List.take, List.drop, List.head?, Option.map, Option.getD,
        linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

/-! The three source error arms are proved at the direct endpoint boundary
before settlement.  Each exposes the pinned selector payload, preserves all
persistent storage, and emits no raw event. -/

theorem setHeartbeatInterval_body_runCompiledTo_error_of_not_admin
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (_newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hnotAdmin : sevm.caller.toB256 ≠ dp.admin) :
    ∃ post,
      Func.RunCompiledTo (runtimeMain dp :: aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 71⟩)
        (setHeartbeatInterval dp) (.error (.revert, post)) ∧
      post.output = customErrorData "SenderNotAdmin" ∧
      post.logs = base.logs ∧
      ∀ a k, post.getStorVal a k = base.getStorVal a k := by
  let data := customErrorData "SenderNotAdmin"
  let post := (base.setMach
    ⟨[], Mem.empty.write 0 data.toB256.toBytes, G⟩).withOutput data
  refine ⟨post, ?_, rfl, rfl, ?_⟩
  · unfold setHeartbeatInterval requireStaticArgs onlyAdmin pushDeployWord
    func_run (9) [0, 0]
    all_goals try { simp [B256.eqCheck, Ne.symm hnotAdmin] }
    case h_body =>
      apply Func.runCompiledTo_revSelector (G := G)
      · simp [customErrorData, B256.length_toBytes]
      · exact Mem.wf_empty
      · exact Mem.reads_empty
      · rfl
      · simp only [Devm.gasLeft_setMach, revSelectorCost]
        rw [Devm.extCost_empty_word]
        norm_num [gVerylow, gBase, gMemory]
        omega
      · simp only [Devm.stack_setMach, List.length_nil]
        omega
  · intro a k
    rfl

theorem setHeartbeatInterval_body_runCompiledTo_error_of_below_min
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hbelow : newInterval < dp.minHeartbeatInterval) :
    ∃ post,
      Func.RunCompiledTo (runtimeMain dp :: aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 98⟩)
        (setHeartbeatInterval dp) (.error (.revert, post)) ∧
      post.output = customErrorData "HeartbeatIntervalBelowMin" ∧
      post.logs = base.logs ∧
      ∀ a k, post.getStorVal a k = base.getStorVal a k := by
  let data := customErrorData "HeartbeatIntervalBelowMin"
  let post := (base.setMach
    ⟨[], Mem.empty.write 0 data.toB256.toBytes, G⟩).withOutput data
  refine ⟨post, ?_, rfl, rfl, ?_⟩
  · unfold setHeartbeatInterval requireStaticArgs onlyAdmin arg cdl
      pushDeployWord
    func_run (14) [0, 1, 1]
    all_goals try { simp [hadmin, B256.eqCheck] }
    all_goals try { rw [harg]; simp [B256.ltCheck, hbelow] }
    case h_body =>
      apply Func.runCompiledTo_revSelector (G := G)
      · simp [customErrorData, B256.length_toBytes]
      · exact Mem.wf_empty
      · exact Mem.reads_empty
      · rfl
      · simp only [Devm.gasLeft_setMach, revSelectorCost]
        rw [Devm.extCost_empty_word]
        norm_num [gVerylow, gBase, gMemory]
        omega
      · simp only [Devm.stack_setMach, List.length_nil]
        omega
  · intro a k
    rfl

theorem setHeartbeatInterval_body_runCompiledTo_error_of_above_max
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hmin : dp.minHeartbeatInterval ≤ newInterval)
    (habove : dp.maxHeartbeatInterval < newInterval) :
    ∃ post,
      Func.RunCompiledTo (runtimeMain dp :: aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 123⟩)
        (setHeartbeatInterval dp) (.error (.revert, post)) ∧
      post.output = customErrorData "HeartbeatIntervalAboveMax" ∧
      post.logs = base.logs ∧
      ∀ a k, post.getStorVal a k = base.getStorVal a k := by
  let data := customErrorData "HeartbeatIntervalAboveMax"
  let post := (base.setMach
    ⟨[], Mem.empty.write 0 data.toB256.toBytes, G⟩).withOutput data
  refine ⟨post, ?_, rfl, rfl, ?_⟩
  · unfold setHeartbeatInterval requireStaticArgs onlyAdmin arg cdl
      pushDeployWord
    func_run (19) [0, 1, 0, 1]
    all_goals try { simp [hadmin, B256.eqCheck] }
    all_goals try {
      rw [harg]
      simp [B256.ltCheck, B256.not_lt.mpr hmin] }
    all_goals try { rw [harg]; simp [B256.gtCheck, habove] }
    case h_body =>
      apply Func.runCompiledTo_revSelector (G := G)
      · simp [customErrorData, B256.length_toBytes]
      · exact Mem.wf_empty
      · exact Mem.reads_empty
      · rfl
      · simp only [Devm.gasLeft_setMach, revSelectorCost]
        rw [Devm.extCost_empty_word]
        norm_num [gVerylow, gBase, gMemory]
        omega
      · simp only [Devm.stack_setMach, List.length_nil]
        omega
  · intro a k
    rfl

set_option maxRecDepth 16384 in
/-- Exact dispatcher bridge for any terminal outcome of the selected
heartbeat-interval setter body. -/
theorem setHeartbeatInterval_dispatch_runCompiledTo
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (bodyGas G : Nat) (out : Execution)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "setHeartbeatInterval" [.uint256])
    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hbody : Func.RunCompiledTo (runtimeMain dp :: aux) sevm
      (base.setMach ⟨[], Mem.empty, G + bodyGas⟩)
      (setHeartbeatInterval dp) out) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty,
        G + setHeartbeatIntervalDispatchGas + bodyGas⟩)
      (runtime dp) out ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  refine ⟨?_, ?_⟩
  · refine Prog.runCompiledTo_intro
      (mid := base.setMach ⟨[], Mem.empty, G + 168 + bodyGas⟩)
      (G := G + 168 + bodyGas) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach,
        setHeartbeatIntervalDispatchGas, gJumpdest]
      omega
    · rfl
    · have hvalueZero : B256.eqCheck sevm.value 0 = 1 := by
        simp [B256.eqCheck, hvalue]
      have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "setHeartbeatInterval" [.uint256] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (33) [0, 0,
        selector "setHeartbeatInterval" [.uint256],
        1, 0, 0, 0, 0, 1]
      have hboundary : G + 168 + bodyGas - 168 = G + bodyGas := by
        omega
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
        runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
        List.take, List.drop, List.head?, Option.map, Option.getD,
        linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

/-- Exact public-dispatch companion for an inclusive warm zero-to-nonzero
update. -/
theorem setHeartbeatInterval_runCompiledTo_zero_of_inclusive
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "setHeartbeatInterval" [.uint256])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hmin : dp.minHeartbeatInterval ≤ newInterval)
    (hmax : newInterval ≤ dp.maxHeartbeatInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hnewNonzero : newInterval ≠ 0) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalDispatchGas +
            setHeartbeatIntervalBodyGasWarmSet⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = newInterval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          (0 : B256).toBytes ++ newInterval.toBytes⟩] ∧
      (∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdata]
    decide
  rcases setHeartbeatInterval_body_runCompiled_zero_of_inclusive
      (runtimeMain dp :: aux) dp sevm base newInterval G
      hbodyData hadmin harg hmin hmax hold horig hwarm hstatic hnewNonzero with
    ⟨post, hbody, hgas, hstore, hlogs, hexpiries⟩
  have hbodyTo : Func.RunCompiledTo (runtimeMain dp :: aux) sevm
      (base.setMach ⟨[], Mem.empty,
        G + setHeartbeatIntervalBodyGasWarmSet⟩)
      (setHeartbeatInterval dp) (.ok post) :=
    Func.RunCompiledTo.of_runCompiled hbody
  rcases setHeartbeatInterval_dispatch_runCompiledTo dp sevm base
      setHeartbeatIntervalBodyGasWarmSet G (.ok post)
      hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨post, hrun, hgas, hstore, hlogs, hexpiries, hcompile⟩

/-- Exact public-dispatch companion for an inclusive same-value update.  The
setter still emits its old/new event and reaches the named store; only the
EIP-2200 no-op gas charge differs from the changed-value success path. -/
theorem setHeartbeatInterval_runCompiledTo_noop_of_inclusive
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (interval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "setHeartbeatInterval" [.uint256])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = interval)
    (hmin : dp.minHeartbeatInterval ≤ interval)
    (hmax : interval ≤ dp.maxHeartbeatInterval)
    (hold : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (horig : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalDispatchGas +
            setHeartbeatIntervalBodyGasWarmUpdate⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G + 2800 ∧
      Devm.getStorVal post sevm.currentTarget
        heartbeatIntervalSlot = interval ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          interval.toBytes ++ interval.toBytes⟩] ∧
      (∀ pauser, canonicalAddress pauser →
        Devm.getStorVal post sevm.currentTarget (expirySlot pauser) =
          Devm.getStorVal base sevm.currentTarget (expirySlot pauser)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdata]
    decide
  rcases setHeartbeatInterval_body_runCompiled_noop_of_inclusive
      (runtimeMain dp :: aux) dp sevm base interval G
      hbodyData hadmin harg hmin hmax hold horig hwarm hstatic with
    ⟨post, hbody, hgas, hstore, hlogs, hexpiries⟩
  have hbodyTo : Func.RunCompiledTo (runtimeMain dp :: aux) sevm
      (base.setMach ⟨[], Mem.empty,
        G + setHeartbeatIntervalBodyGasWarmUpdate⟩)
      (setHeartbeatInterval dp) (.ok post) :=
    Func.RunCompiledTo.of_runCompiled hbody
  rcases setHeartbeatInterval_dispatch_runCompiledTo dp sevm base
      setHeartbeatIntervalBodyGasWarmUpdate G (.ok post)
      hdata hvalue hselector hcodeAddress hcode hbodyTo with
    ⟨hrun, hcompile⟩
  exact ⟨post, hrun, hgas, hstore, hlogs, hexpiries, hcompile⟩

theorem setHeartbeatInterval_runCompiledTo_error_of_not_admin
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "setHeartbeatInterval" [.uint256])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hnotAdmin : sevm.caller.toB256 ≠ dp.admin) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalDispatchGas + 71⟩)
        (runtime dp) (.error (.revert, post)) ∧
      post.output = customErrorData "SenderNotAdmin" ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdata]
    decide
  rcases setHeartbeatInterval_body_runCompiledTo_error_of_not_admin
      dp sevm base newInterval G hbodyData hnotAdmin with
    ⟨post, hbody, houtput, hlogs, hstorage⟩
  rcases setHeartbeatInterval_dispatch_runCompiledTo dp sevm base
      71 G (.error (.revert, post)) hdata hvalue hselector hcodeAddress
      hcode hbody with ⟨hrun, hcompile⟩
  exact ⟨post, hrun, houtput, hlogs, hstorage, hcompile⟩

theorem setHeartbeatInterval_runCompiledTo_error_of_below_min
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "setHeartbeatInterval" [.uint256])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hbelow : newInterval < dp.minHeartbeatInterval) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalDispatchGas + 98⟩)
        (runtime dp) (.error (.revert, post)) ∧
      post.output = customErrorData "HeartbeatIntervalBelowMin" ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdata]
    decide
  rcases setHeartbeatInterval_body_runCompiledTo_error_of_below_min
      dp sevm base newInterval G hbodyData hadmin harg hbelow with
    ⟨post, hbody, houtput, hlogs, hstorage⟩
  rcases setHeartbeatInterval_dispatch_runCompiledTo dp sevm base
      98 G (.error (.revert, post)) hdata hvalue hselector hcodeAddress
      hcode hbody with ⟨hrun, hcompile⟩
  exact ⟨post, hrun, houtput, hlogs, hstorage, hcompile⟩

theorem setHeartbeatInterval_runCompiledTo_error_of_above_max
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (newInterval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "setHeartbeatInterval" [.uint256])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = newInterval)
    (hmin : dp.minHeartbeatInterval ≤ newInterval)
    (habove : dp.maxHeartbeatInterval < newInterval) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + setHeartbeatIntervalDispatchGas + 123⟩)
        (runtime dp) (.error (.revert, post)) ∧
      post.output = customErrorData "HeartbeatIntervalAboveMax" ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hbodyData : sevm.data.length.toB256 <? 36 = 0 := by
    rw [hdata]
    decide
  rcases setHeartbeatInterval_body_runCompiledTo_error_of_above_max
      dp sevm base newInterval G hbodyData hadmin harg hmin habove with
    ⟨post, hbody, houtput, hlogs, hstorage⟩
  rcases setHeartbeatInterval_dispatch_runCompiledTo dp sevm base
      123 G (.error (.revert, post)) hdata hvalue hselector hcodeAddress
      hcode hbody with ⟨hrun, hcompile⟩
  exact ⟨post, hrun, houtput, hlogs, hstorage, hcompile⟩

/-- Canonical calldata for `setHeartbeatInterval(uint256)`. -/
def setHeartbeatIntervalCalldata (newInterval : B256) : Bytes :=
  abiSelectorBytes (selector "setHeartbeatInterval" [.uint256]) ++
    newInterval.toBytes

/-- Clean settlement of an exact direct setter message retains the raw
successful poststate.  Combined with the exact public-dispatch theorem, this
transports the interval write, event, and expiry-slot noninterference to the
message boundary without adding another effect. -/
theorem setHeartbeatInterval_success_settles_cleanly
    (dp : DeployParams) {msg : Msg} {ca : Adr}
    {final settled : Devm} {loc : Nat}
    {newInterval : B256}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = setHeartbeatIntervalCalldata newInterval)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨loc, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hclean : final.error.isNone = true) :
    settled = final := by
  have hsettle := (RunFrame.some_inv hprocess).2
  simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
    executeCode.handleError, processMessage.settle] at hsettle
  have hnotError : final.error.isSome ≠ true := by
    cases herror : final.error <;> simp_all
  rw [if_neg hnotError] at hsettle
  exact Except.ok.inj hsettle

/-- Exact clean direct-message effects, inherited unchanged from the raw
successful setter result. -/
theorem setHeartbeatInterval_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr}
    {final settled : Devm} {loc : Nat}
    {old newInterval : B256}
    (htarget : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = setHeartbeatIntervalCalldata newInterval)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨loc, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hclean : final.error.isNone = true)
    (hstore : final.getStorVal ca heartbeatIntervalSlot = newInterval)
    (hlogs : final.logs = (initDevm msg).logs ++
      [⟨ca, [heartbeatIntervalUpdatedEvent],
        old.toBytes ++ newInterval.toBytes⟩])
    (hexpiries : ∀ pauser, canonicalAddress pauser →
      final.getStorVal ca (expirySlot pauser) =
        (initDevm msg).getStorVal ca (expirySlot pauser)) :
    settled.getStorVal ca heartbeatIntervalSlot = newInterval ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [heartbeatIntervalUpdatedEvent],
          old.toBytes ++ newInterval.toBytes⟩] ∧
      ∀ pauser, canonicalAddress pauser →
        settled.getStorVal ca (expirySlot pauser) =
          (initDevm msg).getStorVal ca (expirySlot pauser) := by
  have hsettled := setHeartbeatInterval_success_settles_cleanly dp
    htarget howner hcodeAddress hcode hvalue hdata hprocess hclean
  subst settled
  exact ⟨hstore, hlogs, hexpiries⟩

/-- Any settled error of an exact direct heartbeat-interval message restores
the complete owner storage and transient storage from message entry.  The
error kind is established by the separate exact compiled error paths; message
settlement intentionally erases that distinction. -/
theorem setHeartbeatInterval_settled_error_restores_owner
    (dp : DeployParams) {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr} {newInterval : B256}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = setHeartbeatIntervalCalldata newInterval)
    (hprocess : ProcessMessage msg slot (.ok post))
    (herror : post.error.isSome) :
    Devm.getStor post ca = msg.benv.state.getStor ca ∧
      post.transientStorage = msg.tenv.transientStorage := by
  have hrollback := ProcessMessage.rollback_of_error hprocess herror
  exact ⟨congrArg (fun state : State => state.getStor ca) hrollback.1,
    hrollback.2⟩

/-- At the exact top-level call boundary, an errored direct
`setHeartbeatInterval` message exposes no receipt log.  This deliberately does
not claim that raw `Devm.logs` are erased by `ProcessMessage`. -/
theorem setHeartbeatInterval_settled_error_logs_eq_nil
    (dp : DeployParams) {msg : Msg} {state : State} {out : MsgCallOutput}
    {ca : Adr} {newInterval : B256}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = setHeartbeatIntervalCalldata newInterval)
    (hrun : processMessageCall msg = .ok (state, out))
    (herror : out.error.isSome) :
    out.logs = [] :=
  processMessageCall_error_logs_eq_nil hrun herror

end Blanc.LidoCircuitBreaker
