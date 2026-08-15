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

end Blanc.LidoCircuitBreaker
