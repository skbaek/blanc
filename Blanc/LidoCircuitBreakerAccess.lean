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

/-- The strict-live heartbeat boundary rules out the zero-current branch of
EIP-2200.  The expiry slot has already been read before its SSTORE, so the
remaining value-cost cases are precisely a clean nonzero update or the
100-gas no-op/dirty family. -/
theorem heartbeat_sstoreValueCost_partition
    (timestamp original current new : B256)
    (hlive : timestamp < current) :
    sstoreValueCost original current new =
        gasStorageUpdate - gasColdSload ∨
      sstoreValueCost original current new = gasWarmAccess := by
  have hcurrentNonzero : current ≠ 0 := by
    intro hzero
    subst current
    rw [B256.lt_iff_toNat_lt_toNat] at hlive
    rw [B256.toNat_zero] at hlive
    omega
  unfold sstoreValueCost
  split_ifs with hchanged horiginalZero
  · exfalso
    apply hcurrentNonzero
    rw [← hchanged.1, horiginalZero]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Every setter SSTORE value state lies in one of the three EIP-2200 charge
classes.  In particular this names the zero, clean-update, and no-op/dirty
cases without assuming a stable original-storage snapshot. -/
theorem setHeartbeatInterval_sstoreValueCost_partition
    (original current new : B256) :
    sstoreValueCost original current new = gasStorageSet ∨
      sstoreValueCost original current new =
        gasStorageUpdate - gasColdSload ∨
      sstoreValueCost original current new = gasWarmAccess := by
  unfold sstoreValueCost
  split_ifs <;> simp

def heartbeatStoreLogTailGasWarmUpdate : Nat := 4310
def heartbeatStoreLogTailGasWarmOther : Nat := 4310

/-- The state component produced by one SLOAD's access-list update. -/
def heartbeatSloadBase (sevm : Sevm) (base : Devm) (key : B256) : Devm :=
  if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys then
    base
  else
    addAccessedStorageKey base sevm.currentTarget key

/-- The actual warm/cold charge of one SLOAD at its current sequential base. -/
def heartbeatSloadCost (sevm : Sevm) (base : Devm) (key : B256) : Nat :=
  if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys then
    gasWarmAccess
  else
    gasColdSload

@[simp] theorem heartbeatSloadBase_getStorVal
    (sevm : Sevm) (base : Devm) (key : B256) (a : Adr) (k : B256) :
    (heartbeatSloadBase sevm base key).getStorVal a k =
      base.getStorVal a k := by
  unfold heartbeatSloadBase
  split_ifs <;> rfl

@[simp] theorem heartbeatSloadBase_logs
    (sevm : Sevm) (base : Devm) (key : B256) :
    (heartbeatSloadBase sevm base key).logs = base.logs := by
  unfold heartbeatSloadBase
  split_ifs <;> rfl

private theorem heartbeatSloadBase_preserves
    (sevm : Sevm) (base : Devm) (key : B256) {pair : Adr × B256}
    (hpair : pair ∈ base.accessedStorageKeys) :
    pair ∈ (heartbeatSloadBase sevm base key).accessedStorageKeys := by
  unfold heartbeatSloadBase
  split_ifs
  · exact hpair
  · change pair ∈ base.accessedStorageKeys.insert
      ⟨sevm.currentTarget, key⟩
    exact Std.HashSet.mem_insert.mpr (Or.inr hpair)

private theorem heartbeatSloadBase_self
    (sevm : Sevm) (base : Devm) (key : B256) :
    (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      (heartbeatSloadBase sevm base key).accessedStorageKeys := by
  unfold heartbeatSloadBase
  split_ifs with hwarm
  · exact hwarm
  · change (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      base.accessedStorageKeys.insert ⟨sevm.currentTarget, key⟩
    exact Std.HashSet.mem_insert_self

def heartbeatAfterCountLoad (sevm : Sevm) (base : Devm) : Devm :=
  heartbeatSloadBase sevm base (countSlot sevm.caller.toB256)

private lemma heartbeat_addAccessedStorageKey_setMach_setMach
    {base : Devm} {m m' : Mach} {target : Adr} {key : B256} :
    (addAccessedStorageKey (base.setMach m) target key).setMach m' =
      (addAccessedStorageKey base target key).setMach m' := rfl

set_option maxRecDepth 4096 in
/-- Exact first heartbeat chunk: caller tagging and the count SLOAD map an
arbitrary warm/cold entry base to `heartbeatAfterCountLoad`, charging the
actual access-list cost and otherwise preserving the base world and logs. -/
private theorem heartbeat_countLoad_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (count : B256) (G : Nat)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) = count) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty,
        G + 8 + heartbeatSloadCost sevm base
          (countSlot sevm.caller.toB256)⟩)
      (Ninst.caller ::: tagTop countRegion +++ Ninst.sload ::: Func.stop)
      ((heartbeatAfterCountLoad sevm base).setMach
        ⟨[count], Mem.empty, G⟩) := by
  by_cases hwarm : (⟨sevm.currentTarget,
      countSlot sevm.caller.toB256⟩ : Adr × B256) ∈
      base.accessedStorageKeys
  · unfold tagTop heartbeatAfterCountLoad heartbeatSloadBase
      heartbeatSloadCost
    simp only [hwarm, if_pos]
    func_run [countSlot sevm.caller.toB256]
    case a =>
      apply Func.RunCompiled.last
      simp [Linst.Run, Linst.run, Devm.getStorVal_setMach, hcount,
        gasWarmAccess]
  · unfold tagTop heartbeatAfterCountLoad heartbeatSloadBase
      heartbeatSloadCost
    simp [hwarm]
    func_run [countSlot sevm.caller.toB256]
    case a =>
      apply Func.RunCompiled.last
      simp [Linst.Run, Linst.run, Devm.getStorVal_setMach, hcount,
        gasColdSload, heartbeat_addAccessedStorageKey_setMach_setMach]

set_option maxRecDepth 4096 in
/-- Continue from the exact count-load chunk without changing its source
association or replaying its warm/cold execution proof. -/
private theorem heartbeat_countLoad_runCompiled_then
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (count : B256) (G : Nat)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) = count)
    (tail : Func) (post : Devm)
    (htail : Func.RunCompiled fs sevm
      ((heartbeatAfterCountLoad sevm base).setMach
        ⟨[count], Mem.empty, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty,
        G + 8 + heartbeatSloadCost sevm base
          (countSlot sevm.caller.toB256)⟩)
      (Ninst.caller ::: tagTop countRegion +++ Ninst.sload ::: tail)
      post := by
  have hload := heartbeat_countLoad_runCompiled fs sevm base count G hcount
  cases hload with
  | next hcaller hload =>
    cases hload with
    | next hpush hload =>
      cases hload with
      | next hor hload =>
        cases hload with
        | next hsload hstop =>
          cases hstop with
          | last hlast =>
            simp [Linst.Run, Linst.run] at hlast
            subst_vars
            exact .next hcaller (.next hpush (.next hor (.next hsload htail)))

set_option maxRecDepth 4096 in
/-- A nonzero loaded count takes the successful side of heartbeat's first
guard, consumes the count word, and leaves the sequential SLOAD base ready for
the expiry load. -/
private theorem heartbeat_registeredGuard_runCompiled_then
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (count : B256) (G : Nat)
    (hcountNonzero : count ≠ 0)
    (tail : Func) (post : Devm)
    (htail : Func.RunCompiled fs sevm
      ((heartbeatAfterCountLoad sevm base).setMach
        ⟨[], Mem.empty, G⟩) tail post) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterCountLoad sevm base).setMach
        ⟨[count], Mem.empty, G + 16⟩)
      (Ninst.iszero :::
        ((.call senderNotPauserErrorSlot) <?> tail))
      post := by
  func_run (1) [0]
  case h_val => simp [B256.eqCheck, hcountNonzero]
  case a =>
    func_run (1)
    exact htail

private theorem heartbeat_registeredGuard_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (count : B256) (G : Nat)
    (hcountNonzero : count ≠ 0) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterCountLoad sevm base).setMach
        ⟨[count], Mem.empty, G + 16⟩)
      (Ninst.iszero :::
        ((.call senderNotPauserErrorSlot) <?> Func.stop))
      ((heartbeatAfterCountLoad sevm base).setMach
        ⟨[], Mem.empty, G⟩) := by
  apply heartbeat_registeredGuard_runCompiled_then fs sevm base count G
    hcountNonzero
  apply Func.RunCompiled.last
  simp [Linst.Run, Linst.run]

def heartbeatAfterExpiryLoad (sevm : Sevm) (base : Devm) : Devm :=
  heartbeatSloadBase sevm (heartbeatAfterCountLoad sevm base)
    (expirySlot sevm.caller.toB256)

set_option maxRecDepth 4096 in
/-- Exact second heartbeat chunk: the expiry SLOAD advances the sequential
access-list state from `heartbeatAfterCountLoad` to `heartbeatAfterExpiryLoad`
and charges its actual warm/cold cost. -/
private theorem heartbeat_expiryLoad_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (oldExpiry : B256) (G : Nat)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterCountLoad sevm base).setMach ⟨[], Mem.empty,
        G + 8 + heartbeatSloadCost sevm
          (heartbeatAfterCountLoad sevm base)
          (expirySlot sevm.caller.toB256)⟩)
      (Ninst.caller ::: tagTop expiryRegion +++ Ninst.sload ::: Func.stop)
      ((heartbeatAfterExpiryLoad sevm base).setMach
        ⟨[oldExpiry], Mem.empty, G⟩) := by
  by_cases hwarm : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈
      (heartbeatAfterCountLoad sevm base).accessedStorageKeys
  · unfold tagTop heartbeatAfterExpiryLoad heartbeatSloadBase
      heartbeatSloadCost
    simp only [hwarm, if_pos]
    func_run [expirySlot sevm.caller.toB256]
    case a =>
      apply Func.RunCompiled.last
      simp [Linst.Run, Linst.run, Devm.getStorVal_setMach,
        heartbeatAfterCountLoad, holdExpiry, gasWarmAccess]
  · unfold tagTop heartbeatAfterExpiryLoad heartbeatSloadBase
      heartbeatSloadCost
    simp [hwarm]
    func_run [expirySlot sevm.caller.toB256]
    case a =>
      apply Func.RunCompiled.last
      simp [Linst.Run, Linst.run, Devm.getStorVal_setMach,
        heartbeatAfterCountLoad, holdExpiry, gasColdSload,
        heartbeat_addAccessedStorageKey_setMach_setMach]

set_option maxRecDepth 4096 in
/-- Continue from the exact expiry-load chunk without changing its source
association or replaying its warm/cold execution proof. -/
private theorem heartbeat_expiryLoad_runCompiled_then
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (oldExpiry : B256) (G : Nat)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (tail : Func) (post : Devm)
    (htail : Func.RunCompiled fs sevm
      ((heartbeatAfterExpiryLoad sevm base).setMach
        ⟨[oldExpiry], Mem.empty, G⟩) tail post) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterCountLoad sevm base).setMach ⟨[], Mem.empty,
        G + 8 + heartbeatSloadCost sevm
          (heartbeatAfterCountLoad sevm base)
          (expirySlot sevm.caller.toB256)⟩)
      (Ninst.caller ::: tagTop expiryRegion +++ Ninst.sload ::: tail)
      post := by
  have hload := heartbeat_expiryLoad_runCompiled fs sevm base oldExpiry G
    holdExpiry
  cases hload with
  | next hcaller hload =>
    cases hload with
    | next hpush hload =>
      cases hload with
      | next hor hload =>
        cases hload with
        | next hsload hstop =>
          cases hstop with
          | last hlast =>
            simp [Linst.Run, Linst.run] at hlast
            subst_vars
            exact .next hcaller (.next hpush (.next hor (.next hsload htail)))

set_option maxRecDepth 4096 in
/-- Strict liveness takes heartbeat's successful expiry-guard arm.  The
strict premise deliberately excludes equality, which remains expired. -/
private theorem heartbeat_liveGuard_runCompiled_then
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (oldExpiry timestamp : B256) (G : Nat)
    (htime : sevm.benvStat.time = timestamp)
    (holdLive : timestamp < oldExpiry)
    (tail : Func) (post : Devm)
    (htail : Func.RunCompiled fs sevm
      ((heartbeatAfterExpiryLoad sevm base).setMach
        ⟨[], Mem.empty, G⟩) tail post) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterExpiryLoad sevm base).setMach
        ⟨[oldExpiry], Mem.empty, G + 19⟩)
      (Ninst.timestamp ::: Ninst.lt :::
        (tail <?> (.call heartbeatExpiredErrorSlot)))
      post := by
  func_run (2) [1]
  case h_val =>
    rw [htime]
    simp [B256.ltCheck, holdLive]
  case a =>
    func_run (1)
    exact htail

private theorem heartbeat_liveGuard_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (oldExpiry timestamp : B256) (G : Nat)
    (htime : sevm.benvStat.time = timestamp)
    (holdLive : timestamp < oldExpiry) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterExpiryLoad sevm base).setMach
        ⟨[oldExpiry], Mem.empty, G + 19⟩)
      (Ninst.timestamp ::: Ninst.lt :::
        (Func.stop <?> (.call heartbeatExpiredErrorSlot)))
      ((heartbeatAfterExpiryLoad sevm base).setMach
        ⟨[], Mem.empty, G⟩) := by
  apply heartbeat_liveGuard_runCompiled_then fs sevm base oldExpiry
    timestamp G htime holdLive
  apply Func.RunCompiled.last
  simp [Linst.Run, Linst.run]

def heartbeatAfterIntervalLoad (sevm : Sevm) (base : Devm) : Devm :=
  heartbeatSloadBase sevm (heartbeatAfterExpiryLoad sevm base)
    heartbeatIntervalSlot

set_option maxRecDepth 4096 in
/-- Exact third heartbeat chunk: pushing and loading the interval advances the
sequential access-list state to `heartbeatAfterIntervalLoad` while preserving
the previously loaded expiry below the interval word. -/
private theorem heartbeat_intervalLoad_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (oldExpiry interval : B256) (G : Nat)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterExpiryLoad sevm base).setMach ⟨[oldExpiry], Mem.empty,
        G + 3 + heartbeatSloadCost sevm
          (heartbeatAfterExpiryLoad sevm base)
          heartbeatIntervalSlot⟩)
      (Ninst.pushB256 heartbeatIntervalSlot ::: Ninst.sload ::: Func.stop)
      ((heartbeatAfterIntervalLoad sevm base).setMach
        ⟨[interval, oldExpiry], Mem.empty, G⟩) := by
  by_cases hwarm : (⟨sevm.currentTarget,
      heartbeatIntervalSlot⟩ : Adr × B256) ∈
      (heartbeatAfterExpiryLoad sevm base).accessedStorageKeys
  · unfold heartbeatAfterIntervalLoad heartbeatSloadBase heartbeatSloadCost
    simp only [hwarm, if_pos]
    func_run
    case a =>
      apply Func.RunCompiled.last
      simp [Linst.Run, Linst.run, Devm.getStorVal_setMach,
        heartbeatAfterExpiryLoad, heartbeatAfterCountLoad, hinterval,
        gasWarmAccess]
  · unfold heartbeatAfterIntervalLoad heartbeatSloadBase heartbeatSloadCost
    simp [hwarm]
    func_run
    case a =>
      apply Func.RunCompiled.last
      simp [Linst.Run, Linst.run, Devm.getStorVal_setMach,
        heartbeatAfterExpiryLoad, heartbeatAfterCountLoad, hinterval,
        gasColdSload, heartbeat_addAccessedStorageKey_setMach_setMach]

/-- Continue the already-proved exact interval push/SLOAD with an arbitrary
successful residual function. -/
private theorem heartbeat_intervalLoad_runCompiled_then
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (carried interval : B256) (G : Nat)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (tail : Func) (post : Devm)
    (htail : Func.RunCompiled fs sevm
      ((heartbeatAfterIntervalLoad sevm base).setMach
        ⟨[interval, carried], Mem.empty, G⟩)
      tail post) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterExpiryLoad sevm base).setMach ⟨[carried], Mem.empty,
        G + 3 + heartbeatSloadCost sevm
          (heartbeatAfterExpiryLoad sevm base)
          heartbeatIntervalSlot⟩)
      (Ninst.pushB256 heartbeatIntervalSlot ::: Ninst.sload ::: tail)
      post := by
  have hload := heartbeat_intervalLoad_runCompiled fs sevm base carried
    interval G hinterval
  cases hload with
  | next hpush hrest =>
    cases hrest with
    | next hsload hstop =>
      cases hstop with
      | last hlast =>
        simp [Linst.Run, Linst.run] at hlast
        subst_vars
        exact .next hpush (.next hsload htail)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Exact successful checked-heartbeat-expiry computation with the interval
SLOAD charged at its actual sequential warm/cold cost. -/
private theorem heartbeat_checkedExpiry_runCompiled_then
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (timestamp interval expiry : B256) (G : Nat)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (extension : CheckedHeartbeatExtension timestamp interval expiry)
    (continuation : Func) (post : Devm)
    (hcontinuation : Func.RunCompiled fs sevm
      ((heartbeatAfterIntervalLoad sevm base).setMach
        ⟨[expiry], Mem.empty, G⟩) continuation post) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterExpiryLoad sevm base).setMach ⟨[], Mem.empty,
        G + 32 + heartbeatSloadCost sevm
          (heartbeatAfterExpiryLoad sevm base)
          heartbeatIntervalSlot⟩)
      (checkedHeartbeatExpiry continuation)
      post := by
  have hsum := CheckedHeartbeatExtension.add_eq extension
  rcases extension with ⟨bound, hexpiry⟩
  have hle : timestamp ≤ expiry := by
    rw [B256.le_iff_toNat_le_toNat, hexpiry,
      B256.toNat_toB256_of_lt bound]
    omega
  let tail : Func :=
    Ninst.add ::: Ninst.dup 0 ::: Ninst.timestamp ::: Ninst.swap 0 :::
      Ninst.lt ::: ((.call arithmeticPanicSlot) <?> continuation)
  have htail : Func.RunCompiled fs sevm
      ((heartbeatAfterIntervalLoad sevm base).setMach
        ⟨[interval, timestamp], Mem.empty, G + 27⟩)
      tail
      post := by
    dsimp [tail]
    func_run (5) [expiry, 0]
    all_goals try {
      rw [B256.add_comm]
      exact hsum }
    all_goals try {
      rw [htime]
      simp only [B256.ltCheck, if_neg (not_lt_of_ge hle)] }
    case a =>
      func_run (1)
      exact hcontinuation
  have hload := heartbeat_intervalLoad_runCompiled_then fs sevm base
    timestamp interval (G + 27) hinterval tail _ htail
  unfold checkedHeartbeatExpiry
  func_run (1)
  rw [htime]
  have hgas :
      G + 32 + heartbeatSloadCost sevm
          (heartbeatAfterExpiryLoad sevm base) heartbeatIntervalSlot - 2 =
        (G + 27) + 3 + heartbeatSloadCost sevm
          (heartbeatAfterExpiryLoad sevm base) heartbeatIntervalSlot := by
    omega
  rw [hgas]
  simpa [tail] using hload

private theorem heartbeat_checkedExpiry_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (timestamp interval expiry : B256) (G : Nat)
    (htime : sevm.benvStat.time = timestamp)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (extension : CheckedHeartbeatExtension timestamp interval expiry) :
    Func.RunCompiled fs sevm
      ((heartbeatAfterExpiryLoad sevm base).setMach ⟨[], Mem.empty,
        G + 32 + heartbeatSloadCost sevm
          (heartbeatAfterExpiryLoad sevm base)
          heartbeatIntervalSlot⟩)
      (checkedHeartbeatExpiry Func.stop)
      ((heartbeatAfterIntervalLoad sevm base).setMach
        ⟨[expiry], Mem.empty, G⟩) := by
  apply heartbeat_checkedExpiry_runCompiled_then fs sevm base timestamp
    interval expiry G htime hinterval extension
  apply Func.RunCompiled.last
  simp [Linst.Run, Linst.run]

theorem heartbeatAfterIntervalLoad_expiry_warm
    (sevm : Sevm) (base : Devm) :
    (⟨sevm.currentTarget, expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈
      (heartbeatAfterIntervalLoad sevm base).accessedStorageKeys := by
  unfold heartbeatAfterIntervalLoad
  apply heartbeatSloadBase_preserves
  unfold heartbeatAfterExpiryLoad
  exact heartbeatSloadBase_self sevm _ _

/-- Worst-value-case sufficient gas with each SLOAD charged at its actual
sequential warm/cold state.  A no-op or dirty SSTORE returns the 2800-gas
difference to the poststate. -/
def heartbeatBodySuccessGas
    (sevm : Sevm) (base : Devm) : Nat :=
  4393 +
    heartbeatSloadCost sevm base (countSlot sevm.caller.toB256) +
    heartbeatSloadCost sevm (heartbeatAfterCountLoad sevm base)
      (expirySlot sevm.caller.toB256) +
    heartbeatSloadCost sevm (heartbeatAfterExpiryLoad sevm base)
      heartbeatIntervalSlot

set_option maxRecDepth 8192 in
private theorem heartbeat_storeLogTail_runCompiled_update
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (originalExpiry oldExpiry expiry : B256) (G : Nat)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (horigExpiry : getOrigStorVal sevm sevm.currentTarget
      (expirySlot sevm.caller.toB256) = originalExpiry)
    (hwarmExpiry : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hstoreCost : sstoreValueCost originalExpiry oldExpiry expiry =
      gasStorageUpdate - gasColdSload) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[expiry], Mem.empty,
          G + heartbeatStoreLogTailGasWarmUpdate⟩)
        (storeHeartbeatExpiryFromStack +++ Func.stop) post ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget
        (expirySlot sevm.caller.toB256) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, sevm.caller.toB256], expiry.toBytes⟩] := by
  unfold storeHeartbeatExpiryFromStack mstoreAt tagTop logWith
    heartbeatStoreLogTailGasWarmUpdate
  apply Exists.intro
  constructor
  · func_run [3, expirySlot sevm.caller.toB256, 2900, 1381]
    case h_ext =>
      change (base.setMach
        ⟨[0, expiry, expiry], Mem.empty, G + 4305⟩).extCost
          [⟨0, 32⟩] = 3
      simpa [gMemory] using
        (Devm.extCost_empty_word (devm := base)
          (S := [0, expiry, expiry]) (G := G + 4305))
    case h_cost =>
      rw [horigExpiry, Devm.getStorVal_setMach, holdExpiry]
      simpa [gasStorageUpdate, gasColdSload] using hstoreCost
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

set_option maxRecDepth 8192 in
private theorem heartbeat_storeLogTail_runCompiled_other
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (originalExpiry oldExpiry expiry : B256) (G : Nat)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (horigExpiry : getOrigStorVal sevm sevm.currentTarget
      (expirySlot sevm.caller.toB256) = originalExpiry)
    (hwarmExpiry : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hstoreCost : sstoreValueCost originalExpiry oldExpiry expiry =
      gasWarmAccess) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[expiry], Mem.empty,
          G + heartbeatStoreLogTailGasWarmOther⟩)
        (storeHeartbeatExpiryFromStack +++ Func.stop) post ∧
      post.gasLeft = G + 2800 ∧
      post.getStorVal sevm.currentTarget
        (expirySlot sevm.caller.toB256) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, sevm.caller.toB256], expiry.toBytes⟩] := by
  unfold storeHeartbeatExpiryFromStack mstoreAt tagTop logWith
    heartbeatStoreLogTailGasWarmOther
  apply Exists.intro
  constructor
  · func_run [3, expirySlot sevm.caller.toB256, 100, 1381]
    case h_ext =>
      change (base.setMach
        ⟨[0, expiry, expiry], Mem.empty, G + 4305⟩).extCost
          [⟨0, 32⟩] = 3
      simpa [gMemory] using
        (Devm.extCost_empty_word (devm := base)
          (S := [0, expiry, expiry]) (G := G + 4305))
    case h_cost =>
      rw [horigExpiry, Devm.getStorVal_setMach, holdExpiry]
      simpa [gasWarmAccess] using hstoreCost
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

set_option maxRecDepth 8192 in
private theorem heartbeat_storeLogTail_runCompiled_partition
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (timestamp originalExpiry oldExpiry expiry : B256) (G : Nat)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (horigExpiry : getOrigStorVal sevm sevm.currentTarget
      (expirySlot sevm.caller.toB256) = originalExpiry)
    (hwarmExpiry : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (holdLive : timestamp < oldExpiry) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[expiry], Mem.empty, G + 4310⟩)
        (storeHeartbeatExpiryFromStack +++ Func.stop) post ∧
      post.gasLeft = G +
        ((gasStorageUpdate - gasColdSload) -
          sstoreValueCost originalExpiry oldExpiry expiry) ∧
      post.getStorVal sevm.currentTarget
        (expirySlot sevm.caller.toB256) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, sevm.caller.toB256], expiry.toBytes⟩] := by
  rcases heartbeat_sstoreValueCost_partition timestamp originalExpiry
      oldExpiry expiry holdLive with hupdate | hother
  · rcases heartbeat_storeLogTail_runCompiled_update fs sevm base
        originalExpiry oldExpiry expiry G holdExpiry horigExpiry hwarmExpiry
        hstatic hupdate with ⟨post, hrun, hgas, hstore, hlogs⟩
    refine ⟨post, hrun, ?_, hstore, hlogs⟩
    simpa [hupdate, gasStorageUpdate, gasColdSload] using hgas
  · rcases heartbeat_storeLogTail_runCompiled_other fs sevm base
        originalExpiry oldExpiry expiry G holdExpiry horigExpiry hwarmExpiry
        hstatic hother with ⟨post, hrun, hgas, hstore, hlogs⟩
    refine ⟨post, hrun, ?_, hstore, hlogs⟩
    simpa [hother, gasStorageUpdate, gasColdSload, gasWarmAccess] using hgas

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- Generic successful heartbeat body over the actual sequential warm/cold
SLOAD costs and the exhaustive successful SSTORE value-cost partition. -/
private theorem heartbeat_body_runCompiled_generic
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (count oldExpiry timestamp interval expiry originalExpiry : B256)
    (G : Nat)
    (htime : sevm.benvStat.time = timestamp)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) = count)
    (hcountNonzero : count ≠ 0)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (horigExpiry : getOrigStorVal sevm sevm.currentTarget
      (expirySlot sevm.caller.toB256) = originalExpiry)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hstatic : sevm.isStatic = false)
    (holdLive : timestamp < oldExpiry)
    (extension : CheckedHeartbeatExtension timestamp interval expiry) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty,
          G + heartbeatBodySuccessGas sevm base⟩)
        heartbeat post ∧
      post.gasLeft = G +
        ((gasStorageUpdate - gasColdSload) -
          sstoreValueCost originalExpiry oldExpiry expiry) ∧
      post.getStorVal sevm.currentTarget
        (expirySlot sevm.caller.toB256) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, sevm.caller.toB256], expiry.toBytes⟩] := by
  let cCount := heartbeatSloadCost sevm base
    (countSlot sevm.caller.toB256)
  let cExpiry := heartbeatSloadCost sevm
    (heartbeatAfterCountLoad sevm base) (expirySlot sevm.caller.toB256)
  let cInterval := heartbeatSloadCost sevm
    (heartbeatAfterExpiryLoad sevm base) heartbeatIntervalSlot
  let gChecked := G + 4310
  let gLive := gChecked + 32 + cInterval
  let gExpiry := gLive + 19
  let gGuard := gExpiry + 8 + cExpiry
  let gCount := gGuard + 16
  have htailHold : (heartbeatAfterIntervalLoad sevm base).getStorVal
      sevm.currentTarget (expirySlot sevm.caller.toB256) = oldExpiry := by
    simpa [heartbeatAfterIntervalLoad, heartbeatAfterExpiryLoad,
      heartbeatAfterCountLoad] using holdExpiry
  rcases heartbeat_storeLogTail_runCompiled_partition fs sevm
      (heartbeatAfterIntervalLoad sevm base) timestamp originalExpiry
      oldExpiry expiry G htailHold horigExpiry
      (heartbeatAfterIntervalLoad_expiry_warm sevm base) hstatic holdLive with
    ⟨post, htail, hgas, hstore, hlogs⟩
  have hchecked := heartbeat_checkedExpiry_runCompiled_then fs sevm base
    timestamp interval expiry gChecked htime hinterval extension
    (storeHeartbeatExpiryFromStack +++ Func.stop) post htail
  have hlive := heartbeat_liveGuard_runCompiled_then fs sevm base oldExpiry
    timestamp gLive htime holdLive (checkedHeartbeatExpiry
      (storeHeartbeatExpiryFromStack +++ Func.stop)) post hchecked
  have hexpiry := heartbeat_expiryLoad_runCompiled_then fs sevm base
    oldExpiry gExpiry holdExpiry
    (Ninst.timestamp ::: Ninst.lt :::
      (checkedHeartbeatExpiry
        (storeHeartbeatExpiryFromStack +++ Func.stop) <?>
        (.call heartbeatExpiredErrorSlot)))
    post (by simpa [gExpiry] using hlive)
  have hguard := heartbeat_registeredGuard_runCompiled_then fs sevm base
    count gGuard hcountNonzero
    (Ninst.caller ::: tagTop expiryRegion +++ Ninst.sload :::
      Ninst.timestamp ::: Ninst.lt :::
        (checkedHeartbeatExpiry
          (storeHeartbeatExpiryFromStack +++ Func.stop) <?>
          (.call heartbeatExpiredErrorSlot)))
    post (by simpa [gGuard, gExpiry, cExpiry] using hexpiry)
  have hbody := heartbeat_countLoad_runCompiled_then fs sevm base count
    gCount hcount
    (Ninst.iszero :::
      ((.call senderNotPauserErrorSlot) <?>
        (Ninst.caller ::: tagTop expiryRegion +++ Ninst.sload :::
          Ninst.timestamp ::: Ninst.lt :::
            (checkedHeartbeatExpiry
              (storeHeartbeatExpiryFromStack +++ Func.stop) <?>
              (.call heartbeatExpiredErrorSlot)))))
    post (by simpa [gCount] using hguard)
  have hinitial : gCount + 8 + cCount =
      G + heartbeatBodySuccessGas sevm base := by
    dsimp [gCount, gGuard, gExpiry, gLive, gChecked, cCount, cExpiry,
      cInterval, heartbeatBodySuccessGas]
    omega
  refine ⟨post, ?_, hgas, hstore, ?_⟩
  · rw [← hinitial]
    simpa only [heartbeat] using hbody
  · simpa [heartbeatAfterIntervalLoad, heartbeatAfterExpiryLoad,
      heartbeatAfterCountLoad] using hlogs

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

/-! ## Heartbeat transition -/

/-- Entry-count failure has source precedence over liveness and arithmetic:
the heartbeat body reaches `SenderNotPauser` after reading only the warm count
slot, with no persistent effect or raw event. -/
theorem heartbeat_body_runCompiledTo_error_of_count_zero
    (dp : DeployParams) (sevm : Sevm) (base : Devm) (G : Nat)
    (hcount : Devm.getStorVal base sevm.currentTarget
      (countSlot sevm.caller.toB256) = 0)
    (hwarm : (⟨sevm.currentTarget,
      countSlot sevm.caller.toB256⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Func.RunCompiledTo (runtimeMain dp :: aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 154⟩)
        heartbeat (.error (.revert, post)) ∧
      post.output = customErrorData "SenderNotPauser" ∧
      post.logs = base.logs ∧
      ∀ a k, post.getStorVal a k = base.getStorVal a k := by
  let data := customErrorData "SenderNotPauser"
  let post := (base.setMach
    ⟨[], Mem.empty.write 0 data.toB256.toBytes, G⟩).withOutput data
  refine ⟨post, ?_, rfl, rfl, ?_⟩
  · unfold heartbeat tagTop
    func_run (7) [countSlot sevm.caller.toB256, 1]
    all_goals try {
      simp only [Devm.getStorVal_setMach, hcount]
      simp [B256.eqCheck] }
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

/-- A registered caller whose expiry is equal to or earlier than the current
timestamp reaches the exact `HeartbeatExpired` source error without a write or
raw event.  Equality is deliberately included. -/
theorem heartbeat_body_runCompiledTo_error_of_expired
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (count oldExpiry timestamp : B256) (G : Nat)
    (htime : sevm.benvStat.time = timestamp)
    (hcount : Devm.getStorVal base sevm.currentTarget
      (countSlot sevm.caller.toB256) = count)
    (hcountNonzero : count ≠ 0)
    (holdExpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (hwarmCount : (⟨sevm.currentTarget,
      countSlot sevm.caller.toB256⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hwarmExpiry : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hexpired : oldExpiry ≤ timestamp) :
    ∃ post,
      Func.RunCompiledTo (runtimeMain dp :: aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 279⟩)
        heartbeat (.error (.revert, post)) ∧
      post.output = customErrorData "HeartbeatExpired" ∧
      post.logs = base.logs ∧
      ∀ a k, post.getStorVal a k = base.getStorVal a k := by
  let data := customErrorData "HeartbeatExpired"
  let post := (base.setMach
    ⟨[], Mem.empty.write 0 data.toB256.toBytes, G⟩).withOutput data
  refine ⟨post, ?_, rfl, rfl, ?_⟩
  · unfold heartbeat tagTop
    func_run (14) [countSlot sevm.caller.toB256, 0,
      expirySlot sevm.caller.toB256, 0]
    all_goals try {
      simp only [Devm.getStorVal_setMach, hcount]
      simp [B256.eqCheck, hcountNonzero] }
    all_goals try {
      simp only [Devm.getStorVal_setMach, holdExpiry, htime]
      simp [B256.ltCheck, B256.not_lt.mpr hexpired] }
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

def heartbeatDispatchGas : Nat := 192

set_option maxRecDepth 16384 in
/-- Exact emitted-runtime dispatcher bridge for any terminal heartbeat body
outcome. -/
theorem heartbeat_dispatch_runCompiledTo
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (bodyGas G : Nat) (out : Execution)
    (hdata : sevm.data.length.toB256 = 4)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "heartbeat" [])
    (_hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hbody : Func.RunCompiledTo (runtimeMain dp :: aux) sevm
      (base.setMach ⟨[], Mem.empty, G + bodyGas⟩) heartbeat out) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty,
        G + heartbeatDispatchGas + bodyGas⟩)
      (runtime dp) out ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  refine ⟨?_, ?_⟩
  · refine Prog.runCompiledTo_intro
      (mid := base.setMach ⟨[], Mem.empty, G + 191 + bodyGas⟩)
      (G := G + 191 + bodyGas) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, heartbeatDispatchGas, gJumpdest]
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
            selector "heartbeat" [] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (37) [0, 0, selector "heartbeat" [],
        1, 1, 0, 0, 0, 0, 1]
      case h_arm =>
        have hboundary : G + 191 + bodyGas - 191 = G + bodyGas := by
          omega
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
          runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
          List.take, List.drop, List.head?, Option.map, Option.getD,
          linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

set_option maxRecDepth 16384 in
/-- Exact generated-runtime heartbeat success over the actual sequential
warm/cold SLOAD costs and exhaustive successful SSTORE value-cost partition. -/
theorem heartbeat_runCompiledTo_of_checkedExtension_generic
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (count oldExpiry timestamp interval expiry originalExpiry : B256)
    (G : Nat)
    (hdata : sevm.data.length.toB256 = 4)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "heartbeat" [])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htime : sevm.benvStat.time = timestamp)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) = count)
    (hcountNonzero : count ≠ 0)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (horigExpiry : getOrigStorVal sevm sevm.currentTarget
      (expirySlot sevm.caller.toB256) = originalExpiry)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hstatic : sevm.isStatic = false)
    (holdLive : timestamp < oldExpiry)
    (extension : CheckedHeartbeatExtension timestamp interval expiry) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + heartbeatDispatchGas + heartbeatBodySuccessGas sevm base⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G +
        ((gasStorageUpdate - gasColdSload) -
          sstoreValueCost originalExpiry oldExpiry expiry) ∧
      post.getStorVal sevm.currentTarget
        (expirySlot sevm.caller.toB256) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, sevm.caller.toB256], expiry.toBytes⟩] ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases heartbeat_body_runCompiled_generic
      (runtimeMain dp :: aux) sevm base count oldExpiry timestamp interval
      expiry originalExpiry G htime hcount hcountNonzero holdExpiry
      horigExpiry hinterval hstatic holdLive extension with
    ⟨post, hbody, hgas, hstore, hlogs⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases heartbeat_dispatch_runCompiledTo dp sevm base
      (heartbeatBodySuccessGas sevm base) G (.ok post) hdata hvalue hselector
      hcodeAddress hcode hbodyTo with ⟨hrun, hcompile⟩
  exact ⟨post, hrun, hgas, hstore, hlogs, hcompile⟩

/-- Exact public-dispatch success for a registered caller that is strictly
live at entry and whose checked extension changes a nonzero expiry. -/
theorem heartbeat_runCompiledTo_of_checkedExtension
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (count oldExpiry timestamp interval expiry : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 4)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "heartbeat" [])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
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
      countSlot sevm.caller.toB256⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hwarmExpiry : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hwarmInterval : (⟨sevm.currentTarget,
      heartbeatIntervalSlot⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (holdLive : timestamp < oldExpiry)
    (holdNonzero : oldExpiry ≠ 0)
    (hchanged : oldExpiry ≠ expiry)
    (extension : CheckedHeartbeatExtension timestamp interval expiry) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + heartbeatDispatchGas + heartbeatBodySuccessGasWarmUpdate⟩)
        (runtime dp) (.ok post) ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget
        (expirySlot sevm.caller.toB256) = expiry ∧
      post.logs = base.logs ++
        [⟨sevm.currentTarget,
          [heartbeatUpdatedEvent, sevm.caller.toB256], expiry.toBytes⟩] ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases heartbeat_body_runCompiled_of_checkedExtension
      (runtimeMain dp :: aux) sevm base count oldExpiry timestamp interval
      expiry G htime hcount hcountNonzero holdExpiry horigExpiry hinterval
      hwarmCount hwarmExpiry hwarmInterval hstatic holdLive holdNonzero
      hchanged extension with
    ⟨post, hbody, hgas, hstore, hlogs⟩
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  rcases heartbeat_dispatch_runCompiledTo dp sevm base
      heartbeatBodySuccessGasWarmUpdate G (.ok post) hdata hvalue hselector
      hcodeAddress hcode hbodyTo with ⟨hrun, hcompile⟩
  exact ⟨post, hrun, hgas, hstore, hlogs, hcompile⟩

theorem heartbeat_runCompiledTo_error_of_count_zero
    (dp : DeployParams) (sevm : Sevm) (base : Devm) (G : Nat)
    (hdata : sevm.data.length.toB256 = 4) (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "heartbeat" [])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) = 0)
    (hwarm : (⟨sevm.currentTarget,
      countSlot sevm.caller.toB256⟩ : Adr × B256) ∈ base.accessedStorageKeys) :
    ∃ post, Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + heartbeatDispatchGas + 154⟩)
        (runtime dp) (.error (.revert, post)) ∧
      post.output = customErrorData "SenderNotPauser" ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases heartbeat_body_runCompiledTo_error_of_count_zero dp sevm base G
      hcount hwarm with ⟨post, hbody, houtput, hlogs, hstorage⟩
  rcases heartbeat_dispatch_runCompiledTo dp sevm base 154 G
      (.error (.revert, post)) hdata hvalue hselector hcodeAddress hcode hbody
      with ⟨hrun, hcompile⟩
  exact ⟨post, hrun, houtput, hlogs, hstorage, hcompile⟩

theorem heartbeat_runCompiledTo_error_of_expired
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (count oldExpiry timestamp : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 4) (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "heartbeat" [])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htime : sevm.benvStat.time = timestamp)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) = count)
    (hcountNonzero : count ≠ 0)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (hwarmCount : (⟨sevm.currentTarget,
      countSlot sevm.caller.toB256⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hwarmExpiry : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hexpired : oldExpiry ≤ timestamp) :
    ∃ post, Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + heartbeatDispatchGas + 279⟩)
        (runtime dp) (.error (.revert, post)) ∧
      post.output = customErrorData "HeartbeatExpired" ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases heartbeat_body_runCompiledTo_error_of_expired dp sevm base
      count oldExpiry timestamp G htime hcount hcountNonzero holdExpiry
      hwarmCount hwarmExpiry hexpired with
    ⟨post, hbody, houtput, hlogs, hstorage⟩
  rcases heartbeat_dispatch_runCompiledTo dp sevm base 279 G
      (.error (.revert, post)) hdata hvalue hselector hcodeAddress hcode hbody
      with ⟨hrun, hcompile⟩
  exact ⟨post, hrun, houtput, hlogs, hstorage, hcompile⟩

def heartbeatArithmeticPanicData : Bytes :=
  (signatureHash "Panic" [.uint256]).toBytes.take 4 ++
    (Nat.toB256 0x11).toBytes

/-- Exact checked-add overflow arm.  The caller is registered and strictly
live at entry; the wrapped EVM sum is below the timestamp, so source control
reaches the production `Panic(0x11)` helper before any SSTORE or log. -/
theorem heartbeat_body_runCompiledTo_error_of_add_wrap
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (count oldExpiry timestamp interval : B256) (G : Nat)
    (htime : sevm.benvStat.time = timestamp)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) = count)
    (hcountNonzero : count ≠ 0)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarmCount : (⟨sevm.currentTarget,
      countSlot sevm.caller.toB256⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hwarmExpiry : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hwarmInterval : (⟨sevm.currentTarget,
      heartbeatIntervalSlot⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (holdLive : timestamp < oldExpiry)
    (hwrap : timestamp + interval < timestamp) :
    ∃ post,
      Func.RunCompiledTo (runtimeMain dp :: aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 424⟩)
        heartbeat (.error (.revert, post)) ∧
      post.output = heartbeatArithmeticPanicData ∧
      post.logs = base.logs ∧
      ∀ a k, post.getStorVal a k = base.getStorVal a k := by
  let post := (base.setMach ⟨[timestamp + interval], Mem.writeStoresRev Mem.empty
    (bytesWords heartbeatArithmeticPanicData).zipIdx, G⟩).withOutput
      heartbeatArithmeticPanicData
  refine ⟨post, ?_, rfl, rfl, ?_⟩
  · unfold heartbeat checkedHeartbeatExpiry tagTop
    func_run (23) [countSlot sevm.caller.toB256, 0,
      expirySlot sevm.caller.toB256, 1,
      timestamp + interval, 1]
    all_goals try {
      simp only [Devm.getStorVal_setMach, hcount]
      simp [B256.eqCheck, hcountNonzero] }
    all_goals try {
      simp only [Devm.getStorVal_setMach, holdExpiry, htime]
      simp [B256.ltCheck, holdLive] }
    all_goals try {
      simp only [Devm.getStorVal_setMach, hinterval, htime]
      rw [B256.add_comm] }
    all_goals try {
      rw [htime]
      simp [B256.ltCheck, hwrap] }
    case h_body =>
      apply Func.runCompiledTo_revData (G := G)
      · exact Mem.wf_empty
      · exact Mem.reads_empty
      · rfl
      · simp [B256.length_toBytes]
      · decide +kernel
      · simp only [Devm.gasLeft_setMach]
        change G + 424 - 396 =
          G + (storesFixedCost
              (bytesWords heartbeatArithmeticPanicData).zipIdx +
            pushCost
              (Nat.toB256 heartbeatArithmeticPanicData.length).toBytes.sig +
            gBase +
            (base.setMach ⟨[timestamp + interval], Mem.empty,
              G + 424 - 396⟩).extCost
              [(0, 32 * (bytesWords heartbeatArithmeticPanicData).length)])
        have hfixed : storesFixedCost
              (bytesWords heartbeatArithmeticPanicData).zipIdx +
            pushCost
              (Nat.toB256 heartbeatArithmeticPanicData.length).toBytes.sig +
            gBase = 22 := by
          decide +kernel
        have hext :
            (base.setMach ⟨[timestamp + interval], Mem.empty,
              G + 424 - 396⟩).extCost
                [(0, 32 * (bytesWords heartbeatArithmeticPanicData).length)] =
              6 := by
          apply Devm.extCost_of_size rfl
          decide +kernel
        rw [hfixed, hext]
        omega
      · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        norm_num
  · intro a k
    rfl

theorem heartbeat_runCompiledTo_error_of_add_wrap
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (count oldExpiry timestamp interval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 4) (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "heartbeat" [])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htime : sevm.benvStat.time = timestamp)
    (hcount : base.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) = count)
    (hcountNonzero : count ≠ 0)
    (holdExpiry : base.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) = oldExpiry)
    (hinterval : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarmCount : (⟨sevm.currentTarget,
      countSlot sevm.caller.toB256⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hwarmExpiry : (⟨sevm.currentTarget,
      expirySlot sevm.caller.toB256⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hwarmInterval : (⟨sevm.currentTarget,
      heartbeatIntervalSlot⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (holdLive : timestamp < oldExpiry)
    (hwrap : timestamp + interval < timestamp) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + heartbeatDispatchGas + 424⟩)
        (runtime dp) (.error (.revert, post)) ∧
      post.output = heartbeatArithmeticPanicData ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases heartbeat_body_runCompiledTo_error_of_add_wrap dp sevm base
      count oldExpiry timestamp interval G htime hcount hcountNonzero
      holdExpiry hinterval hwarmCount hwarmExpiry hwarmInterval holdLive hwrap
      with ⟨post, hbody, houtput, hlogs, hstorage⟩
  rcases heartbeat_dispatch_runCompiledTo dp sevm base 424 G
      (.error (.revert, post)) hdata hvalue hselector hcodeAddress hcode hbody
      with ⟨hrun, hcompile⟩
  exact ⟨post, hrun, houtput, hlogs, hstorage, hcompile⟩

/-- Canonical selector-only calldata for `heartbeat()`. -/
def heartbeatCalldata : Bytes :=
  abiSelectorBytes (selector "heartbeat" [])

/-- Clean settlement of an exact direct heartbeat message retains its raw
successful poststate. -/
theorem heartbeat_success_settles_cleanly
    (dp : DeployParams) {msg : Msg} {ca : Adr}
    {final settled : Devm}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = heartbeatCalldata)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
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

set_option maxRecDepth 16384 in
/-- Exact clean direct-message heartbeat effects, derived from generated
runtime execution rather than supplied as facts about the raw result.

`hgasEntry` identifies the message's seeded gas with the exact dispatcher/body
budget.  `hfilled` supplies the closed execution carried by the same pc-zero
raw slot; `ProcessMessage` alone records that slot but does not certify its
execution. -/
theorem heartbeat_success_settled_effects
    (dp : DeployParams) {msg : Msg} {ca : Adr}
    {final settled : Devm}
    (count oldExpiry timestamp interval expiry originalExpiry : B256)
    (G : Nat)
    (htarget : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = heartbeatCalldata)
    (hgasEntry : msg.gas = G + heartbeatDispatchGas +
      heartbeatBodySuccessGas (initSevm msg) (initDevm msg))
    (htime : (initSevm msg).benvStat.time = timestamp)
    (hcount : (initDevm msg).getStorVal (initSevm msg).currentTarget
      (countSlot (initSevm msg).caller.toB256) = count)
    (hcountNonzero : count ≠ 0)
    (holdExpiry : (initDevm msg).getStorVal
      (initSevm msg).currentTarget
      (expirySlot (initSevm msg).caller.toB256) = oldExpiry)
    (horigExpiry : getOrigStorVal (initSevm msg)
      (initSevm msg).currentTarget
      (expirySlot (initSevm msg).caller.toB256) = originalExpiry)
    (hinterval : (initDevm msg).getStorVal
      (initSevm msg).currentTarget heartbeatIntervalSlot = interval)
    (hstatic : (initSevm msg).isStatic = false)
    (holdLive : timestamp < oldExpiry)
    (extension : CheckedHeartbeatExtension timestamp interval expiry)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩)
      (.ok settled))
    (hfilled : Xlot.Filled
      (.some ⟨⟨0, initSevm msg, initDevm msg⟩, .ok final⟩))
    (hclean : final.error.isNone = true) :
    settled.gasLeft = G +
        ((gasStorageUpdate - gasColdSload) -
          sstoreValueCost originalExpiry oldExpiry expiry) ∧
      settled.getStorVal ca
        (expirySlot msg.caller.toB256) = expiry ∧
      settled.logs = (initDevm msg).logs ++
        [⟨ca, [heartbeatUpdatedEvent, msg.caller.toB256],
          expiry.toBytes⟩] := by
  have hdataInit : (initSevm msg).data = heartbeatCalldata := by
    simpa [initSevm] using hdata
  have hdataLength : (initSevm msg).data.length.toB256 = 4 := by
    rw [hdataInit]
    simp only [heartbeatCalldata, abiSelectorBytes_length]
    decide +kernel
  have hselector : Sevm.selector (initSevm msg) =
      selector "heartbeat" [] := by
    rw [Sevm.selector, Sevm.dataWord, hdataInit, heartbeatCalldata]
    decide +kernel
  have hvalueInit : (initSevm msg).value = 0 := by
    simpa [initSevm] using hvalue
  have hownerInit : (initSevm msg).currentTarget = ca := by
    simpa [initSevm] using howner
  have hcodeAddressInit : (initSevm msg).codeAddress =
      some (initSevm msg).currentTarget := by
    simpa [initSevm, howner] using hcodeAddress
  have hcodeInit : (initSevm msg).code.toList =
      lidoCircuitBreakerCode dp := by
    simpa [initSevm] using hcode
  rcases heartbeat_runCompiledTo_of_checkedExtension_generic dp
      (initSevm msg) (initDevm msg) count oldExpiry timestamp interval
      expiry originalExpiry G hdataLength hvalueInit hselector
      hcodeAddressInit hcodeInit htime hcount hcountNonzero holdExpiry
      horigExpiry hinterval hstatic holdLive extension with
    ⟨post, hrun, hgas, hstore, hlogs, hcompile⟩
  have hentryState :
      (initDevm msg).setMach ⟨[], Mem.empty,
        G + heartbeatDispatchGas +
          heartbeatBodySuccessGas (initSevm msg) (initDevm msg)⟩ =
        initDevm msg := by
    rw [← hgasEntry]
    rfl
  have hrunEntry : Prog.RunCompiledTo (initSevm msg) (initDevm msg)
      (runtime dp) (.ok post) := by
    rw [hentryState] at hrun
    exact hrun
  have hexecEq : exec ⟨0, initSevm msg, initDevm msg⟩ = .ok post :=
    Prog.exec_of_runCompiledTo hrunEntry hcompile
  obtain ⟨hpostExec⟩ :=
    (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok post)).mpr
      hexecEq
  change Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok final)) at hfilled
  obtain ⟨hfinalExec⟩ := hfilled
  have hraw : (.ok final : Execution) = .ok post :=
    Exec.result_unique hfinalExec hpostExec
  have hfinalPost : final = post := Except.ok.inj hraw
  have hsettledFinal := heartbeat_success_settles_cleanly dp htarget howner
    hcodeAddress hcode hvalue hdata hprocess hclean
  have hsettledPost : settled = post := hsettledFinal.trans hfinalPost
  rw [hsettledPost]
  refine ⟨hgas, ?_, ?_⟩
  · simpa [initSevm, howner] using hstore
  · simpa [initSevm, howner] using hlogs

/-- Any settled error of an exact direct heartbeat message restores the
complete owner storage and transient storage from message entry. -/
theorem heartbeat_settled_error_restores_owner
    (dp : DeployParams) {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = heartbeatCalldata)
    (hprocess : ProcessMessage msg slot (.ok post))
    (herror : post.error.isSome) :
    Devm.getStor post ca = msg.benv.state.getStor ca ∧
      post.transientStorage = msg.tenv.transientStorage := by
  have hrollback := ProcessMessage.rollback_of_error hprocess herror
  exact ⟨congrArg (fun state : State => state.getStor ca) hrollback.1,
    hrollback.2⟩

/-- At the exact top-level call boundary, an errored direct heartbeat message
exposes no receipt log.  This does not claim that raw `Devm.logs` are erased by
`ProcessMessage`. -/
theorem heartbeat_settled_error_logs_eq_nil
    (dp : DeployParams) {msg : Msg} {state : State} {out : MsgCallOutput}
    {ca : Adr}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = heartbeatCalldata)
    (hrun : processMessageCall msg = .ok (state, out))
    (herror : out.error.isSome) :
    out.logs = [] :=
  processMessageCall_error_logs_eq_nil hrun herror

end Blanc.LidoCircuitBreaker
