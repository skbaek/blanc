import Blanc.LidoCircuitBreakerCode
import Blanc.LidoCircuitBreakerRegistry
import Blanc.LidoCircuitBreakerRegistryModel
import Blanc.ForwardCall

/-!
Concrete successful exact-code execution control for the CircuitBreaker
Registry proof.  The abstract walk is kept in this small gate-owned module so
its elaboration cost is independent of the large reusable proof owner.
-/

namespace Blanc.LidoCircuitBreaker.RegistrySuccess

open Jaune
open Jaune.Ninst Blanc.Ninst

set_option maxHeartbeats 800000
set_option maxRecDepth 16384

private theorem registerAfterSetLogExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {stack : Stack}
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (hroom : stack.length < 1020)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨stack, M, 10000⟩)
        (loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop)
      (fun ex => ∃ post, ex = .ok post) := by
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hzeroCovered :
      ((0 : B256) * 32).toNat + ((1 : B256) * 32).toNat ≤ M.size := by
    have hoff :
        ((0 : B256) * 32).toNat + ((1 : B256) * 32).toNat = 32 := by
      decide
    omega
  have hnewMemory :
      (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have hextNew (base : Devm) (S : List B256) (G : Nat) :
      (base.setMach ⟨S, M, G⟩).extCost
          [⟨(newPauserWord * 32).toNat, 32⟩] = 0 :=
    Devm.extCost_zero_of_le halign hnewCovered
  have hextZero (base : Devm) (S : List B256) (G : Nat) :
      (base.setMach ⟨S, M, G⟩).extCost
          [⟨((0 : B256) * 32).toNat, ((1 : B256) * 32).toNat⟩] = 0 :=
    Devm.extCost_zero_of_le halign hzeroCovered
  have halignNew :
      (M.read (newPauserWord * 32).toNat 32).2.size % 32 = 0 := by
    rw [hnewMemory]
    exact halign
  have hzeroCoveredNew :
      ((0 : B256) * 32).toNat + ((1 : B256) * 32).toNat ≤
        (M.read (newPauserWord * 32).toNat 32).2.size := by
    rw [hnewMemory]
    exact hzeroCovered
  have hextZeroAfter (base : Devm) (S : List B256) (G : Nat) :
      (base.setMach
        ⟨S, (M.read (newPauserWord * 32).toNat 32).2, G⟩).extCost
          [⟨((0 : B256) * 32).toNat, ((1 : B256) * 32).toNat⟩] = 0 :=
    Devm.extCost_zero_of_le halignNew hzeroCoveredNew
  have hlogLen : ((1 : B256) * 32).toNat = 32 := by decide
  apply Func.execSat_of_runCompiledTo
  · func_run [3, 1381]
    all_goals try {
      simp [hextNew, hextZero, hnewMemory, hnew, runtime, aux,
        gVerylow, gLog, gLogdata, gLogtopic] }
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons]
      omega }
    all_goals try omega
    case h_cost =>
      rw [hextZeroAfter, hlogLen]
      norm_num [gLog, gLogdata, gLogtopic]
    case a => exact .last rfl
  · exact ⟨_, rfl⟩

private theorem registerAfterSetStoreExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {stack : Stack}
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry : (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hroom : stack.length < 1020)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach
        ⟨expirySlot 9 :: 10 :: stack, M, 10000 + gasStorageSet⟩)
        (sstore :::
          loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop)
      (fun ex => ∃ post, ex = .ok post) := by
  apply Func.execSat_next
  · apply Ninst.runCompiled_sstore_warm
      (c := gasStorageSet) (G := 10000)
    · rfl
    · change (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys
      exact hwarmExpiry
    · simp only [Devm.gasLeft_setMach]
      norm_num [gCallStipend, gasStorageSet]
    · exact hstatic
    · change sstoreValueCost
        (getOrigStorVal e e.currentTarget (expirySlot 9))
        (d.getStorVal e.currentTarget (expirySlot 9)) 10 = gasStorageSet
      simp [hexpiryOrig, hexpiry, sstoreValueCost]
      intro h
      exact False.elim ((by decide : (0 : B256) ≠ 10) h)
    · rfl
    · simp only [Devm.gasLeft_setMach]
  · exact registerAfterSetLogExecSatOf
      (stack := stack) hnew hsize halign hroom hstatic

private theorem readNewPauser_after_writeZero
    {M : Mem} {bs : Bytes} {w : B256}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs) :
    ((M.write 0 w.toBytes).read
      (newPauserWord * 32).toNat 32).1 =
      (M.read (newPauserWord * 32).toNat 32).1 := by
  rw [Mem.Reads.read (Mem.Reads.write hwf hreads 0 w.toBytes),
    Mem.Reads.read hreads, List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  rw [Bytes.getD_writeAt, if_neg]
  have hi' := List.mem_range.mp hi
  have hoff : 32 ≤ (newPauserWord * 32).toNat := by decide
  rw [B256.length_toBytes]
  omega

private theorem size_writeZero_word_of_le
    {M : Mem} {w : B256} (h : 32 ≤ M.size) :
    (M.write 0 w.toBytes).size = M.size := by
  rcases hb : w.toBytes with _ | ⟨b, bs⟩
  · exact absurd (hb ▸ B256.length_toBytes w) (by simp)
  · have hlen : (b :: bs).length = 32 := hb ▸ B256.length_toBytes w
    simp only [Mem.write, hlen, Nat.zero_add]
    rw [if_pos h]
    split <;> rfl

private theorem registerAfterSetWriteExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes} {stack : Stack}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry : (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hroom : stack.length < 1020)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨10 :: stack, M, 10000 + gasStorageSet + 20⟩)
        (dup 0 ::: mstoreAt 0 +++
          loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
          loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop)
      (fun ex => ∃ post, ex = .ok post) := by
  let M' := M.write 0 (10 : B256).toBytes
  have hsize' : 768 ≤ M'.size := by
    rw [show M'.size = M.size from size_writeZero_word_of_le (by omega)]
    exact hsize
  have halign' : M'.size % 32 = 0 := by
    rw [show M'.size = M.size from size_writeZero_word_of_le (by omega)]
    exact halign
  have hnew' :
      (M'.read (newPauserWord * 32).toNat 32).1.toB256 = 9 := by
    rw [readNewPauser_after_writeZero hwf hreads]
    exact hnew
  have hnewCovered' : (newPauserWord * 32).toNat + 32 ≤ M'.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hnewMemory' :
      (M'.read (newPauserWord * 32).toNat 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hnewCovered')]
  apply Func.execSat_segment
    (devm' := d.setMach
      ⟨expirySlot 9 :: 10 :: stack, M', 10000 + gasStorageSet⟩)
    (f' := sstore :::
      loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
      logWith 1 0 1 +++ Func.stop)
  · intro ex htail
    func_run (7) [0, 3]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons]
      omega }
    case h_ext =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_zero_of_le halign (by omega)]
    case h_cost =>
      change gVerylow +
        (d.setMach ⟨_, M', _⟩).extCost
          [⟨(newPauserWord * 32).toNat, 32⟩] = 3
      rw [Devm.extCost_zero_of_le halign' hnewCovered']
      norm_num [gVerylow]
    case h_f =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide]
      change Func.ExecWitness _ _
        (d.setMach
          ⟨(regionWord expiryRegion).or
              (M'.read (newPauserWord * 32).toNat 32).1.toB256 :: 10 :: stack,
            (M'.read (newPauserWord * 32).toNat 32).2,
            10000 + gasStorageSet + 20 - 20⟩) _ ex
      rw [hnew', hnewMemory']
      rw [show (regionWord expiryRegion).or 9 = expirySlot 9 by rfl]
      norm_num
      exact htail
  · exact registerAfterSetStoreExecSatOf
      (stack := stack) hnew' hsize' halign'
      hexpiry hexpiryOrig hwarmExpiry hroom hstatic

private theorem registerAfterSetCheckedExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes} {stack : Stack}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (hinterval : d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry : (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hroom : stack.length < 1020)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132⟩)
        (checkedHeartbeatExpiry <|
          dup 0 ::: mstoreAt 0 +++
          loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
          loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop)
      (fun ex => ∃ post, ex = .ok post) := by
  let d' := addAccessedStorageKey d e.currentTarget heartbeatIntervalSlot
  have hexpiry' : d'.getStorVal e.currentTarget (expirySlot 9) = 0 := by
    change d.getStorVal e.currentTarget (expirySlot 9) = 0
    exact hexpiry
  have hwarmExpiry' :
      (e.currentTarget, expirySlot 9) ∈ d'.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simpa [d', addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys]
      using (Or.inr hwarmExpiry :
        heartbeatIntervalSlot = expirySlot 9 ∨
          (e.currentTarget, expirySlot 9) ∈ mt.accessedStorageKeys)
  have hsuffix := registerAfterSetWriteExecSatOf
    (e := e) (d := d') (stack := stack) hwf hreads hnew hsize halign
    hexpiry' hexpiryOrig hwarmExpiry' hroom hstatic
  have hbranch : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d'.setMach ⟨0 :: 10 :: stack, M,
        10000 + gasStorageSet + 20 + (gVerylow + gHigh)⟩)
        ((.call arithmeticPanicSlot) <?>
          (dup 0 ::: mstoreAt 0 +++
            loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop))
        (fun ex => ∃ post, ex = .ok post) := by
    rcases hsuffix with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_branch_zero rfl (by
      simp only [Devm.stack_setMach]
      simp only [List.length_cons]
      omega)
    · rfl
    · exact hw
  apply Func.execSat_segment
    (devm' := d'.setMach ⟨0 :: 10 :: stack, M,
      10000 + gasStorageSet + 20 + (gVerylow + gHigh)⟩)
    (f' := (.call arithmeticPanicSlot) <?>
      (dup 0 ::: mstoreAt 0 +++
        loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
        loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
        logWith 1 0 1 +++ Func.stop))
  · intro ex htail
    func_run (8) [10]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons]
      omega }
    all_goals try omega
    case h_val =>
      change d.getStorVal e.currentTarget heartbeatIntervalSlot +
        e.benvStat.time = 10
      rw [hinterval, htime]
      rfl
    case h_f =>
      have haddMach :
          addAccessedStorageKey
              (d.setMach
                ⟨heartbeatIntervalSlot :: e.benvStat.time :: stack, M,
                  10000 + gasStorageSet + 20 + 2132 - 5⟩)
              e.currentTarget heartbeatIntervalSlot =
            d'.setMach
              ⟨heartbeatIntervalSlot :: e.benvStat.time :: stack, M,
                10000 + gasStorageSet + 20 + 2132 - 5⟩ := rfl
      rw [haddMach, htime]
      norm_num [gVerylow, gHigh]
      exact htail
  · exact hbranch

private theorem registerAfterSetExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes} {stack : Stack}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (hprevious :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (hinterval : d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry : (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hroom : stack.length < 1020)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45⟩)
        registerAfterSet
      (fun ex => ∃ post, ex = .ok post) := by
  let checkedBody : Func :=
    checkedHeartbeatExpiry <|
      dup 0 ::: mstoreAt 0 +++
      loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
      loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
      logWith 1 0 1 +++ Func.stop
  let freshBody : Func :=
    loadWord newPauserWord +++ iszero :::
      (Func.stop <?> checkedBody)
  let oldBody : Func :=
    previousCountKey +++ sload ::: iszero :::
      (pushB256 0 ::: loadWord previousPauserWord +++
          tagTop expiryRegion +++ sstore :::
        pushB256 0 ::: mstoreAt 0 +++
        loadWord previousPauserWord +++
          pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++
        loadWord newPauserWord +++ iszero :::
        (Func.stop <?> checkedBody)) <?>
      (loadWord newPauserWord +++ iszero :::
        (Func.stop <?> checkedBody))
  have hsuffix := registerAfterSetCheckedExecSatOf
    (e := e) (d := d) (stack := stack) hwf hreads hnew hsize halign htime
    hinterval hintervalCold hexpiry hexpiryOrig hwarmExpiry hroom hstatic
  have hnewBranch : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨0 :: stack, M,
        10000 + gasStorageSet + 20 + 2132 + (gVerylow + gHigh)⟩)
        (Func.stop <?> checkedBody)
        (fun ex => ∃ post, ex = .ok post) := by
    rcases hsuffix with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_branch_zero rfl (by
      simp only [Devm.stack_setMach, List.length_cons]
      omega)
    · rfl
    · exact hw
  have hnewTest : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 22⟩)
        freshBody
        (fun ex => ∃ post, ex = .ok post) := by
    have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
      have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
      omega
    have hnewMemory :
        (M.read (newPauserWord * 32).toNat 32).2 = M := by
      rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
    apply Func.execSat_segment
      (devm' := d.setMach ⟨0 :: stack, M,
        10000 + gasStorageSet + 20 + 2132 + (gVerylow + gHigh)⟩)
      (f' := Func.stop <?> checkedBody)
    · intro ex htail
      func_run (3) [3]
      all_goals try {
        simp only [Devm.stack_setMach]
        omega }
      all_goals try omega
      case h_cost =>
        rw [Devm.extCost_zero_of_le halign hnewCovered]
        norm_num [gVerylow]
      case h_f =>
        rw [hnew, hnewMemory]
        norm_num [gVerylow, gHigh]
        exact htail
    · exact hnewBranch
  have hpreviousBranch : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨1 :: stack, M,
        10000 + gasStorageSet + 20 + 2132 + 36⟩)
        (freshBody <?> oldBody)
        (fun ex => ∃ post, ex = .ok post) := by
    rcases hnewTest with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_branch_succ
        (w := 1)
        (G := 10000 + gasStorageSet + 20 + 2132 + 22)
        (by decide) rfl (by
      simp only [Devm.stack_setMach, List.length_cons]
      omega)
    · norm_num [gVerylow, gHigh, gJumpdest]
    · exact hw
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hpreviousMemory :
      (M.read (previousPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hpreviousCovered)]
  apply Func.execSat_segment
    (devm' := d.setMach ⟨1 :: stack, M,
      10000 + gasStorageSet + 20 + 2132 + 36⟩)
    (f' := freshBody <?> oldBody)
  · intro ex htail
    simp only [registerAfterSet]
    func_run (3) [3]
    all_goals try {
      simp only [Devm.stack_setMach]
      omega }
    all_goals try omega
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hpreviousCovered]
      norm_num [gVerylow]
    case h_f =>
      rw [hprevious, hpreviousMemory]
      norm_num [gVerylow, gHigh, gJumpdest]
      exact htail
  · exact hpreviousBranch

private theorem finishSetPauserContinuationExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes} {stack : Stack}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (hprevious :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hcontinuation :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (hinterval : d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry : (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hroom : stack.length < 1020)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 35⟩)
        (loadWord continuationWord +++ iszero :::
          ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot)))
      (fun ex => ∃ post, ex = .ok post) := by
  have hregister := registerAfterSetExecSatOf
    (e := e) (d := d) (stack := stack) hwf hreads hprevious hnew hsize halign
    htime hinterval hintervalCold hexpiry hexpiryOrig hwarmExpiry
    hroom hstatic
  have hlookup :
      ((runtime officialParams).main ::
        (runtime officialParams).aux)[registerAfterSetSlot]? =
          some registerAfterSet := by
    simp [runtime, aux, registerAfterSetSlot]
  have hcall : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 +
          (gVerylow + gMid + gJumpdest)⟩)
        (.call registerAfterSetSlot)
      (fun ex => ∃ post, ex = .ok post) := by
    rcases hregister with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_call' hlookup (by
      simp only [Devm.stack_setMach]
      omega)
    · rfl
    · exact hw
  have hbranch : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨1 :: stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 26⟩)
        ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot))
      (fun ex => ∃ post, ex = .ok post) := by
    rcases hcall with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_branch_succ
        (w := 1)
        (G := 10000 + gasStorageSet + 20 + 2132 + 45 + 12)
        (by decide) rfl (by
          simp only [Devm.stack_setMach, List.length_cons]
          omega)
    · norm_num [gVerylow, gMid, gHigh, gJumpdest]
    · exact hw
  have hcontinuationCovered :
      (continuationWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (continuationWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hcontinuationMemory :
      (M.read (continuationWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hcontinuationCovered)]
  apply Func.execSat_segment
    (devm' := d.setMach ⟨1 :: stack, M,
      10000 + gasStorageSet + 20 + 2132 + 45 + 26⟩)
    (f' := (.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot))
  · intro ex htail
    func_run (3) [3]
    all_goals try {
      simp only [Devm.stack_setMach]
      omega }
    all_goals try omega
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hcontinuationCovered]
      norm_num [gVerylow]
    case h_f =>
      rw [hcontinuation, hcontinuationMemory]
      norm_num
      exact htail
  · exact hbranch

private theorem finishSetPauserExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes} {stack : Stack}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (htarget : (M.read (targetWord * 32).toNat 32).1.toB256 = 7)
    (hprevious :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hcontinuation :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (hinterval : d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry : (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935⟩)
        finishSetPauser
      (fun ex => ∃ post, ex = .ok post) := by
  let eventLog : Log :=
    { address := e.currentTarget
      topics := [pauserSetEvent, 7, 0, 9]
      data := [] }
  let d' := d.addLog eventLog
  have hinterval' :
      d'.getStorVal e.currentTarget heartbeatIntervalSlot = 0 := by
    change d.getStorVal e.currentTarget heartbeatIntervalSlot = 0
    exact hinterval
  have hintervalCold' :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d'.accessedStorageKeys := by
    change (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys
    exact hintervalCold
  have hexpiry' : d'.getStorVal e.currentTarget (expirySlot 9) = 0 := by
    change d.getStorVal e.currentTarget (expirySlot 9) = 0
    exact hexpiry
  have hwarmExpiry' :
      (e.currentTarget, expirySlot 9) ∈ d'.accessedStorageKeys := by
    change (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys
    exact hwarmExpiry
  have hsuffix := finishSetPauserContinuationExecSatOf
    (e := e) (d := d') (stack := stack) hwf hreads hprevious hnew hcontinuation
    hsize halign htime hinterval' hintervalCold' hexpiry'
    hexpiryOrig hwarmExpiry' (by omega) hstatic
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have htargetMemory :
      (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign htargetCovered)]
  have hpreviousMemory :
      (M.read (previousPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hpreviousCovered)]
  have hnewMemory :
      (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have hreadZero : M.read 0 0 = ([], M) := by
    simp [Mem.read, Mem.extend, memExtSize]
    rfl
  have hextNew (base : Devm) (S : List B256) (G : Nat) :
      (base.setMach ⟨S, M, G⟩).extCost
          [⟨(newPauserWord * 32).toNat, 32⟩] = 0 :=
    Devm.extCost_zero_of_le halign hnewCovered
  have hextPrevious (base : Devm) (S : List B256) (G : Nat) :
      (base.setMach
        ⟨S, (M.read (newPauserWord * 32).toNat 32).2, G⟩).extCost
          [⟨(previousPauserWord * 32).toNat, 32⟩] = 0 := by
    rw [hnewMemory]
    exact Devm.extCost_zero_of_le halign hpreviousCovered
  have hextTarget (base : Devm) (S : List B256) (G : Nat) :
      (base.setMach
        ⟨S, ((M.read (newPauserWord * 32).toNat 32).2.read
          (previousPauserWord * 32).toNat 32).2, G⟩).extCost
          [⟨(targetWord * 32).toNat, 32⟩] = 0 := by
    rw [hnewMemory, hpreviousMemory]
    exact Devm.extCost_zero_of_le halign htargetCovered
  have hextZero (base : Devm) (S : List B256) (G : Nat) :
      (base.setMach
        ⟨S, (((M.read (newPauserWord * 32).toNat 32).2.read
          (previousPauserWord * 32).toNat 32).2.read
            (targetWord * 32).toNat 32).2, G⟩).extCost
          [⟨((0 : B256) * 32).toNat, ((0 : B256) * 32).toNat⟩] = 0 := by
    rw [hnewMemory, hpreviousMemory, htargetMemory]
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_zero_of_le halign (by omega)
  apply Func.execSat_segment
    (devm' := d'.setMach ⟨stack, M,
      10000 + gasStorageSet + 20 + 2132 + 45 + 35⟩)
    (f' := loadWord continuationWord +++ iszero :::
      ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot)))
  · intro ex htail
    simp only [finishSetPauser]
    func_run (10) [3, 3, 3, 1875]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons]
      omega }
    all_goals try omega
    all_goals try {
      rw [hextNew]
      norm_num [gVerylow] }
    all_goals try {
      rw [hextPrevious]
      norm_num [gVerylow] }
    all_goals try {
      rw [hextTarget]
      norm_num [gVerylow] }
    case h_cost =>
      rw [hextZero]
      rw [show ((0 : B256) * 32).toNat = 0 by decide]
      norm_num [gLog, gLogdata, gLogtopic]
    case h_f =>
      rw [hnewMemory, hpreviousMemory, htargetMemory]
      rw [hnew, hprevious, htarget]
      rw [show ((0 : B256) * 32).toNat = 0 by decide, hreadZero]
      change Func.ExecWitness _ _
        (d'.setMach ⟨stack, M,
          10000 + gasStorageSet + 20 + 2132 + 45 + 35⟩) _ ex
      exact htail
  · exact hsuffix

private theorem newCountUpdateTailExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes} {stack : Stack}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (htarget : (M.read (targetWord * 32).toNat 32).1.toB256 = 7)
    (hprevious :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hcontinuation :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (hcount : d.getStorVal e.currentTarget (countSlot 9) = 0)
    (hcountOrig : getOrigStorVal e e.currentTarget (countSlot 9) = 0)
    (hcountCold :
      (e.currentTarget, countSlot 9) ∉ d.accessedStorageKeys)
    (hinterval : d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry : (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨countSlot 9 :: stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12 +
          gasStorageSet + 2118⟩)
        (sload ::: pushB256 1 ::: add ::: newCountKey +++
          sstore ::: .call finishSetPauserSlot)
      (fun ex => ∃ post, ex = .ok post) := by
  let d₁ := addAccessedStorageKey d e.currentTarget (countSlot 9)
  let refund := sstoreNewRefundCounter 1
    (getOrigStorVal e e.currentTarget (countSlot 9))
    (d₁.getStorVal e.currentTarget (countSlot 9)) d₁.refundCounter
  let d₂ := (d₁.withRefundCounter refund).setStorVal
    e.currentTarget (countSlot 9) 1
  have hcount₁ : d₁.getStorVal e.currentTarget (countSlot 9) = 0 := by
    change d.getStorVal e.currentTarget (countSlot 9) = 0
    exact hcount
  have hwarmCount₁ :
      (e.currentTarget, countSlot 9) ∈ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simp [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys]
  have hother₂ : ∀ (a : Adr) (k : B256),
      (a, k) ≠ (e.currentTarget, countSlot 9) →
      d₂.getStorVal a k = d₁.getStorVal a k := by
    intro a k hne
    by_cases ha : e.currentTarget = a
    · subst a
      have hk : countSlot 9 ≠ k := fun h => hne (by rw [h])
      show (Devm.getStor _ e.currentTarget).get k = _
      rw [show d₂ = (d₁.withRefundCounter refund).setStorVal
          e.currentTarget (countSlot 9) 1 by rfl,
        setStorVal_getStor_self, Stor.get_set_ne _ hk]
      rfl
    · show (Devm.getStor d₂ a).get k = _
      have hoff : Devm.getStor d₂ a = Devm.getStor d₁ a := by
        simp only [d₂, Devm.getStor, Devm.getAcct, Devm.setStorVal,
          Devm.withRefundCounter, Devm.withState, Devm.setWorld,
          State.setStorVal, Devm.state]
        rw [State.get_set_ne _ ha]
        rfl
      rw [hoff]
      change (Devm.getStor d₁ a).get k = (Devm.getStor d₁ a).get k
      rfl
  have hinterval₂ :
      d₂.getStorVal e.currentTarget heartbeatIntervalSlot = 0 := by
    rw [hother₂ e.currentTarget heartbeatIntervalSlot (by
      intro h
      have hk : heartbeatIntervalSlot = countSlot 9 := congrArg Prod.snd h
      exact (by decide : heartbeatIntervalSlot ≠ countSlot 9) hk)]
    change d.getStorVal e.currentTarget heartbeatIntervalSlot = 0
    exact hinterval
  have hexpiry₂ : d₂.getStorVal e.currentTarget (expirySlot 9) = 0 := by
    rw [hother₂ e.currentTarget (expirySlot 9) (by
      intro h
      have hk : expirySlot 9 = countSlot 9 := congrArg Prod.snd h
      exact (by decide : expirySlot 9 ≠ countSlot 9) hk)]
    change d.getStorVal e.currentTarget (expirySlot 9) = 0
    exact hexpiry
  have hintervalCold₂ :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d₂.accessedStorageKeys := by
    have haccess : d₂.accessedStorageKeys = d₁.accessedStorageKeys := rfl
    rw [haccess]
    rcases d with ⟨mach, mt, world⟩
    simpa [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using And.intro
        (by decide : countSlot 9 ≠ heartbeatIntervalSlot) hintervalCold
  have hwarmExpiry₂ :
      (e.currentTarget, expirySlot 9) ∈ d₂.accessedStorageKeys := by
    have haccess : d₂.accessedStorageKeys = d₁.accessedStorageKeys := rfl
    rw [haccess]
    rcases d with ⟨mach, mt, world⟩
    simpa [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using
      (Or.inr hwarmExpiry : countSlot 9 = expirySlot 9 ∨
        (e.currentTarget, expirySlot 9) ∈ mt.accessedStorageKeys)
  have hfinish := finishSetPauserExecSatOf
    (e := e) (d := d₂) (stack := stack) hwf hreads htarget hprevious hnew hcontinuation
    hsize halign htime hinterval₂ hintervalCold₂ hexpiry₂
    hexpiryOrig hwarmExpiry₂ hroom hstatic
  have hlookup :
      ((runtime officialParams).main ::
        (runtime officialParams).aux)[finishSetPauserSlot]? =
          some finishSetPauser := by
    simp [runtime, aux, finishSetPauserSlot]
  have hcall : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d₂.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12⟩)
        (.call finishSetPauserSlot)
      (fun ex => ∃ post, ex = .ok post) := by
    rcases hfinish with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_call' hlookup (by
      simp only [Devm.stack_setMach]
      omega)
    · rfl
    · exact hw
  have hstore : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d₁.setMach ⟨countSlot 9 :: 1 :: stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12 +
          gasStorageSet⟩)
        (sstore ::: .call finishSetPauserSlot)
      (fun ex => ∃ post, ex = .ok post) := by
    apply Func.execSat_next
    · apply Ninst.runCompiled_sstore_warm
        (c := gasStorageSet)
        (G := 10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12)
      · rfl
      · exact hwarmCount₁
      · norm_num [gCallStipend, gasStorageSet]
      · exact hstatic
      · change sstoreValueCost
          (getOrigStorVal e e.currentTarget (countSlot 9))
          (d₁.getStorVal e.currentTarget (countSlot 9)) 1 = gasStorageSet
        simp [hcountOrig, hcount₁, sstoreValueCost]
        intro h
        exact False.elim ((by decide : (0 : B256) ≠ 1) h)
      · rfl
      · rfl
    · exact hcall
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hnewMemory :
      (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have haddMach (S : List B256) (G : Nat) :
      addAccessedStorageKey (d.setMach ⟨S, M, G⟩)
          e.currentTarget (countSlot 9) =
        d₁.setMach ⟨S, M, G⟩ := rfl
  apply Func.execSat_segment
    (devm' := d₁.setMach ⟨countSlot 9 :: 1 :: stack, M,
      10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12 +
        gasStorageSet⟩)
    (f' := sstore ::: .call finishSetPauserSlot)
  · intro ex htail
    func_run (7) [1, 3, countSlot 9]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons]
      omega }
    all_goals try omega
    all_goals try {
      rw [Devm.extCost_zero_of_le halign hnewCovered]
      norm_num [gVerylow] }
    all_goals try {
      simpa [countSlot, slot] using
        congrArg (fun x : B256 => (regionWord countRegion).or x) hnew }
    all_goals try {
      change 1 + d.getStorVal e.currentTarget (countSlot 9) = 1
      rw [hcount]
      rfl }
    case h_f =>
      rw [hnewMemory, haddMach]
      norm_num
      change Func.ExecWitness _ _
        (d₁.setMach ⟨countSlot 9 :: 1 :: stack, M,
          10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12 +
            gasStorageSet⟩) _ ex
      exact htail
  · exact hstore

private theorem afterOldPauserExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes} {stack : Stack}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (htarget : (M.read (targetWord * 32).toNat 32).1.toB256 = 7)
    (hprevious :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hcontinuation :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (hcount : d.getStorVal e.currentTarget (countSlot 9) = 0)
    (hcountOrig : getOrigStorVal e e.currentTarget (countSlot 9) = 0)
    (hcountCold :
      (e.currentTarget, countSlot 9) ∉ d.accessedStorageKeys)
    (hinterval : d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry : (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164⟩)
        afterOldPauser
      (fun ex => ∃ post, ex = .ok post) := by
  let countTail : Func :=
    sload ::: pushB256 1 ::: add ::: newCountKey +++
      sstore ::: .call finishSetPauserSlot
  let countBody : Func := newCountKey +++ countTail
  have htail := newCountUpdateTailExecSatOf
    (e := e) (d := d) (stack := stack) hwf hreads htarget hprevious hnew hcontinuation
    hsize halign htime hcount hcountOrig hcountCold hinterval hintervalCold
    hexpiry hexpiryOrig hwarmExpiry hroom hstatic
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hnewMemory :
      (M.read (newPauserWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hnewCovered)]
  have hbody : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12 +
          gasStorageSet + 2130⟩)
        countBody
      (fun ex => ∃ post, ex = .ok post) := by
    apply Func.execSat_segment
      (devm' := d.setMach ⟨countSlot 9 :: stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12 +
          gasStorageSet + 2118⟩)
      (f' := countTail)
    · intro ex hnext
      dsimp only [countBody, countTail]
      func_run (4) [3, countSlot 9]
      all_goals try {
        simp only [Devm.stack_setMach, List.length_cons]
        omega }
      all_goals try omega
      all_goals try {
        rw [Devm.extCost_zero_of_le halign hnewCovered]
        norm_num [gVerylow] }
      all_goals try {
        simpa [countSlot, slot] using
          congrArg (fun x : B256 => (regionWord countRegion).or x) hnew }
      case h_f =>
        rw [hnewMemory]
        exact hnext
    · simpa only [countTail] using htail
  have hbranch : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨0 :: stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12 +
          gasStorageSet + 2143⟩)
        ((.call removeTargetSlot) <?> countBody)
      (fun ex => ∃ post, ex = .ok post) := by
    rcases hbody with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_branch_zero rfl (by
      simp only [Devm.stack_setMach, List.length_cons]
      omega)
    · rfl
    · exact hw
  apply Func.execSat_segment
    (devm' := d.setMach ⟨0 :: stack, M,
      10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12 +
        gasStorageSet + 2143⟩)
    (f' := (.call removeTargetSlot) <?> countBody)
  · intro ex hnext
    simp only [afterOldPauser]
    func_run (3) [3]
    all_goals try {
      simp only [Devm.stack_setMach]
      omega }
    all_goals try omega
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign hnewCovered]
      norm_num [gVerylow]
    case h_f =>
      rw [hnew, hnewMemory]
      norm_num
      change Func.ExecWitness _ _
        (d.setMach ⟨0 :: stack, M,
          10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 12 +
            gasStorageSet + 2143⟩)
        ((.call removeTargetSlot) <?> countBody) ex
      exact hnext
  · exact hbranch



private def successfulWritePost (e : Sevm) (d : Devm)
    (key value : B256) : Devm :=
  (d.withRefundCounter (sstoreNewRefundCounter value
    (getOrigStorVal e e.currentTarget key)
    (d.getStorVal e.currentTarget key) d.refundCounter)).setStorVal
      e.currentTarget key value

private theorem successfulWritePost_setMach
    (e : Sevm) (d : Devm) (mach : Mach) (key value : B256) :
    successfulWritePost e (d.setMach mach) key value =
      (successfulWritePost e d key value).setMach mach := by
  rfl

private structure SuccessfulWriteCertificate
    (e : Sevm) (d : Devm) (key value : B256) where
  post : Devm
  post_eq : post = successfulWritePost e d key value
  self : post.getStorVal e.currentTarget key = value
  other : ∀ a k, (a, k) ≠ (e.currentTarget, key) →
    post.getStorVal a k = d.getStorVal a k
  accessedStorageKeys : post.accessedStorageKeys = d.accessedStorageKeys
  accessedAddresses : post.accessedAddresses = d.accessedAddresses
  memory : post.memory = d.memory
  balance : ∀ a, post.getBal a = d.getBal a
  code : ∀ a, post.getCode a = d.getCode a
  logs : post.logs = d.logs
  output : post.output = d.output
  error : post.error = d.error
  accountsToDelete : post.accountsToDelete = d.accountsToDelete
  refundCounter : post.refundCounter = sstoreNewRefundCounter value
    (getOrigStorVal e e.currentTarget key)
    (d.getStorVal e.currentTarget key) d.refundCounter

private def successfulWriteCertificateOf
    (e : Sevm) (d : Devm) (key value : B256) :
    SuccessfulWriteCertificate e d key value := by
  let post := successfulWritePost e d key value
  have hself : post.getStorVal e.currentTarget key = value := by
    show (Devm.getStor _ e.currentTarget).get key = value
    rw [show post =
        (d.withRefundCounter (sstoreNewRefundCounter value
          (getOrigStorVal e e.currentTarget key)
          (d.getStorVal e.currentTarget key)
          d.refundCounter)).setStorVal e.currentTarget key value by rfl,
      setStorVal_getStor_self, Stor.get_set_self]
  have hother : ∀ a k, (a, k) ≠ (e.currentTarget, key) →
      post.getStorVal a k = d.getStorVal a k := by
    intro a k hne
    by_cases ha : e.currentTarget = a
    · subst a
      have hk : key ≠ k := fun h => hne (by rw [h])
      show (Devm.getStor _ e.currentTarget).get k = _
      rw [show post =
          (d.withRefundCounter (sstoreNewRefundCounter value
            (getOrigStorVal e e.currentTarget key)
            (d.getStorVal e.currentTarget key)
            d.refundCounter)).setStorVal e.currentTarget key value by rfl,
        setStorVal_getStor_self, Stor.get_set_ne _ hk]
      rfl
    · show (Devm.getStor post a).get k = _
      have hoff : Devm.getStor post a = Devm.getStor d a := by
        simp only [post, successfulWritePost, Devm.getStor, Devm.getAcct,
          Devm.setStorVal, Devm.withRefundCounter, Devm.withState,
          Devm.setWorld, State.setStorVal, Devm.state]
        rw [State.get_set_ne _ ha]
        rfl
      rw [hoff]
      rfl
  refine {
    post := post
    post_eq := rfl
    self := hself
    other := hother
    accessedStorageKeys := rfl
    accessedAddresses := rfl
    memory := rfl
    balance := ?_
    code := ?_
    logs := rfl
    output := rfl
    error := rfl
    accountsToDelete := rfl
    refundCounter := rfl }
  · intro a
    have hbc := State.setStorVal_balCodeEq d.state e.currentTarget key value
    exact (congrArg Prod.fst (congrFun hbc a)).symm
  · intro a
    have hbc := State.setStorVal_balCodeEq d.state e.currentTarget key value
    exact (congrArg Prod.snd (congrFun hbc a)).symm

private theorem execSat_successfulWrite_step
    {fs : List Func} {e : Sevm} {d : Devm} {key value : B256}
    {stack : List B256} {M : Mem} {G : Nat} {rest : Func}
    {P : Execution → Prop}
    (cert : SuccessfulWriteCertificate e d key value)
    (hcurrent : d.getStorVal e.currentTarget key = 0)
    (horiginal : getOrigStorVal e e.currentTarget key = 0)
    (hvalue : value ≠ 0)
    (hwarm : (e.currentTarget, key) ∈ d.accessedStorageKeys)
    (hstatic : e.isStatic = false)
    (hnext : Func.ExecSat fs e
      (cert.post.setMach ⟨stack, M, G⟩) rest P) :
    Func.ExecSat fs e
      (d.setMach ⟨key :: value :: stack, M, G + gasStorageSet⟩)
      (sstore ::: rest) P := by
  apply Func.execSat_next
  · apply Ninst.runCompiled_sstore_warm (c := gasStorageSet) (G := G)
    · rfl
    · exact hwarm
    · norm_num [gCallStipend, gasStorageSet]
    · exact hstatic
    · change sstoreValueCost
        (getOrigStorVal e e.currentTarget key)
        (d.getStorVal e.currentTarget key) value = gasStorageSet
      simp [horiginal, hcurrent, sstoreValueCost]
      intro h
      exact False.elim (hvalue h.symm)
    · rfl
    · rfl
  · change Func.ExecSat fs e
      ((successfulWritePost e
        (d.setMach ⟨key :: value :: stack, M, G + gasStorageSet⟩)
        key value).setMach ⟨stack, M, G⟩) rest P
    rw [successfulWritePost_setMach, ← cert.post_eq]
    exact hnext

private theorem execSat_loadWord_prepend
    {fs : List Func} {e : Sevm} {d : Devm} {M : Mem}
    {word loaded : B256} {stack : List B256}
    {offsetCost G Gpre : Nat} {rest : Func}
    {P : Execution → Prop}
    (hcovered : (word * 32).toNat + 32 ≤ M.size)
    (halign : M.size % 32 = 0)
    (hread : (M.read (word * 32).toNat 32).1.toB256 = loaded)
    (hoffsetCost : pushCost (word * 32).toBytes.sig = offsetCost)
    (hroom : stack.length < 1024)
    (hgas : Gpre = G + gVerylow + offsetCost)
    (hnext : Func.ExecSat fs e
      (d.setMach ⟨loaded :: stack, M, G⟩) rest P) :
    Func.ExecSat fs e (d.setMach ⟨stack, M, Gpre⟩)
      (loadWord word +++ rest) P := by
  subst Gpre
  have hmemory : (M.read (word * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hcovered)]
  have hmload : Func.ExecSat fs e
      (d.setMach ⟨word * 32 :: stack, M, G + gVerylow⟩)
      (.reg .mload ::: rest) P := by
    apply Func.execSat_next
    · apply Ninst.runCompiled_mload_of (c := gVerylow) (G := G)
      · rfl
      · rw [Devm.extCost_zero_of_le halign hcovered]
        norm_num [gVerylow]
      · exact hread
      · exact hmemory
      · rfl
      · exact hroom
    · exact hnext
  apply Func.execSat_next
  · apply Ninst.runCompiled_pushB256 hoffsetCost rfl
    simpa only [Devm.stack_setMach] using hroom
  · exact hmload

private theorem execSat_tagTop_prepend
    {fs : List Func} {e : Sevm} {d : Devm} {M : Mem}
    {region : Nat} {top tagged : B256} {stack : List B256}
    {tagCost G Gpre : Nat} {rest : Func}
    {P : Execution → Prop}
    (htag : slot region top = tagged)
    (htagCost : pushCost (regionWord region).toBytes.sig = tagCost)
    (hroom : stack.length < 1023)
    (hgas : Gpre = G + gVerylow + tagCost)
    (hnext : Func.ExecSat fs e
      (d.setMach ⟨tagged :: stack, M, G⟩) rest P) :
    Func.ExecSat fs e (d.setMach ⟨top :: stack, M, Gpre⟩)
      (tagTop region +++ rest) P := by
  subst tagged
  subst Gpre
  have hor : Func.ExecSat fs e
      (d.setMach ⟨regionWord region :: top :: stack, M,
        G + gVerylow⟩)
      (.reg .or ::: rest) P := by
    apply Func.execSat_next
    · exact Ninst.runCompiled_binary (by rintro ⟨⟩) (by rfl) rfl rfl
        (by rfl) (by omega)
    · exact hnext
  apply Func.execSat_next
  · apply Ninst.runCompiled_pushB256 htagCost rfl
    simp only [Devm.stack_setMach, List.length_cons]
    omega
  · exact hor

private theorem execSat_loadWord_pushB256_prepend
    {fs : List Func} {e : Sevm} {d : Devm} {M : Mem}
    {word loaded value : B256} {stack : List B256}
    {offsetCost valueCost G Gpre : Nat} {rest : Func}
    {P : Execution → Prop}
    (hcovered : (word * 32).toNat + 32 ≤ M.size)
    (halign : M.size % 32 = 0)
    (hread : (M.read (word * 32).toNat 32).1.toB256 = loaded)
    (hoffsetCost : pushCost (word * 32).toBytes.sig = offsetCost)
    (hvalueCost : pushCost value.toBytes.sig = valueCost)
    (hroom : stack.length < 1023)
    (hgas : Gpre = G + valueCost + gVerylow + offsetCost)
    (hnext : Func.ExecSat fs e
      (d.setMach ⟨value :: loaded :: stack, M, G⟩) rest P) :
    Func.ExecSat fs e (d.setMach ⟨stack, M, Gpre⟩)
      (loadWord word +++ pushB256 value ::: rest) P := by
  subst Gpre
  have hmemory : (M.read (word * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hcovered)]
  have hpushValue : Func.ExecSat fs e
      (d.setMach ⟨loaded :: stack, M, G + valueCost⟩)
      (pushB256 value ::: rest) P := by
    apply Func.execSat_next
    · apply Ninst.runCompiled_pushB256 hvalueCost rfl
      simp only [Devm.stack_setMach, List.length_cons]
      omega
    · exact hnext
  have hmload : Func.ExecSat fs e
      (d.setMach ⟨word * 32 :: stack, M,
        G + valueCost + gVerylow⟩)
      (.reg .mload ::: pushB256 value ::: rest) P := by
    apply Func.execSat_next
    · apply Ninst.runCompiled_mload_of
        (c := gVerylow) (G := G + valueCost)
      · rfl
      · rw [Devm.extCost_zero_of_le halign hcovered]
        norm_num [gVerylow]
      · exact hread
      · exact hmemory
      · rfl
      · omega
    · exact hpushValue
  apply Func.execSat_next
  · apply Ninst.runCompiled_pushB256 hoffsetCost rfl
    simp only [Devm.stack_setMach]
    omega
  · exact hmload

private theorem execSat_loadWord_targetIndexKey_prepend
    {fs : List Func} {e : Sevm} {d : Devm} {M : Mem}
    {word loaded target tagged : B256} {stack : List B256}
    {wordOffsetCost targetOffsetCost tagCost G Gpre : Nat}
    {rest : Func} {P : Execution → Prop}
    (hwordCovered : (word * 32).toNat + 32 ≤ M.size)
    (htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size)
    (halign : M.size % 32 = 0)
    (hread : (M.read (word * 32).toNat 32).1.toB256 = loaded)
    (htarget :
      (M.read (targetWord * 32).toNat 32).1.toB256 = target)
    (htag : slot indexRegion target = tagged)
    (hwordOffsetCost :
      pushCost (word * 32).toBytes.sig = wordOffsetCost)
    (htargetOffsetCost :
      pushCost (targetWord * 32).toBytes.sig = targetOffsetCost)
    (htagCost : pushCost (regionWord indexRegion).toBytes.sig = tagCost)
    (hroom : stack.length < 1022)
    (hgas : Gpre =
      G + gVerylow + tagCost + gVerylow + targetOffsetCost +
        gVerylow + wordOffsetCost)
    (hnext : Func.ExecSat fs e
      (d.setMach ⟨tagged :: loaded :: stack, M, G⟩) rest P) :
    Func.ExecSat fs e (d.setMach ⟨stack, M, Gpre⟩)
      (loadWord word +++ targetIndexKey +++ rest) P := by
  subst tagged
  subst Gpre
  have htargetMemory :
      (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign htargetCovered)]
  have hor : Func.ExecSat fs e
      (d.setMach ⟨regionWord indexRegion :: target :: loaded :: stack, M,
        G + gVerylow⟩)
      (.reg .or ::: rest) P := by
    apply Func.execSat_next
    · exact Ninst.runCompiled_binary (by rintro ⟨⟩) (by rfl) rfl rfl
        (by rfl) (by
          simp only [List.length_cons]
          omega)
    · exact hnext
  have htagPush : Func.ExecSat fs e
      (d.setMach ⟨target :: loaded :: stack, M,
        G + gVerylow + tagCost⟩)
      (pushB256 (regionWord indexRegion) ::: .reg .or ::: rest) P := by
    apply Func.execSat_next
    · apply Ninst.runCompiled_pushB256 htagCost rfl
      simp only [Devm.stack_setMach, List.length_cons]
      omega
    · exact hor
  have htargetLoad : Func.ExecSat fs e
      (d.setMach ⟨targetWord * 32 :: loaded :: stack, M,
        G + gVerylow + tagCost + gVerylow⟩)
      (.reg .mload ::: tagTop indexRegion +++ rest) P := by
    apply Func.execSat_next
    · apply Ninst.runCompiled_mload_of
        (c := gVerylow) (G := G + gVerylow + tagCost)
      · rfl
      · rw [Devm.extCost_zero_of_le halign htargetCovered]
        norm_num [gVerylow]
      · exact htarget
      · exact htargetMemory
      · rfl
      · simp only [List.length_cons]
        omega
    · exact htagPush
  exact execSat_loadWord_pushB256_prepend
    hwordCovered halign hread hwordOffsetCost htargetOffsetCost
    (by omega) rfl htargetLoad

private theorem execSat_sload_cold_prepend
    {fs : List Func} {e : Sevm} {d : Devm} {M : Mem}
    {key value : B256} {stack : List B256} {G Gpre : Nat}
    {rest : Func} {P : Execution → Prop}
    (hvalue : d.getStorVal e.currentTarget key = value)
    (hcold : (e.currentTarget, key) ∉ d.accessedStorageKeys)
    (hroom : stack.length < 1024)
    (hgas : Gpre = G + gasColdSload)
    (hnext : Func.ExecSat fs e
      ((addAccessedStorageKey d e.currentTarget key).setMach
        ⟨value :: stack, M, G⟩) rest P) :
    Func.ExecSat fs e (d.setMach ⟨key :: stack, M, Gpre⟩)
      (.reg .sload ::: rest) P := by
  subst Gpre
  have haddMach :
      addAccessedStorageKey
          (d.setMach ⟨key :: stack, M, G + gasColdSload⟩)
          e.currentTarget key =
        (addAccessedStorageKey d e.currentTarget key).setMach
          ⟨key :: stack, M, G + gasColdSload⟩ := rfl
  apply Func.execSat_next
  · apply Ninst.runCompiled_sload_cold
    · rfl
    · exact hcold
    · exact hvalue
    · rfl
    · exact hroom
  · rw [haddMach]
    exact hnext

private theorem execSat_mstoreAt_word_prepend
    {fs : List Func} {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes}
    {word value : B256} {stack : List B256}
    {offsetCost G Gpre : Nat} {rest : Func} {P : Execution → Prop}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (hcovered : (word * 32).toNat + 32 ≤ M.size)
    (halign : M.size % 32 = 0)
    (hoffsetCost : pushCost (word * 32).toBytes.sig = offsetCost)
    (hroom : stack.length < 1023)
    (hgas : Gpre = G + gVerylow + offsetCost)
    (hnext :
      Mem.Wf (M.write (word * 32).toNat value.toBytes) →
      Mem.Reads (M.write (word * 32).toNat value.toBytes)
        (Bytes.writeAt bs (word * 32).toNat value.toBytes) →
      Func.ExecSat fs e
        (d.setMach ⟨stack,
          M.write (word * 32).toNat value.toBytes, G⟩) rest P) :
    Func.ExecSat fs e (d.setMach ⟨value :: stack, M, Gpre⟩)
      (mstoreAt word +++ rest) P := by
  subst Gpre
  have hwf' : Mem.Wf (M.write (word * 32).toNat value.toBytes) :=
    Mem.Wf.write hwf (word * 32).toNat value.toBytes
  have hreads' :
      Mem.Reads (M.write (word * 32).toNat value.toBytes)
        (Bytes.writeAt bs (word * 32).toNat value.toBytes) :=
    Mem.Reads.write hwf hreads (word * 32).toNat value.toBytes
  have hmstore : Func.ExecSat fs e
      (d.setMach ⟨word * 32 :: value :: stack, M,
        G + gVerylow⟩)
      (.reg .mstore ::: rest) P := by
    apply Func.execSat_next
    · apply Ninst.runCompiled_mstore_of (e := 0) (G := G)
      · rfl
      · rw [Devm.extCost_zero_of_le halign hcovered]
      · norm_num [gVerylow]
      · rfl
    · exact hnext hwf' hreads'
  apply Func.execSat_next
  · apply Ninst.runCompiled_pushB256 hoffsetCost rfl
    simp only [Devm.stack_setMach, List.length_cons]
    omega
  · exact hmstore

private structure AppendArrayWriteCertificate (e : Sevm) (d : Devm) where
  write : SuccessfulWriteCertificate e d (arrayEntrySlot 1) 7
  currentZero : d.getStorVal e.currentTarget (arrayEntrySlot 1) = 0
  originalZero :
    getOrigStorVal e e.currentTarget (arrayEntrySlot 1) = 0
  warm : (e.currentTarget, arrayEntrySlot 1) ∈ d.accessedStorageKeys

private def appendArrayWriteCertificateOf {e : Sevm} {d : Devm}
    (hcurrent : d.getStorVal e.currentTarget (arrayEntrySlot 1) = 0)
    (horiginal : getOrigStorVal e e.currentTarget (arrayEntrySlot 1) = 0)
    (hwarm : (e.currentTarget, arrayEntrySlot 1) ∈ d.accessedStorageKeys) :
    AppendArrayWriteCertificate e d :=
  { write := successfulWriteCertificateOf e d (arrayEntrySlot 1) 7
    currentZero := hcurrent
    originalZero := horiginal
    warm := hwarm }

private structure AppendIndexWriteCertificate
    (e : Sevm) (d : Devm) (array : AppendArrayWriteCertificate e d) where
  write : SuccessfulWriteCertificate e array.write.post (indexSlot 7) 1
  currentZero :
    array.write.post.getStorVal e.currentTarget (indexSlot 7) = 0
  originalZero : getOrigStorVal e e.currentTarget (indexSlot 7) = 0
  warm :
    (e.currentTarget, indexSlot 7) ∈ array.write.post.accessedStorageKeys

private def appendIndexWriteCertificateOf
    {e : Sevm} {d : Devm} (array : AppendArrayWriteCertificate e d)
    (hcurrent : d.getStorVal e.currentTarget (indexSlot 7) = 0)
    (horiginal : getOrigStorVal e e.currentTarget (indexSlot 7) = 0)
    (hwarm : (e.currentTarget, indexSlot 7) ∈ d.accessedStorageKeys) :
    AppendIndexWriteCertificate e d array := by
  have hne :
      (e.currentTarget, indexSlot 7) ≠
        (e.currentTarget, arrayEntrySlot 1) := by
    intro h
    exact (by decide : indexSlot 7 ≠ arrayEntrySlot 1)
      (congrArg Prod.snd h)
  have hzero :
      array.write.post.getStorVal e.currentTarget (indexSlot 7) = 0 := by
    rw [array.write.other _ _ hne]
    exact hcurrent
  have hwarm' :
      (e.currentTarget, indexSlot 7) ∈
        array.write.post.accessedStorageKeys := by
    rw [array.write.accessedStorageKeys]
    exact hwarm
  exact
    { write := successfulWriteCertificateOf e array.write.post
        (indexSlot 7) 1
      currentZero := hzero
      originalZero := horiginal
      warm := hwarm' }

private structure AppendLengthWriteCertificate
    (e : Sevm) (d : Devm) (array : AppendArrayWriteCertificate e d)
    (index : AppendIndexWriteCertificate e d array) where
  write :
    SuccessfulWriteCertificate e index.write.post arrayLengthSlot 1
  currentZero :
    index.write.post.getStorVal e.currentTarget arrayLengthSlot = 0
  originalZero : getOrigStorVal e e.currentTarget arrayLengthSlot = 0
  warm :
    (e.currentTarget, arrayLengthSlot) ∈
      index.write.post.accessedStorageKeys

private def appendLengthWriteCertificateOf
    {e : Sevm} {d : Devm} (array : AppendArrayWriteCertificate e d)
    (index : AppendIndexWriteCertificate e d array)
    (hcurrent : d.getStorVal e.currentTarget arrayLengthSlot = 0)
    (horiginal : getOrigStorVal e e.currentTarget arrayLengthSlot = 0)
    (hwarm : (e.currentTarget, arrayLengthSlot) ∈ d.accessedStorageKeys) :
    AppendLengthWriteCertificate e d array index := by
  have hneIndex :
      (e.currentTarget, arrayLengthSlot) ≠
        (e.currentTarget, indexSlot 7) := by
    intro h
    exact (by decide : arrayLengthSlot ≠ indexSlot 7)
      (congrArg Prod.snd h)
  have hneArray :
      (e.currentTarget, arrayLengthSlot) ≠
        (e.currentTarget, arrayEntrySlot 1) := by
    intro h
    exact (by decide : arrayLengthSlot ≠ arrayEntrySlot 1)
      (congrArg Prod.snd h)
  have hzero :
      index.write.post.getStorVal e.currentTarget arrayLengthSlot = 0 := by
    rw [index.write.other _ _ hneIndex]
    rw [array.write.other _ _ hneArray]
    exact hcurrent
  have hwarm' :
      (e.currentTarget, arrayLengthSlot) ∈
        index.write.post.accessedStorageKeys := by
    rw [index.write.accessedStorageKeys]
    rw [array.write.accessedStorageKeys]
    exact hwarm
  exact
    { write := successfulWriteCertificateOf e index.write.post
        arrayLengthSlot 1
      currentZero := hzero
      originalZero := horiginal
      warm := hwarm' }

private theorem appendTarget_write_suffixExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes} {stack : Stack}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (htarget : (M.read (targetWord * 32).toNat 32).1.toB256 = 7)
    (hlength : (M.read (arrayLengthWord * 32).toNat 32).1.toB256 = 1)
    (hprevious :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hcontinuation :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (harray : d.getStorVal e.currentTarget (arrayEntrySlot 1) = 0)
    (harrayOrig :
      getOrigStorVal e e.currentTarget (arrayEntrySlot 1) = 0)
    (hindex : d.getStorVal e.currentTarget (indexSlot 7) = 0)
    (hindexOrig : getOrigStorVal e e.currentTarget (indexSlot 7) = 0)
    (hlengthStor : d.getStorVal e.currentTarget arrayLengthSlot = 0)
    (hlengthOrig : getOrigStorVal e e.currentTarget arrayLengthSlot = 0)
    (hwarmArray :
      (e.currentTarget, arrayEntrySlot 1) ∈ d.accessedStorageKeys)
    (hwarmIndex :
      (e.currentTarget, indexSlot 7) ∈ d.accessedStorageKeys)
    (hwarmLength :
      (e.currentTarget, arrayLengthSlot) ∈ d.accessedStorageKeys)
    (hcount : d.getStorVal e.currentTarget (countSlot 9) = 0)
    (hcountOrig : getOrigStorVal e e.currentTarget (countSlot 9) = 0)
    (hcountCold :
      (e.currentTarget, countSlot 9) ∉ d.accessedStorageKeys)
    (hinterval :
      d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry :
      (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨arrayEntrySlot 1 :: 7 :: stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 +
          60039⟩)
      (sstore :::
        loadWord arrayLengthWord +++ targetIndexKey +++ sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
          sstore ::: .call afterOldPauserSlot)
      (fun ex => ∃ post, ex = .ok post) := by
  let array := appendArrayWriteCertificateOf harray harrayOrig hwarmArray
  let index := appendIndexWriteCertificateOf array hindex hindexOrig hwarmIndex
  let length := appendLengthWriteCertificateOf array index
    hlengthStor hlengthOrig hwarmLength
  have pairNe {k₁ k₂ : B256} (h : k₁ ≠ k₂) :
      (e.currentTarget, k₁) ≠ (e.currentTarget, k₂) := by
    intro hp
    exact h (congrArg Prod.snd hp)
  have hcountL :
      length.write.post.getStorVal e.currentTarget (countSlot 9) = 0 := by
    rw [length.write.other _ _ (pairNe (by decide)),
      index.write.other _ _ (pairNe (by decide)),
      array.write.other _ _ (pairNe (by decide))]
    exact hcount
  have hintervalL :
      length.write.post.getStorVal e.currentTarget heartbeatIntervalSlot = 0 := by
    rw [length.write.other _ _ (pairNe (by decide)),
      index.write.other _ _ (pairNe (by decide)),
      array.write.other _ _ (pairNe (by decide))]
    exact hinterval
  have hexpiryL :
      length.write.post.getStorVal e.currentTarget (expirySlot 9) = 0 := by
    rw [length.write.other _ _ (pairNe (by decide)),
      index.write.other _ _ (pairNe (by decide)),
      array.write.other _ _ (pairNe (by decide))]
    exact hexpiry
  have haccessL :
      length.write.post.accessedStorageKeys = d.accessedStorageKeys := by
    rw [length.write.accessedStorageKeys, index.write.accessedStorageKeys,
      array.write.accessedStorageKeys]
  have hafter := afterOldPauserExecSatOf
    (e := e) (d := length.write.post) (stack := stack) hwf hreads htarget hprevious hnew
    hcontinuation hsize halign htime hcountL hcountOrig
    (by simpa [haccessL] using hcountCold) hintervalL
    (by simpa [haccessL] using hintervalCold) hexpiryL hexpiryOrig
    (by simpa [haccessL] using hwarmExpiry) hroom hstatic
  have hlookup :
      ((runtime officialParams).main ::
        (runtime officialParams).aux)[afterOldPauserSlot]? =
          some afterOldPauser := by
    simp [runtime, aux, afterOldPauserSlot]
  have hcall : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (length.write.post.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 + 12⟩)
      (.call afterOldPauserSlot)
      (fun ex => ∃ post, ex = .ok post) := by
    rcases hafter with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_call' hlookup (by
      simp only [Devm.stack_setMach]
      omega)
    · rfl
    · exact hw
  have hlengthStore := execSat_successfulWrite_step length.write
    length.currentZero length.originalZero (by decide) length.warm hstatic hcall
  have hlengthCovered :
      (arrayLengthWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (arrayLengthWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hlengthOffsetCost :
      pushCost (arrayLengthWord * 32).toBytes.sig = 3 := by decide
  have hlengthSlotCost : pushCost arrayLengthSlot.toBytes.sig = 3 := by
    decide
  have hlengthSuffix : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (index.write.post.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 + 12 +
          gasStorageSet + 9⟩)
      (loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
        sstore ::: .call afterOldPauserSlot)
      (fun ex => ∃ post, ex = .ok post) := by
    exact execSat_loadWord_pushB256_prepend
      (offsetCost := 3) (valueCost := 3)
      hlengthCovered halign hlength hlengthOffsetCost hlengthSlotCost (by omega)
      (by norm_num [gVerylow]) hlengthStore
  have hindexStore := execSat_successfulWrite_step index.write
    index.currentZero index.originalZero (by decide) index.warm hstatic
    hlengthSuffix
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have htargetOffsetCost :
      pushCost (targetWord * 32).toBytes.sig = 3 := by decide
  have hindexTagCost :
      pushCost (regionWord indexRegion).toBytes.sig = 3 := by decide
  have hindexSuffix : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (array.write.post.setMach ⟨stack, M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 + 12 +
          gasStorageSet + 9 + gasStorageSet + 18⟩)
      (loadWord arrayLengthWord +++ targetIndexKey +++ sstore :::
        loadWord arrayLengthWord +++ pushB256 arrayLengthSlot :::
          sstore ::: .call afterOldPauserSlot)
      (fun ex => ∃ post, ex = .ok post) := by
    exact execSat_loadWord_targetIndexKey_prepend
      (wordOffsetCost := 3) (targetOffsetCost := 3) (tagCost := 3)
      hlengthCovered htargetCovered halign hlength htarget rfl
      hlengthOffsetCost htargetOffsetCost hindexTagCost (by omega)
      (by norm_num [gVerylow]) hindexStore
  exact execSat_successfulWrite_step array.write array.currentZero
    array.originalZero (by decide) array.warm hstatic hindexSuffix

private theorem appendTargetExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (htarget : (M.read (targetWord * 32).toNat 32).1.toB256 = 7)
    (hprevious :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hcontinuation :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (harray : d.getStorVal e.currentTarget (arrayEntrySlot 1) = 0)
    (harrayOrig :
      getOrigStorVal e e.currentTarget (arrayEntrySlot 1) = 0)
    (hindex : d.getStorVal e.currentTarget (indexSlot 7) = 0)
    (hindexOrig : getOrigStorVal e e.currentTarget (indexSlot 7) = 0)
    (hlength : d.getStorVal e.currentTarget arrayLengthSlot = 0)
    (hlengthOrig : getOrigStorVal e e.currentTarget arrayLengthSlot = 0)
    (hlengthCold :
      (e.currentTarget, arrayLengthSlot) ∉ d.accessedStorageKeys)
    (hwarmArray :
      (e.currentTarget, arrayEntrySlot 1) ∈ d.accessedStorageKeys)
    (hwarmIndex :
      (e.currentTarget, indexSlot 7) ∈ d.accessedStorageKeys)
    (hcount : d.getStorVal e.currentTarget (countSlot 9) = 0)
    (hcountOrig : getOrigStorVal e e.currentTarget (countSlot 9) = 0)
    (hcountCold :
      (e.currentTarget, countSlot 9) ∉ d.accessedStorageKeys)
    (hinterval :
      d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry :
      (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hstatic : e.isStatic = false) :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[], M,
        10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 +
          60039 + 2136⟩)
      appendTarget
      (fun ex => ∃ post, ex = .ok post) := by
  let d₁ := addAccessedStorageKey d e.currentTarget arrayLengthSlot
  let M₁ := M.write (arrayLengthWord * 32).toNat (1 : B256).toBytes
  let bs₁ := Bytes.writeAt bs (arrayLengthWord * 32).toNat
    (1 : B256).toBytes
  let suffix : Func :=
    sstore :::
      loadWord arrayLengthWord +++ targetIndexKey +++ sstore :::
      loadWord arrayLengthWord +++ pushB256 arrayLengthSlot ::: sstore :::
      .call afterOldPauserSlot
  let suffixGas : Nat :=
    10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 + 60039
  have hlengthCovered :
      (arrayLengthWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (arrayLengthWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hcontinuationCovered :
      (continuationWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (continuationWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hsize₁ : M₁.size = M.size := by
    dsimp only [M₁]
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using hlengthCovered)
  have halign₁ : M₁.size % 32 = 0 := by rw [hsize₁]; exact halign
  have hsizeBound₁ : 768 ≤ M₁.size := by rw [hsize₁]; exact hsize
  have hlengthCovered₁ :
      (arrayLengthWord * 32).toNat + 32 ≤ M₁.size := by
    rw [hsize₁]
    exact hlengthCovered
  have htargetCovered₁ :
      (targetWord * 32).toNat + 32 ≤ M₁.size := by
    rw [hsize₁]
    exact htargetCovered
  have harray₁ : d₁.getStorVal e.currentTarget (arrayEntrySlot 1) = 0 := by
    change d.getStorVal e.currentTarget (arrayEntrySlot 1) = 0
    exact harray
  have hindex₁ : d₁.getStorVal e.currentTarget (indexSlot 7) = 0 := by
    change d.getStorVal e.currentTarget (indexSlot 7) = 0
    exact hindex
  have hlength₁ : d₁.getStorVal e.currentTarget arrayLengthSlot = 0 := by
    change d.getStorVal e.currentTarget arrayLengthSlot = 0
    exact hlength
  have hcount₁ : d₁.getStorVal e.currentTarget (countSlot 9) = 0 := by
    change d.getStorVal e.currentTarget (countSlot 9) = 0
    exact hcount
  have hinterval₁ :
      d₁.getStorVal e.currentTarget heartbeatIntervalSlot = 0 := by
    change d.getStorVal e.currentTarget heartbeatIntervalSlot = 0
    exact hinterval
  have hexpiry₁ : d₁.getStorVal e.currentTarget (expirySlot 9) = 0 := by
    change d.getStorVal e.currentTarget (expirySlot 9) = 0
    exact hexpiry
  have hwarmArray₁ :
      (e.currentTarget, arrayEntrySlot 1) ∈ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simpa [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using
      (Or.inr hwarmArray : arrayLengthSlot = arrayEntrySlot 1 ∨
        (e.currentTarget, arrayEntrySlot 1) ∈ mt.accessedStorageKeys)
  have hwarmIndex₁ :
      (e.currentTarget, indexSlot 7) ∈ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simpa [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using
      (Or.inr hwarmIndex : arrayLengthSlot = indexSlot 7 ∨
        (e.currentTarget, indexSlot 7) ∈ mt.accessedStorageKeys)
  have hwarmLength₁ :
      (e.currentTarget, arrayLengthSlot) ∈ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simp [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys]
  have hcountCold₁ :
      (e.currentTarget, countSlot 9) ∉ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simpa [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using And.intro
        (by decide : arrayLengthSlot ≠ countSlot 9) hcountCold
  have hintervalCold₁ :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simpa [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using And.intro
        (by decide : arrayLengthSlot ≠ heartbeatIntervalSlot) hintervalCold
  have hwarmExpiry₁ :
      (e.currentTarget, expirySlot 9) ∈ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simpa [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using
      (Or.inr hwarmExpiry : arrayLengthSlot = expirySlot 9 ∨
        (e.currentTarget, expirySlot 9) ∈ mt.accessedStorageKeys)
  have hmstoreTail : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d₁.setMach ⟨[1, 1], M, suffixGas + 24⟩)
      (mstoreAt arrayLengthWord +++
        loadWord targetWord +++ loadWord arrayLengthWord +++
          tagTop arrayRegion +++ suffix)
      (fun ex => ∃ post, ex = .ok post) := by
    apply execSat_mstoreAt_word_prepend
      (offsetCost := 3) (G := suffixGas + 18) (Gpre := suffixGas + 24)
      hwf hreads hlengthCovered halign (by decide) (by decide) (by
        norm_num [gVerylow])
    intro hwf₁ hreads₁
    have readAfterBefore {word : B256}
        (hbefore :
          (word * 32).toNat + 32 ≤ (arrayLengthWord * 32).toNat) :
        Bytes.toB256 (bs₁.sliceD (word * 32).toNat 32 0) =
          (M.read (word * 32).toNat 32).1.toB256 := by
      dsimp only [bs₁]
      rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hbefore]
      rw [← Mem.Reads.read hreads]
    have htargetM₁ :
        (M₁.read (targetWord * 32).toNat 32).1.toB256 = 7 := by
      rw [Mem.Reads.read hreads₁]
      rw [readAfterBefore (by decide)]
      exact htarget
    have hpreviousM₁ :
        (M₁.read (previousPauserWord * 32).toNat 32).1.toB256 = 0 := by
      rw [Mem.Reads.read hreads₁]
      rw [readAfterBefore (by decide)]
      exact hprevious
    have hnewM₁ :
        (M₁.read (newPauserWord * 32).toNat 32).1.toB256 = 9 := by
      rw [Mem.Reads.read hreads₁]
      rw [readAfterBefore (by decide)]
      exact hnew
    have hcontinuationM₁ :
        (M₁.read (continuationWord * 32).toNat 32).1.toB256 = 0 := by
      rw [Mem.Reads.read hreads₁]
      rw [readAfterBefore (by decide)]
      exact hcontinuation
    have hlengthM₁ :
        (M₁.read (arrayLengthWord * 32).toNat 32).1.toB256 = 1 := by
      rw [Mem.Reads.read hreads₁]
      rw [show 32 = (1 : B256).toBytes.length by
        rw [B256.length_toBytes]]
      rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
    have hsuffix := appendTarget_write_suffixExecSatOf
      (e := e) (d := d₁) (M := M₁) (bs := bs₁) (stack := [1])
      hwf₁ hreads₁ htargetM₁ hlengthM₁ hpreviousM₁ hnewM₁
      hcontinuationM₁ hsizeBound₁ halign₁ htime harray₁ harrayOrig
      hindex₁ hindexOrig hlength₁ hlengthOrig hwarmArray₁ hwarmIndex₁
      hwarmLength₁ hcount₁ hcountOrig hcountCold₁ hinterval₁
      hintervalCold₁ hexpiry₁ hexpiryOrig hwarmExpiry₁ (by decide) hstatic
    have htag : Func.ExecSat
        ((runtime officialParams).main :: (runtime officialParams).aux)
        e (d₁.setMach ⟨1 :: 7 :: 1 :: [], M₁, suffixGas + 6⟩)
        (tagTop arrayRegion +++ suffix)
        (fun ex => ∃ post, ex = .ok post) := by
      exact execSat_tagTop_prepend (region := arrayRegion)
        (top := 1) (tagged := arrayEntrySlot 1) (stack := [7, 1])
        (tagCost := 3) (G := suffixGas) (Gpre := suffixGas + 6)
        rfl (by decide) (by decide) (by norm_num [gVerylow]) hsuffix
    have hlengthLoad : Func.ExecSat
        ((runtime officialParams).main :: (runtime officialParams).aux)
        e (d₁.setMach ⟨7 :: 1 :: [], M₁, suffixGas + 12⟩)
        (loadWord arrayLengthWord +++ tagTop arrayRegion +++ suffix)
        (fun ex => ∃ post, ex = .ok post) := by
      exact execSat_loadWord_prepend (offsetCost := 3)
        (G := suffixGas + 6) (Gpre := suffixGas + 12)
        hlengthCovered₁ halign₁ hlengthM₁
        (by decide) (by decide) (by norm_num [gVerylow]) htag
    exact execSat_loadWord_prepend (offsetCost := 3)
      (G := suffixGas + 12) (Gpre := suffixGas + 18)
      htargetCovered₁ halign₁ htargetM₁
      (by decide) (by decide) (by norm_num [gVerylow]) hlengthLoad
  have harith : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d₁.setMach ⟨[0], M, suffixGas + 33⟩)
      (pushB256 1 ::: add ::: dup 0 ::: mstoreAt arrayLengthWord +++
        loadWord targetWord +++ loadWord arrayLengthWord +++
          tagTop arrayRegion +++ suffix)
      (fun ex => ∃ post, ex = .ok post) := by
    apply Func.execSat_segment
      (devm' := d₁.setMach ⟨[1, 1], M, suffixGas + 24⟩)
      (f' := mstoreAt arrayLengthWord +++
        loadWord targetWord +++ loadWord arrayLengthWord +++
          tagTop arrayRegion +++ suffix)
    · intro ex htail
      func_run (3) [1]
      case h_f =>
        norm_num [suffixGas]
        exact htail
    · exact hmstoreTail
  have hsload : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[arrayLengthSlot], M, suffixGas + 2133⟩)
      (sload ::: pushB256 1 ::: add ::: dup 0 :::
        mstoreAt arrayLengthWord +++ loadWord targetWord +++
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ suffix)
      (fun ex => ∃ post, ex = .ok post) := by
    exact execSat_sload_cold_prepend hlength hlengthCold (by decide)
      (by norm_num [gasColdSload]) harith
  apply Func.execSat_next
  · apply Ninst.runCompiled_pushB256 (c := 3) (G := suffixGas + 2133)
      (by decide) rfl
    simp only [Devm.stack_setMach]
    decide
  · change Func.ExecSat _ e
      (d.setMach ⟨[arrayLengthSlot], M, suffixGas + 2133⟩)
      (sload ::: pushB256 1 ::: add ::: dup 0 :::
        mstoreAt arrayLengthWord +++ loadWord targetWord +++
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ suffix)
      (fun ex => ∃ post, ex = .ok post)
    exact hsload

private theorem setPauserFreshAssignmentCallExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (htarget : (M.read (targetWord * 32).toNat 32).1.toB256 = 7)
    (hprevious :
      (M.read (previousPauserWord * 32).toNat 32).1.toB256 = 0)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hcontinuation :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (hassignment : d.getStorVal e.currentTarget (assignmentSlot 7) = 0)
    (hassignmentOrig :
      getOrigStorVal e e.currentTarget (assignmentSlot 7) = 0)
    (hwarmAssignment :
      (e.currentTarget, assignmentSlot 7) ∈ d.accessedStorageKeys)
    (harray : d.getStorVal e.currentTarget (arrayEntrySlot 1) = 0)
    (harrayOrig :
      getOrigStorVal e e.currentTarget (arrayEntrySlot 1) = 0)
    (hindex : d.getStorVal e.currentTarget (indexSlot 7) = 0)
    (hindexOrig : getOrigStorVal e e.currentTarget (indexSlot 7) = 0)
    (hlength : d.getStorVal e.currentTarget arrayLengthSlot = 0)
    (hlengthOrig : getOrigStorVal e e.currentTarget arrayLengthSlot = 0)
    (hlengthCold :
      (e.currentTarget, arrayLengthSlot) ∉ d.accessedStorageKeys)
    (hwarmArray :
      (e.currentTarget, arrayEntrySlot 1) ∈ d.accessedStorageKeys)
    (hwarmIndex :
      (e.currentTarget, indexSlot 7) ∈ d.accessedStorageKeys)
    (hcount : d.getStorVal e.currentTarget (countSlot 9) = 0)
    (hcountOrig : getOrigStorVal e e.currentTarget (countSlot 9) = 0)
    (hcountCold :
      (e.currentTarget, countSlot 9) ∉ d.accessedStorageKeys)
    (hinterval :
      d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry :
      (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hstatic : e.isStatic = false) :
    let appendGas :=
      10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 +
        60039 + 2136
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[assignmentSlot 7, 9, 0], M,
        appendGas + gasStorageSet + 29⟩)
      (sstore ::: iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
      (fun ex => ∃ post, ex = .ok post) := by
  let appendGas : Nat :=
    10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 +
      60039 + 2136
  let oldTail : Func :=
    previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
      previousCountKey +++ sstore ::: .call afterOldPauserSlot
  let branch : Func := (.call appendTargetSlot) <?> oldTail
  let assign := successfulWriteCertificateOf e d (assignmentSlot 7) 9
  have pairNe {key : B256} (hne : key ≠ assignmentSlot 7) :
      (e.currentTarget, key) ≠ (e.currentTarget, assignmentSlot 7) := by
    intro h
    exact hne (congrArg Prod.snd h)
  have offKey {key : B256} (hne : key ≠ assignmentSlot 7) :
      assign.post.getStorVal e.currentTarget key =
        d.getStorVal e.currentTarget key := by
    exact assign.other _ _ (pairNe hne)
  have harrayPost :
      assign.post.getStorVal e.currentTarget (arrayEntrySlot 1) = 0 := by
    rw [offKey (by decide)]
    exact harray
  have hindexPost :
      assign.post.getStorVal e.currentTarget (indexSlot 7) = 0 := by
    rw [offKey (by decide)]
    exact hindex
  have hlengthPost :
      assign.post.getStorVal e.currentTarget arrayLengthSlot = 0 := by
    rw [offKey (by decide)]
    exact hlength
  have hcountPost :
      assign.post.getStorVal e.currentTarget (countSlot 9) = 0 := by
    rw [offKey (by decide)]
    exact hcount
  have hintervalPost :
      assign.post.getStorVal e.currentTarget heartbeatIntervalSlot = 0 := by
    rw [offKey (by decide)]
    exact hinterval
  have hexpiryPost :
      assign.post.getStorVal e.currentTarget (expirySlot 9) = 0 := by
    rw [offKey (by decide)]
    exact hexpiry
  have warmOfOld {key : B256}
      (hmem : (e.currentTarget, key) ∈ d.accessedStorageKeys) :
      (e.currentTarget, key) ∈ assign.post.accessedStorageKeys := by
    rw [assign.accessedStorageKeys]
    exact hmem
  have coldOfOld {key : B256}
      (hmem : (e.currentTarget, key) ∉ d.accessedStorageKeys) :
      (e.currentTarget, key) ∉ assign.post.accessedStorageKeys := by
    rw [assign.accessedStorageKeys]
    exact hmem
  have happend := appendTargetExecSatOf
    (e := e) (d := assign.post) (M := M) (bs := bs)
    hwf hreads htarget hprevious hnew hcontinuation hsize halign htime
    harrayPost harrayOrig hindexPost hindexOrig hlengthPost hlengthOrig
    (coldOfOld hlengthCold) (warmOfOld hwarmArray) (warmOfOld hwarmIndex)
    hcountPost hcountOrig (coldOfOld hcountCold)
    hintervalPost (coldOfOld hintervalCold)
    hexpiryPost hexpiryOrig (warmOfOld hwarmExpiry) hstatic
  have hlookup :
      ((runtime officialParams).main ::
        (runtime officialParams).aux)[appendTargetSlot]? =
          some appendTarget := by
    simp [runtime, aux, appendTargetSlot]
  have hcall : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (assign.post.setMach ⟨[], M, appendGas + 12⟩)
      (.call appendTargetSlot)
      (fun ex => ∃ post, ex = .ok post) := by
    rcases happend with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_call' hlookup (by
      simp only [Devm.stack_setMach]
      decide)
    · rfl
    · exact hw
  have hbranch : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (assign.post.setMach ⟨[1], M, appendGas + 26⟩)
      branch (fun ex => ∃ post, ex = .ok post) := by
    rcases hcall with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_branch_succ (w := 1) (G := appendGas + 12)
      (by decide) rfl (by
        simp only [Devm.stack_setMach, List.length_cons]
        decide)
    · norm_num [gVerylow, gMid, gHigh, gJumpdest]
    · change Func.ExecWitness _ _
        (assign.post.setMach ⟨[], M, appendGas + 12⟩)
        (.call appendTargetSlot) ex
      exact hw
  have hiszero : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (assign.post.setMach ⟨[0], M, appendGas + 29⟩)
      (iszero ::: branch) (fun ex => ∃ post, ex = .ok post) := by
    apply Func.execSat_next
    · exact Ninst.runCompiled_unary (x := 0) (v := 1) (s := [])
        (cost := gVerylow) (G := appendGas + 26)
        (by rintro ⟨⟩) rfl rfl rfl
        (by norm_num [gVerylow]) (by decide)
    · exact hbranch
  simpa only [branch, oldTail, appendGas, Nat.add_right_comm] using
    (execSat_successfulWrite_step assign hassignment hassignmentOrig
      (by decide) hwarmAssignment hstatic hiszero)

private theorem setPauserFreshBodyExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (htarget : (M.read (targetWord * 32).toNat 32).1.toB256 = 7)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hcontinuation :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (hassignment : d.getStorVal e.currentTarget (assignmentSlot 7) = 0)
    (hassignmentOrig :
      getOrigStorVal e e.currentTarget (assignmentSlot 7) = 0)
    (hassignmentCold :
      (e.currentTarget, assignmentSlot 7) ∉ d.accessedStorageKeys)
    (harray : d.getStorVal e.currentTarget (arrayEntrySlot 1) = 0)
    (harrayOrig :
      getOrigStorVal e e.currentTarget (arrayEntrySlot 1) = 0)
    (hindex : d.getStorVal e.currentTarget (indexSlot 7) = 0)
    (hindexOrig : getOrigStorVal e e.currentTarget (indexSlot 7) = 0)
    (hlength : d.getStorVal e.currentTarget arrayLengthSlot = 0)
    (hlengthOrig : getOrigStorVal e e.currentTarget arrayLengthSlot = 0)
    (hlengthCold :
      (e.currentTarget, arrayLengthSlot) ∉ d.accessedStorageKeys)
    (hwarmArray :
      (e.currentTarget, arrayEntrySlot 1) ∈ d.accessedStorageKeys)
    (hwarmIndex :
      (e.currentTarget, indexSlot 7) ∈ d.accessedStorageKeys)
    (hcount : d.getStorVal e.currentTarget (countSlot 9) = 0)
    (hcountOrig : getOrigStorVal e e.currentTarget (countSlot 9) = 0)
    (hcountCold :
      (e.currentTarget, countSlot 9) ∉ d.accessedStorageKeys)
    (hinterval :
      d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry :
      (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hstatic : e.isStatic = false) :
    let appendGas :=
      10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 +
        60039 + 2136
    let assignmentGas := appendGas + gasStorageSet + 29
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[], M, assignmentGas + 2139⟩)
      (targetKey +++ sload ::: dup 0 ::: mstoreAt previousPauserWord +++
        loadWord newPauserWord +++ targetKey +++ sstore ::: iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
      (fun ex => ∃ post, ex = .ok post) := by
  let appendGas : Nat :=
    10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 +
      60039 + 2136
  let assignmentGas : Nat := appendGas + gasStorageSet + 29
  let d₁ := addAccessedStorageKey d e.currentTarget (assignmentSlot 7)
  let M₁ := M.write (previousPauserWord * 32).toNat (0 : B256).toBytes
  let bs₁ := Bytes.writeAt bs (previousPauserWord * 32).toNat
    (0 : B256).toBytes
  let suffix : Func :=
    sstore ::: iszero :::
      ((.call appendTargetSlot) <?>
        (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ sstore ::: .call afterOldPauserSlot))
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hnewCovered : (newPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hpreviousCovered :
      (previousPauserWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (previousPauserWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hMsize₁ : M₁.size = M.size := by
    dsimp only [M₁]
    exact Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using hpreviousCovered)
  have hMalign₁ : M₁.size % 32 = 0 := by rw [hMsize₁]; exact halign
  have hMbound₁ : 768 ≤ M₁.size := by rw [hMsize₁]; exact hsize
  have htargetCovered₁ :
      (targetWord * 32).toNat + 32 ≤ M₁.size := by
    rw [hMsize₁]
    exact htargetCovered
  have hnewCovered₁ :
      (newPauserWord * 32).toNat + 32 ≤ M₁.size := by
    rw [hMsize₁]
    exact hnewCovered
  have hassignment₁ :
      d₁.getStorVal e.currentTarget (assignmentSlot 7) = 0 := by
    change d.getStorVal e.currentTarget (assignmentSlot 7) = 0
    exact hassignment
  have harray₁ : d₁.getStorVal e.currentTarget (arrayEntrySlot 1) = 0 := by
    change d.getStorVal e.currentTarget (arrayEntrySlot 1) = 0
    exact harray
  have hindex₁ : d₁.getStorVal e.currentTarget (indexSlot 7) = 0 := by
    change d.getStorVal e.currentTarget (indexSlot 7) = 0
    exact hindex
  have hlength₁ : d₁.getStorVal e.currentTarget arrayLengthSlot = 0 := by
    change d.getStorVal e.currentTarget arrayLengthSlot = 0
    exact hlength
  have hcount₁ : d₁.getStorVal e.currentTarget (countSlot 9) = 0 := by
    change d.getStorVal e.currentTarget (countSlot 9) = 0
    exact hcount
  have hinterval₁ :
      d₁.getStorVal e.currentTarget heartbeatIntervalSlot = 0 := by
    change d.getStorVal e.currentTarget heartbeatIntervalSlot = 0
    exact hinterval
  have hexpiry₁ : d₁.getStorVal e.currentTarget (expirySlot 9) = 0 := by
    change d.getStorVal e.currentTarget (expirySlot 9) = 0
    exact hexpiry
  have hwarmAssignment₁ :
      (e.currentTarget, assignmentSlot 7) ∈ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simp [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys]
  have warmOld {key : B256}
      (hmem : (e.currentTarget, key) ∈ d.accessedStorageKeys) :
      (e.currentTarget, key) ∈ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simpa [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using
      (Or.inr hmem : assignmentSlot 7 = key ∨
        (e.currentTarget, key) ∈ mt.accessedStorageKeys)
  have coldOld {key : B256} (hne : assignmentSlot 7 ≠ key)
      (hmem : (e.currentTarget, key) ∉ d.accessedStorageKeys) :
      (e.currentTarget, key) ∉ d₁.accessedStorageKeys := by
    rcases d with ⟨mach, mt, world⟩
    simpa [d₁, addAccessedStorageKey, liftMachMetaPure,
      Meta.addAccessedStorageKey, Devm.accessedStorageKeys] using
      And.intro hne hmem
  have hmstoreTail : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d₁.setMach ⟨[0, 0], M, assignmentGas + 24⟩)
      (mstoreAt previousPauserWord +++
        loadWord newPauserWord +++ targetKey +++ suffix)
      (fun ex => ∃ post, ex = .ok post) := by
    apply execSat_mstoreAt_word_prepend
      (offsetCost := 3) (G := assignmentGas + 18)
      (Gpre := assignmentGas + 24)
      hwf hreads hpreviousCovered halign (by decide) (by decide)
      (by norm_num [gVerylow])
    intro hwf₁ hreads₁
    have sliceBefore {word : B256}
        (hbefore :
          (word * 32).toNat + 32 ≤ (previousPauserWord * 32).toNat) :
        Bytes.toB256 (bs₁.sliceD (word * 32).toNat 32 0) =
          (M.read (word * 32).toNat 32).1.toB256 := by
      dsimp only [bs₁]
      rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hbefore]
      rw [← Mem.Reads.read hreads]
    have sliceAfter {word : B256}
        (hafter :
          (previousPauserWord * 32).toNat + 32 ≤ (word * 32).toNat) :
        bs₁.sliceD (word * 32).toNat 32 0 =
          bs.sliceD (word * 32).toNat 32 0 := by
      dsimp only [bs₁]
      rw [List.sliceD_eq_map, List.sliceD_eq_map]
      apply List.map_congr_left
      intro i hi
      rw [Bytes.getD_writeAt]
      rw [if_neg]
      have hi' := List.mem_range.mp hi
      rw [B256.length_toBytes]
      omega
    have htargetM₁ :
        (M₁.read (targetWord * 32).toNat 32).1.toB256 = 7 := by
      rw [Mem.Reads.read hreads₁, sliceBefore (by decide)]
      exact htarget
    have hnewM₁ :
        (M₁.read (newPauserWord * 32).toNat 32).1.toB256 = 9 := by
      rw [Mem.Reads.read hreads₁, sliceBefore (by decide)]
      exact hnew
    have hpreviousM₁ :
        (M₁.read (previousPauserWord * 32).toNat 32).1.toB256 = 0 := by
      rw [Mem.Reads.read hreads₁]
      rw [show 32 = (0 : B256).toBytes.length by
        rw [B256.length_toBytes]]
      rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
    have hcontinuationM₁ :
        (M₁.read (continuationWord * 32).toNat 32).1.toB256 = 0 := by
      rw [Mem.Reads.read hreads₁, sliceAfter (by decide)]
      rw [← Mem.Reads.read hreads]
      exact hcontinuation
    have hassign := setPauserFreshAssignmentCallExecSatOf
      (e := e) (d := d₁) (M := M₁) (bs := bs₁)
      hwf₁ hreads₁ htargetM₁ hpreviousM₁ hnewM₁
      hcontinuationM₁ hMbound₁ hMalign₁ htime hassignment₁
      hassignmentOrig hwarmAssignment₁ harray₁ harrayOrig hindex₁
      hindexOrig hlength₁ hlengthOrig (coldOld (by decide) hlengthCold)
      (warmOld hwarmArray) (warmOld hwarmIndex) hcount₁ hcountOrig
      (coldOld (by decide) hcountCold) hinterval₁
      (coldOld (by decide) hintervalCold) hexpiry₁ hexpiryOrig
      (warmOld hwarmExpiry) hstatic
    have htag : Func.ExecSat
        ((runtime officialParams).main :: (runtime officialParams).aux)
        e (d₁.setMach ⟨7 :: 9 :: 0 :: [], M₁, assignmentGas + 6⟩)
        (tagTop assignmentRegion +++ suffix)
        (fun ex => ∃ post, ex = .ok post) := by
      exact execSat_tagTop_prepend (region := assignmentRegion)
        (top := 7) (tagged := assignmentSlot 7) (stack := [9, 0])
        (tagCost := 3) (G := assignmentGas)
        (Gpre := assignmentGas + 6)
        rfl (by decide) (by decide) (by norm_num [gVerylow]) (by
          simpa only [suffix, assignmentGas, appendGas] using hassign)
    have htargetKey : Func.ExecSat
        ((runtime officialParams).main :: (runtime officialParams).aux)
        e (d₁.setMach ⟨9 :: 0 :: [], M₁, assignmentGas + 12⟩)
        (targetKey +++ suffix)
        (fun ex => ∃ post, ex = .ok post) := by
      simpa only [targetKey, prepend_append] using
        (execSat_loadWord_prepend (offsetCost := 3)
          (G := assignmentGas + 6) (Gpre := assignmentGas + 12)
          htargetCovered₁ hMalign₁ htargetM₁
          (by decide) (by decide) (by norm_num [gVerylow]) htag)
    exact execSat_loadWord_prepend (offsetCost := 3)
      (G := assignmentGas + 12) (Gpre := assignmentGas + 18)
      hnewCovered₁ hMalign₁ hnewM₁
      (by decide) (by decide) (by norm_num [gVerylow]) htargetKey
  have hdup : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d₁.setMach ⟨[0], M, assignmentGas + 27⟩)
      (dup 0 ::: mstoreAt previousPauserWord +++
        loadWord newPauserWord +++ targetKey +++ suffix)
      (fun ex => ∃ post, ex = .ok post) := by
    apply Func.execSat_next
    · exact Ninst.runCompiled_dup (n := 0) (w := 0)
        (G := assignmentGas + 24) rfl (by norm_num [gVerylow]) (by
          simp only [Devm.stack_setMach, List.length_cons]
          decide)
    · exact hmstoreTail
  have hsload : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[assignmentSlot 7], M,
        assignmentGas + 27 + gasColdSload⟩)
      (sload ::: dup 0 ::: mstoreAt previousPauserWord +++
        loadWord newPauserWord +++ targetKey +++ suffix)
      (fun ex => ∃ post, ex = .ok post) := by
    exact execSat_sload_cold_prepend hassignment hassignmentCold (by decide)
      (by norm_num [gasColdSload]) hdup
  have htag : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[7], M,
        assignmentGas + 27 + gasColdSload + 6⟩)
      (tagTop assignmentRegion +++ sload ::: dup 0 :::
        mstoreAt previousPauserWord +++ loadWord newPauserWord +++
        targetKey +++ suffix)
      (fun ex => ∃ post, ex = .ok post) := by
    exact execSat_tagTop_prepend (region := assignmentRegion)
      (top := 7) (tagged := assignmentSlot 7) (stack := [])
      (tagCost := 3) (G := assignmentGas + 27 + gasColdSload)
      (Gpre := assignmentGas + 27 + gasColdSload + 6)
      rfl (by decide) (by decide) (by norm_num [gVerylow]) hsload
  simpa only [targetKey, suffix, prepend_append] using
    (execSat_loadWord_prepend (offsetCost := 3)
      (G := assignmentGas + 27 + gasColdSload + 6)
      (Gpre := assignmentGas + 2139)
      htargetCovered halign htarget (by decide) (by decide)
      (by norm_num [gasColdSload, gVerylow]) htag)

private theorem setPauserKernelFreshExecSatOf
    {e : Sevm} {d : Devm} {M : Mem} {bs : Bytes}
    (hwf : Mem.Wf M) (hreads : Mem.Reads M bs)
    (htarget : (M.read (targetWord * 32).toNat 32).1.toB256 = 7)
    (hnew : (M.read (newPauserWord * 32).toNat 32).1.toB256 = 9)
    (hcontinuation :
      (M.read (continuationWord * 32).toNat 32).1.toB256 = 0)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (htime : e.benvStat.time = 10)
    (hassignment : d.getStorVal e.currentTarget (assignmentSlot 7) = 0)
    (hassignmentOrig :
      getOrigStorVal e e.currentTarget (assignmentSlot 7) = 0)
    (hassignmentCold :
      (e.currentTarget, assignmentSlot 7) ∉ d.accessedStorageKeys)
    (harray : d.getStorVal e.currentTarget (arrayEntrySlot 1) = 0)
    (harrayOrig :
      getOrigStorVal e e.currentTarget (arrayEntrySlot 1) = 0)
    (hindex : d.getStorVal e.currentTarget (indexSlot 7) = 0)
    (hindexOrig : getOrigStorVal e e.currentTarget (indexSlot 7) = 0)
    (hlength : d.getStorVal e.currentTarget arrayLengthSlot = 0)
    (hlengthOrig : getOrigStorVal e e.currentTarget arrayLengthSlot = 0)
    (hlengthCold :
      (e.currentTarget, arrayLengthSlot) ∉ d.accessedStorageKeys)
    (hwarmArray :
      (e.currentTarget, arrayEntrySlot 1) ∈ d.accessedStorageKeys)
    (hwarmIndex :
      (e.currentTarget, indexSlot 7) ∈ d.accessedStorageKeys)
    (hcount : d.getStorVal e.currentTarget (countSlot 9) = 0)
    (hcountOrig : getOrigStorVal e e.currentTarget (countSlot 9) = 0)
    (hcountCold :
      (e.currentTarget, countSlot 9) ∉ d.accessedStorageKeys)
    (hinterval :
      d.getStorVal e.currentTarget heartbeatIntervalSlot = 0)
    (hintervalCold :
      (e.currentTarget, heartbeatIntervalSlot) ∉ d.accessedStorageKeys)
    (hexpiry : d.getStorVal e.currentTarget (expirySlot 9) = 0)
    (hexpiryOrig : getOrigStorVal e e.currentTarget (expirySlot 9) = 0)
    (hwarmExpiry :
      (e.currentTarget, expirySlot 9) ∈ d.accessedStorageKeys)
    (hstatic : e.isStatic = false) :
    let appendGas :=
      10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 +
        60039 + 2136
    let assignmentGas := appendGas + gasStorageSet + 29
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[], M, assignmentGas + 2161⟩)
      setPauserKernel
      (fun ex => ∃ post, ex = .ok post) := by
  let appendGas : Nat :=
    10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 +
      60039 + 2136
  let assignmentGas : Nat := appendGas + gasStorageSet + 29
  let body : Func :=
    targetKey +++ sload ::: dup 0 ::: mstoreAt previousPauserWord +++
      loadWord newPauserWord +++ targetKey +++ sstore ::: iszero :::
      ((.call appendTargetSlot) <?>
        (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ sstore ::: .call afterOldPauserSlot))
  let guarded : Func := (.call pausableZeroErrorSlot) <?> body
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hbody : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[], M, assignmentGas + 2139⟩)
      body (fun ex => ∃ post, ex = .ok post) := by
    simpa only [body, assignmentGas, appendGas] using
      (setPauserFreshBodyExecSatOf
        (e := e) (d := d) (M := M) (bs := bs)
        hwf hreads htarget hnew hcontinuation hsize halign htime
        hassignment hassignmentOrig hassignmentCold harray harrayOrig
        hindex hindexOrig hlength hlengthOrig hlengthCold hwarmArray
        hwarmIndex hcount hcountOrig hcountCold hinterval hintervalCold
        hexpiry hexpiryOrig hwarmExpiry hstatic)
  have hbranch : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[0], M, assignmentGas + 2152⟩)
      guarded (fun ex => ∃ post, ex = .ok post) := by
    rcases hbody with ⟨ex, hw, hp⟩
    refine ⟨ex, ?_, hp⟩
    apply Func.execWitness_branch_zero (G := assignmentGas + 2139)
      rfl (by
        simp only [Devm.stack_setMach, List.length_cons]
        decide)
    · norm_num [gVerylow, gHigh]
    · change Func.ExecWitness _ _
        (d.setMach ⟨[], M, assignmentGas + 2139⟩) body ex
      exact hw
  have htest : Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      e (d.setMach ⟨[7], M, assignmentGas + 2155⟩)
      (iszero ::: guarded) (fun ex => ∃ post, ex = .ok post) := by
    apply Func.execSat_next
    · exact Ninst.runCompiled_unary (x := 7) (v := 0) (s := [])
        (cost := gVerylow) (G := assignmentGas + 2152)
        (by rintro ⟨⟩) rfl rfl (by decide)
        (by norm_num [gVerylow]) (by decide)
    · exact hbranch
  simpa only [setPauserKernel, guarded, body] using
    (execSat_loadWord_prepend (offsetCost := 3)
      (G := assignmentGas + 2155) (Gpre := assignmentGas + 2161)
      htargetCovered halign htarget (by decide) (by decide)
      (by norm_num [gVerylow]) htest)

private def freshKernelOwner : Adr := Nat.toAdr 100

private def freshKernelMem : Mem :=
  ((((Mem.empty.write (durationWord * 32).toNat (0 : B256).toBytes).write
    (targetWord * 32).toNat (7 : B256).toBytes).write
    (newPauserWord * 32).toNat (9 : B256).toBytes).write
    (continuationWord * 32).toNat (0 : B256).toBytes)

private def freshKernelImage : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt [] (durationWord * 32).toNat (0 : B256).toBytes)
        (targetWord * 32).toNat (7 : B256).toBytes)
      (newPauserWord * 32).toNat (9 : B256).toBytes)
    (continuationWord * 32).toNat (0 : B256).toBytes

private def freshKernelCode : ByteArray :=
  ByteArray.mk (lidoCircuitBreakerCode officialParams).toArray

private def freshKernelBaseMsg : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        stat := { (default : BenvStat) with time := 10 } }
    target := some freshKernelOwner
    currentTarget := freshKernelOwner
    codeAddress := some freshKernelOwner
    code := freshKernelCode
    isStatic := false
    accessedStorageKeys := .ofList
      [(freshKernelOwner, arrayEntrySlot (1 : B256)),
        (freshKernelOwner, indexSlot (7 : B256)),
        (freshKernelOwner, expirySlot (9 : B256))] }

private def freshKernelSevm : Sevm := initSevm freshKernelBaseMsg

private def freshKernelBase : Devm := initDevm freshKernelBaseMsg

private def freshKernelGas : Nat :=
  let appendGas :=
    10000 + gasStorageSet + 20 + 2132 + 45 + 1935 + 22164 +
      60039 + 2136
  let assignmentGas := appendGas + gasStorageSet + 29
  assignmentGas + 2161

private def freshKernelPre : Devm :=
  freshKernelBase.setMach ⟨[], freshKernelMem, freshKernelGas⟩

private theorem freshKernelMem_facts :
    Mem.Wf freshKernelMem ∧
    Mem.Reads freshKernelMem freshKernelImage ∧
    freshKernelMem.size = 768 ∧
    freshKernelMem.size % 32 = 0 ∧
    (freshKernelMem.read (targetWord * 32).toNat 32).1.toB256 = 7 ∧
    (freshKernelMem.read (newPauserWord * 32).toNat 32).1.toB256 = 9 ∧
    (freshKernelMem.read
      (continuationWord * 32).toNat 32).1.toB256 = 0 := by
  have hwf₀ := Mem.Wf.write Mem.wf_empty
    (durationWord * 32).toNat (0 : B256).toBytes
  have hr₀ := Mem.Reads.write Mem.wf_empty Mem.reads_empty
    (durationWord * 32).toNat (0 : B256).toBytes
  have hwf₁ := Mem.Wf.write hwf₀
    (targetWord * 32).toNat (7 : B256).toBytes
  have hr₁ := Mem.Reads.write hwf₀ hr₀
    (targetWord * 32).toNat (7 : B256).toBytes
  have hwf₂ := Mem.Wf.write hwf₁
    (newPauserWord * 32).toNat (9 : B256).toBytes
  have hr₂ := Mem.Reads.write hwf₁ hr₁
    (newPauserWord * 32).toNat (9 : B256).toBytes
  have hwf₃ := Mem.Wf.write hwf₂
    (continuationWord * 32).toNat (0 : B256).toBytes
  have hr₃ := Mem.Reads.write hwf₂ hr₂
    (continuationWord * 32).toNat (0 : B256).toBytes
  refine ⟨hwf₃, hr₃, rfl, rfl, rfl, rfl, rfl⟩

private theorem freshKernelState_facts :
    freshKernelSevm.currentTarget = freshKernelOwner ∧
    freshKernelSevm.benvStat.time = 10 ∧
    freshKernelSevm.isStatic = false ∧
    (∀ key, freshKernelBase.getStorVal
      freshKernelSevm.currentTarget key = 0) ∧
    (∀ key, getOrigStorVal freshKernelSevm
      freshKernelSevm.currentTarget key = 0) ∧
    (∀ key,
      (freshKernelSevm.currentTarget, key) ∈
          freshKernelBase.accessedStorageKeys ↔
        key = arrayEntrySlot (1 : B256) ∨
        key = indexSlot (7 : B256) ∨
        key = expirySlot (9 : B256)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro key
    rfl
  · intro key
    rfl
  · intro key
    change (freshKernelOwner, key) ∈
        Std.HashSet.ofList
          [(freshKernelOwner, arrayEntrySlot (1 : B256)),
            (freshKernelOwner, indexSlot (7 : B256)),
            (freshKernelOwner, expirySlot (9 : B256))] ↔ _
    rw [Std.HashSet.mem_ofList]
    simp

private def freshKernelSuccess : Execution → Prop
  | .ok _ => True
  | .error _ => False

set_option maxRecDepth 32768 in
private theorem freshKernelExecSat :
    Func.ExecSat
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshKernelSevm freshKernelPre setPauserKernel
      freshKernelSuccess := by
  rcases freshKernelMem_facts with
    ⟨hwf, hreads, hsize, halign, htarget, hnew, hcontinuation⟩
  rcases freshKernelState_facts with
    ⟨howner, htime, hstatic, hcurrent, horiginal, haccess⟩
  have hcold (key : B256)
      (hneArray : key ≠ arrayEntrySlot (1 : B256))
      (hneIndex : key ≠ indexSlot (7 : B256))
      (hneExpiry : key ≠ expirySlot (9 : B256)) :
      (freshKernelSevm.currentTarget, key) ∉
        freshKernelBase.accessedStorageKeys := by
    rw [haccess]
    simp [hneArray, hneIndex, hneExpiry]
  have hwarmArray :
      (freshKernelSevm.currentTarget, arrayEntrySlot (1 : B256)) ∈
        freshKernelBase.accessedStorageKeys := by
    rw [haccess]
    exact Or.inl rfl
  have hwarmIndex :
      (freshKernelSevm.currentTarget, indexSlot (7 : B256)) ∈
        freshKernelBase.accessedStorageKeys := by
    rw [haccess]
    exact Or.inr (Or.inl rfl)
  have hwarmExpiry :
      (freshKernelSevm.currentTarget, expirySlot (9 : B256)) ∈
        freshKernelBase.accessedStorageKeys := by
    rw [haccess]
    exact Or.inr (Or.inr rfl)
  have hrun := setPauserKernelFreshExecSatOf
    (e := freshKernelSevm) (d := freshKernelBase)
    (M := freshKernelMem) (bs := freshKernelImage)
    hwf hreads htarget hnew hcontinuation (by omega) halign htime
    (hcurrent _) (horiginal _)
    (hcold _ (by decide) (by decide) (by decide))
    (hcurrent _) (horiginal _) (hcurrent _) (horiginal _)
    (hcurrent _) (horiginal _)
    (hcold _ (by decide) (by decide) (by decide))
    hwarmArray hwarmIndex (hcurrent _) (horiginal _)
    (hcold _ (by decide) (by decide) (by decide))
    (hcurrent _)
    (hcold _ (by decide) (by decide) (by decide))
    (hcurrent _) (horiginal _) hwarmExpiry hstatic
  rcases hrun with ⟨ex, hw, post, hpost⟩
  subst ex
  exact ⟨.ok post, hw, trivial⟩

set_option maxRecDepth 32768 in
private theorem freshKernelRun :
    ∃ post,
      Func.RunCompiled
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshKernelSevm freshKernelPre setPauserKernel post := by
  rcases freshKernelExecSat with ⟨ex, hw, hp⟩
  cases ex with
  | ok post => exact ⟨post, hw⟩
  | error err => exact False.elim hp

private theorem freshKernelCode_bytes :
    freshKernelSevm.code.toList =
      lidoCircuitBreakerCode officialParams := by
  change freshKernelCode.toList = lidoCircuitBreakerCode officialParams
  rw [freshKernelCode, ByteArray.toList_eq_toList_data]

private theorem freshKernel_tableEntry :
    ∃ loc,
      (table 0
        ((runtime officialParams).main ::
          (runtime officialParams).aux))[setPauserSlot]? =
        some (loc, setPauserKernel) := by
  simp [runtime, aux, setPauserSlot]
  exact ⟨_, rfl⟩

set_option maxRecDepth 32768 in
private theorem freshKernelExec :
    ∃ loc post,
      ∃ _execution : Exec (loc + 1) freshKernelSevm freshKernelPre (.ok post),
        (table 0
          ((runtime officialParams).main ::
            (runtime officialParams).aux))[setPauserSlot]? =
            some (loc, setPauserKernel) ∧
        freshKernelSevm.code.toList =
          lidoCircuitBreakerCode officialParams := by
  rcases freshKernelRun with ⟨post, run⟩
  rcases freshKernel_tableEntry with ⟨loc, htable⟩
  have hcompiled :
      some freshKernelSevm.code.toList =
        Prog.compile (runtime officialParams) := by
    rw [freshKernelCode_bytes, lidoCircuitBreakerCode_compile]
  have hsub := (subcode_of_get?_eq_some hcompiled htable).2
  have hnopush :=
    (Prog.jumpable_of_get?_table hcompiled htable).2
  rcases Func.exec_of_runCompiled_core run hcompiled rfl (loc + 1)
      hsub hnopush with ⟨execution⟩
  exact ⟨loc, post, execution, htable, freshKernelCode_bytes⟩

private def freshLogicalStorageOfStor (s : Stor) : LogicalStorage :=
  { read := s.get }

private theorem freshKernel_entryWitness :
    RegistryWitness
      (freshLogicalStorageOfStor
        (Devm.getStor freshKernelPre freshKernelOwner)) [] := by
  change RegistryWitness emptyStorage []
  exact emptyWitness

private theorem freshKernel_canonicalFacts :
    canonicalAddress (7 : B256) ∧ canonicalAddress (9 : B256) := by
  constructor
  · unfold canonicalAddress
    change (7 : Nat) < 2 ^ 160
    norm_num
  · unfold canonicalAddress
    change (9 : Nat) < 2 ^ 160
    norm_num

set_option maxRecDepth 32768 in
theorem freshRegistration_exactCode_success_control :
    let image : Bytes :=
      Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt
            (Bytes.writeAt [] (durationWord * 32).toNat
              (0 : B256).toBytes)
            (targetWord * 32).toNat (7 : B256).toBytes)
          (newPauserWord * 32).toNat (9 : B256).toBytes)
        (continuationWord * 32).toNat (0 : B256).toBytes
    ∃ owner : Adr, ∃ sevm : Sevm, ∃ pre : Devm,
      owner = Nat.toAdr 100 ∧
      sevm.currentTarget = owner ∧
      sevm.codeAddress = some owner ∧
      sevm.code.toList = lidoCircuitBreakerCode officialParams ∧
      Mem.Wf pre.memory ∧
      Mem.Reads pre.memory image ∧
      768 ≤ pre.memory.size ∧
      pre.memory.size % 32 = 0 ∧
      (pre.memory.read (targetWord * 32).toNat 32).1.toB256 = 7 ∧
      (pre.memory.read (newPauserWord * 32).toNat 32).1.toB256 = 9 ∧
      (pre.memory.read
        (continuationWord * 32).toNat 32).1.toB256 = 0 ∧
      RegistryWitness
        ({ read := (Devm.getStor pre owner).get } : LogicalStorage) [] ∧
      canonicalAddress (7 : B256) ∧
      canonicalAddress (9 : B256) ∧
      setPauser [] 7 9 = some [((7 : B256), (9 : B256))] ∧
      ∃ loc post,
        ∃ _run : Func.RunCompiled
            ((runtime officialParams).main ::
              (runtime officialParams).aux)
            sevm pre setPauserKernel post,
          ∃ _execution : Exec (loc + 1) sevm pre (.ok post),
            (table 0
              ((runtime officialParams).main ::
                (runtime officialParams).aux))[setPauserSlot]? =
              some (loc, setPauserKernel) := by
  dsimp only
  rcases freshKernelMem_facts with
    ⟨hwf, hreads, hsize, halign, htarget, hnew, hcontinuation⟩
  rcases freshKernel_canonicalFacts with ⟨htargetCanonical, hnewCanonical⟩
  refine ⟨freshKernelOwner, freshKernelSevm, freshKernelPre,
    rfl, rfl, rfl, freshKernelCode_bytes, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, htargetCanonical, hnewCanonical, ?_, ?_⟩
  · simpa only [freshKernelPre, Devm.memory_setMach] using hwf
  · simpa only [freshKernelPre, Devm.memory_setMach, freshKernelImage]
      using hreads
  · simpa only [freshKernelPre, Devm.memory_setMach, hsize]
  · simpa only [freshKernelPre, Devm.memory_setMach] using halign
  · simpa only [freshKernelPre, Devm.memory_setMach] using htarget
  · simpa only [freshKernelPre, Devm.memory_setMach] using hnew
  · simpa only [freshKernelPre, Devm.memory_setMach] using hcontinuation
  · simpa only [freshLogicalStorageOfStor] using freshKernel_entryWitness
  · rfl
  · rcases freshKernelRun with ⟨post, run⟩
    rcases freshKernel_tableEntry with ⟨loc, htable⟩
    have hcompiled :
        some freshKernelSevm.code.toList =
          Prog.compile (runtime officialParams) := by
      rw [freshKernelCode_bytes, lidoCircuitBreakerCode_compile]
    have hsub := (subcode_of_get?_eq_some hcompiled htable).2
    have hnopush := (Prog.jumpable_of_get?_table hcompiled htable).2
    rcases Func.exec_of_runCompiled_core run hcompiled rfl (loc + 1)
        hsub hnopush with ⟨execution⟩
    exact ⟨loc, post, run, execution, htable⟩

set_option maxRecDepth 32768 in
/-- The concrete successful exact-code control instantiates the public
execution-to-source-trace extractor without supplying a trace premise. -/
theorem freshRegistration_extracts_sourceTrace_control :
    ∃ owner sevm pre loc final,
      owner = Nat.toAdr 100 ∧
      sevm.currentTarget = owner ∧
      sevm.codeAddress = some owner ∧
      sevm.code.toList = lidoCircuitBreakerCode officialParams ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor pre owner)) [] ∧
      ∃ _execution : Exec (loc + 1) sevm pre (.ok final),
        (table 0
          ((runtime officialParams).main ::
            (runtime officialParams).aux))[setPauserSlot]? =
            some (loc, setPauserKernel) ∧
        ∃ trace postRegistry postImg,
          setPauserSourceTrace [] 7 9 = some trace ∧
          Mem.Wf postRegistry.memory ∧
          Mem.Reads postRegistry.memory postImg ∧
          Devm.getStor postRegistry owner =
            applyRegistryWrites (Devm.getStor pre owner) trace.writes ∧
          RegistryWitness
            (logicalStorageOfStor (Devm.getStor postRegistry owner))
            trace.postEntries ∧
          Func.Run
            ((runtime officialParams).main ::
              (runtime officialParams).aux)
            sevm postRegistry finishSetPauser final := by
  rcases freshRegistration_exactCode_success_control with
    ⟨owner, sevm, pre, hownerEq, hcurrent, hcodeAddress, hcode, hwf,
      hreads, _hsize, _halign, htargetMemory, hnewMemory,
      hcontinuationMemory, hwEntry, htargetCanonical, hnewCanonical,
      _hmodel, loc, final, _run, execution, htable⟩
  have htargetImage : Bytes.toB256
      (freshKernelImage.sliceD (targetWord * 32).toNat 32 0) = 7 := by
    rw [freshKernelImage]
    rw [← Mem.Reads.read hreads]
    exact htargetMemory
  have hnewImage : Bytes.toB256
      (freshKernelImage.sliceD (newPauserWord * 32).toNat 32 0) = 9 := by
    rw [freshKernelImage]
    rw [← Mem.Reads.read hreads]
    exact hnewMemory
  have hcontinuationImage : Bytes.toB256
      (freshKernelImage.sliceD (continuationWord * 32).toNat 32 0) = 0 := by
    rw [freshKernelImage]
    rw [← Mem.Reads.read hreads]
    exact hcontinuationMemory
  have hwEntry' : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre owner)) [] := by
    simpa [logicalStorageOfStor] using hwEntry
  rcases setPauserKernel_exec_extracts_sourceTrace officialParams
      hcurrent hcodeAddress hcode htable hwf hreads htargetImage hnewImage
      hcontinuationImage hwEntry' htargetCanonical hnewCanonical execution with
    ⟨trace, postRegistry, postImg, htrace, hwfPost, hreadsPost,
      _htargetPost, _hnewPost, _hpreviousPost, _hcontinuationPost,
      hstoragePost, hwPost, hfinish⟩
  exact ⟨owner, sevm, pre, loc, final, hownerEq, hcurrent, hcodeAddress,
    hcode, hwEntry', execution, htable, trace, postRegistry, postImg,
    htrace, hwfPost, hreadsPost, hstoragePost, hwPost, hfinish⟩

end Blanc.LidoCircuitBreaker.RegistrySuccess
