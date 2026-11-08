import Blanc.Lift.SystemExecution.ConsolidationRequest.AmsterdamSystem
import Blanc.Lift.RequestSystem.CoveredCall
import Blanc.MemoryWindows

/-!
# The EIP-7251 system call on the covered forks

The runtime's system path is the fork-free `SysPath` instance of
`Blanc/Lift/SystemExecution/ConsolidationRequest/AmsterdamSystem.lean` (`sysPath`, `sysMemory`): its record
body and excess arm read storage and write memory only, so the same walk serves every fork. Here it is
taken through the covered forks' checked system call (`CoveredSysCall.spec`), and its return window is read
as records.

* `system_call_ok`: with the canonical code installed, from any storage, the checked system call succeeds
  with no error, its post state is `sysState`, it spends at most 114,177 gas, and it returns the first
  `min(2, tail - head)` records, 116 bytes each.
* `system_call_storage`: on storage holding the queue pointers and the excess and count as numbers, with
  no word wrap in the excess, the storage update is the EIP's bookkeeping, read as numbers.

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.
-/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open RequestSystem
open SystemExecution.ConsolidationRequest.Amsterdam (sysPath sysMemory sysShape recordKey recordStage
  recordStage_eq)

/-! ## The return window -/

/-- The bytes one record returns, from the storage read: the source address (the top 20 bytes of its
shifted word), then the three stored calldata words. -/
def recordBytes (rd : B256 → B256) (h i : B256) : Bytes :=
  (rd (recordKey h i) <<< 96).toBytes.sliceD 0 20 0 ++ (rd (1 + recordKey h i)).toBytes ++
    (rd (2 + recordKey h i)).toBytes ++ (rd (3 + recordKey h i)).toBytes

/-- The runtime's output: each record extends the return window by 116 bytes. -/
def sysOutput : SysOutput sysPath sysMemory where
  record := recordBytes
  extend := fun rd h i image hi => by
    have hi' : i < 2 := hi
    show ((recordStage rd h i.toB256).applyImage image).sliceD 0 (116 * (i + 1)) 0 =
      image.sliceD 0 (116 * i) 0 ++ recordBytes rd h i.toB256
    rw [recordStage_eq hi' rd h]
    generalize hS : [(116 * i, (rd (recordKey h i.toB256) <<< 96).toBytes),
       (20 + 116 * i, (rd (1 + recordKey h i.toB256)).toBytes),
       (52 + 116 * i, (rd (2 + recordKey h i.toB256)).toBytes),
       (84 + 116 * i, (rd (3 + recordKey h i.toB256)).toBytes)] = S
    have w0 : (MemoryStage.applyImage S image).sliceD (116 * i) 20 0 =
        (rd (recordKey h i.toB256) <<< 96).toBytes.sliceD 0 20 0 := by
      subst hS
      refine window_at 0 image rfl ?_ (by omega) (by simp only [B256.length_toBytes]; omega)
      avoids_tac
    have w1 : (MemoryStage.applyImage S image).sliceD (116 * i + 20) 32 0 =
        (rd (1 + recordKey h i.toB256)).toBytes := by
      subst hS
      refine (window_at 1 image rfl ?_ (d := 0) (by omega)
        (by simp only [B256.length_toBytes]; omega)).trans (sliceD_self _ (B256.length_toBytes _))
      avoids_tac
    have w2 : (MemoryStage.applyImage S image).sliceD (116 * i + 20 + 32) 32 0 =
        (rd (2 + recordKey h i.toB256)).toBytes := by
      subst hS
      refine (window_at 2 image rfl ?_ (d := 0) (by omega)
        (by simp only [B256.length_toBytes]; omega)).trans (sliceD_self _ (B256.length_toBytes _))
      avoids_tac
    have w3 : (MemoryStage.applyImage S image).sliceD (116 * i + 20 + 32 + 32) 32 0 =
        (rd (3 + recordKey h i.toB256)).toBytes := by
      subst hS
      refine (window_at 3 image rfl ?_ (d := 0) (by omega)
        (by simp only [B256.length_toBytes]; omega)).trans (sliceD_self _ (B256.length_toBytes _))
      avoids_tac
    have pre : (MemoryStage.applyImage S image).sliceD 0 (116 * i) 0 = image.sliceD 0 (116 * i) 0 := by
      subst hS
      apply MemoryStage.applyImage_sliceD_of_avoids
      avoids_tac
    rw [show 116 * (i + 1) = 116 * i + (20 + (32 + (32 + 32))) by omega, List.sliceD_split, Nat.zero_add,
      List.sliceD_split, List.sliceD_split, List.sliceD_split, pre, w0, w1, w2, w3]
    simp only [recordBytes, List.append_assoc]

/-- A record's first key at a queue position, in naturals: `4 + 4 * position`, modulo the word. -/
theorem recordKey_toB256 (h i : Nat) : recordKey h.toB256 i.toB256 = (4 + 4 * (h + i)).toB256 := by
  unfold recordKey
  rw [Nat.toB256_add_toB256, show (4 : B256) = (4 : Nat).toB256 from rfl, Nat.toB256_mul_toB256,
    Nat.toB256_add_toB256, Nat.add_comm i h]

/-! ## The call -/

/-- The bound on the call's gas on a covered fork: two records of four reads and four writes, four more
reads, four stores each priced as a cold first set, the allocation's expansion. -/
theorem frameBound_eq : sysPath.frameBoundOn sysMemory.alloc (gasColdSload + gasStorageSet) = 114177 := by
  decide

/-- The canonical address and code are a system contract. -/
theorem member : (consolidationRequestPredeployAddress, consolidationRequestCode) ∈ systemContracts := by
  unfold systemContracts
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The runtime's system call facts on the covered forks. -/
def sysCall : CoveredSysCall sysPath where
  memory := sysMemory
  target := consolidationRequestPredeployAddress
  bound := 114177
  member := member
  bound_le := Nat.le_of_eq frameBound_eq
  room := by decide

/-- The records a call returns, from the storage it reads: the first `count` from the head. -/
def drained (rd : B256 → B256) : Bytes :=
  sysOutput.drained rd (rd 2) (drainCount sysShape.cap.word (rd 2) (rd 3)).toNat

/-- **The EIP-7251 system call succeeds on every covered fork, from any storage.** With the canonical code
installed, the checked system call returns with no error; its post state is `sysState` (pointers, excess
and count updated as the bytes define, nothing else); it spends at most 114,177 of its 30,000,000 gas; and
it returns the drained records, 116 bytes each. There is no storage premise. -/
theorem system_call_ok {benv : Benv} (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode) :
    ∃ out, processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] =
        .ok (sysState sysShape benv.state consolidationRequestPredeployAddress, out) ∧
      out.error = none ∧ RegularGasWithin out.gasLeft 114177 ∧
      out.returnData = drained (storOf benv.state consolidationRequestPredeployAddress) :=
  let h := sysCall.spec fork installed
  ⟨_, h.1, rfl, h.2, sysOutput.coveredPost_output benv consolidationRequestPredeployAddress⟩

/-! ## The bookkeeping, read as numbers -/

/-- The excess the EIP stores after a call: the stored excess (the inhibitor `2^256 - 1` read as zero)
plus the count, less the per-block target of one, floored at zero. -/
def excessAfter (e n : Nat) : Nat := (if e = 2 ^ 256 - 1 then 0 else e) + n - 1

/-- The records a call takes off a queue of `len`: at most two. -/
def taken (len : Nat) : Nat := min 2 len

theorem drainCount_nat {h t : Nat} (ordered : h ≤ t) (t_lt : t < 2 ^ 256) :
    drainCount sysShape.cap.word h.toB256 t.toB256 = (taken (t - h)).toB256 := by
  have hcap : sysShape.cap.word.toNat = 2 := by decide
  have hdiff : t.toB256 - h.toB256 = (t - h).toB256 := by
    apply B256.toNat_inj
    rw [B256.toNat_sub, B256.toNat_toB256_of_lt t_lt, B256.toNat_toB256_of_lt (by omega),
      B256.toNat_toB256_of_lt (by omega)]
    change (2 ^ 256 + t - h) % 2 ^ 256 = t - h
    omega
  unfold drainCount taken
  rw [hdiff]
  by_cases hlt : t - h < 2
  · have hgt : sysShape.cap.word > (t - h).toB256 := by
      apply B256.lt_iff_toNat_lt_toNat.mpr
      rw [B256.toNat_toB256_of_lt (by omega), hcap]
      exact hlt
    rw [ite_eq_left hgt, Nat.min_eq_right (by omega)]
  · have hgt : ¬ sysShape.cap.word > (t - h).toB256 := by
      intro hg
      have := B256.lt_iff_toNat_lt_toNat.mp hg
      rw [B256.toNat_toB256_of_lt (by omega), hcap] at this
      omega
    rw [ite_eq_right hgt, Nat.min_eq_left (by omega)]
    apply B256.toNat_inj
    rw [hcap]
    rfl

/-- **The EIP-7251 system call's bookkeeping on a covered fork.** On storage whose slots 0 to 3 hold the
excess `e`, the count `n`, the head `h` and the tail `t` with `h ≤ t`, and with no word wrap in the excess
update, the call succeeds as `system_call_ok` says, and its post storage is the EIP's: the excess becomes
`excessAfter e n` (`max(0, e + n - 1)`, the inhibitor read as zero), the count becomes 0, the first
`taken (t - h) = min(2, t - h)` records leave (the head advances by that many, or both pointers reset when
the queue empties), every other slot is unchanged, and the call returns exactly those records, the record at
queue position `q` read from the word keys `4 + 4q` to `4 + 4q + 3` modulo `2 ^ 256`. With `t ≥ 2 ^ 253` such a key
can alias slots 0 to 3; the public `system_call_bookkept` takes the tail below `2 ^ 253` to read records as the
queue. -/
theorem system_call_storage {benv : Benv} (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
    {e n h t : Nat} (he : storOf benv.state consolidationRequestPredeployAddress 0 = e.toB256)
    (hn : storOf benv.state consolidationRequestPredeployAddress 1 = n.toB256)
    (hh : storOf benv.state consolidationRequestPredeployAddress 2 = h.toB256)
    (ht : storOf benv.state consolidationRequestPredeployAddress 3 = t.toB256)
    (e_lt : e < 2 ^ 256) (ordered : h ≤ t) (t_lt : t < 2 ^ 256)
    (noWrap : (if e = 2 ^ 256 - 1 then 0 else e) + n < 2 ^ 256) :
    ∃ σ out, processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] = .ok (σ, out) ∧
      out.error = none ∧ RegularGasWithin out.gasLeft 114177 ∧
      storOf σ consolidationRequestPredeployAddress 0 = (excessAfter e n).toB256 ∧
      storOf σ consolidationRequestPredeployAddress 1 = 0 ∧
      storOf σ consolidationRequestPredeployAddress 2 = (if t - h ≤ 2 then 0 else h + 2).toB256 ∧
      storOf σ consolidationRequestPredeployAddress 3 = (if t - h ≤ 2 then 0 else t).toB256 ∧
      (∀ key : B256, 3 < key.toNat →
        storOf σ consolidationRequestPredeployAddress key =
          storOf benv.state consolidationRequestPredeployAddress key) ∧
      out.returnData = (List.range (taken (t - h))).flatMap fun i =>
        recordBytes (storOf benv.state consolidationRequestPredeployAddress) h.toB256 i.toB256 := by
  obtain ⟨out, hcall, herr, hgas, hret⟩ := system_call_ok fork installed
  refine ⟨_, out, hcall, herr, hgas, ?_⟩
  have hget : ∀ key, storOf (sysState sysShape benv.state consolidationRequestPredeployAddress)
      consolidationRequestPredeployAddress key =
        if (1 : B256) = key then 0
        else if (0 : B256) = key then
          sysShape.next (storOf benv.state consolidationRequestPredeployAddress 0)
            (storOf benv.state consolidationRequestPredeployAddress 1)
        else if storOf benv.state consolidationRequestPredeployAddress 2 +
            drainCount sysShape.cap.word (storOf benv.state consolidationRequestPredeployAddress 2)
              (storOf benv.state consolidationRequestPredeployAddress 3) =
            storOf benv.state consolidationRequestPredeployAddress 3 then
          (if (3 : B256) = key then 0 else if (2 : B256) = key then 0
            else storOf benv.state consolidationRequestPredeployAddress key)
        else (if (2 : B256) = key then storOf benv.state consolidationRequestPredeployAddress 2 +
            drainCount sysShape.cap.word (storOf benv.state consolidationRequestPredeployAddress 2)
              (storOf benv.state consolidationRequestPredeployAddress 3)
          else storOf benv.state consolidationRequestPredeployAddress key) :=
    fun key => sysState_get sysShape benv.state consolidationRequestPredeployAddress key
  generalize hrd : storOf benv.state consolidationRequestPredeployAddress = rd at he hn hh ht hret hget
  have hc : drainCount sysShape.cap.word (rd 2) (rd 3) = (taken (t - h)).toB256 := by
    rw [hh, ht]
    exact drainCount_nat ordered t_lt
  have hnext : sysShape.next (rd 0) (rd 1) = (excessAfter e n).toB256 := by
    rw [he, hn]
    apply B256.toNat_inj
    rw [B256.toNat_toB256_of_lt (by unfold excessAfter; omega)]
    exact plainNext_toNat _ e_lt noWrap
  have hsum : rd 2 + (taken (t - h)).toB256 = (h + taken (t - h)).toB256 := by
    rw [hh, Nat.toB256_add_toB256]
  have hemp : (h + taken (t - h)).toB256 = t.toB256 ↔ t - h ≤ 2 := by
    constructor
    · intro eq
      have := congrArg B256.toNat eq
      rw [B256.toNat_toB256_of_lt (by unfold taken; omega), B256.toNat_toB256_of_lt t_lt] at this
      unfold taken at this
      omega
    · intro le
      unfold taken
      rw [Nat.min_eq_right le, show h + (t - h) = t by omega]
  rw [hc, hsum, ht] at hget
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hget, if_neg (by decide), if_pos rfl, hnext]
  · rw [hget, if_pos rfl]
  · rw [hget, if_neg (by decide), if_neg (by decide)]
    by_cases le : t - h ≤ 2
    · rw [if_pos (hemp.mpr le), if_neg (by decide), if_pos rfl, if_pos le]
      rfl
    · rw [if_neg (fun eq => le (hemp.mp eq)), if_pos rfl, if_neg le]
      unfold taken
      rw [Nat.min_eq_left (by omega)]
  · rw [hget, if_neg (by decide), if_neg (by decide)]
    by_cases le : t - h ≤ 2
    · rw [if_pos (hemp.mpr le), if_pos rfl, if_pos le]
      rfl
    · rw [if_neg (fun eq => le (hemp.mp eq)), if_neg (by decide), if_neg le, ht]
  · intro key hkey
    have hne : ∀ x : B256, x.toNat ≤ 3 → x ≠ key := fun x hx eq => by
      rw [eq] at hx
      omega
    rw [hget, if_neg (hne 1 (by decide)), if_neg (hne 0 (by decide))]
    split
    · rw [if_neg (hne 3 (by decide)), if_neg (hne 2 (by decide))]
    · rw [if_neg (hne 2 (by decide))]
  · rw [hret]
    unfold drained SysOutput.drained
    rw [hh, ht, drainCount_nat ordered t_lt, B256.toNat_toB256_of_lt (by unfold taken; omega)]
    rfl

end Blanc.Lift.ConsolidationRequest
