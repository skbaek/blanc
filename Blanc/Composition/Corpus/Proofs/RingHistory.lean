import Blanc.Corpus.Proofs.BeaconRootsClassification
import Blanc.Corpus.Proofs.HistoryStorage
import Blanc.ExecutionKeptPreCalls
import Blanc.ListFold

namespace Blanc.Corpus.Proofs.RingHistory

open Jaune Blanc.Lift Blanc.Corpus.Freeze

namespace R
open Blanc.Corpus.Freeze.BeaconRoots
open Blanc.Lift.SystemExecution.BeaconRoots

private theorem read_silent {b : KeptBlock} (fork : CoveredFork b.fork) (g : Exec.Frame)
    (entry : Exec.Frame.EntryIn addr beaconRootsCode b.benv.stat g) (caller : g.sevm.caller ≠ systemAddress) :
    Devm.getStor g.post addr = Devm.getStor g.pre addr := by
  obtain ⟨orig, entry⟩ := entry
  rcases g with ⟨pc, sevm, pre, out, run, committed⟩
  cases out with
  | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have zero : pc = 0 := entry.pc
    subst pc
    have selected : CoveredFork sevm.benvStat.fork := by rw [entry.benvStat]; exact fork
    obtain ⟨_, _, _, _, state, _⟩ := Blanc.Lift.BeaconRoots.exec_read entry.code selected entry.stack caller run
    exact congrArg (fun s : State => s.getStor addr) state

/-- One actual clean covered step performs precisely the protocol ring write and preserves both code facts. -/
theorem step {cfg : ChainConfig} {b : KeptBlock} {post : BlockChain}
    (h : KeptStep cfg b post) (fork : CoveredFork b.fork)
    (code : b.parent.state.getCode addr = beaconRootsCode)
    (empty : b.parent.state.getCode systemAddress = ByteArray.empty)
    (senders : NoSenderAt systemAddress b.run.senders)
    (authorities : NoAuthorityAt systemAddress b.run.senders)
    (avoid : NoCreateAt systemAddress b.run.roots) :
    post.state.getCode addr = beaconRootsCode ∧ post.state.getCode systemAddress = ByteArray.empty ∧
      storOf post.state addr = write (storOf b.parent.state addr) (blockWrite b).1 (blockWrite b).2 := by
  have call := processUncheckedSystemTransaction_beaconRoots (benv := b.benv) fork code
  obtain ⟨codePost, emptyPost, _, storagePost⟩ := h.beaconRoots_stor fork code empty senders authorities avoid
    call.1 rfl (read_silent fork)
  refine ⟨codePost, emptyPost, ?_⟩
  have value : systemValue b.benv = b.benv.stat.parentBeaconBlockRoot := by
    apply dataWord_of_append (pre := []) (post := []) rfl
    rfl
  funext k
  change (post.state.getStor addr).get k = _
  rw [storagePost, call.2.1, value]
  simp only [State.getStor_setStorVal_self, Stor.get_set_ite]
  change (if rootKey (blockWrite b).1 = k then (blockWrite b).2 else
    if timeKey (blockWrite b).1 = k then (blockWrite b).1 else storOf b.parent.state addr k) = _
  simp only [write, eq_comm]

/-- The complete clean history preserves installation and folds precisely its protocol writes. -/
theorem history {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    (run : KeptHistory cfg start blocks stop) (covered : ∀ b ∈ blocks, CoveredFork b.fork)
    (code : start.state.getCode addr = beaconRootsCode)
    (empty : start.state.getCode systemAddress = ByteArray.empty) (clean : HistoryClean blocks) :
    stop.state.getCode addr = beaconRootsCode ∧ stop.state.getCode systemAddress = ByteArray.empty ∧
      storOf stop.state addr = writeAll (storOf start.state addr) (blocks.map blockWrite) := by
  revert covered clean
  induction run with
  | refl => intro covered clean; exact ⟨code, empty, rfl⟩
  | @step blocks b post prior current ih =>
    intro covered clean
    have old : ∀ x ∈ blocks, x ∈ blocks ++ [b] := fun x hx => List.mem_append_left _ hx
    obtain ⟨codeParent, emptyParent, storageParent⟩ := ih (fun x hx => covered x (old x hx))
      ⟨fun x hx => clean.senders x (old x hx), fun x hx => clean.authorities x (old x hx),
        fun x hx => clean.creates x (old x hx)⟩
    have here : b ∈ blocks ++ [b] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
    obtain ⟨codePost, emptyPost, storagePost⟩ := step current (covered b here) codeParent emptyParent
      (clean.senders b here) (clean.authorities b here) (clean.creates b here)
    refine ⟨codePost, emptyPost, ?_⟩
    rw [storagePost, storageParent, List.map_append, List.map_singleton]
    exact (fold_snoc_of_equations writeAll (fun s p => write s p.1 p.2)
      (fun _ => rfl) (fun _ p _ => by cases p; rfl) _ _ _).symm

private theorem key_ranges (t : B256) :
    (timeKey t).toNat < 8191 ∧ (rootKey t).toNat = 8191 + (timeKey t).toNat := by
  have bound : (timeKey t).toNat < 8191 := by
    rw [timeKey, B256.toNat_mod (by decide)]
    exact Nat.mod_lt _ (by decide)
  refine ⟨bound, ?_⟩
  rw [rootKey, B256.toNat_add, show ring.toNat = 8191 from rfl, Nat.lo_eq_of_lt (by omega)]

private theorem root_time_ne (a b : B256) : rootKey a ≠ timeKey b := by
  intro same
  have eq := congrArg B256.toNat same
  have ka := key_ranges a
  have kb := key_ranges b
  omega

private theorem root_inj {a b : B256} (same : rootKey a = rootKey b) : timeKey a = timeKey b := by
  apply B256.toNat_inj
  have eq := congrArg B256.toNat same
  have ka := key_ranges a
  have kb := key_ranges b
  omega

private theorem read_write_same (s : B256 → B256) (t v : B256) (positive : t ≠ 0) :
    Blanc.Corpus.Freeze.BeaconRoots.read (write s t v) t = some v := by
  have tag : write s t v (timeKey t) = t := by
    unfold write
    rw [ite_eq_right (root_time_ne t t).symm, ite_eq_left rfl]
  have root : write s t v (rootKey t) = v := by
    unfold write
    exact ite_eq_left rfl
  rw [Blanc.Corpus.Freeze.BeaconRoots.read, ite_eq_left ⟨positive, tag⟩, root]

private theorem read_write_other (s : B256 → B256) (t newer v : B256)
    (different : timeKey newer ≠ timeKey t) :
    Blanc.Corpus.Freeze.BeaconRoots.read (write s newer v) t = Blanc.Corpus.Freeze.BeaconRoots.read s t := by
  have roots : rootKey t ≠ rootKey newer := fun same => different (root_inj same.symm)
  have tag : write s newer v (timeKey t) = s (timeKey t) := by
    unfold write
    rw [ite_eq_right (root_time_ne newer t).symm, ite_eq_right different.symm]
  have root : write s newer v (rootKey t) = s (rootKey t) := by
    unfold write
    rw [ite_eq_right roots, ite_eq_right (root_time_ne t newer)]
  simp only [Blanc.Corpus.Freeze.BeaconRoots.read, tag, root]

private theorem read_writeAll_other (s : B256 → B256) (ws : List (B256 × B256)) (t : B256)
    (different : ∀ p ∈ ws, timeKey p.1 ≠ timeKey t) :
    Blanc.Corpus.Freeze.BeaconRoots.read (writeAll s ws) t = Blanc.Corpus.Freeze.BeaconRoots.read s t := by
  induction ws generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [writeAll, ih (write s p.1 p.2) (fun q hq => different q (List.mem_cons_of_mem p hq))]
    exact read_write_other s t p.1 p.2 (different p (List.mem_cons_self))

/-- A positive ring write reads back unless a later timestamp uses the same timestamp index. -/
theorem read_writeAll (s : B256 → B256) (ws : List (B256 × B256))
    (i : Nat) (hi : i < ws.length) (positive : ws[i].1 ≠ 0)
    (different : ∀ j (hj : j < ws.length), i < j → timeKey ws[j].1 ≠ timeKey ws[i].1) :
    Blanc.Corpus.Freeze.BeaconRoots.read (writeAll s ws) ws[i].1 = some ws[i].2 := by
  induction ws generalizing s i with
  | nil => cases hi
  | cons p ps ih =>
    cases i with
    | zero =>
      change Blanc.Corpus.Freeze.BeaconRoots.read (writeAll (write s p.1 p.2) ps) p.1 = some p.2
      rw [read_writeAll_other]
      · exact read_write_same s p.1 p.2 positive
      · intro q hq
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
        exact different (j + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hj) (by omega)
    | succ i =>
      exact ih (write s p.1 p.2) i (Nat.lt_of_succ_lt_succ hi) positive
        (fun j hj later => different (j + 1) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ later))

/-- Exact frozen R-S3, including the non-overwritten positive timestamp's read-back. -/
theorem r_s3 : R_S3 := by
  intro cfg start stop blocks run covered code empty clean
  have storage := (history run covered code empty clean).2.2
  refine ⟨storage, ?_⟩
  intro i hi positive different
  rw [storage]
  have result := read_writeAll (storOf start.state addr) (blocks.map blockWrite) i
    (by simpa only [List.length_map] using hi)
  simp only [List.getElem_map] at result
  exact result positive (fun j hj later => different j
    (by simpa only [List.length_map] using hj) later)

end R

namespace H
open Blanc.Corpus.Freeze.HistoryStorage
open Blanc.Lift.SystemExecution.HistoryStorage

private theorem read_silent {b : KeptBlock} (fork : CoveredFork b.fork) (g : Exec.Frame)
    (entry : Exec.Frame.EntryIn addr historyStorageCode b.benv.stat g) (caller : g.sevm.caller ≠ systemAddress) :
    Devm.getStor g.post addr = Devm.getStor g.pre addr := by
  obtain ⟨orig, entry⟩ := entry
  rcases g with ⟨pc, sevm, pre, out, run, committed⟩
  cases out with
  | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have zero : pc = 0 := entry.pc
    subst pc
    have selected : CoveredFork sevm.benvStat.fork := by rw [entry.benvStat]; exact fork
    obtain ⟨_, _, _, _, state, _⟩ := Blanc.Lift.HistoryStorage.exec_read_frame
      entry.code selected entry.stack entry.dataLength caller run
    exact congrArg (fun s : State => s.getStor addr) state

/-- One actual clean covered step writes its parent hash into the numbered history slot. -/
theorem step {cfg : ChainConfig} {b : KeptBlock} {post : BlockChain}
    (h : KeptStep cfg b post) (fork : CoveredFork b.fork)
    (code : b.parent.state.getCode addr = historyStorageCode)
    (empty : b.parent.state.getCode systemAddress = ByteArray.empty)
    (senders : NoSenderAt systemAddress b.run.senders)
    (authorities : NoAuthorityAt systemAddress b.run.senders)
    (avoid : NoCreateAt systemAddress b.run.roots) :
    post.state.getCode addr = historyStorageCode ∧ post.state.getCode systemAddress = ByteArray.empty ∧
      storOf post.state addr = write (storOf b.parent.state addr) (blockWrite b).1 (blockWrite b).2 := by
  have callStep : ∀ {beacon : State}, beacon.getCode addr = historyStorageCode →
      beacon.getStor addr = b.parent.state.getStor addr →
      ∃ stHist outHist,
        processUncheckedSystemTransaction (b.benv.withState beacon) addr b.block.header.parentHash.toBytes =
          .ok (stHist, outHist) ∧ outHist.error = none ∧
        stHist.getStor addr = (b.parent.state.getStor addr).set
          ((b.block.header.number.toB256 - 1) % 0x1fff) b.block.header.parentHash := by
    intro beacon codeBeacon same
    have call := processUncheckedSystemTransaction_historyStorage (benv := b.benv.withState beacon)
      fork codeBeacon h.lastBlockHash.1
    refine ⟨_, _, call.1, rfl, ?_⟩
    have value : systemValue (b.benv.withState beacon) = b.block.header.parentHash := by
      apply dataWord_of_append (pre := []) (post := []) rfl
      change (b.benv.stat.blockHashes.getLast?.getD 0).toBytes = _
      rw [h.lastBlockHash.1]
      rfl
    rw [call.2.1, value, State.getStor_setStorVal_self]
    change (beacon.getStor addr).set ((b.block.header.number.toB256 - 1) % 0x1fff) b.block.header.parentHash = _
    rw [same]
  obtain ⟨codePost, emptyPost, _, storagePost⟩ := h.historyStorage_stor fork code empty senders authorities avoid
    (read_silent fork) callStep
  refine ⟨codePost, emptyPost, ?_⟩
  funext k
  change (post.state.getStor addr).get k = _
  rw [storagePost, Stor.get_set_ite]
  change (if key (blockWrite b).1 = k then (blockWrite b).2 else storOf b.parent.state addr k) = _
  simp only [write, eq_comm]

/-- The history-storage fold retains root contents and applies only its block-header writes. -/
theorem history {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    (run : KeptHistory cfg start blocks stop) (covered : ∀ b ∈ blocks, CoveredFork b.fork)
    (code : start.state.getCode addr = historyStorageCode)
    (empty : start.state.getCode systemAddress = ByteArray.empty) (clean : HistoryClean blocks) :
    stop.state.getCode addr = historyStorageCode ∧ stop.state.getCode systemAddress = ByteArray.empty ∧
      storOf stop.state addr = writeAll (storOf start.state addr) (blocks.map blockWrite) := by
  revert covered clean
  induction run with
  | refl => intro covered clean; exact ⟨code, empty, rfl⟩
  | @step blocks b post prior current ih =>
    intro covered clean
    have old : ∀ x ∈ blocks, x ∈ blocks ++ [b] := fun x hx => List.mem_append_left _ hx
    obtain ⟨codeParent, emptyParent, storageParent⟩ := ih (fun x hx => covered x (old x hx))
      ⟨fun x hx => clean.senders x (old x hx), fun x hx => clean.authorities x (old x hx),
        fun x hx => clean.creates x (old x hx)⟩
    have here : b ∈ blocks ++ [b] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
    obtain ⟨codePost, emptyPost, storagePost⟩ := step current (covered b here) codeParent emptyParent
      (clean.senders b here) (clean.authorities b here) (clean.creates b here)
    refine ⟨codePost, emptyPost, ?_⟩
    rw [storagePost, storageParent, List.map_append, List.map_singleton]
    exact (fold_snoc_of_equations writeAll (fun s p => write s p.1 p.2)
      (fun _ => rfl) (fun _ p _ => by cases p; rfl) _ _ _).symm

/-- Exact frozen H-S3, without an added storage or entry premise. -/
theorem h_s3 : H_S3 := by
  intro cfg start stop blocks run covered code empty clean
  exact (history run covered code empty clean).2.2

end H
end Blanc.Corpus.Proofs.RingHistory
