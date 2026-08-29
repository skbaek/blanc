import Blanc.BeaconDepositInsert
import Blanc.ForwardStorageAccess

/-!
# Beacon deposit insertion-loop iteration

Machine-word state, exact dead-prefix gas, and the carrier used to compose the
branch reads and SHA-256 calls before the first live insertion bit.  The
terminal live store remains a separate selected-cost step.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- The machine-visible state at one insertion-loop entry. -/
structure InsertionLoopState where
  height : B256
  size : B256
  node : B256
  keys : KeySet

/-- The low bit selects the terminal live store exactly when nonzero. -/
def InsertionLoopState.live (s : InsertionLoopState) : Prop :=
  ((1 : B256) &&& s.size) ≠ 0

instance instDecidableInsertionLoopStateLive
    (s : InsertionLoopState) : Decidable s.live := by
  unfold InsertionLoopState.live
  infer_instance

/-- The branch key read by a dead step or written by the live step. -/
def InsertionLoopState.key (s : InsertionLoopState) : B256 :=
  branchBase + s.height

/-- Access-set update performed by one selected branch `SLOAD`. -/
def insertionReadKeys (owner : Adr) (keys : KeySet)
    (key : B256) : KeySet :=
  sloadAccessedStorageKeys owner keys key

/-- Warm/cold charge performed by one selected branch `SLOAD`. -/
def insertionReadGas (owner : Adr) (keys : KeySet)
    (key : B256) : Nat :=
  sloadCostOfKeys owner keys key

/-- One machine-word dead insertion step. -/
def InsertionLoopState.step (owner : Adr) (stor : Stor)
    (s : InsertionLoopState) : InsertionLoopState :=
  { height := s.height + 1
    size := s.size >>> 1
    node := hashPair Bytes.sha256 (stor.get s.key) s.node
    keys := insertionReadKeys owner s.keys s.key }

/-- Iterate exactly `n` dead insertion steps. -/
def insertionLoopIter (owner : Adr) (stor : Stor) :
    Nat → InsertionLoopState → InsertionLoopState
  | 0, s => s
  | n + 1, s => insertionLoopIter owner stor n (s.step owner stor)

/-- Exact cost of one dead loop entry through the next loop entry. -/
def insertionDeadStepGas (owner : Adr) (s : InsertionLoopState) : Nat :=
  336 + insertionReadGas owner s.keys s.key

/-- Exact cost of `n` dead entries, excluding the terminal live store. -/
def insertionDeadGas (owner : Adr) (stor : Stor) :
    Nat → InsertionLoopState → Nat
  | 0, _ => 0
  | n + 1, s =>
      insertionDeadStepGas owner s +
        insertionDeadGas owner stor n (s.step owner stor)

/-- Every requested prefix entry has a clear low bit. -/
def InsertionLoopDead (owner : Adr) (stor : Stor) :
    Nat → InsertionLoopState → Prop
  | 0, _ => True
  | n + 1, s => ¬ s.live ∧
      InsertionLoopDead owner stor n (s.step owner stor)

/-- State and symbolic-memory preservation threaded across dead iterations. -/
structure InsertionLoopCarrier (origin base : Devm) (memory : Mem)
    (oldCount : B256) (s : InsertionLoopState) : Type where
  mem : InsertionMemoryCarrier memory oldCount s.size s.node
  stor : ∀ a, Devm.getStor base a = Devm.getStor origin a
  code : ∀ a, base.getCode a = origin.getCode a
  addresses : base.accessedAddresses = origin.accessedAddresses
  keys : base.accessedStorageKeys = s.keys
  logs : base.logs = origin.logs
  output : base.output = origin.output
  error : base.error = origin.error

/-- Selected warm/cold charge of the terminal branch write, phrased entirely
over the predicted loop state and the unchanged pre-insertion storage. -/
def insertionStoreCost (sevm : Sevm) (stor : Stor)
    (s : InsertionLoopState) : Nat :=
  (if (⟨sevm.currentTarget, s.key⟩ : Adr × B256) ∈ s.keys then 0
    else gasColdSload) +
  sstoreValueCost (getOrigStorVal sevm sevm.currentTarget s.key)
    (stor.get s.key) s.node

theorem insertionStoreCost_eq_sstoreCost
    {sevm : Sevm} {origin base : Devm} {memory : Mem}
    {oldCount : B256} {s : InsertionLoopState} {stor : Stor}
    (carrier : InsertionLoopCarrier origin base memory oldCount s)
    (horiginStor : Devm.getStor origin sevm.currentTarget = stor) :
    insertionStoreCost sevm stor s =
      sstoreCost sevm base s.key s.node := by
  have hcurrent :
      base.getStorVal sevm.currentTarget s.key = stor.get s.key := by
    change (Devm.getStor base sevm.currentTarget).get s.key = stor.get s.key
    rw [carrier.stor, horiginStor]
  simp only [insertionStoreCost, sstoreCost, carrier.keys, hcurrent]

@[simp] theorem insertionReadGas_eq_sloadCost
    (sevm : Sevm) (base : Devm) (key : B256) :
    insertionReadGas sevm.currentTarget base.accessedStorageKeys key =
      sloadCost sevm base key := rfl

@[simp] theorem afterSload_accessedStorageKeys_insertion
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).accessedStorageKeys =
      insertionReadKeys sevm.currentTarget base.accessedStorageKeys key := by
  simpa only [insertionReadKeys] using
    Blanc.afterSload_accessedStorageKeys sevm base key

theorem insertionDeadStepGas_ge (owner : Adr) (s : InsertionLoopState) :
    436 ≤ insertionDeadStepGas owner s := by
  unfold insertionDeadStepGas insertionReadGas sloadCostOfKeys
  split <;> simp only [gasWarmAccess, gasColdSload] <;> omega

private lemma insertionFold_getStor_setMach
    {base : Devm} {mach : Mach} {a : Adr} :
    Devm.getStor (base.setMach mach) a = Devm.getStor base a := rfl

private lemma insertionFold_getCode_setMach
    {base : Devm} {mach : Mach} {a : Adr} :
    (base.setMach mach).getCode a = base.getCode a := rfl

private lemma insertionFold_accessedAddresses_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).accessedAddresses = base.accessedAddresses := rfl

private lemma insertionFold_accessedStorageKeys_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).accessedStorageKeys =
      base.accessedStorageKeys := rfl

private lemma insertionFold_logs_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).logs = base.logs := rfl

private lemma insertionFold_output_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).output = base.output := rfl

private lemma insertionFold_error_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).error = base.error := rfl

private def insertionLoopCarrier_step
    {sevm : Sevm} {origin base callPost : Devm}
    {memory : Mem} {oldCount : B256} {s : InsertionLoopState}
    {stor : Stor}
    (carrier : InsertionLoopCarrier origin base memory oldCount s)
    (hmem : InsertionMemoryCarrier callPost.memory oldCount s.size
      (hashPair Bytes.sha256 (stor.get s.key) s.node))
    (hstorage : ∀ a, Devm.getStor callPost a =
      Devm.getStor (afterSload sevm base s.key) a)
    (hcode : ∀ a, callPost.getCode a =
      (afterSload sevm base s.key).getCode a)
    (haddresses : callPost.accessedAddresses =
      (afterSload sevm base s.key).accessedAddresses)
    (hkeys : callPost.accessedStorageKeys =
      (afterSload sevm base s.key).accessedStorageKeys)
    (hlogs : callPost.logs = (afterSload sevm base s.key).logs)
    (houtput : callPost.output = (afterSload sevm base s.key).output)
    (herror : callPost.error = (afterSload sevm base s.key).error) :
    InsertionLoopCarrier origin callPost
      (callPost.memory.write 608 (s.size >>> 1).toBytes)
      oldCount (s.step sevm.currentTarget stor) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [InsertionLoopState.step] using
      hmem.writeShiftedSize (s.size >>> 1)
  · intro a
    rw [hstorage, Blanc.afterSload_getStor, carrier.stor]
  · intro a
    rw [hcode, Blanc.afterSload_getCode, carrier.code]
  · rw [haddresses, Blanc.afterSload_accessedAddresses,
      carrier.addresses]
  · rw [hkeys, afterSload_accessedStorageKeys_insertion, carrier.keys]
    rfl
  · rw [hlogs, Blanc.afterSload_logs, carrier.logs]
  · rw [houtput, Blanc.afterSload_output, carrier.output]
  · rw [herror, Blanc.afterSload_error, carrier.error]

/-- Exact existential CPS composition of any dead insertion prefix. -/
theorem insertionLoop_dead_iterations_exists_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {memory : Mem} {oldCount : B256} {s : InsertionLoopState}
    {stor : Stor} {n K : Nat} {P : Execution → Prop}
    (carrier : InsertionLoopCarrier origin base memory oldCount s)
    (horiginStor : Devm.getStor origin sevm.currentTarget = stor)
    (hdead : InsertionLoopDead sevm.currentTarget stor n s)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      K + insertionDeadGas sevm.currentTarget stor n s < 2 ^ 256)
    (hinsertionContinuation :
      fs[insertionContinuationSlot]? = some insertionContinuation)
    (hinsertionLoop : fs[insertionLoopSlot]? = some insertionLoop)
    (htail :
      ∀ {base' : Devm} {memory' : Mem},
        InsertionLoopCarrier origin base' memory' oldCount
          (insertionLoopIter sevm.currentTarget stor n s) →
        ∃ ex, P ex ∧
          Func.RunCompiledTo fs sevm
            (base'.setMach
              ⟨[(insertionLoopIter sevm.currentTarget stor n s).height],
                memory', K⟩)
            insertionLoop ex) :
    ∃ ex, P ex ∧
      Func.RunCompiledTo fs sevm
        (base.setMach
          ⟨[s.height], memory,
            K + insertionDeadGas sevm.currentTarget stor n s⟩)
        insertionLoop ex := by
  induction n generalizing base memory s with
  | zero =>
      simpa only [insertionLoopIter, insertionDeadGas, Nat.add_zero] using
        htail carrier
  | succ n ih =>
      change ¬ s.live ∧
        InsertionLoopDead sevm.currentTarget stor n
          (s.step sevm.currentTarget stor) at hdead
      rcases hdead with ⟨hdeadNow, hdeadNext⟩
      let next := s.step sevm.currentTarget stor
      let tailGas :=
        insertionDeadGas sevm.currentTarget stor n next
      have htotal :
          K + insertionDeadStepGas sevm.currentTarget s +
            insertionDeadGas sevm.currentTarget stor n next < 2 ^ 256 := by
        simpa only [insertionDeadGas, Nat.add_assoc, next] using hbound
      have hnextBound :
          K + insertionDeadGas sevm.currentTarget stor n next < 2 ^ 256 := by
        have hstep := insertionDeadStepGas_ge sevm.currentTarget s
        omega
      have hshaBound : K + tailGas + 269 < 2 ^ 256 := by
        have hstep := insertionDeadStepGas_ge sevm.currentTarget s
        dsimp only [tailGas]
        omega
      have hval :
          base.getStorVal sevm.currentTarget s.key = stor.get s.key := by
        change (Devm.getStor base sevm.currentTarget).get s.key =
          stor.get s.key
        rw [carrier.stor, horiginStor]
      have hnodelegBase :
          getDelegatedCodeAddress (base.getCode 2) = none := by
        rw [carrier.code]
        exact hnodeleg
      have hwarmBase : (2 : Adr) ∈ base.accessedAddresses := by
        rw [carrier.addresses]
        exact hwarm
      have hbit : ((1 : B256) &&& s.size) = 0 := by
        exact not_ne_iff.mp hdeadNow
      have hkey : s.key = branchBase + s.height := rfl
      let left := stor.get s.key
      let loaded := afterSload sevm base s.key
      let staged :=
        (memory.write 0 left.toBytes).write 32 s.node.toBytes
      let shaBase := loaded.setMach ⟨[], staged, 0⟩
      have hpair : InsertionPairMemoryCarrier shaBase.memory
          oldCount s.size left s.node := by
        simpa only [shaBase, staged, Devm.memory_setMach] using
          (InsertionMemoryCarrier.stagePair
            (left := left) carrier.mem)
      have hnodelegSha :
          getDelegatedCodeAddress (shaBase.getCode 2) = none := by
        simpa only [shaBase, loaded, insertionFold_getCode_setMach,
          Blanc.afterSload_getCode] using hnodelegBase
      have hwarmSha : (2 : Adr) ∈ shaBase.accessedAddresses := by
        change (2 : Adr) ∈ loaded.accessedAddresses
        dsimp only [loaded]
        rw [Blanc.afterSload_accessedAddresses]
        exact hwarmBase
      obtain ⟨callPost, _hstack, _hmemory, hcallMemNE,
          _hgas, _hreturn, hstorage, hcode, haddresses, hkeys,
          hlogs, houtput, herror, hlift⟩ :=
        insertionShaTail_runCompiledTo
          (fs := fs) (sevm := sevm) (base := shaBase)
          (height := s.height) (K := K + tailGas)
          hpair hnodelegSha hwarmSha hpre hdepth hshaBound
          hinsertionContinuation hinsertionLoop
      rcases hcallMemNE with ⟨hcallMem⟩
      have hcallMem' :
          InsertionMemoryCarrier callPost.memory oldCount s.size
            (hashPair Bytes.sha256 (stor.get s.key) s.node) := by
        simpa only [left] using hcallMem
      have hstorage' : ∀ a, Devm.getStor callPost a =
          Devm.getStor loaded a := by
        intro a
        simpa only [shaBase, insertionFold_getStor_setMach] using
          hstorage a
      have hcode' : ∀ a, callPost.getCode a = loaded.getCode a := by
        intro a
        simpa only [shaBase, insertionFold_getCode_setMach] using hcode a
      have haddresses' :
          callPost.accessedAddresses = loaded.accessedAddresses := by
        simpa only [shaBase, insertionFold_accessedAddresses_setMach] using
          haddresses
      have hkeys' :
          callPost.accessedStorageKeys = loaded.accessedStorageKeys := by
        simpa only [shaBase, insertionFold_accessedStorageKeys_setMach] using
          hkeys
      have hlogs' : callPost.logs = loaded.logs := by
        simpa only [shaBase, insertionFold_logs_setMach] using hlogs
      have houtput' : callPost.output = loaded.output := by
        simpa only [shaBase, insertionFold_output_setMach] using houtput
      have herror' : callPost.error = loaded.error := by
        simpa only [shaBase, insertionFold_error_setMach] using herror
      have nextCarrier : InsertionLoopCarrier origin callPost
          (callPost.memory.write 608 (s.size >>> 1).toBytes)
          oldCount next := by
        dsimp only [next, loaded]
        exact insertionLoopCarrier_step carrier hcallMem'
          hstorage' hcode' haddresses' hkeys' hlogs' houtput' herror'
      obtain ⟨ex, hP, hnextRun⟩ :=
        ih nextCarrier hdeadNext hnextBound (by
          intro base' memory' nextCarrier'
          apply htail
          simpa only [insertionLoopIter, next] using nextCarrier')
      have hnextRun' : Func.RunCompiledTo fs sevm
          (callPost.setMach
            ⟨[s.height + 1],
              callPost.memory.write 608 (s.size >>> 1).toBytes,
              K + tailGas⟩)
          insertionLoop ex := by
        simpa only [tailGas, next, InsertionLoopState.step] using hnextRun
      have hshaRun := hlift hnextRun'
      have hvalDead :
          base.getStorVal sevm.currentTarget
            (branchBase + s.height) = left := by
        dsimp only [left]
        rw [← hkey]
        exact hval
      have hstage : Func.RunCompiledTo fs sevm
          (base.setMach
            ⟨[s.height], memory,
              (K + tailGas + 285) + 51 +
                sloadCost sevm base (branchBase + s.height)⟩)
          insertionLoop ex := by
        apply insertionLoopDead_runCompiledTo
          carrier.mem hbit hvalDead
          (by simp only [List.length_nil]; omega)
        simpa only [shaBase, loaded, staged, hkey,
          Devm.setMach_setMach, Devm.memory_setMach] using hshaRun
      have hcost :
          sloadCost sevm base (branchBase + s.height) =
            insertionReadGas sevm.currentTarget s.keys s.key := by
        rw [← hkey, ← insertionReadGas_eq_sloadCost, carrier.keys]
      have hgas :
          (K + tailGas + 285) + 51 +
              sloadCost sevm base (branchBase + s.height) =
            K + insertionDeadGas sevm.currentTarget stor (n + 1) s := by
        rw [hcost]
        dsimp only [tailGas, next]
        simp only [insertionDeadGas, insertionDeadStepGas]
        omega
      rw [hgas] at hstage
      exact ⟨ex, hP, hstage⟩

/-- Fixed-outcome compatibility corollary of the existential CPS carrier. -/
theorem insertionLoop_dead_iterations_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {memory : Mem} {oldCount : B256} {s : InsertionLoopState}
    {stor : Stor} {n K : Nat} {ex : Execution}
    (carrier : InsertionLoopCarrier origin base memory oldCount s)
    (horiginStor : Devm.getStor origin sevm.currentTarget = stor)
    (hdead : InsertionLoopDead sevm.currentTarget stor n s)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      K + insertionDeadGas sevm.currentTarget stor n s < 2 ^ 256)
    (hinsertionContinuation :
      fs[insertionContinuationSlot]? = some insertionContinuation)
    (hinsertionLoop : fs[insertionLoopSlot]? = some insertionLoop)
    (htail :
      ∀ {base' : Devm} {memory' : Mem},
        InsertionLoopCarrier origin base' memory' oldCount
          (insertionLoopIter sevm.currentTarget stor n s) →
        Func.RunCompiledTo fs sevm
          (base'.setMach
            ⟨[(insertionLoopIter sevm.currentTarget stor n s).height],
              memory', K⟩)
          insertionLoop ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[s.height], memory,
          K + insertionDeadGas sevm.currentTarget stor n s⟩)
      insertionLoop ex := by
  obtain ⟨ex', hex, hrun⟩ :=
    insertionLoop_dead_iterations_exists_runCompiledTo
      (P := fun ex' => ex' = ex) carrier horiginStor hdead
      hnodeleg hwarm hpre hdepth hbound
      hinsertionContinuation hinsertionLoop
      (by
        intro base' memory' hcarrier
        exact ⟨ex, rfl, htail hcarrier⟩)
  subst ex'
  exact hrun

/-- Compose a dead prefix with its terminal live store.  The final carrier is
exposed so downstream proofs can classify the one branch write exactly. -/
theorem insertionLoop_deadThenLive_exists_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {memory : Mem} {oldCount : B256} {s : InsertionLoopState}
    {stor : Stor} {n G : Nat}
    (carrier : InsertionLoopCarrier origin base memory oldCount s)
    (horiginStor : Devm.getStor origin sevm.currentTarget = stor)
    (hdead : InsertionLoopDead sevm.currentTarget stor n s)
    (hfinalLive :
      (insertionLoopIter sevm.currentTarget stor n s).live)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G + 2 +
      insertionStoreCost sevm stor
        (insertionLoopIter sevm.currentTarget stor n s))
    (hbound :
      (G + 46 + insertionStoreCost sevm stor
          (insertionLoopIter sevm.currentTarget stor n s)) +
        insertionDeadGas sevm.currentTarget stor n s < 2 ^ 256)
    (hinsertionContinuation :
      fs[insertionContinuationSlot]? = some insertionContinuation)
    (hinsertionLoop : fs[insertionLoopSlot]? = some insertionLoop) :
    ∃ finalBase finalMemory,
      Nonempty (InsertionLoopCarrier origin finalBase finalMemory oldCount
        (insertionLoopIter sevm.currentTarget stor n s)) ∧
      Func.RunCompiledTo fs sevm
        (base.setMach
          ⟨[s.height], memory,
            (G + 46 + insertionStoreCost sevm stor
                (insertionLoopIter sevm.currentTarget stor n s)) +
              insertionDeadGas sevm.currentTarget stor n s⟩)
        insertionLoop
        (.ok ((afterSstore sevm finalBase
          (insertionLoopIter sevm.currentTarget stor n s).key
          (insertionLoopIter sevm.currentTarget stor n s).node).setMach
            ⟨[], finalMemory, G⟩)) := by
  let final := insertionLoopIter sevm.currentTarget stor n s
  let terminalGas := G + 46 + insertionStoreCost sevm stor final
  obtain ⟨ex, hfinal, hrun⟩ :=
    insertionLoop_dead_iterations_exists_runCompiledTo
      (P := fun ex => ∃ finalBase finalMemory,
        Nonempty (InsertionLoopCarrier origin finalBase finalMemory
          oldCount final) ∧
        ex = .ok ((afterSstore sevm finalBase final.key final.node).setMach
          ⟨[], finalMemory, G⟩))
      (K := terminalGas) carrier horiginStor hdead
      hnodeleg hwarm hpre hdepth
      (by simpa only [terminalGas, final] using hbound)
      hinsertionContinuation hinsertionLoop
      (by
        intro finalBase finalMemory finalCarrier
        have hcost :=
          insertionStoreCost_eq_sstoreCost finalCarrier horiginStor
        have hkey : final.key = branchBase + final.height := rfl
        have hbit : ((1 : B256) &&& final.size) ≠ 0 := by
          change final.live at hfinalLive
          exact hfinalLive
        have hsentryFinal : gCallStipend < G + 2 +
            insertionStoreCost sevm stor final := by
          simpa only [final] using hsentry
        rw [hcost, hkey] at hsentryFinal
        have hsentry' : gCallStipend < G + 2 +
            sstoreCost sevm finalBase
              (branchBase + final.height) final.node := by
          exact hsentryFinal
        have hlive := insertionLoopLive_runCompiledTo
          (fs := fs) (sevm := sevm) (base := finalBase)
          (K := G) finalCarrier.mem hbit hsentry' hstatic
        have hcost' :
            sstoreCost sevm finalBase
                (branchBase + final.height) final.node =
              insertionStoreCost sevm stor final := by
          rw [← hkey, ← hcost]
        rw [hcost'] at hlive
        refine ⟨.ok ((afterSstore sevm finalBase final.key final.node).setMach
            ⟨[], finalMemory, G⟩),
          ⟨finalBase, finalMemory, ⟨finalCarrier⟩, rfl⟩, ?_⟩
        simpa only [terminalGas, final, hkey] using hlive)
  rcases hfinal with ⟨finalBase, finalMemory, ⟨finalCarrier⟩, rfl⟩
  exact ⟨finalBase, finalMemory, ⟨finalCarrier⟩,
    by simpa only [terminalGas, final] using hrun⟩

end Blanc.BeaconDeposit
