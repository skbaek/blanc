import Blanc.BeaconDepositRoot
import Blanc.ForwardStorageAccess
import Blanc.WordArithmetic

/-!
# Beacon deposit root-fold iteration

Machine-word state, exact recursive gas, and the carrier used to compose the
32 tail-recursive `rootLoop` iterations.  The separate algebraic bridge below
this layer identifies the word trace with the pure `climb` model once, rather
than reopening word/natural conversions inside every opcode walk.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- The machine-visible state at one `rootLoop` entry. -/
structure RootLoopState where
  height : B256
  size : B256
  node : B256
  keys : KeySet

/-- The low bit selects the live branch exactly when it is nonzero. -/
def RootLoopState.live (s : RootLoopState) : Prop :=
  ((1 : B256) &&& s.size) ≠ 0

instance instDecidableRootLoopStateLive
    (s : RootLoopState) : Decidable s.live := by
  unfold RootLoopState.live
  infer_instance

/-- The storage key read by the selected branch. -/
def RootLoopState.key (s : RootLoopState) : B256 :=
  if s.live then branchBase + s.height else zeroHashBase + s.height

/-- Access-set update performed by one selected SLOAD. -/
def rootReadKeys (owner : Adr) (keys : KeySet) (key : B256) : KeySet :=
  sloadAccessedStorageKeys owner keys key

/-- Warm/cold charge performed by one selected SLOAD. -/
def rootReadGas (owner : Adr) (keys : KeySet) (key : B256) : Nat :=
  sloadCostOfKeys owner keys key

/-- One model-side machine-word root iteration. -/
def RootLoopState.step (owner : Adr) (stor : Stor)
    (s : RootLoopState) : RootLoopState :=
  let key := s.key
  { height := s.height + 1
    size := s.size >>> 1
    node := if s.live then
      hashPair Bytes.sha256 (stor.get key) s.node
    else
      hashPair Bytes.sha256 s.node (stor.get key)
    keys := rootReadKeys owner s.keys key }

/-- Iterate the machine-word state exactly `n` times. -/
def rootLoopIter (owner : Adr) (stor : Stor) :
    Nat → RootLoopState → RootLoopState
  | 0, s => s
  | n + 1, s => rootLoopIter owner stor n (s.step owner stor)

/-- Exact cost of one active loop entry through the next loop entry. -/
def rootLoopStepGas (owner : Adr) (s : RootLoopState) : Nat :=
  (if s.live then 363 else 362) + rootReadGas owner s.keys s.key

/-- Exact cost of `n` active iterations, excluding the terminal dispatch and
`rootFinish`. -/
def rootLoopGas (owner : Adr) (stor : Stor) :
    Nat → RootLoopState → Nat
  | 0, _ => 0
  | n + 1, s =>
      rootLoopStepGas owner s +
        rootLoopGas owner stor n (s.step owner stor)

/-- Every one of the requested entries is still below height 32. -/
def RootLoopActive (owner : Adr) (stor : Stor) :
    Nat → RootLoopState → Prop
  | 0, _ => True
  | n + 1, s =>
      s.height < (32 : B256) ∧
        RootLoopActive owner stor n (s.step owner stor)

/-- State and symbolic-memory preservation threaded across loop iterations. -/
structure RootLoopCarrier (origin base : Devm) (memory : Mem)
    (oldCount : B256) (s : RootLoopState) : Type where
  mem : RootMemoryCarrier memory oldCount s.size s.node
  stor : ∀ a, Devm.getStor base a = Devm.getStor origin a
  code : ∀ a, base.getCode a = origin.getCode a
  addresses : base.accessedAddresses = origin.accessedAddresses
  keys : base.accessedStorageKeys = s.keys
  logs : base.logs = origin.logs
  output : base.output = origin.output
  error : base.error = origin.error

@[simp] theorem rootReadGas_eq_rootSloadCost
    (sevm : Sevm) (base : Devm) (key : B256) :
    rootReadGas sevm.currentTarget base.accessedStorageKeys key =
      sloadCost sevm base key := rfl

@[simp] theorem rootAfterSload_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).accessedStorageKeys =
      rootReadKeys sevm.currentTarget base.accessedStorageKeys key := by
  unfold afterSload rootReadKeys sloadAccessedStorageKeys
  split <;> rfl

@[simp] theorem rootAfterSload_getStor
    (sevm : Sevm) (base : Devm) (key : B256) (address : Adr) :
    Devm.getStor (afterSload sevm base key) address =
      Devm.getStor base address := by
  unfold afterSload
  split <;> rfl

@[simp] theorem rootAfterSload_getCode
    (sevm : Sevm) (base : Devm) (key : B256) (address : Adr) :
    (afterSload sevm base key).getCode address =
      base.getCode address := by
  unfold afterSload
  split <;> rfl

@[simp] theorem rootAfterSload_accessedAddresses
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).accessedAddresses =
      base.accessedAddresses := by
  unfold afterSload
  split <;> rfl

@[simp] theorem rootAfterSload_logs
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).logs = base.logs := by
  unfold afterSload
  split <;> rfl

@[simp] theorem rootAfterSload_output
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).output = base.output := by
  unfold afterSload
  split <;> rfl

@[simp] theorem rootAfterSload_error
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).error = base.error := by
  unfold afterSload
  split <;> rfl

theorem rootLoopStepGas_ge (owner : Adr) (s : RootLoopState) :
    362 ≤ rootLoopStepGas owner s := by
  unfold rootLoopStepGas rootReadGas sloadCostOfKeys
  split <;> split <;> simp only [gasWarmAccess, gasColdSload] <;> omega

/-- Machine-word state at the endpoint's first loop entry. -/
def rootInitialLoopState (base : Devm) (count : B256) : RootLoopState :=
  { height := 0
    size := count
    node := 0
    keys := base.accessedStorageKeys }

/-- The endpoint's initial register image and unchanged world projections form
the first iteration carrier. -/
def rootInitialLoopCarrier (base : Devm) (count : B256) :
    RootLoopCarrier base base (rootInitialMemory count) count
      (rootInitialLoopState base count) :=
  { mem := rootInitialMemory_carrier count
    stor := fun _ => rfl
    code := fun _ => rfl
    addresses := rfl
    keys := rfl
    logs := rfl
    output := rfl
    error := rfl }

private lemma rootFold_getStor_setMach
    {base : Devm} {mach : Mach} {a : Adr} :
    Devm.getStor (base.setMach mach) a = Devm.getStor base a := rfl

private lemma rootFold_accessedAddresses_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).accessedAddresses = base.accessedAddresses := rfl

private lemma rootFold_accessedStorageKeys_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).accessedStorageKeys =
      base.accessedStorageKeys := rfl

private lemma rootFold_logs_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).logs = base.logs := rfl

private lemma rootFold_output_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).output = base.output := rfl

private lemma rootFold_error_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).error = base.error := rfl

private def rootLoopCarrier_step_live
    {sevm : Sevm} {origin base callPost : Devm}
    {memory : Mem} {oldCount : B256} {s : RootLoopState} {stor : Stor}
    (carrier : RootLoopCarrier origin base memory oldCount s)
    (hlive : s.live)
    (hmem : RootMemoryCarrier callPost.memory oldCount s.size
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
    RootLoopCarrier origin callPost
      (callPost.memory.write 608 (s.size >>> 1).toBytes)
      oldCount (s.step sevm.currentTarget stor) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [RootLoopState.step, hlive] using hmem.shiftSize
  · intro a
    rw [hstorage, rootAfterSload_getStor, carrier.stor]
  · intro a
    rw [hcode, rootAfterSload_getCode, carrier.code]
  · rw [haddresses, rootAfterSload_accessedAddresses, carrier.addresses]
  · rw [hkeys, rootAfterSload_accessedStorageKeys, carrier.keys]
    rfl
  · rw [hlogs, rootAfterSload_logs, carrier.logs]
  · rw [houtput, rootAfterSload_output, carrier.output]
  · rw [herror, rootAfterSload_error, carrier.error]

private def rootLoopCarrier_step_dead
    {sevm : Sevm} {origin base callPost : Devm}
    {memory : Mem} {oldCount : B256} {s : RootLoopState} {stor : Stor}
    (carrier : RootLoopCarrier origin base memory oldCount s)
    (hdead : ¬ s.live)
    (hmem : RootMemoryCarrier callPost.memory oldCount s.size
      (hashPair Bytes.sha256 s.node (stor.get s.key)))
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
    RootLoopCarrier origin callPost
      (callPost.memory.write 608 (s.size >>> 1).toBytes)
      oldCount (s.step sevm.currentTarget stor) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [RootLoopState.step, hdead] using hmem.shiftSize
  · intro a
    rw [hstorage, rootAfterSload_getStor, carrier.stor]
  · intro a
    rw [hcode, rootAfterSload_getCode, carrier.code]
  · rw [haddresses, rootAfterSload_accessedAddresses, carrier.addresses]
  · rw [hkeys, rootAfterSload_accessedStorageKeys, carrier.keys]
    rfl
  · rw [hlogs, rootAfterSload_logs, carrier.logs]
  · rw [houtput, rootAfterSload_output, carrier.output]
  · rw [herror, rootAfterSload_error, carrier.error]

/-- Exact existential CPS composition of any active prefix of root-fold
iterations. -/
theorem rootLoop_iterations_exists_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {memory : Mem} {oldCount : B256} {s : RootLoopState}
    {stor : Stor} {n K : Nat} {P : Execution → Prop}
    (carrier : RootLoopCarrier origin base memory oldCount s)
    (horiginStor : Devm.getStor origin sevm.currentTarget = stor)
    (hactive : RootLoopActive sevm.currentTarget stor n s)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      K + rootLoopGas sevm.currentTarget stor n s < 2 ^ 256)
    (hrootContinuation :
      fs[rootContinuationSlot]? = some rootContinuation)
    (hrootLoop : fs[rootLoopSlot]? = some rootLoop)
    (htail :
      ∀ {base' : Devm} {memory' : Mem},
        RootLoopCarrier origin base' memory' oldCount
          (rootLoopIter sevm.currentTarget stor n s) →
        ∃ ex, P ex ∧
          Func.RunCompiledTo fs sevm
            (base'.setMach
              ⟨[(rootLoopIter sevm.currentTarget stor n s).height],
                memory', K⟩)
            rootLoop ex) :
    ∃ ex, P ex ∧
      Func.RunCompiledTo fs sevm
        (base.setMach
          ⟨[s.height], memory,
            K + rootLoopGas sevm.currentTarget stor n s⟩)
        rootLoop ex := by
  induction n generalizing base memory s with
  | zero =>
      simpa only [rootLoopIter, rootLoopGas, Nat.add_zero] using
        htail carrier
  | succ n ih =>
      change s.height < (32 : B256) ∧
        RootLoopActive sevm.currentTarget stor n
          (s.step sevm.currentTarget stor) at hactive
      rcases hactive with ⟨hheight, hactiveNext⟩
      let next := s.step sevm.currentTarget stor
      let tailGas :=
        rootLoopGas sevm.currentTarget stor n next
      have htotal :
          K + rootLoopStepGas sevm.currentTarget s +
            rootLoopGas sevm.currentTarget stor n next < 2 ^ 256 := by
        simpa only [rootLoopGas, Nat.add_assoc, next] using hbound
      have hnextBound :
          K + rootLoopGas sevm.currentTarget stor n next < 2 ^ 256 := by
        have hstep := rootLoopStepGas_ge sevm.currentTarget s
        omega
      have hshaBound : K + tailGas + 269 < 2 ^ 256 := by
        have hstep := rootLoopStepGas_ge sevm.currentTarget s
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
      have hwarmBase :
          (2 : Adr) ∈ base.accessedAddresses := by
        rw [carrier.addresses]
        exact hwarm
      by_cases hlive : s.live
      · have hkey : s.key = branchBase + s.height := by
          simp only [RootLoopState.key, if_pos hlive]
        let left := stor.get s.key
        let loaded := afterSload sevm base s.key
        let staged :=
          (memory.write 0 left.toBytes).write 32 s.node.toBytes
        let shaBase := loaded.setMach ⟨[], staged, 0⟩
        have hpair : RootPairMemoryCarrier shaBase.memory
            oldCount s.size left s.node := by
          simpa only [shaBase, staged, Devm.memory_setMach] using
            (RootMemoryCarrier.stagePair
              (left := left) (right := s.node) carrier.mem)
        have hnodelegSha :
            getDelegatedCodeAddress (shaBase.getCode 2) = none := by
          simpa only [shaBase, loaded, Devm.getCode_setMach,
            rootAfterSload_getCode] using hnodelegBase
        have hwarmSha : (2 : Adr) ∈ shaBase.accessedAddresses := by
          change (2 : Adr) ∈ loaded.accessedAddresses
          dsimp only [loaded]
          rw [rootAfterSload_accessedAddresses]
          exact hwarmBase
        obtain ⟨callPost, _hstack, _hmemory, hcallMemNE,
            _hgas, _hreturn, hstorage, hcode, haddresses, hkeys,
            hlogs, houtput, herror, hlift⟩ :=
          rootShaTail_runCompiledTo
            (fs := fs) (sevm := sevm) (base := shaBase)
            (height := s.height) (K := K + tailGas)
            hpair hnodelegSha hwarmSha hpre hdepth hshaBound
            hrootContinuation hrootLoop
        rcases hcallMemNE with ⟨hcallMem⟩
        have hcallMem' :
            RootMemoryCarrier callPost.memory oldCount s.size
              (hashPair Bytes.sha256 (stor.get s.key) s.node) := by
          simpa only [left, hashPair] using hcallMem
        have hstorage' : ∀ a, Devm.getStor callPost a =
            Devm.getStor loaded a := by
          intro a
          simpa only [shaBase, rootFold_getStor_setMach] using hstorage a
        have hcode' : ∀ a, callPost.getCode a = loaded.getCode a := by
          intro a
          simpa only [shaBase, Devm.getCode_setMach] using hcode a
        have haddresses' :
            callPost.accessedAddresses = loaded.accessedAddresses := by
          simpa only [shaBase, rootFold_accessedAddresses_setMach] using
            haddresses
        have hkeys' :
            callPost.accessedStorageKeys = loaded.accessedStorageKeys := by
          simpa only [shaBase, rootFold_accessedStorageKeys_setMach] using
            hkeys
        have hlogs' : callPost.logs = loaded.logs := by
          simpa only [shaBase, rootFold_logs_setMach] using hlogs
        have houtput' : callPost.output = loaded.output := by
          simpa only [shaBase, rootFold_output_setMach] using houtput
        have herror' : callPost.error = loaded.error := by
          simpa only [shaBase, rootFold_error_setMach] using herror
        have nextCarrier : RootLoopCarrier origin callPost
            (callPost.memory.write 608 (s.size >>> 1).toBytes)
            oldCount next := by
          dsimp only [next, loaded]
          exact rootLoopCarrier_step_live carrier hlive hcallMem'
            hstorage' hcode' haddresses' hkeys' hlogs' houtput' herror'
        obtain ⟨ex, hP, hnextRun⟩ :=
          ih nextCarrier hactiveNext hnextBound (by
            intro base' memory' nextCarrier'
            apply htail
            simpa only [rootLoopIter, next] using nextCarrier')
        have hnextRun' : Func.RunCompiledTo fs sevm
            (callPost.setMach
              ⟨[s.height + 1],
                callPost.memory.write 608 (s.size >>> 1).toBytes,
                K + tailGas⟩)
            rootLoop ex := by
          simpa only [tailGas, next, RootLoopState.step] using hnextRun
        have hshaRun := hlift hnextRun'
        have hvalLive :
            base.getStorVal sevm.currentTarget
              (branchBase + s.height) = left := by
          dsimp only [left]
          rw [← hkey]
          exact hval
        have hstage : Func.RunCompiledTo fs sevm
            (base.setMach
              ⟨[s.height], memory,
                (K + tailGas + 285) + 78 +
                  sloadCost sevm base
                    (branchBase + s.height)⟩)
            rootLoop ex := by
          apply rootLoopLive_runCompiledTo
            carrier.mem hheight hlive hvalLive
            (by simp only [List.length_nil]; omega)
          simpa only [shaBase, loaded, staged, hkey,
            Devm.setMach_setMach, Devm.memory_setMach] using hshaRun
        have hcost :
            sloadCost sevm base (branchBase + s.height) =
              rootReadGas sevm.currentTarget s.keys s.key := by
          rw [← hkey, ← rootReadGas_eq_rootSloadCost, carrier.keys]
        have hgas :
            (K + tailGas + 285) + 78 +
                sloadCost sevm base (branchBase + s.height) =
              K + rootLoopGas sevm.currentTarget stor (n + 1) s := by
          rw [hcost]
          dsimp only [tailGas, next]
          simp only [rootLoopGas, rootLoopStepGas, if_pos hlive]
          omega
        rw [hgas] at hstage
        exact ⟨ex, hP, hstage⟩
      · have hkey : s.key = zeroHashBase + s.height := by
          simp only [RootLoopState.key, if_neg hlive]
        have hbit : ((1 : B256) &&& s.size) = 0 := by
          exact not_ne_iff.mp hlive
        let right := stor.get s.key
        let loaded := afterSload sevm base s.key
        let staged :=
          (memory.write 0 s.node.toBytes).write 32 right.toBytes
        let shaBase := loaded.setMach ⟨[], staged, 0⟩
        have hpair : RootPairMemoryCarrier shaBase.memory
            oldCount s.size s.node right := by
          simpa only [shaBase, staged, Devm.memory_setMach] using
            (RootMemoryCarrier.stagePair
              (left := s.node) (right := right) carrier.mem)
        have hnodelegSha :
            getDelegatedCodeAddress (shaBase.getCode 2) = none := by
          simpa only [shaBase, loaded, Devm.getCode_setMach,
            rootAfterSload_getCode] using hnodelegBase
        have hwarmSha : (2 : Adr) ∈ shaBase.accessedAddresses := by
          change (2 : Adr) ∈ loaded.accessedAddresses
          dsimp only [loaded]
          rw [rootAfterSload_accessedAddresses]
          exact hwarmBase
        obtain ⟨callPost, _hstack, _hmemory, hcallMemNE,
            _hgas, _hreturn, hstorage, hcode, haddresses, hkeys,
            hlogs, houtput, herror, hlift⟩ :=
          rootShaTail_runCompiledTo
            (fs := fs) (sevm := sevm) (base := shaBase)
            (height := s.height) (K := K + tailGas)
            hpair hnodelegSha hwarmSha hpre hdepth hshaBound
            hrootContinuation hrootLoop
        rcases hcallMemNE with ⟨hcallMem⟩
        have hcallMem' :
            RootMemoryCarrier callPost.memory oldCount s.size
              (hashPair Bytes.sha256 s.node (stor.get s.key)) := by
          simpa only [right, hashPair] using hcallMem
        have hstorage' : ∀ a, Devm.getStor callPost a =
            Devm.getStor loaded a := by
          intro a
          simpa only [shaBase, rootFold_getStor_setMach] using hstorage a
        have hcode' : ∀ a, callPost.getCode a = loaded.getCode a := by
          intro a
          simpa only [shaBase, Devm.getCode_setMach] using hcode a
        have haddresses' :
            callPost.accessedAddresses = loaded.accessedAddresses := by
          simpa only [shaBase, rootFold_accessedAddresses_setMach] using
            haddresses
        have hkeys' :
            callPost.accessedStorageKeys = loaded.accessedStorageKeys := by
          simpa only [shaBase, rootFold_accessedStorageKeys_setMach] using
            hkeys
        have hlogs' : callPost.logs = loaded.logs := by
          simpa only [shaBase, rootFold_logs_setMach] using hlogs
        have houtput' : callPost.output = loaded.output := by
          simpa only [shaBase, rootFold_output_setMach] using houtput
        have herror' : callPost.error = loaded.error := by
          simpa only [shaBase, rootFold_error_setMach] using herror
        have nextCarrier : RootLoopCarrier origin callPost
            (callPost.memory.write 608 (s.size >>> 1).toBytes)
            oldCount next := by
          dsimp only [next, loaded]
          exact rootLoopCarrier_step_dead carrier hlive hcallMem'
            hstorage' hcode' haddresses' hkeys' hlogs' houtput' herror'
        obtain ⟨ex, hP, hnextRun⟩ :=
          ih nextCarrier hactiveNext hnextBound (by
            intro base' memory' nextCarrier'
            apply htail
            simpa only [rootLoopIter, next] using nextCarrier')
        have hnextRun' : Func.RunCompiledTo fs sevm
            (callPost.setMach
              ⟨[s.height + 1],
                callPost.memory.write 608 (s.size >>> 1).toBytes,
                K + tailGas⟩)
            rootLoop ex := by
          simpa only [tailGas, next, RootLoopState.step] using hnextRun
        have hshaRun := hlift hnextRun'
        have hvalDead :
            base.getStorVal sevm.currentTarget
              (zeroHashBase + s.height) = right := by
          dsimp only [right]
          rw [← hkey]
          exact hval
        have hstage : Func.RunCompiledTo fs sevm
            (base.setMach
              ⟨[s.height], memory,
                (K + tailGas + 285) + 77 +
                  sloadCost sevm base
                    (zeroHashBase + s.height)⟩)
            rootLoop ex := by
          apply rootLoopDead_runCompiledTo
            carrier.mem hheight hbit hvalDead
            (by simp only [List.length_nil]; omega)
          simpa only [shaBase, loaded, staged, hkey,
            Devm.setMach_setMach, Devm.memory_setMach] using hshaRun
        have hcost :
            sloadCost sevm base (zeroHashBase + s.height) =
              rootReadGas sevm.currentTarget s.keys s.key := by
          rw [← hkey, ← rootReadGas_eq_rootSloadCost, carrier.keys]
        have hgas :
            (K + tailGas + 285) + 77 +
                sloadCost sevm base (zeroHashBase + s.height) =
              K + rootLoopGas sevm.currentTarget stor (n + 1) s := by
          rw [hcost]
          dsimp only [tailGas, next]
          simp only [rootLoopGas, rootLoopStepGas, if_neg hlive]
          omega
        rw [hgas] at hstage
        exact ⟨ex, hP, hstage⟩

/-- Fixed-outcome compatibility corollary of the existential CPS carrier. -/
theorem rootLoop_iterations_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {memory : Mem} {oldCount : B256} {s : RootLoopState}
    {stor : Stor} {n K : Nat} {ex : Execution}
    (carrier : RootLoopCarrier origin base memory oldCount s)
    (horiginStor : Devm.getStor origin sevm.currentTarget = stor)
    (hactive : RootLoopActive sevm.currentTarget stor n s)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      K + rootLoopGas sevm.currentTarget stor n s < 2 ^ 256)
    (hrootContinuation :
      fs[rootContinuationSlot]? = some rootContinuation)
    (hrootLoop : fs[rootLoopSlot]? = some rootLoop)
    (htail :
      ∀ {base' : Devm} {memory' : Mem},
        RootLoopCarrier origin base' memory' oldCount
          (rootLoopIter sevm.currentTarget stor n s) →
        Func.RunCompiledTo fs sevm
          (base'.setMach
            ⟨[(rootLoopIter sevm.currentTarget stor n s).height],
              memory', K⟩)
          rootLoop ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[s.height], memory,
          K + rootLoopGas sevm.currentTarget stor n s⟩)
      rootLoop ex := by
  obtain ⟨ex', hex, hrun⟩ :=
    rootLoop_iterations_exists_runCompiledTo
      (P := fun ex' => ex' = ex) carrier horiginStor hactive
      hnodeleg hwarm hpre hdepth hbound hrootContinuation hrootLoop
      (by
        intro base' memory' hcarrier
        exact ⟨ex, rfl, htail hcarrier⟩)
  subst ex'
  exact hrun

/-! ## Machine-word trace to the pure root model -/

private def rootNatState (height size : Nat) (node : B256)
    (keys : KeySet) : RootLoopState :=
  ⟨Nat.toB256 height, Nat.toB256 size, node, keys⟩

private theorem one_and_toB256 (n : Nat) (hn : n < 2 ^ 256) :
    ((1 : B256) &&& Nat.toB256 n) = Nat.toB256 (n % 2) :=
  Blanc.one_and_toB256_eq_mod_two n hn

private theorem rootNatState_live_iff
    (height size : Nat) (node : B256) (keys : KeySet)
    (hsize : size < 2 ^ 256) :
    (rootNatState height size node keys).live ↔ size % 2 = 1 := by
  unfold RootLoopState.live rootNatState
  rw [one_and_toB256 size hsize]
  constructor
  · intro hnz
    rcases Nat.mod_two_eq_zero_or_one size with hzero | hone
    · rw [hzero] at hnz
      exact (hnz rfl).elim
    · exact hone
  · intro hone hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt (by omega : size % 2 < 2 ^ 256)] at hnat
    simp only [hone] at hnat
    contradiction

private theorem toB256_succ_of_lt_32 (height : Nat)
    (hheight : height < 32) :
    Nat.toB256 height + 1 = Nat.toB256 (height + 1) :=
  Blanc.toB256_add_one_of_lt height (by omega)

private theorem branchBase_add_toB256 (h : Nat) (hh : h < 32) :
    branchBase + Nat.toB256 h = branchSlot h := by
  apply B256.toNat_inj
  rw [B256.toNat_add_eq_of_nof]
  · rw [B256.toNat_toB256_of_lt (by omega : h < 2 ^ 256)]
    unfold branchSlot
    rw [B256.toNat_toB256_of_lt (by omega : 0x100 + h < 2 ^ 256)]
    rfl
  · unfold B256.Nof branchBase
    rw [B256.toNat_toB256_of_lt (by omega : h < 2 ^ 256)]
    change 256 + h < 2 ^ 256
    omega

private theorem zeroHashBase_add_toB256 (h : Nat) (hh : h < 32) :
    zeroHashBase + Nat.toB256 h = zeroHashSlot h := by
  apply B256.toNat_inj
  rw [B256.toNat_add_eq_of_nof]
  · rw [B256.toNat_toB256_of_lt (by omega : h < 2 ^ 256)]
    unfold zeroHashSlot
    rw [B256.toNat_toB256_of_lt (by omega : 0x300 + h < 2 ^ 256)]
    rfl
  · unfold B256.Nof zeroHashBase
    rw [B256.toNat_toB256_of_lt (by omega : h < 2 ^ 256)]
    change 768 + h < 2 ^ 256
    omega

private theorem rootNatState_key_of_odd
    (height size : Nat) (node : B256) (keys : KeySet)
    (hheight : height < 32) (hsize : size < 2 ^ 256)
    (hodd : size % 2 = 1) :
    (rootNatState height size node keys).key = branchSlot height := by
  unfold RootLoopState.key
  rw [if_pos ((rootNatState_live_iff height size node keys hsize).2 hodd)]
  exact branchBase_add_toB256 height hheight

private theorem rootNatState_key_of_even
    (height size : Nat) (node : B256) (keys : KeySet)
    (hheight : height < 32) (hsize : size < 2 ^ 256)
    (heven : size % 2 = 0) :
    (rootNatState height size node keys).key = zeroHashSlot height := by
  have hdead : ¬(rootNatState height size node keys).live := by
    intro hlive
    have := (rootNatState_live_iff height size node keys hsize).1 hlive
    omega
  unfold RootLoopState.key
  rw [if_neg hdead]
  exact zeroHashBase_add_toB256 height hheight

private theorem lowShift (n : Nat) (hn : n < 2 ^ 64) :
    n.toUInt64 >>> (1 : Nat).toUInt64 = (n / 2).toUInt64 :=
  Blanc.toUInt64_shiftRight_one n hn

private theorem shift128 (n : Nat) (hn : n < 2 ^ 64) :
    Nat.toB128 n >>> 1 = Nat.toB128 (n / 2) :=
  Blanc.toB128_shiftRight_one n hn

private theorem shift256_32 (n : Nat) (hn : n < 2 ^ 32) :
    Nat.toB256 n >>> 1 = Nat.toB256 (n / 2) :=
  Blanc.toB256_shiftRight_one n (by omega)

private theorem rootNatState_step_of_odd
    (owner : Adr) (stor : Stor) (height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height < 32) (hsize : size < 2 ^ 32)
    (hodd : size % 2 = 1) :
    (rootNatState height size node keys).step owner stor =
      rootNatState (height + 1) (size / 2)
        (hashPair Bytes.sha256 ((accOfStor stor).branch height) node)
        (rootReadKeys owner keys (branchSlot height)) := by
  have hlive : (rootNatState height size node keys).live :=
    (rootNatState_live_iff height size node keys (by omega)).2 hodd
  unfold RootLoopState.step
  simp only [hlive, if_pos]
  rw [rootNatState_key_of_odd height size node keys hheight (by omega) hodd]
  unfold rootNatState
  rw [toB256_succ_of_lt_32 height hheight, shift256_32 size hsize,
    accOfStor_branch_of_lt stor height hheight]

private theorem rootNatState_step_of_even
    (owner : Adr) (stor : Stor) (height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height < 32) (hsize : size < 2 ^ 32)
    (heven : size % 2 = 0) (hzero : ZeroHashesCorrect stor) :
    (rootNatState height size node keys).step owner stor =
      rootNatState (height + 1) (size / 2)
        (hashPair Bytes.sha256 node (zeroHash Bytes.sha256 height))
        (rootReadKeys owner keys (zeroHashSlot height)) := by
  have hdead : ¬(rootNatState height size node keys).live := by
    intro hlive
    have := (rootNatState_live_iff height size node keys (by omega)).1 hlive
    omega
  unfold RootLoopState.step
  simp only [hdead, if_false]
  rw [rootNatState_key_of_even height size node keys hheight (by omega)
      heven]
  unfold rootNatState
  rw [toB256_succ_of_lt_32 height hheight, shift256_32 size hsize,
    hzero height hheight]

private def rootNatKeys (owner : Adr) :
    Nat → Nat → Nat → KeySet → KeySet
  | 0, _, _, keys => keys
  | k + 1, height, size, keys =>
      rootNatKeys owner k (height + 1) (size / 2)
        (rootReadKeys owner keys
          (if size % 2 = 1 then branchSlot height else zeroHashSlot height))

private theorem div_two_div_pow (n k : Nat) :
    n / 2 / 2 ^ k = n / 2 ^ (k + 1) :=
  Blanc.div_two_div_pow n k

private theorem rootLoopIter_rootNatState
    (owner : Adr) (stor : Stor) (k height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height + k ≤ 32)
    (hsize : size < 2 ^ 32) (hzero : ZeroHashesCorrect stor) :
    rootLoopIter owner stor k (rootNatState height size node keys) =
      rootNatState (height + k) (size / 2 ^ k)
        (climb Bytes.sha256 (accOfStor stor).branch k height size node)
        (rootNatKeys owner k height size keys) := by
  induction k generalizing height size node keys with
  | zero =>
      simp only [rootLoopIter, rootNatKeys, climb, pow_zero, Nat.div_one,
        Nat.add_zero]
  | succ k ih =>
      have hh : height < 32 := by omega
      rw [rootLoopIter]
      rcases Nat.mod_two_eq_zero_or_one size with heven | hodd
      · rw [rootNatState_step_of_even owner stor height size node keys
          hh hsize heven hzero]
        rw [ih (height := height + 1) (size := size / 2)
          (node := hashPair Bytes.sha256 node (zeroHash Bytes.sha256 height))
          (keys := rootReadKeys owner keys (zeroHashSlot height))
          (by omega) (by omega)]
        simp only [climb, rootNatKeys, heven]
        rw [div_two_div_pow]
        congr 1
        all_goals omega
      · rw [rootNatState_step_of_odd owner stor height size node keys
          hh hsize hodd]
        rw [ih (height := height + 1) (size := size / 2)
          (node := hashPair Bytes.sha256 ((accOfStor stor).branch height)
            node)
          (keys := rootReadKeys owner keys (branchSlot height))
          (by omega) (by omega)]
        simp only [climb, rootNatKeys, hodd, if_true]
        rw [div_two_div_pow]
        congr 1
        all_goals omega

private theorem rootInitialLoopState_toB256 (base : Devm) (count : Nat) :
    rootInitialLoopState base (Nat.toB256 count) =
      rootNatState 0 count 0 base.accessedStorageKeys := by
  rfl

/-- The concrete 32-step machine trace computes the pure `climb` node. -/
theorem rootLoopIter_32_initial_eq_climb
    (owner : Adr) (stor : Stor) (base : Devm) (count : Nat)
    (hcount : count < 2 ^ 32) (hzero : ZeroHashesCorrect stor) :
    rootLoopIter owner stor 32
        (rootInitialLoopState base (Nat.toB256 count)) =
      rootNatState 32 0
        (climb Bytes.sha256 (accOfStor stor).branch 32 0 count 0)
        (rootNatKeys owner 32 0 count base.accessedStorageKeys) := by
  rw [rootInitialLoopState_toB256]
  have hdiv : count / 2 ^ 32 = 0 := Nat.div_eq_of_lt hcount
  simpa only [Nat.zero_add, hdiv] using
    rootLoopIter_rootNatState owner stor 32 0 count 0
      base.accessedStorageKeys (by omega) hcount hzero

private theorem rootNatState_height_lt_32
    (height size : Nat) (node : B256) (keys : KeySet)
    (hheight : height < 32) :
    (rootNatState height size node keys).height < (32 : B256) := by
  rw [B256.lt_iff_toNat_lt_toNat]
  change (Nat.toB256 height).toNat < B256.toNat (32 : B256)
  rw [B256.toNat_toB256_of_lt (by omega : height < 2 ^ 256)]
  exact hheight

private theorem rootLoopActive_rootNatState
    (owner : Adr) (stor : Stor) (k height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height + k ≤ 32)
    (hsize : size < 2 ^ 32) (hzero : ZeroHashesCorrect stor) :
    RootLoopActive owner stor k (rootNatState height size node keys) := by
  induction k generalizing height size node keys with
  | zero =>
      simp only [RootLoopActive]
  | succ k ih =>
      rw [RootLoopActive]
      constructor
      · exact rootNatState_height_lt_32 height size node keys (by omega)
      · rcases Nat.mod_two_eq_zero_or_one size with heven | hodd
        · rw [rootNatState_step_of_even owner stor height size node keys
            (by omega) hsize heven hzero]
          exact ih (height := height + 1) (size := size / 2)
            (node := hashPair Bytes.sha256 node
              (zeroHash Bytes.sha256 height))
            (keys := rootReadKeys owner keys (zeroHashSlot height))
            (by omega) (by omega)
        · rw [rootNatState_step_of_odd owner stor height size node keys
            (by omega) hsize hodd]
          exact ih (height := height + 1) (size := size / 2)
            (node := hashPair Bytes.sha256
              ((accOfStor stor).branch height) node)
            (keys := rootReadKeys owner keys (branchSlot height))
            (by omega) (by omega)

/-- All 32 entries in a valid root fold remain below the terminal height. -/
theorem rootLoopActive_32_initial
    (owner : Adr) (stor : Stor) (base : Devm) (count : Nat)
    (hcount : count < 2 ^ 32) (hzero : ZeroHashesCorrect stor) :
    RootLoopActive owner stor 32
      (rootInitialLoopState base (Nat.toB256 count)) := by
  rw [rootInitialLoopState_toB256]
  exact rootLoopActive_rootNatState owner stor 32 0 count 0
    base.accessedStorageKeys (by omega) hcount hzero

/-! ## Endpoint prefix -/

def getDepositRootPrefixGas (sevm : Sevm) (base : Devm) : Nat :=
  103 + sloadCost sevm base depositCountSlot

/-- Exact initialization of the three root registers and entry to the loop. -/
theorem getDepositRootEndpoint_prefix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {count : B256} {K : Nat} {ex : Execution}
    (hvalue : base.getStorVal sevm.currentTarget depositCountSlot = count)
    (hrootLoop : fs[rootLoopSlot]? = some rootLoop)
    (htail : Func.RunCompiledTo fs sevm
      ((afterSload sevm base depositCountSlot).setMach
        ⟨[0], rootInitialMemory count, K⟩)
      rootLoop ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], Mem.empty, K + getDepositRootPrefixGas sevm base⟩)
      getDepositRootEndpoint ex := by
  let loaded := afterSload sevm base depositCountSlot
  let M1 := Mem.empty.write 576 count.toBytes
  let M2 := M1.write 608 count.toBytes
  let M3 := M2.write 640 (0 : B256).toBytes
  have hsize1 : M1.size = 608 := by
    dsimp only [M1]
    rw [Mem.size_write_word_at]
    decide +kernel
  have hsize2 : M2.size = 640 := by
    dsimp only [M2]
    rw [Mem.size_write_word_at, hsize1]
    decide +kernel
  have hsize3 : M3.size = 672 := by
    dsimp only [M3]
    rw [Mem.size_write_word_at, hsize2]
    decide +kernel
  simp only [getDepositRootEndpoint]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := depositCountSlot) (c := gVerylow)
      (G := K + 100 + sloadCost sevm base depositCountSlot)
      (by
        unfold depositCountSlot
        decide +kernel)
      (by
        simp only [Devm.gasLeft_setMach, getDepositRootPrefixGas,
          gVerylow]
        omega)
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (rootSload_runCompiled
      (stack := []) (memory := Mem.empty) (G := K + 100)
      hvalue (by simp only [List.length_nil]; omega)) ?_
  change Func.RunCompiledTo fs sevm
    (loaded.setMach ⟨[count], Mem.empty, K + 100⟩)
    _ ex
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := count) (G := K + 97)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := oldCountWord * 32) (c := gVerylow)
      (G := K + 94)
      (by
        unfold oldCountWord
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := oldCountWord * 32) (v := count) (s := [count])
      (G := K + 34) (e := 57) (M := M1)
      rfl
      (Devm.extCost_of_size (N := Mem.empty)
        (i := (oldCountWord * 32).toNat) (sz := 32)
        rfl (by
          unfold oldCountWord
          decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        dsimp only [M1]
        rfl)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := gVerylow)
      (G := K + 31)
      (by
        unfold shiftedSizeWord
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := shiftedSizeWord * 32) (v := count) (s := [])
      (G := K + 25) (e := 3) (M := M2)
      rfl
      (Devm.extCost_of_size
        (N := M1) (i := (shiftedSizeWord * 32).toNat) (sz := 32)
        hsize1 (by
          unfold shiftedSizeWord
          decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        dsimp only [M2]
        rfl)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := 0) (c := gBase) (G := K + 23)
      pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := nodeWord * 32) (c := gVerylow)
      (G := K + 20)
      (by
        unfold nodeWord
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := nodeWord * 32) (v := 0) (s := [])
      (G := K + 14) (e := 3) (M := M3)
      rfl
      (Devm.extCost_of_size
        (N := M2) (i := (nodeWord * 32).toNat) (sz := 32)
        hsize2 (by
          unfold nodeWord
          decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        dsimp only [M3]
        rfl)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := 0) (c := gBase) (G := K + 12)
      pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.runCompiledTo_call' (G := K) hrootLoop
  · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
  · simpa only [loaded, M1, M2, M3, rootInitialMemory,
      Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using
      htail

end Blanc.BeaconDeposit
