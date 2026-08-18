import Blanc.LidoCircuitBreakerDeploy
import Blanc.ExecutionOccurrence

/-!
Typed source-site and authority vocabulary for the exact Lido CircuitBreaker
runtime.  This module is deliberately below the endpoint proofs: it turns the
literal production inventory into a stable row type without importing another
contract family or changing executable code.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Ninst

/-- The six invocation roles admitted by runtime persistent writes.  These are
runtime guard roles, not authentication or consent claims. -/
inductive InvocationRole
  | adminConfiguration
  | adminRegistry
  | adminExpiry
  | heartbeatExpiry
  | pauseRegistry
  | pauseExpiry
deriving DecidableEq, Repr

/-- One constructor per reviewed runtime SSTORE, in compiler/source order. -/
inductive RuntimePersistentWrite
  | setPauseDurationConfig
  | setHeartbeatIntervalConfig
  | heartbeatExpiry
  | setPauserAssignment
  | setPauserOldCount
  | appendArrayEntry
  | appendReverseIndex
  | appendArrayLength
  | afterOldNewCount
  | removeArrayHole
  | removeMovedIndex
  | removeClearTail
  | removeArrayLength
  | removeClearTargetIndex
  | registerFreshExpiry
  | registerLastOldClear
  | registerLastOldNewExpiry
  | registerRetainedOldNewExpiry
  | pauseLastTargetExpiry
  | pauseRetainedTargetExpiry
deriving DecidableEq, Repr

def RuntimePersistentWrite.all : List RuntimePersistentWrite :=
  [ .setPauseDurationConfig,
    .setHeartbeatIntervalConfig,
    .heartbeatExpiry,
    .setPauserAssignment,
    .setPauserOldCount,
    .appendArrayEntry,
    .appendReverseIndex,
    .appendArrayLength,
    .afterOldNewCount,
    .removeArrayHole,
    .removeMovedIndex,
    .removeClearTail,
    .removeArrayLength,
    .removeClearTargetIndex,
    .registerFreshExpiry,
    .registerLastOldClear,
    .registerLastOldNewExpiry,
    .registerRetainedOldNewExpiry,
    .pauseLastTargetExpiry,
    .pauseRetainedTargetExpiry ]

def RuntimePersistentWrite.index : RuntimePersistentWrite → Nat
  | .setPauseDurationConfig => 0
  | .setHeartbeatIntervalConfig => 1
  | .heartbeatExpiry => 2
  | .setPauserAssignment => 3
  | .setPauserOldCount => 4
  | .appendArrayEntry => 5
  | .appendReverseIndex => 6
  | .appendArrayLength => 7
  | .afterOldNewCount => 8
  | .removeArrayHole => 9
  | .removeMovedIndex => 10
  | .removeClearTail => 11
  | .removeArrayLength => 12
  | .removeClearTargetIndex => 13
  | .registerFreshExpiry => 14
  | .registerLastOldClear => 15
  | .registerLastOldNewExpiry => 16
  | .registerRetainedOldNewExpiry => 17
  | .pauseLastTargetExpiry => 18
  | .pauseRetainedTargetExpiry => 19

def RuntimePersistentWrite.inventoryEntry :
    RuntimePersistentWrite → SourceSite × PersistentWriteClass
  | .setPauseDurationConfig =>
      (⟨"setPauseDuration.config", 0⟩, .configuration)
  | .setHeartbeatIntervalConfig =>
      (⟨"setHeartbeatInterval.config", 1⟩, .configuration)
  | .setPauserAssignment =>
      (⟨"setPauser.assignment", 2⟩, .registryAssignment)
  | .setPauserOldCount =>
      (⟨"setPauser.oldCount", 3⟩, .registryCount)
  | .appendArrayEntry =>
      (⟨"append.arrayEntry", 4⟩, .registryArray)
  | .appendReverseIndex =>
      (⟨"append.reverseIndex", 5⟩, .registryIndex)
  | .appendArrayLength =>
      (⟨"append.arrayLength", 6⟩, .registryArray)
  | .afterOldNewCount =>
      (⟨"afterOld.newCount", 7⟩, .registryCount)
  | .removeArrayHole =>
      (⟨"remove.arrayHole", 8⟩, .registryArray)
  | .removeMovedIndex =>
      (⟨"remove.movedIndex", 9⟩, .registryIndex)
  | .removeClearTail =>
      (⟨"remove.clearTail", 10⟩, .registryArray)
  | .removeArrayLength =>
      (⟨"remove.arrayLength", 11⟩, .registryArray)
  | .removeClearTargetIndex =>
      (⟨"remove.clearTargetIndex", 12⟩, .registryIndex)
  | .registerFreshExpiry =>
      (⟨"register.freshExpiry", 13⟩, .heartbeatExpiry)
  | .registerLastOldClear =>
      (⟨"register.lastOldClear", 14⟩, .heartbeatExpiry)
  | .registerLastOldNewExpiry =>
      (⟨"register.lastOldNewExpiry", 15⟩, .heartbeatExpiry)
  | .registerRetainedOldNewExpiry =>
      (⟨"register.retainedOldNewExpiry", 16⟩, .heartbeatExpiry)
  | .heartbeatExpiry =>
      (⟨"heartbeat.expiry", 17⟩, .heartbeatExpiry)
  | .pauseLastTargetExpiry =>
      (⟨"pause.lastTargetExpiry", 18⟩, .heartbeatExpiry)
  | .pauseRetainedTargetExpiry =>
      (⟨"pause.retainedTargetExpiry", 19⟩, .heartbeatExpiry)

/-- Semantic label order of the frozen literal inventory.  This is distinct
from `all`, whose order follows the compiler's structural source traversal. -/
def RuntimePersistentWrite.inventoryOrder : List RuntimePersistentWrite :=
  [ .setPauseDurationConfig,
    .setHeartbeatIntervalConfig,
    .setPauserAssignment,
    .setPauserOldCount,
    .appendArrayEntry,
    .appendReverseIndex,
    .appendArrayLength,
    .afterOldNewCount,
    .removeArrayHole,
    .removeMovedIndex,
    .removeClearTail,
    .removeArrayLength,
    .removeClearTargetIndex,
    .registerFreshExpiry,
    .registerLastOldClear,
    .registerLastOldNewExpiry,
    .registerRetainedOldNewExpiry,
    .heartbeatExpiry,
    .pauseLastTargetExpiry,
    .pauseRetainedTargetExpiry ]

/-- Permitted invocation roles for each runtime SSTORE row.

Certified in one direction only: every role actually derived by the authority
theorems lies in its row's list, so this list is a sound upper bound.
Tightness — that each listed role is genuinely attainable at that row — is a
separate obligation of the Stage 5 attainment controls, not of this definition,
and it is **partially discharged**: six of the thirty (row, role) pairs carry a
positive witness, and the one negative direction that matters here (a pause
invocation can never reach `afterOldNewCount`) is proved.  The remaining
twenty-four pairs are unproved in both directions, so this list stays a sound
upper bound.  Do not describe the set as exact. -/
def RuntimePersistentWrite.permittedRoles :
    RuntimePersistentWrite → List InvocationRole
  | .setPauseDurationConfig | .setHeartbeatIntervalConfig =>
      [.adminConfiguration]
  | .setPauserAssignment | .setPauserOldCount
  | .appendArrayEntry | .appendReverseIndex | .appendArrayLength
  | .removeArrayHole | .removeMovedIndex | .removeClearTail
  | .removeArrayLength | .removeClearTargetIndex =>
      [.adminRegistry, .pauseRegistry]
  | .afterOldNewCount => [.adminRegistry]
  | .registerFreshExpiry | .registerLastOldClear
  | .registerLastOldNewExpiry | .registerRetainedOldNewExpiry =>
      [.adminExpiry]
  | .heartbeatExpiry => [.heartbeatExpiry]
  | .pauseLastTargetExpiry | .pauseRetainedTargetExpiry => [.pauseExpiry]

/-- Executable structural SSTORE projection of the exact parameterized
runtime.  Unlike the old syntax count, each member retains its full source path
and compiled PC. -/
def isPersistentWriteInstruction : Ninst → Bool
  | .reg .sstore => true
  | _ => false

def runtimePersistentSourceSites (dp : DeployParams) : List Prog.SourceSite :=
  (runtime dp).sourceSites.filter fun site =>
    isPersistentWriteInstruction site.instruction

def RuntimePersistentWrite.sourceSite?
    (dp : DeployParams) (row : RuntimePersistentWrite) : Option Prog.SourceSite :=
  (runtimePersistentSourceSites dp)[row.index]?

/-- Structural match used by the public classifier.  Both source path and
compiled PC are load-bearing; instruction kind is supplied by the filtered
source list. -/
def RuntimePersistentWrite.matchesSource
    (dp : DeployParams) (row : RuntimePersistentWrite)
    (path : Prog.SourcePath) (pc : Nat) : Bool :=
  match row.sourceSite? dp with
  | none => false
  | some site => site.path == path && site.pc == pc

def classifyRuntimePersistentWrite
    (dp : DeployParams) (path : Prog.SourcePath) (pc : Nat) :
    Option RuntimePersistentWrite :=
  RuntimePersistentWrite.all.find? fun row => row.matchesSource dp path pc

theorem RuntimePersistentWrite.all_length :
    RuntimePersistentWrite.all.length = 20 := by
  decide

theorem RuntimePersistentWrite.all_nodup :
    RuntimePersistentWrite.all.Nodup := by
  decide

/-- The semantic label order is definitionally aligned with the frozen literal
inventory, independently of compiler structural source order. -/
theorem RuntimePersistentWrite.inventory_exact :
    RuntimePersistentWrite.inventoryOrder.map
        RuntimePersistentWrite.inventoryEntry =
      persistentWriteInventory := by
  decide

theorem RuntimePersistentWrite.index_lt
    (row : RuntimePersistentWrite) : row.index < 20 := by
  cases row <;> decide

/-- Looking up a row can only return an actual structural source SSTORE from
the exact parameterized runtime. -/
theorem RuntimePersistentWrite.sourceSite?_sound
    {dp : DeployParams} {row : RuntimePersistentWrite}
    {site : Prog.SourceSite}
    (found : row.sourceSite? dp = some site) :
    site ∈ (runtime dp).sourceSites ∧
      site.instruction = .reg .sstore := by
  unfold RuntimePersistentWrite.sourceSite? at found
  rw [List.getElem?_eq_some_iff] at found
  rcases found with ⟨bound, geteq⟩
  have member := List.getElem_mem bound
  rw [geteq] at member
  unfold runtimePersistentSourceSites at member
  rw [List.mem_filter] at member
  refine ⟨member.1, ?_⟩
  rcases site with ⟨path, pc, instruction⟩
  cases instruction with
  | reg regular =>
      cases regular <;> simp_all [isPersistentWriteInstruction]
  | exec execution => simp_all [isPersistentWriteInstruction]
  | push bytes bound => simp_all [isPersistentWriteInstruction]

/-! ## Parameter-independent structural projection -/

/-- Compiler/source shape retaining instruction widths, branch structure, and
every non-PUSH instruction. Push payload bytes and terminal outcomes are
deliberately erased. -/
inductive PersistentSourceShape where
  | last
  | next (size : Nat) (instruction : Option Ninst)
      (rest : PersistentSourceShape)
  | branch (left right : PersistentSourceShape)
  | call

def PersistentSourceShape.byteSize : PersistentSourceShape → Nat
  | .last => 1
  | .next size _ rest => rest.byteSize + size
  | .branch left right => left.byteSize + right.byteSize + 5
  | .call => 4

def isTransientWriteInstruction : Ninst → Bool
  | .reg .tstore => true
  | _ => false

def isExternalCallInstruction : Ninst → Bool
  | .exec _ => true
  | _ => false

/-- The execution opcode carried by an external-call instruction.  Keeping
this projection separate from `Ninst` also gives the finite executable domain
a decidable equality test despite dependent PUSH constructors elsewhere in
`Ninst`. -/
def externalInstruction? : Ninst → Option Xinst
  | .exec instruction => some instruction
  | _ => none

def nonPushInstruction? : Ninst → Option Ninst
  | .push _ _ => none
  | instruction => some instruction

def isNonPushInstruction : Ninst → Bool
  | .push _ _ => false
  | _ => true

def persistentSourceShape : Func → PersistentSourceShape
  | .last _ => .last
  | .next inst rest =>
      .next inst.size (nonPushInstruction? inst)
        (persistentSourceShape rest)
  | .branch left right =>
      .branch (persistentSourceShape left) (persistentSourceShape right)
  | .call _ => .call

def PersistentSourceShape.sourceSites
    (functionIndex : Nat) (steps : List Prog.SourceStep) (pc : Nat) :
    PersistentSourceShape → List Prog.SourceSite
  | .last => []
  | .next size instruction rest =>
      (match instruction with
       | some instruction =>
        [{ path := ⟨functionIndex, steps⟩, pc,
           instruction }]
       | none => []) ++
      rest.sourceSites functionIndex (steps ++ [.rest]) (pc + size)
  | .branch left right =>
      left.sourceSites functionIndex (steps ++ [.branchLeft]) (pc + 4) ++
      right.sourceSites functionIndex (steps ++ [.branchRight])
        (pc + left.byteSize + 5)
  | .call => []

structure PersistentProgramShape where
  main : PersistentSourceShape
  aux : List PersistentSourceShape

def persistentProgramShape (program : Prog) : PersistentProgramShape :=
  ⟨persistentSourceShape program.main,
   program.aux.map persistentSourceShape⟩

def persistentTable :
    Nat → List PersistentSourceShape → List (Nat × PersistentSourceShape)
  | _, [] => []
  | k, body :: rest =>
      (k, body) :: persistentTable (k + body.byteSize + 1) rest

def PersistentProgramShape.sourceSites
    (shape : PersistentProgramShape) : List Prog.SourceSite :=
  (List.range (shape.main :: shape.aux).length).flatMap fun index =>
    match (persistentTable 0 (shape.main :: shape.aux))[index]? with
    | some (pc, body) => body.sourceSites index [] (pc + 1)
    | none => []

theorem PersistentSourceShape.byteSize_eq
    (body : Func) :
    (persistentSourceShape body).byteSize = compsize body := by
  induction body with
  | last outcome => rfl
  | next inst rest ih =>
      simp [persistentSourceShape, PersistentSourceShape.byteSize,
        compsize, ih, Ninst.size_eq_length_toBytes]
  | branch left right ihl ihr =>
      simp [persistentSourceShape, PersistentSourceShape.byteSize,
        compsize, ihl, ihr]
  | call index => rfl

theorem persistentSourceSites_eq
    (body : Func) (functionIndex : Nat) (steps : List Prog.SourceStep)
    (pc : Nat) :
    (body.sourceSites functionIndex steps pc).filter
        (fun site => isNonPushInstruction site.instruction) =
      (persistentSourceShape body).sourceSites functionIndex steps pc := by
  induction body generalizing steps pc with
  | last outcome => rfl
  | next inst rest ih =>
      simp only [Func.sourceSites, List.filter_cons, persistentSourceShape,
        PersistentSourceShape.sourceSites]
      rw [ih]
      cases inst with
      | reg regular => rfl
      | exec execution => rfl
      | push bytes bound => rfl
  | branch left right ihl ihr =>
      simp only [Func.sourceSites, List.filter_append, persistentSourceShape,
        PersistentSourceShape.sourceSites]
      rw [ihl, ihr, PersistentSourceShape.byteSize_eq]
  | call index => rfl

theorem persistentTable_map
    (bodies : List Func) (k : Nat) :
    (_root_.Blanc.table k bodies).map
        (fun entry => (entry.1, persistentSourceShape entry.2)) =
      persistentTable k (bodies.map persistentSourceShape) := by
  induction bodies generalizing k with
  | nil => rfl
  | cons body rest ih =>
      simp only [_root_.Blanc.table, List.map_cons, persistentTable]
      rw [PersistentSourceShape.byteSize_eq, ih]

theorem persistentProgramSourceSites_eq (program : Prog) :
    program.sourceSites.filter
        (fun site => isNonPushInstruction site.instruction) =
      (persistentProgramShape program).sourceSites := by
  unfold Prog.sourceSites PersistentProgramShape.sourceSites
    persistentProgramShape
  rw [List.filter_flatMap]
  simp only [List.length_cons, List.length_map]
  apply List.flatMap_congr
  intro index index_mem
  have htable := persistentTable_map (program.main :: program.aux) 0
  have hget := congrArg (fun xs => xs[index]?) htable
  simp only [List.map_cons, List.getElem?_map] at hget
  split
  next pc body hbody =>
    have mapped := congrArg
      (Option.map fun entry => (entry.1, persistentSourceShape entry.2))
      hbody
    simp only [Option.map_some] at mapped
    rw [hget] at mapped
    rw [mapped]
    exact persistentSourceSites_eq _ _ _ _
  next hnone =>
    have mapped :
        ((_root_.Blanc.table 0
          (program.main :: program.aux))[index]?).map
            (fun entry => (entry.1, persistentSourceShape entry.2)) = none := by
      rw [hnone]
      rfl
    rw [hget] at mapped
    simp [mapped]

theorem filterPersistent_nonPush (sites : List Prog.SourceSite) :
    (sites.filter fun site =>
      isNonPushInstruction site.instruction).filter
        (fun site => isPersistentWriteInstruction site.instruction) =
      sites.filter fun site =>
        isPersistentWriteInstruction site.instruction := by
  rw [List.filter_filter]
  congr 1
  funext site
  cases site.instruction with
  | reg regular => cases regular <;> rfl
  | exec execution => rfl
  | push bytes bound => rfl

theorem filterTransient_nonPush (sites : List Prog.SourceSite) :
    (sites.filter fun site =>
      isNonPushInstruction site.instruction).filter
        (fun site => isTransientWriteInstruction site.instruction) =
      sites.filter fun site =>
        isTransientWriteInstruction site.instruction := by
  rw [List.filter_filter]
  congr 1
  funext site
  cases site.instruction with
  | reg regular => cases regular <;> rfl
  | exec execution => rfl
  | push bytes bound => rfl

theorem filterExternal_nonPush (sites : List Prog.SourceSite) :
    (sites.filter fun site =>
      isNonPushInstruction site.instruction).filter
        (fun site => isExternalCallInstruction site.instruction) =
      sites.filter fun site =>
        isExternalCallInstruction site.instruction := by
  rw [List.filter_filter]
  congr 1
  funext site
  cases site.instruction with
  | reg regular => rfl
  | exec execution => rfl
  | push bytes bound => rfl

def persistentDispatchEntryShapes (xs : List (B256 × Func)) :
    List (B256 × PersistentSourceShape) :=
  xs.map fun entry => (entry.1, persistentSourceShape entry.2)

theorem linearDispatchWith_persistentSourceShape_eq
    {xs ys : List (B256 × Func)}
    (h : persistentDispatchEntryShapes xs =
      persistentDispatchEntryShapes ys) (k : Nat) :
    persistentSourceShape (linearDispatchWith k xs) =
      persistentSourceShape (linearDispatchWith k ys) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [persistentDispatchEntryShapes] at h
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => simp [persistentDispatchEntryShapes] at h
          | cons y ys =>
              cases ys with
              | nil =>
                  cases x with
                  | mk xw xb =>
                    cases y with
                    | mk yw yb =>
                      simp [persistentDispatchEntryShapes] at h
                      rcases h with ⟨rfl, hb⟩
                      simp [linearDispatchWith, persistentSourceShape, hb]
              | cons y' ys => simp [persistentDispatchEntryShapes] at h
      | cons x' xs =>
          cases ys with
          | nil => simp [persistentDispatchEntryShapes] at h
          | cons y ys =>
              cases ys with
              | nil => simp [persistentDispatchEntryShapes] at h
              | cons y' ys =>
                  cases x with
                  | mk xw xb =>
                    cases y with
                    | mk yw yb =>
                      have hhead :
                          (xw, persistentSourceShape xb) =
                            (yw, persistentSourceShape yb) := by
                        simpa [persistentDispatchEntryShapes] using
                          congrArg List.head? h
                      have htail :
                          persistentDispatchEntryShapes (x' :: xs) =
                            persistentDispatchEntryShapes (y' :: ys) := by
                        simpa [persistentDispatchEntryShapes] using
                          congrArg List.tail h
                      have hw : xw = yw := congrArg Prod.fst hhead
                      have hb : persistentSourceShape xb =
                          persistentSourceShape yb :=
                        congrArg Prod.snd hhead
                      subst yw
                      simp only [linearDispatchWith,
                        persistentSourceShape]
                      rw [hb, ih htail]

theorem splitDispatch_persistentSourceShape_eq
    {pivot pivot' : B256} {left right left' right' : Func}
    (hp : pivot = pivot')
    (hl : persistentSourceShape left = persistentSourceShape left')
    (hr : persistentSourceShape right = persistentSourceShape right') :
    persistentSourceShape (splitDispatch pivot left right) =
      persistentSourceShape (splitDispatch pivot' left' right') := by
  subst pivot'
  simp [splitDispatch, persistentSourceShape, hl, hr]

theorem firstSelector_eq_of_persistentDispatchEntryShapes_eq
    {xs ys : List (B256 × Func)}
    (h : persistentDispatchEntryShapes xs =
      persistentDispatchEntryShapes ys) :
    firstSelector xs = firstSelector ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [persistentDispatchEntryShapes] at h
  | cons x xs =>
      cases ys with
      | nil => simp [persistentDispatchEntryShapes] at h
      | cons y ys =>
          have hhead :
              (x.1, persistentSourceShape x.2) =
                (y.1, persistentSourceShape y.2) := by
            simpa [persistentDispatchEntryShapes] using
              congrArg List.head? h
          simpa [firstSelector] using congrArg Prod.fst hhead

theorem hybridDispatchWith_persistentSourceShape_eq
    {xs ys : List (B256 × Func)}
    (h : persistentDispatchEntryShapes xs =
      persistentDispatchEntryShapes ys) (k : Nat) :
    persistentSourceShape (hybridDispatchWith k xs) =
      persistentSourceShape (hybridDispatchWith k ys) := by
  have htake (n : Nat) :
      persistentDispatchEntryShapes (xs.take n) =
        persistentDispatchEntryShapes (ys.take n) := by
    simpa [persistentDispatchEntryShapes] using congrArg (List.take n) h
  have hdrop (n : Nat) :
      persistentDispatchEntryShapes (xs.drop n) =
        persistentDispatchEntryShapes (ys.drop n) := by
    simpa [persistentDispatchEntryShapes] using congrArg (List.drop n) h
  have hslice (drop take : Nat) :
      persistentDispatchEntryShapes ((xs.drop drop).take take) =
        persistentDispatchEntryShapes ((ys.drop drop).take take) := by
    simpa [persistentDispatchEntryShapes] using
      congrArg (List.take take) (hdrop drop)
  unfold hybridDispatchWith
  apply splitDispatch_persistentSourceShape_eq
  · exact firstSelector_eq_of_persistentDispatchEntryShapes_eq (hslice 9 4)
  · apply splitDispatch_persistentSourceShape_eq
    · exact firstSelector_eq_of_persistentDispatchEntryShapes_eq (hslice 5 4)
    · exact linearDispatchWith_persistentSourceShape_eq (htake 5) k
    · exact linearDispatchWith_persistentSourceShape_eq (hslice 5 4) k
  · apply splitDispatch_persistentSourceShape_eq
    · exact firstSelector_eq_of_persistentDispatchEntryShapes_eq (hdrop 13)
    · exact linearDispatchWith_persistentSourceShape_eq (hslice 9 4) k
    · exact linearDispatchWith_persistentSourceShape_eq (hdrop 13) k

set_option maxHeartbeats 800000 in
theorem runtimePersistentEntryShapes_eq (dp : DeployParams) :
    persistentDispatchEntryShapes (funcs dp) =
      persistentDispatchEntryShapes (funcs ⟨0, 0, 0, 0, 0⟩) := by
  rfl

theorem prepend_persistentSourceShape_eq (line : Line) {body body' : Func}
    (h : persistentSourceShape body = persistentSourceShape body') :
    persistentSourceShape (line +++ body) =
      persistentSourceShape (line +++ body') := by
  induction line with
  | nil => exact h
  | cons instruction line ih =>
      simp [prepend, persistentSourceShape, ih]

theorem runtimeMain_persistentSourceShape_eq_zero (dp : DeployParams) :
    persistentSourceShape (runtimeMain dp) =
      persistentSourceShape (runtimeMain ⟨0, 0, 0, 0, 0⟩) := by
  have dispatchShape := hybridDispatchWith_persistentSourceShape_eq
    (runtimePersistentEntryShapes_eq dp) fallbackSlot
  have prefixedShape := prepend_persistentSourceShape_eq fsig dispatchShape
  unfold runtimeMain
  exact prepend_persistentSourceShape_eq
    [callvalue, pushB256 4, calldatasize, lt, Ninst.or] <| by
      simp [persistentSourceShape, prefixedShape]

/-- The complete persistent source shape is independent of all five deployed
words.  This is stronger than a cardinality claim: the full function/path/PC
map of retained SSTOREs is fixed. -/
theorem runtime_persistentProgramShape_eq_zero (dp : DeployParams) :
    persistentProgramShape (runtime dp) =
      persistentProgramShape (runtime ⟨0, 0, 0, 0, 0⟩) := by
  simp [runtime, persistentProgramShape,
    runtimeMain_persistentSourceShape_eq_zero dp]

theorem runtime_persistentProgramShape_eq (dp : DeployParams) :
    persistentProgramShape (runtime dp) =
      persistentProgramShape (runtime officialParams) :=
  (runtime_persistentProgramShape_eq_zero dp).trans
    (runtime_persistentProgramShape_eq_zero officialParams).symm

theorem runtimePersistentSourceSites_eq_official (dp : DeployParams) :
    runtimePersistentSourceSites dp =
      runtimePersistentSourceSites officialParams := by
  change (runtime dp).sourceSites.filter
      (fun site => isPersistentWriteInstruction site.instruction) =
    (runtime officialParams).sourceSites.filter
      (fun site => isPersistentWriteInstruction site.instruction)
  calc
    _ = ((runtime dp).sourceSites.filter fun site =>
        isNonPushInstruction site.instruction).filter
          (fun site => isPersistentWriteInstruction site.instruction) :=
      (filterPersistent_nonPush _).symm
    _ = (persistentProgramShape (runtime dp)).sourceSites.filter
          (fun site => isPersistentWriteInstruction site.instruction) := by
      rw [persistentProgramSourceSites_eq]
    _ = (persistentProgramShape
          (runtime officialParams)).sourceSites.filter
          (fun site => isPersistentWriteInstruction site.instruction) := by
      rw [runtime_persistentProgramShape_eq]
    _ = ((runtime officialParams).sourceSites.filter fun site =>
        isNonPushInstruction site.instruction).filter
          (fun site => isPersistentWriteInstruction site.instruction) := by
      rw [persistentProgramSourceSites_eq]
    _ = _ := filterPersistent_nonPush _

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem runtimeSourceEffectPcs_official :
    let sites :=
      (persistentProgramShape (runtime officialParams)).sourceSites
    (((sites.filter fun site =>
          isPersistentWriteInstruction site.instruction).map
            (fun site => site.pc),
       (sites.filter fun site =>
          isTransientWriteInstruction site.instruction).map
            (fun site => site.pc)),
      (sites.filter fun site =>
        isExternalCallInstruction site.instruction).map
          (fun site => site.pc)) =
    (([413, 1333, 1745, 2287, 2374, 2474, 2517, 2555, 2650, 2827,
       2870, 2910, 2952, 2992, 3212, 3302, 3441, 3586, 3912, 4032],
      [853, 3985, 4105]),
     [3679, 3707]) := by
  decide +kernel

/-- Exact compiled PCs of the twenty structural runtime SSTORE sites, in
source/compiler order. -/
theorem runtimePersistentSourceSites_pcs (dp : DeployParams) :
    (runtimePersistentSourceSites dp).map (fun site => site.pc) =
      [413, 1333, 1745, 2287, 2374, 2474, 2517, 2555, 2650, 2827,
       2870, 2910, 2952, 2992, 3212, 3302, 3441, 3586, 3912, 4032] := by
  unfold runtimePersistentSourceSites
  rw [← filterPersistent_nonPush, persistentProgramSourceSites_eq,
    runtime_persistentProgramShape_eq]
  simpa using congrArg (fun inventory => inventory.1.1)
    runtimeSourceEffectPcs_official

theorem runtimePersistentSourceSites_length (dp : DeployParams) :
    (runtimePersistentSourceSites dp).length = 20 := by
  have exactLength := congrArg List.length
    (runtimePersistentSourceSites_pcs dp)
  simpa using exactLength

theorem runtimePersistentSourceSites_nodup (dp : DeployParams) :
    (runtimePersistentSourceSites dp).Nodup := by
  apply List.Nodup.of_map (fun site => site.pc)
  rw [runtimePersistentSourceSites_pcs]
  decide

theorem map_getElem?_range {α : Type} (xs : List α) :
    (List.range xs.length).map (fun index => xs[index]?) =
      xs.map some := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      rw [List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.getElem?_cons_zero]
      congr 1
      rw [List.map_map]
      have hfun :
          ((fun index => (head :: tail)[index]?) ∘ Nat.succ) =
            fun index => tail[index]? := by
        funext index
        simp [Function.comp_apply, Nat.succ_eq_add_one]
      rw [hfun, ih]

theorem RuntimePersistentWrite.all_indices :
    RuntimePersistentWrite.all.map RuntimePersistentWrite.index =
      List.range 20 := by
  decide

/-- The row list and the structural source list are the same finite domain,
not merely lists with the same size. -/
theorem RuntimePersistentWrite.sourceSites_exact (dp : DeployParams) :
    RuntimePersistentWrite.all.map
        (RuntimePersistentWrite.sourceSite? dp) =
      (runtimePersistentSourceSites dp).map some := by
  unfold RuntimePersistentWrite.sourceSite?
  change (RuntimePersistentWrite.all.map
      RuntimePersistentWrite.index).map
        (fun index => (runtimePersistentSourceSites dp)[index]?) = _
  rw [RuntimePersistentWrite.all_indices,
    ← runtimePersistentSourceSites_length]
  exact map_getElem?_range _

/-- Every structural runtime SSTORE is accounted for by one typed row, and
every typed row accounts for an actual structural runtime SSTORE. -/
theorem runtimePersistentSourceSite_iff_row
    {dp : DeployParams} {site : Prog.SourceSite} :
    site ∈ runtimePersistentSourceSites dp ↔
      ∃ row ∈ RuntimePersistentWrite.all,
        row.sourceSite? dp = some site := by
  constructor
  · intro member
    have mapped : some site ∈
        (runtimePersistentSourceSites dp).map some :=
      List.mem_map.mpr ⟨site, member, rfl⟩
    rw [← RuntimePersistentWrite.sourceSites_exact] at mapped
    rcases List.mem_map.mp mapped with ⟨row, row_mem, found⟩
    exact ⟨row, row_mem, found⟩
  · rintro ⟨row, row_mem, found⟩
    have mapped : row.sourceSite? dp ∈
        RuntimePersistentWrite.all.map
          (RuntimePersistentWrite.sourceSite? dp) :=
      List.mem_map.mpr ⟨row, row_mem, rfl⟩
    rw [RuntimePersistentWrite.sourceSites_exact, found] at mapped
    rcases List.mem_map.mp mapped with
      ⟨candidate, candidate_mem, candidate_eq⟩
    simp only [Option.some.injEq] at candidate_eq
    simpa [candidate_eq] using candidate_mem

theorem RuntimePersistentWrite.index_injective :
    Function.Injective RuntimePersistentWrite.index := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [RuntimePersistentWrite.index]

/-- Structural source ownership is unique: two typed rows cannot name the
same full source site. -/
theorem RuntimePersistentWrite.sourceSite?_injective
    {dp : DeployParams} {left right : RuntimePersistentWrite}
    {site : Prog.SourceSite}
    (left_found : left.sourceSite? dp = some site)
    (right_found : right.sourceSite? dp = some site) :
    left = right := by
  have bound : left.index < (runtimePersistentSourceSites dp).length := by
    rw [runtimePersistentSourceSites_length]
    exact left.index_lt
  have index_eq := (List.getElem?_inj bound
    (runtimePersistentSourceSites_nodup dp)).mp
      (left_found.trans right_found.symm)
  exact RuntimePersistentWrite.index_injective index_eq

/-- A successful classifier result names the exact source path and PC of its
typed row. -/
theorem classifyRuntimePersistentWrite_sound
    {dp : DeployParams} {path : Prog.SourcePath} {pc : Nat}
    {row : RuntimePersistentWrite}
    (classified : classifyRuntimePersistentWrite dp path pc = some row) :
    ∃ site, row.sourceSite? dp = some site ∧
      site.path = path ∧ site.pc = pc := by
  have matched := List.find?_some classified
  unfold RuntimePersistentWrite.matchesSource at matched
  split at matched
  next hnone => simp at matched
  next site hsite =>
    simp only [Bool.and_eq_true, beq_iff_eq] at matched
    exact ⟨site, hsite, matched.1, matched.2⟩

theorem List.find?_eq_some_of_mem_of_unique
    {α : Type} {predicate : α → Bool} {xs : List α} {target : α}
    (member : target ∈ xs)
    (target_matches : predicate target = true)
    (unique : ∀ candidate ∈ xs,
      predicate candidate = true → candidate = target) :
    xs.find? predicate = some target := by
  induction xs with
  | nil => simp at member
  | cons head tail ih =>
      rw [List.find?]
      cases found : predicate head with
      | false =>
          simp
          apply ih
          · rcases List.mem_cons.mp member with head_eq | tail_mem
            · subst head
              rw [target_matches] at found
              contradiction
            · exact tail_mem
          · intro candidate candidate_mem candidate_matches
            exact unique candidate
              (List.mem_cons_of_mem head candidate_mem) candidate_matches
      | true =>
          simp
          rw [unique head (by simp) found]

/-- Conversely, classifying the exact path and PC of any row returns that row,
not merely some member of a cardinality-matched list. -/
theorem classifyRuntimePersistentWrite_complete
    {dp : DeployParams} {row : RuntimePersistentWrite}
    {site : Prog.SourceSite}
    (found : row.sourceSite? dp = some site) :
    classifyRuntimePersistentWrite dp site.path site.pc = some row := by
  unfold classifyRuntimePersistentWrite
  apply List.find?_eq_some_of_mem_of_unique
  · cases row <;> simp [RuntimePersistentWrite.all]
  · unfold RuntimePersistentWrite.matchesSource
    rw [found]
    simp
  · intro candidate candidate_mem candidate_matches
    unfold RuntimePersistentWrite.matchesSource at candidate_matches
    split at candidate_matches
    next hnone => simp at candidate_matches
    next candidateSite candidate_found =>
      simp only [Bool.and_eq_true, beq_iff_eq] at candidate_matches
      have candidate_sound := candidate.sourceSite?_sound candidate_found
      have target_sound := row.sourceSite?_sound found
      have site_eq : candidateSite = site := by
        cases candidateSite
        cases site
        simp_all
      rw [site_eq] at candidate_found
      exact RuntimePersistentWrite.sourceSite?_injective
        candidate_found found

/-- Every typed row decodes to the exact SSTORE instruction in any bytecode
array certified as the compilation of this parameterized runtime. -/
theorem RuntimePersistentWrite.sourceSite?_compiledAt
    {dp : DeployParams} {row : RuntimePersistentWrite}
    {site : Prog.SourceSite} {code : ByteArray}
    (compiled : some code.toList = (runtime dp).compile)
    (found : row.sourceSite? dp = some site) :
    Ninst.At code site.pc (.reg .sstore) := by
  have sound := row.sourceSite?_sound found
  simpa [sound.2] using (runtime dp).sourceSites_sound compiled sound.1

/-! ## Separation from transient, external-call, and constructor domains -/

def runtimeTransientSourceSites (dp : DeployParams) : List Prog.SourceSite :=
  (runtime dp).sourceSites.filter fun site =>
    isTransientWriteInstruction site.instruction

def runtimeExternalCallSourceSites (dp : DeployParams) :
    List Prog.SourceSite :=
  (runtime dp).sourceSites.filter fun site =>
    isExternalCallInstruction site.instruction

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 10000 in
theorem runtimeTransientSourceSites_pcs (dp : DeployParams) :
    (runtimeTransientSourceSites dp).map (fun site => site.pc) =
      [853, 3985, 4105] := by
  unfold runtimeTransientSourceSites
  rw [← filterTransient_nonPush, persistentProgramSourceSites_eq,
    runtime_persistentProgramShape_eq]
  simpa using congrArg (fun inventory => inventory.1.2)
    runtimeSourceEffectPcs_official

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 10000 in
theorem runtimeExternalCallSourceSites_pcs (dp : DeployParams) :
    (runtimeExternalCallSourceSites dp).map (fun site => site.pc) =
      [3679, 3707] := by
  unfold runtimeExternalCallSourceSites
  rw [← filterExternal_nonPush, persistentProgramSourceSites_eq,
    runtime_persistentProgramShape_eq]
  simpa using congrArg (fun inventory => inventory.2)
    runtimeSourceEffectPcs_official

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 10000 in
theorem runtimeExternalCallInstructions_official :
    let sites :=
      (persistentProgramShape (runtime officialParams)).sourceSites
    (sites.filter fun site =>
        isExternalCallInstruction site.instruction).map
          (fun site => externalInstruction? site.instruction) =
      [some .call, some .statcall] := by
  decide +kernel

/-- Exact execution opcodes of the two structural runtime external-call sites,
in source/compiler order. -/
theorem runtimeExternalCallSourceSites_instructions (dp : DeployParams) :
    (runtimeExternalCallSourceSites dp).map
        (fun site => externalInstruction? site.instruction) =
      [some .call, some .statcall] := by
  unfold runtimeExternalCallSourceSites
  rw [← filterExternal_nonPush, persistentProgramSourceSites_eq,
    runtime_persistentProgramShape_eq]
  exact runtimeExternalCallInstructions_official

theorem runtimeTransientSourceSites_length (dp : DeployParams) :
    (runtimeTransientSourceSites dp).length = 3 := by
  simpa using congrArg List.length (runtimeTransientSourceSites_pcs dp)

theorem runtimeExternalCallSourceSites_length (dp : DeployParams) :
    (runtimeExternalCallSourceSites dp).length = 2 := by
  simpa using congrArg List.length (runtimeExternalCallSourceSites_pcs dp)

theorem runtimeTransientSourceSite_instruction
    {dp : DeployParams} {site : Prog.SourceSite}
    (member : site ∈ runtimeTransientSourceSites dp) :
    site.instruction = .reg .tstore := by
  unfold runtimeTransientSourceSites at member
  rw [List.mem_filter] at member
  rcases site with ⟨path, pc, instruction⟩
  cases instruction with
  | reg regular => cases regular <;> simp_all [isTransientWriteInstruction]
  | exec execution => simp_all [isTransientWriteInstruction]
  | push bytes bound => simp_all [isTransientWriteInstruction]

theorem runtimeExternalCallSourceSite_instruction
    {dp : DeployParams} {site : Prog.SourceSite}
    (member : site ∈ runtimeExternalCallSourceSites dp) :
    ∃ instruction, site.instruction = .exec instruction := by
  unfold runtimeExternalCallSourceSites at member
  rw [List.mem_filter] at member
  rcases site with ⟨path, pc, instruction⟩
  cases instruction with
  | reg regular => simp_all [isExternalCallInstruction]
  | exec execution => exact ⟨execution, rfl⟩
  | push bytes bound => simp_all [isExternalCallInstruction]

/-- Every structural runtime external edge is exactly CALL or STATICCALL;
CALLCODE and DELEGATECALL are absent. -/
theorem runtimeExternalCallSourceSite_instruction_exact
    {dp : DeployParams} {site : Prog.SourceSite}
    (member : site ∈ runtimeExternalCallSourceSites dp) :
    site.instruction = .exec .call ∨
      site.instruction = .exec .statcall := by
  have projected : externalInstruction? site.instruction ∈
      (runtimeExternalCallSourceSites dp).map
        (fun source => externalInstruction? source.instruction) := by
    rw [List.mem_map]
    exact ⟨site, member, rfl⟩
  rw [runtimeExternalCallSourceSites_instructions] at projected
  rcases runtimeExternalCallSourceSite_instruction member with
    ⟨instruction, instructionEq⟩
  rw [instructionEq] at projected ⊢
  simpa [externalInstruction?] using projected

/-- Any actually reached same-frame execution opcode in an exact runtime
invocation is one of the runtime's two structural external edges.  The
`ParentPrefix` premise is the executable-boundary evidence that excludes
opcode-looking bytes inside PUSH payloads. -/
theorem runtimeExec_instruction_exact
    {dp : DeployParams} {ca : Adr} {root target : Exec.Deriv}
    {instruction : Xinst}
    (invocation : root.exactInvocation (runtime dp) ca ca)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (instructionAt : Ninst.At target.sevm.code target.pc
      (.exec instruction)) :
    instruction = .call ∨ instruction = .statcall := by
  rcases root.nonPush_sourceSite invocation sameFrame (by trivial)
      instructionAt with ⟨site, member, sitePc, siteInstruction⟩
  have external : site ∈ runtimeExternalCallSourceSites dp := by
    unfold runtimeExternalCallSourceSites
    rw [List.mem_filter]
    exact ⟨member, by simp [siteInstruction, isExternalCallInstruction]⟩
  rcases runtimeExternalCallSourceSite_instruction_exact external with
    callEq | statcallEq
  · rw [siteInstruction] at callEq
    exact Or.inl (by simpa using callEq)
  · rw [siteInstruction] at statcallEq
    exact Or.inr (by simpa using statcallEq)

theorem runtimePersistent_effectDomains_separate
    {dp : DeployParams} {site : Prog.SourceSite}
    (member : site ∈ runtimePersistentSourceSites dp) :
    site ∉ runtimeTransientSourceSites dp ∧
      site ∉ runtimeExternalCallSourceSites dp := by
  have instruction : site.instruction = .reg .sstore := by
    unfold runtimePersistentSourceSites at member
    rw [List.mem_filter] at member
    rcases site with ⟨path, pc, inst⟩
    cases inst with
    | reg regular =>
        cases regular <;> simp_all [isPersistentWriteInstruction]
    | exec execution => simp_all [isPersistentWriteInstruction]
    | push bytes bound => simp_all [isPersistentWriteInstruction]
  constructor
  · intro transient
    rw [runtimeTransientSourceSite_instruction transient] at instruction
    cases instruction
  · intro external
    rcases runtimeExternalCallSourceSite_instruction external with
      ⟨externalInstruction, externalEq⟩
    rw [externalEq] at instruction
    cases instruction

/-- Constructor effects are a separate 2/0/0 program domain, not members of
the runtime's 20/3/2 source map. -/
theorem constructorProgramSiteCounts_exact :
    constructorProgramSiteCounts = (2, 0, 0) :=
  constructor_program_site_counts_exact

end Blanc.LidoCircuitBreaker
