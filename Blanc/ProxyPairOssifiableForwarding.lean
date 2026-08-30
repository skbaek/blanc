import Blanc.ProxyPairOssifiableProgram
import Blanc.DelegatecallEnvelope
import Blanc.ExecutionMessageEffects
import Blanc.MessageExecution

/-!
# Generic forwarding envelope for OssifiableProxy

The child named here is the exact message spawned by the runtime's
`DELEGATECALL`.  The wrapper observation deliberately omits gas and warm-set
bookkeeping.  Moving an implementation property from an ordinary direct call
to this child remains the separate `DirectTargetTransport` obligation from
`Blanc.DelegatecallEnvelope`.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- The compiler table in which the runtime fallback executes. -/
def ossifiableRuntimeFunctions : List Func :=
  runtimeBaseline.main :: runtimeBaseline.aux

/-- The state immediately after a clean delegated child is resumed. -/
def forwardingCleanResume
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm) : Devm :=
  (((incorporateChildOnSuccess d.parent child child.output).setMach
      ⟨1 :: d.parent.stack, d.parent.memory,
        d.parent.gasLeft + child.gasLeft⟩).memWrite
    d.outputOffsetWord.toNat (child.output.take d.outputSizeWord.toNat))

/-- The state immediately after a settled failing child is resumed. -/
def forwardingFailedResume
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm) : Devm :=
  (((incorporateChildOnError d.parent child child.output).setMach
      ⟨0 :: d.parent.stack, d.parent.memory,
        d.parent.gasLeft + child.gasLeft⟩).memWrite
    d.outputOffsetWord.toNat (child.output.take d.outputSizeWord.toNat))

/-- Memory left after the forwarding tail copies and reads the complete child
output at offset zero. -/
def forwardingCopiedMemory (resume : Devm) (output : Bytes) : Mem :=
  ((resume.memory.write 0 output).read 0 output.length).2

/-- Exact frame-local gas charged by the successful returndata tail. -/
def forwardingCleanTailCost (resume : Devm) : Nat :=
  30 + gReturnDataCopy * ceilDiv resume.returnData.length 32 +
    resume.extCost [⟨0, resume.returnData.length⟩]

/-- Exact frame-local gas charged by the reverting returndata tail. -/
def forwardingFailedTailCost (resume : Devm) : Nat :=
  29 + gReturnDataCopy * ceilDiv resume.returnData.length 32 +
    resume.extCost [⟨0, resume.returnData.length⟩]

/-- Exact clean raw endpoint of the wrapper tail. -/
def forwardingCleanPost
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) : Devm :=
  ((forwardingCleanResume d child).setMach
      ⟨d.parent.stack, forwardingCopiedMemory
        (forwardingCleanResume d child) child.output, gas⟩).withOutput
    child.output

/-- Exact reverting raw endpoint of the wrapper tail. -/
def forwardingFailedPost
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) : Devm :=
  ((forwardingFailedResume d child).setMach
      ⟨d.parent.stack, forwardingCopiedMemory
        (forwardingFailedResume d child) child.output, gas⟩).withOutput
    child.output

@[simp] theorem forwardingCleanPost_error
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).error = d.parent.error := rfl

@[simp] theorem forwardingCleanPost_output
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).output = child.output := rfl

@[simp] theorem forwardingCleanPost_logs
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).logs =
      d.parent.logs ++ child.logs := rfl

@[simp] theorem forwardingCleanPost_state
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).state = child.state := rfl

@[simp] theorem forwardingCleanPost_transientStorage
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).transientStorage =
      child.transientStorage := rfl

@[simp] theorem forwardingFailedPost_output
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingFailedPost d child gas).output = child.output := rfl

@[simp] theorem forwardingFailedPost_logs
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingFailedPost d child gas).logs = d.parent.logs := rfl

/-- Reading back the complete byte string just written at offset zero returns
that string. -/
private theorem forwardingReadCopiedMemory
    (memory : Mem) (output : Bytes) :
    ((memory.write 0 output).read 0 output.length).1 = output := by
  cases output with
  | nil => rfl
  | cons byte bytes => exact Mem.read_write_zero memory (by simp)

/-- Writing at offset zero preserves word alignment (when the old image is
large enough) or expands to a word boundary, and always covers the payload. -/
private theorem forwardingCopiedMemory_shape
    (memory : Mem) (output : Bytes)
    (aligned : memory.size % 32 = 0) :
    let copied := memory.write 0 output
    copied.size % 32 = 0 ∧ output.length ≤ copied.size := by
  let copied := memory.write 0 output
  constructor
  · rcases houtput : output with _ | ⟨byte, bytes⟩
    · simpa [copied, houtput, Mem.write] using aligned
    · rw [Mem.size_write_cons]
      split
      · exact aligned
      · rw [ceil32_eq_mul]
        omega
  · rcases houtput : output with _ | ⟨byte, bytes⟩
    · simp
    · rw [Mem.size_write_cons]
      split
      · omega
      · simpa using Nat.le_ceil32 (byte :: bytes).length

@[simp] theorem forwardingCleanResume_returnData
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm) :
    (forwardingCleanResume d child).returnData = child.output := rfl

@[simp] theorem forwardingCleanResume_stack
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm) :
    (forwardingCleanResume d child).stack = 1 :: d.parent.stack := rfl

@[simp] theorem forwardingFailedResume_returnData
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm) :
    (forwardingFailedResume d child).returnData = child.output := rfl

@[simp] theorem forwardingFailedResume_stack
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm) :
    (forwardingFailedResume d child).stack = 0 :: d.parent.stack := rfl

/-- Primitive resource facts from which the exact forwarding returndata tail
is constructed.  This certificate assumes neither a tail walk nor an outer
message result. -/
inductive ForwardingTailBudget
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) : Type
  | clean
      (status : child.error.isSome = false)
      (outputLength : child.output.length < 2 ^ 256)
      (memoryAligned :
        (forwardingCleanResume d child).memory.size % 32 = 0)
      (stackRoom : d.parent.stack.length < 1020)
      (gas : Nat)
      (budget : (forwardingCleanResume d child).gasLeft =
        gas + forwardingCleanTailCost (forwardingCleanResume d child)) :
      ForwardingTailBudget d child
  | failed
      (status : child.error.isSome = true)
      (outputLength : child.output.length < 2 ^ 256)
      (memoryAligned :
        (forwardingFailedResume d child).memory.size % 32 = 0)
      (stackRoom : d.parent.stack.length < 1020)
      (gas : Nat)
      (budget : (forwardingFailedResume d child).gasLeft =
        gas + forwardingFailedTailCost (forwardingFailedResume d child)) :
      ForwardingTailBudget d child

/-- A clean tail walk derived solely from explicit length, alignment, stack,
and gas resources. -/
theorem forwardingCleanTailRun_of_budget
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm)
    (outputLength : child.output.length < 2 ^ 256)
    (memoryAligned :
      (forwardingCleanResume d child).memory.size % 32 = 0)
    (stackRoom : d.parent.stack.length < 1020)
    (gas : Nat)
    (budget : (forwardingCleanResume d child).gasLeft =
      gas + forwardingCleanTailCost (forwardingCleanResume d child)) :
    Func.RunCompiledTo ossifiableRuntimeFunctions sevm
      (forwardingCleanResume d child) proxyReturnTail
      (.ok (forwardingCleanPost d child gas)) := by
  let resume := forwardingCleanResume d child
  let n := child.output.length
  let w := Nat.toB256 n
  let copyCost := gVerylow + gReturnDataCopy * ceilDiv n 32 +
    resume.extCost [⟨0, n⟩]
  let copied := resume.memory.write 0 child.output
  have wordRoundtrip : w.toNat = n :=
    B256.toNat_toB256_of_lt outputLength
  have copiedShape := forwardingCopiedMemory_shape
    resume.memory child.output memoryAligned
  have copiedAligned : copied.size % 32 = 0 := copiedShape.1
  have copiedCovers : n ≤ copied.size := copiedShape.2
  have terminalExt :
      (resume.setMach
        ⟨0 :: w :: d.parent.stack, copied, gas⟩).extCost
          [⟨0, w.toNat⟩] = 0 := by
    rw [wordRoundtrip]
    exact Devm.extCost_zero_of_le copiedAligned (by omega)
  have copiedRead : (copied.read 0 n).1 = child.output :=
    forwardingReadCopiedMemory resume.memory child.output
  change Func.RunCompiledTo ossifiableRuntimeFunctions sevm resume
    (pushB256 0 ::: retdatasize ::: pushB256 0 ::: pushB256 0 :::
      retdatacopy ::: retdatasize ::: swap 1 :::
      Func.branch (Func.last .rev) (Func.last .ret)) _
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
      (G := gas + (25 + copyCost)) pushCost_zero ?_ ?_) ?_
  · have budget' : resume.gasLeft =
        gas + forwardingCleanTailCost resume := budget
    have returnData : resume.returnData = child.output := by
      simpa only [resume] using forwardingCleanResume_returnData d child
    rw [budget']
    unfold forwardingCleanTailCost
    rw [returnData]
    dsimp only [copyCost, n]
    unfold gBase gVerylow
    omega
  · change (1 :: d.parent.stack).length < 1024
    simp only [List.length_cons]
    omega
  · try simp only [Devm.setMach_setMach]
    refine Func.RunCompiledTo.next
      (Ninst.runCompiled_pushItem (r := .retdatasize) (x := w)
        (cost := gBase) (G := gas + (23 + copyCost))
        (by rintro ⟨⟩) ?_ ?_ ?_) ?_
    · rfl
    · simp only [Devm.gasLeft_setMach]
      unfold gBase
      omega
    · simp only [resume, forwardingCleanResume_stack,
        Devm.stack_setMach, List.length_cons]
      omega
    · refine Func.RunCompiledTo.next
        (Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
          (G := gas + (21 + copyCost)) pushCost_zero
          (by simp only [Devm.gasLeft_setMach]; unfold gBase; omega)
          (by simp only [resume, forwardingCleanResume_stack,
            Devm.stack_setMach, List.length_cons]; omega)) ?_
      simp only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.stack_setMach]
      refine Func.RunCompiledTo.next
        (Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
          (G := gas + (19 + copyCost)) pushCost_zero
          (by simp only [Devm.gasLeft_setMach]; unfold gBase; omega)
          (by simp only [resume, forwardingCleanResume_stack,
            Devm.stack_setMach, List.length_cons]; omega)) ?_
      simp only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.stack_setMach]
      refine Func.RunCompiledTo.next
        (Ninst.runCompiled_retdatacopy_of
          (di := 0) (ri := 0) (sz := w)
          (s := 0 :: 1 :: d.parent.stack)
          (c := copyCost) (G := gas + 19) (M := copied)
          rfl ?_ ?_ ?_ ?_) ?_
      · dsimp only [copyCost]
        simp only [resume, Devm.extCost, Devm.memory_setMach,
          memExtsSize, B256.toNat_zero, wordRoundtrip]
      · simp only [resume, Devm.returnData_setMach,
          forwardingCleanResume_returnData, B256.toNat_zero,
          wordRoundtrip, Nat.zero_add]
        exact Nat.le_refl _
      · dsimp only [copied]
        simp only [resume, Devm.memory_setMach, Devm.returnData_setMach,
          forwardingCleanResume_returnData, B256.toNat_zero,
          wordRoundtrip, List.sliceD, List.drop_zero]
        rw [List.takeD_eq_self (0 : UInt8) rfl]
      · simp only [Devm.gasLeft_setMach]
        omega
      · simp only [Devm.setMach_setMach]
        refine Func.RunCompiledTo.next
          (Ninst.runCompiled_pushItem (r := .retdatasize) (x := w)
            (cost := gBase) (G := gas + 17)
            (by rintro ⟨⟩) ?_
            (by
              simp only [resume, Devm.gasLeft_setMach]
              unfold gBase
              omega)
            (by simp only [resume, Devm.stack_setMach,
              List.length_cons]; omega)) ?_
        · rfl
        · refine Func.RunCompiledTo.next
            (Ninst.runCompiled_swap (n := 1)
              (S := 1 :: 0 :: w :: d.parent.stack)
              (G := gas + 14) rfl
              (by
                simp only [Devm.gasLeft_setMach]
                unfold gVerylow
                omega)) ?_
          try simp only [Devm.setMach_setMach, Devm.memory_setMach,
            Devm.stack_setMach]
          refine Func.runCompiledTo_branch_succ
            (w := 1) (s := 0 :: w :: d.parent.stack) (G := gas)
            (by decide) (by simp only [Devm.stack_setMach])
            (by
              simp only [Devm.stack_setMach, List.length_cons]
              omega)
            (by
              simp only [Devm.gasLeft_setMach]
              unfold gVerylow gHigh gJumpdest
              omega) ?_
          try simp only [Devm.setMach_setMach, Devm.memory_setMach]
          let readPost := resume.setMach
            ⟨d.parent.stack, (copied.read 0 n).2, gas⟩
          have terminalRead :
              (resume.setMach
                ⟨d.parent.stack, copied, gas⟩).memRead 0 n =
                ⟨child.output, readPost⟩ := by
            apply Prod.ext
            · change (copied.read 0 n).1 = child.output
              exact copiedRead
            · show (resume.setMach
                  ⟨d.parent.stack, copied, gas⟩).withMemory
                    (copied.read 0 n).2 = readPost
              apply Devm.eq_of_proj <;> rfl
          have terminalMemory := congrArg Prod.snd terminalRead
          have terminalRun := Func.runCompiledTo_ret_word
            (fs := ossifiableRuntimeFunctions) (sevm := sevm)
            (devm := resume.setMach
              ⟨0 :: w :: d.parent.stack, copied, gas⟩)
            (i := 0) (sz := w) (s := d.parent.stack)
            (out := child.output) (G := gas) (e := 0)
            rfl terminalExt (by simp) (by
              have outputRead := congrArg Prod.fst terminalRead
              simpa only [wordRoundtrip, B256.toNat_zero,
                Devm.setMach_setMach, Devm.memory_setMach] using outputRead)
          simpa [forwardingCleanPost, forwardingCopiedMemory,
            resume, copied, n, wordRoundtrip, readPost, terminalRead,
            terminalMemory, B256.toNat_zero,
            Devm.setMach_setMach, Devm.memory_setMach] using
            terminalRun

/-- A failing tail walk is likewise derived from primitive resources; its
terminal opcode is the wrapper's ordinary `REVERT`. -/
theorem forwardingFailedTailRun_of_budget
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm)
    (outputLength : child.output.length < 2 ^ 256)
    (memoryAligned :
      (forwardingFailedResume d child).memory.size % 32 = 0)
    (stackRoom : d.parent.stack.length < 1020)
    (gas : Nat)
    (budget : (forwardingFailedResume d child).gasLeft =
      gas + forwardingFailedTailCost (forwardingFailedResume d child)) :
    Func.RunCompiledTo ossifiableRuntimeFunctions sevm
      (forwardingFailedResume d child) proxyReturnTail
      (.error (.revert, forwardingFailedPost d child gas)) := by
  let resume := forwardingFailedResume d child
  let n := child.output.length
  let w := Nat.toB256 n
  let copyCost := gVerylow + gReturnDataCopy * ceilDiv n 32 +
    resume.extCost [⟨0, n⟩]
  let copied := resume.memory.write 0 child.output
  have wordRoundtrip : w.toNat = n :=
    B256.toNat_toB256_of_lt outputLength
  have copiedShape := forwardingCopiedMemory_shape
    resume.memory child.output memoryAligned
  have copiedAligned : copied.size % 32 = 0 := copiedShape.1
  have copiedCovers : n ≤ copied.size := copiedShape.2
  have terminalExt :
      (resume.setMach
        ⟨0 :: w :: d.parent.stack, copied, gas⟩).extCost
          [⟨0, w.toNat⟩] = 0 := by
    rw [wordRoundtrip]
    exact Devm.extCost_zero_of_le copiedAligned (by omega)
  have copiedRead : (copied.read 0 n).1 = child.output :=
    forwardingReadCopiedMemory resume.memory child.output
  change Func.RunCompiledTo ossifiableRuntimeFunctions sevm resume
    (pushB256 0 ::: retdatasize ::: pushB256 0 ::: pushB256 0 :::
      retdatacopy ::: retdatasize ::: swap 1 :::
      Func.branch (Func.last .rev) (Func.last .ret)) _
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
      (G := gas + (24 + copyCost)) pushCost_zero ?_ ?_) ?_
  · have budget' : resume.gasLeft =
        gas + forwardingFailedTailCost resume := budget
    have returnData : resume.returnData = child.output := by
      simpa only [resume] using forwardingFailedResume_returnData d child
    rw [budget']
    unfold forwardingFailedTailCost
    rw [returnData]
    dsimp only [copyCost, n]
    unfold gBase gVerylow
    omega
  · change (0 :: d.parent.stack).length < 1024
    simp only [List.length_cons]
    omega
  · try simp only [Devm.setMach_setMach]
    refine Func.RunCompiledTo.next
      (Ninst.runCompiled_pushItem (r := .retdatasize) (x := w)
        (cost := gBase) (G := gas + (22 + copyCost))
        (by rintro ⟨⟩) ?_ ?_ ?_) ?_
    · rfl
    · simp only [Devm.gasLeft_setMach]
      unfold gBase
      omega
    · simp only [resume, forwardingFailedResume_stack,
        Devm.stack_setMach, List.length_cons]
      omega
    · refine Func.RunCompiledTo.next
        (Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
          (G := gas + (20 + copyCost)) pushCost_zero
          (by simp only [Devm.gasLeft_setMach]; unfold gBase; omega)
          (by simp only [resume, forwardingFailedResume_stack,
            Devm.stack_setMach, List.length_cons]; omega)) ?_
      simp only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.stack_setMach]
      refine Func.RunCompiledTo.next
        (Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
          (G := gas + (18 + copyCost)) pushCost_zero
          (by simp only [Devm.gasLeft_setMach]; unfold gBase; omega)
          (by simp only [resume, forwardingFailedResume_stack,
            Devm.stack_setMach, List.length_cons]; omega)) ?_
      simp only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.stack_setMach]
      refine Func.RunCompiledTo.next
        (Ninst.runCompiled_retdatacopy_of
          (di := 0) (ri := 0) (sz := w)
          (s := 0 :: 0 :: d.parent.stack)
          (c := copyCost) (G := gas + 18) (M := copied)
          rfl ?_ ?_ ?_ ?_) ?_
      · dsimp only [copyCost]
        simp only [resume, Devm.extCost, Devm.memory_setMach,
          memExtsSize, B256.toNat_zero, wordRoundtrip]
      · simp only [resume, Devm.returnData_setMach,
          forwardingFailedResume_returnData, B256.toNat_zero,
          wordRoundtrip, Nat.zero_add]
        exact Nat.le_refl _
      · dsimp only [copied]
        simp only [resume, Devm.memory_setMach, Devm.returnData_setMach,
          forwardingFailedResume_returnData, B256.toNat_zero,
          wordRoundtrip, List.sliceD, List.drop_zero]
        rw [List.takeD_eq_self (0 : UInt8) rfl]
      · simp only [Devm.gasLeft_setMach]
        omega
      · simp only [Devm.setMach_setMach]
        refine Func.RunCompiledTo.next
          (Ninst.runCompiled_pushItem (r := .retdatasize) (x := w)
            (cost := gBase) (G := gas + 16)
            (by rintro ⟨⟩) ?_
            (by
              simp only [resume, Devm.gasLeft_setMach]
              unfold gBase
              omega)
            (by simp only [resume, Devm.stack_setMach,
              List.length_cons]; omega)) ?_
        · rfl
        · refine Func.RunCompiledTo.next
            (Ninst.runCompiled_swap (n := 1)
              (S := 0 :: 0 :: w :: d.parent.stack)
              (G := gas + 13) rfl
              (by
                simp only [Devm.gasLeft_setMach]
                unfold gVerylow
                omega)) ?_
          try simp only [Devm.setMach_setMach, Devm.memory_setMach,
            Devm.stack_setMach]
          refine Func.runCompiledTo_branch_zero
            (s := 0 :: w :: d.parent.stack) (G := gas)
            (by simp only [Devm.stack_setMach])
            (by
              simp only [Devm.stack_setMach, List.length_cons]
              omega)
            (by
              simp only [Devm.gasLeft_setMach]
              unfold gVerylow gHigh
              omega) ?_
          try simp only [Devm.setMach_setMach, Devm.memory_setMach]
          let readPost := resume.setMach
            ⟨d.parent.stack, (copied.read 0 n).2, gas⟩
          have terminalRead :
              ((resume.setMach
                ⟨d.parent.stack, copied, gas⟩).memRead 0 w.toNat) =
                ⟨child.output, readPost⟩ := by
            apply Prod.ext
            · change (copied.read 0 w.toNat).1 = child.output
              rw [wordRoundtrip]
              exact copiedRead
            · show (resume.setMach
                  ⟨d.parent.stack, copied, gas⟩).withMemory
                    (copied.read 0 w.toNat).2 = readPost
              simp only [readPost, wordRoundtrip]
              apply Devm.eq_of_proj <;> rfl
          have terminalRun := Func.runCompiledTo_rev_of
            (fs := ossifiableRuntimeFunctions) (sevm := sevm)
            (devm := resume.setMach
              ⟨0 :: w :: d.parent.stack, copied, gas⟩)
            (i := 0) (sz := w) (s := d.parent.stack)
            (out := child.output) (d' := readPost) (G := gas) (e := 0)
            rfl terminalExt (by simp) (by
              simpa only [B256.toNat_zero, Devm.setMach_setMach,
                Devm.memory_setMach] using
                terminalRead)
          simpa [forwardingFailedPost, forwardingCopiedMemory,
            resume, copied, n, wordRoundtrip, readPost, terminalRead,
            Devm.setMach_setMach, Devm.memory_setMach] using terminalRun

/-- Frame facts established by the runtime prefix before the exact
`DELEGATECALL`.  Storage is compared with the outer message's saved world
because a payable entry transfer may have changed balances but not storage. -/
structure ForwardingSettlementContext
    (outer : Msg)
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) : Prop where
  owner : sevm.currentTarget = outer.currentTarget
  parentStackRoom : d.parent.stack.length < 1024
  parentError : d.parent.error = none
  parentLogs : d.parent.logs = []
  parentStorage : MessageStorageEqualAt outer.currentTarget
    d.parent.state outer.benv.state
  parentTransient : MessageTransientEqualAt outer.currentTarget
    d.parent.transientStorage outer.tenv.transientStorage

private theorem clean_tail_relation
    (outer : Msg)
    {sevm : Sevm} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor sevm callPre}
    (context : ForwardingSettlementContext outer d)
    (child : Devm) (status : child.error.isSome = false) (gas : Nat) :
    ChildToWrapperSettledAt outer.currentTarget (.ok child)
      ((Frame.ofCall outer).settle
        (.ok (forwardingCleanPost d child gas))) := by
  have statusNone : child.error.isNone = true := by
    cases h : child.error <;> simp_all
  have statusEq : child.error = none := by
    cases h : child.error <;> simp_all
  have finalError : (forwardingCleanPost d child gas).error = none := by
    rw [forwardingCleanPost_error, context.parentError]
  have settledEq :
      (Frame.ofCall outer).settle
          (.ok (forwardingCleanPost d child gas)) =
        .ok (forwardingCleanPost d child gas) := by
    simp only [Frame.ofCall, Frame.settle, Frame.settleMsg,
      executeCode.handleError, processMessage.settle]
    change (if (forwardingCleanPost d child gas).error.isSome = true then
      Except.ok ((forwardingCleanPost d child gas).rollback
        outer.benv.state outer.tenv.transientStorage)
      else Except.ok (forwardingCleanPost d child gas)) =
        Except.ok (forwardingCleanPost d child gas)
    rw [finalError]
    rfl
  rw [settledEq]
  change ChildToWrapperOkAt outer.currentTarget child _
  refine {
    status := by
      rw [statusEq, forwardingCleanPost_error, context.parentError]
      exact DelegatecallStatusRelated.clean
    output := forwardingCleanPost_output d child gas
    logs := by
      rw [forwardingCleanPost_logs, context.parentLogs]
      simp [statusNone]
    storage := by
      intro key
      rw [forwardingCleanPost_state]
    transientStorage := by
      intro key
      rw [forwardingCleanPost_transientStorage] }

private theorem failed_tail_relation
    (outer : Msg)
    {sevm : Sevm} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor sevm callPre}
    (context : ForwardingSettlementContext outer d)
    (child : Devm)
    (certificate : DelegatedChildCertificate d.child (.ok child))
    (status : child.error.isSome = true) (gas : Nat) :
    ChildToWrapperSettledAt outer.currentTarget (.ok child)
      ((Frame.ofCall outer).settle
        (.error (.revert, forwardingFailedPost d child gas))) := by
  have childRollback := ProcessMessage.rollback_of_error
    certificate.process (by simp [status])
  have statusNone : child.error.isNone = false := by
    cases h : child.error <;> simp_all
  have settledEq :
      (Frame.ofCall outer).settle
          (.error (.revert, forwardingFailedPost d child gas)) =
        .ok (MessageExecution.settledRevert outer
          (forwardingFailedPost d child gas)) := rfl
  rw [settledEq]
  change ChildToWrapperOkAt outer.currentTarget child _
  refine {
    status := DelegatecallStatusRelated.failed status
    output := by
      rw [MessageExecution.settledRevert_output,
        forwardingFailedPost_output]
    logs := by
      rw [MessageExecution.settledRevert_logs,
        forwardingFailedPost_logs, context.parentLogs]
      simp [statusNone]
    storage := by
      intro key
      rw [childRollback.1]
      exact context.parentStorage key
    transientStorage := by
      intro key
      rw [childRollback.2]
      exact context.parentTransient key }

/-- At the exact call site, an explicitly certified arbitrary child execution
is wrapped with the proxy's status, returndata, log, and proxy-owned storage
semantics.  The fatal non-consensus channel propagates without entering the
tail; settled child failures take the ordinary wrapper `REVERT` arm. -/
theorem forwarding_atCall_execSat
    (outer : Msg)
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (context : ForwardingSettlementContext outer d)
    (childOut : MessageResult)
    (tail : match childOut with
      | .ok child => ForwardingTailBudget d child
      | .error _ => PUnit)
    (certificate : DelegatedChildCertificate d.child childOut) :
    Func.ExecSat ossifiableRuntimeFunctions sevm callPre
      (delcall ::: proxyReturnTail)
      (fun raw => ChildToWrapperSettledAt outer.currentTarget childOut
        ((Frame.ofCall outer).settle raw)) := by
  have childEnter := d.crossing.1
  have childResult :
      (Frame.ofCall d.child).settle (exec (initEvm d.child)) = childOut := by
    rw [← MessageExecution.processMessage_eq_settle_exec_of_enter
      d.child (initEvm d.child) childEnter]
    exact certificate.result
  cases childOut with
  | error failure =>
      rcases failure with ⟨error, state, created, tra⟩
      have resume : d.resume.run
          ((Frame.ofCall d.child).settle (exec (initEvm d.child))) =
          .error (error,
            (d.parent.withCreatedAccounts created).setWorld
              {d.parent.world with state := state, transientStorage := tra}) := by
        rw [childResult]
        rfl
      apply Func.execSat_next_error
        (Ninst.stepRun_exec_run_error d.step childEnter resume)
      have childNonConsensus : NonConsensus error := by
        exact handleError_error_inv
          (Frame.settle_error_inv (f := Frame.ofCall d.child) rfl childResult)
      have outerResult :
          (Frame.ofCall outer).settle
            (.error (error,
              (d.parent.withCreatedAccounts created).setWorld
                {d.parent.world with state := state, transientStorage := tra})) =
            .error (error, state, created, tra) := by
        cases error with
        | halt reason => exact (childNonConsensus (.halt reason) rfl).elim
        | revert => exact (childNonConsensus .revert rfl).elim
        | crypto reason => rfl
        | internal reason => rfl
      rw [outerResult]
      exact ⟨rfl, (fun _ => rfl), (fun _ => rfl)⟩
  | ok child =>
      cases tail with
      | clean status outputLength memoryAligned stackRoom gas budget =>
          have tailRun := forwardingCleanTailRun_of_budget d child
            outputLength memoryAligned stackRoom gas budget
          have resume : d.resume.run
              ((Frame.ofCall d.child).settle (exec (initEvm d.child))) =
              .ok (forwardingCleanResume d child) := by
            rw [childResult]
            simpa [DelegatecallSpawnDescriptor.resume,
              forwardingCleanResume] using
              (Resume.run_call_ok status context.parentStackRoom)
          have callRun : Ninst.RunCompiled sevm callPre
              (.exec .delcall) (forwardingCleanResume d child) :=
            Ninst.runCompiled_exec_run d.step childEnter resume
          apply Func.execSat_of_runCompiledTo
            (Func.RunCompiledTo.next callRun tailRun)
          exact clean_tail_relation outer context child status gas
      | failed status outputLength memoryAligned stackRoom gas budget =>
          have tailRun := forwardingFailedTailRun_of_budget d child
            outputLength memoryAligned stackRoom gas budget
          have resume : d.resume.run
              ((Frame.ofCall d.child).settle (exec (initEvm d.child))) =
              .ok (forwardingFailedResume d child) := by
            rw [childResult]
            simpa [DelegatecallSpawnDescriptor.resume,
              forwardingFailedResume] using
              (Resume.run_call_err status context.parentStackRoom)
          have callRun : Ninst.RunCompiled sevm callPre
              (.exec .delcall) (forwardingFailedResume d child) :=
            Ninst.runCompiled_exec_run d.step childEnter resume
          apply Func.execSat_of_runCompiledTo
            (Func.RunCompiledTo.next callRun tailRun)
          exact failed_tail_relation outer context child certificate status gas

/-! ## Selector-miss witnesses -/

/-- A census-level non-membership fact has exactly the orientation required by
the linear dispatcher fallback route. -/
theorem runtimeSelectors_miss_of_not_mem (sevm : Sevm)
    (miss : Sevm.selector sevm ∉ runtimeSelectors) :
    ∀ selector ∈ runtimeSelectors, selector ≠ Sevm.selector sevm := by
  intro selector member equal
  apply miss
  rwa [← equal]

private theorem runtimeSelectors_miss_of_selector_lowByte_zero
    (sevm : Sevm)
    (lowByte : (Sevm.selector sevm).2.2.toUInt8 = 0) :
    ∀ selector ∈ runtimeSelectors, selector ≠ Sevm.selector sevm := by
  intro selector member
  have selectorLowByteNonzero : selector.2.2.toUInt8 ≠ 0 := by
    rw [mem_runtimeSelectors_iff] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro collision
  apply selectorLowByteNonzero
  rw [collision, lowByte]

/-- Empty calldata misses every named OssifiableProxy selector. -/
theorem runtimeSelectors_miss_of_data_nil (sevm : Sevm)
    (data : sevm.data = []) :
    ∀ selector ∈ runtimeSelectors, selector ≠ Sevm.selector sevm := by
  apply runtimeSelectors_miss_of_selector_lowByte_zero
  rw [Sevm.selector_eq_toB256_takeD_four, data]
  simp [List.takeD, Bytes.toB256, Bytes.toB256.go]

/-- One-byte calldata is zero-padded by `CALLDATALOAD` and misses the census. -/
theorem runtimeSelectors_miss_of_data_one (sevm : Sevm) (b0 : UInt8)
    (data : sevm.data = [b0]) :
    ∀ selector ∈ runtimeSelectors, selector ≠ Sevm.selector sevm := by
  apply runtimeSelectors_miss_of_selector_lowByte_zero
  rw [Sevm.selector_eq_toB256_takeD_four, data]
  simp only [List.takeD, List.tail, List.headD,
    Bytes.toB256, Bytes.toB256.go]
  bv_decide

/-- Two-byte calldata is zero-padded and misses the census. -/
theorem runtimeSelectors_miss_of_data_two
    (sevm : Sevm) (b0 b1 : UInt8) (data : sevm.data = [b0, b1]) :
    ∀ selector ∈ runtimeSelectors, selector ≠ Sevm.selector sevm := by
  apply runtimeSelectors_miss_of_selector_lowByte_zero
  rw [Sevm.selector_eq_toB256_takeD_four, data]
  simp only [List.takeD, List.tail, List.headD,
    Bytes.toB256, Bytes.toB256.go]
  bv_decide

/-- Three-byte calldata is zero-padded and misses the census. -/
theorem runtimeSelectors_miss_of_data_three
    (sevm : Sevm) (b0 b1 b2 : UInt8)
    (data : sevm.data = [b0, b1, b2]) :
    ∀ selector ∈ runtimeSelectors, selector ≠ Sevm.selector sevm := by
  apply runtimeSelectors_miss_of_selector_lowByte_zero
  rw [Sevm.selector_eq_toB256_takeD_four, data]
  simp only [List.takeD, List.tail, List.headD,
    Bytes.toB256, Bytes.toB256.go]
  bv_decide

/-- The four concrete zero-padding witnesses packaged behind a length bound. -/
theorem runtimeSelectors_miss_of_shortData (sevm : Sevm)
    (short : sevm.data.length < 4) :
    ∀ selector ∈ runtimeSelectors, selector ≠ Sevm.selector sevm := by
  rcases data0 : sevm.data with _ | ⟨b0, tail0⟩
  · exact runtimeSelectors_miss_of_data_nil sevm data0
  · rcases data1 : tail0 with _ | ⟨b1, tail1⟩
    · exact runtimeSelectors_miss_of_data_one sevm b0 (by simp [data0, data1])
    · rcases data2 : tail1 with _ | ⟨b2, tail2⟩
      · exact runtimeSelectors_miss_of_data_two sevm b0 b1
          (by simp [data0, data1, data2])
      · rcases data3 : tail2 with _ | ⟨b3, tail3⟩
        · exact runtimeSelectors_miss_of_data_three sevm b0 b1 b2
            (by simp [data0, data1, data2, data3])
        · simp [data0, data1, data2, data3] at short
          omega

/-- Exact outer-runtime route to the named delegatecall descriptor.  The
`prefix` transformer is execution evidence, not an assumed wrapper result. -/
structure OssifiableForwardingRoute
    (outer : Msg) (afterTransfer : Benv)
    (callPre : Devm)
    (d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre) : Prop where
  transfer : outer.benvAfterTransfer = .ok afterTransfer
  target : outer.target = some outer.currentTarget
  codeAddress : outer.codeAddress = some outer.currentTarget
  proxyNotPrecompile :
    ¬ afterTransfer.stat.rules.isPrecomp outer.currentTarget
  runtimeInstalled : outer.code = runtimeBaselineCode
  runtimeCodeLink : outer.code =
    (outer.benv.state.get outer.currentTarget).code
  selectorMiss : ∀ selector ∈ runtimeSelectors,
    selector ≠ Sevm.selector (initSevm (outer.withBenv afterTransfer))
  implementationSlotWord :
    (afterTransfer.state.get outer.currentTarget).stor.get
      implementationSlot = d.codeWord
  descriptorCode :
    d.code = afterTransfer.state.getCode d.resolvedCodeAddress
  inputOffset : d.inputOffsetWord = 0
  inputSize : d.inputSizeWord.toNat = outer.data.length
  outputOffset : d.outputOffsetWord = 0
  outputSize : d.outputSizeWord = 0
  emptyTail : d.stackTail = []
  childData : d.child.data = outer.data
  afterTransferStat : afterTransfer.stat = outer.benv.stat
  parentStackRoom : d.parent.stack.length < 1024
  parentError : d.parent.error = none
  parentLogs : d.parent.logs = []
  parentStorage : MessageStorageEqualAt outer.currentTarget
    d.parent.state outer.benv.state
  parentTransient : MessageTransientEqualAt outer.currentTarget
    d.parent.transientStorage outer.tenv.transientStorage
  compileLink : some
    (initSevm (outer.withBenv afterTransfer)).code.toList =
      Prog.compile runtimeBaseline
  compiledPrefix : ∀ raw,
    Func.ExecWitness ossifiableRuntimeFunctions
        (initSevm (outer.withBenv afterTransfer)) callPre
        (delcall ::: proxyReturnTail) raw →
      Prog.ExecWitness (initSevm (outer.withBenv afterTransfer))
        (initDevm (outer.withBenv afterTransfer)) runtimeBaseline raw

/-- Frame entry is derived from transfer success, the exact selected code
address, and a fork-relative non-precompile fact.  It does not require the
message-wide `disablePrecompiles` switch. -/
theorem OssifiableForwardingRoute.outerEntry
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d) :
    (Frame.ofCall outer).enter =
      .run (initEvm (outer.withBenv afterTransfer)) :=
  MessageExecution.frameEnter_eq_run_afterTransfer_of_notPrecompile
    outer afterTransfer outer.currentTarget route.transfer route.codeAddress
      route.proxyNotPrecompile

/-- The exact settlement bundle is assembled from the prefix's primitive
parent-state facts. -/
theorem OssifiableForwardingRoute.settlement
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d) :
    ForwardingSettlementContext outer d :=
  { owner := rfl
    parentStackRoom := route.parentStackRoom
    parentError := route.parentError
    parentLogs := route.parentLogs
    parentStorage := route.parentStorage
    parentTransient := route.parentTransient }

/-- The direct/delegated context certificate is constructed from the exact
spawn descriptor plus the two genuinely non-definitional prefix facts:
complete calldata copying and transfer preservation of the block environment. -/
theorem OssifiableForwardingRoute.directContext
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d) :
    DirectToDelegatedContext outer
      (directTargetMessage outer d.codeWord.toAdr
        d.resolvedCodeAddress d.code) d := by
  refine {
    directEq := rfl
    sameCaller := rfl
    sameValue := rfl
    sameData := route.childData.symm
    sameCode := rfl
    sameStatic := rfl
    sameBlockEnvironment := route.afterTransferStat.symm
    sameTransactionEnvironment := rfl
    directGas := rfl
    delegatedGas := rfl
    directDepth := rfl
    delegatedDepth := rfl
    directAccessedAddresses := rfl
    delegatedAccessedAddresses := rfl
    directAccessedStorageKeys := rfl
    delegatedAccessedStorageKeys := rfl
    directTransfer := rfl
    delegatedNoTransfer := rfl
    directTarget := rfl
    delegatedTarget := rfl
    directStorageOwner := rfl
    delegatedStorageOwner := rfl
    directCodeAddress := rfl
    delegatedCodeAddress := rfl
    directBenv := rfl
    delegatedState := rfl
    directTransientStorage := rfl
    delegatedTransientStorage := rfl
    directDisablePrecompiles := rfl
    delegatedDisablePrecompiles := rfl }

/-- Stronger installation facts needed only by results that interpret the
loaded word as a canonical address and require executable implementation code.
The generic forwarding envelope intentionally accepts missing code. -/
structure OssifiableForwardingRoute.ValidInstallation
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d) : Prop where
  canonicalSlotWord : d.codeWord = d.codeWord.toAdr.toB256
  executedCodeNonempty : d.code.toList ≠ []

/-- The old address-shaped slot equation is a consequence of the exact loaded
word plus the narrower canonical-installation premise. -/
theorem OssifiableForwardingRoute.implementationSlotValue_of_validInstallation
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d)
    (valid : route.ValidInstallation) :
    (afterTransfer.state.get outer.currentTarget).stor.get
        implementationSlot = d.codeWord.toAdr.toB256 := by
  exact route.implementationSlotWord.trans valid.canonicalSlotWord

/-- The implementation-specific property transport left deliberately open by
the generic envelope.  Its context is the exact direct/delegated delta carried
by the runtime route, not an asserted message-result equivalence. -/
def OssifiableForwardingRoute.transportObligation
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d)
    (P : Msg → MessageResult → Prop) : Prop :=
  DirectTargetTransport P route.directContext

/-- A concrete scalar-input property.  It is deliberately message-level: the
implementation-specific result theorem can conjoin its own output/storage
claim, while this witness discharges the context-sensitive input component. -/
def ScalarInputWord (word : B256) (msg : Msg) (_out : MessageResult) : Prop :=
  Bytes.toB256 msg.data = word

/-- Complete calldata copying makes the scalar input word transport from the
genuine direct target message to the exact delegated child. -/
theorem OssifiableForwardingRoute.scalarInputWord_transport
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d)
    (word : B256) :
    route.transportObligation (ScalarInputWord word) := by
  intro directOut childOut directTrace childTrace directWord
  dsimp only [ScalarInputWord] at directWord ⊢
  rw [← route.directContext.sameData]
  exact directWord

/-- The exact delegated child retains the proxy as storage owner and records
the descriptor's EIP-150 gas, depth, access, transfer, and code context. -/
theorem OssifiableForwardingRoute.childContext
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (_route : OssifiableForwardingRoute outer afterTransfer callPre d) :
    d.child.currentTarget = outer.currentTarget ∧
      d.child.codeAddress = some d.resolvedCodeAddress ∧
      d.child.gas = d.childGas ∧
      d.child.depth = outer.depth - 1 ∧
      d.child.accessedAddresses = d.parent.accessedAddresses ∧
      d.child.accessedStorageKeys = d.parent.accessedStorageKeys ∧
      d.child.accessedAddresses = d.afterAccess.accessedAddresses ∧
      d.child.accessedStorageKeys = d.afterAccess.accessedStorageKeys ∧
      d.parent.gasLeft = d.afterAccess.gasLeft -
        (d.callCost + d.extensionCost) ∧
      calculateMsgCallGas 0 d.gasWord.toNat d.afterAccess.gasLeft
        d.extensionCost d.accessCharge = ⟨d.callCost, d.childGas⟩ ∧
      d.child.shouldTransferValue = false ∧
      d.child.code = d.code := by
  exact ⟨by rfl, rfl, rfl, by rfl, rfl, rfl, rfl, rfl, rfl,
    d.splitEq, rfl, rfl⟩

/-- Reusable account-altitude forwarding envelope for the complete runtime.
The exact child execution is an input certificate; the outer result is an
existential conclusion derived from compiled execution and message settlement.
Gas and warm-set equality are intentionally absent from the observation. -/
theorem processMessage_forwardingEnvelope
    (outer : Msg) (afterTransfer : Benv)
    (callPre : Devm)
    (d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre)
    (route : OssifiableForwardingRoute outer afterTransfer callPre d)
    (childOut : MessageResult)
    (tail : match childOut with
      | .ok child => ForwardingTailBudget d child
      | .error _ => PUnit)
    (certificate : DelegatedChildCertificate d.child childOut) :
    ∃ wrapperOut,
      processMessage outer = wrapperOut ∧
        ChildToWrapperSettledAt outer.currentTarget childOut wrapperOut := by
  let P : Execution → Prop := fun raw =>
    ChildToWrapperSettledAt outer.currentTarget childOut
      ((Frame.ofCall outer).settle raw)
  have atCall : Func.ExecSat ossifiableRuntimeFunctions
      (initSevm (outer.withBenv afterTransfer)) callPre
      (delcall ::: proxyReturnTail) P :=
    forwarding_atCall_execSat outer d route.settlement childOut
      tail certificate
  rcases atCall with ⟨raw, rawWitness, observation⟩
  have program : Prog.ExecSat
      (initSevm (outer.withBenv afterTransfer))
      (initDevm (outer.withBenv afterTransfer)) runtimeBaseline P :=
    ⟨raw, route.compiledPrefix raw rawWitness, observation⟩
  have executed : P (exec (initEvm (outer.withBenv afterTransfer))) := by
    exact Prog.execSat_out program route.compileLink
  refine ⟨(Frame.ofCall outer).settle
      (exec (initEvm (outer.withBenv afterTransfer))), ?_, executed⟩
  exact MessageExecution.processMessage_eq_settle_exec_of_enter
    outer (initEvm (outer.withBenv afterTransfer)) route.outerEntry

/-! ## Biting theorem-level controls -/

/-- A route cannot simultaneously certify a named selector collision. -/
theorem OssifiableForwardingRoute.rejects_selector_collision
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d)
    {selector : B256} (member : selector ∈ runtimeSelectors)
    (collision : selector =
      Sevm.selector (initSevm (outer.withBenv afterTransfer))) : False :=
  route.selectorMiss selector member collision

/-- The exact slot-word link rejects a different claimed implementation word. -/
theorem OssifiableForwardingRoute.rejects_false_installation_word
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d)
    (falseWord :
      (afterTransfer.state.get outer.currentTarget).stor.get
        implementationSlot ≠ d.codeWord) : False :=
  falseWord route.implementationSlotWord

/-- The spawned delegated child cannot name a storage owner other than the
outer proxy account. -/
theorem OssifiableForwardingRoute.rejects_wrong_storage_owner
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d)
    (wrongOwner : d.child.currentTarget ≠ outer.currentTarget) : False :=
  wrongOwner route.childContext.1

/-- The descriptor itself rejects a zero-depth call site. -/
theorem DelegatecallSpawnDescriptor.rejects_zero_depth
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (zeroDepth : sevm.depth = 0) : False :=
  d.depthHeadroom zeroDepth

/-- The descriptor's EIP-150 split cannot claim a call cost beyond the exact
available call-site budget. -/
theorem DelegatecallSpawnDescriptor.rejects_insufficient_call_budget
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (insufficient : d.afterAccess.gasLeft <
      d.callCost + d.extensionCost) : False := by
  exact (Nat.not_lt_of_ge d.affordable) insufficient

/-- A clean child with less gas than the exact tail charge cannot carry a
primitive tail-budget certificate. -/
theorem ForwardingTailBudget.rejects_insufficient_clean_tail
    {sevm : Sevm} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor sevm callPre} {child : Devm}
    (clean : child.error.isSome = false)
    (insufficient : (forwardingCleanResume d child).gasLeft <
      forwardingCleanTailCost (forwardingCleanResume d child)) :
    ForwardingTailBudget d child → False := by
  intro tail
  cases tail with
  | clean _ _ _ _ gas budget => omega
  | failed failedStatus _ _ _ _ _ => simp_all

/-- A valid installation cannot name empty executed code. -/
theorem OssifiableForwardingRoute.ValidInstallation.rejects_missing_code
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    {route : OssifiableForwardingRoute outer afterTransfer callPre d}
    (valid : route.ValidInstallation) (missing : d.code.toList = []) : False :=
  valid.executedCodeNonempty missing

/-- The successful-channel relation rejects a wrong copied output. -/
theorem ChildToWrapperSettledAt.rejects_ok_output_mismatch
    {owner : Adr} {child wrapper : Devm}
    (mismatch : wrapper.output ≠ child.output) :
    ¬ ChildToWrapperSettledAt owner (.ok child) (.ok wrapper) := by
  intro related
  exact mismatch related.output

/-- A clean child cannot be normalized to a reverting wrapper. -/
theorem ChildToWrapperSettledAt.rejects_clean_child_revert_wrapper
    {owner : Adr} {child wrapper : Devm}
    (childClean : child.error = none)
    (wrapperRevert : wrapper.error = some .revert) :
    ¬ ChildToWrapperSettledAt owner (.ok child) (.ok wrapper) := by
  intro related
  rcases related.status with ⟨_, wrapperClean⟩ | ⟨childFailed, _⟩
  · rw [wrapperRevert] at wrapperClean
    cases wrapperClean
  · rw [childClean] at childFailed
    cases childFailed

/-- The transport interface intentionally supplies no false gas equality:
whenever the actual EIP-150 child budget differs, the genuine direct target
and delegated child expose different `GAS`-sensitive inputs. -/
theorem OssifiableForwardingRoute.gas_sensitive_context_differs
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (_route : OssifiableForwardingRoute outer afterTransfer callPre d)
    (different : outer.gas ≠ d.childGas) :
    (directTargetMessage outer d.codeWord.toAdr
      d.resolvedCodeAddress d.code).gas ≠ d.child.gas := by
  change outer.gas ≠ d.childGas
  exact different

/-- The scalar witness is not vacuous: a different calldata word falsifies
its property for every result. -/
theorem ScalarInputWord.rejects_wrong_word
    {word : B256} {msg : Msg} {out : MessageResult}
    (wrong : Bytes.toB256 msg.data ≠ word) :
    ¬ ScalarInputWord word msg out :=
  wrong

end Blanc.ProxyPair
