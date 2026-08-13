import Blanc.ExecutionSettlement
import Blanc.Compiled
import Blanc.CommonProofs

/-!
Contract-neutral instruction occurrences over finite execution derivations.

The raw chronology records every reached driver node, independently of the
root outcome.  At a spawning node it places the spawning instruction before
the complete child execution and the resumed parent continuation after the
child.  Settlement-aware filtering and compiler/source attribution are built
on this order below.
-/

namespace Blanc

open Jaune

/-- Every reached driver node, in execution order.  This is deliberately not
`Exec.Deriv.le`: the child and resumed continuation of `runOk` are sibling
recursive premises, while the chronology orders the child first. -/
def Exec.rawNodes {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Deriv :=
  let root : Exec.Deriv := ⟨pc, sevm, pre, out, run⟩
  match run with
  | .halt _ => [root]
  | .cont _ next => root :: Exec.rawNodes next
  | .doneErr _ _ _ => [root]
  | .doneOk _ _ _ next => root :: Exec.rawNodes next
  | .runErr _ _ child _ => root :: Exec.rawNodes child
  | .runOk _ _ child _ next =>
      root :: (Exec.rawNodes child ++ Exec.rawNodes next)
termination_by sizeOf run

/-- An exact reached nonterminal instruction.  The result is the instruction's
own step result, not the enclosing derivation's endpoint.  `slot` retains the
concrete recursive child proof when the instruction entered a child frame. -/
structure Exec.NinstOccurrence (root : Exec.Deriv) : Type where
  node : Exec.Deriv
  instruction : Ninst
  slot : Xlot
  stepResult : Execution
  reached : node ∈ Exec.rawNodes root.exc
  decoded : Ninst.At node.sevm.code node.pc instruction
  filled : slot.Filled
  stepRun : Ninst.StepRun node.pc node.sevm node.devm instruction slot stepResult

private theorem List.exists_eq_append_cons_of_mem
    {α : Type} {x : α} {xs : List α} (h : x ∈ xs) :
    ∃ before after, xs = before ++ x :: after := by
  induction xs with
  | nil => simp at h
  | cons head tail ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | htail
      · exact ⟨[], tail, rfl⟩
      · rcases ih htail with ⟨before, after, hsplit⟩
        exact ⟨head :: before, after, by simp [hsplit]⟩

/-- Every occurrence splits the enclosing chronology at its exact proof node. -/
theorem Exec.NinstOccurrence.rawNodes_decomposition
    {root : Exec.Deriv} (occurrence : Exec.NinstOccurrence root) :
    ∃ before after,
      Exec.rawNodes root.exc = before ++ occurrence.node :: after :=
  List.exists_eq_append_cons_of_mem occurrence.reached

/-- Decoding the root of any derivation as a nonterminal instruction recovers
the exact recursive slot and step result for all six `Exec` outcomes. -/
theorem Exec.Deriv.exists_stepRun_of_ninstAt
    (node : Exec.Deriv) {n : Ninst}
    (hat : Ninst.At node.sevm.code node.pc n) :
    ∃ (slot : Xlot) (result : Execution),
      slot.Filled ∧
      Ninst.StepRun node.pc node.sevm node.devm n slot result := by
  rcases node with ⟨pc, sevm, pre, out, run⟩
  have hroot : Evm.step ⟨pc, sevm, pre⟩ =
      Ninst.step ⟨pc, sevm, pre⟩ n := Evm.step_next hat
  cases run with
  | halt hstep =>
      refine ⟨.none, out, trivial, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨rfl, rfl⟩
  | cont hstep next =>
      rename_i pc' post
      refine ⟨.none, .ok post, trivial, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨rfl, rfl⟩
  | doneErr hstep henter hresume =>
      rename_i frame resume pc' settled err
      refine ⟨.none, .error err, trivial, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨settled, RunFrame.of_done henter, hresume.symm⟩
  | doneOk hstep henter hresume next =>
      rename_i frame resume pc' settled post
      refine ⟨.none, .ok post, trivial, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨settled, RunFrame.of_done henter, hresume.symm⟩
  | runErr hstep henter child hresume =>
      rename_i frame resume pc' childEvm raw err
      refine ⟨.some ⟨childEvm, raw⟩, .error err, ⟨child⟩, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨frame.settle raw, RunFrame.of_run henter, hresume.symm⟩
  | runOk hstep henter child hresume next =>
      rename_i frame resume pc' childEvm raw post
      refine ⟨.some ⟨childEvm, raw⟩, .ok post, ⟨child⟩, ?_⟩
      unfold Ninst.StepRun
      rw [← hroot, hstep]
      exact ⟨frame.settle raw, RunFrame.of_run henter, hresume.symm⟩

/-- Membership plus an exact `.next` decode is complete for the rich
occurrence view. -/
theorem Exec.exists_ninstOccurrence_of_mem_rawNodes
    {root node : Exec.Deriv} {n : Ninst}
    (hreached : node ∈ Exec.rawNodes root.exc)
    (hat : Ninst.At node.sevm.code node.pc n) :
    ∃ occurrence : Exec.NinstOccurrence root,
      occurrence.node = node ∧ occurrence.instruction = n := by
  rcases node.exists_stepRun_of_ninstAt hat with ⟨slot, result, hfilled, hrun⟩
  exact ⟨⟨node, n, slot, result, hreached, hat, hfilled, hrun⟩, rfl, rfl⟩

/-- Soundness and completeness of the occurrence view against exact reached
nodes and nonterminal decoding. -/
theorem Exec.ninstOccurrence_iff_mem_rawNodes
    {root node : Exec.Deriv} {n : Ninst} :
    (∃ occurrence : Exec.NinstOccurrence root,
      occurrence.node = node ∧ occurrence.instruction = n) ↔
      node ∈ Exec.rawNodes root.exc ∧
        Ninst.At node.sevm.code node.pc n := by
  constructor
  · rintro ⟨occurrence, rfl, rfl⟩
    exact ⟨occurrence.reached, occurrence.decoded⟩
  · rintro ⟨hreached, hat⟩
    exact Exec.exists_ninstOccurrence_of_mem_rawNodes hreached hat

/-- A successful persistent write occurrence.  There is intentionally no
old-value/new-value inequality: a successful no-op `SSTORE` is retained. -/
structure Exec.SuccessfulSstoreOccurrence (root : Exec.Deriv) : Type where
  occurrence : Exec.NinstOccurrence root
  instruction_eq : occurrence.instruction = .reg .sstore
  stepPost : Devm
  stepSuccess : occurrence.stepResult = .ok stepPost
  key : B256
  value : B256
  popped : Stack.Pop [key, value] occurrence.node.devm.stack stepPost.stack

/-- The storage owner is the executing frame's current target. -/
def Exec.SuccessfulSstoreOccurrence.storageOwner
    {root : Exec.Deriv} (write : Exec.SuccessfulSstoreOccurrence root) : Adr :=
  write.occurrence.node.sevm.currentTarget

/-- Refine a successful decoded `SSTORE` without discarding no-op writes. -/
theorem Exec.NinstOccurrence.toSuccessfulSstore
    {root : Exec.Deriv} (occurrence : Exec.NinstOccurrence root)
    (hinstruction : occurrence.instruction = .reg .sstore)
    {post : Devm} (hsuccess : occurrence.stepResult = .ok post) :
    ∃ write : Exec.SuccessfulSstoreOccurrence root,
      write.occurrence = occurrence := by
  have hrun : Ninst.Run occurrence.node.sevm occurrence.node.devm
      (.reg .sstore) post := by
    refine ⟨occurrence.slot, occurrence.filled, occurrence.node.pc, ?_⟩
    simpa only [hinstruction, hsuccess] using occurrence.stepRun
  rcases of_run_sstore hrun with ⟨key, value, hpop⟩
  exact ⟨⟨occurrence, hinstruction, post, hsuccess, key, value, hpop⟩, rfl⟩

/-- The successful occurrence performs the exact key/value update it records. -/
theorem Exec.SuccessfulSstoreOccurrence.storage_update
    {root : Exec.Deriv} (write : Exec.SuccessfulSstoreOccurrence root) :
    Devm.getStor write.stepPost write.storageOwner =
      (Devm.getStor write.occurrence.node.devm write.storageOwner).set
        write.key write.value := by
  have hrun : Ninst.Run write.occurrence.node.sevm write.occurrence.node.devm
      (.reg .sstore) write.stepPost := by
    refine ⟨write.occurrence.slot, write.occurrence.filled,
      write.occurrence.node.pc, ?_⟩
    simpa only [write.instruction_eq, write.stepSuccess] using
      write.occurrence.stepRun
  exact sstore_getStor_set hrun (pref_of_split write.popped)

/-- The unique same-frame continuation edge.  Entered child proofs are not
edges here: they are the chronological segment crossed by `runOk` before its
parent continuation. -/
inductive Exec.Deriv.ParentStep : Exec.Deriv → Exec.Deriv → Prop
  | cont {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .cont hstep next⟩
  | doneOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Frame} {resume : Resume}
      {settled : Except (EvmError × State × AdrSet × Tra) Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .done settled)
      (hresume : resume.run settled = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .doneOk hstep henter hresume next⟩
  | runOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
      {raw out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (hresume : resume.run (frame.settle raw) = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .runOk hstep henter child hresume next⟩

/-- A same-frame node has only one continuation in one concrete proof. -/
theorem Exec.Deriv.ParentStep.unique
    {root nextLeft nextRight : Exec.Deriv}
    (left : Exec.Deriv.ParentStep nextLeft root)
    (right : Exec.Deriv.ParentStep nextRight root) :
    nextLeft = nextRight := by
  cases left <;> cases right <;> simp_all

/-- A finite same-frame prefix. -/
inductive Exec.Deriv.ParentPrefix : Exec.Deriv → Exec.Deriv → Prop
  | refl (root : Exec.Deriv) : ParentPrefix root root
  | step {root next tail : Exec.Deriv}
      (head : Exec.Deriv.ParentStep next root)
      (rest : Exec.Deriv.ParentPrefix next tail) :
      Exec.Deriv.ParentPrefix root tail

/-- Same-frame prefixes in a fixed execution proof are linearly ordered. -/
theorem Exec.Deriv.ParentPrefix.linear
    {root leftTail rightTail : Exec.Deriv}
    (left : Exec.Deriv.ParentPrefix root leftTail)
    (right : Exec.Deriv.ParentPrefix root rightTail) :
    Exec.Deriv.ParentPrefix leftTail rightTail ∨
      Exec.Deriv.ParentPrefix rightTail leftTail := by
  induction left generalizing rightTail with
  | refl => exact Or.inl right
  | step head rest ih =>
      cases right with
      | refl => exact Or.inr (.step head rest)
      | step rightHead rightRest =>
          cases head.unique rightHead
          exact ih rightRest

/-- One same-frame edge splits the global chronology.  A successful entered
child belongs to the nonempty crossed prefix before the parent resumes. -/
theorem Exec.Deriv.ParentStep.rawNodes_decomposition
    {root next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root) :
    ∃ crossed : List Exec.Deriv,
      crossed ≠ [] ∧
      Exec.rawNodes root.exc = crossed ++ Exec.rawNodes next.exc := by
  cases edge with
  | cont hstep next =>
      refine ⟨[⟨_, _, _, _, .cont hstep next⟩], by simp, ?_⟩
      simp [Exec.rawNodes]
  | doneOk hstep henter hresume next =>
      refine ⟨[⟨_, _, _, _, .doneOk hstep henter hresume next⟩], by simp, ?_⟩
      simp [Exec.rawNodes]
  | runOk hstep henter child hresume next =>
      refine ⟨⟨_, _, _, _, .runOk hstep henter child hresume next⟩ ::
        Exec.rawNodes child, by simp, ?_⟩
      simp [Exec.rawNodes]

/-- Every same-frame prefix gives an exact split of the enclosing global
chronology at its endpoint. -/
theorem Exec.Deriv.ParentPrefix.rawNodes_decomposition
    {root tail : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root tail) :
    ∃ before : List Exec.Deriv,
      Exec.rawNodes root.exc = before ++ Exec.rawNodes tail.exc := by
  induction hprefix with
  | refl => exact ⟨[], rfl⟩
  | step head rest ih =>
      rcases head.rawNodes_decomposition with ⟨crossed, _, hhead⟩
      rcases ih with ⟨before, hrest⟩
      exact ⟨crossed ++ before, by rw [hhead, hrest, List.append_assoc]⟩

/-! ## Executable compiler source sites -/

/-- One structural descent in a source `Func`.  Compiler-only control-flow
bytes are deliberately absent. -/
inductive Prog.SourceStep where
  | rest
  | branchLeft
  | branchRight
deriving DecidableEq, Repr

/-- Stable structural identity of a source instruction. -/
structure Prog.SourcePath where
  functionIndex : Nat
  steps : List Prog.SourceStep
deriving DecidableEq, Repr

/-- An executable compiler-produced source instruction site. -/
structure Prog.SourceSite where
  path : Prog.SourcePath
  pc : Nat
  instruction : Ninst

/-- Enumerate exactly the `.next` nodes of a source function at their compiled
program counters.  `branch` and `call` contribute only compiler glue, so they
do not themselves produce source sites. -/
def Func.sourceSites (functionIndex : Nat) (steps : List Prog.SourceStep)
    (pc : Nat) : Func → List Prog.SourceSite
  | .last _ => []
  | .next instruction tail =>
      { path := ⟨functionIndex, steps⟩, pc, instruction } ::
        Func.sourceSites functionIndex (steps ++ [.rest])
          (pc + instruction.size) tail
  | .branch left right =>
      Func.sourceSites functionIndex (steps ++ [.branchLeft]) (pc + 4) left ++
        Func.sourceSites functionIndex (steps ++ [.branchRight])
          (pc + compsize left + 5) right
  | .call _ => []

/-- Executable source map for every function body in compiler-table order. -/
def Prog.sourceSites (program : Prog) : List Prog.SourceSite :=
  (List.range (program.main :: program.aux).length).flatMap fun index =>
    match (table 0 (program.main :: program.aux))[index]? with
    | some (pc, body) => Func.sourceSites index [] (pc + 1) body
    | none => []

/-- Look up a source site by compiled program counter. -/
def Prog.sourceSiteAt (program : Prog) (pc : Nat) : Option Prog.SourceSite :=
  program.sourceSites.find? fun site => site.pc == pc

/-- Every enumerated function site decodes to its recorded instruction in the
compiler output. -/
theorem Func.sourceSites_sound
    {code : ByteArray} {layout : List (Nat × Func)}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {pc : Nat} {body : Func} {site : Prog.SourceSite}
    (sub : subcode code.toList pc (Func.compile layout pc body))
    (boundary : noPushBefore code pc 32 = true)
    (member : site ∈ Func.sourceSites functionIndex steps pc body) :
    Ninst.At code site.pc site.instruction := by
  induction body generalizing pc steps with
  | last outcome =>
      simp [Func.sourceSites] at member
  | next instruction tail ih =>
      simp only [Func.sourceSites, List.mem_cons] at member
      rcases member with rfl | member
      · rcases of_subcode sub with ⟨compiled, hcompile, hslice⟩
        rcases of_bind_eq_some hcompile with ⟨tailBytes, htail, hwhole⟩
        rw [← of_pure_eq_some hwhole] at hslice
        exact Ninst.at_of_slice (List.slice_prefix hslice)
      · rcases Func.noPushBefore_next sub boundary with
          ⟨nextBoundary, nextSub⟩
        exact ih nextSub nextBoundary member
  | branch left right left_ih right_ih =>
      simp only [Func.sourceSites, List.mem_append] at member
      rcases subcode_compile_branch_jumpable sub boundary with
        ⟨loc, hloc, _, _, _, leftSub, leftBoundary, _, _, rightSub,
          rightBoundary⟩
      rcases member with leftMember | rightMember
      · exact left_ih leftSub leftBoundary leftMember
      · have hpc : loc + 1 = pc + compsize left + 5 := by omega
        rw [hpc] at rightSub rightBoundary
        exact right_ih rightSub rightBoundary rightMember
  | call index =>
      simp [Func.sourceSites] at member

/-- The program-level source map is sound against the exact compiler output. -/
theorem Prog.sourceSites_sound
    {program : Prog} {code : ByteArray} {site : Prog.SourceSite}
    (compiled : some code.toList = program.compile)
    (member : site ∈ program.sourceSites) :
    Ninst.At code site.pc site.instruction := by
  simp only [Prog.sourceSites, List.mem_flatMap] at member
  rcases member with ⟨index, index_mem, member⟩
  split at member
  next body hentry =>
    have sub := (subcode_of_get?_eq_some compiled hentry).2
    have boundary := (Prog.jumpable_of_get?_table compiled hentry).2
    exact Func.sourceSites_sound sub boundary member
  next hnone =>
    simp at member

/-- A successful executable lookup has the requested PC and decodes exactly
as recorded. -/
theorem Prog.sourceSiteAt_sound
    {program : Prog} {code : ByteArray} {pc : Nat} {site : Prog.SourceSite}
    (compiled : some code.toList = program.compile)
    (found : program.sourceSiteAt pc = some site) :
    site.pc = pc ∧ Ninst.At code site.pc site.instruction := by
  constructor
  · have h := List.find?_some found
    simpa [BEq.beq] using h
  · exact program.sourceSites_sound compiled
      (List.mem_of_find?_eq_some found)

end Blanc
