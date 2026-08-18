import Blanc.SourceAttainment
import Blanc.LidoCircuitBreakerAuthority
import Blanc.LidoCircuitBreakerRegistrationWorld

/-!
Forward attainment for exact Lido CircuitBreaker runtime persistent writes.

`Blanc/LidoCircuitBreakerAuthority.lean` states the *upper bound*: every
same-frame runtime `SSTORE` in an exact invocation carries one typed row and
one of that row's permitted invocation roles.  Nothing there says a given
(row, role) pair is ever actually reached, so `permittedRoles` is certified in
one direction only.

`Attainable` below is the matching lower-bound shape.  Its premise set is
exactly the hypothesis block of
`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot`, so a witness is
literally what that theorem consumes, and the row is pinned by the *row's own*
frozen source site rather than existentially hidden.

The rest of this module builds positive witnesses, unconditionally, at the one
concrete admin registration of
`Blanc/LidoCircuitBreakerRegistrationWorld.lean`.  That single walk performs
six persistent writes, and **all six** are attained here: five with the
`.adminRegistry` role — `.setPauserAssignment` (source function 14), the three
`appendTarget` rows `.appendArrayEntry`, `.appendReverseIndex` and
`.appendArrayLength` (function 15), and `.afterOldNewCount` (function 16) — and
one with `.adminExpiry`, the expiry write on `registerAfterSet`'s fresh arm
(function 19, inventory index 17).  One world, one derivation, six rows;
everything after the route is row-independent (`attainable_of_route`).

Three facts made the first route cheap, and all three generalize.  A
`REVERT`-only arm cannot produce an `.ok` outcome at all, so seven of the
seventeen branch crossings need no branch word and no cleanliness antecedent;
six more are the dispatcher's selector comparisons, decided on the concrete
calldata selector alone; and the same-frame premise comes back from the routed
bridge already proved, so no frame-entry-freedom certificate is involved — see
*Same-frame reachability, and why no certificate is needed* below.

The remaining four crossings are the priced ones, and they split by where their
word lives.  The `appendTarget` rows add `setPauserKernel`'s previous-pauser
test, whose word is *storage-valued*: the entry storage has to survive every
earlier crossing, which is why the route carries a `Devm.getStor` chain and the
shared kit gained its `routeTo_branch*_frame` family.  The last three are
*memory*-valued — `afterOldPauser`'s new-pauser test, `finishSetPauser`'s
continuation test and `registerAfterSet`'s previous-pauser test — and none of
them can be made key-anonymous the way the storage one is, so a memory image
travels from `registerPauser`'s staging line as three 32-byte windows.  See
*Carrying one memory word across a route* below.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The attainment predicate -/

/-- A concrete exact runtime execution actually reaches this row's frozen
source site with this invocation role.

Every conjunct is load-bearing.  `row.sourceSite? dp = some site` together with
`site.pc = occurrence.node.pc` is what names the *row*; dropping either would
leave a statement about some runtime `SSTORE`, not about this one.  The frame
premises are the ones
`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot` consumes, so an
`Attainable` witness and that theorem's hypotheses are the same data.

Deliberately no `Decidable` instance: attainment is an execution claim, not a
structural one. -/
def Attainable (dp : DeployParams) (row : RuntimePersistentWrite)
    (role : InvocationRole) : Prop :=
  ∃ (ca : Adr) (globalRoot frameRoot : Exec.Deriv)
    (occurrence : Exec.NinstOccurrence globalRoot) (site : Prog.SourceSite),
    occurrence.instruction = .reg .sstore ∧
    frameRoot ∈ Exec.rawFrameRoots globalRoot.exc ∧
    frameRoot.exactInvocation (runtime dp) ca ca ∧
    Exec.Deriv.ParentPrefix frameRoot occurrence.node ∧
    row.sourceSite? dp = some site ∧
    site.pc = occurrence.node.pc ∧
    RuntimeWriteAuthority dp frameRoot occurrence.node role

/-- Every row named by an attainment witness lies in the runtime's structural
persistent source inventory. -/
theorem RuntimePersistentWrite.mem_runtimePersistentSourceSites
    {dp : DeployParams} {row : RuntimePersistentWrite} {site : Prog.SourceSite}
    (found : row.sourceSite? dp = some site) :
    site ∈ runtimePersistentSourceSites dp := by
  have sound := RuntimePersistentWrite.sourceSite?_sound found
  unfold runtimePersistentSourceSites
  rw [List.mem_filter]
  exact ⟨sound.1, by simp [sound.2, isPersistentWriteInstruction]⟩

/-! ## Refuting a permitted-role widening

`RuntimePersistentWrite.permittedRoles` lists `.afterOldNewCount` as
admin-registry only.  The theorem below is the semantic content of that single
entry: a `.pauseRegistry` authority payload pins its write's own persistent
source site into source functions 14/15/17, and `.afterOldNewCount` sits in
function 16.  No execution is constructed, because none is needed — the two
role payloads are already incompatible at the source-site level. -/

/-- A pause-registry role can never be attained at the `afterOld.newCount`
row.  This is the mutant that a role-widening edit to `permittedRoles` would
have to make typecheck, and it does not. -/
theorem not_attainable_afterOldNewCount_pauseRegistry :
    ¬ Attainable officialParams .afterOldNewCount .pauseRegistry := by
  rintro ⟨ca, globalRoot, frameRoot, occurrence, site, _instructionEq,
    _selected, _invocation, _sameFrame, found, sitePc, authority⟩
  cases authority with
  | pauseRegistry _endpoint _assignedGuard _liveGuard _assigned _live
      writeSite =>
      rcases writeSite with ⟨other, otherMem, otherPc, otherIndex⟩
      have siteEq : other = site :=
        runtimePersistentSourceSite_eq_of_pc otherMem
          (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
          (otherPc.trans sitePc.symm)
      rw [siteEq, RuntimePersistentWrite.sourceSite?_functionIndex found]
        at otherIndex
      exact absurd otherIndex (by decide)

/-! ## The last leg of the `setPauser.assignment` route

`Blanc/SourceAttainment.lean`'s contract-neutral `routeTo_*` kit, exercised on
the exact production `Func`.  Read that module's *route-construction kit*
section before adding a leg: it records why `RouteTo`'s constructors cannot be
`apply`d, which is the one trap in front of every consumer.

This is the leg the
`.setPauserAssignment` row's attainment witness ends with: from the callee root
of `setPauserKernel` down to the assignment `SSTORE`: seventeen crossed source
nodes, one branch, and the designated head.  Nothing here reduces a program
counter.

The three legs in this section take **branch-word** hypotheses, which is what
the shared kit's branch lemmas ask for.  At a successful outcome none of those
words has to be computed — the shared kit's `routeTo_*RevertsOk` pair settles
a branch from a certified-reverting arm alone — so
`setPauserKernel_routeTo_assignment_ok`,
`runtimeMain_routeTo_setPauserAssignment` and
`call_setPauserSlot_routeTo_assignment_ok` supersede them for the witness.
These remain as the general-outcome forms. -/

/-- The kernel's zero-check prefix, spelled out: `loadWord targetWord`'s
expansion followed by `iszero`.  The combinator form unifies here too; this
`def` just names the line once for the three legs that cross it. -/
def setPauserKernelZeroCheck : Line :=
  [Ninst.pushB256 (targetWord * 32), Ninst.mload, Ninst.iszero]

/-- The kernel's assignment prefix, from the fall-through arm to the `SSTORE`;
`targetKey ++ [sload, dup 0] ++ mstoreAt previousPauserWord ++
loadWord newPauserWord ++ targetKey`, spelled out for the same reason. -/
def setPauserKernelAssignmentPrefix : Line :=
  [Ninst.pushB256 (targetWord * 32), Ninst.mload,
   Ninst.pushB256 (regionWord assignmentRegion), Ninst.or,
   Ninst.sload, Ninst.dup 0,
   Ninst.pushB256 (previousPauserWord * 32), Ninst.mstore,
   Ninst.pushB256 (newPauserWord * 32), Ninst.mload,
   Ninst.pushB256 (targetWord * 32), Ninst.mload,
   Ninst.pushB256 (regionWord assignmentRegion), Ninst.or]

/-- Structural source position of the `setPauser.assignment` `SSTORE`. -/
def setPauserAssignmentPath : Prog.SourcePath :=
  ⟨setPauserSlot,
    List.replicate 3 .rest ++ [.branchLeft] ++ List.replicate 14 .rest⟩

/-- Inside `setPauserKernel`, a walk whose zero-check falls through reaches the
assignment `SSTORE` at `setPauserAssignmentPath`.  The nonzero-target branch
word is the leg's only execution premise. -/
theorem setPauserKernel_routeTo_assignment
    {fs : List Func} {sevm : Sevm} {devm : Devm} {out : Execution}
    (h : Func.RunCompiledTo fs sevm devm setPauserKernel out)
    (nonzeroTarget : ∀ devm' : Devm,
      Line.Run sevm devm setPauserKernelZeroCheck devm' →
      ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h
      setPauserAssignmentPath (.reg .sstore) := by
  refine routeTo_line setPauserKernelZeroCheck h
    (fun zeroCheck lineRun tail => ?_)
  refine routeTo_branchLeft tail (nonzeroTarget zeroCheck lineRun)
    (fun _armStart arm => ?_)
  refine routeTo_line setPauserKernelAssignmentPrefix arm
    (fun _writeState _writeRun write => ?_)
  have pathEq :
      ((([] ++ List.replicate setPauserKernelZeroCheck.length
              Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
          List.replicate setPauserKernelAssignmentPrefix.length
            Prog.SourceStep.rest) =
        setPauserAssignmentPath.steps := by
    simp [setPauserAssignmentPath, setPauserKernelZeroCheck,
      setPauserKernelAssignmentPrefix]
  exact pathEq ▸ routeTo_head write setPauserAssignmentPath

/-- The dispatcher's entry guard, spelled literally. -/
def runtimeMainEntryPrefix : Line :=
  [Ninst.callvalue, Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt, Ninst.or]

/-- The dispatcher's opening crossing, on the exact production `runtimeMain`.

This is the named hazard zone: exposing `runtimeMain dp`'s head through
`prepend` is the unfolding that neighbouring stage lemmas pay for with
`unfold runtime runtimeMain hybridDispatchWith` plus a `simpa`.  Through
`routeTo_line` it costs nothing measurable — the route never needs the
compiled form, only the source constructor head. -/
theorem runtimeMain_routeTo_dispatch (dp : DeployParams)
    {fs : List Func} {sevm : Sevm} {devm : Devm} {out : Execution}
    {target : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (runtimeMain dp) out)
    (accepted : ∀ entry : Devm,
      Line.Run sevm devm runtimeMainEntryPrefix entry →
      ∀ (w : B256) (rest : Stack), entry.stack = w :: rest → w = 0)
    (dispatchRoute : ∀ entry : Devm,
      ∀ tail : Func.RunCompiledTo fs sevm entry
        (fsig +++ hybridDispatchWith fallbackSlot (funcs dp)) out,
        Func.RunCompiledTo.RouteTo
          ⟨0, List.replicate 5 .rest ++ [.branchLeft]⟩ tail target
          targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h target targetInstruction := by
  refine routeTo_line runtimeMainEntryPrefix h (fun entry lineRun tail => ?_)
  refine routeTo_branchLeft tail (accepted entry lineRun) (fun body arm => ?_)
  have pathEq :
      ([] ++ List.replicate runtimeMainEntryPrefix.length
            Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft] =
        List.replicate 5 Prog.SourceStep.rest ++
          [Prog.SourceStep.branchLeft] := by
    simp [runtimeMainEntryPrefix]
  exact pathEq ▸ dispatchRoute body arm

/-- The `.call setPauserSlot` crossing, on top of the leg above.

An internal `.call` restarts the source position at the callee's root, so the
target path is `setPauserAssignmentPath` regardless of where in the dispatcher
or in `registerPauser`'s body the call was reached: **no dispatcher path
arithmetic survives the call**.  Only the branch words do. -/
theorem call_setPauserSlot_routeTo_assignment
    {fs : List Func} {sevm : Sevm} {devm : Devm} {out : Execution}
    {current : Prog.SourcePath}
    (lookup : fs[setPauserSlot]? = some setPauserKernel)
    (h : Func.RunCompiledTo fs sevm devm (.call setPauserSlot) out)
    (nonzeroTarget : ∀ kernelStart zeroCheck : Devm,
      Line.Run sevm kernelStart setPauserKernelZeroCheck zeroCheck →
      ∀ (w : B256) (rest : Stack), zeroCheck.stack = w :: rest → w = 0) :
    Func.RunCompiledTo.RouteTo current h setPauserAssignmentPath
      (.reg .sstore) :=
  routeTo_call h lookup fun kernelStart _burn tail =>
    setPauserKernel_routeTo_assignment tail (nonzeroTarget kernelStart)

/-- A crossing that leaves the world state alone leaves storage alone.  Every
`Devm.PopBurnBy` and `Devm.BurnBy` the route kit hands back is `Devm.Rels.eq`
at the `state` field, so this is the whole content of "a branch and a call
write no storage". -/
theorem getStor_of_state {a b : Devm} (h : a.state = b.state) :
    Devm.getStor a = Devm.getStor b := by
  funext adr
  show (a.state.get adr).stor = (b.state.get adr).stor
  rw [h]

/-- Read a branch word off a known stack prefix. -/
theorem head_of_stack_prefix {devm : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ devm.stack) {w : B256} {rest : Stack}
    (hstack : devm.stack = w :: rest) : w = x := by
  rcases hp with ⟨t, ht⟩
  rw [hstack] at ht
  exact (List.cons.inj ht).1

/-- Carry a stack prefix across a branch's own pop. -/
theorem tail_of_stack_prefix {devm devm' : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ devm.stack)
    (hpop : ∃ w : B256, devm.stack = w :: devm'.stack) : xs <<+ devm'.stack := by
  rcases hpop with ⟨w, hw⟩
  rcases hp with ⟨t, ht⟩
  rw [hw] at ht
  exact ⟨t, (List.cons.inj ht).2⟩

/-! ## Carrying one memory word across a route

The `afterOldPauser` rows need a branch word that is **memory**-valued, and
unlike the kernel's storage-valued previous-pauser test it cannot be made
key-anonymous: the word *is* the staged new pauser, and there is nothing else
to read it off.  So a memory image has to travel from `registerPauser`'s
staging line down to `afterOldPauser`'s entry.

The image never becomes a byte list anyone `decide`s on.  Only one 32-byte
window is ever asked about, and three facts keep it symbolic all the way:

* a crossing that leaves memory alone keeps the window
  (`MemWordAt.acrossLine`, and the `.memory` field of every pop and burn);
* an `MLOAD`'s extension keeps it, because `Mem.extend` changes only the
  logical size and `Mem.Reads` reads the backing array
  (`MemWordAt.acrossLoadWord`); and
* a write at or past the end of the window keeps it
  (`MemWordAt.acrossMstoreAt`, on `Bytes.sliceD_writeAt_before`).

Every memory write this route crosses after the staging one lands at
`previousPauserWord`, `continuationWord` or `arrayLengthWord` — byte offsets
576, 608 and 672 — and the window is `[544, 576)`, so the third fact applies
every time and `Mem.Wf` is the only thing that has to be threaded beside the
image itself. -/

/-- A concrete memory image, with the structural invariant the write algebra
needs.  `Mem.Wf` is what rules out `Array.copyD` truncation, so it travels
beside the image rather than being re-derived at each write. -/
def MemImage (devm : Devm) (img : Bytes) : Prop :=
  Mem.Wf devm.memory ∧ Mem.Reads devm.memory img

theorem MemImage.of_memory_eq {a b : Devm} {img : Bytes}
    (h : b.memory = a.memory) (image : MemImage a img) : MemImage b img := by
  obtain ⟨hwf, hreads⟩ := image
  exact ⟨by rw [h]; exact hwf, by rw [h]; exact hreads⟩

theorem MemImage.write {a b : Devm} {img ys : Bytes} {n : Nat}
    (image : MemImage a img) (h : b.memory = a.memory.write n ys) :
    MemImage b (Bytes.writeAt img n ys) := by
  obtain ⟨hwf, hreads⟩ := image
  exact ⟨by rw [h]; exact hwf.write n ys,
    by rw [h]; exact Mem.Reads.write hwf hreads n ys⟩

/-- Memory reads the word `w` at byte offset `offset`.  The image stays
existential: no consumer of this predicate ever names the bytes, which is what
keeps a 640-byte scratch area out of every goal. -/
def MemWordAt (devm : Devm) (offset : Nat) (w : B256) : Prop :=
  Mem.Wf devm.memory ∧
    ∃ img : Bytes, Mem.Reads devm.memory img ∧
      img.sliceD offset 32 0 = w.toBytes

theorem MemWordAt.of_memImage {a : Devm} {img : Bytes} {offset : Nat}
    {w : B256} (image : MemImage a img)
    (hslice : img.sliceD offset 32 0 = w.toBytes) :
    MemWordAt a offset w := ⟨image.1, img, image.2, hslice⟩

/-- The window a write *creates*: reading a word straight back at the offset
it was written to, whatever the image was before. -/
theorem MemWordAt.of_write {a b : Devm} {img : Bytes} {n : Nat} {w : B256}
    (image : MemImage a img) (h : b.memory = a.memory.write n w.toBytes) :
    MemWordAt b n w := by
  refine MemWordAt.of_memImage (image.write h) ?_
  have slice := Bytes.sliceD_writeAt img w.toBytes n
  rwa [B256.length_toBytes] at slice

theorem MemWordAt.of_memory_eq {a b : Devm} {offset : Nat} {w : B256}
    (h : b.memory = a.memory) (window : MemWordAt a offset w) :
    MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  exact ⟨by rw [h]; exact hwf, img, by rw [h]; exact hreads, hslice⟩

theorem MemWordAt.extend {a b : Devm} {offset : Nat} {w : B256} {i n : Nat}
    (h : b.memory = a.memory.extend i n) (window : MemWordAt a offset w) :
    MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  exact ⟨by rw [h]; exact hwf.extend i n, img,
    by rw [h]; exact hreads.extend i n, hslice⟩

/-- A whole-word write that misses the window -- landing entirely after it or
entirely before it -- leaves the window alone.  Both directions are needed:
this route stores at 576 with a window at 544 (after) and at 576 again with a
window at 608 (before). -/
theorem MemWordAt.writeMiss {a b : Devm} {offset : Nat} {w v : B256} {n : Nat}
    (h : b.memory = a.memory.write n v.toBytes)
    (miss : offset + 32 ≤ n ∨ n + 32 ≤ offset)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  obtain ⟨hwf, img, hreads, hslice⟩ := window
  refine ⟨by rw [h]; exact hwf.write n v.toBytes,
    Bytes.writeAt img n v.toBytes,
    by rw [h]; exact Mem.Reads.write hwf hreads n v.toBytes, ?_⟩
  rcases miss with late | early
  · rw [Bytes.sliceD_writeAt_before img v.toBytes offset 32 n late]
    exact hslice
  · rw [Bytes.sliceD_writeAt_after img v.toBytes offset 32 n
      (by rw [B256.length_toBytes]; exact early)]
    exact hslice

/-- The window's own image, forgotten down to what a fresh write needs. -/
theorem MemWordAt.memImage {a : Devm} {offset : Nat} {w : B256}
    (window : MemWordAt a offset w) : ∃ img : Bytes, MemImage a img := by
  obtain ⟨hwf, img, hreads, _⟩ := window
  exact ⟨img, hwf, hreads⟩

/-- `mstoreAt k` writes *somewhere*: the offset is the pushed constant and the
value is forgotten.  `of_run_mstoreAt_val` names the value instead and needs a
stack prefix for it; a crossing only needs the offset. -/
theorem of_run_mstoreAt_mem {e : Sevm} {s s' : Devm} {k : B256}
    (h : Line.Run e s (mstoreAt k) s') :
    ∃ v : B256, s'.memory = s.memory.write (k * 32).toNat v.toBytes := by
  rcases Line.of_run_cons h with ⟨_u, qp, h'⟩
  rcases Line.of_run_cons h' with ⟨_u2, qm, hnil⟩
  cases hnil
  have hpb := of_run_pushB256 qp
  rcases of_run_mstore_val qm with ⟨x, y, hpop, hm⟩
  have hx : (k * 32) = x :=
    (List.of_cons_pref_of_cons_pref (prefix_of_push hpb nil_pref)
      (pref_of_split hpop)).left
  exact ⟨y, by rw [hm, ← hx, ← hpb.memory]⟩

/-- `loadWord k` only *extends* memory. -/
theorem of_run_loadWord_mem {e : Sevm} {s s' : Devm} {k : B256}
    (h : Line.Run e s (loadWord k) s') :
    ∃ i : Nat, s'.memory = s.memory.extend i 32 := by
  rcases Line.of_run_cons h with ⟨_u, qp, h'⟩
  rcases Line.of_run_cons h' with ⟨_u2, qm, hnil⟩
  cases hnil
  have hpb := of_run_pushB256 qp
  rcases of_run_mload_val qm with ⟨x, _, hm, _⟩
  exact ⟨x.toNat, by rw [hm, ← hpb.memory]⟩

/-- Cross a memory-silent line.  `line_inv` discharges the invariant for every
line on this route that contains no `MLOAD` and no `MSTORE`, including the
`SLOAD`s and `SSTORE`s. -/
theorem MemWordAt.acrossLine {e : Sevm} {a b : Devm} {offset : Nat} {w : B256}
    {l : Line} (inv : Line.Inv Devm.memory l) (run : Line.Run e a l b)
    (window : MemWordAt a offset w) : MemWordAt b offset w :=
  MemWordAt.of_memory_eq (Line.of_inv Devm.memory inv run).symm window

/-- Cross `loadWord k`, forgetting the loaded value. -/
theorem MemWordAt.acrossLoadWord {e : Sevm} {a b : Devm} {offset : Nat}
    {w k : B256} (run : Line.Run e a (loadWord k) b)
    (window : MemWordAt a offset w) : MemWordAt b offset w :=
  let ⟨_, hm⟩ := of_run_loadWord_mem run
  MemWordAt.extend hm window

/-- Cross `mstoreAt k` when the write misses the window. -/
theorem MemWordAt.acrossMstoreAt {e : Sevm} {a b : Devm} {offset : Nat}
    {w k : B256}
    (miss : offset + 32 ≤ (k * 32).toNat ∨ (k * 32).toNat + 32 ≤ offset)
    (run : Line.Run e a (mstoreAt k) b) (window : MemWordAt a offset w) :
    MemWordAt b offset w :=
  let ⟨_, hm⟩ := of_run_mstoreAt_mem run
  MemWordAt.writeMiss hm miss window

/-- Cross one instruction that `line_inv` has an instance for. -/
theorem MemWordAt.acrossNinst {e : Sevm} {a b : Devm} {offset : Nat} {w : B256}
    {i : Ninst} [inst : Ninst.Hinv Devm.memory i] (run : Ninst.Run e a i b)
    (window : MemWordAt a offset w) : MemWordAt b offset w :=
  MemWordAt.of_memory_eq (inst.inv run).symm window

/-- Cross one bare `MLOAD`. -/
theorem MemWordAt.acrossMload {e : Sevm} {a b : Devm} {offset : Nat} {w : B256}
    (run : Ninst.Run e a Ninst.mload b) (window : MemWordAt a offset w) :
    MemWordAt b offset w := by
  obtain ⟨_x, _, hm, _⟩ := of_run_mload_val run
  exact MemWordAt.extend hm window

/-- Cross a `LOG`: it reads a window and records it, and only *extends* the
backing array.  `line_inv` has no instance for `LOG`, and correctly so. -/
theorem MemWordAt.acrossLogWith {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} {k : Fin 4} {x y : B256}
    (run : Line.Run e a (logWith k x y) b) (window : MemWordAt a offset w) :
    MemWordAt b offset w := by
  unfold logWith at run
  rcases Line.of_run_cons run with ⟨_s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨_s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨_s3, q3, hnil⟩
  cases hnil
  obtain ⟨_mi, _sz, hm⟩ := of_run_log_mem q3
  exact MemWordAt.extend hm (MemWordAt.of_memory_eq
    ((of_run_pushB256 q1).memory.trans (of_run_pushB256 q2).memory).symm window)

/-- `loadWord k` followed by `iszero`: the shape of every memory-valued test
on this route.  Four branches read one, and the only thing that varies is
which word and what the image holds there. -/
def memoryZeroCheck (k : B256) : Line := loadWord k ++ [Ninst.iszero]

/-- Cross a memory-valued test. -/
theorem MemWordAt.acrossMemoryZeroCheck {e : Sevm} {a b : Devm} {offset : Nat}
    {w k : B256} (run : Line.Run e a (memoryZeroCheck k) b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold memoryZeroCheck at run
  rcases of_run_append (loadWord k) run with ⟨_s1, r1, run⟩
  exact (window.acrossLoadWord r1).acrossLine (by line_inv) run

/-- Read the window back: `MLOAD` at the window's own offset pushes exactly
the word the image holds there. -/
theorem prefix_of_loadWord_window {e : Sevm} {s s' : Devm} {k w : B256}
    {xs : Stack} (window : MemWordAt s (k * 32).toNat w)
    (hp : xs <<+ s.stack) (run : Line.Run e s (loadWord k) s') :
    w :: xs <<+ s'.stack := by
  rcases Line.of_run_cons run with ⟨u, qp, run'⟩
  rcases Line.of_run_cons run' with ⟨_u2, qm, hnil⟩
  cases hnil
  have hpb := of_run_pushB256 qp
  obtain ⟨_hwf, img, hreads, hslice⟩ := window
  have hreads' : Mem.Reads u.memory img := by rw [← hpb.memory]; exact hreads
  obtain ⟨hstack, _, _⟩ :=
    prefix_of_mload_val qm (prefix_of_push hpb hp) hreads'
  rw [hslice, B256.toB256_toBytes] at hstack
  exact hstack

/-- A memory-valued test's branch word: `iszero` of the word the image holds
at the tested offset. -/
theorem memoryZeroCheck_word {e : Sevm} {s s' : Devm} {k w : B256}
    (window : MemWordAt s (k * 32).toNat w)
    (run : Line.Run e s (memoryZeroCheck k) s') :
    ∀ (v : B256) (rest : Stack), s'.stack = v :: rest → v = (w =? 0) := by
  unfold memoryZeroCheck at run
  rcases of_run_append (loadWord k) run with ⟨s1, r1, run⟩
  have p1 : w :: [] <<+ s1.stack := prefix_of_loadWord_window window nil_pref r1
  rcases Line.of_run_cons run with ⟨_s2, q2, hnil⟩
  cases hnil
  intro v rest hstack
  exact head_of_stack_prefix (prefix_of_iszero q2 p1) hstack

/-! ## The dispatcher route

`Blanc/SourceAttainment.lean`'s route-construction kit takes `routeTo_line`'s
prefix in whatever form reads best: `fsig` and `arg k ++ checkNonAddress` are
passed to it below as combinator applications and unify without complaint.
The `def`s here — `splitTest`, `linearTest`, and the guard-cascade lines
further down — name lines that have no combinator form, not workarounds. -/

/-- One `splitDispatch` pivot test, spelled as a list literal. -/
def splitTest (pivot : B256) : Line :=
  [Ninst.dup 0, Ninst.pushB256 pivot, Ninst.gt]

/-- One `linearDispatchWith` selector test, spelled as a list literal. -/
def linearTest (word : B256) : Line :=
  [Ninst.dup 0, Ninst.pushB256 word, Ninst.eq]

/-- A pivot test leaves `pivot > selector` above the retained selector. -/
theorem prefix_of_splitTest {sevm : Sevm} {s s' : Devm} {sel pivot : B256}
    {xs : Stack} (hp : sel :: xs <<+ s.stack)
    (run : Line.Run sevm s (splitTest pivot) s') :
    (pivot >? sel) :: sel :: xs <<+ s'.stack := by
  rcases Line.of_run_cons run with ⟨_s1, hdup, r1⟩
  rcases Line.of_run_cons r1 with ⟨_s2, hpush, r2⟩
  rcases Line.of_run_cons r2 with ⟨_s3, hop, r3⟩
  cases r3
  exact prefix_of_gt hop (prefix_of_push (of_run_pushB256 hpush)
    (prefix_of_dup_val hdup (by show_nth) hp))

/-- A selector test leaves `word = selector` above the retained selector. -/
theorem prefix_of_linearTest {sevm : Sevm} {s s' : Devm} {sel word : B256}
    {xs : Stack} (hp : sel :: xs <<+ s.stack)
    (run : Line.Run sevm s (linearTest word) s') :
    (word =? sel) :: sel :: xs <<+ s'.stack := by
  rcases Line.of_run_cons run with ⟨_s1, hdup, r1⟩
  rcases Line.of_run_cons r1 with ⟨_s2, hpush, r2⟩
  rcases Line.of_run_cons r2 with ⟨_s3, hop, r3⟩
  cases r3
  exact prefix_of_eq hop (prefix_of_push (of_run_pushB256 hpush)
    (prefix_of_dup_val hdup (by show_nth) hp))

set_option maxRecDepth 16384 in
/-- The six selector crossings of `hybridDispatchWith`, on a walk whose
calldata selects `registerPauser`: two `splitDispatch` pivots taken jumped,
then three `linearDispatchWith` misses and the match.

The continuation is quantified over the reached source path, because the
`.call setPauserSlot` further down restarts the position at the callee's root:
no dispatcher path arithmetic survives it, so none is done here.

Two frame observations are carried alongside, on the same chain and for the
same reason: nothing in the dispatcher writes storage or memory, and both
facts are needed further down — storage for `setPauserKernel`'s previous-pauser
test, memory for `afterOldPauser`'s. -/
theorem dispatch_routeTo_registerPauser (dp : DeployParams)
    {fs : List Func} {sevm : Sevm} {devm : Devm} {out : Execution}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm
      (fsig +++ hybridDispatchWith fallbackSlot (funcs dp)) out)
    (selectorEq :
      Sevm.selector sevm = selector "registerPauser" [.address, .address])
    (bodyRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      Devm.getStor devm' = Devm.getStor devm →
      devm'.memory = devm.memory →
      ∀ tail : Func.RunCompiledTo fs sevm devm' (registerPauser dp) out,
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line fsig h (fun s0 run0 tail0 => ?_)
  have p0 : Sevm.selector sevm :: [] <<+ s0.stack := prefix_of_fsig nil_pref run0
  rw [selectorEq] at p0
  have g0 : Devm.getStor s0 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv) run0).symm
  have m0 : s0.memory = devm.memory :=
    (Line.of_inv Devm.memory (by line_inv) run0).symm
  refine routeTo_line (splitTest (selector "pause" [.address])) tail0
    (fun _s1 run1 tail1 => ?_)
  have p1 := prefix_of_splitTest p0 run1
  have g1 := (Line.of_inv Devm.getStor (by line_inv) run1).symm.trans g0
  have m1 := (Line.of_inv Devm.memory (by line_inv) run1).symm.trans m0
  refine routeTo_branchRight_frame tail1
    (fun _w _rest hs => by rw [head_of_stack_prefix p1 hs]; decide)
    (fun _s2 _w2 hpop2 tail2 => ?_)
  have p2 := tail_of_stack_prefix p1 ⟨_, hpop2.stack⟩
  have g2 := (getStor_of_state hpop2.state).symm.trans g1
  have m2 := hpop2.memory.symm.trans m1
  refine routeTo_line (splitTest (selector "getPauser" [.address])) tail2
    (fun _s3 run3 tail3 => ?_)
  have p3 := prefix_of_splitTest p2 run3
  have g3 := (Line.of_inv Devm.getStor (by line_inv) run3).symm.trans g2
  have m3 := (Line.of_inv Devm.memory (by line_inv) run3).symm.trans m2
  refine routeTo_branchRight_frame tail3
    (fun _w _rest hs => by rw [head_of_stack_prefix p3 hs]; decide)
    (fun _s4 _w4 hpop4 tail4 => ?_)
  have p4 := tail_of_stack_prefix p3 ⟨_, hpop4.stack⟩
  have g4 := (getStor_of_state hpop4.state).symm.trans g3
  have m4 := hpop4.memory.symm.trans m3
  refine routeTo_line (linearTest (selector "pauseDuration" [])) tail4
    (fun _s5 run5 tail5 => ?_)
  have p5 := prefix_of_linearTest p4 run5
  have g5 := (Line.of_inv Devm.getStor (by line_inv) run5).symm.trans g4
  have m5 := (Line.of_inv Devm.memory (by line_inv) run5).symm.trans m4
  refine routeTo_branchLeft_frame tail5
    (fun _w _rest hs => by rw [head_of_stack_prefix p5 hs]; decide)
    (fun _s6 hpop6 tail6 => ?_)
  have p6 := tail_of_stack_prefix p5 ⟨_, hpop6.stack⟩
  have g6 := (getStor_of_state hpop6.state).symm.trans g5
  have m6 := hpop6.memory.symm.trans m5
  refine routeTo_line (linearTest (selector "MAX_PAUSE_DURATION" [])) tail6
    (fun _s7 run7 tail7 => ?_)
  have p7 := prefix_of_linearTest p6 run7
  have g7 := (Line.of_inv Devm.getStor (by line_inv) run7).symm.trans g6
  have m7 := (Line.of_inv Devm.memory (by line_inv) run7).symm.trans m6
  refine routeTo_branchLeft_frame tail7
    (fun _w _rest hs => by rw [head_of_stack_prefix p7 hs]; decide)
    (fun _s8 hpop8 tail8 => ?_)
  have p8 := tail_of_stack_prefix p7 ⟨_, hpop8.stack⟩
  have g8 := (getStor_of_state hpop8.state).symm.trans g7
  have m8 := hpop8.memory.symm.trans m7
  refine routeTo_line (linearTest (selector "ADMIN" [])) tail8
    (fun _s9 run9 tail9 => ?_)
  have p9 := prefix_of_linearTest p8 run9
  have g9 := (Line.of_inv Devm.getStor (by line_inv) run9).symm.trans g8
  have m9 := (Line.of_inv Devm.memory (by line_inv) run9).symm.trans m8
  refine routeTo_branchLeft_frame tail9
    (fun _w _rest hs => by rw [head_of_stack_prefix p9 hs]; decide)
    (fun _s10 hpop10 tail10 => ?_)
  have p10 := tail_of_stack_prefix p9 ⟨_, hpop10.stack⟩
  have g10 := (getStor_of_state hpop10.state).symm.trans g9
  have m10 := hpop10.memory.symm.trans m9
  refine routeTo_line
    (linearTest (selector "registerPauser" [.address, .address])) tail10
    (fun _s11 run11 tail11 => ?_)
  have p11 := prefix_of_linearTest p10 run11
  have g11 := (Line.of_inv Devm.getStor (by line_inv) run11).symm.trans g10
  have m11 := (Line.of_inv Devm.memory (by line_inv) run11).symm.trans m10
  refine routeTo_branchRight_frame tail11
    (fun _w _rest hs => by rw [head_of_stack_prefix p11 hs]; decide)
    (fun _s12 _w12 hpop12 tail12 => ?_)
  have g12 := (getStor_of_state hpop12.state).symm.trans g11
  have m12 := hpop12.memory.symm.trans m11
  refine routeTo_line [Ninst.pop] tail12 (fun _s13 run13 tail13 => ?_)
  exact bodyRoute _ _
    ((Line.of_inv Devm.getStor (by line_inv) run13).symm.trans g12)
    ((Line.of_inv Devm.memory (by line_inv) run13).symm.trans m12) tail13

/-! ## The `registerPauser` guard cascade

Four branches, and not one of them costs a branch word: every arm this walk
does *not* take is `Func.rev` or a `.call` to one, so the successful outcome
alone settles all four. -/

/-- `requireStaticArgs 2`'s guard line, spelled literally. -/
def registerStaticArgsTest : Line :=
  [Ninst.pushB256 (Nat.toB256 (4 + 32 * 2)), Ninst.calldatasize, Ninst.lt]

/-- `onlyAdmin`'s guard line, spelled literally. -/
def adminTest (dp : DeployParams) : Line :=
  [Ninst.caller, pushDeployWord dp.admin, Ninst.eq]

/-- `registerPauser`'s staging line, from the admin guard to the kernel call. -/
def registerStagingLine : Line :=
  [Ninst.pushB256 ((32 * (0 : B256)) + 4), Ninst.calldataload,
   Ninst.pushB256 (targetWord * 32), Ninst.mstore,
   Ninst.pushB256 ((32 * (1 : B256)) + 4), Ninst.calldataload,
   Ninst.pushB256 (newPauserWord * 32), Ninst.mstore,
   Ninst.pushB256 0, Ninst.pushB256 (previousPauserWord * 32), Ninst.mstore,
   Ninst.pushB256 0, Ninst.pushB256 (continuationWord * 32), Ninst.mstore]

set_option maxRecDepth 8192 in
/-- From `registerPauser`'s entry to its `.call setPauserSlot`: the static
argument-length guard, two canonical-address guards and the admin guard,
crossed on the strength of the successful outcome alone.

The staging line is the one crossing whose *effect* a caller needs rather than
its invariance -- it is where the two arguments enter memory -- so the
continuation receives the crossing itself: the state the line started from,
that state's memory, and the `Line.Run`.  Everything before the staging line is
memory-silent, which is the whole content of `stage.memory = devm.memory`. -/
theorem registerPauser_routeTo_setPauserCall (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (registerPauser dp) (.ok post))
    (callRoute : ∀ (current : Prog.SourcePath) (stage devm' : Devm),
      Devm.getStor devm' = Devm.getStor devm →
      stage.memory = devm.memory →
      Line.Run sevm stage registerStagingLine devm' →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm devm' (Func.call setPauserSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line registerStaticArgsTest h (fun _s0 r0 tail0 => ?_)
  have g0 : Devm.getStor _s0 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv) r0).symm
  have n0 : _s0.memory = devm.memory :=
    (Line.of_inv Devm.memory (by line_inv) r0).symm
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail0 (fuel := 4) (by rfl)
    (fun _s1 hpop1 tail1 => ?_)
  have g1 := (getStor_of_state hpop1.state).symm.trans g0
  have n1 := hpop1.memory.symm.trans n0
  refine routeTo_line (arg 0 ++ checkNonAddress) tail1 (fun _s2 r2 tail2 => ?_)
  have g2 := (Line.of_inv Devm.getStor (by line_inv) r2).symm.trans g1
  have n2 := (Line.of_inv Devm.memory (by line_inv) r2).symm.trans n1
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail2 (fuel := 4) (by rfl)
    (fun _s3 hpop3 tail3 => ?_)
  have g3 := (getStor_of_state hpop3.state).symm.trans g2
  have n3 := hpop3.memory.symm.trans n2
  refine routeTo_line (arg 1 ++ checkNonAddress) tail3 (fun _s4 r4 tail4 => ?_)
  have g4 := (Line.of_inv Devm.getStor (by line_inv) r4).symm.trans g3
  have n4 := (Line.of_inv Devm.memory (by line_inv) r4).symm.trans n3
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail4 (fuel := 4) (by rfl)
    (fun _s5 hpop5 tail5 => ?_)
  have g5 := (getStor_of_state hpop5.state).symm.trans g4
  have n5 := hpop5.memory.symm.trans n4
  refine routeTo_line (adminTest dp) tail5 (fun _s6 r6 tail6 => ?_)
  have g6 := (Line.of_inv Devm.getStor
    (by unfold adminTest pushDeployWord; line_inv) r6).symm.trans g5
  have n6 := (Line.of_inv Devm.memory
    (by unfold adminTest pushDeployWord; line_inv) r6).symm.trans n5
  refine routeTo_branchRight_of_leftRevertsOk_frame tail6 (fuel := 8) (by rfl)
    (fun _s7 _w7 hpop7 tail7 => ?_)
  have g7 := (getStor_of_state hpop7.state).symm.trans g6
  have n7 := hpop7.memory.symm.trans n6
  refine routeTo_line registerStagingLine tail7 (fun _s8 r8 tail8 => ?_)
  exact callRoute _ _ _
    ((Line.of_inv Devm.getStor (by line_inv) r8).symm.trans g7) n7 r8 tail8

/-! ## The kernel leg and the whole route -/

/-- The kernel's zero-check crossed without its branch word: the
target-is-zero arm is `.call pausableZeroErrorSlot`, which cannot end `.ok`. -/
theorem setPauserKernel_routeTo_assignment_ok (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.ok post)) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h
      setPauserAssignmentPath (.reg .sstore) := by
  refine routeTo_line setPauserKernelZeroCheck h (fun _zeroCheck _run tail => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail (fuel := 8) (by rfl)
    (fun _armStart arm => ?_)
  refine routeTo_line setPauserKernelAssignmentPrefix arm
    (fun _writeState _writeRun write => ?_)
  have pathEq :
      ((([] ++ List.replicate setPauserKernelZeroCheck.length
              Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
          List.replicate setPauserKernelAssignmentPrefix.length
            Prog.SourceStep.rest) =
        setPauserAssignmentPath.steps := by
    simp [setPauserAssignmentPath, setPauserKernelZeroCheck,
      setPauserKernelAssignmentPrefix]
  exact pathEq ▸ routeTo_head write setPauserAssignmentPath

theorem call_setPauserSlot_routeTo_assignment_ok (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm} {current : Prog.SourcePath}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (.call setPauserSlot) (.ok post)) :
    Func.RunCompiledTo.RouteTo current h setPauserAssignmentPath
      (.reg .sstore) :=
  routeTo_call h (by rfl) fun _kernelStart _burn tail =>
    setPauserKernel_routeTo_assignment_ok dp tail

set_option maxRecDepth 16384 in
/-- The complete route: program entry to the `setPauser.assignment` `SSTORE`,
across all twelve branches.  Only the calldata selector is an execution
premise; the successful outcome discharges the other six branch words. -/
theorem runtimeMain_routeTo_setPauserAssignment (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (runtime dp).main (.ok post))
    (selectorEq :
      Sevm.selector sevm = selector "registerPauser" [.address, .address]) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h setPauserAssignmentPath
      (.reg .sstore) := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry _run tail => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail (fuel := 4) (by rfl)
    (fun _body arm => ?_)
  exact dispatch_routeTo_registerPauser dp arm selectorEq
    (fun _current _devm' _stor _mem bodyTail =>
      registerPauser_routeTo_setPauserCall dp bodyTail
        (fun _c _stage _d _stor' _mem' _staging callTail =>
          call_setPauserSlot_routeTo_assignment_ok dp callTail))

/-! ## Pinning the row

`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot` hands back *a*
row and the site it nominates.  The route names a *path*, so the two are
joined by the persistent inventory: PC identity settles which site was
reached, and index identity settles which row owns it. -/

theorem RuntimePersistentWrite.sourceSite?_official {dp : DeployParams}
    {row : RuntimePersistentWrite} {site : Prog.SourceSite}
    (found : row.sourceSite? dp = some site) :
    row.sourceSite? officialParams = some site := by
  unfold RuntimePersistentWrite.sourceSite? at found ⊢
  rwa [runtimePersistentSourceSites_eq_official dp] at found

set_option maxRecDepth 20000 in
/-- Only inventory index `3` — `.setPauserAssignment` — nominates a site whose
source path is `setPauserAssignmentPath`. -/
theorem setPauserAssignment_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some setPauserAssignmentPath) → index = 3 := by
  decide +kernel

/-- A row whose nominated site sits at `setPauserAssignmentPath` is exactly
`.setPauserAssignment`. -/
theorem RuntimePersistentWrite.eq_setPauserAssignment_of_path
    {dp : DeployParams} {row : RuntimePersistentWrite}
    {site : Prog.SourceSite} (found : row.sourceSite? dp = some site)
    (pathEq : site.path = setPauserAssignmentPath) :
    row = .setPauserAssignment := by
  have official := RuntimePersistentWrite.sourceSite?_official found
  unfold RuntimePersistentWrite.sourceSite? at official
  have mapped :
      (runtimePersistentSourceSites officialParams)[row.index]?.map
        (fun s => s.path) = some setPauserAssignmentPath := by
    rw [official]
    exact congrArg some pathEq
  have indexEq : row.index = 3 :=
    setPauserAssignment_index_pin row.index
      (List.mem_range.mpr (by
        have bound := row.index_lt
        omega)) mapped
  exact RuntimePersistentWrite.index_injective indexEq

/-! ## Same-frame reachability, and why no certificate is needed

`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot` consumes
`Exec.Deriv.ParentPrefix frameRoot occurrence.node`, and the routed bridge
returns exactly that, built alongside the derivation it constructs.  Nothing
below has to certify that the registration walk enters no child frame.

That is worth recording, because the certificate route looks mandatory and is
not, and one of the two ways of stating it is not even true.  Reading the
obligation at the *code* level — no reached node decodes an `Xinst` — cannot
hold here at all: the frozen inherited inventory is 20 persistent, 3 transient
and **2 external-call** runtime sites, and both call sites are in
`pauseAfterSet`, so a claim about `node.sevm.code` is a claim about a runtime
that demonstrably contains `CALL` and `STATICCALL`.  The honest version is
about which nodes the walk *visits*, which is what the direct-pause control
establishes as data: `Blanc/LidoCircuitBreakerRegistry.lean`'s private
`DirectPausePath` carries a childless side condition at every `.next` node,
and `directPause_zeroCode_postWrite_error_control` exports the result.

Even that version cannot be replaced by a decidable source-level certificate
in the style of `Func.alwaysRevertsWithin`.  Such a certificate has to pass
*both* arms of every `.branch` it crosses, and this runtime's dispatcher has a
`pause` arm; more sharply, `setPauserKernel` is shared, and its own
continuation branch in `finishSetPauser` selects `.call pauseAfterSetSlot` on
the pause side.  So no static certificate rooted at `runtimeMain` — or even at
`registerPauser` — can be `true`, however call-free the registration walk is.

The route already crosses only same-frame steps, so the fact is free: see
`Blanc/SourceAttainment.lean`'s *Same-frame packaging*. -/

/-- The concrete registration world is an exact runtime invocation. -/
theorem freshWorld_exactInvocation {post : Devm}
    (exc : Exec 0 freshWorldSevm freshWorldPre (.ok post)) :
    (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
      Exec.Deriv).exactInvocation (runtime officialParams)
      freshWorldOwner freshWorldOwner := by
  refine ⟨rfl, freshWorld_currentTarget, ?_, ?_⟩
  · show freshWorldSevm.codeAddress = some freshWorldOwner
    rw [freshWorld_codeAddress, freshWorld_currentTarget]
  · show some freshWorldSevm.code.toList = Prog.compile (runtime officialParams)
    rw [freshWorld_codeBytes, lidoCircuitBreakerCode_compile]

/-! ## The positive witness -/

/-- The first positive attainment witness: the concrete admin registration of
`Blanc/LidoCircuitBreakerRegistrationWorld.lean` reaches the
`.setPauserAssignment` row's own frozen source site with the `.adminRegistry`
invocation role.

Unconditional, and nothing in `Attainable` is relaxed, existentially hidden or
hypothesised: the row is named, the role is named, and the frame premises are
the ones `Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot`
consumes. -/
theorem attainable_setPauserAssignment_adminRegistry :
    Attainable officialParams .setPauserAssignment .adminRegistry := by
  obtain ⟨_trace, post, _htrace, _hentries, _hwitness, hrun, _hexec, _hfilled,
    _hgas, _hexpiry, _hlogs, hcompile⟩ := freshRegistrationWorld_run
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hroute := runtimeMain_routeTo_setPauserAssignment officialParams hwalk
    freshWorld_dataFacts.2.1
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    sameFrame⟩ :=
    Prog.exec_of_runCompiledTo_routeTo hburn hroute hcompile
  have invocation := freshWorld_exactInvocation exc
  have instructionEq : occurrence.instruction = .reg .sstore :=
    hinstr.trans hinstrTarget
  obtain ⟨row, rowSite, _rowMem, found, _classified, rowSitePc, _rowInstr,
    _unique, role, rolePermitted, authority⟩ :=
    Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot occurrence
      instructionEq (Exec.mem_rawFrameRoots_self exc) invocation sameFrame
  have routedMember : site ∈ runtimePersistentSourceSites officialParams := by
    unfold runtimePersistentSourceSites
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hinstrTarget, isPersistentWriteInstruction]⟩
  have siteEq : rowSite = site :=
    runtimePersistentSourceSite_eq_of_pc
      (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
      routedMember (rowSitePc.trans hpc)
  have rowEq : row = .setPauserAssignment :=
    RuntimePersistentWrite.eq_setPauserAssignment_of_path found
      (siteEq ▸ hpath)
  subst rowEq
  have roleEq : role = .adminRegistry := by
    have alternatives : role = .adminRegistry ∨ role = .pauseRegistry := by
      simpa [RuntimePersistentWrite.permittedRoles] using rolePermitted
    rcases alternatives with rfl | rfl
    · rfl
    · exfalso
      cases authority with
      | pauseRegistry _endpoint _assignedGuard _liveGuard assigned _live
          _writeSite =>
          have zero : freshWorldPre.getStorVal freshWorldOwner
              (assignmentSlot freshWorldTarget) = 0 := by
            have witness := freshWorld_preWitness.assignments freshWorldTarget
              freshWorld_targetValid.2
            rw [freshWorld_getStorVal, ← freshWorld_getStor]
            simpa [logicalStorageOfStor, assignmentAt] using witness
          rw [show (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
                Exec.Deriv).sevm = freshWorldSevm from rfl,
            freshWorld_currentTarget, freshWorld_dataFacts.2.2.1,
            show (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
                Exec.Deriv).devm = freshWorldPre from rfl,
            zero, freshWorld_admin] at assigned
          exact absurd assigned.symm (by decide)
  subst roleEq
  exact ⟨freshWorldOwner, ⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩,
    ⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩, occurrence, rowSite,
    instructionEq, Exec.mem_rawFrameRoots_self exc, invocation, sameFrame,
    found, rowSitePc, authority⟩


/-! ## The `appendTarget` rows

`freshRegistrationWorld_run` performs six persistent writes, and three of them
sit in source function 15, `appendTarget`.  Reaching them means crossing
`setPauserKernel`'s *second* branch — the `iszero` on the previous pauser the
kernel just `SLOAD`ed — and that arm's sibling is an ordinary old-pauser
update, not a `REVERT`, so the free crossing of
`routeTo_branchLeft_of_rightRevertsOk` is unavailable and the branch word has
to be computed.

The word is **storage-valued**, which is what the whole storage-carrying
apparatus below exists for: the crossed line's `SLOAD` reads a key the walk
built out of memory, so the `Devm.getStor` of the message-entry state has to
survive twelve earlier crossings to be read here.  It does, because a branch
and a call are `Devm.Rels.eq` in the `state` field
(`routeTo_branch*_frame`, `getStor_of_state`) and no line before the assignment
`SSTORE` contains one.

What *this* branch deliberately does not need is the memory image.  The key is
`slot assignmentRegion m` for **whatever** word `m` the kernel loaded, and this
world's storage is zero at *every* assignment slot — `heartbeatIntervalSlot` is
the only nonzero cell and it is in the config region.  Separating the two takes
no payload bound and no calldata fact, only one bit of the region tag, so this
crossing reads no memory.  The three later branches are not so lucky; the
windows they need are threaded past this point all the same. -/

/-- The config region's tag bit is set where the assignment region's is not, so
the fresh world's one nonzero cell is not an assignment slot — for any payload
whatsoever, canonical or not.  `slot_ne_of_region_ne` cannot be used here: it
needs both payloads below `2 ^ 252`, and a word loaded out of memory has no
such bound. -/
private theorem heartbeatIntervalSlot_ne_assignmentSlot (m : B256) :
    heartbeatIntervalSlot ≠ assignmentSlot m := by
  intro h
  have hl : heartbeatIntervalSlot.1.1 = (0x1000000000000000 : UInt64) := rfl
  have hr : (assignmentSlot m).1.1
      = (0x3000000000000000 : UInt64) ||| m.1.1 := rfl
  have h1 : (0x1000000000000000 : UInt64) = 0x3000000000000000 ||| m.1.1 := by
    rw [← hl, ← hr, h]
  have h2 := congrArg (fun u : UInt64 => u.toNat.testBit 61) h1
  rw [UInt64.toNat_or, Nat.testBit_or] at h2
  simp only [show (0x1000000000000000 : UInt64).toNat.testBit 61 = false from
      by decide,
    show (0x3000000000000000 : UInt64).toNat.testBit 61 = true from by decide,
    Bool.true_or] at h2
  exact Bool.noConfusion h2

/-- At the fresh registration world no target word is assigned a pauser. -/
theorem freshWorld_assignment_zero (m : B256) :
    freshWorldPre.getStorVal freshWorldOwner (assignmentSlot m) = 0 := by
  rw [freshWorld_getStorVal, freshWorldStor,
    Stor.get_set_ne _ (heartbeatIntervalSlot_ne_assignmentSlot m)]
  simp [Stor.get, Stor.empty]

/-- `setPauserKernelAssignmentPrefix` continued across the assignment `SSTORE`
and the previous-pauser zero test: the line whose last word decides the
kernel's second branch. -/
def setPauserKernelAppendPrefix : Line :=
  setPauserKernelAssignmentPrefix ++ [Ninst.sstore, Ninst.iszero]

/-- The kernel's second branch word, at the fresh registration world: the
previous pauser is zero, so the `iszero` above it is not — and the same zero is
what the kernel's own `mstoreAt previousPauserWord` stages, which is the second
conclusion.

The storage premise is that the walk has written no storage yet, which is
exactly what the `Devm.getStor` chain carries down from message entry.  The
loaded target word stays anonymous — see this section's note.  `window` is
needed only for its image: a fresh write's read-back is stated over the image
that was there before it, and any window carries one. -/
theorem freshWorld_previousPauserZero {devm devm' : Devm} {offset : Nat}
    {w : B256}
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (window : MemWordAt devm offset w)
    (run : Line.Run freshWorldSevm devm setPauserKernelAppendPrefix devm') :
    (∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w ≠ 0) ∧
      MemWordAt devm' (previousPauserWord * 32).toNat 0 := by
  unfold setPauserKernelAppendPrefix setPauserKernelAssignmentPrefix at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  rcases Line.of_run_cons run with ⟨s4, q4, run⟩
  have p1 : (targetWord * 32) :: [] <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 q1) nil_pref
  obtain ⟨m, p2⟩ := prefix_of_mload q2 p1
  have p3 : regionWord assignmentRegion :: m :: [] <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 q3) p2
  have p4 : assignmentSlot m :: [] <<+ s4.stack := prefix_of_or q4 p3
  have hstor4 : Devm.getStor s4 = Devm.getStor freshWorldPre := by
    rw [← hstor]
    exact (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons q1 (Line.Run.cons q2 (Line.Run.cons q3
        (Line.Run.cons q4 Line.Run.nil))))).symm
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  obtain ⟨v, p5, hv⟩ := prefix_of_sload q5 p4
  have hzero : v = 0 := by
    rw [hv, freshWorld_currentTarget,
      show Devm.getStorVal s4 freshWorldOwner (assignmentSlot m)
          = freshWorldPre.getStorVal freshWorldOwner (assignmentSlot m) from
        congrArg (fun f : Adr → Stor =>
          (f freshWorldOwner).get (assignmentSlot m)) hstor4]
    exact freshWorld_assignment_zero m
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  have p6 : v :: v :: [] <<+ s6.stack :=
    prefix_of_dup_val q6 (by show_nth) p5
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have p7 := prefix_of_push (of_run_pushB256 q7) p6
  rcases Line.of_run_cons run with ⟨s8, q8, run⟩
  obtain ⟨p8, hmem8⟩ := prefix_of_mstore_val q8 p7
  obtain ⟨_img7, image7⟩ :=
    (((((((window.acrossNinst q1).acrossMload q2).acrossNinst q3).acrossNinst
      q4).acrossNinst q5).acrossNinst q6).acrossNinst q7).memImage
  have staged : MemWordAt s8 (previousPauserWord * 32).toNat 0 := by
    rw [← hzero]
    exact MemWordAt.of_write image7 hmem8
  rcases Line.of_run_cons run with ⟨s9, q9, run⟩
  have p9 := prefix_of_push (of_run_pushB256 q9) p8
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  obtain ⟨n, p10⟩ := prefix_of_mload q10 p9
  rcases Line.of_run_cons run with ⟨s11, q11, run⟩
  have p11 := prefix_of_push (of_run_pushB256 q11) p10
  rcases Line.of_run_cons run with ⟨s12, q12, run⟩
  obtain ⟨m2, p12⟩ := prefix_of_mload q12 p11
  rcases Line.of_run_cons run with ⟨s13, q13, run⟩
  have p13 := prefix_of_push (of_run_pushB256 q13) p12
  rcases Line.of_run_cons run with ⟨s14, q14, run⟩
  have p14 := prefix_of_or q14 p13
  rcases Line.of_run_cons run with ⟨s15, q15, run⟩
  have p15 := prefix_of_sstore q15 p14
  rcases Line.of_run_cons run with ⟨s16, q16, hnil⟩
  cases hnil
  have p16 := prefix_of_iszero q16 p15
  refine ⟨?_, ?_⟩
  · intro w rest hstack
    rw [head_of_stack_prefix p16 hstack, hzero]
    decide
  · exact ((((((((staged.acrossNinst q9).acrossMload q10).acrossNinst
      q11).acrossMload q12).acrossNinst q13).acrossNinst q14).acrossNinst
      q15).acrossNinst q16)

/-! ### From the kernel to `appendTarget`'s three writes

`appendTarget` has no branch at all, so once the fresh arm is taken the three
rows are three different split points of one straight line. -/

/-- `appendTarget`'s prefix up to the array-entry `SSTORE`. -/
def appendArrayEntryPrefix : Line :=
  [Ninst.pushB256 arrayLengthSlot, Ninst.sload, Ninst.pushB256 1, Ninst.add,
    Ninst.dup 0] ++ mstoreAt arrayLengthWord ++ loadWord targetWord ++
    loadWord arrayLengthWord ++ tagTop arrayRegion

/-- From the array-entry `SSTORE` to the reverse-index `SSTORE`. -/
def appendReverseIndexPrefix : Line :=
  Ninst.sstore :: (loadWord arrayLengthWord ++ targetIndexKey)

/-- From the reverse-index `SSTORE` to the array-length `SSTORE`. -/
def appendArrayLengthPrefix : Line :=
  Ninst.sstore :: (loadWord arrayLengthWord ++ [Ninst.pushB256 arrayLengthSlot])

/-- Structural source position of the `append.arrayEntry` `SSTORE`. -/
def appendArrayEntryPath : Prog.SourcePath :=
  ⟨appendTargetSlot, List.replicate 13 .rest⟩

/-- Structural source position of the `append.reverseIndex` `SSTORE`. -/
def appendReverseIndexPath : Prog.SourcePath :=
  ⟨appendTargetSlot, List.replicate 20 .rest⟩

/-- Structural source position of the `append.arrayLength` `SSTORE`. -/
def appendArrayLengthPath : Prog.SourcePath :=
  ⟨appendTargetSlot, List.replicate 24 .rest⟩

/-! ### The staged words, and the lines they survive

`registerPauser`'s staging line is where the new pauser and the zero
continuation enter memory, and the crossings between there and
`registerAfterSet` are the lines below.  Each is split at its own memory
instructions and nowhere else: `line_inv` carries a window across every
memory-silent stretch, including the `SLOAD`s and `SSTORE`s, so only the
`MLOAD`s, the `MSTORE`s and the one `LOG` cost anything.

Three words are read as branch conditions on this route — the new pauser at
544, the previous pauser at 576 and the continuation at 608 — and they are
tracked as three independent windows rather than one image, because they are
created at three different points and each survives the others' writes by the
same one-line disjointness argument. -/

/-- The two words `registerPauser`'s staging line lays down that are later read
as branch conditions. -/
def EntryWindows (devm : Devm) : Prop :=
  MemWordAt devm (newPauserWord * 32).toNat freshWorldPauser ∧
    MemWordAt devm (continuationWord * 32).toNat 0

/-- Those two, plus the previous pauser that `setPauserKernel` stages out of
storage. -/
def KernelWindows (devm : Devm) : Prop :=
  EntryWindows devm ∧ MemWordAt devm (previousPauserWord * 32).toNat 0

/-- What the staging line stages: from empty memory, memory word
`newPauserWord` holds the call's second argument and memory word
`continuationWord` holds zero.

The image is built forward only as far as the new-pauser write and then read
back immediately (`MemWordAt.of_write`), so the target word laid down before it
never has to be described; the continuation window is read back the same way at
the line's last store.  Nothing here evaluates a byte. -/
theorem freshWorld_stagedEntry {stage post : Devm}
    (hmem : stage.memory = Mem.empty)
    (run : Line.Run freshWorldSevm stage registerStagingLine post) :
    EntryWindows post := by
  unfold registerStagingLine at run
  rcases of_run_append (arg 0) run with ⟨s1, r1, run⟩
  have p1 : Sevm.argWord freshWorldSevm 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref r1
  have i1 : MemImage s1 [] :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) r1).symm
      ⟨by rw [hmem]; exact Mem.wf_empty, by rw [hmem]; exact Mem.reads_empty⟩
  rcases of_run_append (mstoreAt targetWord) run with ⟨_s2, r2, run⟩
  obtain ⟨p2, hm2⟩ := of_run_mstoreAt_val r2 p1
  rcases of_run_append (arg 1) run with ⟨_s3, r3, run⟩
  have p3 := prefix_of_arg p2 r3
  have i3 : MemImage _s3 _ :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) r3).symm
      (i1.write hm2)
  rcases of_run_append (mstoreAt newPauserWord) run with ⟨_s4, r4, run⟩
  obtain ⟨_p4, hm4⟩ := of_run_mstoreAt_val r4 p3
  have window : MemWordAt _s4 (newPauserWord * 32).toNat freshWorldPauser := by
    rw [← freshWorld_dataFacts.2.2.2]
    exact MemWordAt.of_write i3 hm4
  rcases of_run_append [Ninst.pushB256 0] run with ⟨_s5, r5, run⟩
  have p5 : (0 : B256) :: [] <<+ _s5.stack := by
    rcases Line.of_run_cons r5 with ⟨_u, qu, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 qu) _p4
  rcases of_run_append (mstoreAt previousPauserWord) run with ⟨_s6, r6, run⟩
  obtain ⟨p6, _⟩ := of_run_mstoreAt_val r6 p5
  rcases of_run_append [Ninst.pushB256 0] run with ⟨_s7, r7, run⟩
  have p7 : (0 : B256) :: [] <<+ _s7.stack := by
    rcases Line.of_run_cons r7 with ⟨_u, qu, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 qu) p6
  have window7 : MemWordAt _s7 (newPauserWord * 32).toNat freshWorldPauser :=
    ((window.acrossLine (by line_inv) r5).acrossMstoreAt (by decide)
      r6).acrossLine (by line_inv) r7
  obtain ⟨_img7, image7⟩ := window7.memImage
  obtain ⟨_p8, hm8⟩ := of_run_mstoreAt_val run p7
  exact ⟨window7.acrossMstoreAt (by decide) run,
    MemWordAt.of_write image7 hm8⟩

/-- The kernel's zero-check reads memory and writes none. -/
theorem MemWordAt.acrossZeroCheck {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a setPauserKernelZeroCheck b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold setPauserKernelZeroCheck at run
  rcases of_run_append (loadWord targetWord) run with ⟨_s1, r1, run⟩
  exact (window.acrossLoadWord r1).acrossLine (by line_inv) run

/-- The kernel's assignment line plus its previous-pauser test.  Its one write
is `mstoreAt previousPauserWord`. -/
theorem MemWordAt.acrossAppendPrefix {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256}
    (miss : offset + 32 ≤ (previousPauserWord * 32).toNat ∨
      (previousPauserWord * 32).toNat + 32 ≤ offset)
    (run : Line.Run e a setPauserKernelAppendPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold setPauserKernelAppendPrefix setPauserKernelAssignmentPrefix at run
  rcases of_run_append (loadWord targetWord) run with ⟨_s1, r1, run⟩
  rcases of_run_append
    [Ninst.pushB256 (regionWord assignmentRegion), Ninst.or, Ninst.sload,
      Ninst.dup 0] run with ⟨_s2, r2, run⟩
  rcases of_run_append (mstoreAt previousPauserWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s4, r4, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s5, r5, run⟩
  exact (((((window.acrossLoadWord r1).acrossLine (by line_inv)
    r2).acrossMstoreAt miss r3).acrossLoadWord r4).acrossLoadWord
    r5).acrossLine (by line_inv) run

/-- `appendTarget`'s first fragment.  Its one write is
`mstoreAt arrayLengthWord`. -/
theorem MemWordAt.acrossArrayEntryPrefix {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256}
    (miss : offset + 32 ≤ (arrayLengthWord * 32).toNat ∨
      (arrayLengthWord * 32).toNat + 32 ≤ offset)
    (run : Line.Run e a appendArrayEntryPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold appendArrayEntryPrefix at run
  rcases of_run_append
    [Ninst.pushB256 arrayLengthSlot, Ninst.sload, Ninst.pushB256 1, Ninst.add,
      Ninst.dup 0] run with ⟨_s1, r1, run⟩
  rcases of_run_append (mstoreAt arrayLengthWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append (loadWord arrayLengthWord) run with ⟨_s4, r4, run⟩
  exact ((((window.acrossLine (by line_inv) r1).acrossMstoreAt miss
    r2).acrossLoadWord r3).acrossLoadWord r4).acrossLine (by line_inv) run

/-- `appendTarget`'s second fragment: reads only. -/
theorem MemWordAt.acrossReverseIndexPrefix {e : Sevm} {a b : Devm}
    {offset : Nat} {w : B256}
    (run : Line.Run e a appendReverseIndexPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold appendReverseIndexPrefix targetIndexKey at run
  rcases of_run_append [Ninst.sstore] run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord arrayLengthWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  exact (((window.acrossLine (by line_inv) r1).acrossLoadWord
    r2).acrossLoadWord r3).acrossLine (by line_inv) run

/-- `appendTarget`'s third fragment: reads only. -/
theorem MemWordAt.acrossArrayLengthPrefix {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a appendArrayLengthPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold appendArrayLengthPrefix at run
  rcases of_run_append [Ninst.sstore] run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord arrayLengthWord) run with ⟨_s2, r2, run⟩
  exact ((window.acrossLine (by line_inv) r1).acrossLoadWord
    r2).acrossLine (by line_inv) run

/-! ### The same crossings on the bundles

Three windows crossing the same line is three instances of one lemma, and the
offsets are concrete, so each `miss` side condition is a `decide` on two
literals.  Bundling them keeps the route theorems reading like the single-window
ones. -/

theorem EntryWindows.of_memory_eq {a b : Devm} (h : b.memory = a.memory)
    (windows : EntryWindows a) : EntryWindows b :=
  ⟨MemWordAt.of_memory_eq h windows.1, MemWordAt.of_memory_eq h windows.2⟩

theorem EntryWindows.acrossZeroCheck {e : Sevm} {a b : Devm}
    (run : Line.Run e a setPauserKernelZeroCheck b)
    (windows : EntryWindows a) : EntryWindows b :=
  ⟨windows.1.acrossZeroCheck run, windows.2.acrossZeroCheck run⟩

theorem EntryWindows.acrossAppendPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a setPauserKernelAppendPrefix b)
    (windows : EntryWindows a) : EntryWindows b :=
  ⟨windows.1.acrossAppendPrefix (by decide) run,
    windows.2.acrossAppendPrefix (by decide) run⟩

theorem KernelWindows.of_memory_eq {a b : Devm} (h : b.memory = a.memory)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨EntryWindows.of_memory_eq h windows.1, MemWordAt.of_memory_eq h windows.2⟩

theorem KernelWindows.acrossLine {e : Sevm} {a b : Devm} {l : Line}
    (inv : Line.Inv Devm.memory l) (run : Line.Run e a l b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossLine inv run, windows.1.2.acrossLine inv run⟩,
    windows.2.acrossLine inv run⟩

theorem KernelWindows.acrossArrayEntryPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a appendArrayEntryPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossArrayEntryPrefix (by decide) run,
    windows.1.2.acrossArrayEntryPrefix (by decide) run⟩,
    windows.2.acrossArrayEntryPrefix (by decide) run⟩

theorem KernelWindows.acrossReverseIndexPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a appendReverseIndexPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossReverseIndexPrefix run,
    windows.1.2.acrossReverseIndexPrefix run⟩,
    windows.2.acrossReverseIndexPrefix run⟩

theorem KernelWindows.acrossArrayLengthPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a appendArrayLengthPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossArrayLengthPrefix run,
    windows.1.2.acrossArrayLengthPrefix run⟩,
    windows.2.acrossArrayLengthPrefix run⟩

theorem KernelWindows.acrossMemoryZeroCheck {e : Sevm} {a b : Devm} {k : B256}
    (run : Line.Run e a (memoryZeroCheck k) b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossMemoryZeroCheck run,
    windows.1.2.acrossMemoryZeroCheck run⟩,
    windows.2.acrossMemoryZeroCheck run⟩

/-- Inside `setPauserKernel` at the fresh registration world: the zero-target
arm is a certified-reverting call, and the previous-pauser test takes the
jumped arm, so the walk reaches `.call appendTargetSlot`. -/
theorem setPauserKernel_routeTo_appendCall {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm setPauserKernel (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (windows : EntryWindows devm)
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call appendTargetSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h targetPath
      targetInstruction := by
  refine routeTo_line setPauserKernelZeroCheck h (fun _z zrun tail => ?_)
  have g0 := (Line.of_inv Devm.getStor (by line_inv) zrun).symm.trans hstor
  have e0 := windows.acrossZeroCheck zrun
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 8) (by rfl)
    (fun _s1 hpop1 arm => ?_)
  have g1 := (getStor_of_state hpop1.state).symm.trans g0
  have e1 := EntryWindows.of_memory_eq hpop1.memory.symm e0
  refine routeTo_line setPauserKernelAppendPrefix arm
    (fun _s2 run2 tail2 => ?_)
  obtain ⟨branchWord, staged⟩ := freshWorld_previousPauserZero g1 e1.1 run2
  refine routeTo_branchRight_frame tail2 branchWord
    (fun _s3 _w3 hpop3 tail3 => ?_)
  exact callRoute _ _
    (KernelWindows.of_memory_eq hpop3.memory.symm
      ⟨e1.acrossAppendPrefix run2, staged⟩) tail3

/-- The `.call setPauserSlot` crossing, carrying the entry storage and the
staged memory word into the kernel. -/
theorem call_setPauserSlot_routeTo_appendCall {devm post : Devm}
    {current targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (.call setPauserSlot) (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (windows : EntryWindows devm)
    (callRoute : ∀ (current' : Prog.SourcePath) (devm' : Devm),
      KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call appendTargetSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current' tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo current h targetPath targetInstruction :=
  routeTo_call h (by rfl) fun _kernelStart burn tail =>
    setPauserKernel_routeTo_appendCall tail
      ((getStor_of_state burn.state).symm.trans hstor)
      (EntryWindows.of_memory_eq burn.memory.symm windows) callRoute

set_option maxRecDepth 16384 in
/-- The complete route from program entry to `appendTarget`'s own root, at the
fresh registration world.  Thirteen branches: six selector comparisons decided
on the concrete calldata selector, six settled by certified-reverting siblings,
and the kernel's storage-valued previous-pauser test.

The continuation also receives the three staged memory words, which is what the
`afterOldPauser` and `registerAfterSet` rows below need and the three
`appendTarget` rows ignore. -/
theorem runtimeMain_routeTo_appendCall {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty)
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call appendTargetSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h targetPath targetInstruction := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry erun tail => ?_)
  have g0 := (Line.of_inv Devm.getStor (by line_inv) erun).symm.trans hstor
  have n0 := (Line.of_inv Devm.memory (by line_inv) erun).symm.trans hmem
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 4) (by rfl)
    (fun _body hpop arm => ?_)
  have g1 := (getStor_of_state hpop.state).symm.trans g0
  have n1 := hpop.memory.symm.trans n0
  exact dispatch_routeTo_registerPauser officialParams arm
    freshWorld_dataFacts.2.1
    (fun _current _devm' dstor dmem bodyTail =>
      registerPauser_routeTo_setPauserCall officialParams bodyTail
        (fun _c _stage _d rstor rmem staging callTail =>
          call_setPauserSlot_routeTo_appendCall callTail
            (rstor.trans (dstor.trans g1))
            (freshWorld_stagedEntry (rmem.trans (dmem.trans n1)) staging)
            callRoute))

/-- The array-entry write: `appendTarget`'s first `SSTORE`. -/
theorem runtimeMain_routeTo_appendArrayEntry {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h appendArrayEntryPath (.reg .sstore) :=
  runtimeMain_routeTo_appendCall h hstor hmem
    fun _current _devm' _window callTail =>
    routeTo_call callTail (by rfl) fun _bodyStart _burn body => by
      refine routeTo_line appendArrayEntryPrefix body
        (fun _s _run write => ?_)
      have pathEq :
          ([] ++ List.replicate appendArrayEntryPrefix.length
            Prog.SourceStep.rest) = appendArrayEntryPath.steps := by
        simp [appendArrayEntryPath, appendArrayEntryPrefix, mstoreAt, loadWord,
          tagTop]
      exact pathEq ▸ routeTo_head write appendArrayEntryPath

/-- The reverse-index write: `appendTarget`'s second `SSTORE`. -/
theorem runtimeMain_routeTo_appendReverseIndex {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h appendReverseIndexPath
      (.reg .sstore) :=
  runtimeMain_routeTo_appendCall h hstor hmem
    fun _current _devm' _window callTail =>
    routeTo_call callTail (by rfl) fun _bodyStart _burn body => by
      refine routeTo_line appendArrayEntryPrefix body
        (fun _s _run entry => ?_)
      refine routeTo_line appendReverseIndexPrefix entry
        (fun _s' _run' write => ?_)
      have pathEq :
          (([] ++ List.replicate appendArrayEntryPrefix.length
              Prog.SourceStep.rest) ++
            List.replicate appendReverseIndexPrefix.length
              Prog.SourceStep.rest) = appendReverseIndexPath.steps := by
        simp [appendReverseIndexPath, appendArrayEntryPrefix,
          appendReverseIndexPrefix, mstoreAt, loadWord, tagTop,
          targetIndexKey]
      exact pathEq ▸ routeTo_head write appendReverseIndexPath

/-- The array-length write: `appendTarget`'s third `SSTORE`. -/
theorem runtimeMain_routeTo_appendArrayLength {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h appendArrayLengthPath (.reg .sstore) :=
  runtimeMain_routeTo_appendCall h hstor hmem
    fun _current _devm' _window callTail =>
    routeTo_call callTail (by rfl) fun _bodyStart _burn body => by
      refine routeTo_line appendArrayEntryPrefix body
        (fun _s _run entry => ?_)
      refine routeTo_line appendReverseIndexPrefix entry
        (fun _s' _run' index => ?_)
      refine routeTo_line appendArrayLengthPrefix index
        (fun _s'' _run'' write => ?_)
      have pathEq :
          ((([] ++ List.replicate appendArrayEntryPrefix.length
                Prog.SourceStep.rest) ++
              List.replicate appendReverseIndexPrefix.length
                Prog.SourceStep.rest) ++
            List.replicate appendArrayLengthPrefix.length
              Prog.SourceStep.rest) = appendArrayLengthPath.steps := by
        simp [appendArrayLengthPath, appendArrayEntryPrefix,
          appendReverseIndexPrefix, appendArrayLengthPrefix, mstoreAt,
          loadWord, tagTop, targetIndexKey]
      exact pathEq ▸ routeTo_head write appendArrayLengthPath

/-! ### Pinning the three rows

`RuntimePersistentWrite.eq_setPauserAssignment_of_path`, generalized: the
inventory index that nominates a given source path names the row, and the only
row-specific input is one decidable index pin. -/

/-- A row whose nominated site sits at `path` is the row that `indexPin`
names. -/
theorem RuntimePersistentWrite.eq_of_path
    {row target : RuntimePersistentWrite} {site : Prog.SourceSite}
    {path : Prog.SourcePath}
    (indexPin : ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
        (fun s => s.path) = some path) → index = target.index)
    (found : row.sourceSite? officialParams = some site)
    (pathEq : site.path = path) :
    row = target := by
  unfold RuntimePersistentWrite.sourceSite? at found
  have mapped :
      (runtimePersistentSourceSites officialParams)[row.index]?.map
        (fun s => s.path) = some path := by
    rw [found]
    exact congrArg some pathEq
  have indexEq : row.index = target.index :=
    indexPin row.index
      (List.mem_range.mpr (by
        have bound := row.index_lt
        omega)) mapped
  exact RuntimePersistentWrite.index_injective indexEq

set_option maxRecDepth 20000 in
/-- Inventory indices `5`, `6` and `7` — `.appendArrayEntry`,
`.appendReverseIndex` and `.appendArrayLength` — are the only ones nominating
the three `appendTarget` paths.  One kernel evaluation settles all three. -/
theorem append_index_pins :
    (∀ index ∈ List.range 20,
        ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some appendArrayEntryPath) → index = 5) ∧
      (∀ index ∈ List.range 20,
        ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some appendReverseIndexPath) → index = 6) ∧
      (∀ index ∈ List.range 20,
        ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some appendArrayLengthPath) → index = 7) := by
  decide +kernel

/-! ### The witnesses

Everything after the route is row-independent, so it is proved once.  The
`.pauseRegistry` alternative is refuted at the *frame root*, not at the write:
a pause invocation's authority payload asserts that the caller is the assigned
pauser of the calldata target, and at this world every assignment slot is zero
while the caller is the nonzero admin.

The tail is stated for an arbitrary expected role, because the rows below it
do not all carry the same one — `afterOld.newCount` permits `.adminRegistry`
alone and `register.freshExpiry` permits `.adminExpiry` alone.  A row whose
`permittedRoles` is a singleton pays nothing for the refutation: its `roles`
premise closes the `.pauseRegistry` disjunct vacuously. -/

/-- The shared tail of every witness at the fresh registration world: a route
to a row's frozen path yields that row attained with the expected role. -/
theorem attainable_of_route {row : RuntimePersistentWrite}
    {expected : InvocationRole} {path : Prog.SourcePath}
    (pin : ∀ {r : RuntimePersistentWrite} {site : Prog.SourceSite},
      r.sourceSite? officialParams = some site → site.path = path → r = row)
    (roles : ∀ r ∈ row.permittedRoles,
      r = expected ∨ r = InvocationRole.pauseRegistry)
    (route : ∀ (devm post : Devm)
      (h : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm (runtime officialParams).main (.ok post)),
      Devm.getStor devm = Devm.getStor freshWorldPre →
      devm.memory = Mem.empty →
      Func.RunCompiledTo.RouteTo ⟨0, []⟩ h path (.reg .sstore)) :
    Attainable officialParams row expected := by
  obtain ⟨_trace, post, _htrace, _hentries, _hwitness, hrun, _hexec, _hfilled,
    _hgas, _hexpiry, _hlogs, hcompile⟩ := freshRegistrationWorld_run
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hroute := route mid post hwalk (getStor_of_state hburn.state).symm
    hburn.memory.symm
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    sameFrame⟩ :=
    Prog.exec_of_runCompiledTo_routeTo hburn hroute hcompile
  have invocation := freshWorld_exactInvocation exc
  have instructionEq : occurrence.instruction = .reg .sstore :=
    hinstr.trans hinstrTarget
  obtain ⟨reached, rowSite, _rowMem, found, _classified, rowSitePc, _rowInstr,
    _unique, role, rolePermitted, authority⟩ :=
    Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot occurrence
      instructionEq (Exec.mem_rawFrameRoots_self exc) invocation sameFrame
  have routedMember : site ∈ runtimePersistentSourceSites officialParams := by
    unfold runtimePersistentSourceSites
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hinstrTarget, isPersistentWriteInstruction]⟩
  have siteEq : rowSite = site :=
    runtimePersistentSourceSite_eq_of_pc
      (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
      routedMember (rowSitePc.trans hpc)
  have rowEq : reached = row := pin found (siteEq ▸ hpath)
  subst rowEq
  have roleEq : role = expected := by
    rcases roles role rolePermitted with rfl | rfl
    · rfl
    · exfalso
      cases authority with
      | pauseRegistry _endpoint _assignedGuard _liveGuard assigned _live
          _writeSite =>
          rw [show (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
                Exec.Deriv).sevm = freshWorldSevm from rfl,
            freshWorld_currentTarget,
            show (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
                Exec.Deriv).devm = freshWorldPre from rfl,
            freshWorld_assignment_zero, freshWorld_admin] at assigned
          exact absurd assigned.symm (by decide)
  subst roleEq
  exact ⟨freshWorldOwner, ⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩,
    ⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩, occurrence, rowSite,
    instructionEq, Exec.mem_rawFrameRoots_self exc, invocation, sameFrame,
    found, rowSitePc, authority⟩

/-- The `append.arrayEntry` row is attained with the `.adminRegistry` role. -/
theorem attainable_appendArrayEntry_adminRegistry :
    Attainable officialParams .appendArrayEntry .adminRegistry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path append_index_pins.1 found pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_appendArrayEntry h hstor hmem)

/-- The `append.reverseIndex` row is attained with the `.adminRegistry`
role. -/
theorem attainable_appendReverseIndex_adminRegistry :
    Attainable officialParams .appendReverseIndex .adminRegistry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path append_index_pins.2.1 found pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_appendReverseIndex h hstor hmem)

/-- The `append.arrayLength` row is attained with the `.adminRegistry` role. -/
theorem attainable_appendArrayLength_adminRegistry :
    Attainable officialParams .appendArrayLength .adminRegistry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path append_index_pins.2.2 found pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_appendArrayLength h hstor hmem)

/-! ## The `afterOld.newCount` row

Source function 16, one `.call` past `appendTarget`.  The fourteenth branch,
and the first whose word is **memory**-valued: `afterOldPauser` opens by
testing the staged new pauser, and -- unlike the kernel's previous-pauser test,
which the entry storage settles for *any* loaded key -- there is nothing to
read this word off except the memory the staging line wrote.  That is what the
window machinery above exists for, and it is the whole of the row's extra cost:
the route is otherwise `runtimeMain_routeTo_appendCall` continued through
`appendTarget`'s three writes.

Role pinning is free here.  `permittedRoles` lists `.adminRegistry` alone, so
the `.pauseRegistry` disjunct of `attainable_of_route`'s `roles` premise closes
by `decide` and no execution-level refutation is involved -- which is a
different fact from `not_attainable_afterOldNewCount_pauseRegistry` above, and
neither implies the other. -/

/-- `afterOldPauser`'s fall-through arm, from the branch to the `SSTORE`:
`newCountKey ++ [sload, push 1, add] ++ newCountKey`. -/
def afterOldNewCountPrefix : Line :=
  newCountKey ++ [Ninst.sload, Ninst.pushB256 1, Ninst.add] ++ newCountKey

/-- Structural source position of the `afterOld.newCount` `SSTORE`. -/
def afterOldNewCountPath : Prog.SourcePath :=
  ⟨afterOldPauserSlot,
    List.replicate 3 .rest ++ [.branchLeft] ++ List.replicate 11 .rest⟩

theorem MemWordAt.acrossNewCountKey {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a newCountKey b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold newCountKey at run
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s1, r1, run⟩
  exact (window.acrossLoadWord r1).acrossLine (by line_inv) run

theorem MemWordAt.acrossNewCountPrefix {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a afterOldNewCountPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold afterOldNewCountPrefix at run
  rcases of_run_append newCountKey run with ⟨_s1, r1, run⟩
  rcases of_run_append [Ninst.sload, Ninst.pushB256 1, Ninst.add] run
    with ⟨_s2, r2, run⟩
  exact ((window.acrossNewCountKey r1).acrossLine (by line_inv)
    r2).acrossNewCountKey run

theorem KernelWindows.acrossNewCountPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a afterOldNewCountPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossNewCountPrefix run,
    windows.1.2.acrossNewCountPrefix run⟩,
    windows.2.acrossNewCountPrefix run⟩

set_option maxRecDepth 16384 in
/-- From program entry to `afterOldPauser`'s own root: the three
`appendTarget` writes crossed, then its tail call.  Both rows past
`appendTarget` start here. -/
theorem runtimeMain_routeTo_afterOldCall {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty)
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call afterOldPauserSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h targetPath targetInstruction := by
  refine runtimeMain_routeTo_appendCall h hstor hmem
    (fun _current _devm' windows callTail => ?_)
  refine routeTo_call callTail (by rfl) (fun _bodyStart burn body => ?_)
  have k0 := KernelWindows.of_memory_eq burn.memory.symm windows
  refine routeTo_line appendArrayEntryPrefix body (fun _s1 r1 entry => ?_)
  refine routeTo_line appendReverseIndexPrefix entry (fun _s2 r2 index => ?_)
  refine routeTo_line appendArrayLengthPrefix index
    (fun _s3 r3 lengthWrite => ?_)
  refine routeTo_line [Ninst.sstore] lengthWrite (fun _s4 r4 afterCall => ?_)
  exact callRoute _ _
    ((((k0.acrossArrayEntryPrefix r1).acrossReverseIndexPrefix
      r2).acrossArrayLengthPrefix r3).acrossLine (by line_inv) r4) afterCall

/-- `afterOldPauser`'s branch word at the fresh registration world: the staged
new pauser is `9`, so its `iszero` is zero and the walk falls through to the
new-count update rather than to `removeTarget`.

The staged window is the only premise, and it is the one thing the whole memory
apparatus is for. -/
theorem freshWorld_newPauserNonzero {devm devm' : Devm}
    (window : MemWordAt devm (newPauserWord * 32).toNat freshWorldPauser)
    (run : Line.Run freshWorldSevm devm (memoryZeroCheck newPauserWord) devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0 := by
  intro w rest hstack
  rw [memoryZeroCheck_word window run w rest hstack]
  decide

/-- Inside `afterOldPauser` at the fresh registration world: the entry test
falls through, so the walk reaches the new-count `SSTORE` and, past it, the
`.call finishSetPauserSlot`. -/
theorem afterOldPauser_routeTo_newCountArm {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm afterOldPauser (.ok post))
    (windows : KernelWindows devm)
    (armRoute : ∀ devm' : Devm, KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm'
        (newCountKey +++ Ninst.sload ::: Ninst.pushB256 1 ::: Ninst.add :::
          newCountKey +++ Ninst.sstore ::: Func.call finishSetPauserSlot)
        (.ok post),
        Func.RunCompiledTo.RouteTo
          ⟨afterOldPauserSlot,
            List.replicate 3 .rest ++ [Prog.SourceStep.branchLeft]⟩ tail
          targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨afterOldPauserSlot, []⟩ h targetPath
      targetInstruction := by
  refine routeTo_line (memoryZeroCheck newPauserWord) h
    (fun _s5 r5 tail5 => ?_)
  refine routeTo_branchLeft_frame tail5
    (freshWorld_newPauserNonzero windows.1.1 r5) (fun _s6 hpop arm => ?_)
  have pathEq :
      ([] ++ List.replicate (memoryZeroCheck newPauserWord).length
            Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft] =
        List.replicate 3 Prog.SourceStep.rest ++
          [Prog.SourceStep.branchLeft] := by
    simp [memoryZeroCheck, loadWord]
  exact pathEq ▸ armRoute _
    (KernelWindows.of_memory_eq hpop.memory.symm
      (windows.acrossMemoryZeroCheck r5)) arm

set_option maxRecDepth 16384 in
/-- The complete route from program entry to the `afterOld.newCount` `SSTORE`:
`runtimeMain_routeTo_afterOldCall`, then the tail call into `afterOldPauser`
and its memory-valued entry test. -/
theorem runtimeMain_routeTo_afterOldNewCount {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h afterOldNewCountPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_afterOldCall h hstor hmem
    (fun _current _devm' windows callTail => ?_)
  refine routeTo_call callTail (by rfl)
    (fun _afterStart afterBurn afterBody => ?_)
  refine afterOldPauser_routeTo_newCountArm afterBody
    (KernelWindows.of_memory_eq afterBurn.memory.symm windows)
    (fun _devm'' _windows'' arm => ?_)
  refine routeTo_line afterOldNewCountPrefix arm (fun _s7 _r7 write => ?_)
  have pathEq :
      ((List.replicate 3 Prog.SourceStep.rest ++
            [Prog.SourceStep.branchLeft]) ++
          List.replicate afterOldNewCountPrefix.length Prog.SourceStep.rest) =
        afterOldNewCountPath.steps := by
    simp [afterOldNewCountPath, afterOldNewCountPrefix, loadWord, newCountKey,
      tagTop]
  exact pathEq ▸ routeTo_head write afterOldNewCountPath

set_option maxRecDepth 20000 in
/-- Inventory index `8` -- `.afterOldNewCount` -- is the only one nominating
`afterOldNewCountPath`. -/
theorem afterOldNewCount_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some afterOldNewCountPath) → index = 8 := by
  decide +kernel

/-- The `afterOld.newCount` row is attained with the `.adminRegistry` role. -/
theorem attainable_afterOldNewCount_adminRegistry :
    Attainable officialParams .afterOldNewCount .adminRegistry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path afterOldNewCount_index_pin found pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_afterOldNewCount h hstor hmem)

/-! ## The expiry row on `registerAfterSet`'s fresh arm

Source function 19, three `.call`s past `appendTarget`.  Four more branches,
three of them memory-valued and settled by the three windows the route already
carries: `finishSetPauser`'s continuation test reads the zero at
`continuationWord`, `registerAfterSet`'s first test reads the zero at
`previousPauserWord`, and its second reads the new pauser again.  The fourth is
`checkedHeartbeatExpiry`'s overflow test, whose sibling is
`Func.revData (Panic(0x11))` and therefore free.

Role pinning is free again, and for the same reason as `afterOld.newCount`:
every `register.*` row permits `.adminExpiry` alone.

**Which row this is.**  `Attainable` pins a row through
`RuntimePersistentWrite.sourceSite?`, which is `RuntimePersistentWrite.index`
into the *structural* inventory, and the structural order of
`registerAfterSet`'s four expiry writes is measured, not assumed:
`Func.sourceSites` visits the fall-through arm first, and
`registerAfterSet`'s fall-through arm is the `previousCountKey` block.  So the
inventory positions are

* index 14 — 31 steps, `previousPauser ≠ 0` and old count retained;
* index 15 — 16 steps, the old pauser's expiry cleared;
* index 16 — 46 steps, the new pauser's expiry after that clear;
* index 17 — 24 steps, `previousPauser = 0`: the **fresh** registration.

The fresh registration world takes the jumped arm at the first test, so the row
it reaches is index 17, whose constructor is named
`.registerRetainedOldNewExpiry`.  The constructor names at 14 and 17 are
transposed relative to this order; that is `Blanc/LidoCircuitBreakerSites.lean`'s
`RuntimePersistentWrite.all` to answer for, and nothing here depends on the
names.  `.registerFreshExpiry` — index 14 — is *not* attainable at this world
at all: its site sits behind `previousPauser ≠ 0`, which this registration is
not. -/

set_option maxRecDepth 100000 in
/-- `arithmeticPanic` is `Func.revData` of a `Panic(0x11)` payload, so
`checkedHeartbeatExpiry`'s overflow arm is certified-reverting and its branch
costs no word.

`by rfl` -- what the other six reverting siblings on this route use -- does
*not* close this one, and the reason is worth recording: `Func.revData`'s node
count is computed from its payload, so the certificate cannot reduce until
`signatureHash "Panic"` does, and the elaborator's `whnf` does not get there.
The kernel does, so this is the one certificate that needs `decide +kernel`.
`Func.revSelector`, which the other reverters use, has a fixed shape and never
looks at its payload. -/
private theorem arithmeticPanic_revertsWithin :
    Func.alwaysRevertsWithin 16
      ((runtime officialParams).main :: (runtime officialParams).aux)
      (Func.call arithmeticPanicSlot) = true := by decide +kernel

/-- `finishSetPauser`'s whole prefix: the `PauserSet` event, then the
continuation test.  The `LOG` in the middle is the only instruction on this
route that `line_inv` has no instance for. -/
def finishSetPauserPrefix : Line :=
  loadWord newPauserWord ++ loadWord previousPauserWord ++
    loadWord targetWord ++ [Ninst.pushB256 pauserSetEvent] ++ logWith 3 0 0 ++
    memoryZeroCheck continuationWord

theorem MemWordAt.acrossFinishPrefix {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a finishSetPauserPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold finishSetPauserPrefix at run
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append [Ninst.pushB256 pauserSetEvent] run with ⟨_s4, r4, run⟩
  rcases of_run_append (logWith 3 0 0) run with ⟨_s5, r5, run⟩
  exact (((((window.acrossLoadWord r1).acrossLoadWord r2).acrossLoadWord
    r3).acrossLine (by line_inv) r4).acrossLogWith r5).acrossMemoryZeroCheck run

theorem KernelWindows.acrossFinishPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a finishSetPauserPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossFinishPrefix run, windows.1.2.acrossFinishPrefix run⟩,
    windows.2.acrossFinishPrefix run⟩

/-- `finishSetPauser`'s branch word at the fresh registration world: the
staging line wrote a zero continuation, so the walk returns to
`registerAfterSet` rather than to `pauseAfterSet`. -/
theorem freshWorld_continuationRegister {devm devm' : Devm}
    (window : MemWordAt devm (continuationWord * 32).toNat 0)
    (run : Line.Run freshWorldSevm devm finishSetPauserPrefix devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w ≠ 0 := by
  unfold finishSetPauserPrefix at run
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append [Ninst.pushB256 pauserSetEvent] run with ⟨_s4, r4, run⟩
  rcases of_run_append (logWith 3 0 0) run with ⟨_s5, r5, run⟩
  have window5 := ((((window.acrossLoadWord r1).acrossLoadWord
    r2).acrossLoadWord r3).acrossLine (by line_inv) r4).acrossLogWith r5
  intro w rest hstack
  rw [memoryZeroCheck_word window5 run w rest hstack]
  decide

/-- `registerAfterSet`'s first branch word: the previous pauser is the zero the
kernel staged, so its `iszero` is not zero and the fresh-registration arm
runs. -/
theorem freshWorld_previousPauserAbsent {devm devm' : Devm}
    (window : MemWordAt devm (previousPauserWord * 32).toNat 0)
    (run : Line.Run freshWorldSevm devm (memoryZeroCheck previousPauserWord)
      devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w ≠ 0 := by
  intro w rest hstack
  rw [memoryZeroCheck_word window run w rest hstack]
  decide

/-- `checkedHeartbeatExpiry`'s overflow-checked addition, up to its branch. -/
def checkedExpiryPrefix : Line :=
  [Ninst.timestamp, Ninst.pushB256 heartbeatIntervalSlot, Ninst.sload,
   Ninst.add, Ninst.dup 0, Ninst.timestamp, Ninst.swap 0, Ninst.lt]

/-- From `checkedHeartbeatExpiry`'s fall-through arm to the expiry
`SSTORE`. -/
def registerFreshArmExpiryPrefix : Line :=
  [Ninst.dup 0] ++ mstoreAt 0 ++ loadWord newPauserWord ++ tagTop expiryRegion

/-- Structural source position of the expiry `SSTORE` on `registerAfterSet`'s
fresh arm: inventory index `17`. -/
def registerFreshArmExpiryPath : Prog.SourcePath :=
  ⟨registerAfterSetSlot,
    List.replicate 3 .rest ++ [.branchRight] ++ List.replicate 3 .rest ++
      [.branchLeft] ++ List.replicate 8 .rest ++ [.branchLeft] ++
      List.replicate 7 .rest⟩

set_option maxRecDepth 16384 in
/-- The complete route from program entry to the `register.freshExpiry`
`SSTORE`: seventeen branches, of which exactly four are paid for — the
dispatcher's six selector comparisons are decided on the calldata selector,
seven more have certified-reverting siblings, and the remaining four read the
three staged memory words. -/
theorem runtimeMain_routeTo_registerFreshArmExpiry {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h registerFreshArmExpiryPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_afterOldCall h hstor hmem
    (fun _current _devm' windows callTail => ?_)
  refine routeTo_call callTail (by rfl)
    (fun _afterStart afterBurn afterBody => ?_)
  refine afterOldPauser_routeTo_newCountArm afterBody
    (KernelWindows.of_memory_eq afterBurn.memory.symm windows)
    (fun _devm'' windows'' arm => ?_)
  refine routeTo_line afterOldNewCountPrefix arm (fun _s1 r1 countWrite => ?_)
  refine routeTo_line [Ninst.sstore] countWrite (fun _s2 r2 finishCall => ?_)
  refine routeTo_call finishCall (by rfl) (fun _fStart fBurn fBody => ?_)
  have w0 := KernelWindows.of_memory_eq fBurn.memory.symm
    ((windows''.acrossNewCountPrefix r1).acrossLine (by line_inv) r2)
  refine routeTo_line finishSetPauserPrefix fBody (fun _s3 r3 tail3 => ?_)
  refine routeTo_branchRight_frame tail3
    (freshWorld_continuationRegister w0.1.2 r3)
    (fun _s4 _w4 hpop4 registerCall => ?_)
  have w1 := KernelWindows.of_memory_eq hpop4.memory.symm
    (w0.acrossFinishPrefix r3)
  refine routeTo_call registerCall (by rfl) (fun _rStart rBurn rBody => ?_)
  have w2 := KernelWindows.of_memory_eq rBurn.memory.symm w1
  refine routeTo_line (memoryZeroCheck previousPauserWord) rBody
    (fun _s5 r5 tail5 => ?_)
  refine routeTo_branchRight_frame tail5
    (freshWorld_previousPauserAbsent w2.2 r5)
    (fun _s6 _w6 hpop6 arm6 => ?_)
  have w3 := KernelWindows.of_memory_eq hpop6.memory.symm
    (w2.acrossMemoryZeroCheck r5)
  refine routeTo_line (memoryZeroCheck newPauserWord) arm6
    (fun _s7 r7 tail7 => ?_)
  refine routeTo_branchLeft tail7 (freshWorld_newPauserNonzero w3.1.1 r7)
    (fun _s8 arm8 => ?_)
  refine routeTo_line checkedExpiryPrefix arm8 (fun _s9 _r9 tail9 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail9 (fuel := 16)
    arithmeticPanic_revertsWithin (fun _s10 arm10 => ?_)
  refine routeTo_line registerFreshArmExpiryPrefix arm10
    (fun _s11 _r11 write => ?_)
  have pathEq :
      ((((((([] ++ List.replicate (memoryZeroCheck previousPauserWord).length
                    Prog.SourceStep.rest) ++ [Prog.SourceStep.branchRight]) ++
                List.replicate (memoryZeroCheck newPauserWord).length
                  Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
            List.replicate checkedExpiryPrefix.length Prog.SourceStep.rest) ++
          [Prog.SourceStep.branchLeft]) ++
        List.replicate registerFreshArmExpiryPrefix.length
          Prog.SourceStep.rest) = registerFreshArmExpiryPath.steps := by
    simp [registerFreshArmExpiryPath, memoryZeroCheck, checkedExpiryPrefix,
      registerFreshArmExpiryPrefix, loadWord, mstoreAt, tagTop]
  exact pathEq ▸ routeTo_head write registerFreshArmExpiryPath

set_option maxRecDepth 20000 in
/-- Inventory index `17` is the only one nominating
`registerFreshArmExpiryPath`. -/
theorem registerFreshArmExpiry_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some registerFreshArmExpiryPath) → index = 17 := by
  decide +kernel

/-- The inventory row at index `17` — the expiry write on `registerAfterSet`'s
fresh arm, whose constructor is named `.registerRetainedOldNewExpiry` — is
attained with the `.adminExpiry` role.

Read the section note before reading the constructor's name as a description of
the site: the row is pinned by `sourceSite?`, and this one's site is the
`previousPauser = 0` write. -/
theorem attainable_registerRetainedOldNewExpiry_adminExpiry :
    Attainable officialParams .registerRetainedOldNewExpiry .adminExpiry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path registerFreshArmExpiry_index_pin found
        pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_registerFreshArmExpiry h hstor hmem)

end Blanc.LidoCircuitBreaker
