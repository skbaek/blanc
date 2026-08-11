import Blanc.Weth10AllowanceArms
import Blanc.Weth10AllowanceCompleteness
import Blanc.Weth10AllowanceSweep

/-!
Shared primitives for the allowance-region occurrence obligations.

`Blanc/Weth10AllowanceCompleteness.lean` states two obligations —
`CompiledAllowanceSstoreReverseComplete` and
`CompiledAllowanceSloadReverseComplete` — whose per-selector arms would
otherwise each be walked twice, once per storage instruction.  Nothing in a
discard step depends on which instruction was executed: the contradiction is
that the *stack top* at that source position is provably outside the tagged
allowance region, and both occurrence relations put the executed key there.
So this module states the discard boundary once, over
`Exec.Frame.AllowanceKeyAccess`, the common weakening of both relations, and
both obligations consume it.

Three groups:

* the common weakening and the generic discard boundary, which relocate an
  occurrence past a storage instruction whose key is discarded;
* the `¬ InRegion .allowance` feeders, one per key shape a WETH10 body
  actually stores to or loads from;
* the allowance-key memory walk, factored out of `approve_effect`, where it
  was inline and unavailable to the other four `allowanceKeyFromMemory`
  sites.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## The common weakening

An `SSTORE` occurrence records `key :: value :: tail <<+ stepPre.stack` and an
`SLOAD` occurrence records `key :: tail <<+ stepPre.stack` together with a
post-stack prefix.  Both therefore carry "the executed key is the pre-stack
top", which is all a discard step uses — in particular the read side's
post-stack prefix is never needed to discard, so no head/tail lemma for the
post-side has to exist. -/

/-- The part of an allowance-region storage access that a discard step uses:
the access is an actual proof-indexed occurrence, its executed key is in the
tagged allowance region, and that key is the instruction's pre-stack top. -/
def Exec.Frame.AllowanceKeyAccess
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (n : Ninst) (stepPre stepPost : Devm) (slot : Xlot)
    (key : B256) : Prop :=
  frame.NinstOccurrence dp ca n stepPre stepPost slot ∧
    InRegion .allowance key ∧
    ∃ tail : Stack, key :: tail <<+ stepPre.stack

/-- The write side weakens to the common form; the stored word joins the
retained stack tail. -/
theorem Exec.Frame.AllowanceSstoreOccurrence.toKeyAccess
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot} {key value : B256}
    (occurrence : frame.AllowanceSstoreOccurrence dp ca stepPre stepPost slot
      key value) :
    frame.AllowanceKeyAccess dp ca (.reg .sstore) stepPre stepPost slot
      key := by
  rcases occurrence with ⟨actual, region, tail, stackPrefix⟩
  exact ⟨actual, region, value :: tail, stackPrefix⟩

/-- The read side weakens to the common form; the pushed word's post-stack
prefix is simply dropped. -/
theorem Exec.Frame.AllowanceSloadOccurrence.toKeyAccess
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot} {key value : B256}
    (occurrence : frame.AllowanceSloadOccurrence dp ca stepPre stepPost slot
      key value) :
    frame.AllowanceKeyAccess dp ca (.reg .sload) stepPre stepPost slot
      key := by
  rcases occurrence with ⟨actual, region, tail, prePrefix, _postPrefix⟩
  exact ⟨actual, region, tail, prePrefix⟩

/-! ## The discard boundary -/

/-- Skip an actually executed source head whose immediate stack top is proved
outside the tagged allowance region.  This is the region-phrased dual of
`Exec.Frame.CompiledCursor.balanceSstoreOccurrence_after_invalidKeyStore`, and
the reusable boundary for every allowance discard site.

Three deliberate generalizations over the balance twin: the swept instruction
is arbitrary, so one lemma serves the write and the read obligation; the
source head is arbitrary, so the lemma applies at any position whose stack top
is known, not only at an `SSTORE`; and no stored-value inequality is assumed,
so no-op stores are covered as well. -/
theorem Exec.Frame.CompiledCursor.allowanceKeyAccess_after_discardedKey
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {source : Ninst} {tail : Func} {final stepPre stepPost : Devm}
    {n : Ninst} {slot : Xlot} {key headKey : B256} {stack : Stack}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.next source tail) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor n
      stepPre stepPost slot)
    (access : frame.AllowanceKeyAccess dp ca n stepPre stepPost slot key)
    (discard : ¬ InRegion .allowance headKey)
    (headPrefix : headKey :: stack <<+ cursor.pre.stack) :
    ∃ tailCursor : frame.CompiledCursor dp ca fs sourceTable tail final,
      frame.NinstOccurrenceFromCursor tailCursor n stepPre stepPost slot := by
  rcases cursor.ninstOccurrenceFromCursor_head_or_tail fromCursor with
    ⟨_sourceEq, preEq⟩ |
      ⟨tailCursor, _sourceSlot, _sourceOccurrence, insideTail⟩
  · subst preEq
    rcases access.2.2 with ⟨accessTail, accessPrefix⟩
    have keyEq : key = headKey :=
      pref_head_unique
        (pref_trans (pref_append [key] accessTail) accessPrefix)
        (pref_trans (pref_append [headKey] stack) headPrefix)
    exact (discard (keyEq ▸ access.2.1)).elim
  · exact ⟨tailCursor, insideTail⟩

/-! ## Region feeders

One named lemma per key shape a WETH10 body actually stores to or loads from.
All but the nonce shape are immediate corollaries of the region projections in
`Blanc/Weth10Core.lean`. -/

/-- An address-shaped key is never in the tagged allowance region. -/
theorem not_allowanceRegion_of_validAdr {key : B256} (valid : ValidAdr key) :
    ¬ InRegion .allowance key := fun region =>
  allowanceRegion_not_valid region valid

/-- The shape every `addressArg` site leaves on the stack: clearing the high
96 bits always lands in the balance region, dirty ABI words included. -/
theorem not_allowanceRegion_normalizedAddress (w : B256) :
    ¬ InRegion .allowance ((~~~ addressMask) &&& w) :=
  not_allowanceRegion_of_validAdr (normalizedAddress_valid w)

/-- The shape a `CALLER` or `ADDRESS` balance key has. -/
theorem not_allowanceRegion_toB256 (a : Adr) :
    ¬ InRegion .allowance a.toB256 :=
  not_allowanceRegion_of_validAdr ⟨a, rfl⟩

/-- The flash counter slot is never in the tagged allowance region. -/
theorem not_allowanceRegion_flashMintedSlot :
    ¬ InRegion .allowance flashMintedSlot := fun region =>
  allowanceRegion_ne_flashSlot region rfl

/-- A nonce-tagged word is never in the tagged allowance region, whatever word
was tagged.  Deliberately stated for an arbitrary `w` rather than for a
normalized address: the `nonces` view tags the *raw* first argument word, so
no address-shape premise is available at that site.  Bit 254 is set by the
tag, and an allowance-region key has it clear. -/
theorem not_allowanceRegion_nonceTagged (w : B256) :
    ¬ InRegion .allowance (nonceTagWord ||| w) := by
  intro region
  have htag : nonceTagWord.1.1 = (0x4000000000000000 : UInt64) := by
    decide +kernel
  have expanded : (0xc000000000000000 : UInt64) &&&
      ((0x4000000000000000 : UInt64) ||| w.1.1) =
      (0x8000000000000000 : UInt64) := by
    have step : keyTag (nonceTagWord ||| w) = regionTag .allowance := region
    unfold keyTag regionTag at step
    change (0xc000000000000000 : UInt64) &&&
      (nonceTagWord.1.1 ||| w.1.1) = (0x8000000000000000 : UInt64) at step
    rwa [htag] at step
  have bit := congrArg (fun u : UInt64 => u.toBitVec.getLsbD 62) expanded
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, BitVec.getLsbD_and,
    BitVec.getLsbD_or] at bit
  simp at bit

/-! ## The allowance-key memory walk

`allowanceKeyFromMemory` is the program's only producer of allowance-region
keys.  Its five sites differ only in how memory words 0 and 1 get filled, so
the composition of `slice_two_words` with
`prefix_of_allowanceKeyFromMemory_image` is the step they all share; it is
stated once here.  The per-site prelude that writes the two words is *not*
shared — see the module note in the report. -/

/-- The exact tagged key `allowanceKeyFromMemory` computes from a readable
memory image whose first two words are `first` and `second`.  This is the
shared half of every allowance-key site's walk. -/
theorem prefix_of_allowanceKeyFromMemory_twoWords
    {e : Sevm} {xs : Stack} {s s' : Devm} {img : Bytes}
    {first : B256} {second : Bytes}
    (hlen : second.length = 32)
    (hp : xs <<+ s.stack)
    (hwf : Mem.Wf s.memory)
    (hreads : Mem.Reads s.memory
      (Bytes.writeAt (Bytes.writeAt img 0 first.toBytes) 32 second))
    (run : Line.Run e s allowanceKeyFromMemory s') :
    (allowanceTagWord |||
        (allowancePayloadMask &&& Bytes.keccak (first.toBytes ++ second))) ::
      xs <<+ s'.stack ∧
      Mem.Wf s'.memory ∧
      Mem.Reads s'.memory
        (Bytes.writeAt (Bytes.writeAt img 0 first.toBytes) 32 second) := by
  rcases prefix_of_allowanceKeyFromMemory_image hp hwf hreads run with
    ⟨stackPrefix, wf, reads⟩
  rw [slice_two_words img first second hlen] at stackPrefix
  exact ⟨stackPrefix, wf, reads⟩

/-- Any key `allowanceKeyFromMemory` produces is in the tagged allowance
region; the positive companion of the feeders above. -/
theorem allowanceKeyFromMemory_region (h : B256) :
    InRegion .allowance
      (allowanceTagWord ||| (allowancePayloadMask &&& h)) :=
  runtimeAllowanceKey_region h

/-- The shared `approve`/`approveAndCall` key entry: write the caller word at
memory word 0, then copy the raw spender argument word to memory word 1. -/
def approveKeyEntry : Line :=
  [Ninst.caller] ++ mstoreAt 0 ++ argCopy 1 0 1

/-- The exact key the shared `approve` entry leaves on the stack.  This is the
prefix walk inlined in `approve_effect`, factored so that every body opening
with `approvePrefix` — `approve` and `approveAndCall` — consumes it instead of
transcribing it. -/
theorem prefix_of_approveKeyEntry
    {e : Sevm} {xs : Stack} {s s' : Devm} {img : Bytes}
    (hp : xs <<+ s.stack)
    (hwf : Mem.Wf s.memory)
    (hreads : Mem.Reads s.memory img)
    (run : Line.Run e s (approveKeyEntry ++ allowanceKeyFromMemory) s') :
    approveRuntimeKey e :: xs <<+ s'.stack := by
  unfold approveKeyEntry at run
  rcases of_run_append ([Ninst.caller] ++ mstoreAt 0 ++ argCopy 1 0 1) run
    with ⟨afterEntry, entryRun, keyRun⟩
  rcases of_run_append ([Ninst.caller] ++ mstoreAt 0) entryRun with
    ⟨afterStore, storeRun, copyRun⟩
  rcases of_run_append [Ninst.caller] storeRun with
    ⟨afterCaller, callerRun, mstoreRun⟩
  rcases Line.of_run_cons callerRun with ⟨callerState, callerStep, callerNil⟩
  cases callerNil
  have callerPush := of_run_caller callerStep
  have hpCaller : e.caller.toB256 :: xs <<+ afterCaller.stack :=
    prefix_of_push callerPush hp
  have memCaller : s.memory = afterCaller.memory := callerPush.memory
  rcases of_run_mstoreAt_val mstoreRun hpCaller with ⟨hpStore, memStore⟩
  rw [show ((0 : B256) * 32).toNat = 0 from rfl] at memStore
  have wfStore : Mem.Wf afterStore.memory := by
    rw [memStore, ← memCaller]
    exact hwf.write _ _
  have readsStore :
      Mem.Reads afterStore.memory
        (Bytes.writeAt img 0 e.caller.toB256.toBytes) := by
    rw [memStore, ← memCaller]
    exact Mem.Reads.write hwf hreads 0 _
  rcases of_run_argCopy101 hpStore copyRun with ⟨hpCopy, memCopy⟩
  have wfCopy : Mem.Wf afterEntry.memory := by
    rw [memCopy]
    exact wfStore.write _ _
  have readsCopy :
      Mem.Reads afterEntry.memory
        (Bytes.writeAt (Bytes.writeAt img 0 e.caller.toB256.toBytes) 32
          (e.data.sliceD 4 32 0)) := by
    rw [memCopy]
    exact Mem.Reads.write wfStore readsStore 32 _
  have hlen : (e.data.sliceD 4 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  rcases prefix_of_allowanceKeyFromMemory_twoWords hlen hpCopy wfCopy
      readsCopy keyRun with ⟨keyPrefix, _wf, _reads⟩
  exact keyPrefix

/-- The `approve` runtime key is in the tagged allowance region. -/
theorem approveRuntimeKey_region (e : Sevm) :
    InRegion .allowance (approveRuntimeKey e) :=
  runtimeAllowanceKey_region _

/-! ## Dispatcher transport

An allowance key is a `keccak` of memory, so an arm must relate the memory at
its body cursor to the frame's entry memory.  The dispatch spine reports
`Devm.DispatchSilent`; these two lines are how an arm spends it. -/

/-- Memory well-formedness survives the generated dispatcher. -/
theorem Devm.DispatchSilent.wf {pre post : Devm}
    (silent : Devm.DispatchSilent pre post) (hwf : Mem.Wf pre.memory) :
    Mem.Wf post.memory := silent.memory ▸ hwf

/-- A readable memory image survives the generated dispatcher. -/
theorem Devm.DispatchSilent.reads {pre post : Devm} {img : Bytes}
    (silent : Devm.DispatchSilent pre post)
    (hreads : Mem.Reads pre.memory img) :
    Mem.Reads post.memory img := silent.memory ▸ hreads

end Weth10

end Blanc
