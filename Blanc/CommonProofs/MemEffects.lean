-- CommonProofs/MemEffects.lean : memory effects of written instructions, scratch-word images and transfer log frames.

import Blanc.CommonProofs.Hinv

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

/-! ### What memory a written instruction writes

The `Hinv Devm.memory` instance family that carries a memory image across a
memory-silent `Line` sits earlier in this file, beside its `Devm.state` /
`Devm.getStor` / `Devm.getCode` siblings — dispatch reachability needs it too,
and instance resolution is position-sensitive within a module.  What follows is
the other half: value-carrying inversions for the three instructions that do
touch memory, in the same shape Step 1 gave `calldataload` and `calldatacopy` —
what was written, and where. -/

/-- A successful `MSTORE8` changes only the machine-local frame, not the
persistent world state. -/
lemma of_run_mstore8_state {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s mstore8 s') : s.state = s'.state := by
  rcases of_run_reg h with ⟨pc, run⟩
  have frame := Rinst.run_instructionFrame pc e s .mstore8
    (by intro equal; cases equal) (by intro equal; cases equal)
  rw [run] at frame
  exact frame.state

/-- `CALLDATACOPY` writes *the calldata slice named by its operands* at *the
offset it popped*, and touches nothing else.

Strengthens `of_run_calldatacopy_val` (Step 1), which named the bytes but could
not relate the intermediate state's memory to the initial one — there was no
`Mem` algebra to say it in. -/
lemma of_run_calldatacopy_mem {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s calldatacopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack ∧
      s'.memory = s.memory.write x.toNat (e.data.sliceD y.toNat z.toNat 0) := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  have hmem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  refine ⟨x, y, z, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
    rw [← eq, show (Devm.memWrite s₄ x.toNat _).stack = s₄.stack from rfl, ← hb.stack]
    exact hp
  · rw [← eq, hmem]
    rfl

/-- `CODECOPY` is log-silent.  Like `MLOAD`, it has no global `Ninst.Hinv`
instance for logs, so constructor-return proofs use this exact successful-run
fact instead of assuming a broader instruction class. -/
lemma of_run_codecopy_logs {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s codecopy s') : s.logs = s'.logs := by
  rcases of_run_reg h with ⟨_, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨_, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨_, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨_, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat h1 with ⟨_, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨_, p2⟩
  rcases Devm.pop_of_popToNat h3 with ⟨_, p3⟩
  have burned := Devm.burn_of_chargeGas h4
  injection h5 with stateEq
  rw [← stateEq]
  exact ((p1.logs.trans p2.logs).trans p3.logs).trans burned.logs

/-- Value-carrying memory companion for `LOG`.  The popped offset/size and
topics are shared with the stack relation, so fixed-shape fragments can pin the
exact memory extension without reopening `Rinst.runCore`. -/
lemma of_run_log_mem_val {e : Sevm} {s s' : Devm} {n : Fin 5}
    (h : Ninst.Run e s (log n) s') :
    ∃ mi sz topics,
      topics.length = n.val ∧
      Stack.Pop (mi :: sz :: topics) s.stack s'.stack ∧
      s'.memory = s.memory.extend mi.toNat sz.toNat := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popN h3 with ⟨hlen, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases hmem : Devm.memRead s₄ x.toNat y.toNat with ⟨data, s₅⟩
  rw [hmem] at run₅
  injection run₅ with eq
  have hpre : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  have hstack : s₅.stack = s₄.stack := by
    have hs := Devm.memRead_stack s₄ x.toNat y.toNat
    rw [hmem] at hs
    exact hs
  have hmemory : s₅.memory = s₄.memory.extend x.toNat y.toNat := by
    simp only [Devm.memRead] at hmem
    rcases hread : s₄.memory.read x.toNat y.toNat with ⟨val, mem⟩
    rw [hread] at hmem
    injection hmem with _ hdevm
    rw [← hdevm]
    show mem = _
    have hm : mem = (s₄.memory.read x.toNat y.toNat).2 := by rw [hread]
    rw [hm]
    rfl
  refine ⟨x, y, topics, hlen, ?_, ?_⟩
  · rw [← eq]
    show Stack.Pop (x :: y :: topics) s.stack s₅.stack
    rw [hstack, ← hb.stack]
    exact (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  · rw [← eq]
    show s₅.memory = _
    rw [hmemory, hpre]

/-- `MSTORE8` at a known stack top, retaining the exact low-byte write. -/
lemma prefix_of_mstore8_val {e} {x y xs} {s s' : Devm}
    (h0 : Ninst.Run e s mstore8 s')
    (h1 : x :: y :: xs <<+ s.stack) :
    xs <<+ s'.stack ∧
      s'.memory = s.memory.write x.toNat [y.2.2.toUInt8] := by
  rcases of_run_mstore8_val h0 with ⟨x', y', h2, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, -⟩
  refine ⟨?_, by rw [hx, hy]; exact hm⟩
  rw [hx, hy] at h1
  exact of_append_pref h2 h1

/-- Every successful `mstoreAt` run begins with the word it consumes at the
head of the input stack. -/
theorem mstoreAt_stack_head
    {e : Sevm} {pre post : Devm} {k : B256}
    (run : Line.Run e pre (mstoreAt k) post) :
    ∃ word tail, word :: tail <<+ pre.stack := by
  unfold mstoreAt at run
  rcases Line.of_run_cons run with ⟨afterPush, hpush, run⟩
  rcases Line.of_run_cons run with ⟨afterStore, hstore, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 hpush
  rcases of_run_mstore hstore with ⟨offset, word, hpop⟩
  have hstack : (k * 32) :: pre.stack =
      offset :: word :: post.stack :=
    pushed.stack.symm.trans hpop
  injection hstack with hoff htail
  refine ⟨word, post.stack, ?_⟩
  rw [htail]
  simpa only [append_nil] using (pref_append (word :: post.stack) [])

/-- A fixed-word `MSTORE` step with the proof-carrying memory image advanced
in lockstep.  This is the shared scratch-decoder wrapper around
`of_run_mstoreAt_val`, `Mem.Wf.write`, and `Mem.Reads.write`. -/
theorem of_run_mstoreAt_image
    {e : Sevm} {pre post : Devm} {word value : B256}
    {tail : Stack} {image : Bytes}
    (hp : value :: tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (run : Line.Run e pre (mstoreAt word) post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (Bytes.writeAt image (word * 32).toNat value.toBytes) ∧
      pre.state = post.state := by
  obtain ⟨stack, memory⟩ := of_run_mstoreAt_val run hp
  refine ⟨stack, ?_, ?_, Line.of_inv Devm.state (by line_inv) run⟩
  · rw [memory]
    exact hwf.write _ _
  · rw [memory]
    exact Mem.Reads.write hwf hreads _ _

/-- `CALLDATACOPY` at a *known* stack top: the value-carrying companion of
`prefix_of_calldatacopy`, with the three popped operands pinned to the words the
walk already knows are there. -/
lemma prefix_of_calldatacopy_val {e} {x y z xs} {s s' : Devm}
    (h0 : Ninst.Run e s calldatacopy s') (h1 : x :: y :: z :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧
      s'.memory = s.memory.write x.toNat (e.data.sliceD y.toNat z.toNat 0) := by
  rcases of_run_calldatacopy_mem h0 with ⟨x', y', z', h2, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, -⟩
  refine ⟨?_, by rw [hx, hy, hz]; exact hm⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

/-- `CODECOPY` at a known stack top, retaining the exact written code slice. -/
lemma prefix_of_codecopy_val {e} {x y z xs} {s s' : Devm}
    (h0 : Ninst.Run e s codecopy s') (h1 : x :: y :: z :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧
      s'.memory = s.memory.write x.toNat
        (e.code.sliceD y.toNat z.toNat (Linst.toUInt8 .stop)) := by
  rcases of_run_codecopy_mem h0 with ⟨x', y', z', h2, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, -⟩
  refine ⟨?_, by rw [hx, hy, hz]; exact hm⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

/-- Exact proof-carrying image update for a successful `CODECOPY`.  Besides the
three-word stack burn, this retains memory well-formedness, the updated image,
and the persistent-state/log frame needed to compose constructor decoders. -/
theorem of_run_codecopy_image
    {e : Sevm} {pre post : Devm} {dst src size : B256}
    {tail : Stack} {image : Bytes}
    (hp : dst :: src :: size :: tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (run : Ninst.Run e pre codecopy post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (Bytes.writeAt image dst.toNat
          (e.code.sliceD src.toNat size.toNat (Linst.toUInt8 .stop))) ∧
      pre.state = post.state ∧
      pre.logs = post.logs := by
  obtain ⟨pstack, memory⟩ := prefix_of_codecopy_val run hp
  refine ⟨pstack, ?_, ?_, Ninst.Hinv.inv run, of_run_codecopy_logs run⟩
  · rw [memory]
    exact Mem.Wf.write hwf _ _
  · rw [memory]
    exact Mem.Reads.write hwf hreads _ _

/-- **What `forwardArgTail` does**, both effects at once: it leaves argument
`k`'s declared tail length on the stack, writes that length into memory word
`lenWord`, and copies the payload into the word after it.

Every word named in the conclusion is a function of `e.data` alone
(`Sevm.tailLen`, `Sevm.tailBytes`), so this is a description of the fragment
rather than a restatement of its instructions — the discipline the arc's fixed
decision 2 requires of anything the callback's calldata image is built from.

No zero padding appears here: `forwardArgTail` writes the payload and nothing
above it, and a caller wanting a reference encoder's padding gets it from the
region above being untouched (see `forwardArgTail`'s own note and `Mem.Reads`). -/
lemma of_forwardArgTail_val {e : Sevm} {s s' : Devm} {k lenWord xs}
    (hp : xs <<+ s.stack) (h : Line.Run e s (forwardArgTail k lenWord) s') :
    (Sevm.tailLen e k :: xs <<+ s'.stack) ∧
      s'.memory =
        (s.memory.write (lenWord * 32).toNat (Sevm.tailLen e k).toBytes).write
          ((lenWord + 1) * 32).toNat (Sevm.tailBytes e k) := by
  -- The code computes `4 + off` while `Sevm.tailPtr` is written `off + 4`, and
  -- likewise `32 + p` against `Sevm.tailBytes`'s `tailPtr + 32`.  `B256` carries
  -- its own `HAdd`, so the commutations are `B256.add_comm`, not `add_comm`.
  have hptr : (4 : B256) + Sevm.argWord e k = Sevm.tailPtr e k := by
    rw [Sevm.tailPtr, B256.add_comm]
  have hoff : (32 : B256) + Sevm.tailPtr e k = Sevm.tailPtr e k + 32 := B256.add_comm
  simp only [forwardArgTail] at h
  -- `arg k`: the head word, which for a dynamic argument is an offset.
  rcases of_run_append (arg k) h with ⟨t1, q1, h⟩
  have hp1 : Sevm.argWord e k :: xs <<+ t1.stack := prefix_of_arg hp q1
  have hm1 : s.memory = t1.memory := Line.of_inv Devm.memory (by line_inv) q1
  -- `pushB256 4 :: add`: the absolute calldata index of the length word.
  rcases Line.of_run_cons h with ⟨t2, q2, h⟩
  have hb2 := of_run_pushB256 q2
  have hp2 : (4 : B256) :: Sevm.argWord e k :: xs <<+ t2.stack :=
    prefix_of_push hb2 hp1
  rcases Line.of_run_cons h with ⟨t3, q3, h⟩
  have hp3 : Sevm.tailPtr e k :: xs <<+ t3.stack := by
    rw [← hptr]; exact prefix_of_add q3 hp2
  have hm3 : s.memory = t3.memory :=
    (hm1.trans hb2.memory).trans (Ninst.Hinv.inv (f := Devm.memory) q3)
  -- `dup 0 :: calldataload`: read the declared length, keeping the pointer.
  rcases Line.of_run_cons h with ⟨t4, q4, h⟩
  have hp4 : Sevm.tailPtr e k :: Sevm.tailPtr e k :: xs <<+ t4.stack :=
    prefix_of_dup_val q4 (Stack.Nth.head _ _) hp3
  have hm4 : s.memory = t4.memory := hm3.trans (Ninst.Hinv.inv (f := Devm.memory) q4)
  rcases Line.of_run_cons h with ⟨t5, q5, h⟩
  have hp5 : Sevm.tailLen e k :: Sevm.tailPtr e k :: xs <<+ t5.stack :=
    prefix_of_calldataload_val q5 hp4
  have hm5 : s.memory = t5.memory :=
    hm4.trans (Ninst.Hinv.inv (f := Devm.memory) q5)
  -- `dup 0 :: mstoreAt lenWord`: republish the length into memory.
  rcases Line.of_run_cons h with ⟨t6, q6, h⟩
  have hp6 : Sevm.tailLen e k :: Sevm.tailLen e k :: Sevm.tailPtr e k :: xs <<+ t6.stack :=
    prefix_of_dup_val q6 (Stack.Nth.head _ _) hp5
  have hm6 : s.memory = t6.memory := hm5.trans (Ninst.Hinv.inv (f := Devm.memory) q6)
  rcases of_run_append (mstoreAt lenWord) h with ⟨t7, q7, h⟩
  rcases of_run_mstoreAt_val q7 hp6 with ⟨hp7, hmw7⟩
  have hm7 : t7.memory =
      s.memory.write (lenWord * 32).toNat (Sevm.tailLen e k).toBytes := by
    rw [hmw7, hm6]
  -- `dup 0 :: swap 1`: the payload's source pointer back on top.
  rcases Line.of_run_cons h with ⟨t8, q8, h⟩
  have hp8 : Sevm.tailLen e k :: Sevm.tailLen e k :: Sevm.tailPtr e k :: xs <<+ t8.stack :=
    prefix_of_dup_val q8 (Stack.Nth.head _ _) hp7
  have hm8 := (Ninst.Hinv.inv (f := Devm.memory) q8).symm.trans hm7
  rcases Line.of_run_cons h with ⟨t9, q9, h⟩
  have hp9 : Sevm.tailPtr e k :: Sevm.tailLen e k :: Sevm.tailLen e k :: xs
      <<+ t9.stack := by
    have h_swap : Stack.Swap (1 : Fin 16).val
        (Sevm.tailLen e k :: Sevm.tailLen e k :: Sevm.tailPtr e k :: xs)
        (Sevm.tailPtr e k :: Sevm.tailLen e k :: Sevm.tailLen e k :: xs) := by
      apply Stack.swapCore_succ
      apply Stack.swapCore_zero
    exact Stack.prefix_of_swap h_swap (of_run_swap q9) hp8
  have hm9 := (Ninst.Hinv.inv (f := Devm.memory) q9).symm.trans hm8
  -- `pushB256 32 :: add`: the payload begins one word past the length word.
  rcases Line.of_run_cons h with ⟨t10, q10, h⟩
  have hb10 := of_run_pushB256 q10
  have hp10 : (32 : B256) :: Sevm.tailPtr e k :: Sevm.tailLen e k ::
      Sevm.tailLen e k :: xs <<+ t10.stack := prefix_of_push hb10 hp9
  have hm10 := hb10.memory.symm.trans hm9
  rcases Line.of_run_cons h with ⟨t11, q11, h⟩
  have hp11 : (32 + Sevm.tailPtr e k) :: Sevm.tailLen e k :: Sevm.tailLen e k ::
      xs <<+ t11.stack := prefix_of_add q11 hp10
  have hm11 := (Ninst.Hinv.inv (f := Devm.memory) q11).symm.trans hm10
  rcases Line.of_run_cons h with ⟨t12, q12, h⟩
  have hb12 := of_run_pushB256 q12
  have hp12 : ((lenWord + 1) * 32 : B256) :: (32 + Sevm.tailPtr e k) ::
      Sevm.tailLen e k :: Sevm.tailLen e k :: xs <<+ t12.stack :=
    prefix_of_push hb12 hp11
  have hm12 := hb12.memory.symm.trans hm11
  -- `calldatacopy`: the payload itself.
  rcases Line.of_run_cons h with ⟨t13, q13, hnil⟩
  cases hnil
  rcases prefix_of_calldatacopy_val q13 hp12 with ⟨hps, hmem⟩
  refine ⟨hps, ?_⟩
  rw [hmem, hm12, Sevm.tailBytes, ← hoff]

/-! ### The returndata, value-carried

Arc B consumed `of_returnDataShorterThan` / `of_checkReturnDataHead` to learn that a
flag was pushed; the callback boundary (Step 4 of the flash-loan arc's plan)
needs them to say what the returndata *is*.  The same projection-restoring
move as Step 1's calldata layer, applied to `RETURNDATASIZE`, `RETURNDATACOPY`
and `MLOAD`, then to the two `Line` fragments built from them. -/

/-- Exact stack and log effect of any fixed-shape `logWith` fragment.

The topic list includes the signature topic, hence its length is `k + 1`.
This general form covers data-less one- and two-topic control-plane events as
well as multiword unindexed data windows; specialized ERC-20 helpers remain
available below. -/
lemma of_logWith_val {e : Sevm} {s s' : Devm} {k : Fin 4}
    {x y : B256} {topics : List B256} {xs : Stack}
    (hlen : topics.length = k.val + 1)
    (hp : topics ++ xs <<+ s.stack)
    (h : Line.Run e s (logWith k x y) s') :
    xs <<+ s'.stack ∧
      s'.logs = s.logs ++
        [⟨e.currentTarget, topics,
          (s.memory.read (x * 32).toNat (y * 32).toNat).1⟩] := by
  rcases Line.of_run_cons h with ⟨s₁, hsize, hrest₁⟩
  rcases Line.of_run_cons hrest₁ with ⟨s₂, hoffset, hrest₂⟩
  rcases Line.of_run_cons hrest₂ with ⟨s₃, hlog, hnil⟩
  cases hnil
  have hbsize := of_run_pushB256 hsize
  have hboffset := of_run_pushB256 hoffset
  have hp₁ : (y * 32) :: topics ++ xs <<+ s₁.stack :=
    prefix_of_push (xs := [y * 32]) (ys := topics ++ xs) hbsize hp
  have hp₂ : (x * 32) :: (y * 32) :: topics ++ xs <<+ s₂.stack :=
    prefix_of_push (xs := [x * 32])
      (ys := (y * 32) :: topics ++ xs) hboffset hp₁
  rcases of_run_log_val hlog with
    ⟨mi, sz, actualTopics, hactualLen, hpop, hlogs⟩
  have hknown : ((x * 32) :: (y * 32) :: topics) <<+ s₂.stack := by
    exact @pref_trans _ ((x * 32) :: (y * 32) :: topics)
      (((x * 32) :: (y * 32) :: topics) ++ xs) _
      ⟨xs, rfl⟩ (by simpa only [cons_append] using hp₂)
  have heq : ((x * 32) :: (y * 32) :: topics) =
      mi :: sz :: actualTopics :=
    List.pref_unique (by simp only [length_cons, hlen, hactualLen, Fin.val_succ]) hknown
      (pref_of_split hpop)
  simp only [List.cons.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  constructor
  · exact of_append_pref hpop (by simpa only [cons_append] using hp₂)
  · rw [hlogs, ← hboffset.logs, ← hbsize.logs,
      ← hboffset.memory, ← hbsize.memory]

/-- A fixed-shape `logWith` preserves any proof-carrying memory image and its
well-formedness; its only memory effect is the read-window extension performed
by `LOG`. -/
lemma of_logWith_image {e : Sevm} {s s' : Devm} {k : Fin 4}
    {x y : B256} {image : Bytes}
    (hwf : Mem.Wf s.memory) (hreads : Mem.Reads s.memory image)
    (h : Line.Run e s (logWith k x y) s') :
    Mem.Wf s'.memory ∧ Mem.Reads s'.memory image := by
  rcases Line.of_run_cons h with ⟨s₁, hsize, hrest₁⟩
  rcases Line.of_run_cons hrest₁ with ⟨s₂, hoffset, hrest₂⟩
  rcases Line.of_run_cons hrest₂ with ⟨_, hlog, hnil⟩
  cases hnil
  have hbsize := of_run_pushB256 hsize
  have hboffset := of_run_pushB256 hoffset
  obtain ⟨mi, sz, hmemory⟩ := of_run_log_mem hlog
  constructor
  · rw [hmemory, ← hboffset.memory, ← hbsize.memory]
    exact hwf.extend mi sz
  · rw [hmemory, ← hboffset.memory, ← hbsize.memory]
    exact hreads.extend mi sz

/-- Exact event effect of the canonical three-topic, one-word log fragment.

`logWith 2 0 1` is the common shape of ERC-20 `Transfer` and `Approval`:
topic0 plus two indexed addresses, and one ABI word read from memory `[0, 32)`.
The theorem keeps the existing stack-prefix API while making the appended log
available to public functional proofs. -/
lemma of_logWith201_val {e : Sevm} {s s' : Devm}
    {ev a b : B256} {xs : Stack}
    (hp : ev :: a :: b :: xs <<+ s.stack)
    (h : Line.Run e s (logWith 2 0 1) s') :
    xs <<+ s'.stack ∧
      s'.logs =
        s.logs ++ [⟨e.currentTarget, [ev, a, b], (s.memory.read 0 32).1⟩] := by
  rcases Line.of_run_cons h with ⟨s₁, h32, hrest₁⟩
  rcases Line.of_run_cons hrest₁ with ⟨s₂, h0, hrest₂⟩
  rcases Line.of_run_cons hrest₂ with ⟨s₃, hlog, hnil⟩
  cases hnil
  have hb32 := of_run_pushB256 h32
  have hb0 := of_run_pushB256 h0
  have h32word : (1 * 32 : B256) = 32 := by decide +kernel
  have h0word : (0 * 32 : B256) = 0 := by decide +kernel
  rw [h32word] at hb32
  rw [h0word] at hb0
  have hp₁ : (32 : B256) :: ev :: a :: b :: xs <<+ s₁.stack := by
    simpa only [cons_append, nil_append] using prefix_of_push hb32 hp
  have hp₂ : (0 : B256) :: 32 :: ev :: a :: b :: xs <<+ s₂.stack := by
    simpa only [cons_append, nil_append] using prefix_of_push hb0 hp₁
  rcases of_run_log_val hlog with
    ⟨mi, sz, topics, hlen, hpop, hlogs⟩
  have hknown : ([0, 32, ev, a, b] : List B256) <<+ s₂.stack := by
    exact @pref_trans _ [0, 32, ev, a, b]
      ([0, 32, ev, a, b] ++ xs) _ ⟨xs, rfl⟩ (by simpa only [cons_append, nil_append] using hp₂)
  have heq : ([0, 32, ev, a, b] : List B256) = mi :: sz :: topics :=
    List.pref_unique (by simp only [length_cons, length_nil, zero_add, reduceAdd, hlen, Fin.isValue,
      Fin.reduceSucc, Fin.coe_ofNat_eq_mod, reduceMod]) hknown (pref_of_split hpop)
  simp only [List.cons.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  constructor
  · exact of_append_pref hpop (by simpa only [cons_append, nil_append] using hp₂)
  · rw [hlogs, ← hb0.logs, ← hb32.logs, ← hb0.memory, ← hb32.memory]
    rfl

/-- Exact memory-extension companion for `of_logWith201_val`.

The two setup pushes preserve memory, while `LOG3` reads the single ABI word
at `[0, 32)` and therefore leaves precisely the memory extension performed by
that read.  This is kept separate from the event theorem so existing consumers
of its stable stack/log interface are unaffected. -/
lemma of_logWith201_mem {e : Sevm} {s s' : Devm}
    {ev a b : B256} {xs : Stack}
    (hp : ev :: a :: b :: xs <<+ s.stack)
    (h : Line.Run e s (logWith 2 0 1) s') :
    s'.memory = s.memory.extend 0 32 := by
  rcases Line.of_run_cons h with ⟨s₁, h32, hrest₁⟩
  rcases Line.of_run_cons hrest₁ with ⟨s₂, h0, hrest₂⟩
  rcases Line.of_run_cons hrest₂ with ⟨s₃, hlog, hnil⟩
  cases hnil
  have hb32 := of_run_pushB256 h32
  have hb0 := of_run_pushB256 h0
  have h32word : (1 * 32 : B256) = 32 := by decide +kernel
  have h0word : (0 * 32 : B256) = 0 := by decide +kernel
  rw [h32word] at hb32
  rw [h0word] at hb0
  have hp₁ : (32 : B256) :: ev :: a :: b :: xs <<+ s₁.stack := by
    simpa only [cons_append, nil_append] using prefix_of_push hb32 hp
  have hp₂ : (0 : B256) :: 32 :: ev :: a :: b :: xs <<+ s₂.stack := by
    simpa only [cons_append, nil_append] using prefix_of_push hb0 hp₁
  rcases of_run_log_mem_val hlog with
    ⟨mi, sz, topics, hlen, hpop, hmemory⟩
  have hknown : ([0, 32, ev, a, b] : List B256) <<+ s₂.stack := by
    exact @pref_trans _ [0, 32, ev, a, b]
      ([0, 32, ev, a, b] ++ xs) _ ⟨xs, rfl⟩ (by simpa only [cons_append, nil_append] using hp₂)
  have heq : ([0, 32, ev, a, b] : List B256) = mi :: sz :: topics :=
    List.pref_unique (by simp only [length_cons, length_nil, zero_add, reduceAdd, hlen, Fin.isValue,
      Fin.reduceSucc, Fin.coe_ofNat_eq_mod, reduceMod]) hknown (pref_of_split hpop)
  simp only [List.cons.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  rw [hmemory, ← hb0.memory, ← hb32.memory]
  rfl

section TransferLogFrame

open scoped LogOutputHinv

/-- The canonical ERC-20 `Transfer(src, dst, amount)` entry emitted by the
shared `transferFromLog` fragment. -/
def transferLogEntry (e : Sevm) (src dst amount : B256) : Log :=
  ⟨e.currentTarget, [transferEvent, src, dst], amount.toBytes⟩

/-- Exact effect of the shared `transferFromLog` fragment, retaining the
concrete post-log memory image.

This is contract-neutral: `transferFromLog` is the ERC-20 event tail that WETH,
WETH10, and the PRORATA WETH vault's asset child all reach, so the walk is
proved once here rather than once per family.  Keeping the resulting image lets
a following fragment reuse the word written for the event data without
replaying the LOG walk. -/
theorem transferFromLog_effect_frame
    {e : Sevm} {s r : Devm} {src dst amount : B256}
    {xs : Stack} {img : Bytes}
    (hp : dst :: amount :: src :: xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (run : Line.Run e s transferFromLog r) :
    amount :: src :: xs <<+ r.stack ∧
      r.logs = s.logs ++ [transferLogEntry e src dst amount] ∧
      Devm.getStor r = Devm.getStor s ∧
      Devm.getBal r = Devm.getBal s ∧
      Devm.getCode r = Devm.getCode s ∧
      r.output = s.output ∧
      Mem.Wf r.memory ∧
      Mem.Reads r.memory (Bytes.writeAt img 0 amount.toBytes) := by
  simp only [transferFromLog] at run
  rcases Line.of_run_cons run with ⟨s1, hdupSrc, run1⟩
  have hp1 : src :: dst :: amount :: src :: xs <<+ s1.stack :=
    prefix_of_dup_val hdupSrc (by show_nth) hp
  rcases Line.of_run_cons run1 with ⟨s2, hevent, run2⟩
  have hbevent := of_run_pushB256 hevent
  have hp2 : transferEvent :: src :: dst :: amount :: src :: xs <<+
      s2.stack := prefix_of_push hbevent hp1
  rcases Line.of_run_cons run2 with ⟨s3, hdupAmount, run3⟩
  have hp3 : amount :: transferEvent :: src :: dst :: amount :: src :: xs <<+
      s3.stack := prefix_of_dup_val hdupAmount (by show_nth) hp2
  rcases of_run_append (mstoreAt 0) run3 with ⟨s4, hstore, hlog⟩
  rcases of_run_mstoreAt_val hstore hp3 with ⟨hp4, hm4⟩
  have hm4' : s4.memory = s3.memory.write 0 amount.toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hm4
  rcases of_logWith201_val hp4 hlog with ⟨hp5, hlogs⟩
  have hlogMem := of_logWith201_mem hp4 hlog
  have hmem_s_s3 : s.memory = s3.memory := by
    calc
      s.memory = s1.memory := Ninst.Hinv.inv (f := Devm.memory) hdupSrc
      _ = s2.memory := hbevent.memory
      _ = s3.memory := Ninst.Hinv.inv (f := Devm.memory) hdupAmount
  let img1 := Bytes.writeAt img 0 amount.toBytes
  have hwf4 : Mem.Wf s4.memory := by
    rw [hm4', ← hmem_s_s3]
    exact h_wf.write 0 amount.toBytes
  have hreads4 : Mem.Reads s4.memory img1 := by
    rw [hm4', ← hmem_s_s3]
    exact Mem.Reads.write h_wf h_reads 0 amount.toBytes
  have hdata : (s4.memory.read 0 32).1 = amount.toBytes := by
    rw [Mem.Reads.read hreads4 0 32,
      show 32 = amount.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt]
  have hlogs_s_s4 : s.logs = s4.logs := by
    calc
      s.logs = s1.logs := Ninst.Hinv.inv (f := Devm.logs) hdupSrc
      _ = s2.logs := hbevent.logs
      _ = s3.logs := Ninst.Hinv.inv (f := Devm.logs) hdupAmount
      _ = s4.logs := Line.of_inv Devm.logs (by
        unfold mstoreAt
        line_inv) hstore
  have hwfR : Mem.Wf r.memory := by
    rw [hlogMem]
    exact hwf4.extend 0 32
  have hreadsR : Mem.Reads r.memory img1 := by
    rw [hlogMem]
    exact Mem.Reads.extend hreads4 0 32
  refine ⟨hp5, ?_, ?_, ?_, ?_, ?_, hwfR, hreadsR⟩
  · rw [hlogs, hdata, ← hlogs_s_s4]
    rfl
  · exact (Line.of_inv Devm.getStor (by line_inv) run).symm
  · exact (Line.of_inv Devm.getBal (by line_inv) run).symm
  · exact (Line.of_inv Devm.getCode (by line_inv) run).symm
  · exact (Line.of_inv Devm.output (by line_inv) run).symm

/-- Memory-premise-free form of the shared `transferFromLog` effect.  The
event data is read straight back out of the write that produced it, so no
`Mem.Wf` or proof-carrying image is needed.  Use this inside a contract body
walk that does not otherwise track memory. -/
theorem transferFromLog_effect
    {e : Sevm} {s r : Devm} {src dst amount : B256} {xs : Stack}
    (hp : dst :: amount :: src :: xs <<+ s.stack)
    (run : Line.Run e s transferFromLog r) :
    amount :: src :: xs <<+ r.stack ∧
      r.logs = s.logs ++ [transferLogEntry e src dst amount] := by
  simp only [transferFromLog] at run
  rcases Line.of_run_cons run with ⟨s1, hdupSrc, run1⟩
  have hp1 : src :: dst :: amount :: src :: xs <<+ s1.stack :=
    prefix_of_dup_val hdupSrc (by show_nth) hp
  rcases Line.of_run_cons run1 with ⟨s2, hevent, run2⟩
  have hbevent := of_run_pushB256 hevent
  have hp2 : transferEvent :: src :: dst :: amount :: src :: xs <<+
      s2.stack := prefix_of_push hbevent hp1
  rcases Line.of_run_cons run2 with ⟨s3, hdupAmount, run3⟩
  have hp3 : amount :: transferEvent :: src :: dst :: amount :: src :: xs <<+
      s3.stack := prefix_of_dup_val hdupAmount (by show_nth) hp2
  rcases of_run_append (mstoreAt 0) run3 with ⟨s4, hstore, hlog⟩
  rcases of_run_mstoreAt_val hstore hp3 with ⟨hp4, hm4⟩
  have hm4' : s4.memory = s3.memory.write 0 amount.toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hm4
  rcases of_logWith201_val hp4 hlog with ⟨hp5, hlogs⟩
  have amountNonempty : amount.toBytes ≠ [] := by
    intro empty
    have lengthEq : amount.toBytes.length = 32 := B256.length_toBytes amount
    rw [empty] at lengthEq
    exact absurd lengthEq (by decide)
  have hdata : (s4.memory.read 0 32).1 = amount.toBytes := by
    rw [hm4', show (32 : Nat) = amount.toBytes.length from
      (B256.length_toBytes amount).symm]
    exact Mem.read_write_zero s3.memory amountNonempty
  have hlogs_s_s4 : s.logs = s4.logs := by
    calc
      s.logs = s1.logs := Ninst.Hinv.inv (f := Devm.logs) hdupSrc
      _ = s2.logs := hbevent.logs
      _ = s3.logs := Ninst.Hinv.inv (f := Devm.logs) hdupAmount
      _ = s4.logs := Line.of_inv Devm.logs (by
        unfold mstoreAt
        line_inv) hstore
  refine ⟨hp5, ?_⟩
  rw [hlogs, hdata, ← hlogs_s_s4]
  rfl

/-- Exact effect of the shared `logTransfer` fragment.

This is the ERC-20 event tail of `transfer(dst, wad)`, the sibling of
`transferFromLog`: the source is the executing frame's caller rather than a
stack word, and the data word is copied straight out of calldata instead of
being taken from the stack.  It is contract-neutral -- WETH, WETH10 and the
PRORATA WETH vault's asset child all reach it through `transferCore` -- so the
walk is proved once here.

The fragment consumes and produces nothing on the stack, so any prefix
survives it. -/
theorem logTransfer_effect
    {e : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s logTransfer r) :
    xs <<+ r.stack ∧
      r.logs = s.logs ++
        [transferLogEntry e e.caller.toB256 (Sevm.argWord e 0)
          (Sevm.argWord e 1)] := by
  simp only [logTransfer, argCopy, cdc] at run
  rcases Line.of_run_cons run with ⟨c1, hsize, run1⟩
  have hsizeB := of_run_pushB256 hsize
  have hc1 : (32 : B256) :: xs <<+ c1.stack := by
    rw [show (1 * 32 : B256) = 32 by decide +kernel] at hsizeB
    exact prefix_of_push hsizeB hp
  rcases Line.of_run_cons run1 with ⟨c2, hsrc, run2⟩
  have hsrcB := of_run_pushB256 hsrc
  have hc2 : (36 : B256) :: 32 :: xs <<+ c2.stack := by
    rw [show (1 * 32 + 4 : B256) = 36 by decide +kernel] at hsrcB
    exact prefix_of_push hsrcB hc1
  rcases Line.of_run_cons run2 with ⟨c3, hdst, run3⟩
  have hdstB := of_run_pushB256 hdst
  have hc3 : (0 : B256) :: 36 :: 32 :: xs <<+ c3.stack := by
    rw [show (0 * 32 : B256) = 0 by decide +kernel] at hdstB
    exact prefix_of_push hdstB hc2
  rcases Line.of_run_cons run3 with ⟨c4, hcopy, run4⟩
  rcases prefix_of_calldatacopy_val hcopy hc3 with ⟨hc4, hcopyMem⟩
  have copyMemory : c4.memory = s.memory.write 0 (e.data.sliceD 36 32 0) := by
    rw [hcopyMem, ← hdstB.memory, ← hsrcB.memory, ← hsizeB.memory]
    rfl
  have copyLogs : s.logs = c4.logs :=
    hsizeB.logs.trans (hsrcB.logs.trans
      (hdstB.logs.trans (Ninst.Hinv.inv (f := Devm.logs) hcopy)))
  rcases of_run_append (arg 0) run4 with ⟨c5, hargRun, run5⟩
  have hc5 : Sevm.argWord e 0 :: xs <<+ c5.stack := prefix_of_arg hc4 hargRun
  have argMemory : c4.memory = c5.memory :=
    Line.of_inv Devm.memory (by line_inv) hargRun
  have argLogs : c4.logs = c5.logs :=
    Line.of_inv Devm.logs (by line_inv) hargRun
  rcases Line.of_run_cons run5 with ⟨c6, hcaller, run6⟩
  have hcallerB := of_run_caller hcaller
  have hc6 : e.caller.toB256 :: Sevm.argWord e 0 :: xs <<+ c6.stack :=
    prefix_of_push hcallerB hc5
  rcases Line.of_run_cons run6 with ⟨c7, hevent, run7⟩
  have heventB := of_run_pushB256 hevent
  have hc7 : transferEvent :: e.caller.toB256 :: Sevm.argWord e 0 :: xs <<+
      c7.stack := prefix_of_push heventB hc6
  rcases of_logWith201_val hc7 run7 with ⟨hc8, hlogs⟩
  have sliceLength : (e.data.sliceD 36 32 0).length = 32 :=
    List.takeD_length _ _ _
  have sliceNonempty : e.data.sliceD 36 32 0 ≠ [] := by
    intro empty
    rw [empty] at sliceLength
    exact absurd sliceLength (by decide)
  have eventMemory : c7.memory = s.memory.write 0 (e.data.sliceD 36 32 0) := by
    rw [← heventB.memory, ← hcallerB.memory, ← argMemory, copyMemory]
  have readBack :
      ((s.memory.write 0 (e.data.sliceD 36 32 0)).read 0 32).1 =
        e.data.sliceD 36 32 0 := by
    have raw := Mem.read_write_zero s.memory sliceNonempty
    rwa [sliceLength] at raw
  have hdata : (c7.memory.read 0 32).1 = (Sevm.argWord e 1).toBytes := by
    rw [eventMemory, readBack]
    show e.data.sliceD 36 32 0 = (Sevm.dataWord e ((32 * 1) + 4)).toBytes
    rw [show ((32 : B256) * 1 + 4) = 36 by decide +kernel]
    unfold Sevm.dataWord
    rw [show ((36 : B256)).toNat = 36 by decide +kernel]
    exact (Bytes.toBytes_toB256_of_length sliceLength).symm
  have eventLogs : s.logs = c7.logs :=
    copyLogs.trans (argLogs.trans
      (hcallerB.logs.trans heventB.logs))
  refine ⟨hc8, ?_⟩
  rw [hlogs, hdata, ← eventLogs]
  rfl

end TransferLogFrame

/-- Load one fixed scratch word against a proof-carrying memory image.  The
caller supplies the image equation for that word; the line preserves the image
and state while pushing the named value. -/
theorem of_run_loadWordAt_image
    {e : Sevm} {pre post : Devm} {word value : B256}
    {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hvalue : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value)
    (run : Line.Run e pre [pushB256 (word * 32), mload] post) :
    value :: tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory image ∧
      pre.state = post.state := by
  rcases Line.of_run_cons run with ⟨afterPush, pushRun, run⟩
  rcases Line.of_run_cons run with ⟨_, loadRun, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 pushRun
  have pPush := prefix_of_push pushed hp
  have pushWf : Mem.Wf afterPush.memory := by
    rw [← pushed.memory]
    exact hwf
  have pushReads : Mem.Reads afterPush.memory image := by
    rw [← pushed.memory]
    exact hreads
  obtain ⟨loaded, memory, _⟩ :=
    prefix_of_mload_val loadRun pPush pushReads
  refine ⟨?_, ?_, ?_, Line.of_inv Devm.state (by line_inv)
    (Line.Run.cons pushRun (Line.Run.cons loadRun Line.Run.nil))⟩
  · simpa only [hvalue, append_eq, nil_append] using loaded
  · rw [memory]
    exact pushWf.extend _ _
  · rw [memory]
    exact pushReads.extend _ _

/-- `of_run_loadWordAt_image` with the exact memory extension retained.  This
is useful when the caller can prove the read window was already covered and
therefore collapse the extension back to the original memory. -/
theorem of_run_loadWordAt_image_memory
    {e : Sevm} {pre post : Devm} {word value : B256}
    {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hvalue : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value)
    (run : Line.Run e pre [pushB256 (word * 32), mload] post) :
    value :: tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory image ∧
      pre.state = post.state ∧
      post.memory = pre.memory.extend (word * 32).toNat 32 := by
  rcases Line.of_run_cons run with ⟨afterPush, pushRun, run⟩
  rcases Line.of_run_cons run with ⟨_, loadRun, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 pushRun
  have pPush := prefix_of_push pushed hp
  have pushWf : Mem.Wf afterPush.memory := by
    rw [← pushed.memory]
    exact hwf
  have pushReads : Mem.Reads afterPush.memory image := by
    rw [← pushed.memory]
    exact hreads
  obtain ⟨loaded, memory, _⟩ :=
    prefix_of_mload_val loadRun pPush pushReads
  refine ⟨?_, ?_, ?_, Line.of_inv Devm.state (by line_inv)
    (Line.Run.cons pushRun (Line.Run.cons loadRun Line.Run.nil)), ?_⟩
  · simpa only [hvalue, append_eq, nil_append] using loaded
  · rw [memory]
    exact pushWf.extend _ _
  · rw [memory]
    exact pushReads.extend _ _
  · rw [memory, ← pushed.memory]

/-- A fixed scratch-word load is log-silent.  `MLOAD` has no global
`Ninst.Hinv` instance for logs, so expose the exact two-instruction fact at
the shared line altitude instead of reproving its register walk in every
constructor or decoder. -/
theorem of_run_loadWordAt_logs
    {e : Sevm} {pre post : Devm} {word : B256}
    (run : Line.Run e pre [pushB256 (word * 32), mload] post) :
    pre.logs = post.logs := by
  rcases Line.of_run_cons run with ⟨afterPush, pushRun, run⟩
  rcases Line.of_run_cons run with ⟨_, loadRun, hnil⟩
  cases hnil
  rcases of_run_reg loadRun with ⟨_, regRun⟩
  simp only [Rinst.run, Rinst.runCore] at regRun
  rcases Except.bind_eq_ok regRun with ⟨⟨_, popPost⟩, popRun, regRun⟩
  rcases Except.bind_eq_ok regRun with ⟨burnPost, burnRun, pushResult⟩
  rcases Devm.pop_of_popToNat popRun with ⟨_, popped⟩
  have burned := Devm.burn_of_chargeGas burnRun
  have pushed := Devm.push_of_push pushResult
  exact (of_run_pushB256 pushRun).logs.trans
    (((popped.logs.trans burned.logs).trans rfl).trans pushed.logs)

/-- `returnDataShorterThan n`, with its flag: the fragment pushes exactly the
comparison `returndatasize <? n` and touches nothing else. -/
lemma of_returnDataShorterThan_val {e : Sevm} {s s' : Devm} {n : B256} {xs}
    (hp : xs <<+ s.stack) (h : Line.Run e s (returnDataShorterThan n) s') :
    ((s.returnData.length.toB256 <? n) :: xs <<+ s'.stack) ∧
      s'.memory = s.memory ∧ s'.returnData = s.returnData := by
  simp only [returnDataShorterThan] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : n :: xs <<+ u1.stack := prefix_of_push hb1 hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hb2 := of_run_returndatasize_val q2
  rw [← hb1.returnData] at hb2
  have hp2 : s.returnData.length.toB256 :: n :: xs <<+ u2.stack :=
    prefix_of_push hb2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, hnil⟩
  cases hnil
  obtain ⟨a, b, hdb⟩ : ∃ a b, Devm.DiffBurn [a, b] [B256.ltCheck a b] u2 s' := by
    rcases of_run_reg q3 with ⟨pc, run⟩
    simp only [Rinst.run, Rinst.runCore] at run
    exact Devm.diffBurn_of_applyBinary run
  refine ⟨prefix_of_lt q3 hp2, ?_, ?_⟩
  · rw [← hdb.memory, ← hb2.memory, ← hb1.memory]
  · rw [← hdb.returnData, ← hb2.returnData, ← hb1.returnData]

/-- `checkReturnDataHead w m`, with its flag: the word the fragment compares
against `w` is *the returndata's head word*, read back through the memory word
it clobbers.  Carries the non-overrun bound the copy enforces — returndata of
at least a word, the reason `returnDataShorterThan` is branched on first — and
the memory image after the clobber. -/
lemma of_checkReturnDataHead_val {e : Sevm} {s s' : Devm} {w m : B256} {bs : Bytes}
    {xs}
    (hp : xs <<+ s.stack) (hwf : Mem.Wf s.memory) (hr : Mem.Reads s.memory bs)
    (h : Line.Run e s (checkReturnDataHead w m) s') :
    ((w =? Bytes.toB256 (s.returnData.sliceD 0 32 0)) :: xs <<+ s'.stack) ∧
      32 ≤ s.returnData.length ∧
      Mem.Wf s'.memory ∧
      Mem.Reads s'.memory
        (Bytes.writeAt bs (m * 32).toNat (s.returnData.sliceD 0 32 0)) ∧
      s'.returnData = s.returnData := by
  simp only [checkReturnDataHead, pushList, List.map] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : (32 : B256) :: xs <<+ u1.stack := prefix_of_push hb1 hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hb2 := of_run_pushB256 q2
  have hp2 : (0 : B256) :: (32 : B256) :: xs <<+ u2.stack :=
    prefix_of_push hb2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, h⟩
  have hb3 := of_run_pushB256 q3
  have hp3 : (m * 32) :: (0 : B256) :: (32 : B256) :: xs <<+ u3.stack :=
    prefix_of_push hb3 hp2
  have hm3 : s.memory = u3.memory := (hb1.memory.trans hb2.memory).trans hb3.memory
  have hrd3 : s.returnData = u3.returnData :=
    (hb1.returnData.trans hb2.returnData).trans hb3.returnData
  rcases Line.of_run_cons h with ⟨u4, q4, h⟩
  rcases prefix_of_returndatacopy_val q4 hp3 with ⟨hp4, hle4, hm4, hrd4⟩
  have hle : 32 ≤ s.returnData.length := by
    rw [hrd3]
    rw [show ((0 : B256)).toNat = 0 from rfl,
      show ((32 : B256)).toNat = 32 from rfl] at hle4
    omega
  have hslice : u3.returnData.sliceD ((0 : B256)).toNat ((32 : B256)).toNat 0
      = s.returnData.sliceD 0 32 0 := by
    rw [← hrd3, show ((0 : B256)).toNat = 0 from rfl,
      show ((32 : B256)).toNat = 32 from rfl]
  have hwf4 : Mem.Wf u4.memory := by
    rw [hm4, ← hm3]
    exact hwf.write _ _
  have hr4 : Mem.Reads u4.memory
      (Bytes.writeAt bs (m * 32).toNat (s.returnData.sliceD 0 32 0)) := by
    rw [hm4, ← hm3, hslice]
    exact hr.write hwf _ _
  rcases Line.of_run_cons h with ⟨u5, q5, h⟩
  have hb5 := of_run_pushB256 q5
  have hp5 : (m * 32) :: xs <<+ u5.stack := prefix_of_push hb5 hp4
  have hwf5 : Mem.Wf u5.memory := by
    rw [← hb5.memory]
    exact hwf4
  have hr5 : Mem.Reads u5.memory
      (Bytes.writeAt bs (m * 32).toNat (s.returnData.sliceD 0 32 0)) := by
    rw [← hb5.memory]
    exact hr4
  rcases Line.of_run_cons h with ⟨u6, q6, h⟩
  rcases prefix_of_mload_val q6 hp5 hr5 with ⟨hp6, hm6, hrd6⟩
  have hlen32 : (s.returnData.sliceD 0 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  have hhead : (Bytes.writeAt bs (m * 32).toNat
      (s.returnData.sliceD 0 32 0)).sliceD ((m * 32)).toNat 32 0
      = s.returnData.sliceD 0 32 0 := by
    conv_lhs =>
      rw [show (32 : Nat) = (s.returnData.sliceD 0 32 0).length from
        hlen32.symm]
    exact Bytes.sliceD_writeAt bs _ _
  rw [hhead] at hp6
  have hwf6 : Mem.Wf u6.memory := by
    rw [hm6]
    exact hwf5.extend _ _
  have hr6 : Mem.Reads u6.memory
      (Bytes.writeAt bs (m * 32).toNat (s.returnData.sliceD 0 32 0)) := by
    rw [hm6]
    exact hr5.extend _ _
  rcases Line.of_run_cons h with ⟨u7, q7, h⟩
  have hb7 := of_run_pushB256 q7
  have hp7 : w :: Bytes.toB256 (s.returnData.sliceD 0 32 0) :: xs <<+ u7.stack :=
    prefix_of_push hb7 hp6
  rcases Line.of_run_cons h with ⟨u8, q8, hnil⟩
  cases hnil
  obtain ⟨a, b, hdb⟩ : ∃ a b, Devm.DiffBurn [a, b] [B256.eqCheck a b] u7 s' := by
    rcases of_run_reg q8 with ⟨pc, run⟩
    simp only [Rinst.run, Rinst.runCore] at run
    exact Devm.diffBurn_of_applyBinary run
  refine ⟨prefix_of_eq q8 hp7, hle, ?_, ?_, ?_⟩
  · rw [← hdb.memory, ← hb7.memory]
    exact hwf6
  · rw [← hdb.memory, ← hb7.memory]
    exact hr6
  · rw [← hdb.returnData, ← hb7.returnData, hrd6, ← hb5.returnData, hrd4,
      ← hrd3]

/-! ### The dynamic tail of a canonically encoded call

`forwardArgTail 3` follows argument 3's head word to its length word and copies
the payload from there.  Under `Sevm.DecodesCallWithTail` those reads recover
exactly the `data` the encoding was built from — the round-trip that keeps a
statement about the forwarded bytes a statement about `data` rather than about
whatever the contract happens to read, which is the vacuity the arc's fixed
decision 2 forbids.

The length premise is unavoidable rather than convenient: `List.length` is an
unbounded `Nat` while the ABI's length word is 256 bits, so `data` longer than
`2 ^ 256` bytes would not round-trip through the encoding at all. -/

lemma tailPtr_three_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    Sevm.tailPtr e 3 = Nat.toB256 132 := by
  simp only [Sevm.tailPtr, argWord_three_of_decodes h]
  rfl

/-- The encoding, split at the tail's length word. -/
lemma decodes_split_tail {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    e.data = (abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++
      B256.toBytes c ++ B256.toBytes (Nat.toB256 128)) ++
      (B256.toBytes (Nat.toB256 data.length) ++
        (data ++ List.replicate (ceil32 data.length - data.length) 0)) := by
  simpa only [append_assoc, Sevm.DecodesCallWithTail, abiCallWithTail, map_cons, map_nil,
    flatten_cons, flatten_nil, append_nil, length_cons, length_nil, zero_add, reduceAdd, reduceMul,
    abiBytesTail] using h

lemma decodes_head_length (sel a b c : B256) :
    (abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++
      B256.toBytes c ++ B256.toBytes (Nat.toB256 128)).length = 132 := by
  rw [List.length_append, List.length_append, List.length_append, List.length_append,
    abiSelectorBytes_length, B256.length_toBytes, B256.length_toBytes,
    B256.length_toBytes, B256.length_toBytes]

lemma tailLen_three_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    Sevm.tailLen e 3 = Nat.toB256 data.length := by
  rw [Sevm.tailLen, tailPtr_three_of_decodes h]
  exact dataWord_of_append (by rw [decodes_head_length]; rfl) (decodes_split_tail h)

lemma tailBytes_three_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (hlen : data.length < 2 ^ 256)
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    Sevm.tailBytes e 3 = data := by
  have hnat : (Nat.toB256 data.length).toNat = data.length := by
    rw [B256.toNat_toB256]
    exact Nat.mod_eq_of_lt hlen
  simp only [Sevm.tailBytes, tailPtr_three_of_decodes h, tailLen_three_of_decodes h,
    hnat]
  have hd : e.data =
      ((abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++
        B256.toBytes c ++ B256.toBytes (Nat.toB256 128)) ++
        B256.toBytes (Nat.toB256 data.length)) ++
      (data ++ List.replicate (ceil32 data.length - data.length) 0) := by
    rw [List.append_assoc]; exact decodes_split_tail h
  have hpre : ((abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++
      B256.toBytes c ++ B256.toBytes (Nat.toB256 128)) ++
      B256.toBytes (Nat.toB256 data.length)).length = 164 := by
    rw [List.length_append, decodes_head_length, B256.length_toBytes]
  show List.sliceD e.data (Nat.toB256 132 + 32).toNat data.length 0 = data
  rw [show (Nat.toB256 132 + (32 : B256)).toNat = 164 from rfl, hd,
    List.sliceD, List.drop_length_append' (by rw [hpre]),
    List.takeD_eq_take _ (by simp only [length_append, length_replicate, le_add_iff_nonneg_right,
      _root_.zero_le]),
    List.take_length_append' rfl]

/-! ### `ceil32` as the EVM computes it

Every Solidity-shaped contract rounds a byte length up to a whole word with
`(len + 31) & ~31`, and a statement about the resulting `argsSize` is a
statement about `ceil32` only once that identity is proved.  `B256` is a nested
pair of `UInt64`s rather than a `BitVec`, so none of the usual bitvector API
applies and there was no `toNat` lemma for `&&&` at all; the three lemmas below
build one, and `bv_decide` is barred here (the protected cone's ban, and 256
bits would be infeasible regardless).

The bound `31 + len < 2 ^ 256` is the same kind of premise as
`tailBytes_three_of_decodes`'s: `List.length` is an unbounded `Nat` while the
machine word is 256 bits. -/

/-- **A frame with no successful outcome settles with some error.**  Cases on
the total function's result: the `.ok` branch is excluded by `h` via
`exec_iff_exec_eq`, which turns the excluded `Exec … (.ok post)` derivation
into the excluded `exec` equation; the `.error` branch is the conclusion
itself. Names no error kind — only that `exec` did not return `.ok`. -/
lemma exec_error_of_no_success {sevm : Sevm} {pre : Devm}
    (h : ∀ post, Exec 0 sevm pre (.ok post) → False) :
    ∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) := by
  rcases hexec : exec ⟨0, sevm, pre⟩ with ⟨e, post⟩ | post
  · exact ⟨e, post, rfl⟩
  · exact absurd ((exec_iff_exec_eq 0 sevm pre (.ok post)).mpr hexec)
      (fun ⟨a⟩ => h post a)

end Blanc
