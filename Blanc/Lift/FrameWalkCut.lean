import Blanc.Lift.FrameWalk
import Blanc.Lift.CursorExact
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.SoundSpan

/-!
# A frame walk reaches the exact state of a cut forward run

`lift_exactM` turns a gas-exact forward run (`SFunc.RunExact`) into *some* execution of the
frame; nothing in its statement says that the execution passes through the forward run's
states, so a call step of the forward run cannot be matched with an element of
`Exec.childFrames`. This module supplies the link on the actual derivation (`XAt`):

* `WalkAt`: the checked walk invariant (the derivation at `pc` in state `d`, the subtree `f`
  checked there over a matched abstract frame and memory map), with one step lemma per tree
  shape (`WalkAt.next`, `.dest`, `.zero`, `.succ`, `.toZero`, `.toSucc`, `.jump`, `.pcAt`,
  `.ret`, `.call`);
* `xa_retExact`: a walked exec-free tree whose gas-exact run returns puts the walk at the
  return address in the run's returned state, same remaining children (an internal callee
  crossed on the actual derivation);
* `xa_cutAt` / `xa_cutAt_start`: a walked checked node and a gas-exact run of a cut of its tree
  (`SFunc.CutCall`: one path to a subtree `tgt`, which becomes `.last .stop`, through no
  external instruction, possibly crossing internal calls into an exec-free, never-halting
  entry set `E`) halting in `s` put the walk at `tgt` in the state `s`, with the same remaining
  children and the checked invariants at `tgt`;
* `xa_staticcall_runCompiled`: at a walked `STATICCALL`, a compiled step of the call from the
  walked state is the frame's actual step, and its child (when a code frame is entered) is the
  head of the remaining children, with the step's return data as its output;
* `SFunc.cutPath`, `SFunc.subAt`, `SFunc.cutPathOk`, `SFunc.cutCall_of_cutPathOk`: a cut along
  an explicit list of steps (`CutStep.cl` crosses a call), checked by evaluation.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-! ## Exact jump steps -/

theorem popBurnBy_two_stack' {x y : B256} {cost : Nat} {s s' : Devm}
    (h : Devm.PopBurnBy [x, y] cost s s') : s.stack = x :: y :: s'.stack := by
  simpa only [Stack.Pop, Split, List.cons_append, List.nil_append] using h.stack

theorem popBurnBy_setMach {xs : List B256} {cost : Nat} {devm devm' : Devm}
    (h : Devm.PopBurnBy xs cost devm devm') :
    devm.setMach ⟨devm'.stack, devm.memory, devm.gasLeft - cost, devm.stateGas⟩ = devm' := by
  refine Devm.eq_of_proj rfl h.memory ?_ h.logs h.refundCounter h.output
    h.accountsToDelete h.returnData h.error h.accessedAddresses
    h.accessedStorageKeys h.state h.createdAccounts h.transientStorage h.stateGas
    h.accountReads h.storageReads h.storageWrites
  have hg := h.gasLeft
  change devm.gasLeft - cost = devm'.gasLeft
  omega

theorem evm_jumpi_zero_of_popBurnBy {pc : Nat} {sevm : Sevm} {devm devm' : Devm} {d : B256}
    (h_at : Jinst.At sevm.code pc .jumpi) (h : Devm.PopBurnBy [d, 0] gHigh devm devm') :
    Evm.step ⟨pc, sevm, devm⟩ = .cont (pc + 1) devm' := by
  have hs := popBurnBy_two_stack' h
  have hg : gHigh ≤ devm.gasLeft := by have := h.gasLeft; omega
  have hstep := Evm.jumpi_cont_zero h_at hs hg
  rw [popBurnBy_setMach h] at hstep
  exact hstep

theorem evm_jumpi_succ_of_popBurnBy {pc : Nat} {sevm : Sevm} {devm devm' : Devm} {d w : B256}
    (h_at : Jinst.At sevm.code pc .jumpi) (hne : w ≠ 0) (hjp : jumpable sevm.code d.toNat = true)
    (h : Devm.PopBurnBy [d, w] gHigh devm devm') :
    Evm.step ⟨pc, sevm, devm⟩ = .cont d.toNat devm' := by
  have hs := popBurnBy_two_stack' h
  have hg : gHigh ≤ devm.gasLeft := by have := h.gasLeft; omega
  have hstep := Evm.jumpi_cont_jump h_at hs hne hg hjp
  rw [popBurnBy_setMach h] at hstep
  exact hstep

/-! ## One checked instruction step keeps the checked invariants -/

section Next

variable {code : ByteArray} {es : List Entry} {ms : List MemMap} {b : Bool} {sevm : Sevm}
  {m pc : Nat} {a : List AVal} {μ : MemMap} {f : SFunc} {ρ : B256} {S base : List B256}
  {d d' : Devm}

private theorem cutNext_nonpush (hfork : CoveredFork sevm.benvStat.fork) (n0 : Ninst)
    (a1 a0 : List AVal) (out : Pattern) (hlen : a.length ≤ 1024)
    (htrans : ninstTransfer n0 (indexPattern a.length) = some out)
    (hread : out.mapM (readBack a) = some a1) (hfold : a0 = foldTop (foldConst n0 a) a1)
    (hrun : Ninst.Run sevm d n0 d') (hstack : d.stack = S ++ base) (hframe : FrameMatches ρ a S)
    (hmem : MemMatches ρ μ d.memory) :
    ∃ S', d'.stack = S' ++ base ∧
      FrameMatches ρ (if b then memFold (memTop n0 a μ) a0 else a0) S' ∧
      MemMatches ρ (if b then absMem n0 a μ else []) d'.memory ∧
      (RetIn (if b then memFold (memTop n0 a μ) a0 else a0) (if b then absMem n0 a μ else []) →
        RetIn a μ) := by
  have hinput :
      Matches ((indexPattern a.length).map (label a ρ) ++ base.map some) d.stack := by
    rw [hstack]
    apply matches_append
    · rw [indexPattern_map_label hlen]
      exact frameMatches_matches hframe
    · exact matches_some_map base
  have hmap := ninstTransfer_map (label a ρ) rfl htrans
  have happ := ninstTransfer_append (base.map some) hmap
  have hout := ninstTransfer_run hfork hinput happ hrun
  rw [mapM_readBack_label hread] at hout
  rcases matches_split hout with ⟨S', below, hsp, hfirst, hbelow⟩
  have hbelow' : below = base := matches_some_map_eq hbelow
  have hinter : d'.stack = S' ++ base := by
    simpa only [hbelow'] using hsp
  have hframe0 : FrameMatches ρ a0 S' := by
    rw [hfold]
    exact frameMatches_foldTop hframe hstack hrun hinter (matches_to_frame hfirst)
  obtain ⟨hframe', hmem'⟩ := step_mem_sound b hfork hframe hstack hmem hrun hinter hframe0
  refine ⟨S', hinter, hframe', hmem', fun h => ?_⟩
  rcases RetIn.of_step b h with h | h | h
  · exact .inl (ret_mem_of_readBack hread (ret_mem_of_foldTop (hfold ▸ h)))
  · exact .inl h
  · exact .inr h

/-- **A checked `.next` step keeps the checked invariants**: the instruction is in the code, and
the subtree is checked at the next pc, over the stepped state. -/
theorem checkNodeM_next_step (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {n : Ninst} (hcheck : checkNodeM code es ms b m pc a μ (.next n f) = true)
    (hjump : jumpsOkNodeM code es b (.next n f) a μ = true)
    (hrun : Ninst.Run sevm d n d') (hstack : d.stack = S ++ base) (hframe : FrameMatches ρ a S)
    (hmem : MemMatches ρ μ d.memory) :
    Ninst.At sevm.code pc n ∧ ∃ (a' : List AVal) (μ' : MemMap) (S' : List B256),
      checkNodeM code es ms b m (pc + n.size) a' μ' f = true ∧
      jumpsOkNodeM code es b f a' μ' = true ∧ d'.stack = S' ++ base ∧ FrameMatches ρ a' S' ∧
      MemMatches ρ μ' d'.memory ∧ (RetIn a' μ' → RetIn a μ) := by
  cases n
  case push bs fits =>
    have hchk := hcheck
    simp only [checkNodeM, absNinst, Bool.and_eq_true] at hchk
    have h_at : Ninst.At sevm.code pc (.push bs fits) := by
      apply Ninst.at_of_slice
      apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.push bs fits))
      rw [hcode]
      exact hchk.1.1
    have hstack' : d'.stack = Bytes.toB256 bs :: (S ++ base) := by
      rw [push_run_stack hrun, hstack]
    have hframe0 :
        FrameMatches ρ (.const (Bytes.toB256 bs) :: a) (Bytes.toB256 bs :: S) :=
      List.Forall₂.cons rfl hframe
    obtain ⟨hframe', hmem'⟩ := step_mem_sound b hfork hframe hstack hmem hrun
      (by rw [hstack']; rfl) hframe0
    have hjump' := hjump
    simp only [jumpsOkNodeM, absNinst] at hjump'
    refine ⟨h_at, _, _, _, hchk.2, hjump', hstack', hframe', hmem', fun h => ?_⟩
    rcases RetIn.of_step b h with h | h | h
    · exact .inl (by simpa only [List.mem_cons, reduceCtorEq, false_or] using h)
    · exact .inl h
    · exact .inr h
  all_goals
    have hchk := hcheck
    simp only [checkNodeM, Bool.and_eq_true] at hchk
    obtain ⟨⟨hb, -⟩, hm⟩ := hchk
    refine ⟨?_, ?_⟩
    · apply Ninst.at_of_slice
      apply bytesAt_slice (ninst_bytes_ne_nil _)
      rw [hcode]
      exact hb
    · split at hm
      · rename_i a0 ha
        rcases absNinst_nonpush_spec (by intro bs fits h; cases h) ha with
          ⟨hlen, out, a1, htrans, hread, hfold⟩
        have hjump' := hjump
        simp only [jumpsOkNodeM, ha] at hjump'
        obtain ⟨S', hst, hfr, hme, hret⟩ :=
          cutNext_nonpush hfork _ a1 a0 out hlen htrans hread hfold hrun hstack hframe hmem
        exact ⟨_, _, S', hm, hjump', hst, hfr, hme, hret⟩
      · cases hm

/-- A checked `.next` node's instruction is in the code at its pc. -/
theorem checkNodeM_next_at (hcode : sevm.code = code) {n : Ninst}
    (hcheck : checkNodeM code es ms b m pc a μ (.next n f) = true) : Ninst.At sevm.code pc n := by
  cases n
  case push bs fits =>
    simp only [checkNodeM, absNinst, Bool.and_eq_true] at hcheck
    apply Ninst.at_of_slice
    apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.push bs fits))
    rw [hcode]
    exact hcheck.1.1
  all_goals
    simp only [checkNodeM, Bool.and_eq_true] at hcheck
    apply Ninst.at_of_slice
    apply bytesAt_slice (ninst_bytes_ne_nil _)
    rw [hcode]
    exact hcheck.1.1

end Next

/-! ## Exact `JUMP` steps -/

theorem evm_jump_of_popBurnBy {pc : Nat} {sevm : Sevm} {devm devm' : Devm} {x : B256}
    (h_at : Jinst.At sevm.code pc .jump) (hjp : jumpable sevm.code x.toNat = true)
    (h : Devm.PopBurnBy [x] gMid devm devm') :
    Evm.step ⟨pc, sevm, devm⟩ = .cont x.toNat devm' := by
  have hs : devm.stack = x :: devm'.stack := by
    simpa only [Stack.Pop, Split, List.cons_append, List.nil_append] using h.stack
  have hg : gMid ≤ devm.gasLeft := by have := h.gasLeft; omega
  have hstep := Evm.jump_cont h_at hs hg hjp
  rw [popBurnBy_setMach h] at hstep
  exact hstep

theorem NoHaltSet.lookup {fs : List SFunc} {S : List Nat} (hS : NoHaltSet fs S = true) {k : Nat}
    {g : SFunc} (hk : k ∈ S) (hg : fs[k]? = some g) :
    g.noHalt = true ∧ g.refs.all (· ∈ S) = true := by
  have h := (List.all_eq_true.mp hS) k hk
  rw [hg] at h
  simpa only [Bool.and_eq_true] using h

/-! ## The checked walk invariant and its steps -/

/-- **The checked walk invariant**: the frame's actual derivation is at `pc` in the state `d`
with the remaining children `L`, and the subtree `f` is checked there over the abstract frame
`a` and the memory map `μ`, returning `m` words to `ρ` above the untouched `base`. -/
structure WalkAt (code : ByteArray) (c : Cert) (ms : List MemMap) (b : Bool) (sevm : Sevm)
    (post : Devm) (L : List Exec.Frame) (ρ : B256) (base : List B256) (m pc : Nat)
    (a : List AVal) (μ : MemMap) (f : SFunc) (d : Devm) : Prop where
  check : checkNodeM code c.entries ms b m pc a μ f = true
  jumps : jumpsOkNodeM code c.entries b f a μ = true
  frame : ∃ S, d.stack = S ++ base ∧ FrameMatches ρ a S
  mem : MemMatches ρ μ d.memory
  xat : XAt sevm post pc d L

section Walk

variable {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool} {sevm : Sevm}
  {post : Devm} {L : List Exec.Frame} {ρ : B256} {base : List B256}
  {m pc : Nat} {a : List AVal} {μ : MemMap} {d d' : Devm}

/-- A checked `JUMPI` node over a matched frame. -/
private theorem branch_decode {f g : SFunc} {S : List B256}
    (hcheck : checkNodeM code c.entries ms b m pc a μ (.branch f g) = true)
    (hjump : jumpsOkNodeM code c.entries b (.branch f g) a μ = true)
    (hframe : FrameMatches ρ a S) :
    ∃ t av2 a' s1 S1, a = .const t :: av2 :: a' ∧ S = t :: s1 :: S1 ∧
      AVal.Matches ρ av2 s1 ∧ FrameMatches ρ a' S1 ∧
      byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
      (av2.jumps? = some true ∨ (checkNodeM code c.entries ms b m (pc + 1) a' μ f = true ∧
        jumpsOkNodeM code c.entries b f a' μ = true)) ∧
      (av2.jumps? = some false ∨ (checkNodeM code c.entries ms b m t.toNat a' μ g = true ∧
        jumpdestOk code t.toNat = true ∧ jumpsOkNodeM code c.entries b g a' μ = true)) := by
  cases a with
  | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
  | cons av a0 =>
    cases av with
    | ret => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | const t =>
      cases a0 with
      | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
      | cons av2 a' =>
        have hcheck0 :
            (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
              (av2.jumps? = some true ∨
                checkNodeM code c.entries ms b m (pc + 1) a' μ f = true)) ∧
            (av2.jumps? = some false ∨
              checkNodeM code c.entries ms b m t.toNat a' μ g = true) := by
          simpa only [checkNodeM, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
        have hjump0 :
            (av2.jumps? = some true ∨ jumpsOkNodeM code c.entries b f a' μ = true) ∧
            (av2.jumps? = some false ∨
              (jumpdestOk code t.toNat = true ∧ jumpsOkNodeM code c.entries b g a' μ = true)) := by
          simpa only [jumpsOkNodeM, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] using hjump
        cases S with
        | nil => cases hframe
        | cons s0 S0 =>
          cases S0 with
          | nil => cases hframe with | cons _ hrest => cases hrest
          | cons s1 S1 =>
            cases hframe with
            | cons h0 hrest =>
              cases hrest with
              | cons h1 htail =>
                have hs0 : s0 = t := h0
                subst hs0
                refine ⟨s0, av2, a', s1, S1, rfl, rfl, h1, htail, hcheck0.1.1, ?_, ?_⟩
                · exact hcheck0.1.2.elim .inl fun p => hjump0.1.elim .inl fun q => .inr ⟨p, q⟩
                · exact hcheck0.2.elim .inl fun p => hjump0.2.elim .inl fun q => .inr ⟨p, q.1, q.2⟩

/-- A checked `JUMPI` to an entry over a matched frame. -/
private theorem branchTo_decode {f : SFunc} {k : Nat} {S : List B256}
    (hcheck : checkNodeM code c.entries ms b m pc a μ (.branchTo f k) = true)
    (hjump : jumpsOkNodeM code c.entries b (.branchTo f k) a μ = true)
    (hframe : FrameMatches ρ a S) :
    ∃ t av2 a' s1 S1 e, a = .const t :: av2 :: a' ∧ S = t :: s1 :: S1 ∧
      AVal.Matches ρ av2 s1 ∧ FrameMatches ρ a' S1 ∧ c.entries[k]? = some e ∧
      byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧ e.pc = t.toNat ∧ e.rets = m ∧
      gotoCompat a' e.frame = true ∧ memCompat μ (ms.getD k []) = true ∧
      jumpdestOk code e.pc = true ∧
      (av2.jumps? = some true ∨ (checkNodeM code c.entries ms b m (pc + 1) a' μ f = true ∧
        jumpsOkNodeM code c.entries b f a' μ = true)) := by
  cases a with
  | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
  | cons av a0 =>
    cases av with
    | ret => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | const t =>
      cases a0 with
      | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
      | cons av2 a' =>
        cases hk : c.entries[k]? with
        | none => simp only [checkNodeM, hk, Bool.false_eq_true] at hcheck
        | some e =>
          have hcheck0 :
              ((((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
                e.pc = t.toNat) ∧ e.rets = m) ∧
                gotoCompat a' e.frame = true) ∧ memCompat μ (ms[k]?.getD []) = true) ∧
                (av2.jumps? = some true ∨
                  checkNodeM code c.entries ms b m (pc + 1) a' μ f = true) := by
            simpa only [checkNodeM, hk, List.getD_eq_getElem?_getD, Bool.and_eq_true,
              beq_iff_eq, Bool.or_eq_true] using hcheck
          have hjump0 :
              jumpdestOk code e.pc = true ∧
                (av2.jumps? = some true ∨ jumpsOkNodeM code c.entries b f a' μ = true) := by
            simpa only [jumpsOkNodeM, hk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] using
              hjump
          have hmc : memCompat μ (ms.getD k []) = true := by
            simpa only [List.getD_eq_getElem?_getD] using hcheck0.1.2
          cases S with
          | nil => cases hframe
          | cons s0 S0 =>
            cases S0 with
            | nil => cases hframe with | cons _ hrest => cases hrest
            | cons s1 S1 =>
              cases hframe with
              | cons h0 hrest =>
                cases hrest with
                | cons h1 htail =>
                  have hs0 : s0 = t := h0
                  subst hs0
                  refine ⟨s0, av2, a', s1, S1, e, rfl, rfl, h1, htail, rfl, hcheck0.1.1.1.1.1,
                    hcheck0.1.1.1.1.2, hcheck0.1.1.1.2, hcheck0.1.1.2, hmc, hjump0.1, ?_⟩
                  exact hcheck0.2.elim .inl fun p => hjump0.2.elim .inl fun q => .inr ⟨p, q⟩

/-- **A walked `.next` step** (a non-spawning instruction). -/
theorem WalkAt.next (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {n : Ninst} {f : SFunc} (hn : ∀ x, n ≠ .exec x)
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ (.next n f) d)
    (hrun : Ninst.RunCompiled sevm d n d') :
    ∃ a' μ', WalkAt code c ms b sevm post L ρ base m (pc + n.size) a' μ' f d' ∧
      (RetIn a' μ' → RetIn a μ) := by
  obtain ⟨S, hstack, hframe⟩ := h.frame
  obtain ⟨xl, hfilled, hsteps⟩ := hrun
  obtain ⟨hat, a', μ', S', hchk', hjmp', hst', hfr', hme', hret⟩ :=
    checkNodeM_next_step hcode hfork h.check h.jumps ⟨xl, hfilled, 0, hsteps 0⟩ hstack hframe
      h.mem
  obtain ⟨d2, hrun2, h2⟩ := xa_next hat hn h.xat
  have e : d2 = d' := ninstRun_eq_of_runCompiled hrun2 ⟨xl, hfilled, hsteps⟩
  subst e
  exact ⟨a', μ', ⟨hchk', hjmp', ⟨S', hst', hfr'⟩, hme', h2⟩, hret⟩

/-- **A walked `JUMPDEST`.** -/
theorem WalkAt.dest (hcode : sevm.code = code) {f : SFunc}
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ (.dest f) d)
    (hburn : Devm.BurnBy gJumpdest d d') :
    WalkAt code c ms b sevm post L ρ base m (pc + 1) a μ f d' := by
  have hcheck' :
      byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
        checkNodeM code c.entries ms b m (pc + 1) a μ f = true := by
    simpa only [checkNodeM, Bool.and_eq_true, beq_iff_eq] using h.check
  have h_at : Jinst.At sevm.code pc .jumpdest := by
    apply byteAt_jinst_at
    rw [hcode]
    exact hcheck'.1
  obtain ⟨S, hstack, hframe⟩ := h.frame
  exact ⟨hcheck'.2, by simpa only [jumpsOkNodeM] using h.jumps,
    ⟨S, by rw [← hburn.stack, hstack], hframe⟩, h.mem.of_memory_eq hburn.memory,
    XAt.cont (Evm.jumpdest_cont h_at hburn) h.xat⟩

/-- **A walked `JUMPI` that falls through.** -/
theorem WalkAt.zero (hcode : sevm.code = code) {f g : SFunc} {x : B256}
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ (.branch f g) d)
    (hpop : Devm.PopBurnBy [x, 0] gHigh d d') :
    ∃ a', WalkAt code c ms b sevm post L ρ base m (pc + 1) a' μ f d' ∧
      (RetIn a' μ → RetIn a μ) := by
  obtain ⟨S, hstack, hframe⟩ := h.frame
  obtain ⟨t, av2, a', s1, S1, rfl, rfl, h1, htail, hb, hf, -⟩ := branch_decode h.check h.jumps hframe
  have h_at : Jinst.At sevm.code pc .jumpi := by
    apply byteAt_jinst_at
    rw [hcode]
    exact hb
  have hs := popBurnBy_two_stack' hpop
  rw [hstack] at hs
  simp only [List.cons_append, List.cons.injEq] at hs
  obtain ⟨-, hsw, hst⟩ := hs
  have hv : AVal.Matches ρ av2 0 := hsw ▸ h1
  obtain ⟨hchk, hjmp⟩ := live_fall hv hf
  exact ⟨a', ⟨hchk, hjmp, ⟨S1, hst.symm, htail⟩, h.mem.of_memory_eq hpop.memory,
    XAt.cont (evm_jumpi_zero_of_popBurnBy h_at hpop) h.xat⟩,
    RetIn.of_frame fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)⟩

/-- **A walked `JUMPI` that jumps.** -/
theorem WalkAt.succ (hcode : sevm.code = code) {f g : SFunc} {x w : B256} (hne : w ≠ 0)
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ (.branch f g) d)
    (hpop : Devm.PopBurnBy [x, w] gHigh d d') :
    ∃ pc' a', WalkAt code c ms b sevm post L ρ base m pc' a' μ g d' ∧
      (RetIn a' μ → RetIn a μ) := by
  obtain ⟨S, hstack, hframe⟩ := h.frame
  obtain ⟨t, av2, a', s1, S1, rfl, rfl, h1, htail, hb, -, hg⟩ := branch_decode h.check h.jumps hframe
  have h_at : Jinst.At sevm.code pc .jumpi := by
    apply byteAt_jinst_at
    rw [hcode]
    exact hb
  have hs := popBurnBy_two_stack' hpop
  rw [hstack] at hs
  simp only [List.cons_append, List.cons.injEq] at hs
  obtain ⟨hxt, hsw, hst⟩ := hs
  subst hxt
  have hv : AVal.Matches ρ av2 w := hsw ▸ h1
  obtain ⟨hchk, hjd, hjmp⟩ := live_taken hne hv hg
  have hjp : jumpable sevm.code t.toNat = true := by
    rw [hcode, jumpable_eq_jumpdestOk]
    exact hjd
  exact ⟨t.toNat, a', ⟨hchk, hjmp, ⟨S1, hst.symm, htail⟩, h.mem.of_memory_eq hpop.memory,
    XAt.cont (evm_jumpi_succ_of_popBurnBy h_at hne hjp hpop) h.xat⟩,
    RetIn.of_frame fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)⟩

/-- **A walked `JUMPI` to an entry that falls through.** -/
theorem WalkAt.toZero (hcode : sevm.code = code) {f : SFunc} {k : Nat} {x : B256}
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ (.branchTo f k) d)
    (hpop : Devm.PopBurnBy [x, 0] gHigh d d') :
    ∃ a', WalkAt code c ms b sevm post L ρ base m (pc + 1) a' μ f d' ∧
      (RetIn a' μ → RetIn a μ) := by
  obtain ⟨S, hstack, hframe⟩ := h.frame
  obtain ⟨t, av2, a', s1, S1, e, rfl, rfl, h1, htail, -, hb, -, -, -, -, -, hf⟩ :=
    branchTo_decode h.check h.jumps hframe
  have h_at : Jinst.At sevm.code pc .jumpi := by
    apply byteAt_jinst_at
    rw [hcode]
    exact hb
  have hs := popBurnBy_two_stack' hpop
  rw [hstack] at hs
  simp only [List.cons_append, List.cons.injEq] at hs
  obtain ⟨-, hsw, hst⟩ := hs
  have hv : AVal.Matches ρ av2 0 := hsw ▸ h1
  obtain ⟨hchk, hjmp⟩ := live_fall hv hf
  exact ⟨a', ⟨hchk, hjmp, ⟨S1, hst.symm, htail⟩, h.mem.of_memory_eq hpop.memory,
    XAt.cont (evm_jumpi_zero_of_popBurnBy h_at hpop) h.xat⟩,
    RetIn.of_frame fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)⟩

/-- **A walked `JUMPI` to an entry that jumps**: the walk enters the entry's tree. -/
theorem WalkAt.toSucc (hc : Cert.CheckedM code c ms b) (hj : Cert.JumpsOkM code c ms b)
    (hcode : sevm.code = code) {f g : SFunc} {k : Nat} {x w : B256} (hne : w ≠ 0)
    (hget : c.prog[k]? = some g)
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ (.branchTo f k) d)
    (hpop : Devm.PopBurnBy [x, w] gHigh d d') :
    ∃ pc' a' μ', WalkAt code c ms b sevm post L ρ base m pc' a' μ' g d' ∧
      (RetIn a' μ' → RetIn a μ) := by
  obtain ⟨S, hstack, hframe⟩ := h.frame
  obtain ⟨t, av2, a', s1, S1, e, rfl, rfl, h1, htail, hk, hb, hpc, hrets, hgc, hmc, hjd, -⟩ :=
    branchTo_decode h.check h.jumps hframe
  have h_at : Jinst.At sevm.code pc .jumpi := by
    apply byteAt_jinst_at
    rw [hcode]
    exact hb
  have hs := popBurnBy_two_stack' hpop
  rw [hstack] at hs
  simp only [List.cons_append, List.cons.injEq] at hs
  obtain ⟨hxt, -, hst⟩ := hs
  subst hxt
  have hjp : jumpable sevm.code t.toNat = true := by
    rw [hcode, jumpable_eq_jumpdestOk, ← hpc]
    exact hjd
  have hentry := hc k e g hk hget
  rw [hpc, hrets] at hentry
  exact ⟨t.toNat, e.frame, ms.getD k [], ⟨hentry, hj k e g hk hget,
    ⟨S1, hst.symm, frameMatches_gotoCompat hgc htail⟩,
    (h.mem.of_memory_eq hpop.memory).of_memCompat hmc,
    XAt.cont (evm_jumpi_succ_of_popBurnBy h_at hne hjp hpop) h.xat⟩,
    fun hr => RetIn.of_frame (fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
      (hr.imp (ret_mem_of_gotoCompat hgc) (mem_snd_of_memCompat hmc))⟩

/-- **A walked `JUMP` to an entry.** -/
theorem WalkAt.jump (hc : Cert.CheckedM code c ms b) (hj : Cert.JumpsOkM code c ms b)
    (hcode : sevm.code = code) {g : SFunc} {k : Nat} {x : B256} (hget : c.prog[k]? = some g)
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ (.jump k) d)
    (hpop : Devm.PopBurnBy [x] gMid d d') :
    ∃ pc' a' μ', WalkAt code c ms b sevm post L ρ base m pc' a' μ' g d' ∧
      (RetIn a' μ' → RetIn a μ) := by
  obtain ⟨S, hstack, hframe⟩ := h.frame
  have hcheck := h.check
  have hjump := h.jumps
  cases a with
  | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
  | cons av a' =>
    cases av with
    | ret => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | const t =>
      cases hk : c.entries[k]? with
      | none => simp only [checkNodeM, hk, Bool.false_eq_true] at hcheck
      | some e =>
        have hcheck0 :
            ((((byteAt code pc = some (Jinst.toUInt8 .jump) ∧
              e.pc = t.toNat) ∧ e.rets = m) ∧
              gotoCompat a' e.frame = true) ∧ memCompat μ (ms[k]?.getD []) = true) := by
          simpa only [checkNodeM, hk, List.getD_eq_getElem?_getD, Bool.and_eq_true,
            beq_iff_eq] using hcheck
        have hmc : memCompat μ (ms.getD k []) = true := by
          simpa only [List.getD_eq_getElem?_getD] using hcheck0.2
        have hjd : jumpdestOk code e.pc = true := by
          simpa only [jumpsOkNodeM, hk] using hjump
        have h_at : Jinst.At sevm.code pc .jump := by
          apply byteAt_jinst_at
          rw [hcode]
          exact hcheck0.1.1.1.1
        cases S with
        | nil => cases hframe
        | cons s0 S1 =>
          cases hframe with
          | cons h0 htail =>
            have hs0 : s0 = t := h0
            subst hs0
            have hs : s0 :: (S1 ++ base) = x :: d'.stack := by
              rw [← List.cons_append, ← hstack]
              simpa only [Stack.Pop, Split, List.cons_append, List.nil_append] using hpop.stack
            obtain ⟨hxt, hst⟩ := List.cons.inj hs
            subst hxt
            have hjp : jumpable sevm.code s0.toNat = true := by
              rw [hcode, jumpable_eq_jumpdestOk, ← hcheck0.1.1.1.2]
              exact hjd
            have hentry := hc k e g hk hget
            rw [hcheck0.1.1.1.2, hcheck0.1.1.2] at hentry
            exact ⟨s0.toNat, e.frame, ms.getD k [], ⟨hentry, hj k e g hk hget,
              ⟨S1, hst.symm, frameMatches_gotoCompat hcheck0.1.2 htail⟩,
              (h.mem.of_memory_eq hpop.memory).of_memCompat hmc,
              XAt.cont (evm_jump_of_popBurnBy h_at hjp hpop) h.xat⟩,
              fun hr => RetIn.of_frame (fun h => List.mem_cons_of_mem _ h)
                (hr.imp (ret_mem_of_gotoCompat hcheck0.1.2) (mem_snd_of_memCompat hmc))⟩

/-- **A walked `PC`.** -/
theorem WalkAt.pcAt (hcode : sevm.code = code) {p : Nat} {f : SFunc}
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ (.pcAt p f) d)
    (hstep : Ninst.StepRun p sevm d (.reg .pc) .none (.ok d')) :
    WalkAt code c ms b sevm post L ρ base m (pc + 1) (.const (Nat.toB256 pc) :: a) μ f d' := by
  have hcheck' :
      (bytesAt code pc (Ninst.toBytes (Ninst.reg .pc)) = true ∧ p = pc) ∧
        checkNodeM code c.entries ms b m (pc + 1) (.const (Nat.toB256 pc) :: a) μ f = true := by
    simpa only [checkNodeM, Bool.and_eq_true, beq_iff_eq] using h.check
  obtain ⟨⟨hbytes, rfl⟩, hchild⟩ := hcheck'
  have h_at : Ninst.At sevm.code p (Ninst.reg .pc) := by
    apply Ninst.at_of_slice
    apply bytesAt_slice (ninst_bytes_ne_nil (Ninst.reg .pc))
    rw [hcode]
    exact hbytes
  have hr : Rinst.run ⟨p, sevm, d⟩ .pc = .ok d' := by
    simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hstep
    exact hstep.2.symm
  have hs : Evm.step ⟨p, sevm, d⟩ = .cont (p + 1) d' := by
    rw [Evm.step_next h_at, Ninst.step_reg]
    simp only [hr, Step.ofExecution]
  obtain ⟨S, hstack, hframe⟩ := h.frame
  exact ⟨hchild, by simpa only [jumpsOkNodeM] using h.jumps,
    ⟨Nat.toB256 p :: S, by rw [pc_stepRun_stack hstep, hstack]; rfl, List.Forall₂.cons rfl hframe⟩,
    h.mem.of_memory_eq (pc_stepRun_memory hstep).symm, XAt.cont hs h.xat⟩

/-- **A walked return `JUMP`**: the walk is at `ρ`, with `m` words above `base`. -/
theorem WalkAt.ret (hcode : sevm.code = code) {x : B256}
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ .ret d)
    (hpop : Devm.PopBurnBy [x] gMid d d') :
    RetIn a μ ∧ ∃ S', XAt sevm post ρ.toNat d' L ∧ d'.stack = S' ++ base ∧ S'.length = m := by
  obtain ⟨S, hstack, hframe⟩ := h.frame
  have hcheck := h.check
  cases a with
  | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
  | cons av a' =>
    cases av with
    | const _ => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | ret =>
      have hcheck' : byteAt code pc = some (Jinst.toUInt8 .jump) ∧ a'.length = m := by
        simpa only [checkNodeM, Bool.and_eq_true, beq_iff_eq] using hcheck
      have h_at : Jinst.At sevm.code pc .jump := by
        apply byteAt_jinst_at
        rw [hcode]
        exact hcheck'.1
      cases S with
      | nil => cases hframe
      | cons t S1 =>
        cases hframe with
        | cons hhead htail =>
          have ht : t = ρ := hhead
          subst ht
          have hs : t :: (S1 ++ base) = x :: d'.stack := by
            rw [← List.cons_append, ← hstack]
            simpa only [Stack.Pop, Split, List.cons_append, List.nil_append] using hpop.stack
          obtain ⟨hxt, hst⟩ := List.cons.inj hs
          subst hxt
          obtain ⟨pc', d1, hrun, -⟩ := xa_jinst h_at h.xat
          obtain ⟨x', -, hpop', hjp⟩ := of_jump_run hrun
          have hx' : x' = t := by
            have hs' : d.stack = x' :: d1.stack := by
              simpa only [Stack.Pop, Split, List.cons_append, List.nil_append] using hpop'.stack
            rw [hstack] at hs'
            exact (List.cons.inj hs').1.symm
          subst hx'
          exact ⟨.inl List.mem_cons_self, S1, XAt.cont (evm_jump_of_popBurnBy h_at hjp hpop) h.xat,
            hst.symm, (List.Forall₂.length_eq htail).symm.trans hcheck'.2⟩

/-- **A walked internal call**: the walk enters the callee's entry tree over the callee's frame
(returning to `r` above `Sr ++ base`); once the callee is back at `r` with its `m'` results, the
walk is at the caller's continuation `f` (memory map reset). -/
theorem WalkAt.call (hc : Cert.CheckedM code c ms b) (hj : Cert.JumpsOkM code c ms b)
    (hcode : sevm.code = code) {k : Nat} {f g : SFunc} {x : B256}
    (hget : c.prog[k]? = some g)
    (h : WalkAt code c ms b sevm post L ρ base m pc a μ (.callNext k f) d)
    (hpop : Devm.PopBurnBy [x] gMid d d') :
    ∃ (r : B256) (Sr : List B256) (m' pc' : Nat) (a' : List AVal) (μ' : MemMap),
      WalkAt code c ms b sevm post L r (Sr ++ base) m' pc' a' μ' g d' ∧
      (RetIn a' μ' → ∀ {d'' : Devm} {Sret : List B256}, XAt sevm post r.toNat d'' L →
        d''.stack = Sret ++ (Sr ++ base) → Sret.length = m' →
        ∃ a'', WalkAt code c ms b sevm post L ρ base m r.toNat a'' [] f d'' ∧
          (RetIn a'' [] → RetIn a μ)) := by
  obtain ⟨S, hstack, hframe⟩ := h.frame
  have hcheck := h.check
  have hjump := h.jumps
  obtain ⟨dcont, rfl⟩ : ∃ dcont, f = .dest dcont := by
    cases f <;> first
      | exact ⟨_, rfl⟩
      | (cases a with
          | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
          | cons av _ => cases av <;> simp only [checkNodeM, Bool.false_eq_true] at hcheck)
  cases a with
  | nil => simp only [checkNodeM, Bool.false_eq_true] at hcheck
  | cons av a' =>
    cases av with
    | ret => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | unk => simp only [checkNodeM, Bool.false_eq_true] at hcheck
    | const t =>
      cases hk : c.entries[k]? with
      | none => simp only [checkNodeM, hk, Bool.false_eq_true] at hcheck
      | some e =>
        simp only [checkNodeM, hk, List.getD_eq_getElem?_getD, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq, List.isEmpty_iff] at hcheck
        simp only [hk, Option.some.injEq, jumpsOkNodeM, Bool.and_eq_true] at hjump
        have hentry := hc k e g hk hget
        have hjentry := hj k e g hk hget
        have hmk : ms.getD k [] = [] := by
          simpa only [List.getD_eq_getElem?_getD] using hcheck.1.2
        have h_at : Jinst.At sevm.code pc .jump := by
          apply byteAt_jinst_at
          rw [hcode]
          exact hcheck.1.1.1.1
        cases S with
        | nil => cases hframe
        | cons s0 S1 =>
          cases hframe with
          | cons h0 htail =>
            have hs0 : s0 = t := h0
            subst hs0
            have hs : s0 :: (S1 ++ base) = x :: d'.stack := by
              rw [← List.cons_append, ← hstack]
              simpa only [Stack.Pop, Split, List.cons_append, List.nil_append] using hpop.stack
            obtain ⟨hxt, hinter⟩ := List.cons.inj hs
            subst hxt
            have hjp : jumpable sevm.code s0.toNat = true := by
              rw [hcode, jumpable_eq_jumpdestOk, ← hcheck.1.1.1.2]
              exact hjump.1
            have hx' : XAt sevm post s0.toNat d' L :=
              XAt.cont (evm_jump_of_popBurnBy h_at hjp hpop) h.xat
            have hentry' : checkNodeM code c.entries ms b e.rets s0.toNat e.frame (ms.getD k [])
                g = true := by
              rw [← hcheck.1.1.1.2]
              exact hentry
            cases hidx : e.frame.findIdx? (· == .ret) with
            | none =>
              have hcall : callCompat 0 a' e.frame = true := by
                simpa only [hidx] using hcheck.2
              rcases frameMatches_callCompat hcall htail with ⟨Sf, Sr, hsplit, hframee, -⟩
              refine ⟨0, Sr, e.rets, s0.toNat, e.frame, ms.getD k [], ⟨hentry', hjentry,
                ⟨Sf, by rw [← hinter, hsplit, List.append_assoc], hframee⟩,
                by rw [hmk]; exact memMatches_nil _ _, hx'⟩, ?_⟩
              intro hret
              exfalso
              rcases hret with hret | hret
              · exact ret_not_mem_of_findIdx_none hidx AVal.ret hret rfl
              · simp only [hmk, List.map_nil, List.not_mem_nil] at hret
            | some i =>
              cases haidx : a'[i]? with
              | none => simp only [hidx, haidx, Bool.false_eq_true, and_false] at hcheck
              | some av =>
                cases av with
                | ret => simp only [hidx, haidx, Bool.false_eq_true, and_false] at hcheck
                | unk => simp only [hidx, haidx, Bool.false_eq_true, and_false] at hcheck
                | const r =>
                  have hcall : callCompat r a' e.frame = true ∧
                      byteAt code r.toNat = some (Jinst.toUInt8 .jumpdest) ∧
                      checkNodeM code c.entries ms b m (r.toNat + 1)
                        (List.replicate e.rets .unk ++ a'.drop e.frame.length) [] dcont = true := by
                    simpa only [hidx, haidx, Bool.and_eq_true, beq_iff_eq] using hcheck.2
                  have hjc : jumpdestOk code e.pc = true ∧ jumpdestOk code r.toNat = true ∧
                      jumpsOkNodeM code c.entries b dcont
                        (List.replicate e.rets .unk ++ a'.drop e.frame.length) [] = true := by
                    simpa only [hidx, haidx, Bool.and_eq_true] using hjump
                  rcases frameMatches_callCompat hcall.1 htail with
                    ⟨Sf, Sr, hsplit, hframee, hframer⟩
                  refine ⟨r, Sr, e.rets, s0.toNat, e.frame, ms.getD k [], ⟨hentry', hjentry,
                    ⟨Sf, by rw [← hinter, hsplit, List.append_assoc], hframee⟩,
                    by rw [hmk]; exact memMatches_nil _ _, hx'⟩, ?_⟩
                  intro _ d'' Sret hx'' hst hlen
                  have hunk : FrameMatches ρ (List.replicate e.rets .unk) Sret := by
                    rw [← hlen]
                    exact frameMatches_unk_length Sret
                  refine ⟨List.replicate e.rets .unk ++ a'.drop e.frame.length,
                    ⟨?_, ?_, ⟨Sret ++ Sr, by rw [hst, List.append_assoc], ?_⟩,
                      memMatches_nil _ _, hx''⟩, ?_⟩
                  · simp only [checkNodeM, hcall.2.1, BEq.rfl, hcall.2.2, Bool.and_self]
                  · simpa only [jumpsOkNodeM] using hjc.2.2
                  · apply matches_to_frame
                    rw [List.map_append]
                    apply matches_append
                    · exact frameMatches_matches hunk
                    · exact frameMatches_matches hframer
                  · intro h'
                    rcases h' with h' | h'
                    · rcases List.mem_append.mp h' with h' | h'
                      · simp only [List.mem_replicate, ne_eq, reduceCtorEq, and_false] at h'
                      · exact .inl (List.mem_cons_of_mem _ (List.mem_of_mem_drop h'))
                    · simp only [List.map_nil, List.not_mem_nil] at h'

end Walk

/-! ## Crossing an exec-free callee on the actual derivation -/

section Cross

variable {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool} {sevm : Sevm}

/-- **A walked exec-free tree whose gas-exact run returns** puts the walk at the return address
in the run's returned state, with `m` words above `base` and the same remaining children. -/
theorem xa_retExact (hc : Cert.CheckedM code c ms b) (hj : Cert.JumpsOkM code c ms b)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {E : List Nat}
    (hE : ExecFreeSet c.prog E = true) {d : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunExact c.prog sevm d f o) :
    ∀ {d' : Devm}, o = .returned d' → f.execFreeIn E = true →
      ∀ {post : Devm} {L : List Exec.Frame} {ρ : B256} {base : List B256} {m pc : Nat}
        {a : List AVal} {μ : MemMap}, WalkAt code c ms b sevm post L ρ base m pc a μ f d →
      RetIn a μ ∧ ∃ S', XAt sevm post ρ.toNat d' L ∧ d'.stack = S' ++ base ∧ S'.length = m := by
  induction run with
  | zero _ hpop _ ih =>
    intro d' hd hfree post L ρ base m pc a μ h
    obtain ⟨a', h', hr⟩ := WalkAt.zero hcode h hpop
    obtain ⟨hret, rest⟩ := ih hd (execFreeIn_branch hfree).1 h'
    exact ⟨hr hret, rest⟩
  | succ _ _ hne hpop _ ih =>
    intro d' hd hfree post L ρ base m pc a μ h
    obtain ⟨pc', a', h', hr⟩ := WalkAt.succ hcode hne h hpop
    obtain ⟨hret, rest⟩ := ih hd (execFreeIn_branch hfree).2 h'
    exact ⟨hr hret, rest⟩
  | toZero _ hpop _ ih =>
    intro d' hd hfree post L ρ base m pc a μ h
    obtain ⟨a', h', hr⟩ := WalkAt.toZero hcode h hpop
    obtain ⟨hret, rest⟩ := ih hd (execFreeIn_branchTo hfree).1 h'
    exact ⟨hr hret, rest⟩
  | toSucc _ _ hne hget hpop _ ih =>
    intro d' hd hfree post L ρ base m pc a μ h
    obtain ⟨pc', a', μ', h', hr⟩ := WalkAt.toSucc hc hj hcode hne hget h hpop
    obtain ⟨hret, rest⟩ :=
      ih hd (ExecFreeSet.lookup hE (execFreeIn_branchTo hfree).2 hget) h'
    exact ⟨hr hret, rest⟩
  | last _ => intro d' hd; cases hd
  | next hrun _ ih =>
    intro d' hd hfree post L ρ base m pc a μ h
    obtain ⟨hn, hf⟩ := execFreeIn_next hfree
    obtain ⟨a', μ', h', hr⟩ := WalkAt.next hcode hfork hn h hrun
    obtain ⟨hret, rest⟩ := ih hd hf h'
    exact ⟨hr hret, rest⟩
  | dest hburn _ ih =>
    intro d' hd hfree post L ρ base m pc a μ h
    exact ih hd (execFreeIn_dest hfree) (WalkAt.dest hcode h hburn)
  | jump _ hget hpop _ ih =>
    intro d' hd hfree post L ρ base m pc a μ h
    obtain ⟨pc', a', μ', h', hr⟩ := WalkAt.jump hc hj hcode hget h hpop
    obtain ⟨hret, rest⟩ := ih hd (ExecFreeSet.lookup hE (execFreeIn_jump hfree) hget) h'
    exact ⟨hr hret, rest⟩
  | ret _ hpop =>
    intro d' hd hfree post L ρ base m pc a μ h
    cases hd
    exact WalkAt.ret hcode h hpop
  | callHalt _ _ _ _ _ => intro d' hd; cases hd
  | callRet _ hget hpop _ _ ihrun ihcont =>
    intro d' hd hfree post L ρ base m pc a μ h
    obtain ⟨hf, hk⟩ := execFreeIn_callNext hfree
    obtain ⟨r, Sr, m', pc', a', μ', hw, hcont⟩ := WalkAt.call hc hj hcode hget h hpop
    obtain ⟨hret, S', hx, hst, hlen⟩ := ihrun rfl (ExecFreeSet.lookup hE hk hget) hw
    obtain ⟨a'', hw'', hr⟩ := hcont hret hx hst hlen
    obtain ⟨hret', rest⟩ := ihcont hd (execFreeIn_dest hf) hw''
    exact ⟨hr hret', rest⟩
  | pcAt hstep _ ih =>
    intro d' hd hfree post L ρ base m pc a μ h
    obtain ⟨hret, rest⟩ := ih hd (execFreeIn_pcAt hfree) (WalkAt.pcAt hcode h hstep)
    exact ⟨RetIn.of_frame (fun h => by simpa only [List.mem_cons, reduceCtorEq, false_or] using h)
      hret, rest⟩

end Cross

/-! ## The cut walk -/

/-- `SFunc.CutCall fs E tgt f f'`: as `SFunc.CutAt`, and the path may also cross an internal call
into an entry of `E` (the cut keeps the `.callNext` and continues in its continuation). -/
inductive SFunc.CutCall (fs : List SFunc) (E : List Nat) (tgt : SFunc) : SFunc → SFunc → Prop
  | here : SFunc.CutCall fs E tgt tgt (.last .stop)
  | next {n : Ninst} {f f' : SFunc} :
    (∀ x : Xinst, n ≠ .exec x) → SFunc.CutCall fs E tgt f f' →
    SFunc.CutCall fs E tgt (.next n f) (.next n f')
  | dest {f f' : SFunc} :
    SFunc.CutCall fs E tgt f f' → SFunc.CutCall fs E tgt (.dest f) (.dest f')
  | zero {f f' g : SFunc} :
    SFunc.CutCall fs E tgt f f' → SFunc.CutCall fs E tgt (.branch f g) (.branch f' .undefined)
  | succ {f g g' : SFunc} :
    SFunc.CutCall fs E tgt g g' → SFunc.CutCall fs E tgt (.branch f g) (.branch .undefined g')
  | toZero {f f' : SFunc} {k : Nat} :
    SFunc.CutCall fs E tgt f f' → SFunc.CutCall fs E tgt (.branchTo f k) (.branch f' .undefined)
  | toSucc {f g g' : SFunc} {k : Nat} :
    fs[k]? = some g → SFunc.CutCall fs E tgt g g' →
    SFunc.CutCall fs E tgt (.branchTo f k) (.branch .undefined g')
  | call {f f' : SFunc} {k : Nat} :
    k ∈ E → SFunc.CutCall fs E tgt f f' → SFunc.CutCall fs E tgt (.callNext k f) (.callNext k f')

section Cut

variable {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool} {sevm : Sevm}

/-- **A walked checked node reaches the halting state of a cut run** (see the module note).
The cut may cross calls into `E`, an exec-free closed entry set none of whose trees halts. -/
theorem xa_cutAt (hc : Cert.CheckedM code c ms b) (hj : Cert.JumpsOkM code c ms b)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {E : List Nat}
    (hE : ExecFreeSet c.prog E = true) (hN : NoHaltSet c.prog E = true) {tgt f f' : SFunc}
    (cut : SFunc.CutCall c.prog E tgt f f') :
    ∀ {d s : Devm}, SFunc.RunExact c.prog sevm d f' (.halted s) →
      ∀ {post : Devm} {L : List Exec.Frame} {ρ : B256} {base : List B256} {m pc : Nat}
        {a : List AVal} {μ : MemMap}, WalkAt code c ms b sevm post L ρ base m pc a μ f d →
      ∃ (m' pc' : Nat) (a' : List AVal) (μ' : MemMap),
        WalkAt code c ms b sevm post L ρ base m' pc' a' μ' tgt s := by
  induction cut with
  | here =>
    intro d s run post L ρ base m pc a μ h
    cases run with
    | last stop =>
      have self : Linst.Run sevm d .stop (.ok d) := rfl
      have e : s = d := (Except.ok.inj (stop.symm.trans self))
      subst e
      exact ⟨m, pc, a, μ, h⟩
  | next hn _ ih =>
    intro d s run post L ρ base m pc a μ h
    cases run with
    | next compiled rest =>
      obtain ⟨a', μ', h', -⟩ := WalkAt.next hcode hfork hn h compiled
      exact ih rest h'
  | dest _ ih =>
    intro d s run post L ρ base m pc a μ h
    cases run with
    | dest hburn rest => exact ih rest (WalkAt.dest hcode h hburn)
  | zero _ ih =>
    intro d s run post L ρ base m pc a μ h
    cases run with
    | succ _ _ _ _ rest => cases rest
    | zero _ hpop rest =>
      obtain ⟨a', h', -⟩ := WalkAt.zero hcode h hpop
      exact ih rest h'
  | succ _ ih =>
    intro d s run post L ρ base m pc a μ h
    cases run with
    | zero _ _ rest => cases rest
    | succ _ _ hne hpop rest =>
      obtain ⟨pc', a', h', -⟩ := WalkAt.succ hcode hne h hpop
      exact ih rest h'
  | toZero _ ih =>
    intro d s run post L ρ base m pc a μ h
    cases run with
    | succ _ _ _ _ rest => cases rest
    | zero _ hpop rest =>
      obtain ⟨a', h', -⟩ := WalkAt.toZero hcode h hpop
      exact ih rest h'
  | toSucc hget _ ih =>
    intro d s run post L ρ base m pc a μ h
    cases run with
    | zero _ _ rest => cases rest
    | succ _ _ hne hpop rest =>
      obtain ⟨pc', a', μ', h', -⟩ := WalkAt.toSucc hc hj hcode hne hget h hpop
      exact ih rest h'
  | call hk _ ih =>
    intro d s run post L ρ base m pc a μ h
    cases run with
    | callHalt _ hget _ hrun =>
      obtain ⟨hnh, hrefs⟩ := NoHaltSet.lookup hN hk hget
      exact (SFunc.RunP.not_halted hN hnh hrefs hrun.toRun rfl).elim
    | callRet _ hget hpop hrun rest =>
      obtain ⟨r, Sr, m', pc', a', μ', hw, hcont⟩ := WalkAt.call hc hj hcode hget h hpop
      obtain ⟨hret, S', hx, hst, hlen⟩ :=
        xa_retExact hc hj hcode hfork hE hrun rfl (ExecFreeSet.lookup hE hk hget) hw
      obtain ⟨a'', hw'', -⟩ := hcont hret hx hst hlen
      exact ih rest hw''

/-- **The cut walk from a frame's start**: a frame whose first entry is checked at pc `0`, walked
from its start in `pre` with remaining children `L`, reaches the cut subtree `tgt` in the cut
run's halting state `s`, with the same `L`, at a pc where `tgt` is checked. -/
theorem xa_cutAt_start (hc : Cert.CheckedM code c ms b) (hj : Cert.JumpsOkM code c ms b)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {E : List Nat}
    (hE : ExecFreeSet c.prog E = true) (hN : NoHaltSet c.prog E = true)
    {e : Entry} {f0 tgt f' : SFunc} (he : c.entries[0]? = some e) (hf : c.prog[0]? = some f0)
    (hpc : e.pc = 0) (hfr : e.frame = []) (hm0 : ms.getD 0 [] = [])
    (cut : SFunc.CutCall c.prog E tgt f0 f')
    {pre s post : Devm} {L : List Exec.Frame}
    (run : SFunc.RunExact c.prog sevm pre f' (.halted s)) (h : XAt sevm post 0 pre L) :
    ∃ (m' pc' : Nat) (a' : List AVal) (μ' : MemMap),
      WalkAt code c ms b sevm post L 0 pre.stack m' pc' a' μ' tgt s := by
  have hf' := hc 0 e f0 he hf
  have hentry := hj 0 e f0 he hf
  rw [hm0, hpc, hfr] at hf'
  rw [hm0, hfr] at hentry
  exact xa_cutAt hc hj hcode hfork hE hN cut run ⟨hf', hentry,
    ⟨[], rfl, by simp only [FrameMatches, List.forall₂_nil_right_iff]⟩, memMatches_nil _ _, h⟩

end Cut

/-! ## Cuts along explicit steps -/

/-- One step of a cut path: an instruction, a jumpdest, the fall-through or the taken arm of a
`.branch`, the fall-through or the taken goto of a `.branchTo`, or an internal call crossed to
its continuation. -/
inductive CutStep where
  | nx | ds | z | s | tz | ts | cl
  deriving DecidableEq, Repr

/-- The tree `f` cut along the steps `p` (`SFunc.CutCall`'s shape). -/
def SFunc.cutPath (fs : List SFunc) : List CutStep → SFunc → SFunc
  | [], _ => .last .stop
  | .nx :: p, .next n f => .next n (SFunc.cutPath fs p f)
  | .ds :: p, .dest f => .dest (SFunc.cutPath fs p f)
  | .z :: p, .branch f _ => .branch (SFunc.cutPath fs p f) .undefined
  | .s :: p, .branch _ g => .branch .undefined (SFunc.cutPath fs p g)
  | .tz :: p, .branchTo f _ => .branch (SFunc.cutPath fs p f) .undefined
  | .ts :: p, .branchTo _ k =>
    match fs[k]? with
    | some g => .branch .undefined (SFunc.cutPath fs p g)
    | none => .undefined
  | .cl :: p, .callNext k f => .callNext k (SFunc.cutPath fs p f)
  | _ :: _, _ => .undefined

/-- The subtree the steps `p` reach in `f`. -/
def SFunc.subAt (fs : List SFunc) : List CutStep → SFunc → SFunc
  | [], f => f
  | .nx :: p, .next _ f => SFunc.subAt fs p f
  | .ds :: p, .dest f => SFunc.subAt fs p f
  | .z :: p, .branch f _ => SFunc.subAt fs p f
  | .s :: p, .branch _ g => SFunc.subAt fs p g
  | .tz :: p, .branchTo f _ => SFunc.subAt fs p f
  | .ts :: p, .branchTo _ k =>
    match fs[k]? with
    | some g => SFunc.subAt fs p g
    | none => .undefined
  | .cl :: p, .callNext _ f => SFunc.subAt fs p f
  | _ :: _, _ => .undefined

/-- The steps `p` follow `f`'s shape, through no external instruction, crossing calls only into
`E`. -/
def SFunc.cutPathOk (fs : List SFunc) (E : List Nat) : List CutStep → SFunc → Bool
  | [], _ => true
  | .nx :: p, .next n f =>
    (match n with
     | .exec _ => false
     | _ => true) && SFunc.cutPathOk fs E p f
  | .ds :: p, .dest f => SFunc.cutPathOk fs E p f
  | .z :: p, .branch f _ => SFunc.cutPathOk fs E p f
  | .s :: p, .branch _ g => SFunc.cutPathOk fs E p g
  | .tz :: p, .branchTo f _ => SFunc.cutPathOk fs E p f
  | .ts :: p, .branchTo _ k =>
    match fs[k]? with
    | some g => SFunc.cutPathOk fs E p g
    | none => false
  | .cl :: p, .callNext k f => decide (k ∈ E) && SFunc.cutPathOk fs E p f
  | _ :: _, _ => false

theorem SFunc.cutCall_of_cutPathOk {fs : List SFunc} {E : List Nat} :
    ∀ (p : List CutStep) (f : SFunc), SFunc.cutPathOk fs E p f = true →
      SFunc.CutCall fs E (SFunc.subAt fs p f) f (SFunc.cutPath fs p f)
  | [], f, _ => .here
  | .nx :: p, .next n f, h => by
    simp only [SFunc.cutPathOk, Bool.and_eq_true] at h
    refine .next ?_ (SFunc.cutCall_of_cutPathOk p f h.2)
    intro x hx
    subst hx
    simp only [Bool.false_eq_true] at h
    exact h.1
  | .ds :: p, .dest f, h => .dest (SFunc.cutCall_of_cutPathOk p f h)
  | .z :: p, .branch f _, h => .zero (SFunc.cutCall_of_cutPathOk p f h)
  | .s :: p, .branch _ g, h => .succ (SFunc.cutCall_of_cutPathOk p g h)
  | .tz :: p, .branchTo f _, h => .toZero (SFunc.cutCall_of_cutPathOk p f h)
  | .ts :: p, .branchTo _ k, h => by
    simp only [SFunc.cutPathOk] at h
    cases hk : fs[k]? with
    | none => rw [hk] at h; cases h
    | some g =>
      rw [hk] at h
      simp only [SFunc.subAt, SFunc.cutPath, hk]
      exact .toSucc hk (SFunc.cutCall_of_cutPathOk p g h)
  | .cl :: p, .callNext k f, h => by
    simp only [SFunc.cutPathOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .call h.1 (SFunc.cutCall_of_cutPathOk p f h.2)

/-! ## A walked call step that a compiled step also runs -/

/-- **A compiled `STATICCALL` step from a walked state is the frame's step**: the walk continues
in its state, and when a code frame is entered (the flag is nonzero and the target is not an
precompile) the head of the remaining children is the call's child, whose output is
the step's return data. -/
theorem xa_staticcall_runCompiled {sevm : Sevm} {post d d' : Devm} {pc : Nat}
    {L : List Exec.Frame} (fork : CoveredFork sevm.benvStat.fork)
    (hat : Ninst.At sevm.code pc (.exec .staticcall))
    {g t ii is oi os : B256} {S : List B256} (hstack : d.stack = g :: t :: ii :: is :: oi :: os :: S)
    (h : XAt sevm post pc d L) (hrun : Ninst.RunCompiled sevm d (.exec .staticcall) d')
    {flag : B256} {rest : List B256} (hflag : d'.stack = flag :: rest) (hnz : flag ≠ 0)
    (hframed : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) :
    ∃ c L', L = c :: L' ∧ XAt sevm post (pc + 1) d' L' ∧
      ChildOf d d' t.toAdr (d.memory.read ii.toNat is.toNat).1 0 true c := by
  obtain ⟨d2, hrun2, L', h2, hk⟩ := xa_staticcall fork hat hstack h
  have e : d2 = d' := ninstRun_eq_of_runCompiled hrun2 hrun
  subst e
  rcases hk flag rest hflag hnz with ⟨hpre, -⟩ | ⟨c, hL, -, -, hch⟩
  · exact absurd hpre hframed
  · exact ⟨c, L', hL, h2, hch⟩

end Blanc.Lift
