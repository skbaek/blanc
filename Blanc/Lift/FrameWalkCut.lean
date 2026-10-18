import Blanc.Lift.FrameWalk
import Blanc.Lift.CursorExact

/-!
# A frame walk reaches the exact state of a cut forward run

`lift_exactM` turns a gas-exact forward run (`SFunc.RunExact`) into *some* execution of the
frame; nothing in its statement says that the execution passes through the forward run's
states, so a call step of the forward run cannot be matched with an element of
`Exec.childFrames`. This module supplies the link on the actual derivation (`XAt`):

* `xa_cutAt`: a checked node walked by `XAt`, and a gas-exact run of a cut of its tree
  (`SFunc.CutAt`: one exec-free path to a subtree `tgt`, which becomes `.last .stop`) halting in
  `s`, put the walk at `tgt` in the state `s`, with the same remaining children and the checked
  invariants at `tgt`;
* `xa_exec_runCompiled`: at a walked `CALL`/`STATICCALL`, a compiled step of the call from the
  walked state is the frame's actual step, and its child (when a code frame is entered) is the
  head of the remaining children, with the step's return data as its output;
* `SFunc.cutPath`, `SFunc.subAt`, `SFunc.cutPathOk`, `SFunc.cutAt_of_cutPathOk`: a cut along an
  explicit list of steps, checked by evaluation.

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
      MemMatches ρ (if b then absMem n0 a μ else []) d'.memory := by
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
  exact ⟨S', hinter, hframe', hmem'⟩

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
      MemMatches ρ μ' d'.memory := by
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
    exact ⟨h_at, _, _, _, hchk.2, hjump', hstack', hframe', hmem'⟩
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
        obtain ⟨S', hst, hfr, hme⟩ :=
          cutNext_nonpush hfork _ a1 a0 out hlen htrans hread hfold hrun hstack hframe hmem
        exact ⟨_, _, S', hm, hjump', hst, hfr, hme⟩
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

/-! ## The cut walk -/

section Cut

variable {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool} {sevm : Sevm}

/-- **A walked checked node reaches the halting state of a cut run** (see the module note). -/
theorem xa_cutAt (hc : Cert.CheckedM code c ms b) (hj : Cert.JumpsOkM code c ms b)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {tgt f f' : SFunc}
    (cut : SFunc.CutAt c.prog tgt f f') :
    ∀ {fs' : List SFunc} {d s : Devm}, SFunc.RunExact fs' sevm d f' (.halted s) →
      ∀ {pc m : Nat} {a : List AVal} {ρ : B256} {S base : List B256} {μ : MemMap},
      checkNodeM code c.entries ms b m pc a μ f = true →
      jumpsOkNodeM code c.entries b f a μ = true →
      d.stack = S ++ base → FrameMatches ρ a S → MemMatches ρ μ d.memory →
      ∀ {post : Devm} {L : List Exec.Frame}, XAt sevm post pc d L →
      ∃ (pc' m' : Nat) (a' : List AVal) (S' : List B256) (μ' : MemMap),
        XAt sevm post pc' s L ∧ checkNodeM code c.entries ms b m' pc' a' μ' tgt = true ∧
        jumpsOkNodeM code c.entries b tgt a' μ' = true ∧ s.stack = S' ++ base ∧
        FrameMatches ρ a' S' ∧ MemMatches ρ μ' s.memory := by
  induction cut with
  | here =>
    intro fs' d s run pc m a ρ S base μ hcheck hjump hstack hframe hmem post L h
    cases run with
    | last stop =>
      have self : Linst.Run sevm d .stop (.ok d) := rfl
      have e : s = d := (Except.ok.inj (stop.symm.trans self))
      subst e
      exact ⟨pc, m, a, S, μ, h, hcheck, hjump, hstack, hframe, hmem⟩
  | @next n f f' hn cut ih =>
    intro fs' d s run pc m a ρ S base μ hcheck hjump hstack hframe hmem post L h
    cases run with
    | next compiled rest =>
      rename_i d1
      obtain ⟨xl, hfilled, hsteps⟩ := compiled
      have hrunN : Ninst.Run sevm d n d1 := ⟨xl, hfilled, 0, hsteps 0⟩
      obtain ⟨hat, a', μ', S', hchk', hjmp', hst', hfr', hme'⟩ :=
        checkNodeM_next_step hcode hfork hcheck hjump hrunN hstack hframe hmem
      obtain ⟨d2, hrun2, h2⟩ := xa_next hat hn h
      have e : d2 = d1 := ninstRun_eq_of_runCompiled hrun2 ⟨xl, hfilled, hsteps⟩
      subst e
      exact ih rest hchk' hjmp' hst' hfr' hme' h2
  | @dest f f' cut ih =>
    intro fs' d s run pc m a ρ S base μ hcheck hjump hstack hframe hmem post L h
    cases run with
    | dest hburn rest =>
      rename_i d1
      have hcheck' :
          byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
            checkNodeM code c.entries ms b m (pc + 1) a μ f = true := by
        simpa only [checkNodeM, Bool.and_eq_true, beq_iff_eq] using hcheck
      have h_at : Jinst.At sevm.code pc .jumpdest := by
        apply byteAt_jinst_at
        rw [hcode]
        exact hcheck'.1
      have hstack' : d1.stack = S ++ base := by
        rw [← hburn.stack, hstack]
      exact ih rest hcheck'.2 (by simpa only [jumpsOkNodeM] using hjump) hstack' hframe
        (hmem.of_memory_eq hburn.memory) (XAt.cont (Evm.jumpdest_cont h_at hburn) h)
  | @zero f f' g cut ih =>
    intro fs' d s run pc m a ρ S base μ hcheck hjump hstack hframe hmem post L h
    cases run with
    | succ dd w hne hpop rest => cases rest
    | zero dd hpop rest =>
      rename_i d1
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
            have h_at : Jinst.At sevm.code pc .jumpi := by
              apply byteAt_jinst_at
              rw [hcode]
              exact hcheck0.1.1
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
                    have hs := popBurnBy_two_stack' hpop
                    rw [hstack] at hs
                    simp only [List.cons_append, List.cons.injEq] at hs
                    have hv : AVal.Matches ρ av2 0 := hs.2.1 ▸ h1
                    exact ih rest (live_fall hv hcheck0.1.2) (live_fall hv hjump0.1) hs.2.2.symm
                      htail (hmem.of_memory_eq hpop.memory)
                      (XAt.cont (evm_jumpi_zero_of_popBurnBy h_at hpop) h)
  | @succ f g g' cut ih =>
    intro fs' d s run pc m a ρ S base μ hcheck hjump hstack hframe hmem post L h
    cases run with
    | zero dd hpop rest => cases rest
    | succ dd w hne hpop rest =>
      rename_i d1
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
            have h_at : Jinst.At sevm.code pc .jumpi := by
              apply byteAt_jinst_at
              rw [hcode]
              exact hcheck0.1.1
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
                    have hs := popBurnBy_two_stack' hpop
                    rw [hstack] at hs
                    simp only [List.cons_append, List.cons.injEq] at hs
                    have hv : AVal.Matches ρ av2 w := hs.2.1 ▸ h1
                    have hs0 : s0 = t := h0
                    have hdt : dd = t := hs.1.symm.trans hs0
                    subst hdt
                    have hj' := live_taken hne hv hjump0.2
                    have hjp : jumpable sevm.code dd.toNat = true := by
                      rw [hcode, jumpable_eq_jumpdestOk]
                      exact hj'.1
                    exact ih rest (live_taken hne hv hcheck0.2) hj'.2 hs.2.2.symm
                      htail (hmem.of_memory_eq hpop.memory)
                      (XAt.cont (evm_jumpi_succ_of_popBurnBy h_at hne hjp hpop) h)
  | @toZero f f' k cut ih =>
    intro fs' d s run pc m a ρ S base μ hcheck hjump hstack hframe hmem post L h
    cases run with
    | succ dd w hne hpop rest => cases rest
    | zero dd hpop rest =>
      rename_i d1
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
              have h_at : Jinst.At sevm.code pc .jumpi := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck0.1.1.1.1.1
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
                      have hs := popBurnBy_two_stack' hpop
                      rw [hstack] at hs
                      simp only [List.cons_append, List.cons.injEq] at hs
                      have hv : AVal.Matches ρ av2 0 := hs.2.1 ▸ h1
                      exact ih rest (live_fall hv hcheck0.2) (live_fall hv hjump0.2) hs.2.2.symm
                        htail (hmem.of_memory_eq hpop.memory)
                        (XAt.cont (evm_jumpi_zero_of_popBurnBy h_at hpop) h)
  | @toSucc f g g' k hget cut ih =>
    intro fs' d s run pc m a ρ S base μ hcheck hjump hstack hframe hmem post L h
    cases run with
    | zero dd hpop rest => cases rest
    | succ dd w hne hpop rest =>
      rename_i d1
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
              have hmc : memCompat μ (ms.getD k []) = true := by
                simpa only [List.getD_eq_getElem?_getD] using hcheck0.1.2
              have hjump0 :
                  jumpdestOk code e.pc = true ∧
                    (av2.jumps? = some true ∨ jumpsOkNodeM code c.entries b f a' μ = true) := by
                simpa only [jumpsOkNodeM, hk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] using
                  hjump
              rcases cert_prog_of_entry c k e hk with ⟨g0, hg0⟩
              have hgg : g = g0 := Option.some.inj (hget.symm.trans hg0)
              subst hgg
              have hentry := hc k e g hk hg0
              have h_at : Jinst.At sevm.code pc .jumpi := by
                apply byteAt_jinst_at
                rw [hcode]
                exact hcheck0.1.1.1.1.1
              have hje : jumpdestOk code t.toNat = true := by
                simpa only [hcheck0.1.1.1.1.2] using hjump0.1
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
                      have hs := popBurnBy_two_stack' hpop
                      rw [hstack] at hs
                      simp only [List.cons_append, List.cons.injEq] at hs
                      have hs0 : s0 = t := h0
                      have hdt : dd = t := hs.1.symm.trans hs0
                      subst hdt
                      have hjp : jumpable sevm.code dd.toNat = true := by
                        rw [hcode, jumpable_eq_jumpdestOk]
                        exact hje
                      have hframe' : FrameMatches ρ e.frame S1 :=
                        frameMatches_gotoCompat hcheck0.1.1.2 htail
                      have hentry' :
                          checkNodeM code c.entries ms b e.rets dd.toNat e.frame (ms.getD k [])
                            g = true := by
                        simpa only [List.getD_eq_getElem?_getD, hcheck0.1.1.1.1.2] using hentry
                      exact ih rest hentry' (hj k e g hk hget) hs.2.2.symm hframe'
                        ((hmem.of_memory_eq hpop.memory).of_memCompat hmc)
                        (XAt.cont (evm_jumpi_succ_of_popBurnBy h_at hne hjp hpop) h)

/-- **The cut walk from a frame's start**: a frame whose first entry is checked at pc `0`, walked
from its start in `pre` with remaining children `L`, reaches the cut subtree `tgt` in the cut
run's halting state `s`, with the same `L`, at a pc where `tgt` is checked. -/
theorem xa_cutAt_start (hc : Cert.CheckedM code c ms b) (hj : Cert.JumpsOkM code c ms b)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {e : Entry} {f0 tgt f' : SFunc} (he : c.entries[0]? = some e) (hf : c.prog[0]? = some f0)
    (hpc : e.pc = 0) (hfr : e.frame = []) (hm0 : ms.getD 0 [] = [])
    (cut : SFunc.CutAt c.prog tgt f0 f')
    {fs' : List SFunc} {pre s post : Devm} {L : List Exec.Frame}
    (run : SFunc.RunExact fs' sevm pre f' (.halted s)) (h : XAt sevm post 0 pre L) :
    ∃ (pc' m' : Nat) (a' : List AVal) (S' : List B256) (μ' : MemMap),
      XAt sevm post pc' s L ∧ checkNodeM code c.entries ms b m' pc' a' μ' tgt = true ∧
      s.stack = S' ++ pre.stack := by
  have hf' := hc 0 e f0 he hf
  have hentry := hj 0 e f0 he hf
  rw [hm0, hpc, hfr] at hf'
  rw [hm0, hfr] at hentry
  obtain ⟨pc', m', a', S', μ', h', hchk, -, hst, -, -⟩ :=
    xa_cutAt hc hj hcode hfork cut run hf' hentry (S := []) (base := pre.stack) (ρ := 0) rfl
      (by simp only [FrameMatches, List.forall₂_nil_right_iff]) (memMatches_nil _ _) h
  exact ⟨pc', m', a', S', μ', h', hchk, hst⟩

end Cut

/-! ## Cuts along explicit steps -/

/-- One step of a cut path: an instruction, a jumpdest, the fall-through or the taken arm of a
`.branch`, the fall-through or the taken goto of a `.branchTo`. -/
inductive CutStep where
  | nx | ds | z | s | tz | ts
  deriving DecidableEq, Repr

/-- The tree `f` cut along the steps `p` (`SFunc.CutAt`'s shape). -/
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
  | _ :: _, _ => .undefined

/-- The steps `p` follow `f`'s shape, through no external instruction. -/
def SFunc.cutPathOk (fs : List SFunc) : List CutStep → SFunc → Bool
  | [], _ => true
  | .nx :: p, .next n f =>
    (match n with
     | .exec _ => false
     | _ => true) && SFunc.cutPathOk fs p f
  | .ds :: p, .dest f => SFunc.cutPathOk fs p f
  | .z :: p, .branch f _ => SFunc.cutPathOk fs p f
  | .s :: p, .branch _ g => SFunc.cutPathOk fs p g
  | .tz :: p, .branchTo f _ => SFunc.cutPathOk fs p f
  | .ts :: p, .branchTo _ k =>
    match fs[k]? with
    | some g => SFunc.cutPathOk fs p g
    | none => false
  | _ :: _, _ => false

theorem SFunc.cutAt_of_cutPathOk {fs : List SFunc} :
    ∀ (p : List CutStep) (f : SFunc), SFunc.cutPathOk fs p f = true →
      SFunc.CutAt fs (SFunc.subAt fs p f) f (SFunc.cutPath fs p f)
  | [], f, _ => .here
  | .nx :: p, .next n f, h => by
    simp only [SFunc.cutPathOk, Bool.and_eq_true] at h
    refine .next ?_ (SFunc.cutAt_of_cutPathOk p f h.2)
    intro x hx
    subst hx
    simp only [Bool.false_eq_true] at h
    exact h.1
  | .ds :: p, .dest f, h => .dest (SFunc.cutAt_of_cutPathOk p f h)
  | .z :: p, .branch f _, h => .zero (SFunc.cutAt_of_cutPathOk p f h)
  | .s :: p, .branch _ g, h => .succ (SFunc.cutAt_of_cutPathOk p g h)
  | .tz :: p, .branchTo f _, h => .toZero (SFunc.cutAt_of_cutPathOk p f h)
  | .ts :: p, .branchTo _ k, h => by
    simp only [SFunc.cutPathOk] at h
    cases hk : fs[k]? with
    | none => rw [hk] at h; cases h
    | some g =>
      rw [hk] at h
      simp only [SFunc.subAt, SFunc.cutPath, hk]
      exact .toSucc hk (SFunc.cutAt_of_cutPathOk p g h)

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
