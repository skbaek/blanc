import Blanc.Lift.LidoCircuitBreakerDeployed.Frame

/-!
# The Lido frame with the memory shape carried to the wrappers

`Frame.lean` assembles the frame with `SFunc.RunP.hoare_single_call_with_gotos`,
whose carried condition must be stable under every state-preserving change,
so nothing about memory reaches a selector wrapper: `LidoWriterSpecs`'s fields
quantify over wrapper-entry states with arbitrary memory.  The setPauser
branch walks (`setPauser_*_inv`) track memory exactly and need it well formed
and word aligned (`Mem.Wf`, `size % 32 = 0`).  Real frames enter with empty
memory (`Exec.FreshEntry`), and the dispatcher (entry 0) only pushes, compares,
loads calldata and stores the free-memory pointer, so the wrapper is entered
with `MemOK` memory.

This module carries that fact:

* `SFunc.RunP.hoare_gotos_mem`: a dispatcher Hoare lemma for trees built only
  from `instMemSafe` instructions, reverts, and gotos into `W`; it hands each
  wrapper both the state-stable condition and `MemOK` of the wrapper-entry
  memory.  Everything it needs about an instruction is `memSafe_step`.
* `LidoWriterSpecsM A`: `LidoWriterSpecs A` with `MemOK d.memory` added to both
  fields' premises, and the frame, soundness and history rungs over it.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open Blanc.ExecutionTrace

/-- Word-aligned, well-formed memory: what every real frame's memory satisfies. -/
def MemOK (μ : Mem) : Prop := Mem.Wf μ ∧ μ.size % 32 = 0

theorem memOK_empty : MemOK Mem.empty := ⟨Mem.wf_empty, rfl⟩

theorem MemOK.write_word {μ : Mem} (h : MemOK μ) (i : Nat) (w : B256) :
    MemOK (μ.write i w.toBytes) := by
  refine ⟨h.1.write i _, ?_⟩
  rw [Mem.size_write_word_at]
  split_ifs
  · exact h.2
  · rw [ceil32_eq_mul]; omega


/-- The dispatcher's instructions: none writes the world, and memory changes
only by a word store. -/
def instMemSafe : Ninst → Bool
  | .push _ _ => true
  | .reg (.dup _) => true
  | .reg .eq => true
  | .reg .gt => true
  | .reg .lt => true
  | .reg .iszero => true
  | .reg .shr => true
  | .reg .calldataload => true
  | .reg .calldatasize => true
  | .reg .callvalue => true
  | .reg .pop => true
  | .reg .mstore => true
  | _ => false

private theorem reg_run {s : Sevm} {d d' : Devm} {r : Rinst}
    (h : Ninst.Run s d (.reg r) d') : ∃ pc, Rinst.run ⟨pc, s, d⟩ r = .ok d' := by
  rcases h with ⟨xl, _, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
  exact ⟨pc, run.2.symm⟩

private theorem reg_state {s : Sevm} {d d' : Devm} {r : Rinst}
    (h1 : r ≠ .sstore) (h2 : r ≠ .tstore) (h : Ninst.Run s d (.reg r) d') :
    d'.state = d.state := by
  obtain ⟨pc, run⟩ := reg_run h
  exact (Rinst.preserves_state h1 h2 run).symm

/-- A `instMemSafe` step keeps the persistent state and `MemOK`. -/
theorem memSafe_step {s : Sevm} {d d' : Devm} {n : Ninst} (hn : instMemSafe n = true)
    (h : Ninst.Run s d n d') : d'.state = d.state ∧ (MemOK d.memory → MemOK d'.memory) := by
  cases n with
  | push xs le =>
    have hb := Devm.pushBurn_of_run (Ninst.run_push_eq h)
    exact ⟨hb.state.symm, fun hm => hb.memory ▸ hm⟩
  | reg r =>
    cases r <;>
      first
      | exact absurd hn Bool.false_ne_true
      | (refine ⟨reg_state (by intro e; cases e) (by intro e; cases e) h, fun hm => ?_⟩
         obtain ⟨x, y, -, hmem⟩ := of_run_mstore_val h
         rw [hmem]
         exact hm.write_word _ _)
      | exact ⟨reg_state (by intro e; cases e) (by intro e; cases e) h,
          fun hm => (Ninst.Hinv.inv (f := Devm.memory) h) ▸ hm⟩
  | exec _ => exact absurd hn Bool.false_ne_true
  | dupn _ => exact absurd hn Bool.false_ne_true
  | swapn _ => exact absurd hn Bool.false_ne_true
  | exchange _ => exact absurd hn Bool.false_ne_true

/-- A dispatcher-shaped tree: `instMemSafe` instructions, reverts, and conditional
gotos into `W`. -/
def treeDispMem (W : List Nat) : SFunc → Bool
  | .branch f g => treeDispMem W f && treeDispMem W g
  | .branchTo f k => decide (k ∈ W) && treeDispMem W f
  | .next n f => instMemSafe n && treeDispMem W f
  | .dest f => treeDispMem W f
  | .last .revert => true
  | _ => false

/-- **The dispatcher Hoare lemma with memory.**  A run of a `dispMem W` tree from
a state satisfying the state-stable `Φ₀` and `MemOK` ends in `Φ₁`, given that
every goto target in `W` takes such a state to `Φ₁`. -/
theorem SFunc.RunP.hoare_gotos_mem {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {fs : List SFunc} {sevm : Sevm} {W : List Nat} {Φ₀ Φ₁ : Devm → Prop}
    (hstable0 : ∀ {d d'}, d.state = d'.state → Φ₀ d → Φ₀ d')
    (hwrap : ∀ {k g}, k ∈ W → fs[k]? = some g →
      ∀ {d o}, Φ₀ d → MemOK d.memory → SFunc.RunP P fs sevm d g o → Φ₁ (Outcome.devm o))
    {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunP P fs sevm devm f o) (hf : treeDispMem W f = true)
    (h0 : Φ₀ devm) (hm : MemOK devm.memory) : Φ₁ (Outcome.devm o) := by
  induction run with
  | zero d pop run ih =>
      simp only [treeDispMem, Bool.and_eq_true] at hf
      exact ih hf.1 (hstable0 pop.state h0) (pop.memory ▸ hm)
  | succ d w hnz pop run ih =>
      simp only [treeDispMem, Bool.and_eq_true] at hf
      exact ih hf.2 (hstable0 pop.state h0) (pop.memory ▸ hm)
  | toZero d pop run ih =>
      simp only [treeDispMem, Bool.and_eq_true] at hf
      exact ih hf.2 (hstable0 pop.state h0) (pop.memory ▸ hm)
  | toSucc d w hnz lookup pop run ih =>
      simp only [treeDispMem, Bool.and_eq_true] at hf
      exact hwrap (of_decide_eq_true hf.1) lookup (hstable0 pop.state h0)
        (pop.memory ▸ hm) run
  | last hrun =>
      rename_i l
      cases l <;> first
        | exact absurd hf Bool.false_ne_true
        | exact absurd hrun Linst.not_run_revert_ok
  | next hrun run ih =>
      simp only [treeDispMem, Bool.and_eq_true] at hf
      obtain ⟨hs, hmem⟩ := memSafe_step hf.1 (hP hrun)
      exact ih hf.2 (hstable0 hs.symm h0) (hmem hm)
  | dest burn run ih =>
      simp only [treeDispMem] at hf
      exact ih hf (hstable0 burn.state h0) (burn.memory ▸ hm)
  | jump => exact absurd hf Bool.false_ne_true
  | ret => exact absurd hf Bool.false_ne_true
  | callHalt => exact absurd hf Bool.false_ne_true
  | callRet => exact absurd hf Bool.false_ne_true
  | pcAt => exact absurd hf Bool.false_ne_true

theorem entry0_dispMem : treeDispMem wrapperEntries t_0000_c0 = true := by
  decide +kernel

/-- `LidoWriterSpecs` with the wrapper-entry memory known to be `MemOK`. -/
structure LidoWriterSpecsM (A : List LidoCircuitBreaker.Entry → Sevm → Prop) : Prop where
  registerPauser : ∀ {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc},
    CoveredFork sevm.benvStat.fork → prog[59]? = some w →
    LocalApart sevm → EntryAt A sevm d → MemOK d.memory →
    lidoSpec.Pre sevm.currentTarget sevm d → SFunc.Run prog sevm d w o →
    lidoSpec.Post sevm.currentTarget sevm (Outcome.devm o)
  pause : ∀ {R : Exec.Deriv} {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc},
    CoveredFork sevm.benvStat.fork → sevm.code = code →
    Exec.FrameAdmitted sevm.currentTarget (lidoFrameEntry A) R.exc →
    LidoDeeper (lidoFrameEntry A) sevm →
    prog[49]? = some w →
    LocalApart sevm → EntryAt A sevm d → MemOK d.memory →
    lidoSpec.Pre sevm.currentTarget sevm d → SFunc.RunP (StepIn R) prog sevm d w o →
    lidoSpec.Post sevm.currentTarget sevm (Outcome.devm o)


private instance : Inhabited SFunc := ⟨.undefined⟩

section Frame

variable {A : List LidoCircuitBreaker.Entry → Sevm → Prop} {sevm : Sevm}

/-- **The frame postcondition with memory carried**: `lido_frame_post_in` over
`LidoWriterSpecsM`, for a frame entered with `MemOK` memory. -/
theorem lido_frame_post_in_mem {R : Exec.Deriv} (W : LidoWriterSpecsM A) {pre post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hcode : sevm.code = code)
    (hrun : SProg.RunP (StepIn R) prog sevm pre post)
    (hloc : LocalApart sevm) (hA : EntryAt A sevm pre) (hmem : MemOK pre.memory)
    (hadmR : Exec.FrameAdmitted sevm.currentTarget (lidoFrameEntry A) R.exc)
    (ih : LidoDeeper (lidoFrameEntry A) sevm)
    (hpre : lidoSpec.Pre sevm.currentTarget sevm pre) :
    lidoSpec.Post sevm.currentTarget sevm post := by
  obtain ⟨f, hf, run⟩ := hrun
  rw [entry0_lookup] at hf
  cases hf
  have stable0 : ∀ {d d' : Devm}, d.state = d'.state →
      (lidoSpec.Pre sevm.currentTarget sevm d ∧ EntryAt A sevm d) →
      (lidoSpec.Pre sevm.currentTarget sevm d' ∧ EntryAt A sevm d') := by
    intro d d' hs h
    refine ⟨h.1.state_eq hs.symm, ?_⟩
    unfold EntryAt
    rw [getStor_eq_of_state_eq hs.symm]
    exact h.2
  refine SFunc.RunP.hoare_gotos_mem StepIn.toRun (W := wrapperEntries)
    (Φ₀ := fun d => lidoSpec.Pre sevm.currentTarget sevm d ∧ EntryAt A sevm d)
    (Φ₁ := lidoSpec.Post sevm.currentTarget sevm) stable0 ?_ run entry0_dispMem
    ⟨hpre, hA⟩ hmem
  intro k g hk hg d o hd hdm r
  have hinv : RegInv (Devm.getStor d sevm.currentTarget) := hd.1.inv.left rfl
  have post_of : RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) →
      lidoSpec.Post sevm.currentTarget sevm (Outcome.devm o) := fun h => ⟨trivial, h⟩
  have silentCase : k ∈ silentEntries →
      lidoSpec.Post sevm.currentTarget sevm (Outcome.devm o) :=
    fun hs => post_of (silentCallee_regInv hs hg hinv (r.mono StepIn.toRun))
  simp only [wrapperEntries, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact silentCase (by decide)
  · exact post_of (setPauseDuration_wrapper_regInv hg hloc.2.1 hinv (r.mono StepIn.toRun))
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact post_of (setHeartbeatInterval_wrapper_regInv hg hloc.2.2 hinv (r.mono StepIn.toRun))
  · exact W.pause hfork hcode hadmR ih hg hloc hd.2 hdm hd.1 r
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact post_of (heartbeat_wrapper_regInv hg hloc.1 hinv (r.mono StepIn.toRun))
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact silentCase (by decide)
  · exact W.registerPauser hfork hg hloc hd.2 hdm hd.1 (r.mono StepIn.toRun)

end Frame

/-- Frame soundness, trace-admitted, over `LidoWriterSpecsM`: the frame's fresh
entry supplies the empty memory. -/
theorem lidoSpec_soundAdmitted_mem {A : List LidoCircuitBreaker.Entry → Sevm → Prop}
    (W : LidoWriterSpecsM A) (ca : Adr) : lidoSpec.SoundAdmitted ca (lidoFrameEntry A) := by
  intro sevm pre post hfork execution hrun hca admitted ih _ hpre
  subst hca
  have hin := lift_sound_in cert_check hrun.1 hfork execution
  obtain ⟨hfresh, hloc, hA⟩ := admitted.root rfl
  have hmem : MemOK pre.memory := by rw [hfresh.2]; exact memOK_empty
  exact lido_frame_post_in_mem (R := ⟨0, sevm, pre, .ok post, execution⟩) W hfork hrun.1 hin
    hloc hA hmem admitted ih hpre

theorem lidoSpec_preservesAdmitted_mem {A : List LidoCircuitBreaker.Entry → Sevm → Prop}
    (W : LidoWriterSpecsM A) (ca : Adr) : lidoSpec.PreservesAdmitted ca (lidoFrameEntry A) :=
  lidoSpec.preserves_inv_admitted ca (lidoFrameEntry A) (lidoSpec_soundAdmitted_mem W ca)

/-- **History rung over `LidoWriterSpecsM`.** -/
theorem lido_history_preserves_inv_mem {A : List LidoCircuitBreaker.Entry → Sevm → Prop}
    (W : LidoWriterSpecsM A)
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca (lidoEntry A))
    (inv : lidoSpec.StateInv ca checkpoint.state) :
    lidoSpec.StateInv ca future.state :=
  trace.stateInv_admitted_sem (lidoSpec_preservesAdmitted_mem W ca)
    ((trace.freshFrameAdmitted ca).and admitted) inv

end Blanc.Lift.LidoCircuitBreakerDeployed
