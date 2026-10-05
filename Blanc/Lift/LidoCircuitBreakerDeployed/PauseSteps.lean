import Blanc.Lift.LidoCircuitBreakerDeployed.Writers
import Blanc.Lift.StaticCall

/-!
# Steps the `pause` walk needs

Generic inversions the `pause` body (entry 13) uses beyond `Writers.lean`:
node inversions for runs under an arbitrary step relation (`pause` runs under
`StepIn R`, which the one `CALL` needs), the stack shape after `EXTCODESIZE`
and `CALL`, code preservation for trees with no external step, and the return
shapes of the decoders 7 and 33 (the transient-storage steps `ri_tload`,
`ri_tstore` now live in `Blanc/Lift/WalkSteps.lean`).  None mentions the
contract except the entry lemmas at the end.  Hoist candidates for `Blanc/Lift`
(the node inversions, the stack shapes, `RunP.code_of_regOnly` with `NoHalt`'s
`instRegOnly`/`treeRegOnly`/`RegOnlySet`).
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open AbstractStackSafety

/-! ## Node inversions under an arbitrary step relation -/

section RunP

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {b : Devm}
  {S : List B256} {M : Mem} {G : Nat} {f g : SFunc} {o : Outcome}

theorem rp_next {n : Ninst} {d : Devm} (run : SFunc.RunP P fs sevm d (.next n f) o) :
    ∃ d', P sevm d n d' ∧ SFunc.RunP P fs sevm d' f o := by
  cases run with
  | next h k => exact ⟨_, h, k⟩

theorem rp_dest (run : SFunc.RunP P fs sevm (St b S M G) (.dest f) o) :
    ∃ G', SFunc.RunP P fs sevm (St b S M G') f o := by
  cases run with
  | dest h k => exact ⟨_, (St.of_burn h) ▸ k⟩

theorem rp_branch {dd w : B256}
    (run : SFunc.RunP P fs sevm (St b (dd :: w :: S) M G) (.branch f g) o) :
    (w = 0 ∧ ∃ G', SFunc.RunP P fs sevm (St b S M G') f o) ∨
      (w ≠ 0 ∧ ∃ G', SFunc.RunP P fs sevm (St b S M G') g o) := by
  cases run with
  | zero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | succ d0 w0 hw h k =>
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, e ▸ k⟩

theorem rp_call {k : Nat} {dd : B256} (hk : fs[k]? = some g)
    (run : SFunc.RunP P fs sevm (St b (dd :: S) M G) (.callNext k f) o) :
    ∃ G', (∃ D, SFunc.RunP P fs sevm (St b S M G') g (.returned D) ∧
        SFunc.RunP P fs sevm D f o) ∨
      (∃ D, SFunc.RunP P fs sevm (St b S M G') g (.halted D) ∧ o = .halted D) := by
  cases run with
  | callHalt d0 hk' h hr =>
      rw [hk] at hk'
      cases hk'
      exact ⟨_, .inr ⟨_, (St.of_pop1 h).2 ▸ hr, rfl⟩⟩
  | callRet d0 hk' h hr k =>
      rw [hk] at hk'
      cases hk'
      exact ⟨_, .inl ⟨_, (St.of_pop1 h).2 ▸ hr, k⟩⟩

end RunP

/-! ## Transient storage, `EXTCODESIZE` and `CALL` -/

section Steps

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- A full-stack pattern of known words matches only that stack. -/
theorem matches_known_iff : ∀ (S rest : List B256), Matches (S.map some) rest ↔ rest = S
  | [], [] => by simp only [List.map_nil, matches_nil]
  | [], _ :: _ => by simp only [List.map_nil, Matches, reduceCtorEq]
  | _ :: _, [] => by simp only [List.map_cons, Matches, List.nil_eq, reduceCtorEq]
  | x :: S, y :: rest => by
      simp only [List.map_cons, Matches, WordMatches, reduceCtorEq, false_or, Option.some.injEq,
        List.cons.injEq, matches_known_iff S rest]
      exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

/-- A stack matching one unknown word over known words is that word over them. -/
theorem stack_of_matches {S st : List B256} (h : Matches (none :: S.map some) st) :
    ∃ v, st = v :: S := by
  cases st with
  | nil => exact h.elim
  | cons v rest => exact ⟨v, by rw [(matches_known_iff S rest).mp h.2]⟩

/-- `EXTCODESIZE` pushes one word over the popped address and keeps the world. -/
theorem extcodesize_step {x : B256} {d : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (x :: S) M G) (.reg .extcodesize) d) :
    (∃ v, d.stack = v :: S) ∧ d.state = b.state := by
  have hm : Matches ((none :: S.map some) : Pattern) (St b (x :: S) M G).stack :=
    ⟨Or.inl rfl, (matches_known_iff S S).mpr rfl⟩
  refine ⟨stack_of_matches (ninstTransfer_run hfork hm rfl h), ?_⟩
  rcases of_run_reg h with ⟨pc, run⟩
  have hf := Rinst.run_instructionFrame pc sevm (St b (x :: S) M G) .extcodesize
    (by intro e; cases e) (by intro e; cases e)
  rw [run] at hf
  exact hf.state.symm

/-- `CALL` leaves one flag word over the seven popped arguments. -/
theorem call_stack {g t v ai as ro rs : B256} {d : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (g :: t :: v :: ai :: as :: ro :: rs :: S) M G) (.exec .call) d) :
    ∃ flag, d.stack = flag :: S := by
  have hm : Matches ((none :: none :: none :: none :: none :: none :: none :: S.map some) :
      Pattern) (St b (g :: t :: v :: ai :: as :: ro :: rs :: S) M G).stack :=
    ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
      (matches_known_iff S S).mpr rfl⟩
  exact stack_of_matches (ninstTransfer_run hfork hm rfl h)

end Steps

/-! ## Code is kept by runs with no external step -/

private theorem code_of_step {sevm : Sevm} {d d' : Devm} {n : Ninst} (hn : instRegOnly n = true)
    (h : Ninst.Run sevm d n d') : Devm.getCode d' = Devm.getCode d := by
  cases n with
  | reg r => exact (Ninst.Hinv.inv (f := Devm.getCode) h).symm
  | push xs le => exact (Ninst.Hinv.inv (f := Devm.getCode) h).symm
  | exec _ => exact absurd hn Bool.false_ne_true
  | dupn _ => exact absurd hn Bool.false_ne_true
  | swapn _ => exact absurd hn Bool.false_ne_true
  | exchange _ => exact absurd hn Bool.false_ne_true

/-- A run of a `treeRegOnly` tree whose references close in a `RegOnlySet` keeps
every account's code. -/
theorem SFunc.RunP.code_of_regOnly {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc} {S : List Nat}
    (hS : RegOnlySet fs S = true) {sevm : Sevm} {devm : Devm} {f : SFunc} {o : Outcome}
    (hf : treeRegOnly f = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.RunP P fs sevm devm f o) :
    Devm.getCode (Outcome.devm o) = Devm.getCode devm := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      treeRegOnly g = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  have ofState : ∀ {a c : Devm}, a.state = c.state → Devm.getCode a = Devm.getCode c :=
    fun h => funext (getCode_eq_of_state_eq h)
  induction run with
  | zero d pop run ih =>
      simp only [treeRegOnly, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact (ih hf.1 hrefs.1).trans (ofState pop.state).symm
  | succ d w hnz pop run ih =>
      simp only [treeRegOnly, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact (ih hf.2 hrefs.2).trans (ofState pop.state).symm
  | toZero d pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      exact (ih hf hrefs.2).trans (ofState pop.state).symm
  | toSucc d w hnz lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact (ih ht.1 ht.2).trans (ofState pop.state).symm
  | last hrun =>
      rename_i l
      cases l <;> first
        | exact absurd hf Bool.false_ne_true
        | exact absurd hrun Linst.not_run_revert_ok
  | next hrun run ih =>
      simp only [treeRegOnly, Bool.and_eq_true] at hf
      exact (ih hf.2 hrefs).trans (code_of_step hf.1 (hP hrun))
  | dest burn run ih =>
      exact (ih hf hrefs).trans (ofState burn.state).symm
  | jump d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, List.all_nil, Bool.and_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs) lookup
      exact (ih ht.1 ht.2).trans (ofState pop.state).symm
  | ret d pop => exact (ofState pop.state).symm
  | callHalt d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact (ih ht.1 ht.2).trans (ofState pop.state).symm
  | callRet d lookup pop run tail ihRun ihTail =>
      simp only [treeRegOnly] at hf
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact (ihTail hf hrefs.2).trans ((ihRun ht.1 ht.2).trans (ofState pop.state).symm)
  | pcAt hrun _ run ih =>
      simp only [treeRegOnly] at hf
      simp only [SFunc.refs] at hrefs
      exact (ih hf hrefs).trans (code_of_step (n := .reg .pc) rfl (hP hrun))

/-! ## Entry 32 at an arbitrary return tag -/

/-- **`setPauser(t, 0)` (entry 32) from a caller whose return tag is `ra`**: a
successful run from well-formed memory preserves `RegInv`, keeps code, and
returns to `base`, given the branch keys faithful at `2 ^ 160`.  The four
`setPauser_*_inv` branch walks prove it for an arbitrary `ra` (`entry32Spec`);
`pause` calls entry 32 with tag `0x6ce`. -/
def Entry32Spec (ra : B256) : Prop :=
  ∀ {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {t : B256} {base : List B256} {post : Devm}
    {entries : List Entry},
    CoveredFork sevm.benvStat.fork → MemOK M →
    RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries →
    canonicalAddress t →
    (t ≠ 0 → RegistryKeysFaithful (2 ^ 160) (setPauserKeys entries t 0)) →
    SFunc.Run prog sevm (St b (0 :: t :: 3 :: ra :: base) M G) t_0934_c32 (.returned post) →
    RegInv (Devm.getStor post sevm.currentTarget) ∧
      Devm.getCode post = Devm.getCode b ∧ ∃ b' M' G', post = St b' base M' G'

theorem entry32_code {sevm : Sevm} {d post : Devm}
    (run : SFunc.Run prog sevm d t_0934_c32 (.returned post)) :
    Devm.getCode post = Devm.getCode d := by
  have h := (List.all_eq_true.mp setPauserClosure_regOnly) 32 (by decide)
  rw [show prog[32]? = some t_0934_c32 from rfl] at h
  simp only [Bool.and_eq_true] at h
  exact SFunc.RunP.code_of_regOnly id setPauserClosure_regOnly h.1 h.2 run

theorem entry32Spec (ra : B256) : Entry32Spec ra := by
  intro hfork hmem hw ht hkeys run
  obtain ⟨hinv, hpost⟩ := setPauser_step hfork hmem hw ht (canonicalAddress_zero) hkeys run
  exact ⟨hinv, by rw [entry32_code run]; rfl, hpost⟩
where
  canonicalAddress_zero : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num only

/-! ## The single-address decoder (entry 7) and the bool decoder (entry 33) -/

/-- Entry 7 (`abi_decode_address` over `calldatasize`) returns the canonical
calldata word at 4. -/
theorem entry7_ret {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {cds ra : B256}
    {xs : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b ((4 : B256) :: cds :: ra :: xs) M G) t_0fec_c7
      (.returned D)) :
    canonicalAddress (Sevm.dataWord sevm 4) ∧ ∃ G', D = St b (Sevm.dataWord sevm 4 :: xs) M G' := by
  have run := run.cut
  unfold t_0fec_c7 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup (w := cds) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨z, G7, rfl⟩ := ri_slt s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G10, run⟩ | ⟨-, G10, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run (by decide)).elim
  unfold t_0ffc_c7 at run
  obtain ⟨G11, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_dup (w := (4 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨G15, hcall⟩ := ric_call (g := t_0f93_c29) rfl run
  rcases hcall with ⟨D1, r1, run⟩ | ⟨D1, -, hr⟩
  swap
  · cases hr
  obtain ⟨ht, G16, rfl⟩ := entry29_ret r1
  refine ⟨ht, ?_⟩
  unfold t_1005_c7 at run
  obtain ⟨G17, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_swap (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_swap (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_pop s1
  obtain ⟨G23, hr⟩ := ric_ret run
  injection hr with hr
  injection hr with hr
  simp only [List.set] at hr
  exact ⟨G23, hr⟩

/-- Entry 33 (`abi_decode_bool`) returns one word above the caller's stack, over
the same base. -/
theorem entry33_ret {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {h e ra : B256}
    {xs : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b (h :: e :: ra :: xs) M G) t_10bb_c33 (.returned D)) :
    ∃ v M' G', D = St b (v :: xs) M' G' := by
  have run := run.cut
  unfold t_10bb_c33 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_dup (w := h) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup (w := e) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨z, G7, rfl⟩ := ri_slt s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G10, run⟩ | ⟨-, G10, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run (by decide)).elim
  unfold t_10cb_c33 at run
  obtain ⟨G11, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_dup (w := h) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G20, run⟩ | ⟨-, G20, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run (by decide)).elim
  unfold t_1005_c33 at run
  obtain ⟨G21, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_swap (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_swap (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_pop s1
  obtain ⟨G27, hr⟩ := ric_ret run
  injection hr with hr
  injection hr with hr
  simp only [List.set] at hr
  exact ⟨_, _, G27, hr⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
