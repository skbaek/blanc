import Blanc.Lift.CursorSourceRun

namespace Blanc.Lift
open Jaune

/-- A source return retains the original successful continuation execution and
the cursor checked against the remaining actual continuation stack. -/
def CursorSourceReturn (code : ByteArray) (c : Cert)
    (F : Exec.Deriv) (κ : Cursor) (post : Devm) : Prop :=
  ∃ (continuation : Cont) (tail : List Cont) (state : Devm)
    (run : Exec (Cont.tagOf κ.K).toNat F.sevm state (.ok post)),
    κ.K = continuation :: tail ∧ continuation.live = true ∧
    Exec.Deriv.lt ⟨(Cont.tagOf κ.K).toNat, F.sevm, state, .ok post, run⟩ F ∧
    SFunc.RunP (StepIn F) c.prog F.sevm F.devm κ.f (.returned state) ∧
    CursorOK code c ⟨(Cont.tagOf κ.K).toNat, F.sevm, state, .ok post, run⟩
      ⟨continuation.f, continuation.tag.toNat,
        List.replicate continuation.rets .unk ++ continuation.a, continuation.m, tail⟩

/-- A checked actual successful cursor either halts with its own result, or
returns through its actual checked continuation. -/
theorem CursorOK.sourceRunReturn {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {κ : Cursor} (checked : Cert.check code c = true)
    (placed : CursorOK code c F κ) {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    SFunc.RunP (StepIn F) c.prog F.sevm F.devm κ.f (.halted post) ∨
      CursorSourceReturn code c F κ post := by
  obtain ⟨S, base, stack, frame, continuations⟩ := placed.stack
  have check : checkNodeM code c.entries [] false κ.m F.pc κ.a [] κ.f = true := by
    rw [placed.pc_eq, ← checkNode_eq_checkNodeM]
    exact placed.check
  have source := node_soundM (Cert.checkedM_of_check checked) F F
    (fun r member => List.mem_cons_of_mem _ member) post success placed.code_eq fork
    κ.m κ.a κ.f (Cont.tagOf κ.K) S base [] check stack frame (memMatches_nil _ _)
  rcases source with halted | ⟨ret, state, returned, actual, smaller, run, stateStack, arity⟩
  · exact Or.inl halted
  · have present : AVal.ret ∈ κ.a := by simpa only [RetIn, List.map_nil,
      List.not_mem_nil, or_false] using ret
    obtain ⟨k, K, sameK, live, count⟩ := placed.retOK present
    rw [sameK] at continuations
    cases continuations with
    | @cons k K S0 rest callerFrame callerRet callerCheck restOK =>
      refine Or.inr ⟨k, K, state, actual, sameK, live, smaller, run, ?_⟩
      refine ⟨placed.code_eq, ?_, callerCheck live, ?_, ?_⟩
      · change (Cont.tagOf κ.K).toNat = k.tag.toNat
        rw [sameK]
        rfl
      · intro member
        apply callerRet
        exact (List.mem_append.mp member).resolve_left (by
          intro inUnknown
          have := List.eq_of_mem_replicate inUnknown
          cases this)
      · refine ⟨returned ++ S0, rest, ?_, ?_, restOK⟩
        · rw [stateStack, List.append_assoc]
        · have unknown := frameMatches_unk_length (ρ := Cont.tagOf K) returned
          rw [arity, ← count] at unknown
          exact List.rel_append unknown callerFrame

end Blanc.Lift
