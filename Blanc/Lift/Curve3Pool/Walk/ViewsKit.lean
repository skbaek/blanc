import Blanc.Lift.Curve3Pool.Walk.ViewsDispatch
import Blanc.Lift.Curve3Pool.Callee.A
import Blanc.Lift.FrameWalkNode
import Blanc.Lift.InvWalkCallNext

/-!
# The views' walking kit: `PC` on the derivation and bridged callees

* `xa_pcAt`: a `PC` step on the actual derivation pushes its own pc (the internal-call idiom
  `PUSH1 6; PC; ADD; PUSH2 callee; JUMP` pushes the return tag);
* `xa_calleeC`: crossing a certified exec-free callee (Bridge.lean's `xa_callee`) with the
  certificate's checkedness `hc : Cert.CheckedM code cert mems true` as a premise, so that walk
  files need not import `Check.lean`;
* `xa_vA`: `_A` (entry 27) crossed and read through its spec `a_spec`: the walk resumes at the
  return tag with the amplification `aChk s t` on the caller's stack, over `aBase`, the memory
  kept off `aWin`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {S : List B256} {M : Mem}
  {G pc : Nat}

/-- **A `PC` step** on the actual derivation pushes its pc. -/
theorem xa_pcAt {pc' : Nat} (hat : Ninst.At sevm.code pc (.reg .pc)) (hpc : pc + 1 = pc')
    (h : XAt sevm post pc (St b S M G) L) :
    ∃ G', XAt sevm post pc' (St b (Nat.toB256 pc :: S) M G') L := by
  have hstep : Evm.step ⟨pc, sevm, St b S M G⟩ = Ninst.step ⟨pc, sevm, St b S M G⟩ (.reg .pc) :=
    Evm.step_next hat
  obtain ⟨exc, rfl, hg⟩ := h
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | @cont _ _ _ _ d' _ h next =>
    have hs := hstep.symm.trans h
    cases Ninst.step_cont_pc hs
    have sr : Ninst.StepRun pc sevm (St b S M G) (.reg .pc) .none (.ok d') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨trivial, trivial⟩
    have hp := Devm.pushBurn_of_pushItem (pushItem_of_stepRun_pc sr)
    have hst : _ := hp.stack
    simp only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] at hst
    have e := St.of_stackRel hp
    rw [hst] at e
    subst hpc
    have hx : XAt sevm post (pc + 1) d' _ := ⟨next, rfl, lt_trans (gas_cont h) hg⟩
    exact ⟨_, XAt.of_eq e hx⟩
  | doneOk h _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    cases hx
  | runOk h _ _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    cases hx

set_option hygiene false in
/-- A `PC` at the walk's pc, landing at `pc'`. -/
macro "xpc " pc:term:max : tactic => `(tactic| (
  replace h := xa_pcAt (pc' := $pc) (atN hcode (by kernel_rfl)) (by rfl) h
  obtain ⟨_, h⟩ := h))

/-- **Crossing a certified exec-free callee** (`xa_callee`, Bridge.lean), with the
certificate's checkedness as a premise. -/
theorem xa_calleeC (hc : Cert.CheckedM code cert mems true) {k : Nat} {e : Entry} {f : SFunc}
    {E : List Nat}
    (hk : cert.entries[k]? = some e) (hf : cert.prog[k]? = some f)
    (hm : mems.getD k [] = []) (hE : ExecFreeSet cert.prog E = true)
    (hfree : f.execFreeIn E = true)
    {sevm : Sevm} {post d : Devm} {ρ : B256} {S base : List B256} {L : List Exec.Frame}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstack : d.stack = S ++ base) (hframe : FrameMatches ρ e.frame S)
    (h : XAt sevm post e.pc d L) :
    (SFunc.Run cert.prog sevm d f (.halted post) ∧ L = []) ∨
      ∃ (d' : Devm) (S' : List B256),
        SFunc.Run cert.prog sevm d f (.returned d') ∧ XAt sevm post ρ.toNat d' L ∧
        d'.stack = S' ++ base ∧ S'.length = e.rets := by
  have hcheck := hc k e f hk hf
  rw [hm] at hcheck
  exact xa_node_span hc hE hcode hfork hcheck hfree hstack hframe (memMatches_nil _ _) h

/-! ## `_A` -/

theorem vk_a_entry : cert.entries[27]? = some ⟨0xa9, [.ret], 1⟩ := rfl
theorem vk_a_mems : mems.getD 27 [] = [] := by decide
theorem vk_a_execFreeSet : ExecFreeSet cert.prog [27] = true := by decide
theorem vk_a_free : t_00a9_c27.execFreeIn [27] = true := by decide

/-- **`_A` crossed and read**: a walk at `_A`'s entry with the return tag `ρ` over `S` resumes
at `ρ` with `aChk s t` on `S`, over `aBase`, the memory kept off `aWin`, the same remaining
children. -/
theorem xa_vA (hc : Cert.CheckedM code cert mems true) {sevm : Sevm} {post b : Devm} {ρ : B256}
    {S : List B256} {M : Mem} {G : Nat} {L : List Exec.Frame} {s : State}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hwf : Mem.Wf M)
    (h : XAt sevm post 0xa9 (St b (ρ :: S) M G) L) :
    ∃ v M' G', XAt sevm post ρ.toNat (St (aBase sevm b) (v :: S) M' G') L ∧
      aChk s sevm.benvStat.time.toNat = some v.toNat ∧ Mem.KeepsOff M M' aWin ∧ Mem.Wf M' ∧
      (M.size % 32 = 0 → M'.size % 32 = 0) := by
  rcases xa_calleeC hc vk_a_entry prog_27 vk_a_mems vk_a_execFreeSet vk_a_free hcode hfork
      (S := [ρ]) (base := S) rfl (List.Forall₂.cons rfl .nil) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, he, -⟩ := a_spec hfork ha hwf run
    cases he
  · obtain ⟨d, he, v, M', G', rfl, hv, hk, hw, hal⟩ := a_spec hfork ha hwf run
    cases he
    exact ⟨v, M', G', hx, hv, hk, hw, hal⟩

end

end Blanc.Lift.Curve3Pool
