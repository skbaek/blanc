import Blanc.Lift.Curve3Pool.Walk.Kit
import Blanc.Lift.FrameWalkNode
import Blanc.Lift.MemGlue
import Blanc.Lift.FrameWalkAligned
import Blanc.Lift.Curve3Pool.Callee.A
import Blanc.Lift.Curve3Pool.Callee.GetDMem

/-!
# `add_liquidity`'s walk kit: the internal calls

`add_liquidity` calls `_A` once and `get_D_mem` up to three times. The walk reaches each callee's
entry on the actual derivation and crosses it with `xa_node_span` and the callee's contract
(`a_spec`, `getDMem_spec`). The certificate's checked-node fact is a hypothesis
(`hchk : Cert.CheckedM code cert mems true`), so the walk files stay clear of `Check.lean`; the
top-level file discharges it with `cert_checkM`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift


set_option hygiene false in
/-- As `xmo`, keeping the memory's size aligned (`hA`). -/
macro "xma " pc:term:max n:term:max ri:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := $n) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  have e := $ri hR hW hA s
  clear s hR hW hA
  obtain ⟨M, _, rfl, hR, hW, hA⟩ := e))


set_option hygiene false in
/-- An aligned `MLOAD` at `o` whose word is read off `hf : WordAt img₀ o w`, past any word
writes disjoint from it on top of `img₀`. -/
macro "xml " pc:term:max o:term:max hf:term:max : tactic => `(tactic| (
  xma $pc (.reg .mload) (ri_mload_imgAtA (o := $o) rfl)
  try simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [($hf).read] at h))

/-- **Crossing a certified exec-free callee** (`xa_callee` with the checked certificate as a
hypothesis). -/
theorem xa_al_callee {k : Nat} {e : Entry} {f : SFunc} {E : List Nat}
    (hchk : Cert.CheckedM code cert mems true)
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
  have hcheck := hchk k e f hk hf
  rw [hm] at hcheck
  exact xa_node_span hchk hE hcode hfork hcheck hfree hstack hframe (memMatches_nil _ _) h

theorem al_a_entry : cert.entries[27]? = some ⟨0xa9, [.ret], 1⟩ := rfl
theorem al_a_prog : cert.prog[27]? = some t_00a9_c27 := rfl
theorem al_a_mems : mems.getD 27 [] = [] := by decide
theorem al_a_execFreeSet : ExecFreeSet cert.prog [27] = true := by decide
theorem al_a_free : t_00a9_c27.execFreeIn [27] = true := by decide

/-- **`_A` crossed**: from its entry with return address `ρ` above the caller's stack `S`, the
walk resumes at `ρ` over `aBase`, with `aChk` on top, the memory kept off `aWin`. -/
theorem xa_al_A {sevm : Sevm} {post b : Devm} {ρ : B256} {S : List B256} {M : Mem} {G : Nat}
    {s : State} {L : List Exec.Frame} (hchk : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hwf : Mem.Wf M)
    (h : XAt sevm post 0xa9 (St b (ρ :: S) M G) L) :
    ∃ v M' G', aChk s sevm.benvStat.time.toNat = some v.toNat ∧ Mem.KeepsOff M M' aWin ∧
      Mem.Wf M' ∧ (M.size % 32 = 0 → M'.size % 32 = 0) ∧
      XAt sevm post ρ.toNat (St (aBase sevm b) (v :: S) M' G') L := by
  rcases xa_al_callee hchk al_a_entry al_a_prog al_a_mems al_a_execFreeSet al_a_free hcode hfork
      (S := [ρ]) (base := S) rfl (List.Forall₂.cons rfl .nil) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, hd, -⟩ := a_spec hfork ha hwf run
    cases hd
  · obtain ⟨d, hd, v, M', G', rfl, hv, hk, hw, hs⟩ := a_spec hfork ha hwf run
    cases hd
    exact ⟨v, M', G', hv, hk, hw, hs, hx⟩

theorem al_gdm_entry : cert.entries[29]? = some ⟨0x7b7, [.ret, .unk, .unk, .unk, .unk], 1⟩ := rfl
theorem al_gdm_prog : cert.prog[29]? = some t_07b7_c29 := rfl
theorem al_gdm_mems : mems.getD 29 [] = [] := by decide

/-- **`get_D_mem` crossed**: from its entry with `ρ, b0, b1, b2, amp` above the caller's stack
`S`, the walk resumes at `ρ` over the same base with `D` on top, `getDMem` computing it, the
memory kept off `gdmWin`. -/
theorem xa_al_getDMem {sevm : Sevm} {post b : Devm} {ρ b0 b1 b2 amp : B256} {S : List B256}
    {M : Mem} {G : Nat} {L : List Exec.Frame} (hchk : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hwf : Mem.Wf M) (hsz : M.size % 32 = 0)
    (h : XAt sevm post 0x7b7 (St b (ρ :: b0 :: b1 :: b2 :: amp :: S) M G) L) :
    ∃ v M' G', getDMem ⟨b0.toNat, b1.toNat, b2.toNat⟩ amp.toNat = some v.toNat ∧
      Mem.KeepsOff M M' gdmWin ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      XAt sevm post ρ.toNat (St b (v :: S) M' G') L := by
  rcases xa_al_callee hchk al_gdm_entry al_gdm_prog al_gdm_mems gdm_execFreeSet gdm_free hcode
      hfork (S := [ρ, b0, b1, b2, amp]) (base := S) rfl
      (.cons rfl (.cons trivial (.cons trivial (.cons trivial (.cons trivial .nil))))) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, hd, -⟩ := getDMem_spec hwf hsz run
    cases hd
  · obtain ⟨d, hd, v, M', G', rfl, hv, hk, -, hw, hs⟩ := getDMem_spec hwf hsz run
    cases hd
    exact ⟨v, M', G', hv, hk, hw, hs, hx⟩

/-- **`PC`**, on the actual derivation: it pushes its own offset. -/
theorem xa_al_pc {sevm : Sevm} {post b : Devm} {S : List B256} {M : Mem} {G pc : Nat}
    {L : List Exec.Frame} (hat : Ninst.At sevm.code pc (.reg .pc))
    (h : XAt sevm post pc (St b S M G) L) :
    ∃ G', XAt sevm post (pc + 1) (St b (Nat.toB256 pc :: S) M G') L := by
  have hstep : Evm.step ⟨pc, sevm, St b S M G⟩ = Ninst.step ⟨pc, sevm, St b S M G⟩ (.reg .pc) :=
    Evm.step_next hat
  obtain ⟨exc, rfl, hg⟩ := h
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | cont h next =>
    rename_i d'
    have hs := hstep.symm.trans h
    cases Ninst.step_cont_pc hs
    have hrun : Ninst.StepRun pc sevm (St b S M G) (.reg .pc) .none (.ok d') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨trivial, trivial⟩
    have hst := pc_stepRun_stack hrun
    simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hrun
    have hr := hrun.2.symm
    simp only [Rinst.run, Rinst.runCore] at hr
    rw [pushItem_def] at hr
    have e := St.of_stackRel (Devm.pushBurn_of_run hr)
    rw [hst, St.stack] at e
    refine ⟨d'.gasLeft, ?_⟩
    rw [← e]
    exact ⟨next, rfl, lt_trans (gas_cont h) hg⟩
  | doneOk h _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    cases hx
  | runOk h _ _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    cases hx

/-- `ADDRESS`, inverted: the frame's own address pushed. -/
theorem ri_al_address {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
    (h : Ninst.Run sevm (St b S M G) (.reg .address) d) :
    ∃ G', d = St b (sevm.currentTarget.toB256 :: S) M G' := by
  have hp := of_run_address h
  have hs : d.stack = sevm.currentTarget.toB256 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

end Blanc.Lift.Curve3Pool
