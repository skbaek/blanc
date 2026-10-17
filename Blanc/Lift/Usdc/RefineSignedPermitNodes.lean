import Blanc.Lift.Usdc.RefineSignedPermitFrames
import Blanc.Lift.Usdc.RefineSignedPermitKeep
import Blanc.Lift.Usdc.RefineSignedAuth

/-!
# The library-call nodes of `permit` and `cancelAuthorization` (U6e4)

The only external instruction of a successful `permit` or `cancelAuthorization` frame is the
library `DELEGATECALL`.  `cancel_node`: it is reached with the frame's starting world
(`Reach.preExec_state` from the wrapper on).  `permit_node`: `_permit` bumps the owner's nonce
before its digest, so the reach is walked exactly up to that store (`rstepX`, `rr_shuffle`,
`rr_call_silent`) and `Reach.preExec_state` runs from just after it: the world at the node is the
starting world with the owner's nonce word written.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

theorem route_permit_vrs : dispTree.selWalk 0xd505accf = .inl (0xd505accf, 132) := rfl
theorem route_permit_bytes : dispTree.selWalk 0x9fd5a6cf = .inl (0x9fd5a6cf, 149) := rfl
theorem route_cancel_vrs : dispTree.selWalk 0x5a049a70 = .inl (0x5a049a70, 159) := rfl
theorem route_cancel_bytes : dispTree.selWalk 0xb7b72899 = .inl (0xb7b72899, 136) := rfl

/-! ## cancelAuthorization: no store before the library call -/

def cancelW0 : List Nat := [6, 76, 77, 78, 79, 106, 107, 110]
def cancelW : List Nat := [11, 28, 52, 89, 97, 111, 117, 136, 159]
def cancelE : List Nat := [4]

theorem cancel_silent : SilentSet cert.prog cancelW0 = true := by decide +kernel
theorem cancel_execFree : ExecFreeSet cert.prog cancelE = true := by decide +kernel
theorem cancel_preExec :
    PreExecSet cert.prog (· == .delegatecall) cancelW0 cancelW cancelE = true := by
  decide +kernel

/-- **The library call of a cancellation frame**: every external-instruction node of its own chain
is a `DELEGATECALL` reached with the frame's starting world. -/
theorem cancel_node {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) {σ : B256} {j : Nat}
    (sel : Blanc.Sevm.selector sevm = σ) (route : dispTree.selWalk σ = .inl (σ, j))
    (hj : j ∈ cancelW) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall ∧ N.devm.state = pre.state := by
  intro N hN x hx
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix Impl.cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl code fork hN
  obtain ⟨g0, hf0, -⟩ := ok.tree_of_exec hx
  have hT : AtExec (κ.conf N.devm) := ⟨x, g0, hf0⟩
  change Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) implProg sevm ⟨pre, Impl.t_0000_c0, []⟩
    (κ.conf N.devm) at reach
  obtain ⟨M, G, dreach⟩ := impl_preamble_reach StepIn.toRun reach hT
  rw [sel] at dreach
  obtain ⟨-, g, G', hg, greach⟩ := Reach.selWalk_inl StepIn.toRun route dreach hT
  obtain ⟨hs, x', f', hf, hx'⟩ := Reach.preExec_state StepIn.toRun cancel_execFree cancel_silent
    cancel_preExec greach hT (.inl ⟨PreExecSet.lookup cancel_preExec hj hg,
      fun _ h => absurd h List.not_mem_nil⟩)
  have e : SFunc.next (.exec x) g0 = .next (.exec x') f' := hf0.symm.trans hf
  injection e with e1
  injection e1 with e2
  subst e2
  exact ⟨by simpa only [beq_iff_eq] using hx', hs⟩

/-! ## permit: the nonce store before the library call -/

/-- One straight-line step of a reach, also over `SHL` and `TIMESTAMP`. -/
macro "rstepX " h:ident t:ident : tactic => `(tactic| first
  | rstep $h $t
  | (have h' := rr_next $h $t; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     first
     | (obtain ⟨_, e⟩ := ri_shl (StepIn.toRun hd); subst e; clear hd)
     | (obtain ⟨_, e⟩ := ri_timestamp (StepIn.toRun hd); subst e; clear hd)))

/-- Enter an internal call whose continuation is exec-free: the target lies in the callee. -/
macro "rinto " h:ident t:ident : tactic => `(tactic|
  (have h' := rr_callInto familyFree_execFree rfl (by decide)
      (fun _ hs => absurd hs List.not_mem_nil) $h $t
   clear $h
   obtain ⟨_, T', $h:ident, eT⟩ := h'
   subst eT
   replace $t:ident := AtExec.below.mp $t))

theorem st_state' (b : Devm) (S : List B256) (M : Mem) (G : Nat) : (St b S M G).state = b.state :=
  rfl

theorem rr_branchTo {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {f g : SFunc} {k : Nat} {K : List SFunc}
    {T : Conf} {dd w : B256} (hk : fs[k]? = some g)
    (run : Reach P fs sevm ⟨St b (dd :: w :: S) M G, .branchTo f k, K⟩ T) (hT : AtExec T) :
    (w = 0 ∧ ∃ G', Reach P fs sevm ⟨St b S M G', f, K⟩ T) ∨
      (w ≠ 0 ∧ ∃ G', Reach P fs sevm ⟨St b S M G', g, K⟩ T) := by
  rcases Reach.branchTo run hT with ⟨t, d', pop, rest⟩ | ⟨t, w0, g', d', hw, hk', pop, rest⟩
  · obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    exact .inl ⟨hw, _, e ▸ rest⟩
  · rw [hk] at hk'
    cases hk'
    obtain ⟨-, hw', e⟩ := St.of_pop2 pop
    exact .inr ⟨hw' ▸ hw, _, e ▸ rest⟩

/-- `_permit`'s region after the nonce store: `_hashTypedDataV4` (79) is silent, the copy loop (80)
and the call site (9) run up to the library call, after which only `_approve` (81) is left. -/
def permitW0 : List Nat := [79]
def permitW : List Nat := [9, 80]
def permitE : List Nat := [6, 76, 77, 78, 81, 106, 107]

theorem permit_silent : SilentSet cert.prog permitW0 = true := by decide +kernel
theorem permit_execFree : ExecFreeSet cert.prog permitE = true := by decide +kernel
theorem permit_preExec :
    PreExecSet cert.prog (· == .delegatecall) permitW0 permitW permitE = true := by
  decide +kernel
theorem permit_after_store :
    (SFunc.lineDrop 27 t_4738_c8).preExec (· == .delegatecall) permitW0 permitW permitE = true := by
  decide +kernel

/-- **`_permit`'s body on a reach to its library call** (entry 8, from its deadline flag): the
world at the call is the entry's with the owner's nonce word written. -/
theorem e8_reach {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {fl x0 x1 x2 x3 x4 ret : B256} {T : Conf} (fork : CoveredFork sevm.benvStat.fork)
    (h : Reach (StepIn R) cert.prog sevm
      ⟨St b (fl :: x0 :: x1 :: x2 :: x3 :: x4 :: ret :: S) M G, t_46c0_c8, []⟩ T)
    (hT : AtExec T) :
    (∃ w, Devm.getStor T.d sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (nonceSlot x4.toAdr) w) ∧
      ∃ f', T.f = .next (.exec .delegatecall) f' := by
  repeat rstep h hT
  rbranch h hT
  repeat rstep h hT
  obtain ⟨b1, Y, M1, G1, hs1, hY, h⟩ := rr_call_silent StepIn.toRun Impl.cert_check fork
    (Sk := sil78) (E := permitE) sil78_silent permit_execFree (by decide) (by decide)
    (e := ⟨0x4276, [.ret], 1⟩) rfl rfl (by exact List.Forall₂.cons rfl .nil) hT h
  match Y, hY, h with
  | [y], _, h =>
    iterate 27 rstep h hT
    obtain ⟨hs, x', f', hf, hx'⟩ := Reach.preExec_state StepIn.toRun permit_execFree permit_silent
      permit_preExec h hT (.inl ⟨permit_after_store, fun _ h => absurd h List.not_mem_nil⟩)
    obtain rfl : x' = .delegatecall := by simpa only [beq_iff_eq] using hx'
    simp only [st_state'] at hs
    refine ⟨⟨(Devm.getStor b sevm.currentTarget).get (nonceSlot x4.toAdr) + 1, ?_⟩, f', hf⟩
    rw [getStor_of_state hs, afterSstore_getStor_self, afterSload_getStor, getStor_of_state hs1,
      keccak_scratch, word_ff20, gsv, getStor_of_state hs1]
    rfl

/-- **`_permit(owner, spender, value, deadline, signature)` on a reach** (entry 94, with its goto
into entry 8). -/
theorem e94_reach {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {x0 x1 x2 x3 x4 ret : B256} {T : Conf} (fork : CoveredFork sevm.benvStat.fork)
    (h : Reach (StepIn R) cert.prog sevm
      ⟨St b (x0 :: x1 :: x2 :: x3 :: x4 :: ret :: S) M G, t_4692_c94, []⟩ T)
    (hT : AtExec T) :
    (∃ w, Devm.getStor T.d sevm.currentTarget =
        (Devm.getStor b sevm.currentTarget).set (nonceSlot x4.toAdr) w) ∧
      ∃ f', T.f = .next (.exec .delegatecall) f' := by
  repeat rstep h hT
  rcases rr_branchTo rfl h hT with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · rstep h hT
    rstepX h hT
    iterate 3 rstep h hT
    exact e8_reach fork h hT
  · exact e8_reach fork h hT

/-- From a node of a frame's own chain to a reach of the certificate at the selector's wrapper. -/
theorem node_reach {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) {σ : B256} {j : Nat}
    (sel : Blanc.Sevm.selector sevm = σ) (route : dispTree.selWalk σ = .inl (σ, j))
    {N : Exec.Deriv} (hN : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N) {x : Xinst}
    (hx : Ninst.At N.sevm.code N.pc (.exec x)) :
    ∃ T g M G, AtExec T ∧ T.d = N.devm ∧ (∀ x' f', T.f = .next (.exec x') f' → x' = x) ∧
      cert.prog[j]? = some g ∧
      Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) cert.prog sevm
        ⟨St pre (σ :: pre.stack) M G, g, []⟩ T := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix Impl.cert_check
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl code fork hN
  obtain ⟨g0, hf0, -⟩ := ok.tree_of_exec hx
  have hT : AtExec (κ.conf N.devm) := ⟨x, g0, hf0⟩
  change Reach (StepIn ⟨0, sevm, pre, .ok post, run⟩) implProg sevm ⟨pre, Impl.t_0000_c0, []⟩
    (κ.conf N.devm) at reach
  obtain ⟨M, G, dreach⟩ := impl_preamble_reach StepIn.toRun reach hT
  rw [sel] at dreach
  obtain ⟨-, g, G', hg, greach⟩ := Reach.selWalk_inl StepIn.toRun route dreach hT
  refine ⟨_, g, M, G', hT, rfl, fun x' f' hf => ?_, hg, greach⟩
  have e : SFunc.next (.exec x) g0 = .next (.exec x') f' := hf0.symm.trans hf
  injection e with e1
  injection e1 with e2
  exact e2.symm

theorem ff20_word4 (sevm : Sevm) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        Sevm.dataWord sevm (Bytes.toB256 [4])).toAdr = (Sevm.dataWord sevm 4).toAdr := by
  rw [ff20_word, toAdr_toB256]
  rfl

/-- **The library call of `permit(owner, spender, value, deadline, v, r, s)`**: every
external-instruction node of the frame's chain is a `DELEGATECALL`, reached with the starting
world plus a write of the owner's nonce word. -/
theorem permit_node_vrs {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xd505accf) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall ∧
        ∃ w, N.devm.state.getStor sevm.currentTarget =
          (pre.state.getStor sevm.currentTarget).set (nonceSlot (Sevm.dataWord sevm 4).toAdr) w := by
  intro N hN x hx
  obtain ⟨T, g, M, G, hT, hd, hxT, hg, h⟩ := node_reach run code fork sel route_permit_vrs hN hx
  cases hg
  rw [← hd]
  clear hd hN hx
  repeat rstep h hT
  rbranch h hT
  repeat rstep h hT
  rinto h hT
  repeat rstep h hT
  rbranch h hT
  repeat rstep h hT
  rinto h hT
  repeat rstepX h hT
  rinto h hT
  obtain ⟨⟨w, hw⟩, f', hf⟩ := e94_reach fork h hT
  refine ⟨(hxT _ _ hf).symm, w, ?_⟩
  rw [ff20_word4, afterSload_getStor] at hw
  exact hw

theorem rr_seg_w149 {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {T : Conf}
    {K : List SFunc} (fork : CoveredFork sevm.benvStat.fork) (hT : AtExec T)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : B256} {S : List B256}
    (run : Reach (StepIn R) cert.prog sevm ⟨St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 ::
      x8 :: x9 :: S) M G, t_0be5_c149, K⟩ T) :
    ∃ b' u0 M' G', b'.state = b.state ∧ Reach (StepIn R) cert.prog sevm
      ⟨St b' (Nat.toB256 0x2e53 :: u0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: S) M' G',
        .callNext 41 t_0489_c149, K⟩ T := by
  obtain ⟨b', Y, M', G', hs, hY, h⟩ := rr_shuffle StepIn.toRun
    (X := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]) fork hT seg_w149_check rfl run
  carried_out hY h
  exact ⟨b', _, M', G', hs, h⟩

/-- **The library call of `permit(owner, spender, value, deadline, signature)`**, as
`permit_node_vrs`. -/
theorem permit_node_bytes {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x9fd5a6cf) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .delegatecall ∧
        ∃ w, N.devm.state.getStor sevm.currentTarget =
          (pre.state.getStor sevm.currentTarget).set (nonceSlot (Sevm.dataWord sevm 4).toAdr) w := by
  intro N hN x hx
  obtain ⟨T, g, M, G, hT, hd, hxT, hg, h⟩ := node_reach run code fork sel route_permit_bytes hN hx
  cases hg
  rw [← hd]
  clear hd hN hx
  repeat rstep h hT
  rbranch h hT
  repeat rstep h hT
  rbranch h hT
  have h' := rr_seg_w149 fork hT h
  clear h
  obtain ⟨b1, u0, M1, G1, hs1, h⟩ := h'
  rinto h hT
  repeat rstep h hT
  rbranch h hT
  repeat rstep h hT
  rinto h hT
  obtain ⟨⟨w, hw⟩, f', hf⟩ := e94_reach fork h hT
  refine ⟨(hxT _ _ hf).symm, w, ?_⟩
  rw [ff20_word4, afterSload_getStor, getStor_of_state hs1] at hw
  exact hw

end Blanc.Lift.Usdc
