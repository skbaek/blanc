import Blanc.Composition.Weth9Token
import Blanc.Lift.Weth9.Route
import Blanc.Lift.Weth9.Lift
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.InvWalkOps
import Blanc.Lift.WalkSteps
import Blanc.Lift.ByteWindowMemory

/-!
# WETH9 output inversion: the dispatcher and the free-pointer memory

A successful run of the deployed WETH9 is a run of the lifted program (`exec_lift`); this module
inverts the dispatcher exactly (the selector reaches its wrapper with the stack `[sel]` and the
dispatcher's memory), and gives memory steps that carry the free-memory pointer `0x60` while
forgetting the rest of memory.
-/

namespace Blanc.Composition.Weth9Token

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9

section Dispatch

variable {fs : List SFunc} {sevm : Sevm}

/-- One exact dispatcher comparison, inverted. -/
theorem link_cut (l : Link) {rest : SFunc} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {r : Seg} {sel : B256}
    (run : SFunc.RunCut fs sevm [] (St b (sel :: S) M G) (chain l.line (.branchTo rest l.k)) r) :
    (sel = Bytes.toB256 l.σ ∧ ∃ g G', fs[l.k]? = some g ∧
        SFunc.RunCut fs sevm [] (St b (sel :: S) M G') g r) ∨
      (sel ≠ Bytes.toB256 l.σ ∧ ∃ G', SFunc.RunCut fs sevm [] (St b (sel :: S) M G') rest r) := by
  change SFunc.RunCut fs sevm [] _ (.next (.reg (.dup 0)) (.next (.push l.σ l.hσ)
    (.next (.reg .eq) (.next (.push l.dest l.hd) (.branchTo rest l.k))))) r at run
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_eq hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  cases h with
  | toZero d0 hp k =>
    obtain ⟨-, hw, e⟩ := St.of_pop2 hp
    exact .inr ⟨fun hs => ne_of_eqc_eq hw hs.symm, _, e ▸ k⟩
  | toSuccCut _ _ _ hk _ => exact absurd hk List.not_mem_nil
  | toSucc d0 w0 hw _ hk hp k =>
    obtain ⟨-, hw', e⟩ := St.of_pop2 hp
    subst hw'
    exact .inl ⟨(eq_of_eqc_ne hw).symm, _, _, hk, e ▸ k⟩

/-- The comparisons in order, inverted exactly. -/
theorem dispatch_cut :
    ∀ (ls : List Link) {f : SFunc} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}
      {sel : B256},
      SFunc.RunCut fs sevm [] (St b (sel :: S) M G) (dispatchTree ls f) r →
      (∃ l ∈ ls, sel = Bytes.toB256 l.σ ∧ ∃ g G', fs[l.k]? = some g ∧
          SFunc.RunCut fs sevm [] (St b (sel :: S) M G') g r) ∨
        ((∀ l ∈ ls, sel ≠ Bytes.toB256 l.σ) ∧
          ∃ G', SFunc.RunCut fs sevm [] (St b (sel :: S) M G') f r)
  | [], _, _, _, _, G, _, _, run => .inr ⟨fun _ hl => absurd hl List.not_mem_nil, G, run⟩
  | l :: ls, f, b, S, M, G, r, sel, run => by
    rcases link_cut l run with ⟨hs, g, G', hg, k⟩ | ⟨hne, G', k⟩
    · exact .inl ⟨l, List.mem_cons_self, hs, g, G', hg, k⟩
    · rcases dispatch_cut ls k with ⟨l', hl', hs, g, G'', hg, k'⟩ | ⟨hne', G'', k'⟩
      · exact .inl ⟨l', List.mem_cons_of_mem _ hl', hs, g, G'', hg, k'⟩
      · refine .inr ⟨fun l'' hl'' => ?_, G'', k'⟩
        rcases List.mem_cons.mp hl'' with rfl | hl''
        · exact hne
        · exact hne' l'' hl''


set_option hygiene false in
open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- Invert one straight-line step `hd : Ninst.Run sevm (St …) n d` by the inversion lemma of the
instruction `n`, chosen syntactically (a wrong lemma is never tried, so the semantics is never
unfolded), substituting `d`. -/
elab "ri_auto " hd:ident : tactic => withMainContext do
  let ty ← instantiateMVars (← inferType (← getLocalDeclFromUserName hd.getId).toExpr)
  let mut ninst : Option Expr := none
  for a in ty.getAppArgs do
    if (← whnfR (← inferType a)).isConstOf ``Ninst then ninst := some a
  let some n := ninst | throwError "ri_auto: not an instruction step"
  let n ← whnfR n
  let fn := n.getAppFn.constName?
  let tac : TSyntax `tactic ← match fn with
    | some ``Ninst.push => `(tactic| obtain ⟨_, rfl⟩ := ri_push $hd)
    | some ``Ninst.reg =>
      let r ← whnfR n.appArg!
      match r.getAppFn.constName? with
      | some ``Rinst.dup => `(tactic| obtain ⟨_, rfl⟩ := ri_dup rfl $hd)
      | some ``Rinst.swap => `(tactic| obtain ⟨_, rfl⟩ := ri_swap rfl $hd)
      | some ``Rinst.pop => `(tactic| obtain ⟨_, rfl⟩ := ri_pop $hd)
      | some ``Rinst.and => `(tactic| obtain ⟨_, rfl⟩ := ri_and $hd)
      | some ``Rinst.add => `(tactic| obtain ⟨_, rfl⟩ := ri_add $hd)
      | some ``Rinst.sub => `(tactic| obtain ⟨_, rfl⟩ := ri_sub $hd)
      | some ``Rinst.div => `(tactic| obtain ⟨_, rfl⟩ := ri_div $hd)
      | some ``Rinst.eq => `(tactic| obtain ⟨_, rfl⟩ := ri_eq $hd)
      | some ``Rinst.lt => `(tactic| obtain ⟨_, rfl⟩ := ri_lt $hd)
      | some ``Rinst.iszero => `(tactic| obtain ⟨_, rfl⟩ := ri_iszero $hd)
      | some ``Rinst.caller => `(tactic| obtain ⟨_, rfl⟩ := ri_caller $hd)
      | some ``Rinst.callvalue => `(tactic| obtain ⟨_, rfl⟩ := ri_callvalue $hd)
      | some ``Rinst.calldatasize => `(tactic| obtain ⟨_, rfl⟩ := ri_calldatasize $hd)
      | some ``Rinst.calldataload => `(tactic| obtain ⟨_, rfl⟩ := ri_calldataload $hd)
      | some ``Rinst.mstore => `(tactic| obtain ⟨_, rfl⟩ := ri_mstore $hd)
      | some ``Rinst.mload => `(tactic| obtain ⟨_, rfl⟩ := ri_mload $hd)
      | some ``Rinst.keccak256 => `(tactic| obtain ⟨_, rfl⟩ := ri_keccak $hd)
      | _ => throwError "ri_auto: unsupported instruction {r}"
    | _ => throwError "ri_auto: unsupported instruction {n}"
  evalTactic tac

set_option hygiene false in
/-- One straight-line step of a cut walk over the run `h` (hygiene off: the walk's run is always
named `h`); the spent step and run are cleared. -/
macro "iv" : tactic => `(tactic| first
  | (obtain ⟨_, h'⟩ := ric_dest h; clear h; rename' h' => h)
  | (obtain ⟨d, hd, h'⟩ := ric_next h; clear h; ri_auto hd; clear hd; rename' h' => h))

/-- The dispatcher's memory after `mstore(0x40, 0x60)`. -/
theorem memFp_ptr : PtrMem 0x60 96 memFp := by
  unfold memFp; exact PtrMem.init _

/-- **The dispatcher, inverted.**  A successful run of the lifted WETH9 on calldata of at least four
bytes enters the wrapper of a link whose selector is the calldata selector, with the stack `[sel]`
and the dispatcher's memory, or runs the fallback. -/
theorem weth9_entry_cut {b post : Devm} {G : Nat} (hshort : ¬ shortCall sevm)
    (run : SProg.Run prog sevm (St b [] Mem.empty G) post) :
    (∃ l ∈ links, Sevm.selector sevm = Bytes.toB256 l.σ ∧ ∃ g G', prog[l.k]? = some g ∧
        SFunc.Run prog sevm (St b [Sevm.selector sevm] memFp G') g (.halted post)) ∨
      (∀ l ∈ links, Sevm.selector sevm ≠ Bytes.toB256 l.σ) := by
  obtain ⟨f, hf, run⟩ := run
  rw [entry0_lookup] at hf
  cases hf
  have h := SFunc.Run.cut run
  rw [tree_0000] at h
  simp only [chain, preamble] at h
  iv; iv; iv; iv; iv; iv; iv
  rcases ric_branch h with ⟨hz, _, h⟩ | ⟨hnz, _, -⟩
  · rw [tree_000d] at h
    simp only [chain, extractLine] at h
    iv; iv; iv; iv; iv; iv; iv
    rw [show Bytes.toB256 [0x00] = (0 : B256) from rfl, sel_extract,
      show Mem.empty.write (Bytes.toB256 [0x40]).toNat (Bytes.toB256 [0x60]).toBytes = memFp
        from rfl] at h
    rcases dispatch_cut links h with ⟨l, hl, hs, g, G', hg, k⟩ | ⟨hne, -⟩
    · exact .inl ⟨l, hl, hs, g, G', hg, k.uncut⟩
    · exact .inr hne
  · exact absurd (ltc_ne_zero hnz) hshort

end Dispatch


/-! ## `balanceOf` -/

section BalanceOf

variable {fs : List SFunc} {sevm : Sevm}

/-- The mapping getter at `0xb18`, inverted: it returns the balance slot of its argument, read
from the base it was entered at, and keeps the free-memory pointer. -/
theorem bal_callee_inv {b : Devm} {a r : B256} {S : List B256} {M : Mem} {n G : Nat} {o : Outcome}
    (hfork : CoveredFork sevm.benvStat.fork) (hM : PtrMem 0x60 n M)
    (run : SFunc.Run fs sevm (St b (a :: r :: S) M G) t_0b18_c6 o) :
    ∃ b' M' n' G', PtrMem 0x60 n' M' ∧
      o = .returned (St b' (b.getStorVal sevm.currentTarget (mapSlot a 3) :: r :: S) M' G') := by
  have h := SFunc.Run.cut run
  unfold t_0b18_c6 at h
  iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload hfork hd
  iv
  obtain ⟨G', hG⟩ := ric_ret h
  have e32 : (Bytes.toB256 [0x20]).toNat = 32 := rfl
  have e0 : (Bytes.toB256 [0x00]).toNat = 0 := rfl
  have e64 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have key := Mem.read_two_word_writes_at_raw_right_first M 0 a (Bytes.toB256 [0x03])
  rw [Nat.zero_add] at key
  rw [e32, e0, e64, key, show Bytes.toB256 [0x03] = 3 from rfl] at hG
  exact ⟨_, _, _, G', ((hM.write 32 3 (.inl (le_refl _))).write 0 a (.inl (by omega))).extend 0 64,
    Seg.done.inj hG⟩

/-- The one-word ABI tail at `0x2cc`, inverted: it returns the word on top of the stack. -/
theorem word_tail_inv {b : Devm} {v : B256} {R : List B256} {M : Mem} {n G : Nat} {o : Outcome}
    (hM : PtrMem 0x60 n M) (run : SFunc.Run fs sevm (St b (v :: R) M G) t_02cc_c22 o) :
    ∃ D, o = .halted D ∧ D.output = v.toBytes := by
  have h := SFunc.Run.cut run
  unfold t_02cc_c22 at h
  iv; iv; iv
  have e64 : (Bytes.toB256 [0x40]).toNat = 64 := rfl
  have r1 : (M.read 64 32).2 = M := hM.read_self (by have := hM.ge; omega)
  have w1 : Bytes.toB256 (M.read 64 32).1 = 0x60 := hM.word
  rw [e64, r1, w1] at h
  iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv
  have hM2 : PtrMem 0x60 _ (M.write (0x60 : B256).toNat v.toBytes) := hM.write 96 v (.inr (le_refl _))
  have r2 := hM2.read_self (i := 64) (sz := 32) (by have := hM2.ge; omega)
  have w2 : Bytes.toB256 ((M.write (0x60 : B256).toNat v.toBytes).read 64 32).1 = 0x60 := hM2.word
  rw [e64, r2, w2] at h
  iv; iv; iv; iv
  cases h with
  | last hr =>
    obtain ⟨hout, -, -⟩ := ri_return (S := R) hr
    refine ⟨_, rfl, ?_⟩
    rw [hout, show (Bytes.toB256 [0x20] + 96 - 96 : B256).toNat = 32 from by decide]
    exact Mem.read_write_word_of_wf hM.wf _ v

theorem prog_get_6 : prog[6]? = some t_0b18_c6 := by
  simp only [prog, Cert.prog, cert, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ,
    List.getElem_cons_zero]

theorem prog_get_22 : prog[22]? = some t_0295_c22 := by
  simp only [prog, Cert.prog, cert, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ,
    List.getElem_cons_zero]

/-- The `balanceOf` wrapper at `0x295`, entered from the dispatcher, inverted: the frame halts
answering the balance slot of the argument's address, read from the frame's pre-state. -/
theorem bal_wrapper_inv {pre post : Devm} {G : Nat} (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St pre [Sevm.selector sevm] memFp G) t_0295_c22 (.halted post)) :
    post.output = (pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  have h := SFunc.Run.cut run
  unfold t_0295_c22 at h
  iv; iv; iv; iv
  rcases ric_branch h with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · unfold t_029c_c22 at h
    iv; iv
    exact (ric_revert h).elim
  · unfold t_02a0_c22 at h
    iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv; iv
    obtain ⟨_, hc⟩ := ric_call prog_get_6 h
    rcases hc with ⟨D, hcal, h⟩ | ⟨D, hcal, -⟩
    · obtain ⟨b', M', n', G'', hM', hD⟩ := bal_callee_inv hfork memFp_ptr hcal
      cases hD
      obtain ⟨D, hD, hout⟩ := word_tail_inv hM' h.uncut
      cases hD
      rw [hout, ff20_and_word, show Bytes.toB256 [0x04] = 4 from rfl]
      rfl
    · obtain ⟨_, _, _, _, -, hD⟩ := bal_callee_inv hfork memFp_ptr hcal
      cases hD

/-- **Universal `balanceOf` output.**  Every successful run of the deployed WETH9 — at any gas, static
or not — whose calldata selects `balanceOf(address)` answers the balance slot of the argument's
address in the frame's pre-state. -/
theorem weth9_balanceOf_output {pre post : Devm} {G : Nat} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hshort : ¬ shortCall sevm)
    (hsel : Sevm.selector sevm = 0x70a08231)
    (run : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)) :
    post.output = (pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr)).toBytes := by
  rcases weth9_entry_cut hshort (exec_lift hcode hfork run) with ⟨l, hl, hs, g, G', hg, k⟩ | hne
  · rw [hsel] at hs
    simp only [links, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd hs (by decide)
      | (rw [prog_get_22] at hg
         cases hg
         exact bal_wrapper_inv hfork k)
  · have hm : links[6] ∈ links := List.getElem_mem (by decide)
    exact (hne _ hm (hsel.trans (by decide))).elim

end BalanceOf

end Blanc.Composition.Weth9Token
