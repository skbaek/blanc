import Blanc.Lift.UniswapV2Factory.Window
import Blanc.Lift.UniswapV2Factory.Check
import Blanc.Lift.PrefixTransfer
import Blanc.Lift.CallSiteChildren
import Blanc.CallSpawnExact
import Blanc.ExecutionSettledOwnCode

/-!
# What the factory runtime spawns

`factory_children_fresh`: every direct child of a frame running the factory code from pc `0` is static,
or targets an address that had no code when the frame began, or targets `0`.  The certificate spawns only
by `CALL`, `STATICCALL` and `CREATE2` (`CursorOK.exec_spawn`).  A `CREATE2` child targets an address the
collision check found unprotected.  The only `CALL` nodes are the `initialize` call sites of the two clones
of `createPair` (`cert_windowOk`), and the window walk from the `CREATE2` node (`window_track`, with the
exact-word prefix transfer) shows that the `CALL`'s target operand is the `CREATE2` result masked to 160
bits: `0`, or the new address (`factory_call_target`).  The embedded Pair creation code is never evaluated.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune AbstractStackSafety

/-- The 160-bit address mask the factory pushes. -/
def maskBytes : Bytes := [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

def mask : B256 := Bytes.toB256 maskBytes

theorem toAdr_and_mask (v : B256) : (v &&& mask).toAdr = v.toAdr := by
  rw [show mask = ⟨⟨0, 0xffffffff⟩, ⟨0xffffffffffffffff, 0xffffffffffffffff⟩⟩ from rfl]
  obtain ⟨⟨hh, hl⟩, ⟨lh, ll⟩⟩ := v
  show ((hl &&& 4294967295).toUInt32, lh &&& 18446744073709551615, ll &&& 18446744073709551615) =
    (hl.toUInt32, lh, ll)
  rw [UInt64.toUInt32_and, show (4294967295 : UInt64).toUInt32 = -1 from rfl,
    show (18446744073709551615 : UInt64) = -1 from rfl, UInt32.and_neg_one, UInt64.and_neg_one,
    UInt64.and_neg_one]

/-- The window edge transfer: exact on the mask literal and on `AND` of known words; other literals are
forgotten. -/
def EdgeOp.transfer : EdgeOp → Pattern → Option Pattern
  | .inst (.push bs _), p => if bs = maskBytes then some (some mask :: p) else some (none :: p)
  | .inst n, p => prefixTransfer n p
  | .branch, p => some (p.drop 2)
  | .dest, p => some p

private theorem matches_drop_two {p : Pattern} {rest s : Stack} {x y : B256}
    (h : Matches (p ++ rest.map some) (x :: y :: s)) :
    ∃ rest' : Stack, Matches (p.drop 2 ++ rest'.map some) s := by
  match p, h with
  | [], h =>
      simp only [List.nil_append] at h
      have := matches_some_map_eq h
      exact ⟨s, by simpa only [List.drop_nil, List.nil_append] using matches_some_map s⟩
  | [_], h =>
      exact ⟨s, by simpa only [List.drop_succ_cons, List.drop_nil, List.nil_append] using
        matches_some_map s⟩
  | _ :: _ :: q, ⟨_, _, hq⟩ => exact ⟨rest, hq⟩

/-- **One window edge, soundly.** -/
theorem ConfStep.window {Q : ∀ pc sevm devm exn, Exec pc sevm devm exn → Prop} {fs : List SFunc}
    {sevm : Sevm} {d d' : Devm} {f f' : SFunc} {K K' : List SFunc} {o : EdgeOp}
    {p q : Pattern} {rest : Stack} (hfork : CoveredFork sevm.benvStat.fork)
    (step : ConfStep (Ninst.RunWith Q) fs sevm ⟨d, f, K⟩ ⟨d', f', K'⟩)
    (head : edgeOp f = some o) (checked : o.transfer p = some q)
    (matched : Matches (p ++ rest.map some) d.stack) :
    ∃ rest' : Stack, Matches (q ++ rest'.map some) d'.stack := by
  cases step with
  | @next _ _ n _ _ h =>
      simp only [edgeOp, Option.some.injEq] at head
      subst head
      cases n with
      | push bs fits =>
          rw [push_run_stack h.toRun]
          simp only [EdgeOp.transfer] at checked
          split at checked
          · rename_i same
            cases checked
            subst same
            exact ⟨rest, Or.inr rfl, matched⟩
          · cases checked
            exact ⟨rest, Or.inl rfl, matched⟩
      | _ =>
        simp only [EdgeOp.transfer] at checked
        exact prefixTransfer_run hfork matched checked h.toRun
  | dest burn =>
      simp only [edgeOp, Option.some.injEq] at head
      subst head
      simp only [EdgeOp.transfer, Option.some.injEq] at checked
      subst checked
      exact ⟨rest, burn.stack ▸ matched⟩
  | zero t pop =>
      simp only [edgeOp, Option.some.injEq] at head
      subst head
      simp only [EdgeOp.transfer, Option.some.injEq] at checked
      subst checked
      rw [popBurn_two_stack pop] at matched
      exact matches_drop_two matched
  | succ t w _ pop =>
      simp only [edgeOp, Option.some.injEq] at head
      subst head
      simp only [EdgeOp.transfer, Option.some.injEq] at checked
      subst checked
      rw [popBurn_two_stack pop] at matched
      exact matches_drop_two matched
  | toZero => simp only [edgeOp, reduceCtorEq] at head
  | toSucc => simp only [edgeOp, reduceCtorEq] at head
  | jump => simp only [edgeOp, reduceCtorEq] at head
  | call => simp only [edgeOp, reduceCtorEq] at head
  | ret => simp only [edgeOp, reduceCtorEq] at head
  | pcAt => simp only [edgeOp, reduceCtorEq] at head

/-- The window patterns, from the `CREATE2` result `v` on top to the `CALL` node, whose target operand
is `v &&& mask`. -/
def pats (v : B256) : List Pattern := [
  [some v],
  [none, some v],
  [none, none, some v],
  [none, none, some v],
  [none, none, none, some v],
  [none, none, none, none, some v],
  [none, none, some v],
  [some mask, none, none, some v],
  [none, some mask, none, none, some v, none, none, none, none],
  [some mask, none, some mask, none, none, some v, none, none, none, none],
  [none, some mask, none, none, some v, none, none, none, none],
  [none, none, some mask, none, none, some v, none, none, none, none],
  [none, none, none, some mask, none, none, some v, none, none, none, none],
  [none, none, some mask, none, none, some v, none, none, none, none],
  [some mask, none, none, some v, none, none, none, none],
  [none, some mask, none, none, some v, none, none, none, none],
  [some mask, none, some mask, none, none, some v, none, none, none, none],
  [none, some mask, none, none, some v, none, none, none, none],
  [none, none, some mask, none, none, some v, none, none, none, none],
  [none, none, none, some mask, none, none, some v, none, none, none, none],
  [none, none, some mask, none, none, some v, none, none, none, none],
  [some mask, none, none, some v, none, none, none, none],
  [none, none, some mask, some v, none, none, none, none],
  [none, none, some mask, some v, none, none, none, none],
  [some v, none, some mask, none, none, none, none, none],
  [none, none, some mask, none, none, none, none, none, some v],
  [none, some mask, none, none, none, none, none, some v],
  [some mask, none, none, none, none, none, none, some v],
  [some v, some mask, none, none, none, none, none, none, some v],
  [some (v &&& mask), none, none, none, none, none, none, some v],
  [none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [some (v &&& mask), some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, none, none, some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v],
  [none, some (v &&& mask), none, none, none, none, none, none, none, some (v &&& mask), none, none, none, none, some v]
]

/-- Consecutive patterns are related by consecutive edges. -/
def ChainOk : List EdgeOp → List Pattern → Prop
  | [], _ => True
  | o :: os, p :: q :: ps => o.transfer p = some q ∧ ChainOk os (q :: ps)
  | _ :: _, _ => False

theorem pats_chain (v : B256) : ChainOk windowOps (pats v) := by
  simp only [windowOps, pats, ChainOk]
  repeat (first | exact trivial | refine ⟨rfl, ?_⟩)

theorem ChainOk.get : ∀ {os : List EdgeOp} {ps : List Pattern}, ChainOk os ps →
    ∀ {j : Nat} {o : EdgeOp}, os[j]? = some o →
      ∃ p q, ps[j]? = some p ∧ ps[j + 1]? = some q ∧ o.transfer p = some q
  | [], _, _, _, _, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | _ :: _, [], h, _, _, _ => h.elim
  | _ :: _, [_], h, _, _, _ => h.elim
  | o' :: os, p :: q :: ps, ⟨step, rest⟩, j, o, h => by
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          exact ⟨p, q, rfl, rfl, step⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at h
          obtain ⟨p', q', hp, hq, t⟩ := ChainOk.get rest h
          exact ⟨p', q', by simpa only [List.getElem?_cons_succ] using hp,
            by simpa only [List.getElem?_cons_succ] using hq, t⟩

/-- The tracked word: `0`, or an address that had no code at the frame's entry `pre`. -/
def Fresh (pre : Devm) (v : B256) : Prop := v.toAdr = 0 ∨ (pre.getCode v.toAdr).toList = []

/-- At window index `k`, the node's stack matches the window pattern of some fresh `v`. -/
def WTrack (pre : Devm) (k : Nat) (F : Exec.Deriv) : Prop :=
  ∃ (v : B256) (p : Pattern) (rest : Stack), Fresh pre v ∧ (pats v)[k % 100]? = some p ∧
    Matches (p ++ rest.map some) F.devm.stack

theorem windowOps_length : windowOps.length = 59 := rfl

private theorem zero_toAdr : (0 : B256).toAdr = 0 := by
  rw [← show (0 : Adr).toB256 = (0 : B256) by decide, toAdr_toB256]

/-- One clone's window lies in `window`. -/
private theorem mem_window {e : WindowEntry} (he : e ∈ window) :
    ∃ (t5 t6 : SFunc) (base j : Nat), j < 60 ∧ (base = 0 ∨ base = 100) ∧
      e = (wtree t5 t6 j, wpred t5 t6 j, base + j) ∧
      wpred t5 t6 0 = .next (.exec .create2) (wtree t5 t6 0) ∧
      (∀ j < 59, edgeOp (wtree t5 t6 j) = windowOps[j]?) ∧
      (∀ j < 60, (wtree t5 t6 j, wpred t5 t6 j, base + j) ∈ window) := by
  simp only [window, windowOf, List.mem_append, List.mem_map, List.mem_range] at he
  rcases he with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · refine ⟨_, _, 0, j, hj, Or.inl rfl, rfl, wpred_zero_c2, windowOps_c2, fun k hk => ?_⟩
    simp only [window, windowOf, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨k, hk, rfl⟩
  · refine ⟨_, _, 100, j, hj, Or.inr rfl, rfl, wpred_zero_c10, windowOps_c10, fun k hk => ?_⟩
    simp only [window, windowOf, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨k, hk, rfl⟩

/-- **The window is carried along every edge** of a factory frame's chain. -/
theorem window_carry {R : Exec.Deriv} (fork : CoveredFork R.sevm.benvStat.fork)
    {F F' : Exec.Deriv} {κ κ' : Cursor} {e : WindowEntry}
    (chain : Exec.Deriv.ParentPrefix R F) (he : e ∈ window) (hf : κ.f = e.2.1) (hf' : κ'.f = e.1)
    (stateful : ConfStep (Ninst.RunWith (Cursor.DescOf F)) cert.prog F.sevm (κ.conf F.devm)
      (κ'.conf F'.devm))
    (track : ∀ e' ∈ window, κ.f = e'.1 → WTrack R.devm e'.2.2 F) : WTrack R.devm e.2.2 F' := by
  have nodeFork : CoveredFork F.sevm.benvStat.fork := by
    rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain]; exact fork
  obtain ⟨t5, t6, base, j, hj, hbase, rfl, zero, ops, members⟩ := mem_window he
  dsimp only at hf hf' ⊢
  cases j with
  | zero =>
      rw [zero] at hf
      have st : ConfStep (Ninst.RunWith (Cursor.DescOf F)) cert.prog F.sevm
          ⟨F.devm, .next (.exec .create2) (wtree t5 t6 0), κ.K.map Cont.f⟩
          (κ'.conf F'.devm) := hf ▸ stateful
      generalize hT : κ'.conf F'.devm = T at st
      cases st with
      | next h =>
          have hd := congrArg Conf.d hT
          dsimp only at hd
          obtain ⟨_, _, _, _, w, xs, -, hw, result⟩ := create2_run_result nodeFork h.toRun
          rw [← hd] at hw
          refine ⟨w, [some w], xs, ?_, ?_, ?_⟩
          · rcases result with rfl | ⟨na, rfl, unprotected⟩
            · exact Or.inl zero_toAdr
            · right
              rw [toAdr_toB256]
              by_contra nonempty
              have keep := (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 na nonempty
              exact unprotected (State.Protected.of_code_ne_nil (by
                change (F.devm.getCode na).toList ≠ []
                rw [keep]
                exact nonempty))
          · rw [show (base + 0) % 100 = 0 by omega]
            rfl
          · rw [hw]
            exact ⟨Or.inr rfl, matches_some_map xs⟩
  | succ j =>
      obtain ⟨v, p, rest, fresh, hp, matched⟩ := track _ (members j (by omega)) hf
      dsimp only at hp
      rw [show (base + j) % 100 = j by omega] at hp
      obtain ⟨o, ho⟩ : ∃ o, windowOps[j]? = some o :=
        ⟨windowOps[j]'(by rw [windowOps_length]; omega), List.getElem?_eq_getElem _⟩
      obtain ⟨p', q, hp', hq, transfer⟩ := ChainOk.get (pats_chain v) ho
      rw [hp] at hp'
      cases hp'
      obtain ⟨rest', matched'⟩ := ConfStep.window nodeFork stateful
        (by rw [hf]; exact (ops j (by omega)).trans ho) transfer matched
      exact ⟨v, q, rest', fresh, by rw [show (base + (j + 1)) % 100 = j + 1 by omega]; exact hq,
        matched'⟩

/-- **The factory's `CALL` target.**  At a node of the chain of a frame running the factory code from pc
`0` that decodes `CALL`, the target operand is `0` or an address with no code at the frame's entry, up to
the 160-bit mask the `CALL` applies. -/
theorem factory_call_target {R N : Exec.Deriv} (hpc : R.pc = 0) (hcode : R.sevm.code = code)
    (fork : CoveredFork R.sevm.benvStat.fork) (chain : Exec.Deriv.ParentPrefix R N)
    (hat : Ninst.At N.sevm.code N.pc (.exec .call)) :
    ∃ (g t : B256) (rest : Stack), N.devm.stack = g :: t :: rest ∧ Fresh R.devm t := by
  obtain ⟨κ, ok, checked, track⟩ := window_track cert_check cert_windowOk hpc hcode fork
    (WTrack R.devm)
    (fun chainF he hf hf' _ stateful _ track => window_carry fork chainF he hf hf' stateful track)
    chain
  obtain ⟨g', tree, -⟩ := ok.tree_of_exec hat
  have site := checked.callSite tree
  have atWindow : ∃ base, (base = 0 ∨ base = 100) ∧
      ∃ e ∈ window, κ.f = e.1 ∧ e.2.2 = base + 59 := by
    simp only [callSites, List.mem_cons, List.not_mem_nil, or_false] at site
    rcases site with here | here
    · exact ⟨0, Or.inl rfl, _, by
        simp only [window, windowOf, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl ⟨59, by omega, rfl⟩, tree.trans here, rfl⟩
    · exact ⟨100, Or.inr rfl, _, by
        simp only [window, windowOf, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨59, by omega, rfl⟩, tree.trans here, rfl⟩
  obtain ⟨base, hbase, e, he, at₀, index⟩ := atWindow
  obtain ⟨v, p, rest, fresh, hp, matched⟩ := track e he at₀
  rw [index, show (base + 59) % 100 = 59 by omega] at hp
  have shape : ∃ q, p = none :: some (v &&& mask) :: q := ⟨_, (Option.some.inj hp).symm⟩
  obtain ⟨q, rfl⟩ := shape
  match hstack : N.devm.stack, matched with
  | g :: t :: tail, ⟨_, ht, _⟩ =>
      refine ⟨g, t, tail, rfl, ?_⟩
      rw [ht.eq_of_some]
      unfold Fresh
      rw [toAdr_and_mask]
      exact fresh

/-- **What the factory spawns.**  Every direct child of a frame running the factory code from pc `0` is
static, or targets `0`, or targets an address that had no code when the frame began. -/
theorem factory_children_fresh {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork) :
    ∀ c ∈ Exec.childFrames run, c.sevm.isStatic = true ∨ c.sevm.currentTarget = 0 ∨
      (pre.getCode c.sevm.currentTarget).toList = [] := by
  intro c member
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c member
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeFork : CoveredFork N.sevm.benvStat.fork := by rw [sevmEq]; exact fork
  have target : c.sevm.currentTarget = f.inner.currentTarget := by
    rw [childEq, Frame.enter_run_currentTarget enter]
  have freshOf : ∀ {a : Adr}, ¬ State.Protected N.devm.state a → (pre.getCode a).toList = [] := by
    intro a unprotected
    by_contra nonempty
    have keep := (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 a nonempty
    exact unprotected (State.Protected.of_code_ne_nil (by
      change (N.devm.getCode a).toList ≠ []
      rw [keep]
      exact nonempty))
  obtain ⟨κ₀, -, ok₀⟩ := cursor_of_parentPrefix cert_check rfl codeEq fork chain
  rcases ok₀.exec_spawn hat with rfl | rfl | rfl
  · obtain ⟨g, t, rest, hstack, fresh⟩ := factory_call_target (R := ⟨0, sevm, pre, out, run⟩) rfl
      codeEq fork chain hat
    obtain ⟨g', c', v', ii, is, oi, os, rest', hs7⟩ := Xinst.step_call_spawn_stack nodeFork hx
    have same := hstack.symm.trans hs7
    simp only [List.cons.injEq] at same
    obtain ⟨rfl, rfl, -⟩ := same
    have hn : Ninst.step ⟨0, N.sevm, N.devm⟩ Ninst.call = .spawn f rsm 1 := by
      rw [Ninst.call, Ninst.step_exec]
      simp only [hx, XStep.toStep]
    obtain ⟨_, _, _, _, _, -, -, -, -, -, hframe, -⟩ := Ninst.step_call_spawn_exact hn hs7 nodeFork
    have childTarget : c.sevm.currentTarget = t.toAdr := by
      rw [target, hframe]
      rfl
    rw [childTarget]
    rcases fresh with zero | empty
    · exact Or.inr (Or.inl zero)
    · exact Or.inr (Or.inr empty)
  · left
    rw [childEq]
    exact (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic hx)
  · right; right
    rw [target]
    exact freshOf (Xinst.step_create2_spawn_unprotected nodeFork hx)

end Blanc.Lift.UniswapV2Factory
