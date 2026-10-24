import Blanc.Lift.UniswapV2Factory.CallShape
import Blanc.Lift.HistWindow

/-!
# What the factory runtime spawns, from rule facts

`CallShape.lean` states the factory's call shape under a covered fork. The forms here read only
`rules.stateGas = none` and `rules.op.create2 = true`, so they hold at Muir Glacier, the fork of the
Pair's deployment block:

* `ConfStep.windowH`, `window_carryH` — the window edges and their carry;
* `factory_call_targetH` — the `CALL` target operand is `0` or an address with no code at the
  frame's entry, up to the 160-bit mask;
* `factory_children_freshH` — every direct child of a frame running the factory code from pc `0`
  is static, or targets `0`, or targets an address that had no code when the frame began.

Each is its covered counterpart with the covered-fork facts replaced by the rule facts it reads,
over the shared forms of `HistWindow.lean`.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune AbstractStackSafety

private theorem zero_toAdr : (0 : B256).toAdr = 0 := by
  rw [← show (0 : Adr).toB256 = (0 : B256) by decide, toAdr_toB256]

/-- An entry of one clone's window is that clone's tree, predecessor and index at some `j < 60`,
and every index of the clone has its entry. -/
theorem mem_windowOf {t5 t6 : SFunc} {base : Nat} {e : WindowEntry} (he : e ∈ windowOf t5 t6 base) :
    ∃ j, j < 60 ∧ e = (wtree t5 t6 j, wpred t5 t6 j, base + j) ∧
      ∀ k < 60, (wtree t5 t6 k, wpred t5 t6 k, base + k) ∈ windowOf t5 t6 base := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  exact ⟨j, List.mem_range.mp hj, rfl, fun k hk => List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩⟩

/-- An entry of `window` is one clone's (from `mem_windowOf`), with that clone's window facts. -/
private theorem mem_window {e : WindowEntry} (he : e ∈ window) :
    ∃ (t5 t6 : SFunc) (base j : Nat), j < 60 ∧ (base = 0 ∨ base = 100) ∧
      e = (wtree t5 t6 j, wpred t5 t6 j, base + j) ∧
      wpred t5 t6 0 = .next (.exec .create2) (wtree t5 t6 0) ∧
      (∀ j < 59, edgeOp (wtree t5 t6 j) = windowOps[j]?) ∧
      (∀ j < 60, (wtree t5 t6 j, wpred t5 t6 j, base + j) ∈ window) := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨j, hj, rfl, members⟩ := mem_windowOf he
    exact ⟨_, _, 0, j, hj, Or.inl rfl, rfl, wpred_zero_c2, windowOps_c2,
      fun k hk => List.mem_append_left _ (members k hk)⟩
  · obtain ⟨j, hj, rfl, members⟩ := mem_windowOf he
    exact ⟨_, _, 100, j, hj, Or.inr rfl, rfl, wpred_zero_c10, windowOps_c10,
      fun k hk => List.mem_append_right _ (members k hk)⟩

/-- **One window edge, soundly, from `rules.stateGas = none`.** -/
theorem ConfStep.windowH {Q : ∀ pc sevm devm exn, Exec pc sevm devm exn → Prop} {fs : List SFunc}
    {sevm : Sevm} {d d' : Devm} {f f' : SFunc} {K K' : List SFunc} {o : EdgeOp}
    {p q : Pattern} {rest : Stack} (hsg : sevm.benvStat.rules.stateGas = none)
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
        exact prefixTransfer_runH hsg matched checked h.toRun
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
      exact matches_append_drop 2 matched
  | succ t w _ pop =>
      simp only [edgeOp, Option.some.injEq] at head
      subst head
      simp only [EdgeOp.transfer, Option.some.injEq] at checked
      subst checked
      rw [popBurn_two_stack pop] at matched
      exact matches_append_drop 2 matched
  | toZero => simp only [edgeOp, reduceCtorEq] at head
  | toSucc => simp only [edgeOp, reduceCtorEq] at head
  | jump => simp only [edgeOp, reduceCtorEq] at head
  | call => simp only [edgeOp, reduceCtorEq] at head
  | ret => simp only [edgeOp, reduceCtorEq] at head
  | pcAt => simp only [edgeOp, reduceCtorEq] at head

/-- **The window is carried along every edge**, from `rules.stateGas = none` and `CREATE2` of a factory frame's chain. -/
theorem window_carryH {R : Exec.Deriv} (hsg : R.sevm.benvStat.rules.stateGas = none)
    (hcreate2 : R.sevm.benvStat.rules.op.create2 = true)
    {F F' : Exec.Deriv} {κ κ' : Cursor} {e : WindowEntry}
    (chain : Exec.Deriv.ParentPrefix R F) (he : e ∈ window) (hf : κ.f = e.2.1) (hf' : κ'.f = e.1)
    (stateful : ConfStep (Ninst.RunWith (Cursor.DescOf F)) cert.prog F.sevm (κ.conf F.devm)
      (κ'.conf F'.devm))
    (track : ∀ e' ∈ window, κ.f = e'.1 → WTrack R.devm e'.2.2 F) : WTrack R.devm e.2.2 F' := by
  have nodeSg : F.sevm.benvStat.rules.stateGas = none := by
    rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain]; exact hsg
  have nodeCreate2 : F.sevm.benvStat.rules.op.create2 = true := by
    rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain]; exact hcreate2
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
          obtain ⟨_, _, _, _, w, xs, -, hw, result⟩ := create2_run_resultH nodeSg nodeCreate2 h.toRun
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
      obtain ⟨rest', matched'⟩ := ConfStep.windowH nodeSg stateful
        (by rw [hf]; exact (ops j (by omega)).trans ho) transfer matched
      exact ⟨v, q, rest', fresh, by rw [show (base + (j + 1)) % 100 = j + 1 by omega]; exact hq,
        matched'⟩

/-- **The factory's `CALL` target, from rule facts.**  At a node of the chain of a frame running the factory code from pc
`0` that decodes `CALL`, the target operand is `0` or an address with no code at the frame's entry, up to
the 160-bit mask the `CALL` applies. -/
theorem factory_call_targetH {R N : Exec.Deriv} (hpc : R.pc = 0) (hcode : R.sevm.code = code)
    (hsg : R.sevm.benvStat.rules.stateGas = none)
    (hcreate2 : R.sevm.benvStat.rules.op.create2 = true) (chain : Exec.Deriv.ParentPrefix R N)
    (hat : Ninst.At N.sevm.code N.pc (.exec .call)) :
    ∃ (g t : B256) (rest : Stack), N.devm.stack = g :: t :: rest ∧ Fresh R.devm t := by
  obtain ⟨κ, ok, checked, track⟩ := window_trackH cert_check cert_windowOk hpc hcode hsg
    (WTrack R.devm)
    (fun chainF he hf hf' _ stateful _ track => window_carryH hsg hcreate2 chainF he hf hf' stateful track)
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

/-- **What the factory spawns, from rule facts.**  Every direct child of a frame running the factory code from pc `0` is
static, or targets `0`, or targets an address that had no code when the frame began. -/
theorem factory_children_freshH {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (codeEq : sevm.code = code)
    (hsg : sevm.benvStat.rules.stateGas = none) (hcreate2 : sevm.benvStat.rules.op.create2 = true) :
    ∀ c ∈ Exec.childFrames run, c.sevm.isStatic = true ∨ c.sevm.currentTarget = 0 ∨
      (pre.getCode c.sevm.currentTarget).toList = [] := by
  intro c member
  obtain ⟨N, f, rsm, pc', cevm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) c member
  obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv step
  have sevmEq : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeSg : N.sevm.benvStat.rules.stateGas = none := by rw [sevmEq]; exact hsg
  have nodeCreate2 : N.sevm.benvStat.rules.op.create2 = true := by rw [sevmEq]; exact hcreate2
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
  obtain ⟨κ₀, reach, ok₀⟩ := cursor_of_parentPrefix_noStateGas cert_check rfl codeEq hsg chain
  rcases ok₀.exec_spawn_undelegated (Cursor.execsSatisfy_of_reachable (by decide +kernel) reach) hat
    with rfl | rfl | rfl
  · obtain ⟨g, t, rest, hstack, fresh⟩ := factory_call_targetH (R := ⟨0, sevm, pre, out, run⟩) rfl
      codeEq hsg hcreate2 chain hat
    have childTarget : c.sevm.currentTarget = t.toAdr := by
      rw [target]
      exact Xinst.step_call_spawn_targetH nodeSg hstack hx
    rw [childTarget]
    rcases fresh with zero | empty
    · exact Or.inr (Or.inl zero)
    · exact Or.inr (Or.inr empty)
  · left
    rw [childEq]
    exact (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic hx)
  · right; right
    rw [target]
    exact freshOf (Xinst.step_create2_spawn_unprotectedH nodeSg nodeCreate2 hx)

end Blanc.Lift.UniswapV2Factory
