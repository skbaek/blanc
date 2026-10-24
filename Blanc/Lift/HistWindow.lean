import Blanc.Lift.PrefixTransfer
import Blanc.Lift.CursorWindow
import Blanc.ExecutionSettledOwnCode

/-!
# Window tracking and spawn shapes from rule facts

The window kit of `PrefixTransfer.lean`, `CursorWindow.lean`, `CallSiteChildren.lean` and
`ExecutionSettledOwnCode.lean` takes `CoveredFork`, though each lemma reads only
`rules.stateGas = none` (and `CREATE2` reads `rules.op.create2`). The forms below state exactly
those facts, so they apply under every pre-Amsterdam schedule:

* `prefixTransfer_runH` — the exact-word prefix transfer is sound;
* `create2_run_resultH` — a successful `CREATE2` replaces its operands by `0` or an address that
  was unprotected in the spawning world;
* `window_trackH` — a window property is carried along a frame's chain;
* `Xinst.step_call_spawn_stackH`, `Xinst.step_call_spawn_targetH` — a spawning `CALL` popped its
  seven operands and its child runs at the popped callee;
* `Xinst.step_create2_spawn_unprotectedH` — a `CREATE2` child targets an unprotected account;
* `List.swap_some_length`, `Cert.windowOk_mem`, `matches_append_drop` — a successful `SWAP`
  reaches its operand and keeps the length; every body of a window-checked certificate passes the
  edge check; dropping words keeps a pattern-over-rest match.

Each is the covered lemma with the covered-fork facts replaced by the rule facts it reads.
Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- A successful `SWAP` reaches its operand and keeps the stack's length. -/
theorem List.swap_some_length : ∀ {l l' : Stack} {i : Nat}, Jaune.List.swap l i = some l' →
    i + 2 ≤ l.length ∧ l'.length = l.length
  | [], _, _, h => by simp only [Jaune.List.swap, reduceCtorEq] at h
  | x :: l, l', i, h => by
      cases e : l[i]? with
      | none => simp only [Jaune.List.swap, e, Option.bind_eq_bind, Option.bind_none,
          reduceCtorEq] at h
      | some y =>
          simp only [Jaune.List.swap, e, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq] at h
          subst h
          have hi := (List.getElem?_eq_some_iff.mp e).1
          simp only [List.length_cons, List.length_set]
          exact ⟨by omega, trivial⟩

/-- Dropping `n` words from a pattern-over-concrete-rest match and from the stack keeps a match
over some concrete rest. -/
theorem matches_append_drop : ∀ (n : Nat) {p : Pattern} {rest s : Stack},
    Matches (p ++ rest.map some) s → ∃ rest' : Stack, Matches (p.drop n ++ rest'.map some) (s.drop n)
  | 0, _, rest, _, h => ⟨rest, h⟩
  | n + 1, [], _, s, _ => ⟨s.drop (n + 1), matches_some_map _⟩
  | _ + 1, _ :: _, _, [], h => h.elim
  | n + 1, _ :: _, _, _ :: _, ⟨_, h⟩ => matches_append_drop n h

/-- Every function body of a window-checked certificate passes the edge check and is no window
tree. -/
theorem Cert.windowOk_mem {E : List WindowEntry} {sites : List SFunc} {c : Cert}
    (hw : c.windowOk E sites = true) {g : SFunc} (hg : g ∈ c.prog) :
    g.windowEdges E sites = true ∧ notWindow E g = true :=
  Bool.and_eq_true _ _ ▸ List.all_eq_true.mp hw g hg

/-- **Soundness of the prefix transfer, from `rules.stateGas = none`.**  `prefixTransfer_run`
with its covered-fork fact replaced by the one it reads. -/
theorem prefixTransfer_runH {sevm : Sevm} {d d' : Devm} {n : Ninst} {p p' : Pattern}
    {rest : Stack} (hsg : sevm.benvStat.rules.stateGas = none)
    (matched : Matches (p ++ rest.map some) d.stack) (checked : prefixTransfer n p = some p')
    (run : Ninst.Run sevm d n d') : ∃ rest' : Stack, Matches (p' ++ rest'.map some) d'.stack := by
  have generic : ∀ {q : Pattern} {rest : Stack}, Matches (q ++ rest.map some) d.stack →
      ninstTransfer n q = some p' → ∃ rest' : Stack, Matches (p' ++ rest'.map some) d'.stack :=
    fun {q} {rest} m t => ⟨rest, ninstTransfer_run_noStateGas hsg m (ninstTransfer_append (rest.map some) t) run⟩
  cases n with
  | push bs fits =>
      simp only [prefixTransfer, Option.some.injEq] at checked
      subst checked
      exact ⟨rest, by rw [push_run_stack run]; exact ⟨Or.inr rfl, matched⟩⟩
  | reg r =>
      cases r with
      | dup i =>
          obtain ⟨x, hx, -⟩ := of_run_dup run
          have depth : i.val + 1 ≤ d.stack.length := (List.getElem?_eq_some_iff.mp hx).1
          exact generic (matches_padPattern matched depth) checked
      | swap i => exact generic (matches_padPattern matched (List.swap_some_length (of_run_swap run)).1) checked
      | and =>
          match p, matched, checked with
          | some x :: some y :: q, matched, checked =>
              simp only [prefixTransfer, Option.some.injEq] at checked
              subst checked
              rcases of_run_reg run with ⟨pc, hr⟩
              simp only [Rinst.run, Rinst.runCore] at hr
              obtain ⟨a, b, hd⟩ := Devm.diffBurn_of_applyBinary hr
              obtain ⟨mid, pop, push⟩ := hd.stack
              simp only [Stack.Pop, Stack.Push, Split, List.nil_append, List.cons_append] at pop push
              rw [pop] at matched
              obtain ⟨hxw, hyw, hq⟩ := matched
              rw [push, hxw.eq_of_some, hyw.eq_of_some]
              exact ⟨rest, Or.inr rfl, hq⟩
          | [], matched, checked => exact generic matched checked
          | [none], matched, checked => exact generic matched checked
          | [some x], matched, checked => exact generic matched checked
          | none :: _ :: q, matched, checked => exact generic matched checked
          | some x :: none :: q, matched, checked => exact generic matched checked
      | _ => exact generic matched checked
  | _ => exact generic matched checked

/-- **The word a `CREATE2` leaves, from rule facts.**  `create2_run_result` from
`rules.stateGas = none` and `rules.op.create2 = true`.  A successful `CREATE2` replaces its four operands by `0` or by the
new address, which was unprotected in the spawning world. -/
theorem create2_run_resultH {sevm : Sevm} {d d' : Devm} (hsg : sevm.benvStat.rules.stateGas = none)
    (hcreate2 : sevm.benvStat.rules.op.create2 = true)
    (run : Ninst.Run sevm d (.exec .create2) d') :
    ∃ (v i sz salt w : B256) (xs : Stack), d.stack = v :: i :: sz :: salt :: xs ∧
      d'.stack = w :: xs ∧ (w = 0 ∨ ∃ na, w = na.toB256 ∧ ¬ State.Protected d.state na) := by
  rcases run with ⟨xl, -, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    hsg, hcreate2, ↓reduceIte, Bind.bind, Except.bind] at h_run
  rcases eq1 : Devm.pop d with _ | ⟨v1, s1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e1 := (Devm.pop_of_pop eq1)
  rcases eq2 : Devm.popToNat s1 with _ | ⟨n2, s2⟩ <;> simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq2 with ⟨x2, f2, -⟩
  rcases eq3 : Devm.popToNat s2 with _ | ⟨n3, s3⟩ <;> simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq3 with ⟨x3, f3, -⟩
  rcases eq4 : Devm.pop s3 with _ | ⟨v4, s4⟩ <;> simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e4 := (Devm.pop_of_pop eq4)
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i s5 eq5
  have b5 := Devm.burn_of_chargeGas eq5
  obtain ⟨w, hw, result⟩ := genericCreate_result h_run
  have stack : d.stack = v1 :: x2 :: x3 :: v4 :: s4.stack := by
    have a := e1.stack
    have b := f2.stack
    have c := f3.stack
    have d4 := e4.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at a b c d4
    rw [a, b, c, d4]
  have state : (s5.memExtends [(n2, n3)]).state = d.state := by
    rw [show (s5.memExtends [(n2, n3)]).state = s5.state from rfl, ← b5.state, ← e4.state,
      ← f3.state, ← f2.state, ← e1.state]
  refine ⟨v1, x2, x3, v4, w, s4.stack, stack, ?_, ?_⟩
  · rw [hw, show (s5.memExtends [(n2, n3)]).stack = s5.stack from rfl, ← b5.stack]
  · rcases result with rfl | ⟨rfl, unprotected⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, state ▸ unprotected⟩

/-- **Window tracking, from `rules.stateGas = none`.**  `window_track` with its covered-fork fact
replaced by the one it reads.  Along the chain of a frame of certified code entered at pc `0`, every node sits
at a checked cursor, and at a window tree `W` of index `j` the node satisfies `Track j`, provided `Track`
is carried along every window edge: from the predecessor's node (and `Track` of the predecessor's own
window indices) across the actual step to the window tree. -/
theorem window_trackH {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {E : List WindowEntry} {sites : List SFunc} (hw : c.windowOk E sites = true)
    {R : Exec.Deriv} (hpc : R.pc = 0) (hcode : R.sevm.code = code)
    (hsg : R.sevm.benvStat.rules.stateGas = none) (Track : Nat → Exec.Deriv → Prop)
    (carry : ∀ {F F' : Exec.Deriv} {κ κ' : Cursor} {e : WindowEntry},
      Exec.Deriv.ParentPrefix R F → e ∈ E → κ.f = e.2.1 → κ'.f = e.1 → CursorOK code c F κ →
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm (κ.conf F.devm) (κ'.conf F'.devm) →
      Exec.Deriv.ParentStep F' F → (∀ e' ∈ E, κ.f = e'.1 → Track e'.2.2 F) → Track e.2.2 F')
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix R N) :
    ∃ κ, CursorOK code c N κ ∧ κ.Checked E sites ∧ ∀ e ∈ E, κ.f = e.1 → Track e.2.2 N := by
  suffices h : ∀ {F n : Exec.Deriv}, Exec.Deriv.ParentPrefix F n →
      ∀ κ₀, CursorOK code c F κ₀ → F.sevm.benvStat.rules.stateGas = none →
      Exec.Deriv.ParentPrefix R F → κ₀.Checked E sites →
      (∀ e ∈ E, κ₀.f = e.1 → Track e.2.2 F) →
      ∃ κ, CursorOK code c n κ ∧ κ.Checked E sites ∧ ∀ e ∈ E, κ.f = e.1 → Track e.2.2 n by
    have startChecked : (Cursor.start c).Checked E sites ∧ notWindow E (Cursor.start c).f = true := by
      cases c with
      | nil => simp only [Cert.check, List.all_nil, Bool.and_true, Bool.false_eq_true] at hc
      | cons p c =>
          have := Cert.windowOk_mem hw (g := p.2) (List.mem_of_getElem? (i := 0) rfl)
          exact ⟨⟨this.1, fun _ h => by cases h⟩, this.2⟩
    exact h chain _ (cursor_start hc hpc hcode) hsg (.refl R) startChecked.1
      (fun e he at₀ => (notWindow_spec startChecked.2 he at₀.symm).elim)
  intro F n hp
  induction hp with
  | refl root => exact fun κ₀ ok _ _ checked track => ⟨κ₀, ok, checked, track⟩
  | step head _ ih =>
      intro κ₀ ok fork prefixR checked track
      obtain ⟨κ₁, synthetic, stateful, ok₁⟩ := cursor_stepS_noStateGas hc ok head fork
      have checked₁ := checked.step hw synthetic
      have track₁ : ∀ e ∈ E, κ₁.f = e.1 → Track e.2.2 _ := fun e he at₁ =>
        carry prefixR he (checked.entrance hw synthetic he at₁) at₁ ok stateful head track
      exact ih κ₁ ok₁ (by rw [Cursor.parentStep_sevm head]; exact fork) (prefixR.snoc head)
        checked₁ track₁

/-- `Xinst.step_call_spawn_stack` from `rules.stateGas = none`: a spawning `CALL` popped at least
its seven operands. -/
theorem Xinst.step_call_spawn_stackH {sevm : Sevm} {s : Devm} {f : Frame} {rsm : Resume}
    (hsg : sevm.benvStat.rules.stateGas = none) (hx : Xinst.step sevm s .call = .spawn f rsm) :
    ∃ g c v ii is oi os rest, s.stack = g :: c :: v :: ii :: is :: oi :: os :: rest := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [hsg] at hx
  rcases eq1 : Devm.pop s with _ | ⟨g, d1⟩ <;> simp only [eq1] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have e1 := (Devm.pop_of_pop eq1).stack
  rcases eq2 : Devm.popToAdr d1 with _ | ⟨_, d2⟩ <;> simp only [eq2] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨c, -, p2⟩ := Devm.pop_of_popToAdr eq2
  have e2 := (Devm.pop_of_pop p2).stack
  rcases eq3 : Devm.pop d2 with _ | ⟨v, d3⟩ <;> simp only [eq3] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have e3 := (Devm.pop_of_pop eq3).stack
  rcases eq4 : Devm.popToNat d3 with _ | ⟨_, d4⟩ <;> simp only [eq4] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨ii, f4, -⟩ := Devm.pop_of_popToNat_val eq4
  have e4 := f4.stack
  rcases eq5 : Devm.popToNat d4 with _ | ⟨_, d5⟩ <;> simp only [eq5] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨is, f5, -⟩ := Devm.pop_of_popToNat_val eq5
  have e5 := f5.stack
  rcases eq6 : Devm.popToNat d5 with _ | ⟨_, d6⟩ <;> simp only [eq6] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨oi, f6, -⟩ := Devm.pop_of_popToNat_val eq6
  have e6 := f6.stack
  rcases eq7 : Devm.popToNat d6 with _ | ⟨_, d7⟩ <;> simp only [eq7] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  obtain ⟨os, f7, -⟩ := Devm.pop_of_popToNat_val eq7
  have e7 := f7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1 e2 e3 e4 e5 e6 e7
  exact ⟨g, c, v, ii, is, oi, os, d7.stack, by rw [e1, e2, e3, e4, e5, e6, e7]⟩

/-- `Xinst.step_create2_spawn_unprotected` from `rules.stateGas = none` and `rules.op.create2`: a
`CREATE2` spawn targets an account that is not protected in the spawning world. -/
theorem Xinst.step_create2_spawn_unprotectedH {sevm : Sevm} {d : Devm} {frame : Frame}
    {rsm : Resume} (hsg : sevm.benvStat.rules.stateGas = none)
    (hcreate2 : sevm.benvStat.rules.op.create2 = true)
    (h : Xinst.step sevm d .create2 = .spawn frame rsm) :
    ¬ State.Protected d.state frame.inner.currentTarget := by
  simp only [Xinst.step, hsg, hcreate2, ↓reduceIte, Bind.bind,
    Except.bind] at h
  rcases eq1 : Devm.pop d with _ | ⟨v1, s1⟩ <;> simp only [eq1] at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  rcases eq2 : Devm.popToNat s1 with _ | ⟨n2, s2⟩ <;> simp only [eq2] at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  rcases eq3 : Devm.popToNat s2 with _ | ⟨n3, s3⟩ <;> simp only [eq3] at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  rcases eq4 : Devm.pop s3 with _ | ⟨v4, s4⟩ <;> simp only [eq4] at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  split at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  rename_i s5 eq5
  simp only [XStep.ofExcept, pure, Except.pure] at h
  have state : (s5.memExtends [(n2, n3)]).state = d.state := by
    obtain ⟨x2, f2, -⟩ := Devm.pop_of_popToNat_val eq2
    obtain ⟨x3, f3, -⟩ := Devm.pop_of_popToNat_val eq3
    rw [show (s5.memExtends [(n2, n3)]).state = s5.state from rfl,
      ← (Devm.burn_of_chargeGas eq5).state, ← (Devm.pop_of_pop eq4).state, ← f3.state,
      ← f2.state, ← (Devm.pop_of_pop eq1).state]
  rw [← state, (genericCreate_step_spawn_exact h).1]
  exact genericCreate_step_spawn_target_unprotected h

/-- **A `CALL` child runs at the popped callee**, from `rules.stateGas = none`: whatever the access
schedule and delegation flag, the frame a spawning `CALL` enters has the second operand as its
target. -/
theorem Xinst.step_call_spawn_targetH {sevm : Sevm} {s : Devm} {f : Frame} {rsm : Resume}
    {g c : B256} {rest : List B256}
    (hsg : sevm.benvStat.rules.stateGas = none) (hstack : s.stack = g :: c :: rest)
    (hx : Xinst.step sevm s .call = .spawn f rsm) : f.inner.currentTarget = c.toAdr := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [hsg] at hx
  rw [Devm.pop_eq_ok hstack] at hx
  simp only at hx
  rw [Devm.popToAdr_eq_ok (devm := s.setMach ⟨c :: rest, s.memory, s.gasLeft, s.stateGas⟩) rfl]
    at hx
  simp only at hx
  repeat' split at hx
  all_goals simp only [XStep.ofExcept, reduceCtorEq, Pure.pure, Except.pure] at hx
  all_goals first
    | exact (genericCall.step_spawn_frame hx).2.1

end Blanc.Lift
