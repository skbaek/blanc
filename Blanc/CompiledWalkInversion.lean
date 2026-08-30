import Blanc.RevertPayload

/-!
# Contract-neutral inversion of compiled function walks

The `Func.RunCompiledTo` relation is inductive in the construction direction,
but consumers that inspect an already-built walk need the corresponding small
inversion lemmas.  These facts depend only on the shared compiled semantics;
they do not mention a contract, selector table, or deployment family.
-/

namespace Blanc

open Jaune

/-- `Func.RunCompiledTo` at a `.next` node. -/
theorem runCompiledTo_next_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {i : Ninst} {f : Func} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (Func.next i f) ex) :
    ∃ mid, Ninst.RunCompiled sevm devm i mid ∧
      Func.RunCompiledTo fs sevm mid f ex := by
  cases h with | next hn hrest => exact ⟨_, hn, hrest⟩

/-- `Func.RunCompiledTo` at a `.branch` node. -/
theorem runCompiledTo_branch_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f g : Func} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (Func.branch f g) ex) :
    (∃ armPre, devm.stack = 0 :: armPre.stack ∧
        Devm.PopBurnBy [0] (gVerylow + gHigh) devm armPre ∧
        Func.RunCompiledTo fs sevm armPre f ex) ∨
      (∃ (w : B256) (armPre : Devm), w ≠ 0 ∧
        devm.stack = w :: armPre.stack ∧
        Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm armPre ∧
        Func.RunCompiledTo fs sevm armPre g ex) := by
  cases h with
  | zero hroom hpop harm => exact Or.inl ⟨_, hpop.stack, hpop, harm⟩
  | succ hne hroom hpop harm =>
    exact Or.inr ⟨_, _, hne, hpop.stack, hpop, harm⟩

/-- `Func.RunCompiledTo` at a `.call` node, against a known table entry. -/
theorem runCompiledTo_call_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {k : Nat} {f : Func} {ex : Execution}
    (h_get : fs[k]? = some f)
    (h : Func.RunCompiledTo fs sevm devm (Func.call k) ex) :
    ∃ mid, Devm.BurnBy (gVerylow + gMid + gJumpdest) devm mid ∧
      Func.RunCompiledTo fs sevm mid f ex := by
  cases h with
  | call hget hroom hburn hrest =>
    cases Option.some.inj (hget.symm.trans h_get)
    exact ⟨_, hburn, hrest⟩

/-- A walk of a `Line`-prefixed body splits at the line's end. -/
theorem runCompiledTo_prepend_inv {fs : List Func} {sevm : Sevm}
    {l : Line} {f : Func} {ex : Execution} :
    ∀ {devm : Devm}, Func.RunCompiledTo fs sevm devm (l +++ f) ex →
      ∃ mid, Line.Run sevm devm l mid ∧
        Func.RunCompiledTo fs sevm mid f ex := by
  induction l with
  | nil => exact fun h => ⟨_, Line.Run.nil, h⟩
  | cons i l ih =>
    intro devm h
    obtain ⟨mid, hn, hrest⟩ := runCompiledTo_next_inv h
    obtain ⟨fin, hline, hf⟩ := ih hrest
    exact ⟨fin, Line.Run.cons (Ninst.Run.of_runCompiled hn) hline, hf⟩

/-- `ISZERO` preserves memory and return data while replacing the stack head. -/
theorem iszero_stack_inv {sevm : Sevm} {pre post : Devm} {w : B256}
    {rest : List B256}
    (run : Ninst.RunCompiled sevm pre Ninst.iszero post)
    (h_stk : pre.stack = w :: rest) :
    post.stack = (w =? 0) :: rest ∧ post.memory = pre.memory ∧
      post.returnData = pre.returnData := by
  rcases of_run_reg (Ninst.Run.of_runCompiled run) with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  obtain ⟨x, hdiff⟩ := Devm.diffBurn_of_applyUnary hrun
  obtain ⟨mid, hpop, hpush⟩ := hdiff.stack
  have hpop' : w :: rest = x :: mid := by rw [← h_stk]; exact hpop
  injection hpop' with hw hrest
  subst hw
  subst hrest
  exact ⟨hpush, hdiff.memory.symm, hdiff.returnData.symm⟩

/-- `Func.RunCompiledTo` at a `.last` node. -/
theorem runCompiledTo_last_inv {fs : List Func} {sevm : Sevm} {devm : Devm}
    {l : Linst} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (Func.last l) ex) :
    Linst.Run sevm devm l ex := by
  cases h with | last h => exact h

/-- A successful compiled `STOP` returns its exact input machine state. -/
theorem Func.RunCompiledTo.stop_eq
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.RunCompiledTo fs sevm pre Func.stop (.ok post)) :
    post = pre := by
  have terminal := runCompiledTo_last_inv run
  simp [Linst.Run, Linst.run] at terminal
  exact terminal.symm

/-- `REVERT` cannot produce a successful outcome, however its operand reads
fail.  This is the successful-outcome half of the contract-neutral terminal
inversion used by compiled-walk eliminators. -/
theorem Linst.not_run_rev_ok {sevm : Sevm} {devm post : Devm}
    (run : Linst.Run sevm devm .rev (.ok post)) : False := by
  simp only [Linst.Run, Linst.run] at run
  rcases Except.bind_eq_ok run with ⟨_v1, _h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨_v2, _h3, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨_v3, _h5, h6⟩
  contradiction

private theorem prependStoresRev_not_ok
    {fs : List Func} {sevm : Sevm} {rest : Func}
    (terminal : ∀ {pre post : Devm},
      Func.RunCompiledTo fs sevm pre rest (.ok post) → False)
    (iws : List (B256 × Nat)) :
    ∀ {pre post : Devm},
      Func.RunCompiledTo fs sevm pre (prependStoresRev iws rest) (.ok post) →
        False := by
  induction iws generalizing rest with
  | nil =>
      intro pre post run
      exact terminal (by simpa [prependStoresRev] using run)
  | cons iw iws ih =>
      intro pre post run
      apply ih (rest := prependStore iw.1 iw.2 rest)
      · intro innerPre innerPost innerRun
        unfold prependStore at innerRun
        obtain ⟨_, -, innerRun⟩ := runCompiledTo_next_inv innerRun
        obtain ⟨_, -, innerRun⟩ := runCompiledTo_next_inv innerRun
        obtain ⟨_, -, innerRun⟩ := runCompiledTo_next_inv innerRun
        exact terminal innerRun
      · simpa [prependStoresRev] using run

/-- `Func.revData` cannot end in a successful outcome.  This is the exact
compiled-walk elimination seam: it peels the generated constant-word stores
and reaches the terminal `REVERT`, without a fuel bound or evaluator result. -/
theorem Func.RunCompiledTo.not_ok_revData
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {blob : Bytes}
    (run : Func.RunCompiledTo fs sevm pre (Func.revData blob) (.ok post)) :
    False := by
  unfold Func.revData at run
  apply prependStoresRev_not_ok (iws := (bytesWords blob).zipIdx) ?_ run
  intro innerPre innerPost innerRun
  obtain ⟨_, -, innerRun⟩ := runCompiledTo_next_inv innerRun
  obtain ⟨_, -, innerRun⟩ := runCompiledTo_next_inv innerRun
  exact Linst.not_run_rev_ok (runCompiledTo_last_inv innerRun)

/-- A zero stack head forces the fall-through arm of a compiled branch and
preserves the known tail across the branch pop. -/
theorem Func.RunCompiledTo.zero_branch_of_prefix
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {left right : Func} {xs : Stack}
    (hp : (0 : B256) :: xs <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre (Func.branch left right) out) :
    ∃ armPre,
      Devm.PopBurnBy [0] (gVerylow + gHigh) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre left out ∧
      xs <<+ armPre.stack := by
  rcases runCompiledTo_branch_inv run with hzero | hsucc
  · rcases hzero with ⟨armPre, -, hpop, harm⟩
    have tail := (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hp).2
    exact ⟨armPre, hpop, harm, tail⟩
  · rcases hsucc with ⟨w, armPre, hw, hstack, -, -⟩
    have pw : w :: ([] : Stack) <<+ pre.stack :=
      ⟨armPre.stack, by simpa [Split] using hstack⟩
    exact (hw (pref_head_unique hp pw).symm).elim

/-- A known nonzero stack head forces the jumped arm of a compiled branch and
preserves the known tail across the branch pop. -/
theorem Func.RunCompiledTo.succ_branch_of_prefix
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {left right : Func} {w : B256} {xs : Stack}
    (hw : w ≠ 0) (hp : w :: xs <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre (Func.branch left right) out) :
    ∃ armPre branchWord,
      branchWord ≠ 0 ∧
      Devm.PopBurnBy [branchWord] (gVerylow + gHigh + gJumpdest) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre right out ∧
      xs <<+ armPre.stack := by
  rcases runCompiledTo_branch_inv run with hzero | hsucc
  · rcases hzero with ⟨armPre, hstack, -, -⟩
    have pzero : (0 : B256) :: ([] : Stack) <<+ pre.stack :=
      ⟨armPre.stack, by simpa [Split] using hstack⟩
    exact (hw (pref_head_unique hp pzero)).elim
  · rcases hsucc with ⟨branchWord, armPre, hnz, hstack, hpop, harm⟩
    have pword : branchWord :: ([] : Stack) <<+ pre.stack :=
      ⟨armPre.stack, by simpa [Split] using hstack⟩
    have hword : branchWord = w := pref_head_unique pword hp
    subst branchWord
    have tail := (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hp).2
    exact ⟨armPre, w, hnz, hpop, harm, tail⟩

/-- Peel the shared nonpayable wrapper at an **arbitrary** outcome.  The
`_of_ok` form below can only see `sevm.value = 0` because it succeeded; a
negative theorem knows the value from its own hypothesis instead, and still
needs the body walk. -/
theorem Func.RunCompiledTo.nonpayable_body_of_value_zero
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {body : Func} {tail : Stack}
    (valueZero : sevm.value = 0)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre (nonpayable body) out) :
    ∃ bodyPre,
      Func.RunCompiledTo fs sevm bodyPre body out ∧
      tail <<+ bodyPre.stack ∧
      Devm.getStor pre = Devm.getStor bodyPre := by
  unfold nonpayable at run
  obtain ⟨afterValue, qvalue, run⟩ := runCompiledTo_next_inv run
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have rvalue := Ninst.Run.of_runCompiled qvalue
  have rzero := Ninst.Run.of_runCompiled qzero
  have pValue := prefix_of_push (of_run_callvalue rvalue) hp
  have pTest := prefix_of_iszero rzero pValue
  have pOne : (1 : B256) :: tail <<+ testPre.stack := by
    simpa [valueZero, B256.eqCheck] using pTest
  obtain ⟨bodyPre, _, -, hpop, bodyRun, pBody⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) pOne branchRun
  have bodyStor : Devm.getStor pre = Devm.getStor bodyPre :=
    (Ninst.Hinv.inv (f := Devm.getStor) rvalue).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) rzero).trans
        (funext (getStor_eq_of_state_eq hpop.state)))
  exact ⟨bodyPre, bodyRun, pBody, bodyStor⟩

/-- A successful walk through the shared nonpayable modifier proves zero call
value and reaches its protected body without changing storage. -/
theorem Func.RunCompiledTo.nonpayable_body_of_ok
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {body : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre (nonpayable body) (.ok post)) :
    sevm.value = 0 ∧
      ∃ bodyPre,
        Func.RunCompiledTo fs sevm bodyPre body (.ok post) ∧
        tail <<+ bodyPre.stack ∧
        Devm.getStor pre = Devm.getStor bodyPre := by
  have valueZero : sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable
      (Func.Run.of_runCompiled
        (Func.RunCompiled.of_runCompiledTo_ok run))
  exact ⟨valueZero,
    Func.RunCompiledTo.nonpayable_body_of_value_zero valueZero hp run⟩

private lemma of_run_rev_empty {sevm : Sevm} {devm : Devm} {s : List B256}
    {ex : Execution}
    (h_stk : devm.stack = (0 : B256) :: (0 : B256) :: s)
    (h_run : Linst.Run sevm devm .rev ex) :
    ∃ post, ex = .error (.revert, post) ∧ post.output = [] := by
  have h_eq : Linst.run sevm devm .rev = ex := h_run
  have h_gas : devm.extCost
      [⟨((0 : B256)).toNat, ((0 : B256)).toNat⟩] ≤ devm.gasLeft := by
    rw [show ((0 : B256)).toNat = 0 from rfl, Devm.extCost_empty_window]
    exact Nat.zero_le _
  refine ⟨_, h_eq.symm.trans (Linst.run_rev_eq_error h_stk h_gas rfl), ?_⟩
  show (devm.memory.read ((0 : B256)).toNat ((0 : B256)).toNat).1 = []
  rfl

/-- `Func.rev` reverts with an empty payload from an arbitrary compiled walk. -/
theorem runCompiledTo_rev_inv {fs : List Func} {sevm : Sevm} {devm : Devm}
    {ex : Execution} (run : Func.RunCompiledTo fs sevm devm Func.rev ex) :
    ∃ post, ex = .error (.revert, post) ∧ post.output = [] := by
  rw [Func.rev] at run
  obtain ⟨d1, r1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d2, r2, run⟩ := runCompiledTo_next_inv run
  have hrev := runCompiledTo_last_inv run
  have p1 := of_run_pushB256 (Ninst.Run.of_runCompiled r1)
  have p2 := of_run_pushB256 (Ninst.Run.of_runCompiled r2)
  have hstk : d2.stack = (0 : B256) :: (0 : B256) :: devm.stack := by
    rw [p2.stack, p1.stack]; rfl
  exact of_run_rev_empty hstk hrev

private lemma of_run_rev_window {sevm : Sevm} {devm : Devm} {i sz : B256}
    {s : List B256} {ex : Execution}
    (h_stk : devm.stack = i :: sz :: s)
    (h_run : Linst.Run sevm devm .rev ex) :
    (∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, ex = .error (.revert, post) ∧
        post.output = (devm.memory.read i.toNat sz.toNat).1) := by
  have h_eq : Linst.run sevm devm .rev = ex := h_run
  rcases Nat.lt_or_ge devm.gasLeft (devm.extCost [⟨i.toNat, sz.toNat⟩])
    with h_gas | h_gas
  · have h_oog : Linst.run sevm devm .rev
        = .error ⟨.halt (.outOfGas .none),
            devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
      show (do
        let ⟨index, d⟩ ← devm.popToNat
        let ⟨size, d⟩ ← d.popToNat
        let cost := d.extCost [⟨index, size⟩]
        let d ← chargeGas cost d
        let ⟨output, d⟩ := d.memRead index size
        let d := d.withOutput output
        Except.error ⟨.revert, d⟩) = _
      rw [Devm.popToNat_eq_ok h_stk]
      simp only [bind, Except.bind]
      rw [Devm.popToNat_eq_ok
        (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl]
      simp only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.gasLeft_setMach]
      have h_ext : (devm.setMach
          ⟨s, devm.memory, devm.gasLeft⟩).extCost
          [⟨i.toNat, sz.toNat⟩] = devm.extCost [⟨i.toNat, sz.toNat⟩] := rfl
      rw [h_ext]
      have hcg : chargeGas (devm.extCost [⟨i.toNat, sz.toNat⟩])
          (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) =
            .error ⟨.halt (.outOfGas .none),
              devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
        rw [chargeGas_def]
        have hs : safeSub (devm.setMach
            ⟨s, devm.memory, devm.gasLeft⟩).gasLeft
            (devm.extCost [⟨i.toNat, sz.toNat⟩]) = none := by
          unfold safeSub
          rw [if_neg (by simp only [Devm.gasLeft_setMach]; omega)]
        rw [hs]
      rw [hcg]
    exact Or.inl ⟨_, h_eq.symm.trans h_oog⟩
  · exact Or.inr ⟨_, h_eq.symm.trans (Linst.run_rev_eq_error h_stk h_gas rfl),
      rfl⟩

private lemma read_selector_of_write_zero {μ : Mem} {ys : Bytes}
    (h : ys.length = 32) :
    ((μ.write 0 ys).read 28 4).1 = ys.drop 28 := by
  have hne : ys ≠ [] := by
    intro hn; rw [hn] at h; exact absurd h (by decide)
  have hfull := Mem.read_write_zero μ hne
  rw [h] at hfull
  have hshift : ∀ M : Mem, (M.read 28 4).1 = ((M.read 0 32).1).drop 28 := by
    intro M
    show Array.sliceD M.data 28 4 0 = (Array.sliceD M.data 0 32 0).drop 28
    rw [Array.sliceD_eq_map, Array.sliceD_eq_map]
    rfl
  rw [hshift, hfull]

private lemma toBytes_toB256_drop28 (data : Bytes) (h : data.length = 4) :
    data.toB256.toBytes.drop 28 = data := by
  have hp := Bytes.toBytes_toB256_of_length
    (xs := List.replicate 28 0 ++ data) (by simp [h])
  exact (by
    simpa [Bytes.toB256_zero_cons] using congrArg (List.drop 28) hp)

/-- `Func.revSelector` reverts with its four-byte payload, or can run out of gas
on the final nonempty revert window. -/
theorem runCompiledTo_revSelector_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {data : Bytes} {hlen : data.length = 4} {ex : Execution}
    (run : Func.RunCompiledTo fs sevm devm (Func.revSelector data hlen) ex) :
    (∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, ex = .error (.revert, post) ∧ post.output = data) := by
  rw [Func.revSelector] at run
  obtain ⟨d1, r1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d2, r2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d3, r3, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d4, r4, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d5, r5, run⟩ := runCompiledTo_next_inv run
  have hrev := runCompiledTo_last_inv run
  have p1 := of_run_push (Ninst.Run.of_runCompiled r1)
  have p2 := of_run_pushB256 (Ninst.Run.of_runCompiled r2)
  have hp2 := prefix_of_push p2 (prefix_of_push p1 nil_pref)
  obtain ⟨-, hm3⟩ :=
    prefix_of_mstore_val (Ninst.Run.of_runCompiled r3) hp2
  have p4 := of_run_pushB256 (Ninst.Run.of_runCompiled r4)
  have p5 := of_run_pushB256 (Ninst.Run.of_runCompiled r5)
  have hm5 : d5.memory = d2.memory.write 0 data.toB256.toBytes := by
    rw [← p5.memory, ← p4.memory, hm3]; rfl
  have hstk5 : d5.stack = (28 : B256) :: (4 : B256) :: d3.stack := by
    rw [p5.stack, p4.stack]; rfl
  rcases of_run_rev_window hstk5 hrev with h_oog | ⟨post, hpost, hout⟩
  · exact Or.inl h_oog
  · refine Or.inr ⟨post, hpost, ?_⟩
    rw [hout, hm5,
      show ((28 : B256)).toNat = 28 from rfl,
      show ((4 : B256)).toNat = 4 from rfl,
      read_selector_of_write_zero (B256.length_toBytes _),
      toBytes_toB256_drop28 data hlen]

/-- A known call to an empty-data `REVERT` body cannot produce `.ok`. -/
theorem Func.RunCompiledTo.not_ok_call_rev
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {slot : Nat}
    (hget : fs[slot]? = some Func.rev)
    (run : Func.RunCompiledTo fs sevm pre (.call slot) (.ok post)) : False := by
  obtain ⟨_, -, bodyRun⟩ := runCompiledTo_call_inv hget run
  rcases runCompiledTo_rev_inv bodyRun with ⟨_, impossible, -⟩
  cases impossible

/-- A successful compiled branch must use its zero/fall-through arm when the
jumped arm has separately been proved unable to return `.ok`. -/
theorem Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {left right : Func}
    (rightNotOk : ∀ {armPre},
      Func.RunCompiledTo fs sevm armPre right (.ok post) → False)
    (run : Func.RunCompiledTo fs sevm pre
      (Func.branch left right) (.ok post)) :
    ∃ armPre,
      Devm.PopBurnBy [0] (gVerylow + gHigh) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre left (.ok post) := by
  rcases runCompiledTo_branch_inv run with
    ⟨armPre, _stack, pop, armRun⟩ |
    ⟨_word, _armPre, _nonzero, _stack, _pop, rightRun⟩
  · exact ⟨armPre, pop, armRun⟩
  · exact (rightNotOk rightRun).elim

/-- A successful compiled branch whose jumped arm is a fixed empty-data
reverter must continue through the zero/fall-through arm. -/
theorem Func.RunCompiledTo.zero_branch_of_ok_call_rev
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {rest : Func} {slot : Nat}
    (hget : fs[slot]? = some Func.rev)
    (run : Func.RunCompiledTo fs sevm pre
      (Func.branch rest (.call slot)) (.ok post)) :
    ∃ armPre,
      Devm.PopBurnBy [0] (gVerylow + gHigh) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre rest (.ok post) := by
  exact Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok
    (fun rightRun => Func.RunCompiledTo.not_ok_call_rev hget rightRun) run

/-- Prefix-retaining form of
`zero_branch_of_ok_of_right_not_ok`. -/
theorem Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok_of_prefix
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {left right : Func} {flag : B256} {xs : Stack}
    (rightNotOk : ∀ {armPre},
      Func.RunCompiledTo fs sevm armPre right (.ok post) → False)
    (hp : flag :: xs <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (Func.branch left right) (.ok post)) :
    ∃ armPre,
      flag = 0 ∧
      Devm.PopBurnBy [0] (gVerylow + gHigh) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre left (.ok post) ∧
      xs <<+ armPre.stack := by
  obtain ⟨armPre, pop, armRun⟩ :=
    Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok rightNotOk run
  have pzero : (0 : B256) :: ([] : Stack) <<+ pre.stack :=
    ⟨armPre.stack, pop.stack⟩
  have flagZero : flag = 0 := pref_head_unique hp pzero
  subst flag
  exact ⟨armPre, rfl, pop, armRun,
    (popBurn_pref (Devm.PopBurn.of_popBurnBy pop) hp).2⟩

/-- Prefix-retaining form of `zero_branch_of_ok_call_rev`.  It additionally
identifies the caller's known head with zero and transports its tail across
the branch pop. -/
theorem Func.RunCompiledTo.zero_branch_of_ok_call_rev_of_prefix
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {rest : Func} {slot : Nat} {flag : B256} {xs : Stack}
    (hget : fs[slot]? = some Func.rev)
    (hp : flag :: xs <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (Func.branch rest (.call slot)) (.ok post)) :
    ∃ armPre,
      flag = 0 ∧
      Devm.PopBurnBy [0] (gVerylow + gHigh) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre rest (.ok post) ∧
      xs <<+ armPre.stack := by
  exact Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok_of_prefix
    (fun rightRun => Func.RunCompiledTo.not_ok_call_rev hget rightRun)
    hp run

/-- A known call to a four-byte selector reverter cannot produce `.ok`. -/
theorem Func.RunCompiledTo.not_ok_call_revSelector
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {slot : Nat}
    {data : Bytes} {hlen : data.length = 4}
    (hget : fs[slot]? = some (Func.revSelector data hlen))
    (run : Func.RunCompiledTo fs sevm pre (.call slot) (.ok post)) : False := by
  obtain ⟨_, -, bodyRun⟩ := runCompiledTo_call_inv hget run
  rcases runCompiledTo_revSelector_inv bodyRun with
    ⟨_, impossible⟩ | ⟨_, impossible, -⟩ <;> cases impossible

/-- A known call to an arbitrary-data reverter cannot produce `.ok`. -/
theorem Func.RunCompiledTo.not_ok_call_revData
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {slot : Nat}
    {blob : Bytes}
    (hget : fs[slot]? = some (Func.revData blob))
    (run : Func.RunCompiledTo fs sevm pre (.call slot) (.ok post)) : False := by
  obtain ⟨_, -, bodyRun⟩ := runCompiledTo_call_inv hget run
  exact Func.RunCompiledTo.not_ok_revData bodyRun

end Blanc
