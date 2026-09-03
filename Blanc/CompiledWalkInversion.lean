import Blanc.RevertPayload
import Blanc.TransientInvariance

/-!
# Contract-neutral inversion of compiled function walks

The `Func.RunCompiledTo` relation is inductive in the construction direction,
but consumers that inspect an already-built walk need the corresponding small
inversion lemmas.  These facts depend only on the shared compiled semantics;
they do not mention a contract, selector table, or deployment family.
-/

namespace Blanc

open Jaune
open scoped LogOutputHinv

/-! ## One walk vocabulary for two relations

`Func.Run` and `Func.RunCompiledTo … (.ok ·)` are inverted by the same five
principles, and a contract's storage, memory, stack and log reasoning uses
nothing else.  Only the *gas* differs: the compiled relation pins each step's
cost, the source relation only requires it not to rise.

`Func.WalkInv` names those five principles at the source shapes, which the
compiled relation satisfies by forgetting its gas.  A trace stated over an
abstract `R` therefore serves both consumers from one proof: a compiled caller
instantiates `R` at the compiled relation and keeps compiled continuations, a
ladder obligation instantiates it at `Func.Run`.

This is what lets a contract's effect proofs be written once instead of once
per relation — and the alternative is not two cheap proofs but one proof and
one near-identical copy, which the proof-duplication ratchet rejects. -/

/-- The inversion principles shared by the source walk and the gas-exact
compiled walk, stated at the source shapes. -/
class Func.WalkInv
    (R : List Func → Sevm → Devm → Func → Devm → Prop) : Prop where
  /-- A `.next` node runs its instruction and continues. -/
  next : ∀ {fs : List Func} {sevm : Sevm} {pre post : Devm} {i : Ninst}
    {f : Func}, R fs sevm pre (Func.next i f) post →
    ∃ mid, Ninst.Run sevm pre i mid ∧ R fs sevm mid f post
  /-- A `.branch` node takes the zero arm or a nonzero arm. -/
  branch : ∀ {fs : List Func} {sevm : Sevm} {pre post : Devm} {f g : Func},
    R fs sevm pre (Func.branch f g) post →
    (∃ mid, Devm.PopBurn [0] pre mid ∧ R fs sevm mid f post) ∨
      (∃ (w : B256) (mid mid' : Devm), w ≠ 0 ∧ Devm.PopBurn [w] pre mid ∧
        Devm.Burn mid mid' ∧ R fs sevm mid' g post)
  /-- A `.call` node resolves its index in the fixed context. -/
  call : ∀ {fs : List Func} {sevm : Sevm} {pre post : Devm} {k : Nat},
    R fs sevm pre (Func.call k) post →
    ∃ f mid, fs[k]? = some f ∧ Devm.Burn pre mid ∧ R fs sevm mid f post
  /-- No successful walk witnesses `Func.revert`. -/
  noRevert : ∀ {fs : List Func} {sevm : Sevm} {pre post : Devm},
    ¬ R fs sevm pre Func.revert post
  /-- Every walk is in particular a source walk, so a generic trace can still
  reach a lemma stated only at `Func.Run`.  This is the direction that costs
  nothing: the compiled relation pins the gas the source relation only
  bounds. -/
  toRun : ∀ {fs : List Func} {sevm : Sevm} {pre post : Devm} {f : Func},
    R fs sevm pre f post → Func.Run fs sevm pre f post

instance : Func.WalkInv Func.Run where
  toRun := id
  next := of_run_next
  branch := of_run_branch
  call := fun h => by
    obtain ⟨f, mid, hget, hburn, hrun⟩ := of_run_call h
    exact ⟨f, mid, hget, hburn, hrun⟩
  noRevert := not_run_revert

/-- A `Line` prefix, derived from `next` rather than assumed. -/
theorem Func.WalkInv.prepend
    {R : List Func → Sevm → Devm → Func → Devm → Prop} [Func.WalkInv R]
    {fs : List Func} {sevm : Sevm} {post : Devm} {l : Line} {f : Func} :
    ∀ {pre : Devm}, R fs sevm pre (l +++ f) post →
      ∃ mid, Line.Run sevm pre l mid ∧ R fs sevm mid f post := by
  induction l with
  | nil => exact fun h => ⟨_, Line.Run.nil, h⟩
  | cons i l ih =>
    intro pre h
    obtain ⟨mid, hstep, hrest⟩ := Func.WalkInv.next h
    obtain ⟨fin, hline, hf⟩ := ih hrest
    exact ⟨fin, Line.Run.cons hstep hline, hf⟩

/-- The zero arm, selected by a known stack prefix rather than by inspecting
the branch word. -/
theorem Func.WalkInv.zero_branch_of_prefix
    {R : List Func → Sevm → Devm → Func → Devm → Prop} [Func.WalkInv R]
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {left right : Func}
    {xs : Stack}
    (hp : (0 : B256) :: xs <<+ pre.stack)
    (run : R fs sevm pre (Func.branch left right) post) :
    ∃ armPre, Devm.PopBurn [0] pre armPre ∧ R fs sevm armPre left post ∧
      xs <<+ armPre.stack := by
  rcases Func.WalkInv.branch run with
    ⟨mid, hpop, harm⟩ | ⟨w, mid, mid', hw, hpop, -, -⟩
  · exact ⟨mid, hpop, harm, (popBurn_pref hpop hp).2⟩
  · exact absurd (popBurn_pref hpop hp).1 hw

/-- Composing the branch pop with the jumped arm's burn.  Both relations fix
everything but gas and only relax it, so the composite is again a pop. -/
theorem Devm.PopBurn.trans_burn {xs : List B256} {a b c : Devm}
    (hp : Devm.PopBurn xs a b) (hb : Devm.Burn b c) : Devm.PopBurn xs a c :=
  { stack := by rw [← hb.stack]; exact hp.stack
    memory := hp.memory.trans hb.memory,
    gasLeft := le_trans hb.gasLeft hp.gasLeft,
    logs := hp.logs.trans hb.logs,
    refundCounter := hp.refundCounter.trans hb.refundCounter,
    output := hp.output.trans hb.output,
    accountsToDelete := hp.accountsToDelete.trans hb.accountsToDelete,
    returnData := hp.returnData.trans hb.returnData,
    error := hp.error.trans hb.error,
    accessedAddresses := hp.accessedAddresses.trans hb.accessedAddresses,
    accessedStorageKeys := hp.accessedStorageKeys.trans hb.accessedStorageKeys,
    state := hp.state.trans hb.state,
    createdAccounts := hp.createdAccounts.trans hb.createdAccounts,
    transientStorage := hp.transientStorage.trans hb.transientStorage }

/-- The nonzero arm, selected the same way.  The jumped arm's extra burn is
folded into the pop, so this has the same four-part shape as the zero arm. -/
theorem Func.WalkInv.succ_branch_of_prefix
    {R : List Func → Sevm → Devm → Func → Devm → Prop} [Func.WalkInv R]
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {left right : Func}
    {w : B256} {xs : Stack}
    (hw : w ≠ 0) (hp : w :: xs <<+ pre.stack)
    (run : R fs sevm pre (Func.branch left right) post) :
    ∃ armPre, Devm.PopBurn [w] pre armPre ∧ R fs sevm armPre right post ∧
      xs <<+ armPre.stack := by
  rcases Func.WalkInv.branch run with
    ⟨mid, hpop, -⟩ | ⟨w', mid, mid', hw', hpop, hburn, harm⟩
  · exact absurd (popBurn_pref hpop hp).1.symm hw
  · obtain rfl : w' = w := (popBurn_pref hpop hp).1
    refine ⟨mid', hpop.trans_burn hburn, harm, ?_⟩
    rw [← hburn.stack]
    exact (popBurn_pref hpop hp).2

/-- The zero arm of a guard whose nonzero arm reverts. -/
theorem Func.WalkInv.branch_revert
    {R : List Func → Sevm → Devm → Func → Devm → Prop} [Func.WalkInv R]
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {f : Func}
    (h : R fs sevm pre (Func.revert <?> f) post) :
    ∃ mid, Devm.PopBurn [0] pre mid ∧ R fs sevm mid f post := by
  rcases Func.WalkInv.branch h with ⟨mid, hpop, hrun⟩ | ⟨w, mid, mid', _, _, _, hrun⟩
  · exact ⟨mid, hpop, hrun⟩
  · exact absurd hrun Func.WalkInv.noRevert

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
theorem Linst.not_run_revert_ok {sevm : Sevm} {devm post : Devm}
    (run : Linst.Run sevm devm .revert (.ok post)) : False := by
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

/-- `Func.revertData` cannot end in a successful outcome.  This is the exact
compiled-walk elimination seam: it peels the generated constant-word stores
and reaches the terminal `REVERT`, without a fuel bound or evaluator result. -/
theorem Func.RunCompiledTo.not_ok_revertData
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {blob : Bytes}
    (run : Func.RunCompiledTo fs sevm pre (Func.revertData blob) (.ok post)) :
    False := by
  unfold Func.revertData at run
  apply prependStoresRev_not_ok (iws := (bytesWords blob).zipIdx) ?_ run
  intro innerPre innerPost innerRun
  obtain ⟨_, -, innerRun⟩ := runCompiledTo_next_inv innerRun
  obtain ⟨_, -, innerRun⟩ := runCompiledTo_next_inv innerRun
  exact Linst.not_run_revert_ok (runCompiledTo_last_inv innerRun)

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

private lemma of_run_revert_empty {sevm : Sevm} {devm : Devm} {s : List B256}
    {ex : Execution}
    (h_stk : devm.stack = (0 : B256) :: (0 : B256) :: s)
    (h_run : Linst.Run sevm devm .revert ex) :
    ∃ post, ex = .error (.revert, post) ∧ post.output = [] := by
  have h_eq : Linst.run sevm devm .revert = ex := h_run
  have h_gas : devm.extCost
      [⟨((0 : B256)).toNat, ((0 : B256)).toNat⟩] ≤ devm.gasLeft := by
    rw [show ((0 : B256)).toNat = 0 from rfl, Devm.extCost_empty_window]
    exact Nat.zero_le _
  refine ⟨_, h_eq.symm.trans (Linst.run_revert_eq_error h_stk h_gas rfl), ?_⟩
  show (devm.memory.read ((0 : B256)).toNat ((0 : B256)).toNat).1 = []
  rfl

/-- `Func.revert` reverts with an empty payload from an arbitrary compiled walk. -/
theorem runCompiledTo_revert_inv {fs : List Func} {sevm : Sevm} {devm : Devm}
    {ex : Execution} (run : Func.RunCompiledTo fs sevm devm Func.revert ex) :
    ∃ post, ex = .error (.revert, post) ∧ post.output = [] := by
  rw [Func.revert] at run
  obtain ⟨d1, r1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨d2, r2, run⟩ := runCompiledTo_next_inv run
  have hrev := runCompiledTo_last_inv run
  have p1 := of_run_pushB256 (Ninst.Run.of_runCompiled r1)
  have p2 := of_run_pushB256 (Ninst.Run.of_runCompiled r2)
  have hstk : d2.stack = (0 : B256) :: (0 : B256) :: devm.stack := by
    rw [p2.stack, p1.stack]; rfl
  exact of_run_revert_empty hstk hrev

/-- The successful compiled walk as a five-place relation.  A generic trace is
instantiated at this name — `nonzeroCaller_trace (R := Func.RunOk) …` — because
recovering the outcome wrapper from `Func.RunCompiledTo … (.ok post)` is a
higher-order unification Lean will not guess. -/
abbrev Func.RunOk (fs : List Func) (sevm : Sevm) (pre : Devm) (f : Func)
    (post : Devm) : Prop :=
  Func.RunCompiledTo fs sevm pre f (.ok post)

/-- The gas-exact compiled walk meets the shared inversion vocabulary: each
principle is its compiled counterpart with the cost forgotten.  The `.succ`
arm has no separate `Devm.Burn` step — the compiled relation folds the
jumpdest into the pop's cost — so the source shape is met at a reflexive
burn. -/
instance : Func.WalkInv Func.RunOk where
  next h := by
    obtain ⟨mid, hstep, hrest⟩ := runCompiledTo_next_inv h
    exact ⟨mid, Ninst.Run.of_runCompiled hstep, hrest⟩
  branch h := by
    rcases runCompiledTo_branch_inv h with
      ⟨mid, -, hpop, hrun⟩ | ⟨w, mid, hne, -, hpop, hrun⟩
    · exact Or.inl ⟨mid, Devm.PopBurn.of_popBurnBy hpop, hrun⟩
    · exact Or.inr ⟨w, mid, mid, hne, Devm.PopBurn.of_popBurnBy hpop,
        Devm.Burn.refl, hrun⟩
  call h := by
    cases h with
    | call hget _ hburn hrest =>
      exact ⟨_, _, hget, Devm.Burn.of_burnBy hburn, hrest⟩
  noRevert h := by
    obtain ⟨_, hex, -⟩ := runCompiledTo_revert_inv h
    exact absurd hex (by simp)
  toRun h := Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok h)

/-- A compiled walk of `nonpayable body` at nonzero call value takes the
empty-revert arm. No premise about `body` is admitted, so the compiler guard
precedes every decoder, authorization check, and body effect. -/
theorem Func.RunCompiledTo.nonpayable_revert_of_value_nonzero
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {body : Func} {tail : Stack}
    (valueNonzero : sevm.value ≠ 0)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre (nonpayable body) out) :
    ∃ post,
      out = .error (.revert, post) ∧
      post.output = [] := by
  unfold nonpayable at run
  obtain ⟨valuePost, qvalue, run⟩ := runCompiledTo_next_inv run
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have pValue := prefix_of_push
    (of_run_callvalue (Ninst.Run.of_runCompiled qvalue)) hp
  have pTest := prefix_of_iszero (Ninst.Run.of_runCompiled qzero) pValue
  have pZero : (0 : B256) :: tail <<+ testPre.stack := by
    simpa [B256.eqCheck, valueNonzero] using pTest
  obtain ⟨revertPre, _, revertRun, _⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  exact runCompiledTo_revert_inv revertRun

private lemma of_run_revert_window {sevm : Sevm} {devm : Devm} {i sz : B256}
    {s : List B256} {ex : Execution}
    (h_stk : devm.stack = i :: sz :: s)
    (h_run : Linst.Run sevm devm .revert ex) :
    (∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, ex = .error (.revert, post) ∧
        post.output = (devm.memory.read i.toNat sz.toNat).1) := by
  have h_eq : Linst.run sevm devm .revert = ex := h_run
  rcases Nat.lt_or_ge devm.gasLeft (devm.extCost [⟨i.toNat, sz.toNat⟩])
    with h_gas | h_gas
  · have h_oog : Linst.run sevm devm .revert
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
  · exact Or.inr ⟨_, h_eq.symm.trans (Linst.run_revert_eq_error h_stk h_gas rfl),
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

/-- `Func.revertSelector` reverts with its four-byte payload, or can run out of gas
on the final nonempty revert window. -/
theorem runCompiledTo_revertSelector_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {data : Bytes} {hlen : data.length = 4} {ex : Execution}
    (run : Func.RunCompiledTo fs sevm devm (Func.revertSelector data hlen) ex) :
    (∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, ex = .error (.revert, post) ∧ post.output = data) := by
  rw [Func.revertSelector] at run
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
  rcases of_run_revert_window hstk5 hrev with h_oog | ⟨post, hpost, hout⟩
  · exact Or.inl h_oog
  · refine Or.inr ⟨post, hpost, ?_⟩
    rw [hout, hm5,
      show ((28 : B256)).toNat = 28 from rfl,
      show ((4 : B256)).toNat = 4 from rfl,
      read_selector_of_write_zero (B256.length_toBytes _),
      toBytes_toB256_drop28 data hlen]

/-- Invert the constant-store prefix while retaining its exact memory image
and the three state components relevant to a panic frame. -/
theorem runCompiledTo_prependStoresRev_frame_inv
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {stores : List (B256 × Nat)} {rest : Func} {ex : Execution}
    (hbound : ∀ store ∈ stores, 32 * store.2 < 2 ^ 256)
    (run : Func.RunCompiledTo fs sevm pre
      (prependStoresRev stores rest) ex) :
    ∃ mid,
      Func.RunCompiledTo fs sevm mid rest ex ∧
      Devm.getStor pre = Devm.getStor mid ∧
      pre.transientStorage = mid.transientStorage ∧
      pre.logs = mid.logs ∧
      mid.memory = Mem.writeStoresRev pre.memory stores := by
  induction stores generalizing pre rest with
  | nil =>
      exact ⟨pre, run, rfl, rfl, rfl, rfl⟩
  | cons store stores ih =>
      have hhead : 32 * store.2 < 2 ^ 256 := hbound store (by simp)
      have htail : ∀ item ∈ stores, 32 * item.2 < 2 ^ 256 := by
        intro item hitem
        exact hbound item (by simp [hitem])
      change Func.RunCompiledTo fs sevm pre
        (prependStoresRev stores
          (prependStore store.1 store.2 rest)) ex at run
      obtain ⟨storePre, hstorePre, hstorPrefix, htransientPrefix,
        hlogsPrefix, hmemoryPrefix⟩ := ih htail run
      unfold prependStore at hstorePre
      obtain ⟨wordPost, hpushWord, hstorePre⟩ :=
        runCompiledTo_next_inv hstorePre
      obtain ⟨indexPost, hpushIndex, hstorePre⟩ :=
        runCompiledTo_next_inv hstorePre
      obtain ⟨mid, hmstore, hrest⟩ := runCompiledTo_next_inv hstorePre
      have rpushWord := Ninst.Run.of_runCompiled hpushWord
      have rpushIndex := Ninst.Run.of_runCompiled hpushIndex
      have rmstore := Ninst.Run.of_runCompiled hmstore
      have pword := of_run_pushB256 rpushWord
      have pindex := of_run_pushB256 rpushIndex
      obtain ⟨index, word, hpop, hmemory⟩ := of_run_mstore_val rmstore
      have hoperands :
          index = Nat.toB256 (32 * store.2) ∧ word = store.1 := by
        unfold Stack.Pop Split at hpop
        rw [pindex.stack, pword.stack] at hpop
        injection hpop with hindex htail
        injection htail with hword _
        exact ⟨hindex.symm, hword.symm⟩
      refine ⟨mid, hrest, ?_, ?_, ?_, ?_⟩
      · exact hstorPrefix.trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rpushWord).trans
            ((Ninst.Hinv.inv (f := Devm.getStor) rpushIndex).trans
              (Ninst.Hinv.inv (f := Devm.getStor) rmstore)))
      · exact htransientPrefix.trans
          ((Ninst.Hinv.inv (f := Devm.transientStorage) rpushWord).trans
            ((Ninst.Hinv.inv (f := Devm.transientStorage) rpushIndex).trans
              (Ninst.Hinv.inv (f := Devm.transientStorage) rmstore)))
      · exact hlogsPrefix.trans
          (pword.logs.trans
            (pindex.logs.trans (Ninst.Hinv.inv (f := Devm.logs) rmstore)))
      · rw [hmemory, hoperands.1, hoperands.2,
          ← pindex.memory, ← pword.memory, hmemoryPrefix,
          B256.toNat_toB256_of_lt hhead]
        rfl

/-- Invert `REVERT` with known operands while retaining its frame effects.
The final window-expansion charge is the only remaining out-of-gas point. -/
theorem of_run_revert_window_frame
    {sevm : Sevm} {devm : Devm} {i sz : B256}
    {tail : List B256} {ex : Execution}
    (hstack : devm.stack = i :: sz :: tail)
    (run : Linst.Run sevm devm .revert ex) :
    (∃ d,
      ex = .error (.halt (.outOfGas .none), d) ∧
      Devm.getStor d = Devm.getStor devm ∧
      d.transientStorage = devm.transientStorage ∧
      d.logs = devm.logs) ∨
    (∃ post,
      ex = .error (.revert, post) ∧
      post.output = (devm.memory.read i.toNat sz.toNat).1 ∧
      Devm.getStor post = Devm.getStor devm ∧
      post.transientStorage = devm.transientStorage ∧
      post.logs = devm.logs) := by
  have heq : Linst.run sevm devm .revert = ex := run
  rcases Nat.lt_or_ge devm.gasLeft
      (devm.extCost [⟨i.toNat, sz.toNat⟩]) with hgas | hgas
  · have hoog : Linst.run sevm devm .revert =
        .error ⟨.halt (.outOfGas .none),
          devm.setMach ⟨tail, devm.memory, devm.gasLeft⟩⟩ := by
      show (do
        let ⟨index, d⟩ ← devm.popToNat
        let ⟨size, d⟩ ← d.popToNat
        let cost := d.extCost [⟨index, size⟩]
        let d ← chargeGas cost d
        let ⟨output, d⟩ := d.memRead index size
        let d := d.withOutput output
        Except.error ⟨.revert, d⟩) = _
      rw [Devm.popToNat_eq_ok hstack]
      simp only [bind, Except.bind]
      rw [Devm.popToNat_eq_ok
        (devm := devm.setMach
          ⟨sz :: tail, devm.memory, devm.gasLeft⟩) rfl]
      simp only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.gasLeft_setMach]
      have hext : (devm.setMach
          ⟨tail, devm.memory, devm.gasLeft⟩).extCost
          [⟨i.toNat, sz.toNat⟩] =
            devm.extCost [⟨i.toNat, sz.toNat⟩] := rfl
      rw [hext]
      have hcharge : chargeGas
          (devm.extCost [⟨i.toNat, sz.toNat⟩])
          (devm.setMach ⟨tail, devm.memory, devm.gasLeft⟩) =
            .error ⟨.halt (.outOfGas .none),
              devm.setMach ⟨tail, devm.memory, devm.gasLeft⟩⟩ := by
        rw [chargeGas_def]
        have hsafe : safeSub
            (devm.setMach ⟨tail, devm.memory, devm.gasLeft⟩).gasLeft
            (devm.extCost [⟨i.toNat, sz.toNat⟩]) = none := by
          unfold safeSub
          rw [if_neg (by simp only [Devm.gasLeft_setMach]; omega)]
        rw [hsafe]
      rw [hcharge]
    exact Or.inl ⟨_, heq.symm.trans hoog, rfl, rfl, rfl⟩
  · let post :=
      ((devm.setMach ⟨tail, devm.memory,
        devm.gasLeft - devm.extCost [⟨i.toNat, sz.toNat⟩]⟩).memRead
          i.toNat sz.toNat).2.withOutput
        (devm.memory.read i.toNat sz.toNat).1
    have hpost : Linst.run sevm devm .revert = .error (.revert, post) := by
      exact Linst.run_revert_eq_error hstack hgas rfl
    have hframe := Linst.run_instructionFrame sevm devm .revert (by decide)
    rw [hpost] at hframe
    refine Or.inr ⟨post, heq.symm.trans hpost, ?_, ?_, ?_, ?_⟩
    · rfl
    · funext owner
      exact (hframe.getStor owner).symm
    · exact hframe.transientStorage.symm
    · dsimp only [post]
      change ((devm.setMach ⟨tail, devm.memory,
        devm.gasLeft - devm.extCost [⟨i.toNat, sz.toNat⟩]⟩).memRead
          i.toNat sz.toNat).2.logs = devm.logs
      let base := devm.setMach ⟨tail, devm.memory,
        devm.gasLeft - devm.extCost [⟨i.toNat, sz.toNat⟩]⟩
      change (base.memRead i.toNat sz.toNat).2.logs = devm.logs
      have hread : (base.memRead i.toNat sz.toNat).2.logs = base.logs := by
        unfold Devm.memRead
        rfl
      exact hread.trans (by rfl)

/-- Invert an arbitrary constant-data reverter, including its final
out-of-gas leg and its exact state frame. -/
theorem runCompiledTo_revertData_frame_inv
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {blob image : Bytes} {ex : Execution}
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hblob : blob.length < 2 ^ 256)
    (hwords : 32 * (bytesWords blob).length < 2 ^ 256)
    (run : Func.RunCompiledTo fs sevm pre (Func.revertData blob) ex) :
    (∃ d,
      ex = .error (.halt (.outOfGas .none), d) ∧
      Devm.getStor d = Devm.getStor pre ∧
      d.transientStorage = pre.transientStorage ∧
      d.logs = pre.logs) ∨
    (∃ post,
      ex = .error (.revert, post) ∧
      post.output = blob ∧
      Devm.getStor post = Devm.getStor pre ∧
      post.transientStorage = pre.transientStorage ∧
      post.logs = pre.logs) := by
  have hbound : ∀ store ∈ (bytesWords blob).zipIdx,
      32 * store.2 < 2 ^ 256 := by
    intro store hstore
    have hget : (bytesWords blob)[store.2]? = some store.1 :=
      (List.mk_mem_zipIdx_iff_getElem?).mp hstore
    have hindex : store.2 < (bytesWords blob).length :=
      (List.getElem?_eq_some_iff.mp hget).1
    omega
  unfold Func.revertData at run
  obtain ⟨revertPre, htail, hstorPrefix, htransientPrefix,
    hlogsPrefix, hmemory⟩ :=
    runCompiledTo_prependStoresRev_frame_inv hbound run
  obtain ⟨lengthPost, hpushLength, htail⟩ :=
    runCompiledTo_next_inv htail
  obtain ⟨windowPre, hpushZero, hrev⟩ := runCompiledTo_next_inv htail
  have rpushLength := Ninst.Run.of_runCompiled hpushLength
  have rpushZero := Ninst.Run.of_runCompiled hpushZero
  have plength := of_run_pushB256 rpushLength
  have pzero := of_run_pushB256 rpushZero
  have hstack : windowPre.stack =
      (0 : B256) :: Nat.toB256 blob.length :: revertPre.stack := by
    rw [pzero.stack, plength.stack]
    simp only [List.singleton_append]
  have hstorWindow : Devm.getStor pre = Devm.getStor windowPre :=
    hstorPrefix.trans
      ((Ninst.Hinv.inv (f := Devm.getStor) rpushLength).trans
        (Ninst.Hinv.inv (f := Devm.getStor) rpushZero))
  have htransientWindow :
      pre.transientStorage = windowPre.transientStorage :=
    htransientPrefix.trans
      ((Ninst.Hinv.inv (f := Devm.transientStorage) rpushLength).trans
        (Ninst.Hinv.inv (f := Devm.transientStorage) rpushZero))
  have hlogsWindow : pre.logs = windowPre.logs :=
    hlogsPrefix.trans (plength.logs.trans pzero.logs)
  have hmemoryWindow : windowPre.memory =
      Mem.writeStoresRev pre.memory (bytesWords blob).zipIdx :=
    pzero.memory.symm.trans (plength.memory.symm.trans hmemory)
  have hlast := runCompiledTo_last_inv hrev
  rcases of_run_revert_window_frame hstack hlast with
    ⟨d, hex, hstor, htransient, hlogs⟩ |
      ⟨post, hex, houtput, hstor, htransient, hlogs⟩
  · exact Or.inl ⟨d, hex, hstor.trans hstorWindow.symm,
      htransient.trans htransientWindow.symm,
      hlogs.trans hlogsWindow.symm⟩
  · have hpayload : post.output = blob := by
      rw [houtput, hmemoryWindow, B256.toNat_zero,
        B256.toNat_toB256_of_lt hblob,
        Mem.read_writeStoresRev_bytesWords hwf hreads]
    exact Or.inr ⟨post, hex, hpayload, hstor.trans hstorWindow.symm,
      htransient.trans htransientWindow.symm,
      hlogs.trans hlogsWindow.symm⟩

/-- Call-level wrapper for an auxiliary slot known to contain `Func.revertData`.
The conclusion remains explicitly tied to that call walk; no payload is
inferred merely from an error flag. -/
theorem runCompiledTo_call_revertData_frame_inv
    {fs : List Func} {sevm : Sevm} {pre : Devm} {slot : Nat}
    {blob image : Bytes} {ex : Execution}
    (hget : fs[slot]? = some (Func.revertData blob))
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hblob : blob.length < 2 ^ 256)
    (hwords : 32 * (bytesWords blob).length < 2 ^ 256)
    (run : Func.RunCompiledTo fs sevm pre (.call slot) ex) :
    (∃ d,
      ex = .error (.halt (.outOfGas .none), d) ∧
      Devm.getStor d = Devm.getStor pre ∧
      d.transientStorage = pre.transientStorage ∧
      d.logs = pre.logs) ∨
    (∃ post,
      ex = .error (.revert, post) ∧
      post.output = blob ∧
      Devm.getStor post = Devm.getStor pre ∧
      post.transientStorage = pre.transientStorage ∧
      post.logs = pre.logs) := by
  obtain ⟨bodyPre, hburn, bodyRun⟩ := runCompiledTo_call_inv hget run
  have hwfBody : Mem.Wf bodyPre.memory := by
    rw [← hburn.memory]
    exact hwf
  have hreadsBody : Mem.Reads bodyPre.memory image := by
    rw [← hburn.memory]
    exact hreads
  rcases runCompiledTo_revertData_frame_inv hwfBody hreadsBody hblob hwords
      bodyRun with
    ⟨d, hex, hstor, htransient, hlogs⟩ |
      ⟨post, hex, hpayload, hstor, htransient, hlogs⟩
  · exact Or.inl ⟨d, hex,
      hstor.trans (funext (getStor_eq_of_state_eq hburn.state)).symm,
      htransient.trans hburn.transientStorage.symm,
      hlogs.trans hburn.logs.symm⟩
  · exact Or.inr ⟨post, hex, hpayload,
      hstor.trans (funext (getStor_eq_of_state_eq hburn.state)).symm,
      htransient.trans hburn.transientStorage.symm,
      hlogs.trans hburn.logs.symm⟩

/-- A known call to an empty-data `REVERT` body cannot produce `.ok`. -/
theorem Func.RunCompiledTo.not_ok_call_revert
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {slot : Nat}
    (hget : fs[slot]? = some Func.revert)
    (run : Func.RunCompiledTo fs sevm pre (.call slot) (.ok post)) : False := by
  obtain ⟨_, -, bodyRun⟩ := runCompiledTo_call_inv hget run
  rcases runCompiledTo_revert_inv bodyRun with ⟨_, impossible, -⟩
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
theorem Func.RunCompiledTo.zero_branch_of_ok_call_revert
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {rest : Func} {slot : Nat}
    (hget : fs[slot]? = some Func.revert)
    (run : Func.RunCompiledTo fs sevm pre
      (Func.branch rest (.call slot)) (.ok post)) :
    ∃ armPre,
      Devm.PopBurnBy [0] (gVerylow + gHigh) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre rest (.ok post) := by
  exact Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok
    (fun rightRun => Func.RunCompiledTo.not_ok_call_revert hget rightRun) run

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

/-- Prefix-retaining form of `zero_branch_of_ok_call_revert`.  It additionally
identifies the caller's known head with zero and transports its tail across
the branch pop. -/
theorem Func.RunCompiledTo.zero_branch_of_ok_call_revert_of_prefix
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {rest : Func} {slot : Nat} {flag : B256} {xs : Stack}
    (hget : fs[slot]? = some Func.revert)
    (hp : flag :: xs <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (Func.branch rest (.call slot)) (.ok post)) :
    ∃ armPre,
      flag = 0 ∧
      Devm.PopBurnBy [0] (gVerylow + gHigh) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre rest (.ok post) ∧
      xs <<+ armPre.stack := by
  exact Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok_of_prefix
    (fun rightRun => Func.RunCompiledTo.not_ok_call_revert hget rightRun)
    hp run

/-- A known call to a four-byte selector reverter cannot produce `.ok`. -/
theorem Func.RunCompiledTo.not_ok_call_revertSelector
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {slot : Nat}
    {data : Bytes} {hlen : data.length = 4}
    (hget : fs[slot]? = some (Func.revertSelector data hlen))
    (run : Func.RunCompiledTo fs sevm pre (.call slot) (.ok post)) : False := by
  obtain ⟨_, -, bodyRun⟩ := runCompiledTo_call_inv hget run
  rcases runCompiledTo_revertSelector_inv bodyRun with
    ⟨_, impossible⟩ | ⟨_, impossible, -⟩ <;> cases impossible

/-- A known call to an arbitrary-data reverter cannot produce `.ok`. -/
theorem Func.RunCompiledTo.not_ok_call_revertData
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {slot : Nat}
    {blob : Bytes}
    (hget : fs[slot]? = some (Func.revertData blob))
    (run : Func.RunCompiledTo fs sevm pre (.call slot) (.ok post)) : False := by
  obtain ⟨_, -, bodyRun⟩ := runCompiledTo_call_inv hget run
  exact Func.RunCompiledTo.not_ok_revertData bodyRun

/-- One compiled instruction, including a CALL-family crossing that retains a
whole sub-execution, leaves already-installed code where it is.  `CREATE` is
the only opcode that installs code, and it installs it at a fresh account, so
an account whose code is already non-empty keeps exactly that code. -/
lemma Ninst.runCompiled_preserves_getCode
    {sevm : Sevm} {pre post : Devm} {n : Ninst} {owner : Adr}
    (run : Ninst.RunCompiled sevm pre n post)
    (nonempty : (pre.getCode owner).toList ≠ []) :
    post.getCode owner = pre.getCode owner := by
  rcases run with ⟨xl, filled, steps⟩
  have slotCode : Xlot.Rel Devm.CodePreserve xl := by
    rcases xl with _ | ⟨evm, raw⟩
    · trivial
    · rcases filled with ⟨childRun⟩
      cases raw <;> exact Exec.preserves_getCode childRun
  exact Ninst.codePreserve_effectRec n slotCode (steps 0) owner nonempty


/-- A whole successful compiled walk leaves already-installed code where it is.

This lifts `Ninst.runCompiled_preserves_getCode` over every constructor of the
compiled walk, including internal `Func.call` jumps and CALL-family crossings
that retain a sub-execution.  It is what lets a configuration premise about an
installed program survive an arbitrary stretch of a contract body without
threading state through each individual step. -/
lemma Func.runCompiledTo_preserves_getCode
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {f : Func} {owner : Adr}
    (run : Func.RunCompiledTo fs sevm pre f (.ok post))
    (nonempty : (pre.getCode owner).toList ≠ []) :
    post.getCode owner = pre.getCode owner := by
  have sourceRun : Func.Run fs sevm pre f post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  refine Func.effect codePreserve_refl_trans.2 ?_ ?_
    (Ninst.effect_of_effectRec codePreserve_refl_trans.1
      codePreserve_refl_trans.2 Ninst.codePreserve_effectRec
      Jinst.codePreserve_effect Linst.codePreserve_effect)
    Linst.codePreserve_effect sourceRun owner nonempty
  · intro xs a b pop account _
    exact (getCode_eq_of_state_eq pop.state account).symm
  · intro a b burn account _
    exact (getCode_eq_of_state_eq burn.state account).symm


/-- The frame a quiet stretch of a compiled walk leaves behind: neither the
persistent world nor the event log moves.  Arithmetic bodies that only touch
memory and the stack satisfy it, and it composes along a walk, so a
configuration premise stated at one point carries to any later point the frame
reaches. -/
def Devm.QuietFrame (pre post : Devm) : Prop :=
  pre.state = post.state ∧ pre.logs = post.logs

theorem Devm.QuietFrame.rfl' (d : Devm) : Devm.QuietFrame d d := ⟨rfl, rfl⟩

theorem Devm.QuietFrame.mk' {a b : Devm} (state : a.state = b.state)
    (logs : a.logs = b.logs) : Devm.QuietFrame a b := ⟨state, logs⟩

theorem Devm.QuietFrame.trans {a b c : Devm}
    (first : Devm.QuietFrame a b) (second : Devm.QuietFrame b c) :
    Devm.QuietFrame a c :=
  ⟨first.1.trans second.1, first.2.trans second.2⟩

/-- Every `Line` whose instructions preserve both projections is quiet. -/
theorem Devm.QuietFrame.ofLine {sevm : Sevm} {a b : Devm} {line : Line}
    (stateInv : Line.Inv Devm.state line) (logsInv : Line.Inv Devm.logs line)
    (run : Line.Run sevm a line b) : Devm.QuietFrame a b :=
  ⟨Line.of_inv Devm.state stateInv run, Line.of_inv Devm.logs logsInv run⟩

/-- One quiet instruction. -/
theorem Devm.QuietFrame.ofNinst {sevm : Sevm} {a b : Devm} {i : Ninst}
    [Ninst.Hinv Devm.state i] [Ninst.Hinv Devm.logs i]
    (run : Ninst.Run sevm a i b) : Devm.QuietFrame a b :=
  ⟨Ninst.Hinv.inv (f := Devm.state) run, Ninst.Hinv.inv (f := Devm.logs) run⟩

theorem Devm.QuietFrame.ofPopBurnBy {xs : List B256} {cost : Nat}
    {a b : Devm} (pop : Devm.PopBurnBy xs cost a b) : Devm.QuietFrame a b :=
  ⟨pop.state, pop.logs⟩

theorem Devm.QuietFrame.ofBurnBy {cost : Nat} {a b : Devm}
    (burn : Devm.BurnBy cost a b) : Devm.QuietFrame a b :=
  ⟨burn.state, burn.logs⟩

/-- The gas-forgetting counterparts, for a walk inverted through
`Func.WalkInv`. -/
theorem Devm.QuietFrame.ofPopBurn {xs : List B256} {a b : Devm}
    (pop : Devm.PopBurn xs a b) : Devm.QuietFrame a b :=
  ⟨pop.state, pop.logs⟩

theorem Devm.QuietFrame.ofBurn {a b : Devm}
    (burn : Devm.Burn a b) : Devm.QuietFrame a b :=
  ⟨burn.state, burn.logs⟩

/-- **Dispatch exhaustiveness.**  A compiled walk through `dispatchWith` that
*succeeds* must have matched one of the tree's selectors.

The contrapositive is the content: every miss falls through to the revert slot,
and a revert is not a success.  This is what lets a whole-program theorem case
on the selector table and know the case analysis is complete -- without it, a
statement about "any successful message" would have to leave the unmatched
selector as an unproved gap. -/
theorem sig_mem_of_dispatchWith_ok :
    ∀ {dt : DispatchTree} {sig : B256} {fs : List Func} {k : Nat}
      {sevm : Sevm} {s post : Devm} {tail : Stack},
      fs[k]? = some Func.revert →
      sig :: tail <<+ s.stack →
      Func.RunCompiledTo fs sevm s (dispatchWith k dt) (.ok post) →
      ∃ body, (sig, body) ∈ dt := by
  intro dt
  induction dt with
  | leaf w p =>
    intro sig fs k sevm s post tail revertLookup hp run
    simp only [dispatchWith] at run
    obtain ⟨pushPost, pushRun, run⟩ := runCompiledTo_next_inv run
    have pushed := of_run_pushB256 (Ninst.Run.of_runCompiled pushRun)
    have hp1 : w :: sig :: tail <<+ pushPost.stack :=
      prefix_of_push pushed hp
    obtain ⟨testPost, testRun, branchRun⟩ := runCompiledTo_next_inv run
    have testPrefix :=
      prefix_of_eq (Ninst.Run.of_runCompiled testRun) hp1
    by_cases hit : w = sig
    · exact ⟨p, by rw [hit]; exact rfl⟩
    · exfalso
      have zeroPrefix : (0 : B256) :: tail <<+ testPost.stack := by
        simpa [B256.eqCheck, hit] using testPrefix
      obtain ⟨missPre, -, missRun, -⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
      exact Func.RunCompiledTo.not_ok_call_revert revertLookup missRun
  | fork tl tr ihl ihr =>
    intro sig fs k sevm s post tail revertLookup hp run
    simp only [dispatchWith] at run
    obtain ⟨dupPost, dupRun, run⟩ := runCompiledTo_next_inv run
    have dupPrefix : sig :: sig :: tail <<+ dupPost.stack :=
      prefix_of_dup_val (Ninst.Run.of_runCompiled dupRun) (by show_nth) hp
    obtain ⟨pushPost, pushRun, run⟩ := runCompiledTo_next_inv run
    have pushed := of_run_pushB256 (Ninst.Run.of_runCompiled pushRun)
    have hp1 : leftmostFsig tr :: sig :: sig :: tail <<+ pushPost.stack :=
      prefix_of_push pushed dupPrefix
    obtain ⟨testPost, testRun, branchRun⟩ := runCompiledTo_next_inv run
    have testPrefix :=
      prefix_of_gt (Ninst.Run.of_runCompiled testRun) hp1
    rcases runCompiledTo_branch_inv branchRun with left | right
    · obtain ⟨leftPre, -, leftPop, leftRun⟩ := left
      have leftPrefix : sig :: tail <<+ leftPre.stack :=
        (popBurn_pref (Devm.PopBurn.of_popBurnBy leftPop) testPrefix).2
      obtain ⟨body, mem⟩ := ihr revertLookup leftPrefix leftRun
      exact ⟨body, Or.inr mem⟩
    · obtain ⟨flag, rightPre, -, -, rightPop, rightRun⟩ := right
      have rightPrefix : sig :: tail <<+ rightPre.stack :=
        (popBurn_pref (Devm.PopBurn.of_popBurnBy rightPop) testPrefix).2
      obtain ⟨body, mem⟩ := ihl revertLookup rightPrefix rightRun
      exact ⟨body, Or.inl mem⟩


end Blanc
