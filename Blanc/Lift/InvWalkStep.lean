import Blanc.Lift.InvWalkWorld
import Blanc.Lift.WalkSteps
import Blanc.AddressSlotProofs
import Blanc.ForwardStorageAccess
import Blanc.Lift.MapSlot
import Blanc.Lift.HistAccessWalk
import Blanc.HistoricalFork

/-!
# A one-lemma inversion step, and the inversion helpers of solc walks

`stepX` computes the successor walk state `St b' S' M'` of the straight-line instructions an
inversion walk crosses (stack, memory, the selected `SLOAD`/`SSTORE` bases, `LOG3`), and
`ri_stepX` inverts any of them at once; the `istep` tactic runs one such step (or a `JUMPDEST`)
of a cut run, so a straight-line segment is `repeat istep h`.  `ibranch` crosses a conditional
jump whose other arm only reverts (`SFunc.noOk`).  `ric_callR` enters an internal callee that
cannot halt; `SFunc.noExit`/`NoExitSet` with `SFunc.RunP.false_of_noExit` close an arm that can
only revert through loops and gotos (a solc error-message copy).  `ret_named` names a returned
state by its storage.  The word facts read solc's comparison flags, mapping-slot scratch
writes, address masks and SafeMath guards as natural-number facts.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- The successor of a straight-line instruction over the walk state `St b S M G`, when the
instruction is one of the forms below: base, stack and memory. -/
def stepX (sevm : Sevm) : Ninst → Devm → List B256 → Mem → Option (Devm × List B256 × Mem)
  | .push xs _, b, S, M => some (b, xs.toB256 :: S, M)
  | .reg (.dup n), b, S, M => S[n.val]?.map fun w => (b, w :: S, M)
  | .reg (.swap n), b, S, M => (Jaune.List.swap S n.val).map fun S' => (b, S', M)
  | .reg .pop, b, _ :: S, M => some (b, S, M)
  | .reg .and, b, x :: y :: S, M => some (b, (x &&& y) :: S, M)
  | .reg .or, b, x :: y :: S, M => some (b, (x ||| y) :: S, M)
  | .reg .add, b, x :: y :: S, M => some (b, (x + y) :: S, M)
  | .reg .sub, b, x :: y :: S, M => some (b, (x - y) :: S, M)
  | .reg .div, b, x :: y :: S, M => some (b, (x / y) :: S, M)
  | .reg .eq, b, x :: y :: S, M => some (b, B256.eqCheck x y :: S, M)
  | .reg .lt, b, x :: y :: S, M => some (b, B256.ltCheck x y :: S, M)
  | .reg .gt, b, x :: y :: S, M => some (b, B256.gtCheck x y :: S, M)
  | .reg .shr, b, x :: y :: S, M => some (b, (y >>> x.toNat) :: S, M)
  | .reg .iszero, b, x :: S, M => some (b, B256.eqCheck x 0 :: S, M)
  | .reg .not, b, x :: S, M => some (b, (~~~ x) :: S, M)
  | .reg .caller, b, S, M => some (b, sevm.caller.toB256 :: S, M)
  | .reg .callvalue, b, S, M => some (b, sevm.value :: S, M)
  | .reg .calldatasize, b, S, M => some (b, sevm.data.length.toB256 :: S, M)
  | .reg .calldataload, b, x :: S, M => some (b, Sevm.dataWord sevm x :: S, M)
  | .reg .mload, b, i :: S, M =>
      some (b, Bytes.toB256 (M.read i.toNat 32).1 :: S, (M.read i.toNat 32).2)
  | .reg .mstore, b, i :: v :: S, M => some (b, S, M.write i.toNat v.toBytes)
  | .reg .codecopy, b, di :: ci :: sz :: S, M =>
      some (b, S, M.write di.toNat (sevm.code.sliceD ci.toNat sz.toNat (Linst.toUInt8 .stop)))
  | .reg .keccak256, b, i :: sz :: S, M =>
      some (b, (M.read i.toNat sz.toNat).1.keccak :: S, (M.read i.toNat sz.toNat).2)
  | .reg .sload, b, k :: S, M =>
      some (afterSload sevm b k, b.getStorVal sevm.currentTarget k :: S, M)
  | .reg .sstore, b, k :: v :: S, M => some (afterSstore sevm b k v, S, M)
  | .reg (.log 3), b, i :: sz :: t1 :: t2 :: t3 :: S, M =>
      some (b.addLog ⟨sevm.currentTarget, [t1, t2, t3], (M.read i.toNat sz.toNat).1⟩, S,
        (M.read i.toNat sz.toNat).2)
  | _, _, _, _ => none

private theorem ri_stepX_of_storageFork {sevm : Sevm} {b b' d : Devm} {S S' : List B256} {M M' : Mem} {G : Nat}
    {n : Ninst} (storageFork : (n = .reg .sload ∨ n = .reg .sstore) →
      ShanghaiOnwards sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b S M G) n d) (hs : stepX sevm n b S M = some (b', S', M')) :
    ∃ G', d = St b' S' M' G' := by
  unfold stepX at hs
  split at hs
  · cases hs; exact ri_push h
  · rename_i n
    rcases hget : S[n.val]? with _ | w <;> rw [hget] at hs <;> cases hs
    exact ri_dup hget h
  · rename_i n
    rcases hsw : Jaune.List.swap S n.val with _ | T <;> rw [hsw] at hs <;> cases hs
    exact ri_swap hsw h
  · cases hs; exact ri_pop h
  · cases hs; exact ri_and h
  · cases hs; exact ri_or h
  · cases hs; exact ri_add h
  · cases hs; exact ri_sub h
  · cases hs; exact ri_div h
  · cases hs; exact ri_eq h
  · cases hs; exact ri_lt h
  · cases hs; exact ri_gt h
  · cases hs; exact ri_shr h
  · cases hs; exact ri_iszero h
  · cases hs; exact ri_not h
  · cases hs; exact ri_caller h
  · cases hs; exact ri_callvalue h
  · cases hs; exact ri_calldatasize h
  · cases hs; exact ri_calldataload h
  · cases hs; exact ri_mload h
  · cases hs; exact ri_mstore h
  · cases hs; exact ri_codecopy h
  · cases hs; exact ri_keccak h
  · cases hs; exact ri_sload (storageFork (.inl rfl)) h
  · cases hs; exact ri_sstore (storageFork (.inr rfl)) h
  · cases hs; exact ri_log3 h
  · cases hs

/-- The original covered-fork step inversion. -/
theorem ri_stepX {sevm : Sevm} {b b' d : Devm} {S S' : List B256} {M M' : Mem} {G : Nat}
    {n : Ninst} (fork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b S M G) n d) (hs : stepX sevm n b S M = some (b', S', M')) :
    ∃ G', d = St b' S' M' G' :=
  ri_stepX_of_storageFork (fun _ => fork) h hs

/-- A nonstorage straight-line step is inverted under the actual rules, with no fork premise. -/
theorem ri_stepX_nonstorage {sevm : Sevm} {b b' d : Devm} {S S' : List B256}
    {M M' : Mem} {G : Nat} {n : Ninst}
    (notSload : n ≠ .reg .sload) (notSstore : n ≠ .reg .sstore)
    (h : Ninst.Run sevm (St b S M G) n d) (hs : stepX sevm n b S M = some (b', S', M')) :
    ∃ G', d = St b' S' M' G' :=
  ri_stepX_of_storageFork (fun storage => (storage.elim notSload notSstore).elim) h hs

/-- `stepX` under the frame's actual access schedule and refund regime: `SLOAD` and `SSTORE` take
their historical successors `afterSloadH` and `afterSstoreH`, every other instruction is `stepX`'s. -/
def stepXH (sevm : Sevm) : Ninst → Devm → List B256 → Mem → Option (Devm × List B256 × Mem)
  | .reg .sload, b, k :: S, M =>
      some (afterSloadH sevm b k, b.getStorVal sevm.currentTarget k :: S, M)
  | .reg .sstore, b, k :: v :: S, M => some (afterSstoreH sevm b k v, S, M)
  | n, b, S, M => stepX sevm n b S M

/-- The historical step inversion: from a `HistFork` premise, so Byzantium through BPO2. -/
theorem ri_stepXH {sevm : Sevm} {b b' d : Devm} {S S' : List B256} {M M' : Mem} {G : Nat}
    {n : Ninst} (fork : HistFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b S M G) n d) (hs : stepXH sevm n b S M = some (b', S', M')) :
    ∃ G', d = St b' S' M' G' := by
  by_cases hl : n = .reg .sload
  · subst hl
    rcases S with _ | ⟨k, S⟩
    · exact absurd hs (by simp only [stepXH, stepX, reduceCtorEq, not_false_eq_true])
    · simp only [stepXH, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact ri_sloadH fork.bal_none h
  by_cases hw : n = .reg .sstore
  · subst hw
    rcases S with _ | ⟨k, _ | ⟨v, S⟩⟩
    · exact absurd hs (by simp only [stepXH, stepX, reduceCtorEq, not_false_eq_true])
    · exact absurd hs (by simp only [stepXH, stepX, reduceCtorEq, not_false_eq_true])
    · simp only [stepXH, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact ri_sstoreH fork.stateGas_none fork.bal_none h
  · have e : stepXH sevm n b S M = stepX sevm n b S M := by
      unfold stepXH
      split
      · exact absurd rfl hl
      · exact absurd rfl hw
      · rfl
    exact ri_stepX_nonstorage hl hw h (e.symm.trans hs)

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- Succeeds exactly when the local context holds a hypothesis headed by `Blanc.CoveredFork`
(`covered`) or by `Blanc.HistFork`: `istep` picks its fork lemma by it, because a failed
`‹CoveredFork _›` inside a term is logged, not thrown, so `first` would not fall through. -/
elab "fork_hyp_in_ctx " which:ident : tactic => withMainContext do
  let head := if which.getId.eraseMacroScopes == `covered then ``Blanc.CoveredFork else ``Blanc.HistFork
  let found := (← getLCtx).decls.foldl (init := false) fun found decl? =>
    found || match decl? with
      | some decl => decl.type.getAppFn.isConstOf head
      | none => false
  unless found do throwError "no {which.getId} fork hypothesis in context"

/-- One straight-line step of a cut run, over the covered forks or, from a `HistFork` hypothesis,
over every historical fork (`SLOAD`/`SSTORE` then leave `afterSloadH`/`afterSstoreH`). -/
macro "istep " h:ident : tactic => `(tactic|
  first
  | (have h' := ric_dest $h; clear $h; obtain ⟨_, $h:ident⟩ := h')
  | (fork_hyp_in_ctx covered
     have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_stepX ‹CoveredFork _› hd rfl
     try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e
     subst e; clear hd)
  | (fork_hyp_in_ctx hist
     have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
     obtain ⟨_, e⟩ := ri_stepXH ‹HistFork _› hd rfl
     try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e
     subst e; clear hd))

/-- A solc mapping slot from its scratch writes (`mstore(0, key)`, `mstore(32, base)`,
`keccak256(0, 64)`), with the pushed offsets as the code has them. -/
theorem keccak_scratch (μ : Mem) (key base : B256) :
    (((μ.write (Bytes.toB256 [0]).toNat key.toBytes).write (Bytes.toB256 [32]).toNat
      base.toBytes).read (Bytes.toB256 [0]).toNat (Bytes.toB256 [64]).toNat).1.keccak =
      Blanc.Lift.mapSlot key base := by
  have e := Mem.read_two_word_writes_at_raw μ 0 key base
  exact congrArg Bytes.keccak e



/-- A conditional jump of a cut run: the arm that reverts closes, the other is kept with its
condition. -/
macro "ibranch " h:ident c:ident : tactic => `(tactic|
  (have h' := ric_branch $h; clear $h; rcases h' with ⟨$c, _, $h⟩ | ⟨$c, _, $h⟩ <;>
    try (exact (SFunc.RunCutP.false_of_noOk $h (by decide)).elim)))


/-! ## Word facts of the comparison flags -/





theorem word_ff20 (x : B256) :
    (x &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) = x.toAdr.toB256 := by
  rw [B256.and_comm]
  exact ff20_and_word x




end Blanc.Lift
