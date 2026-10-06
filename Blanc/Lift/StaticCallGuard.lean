import Blanc.Lift.StaticCall
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.ExactWalkMemory
import Blanc.Lift.ExactWalkCutOps
/-! Literal STATICCALL success and ABI return-width guards with retained provenance. -/

namespace Blanc.Lift
open Jaune

/-- The call-success guard retains the original instruction witness and complete reply. -/
theorem staticCallGuard_invP {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256}
    {C : List Nat} {M : Mem} {G : Nat} {z t ii is oi os : B256} {seg : Seg}
    {callTree failureTree successTree : SFunc} (destination : Bytes)
    (le : destination.length ≤ 32)
    (shape : callTree = .dest (.next (.reg .pop) (.next (.reg .gas)
      (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
        (.next (.reg .iszero) (.next (.push destination le)
          (.branch failureTree successTree)))))))))
    (project : ∀ {s d i d'}, P s d i d' → Ninst.Run s d i d')
    (fork : CoveredFork sevm.benvStat.fork) (noFail : failureTree.noOk = true)
    (run : SFunc.RunCutP P fs sevm C (St b (z :: t :: ii :: is :: oi :: os :: S) M G)
      callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      P sevm (St b (gw :: t :: ii :: is :: oi :: os :: S) M callGas) (.exec .staticcall) d ∧
      StaticCallPost b d S M ii is oi os 1 out ∧ out.length < 2^256 ∧
      StaticAnswered sevm b t.toAdr (M.read ii.toNat is.toNat).1 out ∧
      SFunc.RunCutP P fs sevm C
        (St d (0 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
          oi.toNat (out.take os.toNat)) tailGas) successTree seg := by
  rw [shape] at run
  obtain ⟨_, h⟩ := ric_destP run
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨gw, callGas, rfl⟩ := ri_gas (project hs)
  obtain ⟨d, hcall, h⟩ := ric_nextP h
  obtain ⟨flag, out, post, bound, answered⟩ := ri_staticcall_bounded fork (project hcall)
  rw [post.eq_St] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hs)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨accepted, tailGas, h⟩
  · exact (failed.false_of_noOk noFail).elim
  · have zeroFlag : B256.eqCheck flag 0 = 0 := eq_zero_of_iszero_ne_zero accepted
    rcases post.flag with zero | one
    · rw [zero, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zeroFlag
      exact False.elim ((by decide : (1 : B256) ≠ 0) zeroFlag)
    · subst flag
      refine ⟨gw, callGas, d, out, tailGas, hcall, post, bound, answered rfl, ?_⟩
      simpa only [show B256.eqCheck (1 : B256) 0 = 0 from by decide] using h

/-- Forward success uses the supplied compiled call and its actual returned state. -/
theorem staticCallGuard_exact {fs : List SFunc} {sevm : Sevm} {b d : Devm}
    {S : List B256} {M : Mem} {callGas tailGas : Nat} {z t ii is oi os : B256}
    {o : Outcome} {callTree failureTree successTree : SFunc} (destination : Bytes)
    (le : destination.length ≤ 32) (nonempty : destination ≠ [])
    (shape : callTree = .dest (.next (.reg .pop) (.next (.reg .gas)
      (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
        (.next (.reg .iszero) (.next (.push destination le)
          (.branch failureTree successTree)))))))))
    (fork : CoveredFork sevm.benvStat.fork) (room : S.length ≤ 1018)
    (call : Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: t :: ii :: is :: oi :: os :: S) M callGas)
      (.exec .staticcall) d)
    (success : d.stack = 1 :: S) (returnedGas : d.gasLeft = tailGas + 22)
    (body : SFunc.RunExact fs sevm
      (St d (0 :: S) ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
        oi.toNat (d.returnData.take os.toNat)) tailGas) successTree o) :
    SFunc.RunExact fs sevm (St b (z :: t :: ii :: is :: oi :: os :: S) M (callGas + 5))
      callTree o := by
  cases destination with
  | nil => exact (nonempty rfl).elim
  | cons hd tl =>
    rw [shape]
    apply rx_dest
    apply rx_pop
    apply rx_gas (by simp only [List.length_cons]; omega)
    apply rx_staticcall fork call
    intro flag out post answered
    have flagEq : flag = 1 := (List.cons.inj (post.stack.symm.trans success)).1
    subst flag
    rw [returnedGas]
    apply rx_iszero (v := 0) (by decide) (by omega)
    apply rx_dup1 (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    rw [post.returnData] at body
    exact body

/-- The literal seven instructions comparing the full returndata width. -/
def returnWidthCompareLine : List Ninst :=
  [.push [0x40] (by decide), .reg .mload, .reg .returndatasize,
    .push [0x20] (by decide), .reg (.dup 1), .reg .lt, .reg .iszero]

/-- The supplied linear execution retains the real width comparison state. -/
theorem returnWidthCompareLine_inv {sevm : Sevm} {b d : Devm}
    {R : List B256} {M : Mem} {G : Nat} {p : B256} {n : Nat}
    (mem : PtrMem p n M)
    (line : Line.Run sevm (St b R M G) returnWidthCompareLine d) :
    ∃ G', d = St b
      (B256.eqCheck (B256.ltCheck b.returnData.length.toB256 32) 0 ::
        b.returnData.length.toB256 :: p :: R) M G' := by
  dsimp only [returnWidthCompareLine] at line
  obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨middle, hs, line⟩ := Line.of_run_cons line
  obtain ⟨_, eq⟩ := ri_mload hs
  have word : Bytes.toB256 (M.read 64 32).1 = p := mem.word
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word,
    mem.read_self mem.ge] at eq
  subst middle
  obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_returndatasize hs
  obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_lt hs
  obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero hs
  cases line
  exact ⟨_, rfl⟩

/-- The literal return-width guard derives width from full bounded returndata. -/
theorem returnWidthGuard_invP {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {b : Devm} {R : List B256}
    {C : List Nat} {M : Mem} {G : Nat} {a x y z p : B256} {n : Nat} {seg : Seg}
    {returnTree shortTree decodeTree : SFunc} (destination : Bytes)
    (le : destination.length ≤ 32)
    (shape : returnTree = .dest (.next (.reg .pop) (.next (.reg .pop)
      (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x40] (by decide))
        (.next (.reg .mload) (.next (.reg .returndatasize)
          (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt)
            (.next (.reg .iszero) (.next (.push destination le)
              (.branch shortTree decodeTree))))))))))))))
    (project : ∀ {s d i d'}, P s d i d' → Ninst.Run s d i d')
    (mem : PtrMem p n M) (bound : b.returnData.length < 2^256)
    (noShort : shortTree.noOk = true)
    (run : SFunc.RunCutP P fs sevm C (St b (a :: x :: y :: z :: R) M G) returnTree seg) :
    32 ≤ b.returnData.length ∧ ∃ G',
      SFunc.RunCutP P fs sevm C
        (St b (b.returnData.length.toB256 :: p :: R) M G') decodeTree seg := by
  rw [shape] at run
  obtain ⟨_, h⟩ := ric_destP run
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hs)
  change SFunc.RunCutP P fs sevm C _
    (returnWidthCompareLine.foldr SFunc.next (.next (.push destination le)
      (.branch shortTree decodeTree))) seg at h
  obtain ⟨compared, line, h⟩ := h.split_nexts (fun step => project step) returnWidthCompareLine
  obtain ⟨_, state⟩ := returnWidthCompareLine_inv mem line
  rw [state] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hs)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨accepted, G', h⟩
  · exact (failed.false_of_noOk noShort).elim
  · have width := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero accepted)
    rw [B256.toNat_toB256_of_lt bound] at width
    exact ⟨width, G', h⟩

/-- Exact return-width guards keep arbitrary pointer values and allocated sizes. -/
theorem returnWidthGuard_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {a x y z p : B256} {n : Nat} {o : Outcome}
    {returnTree shortTree decodeTree : SFunc} (destination : Bytes)
    (le : destination.length ≤ 32) (nonempty : destination ≠ [])
    (shape : returnTree = .dest (.next (.reg .pop) (.next (.reg .pop)
      (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x40] (by decide))
        (.next (.reg .mload) (.next (.reg .returndatasize)
          (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt)
            (.next (.reg .iszero) (.next (.push destination le)
              (.branch shortTree decodeTree))))))))))))))
    (mem : PtrMem p n M) (room : R.length ≤ 1020)
    (bound : b.returnData.length < 2^256) (width : 32 ≤ b.returnData.length)
    (body : SFunc.RunExact fs sevm
      (St b (b.returnData.length.toB256 :: p :: R) M G) decodeTree o) :
    SFunc.RunExact fs sevm (St b (a :: x :: y :: z :: R) M (G + 42)) returnTree o := by
  have enough : B256.ltCheck b.returnData.length.toB256 32 = 0 := by
    rw [B256.ltCheck, ite_eq_right]
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt bound]
    change ¬ b.returnData.length < 32
    omega
  cases destination with
  | nil => exact (nonempty rfl).elim
  | cons hd tl =>
    rw [shape]
    apply rx_dest
    apply rx_pop
    apply rx_pop
    apply rx_pop
    apply rx_pop
    apply rx_push (w := 64) rfl (by omega)
    apply rx_mload (i := 64) (v := p) (c := 3)
      (by rw [St.extCost_eq mem.size, memExtSize_of_le mem.n32 mem.ge, Nat.sub_self]; rfl)
      mem.word (mem.read_self mem.ge) (by omega)
    apply rx_returndatasize (by simp only [List.length_cons]; omega)
    apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
    apply rx_dup2 (by simp only [List.length_cons]; omega)
    apply rx_lt enough (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body

end Blanc.Lift
