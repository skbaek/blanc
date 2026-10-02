import Blanc.Lift.UniswapV2Pair.UpdateSource
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.StaticCall

/-! The concrete balanceOf request and answer windows of the two sync calls. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def balanceOfSelectorWord : B256 := Bytes.toB256
  [0x70, 0xa0, 0x82, 0x31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def balanceRequestMemory (M : Mem) (pair : Adr) : Mem :=
  (M.write 128 balanceOfSelectorWord.toBytes).write 132 pair.toB256.toBytes

def balanceRequestImage (M : Mem) (pair : Adr) : Bytes :=
  Bytes.writeAt (Bytes.writeAt M.data.toList 128 balanceOfSelectorWord.toBytes)
    132 pair.toB256.toBytes

/-- The second overlapping store replaces the selector word after its first four bytes. -/
theorem balanceRequestImage_read (M : Mem) (pair : Adr) :
    (balanceRequestImage M pair).sliceD 128 36 0 =
      ExternalOperation.encode (.balanceOf pair) := by
  unfold balanceRequestImage
  rw [show (36 : Nat) = 4 + 32 from rfl, List.sliceD_split]
  rw [Bytes.sliceD_writeAt_before _ _ 128 4 132 (by omega)]
  rw [Bytes.sliceD_writeAt_inside _ balanceOfSelectorWord.toBytes 128 128 4
    (by omega) (by rw [B256.length_toBytes]; omega)]
  rw [show (128 - 128 : Nat) = 0 from rfl,
    show balanceOfSelectorWord.toBytes.sliceD 0 4 0 = [0x70, 0xa0, 0x82, 0x31] from by decide]
  rw [show (128 + 4 : Nat) = 132 from rfl,
    ← B256.length_toBytes pair.toB256, Bytes.sliceD_writeAt]
  simp only [ExternalOperation.encode, encodeWords, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- The actual two MSTOREs install exactly the source's 36-byte request. -/
theorem balanceRequestMemory_read {M : Mem} (wf : Mem.Wf M) (pair : Adr) :
    ((balanceRequestMemory M pair).read 128 36).1 =
      ExternalOperation.encode (.balanceOf pair) := by
  have first := Mem.Reads.write wf (Mem.reads_data M) 128 balanceOfSelectorWord.toBytes
  have both := Mem.Reads.write (wf.write 128 balanceOfSelectorWord.toBytes) first
    132 pair.toB256.toBytes
  change Mem.Reads (balanceRequestMemory M pair) (balanceRequestImage M pair) at both
  rw [both.read]
  exact balanceRequestImage_read M pair

/-- The request leaves the free pointer intact while allocating both overlapping words. -/
theorem balanceRequestMemory_ptr {M : Mem} {n : Nat} (mem : PtrMem 128 n M) (pair : Adr) :
    PtrMem 128 (memExtSize (memExtSize n 128 32) 132 32)
      (balanceRequestMemory M pair) := by
  exact (mem.write 128 balanceOfSelectorWord (Or.inr (by decide))).write
    132 pair.toB256 (Or.inr (by decide))

def balanceReplyMemory (M : Mem) (pair : Adr) (out : Bytes) : Mem :=
  ((balanceRequestMemory M pair).extends [(128, 36), (128, 32)]).write 128 (out.take 32)

/-- Only the first word is decoded, while the actual call retains full returndata. -/
theorem balanceReplyMemory_word {M : Mem} (wf : Mem.Wf M) (pair : Adr) (out : Bytes)
    (long : 32 ≤ out.length) :
    Bytes.toB256 ((balanceReplyMemory M pair out).read 128 32).1 =
      Bytes.toB256 (out.take 32) := by
  have length : (out.take 32).length = 32 := by
    rw [List.length_take, Nat.min_eq_left long]
  have requestWf : Mem.Wf (balanceRequestMemory M pair) :=
    (wf.write 128 balanceOfSelectorWord.toBytes).write 132 pair.toB256.toBytes
  have image := Mem.Reads.extends [(128, 36), (128, 32)]
    (Mem.reads_data (balanceRequestMemory M pair))
  have written := Mem.Reads.write (requestWf.extends [(128, 36), (128, 32)])
    image 128 (out.take 32)
  unfold balanceReplyMemory
  have slice := Bytes.sliceD_writeAt (balanceRequestMemory M pair).data.toList (out.take 32) 128
  rw [length] at slice
  rw [written.read, slice]

/-- Arbitrary truncated output leaves the scratch allocation and free pointer intact. -/
theorem balanceReplyMemory_ptr {M : Mem} {pair : Adr} (out : Bytes)
    (mem : PtrMem 128 192 (balanceRequestMemory M pair)) :
    PtrMem 128 192 (balanceReplyMemory M pair out) := by
  unfold balanceReplyMemory
  generalize requestEq : balanceRequestMemory M pair = request at mem ⊢
  have extendedEq : request.extends [(128, 36), (128, 32)] = request := by
    unfold Mem.extends
    rw [mem.size]
    change (⟨request.data, 192⟩ : Mem) = request
    rw [← mem.size]
  rw [extendedEq]
  have shortWrite : (out.take 32).length ≤ 32 := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  refine ⟨(Mem.size_write_of_le (by rw [mem.size]; omega)).trans mem.size,
    mem.n32, mem.wf.write _ _, ?_⟩
  have keep := MemMatches.write 128 (out.take 32) mem.map
  simpa only [memKill, List.filter_cons, List.filter_nil,
    show decide (64 + 32 ≤ 128) = true from by decide,
    Bool.true_or, ite_true] using keep

inductive SyncBalanceSite where
  | first | second
  deriving DecidableEq

def SyncBalanceSite.returnTree : SyncBalanceSite → SFunc
  | .first => t_1ef1_c31
  | .second => t_1f8e_c31

def SyncBalanceSite.decodeTree : SyncBalanceSite → SFunc
  | .first => t_1f07_c31
  | .second => t_1fa4_c31

/-- Both actual return-size tests accept arbitrary trailing bytes after the first word. -/
theorem balanceReturn_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {a x y z : B256} {o : Outcome} (site : SyncBalanceSite)
    (mem : PtrMem 128 192 M) (room : R.length ≤ 1020)
    (short : b.returnData.length < 2 ^ 256) (long : 32 ≤ b.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St b (b.returnData.length.toB256 :: 128 :: R) M G) site.decodeTree o) :
    SFunc.RunExact cert.prog sevm (St b (a :: x :: y :: z :: R) M (G + 42))
      site.returnTree o := by
  have enough : B256.ltCheck b.returnData.length.toB256 32 = 0 := by
    rw [B256.ltCheck, ite_eq_right]
    rw [B256.lt_iff_toNat_lt_toNat]
    rw [B256.toNat_toB256_of_lt short]
    change ¬ b.returnData.length < 32
    omega
  cases site
  all_goals simp only [SyncBalanceSite.returnTree, SyncBalanceSite.decodeTree] at body ⊢
  all_goals simp only [t_1ef1_c31, t_1f8e_c31]
  all_goals apply rx_dest
  all_goals apply rx_pop
  all_goals apply rx_pop
  all_goals apply rx_pop
  all_goals apply rx_pop
  all_goals refine rx_push (w := 64) rfl (by omega) ?_
  all_goals
    refine rx_mload (i := 64) (v := 128) (c := 3)
      (by rw [St.extCost_eq mem.size]; decide) mem.word
      (mem.read_self (by decide : 64 + 32 ≤ 192)) (by omega) ?_
  all_goals refine rx_returndatasize (by simp only [List.length_cons]; omega) ?_
  all_goals refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  all_goals refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  all_goals refine rx_lt enough (by simp only [List.length_cons]; omega) ?_
  all_goals refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  case first =>
    apply rx_push (w := 0x1f07) rfl (by simp only [List.length_cons]; omega)
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body
  case second =>
    apply rx_push (w := 0x1fa4) rfl (by simp only [List.length_cons]; omega)
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body

def SyncBalanceSite.callTree : SyncBalanceSite → SFunc
  | .first => t_1edd_c31
  | .second => t_1f7a_c31

def SyncBalanceSite.failureTree : SyncBalanceSite → SFunc
  | .first => t_1ee8_c31
  | .second => t_1f85_c31

def SyncBalanceSite.returnDestination : SyncBalanceSite → Bytes
  | .first => [0x1e, 0xf1]
  | .second => [0x1f, 0x8e]

/-- The actual call sites preserve the call's derivation provenance, derive its
successful flag and full return-data bound, and retain the same continuation. -/
theorem balanceCall_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {z token a x y : B256} {seg : Seg} (site : SyncBalanceSite)
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R) M G)
      site.callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      StepIn D sevm
        (St b (gw :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R) M callGas)
        (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) M 128 36 128 32 1 out ∧
      out.length < 2^256 ∧
      StaticAnswered sevm b token.toAdr (M.read 128 36).1 out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (0 :: a :: x :: y :: R)
          ((M.extends [(128, 36), (128, 32)]).write 128 (out.take 32)) tailGas)
        site.returnTree seg := by
  have shape : site.callTree = .dest (.next (.reg .pop) (.next (.reg .gas)
      (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
        (.next (.reg .iszero) (.next (.push site.returnDestination
          (by cases site <;> decide)) (.branch site.failureTree site.returnTree)))))))) := by
    cases site <;> rfl
  rw [shape] at run
  obtain ⟨_, h⟩ := ric_destP run
  obtain ⟨_, hs, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h
  obtain ⟨gw, callGas, rfl⟩ := ri_gas (StepIn.toRun hs)
  obtain ⟨d, hcall, h⟩ := ric_nextP h
  obtain ⟨flag, out, post, bound, answered⟩ := ri_staticcall_bounded fork (StepIn.toRun hcall)
  rw [post.eq_St] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP h with ⟨-, _, failed⟩ | ⟨accepted, tailGas, h⟩
  · have noFail : site.failureTree.noOk = true := by cases site <;> decide
    exact False.elim (failed.false_of_noOk noFail)
  · have zeroFlag : B256.eqCheck flag 0 = 0 := eq_zero_of_iszero_ne_zero accepted
    rcases post.flag with zero | one
    · rw [zero, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zeroFlag
      exact False.elim ((by decide : (1 : B256) ≠ 0) zeroFlag)
    · subst flag
      refine ⟨gw, callGas, d, out, tailGas, hcall, post, bound, answered rfl, ?_⟩
      simpa only [show B256.eqCheck (1 : B256) 0 = 0 from by decide,
        show (128 : B256).toNat = 128 from rfl,
        show (36 : B256).toNat = 36 from rfl,
        show (32 : B256).toNat = 32 from rfl] using h

def SyncBalanceSite.shortTree : SyncBalanceSite → SFunc
  | .first => t_1f03_c31
  | .second => t_1fa0_c31

def SyncBalanceSite.decodeDestination : SyncBalanceSite → Bytes
  | .first => [0x1f, 0x07]
  | .second => [0x1f, 0xa4]

/-- Successful bytes derive the decoder's minimum width from the full, bounded
return data and keep the same provenance relation through the return-size guard. -/
theorem balanceReturn_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {a x y z : B256} {seg : Seg} (site : SyncBalanceSite)
    (mem : PtrMem 128 192 M) (short : b.returnData.length < 2^256)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (a :: x :: y :: z :: R) M G) site.returnTree seg) :
    32 ≤ b.returnData.length ∧ ∃ G',
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St b (b.returnData.length.toB256 :: 128 :: R) M G') site.decodeTree seg := by
  have shape : site.returnTree = .dest (.next (.reg .pop) (.next (.reg .pop)
      (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x40] (by decide))
        (.next (.reg .mload) (.next (.reg .returndatasize)
          (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt)
            (.next (.reg .iszero) (.next (.push site.decodeDestination
              (by cases site <;> decide)) (.branch site.shortTree site.decodeTree))))))))))))) := by
    cases site <;> rfl
  rw [shape] at run
  obtain ⟨_, h⟩ := ric_destP run
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨d, hs, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_mload (StepIn.toRun hs)
  have word : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word,
    mem.read_self (by decide : 64 + 32 ≤ 192)] at eq
  subst d
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_returndatasize (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP h with ⟨-, _, failed⟩ | ⟨accepted, G', h⟩
  · have noShort : site.shortTree.noOk = true := by cases site <;> decide
    exact False.elim (failed.false_of_noOk noShort)
  · have width := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero accepted)
    rw [B256.toNat_toB256_of_lt short] at width
    exact ⟨width, G', h⟩

/-- A successful actual balance call consumes the overlapping request, derives
both return-length guards, and reaches the decoder with full returndata retained. -/
theorem balanceObservation_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {z token a x y : B256} {seg : Seg} (site : SyncBalanceSite)
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) G) site.callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      StepIn D sevm
        (St b (gw :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
          (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) (balanceRequestMemory M sevm.currentTarget)
        128 36 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2^256 ∧
      StaticAnswered sevm b token.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (out.length.toB256 :: 128 :: R)
          (balanceReplyMemory M sevm.currentTarget out) tailGas) site.decodeTree seg := by
  obtain ⟨gw, callGas, d, out, _, call, post, bound, answered, tail⟩ :=
    balanceCall_inv site fork run
  have full : d.returnData.length < 2^256 := by rw [post.returnData]; exact bound
  change SFunc.RunCutP (StepIn D) cert.prog sevm C
    (St d (0 :: a :: x :: y :: R) (balanceReplyMemory M sevm.currentTarget out) _) _ _ at tail
  obtain ⟨long, tailGas, decoded⟩ :=
    balanceReturn_inv site (balanceReplyMemory_ptr out mem) full tail
  rw [post.returnData] at long decoded
  rw [balanceRequestMemory_read wf sevm.currentTarget] at answered
  exact ⟨gw, callGas, d, out, tailGas, call, post, long, bound, answered, decoded⟩

/-- Each literal call site has five gas before the actual callee step and
22 gas after it; the callee premise supplies its actual result and remaining gas. -/
theorem balanceCall_exact {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {callGas tailGas : Nat} {z token a x y : B256} {o : Outcome}
    (site : SyncBalanceSite) (fork : CoveredFork sevm.benvStat.fork)
    (room : R.length ≤ 1015)
    (call : Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R) M callGas)
      (.exec .staticcall) d)
    (success : d.stack = 1 :: a :: x :: y :: R)
    (returnedGas : d.gasLeft = tailGas + 22)
    (body : SFunc.RunExact cert.prog sevm
      (St d (0 :: a :: x :: y :: R)
        ((M.extends [(128, 36), (128, 32)]).write 128 (d.returnData.take 32)) tailGas)
      site.returnTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R) M (callGas + 5))
      site.callTree o := by
  have shape : site.callTree = .dest (.next (.reg .pop) (.next (.reg .gas)
      (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
        (.next (.reg .iszero) (.next (.push site.returnDestination
          (by cases site <;> decide)) (.branch site.failureTree site.returnTree)))))))) := by
    cases site <;> rfl
  rw [shape]
  apply rx_dest
  apply rx_pop
  apply rx_gas (by simp only [List.length_cons]; omega)
  apply rx_staticcall fork call
  intro flag out post answered
  have flagEq : flag = 1 := (List.cons.inj (post.stack.symm.trans success)).1
  subst flag
  simp only [show (128 : B256).toNat = 128 from rfl,
    show (36 : B256).toNat = 36 from rfl,
    show (32 : B256).toNat = 32 from rfl, returnedGas]
  apply rx_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  cases site <;>
    simp only [SyncBalanceSite.returnDestination, SyncBalanceSite.failureTree,
      SyncBalanceSite.returnTree] at body ⊢
  all_goals
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    rw [post.returnData] at body
    exact body

/-- The full actual call and return guard consume exactly64 local gas after the
callee, with arbitrary successful output bytes of at least the decoder width. -/
theorem balanceObservation_exact {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {callGas decodeGas : Nat} {z token a x y : B256} {o : Outcome}
    (site : SyncBalanceSite) (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (room : R.length ≤ 1015)
    (call : Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: a :: x :: y :: R)
    (returnedGas : d.gasLeft = decodeGas + 64)
    (long : 32 ≤ d.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: 128 :: R)
        (balanceReplyMemory M sevm.currentTarget d.returnData) decodeGas) site.decodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) (callGas + 5)) site.callTree o := by
  have raw : Ninst.Run sevm
      (St b (callGas.toB256 :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d := by
    obtain ⟨xl, filled, step⟩ := call
    exact ⟨xl, filled, 0, step 0⟩
  have bound := ReturnDataBound.staticcall_returnData_length_lt raw fork
  apply balanceCall_exact (tailGas := decodeGas + 42) site fork room call success (by omega)
  change SFunc.RunExact cert.prog sevm
    (St d (0 :: a :: x :: y :: R)
      (balanceReplyMemory M sevm.currentTarget d.returnData) (decodeGas + 42)) site.returnTree o
  exact balanceReturn_exact site (balanceReplyMemory_ptr d.returnData mem)
    (by omega) bound long body

/-- The actual certificate tail immediately after each balance-word MLOAD. -/
def SyncBalanceSite.afterDecodeTree (site : SyncBalanceSite) : SFunc :=
  match site.decodeTree with
  | .dest (.next _ (.next _ tail)) => tail
  | _ => .undefined

/-- The decoder reads the word from the actual overlapping STATICCALL output
window; any additional returned bytes remain in full returndata. -/
theorem balanceDecode_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {lengthWord : B256} {out : Bytes} {seg : Seg} (site : SyncBalanceSite)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M) (long : 32 ≤ out.length)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (lengthWord :: 128 :: R) (balanceReplyMemory M sevm.currentTarget out) G)
      site.decodeTree seg) :
    ∃ G', SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (Bytes.toB256 (out.take 32) :: R)
        (balanceReplyMemory M sevm.currentTarget out) G') site.afterDecodeTree seg := by
  have shape : site.decodeTree = .dest (.next (.reg .pop)
      (.next (.reg .mload) site.afterDecodeTree)) := by cases site <;> rfl
  rw [shape] at run
  obtain ⟨_, h⟩ := ric_destP run
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨d, hs, h⟩ := ric_nextP h
  obtain ⟨G', eq⟩ := ri_mload (StepIn.toRun hs)
  rw [show (128 : B256).toNat = 128 from rfl,
    balanceReplyMemory_word wf sevm.currentTarget out long,
    (balanceReplyMemory_ptr out mem).read_self (by decide : 128 + 32 ≤ 192)] at eq
  subst d
  exact ⟨G', h⟩

/-- The actual decoder prefix costs six gas with its32-byte read in the allocated
reply window, and forwards precisely the decoded balance word. -/
theorem balanceDecode_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {lengthWord : B256} {out : Bytes} {o : Outcome} (site : SyncBalanceSite)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M) (long : 32 ≤ out.length) (room : R.length ≤ 1022)
    (body : SFunc.RunExact cert.prog sevm
      (St b (Bytes.toB256 (out.take 32) :: R)
        (balanceReplyMemory M sevm.currentTarget out) G) site.afterDecodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (lengthWord :: 128 :: R) (balanceReplyMemory M sevm.currentTarget out) (G + 6))
      site.decodeTree o := by
  have shape : site.decodeTree = .dest (.next (.reg .pop)
      (.next (.reg .mload) site.afterDecodeTree)) := by cases site <;> rfl
  rw [shape]
  apply rx_dest
  apply rx_pop
  apply rx_mload (i := 128) (v := Bytes.toB256 (out.take 32)) (c := 3)
    (by simp only [St.extCost_eq, (balanceReplyMemory_ptr out mem).size]; rfl)
    (balanceReplyMemory_word wf sevm.currentTarget out long)
    ((balanceReplyMemory_ptr out mem).read_self (by decide : 128 + 32 ≤ 192))
    (by omega)
  exact body

/-- The actual balance observation reaches the source balance word, retaining
its full output, precise request, actual call provenance and same continuation. -/
theorem balanceRead_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {z token a x y : B256} {seg : Seg} (site : SyncBalanceSite)
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) G) site.callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      StepIn D sevm
        (St b (gw :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
          (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) (balanceRequestMemory M sevm.currentTarget)
        128 36 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2^256 ∧
      StaticAnswered sevm b token.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (Bytes.toB256 (out.take 32) :: R)
          (balanceReplyMemory M sevm.currentTarget out) tailGas) site.afterDecodeTree seg := by
  obtain ⟨gw, callGas, d, out, _, call, post, long, bound, answered, tail⟩ :=
    balanceObservation_inv site fork mem wf run
  obtain ⟨tailGas, decoded⟩ := balanceDecode_inv site mem wf long tail
  exact ⟨gw, callGas, d, out, tailGas, call, post, long, bound, answered, decoded⟩

/-- Five local gas precede the callee and70 follow it through the actual MLOAD.
The only external premises describe the actual primitive call's success, width and gas. -/
theorem balanceRead_exact {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {callGas tailGas : Nat} {z token a x y : B256} {o : Outcome}
    (site : SyncBalanceSite) (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M) (room : R.length ≤ 1015)
    (call : Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: a :: x :: y :: R)
    (returnedGas : d.gasLeft = tailGas + 70)
    (long : 32 ≤ d.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St d (Bytes.toB256 (d.returnData.take 32) :: R)
        (balanceReplyMemory M sevm.currentTarget d.returnData) tailGas) site.afterDecodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) (callGas + 5)) site.callTree o := by
  apply balanceObservation_exact (decodeGas := tailGas + 6) site fork mem room call
    success (by omega) long
  exact balanceDecode_exact site mem wf long (by omega) body

end Blanc.Lift.UniswapV2Pair
