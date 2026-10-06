import Blanc.Lift.StaticCallGuard
import Blanc.Lift.ByteWindowMemory
import Blanc.Lift.WalkSteps
import Blanc.Lift.CodeSizeWalk
import Blanc.Lift.ExactWalkSolc
import Blanc.AddressSlotProofs
import Blanc.Lift.UniswapV2Pair.Cert
import Blanc.Lift.UniswapV2Pair.Execution

/-! The literal factory feeTo request, retained answer and fee68 call guards. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def feeToSelectorWord : B256 := Bytes.toB256
  [0x01, 0x7e, 0x7e, 0x58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def feeRequestMemory (M : Mem) : Mem := M.write 128 feeToSelectorWord.toBytes

def feeReplyMemory (M : Mem) (out : Bytes) : Mem :=
  ((feeRequestMemory M).extends [(128, 4), (128, 32)]).write 128 (out.take 32)

/-- The actual selector MSTORE supplies exactly the four-byte feeTo request. -/
theorem feeRequestMemory_read {M : Mem} (wf : Mem.Wf M) :
    ((feeRequestMemory M).read 128 4).1 = ExternalOperation.encode .feeTo := by
  have written := Mem.Reads.write wf (Mem.reads_data M) 128 feeToSelectorWord.toBytes
  change Mem.Reads (feeRequestMemory M) (Bytes.writeAt M.data.toList 128 feeToSelectorWord.toBytes)
    at written
  rw [written.read, Bytes.sliceD_writeAt_inside _ feeToSelectorWord.toBytes 128 128 4
    (by omega) (by rw [B256.length_toBytes]; omega)]
  exact (by decide : feeToSelectorWord.toBytes.sliceD (128 - 128) 4 0 =
    ExternalOperation.encode .feeTo)

/-- Writing the request preserves the actual callers' fixed scratch allocation. -/
theorem feeRequestMemory_ptr {M : Mem} (mem : PtrMem 128 192 M) :
    PtrMem 128 192 (feeRequestMemory M) := by
  exact mem.write 128 feeToSelectorWord (Or.inr (by decide))

/-- Only the first output word is copied; the call's full answer remains separate. -/
theorem feeReplyMemory_word {M : Mem} (wf : Mem.Wf M) (out : Bytes)
    (long : 32 ≤ out.length) :
    Bytes.toB256 ((feeReplyMemory M out).read 128 32).1 = Bytes.toB256 (out.take 32) := by
  have length : (out.take 32).length = 32 := by
    rw [List.length_take, Nat.min_eq_left long]
  have requestWf : Mem.Wf (feeRequestMemory M) := wf.write 128 feeToSelectorWord.toBytes
  have image := Mem.Reads.extends [(128, 4), (128, 32)]
    (Mem.reads_data (feeRequestMemory M))
  have written := Mem.Reads.write (requestWf.extends [(128, 4), (128, 32)])
    image 128 (out.take 32)
  unfold feeReplyMemory
  have slice := Bytes.sliceD_writeAt (feeRequestMemory M).data.toList (out.take 32) 128
  rw [length] at slice
  rw [written.read, slice]

/-- Arbitrary truncated replies preserve the same pointer and high-water bound. -/
theorem feeReplyMemory_ptr {M : Mem} (out : Bytes) (mem : PtrMem 128 192 (feeRequestMemory M)) :
    PtrMem 128 192 (feeReplyMemory M out) := by
  unfold feeReplyMemory
  generalize requestEq : feeRequestMemory M = request at mem ⊢
  have extendedEq : request.extends [(128, 4), (128, 32)] = request := by
    unfold Mem.extends
    rw [mem.size]
    change (⟨request.data, 192⟩ : Mem) = request
    rw [← mem.size]
  rw [extendedEq]
  apply mem.write_bytes_of_le 128 (out.take 32)
  · rw [List.length_take]
    have := Nat.min_le_left 32 out.length
    omega
  · exact Or.inr (by decide)

/-- The actual fee call retains its primitive derivation and full arbitrary reply. -/
theorem feeCall_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {z factory a x y : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (z :: factory :: 128 :: 4 :: 128 :: 32 :: a :: x :: y :: R) M G)
      t_2757_c68 seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      StepIn D sevm
        (St b (gw :: factory :: 128 :: 4 :: 128 :: 32 :: a :: x :: y :: R) M callGas)
        (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) M 128 4 128 32 1 out ∧
      out.length < 2^256 ∧ StaticAnswered sevm b factory.toAdr (M.read 128 4).1 out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (0 :: a :: x :: y :: R)
          ((M.extends [(128, 4), (128, 32)]).write 128 (out.take 32)) tailGas)
        t_276b_c68 seg := by
  exact staticCallGuard_invP [0x27, 0x6b] (by decide) rfl StepIn.toRun fork (by decide) run

/-- Successful fee bytes derive minimum width from the actual return guard. -/
theorem feeReturn_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {a x y z : B256} {seg : Seg}
    (mem : PtrMem 128 192 M) (bound : b.returnData.length < 2^256)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (a :: x :: y :: z :: R) M G) t_276b_c68 seg) :
    32 ≤ b.returnData.length ∧ ∃ G',
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St b (b.returnData.length.toB256 :: 128 :: R) M G') t_2781_c68 seg := by
  exact returnWidthGuard_invP [0x27, 0x81] (by decide) rfl StepIn.toRun mem bound (by decide) run

/-- The real feeTo observation supplies four bytes and preserves its answer and post-call world. -/
theorem feeObservation_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {z factory a x y : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (feeRequestMemory M)) (wf : Mem.Wf M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (z :: factory :: 128 :: 4 :: 128 :: 32 :: a :: x :: y :: R)
        (feeRequestMemory M) G) t_2757_c68 seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (decodeGas : Nat),
      StepIn D sevm
        (St b (gw :: factory :: 128 :: 4 :: 128 :: 32 :: a :: x :: y :: R)
          (feeRequestMemory M) callGas) (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) (feeRequestMemory M) 128 4 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2^256 ∧
      StaticAnswered sevm b factory.toAdr (ExternalOperation.encode .feeTo) out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (out.length.toB256 :: 128 :: R) (feeReplyMemory M out) decodeGas)
        t_2781_c68 seg := by
  obtain ⟨gw, callGas, d, out, _, call, post, bound, answered, tail⟩ := feeCall_inv fork run
  have full : d.returnData.length < 2^256 := by rw [post.returnData]; exact bound
  change SFunc.RunCutP (StepIn D) cert.prog sevm C
    (St d (0 :: a :: x :: y :: R) (feeReplyMemory M out) _) _ _ at tail
  obtain ⟨long, decodeGas, decoded⟩ := feeReturn_inv (feeReplyMemory_ptr out mem) full tail
  rw [post.returnData] at long decoded
  rw [feeRequestMemory_read wf] at answered
  exact ⟨gw, callGas, d, out, decodeGas, call, post, long, bound, answered, decoded⟩

/-- Exact fee calls use the actual compiled callee step and its supplied remaining gas. -/
theorem feeCall_exact {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {callGas tailGas : Nat} {z factory a x y : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1015)
    (call : Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: factory :: 128 :: 4 :: 128 :: 32 :: a :: x :: y :: R) M callGas)
      (.exec .staticcall) d)
    (success : d.stack = 1 :: a :: x :: y :: R) (returnedGas : d.gasLeft = tailGas + 22)
    (body : SFunc.RunExact cert.prog sevm
      (St d (0 :: a :: x :: y :: R)
        ((M.extends [(128, 4), (128, 32)]).write 128 (d.returnData.take 32)) tailGas)
      t_276b_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: factory :: 128 :: 4 :: 128 :: 32 :: a :: x :: y :: R) M (callGas + 5))
      t_2757_c68 o := by
  exact staticCallGuard_exact [0x27, 0x6b] (by decide) (by decide) rfl fork
    (by simp only [List.length_cons]; omega) call success returnedGas body

/-- The exact literal return guard accepts trailing bytes without truncating the observation. -/
theorem feeReturn_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {a x y z : B256} {o : Outcome}
    (mem : PtrMem 128 192 M) (room : R.length ≤ 1020)
    (bound : b.returnData.length < 2^256) (long : 32 ≤ b.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St b (b.returnData.length.toB256 :: 128 :: R) M G) t_2781_c68 o) :
    SFunc.RunExact cert.prog sevm (St b (a :: x :: y :: z :: R) M (G + 42))
      t_276b_c68 o := by
  exact returnWidthGuard_exact [0x27, 0x81] (by decide) (by decide) rfl mem room bound long body

/-- The producer supplies its own return bound; the two local guards cost64 after the call. -/
theorem feeObservation_exact {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {callGas decodeGas : Nat} {z factory a x y : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 (feeRequestMemory M))
    (room : R.length ≤ 1015)
    (call : Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: factory :: 128 :: 4 :: 128 :: 32 :: a :: x :: y :: R)
        (feeRequestMemory M) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: a :: x :: y :: R)
    (returnedGas : d.gasLeft = decodeGas + 64) (long : 32 ≤ d.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: 128 :: R) (feeReplyMemory M d.returnData) decodeGas)
      t_2781_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: factory :: 128 :: 4 :: 128 :: 32 :: a :: x :: y :: R)
        (feeRequestMemory M) (callGas + 5)) t_2757_c68 o := by
  have raw : Ninst.Run sevm
      (St b (callGas.toB256 :: factory :: 128 :: 4 :: 128 :: 32 :: a :: x :: y :: R)
        (feeRequestMemory M) callGas) (.exec .staticcall) d := by
    obtain ⟨xl, filled, step⟩ := call
    exact ⟨xl, filled, 0, step 0⟩
  have bound := ReturnDataBound.staticcall_returnData_length_lt raw fork
  apply feeCall_exact (tailGas := decodeGas + 42) fork room call success (by omega)
  change SFunc.RunExact cert.prog sevm
    (St d (0 :: a :: x :: y :: R) (feeReplyMemory M d.returnData) (decodeGas + 42)) t_276b_c68 o
  exact feeReturn_exact (feeReplyMemory_ptr d.returnData mem) (by omega) bound long body

def feeFactoryWord (sevm : Sevm) (b : Devm) : B256 :=
  (b.getStorVal sevm.currentTarget 5).toAdr.toB256

def feeFactoryLoadWorld (sevm : Sevm) (b : Devm) : Devm := afterSload sevm b 5

def feeCodeGuardTree : SFunc :=
  .next (.reg .extcodesize) (.next (.reg .iszero) (.next (.reg (.dup 0))
    (.next (.reg .iszero) (.next (.push [0x27, 0x57] (by decide))
      (.branch t_2753_c68 t_2757_c68)))))

/-- The factory code guard derives presence and retains actual account warming. -/
theorem feeCodeGuard_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {S : List B256} {C : List Nat} {M : Mem} {G : Nat} {factory : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (factory :: S) M G) feeCodeGuardTree seg) :
    (b.getCode factory.toAdr).size.toB256 ≠ 0 ∧ ∃ gas,
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St (temporalAccountAccessBase b factory.toAdr) (0 :: S) M gas) t_2757_c68 seg := by
  unfold feeCodeGuardTree at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_extcodesize fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, gas, tail⟩
  · exact (failed.false_of_noOk (by decide)).elim
  · have zero := eq_zero_of_iszero_ne_zero accepted
    have nonzero : (b.getCode factory.toAdr).size.toB256 ≠ 0 := by
      intro hz
      rw [hz, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    refine ⟨nonzero, gas, ?_⟩
    simpa only [zero] using tail

/-- The code guard has22 local gas and the selected factory-account access cost. -/
theorem feeCodeGuard_exact {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G : Nat} {factory : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : S.length ≤ 1021)
    (nonzero : (b.getCode factory.toAdr).size.toB256 ≠ 0)
    (body : SFunc.RunExact cert.prog sevm
      (St (temporalAccountAccessBase b factory.toAdr) (0 :: S) M G) t_2757_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (factory :: S) M (G + 22 + temporalAccountAccessCost b factory.toAdr))
      feeCodeGuardTree o := by
  unfold feeCodeGuardTree
  apply rx_extcodesize fork (by omega)
  have zero : B256.eqCheck (b.getCode factory.toAdr).size.toB256 0 = 0 := by
    simp only [B256.eqCheck, nonzero, ite_false]
  apply rx_iszero zero (by omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body

/-- The actual fee entry loads and masks slot5, stages the selector, and reaches the code guard. -/
theorem feePreparation_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {r1 r0 ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (r1 :: r0 :: ρ :: R) M G) t_26ec_c68 seg) :
    ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St (feeFactoryLoadWorld sevm b)
        (feeFactoryWord sevm b :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) gas) feeCodeGuardTree seg := by
  have h := run
  unfold t_26ec_c68 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_exp (StepIn.toRun hs)
  rw [show B256.bexp (Bytes.toB256 [0x01, 0x00]) (Bytes.toB256 [0x00]) = 1 from by
    unfold B256.bexp
    rw [show (Bytes.toB256 [0x00]).toNat = 0 from rfl]
    simp only [Nat.powMod, Nat.powMod.go]
    rfl] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_div (StepIn.toRun hs)
  rw [show b.getStorVal sevm.currentTarget (Bytes.toB256 [5]) / (1 : B256) =
    b.getStorVal sevm.currentTarget (Bytes.toB256 [5]) from by
      apply B256.toNat_inj
      rw [B256.toNat_div (by decide), show (1 : B256).toNat = 1 from rfl, Nat.div_one]] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [ff20_and_word] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [ff20_and_adr] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨d, hs, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_mload (StepIn.toRun hs)
  have pointerWord : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, pointerWord, mem.read_self mem.ge] at eq
  subst d
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff] &&& Bytes.toB256 [0x01, 0x7e, 0x7e, 0x58] =
    Bytes.toB256 [0x01, 0x7e, 0x7e, 0x58] from by decide] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_shl (StepIn.toRun hs)
  rw [show Bytes.toB256 [0x01, 0x7e, 0x7e, 0x58] <<< (Bytes.toB256 [0xe0]).toNat =
    feeToSelectorWord from by decide] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl (StepIn.toRun hs)
  have requestMem := feeRequestMemory_ptr mem
  change PtrMem 128 192 (M.write 128 feeToSelectorWord.toBytes) at requestMem
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨d, hs, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_mload (StepIn.toRun hs)
  have requestWord : Bytes.toB256 ((M.write 128 feeToSelectorWord.toBytes).read 64 32).1 = 128 :=
    requestMem.word
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, requestWord,
    requestMem.read_self requestMem.ge] at eq
  subst d
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨gas, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  exact ⟨gas, h⟩

/-- All36 preparation instructions have115 fixed gas plus the actual slot5 read. -/
theorem feePreparation_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G load : Nat} {r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (room : R.length ≤ 1008) (charge : load = sloadCost sevm b 5)
    (body : SFunc.RunExact cert.prog sevm
      (St (feeFactoryLoadWorld sevm b)
        (feeFactoryWord sevm b :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) G) feeCodeGuardTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (r1 :: r0 :: ρ :: R) M (G + load + 115)) t_26ec_c68 o := by
  have requestMem := feeRequestMemory_ptr mem
  have exponent : B256.bexp (Bytes.toB256 [0x01, 0x00]) (Bytes.toB256 [0x00]) = 1 := by
    unfold B256.bexp
    rw [show (Bytes.toB256 [0x00]).toNat = 0 from rfl]
    simp only [Nat.powMod, Nat.powMod.go]
    rfl
  unfold t_26ec_c68
  apply rx_dest
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  rw [show G + load + 99 = (G + 99) + load from by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_exp (by decide) (by simp only [List.length_cons]; omega)
  rw [exponent]
  apply rx_swap1
  apply rx_div (v := b.getStorVal sevm.currentTarget 5)
    (by apply B256.toNat_inj
        rw [B256.toNat_div (by decide), show (1 : B256).toNat = 1 from rfl, Nat.div_one])
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega)
  apply rx_and (v := feeFactoryWord sevm b) (addressSlotReadWord_eq_toAdr_toB256 _)
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega)
  apply rx_and (v := feeFactoryWord sevm b) (addressSlotReadWord_toB256 _)
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x017e7e58) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem.size, memExtSize_of_le mem.n32 mem.ge, Nat.sub_self]; rfl)
    mem.word (mem.read_self mem.ge) (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := 0x017e7e58) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 224) rfl (by simp only [List.length_cons]; omega)
  apply rx_shl (v := feeToSelectorWord) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 128) (c := 3) (M' := feeRequestMemory M)
    (by rw [St.extCost_eq mem.size]; rfl) rfl
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  rw [show (4 : B256) + 128 = 132 from by decide]
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq requestMem.size, memExtSize_of_le requestMem.n32 requestMem.ge,
      Nat.sub_self]; rfl)
    requestMem.word (requestMem.read_self requestMem.ge) (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_sub (by simp only [List.length_cons]; omega)
  rw [show (132 : B256) - 128 = 4 from by decide]
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  exact body

def feeFactoryCallWorld (sevm : Sevm) (b : Devm) : Devm :=
  temporalAccountAccessBase (feeFactoryLoadWorld sevm b) (feeFactoryWord sevm b).toAdr

/-- The actual fee68 prefix produces the selected feeTo observation and original decoder continuation. -/
theorem feeFactoryObservation_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {r1 r0 ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (r1 :: r0 :: ρ :: R) M G) t_26ec_c68 seg) :
    ( (feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr ).size.toB256 ≠ 0 ∧
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (decodeGas : Nat),
      StepIn D sevm
        (St (feeFactoryCallWorld sevm b)
          (gw :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
            132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
          (feeRequestMemory M) callGas) (.exec .staticcall) d ∧
      StaticCallPost (feeFactoryCallWorld sevm b) d
        (132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) 128 4 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2^256 ∧
      StaticAnswered sevm (feeFactoryCallWorld sevm b) (feeFactoryWord sevm b).toAdr
        (ExternalOperation.encode .feeTo) out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (out.length.toB256 :: 128 :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
          (feeReplyMemory M out) decodeGas) t_2781_c68 seg := by
  obtain ⟨_, preparation⟩ := feePreparation_inv fork mem run
  obtain ⟨code, _, callGuard⟩ := feeCodeGuard_inv fork preparation
  obtain ⟨gw, callGas, d, out, decodeGas, step, post, width, bound, answer, continuation⟩ :=
    feeObservation_inv fork (feeRequestMemory_ptr mem) mem.wf callGuard
  exact ⟨code, gw, callGas, d, out, decodeGas, step, post, width, bound, answer, continuation⟩

/-- The full prefix consumes a genuine callee, retaining selected slot and account charges. -/
theorem feeFactoryObservation_exact {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {callGas decodeGas : Nat} {r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (room : R.length ≤ 1008)
    (code : ((feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr).size.toB256 ≠ 0)
    (call : Ninst.RunCompiled sevm
      (St (feeFactoryCallWorld sevm b)
        (callGas.toB256 :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm b ::
      0 :: 0 :: r1 :: r0 :: ρ :: R)
    (returnedGas : d.gasLeft = decodeGas + 64) (width : 32 ≤ d.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: 128 :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeReplyMemory M d.returnData) decodeGas) t_2781_c68 o) :
    SFunc.RunExact cert.prog sevm (St b (r1 :: r0 :: ρ :: R) M
      (callGas + sloadCost sevm b 5 +
        temporalAccountAccessCost (feeFactoryLoadWorld sevm b) (feeFactoryWord sevm b).toAdr + 142))
      t_26ec_c68 o := by
  rw [show callGas + sloadCost sevm b 5 +
      temporalAccountAccessCost (feeFactoryLoadWorld sevm b) (feeFactoryWord sevm b).toAdr + 142 =
    (callGas + 5 + 22 +
      temporalAccountAccessCost (feeFactoryLoadWorld sevm b) (feeFactoryWord sevm b).toAdr) +
        sloadCost sevm b 5 + 115 from by omega]
  apply feePreparation_exact fork mem room rfl
  apply feeCodeGuard_exact fork (by simp only [List.length_cons]; omega) code
  exact feeObservation_exact fork (feeRequestMemory_ptr mem)
    (by simp only [List.length_cons]; omega) call success returnedGas width body

end Blanc.Lift.UniswapV2Pair
