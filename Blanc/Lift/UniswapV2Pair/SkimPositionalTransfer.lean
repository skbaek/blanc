import Blanc.Lift.UniswapV2Pair.SkimPositionalReply
import Blanc.Lift.UniswapV2Pair.PairCheckedSubCursor
import Blanc.Lift.UniswapV2Pair.PairTransferRequestCursor
import Blanc.Lift.UniswapV2Pair.PairTransferReplyCursor

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def SkimBalanceSite.subReturnTree : SkimBalanceSite → SFunc
  | .first => t_1a26_c34
  | .second => t_1a26_c67

def SkimBalanceSite.transferReturnTree : SkimBalanceSite → SFunc
  | .first => t_1a2b_c34
  | .second => t_1aca_c67

def skimSubCalleeLine : List Ninst := [
  .reg (.swap 0), .push [0xff, 0xff, 0xff, 0xff] (by decide),
  .push [0x22, 0x6e] (by decide), .reg .and]

/-- Checked subtraction and the actual helper call preserve the original
continuation for each of Skim's two physical balance replies. -/
theorem skim_transfer_callee_cursor_state {start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {x y rho : B256}
    (site : SkimBalanceSite)
    (cut : CursorStateAt code cert start site.afterDecodeTree b (x :: y :: rho :: R) M K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    y ≤ x ∧ Nonempty (CursorStateAt code cert start t_1fdb_c57 b
      ((x - y) :: R) M (site.transferReturnTree :: K)) := by
  obtain ⟨caller⟩ := cut.line cert_check success fork skimSubCalleeLine rfl
    (by intro n member z equal; subst n
        simp only [skimSubCalleeLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := 0x226e :: y :: x :: rho :: R) (by
      intro G d line
      dsimp only [skimSubCalleeLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      obtain ⟨_, rfl⟩ := ri_swap (S' := y :: x :: rho :: R) rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      cases line
      obtain ⟨g, result⟩ := ri_and step
      exact ⟨g, by simpa only [show Bytes.toB256 [0x22, 0x6e] &&&
        Bytes.toB256 [0xff, 0xff, 0xff, 0xff] = (0x226e : B256) from by decide] using result⟩)
  obtain ⟨sub⟩ := caller.call cert_check success fork rfl
  obtain ⟨cover, ⟨subtracted⟩⟩ := pair_sub59_cursor_state sub success fork
  have shape : site.subReturnTree = .dest (.next (.push [0x1f, 0xdb] (by decide))
      (.callNext 57 site.transferReturnTree)) := by cases site <;> rfl
  change CursorStateAt code cert start site.subReturnTree b ((x - y) :: R) M K at subtracted
  rw [shape] at subtracted
  obtain ⟨opened⟩ := subtracted.dest cert_check success fork
  obtain ⟨transferCaller⟩ := opened.line cert_check success fork [.push [0x1f, 0xdb] (by decide)] rfl
    (by intro n member z equal; subst n; simp only [List.mem_singleton, reduceCtorEq] at member)
    (by intro G d line
        obtain ⟨_, step, line⟩ := Line.of_run_cons line
        cases line
        exact ri_push step)
  exact ⟨cover, transferCaller.call cert_check success fork rfl⟩

structure SkimTransferObservation (root start : Exec.Deriv) (site : SkimBalanceSite)
    (b : Devm) (M : Mem) (p amount toWord tokenWord rho : B256)
    (R : List B256) (K : List SFunc) where
  call : CallOccurrenceStep root .call
  gas : Nat
  cursor : Cursor
  gap : Exec.Deriv.ExecFreeUntil start call.occurrence.node
  sevm : call.occurrence.node.sevm = start.sevm
  exn : call.occurrence.node.exn = start.exn
  input : call.occurrence.node.devm = St b
    (gas.toB256 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
    (safeTransfer_dynamicCallMemory M p amount toWord) gas
  calldata : (call.occurrence.node.devm.memory.read (p + 164).toNat 68).1 =
    abiSelectorBytes 0xa9059cbb ++
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes
  primitive : Ninst.RunWith (Cursor.DescOf call.occurrence.node) start.sevm
    call.occurrence.node.devm (.exec .call) call.returned.devm
  placed : CursorOK code cert call.returned cursor
  tree : cursor.f = pairTransferAfterCallTree
  continuations : cursor.K.map Cont.f = site.transferReturnTree :: K
  stack : call.returned.devm.stack =
    1 :: (68 + (p + 164)) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R
  memory : call.returned.devm.memory = safeTransfer_dynamicCallMemory M p amount toWord
  output : call.returned.devm.output = b.output
  bound : call.returned.devm.returnData.length < 2 ^ 160
  accepted : call.returned.devm.returnData = [] ∨
    (32 ≤ call.returned.devm.returnData.length ∧
      Bytes.toB256 (call.returned.devm.returnData.sliceD 0 32 0) ≠ 0)
  returned : CursorStateAt code cert call.returned site.transferReturnTree
    call.returned.devm R (swapTransferMemory M p amount toWord call.returned.devm.returnData) K

/-- The shared physical transfer donors classify the exact original Skim CALL
and return through its real suspended continuation. -/
theorem skim_transfer_observation_of_callee {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (site : SkimBalanceSite)
    (cut : CursorStateAt code cert start t_1fdb_c57 b
      (amount :: toWord :: tokenWord :: rho :: R) M (site.transferReturnTree :: K))
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : root.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    Nonempty (SkimTransferObservation root start site b M p amount toWord tokenWord rho R K) := by
  have successStart : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨requestMem, ⟨request⟩⟩ := pair_transfer_request_cursor_state cut successStart fork mem lower width
  obtain ⟨step, cursor, gas, gap, env, outcome, input, primitive, placed, tree, conts⟩ :=
    pair_transfer_call_of_gas_cursor request reached successStart fork
  have data := safeTransfer_dynamicCall_data (amount := amount) (toWord := toWord)
    mem.wf lower (by omega : p.toNat + 164 < 2 ^ 256)
  have memoryEq : step.occurrence.node.devm.memory = safeTransfer_dynamicCallMemory M p amount toWord := by
    rw [input, St.memory]
  have fit := safeTransfer_dynamicCall_fit (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨stack, memory, output, bound, accepted, ⟨returned⟩⟩ :=
    pair_transfer_reply_cursor_state step input placed tree conts success
      (by rw [env]; exact fork) requestMem lower width fit
  exact ⟨⟨step, gas, cursor, gap, env, outcome, input,
    (congrArg (fun N : Mem => (N.read (p + 164).toNat 68).1) memoryEq).trans data,
    primitive, placed, tree, conts, stack, memory, output, bound, accepted, returned⟩⟩

structure SkimTwoCalls (root : Exec.Deriv) (b : Devm) (toWord : B256) (R : List B256) where
  first : SkimFirstObservation root b toWord R
  cover : skimReserve0 root.sevm b ≤ Bytes.toB256 (first.out.take 32)
  transfer : SkimTransferObservation root first.call.returned .first first.call.returned.devm
    (balanceReplyMemory getterInitMemory root.sevm.currentTarget first.out)
    128 (Bytes.toB256 (first.out.take 32) - skimReserve0 root.sevm b) toWord
    (skimToken0 root.sevm b) 0x1a2b
    (skimToken1 root.sevm b :: skimToken0 root.sevm b :: toWord :: R) []

/-- The first transfer consumes the balance decoded from the same preceding
static call; the second operation starts at that actual returned world. -/
theorem skim_two_calls_of_prefix {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {toWord : B256}
    (cut : CursorStateAt code cert root t_194f_c34 (afterSload root.sevm b 12)
      (toWord :: R) getterInitMemory [])
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (SkimTwoCalls root b toWord R) := by
  obtain ⟨first⟩ := skim_first_observation_of_prefix cut success fork
  have reached := first.call.sameFrame.snoc first.call.edge
  have env : first.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached
  have successRet : first.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  have decoded : CursorStateAt code cert first.call.returned SkimBalanceSite.first.afterDecodeTree
      first.call.returned.devm
      (Bytes.toB256 (first.out.take 32) :: skimReserve0 root.sevm b :: 0x1a26 ::
        toWord :: skimToken0 root.sevm b :: 0x1a2b :: skimToken1 root.sevm b ::
        skimToken0 root.sevm b :: toWord :: R)
      (balanceReplyMemory getterInitMemory root.sevm.currentTarget first.out) [] := first.decoded
  obtain ⟨cover, ⟨callee⟩⟩ := skim_transfer_callee_cursor_state .first decoded successRet
    (by rw [env]; exact fork)
  obtain ⟨transfer⟩ := skim_transfer_observation_of_callee .first callee reached success
    (by rw [env]; exact fork)
    (balanceReplyMemory_ptr first.out (balanceRequestMemory_ptr getterInitMemory_ptr root.sevm.currentTarget))
    (by decide) (by decide)
  exact ⟨⟨first, cover, transfer⟩⟩

end Blanc.Lift.UniswapV2Pair
