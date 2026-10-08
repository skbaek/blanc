import Blanc.Lift.UniswapV2Pair.SwapPositionalCallback
import Blanc.Lift.UniswapV2Pair.SwapBalanceWalk
import Blanc.Lift.CursorNoExecSuffix

/-! Both final balance observations retain their own original-root STATICCALL. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def swapBalanceCallTree (second : Bool) : SFunc := if second then t_0acb_c5 else t_0a2f_c5

def swapBalanceCodeFailure (second : Bool) : SFunc := if second then t_0ac7_c5 else t_0a2b_c5

def swapBalanceCallFailure (second : Bool) : SFunc := if second then t_0ad6_c5 else t_0a3a_c5

def swapBalanceReturnTree (second : Bool) : SFunc := if second then t_0adf_c5 else t_0a43_c5

def swapBalanceShortTree (second : Bool) : SFunc := if second then t_0af1_c5 else t_0a55_c5

def swapBalanceDecodeTree (second : Bool) : SFunc := if second then t_0af5_c5 else t_0a59_c5

def swapBalanceCodeDestination (second : Bool) : Bytes := if second then [0x0a,0xcb] else [0x0a,0x2f]

def swapBalanceCallDestination (second : Bool) : Bytes := if second then [0x0a,0xdf] else [0x0a,0x43]

def swapBalanceReturnDestination (second : Bool) : Bytes := if second then [0x0a,0xf5] else [0x0a,0x59]

def swapBalanceCodeTree (second : Bool) : SFunc :=
  syncCodeGuardLine.foldr SFunc.next
    (.next (.push (swapBalanceCodeDestination second) (by cases second <;> decide))
      (.branch (swapBalanceCodeFailure second) (swapBalanceCallTree second)))

def swapBalanceReplyTree (second : Bool) : SFunc :=
  (callFlagGuardLine (swapBalanceCallDestination second) (by cases second <;> decide)).foldr
    SFunc.next (.branch (swapBalanceCallFailure second) (swapBalanceReturnTree second))

/-- One exact static observation and its complete physical memory decoder. -/
structure SwapBalanceOccurrence (root start : Exec.Deriv) (b : Devm) (S : List B256)
    (M : Mem) (p token : B256) (second : Bool) (K : List SFunc) where
  step : CallOccurrenceStep root .staticcall
  gas : Nat
  gap : Exec.Deriv.ExecFreeUntil start step.occurrence.node
  sevmEq : step.occurrence.node.sevm = start.sevm
  codePresent : (b.getCode (swapTokenWord token).toAdr).size.toB256 ≠ 0
  input : step.occurrence.node.devm = St (temporalAccountAccessBase b (swapTokenWord token).toAdr)
    (gas.toB256 :: swapTokenWord token :: p :: 36 :: p :: 32 ::
      (p + 36) :: 0x70a08231 :: swapTokenWord token :: S)
    (swapBalanceRequest M p start.sevm.currentTarget) gas
  out : Bytes
  reply : StaticCallPost (temporalAccountAccessBase b (swapTokenWord token).toAdr)
    step.returned.devm ((p + 36) :: 0x70a08231 :: swapTokenWord token :: S)
    (swapBalanceRequest M p start.sevm.currentTarget) p 36 p 32 1 out
  short : out.length < 2 ^ 256
  long : 32 ≤ out.length
  calldata : ((swapBalanceRequest M p start.sevm.currentTarget).read p.toNat 36).1 =
    ExternalOperation.encode (.balanceOf start.sevm.currentTarget)
  answered : StaticAnswered start.sevm (temporalAccountAccessBase b (swapTokenWord token).toAdr)
    (swapTokenWord token).toAdr (ExternalOperation.encode (.balanceOf start.sevm.currentTarget)) out
  memory : step.returned.devm.memory = swapBalanceReply M p start.sevm.currentTarget out
  replyCut : CursorStateAt code cert step.returned (swapBalanceReplyTree second)
    step.returned.devm (1 :: (p + 36) :: 0x70a08231 :: swapTokenWord token :: S)
    step.returned.devm.memory K
  replyNode : replyCut.node = step.returned
  tail : CursorStateAt code cert step.returned (swapBalanceDecodedTail second)
    step.returned.devm (Bytes.toB256 (out.take 32) :: S)
    (swapBalanceReply M p start.sevm.currentTarget out) K
  pointer : PtrMem p (swapRequestSize (M.size) p) (swapBalanceReply M p start.sevm.currentTarget out)

/-- The supplied staged balance query derives its actual code guard, reply
flag, full bytes and word at the same moving pointer. -/
theorem swap_balance_occurrence {root start : Exec.Deriv} {b post : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} {p token : B256} {second : Bool} {n : Nat}
    (cut : CursorStateAt code cert start (swapBalanceCodeTree second) b
      (swapTokenWord token :: swapTokenWord token :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: swapTokenWord token :: S) (swapBalanceRequest M p start.sevm.currentTarget) K)
    (reached : Exec.Deriv.ParentPrefix root start) (success : root.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    Nonempty (SwapBalanceOccurrence root start b S M p token second K) := by
  have startSuccess : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨present, ⟨checked⟩⟩ := pair_code_guard_cursor_state cut startSuccess fork
    (swapBalanceCodeDestination second) (by cases second <;> decide) rfl
    (by cases second <;> decide)
  have callShape : swapBalanceCallTree second = .dest (.next (.reg .pop)
      (.next (.reg .gas) (.next (.exec .staticcall) (swapBalanceReplyTree second)))) := by
    cases second <;> rfl
  rw [callShape] at checked
  obtain ⟨checked⟩ := checked.dest cert_check startSuccess fork
  obtain ⟨gasCut⟩ := checked.line cert_check startSuccess fork [.reg .pop]
    rfl
    (by intro n member x equal; subst n
        simp only [List.mem_singleton, reduceCtorEq] at member)
    (by intro gas d line
        obtain ⟨_, primitive, line⟩ := Line.of_run_cons line
        obtain ⟨gas', state⟩ := ri_pop primitive
        cases line
        exact ⟨gas', state⟩)
  obtain ⟨step, cursor, gas, gap, env, _, input, _, placed, tree, conts⟩ :=
    gasCut.gasCall cert_check reached startSuccess fork
  have retEnv : step.returned.sevm = start.sevm :=
    (Cursor.parentStep_sevm step.edge).trans env
  have retSuccess : step.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq (step.sameFrame.snoc step.edge)).trans success
  have raw : Ninst.Run start.sevm step.occurrence.node.devm (.exec .staticcall)
      step.returned.devm := by
    refine ⟨step.occurrence.slot, step.occurrence.filled, step.occurrence.node.pc, ?_⟩
    rw [← env]
    simpa only [step.instruction, step.result] using step.occurrence.stepRun
  rw [input] at raw
  obtain ⟨flag, out, reply, short, answered⟩ := ri_staticcall_bounded fork raw
  let replyCut : CursorStateAt code cert step.returned (swapBalanceReplyTree second)
      step.returned.devm (flag :: (p + 36) :: 0x70a08231 :: swapTokenWord token :: S)
      step.returned.devm.memory K :=
    ⟨step.returned, cursor, .refl _, rfl, rfl, placed,
      (by rw [tree]), ⟨_, St.self reply.stack rfl⟩, conts⟩
  obtain ⟨one, ⟨returnCut⟩⟩ := replyCut.callFlag cert_check retSuccess
    (by rw [retEnv]; exact fork) (swapBalanceCallDestination second)
    (by cases second <;> decide) rfl reply.flag (by cases second <;> decide)
  subst flag
  have memory : step.returned.devm.memory = swapBalanceReply M p start.sevm.currentTarget out := reply.memory
  have pointer := swapBalanceReply_ptr (pair := start.sevm.currentTarget) out mem lower width
  have pointer' := memory.symm ▸ pointer
  have full : step.returned.devm.returnData.length < 2 ^ 256 := by
    rw [reply.returnData]
    exact short
  obtain ⟨long, ⟨tail⟩⟩ := returnCut.returnWord
    (shortTree := swapBalanceShortTree second) (decodeTree := swapBalanceDecodeTree second)
    (tail := swapBalanceDecodedTail second) cert_check retSuccess
    (by rw [retEnv]; exact fork) (swapBalanceReturnDestination second)
    (by cases second <;> decide) (by cases second <;> rfl)
    (by cases second <;> rfl) pointer' (by
      have cover := swapRequestSize_cover mem
      omega) full (by cases second <;> decide)
  rw [reply.returnData] at long
  have calldata := swapBalanceRequest_read (pair := start.sevm.currentTarget) mem.wf width
  have answered' := answered rfl
  rw [show (36 : B256).toNat = 36 from rfl, calldata] at answered'
  rw [memory, swapBalanceReply_word mem.wf out long] at tail
  have ptrSize : n = M.size := mem.size.symm
  rw [ptrSize] at pointer
  exact ⟨⟨step, gas, gap, env, present, input, out, reply, short, long, calldata,
    answered', memory, replyCut, rfl, tail, pointer⟩⟩

/-- The first balance request starts at the actual post-callback join. -/
theorem swap_first_balance_cursor_state {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {p t1 t0 : B256} {n : Nat}
    (cut : CursorStateAt code cert start t_09c3_c5 b (t1 :: t0 :: 0 :: 0 :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start) (success : root.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    Nonempty (SwapBalanceOccurrence root start b (t1 :: t0 :: 0 :: 0 :: R) M p t0 false K) := by
  have startSuccess : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨cut⟩ := cut.dest cert_check startSuccess fork
  obtain ⟨cut⟩ := cut.line cert_check startSuccess fork swapRequestLine rfl
    (by intro n member x equal; subst n
        simp only [swapRequestLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (swapRequestLine_inv mem lower width)
  obtain ⟨cut⟩ := cut.line cert_check startSuccess fork swapBalance0MaskLine rfl
    (by intro n member x equal; subst n
        simp only [swapBalance0MaskLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    swapBalance0MaskLine_inv
  obtain ⟨cut⟩ := cut.line cert_check startSuccess fork (swapStagePrepare false) rfl
    (by intro n member x equal; subst n
        simp only [swapStagePrepare, ite_false, List.mem_append, List.mem_cons,
          List.not_mem_nil, reduceCtorEq, or_self] at member)
    swapStagePrepare_inv
  exact swap_balance_occurrence cut reached success fork mem lower width

/-- The second request starts after decoding the first actual reply. -/
theorem swap_second_balance_cursor_state {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {p t1 t0 bal0 : B256} {n : Nat}
    (cut : CursorStateAt code cert start (swapBalanceDecodedTail false) b
      (bal0 :: t1 :: t0 :: 0 :: 0 :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start) (success : root.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    Nonempty (SwapBalanceOccurrence root start b (t1 :: t0 :: 0 :: bal0 :: R) M p t1 true K) := by
  have startSuccess : start.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success
  obtain ⟨cut⟩ := cut.line cert_check startSuccess fork swapRequestLine rfl
    (by intro n member x equal; subst n
        simp only [swapRequestLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (swapRequestLine_inv mem lower width)
  obtain ⟨cut⟩ := cut.line cert_check startSuccess fork swapBalance1MaskLine rfl
    (by intro n member x equal; subst n
        simp only [swapBalance1MaskLine, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    swapBalance1MaskLine_inv
  obtain ⟨cut⟩ := cut.line cert_check startSuccess fork (swapStagePrepare true) rfl
    (by intro n member x equal; subst n
        simp only [swapStagePrepare, ite_true, List.mem_append, List.mem_cons,
          List.not_mem_nil, reduceCtorEq, or_self] at member)
    swapStagePrepare_inv
  exact swap_balance_occurrence cut reached success fork mem lower width

/-- The physically decoded first balance replaces its own cached local slot. -/
def swapBalance1LocalsStack (sevm : Sevm) (b : Devm) (out0 : Bytes) : List B256 :=
  (swapRawLocalsStack sevm b).set 3 (Bytes.toB256 (out0.take 32))

/-- All optional calls and both required observations belong to one original
execution. The second observation consumes the first one's actual reply image. -/
structure SwapBalances (root : Exec.Deriv) (sevm : Sevm) (b : Devm) where
  optional : SwapCallbacks root sevm b
  first : SwapBalanceOccurrence root optional.callback.next optional.callback.world
    (swapRawLocalsStack sevm b) optional.callback.memory optional.transfers.second.ptr
    (swapInitialToken0 sevm b) false [t_0257_c99]
  second : SwapBalanceOccurrence root first.step.returned first.step.returned.devm
    (swapBalance1LocalsStack sevm b first.out)
    (swapBalanceReply optional.callback.memory optional.transfers.second.ptr
      optional.callback.next.sevm.currentTarget first.out)
    optional.transfers.second.ptr (swapInitialToken1 sevm b) true [t_0257_c99]

/-- Both final balance calls are derived from the same original successful
Swap; every full reply, decoder and gas is selected internally. -/
theorem swap_balances_cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (SwapBalances ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b) := by
  obtain ⟨optional⟩ := swap_callback_cursor_state codeEq fork selector run
  obtain ⟨n, mem⟩ := optional.callback.mem
  have forkC : CoveredFork optional.callback.next.sevm.benvStat.fork := by
    rw [optional.callback.sevmEq, optional.transfers.second.sevmEq, optional.transfers.first.sevmEq]
    exact fork
  have cut := optional.callback.cut
  dsimp only [swapRawLocalsStack, swapBodyStack] at cut
  obtain ⟨first⟩ := swap_first_balance_cursor_state cut optional.callback.reached rfl forkC mem
    optional.transfers.secondLower (by have upper := optional.transfers.secondUpper; omega)
  have fork0 : CoveredFork first.step.returned.sevm.benvStat.fork := by
    rw [Cursor.parentStep_sevm first.step.edge, first.sevmEq]
    exact forkC
  obtain ⟨second⟩ := swap_second_balance_cursor_state first.tail
    (first.step.sameFrame.snoc first.step.edge) rfl fork0 first.pointer
    optional.transfers.secondLower (by have upper := optional.transfers.secondUpper; omega)
  exact ⟨⟨optional, first, second⟩⟩

/-- The actual final reply's checked continuation and original stop entry
exclude every later same-frame external instruction. -/
theorem SwapBalances.noExecTail {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : SwapBalances root sevm b) (fork : CoveredFork root.sevm.benvStat.fork) :
    ∀ N, Exec.Deriv.ParentPrefix r.second.step.returned N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  have env : r.second.step.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq (r.second.step.sameFrame.snoc r.second.step.edge)
  rw [← r.second.replyNode]
  apply r.second.replyCut.placed.noExecSuffix cert_check
    (by rw [r.second.replyNode, env]; exact fork) (E := [6,7,8,9,18,19,20,21,22,58,59,60,65,66]) (by decide)
  · rw [r.second.replyCut.tree]; decide
  · intro f member
    rw [r.second.replyCut.continuations] at member
    simp only [List.mem_singleton] at member
    subst f
    decide

end Blanc.Lift.UniswapV2Pair
