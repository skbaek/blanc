import Blanc.Lift.UniswapV2Pair.SkimPositionalFirst
import Blanc.Lift.CursorBalanceReply
import Blanc.ExecutionModelAccounting

namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive SkimBalanceSite where
  | first
  | second

def SkimBalanceSite.afterCallTree : SkimBalanceSite → SFunc
  | .first => skimFirstAfterCallTree
  | .second => (callFlagGuardLine [0x1a, 0x02] (by decide)).foldr SFunc.next
      (.branch t_19f9_c67 t_1a02_c67)

def SkimBalanceSite.returnTree : SkimBalanceSite → SFunc
  | .first => t_1a02_c34
  | .second => t_1a02_c67

def SkimBalanceSite.afterDecodeTree (site : SkimBalanceSite) : SFunc :=
  .next (.reg (.swap 0)) (.next (.push [0xff, 0xff, 0xff, 0xff] (by decide))
    (.next (.push [0x22, 0x6e] (by decide)) (.next (.reg .and)
      (.callNext 59 (match site with | .first => t_1a26_c34 | .second => t_1a26_c67)))))

/-- Both checked contexts decode at the supplied actual returned cursor. -/
theorem skim_actual_reply_cursor {F : Exec.Deriv} {κ : Cursor}
    {post : Devm} {R : List B256} {M : Mem} {flag a x y p : B256} {n : Nat}
    (site : SkimBalanceSite) (placed : CursorOK code cert F κ)
    (tree : κ.f = site.afterCallTree) (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork)
    (state : F.devm = St F.devm (flag :: a :: x :: y :: R) M F.devm.gasLeft)
    (flag01 : flag = 0 ∨ flag = 1) (mem : PtrMem p n M)
    (fit : p.toNat + 32 ≤ n) (bound : F.devm.returnData.length < 2 ^ 256) :
    flag = 1 ∧ 32 ≤ F.devm.returnData.length ∧
      Nonempty (CursorStateAt code cert F site.afterDecodeTree F.devm
        (Bytes.toB256 (M.read p.toNat 32).1 :: R) M (κ.K.map Cont.f)) := by
  let cut : CursorStateAt code cert F site.afterCallTree F.devm
      (flag :: a :: x :: y :: R) M (κ.K.map Cont.f) :=
    ⟨F, κ, .refl F, rfl, rfl, placed, tree, ⟨F.devm.gasLeft, state⟩, rfl⟩
  have guarded : flag = 1 ∧ Nonempty (CursorStateAt code cert F site.returnTree
      F.devm (0 :: a :: x :: y :: R) M (κ.K.map Cont.f)) := by
    cases site with
    | first =>
      exact cut.callFlag (failedTree := t_19f9_c34) (returnTree := t_1a02_c34)
        cert_check success fork [0x1a, 0x02] (by decide) rfl flag01 (by decide)
    | second =>
      exact cut.callFlag (failedTree := t_19f9_c67) (returnTree := t_1a02_c67)
        cert_check success fork [0x1a, 0x02] (by decide) rfl flag01 (by decide)
  obtain ⟨one, ⟨returned⟩⟩ := guarded
  refine ⟨one, ?_⟩
  cases site with
  | first =>
    exact returned.returnWord (shortTree := t_1a14_c34) (decodeTree := t_1a18_c34)
      cert_check success fork [0x1a, 0x18] (by decide) rfl rfl mem fit bound (by decide)
  | second =>
    exact returned.returnWord (shortTree := t_1a14_c67) (decodeTree := t_1a18_c67)
      cert_check success fork [0x1a, 0x18] (by decide) rfl rfl mem fit bound (by decide)

structure SkimFirstObservation (root : Exec.Deriv) (b : Devm)
    (toWord : B256) (R : List B256) where
  call : CallOccurrenceStep root .staticcall
  cursor : Cursor
  gas : Nat
  out : Bytes
  nonstatic : root.sevm.isStatic = false
  codeGuard : ((skimCachedWorld root.sevm b).getCode (skimToken0 root.sevm b).toAdr).size.toB256 ≠ 0
  gap : Exec.Deriv.ExecFreeUntil root call.occurrence.node
  sevm : call.occurrence.node.sevm = root.sevm
  exn : call.occurrence.node.exn = root.exn
  input : call.occurrence.node.devm = St
    (temporalAccountAccessBase (skimCachedWorld root.sevm b) (skimToken0 root.sevm b).toAdr)
    (gas.toB256 :: skimToken0 root.sevm b :: 128 :: 36 :: 128 :: 32 ::
      skimFirstBalanceRest root.sevm b toWord R)
    (balanceRequestMemory getterInitMemory root.sevm.currentTarget) gas
  primitive : Ninst.RunWith (Cursor.DescOf call.occurrence.node) root.sevm
    call.occurrence.node.devm (.exec .staticcall) call.returned.devm
  placed : CursorOK code cert call.returned cursor
  tree : cursor.f = skimFirstAfterCallTree
  continuations : cursor.K.map Cont.f = []
  reply : StaticCallPost
    (temporalAccountAccessBase (skimCachedWorld root.sevm b) (skimToken0 root.sevm b).toAdr)
    call.returned.devm (skimFirstBalanceRest root.sevm b toWord R)
    (balanceRequestMemory getterInitMemory root.sevm.currentTarget) 128 36 128 32 1 out
  long : 32 ≤ out.length
  bound : out.length < 2 ^ 256
  answered : StaticAnswered root.sevm
    (temporalAccountAccessBase (skimCachedWorld root.sevm b) (skimToken0 root.sevm b).toAdr)
    (skimToken0 root.sevm b).toAdr
    (ExternalOperation.encode (.balanceOf root.sevm.currentTarget)) out
  decoded : CursorStateAt code cert call.returned SkimBalanceSite.first.afterDecodeTree
    call.returned.devm
    (Bytes.toB256 (out.take 32) :: (skimFirstBalanceRest root.sevm b toWord R).tail.tail.tail)
    (balanceReplyMemory getterInitMemory root.sevm.currentTarget out) []

/-- The observation and physical decoding come from the same first occurrence. -/
theorem skim_first_observation_of_prefix {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {toWord : B256}
    (cut : CursorStateAt code cert root t_194f_c34 (afterSload root.sevm b 12)
      (toWord :: R) getterInitMemory [])
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (SkimFirstObservation root b toWord R) := by
  obtain ⟨nonstatic, codeGuard, step, cursor, gas, gap, env, outcome, input,
    primitive, placed, tree, conts⟩ := skim_first_call_of_prefix cut success fork
  have envRet : step.returned.sevm = root.sevm := (Cursor.parentStep_sevm step.edge).trans env
  have successRet : step.returned.exn = .ok post := by
    exact (Blanc.Exec.Deriv.ParentPrefix.exn_eq (step.sameFrame.snoc step.edge)).trans success
  have call := primitive.toRun
  rw [input] at call
  obtain ⟨flag, out, reply, bound, answered⟩ := ri_staticcall_bounded fork call
  have mem := balanceReplyMemory_ptr out
    (balanceRequestMemory_ptr getterInitMemory_ptr root.sevm.currentTarget)
  obtain ⟨one, long, ⟨decoded⟩⟩ := skim_actual_reply_cursor
    (M := balanceReplyMemory getterInitMemory root.sevm.currentTarget out)
    (p := 128) (n := 192) .first placed tree successRet
    (by rw [envRet]; exact fork) reply.eq_St reply.flag mem (by decide) (by
      rw [reply.returnData]; exact bound)
  rw [reply.returnData] at long
  rw [conts, show (128 : B256).toNat = 128 from rfl, balanceReplyMemory_word getterInitMemory_ptr.wf root.sevm.currentTarget out long]
    at decoded
  have accepted := answered one
  change StaticAnswered root.sevm _ _
    ((balanceRequestMemory getterInitMemory root.sevm.currentTarget).read 128 36).1 out at accepted
  rw [balanceRequestMemory_read getterInitMemory_ptr.wf] at accepted
  rw [one] at reply
  exact ⟨⟨step, cursor, gas, out, nonstatic, codeGuard, gap, env, outcome, input,
    primitive, placed, tree, conts, reply, long, bound, accepted, decoded⟩⟩

end Blanc.Lift.UniswapV2Pair
