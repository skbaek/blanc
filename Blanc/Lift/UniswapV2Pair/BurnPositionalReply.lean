import Blanc.Lift.CursorSourceRun
import Blanc.Lift.CursorBalanceReply
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.BurnPrefixWalk

/-! Actual initial Burn replies and their checked decoding continuations. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def BurnInitialBalanceSite.afterCallTree (site : BurnInitialBalanceSite) : SFunc :=
  match site.callTree with
  | .dest (.next _ (.next _ (.next _ tail))) => tail
  | _ => .undefined

/-- The successful suffix at an actual initial reply requires the real call
flag and complete returndata width. It retains that same physical reply memory. -/
theorem burn_initial_reply_guards {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {d : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {flag a x y : B256} {seg : Seg}
    (site : BurnInitialBalanceSite)
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (flag01 : flag = 0 ∨ flag = 1) (mem : PtrMem 128 192 M)
    (bound : d.returnData.length < 2 ^ 256)
    (run : SFunc.RunCutP P fs sevm C (St d (flag :: a :: x :: y :: R) M G)
      site.afterCallTree seg) :
    flag = 1 ∧ 32 ≤ d.returnData.length := by
  have shape : site.afterCallTree =
      .next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero)
        (.next (.push (match site with | .first => [0x15,0x0f] | .second => [0x15,0xad])
          (by cases site <;> (change (2 : Nat) ≤ 32; decide)))
          (.branch (match site with | .first => t_1506_c37 | .second => t_15a4_c37)
            site.returnTree)))) := by cases site <;> rfl
  rw [shape] at run
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (project step)
  obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (project step)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, tailGas, tail⟩
  · exact (failed.false_of_noOk (by
      cases site with
      | first => exact (by decide : t_1506_c37.noOk = true)
      | second => exact (by decide : t_15a4_c37.noOk = true))).elim
  · have zeroFlag : B256.eqCheck flag 0 = 0 := eq_zero_of_iszero_ne_zero accepted
    have one : flag = 1 := by
      rcases flag01 with zero | one
      · rw [zero, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zeroFlag
        exact ((by decide : (1 : B256) ≠ 0) zeroFlag).elim
      · exact one
    subst flag
    have tail' : SFunc.RunCutP P fs sevm C (St d (0 :: a :: x :: y :: R) M tailGas) site.returnTree seg := by
      simpa only [show B256.eqCheck (1 : B256) 0 = 0 from by decide] using tail
    have width : 32 ≤ d.returnData.length := by
      cases site
      · exact (returnWidthGuard_invP [0x15,0x25] (by decide) rfl project mem bound (by decide) tail').1
      · exact (returnWidthGuard_invP [0x15,0xc3] (by decide) rfl project mem bound (by decide) tail').1
    exact ⟨rfl, width⟩

/-- Only the actual returned node supplies the source suffix used for reply
guards; the call's already classified physical reply state remains unchanged. -/
theorem burn_initial_actual_reply_guards {F : Exec.Deriv} {κ : Cursor}
    {b post : Devm} {R : List B256} {M : Mem} {flag a x y : B256} {out : Bytes}
    (site : BurnInitialBalanceSite) (placed : CursorOK code cert F κ)
    (tree : κ.f = site.afterCallTree) (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork)
    (reply : StaticCallPost b F.devm (a :: x :: y :: R)
      (balanceRequestMemory M F.sevm.currentTarget) 128 36 128 32 flag out)
    (mem : PtrMem 128 192 (balanceReplyMemory M F.sevm.currentTarget out))
    (bound : out.length < 2 ^ 256) :
    flag = 1 ∧ 32 ≤ out.length := by
  obtain ⟨outcome, source⟩ := placed.sourceRun cert_check success fork
  rw [tree, reply.eq_St] at source
  have source' : SFunc.RunCutP (StepIn F) cert.prog F.sevm []
      (St F.devm (flag :: a :: x :: y :: R)
        (balanceReplyMemory M F.sevm.currentTarget out) F.devm.gasLeft)
      site.afterCallTree (.done outcome) := SFunc.runP_iff_runCutP_nil.mp source
  have classified := burn_initial_reply_guards site (fun step => step.toRun)
    reply.flag mem (by rw [reply.returnData]; exact bound) source'
  rw [reply.returnData] at classified
  exact classified


/-- Classify and decode the supplied actual returned parent, preserving its
complete world, physical reply memory, and original mapped continuation. -/
theorem burn_initial_actual_reply_cursor {F : Exec.Deriv} {κ : Cursor}
    {b post : Devm} {R : List B256} {M : Mem} {flag a x y : B256} {out : Bytes}
    (site : BurnInitialBalanceSite) (placed : CursorOK code cert F κ)
    (tree : κ.f = site.afterCallTree) (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork)
    (reply : StaticCallPost b F.devm (a :: x :: y :: R)
      (balanceRequestMemory M F.sevm.currentTarget) 128 36 128 32 flag out)
    (mem : PtrMem 128 192 (balanceReplyMemory M F.sevm.currentTarget out))
    (bound : out.length < 2 ^ 256) :
    flag = 1 ∧ 32 ≤ out.length ∧
      Nonempty (CursorStateAt code cert F site.afterDecodeTree F.devm
        (Bytes.toB256 ((balanceReplyMemory M F.sevm.currentTarget out).read 128 32).1 :: R)
        (balanceReplyMemory M F.sevm.currentTarget out) (κ.K.map Cont.f)) := by
  let cut : CursorStateAt code cert F site.afterCallTree F.devm
      (flag :: a :: x :: y :: R) (balanceReplyMemory M F.sevm.currentTarget out)
      (κ.K.map Cont.f) :=
    ⟨F, κ, .refl F, rfl, rfl, placed, tree, ⟨F.devm.gasLeft, reply.eq_St⟩, rfl⟩
  have guarded : flag = 1 ∧ Nonempty (CursorStateAt code cert F site.returnTree
      F.devm (0 :: a :: x :: y :: R) (balanceReplyMemory M F.sevm.currentTarget out)
      (κ.K.map Cont.f)) := by
    cases site with
    | first =>
      exact cut.callFlag (failedTree := t_1506_c37) (returnTree := t_150f_c37)
        cert_check success fork [0x15,0x0f] (by decide)
        rfl reply.flag (by decide)
    | second =>
      exact cut.callFlag (failedTree := t_15a4_c37) (returnTree := t_15ad_c37)
        cert_check success fork [0x15,0xad] (by decide)
        rfl reply.flag (by decide)
  obtain ⟨one, returned⟩ := guarded
  obtain ⟨returned⟩ := returned
  have full : F.devm.returnData.length < 2 ^ 256 := by rw [reply.returnData]; exact bound
  have decoded : 32 ≤ F.devm.returnData.length ∧
      Nonempty (CursorStateAt code cert F site.afterDecodeTree F.devm
        (Bytes.toB256 ((balanceReplyMemory M F.sevm.currentTarget out).read 128 32).1 :: R)
        (balanceReplyMemory M F.sevm.currentTarget out) (κ.K.map Cont.f)) := by
    cases site with
    | first =>
      exact returned.returnWord (p := 128) (n := 192)
        (shortTree := t_1521_c37) (decodeTree := t_1525_c37)
        (tail := BurnInitialBalanceSite.first.afterDecodeTree)
        cert_check success fork [0x15,0x25] (by decide)
        rfl rfl mem (by decide) full (by decide)
    | second =>
      exact returned.returnWord (p := 128) (n := 192)
        (shortTree := t_15bf_c37) (decodeTree := t_15c3_c37)
        (tail := BurnInitialBalanceSite.second.afterDecodeTree)
        cert_check success fork [0x15,0xc3] (by decide)
        rfl rfl mem (by decide) full (by decide)
  rw [reply.returnData] at decoded
  exact ⟨one, decoded⟩

end Blanc.Lift.UniswapV2Pair
