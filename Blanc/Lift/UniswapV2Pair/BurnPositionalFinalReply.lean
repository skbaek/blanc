import Blanc.Lift.UniswapV2Pair.BurnPositionalFinalCall
import Blanc.Lift.CursorBalanceReply

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The supplied final-query returned parent supplies its own flag, full reply
width and physical decoded word, with the original continuations retained. -/
theorem burn_final_actual_reply_cursor {F : Exec.Deriv} {κ : Cursor}
    {b post : Devm} {R : List B256} {M : Mem} {flag a x y p : B256} {out : Bytes} {n : Nat}
    (site : BurnFinalBalanceSite) (placed : CursorOK code cert F κ)
    (tree : κ.f = burnFinalAfterCallTree site) (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork)
    (reply : StaticCallPost b F.devm (a :: x :: y :: R) M p 36 p 32 flag out)
    (mem : PtrMem p n M) (low : 96 ≤ p.toNat) (fit : p.toNat + 36 ≤ n)
    (bound : out.length < 2 ^ 256) :
    flag = 1 ∧ 32 ≤ out.length ∧
      PtrMem p n (burnBalanceReplyMemory M p out) ∧
      Nonempty (CursorStateAt code cert F site.afterDecodeTree F.devm
        (Bytes.toB256 (out.take 32) :: R) (burnBalanceReplyMemory M p out) (κ.K.map Cont.f)) := by
  let cut : CursorStateAt code cert F (burnFinalAfterCallTree site) F.devm
      (flag :: a :: x :: y :: R) (burnBalanceReplyMemory M p out) (κ.K.map Cont.f) :=
    ⟨F, κ, .refl F, rfl, rfl, placed, tree, ⟨F.devm.gasLeft, reply.eq_St⟩, rfl⟩
  have guarded : flag = 1 ∧ Nonempty (CursorStateAt code cert F site.returnTree
      F.devm (0 :: a :: x :: y :: R) (burnBalanceReplyMemory M p out) (κ.K.map Cont.f)) := by
    cases site with
    | first =>
      exact cut.callFlag (failedTree := t_171a_c13) (returnTree := t_1723_c13)
        cert_check success fork [0x17,0x23] (by decide) rfl reply.flag (by decide)
    | second =>
      exact cut.callFlag (failedTree := t_17b6_c13) (returnTree := t_17bf_c13)
        cert_check success fork [0x17,0xbf] (by decide) rfl reply.flag (by decide)
  obtain ⟨one, ⟨returned⟩⟩ := guarded
  have replyMem := burnBalanceReplyMemory_ptr out mem low fit
  have full : F.devm.returnData.length < 2 ^ 256 := by rw [reply.returnData]; exact bound
  have decoded : 32 ≤ F.devm.returnData.length ∧
      Nonempty (CursorStateAt code cert F site.afterDecodeTree F.devm
        (Bytes.toB256 ((burnBalanceReplyMemory M p out).read p.toNat 32).1 :: R)
        (burnBalanceReplyMemory M p out) (κ.K.map Cont.f)) := by
    cases site with
    | first =>
      exact returned.returnWord (p := p) (n := n)
        (shortTree := t_1735_c13) (decodeTree := t_1739_c13)
        (tail := BurnFinalBalanceSite.first.afterDecodeTree)
        cert_check success fork [0x17,0x39] (by decide)
        rfl rfl replyMem (by omega) full (by decide)
    | second =>
      exact returned.returnWord (p := p) (n := n)
        (shortTree := t_17d1_c13) (decodeTree := t_17d5_c13)
        (tail := BurnFinalBalanceSite.second.afterDecodeTree)
        cert_check success fork [0x17,0xd5] (by decide)
        rfl rfl replyMem (by omega) full (by decide)
  rw [reply.returnData] at decoded
  rw [burnBalanceReplyMemory_word mem fit decoded.1] at decoded
  exact ⟨one, decoded.1, replyMem, decoded.2⟩

end Blanc.Lift.UniswapV2Pair
