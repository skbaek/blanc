import Blanc.Lift.HistCursorCalls
import Blanc.Lift.CursorBalanceReply
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk

/-! Actual Mint static replies, call guards, and physical decoding. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem mint_balance_reply_cursor_stateH {start : Exec.Deriv} {b post : Devm}
    {f : SFunc} {R : List B256} {M : Mem} {K : List SFunc} {flag a x y : B256} {out : Bytes}
    (site : MintBalanceSite)
    (cut : CursorStateAt code cert start f b (flag :: a :: x :: y :: R)
      (balanceReplyMemory M start.sevm.currentTarget out) K)
    (shape : f = (callFlagGuardLine (match site with | .first => [0x11,0x22] | .second => [0x11,0xc5])
      (by cases site <;> (change (2 : Nat) ≤ 32; decide))).foldr SFunc.next
      (.branch (match site with | .first => t_1119_c41 | .second => t_11bc_c41) site.returnTree))
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (flag01 : flag = 0 ∨ flag = 1) (data : b.returnData = out)
    (bound : out.length < 2 ^ 256)
    (mem : PtrMem 128 192 (balanceRequestMemory M start.sevm.currentTarget))
    (wf : Mem.Wf M) :
    flag = 1 ∧ 32 ≤ out.length ∧
      Nonempty (CursorStateAt code cert start site.afterDecodeTree b
        (Bytes.toB256 (out.take 32) :: R)
        (balanceReplyMemory M start.sevm.currentTarget out) K) := by
  cases site with
  | first =>
    obtain ⟨one, returned⟩ := cut.callFlagH (failedTree := t_1119_c41)
      (returnTree := MintBalanceSite.first.returnTree) cert_check success stateGas
      [0x11,0x22] (by decide) shape flag01 (by decide)
    obtain ⟨returned⟩ := returned
    obtain ⟨width, decoded⟩ := returned.returnWordH
      (shortTree := t_1134_c41) (decodeTree := MintBalanceSite.first.decodeTree)
      (tail := MintBalanceSite.first.afterDecodeTree) (p := 128) (n := 192)
      cert_check success stateGas [0x11,0x38] (by decide) rfl rfl
      (balanceReplyMemory_ptr out mem) (by decide : (128 : B256).toNat + 32 ≤ 192)
      (by rw [data]; exact bound) (by decide)
    rw [data] at width
    rw [show (128 : B256).toNat = 128 from rfl,
      balanceReplyMemory_word wf start.sevm.currentTarget out width] at decoded
    exact ⟨one, width, decoded⟩
  | second =>
    obtain ⟨one, returned⟩ := cut.callFlagH (failedTree := t_11bc_c41)
      (returnTree := MintBalanceSite.second.returnTree) cert_check success stateGas
      [0x11,0xc5] (by decide) shape flag01 (by decide)
    obtain ⟨returned⟩ := returned
    obtain ⟨width, decoded⟩ := returned.returnWordH
      (shortTree := t_11d7_c41) (decodeTree := MintBalanceSite.second.decodeTree)
      (tail := MintBalanceSite.second.afterDecodeTree) (p := 128) (n := 192)
      cert_check success stateGas [0x11,0xdb] (by decide) rfl rfl
      (balanceReplyMemory_ptr out mem) (by decide : (128 : B256).toNat + 32 ≤ 192)
      (by rw [data]; exact bound) (by decide)
    rw [data] at width
    rw [show (128 : B256).toNat = 128 from rfl,
      balanceReplyMemory_word wf start.sevm.currentTarget out width] at decoded
    exact ⟨one, width, decoded⟩


end Blanc.Lift.UniswapV2Pair
