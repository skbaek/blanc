import Blanc.Lift.InvWalkStep

/-!
# The `Approval` log a reader filters on

`approvalTopic` and `LogsApprovalAs` state what each coin's `Approval` law concludes. Nothing here names a coin.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.Lift

/-- The `Approval(address,address,uint256)` topic. -/
def approvalTopic : B256 := 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925

/-- The push of `approvalTopic` as the certified runtimes spell it. -/
theorem approvalTopic_bytes : Bytes.toB256 [0x8c, 0x5b, 0xe1, 0xe5, 0xeb, 0xec, 0x7d, 0x5b, 0xd1, 0x4f, 0x71, 0x42, 0x7d,
    0x1e, 0x84, 0xf3, 0xdd, 0x03, 0x14, 0xc0, 0xf7, 0xb2, 0x29, 0x1e, 0x5b, 0x20, 0x0a, 0xc8, 0xc7, 0xc3, 0xb9, 0x25] =
    approvalTopic := by decide

/-- A frame's logs hold `Approval` with `h` as owner, at `T`. This is what `eth_getLogs` filters on. -/
def FrameLogsApproval (T h : Adr) (F : Exec.Frame) : Prop :=
  ∃ l ∈ F.post.logs, l.address = T ∧ l.topics.take 2 = [approvalTopic, h.toB256]

/-- A successful `RETURN` halt keeps the base's logs. -/
theorem ric_return_logs {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b post : Devm}
    {i sz : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunCut fs sevm C (St b (i :: sz :: S) M G) (.last .return_)
      (.done (.halted post))) : post.logs = b.logs := by
  cases run with
  | last hl => exact (ri_return hl).2.2

end Blanc.Lift.CurveCoins
