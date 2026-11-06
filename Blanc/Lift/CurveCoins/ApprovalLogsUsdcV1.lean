import Blanc.Lift.ApprovalLog
import Blanc.Lift.Usdc.V1ApproveRetainedLog
import Blanc.Lift.Usdc.AllowLocality
import Blanc.Lift.Usdc.InitRowsHistory

/-!
# USDC FiatTokenV1: a store that raises a tracked row, other than `initialize`, logs `Approval`

`implV1_allowSitesOk` certifies `selV1`: `approve` caller-keyed, `initialize` the only other writer. V1 has no signed
writer. `V1ApproveRetainedLog.frame_approve_write_emits` is the walk.
-/

namespace Blanc.Lift.CurveCoins.UsdcV1

open Jaune Blanc Blanc.Lift

/-- **A committed V1 frame with a store that raises one of `pair`'s tracked rows, other than in `initialize`, logs
`Approval` with `pair` as owner.** `sep` is hash freshness for the frame, as in `implV1_allowLocality`. -/
theorem row_raised_logs {pair : Adr} {Tr : Adr → Prop} {F : Exec.Frame} (hpc : F.pc = 0)
    (hcode : F.sevm.code = Usdc.ImplV1.code) (hsg : F.sevm.benvStat.rules.stateGas = none)
    (bal : F.sevm.benvStat.rules.bal = none) {node : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv F) node) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some w)
    (sep : WriteSite.RowSep 10 pair.toB256 (WriteSite.AllowKey Tr) (WriteSite.wsRoot Usdc.ImplV1Ws.implWsAnn)
      (WriteSite.Env.root F.sevm))
    (tracked : ∃ g, Tr g ∧ Usdc.allowSlot pair g = w.key)
    (raises : (node.devm.getStorVal node.sevm.currentTarget w.key).toNat < w.value.toNat)
    (notInit : Blanc.Sevm.selector F.sevm ≠ 0x3357162b) :
    FrameLogsApproval F.sevm.currentTarget pair F := by
  rcases WriteSite.rawWrite_rowClass (G := Exec.Frame.rootDeriv F) (t := Usdc.selV1) (b := 10) hpc hsg chain Usdc.ImplV1.cert_check
    Usdc.implV1_wsCert hcode (by decide) Usdc.implV1_allowSitesOk sep found tracked with allowed | le
  · have root : Usdc.selV1.selT.eval (WriteSite.Env.root F.sevm) = Blanc.Sevm.selector F.sevm := Usdc.selV1T_root _
    rcases allowed with ⟨sel, caller⟩ | ⟨sel, -⟩ | sel
    · have hsel : Blanc.Sevm.selector F.sevm = 0x095ea7b3 := root.symm.trans (List.mem_singleton.mp sel)
      have hc : F.sevm.caller = pair := by
        have e : (WriteSite.Env.root F.sevm).caller = F.sevm.caller.toB256 := rfl
        have c : (WriteSite.Env.root F.sevm).caller.toAdr = pair := caller
        rw [e, toAdr_toB256] at c
        exact c
      obtain ⟨-, event⟩ := Usdc.V1ApproveRetainedLog.frame_approve_write_emits hpc hcode hsg bal hsel chain found
      subst hc
      exact ⟨_, event, rfl, rfl⟩
    · exact (List.not_mem_nil sel).elim
    · have s : Blanc.Sevm.selector F.sevm = 0x3357162b := root.symm.trans (List.mem_singleton.mp sel)
      exact absurd s notInit
  · exact absurd raises (Nat.not_lt.mpr le)

end Blanc.Lift.CurveCoins.UsdcV1
