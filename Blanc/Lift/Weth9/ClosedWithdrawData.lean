import Blanc.Lift.Weth9.ClosedSigningData

/-! Concrete gas and address side conditions of the full one-wei exit. -/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc

theorem closed_withdraw_intrinsic : withdrawIntrinsicGas amount = 21204 := by
  simp only [withdrawIntrinsicGas, withdrawCalldata, amount, wdSel_eq]
  decide +kernel

theorem closed_withdraw_frame : withdrawFrameGas amount = 13940 := by decide +kernel

theorem closed_withdraw_gas :
    withdrawIntrinsicGas amount + withdrawFrameGas amount + 811 ≤ withdrawTx.gas := by
  rw [closed_withdraw_intrinsic, closed_withdraw_frame]
  change 35955 ≤ 40000
  decide +kernel

theorem closed_withdraw_cap : withdrawTx.gas ≤ 16777216 := by decide +kernel

theorem closed_withdraw_nonceMax : withdrawTx.nonce ≠ UInt64.max := by decide +kernel

theorem closed_sender_precompile : Fork.bpo2.ruleSet.isPrecomp senderE = false := by
  decide +kernel

theorem closed_contract_precompile : Fork.bpo2.ruleSet.isPrecomp contractAddress = false := by
  decide +kernel

theorem closed_coinbase_sender : (0 : Adr) ≠ senderE := by decide +kernel

theorem closed_coinbase_contract : (0 : Adr) ≠ contractAddress := by decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
