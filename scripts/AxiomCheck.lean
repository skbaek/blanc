import Blanc.Solvent
import Blanc.Conserved
import Blanc.FlashSpec
import Blanc.WethCode
import Blanc.FmintCode
import Blanc.Compiled
import Blanc.Reverts
import Blanc.FmintLive
import Blanc.FmintReverts
import Blanc.WethLive
import Blanc.FmintGas
import Blanc.WethGas
import Blanc.FmintSettles
import Blanc.Weth10Backed
import Blanc.Weth10Spec

#print axioms Blanc.weth_preserves_solvent
#print axioms Blanc.stateTransition_preserves_solvent
#print axioms Blanc.chain_preserves_solvent
#print axioms Blanc.addBlockToChain_preserves_solvent
#print axioms Blanc.stateTransitionUsing_preserves_solvent
#print axioms Blanc.chainUsing_preserves_solvent
#print axioms Blanc.addBlockToChainUsing_preserves_solvent
#print axioms Blanc.fmint_preserves_conserved
#print axioms Blanc.stateTransition_preserves_conserved
#print axioms Blanc.chain_preserves_conserved
#print axioms Blanc.addBlockToChain_preserves_conserved
#print axioms Blanc.stateTransitionUsing_preserves_conserved
#print axioms Blanc.chainUsing_preserves_conserved
#print axioms Blanc.addBlockToChainUsing_preserves_conserved
#print axioms Blanc.Fmint.fmint_flashLoan_spec
#print axioms Blanc.Fmint.no_success_of_callback_never_magic
#print axioms Blanc.Fmint.no_success_of_callback_never_returns_word
#print axioms Blanc.Fmint.no_success_of_token_ne_self
#print axioms Blanc.Fmint.no_success_of_receiver_not_address
#print axioms Blanc.Fmint.no_success_of_amount_over_maxFlashLoan
#print axioms Blanc.Fmint.no_success_of_allowance_below_amount
#print axioms Blanc.Fmint.no_success_of_balance_below_amount
#print axioms Blanc.Fmint.settles_with_error_of_callback_never_magic
#print axioms Blanc.Fmint.settles_with_error_of_callback_never_returns_word
#print axioms Blanc.Fmint.settles_with_error_of_token_ne_self
#print axioms Blanc.Fmint.settles_with_error_of_receiver_not_address
#print axioms Blanc.Fmint.settles_with_error_of_amount_over_maxFlashLoan
#print axioms Blanc.Fmint.settles_with_error_of_allowance_below_amount
#print axioms Blanc.Fmint.settles_with_error_of_balance_below_amount
#print axioms Blanc.wethCode_compile
#print axioms Blanc.fmintCode_compile
#print axioms Blanc.ProcessMessage.rollback_of_error
#print axioms Blanc.Fmint.rollback_of_callback_failure
#print axioms Blanc.Fmint.rollback_of_no_success
#print axioms Blanc.Fmint.rollback_of_no_success_total
#print axioms Blanc.Fmint.rollback_of_callback_never_magic
#print axioms Blanc.Fmint.rollback_of_callback_never_returns_word
#print axioms Blanc.Fmint.rollback_of_token_ne_self
#print axioms Blanc.Fmint.rollback_of_receiver_not_address
#print axioms Blanc.Fmint.rollback_of_amount_over_maxFlashLoan
#print axioms Blanc.Fmint.rollback_of_allowance_below_amount
#print axioms Blanc.Fmint.rollback_of_balance_below_amount
#print axioms Blanc.Prog.exec_of_runCompiled
#print axioms Blanc.Prog.runCompiled_iff_exec
#print axioms Blanc.Prog.exec_of_runCompiledTo
#print axioms Blanc.Fmint.totalSupply_runCompiled
#print axioms Blanc.Fmint.fmint_totalSupply_succeeds
#print axioms Blanc.weth_balanceOf_runCompiled
#print axioms Blanc.weth_balanceOf_succeeds
#print axioms Blanc.weth_balanceOf_gas_exact
#print axioms Blanc.weth_balanceOf_gas_of_runCompiled
#print axioms Blanc.Fmint.totalSupply_gas_exact
#print axioms Blanc.Fmint.totalSupply_gas_of_runCompiled
#print axioms Blanc.weth_decimals_runCompiled
#print axioms Blanc.weth_decimals_gas_exact
#print axioms Blanc.weth_decimals_succeeds
#print axioms Blanc.weth_decimals_gas_of_runCompiled
#print axioms Blanc.wethGas_eq_with
#print axioms Blanc.weth_balanceOf_gas_exact_wethGas
#print axioms Blanc.weth_decimals_gas_exact_wethGas
#print axioms Blanc.Fmint.decimals_runCompiled
#print axioms Blanc.Fmint.decimals_gas_exact
#print axioms Blanc.Fmint.fmint_decimals_succeeds
#print axioms Blanc.Fmint.decimals_gas_of_runCompiled
#print axioms Blanc.Fmint.fmintGas_eq_with
#print axioms Blanc.Fmint.totalSupply_gas_exact_fmintGas
#print axioms Blanc.Fmint.decimals_gas_exact_fmintGas
#print axioms Blanc.weth_balanceOf_gas_of_runCompiled_wethGas
#print axioms Blanc.weth_decimals_gas_of_runCompiled_wethGas
#print axioms Blanc.Fmint.totalSupply_gas_of_runCompiled_fmintGas
#print axioms Blanc.Fmint.decimals_gas_of_runCompiled_fmintGas
#print axioms Blanc.weth_balanceOf_warm_runCompiled
#print axioms Blanc.weth_balanceOf_warm_gas_exact
#print axioms Blanc.wethGasMax_eq_with
#print axioms Blanc.wethGas_le_max
#print axioms Blanc.Fmint.totalSupply_warm_runCompiled
#print axioms Blanc.Fmint.totalSupply_warm_gas_exact
#print axioms Blanc.Fmint.fmintGasMax_eq_with
#print axioms Blanc.Fmint.fmintGas_le_max
#print axioms Blanc.Fmint.unknownSelector_runCompiledTo
#print axioms Blanc.Fmint.fmint_unknown_selector_reverts
#print axioms Blanc.Fmint.tokenNeSelf_runCompiledTo
#print axioms Blanc.Fmint.fmint_token_ne_self_reverts
#print axioms Blanc.rollback_revert_of_exec_revert
#print axioms Blanc.rollback_revert_of_runCompiledTo
#print axioms Blanc.Fmint.rollback_revert_of_token_ne_self
#print axioms Blanc.Fmint.fmint_flashLoan_settles
#print axioms Blanc.Fmint.fmint_flashLoan_frame_settles
#print axioms Blanc.Fmint.receiverNotAddress_runCompiledTo
#print axioms Blanc.Fmint.fmint_receiver_not_address_reverts
#print axioms Blanc.Fmint.fmint_amount_over_bound_reverts
#print axioms Blanc.Fmint.fmint_flashLoan_settles_of_call
#print axioms Blanc.Stor.Weth10Inv.silent
#print axioms Blanc.Stor.Weth10Inv.deposit
#print axioms Blanc.Stor.Weth10Inv.transfer
#print axioms Blanc.Stor.Weth10Inv.flashMint
#print axioms Blanc.Stor.Weth10Inv.flashBurn
#print axioms Blanc.Stor.Weth10Inv.withdraw
#print axioms Blanc.Stor.Weth10Inv.of_empty
#print axioms Blanc.Weth10.backedSpec
