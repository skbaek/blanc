import Blanc.Solvent
import Blanc.Conserved
import Blanc.FlashSpec
import Blanc.WethCode
import Blanc.FmintCode
import Blanc.Weth10Code
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
import Blanc.Weth10Sound
import Blanc.Weth10StateSound
import Blanc.Weth10Live
import Blanc.Weth10Read
import Blanc.Weth10StateFunctional
import Blanc.Weth10FlashFunctional
import Blanc.Weth10TransferFunctional
import Blanc.Weth10Erc677Functional
import Blanc.Weth10Permit
import Blanc.Weth10Errors
import Blanc.Weth10DeployProof
import Blanc.Weth10Stable
import Blanc.Weth10Redeemable

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
#print axioms Blanc.Weth10.weth10_compiles
#print axioms Blanc.Weth10.weth10Code_compile
#print axioms Blanc.Func.compile_eq_emitUnchecked
#print axioms Blanc.Table.compile_eq_emitUnchecked
#print axioms Blanc.Prog.compile_eq_emitUnchecked
#print axioms Blanc.Func.CompileShape.byteSize_compileShape
#print axioms Blanc.Func.length_emitByShape
#print axioms Blanc.Func.getD_emitByShape
#print axioms Blanc.Func.emitByShape_compileShape
#print axioms Blanc.Func.CompileShape.locations_compileShapes
#print axioms Blanc.Table.emitByShape_compileShapes
#print axioms Blanc.Prog.emitByShape_compileShape
#print axioms Blanc.Func.exec_of_runCompiled_subcode
#print axioms Blanc.Func.exec_of_runCompiled_prefix
#print axioms Blanc.Func.exec_of_runCompiledTo_subcode
#print axioms Blanc.Func.exec_of_runCompiledTo_prefix
#print axioms Blanc.Rinst.runCore_extcodesize_cold_eq_ok
#print axioms Blanc.Rinst.runCore_extcodesize_warm_eq_ok
#print axioms Blanc.Ninst.runCompiled_extcodesize_cold
#print axioms Blanc.Ninst.runCompiled_extcodesize_warm
#print axioms Blanc.Func.runCompiledTo_revReturnData
#print axioms Blanc.Frame.enter_eq_done_executePrecomp
#print axioms Blanc.Xinst.step_statcall
#print axioms Blanc.Xinst.step_statcall_spawn
#print axioms Blanc.Ninst.runCompiled_statcall_doneFrame
#print axioms Blanc.of_run_call_val_with_depth
#print axioms Blanc.of_run_statcall_val_with_depth_cause
#print axioms Blanc.of_run_statcall_val_with_depth
#print axioms Blanc.Weth10.flashFee_runCompiled
#print axioms Blanc.Weth10.balanceOf_cold_runCompiled
#print axioms Blanc.Weth10.balanceOf_warm_runCompiled
#print axioms Blanc.Weth10.totalSupply_cold_runCompiled
#print axioms Blanc.Weth10.totalSupply_warm_runCompiled
#print axioms Blanc.Weth10.maxFlashLoan_cold_runCompiled
#print axioms Blanc.Weth10.maxFlashLoan_warm_runCompiled
#print axioms Blanc.Weth10.maxFlashLoan_other_runCompiled
#print axioms Blanc.Weth10.name_exec_output
#print axioms Blanc.Weth10.symbol_exec_output
#print axioms Blanc.Weth10.callbackSuccess_exec_output
#print axioms Blanc.Weth10.permitTypehash_exec_output
#print axioms Blanc.Weth10.decimals_exec_output
#print axioms Blanc.Weth10.deploymentChainId_exec_output
#print axioms Blanc.Weth10.domainSeparator_output
#print axioms Blanc.Weth10.domainSeparator_exec_output
#print axioms Blanc.Weth10.balanceOf_exec_output
#print axioms Blanc.Weth10.allowance_exec_output
#print axioms Blanc.Weth10.nonces_exec_output
#print axioms Blanc.Weth10.flashMinted_exec_output
#print axioms Blanc.Weth10.totalSupply_exec_output
#print axioms Blanc.Weth10.maxFlashLoan_exec_output
#print axioms Blanc.Weth10.flashFee_exec_output
#print axioms Blanc.Weth10.approve_exec_effect
#print axioms Blanc.Weth10.depositTo_exec_effect
#print axioms Blanc.Weth10.deposit_exec_effect
#print axioms Blanc.Weth10.receive_exec_effect
#print axioms Blanc.Weth10.permit_exec_success_effect
#print axioms Blanc.Weth10.permit_exec_expired_no_success
#print axioms Blanc.Weth10.permit_exec_invalid_no_success
#print axioms Blanc.Weth10.of_flashLoanSuccessTail
#print axioms Blanc.Weth10.of_flashSettle_allowance
#print axioms Blanc.Weth10.flashBurn_effect
#print axioms Blanc.Weth10.flashLoan_successEffect
#print axioms Blanc.Weth10.weth10_flashLoan_successEffect
#print axioms Blanc.Weth10.weth10_transfer_successEffect
#print axioms Blanc.Weth10.weth10_withdraw_successEffect
#print axioms Blanc.Weth10.weth10_withdrawTo_successEffect
#print axioms Blanc.Weth10.weth10_transferFrom_successEffect
#print axioms Blanc.Weth10.weth10_withdrawFrom_successEffect
#print axioms Blanc.Weth10.of_spendCallerAllowanceThen_effect
#print axioms Blanc.Weth10.transfer_effect_failureOrder
#print axioms Blanc.Weth10.transferFrom_effect_failureOrder
#print axioms Blanc.Weth10.withdrawal_effect_failureOrder
#print axioms Blanc.Weth10.delegatedAllowance_effect_precedence
#print axioms Blanc.Weth10.transferThen_callbackPrefix_effect
#print axioms Blanc.Weth10.callBoolCallback_successEffect
#print axioms Blanc.Weth10.approveAndCall_successEffect
#print axioms Blanc.Weth10.weth10_approveAndCall_successEffect
#print axioms Blanc.Weth10.depositToAndCall_successEffect
#print axioms Blanc.Weth10.weth10_depositToAndCall_successEffect
#print axioms Blanc.Weth10.transferAndCall_successEffect
#print axioms Blanc.Weth10.weth10_transferAndCall_successEffect
#print axioms Blanc.Weth10.erc677_codelessCallback_runCompiledTo
#print axioms Blanc.Weth10.erc677_childRevert_runCompiledTo
#print axioms Blanc.Weth10.erc677_shortReturn_runCompiledTo
#print axioms Blanc.Weth10.lockedErrorGuard_runCompiledTo
#print axioms Blanc.Weth10.codelessCallback_runCompiledTo
#print axioms Blanc.Weth10.callbackBubble_runCompiledTo
#print axioms Blanc.Weth10.callbackShort_runCompiledTo
#print axioms Blanc.Weth10.flashCallback_wrongMagic_runCompiledTo
#print axioms Blanc.Weth10.nonpayable_runCompiledTo
#print axioms Blanc.Weth10.flashFee_wrongToken_runCompiledTo
#print axioms Blanc.Weth10.flashLoan_lockedGuardOrder
#print axioms Blanc.Weth10.permit_expiredBeforeNonceUpdate
#print axioms Blanc.Weth10.transfer_lockedGuardOrder
#print axioms Blanc.Weth10.transferFromCore_lockedGuardOrder
#print axioms Blanc.Weth10.withdraw_lockedGuardOrder
#print axioms Blanc.Weth10.spendCallerAllowanceThen_finitePrecedence
#print axioms Blanc.Weth10.flashSettle_finitePrecedence
#print axioms Blanc.Weth10.flashCallback_errorPrecedence
#print axioms Blanc.Weth10.rollback_revert_of_weth10_runCompiledTo
#print axioms Blanc.Weth10.rollback_empty_of_weth10_runCompiledTo
#print axioms Blanc.Weth10.rollback_errorData_of_weth10_runCompiledTo
#print axioms Blanc.Weth10.rollback_bubbledChild_of_weth10_runCompiledTo
#print axioms Blanc.ProcessMessage.rollback_of_error
#print axioms Blanc.Fmint.rollback_of_callback_failure
#print axioms Blanc.rollback_of_no_success
#print axioms Blanc.rollback_of_no_success_total
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
#print axioms Blanc.ContractSpec.post_of_run_dispatch
#print axioms Blanc.ContractSpec.sound_of_receive_dispatch
#print axioms Blanc.ContractSpec.preserves_of_receive_dispatch
#print axioms Blanc.Weth10.mintCaller_storage
#print axioms Blanc.Weth10.backedSpec_receiveEther_funcSound
#print axioms Blanc.Weth10.backedSpec_deposit_funcSound
#print axioms Blanc.Weth10.backedSpec_name_funcSound
#print axioms Blanc.Weth10.backedSpec_totalSupply_funcSound
#print axioms Blanc.Weth10.backedSpec_permitTypehash_funcSound
#print axioms Blanc.Weth10.backedSpec_decimals_funcSound
#print axioms Blanc.Weth10.backedSpec_domainSeparator_funcSound
#print axioms Blanc.Weth10.backedSpec_maxFlashLoan_funcSound
#print axioms Blanc.Weth10.backedSpec_balanceOf_funcSound
#print axioms Blanc.Weth10.backedSpec_nonces_funcSound
#print axioms Blanc.Weth10.backedSpec_callbackSuccess_funcSound
#print axioms Blanc.Weth10.backedSpec_flashMinted_funcSound
#print axioms Blanc.Weth10.backedSpec_symbol_funcSound
#print axioms Blanc.Weth10.backedSpec_deploymentChainId_funcSound
#print axioms Blanc.Weth10.backedSpec_allowance_funcSound
#print axioms Blanc.Weth10.backedSpec_flashFee_funcSound
#print axioms Blanc.Weth10.backedSpec_approve_funcSound
#print axioms Blanc.Weth10.backedSpec_depositTo_funcSound
#print axioms Blanc.Weth10.backedSpec_withdraw_funcSound
#print axioms Blanc.Weth10.backedSpec_transfer_funcSound
#print axioms Blanc.Weth10.backedSpec_withdrawTo_funcSound
#print axioms Blanc.Weth10.backedSpec_transferFrom_funcSound
#print axioms Blanc.Weth10.backedSpec_withdrawFrom_funcSound
#print axioms Blanc.Weth10.backedSpec_depositToAndCall_funcSound
#print axioms Blanc.Weth10.backedSpec_approveAndCall_funcSound
#print axioms Blanc.Weth10.backedSpec_transferAndCall_funcSound
#print axioms Blanc.Weth10.backedSpec_flashLoan_funcSound
#print axioms Blanc.Weth10.backedSpec_permit_funcSound
#print axioms Blanc.Weth10.weth10Funcs_exactRelFuncSound
#print axioms Blanc.Weth10.flashExactDepth
#print axioms Blanc.Weth10.weth10Funcs_backed_funcSound
#print axioms Blanc.Weth10.backedSpec_sound_of_funcSound_all
#print axioms Blanc.Weth10.backedSpec_preserves_of_funcSound_all
#print axioms Blanc.Weth10.backedSpec_sound
#print axioms Blanc.Weth10.backedSpec_preserves
#print axioms Blanc.Weth10.weth10InitFunc_runCompiled_zero
#print axioms Blanc.Weth10.weth10Init_exec_zero
#print axioms Blanc.Weth10.weth10Init_exec_nonzero
#print axioms Blanc.Weth10.processCreateMessage_weth10_success
#print axioms Blanc.Weth10.freshDeployment_staticCertificate
#print axioms Blanc.Weth10.flashExactSpec_preserves
#print axioms Blanc.Weth10.processTransaction_preserves_stable
#print axioms Blanc.Weth10.stateTransitionWith_preserves_stable
#print axioms Blanc.Weth10.stateTransitionUsing_preserves_stable
#print axioms Blanc.Weth10.stateTransition_preserves_stable
#print axioms Blanc.Weth10.chainUsing_preserves_stable
#print axioms Blanc.Weth10.chain_preserves_stable
#print axioms Blanc.Weth10.addBlockToChainWith_preserves_stable
#print axioms Blanc.Weth10.addBlockToChainUsing_preserves_stable
#print axioms Blanc.Weth10.addBlockToChain_preserves_stable
#print axioms Blanc.Weth10.Stable.solvent
#print axioms Blanc.Weth10.chain_reachable_backed_and_flash_zero
#print axioms Blanc.Weth10.processCreateMessage_establishes_stable
#print axioms Blanc.Xinst.step_call_nonzero_insufficient
#print axioms Blanc.Xinst.step_call_nonzero_spawn
#print axioms Blanc.Ninst.runCompiled_call_nonzero_codeFree
#print axioms Blanc.Weth10.redemptionRuntimeCeiling_eq
#print axioms Blanc.Weth10.Stable.bookedBalanceNat_le_contractEth
#print axioms Blanc.Weth10.withdrawTo_exec
#print axioms Blanc.Weth10.withdraw_exec
#print axioms Blanc.Weth10.processMessageCall_eq_of_exec
#print axioms Blanc.Weth10.Stable.messageRedemption_enabled_of_le
#print axioms Blanc.Weth10.Stable.selfRedemption_enabled_of_le
#print axioms Blanc.Weth10.AdmissibleRedemptionTx.processTransaction_eq_of_message
#print axioms Blanc.Weth10.Stable.transactionRedemption_enabled_of_le
#print axioms Blanc.Weth10.outerOkWithFailedReceipt_not_redemptionEnabled
