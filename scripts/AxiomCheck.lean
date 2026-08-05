import Blanc.Solvent
import Blanc.Conserved
import Blanc.FlashSpec
import Blanc.WethCode
import Blanc.FmintCode
import Blanc.Compiled

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
