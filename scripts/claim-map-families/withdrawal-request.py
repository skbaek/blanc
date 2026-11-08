"""The withdrawal-request family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `withdrawal-request` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = ['5.7 EIP-7002 withdrawal requests']
PARTS = ['Trust base', 'Summary matrix', 'Disclosures and limits', 'Uses of the shared API', 'See also']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = ['Blanc.Lift.WithdrawalRequest.history_fifo',
 'Blanc.Lift.WithdrawalRequest.history_fifo_mainnet',
 'Blanc.Lift.WithdrawalRequest.block_word_delivery',
 'Blanc.Lift.WithdrawalRequest.wordSystem_excess_wraps',
 'Blanc.Lift.WithdrawalRequest.word_fee_eq_iff_natFeeDomain',
 'Blanc.Lift.WithdrawalRequest.FeeCounterexample.nat_fee_guarantee_refuted',
 'Blanc.Lift.WithdrawalRequest.history_submission_nat_live',
 'Blanc.Lift.WithdrawalRequest.fee_le_spec',
 'Blanc.Lift.WithdrawalRequest.fee_eq_spec_iff',
 'Blanc.Lift.WithdrawalRequest.FeeCounterexample.fee_guarantee_refuted',
 'Blanc.Lift.WithdrawalRequest.system_call_succeeds',
 'Blanc.Lift.WithdrawalRequest.history_system_call_succeeds',
 'Blanc.Lift.WithdrawalRequest.history_submission_live',
 'Blanc.Lift.WithdrawalRequest.history_submission_queued',
 'Blanc.Lift.WithdrawalRequest.history_system_call_succeeds_mainnet',
 'Blanc.Lift.WithdrawalRequest.history_submission_live_mainnet',
 'Blanc.Lift.WithdrawalRequest.history_submission_queued_mainnet',
 'Blanc.Lift.WithdrawalRequest.deploy',
 'Blanc.Lift.WithdrawalRequest.deploy_mainnet',
 'Blanc.Lift.WithdrawalRequest.history_payments',
 'Blanc.Lift.WithdrawalRequest.history_payments_mainnet',
 'Blanc.Lift.WithdrawalRequest.history_delivery',
 'Blanc.Lift.WithdrawalRequest.history_delivery_mainnet',
 'Blanc.Lift.WithdrawalRequest.DrainControl.historyFifo_of_checkpoint_needs_systemEmpty']

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = ['synthetic',
 'at most 2^254 committed submission-payment occurrences',
 'the witness lives only in the model',
 'success is classified, failure is not',
 'not a code-only fact',
 'no claim that the chain produces those later blocks',
 'not a proved minimum',
 'no transaction-level liveness',
 'validator authorization',
 'not a practical attack',
 "not that one fits mainnet's gas limits"]

# Glossary rows the file's "Named premises" table must keep at least.
GLOSSARY_ROWS = 0

# The artifacts the file's table states: address -> (label, lifted input file or None for a
# proxy, certificate ids whose provenance records the creation, implementation address for a proxy).
ARTIFACTS = {}

# Lines of the file that cite another family and cannot move without rewording (substrings).
MIXED_CITATIONS = []
