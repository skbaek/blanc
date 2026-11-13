"""The builder-request family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `builder-request` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = ['5.13 EIP-8282 builder requests']
PARTS = ['Disclosures and limits', 'Uses of the shared API']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = [
    'Blanc.Lift.BuilderRequest.ValidJointG.registration_authorization',
    'Blanc.Lift.BuilderRequest.ValidJointG.deposit_fate',
    'Blanc.Lift.BuilderRequest.ValidJointG.deposit_value',
    'Blanc.Lift.BuilderRequest.ValidJointG.exit_authorization',
    'Blanc.Lift.BuilderRequest.ValidJointG.exit_authorization_caller',
    'Blanc.Lift.BuilderRequest.ValidJointG.exit_fate',
    'Blanc.Lift.BuilderRequest.ValidJointG.exit_resolution_unique',
    'Blanc.Lift.BuilderRequest.ValidJointG.builder_balance_equation',
    'Blanc.Lift.BuilderRequest.ValidJointG.builder_withdrawal_provenance',
    'Blanc.Lift.BuilderRequest.ValidJointG.payment_debit_at_most_once',
    'Blanc.Lift.BuilderRequest.ValidJointG.withdrawal_ledger',
    'Blanc.Lift.BuilderRequest.ValidJointG.builder_separation',
    'Blanc.Lift.BuilderRequest.ValidJointG.builder_total_run_onboarded',
    'Blanc.Composition.BuilderRequestClassification.b_s2_deposit',
    'Blanc.Composition.BuilderRequestClassification.b_s2_exit',
    'Blanc.Composition.Corpus.Proofs.BuilderCheckpoint.b_s4',
    'Blanc.Lift.BuilderRequest.ActualFeeBounds.deposit_every_boundary',
    'Blanc.Lift.BuilderRequest.ActualFeeBounds.exit_every_boundary',
    'Blanc.Lift.BuilderRequest.ActualFeeBounds.deposit_delivery',
    'Blanc.Lift.BuilderRequest.ActualFeeBounds.exit_delivery',
    'Blanc.Lift.BuilderRequest.ValidJointG.deposit_fate_no_pre_anchor_emissions',
    'Blanc.Lift.BuilderRequest.ValidJointG.exit_fate_no_pre_anchor_emissions',
]

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = [
    'no gloas mainnet exists',
    'payout liveness',
    'orphaned payloads have no b2 fate',
    'computational checker soundness does not constitute an external multi-client replay trace',
]

# Glossary rows the file's "Named premises" table must keep at least.
GLOSSARY_ROWS = 0

# The artifacts the file's table states: address -> (label, lifted input file or None for a
# proxy, certificate ids whose provenance records the creation, implementation address for a proxy).
ARTIFACTS = {}

# Lines of the file that cite another family and cannot move without rewording (substrings).
MIXED_CITATIONS = []
