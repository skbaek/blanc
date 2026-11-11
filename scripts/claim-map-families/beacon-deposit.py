"""The beacon-deposit family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `beacon-deposit` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = ['5.2 Beacon deposit']
PARTS = ['Artifacts']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = ['Blanc.Lift.BeaconDeposit.configuredHistory_solInv_sys',
 'Blanc.Lift.BeaconDeposit.Creation.beacon_deploy_covered',
 'Blanc.Lift.BeaconDeposit.beacon_deposits']

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = ['there is no transaction-level beacon liveness']

# Glossary rows the file's "Named premises" table must keep at least.
GLOSSARY_ROWS = 0

# The artifacts the file's table states: address -> (label, lifted input file or None for a
# proxy, certificate ids whose provenance records the creation, implementation address for a proxy).
ARTIFACTS = {
    "0x00000000219ab540356cBB839Cbe05303d7705Fa": ("Beacon deposit", "beacon-deposit-runtime.hex",
                                                   ["beacon-deposit", "beacon-deposit-creation"], None),
}

# Lines of the file that cite another family and cannot move without rewording (substrings).
MIXED_CITATIONS = []

# Identifier-shaped spans of the file that name something other than a Blanc declaration.
NON_LEAN_IDENTIFIERS = ["get_deposit_count", "get_deposit_root"]
