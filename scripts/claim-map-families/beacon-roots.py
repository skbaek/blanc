"""The beacon-roots family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `beacon-roots` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

import hashlib

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = ['5.14 EIP-4788 beacon block root']
PARTS = ['Artifacts', 'Summary matrix', 'Disclosures and limits', 'Named premises and definitions',
         'Checking this document']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = [
    'Blanc.Corpus.Proofs.R.r_s1',
    'Blanc.Corpus.Proofs.R.r_s1_control',
    'Blanc.Corpus.Proofs.BeaconRoots.r_s2',
    'Blanc.Corpus.Proofs.BeaconRoots.r_s2_control',
    'Blanc.Corpus.Proofs.RingHistory.R.r_s3',
    'Blanc.Composition.Corpus.Proofs.RingHistoryControls.r_s3_control',
    'Blanc.Corpus.Proofs.RingRoots.r_s4',
    'Blanc.Corpus.Proofs.R.r_s6',
    'Blanc.Corpus.Proofs.BeaconRoots.r_s7',
    'Blanc.Composition.BeaconRootsRetention.r_s8_time',
    'Blanc.Composition.Corpus.Proofs.RingJointControls.r_s8_time_control',
    'Blanc.Composition.Corpus.Proofs.RingJointRetention.r_s8_slot',
    'Blanc.Composition.BeaconRootsSlotControl.slot_grid_control',
    'Blanc.Composition.Corpus.Proofs.RingJointRetention.r_s9',
    'Blanc.Composition.Corpus.Proofs.RingJointControls.r_s9_control',
    'Blanc.Corpus.Proofs.R.r_s10',
]

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = [
    'success is classified, failure is not',
    'accepts and retains any value',
    'the mainnet root is an observation, not a deployment',
    'lean does not authenticate them',
    'no transaction-level liveness',
    'arithmetic mechanism control',
    'sentinel collision',
    'chain-relative: no canonicality',
    'amsterdam is covered only for the protocol system call',
]

# Glossary rows the file's "Named premises" table must keep at least.
GLOSSARY_ROWS = 8

# Canonical system contract bytes; `check` holds the Artifacts row against Blanc/SystemContracts.lean.
ARTIFACTS = {}

# Lines of the file that cite another family and cannot move without rewording (substrings).
MIXED_CITATIONS = []

# Identifier-shaped spans of the file that name something other than a Blanc declaration.
NON_LEAN_IDENTIFIERS = [
    'SYSTEM_ADDRESS', 'SLOT_DURATION_MS', 'STORAGE_SET',
    'parent_root', 'state_root', 'latest_block_header', 'parentBeaconBlockRoot',
    'beaconRootsCall', 'mainnetChainConfig', 'process_slot',
]

ADDRESS = "0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02"
DEFINITION = "beaconRootsCode"


def check(checker, auth, body, errors):
    """The Artifacts row: size and SHA-256 equal the bytes written in Blanc/SystemContracts.lean."""
    rows = [r for r in checker.table_rows(checker.section(body, "Artifacts")) if len(r) == 5]
    hits = [r for r in rows if r[1] == ADDRESS]
    if len(hits) != 1:
        errors.append(f"beacon-roots: expected one Artifacts row at {ADDRESS}, found {len(hits)}")
        return
    _runtime, _address, size, digest, definition = hits[0]
    code = auth.system_code(DEFINITION)
    if code is None:
        errors.append(f"{checker.SYSTEM_CONTRACTS} no longer defines {DEFINITION}")
        return
    if checker.to_int(size) != len(code):
        errors.append(f"beacon-roots: bytes {size} differ from the Lean bytes ({len(code)})")
    if digest != hashlib.sha256(code).hexdigest():
        errors.append("beacon-roots: SHA-256 differs from the Lean bytes")
    if f"`Blanc.{DEFINITION}`" not in definition:
        errors.append(f"beacon-roots: Artifacts row does not cite {DEFINITION}")


def falsifiers(checker):
    """A wrong digest in the family file's own Artifacts row must be rejected."""
    digest = "cb7bd3e115730f7d57c15cd892880ed517ff4421bf43dfc7591198868fffe31d"

    def wrong_digest(a, b):
        text = b.get("beacon-roots") or ""
        if digest not in text:
            raise KeyError(digest)
        return a, {**b, "beacon-roots": text.replace(digest, "0" * 64, 1)}

    return [("beacon-roots artifact digest", "beacon-roots: SHA-256 differs from the Lean bytes", wrong_digest)]
