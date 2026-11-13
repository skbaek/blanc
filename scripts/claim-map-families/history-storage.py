"""The history-storage family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `history-storage` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

import hashlib

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = ['5.15 EIP-2935 historical block hashes']
PARTS = ['Artifacts', 'Summary matrix', 'Disclosures and limits', 'Named premises and definitions',
         'Checking this document']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = [
    'Blanc.Corpus.Proofs.H.h_s1',
    'Blanc.Corpus.Proofs.H.h_s1_control',
    'Blanc.Corpus.Proofs.HistoryStorage.h_s2',
    'Blanc.Corpus.Proofs.HistoryStorage.h_s2_control',
    'Blanc.Corpus.Proofs.RingHistory.H.h_s3',
    'Blanc.Composition.Corpus.Proofs.RingHistoryControls.h_s3_control',
    'Blanc.Corpus.Proofs.RingRoots.h_s4',
    'Blanc.Corpus.Proofs.H.h_s6',
    'Blanc.Corpus.Proofs.HistoryStorage.h_s7',
    'Blanc.Composition.Corpus.Proofs.RingJointRetention.h_s8',
    'Blanc.Composition.Corpus.Proofs.RingHistoryControls.h_s8_control',
    'Blanc.Composition.Corpus.Proofs.RingJointRetention.h_s9',
    'Blanc.Composition.Corpus.Proofs.RingJointControls.h_s9_control',
    'Blanc.Composition.Corpus.Proofs.RingJointRetention.h_s9_joint',
    'Blanc.Composition.Corpus.Proofs.RingJointControls.h_s9_joint_control',
    'Blanc.Corpus.Proofs.H.h_s10',
]

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = [
    'success is classified, failure is not',
    'accepts and retains any value',
    'no presence tag',
    'the mainnet root is an observation, not a deployment',
    'lean does not authenticate them',
    'no transaction-level liveness',
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
    'SYSTEM_ADDRESS', 'STORAGE_SET',
    'block_hash', 'parent_hash', 'block_number', 'latest_execution_payload_header',
    'lastHash', 'historyStorageCall', 'blockHashes', 'parentHash', 'validateHeader', 'mainnetChainConfig',
]

ADDRESS = "0x0000F90827F1C53a10cb7A02335B175320002935"
DEFINITION = "historyStorageCode"


def check(checker, auth, body, errors):
    """The Artifacts row: size and SHA-256 equal the bytes written in Blanc/SystemContracts.lean."""
    rows = [r for r in checker.table_rows(checker.section(body, "Artifacts")) if len(r) == 5]
    hits = [r for r in rows if r[1] == ADDRESS]
    if len(hits) != 1:
        errors.append(f"history-storage: expected one Artifacts row at {ADDRESS}, found {len(hits)}")
        return
    _runtime, _address, size, digest, definition = hits[0]
    code = auth.system_code(DEFINITION)
    if code is None:
        errors.append(f"{checker.SYSTEM_CONTRACTS} no longer defines {DEFINITION}")
        return
    if checker.to_int(size) != len(code):
        errors.append(f"history-storage: bytes {size} differ from the Lean bytes ({len(code)})")
    if digest != hashlib.sha256(code).hexdigest():
        errors.append("history-storage: SHA-256 differs from the Lean bytes")
    if f"`Blanc.{DEFINITION}`" not in definition:
        errors.append(f"history-storage: Artifacts row does not cite {DEFINITION}")


def falsifiers(checker):
    """A wrong digest in the family file's own Artifacts row must be rejected."""
    digest = "41cd74981e0201f79ebca054c4e8102a7e6faa28ce015d0048ab2250c1222c67"

    def wrong_digest(a, b):
        text = b.get("history-storage") or ""
        if digest not in text:
            raise KeyError(digest)
        return a, {**b, "history-storage": text.replace(digest, "0" * 64, 1)}

    return [("history-storage artifact digest", "history-storage: SHA-256 differs from the Lean bytes", wrong_digest)]
