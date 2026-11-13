"""The consolidation-request family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `consolidation-request` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

import hashlib

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = ['5.12 EIP-7251 consolidation requests']
PARTS = ['Artifacts', 'Summary matrix', 'Disclosures and limits', 'Named premises and definitions',
         'Checking this document', 'See also']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = ['Blanc.Composition.ConsolidationRequestPublic.system_call_succeeds',
 'Blanc.Composition.ConsolidationRequestPublic.system_call_bookkept',
 'Blanc.Composition.ConsolidationRequestPublic.exec_succeeded',
 'Blanc.Composition.ConsolidationRequestPublic.fee_le_spec',
 'Blanc.Composition.ConsolidationRequestPublic.fee_eq_spec_of_le',
 'Blanc.Composition.ConsolidationRequestPublic.fee_lt_spec_2893',
 'Blanc.Composition.ConsolidationRequestPublic.history_fifo',
 'Blanc.Composition.ConsolidationRequestPublic.history_fifo_mainnet',
 'Blanc.Composition.ConsolidationRequestPublic.submission_queued',
 'Blanc.Composition.ConsolidationRequestPublic.submission_live',
 'Blanc.Corpus.Proofs.Consolidation.c_s2',
 'Blanc.Corpus.Proofs.Consolidation.c_s6',
 'Blanc.Corpus.Proofs.Consolidation.c_s8',
 'Blanc.Composition.ConsolidationRequestJoint.c_s9_authorization',
 'Blanc.Composition.ConsolidationRequestJoint.c_s9_fate',
 'Blanc.Composition.ConsolidationRequestBalance.c_s9_balance',
 'Blanc.Lift.SystemExecution.ConsolidationRequest.Amsterdam.system_call_ok']

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = ['success is classified, failure is not',
 'its output field is stated only when head ≤ tail',
 'at most 2^253 committed submissions',
 'not a proved minimum',
 'no transaction-level liveness',
 'validator authorization',
 'not a practical attack',
 'no such history is proved',
 'the mainnet root is an observation, not a deployment',
 'lean does not authenticate them',
 'no closed counterexample',
 'amsterdam is not covered']

# Glossary rows the file's "Named premises" table must keep at least.
GLOSSARY_ROWS = 10

# The EIP-7251 bytes are a canonical system contract, not a lifted input; `check` holds its row.
ARTIFACTS = {}

# Lines of the file that cite another family and cannot move without rewording (substrings).
MIXED_CITATIONS = []

ADDRESS = "0x0000BBdDc7CE488642fb579F8B00f3a590007251"
DEFINITION = "consolidationRequestCode"


def check(checker, auth, body, errors):
    """The Artifacts row: size and SHA-256 equal the bytes written in Blanc/SystemContracts.lean."""
    rows = [r for r in checker.table_rows(checker.section(body, "Artifacts")) if len(r) == 5]
    hits = [r for r in rows if r[1] == ADDRESS]
    if len(hits) != 1:
        errors.append(f"consolidation-request: expected one Artifacts row at {ADDRESS}, found {len(hits)}")
        return
    _runtime, _address, size, digest, definition = hits[0]
    code = auth.system_code(DEFINITION)
    if code is None:
        errors.append(f"{checker.SYSTEM_CONTRACTS} no longer defines {DEFINITION}")
        return
    if checker.to_int(size) != len(code):
        errors.append(f"consolidation-request: bytes {size} differ from the Lean bytes ({len(code)})")
    if digest != hashlib.sha256(code).hexdigest():
        errors.append("consolidation-request: SHA-256 differs from the Lean bytes")
    if f"`Blanc.{DEFINITION}`" not in definition:
        errors.append(f"consolidation-request: Artifacts row does not cite {DEFINITION}")


def falsifiers(checker):
    """A wrong digest in the Artifacts row must be rejected."""
    def wrong_digest(a, b):
        digest = "99e3d84dc4a4440c78a64619a2b451c08654cc83b44441585cb6db159478d661"
        return a, checker.replace_in(b, digest, "0" * 64)
    return [("consolidation-request artifact digest", "SHA-256 differs from the Lean bytes", wrong_digest)]
