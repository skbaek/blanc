"""The curve-3crv family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `curve-3crv` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = ['5.3 Curve 3Crv']
PARTS = ['Artifacts',
 'Summary matrix',
 'Disclosures and limits',
 'Named premises and definitions',
 'Uses of the shared API',
 'See also']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = ['Blanc.Lift.Curve3Crv.c3crv_history_committed_derived',
 'Blanc.Lift.Curve3Crv.c3crv_frame_refines',
 'Blanc.Lift.Curve3Crv.Creation.curve_deploy_covered',
 'Blanc.Lift.Curve3Crv.c3crv_conserved',
 'Blanc.Lift.Curve3Crv.c3crv_policy']

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = ['amsterdam is not covered',
 'modeled deployment',
 'not historical inclusion',
 'not chained',
 'no closed cost formula',
 'no transaction-level liveness']

# Glossary rows the file's "Named premises" table must keep at least.
GLOSSARY_ROWS = 6

# The artifacts the file's table states: address -> (label, lifted input file or None for a
# proxy, certificate ids whose provenance records the creation, implementation address for a proxy).
ARTIFACTS = {'0x6c3F90f043a72FA612cbac8115EE7e52BDe6E490': ('Curve 3Crv LP token',
                                                'curve-3crv-runtime.hex',
                                                ['curve-3crv', 'curve-3crv-creation'],
                                                None)}

# Lines of the file that cite another family and cannot move without rewording (substrings).
MIXED_CITATIONS = []
