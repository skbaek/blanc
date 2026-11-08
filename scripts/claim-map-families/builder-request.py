"""The builder-request family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `builder-request` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = []
PARTS = ['Uses of the shared API']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = []

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = []

# Glossary rows the file's "Named premises" table must keep at least.
GLOSSARY_ROWS = 0

# The artifacts the file's table states: address -> (label, lifted input file or None for a
# proxy, certificate ids whose provenance records the creation, implementation address for a proxy).
ARTIFACTS = {}

# Lines of the file that cite another family and cannot move without rewording (substrings).
MIXED_CITATIONS = []
