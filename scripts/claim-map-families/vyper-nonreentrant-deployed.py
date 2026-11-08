"""The vyper-nonreentrant-deployed family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `vyper-nonreentrant-deployed` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = ['5.5 Vyper V+', '5.6 Vyper V−']
PARTS = ['Artifacts',
 'Trust base',
 'Summary matrix',
 'Disclosures and limits',
 'Named premises and definitions',
 'Uses of the shared API',
 'See also']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = ['Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion',
 'Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_witness_covered',
 'Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_witness2_covered',
 'Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top.vminus_witness_covered',
 'Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_process',
 'Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.vminus_attack',
 'Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.vplus_exit']

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = ['not historical inclusion', 'synthetic', 'fixed signed transaction', 'not a kernel fact']

# Glossary rows the file's "Named premises" table must keep at least.
GLOSSARY_ROWS = 1

# The artifacts the file's table states: address -> (label, lifted input file or None for a
# proxy, certificate ids whose provenance records the creation, implementation address for a proxy).
ARTIFACTS = {'0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9': ('V+ implementation',
                                                'vyper-847e-runtime.hex',
                                                ['vyper-847e'],
                                                None),
 '0x21e27a5e5513d6e65c4f830167390997aa84843a': ('V+ proxy',
                                                None,
                                                [],
                                                '0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9'),
 '0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e': ('V- implementation',
                                                'vyper-6326-runtime.hex',
                                                ['vyper-6326'],
                                                None),
 '0x9848482da3ee3076165ce6497eda906e66bb85c5': ('V- proxy',
                                                None,
                                                [],
                                                '0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e')}

# Lines of the file that cite another family and cannot move without rewording (substrings).
MIXED_CITATIONS = ['| Signature recovery |']
