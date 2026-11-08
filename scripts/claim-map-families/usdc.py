"""The usdc family's part of scripts/check-deployed-claim-map.py.

Loaded by the checker while `usdc` is live; it leaves with the family's release
(scripts/release.py) and comes back on restore."""

# Its Section 5 subsections, then its parts of the shared sections, in this order.
SECTIONS = ['5.10 USDC']
PARTS = ['Artifacts',
 'Disclosures and limits',
 'Named premises and definitions',
 'Checking this document',
 'Uses of the shared API']

# The headline results the file exists to carry.  A row deleted from the document fails here.
REQUIRED_HEADLINES = ['Blanc.Lift.Token.BookLaws',
 'Blanc.Lift.Token.Core',
 'Blanc.Lift.Token.SelfCaller',
 'Blanc.Lift.Token.TransferLive',
 'Blanc.Lift.checkNode_call_at_delegatecall',
 'Blanc.Lift.Usdc.proxy_forwards',
 'Blanc.Lift.Usdc.proxy_forwards_control',
 'Blanc.Lift.Usdc.impl_children',
 'Blanc.Lift.Usdc.lib_children',
 'Blanc.Lift.Usdc.usdcBook_lawsS',
 'Blanc.Lift.Usdc.usdc_history_replayAt',
 'Blanc.Lift.Usdc.usdc_history_slots',
 'Blanc.Lift.Usdc.usdc_history_end',
 'Blanc.Composition.UsdcToken.usdcCore',
 'Blanc.Composition.UniswapV2PairUsdcWeth9.PairUsdcAllowQuiet']

# Load-bearing non-claims of the file (normalized substrings).
NONCLAIM_PHRASES = ['synthetic',
 'governance premise',
 'never-signer premise',
 'excluded positions',
 'liveness premises',
 'key universe',
 'the closed single-block usdc instance']

# Glossary rows the file's "Named premises" table must keep at least.
GLOSSARY_ROWS = 4

# The artifacts the file's table states: address -> (label, lifted input file or None for a
# proxy, certificate ids whose provenance records the creation, implementation address for a proxy).
ARTIFACTS = {'0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48': ('USDC FiatTokenProxy',
                                                'usdc-proxy-runtime.hex',
                                                ['usdc-proxy'],
                                                None),
 '0x43506849D7C04F9138D1A2050bbF3A0c054402dd': ('USDC FiatTokenV2_2 implementation',
                                                'usdc-impl-runtime.hex',
                                                ['usdc-impl'],
                                                None),
 '0x800C32EaA2a6c93cF4CB51794450ED77fBfbB172': ('USDC SignatureChecker library',
                                                'usdc-lib-runtime.hex',
                                                ['usdc-lib'],
                                                None)}

# Lines of the file that cite another family and cannot move without rewording (substrings).
MIXED_CITATIONS = []

# The three USDC runtimes, like the Pair's, are code reads at one finalized block; the
# implementation is the address the proxy's implementation slot holds there, and the library is
# linked into the implementation by PUSH20.
USDC_MARKER = "**The USDC rows.**"
USDC_INPUTS = {
    "usdc-proxy": "usdc-proxy-runtime.hex",
    "usdc-impl": "usdc-impl-runtime.hex",
    "usdc-lib": "usdc-lib-runtime.hex",
}
USDC_IMPLEMENTATION = "0x43506849D7C04F9138D1A2050bbF3A0c054402dd"
USDC_LIBRARY = "0x800C32EaA2a6c93cF4CB51794450ED77fBfbB172"


def check(api, auth, body: str, errors: list[str]) -> None:
    """The USDC rows' code-read record, implementation slot and library links."""

    re, to_int, keccak = api.re, api.to_int, api.keccak
    at = body.find(USDC_MARKER)
    if at < 0:
        errors.append("USDC: the USDC rows' record is not stated")
        return
    end = body.find("\n\n", at)
    flat = " ".join(body[at:end if end >= 0 else len(body)].split())
    read = re.search(r"finalized block (\d[\d,]*) \(block hash (0x[0-9a-fA-F]{64})\)", flat)
    if read is None:
        errors.append("USDC: the code-read block and block hash are not stated")
    for cid, filename in USDC_INPUTS.items():
        if f"`scripts/lift/inputs/{filename}`" not in flat:
            errors.append(f"USDC: the lifted input {filename} is not named")
        if read is None:
            continue
        provenance = auth.provenance([cid]).lower()
        if not re.search(r"\bblock\s+" + str(to_int(read.group(1))) + r"\b", provenance):
            errors.append(f"USDC: code-read block {read.group(1)} is not in the {cid} certificate provenance")
        if read.group(2).lower() not in provenance:
            errors.append(f"USDC: the code-read block hash is not in the {cid} certificate provenance")
    slot = re.search(r"implementation slot (0x[0-9a-fA-F]{64})", flat)
    impl_provenance = auth.provenance(["usdc-impl"]).lower()
    if slot is None:
        errors.append("USDC: the proxy's implementation slot is not stated")
    elif slot.group(1).lower() not in impl_provenance or USDC_IMPLEMENTATION[2:].lower() not in impl_provenance:
        errors.append("USDC: the implementation slot and its value are not in the usdc-impl certificate provenance")
    elif "0x" + keccak.keccak256(b"org.zeppelinos.proxy.implementation").hex() != slot.group(1).lower():
        errors.append("USDC: the stated implementation slot is not keccak256(\"org.zeppelinos.proxy.implementation\")")
    sites = re.search(r"PUSH20 sites \(bytes (\d[\d,]*) and (\d[\d,]*)\)", flat)
    runtime = auth.runtime.get(USDC_INPUTS["usdc-impl"], b"")
    if sites is None:
        errors.append("USDC: the library's PUSH20 sites in the implementation are not stated")
    elif not runtime:
        errors.append("USDC: the implementation runtime input is missing")
    else:
        library = bytes.fromhex(USDC_LIBRARY[2:])
        for site in (to_int(sites.group(1)), to_int(sites.group(2))):
            if runtime[site:site + 21] != b"\x73" + library:
                errors.append(f"USDC: byte {site} of the implementation runtime is not PUSH20 of the library address")


def falsifiers(api) -> list:
    """``(label, expected diagnostic, mutate)``; each must be rejected while the family is live."""

    replace_in, map_all = api.replace_in, api.map_all
    drop_headline, remove_all = api.drop_headline, api.remove_all
    return [
        ("wrong USDC code-read block", "USDC: code-read block",
         lambda a, b: (a, replace_in(b, "finalized block 26,213,219", "finalized block 26,213,220"))),
        ("wrong USDC library site", "is not PUSH20 of the library address",
         lambda a, b: (a, replace_in(b, "PUSH20 sites (bytes 18,390 and 20,105)", "PUSH20 sites (bytes 18,391 and 20,105)"))),
        ("wrong USDC implementation slot", "implementation slot",
         lambda a, b: (a, replace_in(b, "0x7050c9e0f4ca769c", "0x7050c9e0f4ca769d"))),
        ("deleted USDC headline", "required headline",
         lambda a, b: (a, map_all(b, lambda t: drop_headline(t, "Blanc.Lift.Usdc.usdc_history_end")))),
        ("dropped USDC disclosure", "load-bearing disclosure vanished",
         lambda a, b: (a, map_all(b, lambda t: remove_all(t, "never-signer premise")))),
    ]
