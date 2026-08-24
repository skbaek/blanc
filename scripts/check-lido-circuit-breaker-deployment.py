#!/usr/bin/env python3
"""Fail-closed source assurance for the Lido CircuitBreaker deployment root.

This is deliberately a source gate, not a replay runner.  It pins the complete
normalised public deployment declarations and independently checks the facts
which make a direct, successful, prepared-state deployment meaningful.  The
separate finite replay channel must never be credited as a Lean root.
"""
from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path

DEFAULT_ROOT = Path(__file__).resolve().parent.parent
VERDICT = "S9 Lido CircuitBreaker deployment-root assurance"


class Failure(Exception):
    pass


def fail(message: str) -> None:
    raise Failure(message)


# This exact family is intentionally small: inputs, prepared context, direct
# message execution, transaction, suffix, and root.  WETH is architectural
# evidence only and is forbidden from this family.
SOURCES = {
    "compiled": "Blanc/DeploymentCompiled.lean",
    "base": "Blanc/DeploymentMessage.lean",
    "layout": "Blanc/LidoCircuitBreakerDeploymentLayout.lean",
    "trace": "Blanc/LidoCircuitBreakerDeploymentTrace.lean",
    "input": "Blanc/LidoCircuitBreakerDeploymentInput.lean",
    "message": "Blanc/LidoCircuitBreakerDeploymentMessage.lean",
    "transaction": "Blanc/LidoCircuitBreakerDeploymentTransaction.lean",
    "block": "Blanc/LidoCircuitBreakerDeploymentBlock.lean",
    "root": "Blanc/LidoCircuitBreakerDeploymentRoot.lean",
}

AXIOM_CHECK = "scripts/AxiomCheck.lean"
AXIOM_GATE = "scripts/check.sh"
PUBLIC_THEOREM_COUNT = 161
PUBLIC_THEOREM_INVENTORY_SHA256 = (
    "146d7254d9755b7ba1f29eefa37a3d4fa9c56e8953fd65ed2eabd0ebb28f2bee"
)
AXIOM_EXPECTATIONS_SHA256 = (
    "4a86d308306234b175517b729370638303514baf9d6b870d3e47de8694720215"
)

# Kept as digests rather than copies to make this executable readable.  The
# digest is over comment-free, whitespace-normalised *complete declarations*,
# including the proof term; a changed body cannot silently pass.  The separate
# channels below prevent an author from merely updating a digest after a
# weakening.
PINS = {
    # Filled from the committed direct-root interface by this gate's author.
    # Values are patched in with the parser below; an empty value fails closed.
    "OfficialConstructorExecutionTrace": "65a6a11a222041800858428fceebe46d319e704bc27aec768d504e270d48b889",
    "OfficialCreateMessageResult": "846e6ca7c073eb4575bf827e1e68c4d671a3e35e13624b81c0766376f3263612",
    "OfficialConstructorMessageResult": "ac72fa7080ad768826622ca3a4d17f6a859c7be69d8b52426fffd0304087b5ab",
    "CanonicalDeploymentBase": "7a3fcdd9ac9e90418d31c9425eef3e21fdb7d41798ef54f219652bcf0914787a",
    "CanonicalOfficialDeploymentBlock": "d4fe65bff5cbe0eab8bc78a110f75bc0f97bcf0d34231bf5a8f11e04b7cd4205",
    "PreparedDeploymentContext": "af9495545537f026f4f63b4d206f40f4c8a069aaea9f069b1451a72a44d0bed3",
    "OfficialDeploymentTransactionResult": "1f9e1762be26367e57e8efd538fc7252095867a40f1963e06d18310d9749710a",
    "OfficialDeploymentSuffixResult": "3c359fd060bd6c981d177062d40bc52e4e7ce5d9d69220e31966b5a02e0f4977",
    "DeploymentRoot": "1073eeb97564b9b987576c18ff1d48ce6f4aaae10412caf36cf95f7a16409593",
    "canonicalDeploymentStep_establishes_root": "f9ad429746fde433fd5e942b92e492f8182e494d0a263bd2423585be6f2c705b",
    "DeploymentRoot.reflReach": "db5340c05d64eaacd1a250c81e4c87d285672e8ad7a348b5c87f59db04d4e8e7",
    "DeploymentRoot.reachable_registryStable": "6b0e847c71a438cfc66fb641b33c923c87007d60607efffc461030e6f00ba4c4",
    "DeploymentRoot.reachable_code": "81a6786d083b03c2385428f6ca09a79e935ac1ce73242349fe4ecbf136fabbbd",
    "DeploymentRoot.reachable_installedCode": "d7f912846c7b60d6fce05d7ca07e381b861cb00471c5febe7495fb29964db4b8",
    "DeploymentRoot.reachable_witness": "2c7ac7c5246432ba6a0f1b08270f3937641417d5f6c0ca29c2d72774770f0ac1",
    "DeploymentRoot.reachable_membership": "f210b1b06d95c79a9f88e3313ae33a158e2d7fe52b21a423ed9a46ecba05b983",
    "DeploymentRoot.reachable_countConservation": "fa121124d70ca1d41dad767e50c8943c6f1027952e0a04d61ea18bdc4221711e",
}

# Every channel is exact source vocabulary with independent security meaning.
# They are intentionally redundant with PINS: this makes a careless re-pin a
# detectable review event, not a way to bless result smuggling or a weak root.
CHANNELS = {
    "OfficialConstructorExecutionTrace": (
        "target_eq", "fullInput", "prefixCompile", "validationCheckpoints",
        "errorArmLayout", "effectCheckpoints", "Jaune.exec",
        "officialConstructorRequiredGas",
    ),
    "OfficialCreateMessageResult": (
        "processCreateMessage", "OfficialCreateMessageExecution", "installed",
        "pauseDuration", "heartbeatInterval", "emptyRegistry", "coherent",
        "officialConstructorLogs", "returnData", "gasLeft", "error",
        "refundCounter", "accountsToDelete", "RegistryStable",
    ),
    "OfficialConstructorMessageResult": (
        "msg.target = none", "processMessageCall", "OfficialCreateMessageResult",
        "officialMessageOutputOf", "installed", "pauseDuration",
        "heartbeatInterval", "emptyRegistry", "officialConstructorLogs",
        "returnData", "gasLeft", "error", "accountsToDelete", "RegistryStable",
    ),
    "CanonicalDeploymentBase": (
        "validContext", "ValidContext", "chainId_eq", "SumNof", "computeContractAddress",
        "target_noCodeOrNonce", "target_noStorage", "beaconCode", "historyCode",
        "withdrawalRequestCode", "consolidationRequestCode",
    ),
    "CanonicalOfficialDeploymentBlock": (
        "txs_eq", "decode_eq", "ommers_eq", "withdrawals_eq", "type_eq", ".two",
        "none []", "value_eq", "officialFullCreateInput", "nonce_eq",
        "recoveredSender", "validated", "checked", "upfront_funded",
        "gas_bound", "block_gas_room", "target_eq",
    ),
    "PreparedDeploymentContext": (
        "DeploymentSystemPrefix", "beginTransaction", "incrNonce", "subBal",
        "prepareMessage", "msg_target_eq", "msg_code_eq", "officialFullCreateInput",
        "noCodeOrNonce", "noStorage", "originalState_eq", "pauseCold",
        "heartbeatCold", "pauseOriginal", "heartbeatOriginal", "msg_static_eq",
    ),
    "OfficialDeploymentTransactionResult": (
        "processTransaction", "OfficialConstructorMessageResult", "installed",
        "pauseDuration", "heartbeatInterval", "emptyRegistry", "RegistryStable",
        "blockLogs :", "officialConstructorLogs", "requests", "depositRequests",
        "receiptKeys", "receiptEntry", "receiptLogs", "receiptSucceeded :",
        "withdrawalRequestCode", "consolidationRequestCode",
    ),
    "OfficialDeploymentSuffixResult": (
        "withdrawalRun", "withdrawalReturnData", "consolidationRun",
        "consolidationReturnData", "processGeneralPurposeRequests", "RegistryStable",
    ),
    "DeploymentRoot": (
        "CanonicalDeploymentBase", "CanonicalOfficialDeploymentBlock",
        "OfficialDeploymentTransactionResult", "OfficialDeploymentSuffixResult",
        "stateTransitionUsing", "ChainConfig.pragueOnly", "applyBody",
        "post = deployed.state", "target_ne_zero", "target_not_precompile",
        "installed", "pauseDuration", "heartbeatInterval", "emptyRegistry",
        "RegistryStable", "deployed_validContext", "deployed_chainId",
    ),
    "canonicalDeploymentStep_establishes_root": (
        "prepareCanonicalDeploymentContext", "canonicalDeploymentTransaction_succeeds",
        "canonicalDeploymentSuffix_succeeds", "canonicalDeploymentApplyBody_succeeds",
        "stateTransitionUsing", "DeploymentRoot",
    ),
    "DeploymentRoot.reflReach": ("ReachUsing", "ChainConfig.pragueOnly", "deployed"),
    "DeploymentRoot.reachable_registryStable": (
        "ReachUsing", "chainUsing_preserves_registryStable", "RegistryStable",
    ),
    "DeploymentRoot.reachable_code": ("ReachUsing", "Prog.compile", "runtime officialParams"),
    "DeploymentRoot.reachable_installedCode": (
        "ReachUsing", "lidoCircuitBreakerCode officialParams",
    ),
    "DeploymentRoot.reachable_witness": ("ReachUsing", "∃ entries", "RegistryWitness"),
    "DeploymentRoot.reachable_membership": (
        "ReachUsing", "canonicalAddress", "assignmentSlot", "indexSlot", "findEntry",
    ),
    "DeploymentRoot.reachable_countConservation": (
        "ReachUsing", "countSlot", "assignmentCount", "entries.length",
    ),
}

DECL_KINDS = r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|example)"
DECL_HEAD = re.compile(
    r"^(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*)"
    r"(?P<kind>" + DECL_KINDS + r")\s+(?P<name>[^\s({\[:]+)")
DECL_BOUNDARY = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:" + DECL_KINDS + r"|namespace|end|section|variable|open|import|attribute|macro|syntax|notation|set_option)\b")


def strip_comments(source: str) -> str:
    """Blank nested Lean comments without touching strings or offsets."""
    out, i, depth = [], 0, 0
    while i < len(source):
        if depth == 0 and source[i] == '"':
            out.append(source[i]); i += 1
            while i < len(source):
                out.append(source[i])
                if source[i] == "\\" and i + 1 < len(source):
                    out.append(source[i + 1]); i += 2; continue
                if source[i] == '"':
                    i += 1; break
                i += 1
            continue
        if source.startswith("/-", i):
            depth += 1; out.append("  "); i += 2; continue
        if depth and source.startswith("-/", i):
            depth -= 1; out.append("  "); i += 2; continue
        if depth:
            out.append("\n" if source[i] == "\n" else " "); i += 1; continue
        if source.startswith("--", i):
            stop = source.find("\n", i)
            stop = len(source) if stop < 0 else stop
            out.append(" " * (stop - i)); i = stop; continue
        out.append(source[i]); i += 1
    if depth:
        fail("unterminated block comment: cannot distinguish code from comment")
    return "".join(out)


def declarations(source: str) -> dict[str, str]:
    """Extract complete namespace-qualified declarations from comment-free text."""
    code = strip_comments(source)
    lines = code.splitlines(keepends=True)
    starts, pos = [], 0
    for line in lines:
        starts.append(pos); pos += len(line)
    namespaces, found = [], []
    for number, raw in enumerate(lines):
        line = raw.rstrip("\n")
        opening = re.match(r"^namespace\s+(\S+)", line)
        if opening:
            namespaces.append(opening.group(1)); continue
        closing = re.match(r"^end\s+(\S+)", line)
        if closing and namespaces and namespaces[-1] == closing.group(1):
            namespaces.pop()
            continue
        head = DECL_HEAD.match(line)
        if head:
            found.append((starts[number], ".".join(namespaces), head.group("name")))
    result = {}
    for offset, namespace, name in found:
        boundary = DECL_BOUNDARY.search(code, offset + 1)
        end = boundary.start() if boundary else len(code)
        # The controlled owners have no duplicate exported names.  Retaining
        # Lean's spelled declaration name (including `DeploymentRoot.foo`) is
        # both less surprising and lets the shared neutral base be pinned.
        key = name
        result[key] = code[offset:end].rstrip()
    return result


def normalise(text: str) -> str:
    # Strings stay tokenised as strings: this does not treat comment-like text
    # in a string as syntax, and whitespace changes outside strings are benign.
    chunks, i = [], 0
    while i < len(text):
        if text[i] != '"':
            j = text.find('"', i)
            j = len(text) if j < 0 else j
            chunks.append(re.sub(r"\s+", " ", text[i:j])); i = j; continue
        j = i + 1
        while j < len(text):
            if text[j] == "\\": j += 2; continue
            if text[j] == '"': j += 1; break
            j += 1
        chunks.append(text[i:j]); i = j
    return "".join(chunks).strip()


def digest(text: str) -> str:
    return hashlib.sha256(normalise(text).encode()).hexdigest()


def source_map(root: Path) -> dict[str, str]:
    result = {}
    for owner, relative in SOURCES.items():
        path = root / relative
        if not path.is_file():
            fail(f"missing required deployment owner: {relative}")
        result[owner] = path.read_text()
    return result


def all_declarations(sources: dict[str, str]) -> dict[str, str]:
    result = {}
    for owner, source in sources.items():
        for name, text in declarations(source).items():
            if name in result:
                fail(f"ambiguous declaration name {name!r} across deployment owners")
            result[name] = text
    return result


def public_theorem_names(sources: dict[str, str]) -> list[str]:
    """Derive every non-private theorem/lemma with its Lean namespace."""
    result: list[str] = []
    for source in sources.values():
        namespaces: list[str] = []
        for line in strip_comments(source).splitlines():
            opening = re.match(r"^namespace\s+(\S+)", line)
            if opening:
                namespaces.append(opening.group(1))
                continue
            closing = re.match(r"^end\s+(\S+)", line)
            if closing and namespaces and namespaces[-1] == closing.group(1):
                namespaces.pop()
                continue
            head = re.match(
                r"^(?P<mods>(?:(?:private|protected|noncomputable)\s+)*)"
                r"(?:theorem|lemma)\s+(?P<name>[^\s({\[:]+)", line,
            )
            if head and "private" not in head.group("mods").split():
                result.append(".".join((*namespaces, head.group("name"))))
    return result


def require_axiom_inventory(root: Path, sources: dict[str, str]) -> None:
    """Tie this source family to its exact repository-wide axiom probes."""
    names = public_theorem_names(sources)
    if len(names) != PUBLIC_THEOREM_COUNT or len(set(names)) != len(names):
        fail(
            "public theorem inventory changed "
            f"(expected {PUBLIC_THEOREM_COUNT} unique names, got "
            f"{len(names)} names/{len(set(names))} unique)"
        )
    inventory = "\n".join(sorted(names)) + "\n"
    if hashlib.sha256(inventory.encode()).hexdigest() != PUBLIC_THEOREM_INVENTORY_SHA256:
        fail("public theorem inventory changed")

    axiom_path, gate_path = root / AXIOM_CHECK, root / AXIOM_GATE
    if not axiom_path.is_file() or not gate_path.is_file():
        fail("deployment axiom inventory or exact-set gate is missing")
    axiom_text, gate_text = axiom_path.read_text(), gate_path.read_text()
    if axiom_text.count("import Blanc.LidoCircuitBreakerDeploymentRoot") != 1:
        fail("axiom inventory must import the final deployment-root owner exactly once")
    printed = re.findall(r"^#print axioms\s+([^\s]+)", axiom_text, re.M)
    for name in names:
        if printed.count(name) != 1:
            fail(f"{name}: expected exactly one public axiom probe")

    standard = re.search(r'^STANDARD="([^"]*)"$', gate_text, re.M)
    marker = 'ROWS="\\\n'
    if standard is None or marker not in gate_text or '"\n# Secondary' not in gate_text:
        fail("cannot parse the repository exact-set axiom gate")
    row_block = gate_text.split(marker, 1)[1].split('"\n# Secondary', 1)[0]
    rows: dict[str, list[str]] = {}
    for row in row_block.splitlines():
        if "|" not in row:
            continue
        name, expected = row.split("|", 1)
        rows.setdefault(name, []).append(
            expected.replace("$STANDARD", standard.group(1))
        )
    expectations: list[str] = []
    for name in names:
        values = rows.get(name, [])
        if len(values) != 1:
            fail(f"{name}: expected exactly one pinned axiom expectation")
        expectations.append(name + "|" + values[0])
    canonical = "\n".join(sorted(expectations)) + "\n"
    if hashlib.sha256(canonical.encode()).hexdigest() != AXIOM_EXPECTATIONS_SHA256:
        fail("deployment public axiom expectations changed")


def require_channels(decls: dict[str, str]) -> None:
    for name, tokens in CHANNELS.items():
        text = decls.get(name)
        if text is None:
            fail(f"missing required public declaration {name}")
        for token in tokens:
            if token not in text:
                fail(f"{name}: missing required semantic fragment {token!r}")


def require_pins(decls: dict[str, str]) -> None:
    for name, expected in PINS.items():
        actual = decls.get(name)
        if actual is None:
            fail(f"missing pinned declaration {name}")
        if not expected:
            fail(f"{name}: deployment pin is not installed")
        observed = digest(actual)
        if observed != expected:
            fail(f"{name}: complete normalised body changed (expected {expected}, got {observed})")


def premise_discipline(decls: dict[str, str]) -> None:
    base, block = decls["CanonicalDeploymentBase"], decls["CanonicalOfficialDeploymentBlock"]
    forbidden_inputs = (
        "PreparedDeploymentContext", "OfficialConstructorExecutionTrace",
        "OfficialCreateMessageResult", "OfficialConstructorMessageResult",
        "OfficialDeploymentTransactionResult", "OfficialDeploymentSuffixResult",
        "RegistryCoherent", "RegistryStable", "receiptsTrie", "receipt",
        "post :", "poststate", "installed", "returnData",
    )
    for label, text in (("CanonicalDeploymentBase", base), ("CanonicalOfficialDeploymentBlock", block)):
        for token in forbidden_inputs:
            if token in text:
                fail(f"{label}: forbidden execution/result smuggling token {token!r}")

    theorem = decls["canonicalDeploymentStep_establishes_root"]
    head = theorem.split(":= by", 1)[0]
    binders = re.findall(r"\((h\w+)\s*:", head)
    if binders != ["hbase", "henv", "hstep"]:
        fail("root theorem: expected only hbase, henv, hstep proof premises; got " + repr(binders))
    if "hstep : stateTransitionUsing (ChainConfig.pragueOnly chainId)" not in head or \
            "base cb.block = .ok deployed" not in head:
        fail("root theorem: hstep is not the configured successful transition")
    forbidden_premises = ("receipt", "OfficialDeploymentTransactionResult", "OfficialConstructorMessageResult",
                          "RegistryStable", "RegistryCoherent", "applyBody")
    for token in forbidden_premises:
        if token in head:
            fail(f"root theorem: separate result/receipt premise {token!r} is forbidden")


def trust_and_scope(sources: dict[str, str]) -> None:
    joined = "\n".join(sources.values())
    code = strip_comments(joined)
    # Local proof trust is forbidden even in a comment: a claimed escape hatch
    # must be visible to review.  `unsafe` is caught as a declaration modifier.
    for token in (
        "sorry", "admit", "axiom", "opaque", "native_decide",
        "implemented_by", "unsafe", "AXIOM_EXCEPTIONS",
    ):
        if re.search(r"\b" + re.escape(token) + r"\b", joined, re.I):
            fail(f"deployment family contains forbidden trust token {token!r}")
    if re.search(r"\b(?:Weth|WETH)\w*\b", code):
        fail("deployment family imports or names WETH; Lido contracts are siblings")
    if re.search(r"(?m)^\s*partial\s+(?:def|theorem|lemma|instance)\b", code):
        fail("deployment family contains a forbidden object-level partial declaration")
    # Scope terms are rejected in code and claims/comments alike.  `create` is
    # not banned: direct top-level creation is required; CREATE2 is not.
    for token in ("factory", "proxy", "CREATE2", "CREATE3", "mainnet", "clone"):
        if re.search(r"\b" + token + r"\b", joined, re.I):
            fail(f"deployment family makes forbidden scope/identity claim {token!r}")


def actual_execution_sites(decls: dict[str, str]) -> None:
    """Cross-boundary checks that cannot be satisfied by isolated field names."""
    requirements = {
        "OfficialConstructorExecutionTrace": ("Jaune.exec", "OfficialConstructorEffectCheckpoints"),
        "OfficialCreateMessageResult": ("processCreateMessage msg = .ok post",),
        "OfficialConstructorMessageResult": ("processMessageCall msg = .ok (post, out)",),
        "OfficialDeploymentTransactionResult": ("processTransaction ctx.txInput .init tx 0 = .ok (post, bout)",),
        "OfficialDeploymentSuffixResult": ("processCheckedSystemTransaction", "processGeneralPurposeRequests"),
        "DeploymentRoot": ("stateTransitionUsing", "applyBody", "Nonempty (OfficialDeploymentSuffixResult"),
    }
    for name, fragments in requirements.items():
        for fragment in fragments:
            if fragment not in decls[name]:
                fail(f"{name}: missing actual execution/body site {fragment!r}")


def run(root: Path) -> None:
    sources = source_map(root)
    decls = all_declarations(sources)
    require_pins(decls)
    require_channels(decls)
    premise_discipline(decls)
    actual_execution_sites(decls)
    trust_and_scope(sources)
    require_axiom_inventory(root, sources)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT,
                        help="repository root (used by source-level falsifiers)")
    parser.add_argument("--print-pins", action="store_true",
                        help="print observed pins; review aid, never a passing check")
    args = parser.parse_args(argv)
    try:
        sources = source_map(args.root)
        decls = all_declarations(sources)
        if args.print_pins:
            for name in PINS:
                if name not in decls:
                    fail(f"missing pinned declaration {name}")
                print(f"{name} {digest(decls[name])}")
            return 0
        run(args.root)
    except (Failure, OSError, UnicodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        print(f"{VERDICT}: FAIL", file=sys.stderr)
        return 1
    print(
        f"{VERDICT}: PASS ({len(PINS)} full pins, "
        f"{sum(map(len, CHANNELS.values()))} semantic fragments, "
        f"{PUBLIC_THEOREM_COUNT} axiom-pinned public theorems)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
