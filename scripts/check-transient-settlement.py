#!/usr/bin/env python3
"""Fail-closed ownership, evaluator, deletion, and mutant gate for F3."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parent.parent
MANIFEST_PATH = ROOT / "scripts/transient-settlement-owner-manifest.json"
FIXTURE = ROOT / "scripts/TransientSettlementRegression.lean"
EXPECTED = "[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]"

DECL_RE = re.compile(
    r"(?m)^\s*(?:@\[[^]]+\]\s*)*"
    r"((?:(?:private|protected|noncomputable|unsafe)\s+)*)"
    r"(theorem|lemma|structure|def|inductive|abbrev|opaque|axiom|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.?!]*(?:\.[A-Za-z_][A-Za-z0-9_'.?!]*)*)"
)
IMPORT_RE = re.compile(r"(?m)^import\s+([A-Za-z0-9_.]+)\s*$")


MUTANTS = {
    "-- ADDRESS-COORDINATE-MUTANT-CONTROL":
        "private theorem addressCoordinateMutant : (match cellClear with | .ok post => post.getTransVal addressB key == 0 | _ => false) = true := by native_decide\n",
    "-- KEY-COORDINATE-MUTANT-CONTROL":
        "private theorem keyCoordinateMutant : (match cellClear with | .ok post => post.getTransVal addressA otherKey == 0 | _ => false) = true := by native_decide\n",
    "-- OPERAND-ORDER-MUTANT-CONTROL":
        "private theorem operandOrderMutant : (match cellClear with | .ok post => post.getTransVal addressA 0 == key | _ => false) = true := by native_decide\n",
    "-- WHOLE-MAP-CLEAR-MUTANT-CONTROL":
        "private theorem wholeMapClearMutant : (match cellClear with | .ok post => post.getTransVal addressA otherKey == 0 | _ => false) = true := by native_decide\n",
    "-- STATIC-GUARD-MUTANT-CONTROL":
        "private theorem staticGuardMutant : staticTstoreControl = false := by native_decide\n",
    "-- STATIC-PRECEDENCE-MUTANT-CONTROL":
        "private theorem staticPrecedenceMutant : staticUnderstackControl = false := by native_decide\n",
    "-- FIELD-ONLY-DIRECT-CALL-MUTANT-CONTROL":
        "private theorem fieldOnlyMutant : (match Xinst.step dynamicSevm staticCallPre .callcode with | .spawn frame _ => frame.inner.currentTarget != frame.inner.codeAddress.getD 0 | _ => false) = true := by native_decide\n",
    "-- CALLCODE-DIRECT-MUTANT-CONTROL":
        "private theorem callcodeDirectMutant : (match Xinst.step dynamicSevm staticCallPre .callcode with | .spawn frame _ => frame.inner.currentTarget == addressB | _ => false) = true := by native_decide\n",
    "-- DELEGATECALL-DIRECT-MUTANT-CONTROL":
        "private theorem delegatecallDirectMutant : (match Xinst.step dynamicSevm staticDelcallPre .delegatecall with | .spawn frame _ => frame.inner.shouldTransferValue | _ => false) = true := by native_decide\n",
    "-- STATIC-PARENT-MUTANT-CONTROL":
        "private theorem staticParentMutant : staticCallFamilyControls = false := by native_decide\n",
    "-- STATIC-CREATE-MUTANT-CONTROL":
        "private theorem staticCreateMutant : staticCreateControl = false := by native_decide\n",
    "-- DELEGATED-CODE-IDENTITY-MUTANT-CONTROL":
        "private theorem delegatedCodeMutant : (match Xinst.step delegatedSevm delegatedPre .call with | .spawn frame _ => frame.inner.code == delegationCode | _ => false) = true := by native_decide\n",
    "-- CHILD-OUTER-ROLLBACK-MUTANT-CONTROL":
        "private theorem rollbackBoundaryMutant : (let msg := childMessage failedCode; match processMessage msg with | .ok child => child.getStorVal addressB 5 == 3 | _ => false) = true := by native_decide\n",
    "-- RAW-LOG-CLEAR-MUTANT-CONTROL":
        "private theorem rawLogClearMutant : rawRollbackKeepsLogs = false := by native_decide\n",
    "-- CHILD-LOG-APPEND-MUTANT-CONTROL":
        "private theorem childLogAppendMutant : (let msg := childMessage failedCode; match processMessage msg with | .ok child => (match (Resume.call settlementParent 0 0).run (.ok child) with | .ok resumed => resumed.logs.length == settlementParent.logs.length + child.logs.length | _ => false) | _ => false) = true := by native_decide\n",
    "-- FATAL-CAUGHT-MUTANT-CONTROL":
        "private theorem fatalCaughtMutant : fatalResumeControl = false := by native_decide\n",
    "-- TOP-LEVEL-LOG-LEAK-MUTANT-CONTROL":
        "private theorem topLevelLeakMutant : (match processMessageCall (messageWithCode failedCode) with | .ok (_, out) => out.logs.length == 1 | _ => false) = true := by native_decide\n",
    "-- REVERT-DATA-ERASURE-MUTANT-CONTROL":
        "private theorem revertDataMutant : (match processMessageCall (messageWithCode failedCode) with | .ok (_, out) => out.returnData == [] | _ => false) = true := by native_decide\n",
    "-- UNLINKED-RECEIPT-MUTANT-CONTROL":
        "private theorem receiptLinkMutant : (match processTransaction failedTransactionBenv failedInitialBout tx0 0 with | .ok (_, bout) => bout.blockLogs.isEmpty | _ => false) = true := by native_decide\n",
    "-- UNRELATED-TRANSACTIONS-MUTANT-CONTROL":
        "private theorem unrelatedTransactionsMutant : (match processTransaction transactionBenv .init tx1 0 with | .ok _ => true | _ => false) = true := by native_decide\n",
    "-- CROSS-TRANSACTION-INHERITANCE-MUTANT-CONTROL":
        "private theorem inheritedTransientMutant : (match firstTransaction with | .ok (state1, bout1) => match preparedMessageFor (transactionBenv.withState state1) bout1 tx1 1 with | .ok msg2 => match processMessage msg2 with | .ok raw2 => raw2.getTransVal txTarget key == 42 | _ => false | _ => false | _ => false) = true := by native_decide\n",
    "-- PER-FRAME-CLEAR-MUTANT-CONTROL":
        "private theorem perFrameClearMutant : (initDevm foreignMsg).getTransVal addressA key = 0 := by native_decide\n",
}


def fail(message: str) -> None:
    raise SystemExit(f"ERROR — transient-settlement: {message}")


def read(path: pathlib.Path) -> str:
    try:
        return path.read_text()
    except OSError as exc:
        fail(f"cannot read {path.relative_to(ROOT)}: {exc}")


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_header(text: str) -> str:
    return " ".join(text.split())


def without_comments(text: str) -> str:
    """Remove nested Lean comments while preserving line structure."""
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        else:
            ch = text[i]
            out.append(ch if depth == 0 or ch == "\n" else " ")
            i += 1
    if depth:
        fail("unterminated Lean block comment")
    return "".join(out)


def command_text(text: str) -> str:
    """Mask comments and strings without changing offsets or line boundaries.

    This scanner is for command identity only. Frozen signature digests retain
    their historical block-comment-only normalization in without_comments.
    """
    out = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                fail("unterminated Lean block comment")
        elif text[i] == "'" and (char := re.match(r"'(?:\\.|[^'\\\n])'", text[i:])):
            i += len(char.group())
        elif text[i] == '"':
            # Raw strings require delimiter-aware scanning; reject rather than
            # misinterpret an embedded namespace command.
            if i and (text[i - 1] == "#" or
                      (text[i - 1] == "r" and
                       (i < 2 or not text[i - 2].isalnum()))):
                fail("unsupported Lean raw string")
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            if i >= len(text):
                fail("unterminated Lean string")
            i += 1
        else:
            i += 1
            continue
        for j in range(start, i):
            if out[j] != "\n":
                out[j] = " "
    return "".join(out)


NAME = r"[A-Za-z_][A-Za-z0-9_'?!]*(?:\.[A-Za-z_][A-Za-z0-9_'?!]*)*"
SCOPE_RE = re.compile(r"(?m)^[ \t]*(namespace|section|end)\b([^\n]*)$")


def declaration_names(text: str, matches: list[re.Match]) -> dict[int, str]:
    """Resolve declaration identities with a balanced namespace/section stack.

    Only standalone scope commands and ordinary identifiers are supported.
    Unsupported spellings fail closed rather than silently losing ownership.
    """
    scopes: list[tuple[str, str, str]] = []
    namespace = ""
    names: dict[int, str] = {}
    events = [(m.start(), "scope", m) for m in SCOPE_RE.finditer(text)]
    events += [(m.start(), "declaration", m) for m in matches]
    for _, event, match in sorted(events):
        if event == "declaration":
            name = match.group(3)
            if re.fullmatch(NAME, name) is None:
                fail(f"unsupported Lean declaration name {name}")
            if name.startswith("_root_."):
                full_name = name[len("_root_."):]
            else:
                full_name = ".".join(part for part in (namespace, name) if part)
            names[match.start()] = full_name
            continue
        command, argument = match.groups()
        argument = argument.strip()
        if argument and re.fullmatch(NAME, argument) is None:
            fail(f"unsupported Lean scope command: {command} {argument}")
        if command == "end":
            if not scopes:
                fail("unmatched Lean end command")
            _, opened, previous = scopes.pop()
            if argument and argument != opened:
                fail(f"mismatched Lean end {argument}, expected {opened}")
            namespace = previous
        else:
            if command == "namespace" and not argument:
                fail("unnamed Lean namespace")
            scopes.append((command, argument, namespace))
            if command == "namespace":
                if argument.startswith("_root_."):
                    fail("unsupported root-qualified Lean namespace command")
                namespace = ".".join(part for part in (namespace, argument) if part)
    if scopes:
        fail("unclosed Lean namespace or section")
    return names


def declarations(text: str, *, qualified: bool = True) -> dict[str, tuple[str, str]]:
    result: dict[str, tuple[str, str]] = {}
    # The manifest and WETH aggregate predate full-name keys. Keep their
    # source-spelled projection explicit and reject ambiguous projections;
    # corpus ownership/shadow scans use qualified identities instead.
    commands = command_text(text)
    matches = list(DECL_RE.finditer(commands))
    full_names = declaration_names(commands, matches)
    declaration_heads = re.finditer(
        r"(?m)^[ \t]*(?:@\[[^]]+\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
        r"(?:theorem|lemma|structure|def|inductive|abbrev|opaque|axiom|class)\b", commands)
    for head in declaration_heads:
        if not any(m.start() <= head.start() and m.end() > head.end() for m in matches):
            fail("unsupported Lean declaration spelling")
    text = without_comments(text)
    # Keep exact historic header boundaries for the immutable schema-1 hashes.
    header_matches = {m.start(3): m for m in DECL_RE.finditer(text)}
    seen: set[str] = set()
    for i, match in enumerate(matches):
        modifiers, kind, name = match.groups()
        if "private" in modifiers.split():
            continue
        full_name = full_names[match.start()]
        if full_name in seen:
            fail(f"duplicate public declaration {full_name}")
        seen.add(full_name)
        name = full_name if qualified else name
        header_match = header_matches.get(match.start(3))
        if header_match is None:
            fail(f"unsupported declaration header for {full_name}")
        following = header_matches.get(matches[i + 1].start(3)) if i + 1 < len(matches) else None
        end_bound = following.start() if following is not None else len(text)
        chunk = text[header_match.start():end_bound]
        if kind in {"structure", "class", "inductive"}:
            header = normalize_header(chunk)
            if name in result:
                fail(f"ambiguous legacy declaration name {name}")
            result[name] = (kind, header)
            continue
        if kind in {"theorem", "lemma"}:
            stop = re.search(r"(?:\s:=\s+(?:by\b|\n)|\n\s*\|)", chunk)
            if stop is None:
                stop = re.search(r"\s:=\s", chunk)
        elif kind in {"structure", "inductive"}:
            stop = re.search(r"(?:\swhere(?:\s|$)|\n\s*\|)", chunk)
        else:
            stop = re.search(r"(?:\s:=\s|\n\s*\|)", chunk)
        if stop is None:
            fail(f"cannot find header terminator for {name}")
        header = normalize_header(chunk[:stop.start()])
        if name in result:
            fail(f"ambiguous legacy declaration name {name}")
        result[name] = (kind, header)
    return result


def legacy_declarations(text: str) -> dict[str, tuple[str, str]]:
    """Frozen schema-1 source-spelled keys, never for contract shadow scans."""
    return declarations(text, qualified=False)


def parser_controls() -> None:
    """In-memory falsifiers: no Lean process or source mutation is involved."""
    valid = {
        "nested": ("namespace Drip\nnamespace Step\ntheorem accounting_exact : True := by trivial\nend Step\nnamespace Chain\ntheorem accounting_exact : True := by trivial\nend Chain\nend Drip\n",
                   {"Drip.Step.accounting_exact", "Drip.Chain.accounting_exact"}),
        "dotted/reopened/section": ("namespace A.B\nsection S\ntheorem x : True := by trivial\nend S\nend A.B\nnamespace A.B\nsection\ntheorem y : True := by trivial\nend\nend A.B\n",
                                   {"A.B.x", "A.B.y"}),
        "qualified/root/private": ("namespace A\ntheorem B.x : True := by trivial\ntheorem _root_.C.x : True := by trivial\nprivate theorem hidden : True := by trivial\nend A\n",
                                   {"A.B.x", "C.x"}),
        "lexical": ('-- namespace Fake\n/- namespace Outer /- end -/ -/\nnamespace Real -- namespace Fake\nprivate def text := "namespace Bogus\nend\ntheorem spoof : True := by trivial"\ntheorem x : True := by trivial\nend Real\n',
                    {"Real.x"}),
    }
    for label, (text, expected) in valid.items():
        if set(declarations(text)) != expected:
            fail(f"parser positive control failed: {label}")
    invalid = {
        "reopened duplicate": ("namespace A\ntheorem x : True := by trivial\nend A\nnamespace A\ntheorem x : True := by trivial\nend A\n", "duplicate public declaration A.x"),
        "dotted duplicate": ("namespace A\ntheorem B.x : True := by trivial\nnamespace B\ntheorem x : True := by trivial\nend B\nend A\n", "duplicate public declaration A.B.x"),
        "root duplicate": ("namespace A\ntheorem _root_.x : True := by trivial\nend A\ntheorem x : True := by trivial\n", "duplicate public declaration x"),
        "section duplicate": ("namespace A\nsection S\ntheorem x : True := by trivial\nend S\ntheorem x : True := by trivial\nend A\n", "duplicate public declaration A.x"),
        "unclosed": ("namespace A\n", "unclosed Lean"),
        "unmatched": ("end A\n", "unmatched Lean"),
        "mismatched": ("namespace A\nend B\n", "mismatched Lean"),
        "malformed": ("namespace A; namespace B\n", "unsupported Lean scope"),
        "quoted namespace": ("namespace «A»\n", "unsupported Lean scope"),
        "quoted declaration": ("theorem «x» : True := by trivial\n", "unsupported Lean declaration"),
        "raw string": ('private def s := r#"namespace A"#\n', "unsupported Lean raw string"),
        "comment": ("/- unterminated", "unterminated Lean block comment"),
        "string": ('private def s := "unterminated', "unterminated Lean string"),
    }
    for label, (text, reason) in invalid.items():
        try:
            declarations(text)
        except SystemExit as exc:
            if reason not in str(exc):
                fail(f"parser falsifier failed at wrong boundary: {label}: {exc}")
        else:
            fail(f"parser falsifier did not bite: {label}")
    try:
        legacy_declarations(valid["nested"][0])
    except SystemExit as exc:
        if "ambiguous legacy declaration" not in str(exc):
            raise
    else:
        fail("legacy projection silently lost a declaration")
    for spelling in ("cell", "Nested.cell", "_root_.cell"):
        text = f"namespace Contract\ntheorem {spelling} : True := by trivial\nend Contract\n"
        if not any(shadows(name, "Owner.cell") for name in declarations(text)):
            fail(f"namespace shadow falsifier did not bite: {spelling}")
    if shadows("Contract.innocent", "Owner.cell"):
        fail("unrelated declaration incorrectly classified as a shadow")


def load_manifest() -> dict:
    try:
        data = json.loads(read(MANIFEST_PATH))
    except json.JSONDecodeError as exc:
        fail(f"invalid JSON manifest: {exc}")
    expected = {
        "schema", "commonModule", "rootModule", "requiredRootImport",
        "exactCommonImports", "owners", "signatureHashes", "movedDonors",
        "donorSource", "touchedConsumers", "forbiddenTraceFamily",
        "requiredPositiveTheorems", "frozenAssuranceFiles",
        "movedSignatureHashes", "touchedConsumerHashes", "jaunePinFiles",
        "wethPublicHeaderAggregate", "requiredSharedClassification",
    }
    if set(data) != expected or data["schema"] != 1:
        fail("manifest schema/keys are not exact")
    for key in expected - {"schema", "signatureHashes", "frozenAssuranceFiles"}:
        if not data[key]:
            fail(f"manifest field {key} is empty")
    return data


def audit_source(data: dict, common_text: str | None = None) -> None:
    common_path = ROOT / data["commonModule"]
    text = read(common_path) if common_text is None else common_text
    imports = IMPORT_RE.findall(text)
    if imports != data["exactCommonImports"]:
        fail(f"common imports are {imports}, expected {data['exactCommonImports']}")
    if any(name.startswith("Blanc.Weth") for name in imports):
        fail("common module imports a contract")
    if re.search(r"(?m)^\s*(?:export|alias)\b", without_comments(text)):
        fail("common module contains an export or alias command")
    root_imports = IMPORT_RE.findall(read(ROOT / data["rootModule"]))
    if root_imports.count(data["requiredRootImport"]) != 1:
        fail("root import is absent or duplicated")
    actual = legacy_declarations(text)
    full_owned = {name: kind for name, (kind, _) in declarations(text).items()}
    if full_owned != {f"Blanc.{name}": kind for name, kind in data["owners"]}:
        fail("public owner set mismatch: namespace-qualified identities drifted")
    expected = {name: kind for name, kind in data["owners"]}
    actual_owned = {name: kind for name, (kind, _) in actual.items()}
    if actual_owned != expected:
        fail(f"public owner set mismatch: actual={actual_owned}, expected={expected}")
    hashes = data["signatureHashes"]
    if set(hashes) != set(expected):
        fail("signature hash keys do not exactly match owners")
    for name, (_, header) in actual.items():
        got = hashlib.sha256(header.encode()).hexdigest()
        if got != hashes[name]:
            fail(f"signature drift for {name}: {got}")
    for forbidden in data["forbiddenTraceFamily"]:
        if re.search(rf"\b{re.escape(forbidden)}\b", text):
            fail(f"forbidden WETH trace-family name appears: {forbidden}")


def shadows(candidate: str, protected: str) -> bool:
    """Retain the contract-wide short-name ban across every namespace."""
    return candidate.rsplit(".", 1)[-1] == protected.rsplit(".", 1)[-1]


def audit_moves(data: dict) -> None:
    donor_text = read(ROOT / data["donorSource"])
    layering = read(ROOT / "scripts/check-layering.py")
    contract_match = re.search(r"(?s)^CONTRACTS\s*=\s*\{(.*?)\n\}\n", layering, re.M)
    if contract_match is None:
        fail("cannot parse contract modules from the layering classification")
    contract_modules = [ROOT / "Blanc" / f"{name}.lean" for name in
        re.findall(r'"([A-Z][A-Za-z0-9_]*)"', contract_match.group(1))]
    if not contract_modules or any(not path.is_file() for path in contract_modules):
        fail("layering contract classification contains an absent module")
    protected_names = {name for name, _ in data["owners"]}
    contract_inventory: dict[pathlib.Path, dict[str, tuple[str, str]]] = {}
    for contract_path in contract_modules:
        contract_text = read(contract_path)
        if re.search(r"(?m)^\s*(?:export|alias)\b", command_text(contract_text)):
            fail(f"contract alias/export command is forbidden: {contract_path.relative_to(ROOT)}")
        contract_decls = declarations(contract_text)
        contract_inventory[contract_path] = contract_decls
        for name in protected_names:
            if any(shadows(candidate, name) for candidate in contract_decls):
                fail(f"new-owner contract shadow survives for {name} in {contract_path.relative_to(ROOT)}")
    moved_hashes = data["movedSignatureHashes"]
    moved_names = {name for _, name, _ in data["movedDonors"]}
    if set(moved_hashes) != moved_names:
        fail("moved-signature hash keys do not exactly match moved donors")
    for owner_file, name, kind in data["movedDonors"]:
        owner_text = read(ROOT / owner_file)
        owner_decls = legacy_declarations(owner_text)
        if declarations(owner_text).get(f"Blanc.{name}", (None,))[0] != kind:
            fail(f"moved donor {name} absent from {owner_file} at its qualified owner")
        if name not in owner_decls or owner_decls[name][0] != kind:
            fail(f"moved donor {name} absent from {owner_file}")
        got = hashlib.sha256(owner_decls[name][1].encode()).hexdigest()
        if got != moved_hashes[name]:
            fail(f"moved donor signature drift for {name}: {got}")
        for contract_path in contract_modules:
            if any(shadows(candidate, name) for candidate in
                   contract_inventory[contract_path]):
                fail(f"contract shadow survives for {name} in {contract_path.relative_to(ROOT)}")
    if set(data["touchedConsumerHashes"]) != set(data["touchedConsumers"]):
        fail("touched-consumer hash keys do not exactly match touched consumers")
    for consumer in data["touchedConsumers"]:
        if not (ROOT / consumer).is_file():
            fail(f"touched consumer is absent: {consumer}")
        if sha256(ROOT / consumer) != data["touchedConsumerHashes"][consumer]:
            fail(f"touched consumer drifted beyond its pinned owner-reference edit: {consumer}")


def audit_architecture(data: dict) -> None:
    layering = read(ROOT / "scripts/check-layering.py")
    module = data["requiredSharedClassification"]
    shared_match = re.search(r"(?s)^SHARED\s*=\s*\[(.*?)\]\n\nCONTRACTS", layering, re.M)
    if shared_match is None:
        fail("cannot parse the layering SHARED classification")
    shared = re.findall(r'"([A-Za-z0-9_]+)"', shared_match.group(1))
    if shared.count(module) != 1:
        fail(f"{module} is absent or duplicated in the shared classification")
    contract_text = layering[layering.find("CONTRACTS ="):layering.find("ROOTS =")]
    if re.search(rf'"{re.escape(module)}"', contract_text):
        fail(f"{module} is also classified as a contract module")
    for rel, expected in data["jaunePinFiles"].items():
        if sha256(ROOT / rel) != expected:
            fail(f"Blanc's Jaune pin file changed: {rel}")

    # Public WETH statements are frozen as one order-independent digest. This
    # permits no unrecorded statement drift while avoiding a large per-file
    # manifest. The two intentionally edited consumers are additionally
    # pinned byte-for-byte above.
    headers: list[str] = []
    for path in sorted((ROOT / "Blanc").glob("Weth*.lean")):
        for name, (kind, header) in sorted(legacy_declarations(read(path)).items()):
            headers.append(f"{path.name}:{kind}:{name}:{header}")
    aggregate = hashlib.sha256("\n".join(headers).encode()).hexdigest()
    if aggregate != data["wethPublicHeaderAggregate"]:
        fail(f"WETH public-statement aggregate drifted: {aggregate}")


def audit_frozen(data: dict) -> None:
    frozen = data["frozenAssuranceFiles"]
    if not frozen:
        fail("frozen assurance hash map is empty")
    for rel, expected in frozen.items():
        path = ROOT / rel
        if sha256(path) != expected:
            fail(f"frozen predecessor assurance file changed: {rel}")


def run_lean(path: pathlib.Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180,
    )


def audit_fixture(data: dict) -> None:
    text = read(FIXTURE)
    for name in data["requiredPositiveTheorems"]:
        if not re.search(rf"(?m)^private\s+theorem\s+{re.escape(name)}\b", text):
            fail(f"required positive theorem absent: {name}")
    proc = run_lean(FIXTURE)
    if proc.returncode != 0 or proc.stderr:
        fail(f"fixture compilation failed\n{proc.stdout}{proc.stderr}")
    if " ".join(proc.stdout.split()) != " ".join(EXPECTED.split()):
        fail(f"evaluator vector drifted: {proc.stdout.strip()}")
    mutant = text
    for marker, snippet in MUTANTS.items():
        if text.count(marker) != 1:
            fail(f"mutant marker absent or duplicated: {marker}")
        mutant = mutant.replace(marker, snippet + marker)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="TransientSettlementMutants-",
        dir=ROOT / "scripts", delete=False,
    ) as handle:
        handle.write(mutant)
        tmp = pathlib.Path(handle.name)
    try:
        result = run_lean(tmp)
    finally:
        tmp.unlink(missing_ok=True)
    output = result.stdout + result.stderr
    if result.returncode == 0 or output.count("native_decide") < len(MUTANTS):
        fail(f"batched mutants did not all fail for their pinned reason\n{output}")


def deletion_controls(data: dict, *, static: bool, semantic: bool) -> None:
    if static:
        source = read(ROOT / data["commonModule"])
        for name, _ in data["owners"]:
            pattern = re.compile(
                rf"(?m)^((?:theorem|lemma|structure|def|inductive)\s+){re.escape(name)}\b"
            )
            changed, count = pattern.subn(
                rf"\1deleted_{name.replace('.', '_')}", source, count=1
            )
            if count != 1:
                fail(f"cannot live-delete {name}")
            try:
                audit_source(data, changed)
            except SystemExit as exc:
                if "public owner set mismatch" not in str(exc):
                    raise
            else:
                fail(f"live deletion was not detected: {name}")
        for owner_file, name, _ in data["movedDonors"]:
            owner_text = read(ROOT / owner_file)
            changed, count = re.subn(
                rf"(?m)^(\s*(?:theorem|lemma)\s+){re.escape(name)}\b",
                rf"\1deleted_{name.replace('.', '_')}", owner_text, count=1,
            )
            if count != 1 or name in legacy_declarations(changed):
                fail(f"moved-donor deletion was not detected: {name}")

    if semantic:
        fixture = read(FIXTURE)
        for name in data["requiredPositiveTheorems"]:
            changed, count = re.subn(
                rf"(?m)^(private\s+theorem\s+){re.escape(name)}\b",
                rf"\1deleted_{name}", fixture, count=1,
            )
            if count != 1 or re.search(
                rf"(?m)^private\s+theorem\s+{re.escape(name)}\b", changed
            ):
                fail(f"positive deletion was not detected: {name}")
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".lean", prefix="TransientSettlementDeletion-",
                dir=ROOT / "scripts", delete=False,
            ) as handle:
                handle.write(changed)
                tmp = pathlib.Path(handle.name)
            try:
                result = run_lean(tmp)
            finally:
                tmp.unlink(missing_ok=True)
            if result.returncode == 0 or name not in result.stdout + result.stderr:
                fail(f"live positive deletion did not fail through {name}")


def write_manifest(data: dict) -> None:
    """Regenerate only byte/header fields derived from the declared sources."""

    data = dict(data)
    data["jaunePinFiles"] = {
        relative: sha256(ROOT / relative) for relative in data["jaunePinFiles"]
    }
    actual = legacy_declarations(read(ROOT / data["commonModule"]))
    data["signatureHashes"] = {
        name: hashlib.sha256(actual[name][1].encode()).hexdigest()
        for name, _ in data["owners"]
    }
    data["movedSignatureHashes"] = {
        name: hashlib.sha256(
            legacy_declarations(read(ROOT / owner_file))[name][1].encode()
        ).hexdigest()
        for owner_file, name, _ in data["movedDonors"]
    }
    data["touchedConsumerHashes"] = {
        relative: sha256(ROOT / relative) for relative in data["touchedConsumers"]
    }
    headers = []
    for path in sorted((ROOT / "Blanc").glob("Weth*.lean")):
        for name, (kind, header) in sorted(legacy_declarations(read(path)).items()):
            headers.append(f"{path.name}:{kind}:{name}:{header}")
    data["wethPublicHeaderAggregate"] = hashlib.sha256(
        "\n".join(headers).encode()
    ).hexdigest()
    data["frozenAssuranceFiles"] = {
        relative: sha256(ROOT / relative)
        for relative in data["frozenAssuranceFiles"]
    }
    rendered = json.dumps(data, indent=2, sort_keys=True) + "\n"
    temporary = MANIFEST_PATH.with_suffix(".json.tmp")
    temporary.write_text(rendered, encoding="utf-8")
    temporary.replace(MANIFEST_PATH)
    print(f"OK — transient-settlement manifest: wrote {MANIFEST_PATH.relative_to(ROOT)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    phase = parser.add_mutually_exclusive_group()
    phase.add_argument("--static-only", action="store_true")
    phase.add_argument("--semantic-only", action="store_true")
    parser.add_argument("--print-signatures", action="store_true")
    parser.add_argument("--print-compatibility", action="store_true")
    parser.add_argument("--write-manifest", action="store_true")
    arguments = parser.parse_args()
    data = load_manifest()
    if arguments.write_manifest:
        write_manifest(data)
        return
    if arguments.print_signatures:
        actual = legacy_declarations(read(ROOT / data["commonModule"]))
        print(json.dumps({name: hashlib.sha256(header.encode()).hexdigest()
                          for name, (_, header) in actual.items()}, indent=2))
        return
    if arguments.print_compatibility:
        moved = {}
        for owner_file, name, _ in data["movedDonors"]:
            moved[name] = hashlib.sha256(
                legacy_declarations(read(ROOT / owner_file))[name][1].encode()
            ).hexdigest()
        headers = []
        for path in sorted((ROOT / "Blanc").glob("Weth*.lean")):
            for name, (kind, header) in sorted(legacy_declarations(read(path)).items()):
                headers.append(f"{path.name}:{kind}:{name}:{header}")
        print(json.dumps({
            "movedSignatureHashes": moved,
            "touchedConsumerHashes": {
                rel: sha256(ROOT / rel) for rel in data["touchedConsumers"]
            },
            "wethPublicHeaderAggregate": hashlib.sha256(
                "\n".join(headers).encode()
            ).hexdigest(),
        }, indent=2))
        return
    if not arguments.semantic_only:
        parser_controls()
        audit_source(data)
        audit_moves(data)
        audit_architecture(data)
        audit_frozen(data)
    deletion_controls(
        data, static=not arguments.semantic_only, semantic=not arguments.static_only
    )
    if not arguments.static_only:
        audit_fixture(data)
    if arguments.static_only:
        print(
            "OK — transient-settlement static: "
            f"{len(data['owners'])} owned declarations, "
            f"{len(data['movedDonors'])} donor moves"
        )
    elif arguments.semantic_only:
        print(
            "OK — transient-settlement semantic: "
            f"25 evaluator controls, {len(MUTANTS)} mutants"
        )
    else:
        print(
            "OK — transient-settlement: "
            f"{len(data['owners'])} owned declarations, "
            f"{len(data['movedDonors'])} donor moves, "
            f"25 evaluator controls, {len(MUTANTS)} mutants"
        )


if __name__ == "__main__":
    main()
