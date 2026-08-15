#!/usr/bin/env python3
"""Fail-closed assurance for the CircuitBreaker Registry RI7 controls.

This gate deliberately owns only the Registry proof owner and its two small
fixtures.  It compiles both fixtures, pins the public surface that lets callers
reuse the proof, verifies the four protected fixture controls' trust surface,
and runs in-memory falsifiers against the same static validator.
"""

from __future__ import annotations

import hashlib
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Mapping


ROOT = Path(__file__).resolve().parent.parent
OWNER = "Blanc/LidoCircuitBreakerRegistry.lean"
SUCCESS = "scripts/LidoCircuitBreakerRegistrySuccess.lean"
REGRESSION = "scripts/LidoCircuitBreakerRegistryRegression.lean"

NAMESPACES = {
    OWNER: "Blanc.LidoCircuitBreaker",
    SUCCESS: "Blanc.LidoCircuitBreaker.RegistrySuccess",
    REGRESSION: "Blanc.LidoCircuitBreaker",
}
REGISTRY_MUTANT_NAMESPACE = "Blanc.LidoCircuitBreaker.RegistryMutants"

# The reusable production Registry API plus every Registry declaration protected
# by ClaimCheck/AxiomCheck, then the three RI7 exact-code controls and seven
# independent logical-storage mutants.  All are intentionally public.
REQUIRED = {
    OWNER: (
        "slot_toNat_of_region_payload_lt",
        "slot_injective_payload",
        "slot_ne_of_region_ne",
        "RegistryWitness.entries_length_le",
        "setPauserSourceTrace",
        "setPauserSourceTrace_writes",
        "setPauser_run_extracts_sourceTrace",
        "setPauser_sourceTrace_refines_model",
        "RegistryWitness.applySetPauserSourceTrace",
        "setPauserKernel_tableEntry",
        "runtime_registry_lookups",
        "setPauser_zero_runCompiledTo_pausableZero_noRegistryWrite",
        "registerAfterSet_runCompiledTo_preserves_registry",
        "setPauserKernel_run_of_exec",
        "setPauserKernel_exec_extracts_sourceTrace",
        "registerPauser_kernel_exec_preserves_registry",
        "pause_kernel_exec_reaches_pauseAfterSet",
        "registerPauser_settled_error_restores_registry",
        "pause_settled_error_restores_registry",
        "membershipEquivalence_registerPauser",
        "cleanStateAfterRemoval_registerPauser",
        "globalCountConservation_registerPauser",
        "pause_direct_postWrite_revert_settles_and_restores_registry",
        "directPause_zeroCode_postWrite_error_control",
    ),
    SUCCESS: (
        "freshRegistration_exactCode_success_control",
        "freshRegistration_extracts_sourceTrace_control",
    ),
    REGRESSION: (
        "targetZeroGuardAfterAssignment_compiled_rejected",
        "assignmentOmitted_rejected",
        "distinctOldCountOmitted_rejected",
        "distinctNewCountOmitted_rejected",
        "freshZeroBasedIndexLength_rejected",
        "middleRemovalHoleTailOmitted_rejected",
        "movedIndexOmitted_rejected",
        "removedTargetIndexClearOmitted_rejected",
    ),
}

# Filled with SHA-256 of whitespace/comment-normalized declaration headers.
# A header reaches the declaration's defining `:=`, so theorem assumptions and
# conclusion are pinned while implementation-only proof changes remain free.
EXPECTED_HEADERS = {
    "slot_toNat_of_region_payload_lt": "756ea0a7b48a741c04852fbceb3469b37982b8786c1ffa2c14cb48fdf40cf82d",
    "slot_injective_payload": "cc94a59d122af841f255df9ca2dfb70db6c42e6dcfbcaa08d56464537b3b226e",
    "slot_ne_of_region_ne": "90248b058f20e5f0e22409eac1945da1c1fa3a039f76de9b64a38bb6145f1380",
    "RegistryWitness.entries_length_le": "a902c072a364170df688195267472463bfcf716d605523bec1c81c077f85fd41",
    "setPauserSourceTrace": "5bbf19b18e73638ff009eef8a98bbf75cdaa8aaaee35b12b5f5122851521407b",
    "setPauserSourceTrace_writes": "893de8d4caa8ff467be119a6ca341930e88d0192f8b158f2ad27dd018044f946",
    "setPauser_run_extracts_sourceTrace": "fb3efeb75bc202f0c9389e7e0c7d4623b3af4e1b58953598d8efc3b7e20039c5",
    "setPauser_sourceTrace_refines_model": "56eff48639fd6519f545e0aa3a8d15a487780a6578bcfcb6344811eb727080ca",
    "RegistryWitness.applySetPauserSourceTrace": "3f2c0af350bf81e6a4467d1e21ea54be9b7fc8cf092252311f2f3f68ad0172a7",
    "setPauserKernel_tableEntry": "9879e741fcb228f9fac6cb0f82112b446e4f03566e4bdd1fa414f317c886da64",
    "runtime_registry_lookups": "8149fe3ef2b29bc3704d33d49845def456ee72609a2e014b19a660df4af2a288",
    "setPauser_zero_runCompiledTo_pausableZero_noRegistryWrite": "fb8100a4cf4590959aceef181c1fcd34ed27d4e8730c46533943e8f78ff755e2",
    "registerAfterSet_runCompiledTo_preserves_registry": "892cb128fa61e6fcd933996af06fb315c232840de7a1c8bceb0a462911023622",
    "setPauserKernel_run_of_exec": "04e0b1ada596ff1226fa13e3e3e3f0e4143b3e6d9d3de41d4519975188b9d45d",
    "setPauserKernel_exec_extracts_sourceTrace": "13225d0fe847e475201570381c92f4c3585f50131769397cb0c1703b1407755b",
    "registerPauser_kernel_exec_preserves_registry": "1850079741625a9ce68cace80459dc39569e01550c4f0788a65137570491fffa",
    "pause_kernel_exec_reaches_pauseAfterSet": "08f1056ae265469e768092e47fb246b037544be720e02f4af4aa2c65728ecaa8",
    "registerPauser_settled_error_restores_registry": "1fa1839d0948c66ede86f9a4d7b1f6388aa24f744562e82951a2966de71e597e",
    "pause_settled_error_restores_registry": "6c8f7b01b94b1c04ab77124d27e7dc4c692a66f0db138e7255f7b953d600a016",
    "membershipEquivalence_registerPauser": "c6774d15da73c2e14c45896d8ae15da825ae56ebf4e7e86d94e970c108e54ab1",
    "cleanStateAfterRemoval_registerPauser": "46b180d3dc55e08b462ac4f1a419c91c948d7b37db096e7516bb0a01ad6b25fb",
    "globalCountConservation_registerPauser": "c1fc837fde49e39ce75ad873d97026e64a5b9619dd1dbb57cf68e5e5f065ab51",
    "pause_direct_postWrite_revert_settles_and_restores_registry": "062a536d9a706f86047f69d8cea7d962eb78763c4f942ec15a56429cb8d1025a",
    "directPause_zeroCode_postWrite_error_control": "1625f698c2e554a03f892f34343b683d5b2c46c2b2ce3bed4330917221f34698",
    "freshRegistration_exactCode_success_control": "5a38b1755f2c0b3ecb10ecd742fb7661459c343215a8128a7e9f9032c03781cd",
    "freshRegistration_extracts_sourceTrace_control": "42f1f553b40508a4c16afb76e32a196056d831f03ea279c00a70939c314fe3be",
    "targetZeroGuardAfterAssignment_compiled_rejected": "576e1efe73cb5808e14d2aaf9d97cfb89c028825780a1086fcb4b9e8765106be",
    "assignmentOmitted_rejected": "307661553400ed09f45d0feee6e0d81c326220dbf7259c1b0d1aa43d1cc4873d",
    "distinctOldCountOmitted_rejected": "249b4c1682b4c59fe8262a2fc3c9b2d7a7f976e8cc07e0ebf997e3f20eb0973c",
    "distinctNewCountOmitted_rejected": "4560e3e52ff02e3474685f440480cef2cec37ccac97b47f466a0f655d20fc81c",
    "freshZeroBasedIndexLength_rejected": "71e5381bedf5f71d7088a8b93057ed44d80a9d092c3427e9c13f78cf09ee7ff0",
    "middleRemovalHoleTailOmitted_rejected": "b8b7ce186e98e9b26ca9ba6dcffefe6c8a65c66042f4839169f37dad185da825",
    "movedIndexOmitted_rejected": "53525b8901a453596f315137bd46d93a87d0388941cebd5a5768b637449385c1",
    "removedTargetIndexClearOmitted_rejected": "3009eb91c335faa90853f83533bde0bbd2faccaf6d85651731667d9d537e9997",
}

DECL = re.compile(
    r"(?m)^(?P<access>private\s+)?(?P<kind>theorem|def)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "axiom": re.compile(r"\baxiom\b"),
    "opaque": re.compile(r"\bopaque\b"),
    "native reduction": re.compile(r"\bofReduce(?:Bool)?\b"),
    "implemented_by": re.compile(r"\bimplemented_by\b"),
    "extern": re.compile(r"@\s*\[\s*extern\b"),
}
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_CONTROLS = (
    (SUCCESS, "Blanc.LidoCircuitBreaker.RegistrySuccess.freshRegistration_exactCode_success_control"),
    (SUCCESS, "Blanc.LidoCircuitBreaker.RegistrySuccess.freshRegistration_extracts_sourceTrace_control"),
    (REGRESSION, (
        "Blanc.LidoCircuitBreaker.RegistryMutants."
        "targetZeroGuardAfterAssignment_compiled_rejected"
    )),
    (REGRESSION, "Blanc.LidoCircuitBreaker.RegistryMutants.distinctNewCountOmitted_rejected"),
)


class Regression(RuntimeError):
    pass


def fail(message: str) -> None:
    raise Regression(message)


def strip_comments(source: str) -> str:
    """Remove Lean line/nested block comments, retaining source positions."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(source):
        pair = source[i : i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif not in_string and pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif not in_string and pair == "--":
            end = source.find("\n", i)
            if end == -1:
                out.extend(" " * (len(source) - i))
                break
            out.extend(" " * (end - i))
            out.append("\n")
            i = end + 1
        else:
            ch = source[i]
            out.append(ch)
            if ch == '"' and (i == 0 or source[i - 1] != "\\"):
                in_string = not in_string
            i += 1
    if depth:
        fail("unterminated Lean block comment")
    return "".join(out)


def declaration_header(
    source: str, match: re.Match[str], cleaned: str | None = None
) -> str:
    """Return the header through its declaration-level defining token.

    Lean theorem statements may begin with offside-rule ``let x := ...``
    bindings.  A textual search therefore pins only the binding, rather than
    the conclusion.  This scanner follows strings, comments, delimiters, and
    top-level let indentation.  A theorem which used a top-level `let` must
    close with ``:= by``; ordinary one-line theorem proof terms (which cannot
    conceal a declaration-header let) remain supported.  Definitions use the
    same balanced scan without the theorem-specific `by` requirement.
    """
    start = match.start()
    if cleaned is None:
        cleaned = strip_comments(source)
    next_decl = DECL.search(cleaned, match.end())
    i = match.end()
    depth = 0
    in_string = False
    pending_let = False
    let_indent: int | None = None
    saw_top_level_let = False
    at_line_start = False
    column = 0

    def word_at(position: int) -> tuple[str, int]:
        end = position
        while end < len(cleaned) and (cleaned[end].isalnum() or cleaned[end] in "_'."):
            end += 1
        return cleaned[position:end], end

    while i < len(cleaned):
        if next_decl is not None and i >= next_decl.start():
            fail(f"{match.group('name')}: declaration header has no defining :=")
        ch = cleaned[i]
        if in_string:
            if ch == '"' and (i == 0 or cleaned[i - 1] != "\\"):
                in_string = False
            if ch == "\n":
                column = 0
                at_line_start = True
            else:
                column += 1
            i += 1
            continue
        if ch == '"':
            in_string = True
            column += 1
            i += 1
            continue
        if ch == "\n":
            column = 0
            at_line_start = True
            i += 1
            continue
        if at_line_start and ch in " \t":
            column += 1
            i += 1
            continue
        if at_line_start:
            if let_indent is not None and column <= let_indent:
                let_indent = None
            at_line_start = False
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth < 0:
                fail(f"{match.group('name')}: unbalanced delimiter in header")
        elif depth == 0 and (ch.isalpha() or ch == "_"):
            word, end = word_at(i)
            if word == "let":
                pending_let = True
            elif word == "in" and let_indent is not None:
                let_indent = None
            column += end - i
            i = end
            continue
        elif depth == 0 and ch == ";" and let_indent is not None:
            let_indent = None
        elif depth == 0 and cleaned.startswith(":=", i):
            if pending_let:
                pending_let = False
                let_indent = column
                saw_top_level_let = True
                i += 2
                column += 2
                continue
            if let_indent is not None:
                fail(f"{match.group('name')}: unresolved top-level let before :=")
            if match.group("kind") == "theorem":
                tail = cleaned[i + 2:].lstrip()
                if saw_top_level_let and not re.match(r"by\b", tail):
                    fail(f"{match.group('name')}: theorem defining token is not := by")
            return cleaned[start : i + 2]
        column += 1
        i += 1
    fail(f"{match.group('name')}: missing declaration-level defining :=")


def normalized_header(source: str, match: re.Match[str], cleaned: str | None = None) -> str:
    return " ".join(declaration_header(source, match, cleaned).split())


def digest(header: str) -> str:
    return hashlib.sha256(header.encode("utf-8")).hexdigest()


def sources() -> dict[str, str]:
    # Shadows anywhere in first-party Lean source are forbidden, not merely in
    # imports chosen by today's fixtures.
    result: dict[str, str] = {}
    for path in (ROOT / "Blanc").rglob("*.lean"):
        result[path.relative_to(ROOT).as_posix()] = path.read_text()
    for path in (ROOT / "scripts").rglob("*.lean"):
        result[path.relative_to(ROOT).as_posix()] = path.read_text()
    return result


def declaration_index(cleaned_sources: Mapping[str, str]) -> dict[str, list[tuple[str, re.Match[str]]]]:
    """Index every candidate once, so each falsifier stays linear in source."""
    index: dict[str, list[tuple[str, re.Match[str]]]] = {}
    for path, cleaned in cleaned_sources.items():
        for match in DECL.finditer(cleaned):
            index.setdefault(match.group("name"), []).append((path, match))
    return index


def owner_namespace(owner: str, name: str) -> str:
    if owner == REGRESSION:
        return REGISTRY_MUTANT_NAMESPACE
    return NAMESPACES[owner]


def namespace_marker(owner: str, namespace: str) -> str:
    if owner == REGRESSION:
        return "namespace RegistryMutants"
    return f"namespace {namespace}"


def namespace_end_marker(owner: str, namespace: str) -> str:
    if owner == REGRESSION:
        return "end RegistryMutants"
    return f"end {namespace}"


def validate(all_sources: Mapping[str, str]) -> None:
    cleaned_sources = {path: strip_comments(source) for path, source in all_sources.items()}
    declarations = declaration_index(cleaned_sources)
    for path in REQUIRED:
        if path not in all_sources:
            fail(f"missing owner file {path}")
        if f"namespace {NAMESPACES[path]}" not in cleaned_sources[path]:
            fail(f"{path}: missing namespace {NAMESPACES[path]}")

    for path in REQUIRED:
        cleaned = cleaned_sources[path]
        for label, pattern in FORBIDDEN.items():
            if pattern.search(cleaned):
                fail(f"{path}: forbidden trust pattern {label}")

    for owner, names in REQUIRED.items():
        for name in names:
            found = declarations.get(name, [])
            if len(found) != 1:
                fail(f"{name}: expected exactly one declaration, found {len(found)}")
            actual_path, match = found[0]
            if actual_path != owner:
                fail(f"{name}: owned by {actual_path}, expected {owner}")
            if match.group("access"):
                fail(f"{name}: required declaration is private")
            cleaned_owner = cleaned_sources[owner]
            namespace = owner_namespace(owner, name)
            namespace_start = cleaned_owner.find(namespace_marker(owner, namespace))
            namespace_end = cleaned_owner.find(
                namespace_end_marker(owner, namespace), namespace_start
            )
            if not (namespace_start < match.start() < namespace_end):
                fail(f"{name}: not enclosed by {namespace}")
            actual = digest(normalized_header(all_sources[owner], match, cleaned_owner))
            expected = EXPECTED_HEADERS[name]
            if actual != expected:
                fail(f"{name}: header SHA-256 mismatch ({actual})")


def assert_falsifiers(all_sources: Mapping[str, str]) -> int:
    """Prove this validator actually rejects its intended failure channels."""
    target = "setPauserKernel_exec_extracts_sourceTrace"
    owner = OWNER
    original = all_sources[owner]
    count = 0

    def rejected(label: str, changed: dict[str, str]) -> None:
        nonlocal count
        try:
            validate(changed)
        except Regression:
            count += 1
            return
        fail(f"falsifier accepted: {label}")

    deleted = dict(all_sources)
    deleted[owner] = original.replace(
        f"\ntheorem {target}", f"\ntheorem deleted_{target}", 1
    )
    rejected("deletion", deleted)

    ri5_deleted = dict(all_sources)
    ri5_deleted[owner] = original.replace(
        "theorem registerPauser_kernel_exec_preserves_registry",
        "theorem deleted_registerPauser_kernel_exec_preserves_registry",
        1,
    )
    rejected("RI5 deletion", ri5_deleted)

    new_count_deleted = dict(all_sources)
    new_count_deleted[REGRESSION] = new_count_deleted[REGRESSION].replace(
        "theorem distinctNewCountOmitted_rejected",
        "theorem deleted_distinctNewCountOmitted_rejected",
        1,
    )
    rejected("new-count mutant deletion", new_count_deleted)

    renamed = dict(all_sources)
    renamed[SUCCESS] = renamed[SUCCESS].replace(
        "freshRegistration_exactCode_success_control",
        "renamed_success_control", 1,
    )
    rejected("rename", renamed)

    fresh_extractor_deleted = dict(all_sources)
    fresh_extractor_deleted[SUCCESS] = fresh_extractor_deleted[SUCCESS].replace(
        "theorem freshRegistration_extracts_sourceTrace_control",
        "theorem deleted_freshRegistration_extracts_sourceTrace_control",
        1,
    )
    rejected("fresh-success extractor deletion", fresh_extractor_deleted)

    shadowed = dict(all_sources)
    shadowed["Blanc/RegistryAssuranceShadow.lean"] = (
        "namespace Blanc.LidoCircuitBreaker\n"
        f"theorem {target} : True := by trivial\n"
        "end Blanc.LidoCircuitBreaker\n"
    )
    rejected("shadow", shadowed)

    mutated = dict(all_sources)
    mutated[owner] = original.replace(
        "theorem runtime_registry_lookups (dp : DeployParams) :",
        "theorem runtime_registry_lookups (dp : DeployParams) : True :=",
        1,
    )
    rejected("header mutation", mutated)

    target_zero_mutated = dict(all_sources)
    target_zero_mutated[owner] = original.replace(
        "occurrence.instruction ≠ .reg .sstore := by",
        "occurrence.instruction = .reg .sstore := by",
        1,
    )
    rejected("target-zero conclusion mutation after lets", target_zero_mutated)

    clean_removal_mutated = dict(all_sources)
    clean_removal_mutated[owner] = original.replace(
        "target ∉ trace.postEntries.map Prod.fst) ∧",
        "target ∈ trace.postEntries.map Prod.fst) ∧",
        1,
    )
    rejected("clean-removal conclusion mutation after lets", clean_removal_mutated)

    fresh_success_mutated = dict(all_sources)
    fresh_success_mutated[SUCCESS] = fresh_success_mutated[SUCCESS].replace(
        "setPauser [] 7 9 = some [((7 : B256), (9 : B256))] ∧",
        "setPauser [] 7 9 = none ∧",
        1,
    )
    rejected("fresh-success conclusion mutation after lets", fresh_success_mutated)

    forbidden = dict(all_sources)
    forbidden[REGRESSION] += "\ntheorem forbidden_control : True := by sorry\n"
    rejected("forbidden pattern", forbidden)
    return count


def run(command: list[str]) -> str:
    completed = subprocess.run(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    if completed.returncode:
        fail(f"command failed ({' '.join(command)}):\n{completed.stdout.rstrip()}")
    return completed.stdout


def compile_fixture(relative: str) -> None:
    run(["lake", "env", "lean", relative])


def axiom_check(relative: str, qualified: str) -> None:
    source = (ROOT / relative).read_text()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="registry-axioms-", dir=ROOT,
        encoding="utf-8", delete=False,
    ) as handle:
        temporary = Path(handle.name)
        handle.write(source)
        handle.write(f"\n#print axioms {qualified}\n")
    try:
        output = run(["lake", "env", "lean", str(temporary.relative_to(ROOT))])
    finally:
        temporary.unlink(missing_ok=True)
    match = re.search(
        r"'" + re.escape(qualified) + r"' depends on axioms: \[([^\]]*)\]",
        output,
        re.DOTALL,
    )
    if not match:
        fail(f"{qualified}: unrecognised #print axioms output: {output.rstrip()}")
    actual = {item.strip() for item in match.group(1).split(",") if item.strip()}
    if actual != EXPECTED_AXIOMS:
        fail(f"{qualified}: axioms {sorted(actual)}, expected {sorted(EXPECTED_AXIOMS)}")


def main() -> None:
    all_sources = sources()
    validate(all_sources)
    falsifier_count = assert_falsifiers(all_sources)
    compile_fixture(SUCCESS)
    compile_fixture(REGRESSION)
    for relative, qualified in AXIOM_CONTROLS:
        axiom_check(relative, qualified)
    owner_count = len(REQUIRED[OWNER])
    header_count = len(EXPECTED_HEADERS)
    success_count = len(REQUIRED[SUCCESS])
    storage_mutant_count = len(REQUIRED[REGRESSION]) - 1
    print(
        f"OK — Lido CircuitBreaker Registry RI7: {owner_count} Registry declarations, "
        f"{header_count} header pins, {success_count + 1} exact-code controls, "
        f"{storage_mutant_count} storage mutants, {falsifier_count} falsifiers, "
        f"and {len(AXIOM_CONTROLS)} axiom pins"
    )


if __name__ == "__main__":
    try:
        main()
    except Regression as error:
        print(f"REGRESSION — Lido CircuitBreaker Registry RI7: {error}", file=sys.stderr)
        sys.exit(1)
