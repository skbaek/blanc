#!/usr/bin/env python3
"""Validate proof-recipes.toml and generate its Markdown and Lean surfaces.

The repository's gate runtime includes Python 3.9 without a TOML package.  This
script therefore implements the deliberately small TOML subset used by the
registry: integer and double-quoted string scalars, arrays of double-quoted
strings, and ``[[recipe]]`` tables.  Anything outside that subset is rejected
rather than guessed at.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shutil
import sys
import tempfile
import unicodedata
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

from module_path_policy import (
    ModulePathPolicyError,
    audit_census,
    policy_self_test,
    resolve_bound_file,
    resolve_module_file,
    resolve_source_file,
    validate_module_path,
    walk_module_files,
)


REGISTRY_PATH = Path("scripts/proof-recipes.toml")
MARKDOWN_PATH = "docs/PROOF_RECIPES.md"
LEAN_PATH = "Blanc/ProofRecipesGenerated.lean"
TACTICS_PATH = Path("Blanc/Tactics.lean")
SUGGESTIONS_PATH = Path("scripts/ProofRecipeSuggestions.lean")
MANIFEST_PATH = Path("lake-manifest.json")
LAKEFILE_PATH = Path("lakefile.lean")

# The pinned Jaune dependency, as Lake materializes it. These are fixed
# constants of this script, never registry-supplied strings, so they do not go
# through the raw-string module-path policy (which exists for the registry's
# attacker-and-typo-controlled Blanc module values); the walk below refuses
# symbolic links itself and never leaves the package directory.
JAUNE_PACKAGE_PARTS = (".lake", "packages", "jaune")
JAUNE_LIBRARY_DIR = "Jaune"
JAUNE_LIBRARY_AGGREGATE = "Jaune.lean"

TOP_LEVEL_KEYS = {"schema_version", "generated_notice"}
REQUIRED_RECIPE_KEYS = {
    "id",
    "status",
    "triggers",
    "preferred_path",
    "boundary",
    "owner_module",
    "canonical_example",
    "symbols",
    "review_owner",
    "review_date",
}
OPTIONAL_RECIPE_KEYS = {"anti_patterns"}
STATUSES = {"active", "partial", "planned"}
TRIGGER_KINDS = {
    "goal-head": "lean-name",
    "implication-premise": "lean-name",
    "goal-shape": "slug",
    "context-shape": "slug",
}
SYMBOL_KINDS = {"tactic", "declaration", "module"}

KEY_RE = re.compile(r"[a-z][a-z0-9_]*\Z")
ID_RE = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*\Z")
SLUG_RE = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*\Z")
LEAN_PART = r"[A-Za-z_][A-Za-z0-9_']*[?!]?"
LEAN_NAME_RE = re.compile(rf"{LEAN_PART}(?:\.{LEAN_PART})*\Z")
REVIEW_OWNER_RE = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*\Z")
DECL_KINDS = {
    "abbrev",
    "axiom",
    "class",
    "def",
    "inductive",
    "lemma",
    "opaque",
    "structure",
    "theorem",
}
QUALIFIED = rf"{LEAN_PART}(?:\.{LEAN_PART})*"
NAMESPACE_RE = re.compile(rf"^\s*namespace\s+({QUALIFIED})\s*$")
SECTION_RE = re.compile(rf"^\s*(?:noncomputable\s+)?section(?:\s+{QUALIFIED})?\s*$")
END_RE = re.compile(rf"^\s*end(?:\s+{QUALIFIED})?\s*$")
DECL_RE = re.compile(
    rf"^\s*(?:@\[[^]]+\]\s*)*"
    rf"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    rf"(?:{'|'.join(sorted(DECL_KINDS))})\s+({QUALIFIED})(?=\s|:|\{{|\(|$)"
)


class RecipeError(Exception):
    """A fail-closed registry, source-inventory, or drift failure."""


@dataclass(frozen=True)
class Recipe:
    id: str
    status: str
    triggers: Tuple[str, ...]
    preferred_path: str
    boundary: str
    owner_module: str
    canonical_example: str
    symbols: Tuple[str, ...]
    anti_patterns: Tuple[str, ...]
    review_owner: str
    review_date: str


@dataclass(frozen=True)
class Registry:
    schema_version: int
    generated_notice: str
    recipes: Tuple[Recipe, ...]
    # Populations the trigger-soundness checks covered on this run, reported in
    # the terminal verdict so a run that could not resolve the pinned dependency
    # does not read like one that resolved all of it:
    # (Jaune dispatch surface, of which resolved against the pinned source,
    #  recipes with a harness case, triggers with a reachability witness).
    coverage: Tuple[int, int, int, int] = (0, 0, 0, 0)


def parse_basic_string(token: str, where: str) -> str:
    """Parse the JSON-compatible subset of TOML basic strings."""
    if not token.startswith('"') or not token.endswith('"'):
        raise RecipeError(f"{where}: expected a double-quoted string")
    try:
        value = json.loads(token)
    except (json.JSONDecodeError, TypeError) as exc:
        raise RecipeError(f"{where}: malformed string: {exc}") from exc
    if not isinstance(value, str):
        raise RecipeError(f"{where}: expected a string")
    return value


def split_array_items(body: str, where: str) -> List[str]:
    items: List[str] = []
    start = 0
    quoted = False
    escaped = False
    for index, char in enumerate(body):
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char == ",":
            item = body[start:index].strip()
            if item:
                items.append(item)
            else:
                raise RecipeError(f"{where}: empty array item")
            start = index + 1
    if quoted:
        raise RecipeError(f"{where}: unterminated string in array")
    tail = body[start:].strip()
    if tail:
        items.append(tail)
    return items


def parse_value(token: str, where: str) -> Any:
    token = token.strip()
    if not token:
        raise RecipeError(f"{where}: missing value")
    if token.startswith("["):
        if not token.endswith("]"):
            raise RecipeError(f"{where}: unterminated array")
        body = token[1:-1].strip()
        if not body:
            return []
        return [parse_basic_string(item, where) for item in split_array_items(body, where)]
    if token.startswith('"'):
        return parse_basic_string(token, where)
    if re.fullmatch(r"0|[1-9][0-9]*", token):
        return int(token)
    raise RecipeError(f"{where}: unsupported TOML value {token!r}")


def array_complete(text: str) -> bool:
    quoted = False
    escaped = False
    depth = 0
    for char in text:
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth < 0:
                return False
    return not quoted and depth == 0


def parse_registry_text(text: str, source: str) -> Tuple[Dict[str, Any], List[Dict[str, Any]]]:
    top: Dict[str, Any] = {}
    recipes: List[Dict[str, Any]] = []
    current: Optional[Dict[str, Any]] = None
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        number = index + 1
        stripped = lines[index].strip()
        index += 1
        if not stripped or stripped.startswith("#"):
            continue
        if stripped == "[[recipe]]":
            current = {}
            recipes.append(current)
            continue
        if stripped.startswith("["):
            raise RecipeError(f"{source}:{number}: only [[recipe]] tables are supported")
        if "=" not in stripped:
            raise RecipeError(f"{source}:{number}: expected key = value")
        key, raw_value = (part.strip() for part in stripped.split("=", 1))
        if not KEY_RE.fullmatch(key):
            raise RecipeError(f"{source}:{number}: invalid key {key!r}")
        target = top if current is None else current
        if key in target:
            raise RecipeError(f"{source}:{number}: duplicate key {key!r}")
        if raw_value.startswith("[") and not array_complete(raw_value):
            chunks = [raw_value]
            while index < len(lines) and not array_complete("\n".join(chunks)):
                continuation = lines[index].strip()
                index += 1
                if continuation.startswith("#"):
                    raise RecipeError(
                        f"{source}:{index}: comments inside arrays are not supported"
                    )
                chunks.append(continuation)
            raw_value = "\n".join(chunks)
        target[key] = parse_value(raw_value, f"{source}:{number}:{key}")
    return top, recipes


def strip_lean_comments(text: str, source: str) -> str:
    """Remove nested Lean comments while preserving strings and line layout."""
    out: List[str] = []
    index = 0
    depth = 0
    quoted = False
    escaped = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                out.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
            continue
        if not quoted and text.startswith("/-", index):
            depth = 1
            out.extend("  ")
            index += 2
        elif not quoted and text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                out.append(" ")
                index += 1
        else:
            char = text[index]
            out.append(char)
            if quoted:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    quoted = False
            elif char == '"':
                quoted = True
            index += 1
    if depth:
        raise RecipeError(f"{source}: unterminated Lean block comment")
    if quoted:
        raise RecipeError(f"{source}: unterminated Lean string")
    return "".join(out)


def qualify(namespace: Sequence[str], name: str) -> str:
    if name.startswith("_root_."):
        return name[len("_root_.") :]
    if name == "Blanc" or name.startswith("Blanc."):
        return name
    return ".".join([*namespace, name]) if namespace else name


def declarations_in(path: Path) -> Set[str]:
    try:
        clean = strip_lean_comments(path.read_text(encoding="utf-8"), str(path))
    except OSError as exc:
        raise RecipeError(f"cannot read Lean source {path}: {exc}") from exc
    scopes: List[Tuple[str, List[str]]] = []
    found: Set[str] = set()
    for number, line in enumerate(clean.splitlines(), 1):
        if match := NAMESPACE_RE.match(line):
            scopes.append(("namespace", match.group(1).split(".")))
        elif SECTION_RE.match(line):
            scopes.append(("section", []))
        elif END_RE.match(line):
            if not scopes:
                raise RecipeError(f"{path}:{number}: unmatched end")
            scopes.pop()
        elif match := DECL_RE.match(line):
            namespace = [
                part
                for scope_kind, parts in scopes
                if scope_kind == "namespace"
                for part in parts
            ]
            found.add(qualify(namespace, match.group(1)))
    if scopes:
        raise RecipeError(f"{path}: unclosed namespace or section")
    return found


def lean_sources(root: Path, aggregate_raw: str = "Blanc.lean") -> List[Path]:
    try:
        paths: List[Path] = []
        root_names = os.listdir(str(root))
        aggregate_alias = any(
            unicodedata.normalize("NFC", name).casefold()
            == unicodedata.normalize("NFC", aggregate_raw).casefold()
            for name in root_names
        )
        if aggregate_raw != "Blanc.lean" or aggregate_raw in root_names or aggregate_alias:
            paths.append(resolve_source_file(
                root, aggregate_raw, site="proof-recipe-root-aggregate"
            ))
        paths.extend(walk_module_files(root, site="proof-recipe-source-walk"))
        return paths
    except ModulePathPolicyError as error:
        raise RecipeError(f"module-path policy: {error}") from error


def declaration_inventory(root: Path) -> Tuple[Set[str], Dict[Path, Set[str]]]:
    all_names: Set[str] = set()
    per_file: Dict[Path, Set[str]] = {}
    for path in lean_sources(root):
        names = declarations_in(path)
        per_file[path.resolve()] = names
        all_names.update(names)
    return all_names, per_file


def tactic_inventory(root: Path) -> Set[str]:
    found: Set[str] = set()
    quoted = re.compile(r'"([A-Za-z_][A-Za-z0-9_]*[?!]?)"')
    for path in lean_sources(root):
        clean = strip_lean_comments(path.read_text(encoding="utf-8"), str(path))
        for match in re.finditer(r"\b(?:syntax|elab|macro)\b", clean):
            chunk = clean[match.start() : match.start() + 800]
            blank = re.search(r"\n\s*\n", chunk)
            if blank:
                chunk = chunk[: blank.start()]
            if not re.search(r":\s*tactic\b", chunk):
                continue
            found.update(name.group(1) for name in quoted.finditer(chunk))
    return found


def canonical_declaration(name: str) -> str:
    return name if name.startswith("Blanc.") else f"Blanc.{name}"


def resolve_example_declaration(name: str, candidates: Set[str]) -> Optional[str]:
    """Resolve an example's file-local name, rejecting ambiguous suffixes."""
    canonical = canonical_declaration(name)
    if canonical in candidates:
        return canonical
    matches = sorted(candidate for candidate in candidates if candidate.endswith(f".{name}"))
    return matches[0] if len(matches) == 1 else None


def expect_string(mapping: Dict[str, Any], key: str, where: str) -> str:
    value = mapping[key]
    if not isinstance(value, str):
        raise RecipeError(f"{where}.{key}: expected string")
    if not value or value != value.strip() or "\n" in value or "\r" in value:
        raise RecipeError(f"{where}.{key}: expected a nonempty single-line string")
    return value


def expect_string_array(mapping: Dict[str, Any], key: str, where: str) -> Tuple[str, ...]:
    value = mapping[key]
    if not isinstance(value, list) or not value:
        raise RecipeError(f"{where}.{key}: expected a nonempty string array")
    if any(not isinstance(item, str) or not item or item != item.strip() for item in value):
        raise RecipeError(f"{where}.{key}: every item must be a nonempty trimmed string")
    if len(set(value)) != len(value):
        raise RecipeError(f"{where}.{key}: duplicate item")
    return tuple(value)


def validate_trigger(trigger: str, where: str) -> None:
    kind, separator, value = trigger.partition(":")
    if not separator or kind not in TRIGGER_KINDS:
        raise RecipeError(
            f"{where}: trigger {trigger!r} is outside the controlled vocabulary "
            f"{sorted(TRIGGER_KINDS)}"
        )
    value_kind = TRIGGER_KINDS[kind]
    if value_kind == "lean-name" and not LEAN_NAME_RE.fullmatch(value):
        raise RecipeError(f"{where}: trigger {trigger!r} needs a Lean declaration name")
    if value_kind == "slug" and not SLUG_RE.fullmatch(value):
        raise RecipeError(f"{where}: trigger {trigger!r} needs a lowercase kebab slug")


def proof_recipe_trigger_inventory(root: Path) -> Dict[str, str]:
    """Read the explicit fail-closed trigger dispatch from Blanc/Tactics.lean.

    Maps each implemented trigger to the source text of its arm, so
    ``validate_trigger_dispatch`` can check that the arm still dispatches on
    live declarations.
    """
    path = root / TACTICS_PATH
    try:
        clean = strip_lean_comments(path.read_text(encoding="utf-8"), str(path))
    except OSError as exc:
        raise RecipeError(f"cannot read trigger matcher {TACTICS_PATH}: {exc}") from exc

    lines = clean.splitlines()
    starts = [
        index
        for index, line in enumerate(lines)
        if re.match(r"^def\s+proofRecipeTriggerMatches\b", line)
    ]
    if len(starts) != 1:
        raise RecipeError(
            f"{TACTICS_PATH}: expected exactly one proofRecipeTriggerMatches definition, "
            f"found {len(starts)}"
        )
    start = starts[0]
    end = next(
        (
            index
            for index in range(start + 1, len(lines))
            if lines[index] and not lines[index][0].isspace()
        ),
        len(lines),
    )
    body = lines[start:end]
    matches = [
        (index, match.group(1))
        for index, line in enumerate(body)
        if (match := re.match(r"^(\s*)match\s+trigger\s+with\s*$", line))
    ]
    if len(matches) != 1:
        raise RecipeError(
            f"{TACTICS_PATH}: proofRecipeTriggerMatches must contain exactly one "
            f"`match trigger with`, found {len(matches)}"
        )
    match_index, indent = matches[0]
    arm_re = re.compile(rf"^{re.escape(indent)}\|\s*(.*?)\s*=>")
    literal_re = re.compile(r'"(?:[^"\\]|\\.)*"\Z')
    triggers: Dict[str, str] = {}
    wildcard_count = 0
    saw_wildcard = False
    current: Optional[str] = None
    for line in body[match_index + 1 :]:
        arm = arm_re.match(line)
        if not arm:
            if current is not None:
                triggers[current] += "\n" + line
            continue
        current = None
        pattern = arm.group(1)
        if saw_wildcard:
            raise RecipeError(
                f"{TACTICS_PATH}: proofRecipeTriggerMatches fail-closed wildcard "
                "must be its final arm"
            )
        if pattern == "_":
            if line.strip() != "| _ => return false":
                raise RecipeError(
                    f"{TACTICS_PATH}: proofRecipeTriggerMatches wildcard must be "
                    "exactly `| _ => return false`"
                )
            wildcard_count += 1
            saw_wildcard = True
            continue
        if not literal_re.fullmatch(pattern):
            raise RecipeError(
                f"{TACTICS_PATH}: unsupported proofRecipeTriggerMatches arm {pattern!r}; "
                "use one explicit string literal per trigger"
            )
        trigger = parse_basic_string(pattern, f"{TACTICS_PATH}: trigger matcher arm")
        if trigger in triggers:
            raise RecipeError(
                f"{TACTICS_PATH}: duplicate proofRecipeTriggerMatches arm {trigger!r}"
            )
        triggers[trigger] = line
        current = trigger
    if wildcard_count != 1:
        raise RecipeError(
            f"{TACTICS_PATH}: proofRecipeTriggerMatches must have exactly one "
            f"fail-closed wildcard, found {wildcard_count}"
        )
    if not triggers:
        raise RecipeError(f"{TACTICS_PATH}: proofRecipeTriggerMatches has no explicit triggers")
    return triggers


# A Lean name literal inside a trigger arm: `Blanc.Foo.bar, or ``Blanc.Foo.bar.
# Only this repository's own names are checkable here; Jaune's census is not
# read by this generator, so `Jaune.*` dispatch names are deliberately out of
# scope and a Jaune rename is caught by the pin-move gates instead.
DISPATCH_NAME_RE = re.compile(r"``?(Blanc\.[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)")

# Any Lean name literal, whoever owns it. Used only to tell an arm that
# dispatches on a name this repository cannot check from one that dispatches on
# no name at all -- two different reasons to be outside the checked population,
# and each has to be stated rather than inferred.
ANY_DISPATCH_NAME_RE = re.compile(r"``?([A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)")

# A call to one of this module's own trigger helper predicates. Several arms
# state their whole condition as `proofRecipeIsByteSizeComposition target` and
# name nothing themselves; the names they dispatch on live one level down, in
# the helper. Following the call is what makes those arms checkable at all.
DISPATCH_HELPER_RE = re.compile(r"\b(proofRecipe[A-Za-z0-9_']*[?!]?)")
DISPATCH_HELPER_DEF_RE = re.compile(r"^def\s+(proofRecipe[A-Za-z0-9_']*[?!]?)\s*[:(]")

# The dispatcher itself is not one of its own helpers: following it would put
# every arm's names in every arm's closure and restore exactly the masking the
# per-arm guard exists to remove.
TRIGGER_MATCHER = "proofRecipeTriggerMatches"

# Trigger arms that dispatch on no Blanc declaration even after their helper
# predicates are followed, each with the reason it cannot be checked here. An
# arm leaves the per-arm guard by being written down with a reason, never by
# quietly contributing nothing; and the entries are themselves checked, so one
# that becomes checkable, or stops matching its stated reason, fails.
UNCHECKED_DISPATCH_ARMS: Dict[str, str] = {
    "context-shape:intermediate-devm":
        "counts local hypotheses headed by Jaune.Devm",
    "goal-shape:devm-common-update-law":
        "names Jaune.Devm and Jaune state updaters only",
    "goal-shape:devm-update-projection":
        "proofRecipeIsDevmProjectionBridge dispatches on Jaune.Devm projections "
        "and updaters only",
    "goal-shape:full-length-slice":
        "names Jaune.List.sliceD only",
    "goal-shape:message-execution-settlement":
        "names Jaune.processMessage, Jaune.exec and Jaune.initEvm only",
    "goal-shape:successor-projection":
        "names Jaune.Devm updaters and reuses the same Jaune-only projection "
        "bridge",
    "goal-shape:shared-subject-kernel-decision":
        "structural: proofRecipeHasRepeatedClosedLetSubject decides on the "
        "shape of the term and names no declaration at all",
}

# The reasons above divide in two, and the division is checkable: a foreign arm
# must still dispatch on some name, and a structural arm must dispatch on none.
STRUCTURAL_DISPATCH_ARMS = frozenset({"goal-shape:shared-subject-kernel-decision"})

# Every Jaune name any trigger arm dispatches on, through its helper predicates.
#
# ``validate_trigger_dispatch`` above can only see this repository's own names,
# so the Jaune half of the dispatch was unchecked in two different ways. Six
# arms dispatch on Jaune names only and sit in ``UNCHECKED_DISPATCH_ARMS``; two
# more -- ``goal-shape:operand-stack-fault-free`` and
# ``goal-shape:terminal-return-revert`` -- are *inside* the checked population
# because they also name Blanc declarations, and their Jaune disjuncts were
# silently unchecked while the arm reported green. Blanc consumes Jaune through
# a Git-pinned Lake dependency, so a pin bump that renames one of these leaves
# every one of those arms compiling and comparing against a name nothing
# produces.
#
# The surface is bound to the pin it was verified against. Two checks are
# always available, with no dependency materialized:
#   * the names the arms actually dispatch on must equal this set exactly, in
#     both directions, so the population cannot drift by accident; and
#   * ``JAUNE_DISPATCH_PIN`` must equal the rev ``lake-manifest.json`` and
#     ``lakefile.lean`` pin, so a pin bump -- the event that causes the failure
#     -- fails the gate until the surface is re-verified against the new Jaune.
# When ``.lake/packages/jaune`` is materialized at that exact rev, every name is
# additionally resolved against the pinned source. See ``validate_jaune_dispatch``
# for what that verification does and does not establish.
JAUNE_DISPATCH_PIN = "0cc7f56aa5159aec57424a04f8c3731618e91441"
JAUNE_DISPATCH_SURFACE = frozenset({
    "Jaune.Devm",
    "Jaune.Devm.accessedAddresses",
    "Jaune.Devm.accessedStorageKeys",
    "Jaune.Devm.accountsToDelete",
    "Jaune.Devm.createdAccounts",
    "Jaune.Devm.error",
    "Jaune.Devm.gasLeft",
    "Jaune.Devm.logs",
    "Jaune.Devm.mach",
    "Jaune.Devm.memWrite",
    "Jaune.Devm.memory",
    "Jaune.Devm.meta",
    "Jaune.Devm.output",
    "Jaune.Devm.refundCounter",
    "Jaune.Devm.returnData",
    "Jaune.Devm.setMach",
    "Jaune.Devm.setMeta",
    "Jaune.Devm.setStorVal",
    "Jaune.Devm.setWorld",
    "Jaune.Devm.stack",
    "Jaune.Devm.state",
    "Jaune.Devm.transientStorage",
    "Jaune.Devm.world",
    "Jaune.ExceptionalHalt.stackOverflow",
    "Jaune.ExceptionalHalt.stackUnderflow",
    "Jaune.Linst.return_",
    "Jaune.Linst.revert",
    "Jaune.List.sliceD",
    "Jaune.addAccessedStorageKey",
    "Jaune.exec",
    "Jaune.initEvm",
    "Jaune.processMessage",
})

# Names outside both namespaces that an arm may dispatch on. These are Lean core
# and are not pinned by this repository at all, so they are stated here rather
# than left to fall through whichever of the two checks happens to ignore them.
CORE_DISPATCH_NAMES = frozenset({"Eq", "Iff", "LE.le", "LT.lt", "Ne"})

# Registered recipes with no case in ``scripts/ProofRecipeSuggestions.lean``,
# each with what a case would have to exhibit.
#
# A trigger arm that is live -- every name it compares against exists -- can
# still never fire, because nothing says a goal ever presents those names where
# the arm looks for them. That reachability question is not decidable from the
# registry and ``Blanc/Tactics.lean`` (see ``validate_harness_coverage``); the
# only evidence available is a real goal that the elaborator agrees the trigger
# matches, which is what the suggestions harness is. This table is therefore the
# list of recipes for which no such evidence exists, grandfathered by name so
# that the *next* recipe added without a harness case fails instead of joining
# them silently. It is checked in both directions: a listed recipe that gains a
# case, or that leaves the registry, fails.
UNWITNESSED_RECIPES: Dict[str, str] = {
    # Empty: every registered recipe currently has a harness case. The
    # table stays so the next recipe added without a case fails here
    # instead of joining a silent gap; list it with what a case would
    # have to exhibit.
}

# Triggers whose reachability is *proved*: the harness states a real goal and
# ``expect_recipe_trigger`` makes the elaborator decide the arm's own predicate
# on it, so the arm demonstrably fires. A bare ``blanc_suggest`` case does not
# prove this -- the tactic only logs, so an example compiles whether or not any
# trigger matched -- and neither does an ``-- EXPECT:`` comment, which is prose.
# The set is pinned by name rather than counted so that losing a witness and
# gaining an unrelated one cannot cancel out.
REACHABILITY_WITNESSED_TRIGGERS = frozenset({
    "context-shape:intermediate-devm",
    "goal-head:CompiledStackSafety.Certificate",
    "goal-head:ContractSpec.PreservesAdmitted",
    "goal-head:Func.ExecSat",
    "goal-head:Func.Inv",
    "goal-head:Func.RunCompiled",
    "goal-head:Func.RunCompiledTo",
    "goal-head:Line.Inv",
    "goal-head:LinkCertificate",
    "goal-head:Linst.Inv",
    "goal-head:MemWordAt",
    "goal-head:MigrationSound",
    "goal-head:ReturnsWord",
    "goal-head:StateReplay",
    "goal-shape:accepted-bool-word",
    "goal-shape:bounded-creation-word-encoder",
    "goal-shape:compile-shape-prepend-congruence",
    "goal-shape:compiled-shape-byte-navigation",
    "goal-shape:compileshape-bytesize",
    "goal-shape:constant-error-guard",
    "goal-shape:devm-common-update-law",
    "goal-shape:devm-update-projection",
    "goal-shape:exact-retained-storage-effects",
    "goal-shape:fixed-byte-offset",
    "goal-shape:frame-root-carrying",
    "goal-shape:full-length-slice",
    "goal-shape:linear-dispatch-selection",
    "goal-shape:message-execution-settlement",
    "goal-shape:raw-sstore-free-compiled-path",
    "goal-shape:retained-wrapper-trace",
    "goal-shape:retained-write-noninterference",
    "goal-shape:runcompiled-family-compression",
    "goal-shape:selector-separation",
    "goal-shape:shared-subject-kernel-decision",
    "goal-shape:stack-prefix-line-run",
    "goal-shape:successor-projection",
    "goal-shape:symbolic-label-linking",
    "goal-shape:tagged-storage-region-separation",
    "goal-shape:terminal-return-revert",
    "goal-shape:trace-local-frame-admission",
    "implication-premise:Func.Run",
    "implication-premise:Line.Run",
})

EXPECT_COMMENT_RE = re.compile(r"^-- EXPECT: ([a-z][a-z0-9]*(?:-[a-z0-9]+)*)\s*$", re.MULTILINE)
EXPECT_TRIGGER_RE = re.compile(r'\bexpect_recipe_trigger\s+"([^"\n]*)"')
EXPECT_NO_TRIGGER_RE = re.compile(r'\bexpect_no_recipe_trigger\s+"([^"\n]*)"')

CONSTRUCTOR_RE = re.compile(rf"^\s+\|\s*({LEAN_PART})(?=\s|:|\(|\{{|$)")


def constructors_in(path: Path) -> Set[str]:
    """Inductive constructor names, qualified like ``declarations_in``.

    Trigger arms legitimately dispatch on a constructor such as
    ``Blanc.Func.branch``, which is not a top-level declaration. This is a
    separate, additive census so the shared declaration inventory that symbol
    validation uses keeps its exact meaning.
    """
    try:
        clean = strip_lean_comments(path.read_text(encoding="utf-8"), str(path))
    except OSError as exc:
        raise RecipeError(f"cannot read Lean source {path}: {exc}") from exc
    scopes: List[Tuple[str, List[str]]] = []
    found: Set[str] = set()
    owner: Optional[str] = None
    for line in clean.splitlines():
        if match := NAMESPACE_RE.match(line):
            scopes.append(("namespace", match.group(1).split(".")))
            owner = None
        elif SECTION_RE.match(line):
            scopes.append(("section", []))
            owner = None
        elif END_RE.match(line):
            if scopes:
                scopes.pop()
            owner = None
        elif match := DECL_RE.match(line):
            namespace = [
                part
                for scope_kind, parts in scopes
                if scope_kind == "namespace"
                for part in parts
            ]
            owner = (
                qualify(namespace, match.group(1))
                if re.match(r"^\s*(?:@\[[^]]+\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*inductive\b", line)
                else None
            )
        elif owner is not None and (match := CONSTRUCTOR_RE.match(line)):
            found.add(f"{owner}.{match.group(1)}")
        elif line.strip() and not line[0].isspace():
            owner = None
    return found


def constructor_inventory(root: Path) -> Set[str]:
    found: Set[str] = set()
    for path in lean_sources(root):
        found.update(constructors_in(path))
    return found


def proof_recipe_helper_bodies(root: Path) -> Dict[str, str]:
    """The source of every ``proofRecipe*`` helper predicate, by name.

    An arm's condition is often a single call -- ``proofRecipeIsByteSizeComposition
    target`` -- and the Lean names it really dispatches on are inside the
    helper. ``blanc_suggest`` stops firing just as silently when one of those is
    renamed, so the closure over these bodies, not the arm's own text, is the
    population this check has to reason about.

    The dispatcher itself is excluded: its body is every arm, and following it
    would let each arm borrow every other arm's names.
    """
    path = root / TACTICS_PATH
    try:
        clean = strip_lean_comments(path.read_text(encoding="utf-8"), str(path))
    except OSError as exc:
        raise RecipeError(f"cannot read trigger matcher {TACTICS_PATH}: {exc}") from exc
    lines = clean.splitlines()
    bodies: Dict[str, str] = {}
    index = 0
    while index < len(lines):
        definition = DISPATCH_HELPER_DEF_RE.match(lines[index])
        if not definition:
            index += 1
            continue
        end = index + 1
        while end < len(lines) and (not lines[end] or lines[end][0].isspace()):
            end += 1
        name = definition.group(1)
        if name in bodies:
            raise RecipeError(
                f"{TACTICS_PATH}: duplicate trigger helper definition {name!r}"
            )
        bodies[name] = "\n".join(lines[index:end])
        index = end
    bodies.pop(TRIGGER_MATCHER, None)
    return bodies


def arm_dispatch_closure(arm: str, helpers: Dict[str, str]) -> Set[str]:
    """Every Lean name literal an arm dispatches on, through its helpers."""
    names: Set[str] = set()
    pending = [arm]
    followed: Set[str] = set()
    while pending:
        text = pending.pop()
        names.update(ANY_DISPATCH_NAME_RE.findall(text))
        for helper in DISPATCH_HELPER_RE.findall(text):
            if helper in helpers and helper not in followed:
                followed.add(helper)
                pending.append(helpers[helper])
    return names


def validate_trigger_dispatch(
    arms: Dict[str, str], names: Set[str], helpers: Dict[str, str]
) -> int:
    """Every trigger must still be able to fire, and every arm must be checked.

    ``load_and_validate`` already rejects a registry trigger with no arm in
    ``Blanc/Tactics.lean``. That is not enough: an arm compares the goal against
    Lean *names*, and a renamed or deleted declaration leaves the arm compiling
    and comparing against a name nothing produces, so ``blanc_suggest`` silently
    stops firing and the recipe becomes decorative. This check reads the names
    each arm dispatches on -- through its helper predicates, because several
    arms name nothing themselves -- and requires them to be live.

    The anti-vacuity guard is per arm, not per table. A guard over the whole
    table is satisfied by the arms that do dispatch on live names, so rewording
    one arm out of its sight leaves it masked by its neighbours; the arm this
    check no longer covers is exactly the arm most likely to have gone quiet.
    An arm outside the checked population is therefore listed by name in
    ``UNCHECKED_DISPATCH_ARMS`` with the reason it cannot be checked here, and
    those listings are checked too, so the population cannot drift by accident
    in either direction.

    Returns the number of names checked.
    """
    checked = 0
    failures: List[str] = []
    vacuous: List[str] = []
    closures = {trigger: arm_dispatch_closure(arms[trigger], helpers) for trigger in arms}
    for trigger in sorted(arms):
        own = sorted(name for name in closures[trigger] if name.startswith("Blanc."))
        for name in own:
            checked += 1
            if name not in names:
                failures.append(
                    f"{TACTICS_PATH}: trigger {trigger!r} dispatches on {name}, "
                    f"which is not a declaration in this repository — the arm "
                    f"compiles but can never fire, so its recipe is decorative"
                )
        if not own and trigger not in UNCHECKED_DISPATCH_ARMS:
            vacuous.append(
                f"{TACTICS_PATH}: trigger {trigger!r} dispatches on no Blanc "
                f"declaration, even through its helper predicates — it is outside "
                f"this check entirely, so add it to UNCHECKED_DISPATCH_ARMS with "
                f"the reason it cannot be checked here, or restore the name it "
                f"used to compare against"
            )
    if failures:
        raise RecipeError("; ".join(failures))
    if not checked:
        raise RecipeError(
            f"{TACTICS_PATH}: no proofRecipeTriggerMatches arm dispatches on a "
            f"Blanc declaration — the trigger dispatch has been reworded out of "
            f"this check's sight"
        )
    for trigger, reason in sorted(UNCHECKED_DISPATCH_ARMS.items()):
        if trigger not in arms:
            vacuous.append(
                f"{TACTICS_PATH}: UNCHECKED_DISPATCH_ARMS lists {trigger!r} "
                f"({reason}), which is not an arm of proofRecipeTriggerMatches"
            )
            continue
        closure = closures[trigger]
        if any(name.startswith("Blanc.") for name in closure):
            vacuous.append(
                f"{TACTICS_PATH}: trigger {trigger!r} is listed as unchecked "
                f"({reason}) but now dispatches on a Blanc declaration — remove "
                f"it from UNCHECKED_DISPATCH_ARMS so the per-arm check covers it"
            )
        elif trigger in STRUCTURAL_DISPATCH_ARMS:
            if closure:
                vacuous.append(
                    f"{TACTICS_PATH}: trigger {trigger!r} is listed as structural "
                    f"but dispatches on {sorted(closure)}"
                )
        elif not closure:
            vacuous.append(
                f"{TACTICS_PATH}: trigger {trigger!r} is listed as dispatching on "
                f"foreign names ({reason}) but dispatches on no name at all"
            )
    if vacuous:
        raise RecipeError("; ".join(vacuous))
    return checked


FOREIGN_STRUCT_RE = re.compile(
    rf"^\s*(?:@\[[^]]+\]\s*)*"
    rf"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    rf"(structure|inductive)\s+({QUALIFIED})(?=\s|:|\(|\{{|$)"
)
FOREIGN_FIELD_RE = re.compile(rf"^\s+(?:«({LEAN_PART})»|({LEAN_PART}))\s*:(?!=)")
MUTUAL_RE = re.compile(r"^\s*mutual\s*$")


def foreign_qualify(namespace: Sequence[str], name: str) -> str:
    if name.startswith("_root_."):
        return name[len("_root_.") :]
    return ".".join([*namespace, name]) if namespace else name


def foreign_declarations_in(path: Path) -> Set[str]:
    """Declarations, structure fields and constructors of a dependency module.

    A separate, additive census, for the same reason ``constructors_in`` is one:
    the shared Blanc inventory that symbol validation uses keeps its exact
    meaning. It differs from that inventory in three ways that a dependency
    needs and Blanc's own sources do not:

    * qualification is generic -- ``declarations_in`` short-circuits names that
      already start with ``Blanc.``, which would silently drop a dependency's
      namespace;
    * ``mutual``/``end`` is a scope, which Jaune uses and Blanc does not. Without
      it the reader pops the enclosing ``namespace Jaune`` at the first such
      ``end`` and every later declaration is censused unqualified, so a live name
      reads as dead; and
    * structure fields are projections a trigger arm legitimately dispatches on
      (``Jaune.Devm.mach`` is a field, not a ``def``), so they are counted --
      only inside a ``structure`` body, so an indented ``name : type`` elsewhere
      cannot invent one.

    Fails closed on an unbalanced scope stack rather than returning a census
    whose names are wrong.
    """
    try:
        clean = strip_lean_comments(path.read_text(encoding="utf-8"), str(path))
    except OSError as exc:
        raise RecipeError(f"cannot read dependency source {path}: {exc}") from exc
    scopes: List[Tuple[str, List[str]]] = []
    found: Set[str] = set()
    owner: Optional[str] = None
    owner_kind: Optional[str] = None
    for number, line in enumerate(clean.splitlines(), 1):
        if match := NAMESPACE_RE.match(line):
            scopes.append(("namespace", match.group(1).split(".")))
            owner = None
        elif SECTION_RE.match(line) or MUTUAL_RE.match(line):
            scopes.append(("section", []))
            owner = None
        elif END_RE.match(line):
            if not scopes:
                raise RecipeError(f"{path}:{number}: unmatched end")
            scopes.pop()
            owner = None
        elif match := FOREIGN_STRUCT_RE.match(line):
            namespace = [
                part
                for scope_kind, parts in scopes
                if scope_kind == "namespace"
                for part in parts
            ]
            owner = foreign_qualify(namespace, match.group(2))
            owner_kind = match.group(1)
            found.add(owner)
        elif match := DECL_RE.match(line):
            namespace = [
                part
                for scope_kind, parts in scopes
                if scope_kind == "namespace"
                for part in parts
            ]
            found.add(foreign_qualify(namespace, match.group(1)))
            owner = None
        elif owner is not None and owner_kind == "inductive" and (
            match := CONSTRUCTOR_RE.match(line)
        ):
            found.add(f"{owner}.{match.group(1)}")
        elif owner is not None and owner_kind == "structure" and (
            match := FOREIGN_FIELD_RE.match(line)
        ):
            found.add(f"{owner}.{match.group(1) or match.group(2)}")
        elif line.strip() and not line[0].isspace():
            owner = None
    if scopes:
        raise RecipeError(f"{path}: unclosed namespace, section or mutual block")
    return found


def jaune_package_root(root: Path) -> Optional[Path]:
    """``.lake/packages/jaune`` if Lake has materialized it, else ``None``.

    Every component is required to be a real directory entry: a symbolic link
    anywhere on the way in would let the census read some other checkout while
    the rev check below reports the pinned one.
    """
    current = root
    for component in JAUNE_PACKAGE_PARTS:
        current = current / component
        if current.is_symlink():
            raise RecipeError(
                f"symbolic-link filesystem alias is forbidden on the pinned "
                f"dependency path: {current}"
            )
        if not current.is_dir():
            return None
    return current


def jaune_library_sources(package: Path) -> List[Path]:
    """The pinned package's library modules: ``Jaune.lean`` and ``Jaune/**``.

    Deliberately not the whole checkout. The package's own ``scripts/*.lean``
    pilots declare names that are not part of the library Blanc imports, and
    counting them would let a name that no Blanc goal can ever contain read as
    live.
    """
    found: List[Path] = []
    aggregate = package / JAUNE_LIBRARY_AGGREGATE
    if aggregate.is_symlink():
        raise RecipeError(f"symbolic-link filesystem alias is forbidden: {aggregate}")
    if aggregate.is_file():
        found.append(aggregate)

    def visit(directory: Path) -> None:
        try:
            with os.scandir(str(directory)) as iterator:
                entries = sorted(iterator, key=lambda entry: entry.name)
        except OSError as error:
            raise RecipeError(
                f"cannot enumerate pinned dependency directory {directory}: {error}"
            ) from error
        for entry in entries:
            entry_path = directory / entry.name
            if entry.is_symlink():
                raise RecipeError(
                    f"symbolic-link filesystem alias is forbidden in the pinned "
                    f"dependency tree: {entry_path}"
                )
            if entry.is_dir(follow_symlinks=False):
                visit(entry_path)
            elif entry.name.endswith(".lean"):
                found.append(entry_path)

    library = package / JAUNE_LIBRARY_DIR
    if library.is_symlink():
        raise RecipeError(f"symbolic-link filesystem alias is forbidden: {library}")
    if library.is_dir():
        visit(library)
    if not found:
        raise RecipeError(
            f"pinned dependency {package} has no {JAUNE_LIBRARY_AGGREGATE} and no "
            f"{JAUNE_LIBRARY_DIR}/**/*.lean library modules to census"
        )
    return sorted(found)


def foreign_declaration_inventory(package: Path) -> Set[str]:
    found: Set[str] = set()
    for path in jaune_library_sources(package):
        found.update(foreign_declarations_in(path))
    return found


def manifest_jaune_rev(root: Path) -> str:
    path = root / MANIFEST_PATH
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise RecipeError(f"cannot read {MANIFEST_PATH}: {error}") from error
    packages = document.get("packages") if isinstance(document, dict) else None
    if not isinstance(packages, list):
        raise RecipeError(f"{MANIFEST_PATH}: no packages array")
    revisions = [
        entry.get("rev")
        for entry in packages
        if isinstance(entry, dict) and entry.get("name") == "jaune"
    ]
    if len(revisions) != 1 or not isinstance(revisions[0], str):
        raise RecipeError(
            f"{MANIFEST_PATH}: expected exactly one jaune package with a rev, "
            f"found {len(revisions)}"
        )
    return revisions[0]


def lakefile_jaune_rev(root: Path) -> str:
    path = root / LAKEFILE_PATH
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as error:
        raise RecipeError(f"cannot read {LAKEFILE_PATH}: {error}") from error
    matches = re.findall(
        r'require\s+jaune\s+from\s+git\s+"[^"\n]*"\s*@\s*"([^"\n]*)"', text
    )
    if len(matches) != 1:
        raise RecipeError(
            f"{LAKEFILE_PATH}: expected exactly one pinned `require jaune from git` "
            f"clause, found {len(matches)}"
        )
    return matches[0]


def materialized_jaune_rev(package: Path) -> str:
    head = package / ".git" / "HEAD"
    if head.is_symlink() or not head.is_file():
        raise RecipeError(
            f"pinned dependency {package} is materialized but its checked-out "
            f"revision cannot be established from {head} — re-run `lake update` "
            f"rather than censusing an unidentified Jaune"
        )
    try:
        value = head.read_text(encoding="utf-8").strip()
    except OSError as error:
        raise RecipeError(f"cannot read {head}: {error}") from error
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise RecipeError(
            f"{head} is {value!r}, not a detached 40-hex revision — the pinned "
            f"dependency checkout is not the one lake-manifest.json names"
        )
    return value


def validate_jaune_dispatch(
    closures: Dict[str, Set[str]], root: Path
) -> Tuple[int, int]:
    """Close the half of the trigger dispatch ``validate_trigger_dispatch`` cannot see.

    That check reads only ``Blanc.`` names, so every Jaune name any arm compares
    against was unchecked -- including the Jaune disjuncts of two arms that the
    per-arm guard reports as checked. This one binds the whole Jaune dispatch
    surface to the pin it was verified against, and resolves it against the
    pinned source whenever Lake has materialized it.

    Returns ``(surface size, names resolved against the pinned source)``; the
    second number is zero when the dependency is not materialized, and the
    caller prints it, so a run that could not resolve anything says so instead
    of reading like a run that resolved everything.
    """
    if not JAUNE_DISPATCH_SURFACE:
        raise RecipeError(
            "JAUNE_DISPATCH_SURFACE is empty — the Jaune half of the trigger "
            "dispatch would be checked over nothing"
        )
    actual: Set[str] = set()
    stray: Set[str] = set()
    for closure in closures.values():
        for name in closure:
            if name.startswith("Jaune."):
                actual.add(name)
            elif not name.startswith("Blanc.") and name not in CORE_DISPATCH_NAMES:
                stray.add(name)
    if stray:
        raise RecipeError(
            f"{TACTICS_PATH}: trigger dispatch names {sorted(stray)}, which are "
            f"neither Blanc nor Jaune nor listed in CORE_DISPATCH_NAMES — no check "
            f"resolves them, so add them to a population that does"
        )
    missing = sorted(JAUNE_DISPATCH_SURFACE - actual)
    unlisted = sorted(actual - JAUNE_DISPATCH_SURFACE)
    if missing or unlisted:
        raise RecipeError(
            f"{TACTICS_PATH}: the Jaune dispatch surface drifted: no arm dispatches "
            f"on {missing}; {unlisted} is dispatched on but unlisted — re-verify "
            f"JAUNE_DISPATCH_SURFACE against the pinned Jaune and update it, so the "
            f"listing keeps naming exactly what the arms compare against"
        )
    manifest = manifest_jaune_rev(root)
    lakefile = lakefile_jaune_rev(root)
    if manifest != lakefile:
        raise RecipeError(
            f"{MANIFEST_PATH} pins jaune at {manifest} but {LAKEFILE_PATH} requires "
            f"{lakefile}"
        )
    if manifest != JAUNE_DISPATCH_PIN:
        raise RecipeError(
            f"the Jaune pin moved to {manifest}: JAUNE_DISPATCH_SURFACE was verified "
            f"against {JAUNE_DISPATCH_PIN}, so every arm that dispatches on a Jaune "
            f"name is now unverified — re-verify the surface against the new pin "
            f"with the dependency materialized and update JAUNE_DISPATCH_PIN"
        )
    package = jaune_package_root(root)
    if package is None:
        return len(JAUNE_DISPATCH_SURFACE), 0
    checkout = materialized_jaune_rev(package)
    if checkout != JAUNE_DISPATCH_PIN:
        raise RecipeError(
            f"{package} is checked out at {checkout}, not the pinned "
            f"{JAUNE_DISPATCH_PIN} — censusing it would verify the dispatch surface "
            f"against a Jaune this repository does not depend on"
        )
    names = foreign_declaration_inventory(package)
    dead = sorted(name for name in JAUNE_DISPATCH_SURFACE if name not in names)
    if dead:
        raise RecipeError(
            f"{TACTICS_PATH}: trigger dispatch compares against {dead}, which the "
            f"pinned Jaune does not declare — the arm compiles but can never fire, "
            f"so its recipe is decorative"
        )
    return len(JAUNE_DISPATCH_SURFACE), len(JAUNE_DISPATCH_SURFACE)


def validate_harness_coverage(
    root: Path, recipe_ids: Set[str], arms: Set[str]
) -> Tuple[int, int]:
    """Enumerate the registry against the suggestions harness.

    Liveness is not reachability. ``validate_trigger_dispatch`` and
    ``validate_jaune_dispatch`` together establish that every name an arm
    compares against exists; neither says a goal ever presents that name where
    the arm looks for it, and an arm that no goal can reach is exactly as
    decorative as one that compares against a departed name.

    Reachability is not decidable from the registry and ``Blanc/Tactics.lean``.
    The dispatcher's ``head`` is computed from a goal expression at tactic time,
    and neither file contains a goal; the question is a property of the corpus of
    statements authors write, including ones not yet written, so no amount of
    reading these two files answers it. Even the elaborator answers only the
    bounded form of the question -- does this trigger match *this* goal -- which
    is precisely what ``scripts/ProofRecipeSuggestions.lean`` asks it, once per
    case, under ``scripts/check.sh``.

    So the evidence that a trigger can fire is an exhibited goal, and this check
    is an enumeration rather than an analysis:

    * every registered recipe has a harness case or is named in
      ``UNWITNESSED_RECIPES``, both directions checked, so the next recipe added
      without one fails instead of joining the grandfathered list silently;
    * every ``-- EXPECT:`` id names a registered recipe, so a renamed recipe
      cannot leave a comment pointing at nothing;
    * every trigger string in the harness names a real arm. A misspelled
      ``expect_no_recipe_trigger`` is the sharpest case: the dispatcher's
      fail-closed wildcard returns ``false`` for an unknown trigger, so the
      negative control passes by construction and stops testing anything; and
    * the triggers with a positive ``expect_recipe_trigger`` case -- the only
      machine-checked reachability evidence in the repository -- are pinned by
      name, so one cannot be lost while another is gained.

    Returns ``(recipes with a harness case, triggers with a reachability witness)``.
    """
    path = root / SUGGESTIONS_PATH
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as error:
        raise RecipeError(f"cannot read {SUGGESTIONS_PATH}: {error}") from error
    expected_ids = set(EXPECT_COMMENT_RE.findall(text))
    if not expected_ids:
        raise RecipeError(
            f"{SUGGESTIONS_PATH}: no `-- EXPECT: <recipe id>` case at all — the "
            f"registry/harness enumeration has been reworded out of this check's "
            f"sight"
        )
    orphans = sorted(expected_ids - recipe_ids)
    if orphans:
        raise RecipeError(
            f"{SUGGESTIONS_PATH}: `-- EXPECT:` names {orphans}, which "
            f"{REGISTRY_PATH} does not register"
        )
    uncovered = recipe_ids - expected_ids
    unexplained = sorted(uncovered - set(UNWITNESSED_RECIPES))
    if unexplained:
        raise RecipeError(
            f"{SUGGESTIONS_PATH}: recipes {unexplained} have no case, so nothing "
            f"shows their triggers can fire on a real goal — add a case, or add "
            f"each to UNWITNESSED_RECIPES with what a case would have to exhibit"
        )
    stale = sorted(set(UNWITNESSED_RECIPES) - uncovered)
    if stale:
        raise RecipeError(
            f"UNWITNESSED_RECIPES lists {stale}, which now has a harness case or is "
            f"no longer registered — remove the listing so the enumeration keeps "
            f"naming exactly the uncovered recipes"
        )
    positive = set(EXPECT_TRIGGER_RE.findall(text))
    negative = set(EXPECT_NO_TRIGGER_RE.findall(text))
    if not positive:
        raise RecipeError(
            f"{SUGGESTIONS_PATH}: no positive expect_recipe_trigger case — nothing "
            f"in the repository witnesses that any trigger fires on a real goal"
        )
    unknown = sorted((positive | negative) - arms)
    if unknown:
        raise RecipeError(
            f"{SUGGESTIONS_PATH}: {unknown} is not an arm of "
            f"proofRecipeTriggerMatches — the dispatcher's fail-closed wildcard "
            f"returns false for it, so a negative control on it passes over nothing "
            f"and a positive one can never pass"
        )
    gained = sorted(positive - REACHABILITY_WITNESSED_TRIGGERS)
    lost = sorted(REACHABILITY_WITNESSED_TRIGGERS - positive)
    if gained or lost:
        raise RecipeError(
            f"{SUGGESTIONS_PATH}: the reachability-witness population drifted: "
            f"{gained} gained a positive expect_recipe_trigger case and is not "
            f"listed; {lost} is listed but no longer has one — update "
            f"REACHABILITY_WITNESSED_TRIGGERS so a lost witness cannot be masked by "
            f"an unrelated new one"
        )
    return len(expected_ids), len(positive)


def validate_symbol(
    symbol: str,
    where: str,
    root: Path,
    declarations: Set[str],
    tactics: Set[str],
) -> None:
    kind, separator, value = symbol.partition(":")
    if not separator or kind not in SYMBOL_KINDS or not value:
        raise RecipeError(
            f"{where}: symbol {symbol!r} must be kind:value with kind in "
            f"{sorted(SYMBOL_KINDS)}"
        )
    if kind == "tactic":
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*[?!]?", value):
            raise RecipeError(f"{where}: invalid tactic name {value!r}")
        if value not in tactics:
            raise RecipeError(f"{where}: tactic {value!r} was not found in Blanc Lean sources")
    elif kind == "declaration":
        if not LEAN_NAME_RE.fullmatch(value):
            raise RecipeError(f"{where}: invalid declaration name {value!r}")
        name = canonical_declaration(value)
        if name not in declarations:
            raise RecipeError(f"{where}: declaration {value!r} ({name}) was not found")
    else:
        symbol_module_file(root, value, where)


def symbol_module_file(root: Path, value: str, where: str) -> Path:
    try:
        return resolve_module_file(root, value, site="proof-recipe-symbol-module")
    except ModulePathPolicyError as error:
        raise RecipeError(f"{where}: invalid module {value!r}: {error}") from error


def owner_module_file(root: Path, value: str, where: str) -> Path:
    try:
        return resolve_module_file(root, value, site="proof-recipe-owner-module")
    except ModulePathPolicyError as error:
        raise RecipeError(f"{where}: invalid Blanc module {value!r}: {error}") from error


def canonical_example_file(root: Path, value: str, where: str) -> Path:
    try:
        return resolve_module_file(root, value, site="proof-recipe-canonical-example")
    except ModulePathPolicyError as error:
        raise RecipeError(f"{where}: invalid file {value!r}: {error}") from error


def load_and_validate(root: Path) -> Registry:
    registry_path = root / REGISTRY_PATH
    try:
        text = registry_path.read_text(encoding="utf-8")
    except OSError as exc:
        raise RecipeError(f"cannot read {REGISTRY_PATH}: {exc}") from exc
    top, raw_recipes = parse_registry_text(text, REGISTRY_PATH.as_posix())
    unknown_top = set(top) - TOP_LEVEL_KEYS
    missing_top = TOP_LEVEL_KEYS - set(top)
    if unknown_top or missing_top:
        raise RecipeError(
            f"top-level schema mismatch: missing {sorted(missing_top)}, "
            f"unknown {sorted(unknown_top)}"
        )
    if top["schema_version"] != 1 or isinstance(top["schema_version"], bool):
        raise RecipeError("schema_version must be the integer 1")
    if not isinstance(top["generated_notice"], str) or not top["generated_notice"].strip():
        raise RecipeError("generated_notice must be a nonempty string")
    if not raw_recipes:
        raise RecipeError("registry contains no [[recipe]] entries")

    declarations, per_file = declaration_inventory(root)
    tactics = tactic_inventory(root)
    supported_triggers = proof_recipe_trigger_inventory(root)
    helpers = proof_recipe_helper_bodies(root)
    validate_trigger_dispatch(
        supported_triggers,
        declarations | constructor_inventory(root),
        helpers,
    )
    jaune_surface, jaune_resolved = validate_jaune_dispatch(
        {
            trigger: arm_dispatch_closure(arm, helpers)
            for trigger, arm in supported_triggers.items()
        },
        root,
    )
    seen_ids: Set[str] = set()
    recipes: List[Recipe] = []
    for index, raw in enumerate(raw_recipes, 1):
        where = f"recipe[{index}]"
        missing = REQUIRED_RECIPE_KEYS - set(raw)
        unknown = set(raw) - REQUIRED_RECIPE_KEYS - OPTIONAL_RECIPE_KEYS
        if missing or unknown:
            raise RecipeError(
                f"{where}: schema mismatch: missing {sorted(missing)}, "
                f"unknown {sorted(unknown)}"
            )
        recipe_id = expect_string(raw, "id", where)
        if not ID_RE.fullmatch(recipe_id):
            raise RecipeError(f"{where}.id: expected a stable lowercase kebab id")
        if recipe_id in seen_ids:
            raise RecipeError(f"{where}.id: duplicate recipe id {recipe_id!r}")
        seen_ids.add(recipe_id)
        status = expect_string(raw, "status", where)
        if status not in STATUSES:
            raise RecipeError(f"{where}.status: expected one of {sorted(STATUSES)}")
        triggers = expect_string_array(raw, "triggers", where)
        for trigger in triggers:
            validate_trigger(trigger, f"{where}.triggers")
            if trigger not in supported_triggers:
                raise RecipeError(
                    f"{where}.triggers: trigger {trigger!r} is not implemented by "
                    f"{TACTICS_PATH}"
                )
        preferred_path = expect_string(raw, "preferred_path", where)
        boundary = expect_string(raw, "boundary", where)
        owner_module = expect_string(raw, "owner_module", where)
        owner_module_file(root, owner_module, f"{where}.owner_module")
        canonical_example = expect_string(raw, "canonical_example", where)
        example_file, separator, example_decl = canonical_example.partition(":")
        if not separator or not LEAN_NAME_RE.fullmatch(example_decl):
            raise RecipeError(
                f"{where}.canonical_example: expected Blanc/File.lean:Declaration.Name"
            )
        example_path = canonical_example_file(
            root, example_file, f"{where}.canonical_example"
        )
        example_name = resolve_example_declaration(
            example_decl, per_file.get(example_path, set())
        )
        if example_name is None:
            raise RecipeError(
                f"{where}.canonical_example: declaration {example_decl!r} was not found "
                f"uniquely in {example_file}"
            )
        symbols = expect_string_array(raw, "symbols", where)
        for symbol in symbols:
            validate_symbol(symbol, f"{where}.symbols", root, declarations, tactics)
        anti_patterns: Tuple[str, ...] = ()
        if "anti_patterns" in raw:
            anti_patterns = expect_string_array(raw, "anti_patterns", where)
            for anti_pattern in anti_patterns:
                if not SLUG_RE.fullmatch(anti_pattern):
                    raise RecipeError(
                        f"{where}.anti_patterns: {anti_pattern!r} is not a lowercase kebab slug"
                    )
        review_owner = expect_string(raw, "review_owner", where)
        if not REVIEW_OWNER_RE.fullmatch(review_owner):
            raise RecipeError(f"{where}.review_owner: expected a lowercase kebab owner")
        review_date = expect_string(raw, "review_date", where)
        try:
            parsed_date = datetime.date.fromisoformat(review_date)
        except ValueError as exc:
            raise RecipeError(f"{where}.review_date: expected YYYY-MM-DD") from exc
        if parsed_date.isoformat() != review_date:
            raise RecipeError(f"{where}.review_date: expected canonical YYYY-MM-DD")
        recipes.append(
            Recipe(
                id=recipe_id,
                status=status,
                triggers=triggers,
                preferred_path=preferred_path,
                boundary=boundary,
                owner_module=owner_module,
                canonical_example=canonical_example,
                symbols=symbols,
                anti_patterns=anti_patterns,
                review_owner=review_owner,
                review_date=review_date,
            )
        )
    witnessed_recipes, witnessed_triggers = validate_harness_coverage(
        root, seen_ids, set(supported_triggers)
    )
    return Registry(
        1,
        top["generated_notice"],
        tuple(recipes),
        (jaune_surface, jaune_resolved, witnessed_recipes, witnessed_triggers),
    )


def markdown_link(path: str) -> str:
    return f"[{path}](../{path})"


def render_markdown(registry: Registry) -> str:
    out = [
        "<!-- GENERATED FILE — do not edit by hand. -->",
        "<!-- Regenerate with: python3 scripts/generate-proof-recipes.py --write -->",
        "",
        "# Blanc proof recipes",
        "",
        registry.generated_notice,
        "",
        "Consult these recipes before beginning a manual multi-step walk or inversion.",
        "A suggestion is guidance, not a proof that its recipe applies at a particular goal.",
        "",
    ]
    for recipe in registry.recipes:
        example_file, _, example_decl = recipe.canonical_example.partition(":")
        out.extend(
            [
                f"## `{recipe.id}`",
                "",
                f"- Status: `{recipe.status}`",
                "- Triggers: " + ", ".join(f"`{trigger}`" for trigger in recipe.triggers),
                f"- Preferred path: {recipe.preferred_path}",
                f"- Boundary: {recipe.boundary}",
                f"- Owner module: {markdown_link(recipe.owner_module)}",
                f"- Canonical example: {markdown_link(example_file)} — `{example_decl}`",
                "- Registered symbols: " + ", ".join(f"`{symbol}`" for symbol in recipe.symbols),
            ]
        )
        if recipe.anti_patterns:
            out.append(
                "- Advisory anti-patterns: "
                + ", ".join(f"`{item}`" for item in recipe.anti_patterns)
            )
        out.extend(
            [
                f"- Review: `{recipe.review_owner}` on `{recipe.review_date}`",
                "",
            ]
        )
    return "\n".join(out)


def lean_string(value: str) -> str:
    escaped = (
        value.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
    )
    return f'"{escaped}"'


def render_lean(registry: Registry) -> str:
    out = [
        "-- ProofRecipesGenerated.lean : goal-shape recipe data for Blanc tactics.",
        "--",
        "-- GENERATED FILE — do not edit by hand. Regenerate with:",
        "--",
        "--     python3 scripts/generate-proof-recipes.py --write",
        "",
        "namespace Blanc.ProofRecipes",
        "",
        "/-- A generated proof-engineering suggestion. All matching is advisory. -/",
        "structure Recipe where",
        "  id : String",
        "  status : String",
        "  triggers : List String",
        "  preferredPath : String",
        "  symbols : List String",
        "  boundary : String",
        "  deriving Repr, Inhabited",
        "",
        "/-- Recipes generated from `scripts/proof-recipes.toml`, in registry order. -/",
        "def recipes : List Recipe := [",
    ]
    for recipe in registry.recipes:
        trigger_text = ", ".join(lean_string(trigger) for trigger in recipe.triggers)
        symbol_text = ", ".join(lean_string(symbol) for symbol in recipe.symbols)
        out.extend(
            [
                "  {",
                f"    id := {lean_string(recipe.id)}",
                f"    status := {lean_string(recipe.status)}",
                f"    triggers := [{trigger_text}]",
                f"    preferredPath := {lean_string(recipe.preferred_path)}",
                f"    symbols := [{symbol_text}]",
                f"    boundary := {lean_string(recipe.boundary)}",
                "  },",
            ]
        )
    out.extend(["]", "", "end Blanc.ProofRecipes", ""])
    return "\n".join(out)


def generated_surfaces(registry: Registry) -> Dict[str, str]:
    return {MARKDOWN_PATH: render_markdown(registry), LEAN_PATH: render_lean(registry)}


def write_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle = tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        newline="",
        dir=path.parent,
        prefix=f".{path.name}.",
        delete=False,
    )
    temporary = Path(handle.name)
    try:
        with handle:
            handle.write(text)
        os.chmod(temporary, 0o644)
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def compare_surfaces(root: Path, expected: Dict[str, str]) -> List[str]:
    failures: List[str] = []
    for relative, wanted in expected.items():
        try:
            path = resolve_bound_file(
                root, relative, allow_missing=False,
                site="proof-recipe-generated-read",
            )
            actual = path.read_text(encoding="utf-8")
        except (OSError, ModulePathPolicyError) as exc:
            failures.append(f"{relative}: cannot read generated surface: {exc}")
            continue
        if actual != wanted:
            failures.append(
                f"{relative}: generated surface drift; run "
                "python3 scripts/generate-proof-recipes.py --write"
            )
    return failures


def make_self_test_root(root: Path, target: Path) -> None:
    sources = lean_sources(root)
    (target / "scripts").mkdir(parents=True)
    (target / "docs").mkdir()
    shutil.copy2(root / REGISTRY_PATH, target / REGISTRY_PATH)
    shutil.copy2(root / SUGGESTIONS_PATH, target / SUGGESTIONS_PATH)
    shutil.copy2(root / MANIFEST_PATH, target / MANIFEST_PATH)
    shutil.copy2(root / LAKEFILE_PATH, target / LAKEFILE_PATH)
    shutil.copytree(root / "Blanc", target / "Blanc")
    aggregate = next((path for path in sources if path.name == "Blanc.lean"), None)
    if aggregate is not None:
        shutil.copy2(aggregate, target / "Blanc.lean")
    make_self_test_jaune_package(target)


# The self-test's stand-in for the pinned Lake dependency. It is built from
# ``JAUNE_DISPATCH_SURFACE`` so the fixture cannot fall behind the surface it
# exists to resolve, and the three shapes that the real Jaune uses and Blanc's
# own sources do not -- a ``mutual`` block, a French-quoted structure field, and
# a projection that is a field rather than a ``def`` -- are written out
# explicitly, so the parser features are controlled rather than assumed.
SELF_TEST_JAUNE_STRUCTURES: Dict[str, Tuple[str, ...]] = {
    "Jaune.Devm": ("mach", "meta", "world"),
}
SELF_TEST_JAUNE_INDUCTIVES: Dict[str, Tuple[str, ...]] = {
    "Jaune.ExceptionalHalt": ("stackOverflow", "stackUnderflow"),
    "Jaune.Linst": ("return_", "revert"),
}


def self_test_jaune_source(surface: Iterable[str]) -> str:
    remaining = set(surface)
    lines = ["namespace Jaune", ""]
    for owner, fields in sorted(SELF_TEST_JAUNE_STRUCTURES.items()):
        local = owner.split(".", 1)[1]
        lines.append(f"structure {local} : Type where")
        for field in fields:
            quoted = f"«{field}»" if field == "meta" else field
            lines.append(f"  {quoted} : Nat")
            remaining.discard(f"{owner}.{field}")
        remaining.discard(owner)
        lines.append("")
    for owner, constructors in sorted(SELF_TEST_JAUNE_INDUCTIVES.items()):
        local = owner.split(".", 1)[1]
        lines.append(f"inductive {local} : Type where")
        for constructor in constructors:
            lines.append(f"  | {constructor}")
            remaining.discard(f"{owner}.{constructor}")
        remaining.discard(owner)
        lines.append("")
    projections = sorted(name for name in remaining if name.startswith("Jaune.Devm."))
    others = sorted(remaining - set(projections))
    lines.append("mutual")
    for name in projections:
        lines.append(f"def {name.split('.', 1)[1]} (devm : Devm) : Nat := 0")
    lines.append("end")
    lines.append("")
    for name in others:
        lines.append(f"def {name.split('.', 1)[1]} : Nat := 0")
    lines.extend(["", "end Jaune", ""])
    return "\n".join(lines)


def make_self_test_jaune_package(target: Path) -> None:
    package = target.joinpath(*JAUNE_PACKAGE_PARTS)
    (package / JAUNE_LIBRARY_DIR).mkdir(parents=True)
    (package / ".git").mkdir()
    (package / ".git" / "HEAD").write_text(
        f"{JAUNE_DISPATCH_PIN}\n", encoding="utf-8"
    )
    (package / JAUNE_LIBRARY_AGGREGATE).write_text(
        "import Jaune.Surface\n", encoding="utf-8"
    )
    (package / JAUNE_LIBRARY_DIR / "Surface.lean").write_text(
        self_test_jaune_source(JAUNE_DISPATCH_SURFACE), encoding="utf-8"
    )


def replace_once(text: str, old: str, new: str, label: str) -> str:
    if text.count(old) != 1:
        raise RecipeError(
            f"self-test setup {label}: expected one occurrence of {old!r}, "
            f"found {text.count(old)}"
        )
    return text.replace(old, new, 1)


def remove_first_scalar_field(text: str, key: str, label: str) -> str:
    """Remove the first one-line scalar field without pinning its value."""
    pattern = re.compile(rf"^{re.escape(key)} = .*\n", re.MULTILINE)
    mutated, count = pattern.subn("", text, count=1)
    if count != 1:
        raise RecipeError(
            f"self-test setup {label}: expected at least one {key!r} scalar field"
        )
    return mutated


def self_test(root: Path) -> None:
    policy_controls, closed_skips, explicit_sites = policy_self_test(
        Path(__file__).resolve().parents[1]
    )
    print(
        "OK — module-path policy self-test: "
        f"{policy_controls}/{policy_controls} raw, census, containment, and alias controls; "
        f"{explicit_sites} explicit dereference site(s) inventoried; "
        f"{closed_skips} host-inexpressible "
        "case/normalization alias control(s) skipped closed"
    )
    controls = 0
    with tempfile.TemporaryDirectory(prefix="proof-recipes-") as directory:
        test_root = Path(directory) / "blanc"
        make_self_test_root(root, test_root)
        registry = load_and_validate(test_root)
        surfaces = generated_surfaces(registry)
        for relative, text in surfaces.items():
            write_atomic(test_root / relative, text)
        if compare_surfaces(test_root, surfaces):
            raise RecipeError("self-test setup: freshly generated surfaces did not compare")

        markdown = test_root / MARKDOWN_PATH
        markdown.write_text(markdown.read_text(encoding="utf-8") + "perturbed\n", encoding="utf-8")
        drift = compare_surfaces(test_root, surfaces)
        if not drift or MARKDOWN_PATH not in drift[0]:
            raise RecipeError("self-test: perturbed generated Markdown was not rejected")
        controls += 1

        original = (test_root / REGISTRY_PATH).read_text(encoding="utf-8")

        def rejected(label: str, mutated: str, expected: str) -> None:
            nonlocal controls
            (test_root / REGISTRY_PATH).write_text(mutated, encoding="utf-8")
            try:
                load_and_validate(test_root)
            except RecipeError as exc:
                if expected not in str(exc):
                    raise RecipeError(
                        f"self-test {label}: expected {expected!r}, got {str(exc)!r}"
                    ) from exc
            else:
                raise RecipeError(f"self-test {label}: malformed registry passed")
            finally:
                (test_root / REGISTRY_PATH).write_text(original, encoding="utf-8")
            controls += 1

        rejected(
            "duplicate-id",
            replace_once(
                original,
                'id = "line-run-split"',
                'id = "runcompiled-construction"',
                "duplicate-id",
            ),
            "duplicate recipe id",
        )
        rejected(
            "bad-status",
            replace_once(
                original,
                'id = "runcompiled-construction"\nstatus = "active"',
                'id = "runcompiled-construction"\nstatus = "retired"',
                "bad-status",
            ),
            "expected one of",
        )
        rejected(
            "bad-trigger",
            replace_once(
                original,
                '"goal-head:Func.RunCompiled",',
                '"mystery:Func.RunCompiled",',
                "bad-trigger",
            ),
            "controlled vocabulary",
        )
        rejected(
            "unimplemented-trigger",
            replace_once(
                original,
                '"goal-head:Func.RunCompiled",',
                '"goal-head:Func.UnimplementedTrigger",',
                "unimplemented-trigger",
            ),
            "is not implemented by Blanc/Tactics.lean",
        )
        rejected(
            "missing-field",
            remove_first_scalar_field(original, "boundary", "missing-field"),
            "missing ['boundary']",
        )

        tactics_path = test_root / TACTICS_PATH
        tactics_original = tactics_path.read_text(encoding="utf-8")

        def rejected_tactics(label: str, mutated: str, expected: str) -> None:
            nonlocal controls
            if mutated == tactics_original:
                raise RecipeError(f"self-test {label}: mutation changed nothing")
            tactics_path.write_text(mutated, encoding="utf-8")
            try:
                load_and_validate(test_root)
            except RecipeError as exc:
                if expected not in str(exc):
                    raise RecipeError(
                        f"self-test {label}: expected {expected!r}, got {str(exc)!r}"
                    ) from exc
            else:
                raise RecipeError(f"self-test {label}: dead trigger dispatch passed")
            finally:
                tactics_path.write_text(tactics_original, encoding="utf-8")
            controls += 1

        # A trigger arm that compiles and can never fire: the declaration it
        # compares against no longer exists, so blanc_suggest goes quiet and the
        # recipe becomes decorative without any surface changing.
        rejected_tactics(
            "dead-trigger-dispatch",
            replace_once(
                tactics_original,
                "`Blanc.Func.RunCompiled\n",
                "`Blanc.Func.DepartedRunCompiled\n",
                "dead-trigger-dispatch",
            ),
            "can never fire",
        )
        # ... and the check is not vacuous: dispatch reworded out of its sight
        # fails rather than passing green over an empty population.
        rejected_tactics(
            "emptied-trigger-dispatch",
            tactics_original.replace("`Blanc.", "`Departed."),
            "reworded out of",
        )
        # ... and the guard is per arm, not per table.  One arm reworded out of
        # sight leaves forty-five neighbours dispatching on live names, which is
        # everything a table-wide guard asks for, while the arm nobody is
        # checking any more is exactly the arm most likely to have gone quiet.
        rejected_tactics(
            "vacuous-trigger-arm",
            replace_once(
                tactics_original,
                '| "goal-head:MemImage" => return head == some `Blanc.MemImage',
                '| "goal-head:MemImage" => return head == some `Departed.MemImage',
                "vacuous-trigger-arm",
            ),
            "outside this check entirely",
        )
        # An arm whose whole condition is one helper call names nothing itself.
        # Before the check followed the call, renaming what the helper compares
        # against left the arm dead and this check silent.
        rejected_tactics(
            "dead-helper-dispatch",
            replace_once(
                tactics_original,
                "compileShapeName == `Blanc.Func.compileShape",
                "compileShapeName == `Blanc.Func.departedCompileShape",
                "dead-helper-dispatch",
            ),
            "can never fire",
        )
        # The arms that are outside it are outside it by name and for a stated
        # reason, and the statement is checked: an arm that becomes checkable
        # must rejoin the population rather than keep its exemption.
        rejected_tactics(
            "stale-unchecked-dispatch-listing",
            replace_once(
                tactics_original,
                "`Jaune.List.sliceD",
                "`Blanc.Line.Run",
                "stale-unchecked-dispatch-listing",
            ),
            "remove it from UNCHECKED_DISPATCH_ARMS",
        )
        if load_and_validate(test_root) is None:
            raise RecipeError("self-test: trigger-dispatch restoration failed")

        package_root = test_root.joinpath(*JAUNE_PACKAGE_PARTS)
        files = {
            "harness": test_root / SUGGESTIONS_PATH,
            "manifest": test_root / MANIFEST_PATH,
            "lakefile": test_root / LAKEFILE_PATH,
            "tactics": tactics_path,
            "jaune-source": package_root / JAUNE_LIBRARY_DIR / "Surface.lean",
            "jaune-head": package_root / ".git" / "HEAD",
        }
        originals = {
            name: path.read_text(encoding="utf-8") for name, path in files.items()
        }

        def rejected_files(
            label: str, mutations: Dict[str, str], expected: str
        ) -> None:
            """Reject a tree mutated across one or more of ``files``."""
            nonlocal controls
            for name, mutated in mutations.items():
                if mutated == originals[name]:
                    raise RecipeError(
                        f"self-test setup {label}: {name} mutation changed nothing"
                    )
                files[name].write_text(mutated, encoding="utf-8")
            try:
                load_and_validate(test_root)
            except RecipeError as exc:
                if expected not in str(exc):
                    raise RecipeError(
                        f"self-test {label}: expected {expected!r}, got {str(exc)!r}"
                    ) from exc
            else:
                raise RecipeError(f"self-test {label}: mutated tree passed")
            finally:
                for name in mutations:
                    files[name].write_text(originals[name], encoding="utf-8")
            controls += 1

        moved_pin = "f" * 40

        # The Jaune half of the dispatch. A listed name no arm compares against
        # any more, and a name compared against that no listing covers, are two
        # different drifts and both have to fail: the surface is only evidence
        # while it names exactly what the arms dispatch on.
        rejected_files(
            "jaune-surface-name-departed",
            {"tactics": replace_once(
                originals["tactics"],
                "`Jaune.List.sliceD",
                "`Jaune.List.renamedSliceD",
                "jaune-surface-name-departed",
            )},
            "no arm dispatches on",
        )
        rejected_files(
            "jaune-surface-name-unlisted",
            {"tactics": replace_once(
                originals["tactics"],
                "return proofRecipeContainsName `Jaune.List.sliceD target",
                "return proofRecipeContainsName `Jaune.List.sliceD target ||\n"
                "        proofRecipeContainsName `Jaune.List.unlistedSliceD target",
                "jaune-surface-name-unlisted",
            )},
            "is dispatched on but unlisted",
        )
        # The pin bump is the event that kills these arms, and it is the one
        # moment the check can bite with no dependency materialized at all.
        rejected_files(
            "jaune-pin-moved",
            {
                "manifest": originals["manifest"].replace(
                    JAUNE_DISPATCH_PIN, moved_pin
                ),
                "lakefile": originals["lakefile"].replace(
                    JAUNE_DISPATCH_PIN, moved_pin
                ),
            },
            "the Jaune pin moved to",
        )
        rejected_files(
            "jaune-pin-disagreement",
            {"manifest": originals["manifest"].replace(JAUNE_DISPATCH_PIN, moved_pin)},
            f"requires {JAUNE_DISPATCH_PIN}",
        )
        # ... and when the dependency is materialized, the arm that compares
        # against a name the pinned Jaune no longer declares is the original
        # failure, now reachable across the pin.
        rejected_files(
            "jaune-dead-dispatch",
            {"jaune-source": replace_once(
                originals["jaune-source"],
                "def Devm.setStorVal (devm : Devm) : Nat := 0\n",
                "",
                "jaune-dead-dispatch",
            )},
            "can never fire",
        )
        rejected_files(
            "jaune-package-rev-mismatch",
            {"jaune-head": f"{moved_pin}\n"},
            "censusing it would verify the dispatch surface",
        )

        # Liveness is not reachability: the registry/harness enumeration.
        rejected_files(
            "unwitnessed-recipe-unlisted",
            {"harness": replace_once(
                originals["harness"],
                "-- EXPECT: full-length-slice\n",
                "",
                "unwitnessed-recipe-unlisted",
            )},
            "have no case, so nothing shows their triggers can fire",
        )
        rejected_files(
            "stale-unwitnessed-listing",
            {"harness": replace_once(
                originals["harness"],
                "-- EXPECT: full-length-slice\n",
                "-- EXPECT: full-length-slice\n-- EXPECT: constant-error-guard\n",
                "stale-unwitnessed-listing",
            )},
            "now has a harness case or is no longer registered",
        )
        rejected_files(
            "orphan-expect-comment",
            {"harness": replace_once(
                originals["harness"],
                "-- EXPECT: memory-window-transport\n",
                "-- EXPECT: departed-recipe\n",
                "orphan-expect-comment",
            )},
            "does not register",
        )
        # The sharpest of them: the dispatcher's fail-closed wildcard returns
        # false for an unknown trigger, so a misspelled negative control passes
        # by construction and silently stops testing anything.
        rejected_files(
            "vacuous-negative-control",
            {"harness": replace_once(
                originals["harness"],
                'expect_no_recipe_trigger "goal-head:MemImage"',
                'expect_no_recipe_trigger "goal-head:MemImageTypo"',
                "vacuous-negative-control",
            )},
            "is not an arm of",
        )
        rejected_files(
            "reachability-witness-drift",
            {"harness": replace_once(
                originals["harness"],
                'expect_recipe_trigger "goal-head:MemWordAt"',
                'expect_recipe_trigger "goal-head:MemImage"',
                "reachability-witness-drift",
            )},
            "reachability-witness population drifted",
        )
        if load_and_validate(test_root) is None:
            raise RecipeError("self-test: dispatch/harness restoration failed")
        rejected(
            "missing-tactic",
            replace_once(original, "tactic:func_run", "tactic:no_such_tactic", "missing-tactic"),
            "was not found in Blanc Lean sources",
        )
        rejected(
            "missing-declaration",
            replace_once(
                original,
                "declaration:Func.RunCompiledTo",
                "declaration:Func.NoSuchDeclaration",
                "missing-declaration",
            ),
            "was not found",
        )
        rejected(
            "missing-module",
            replace_once(
                original,
                "module:Blanc/ForwardCall.lean",
                "module:Blanc/NoSuchModule.lean",
                "missing-module",
            ),
            "not an exact directory entry",
        )
        outside = Path(directory) / "outside"
        outside.mkdir()
        (outside / "Back").symlink_to(test_root / "Blanc", target_is_directory=True)
        (test_root / "Blanc" / "Out").symlink_to(
            outside, target_is_directory=True
        )
        out_and_back = "Blanc/Out/Back/Forward.lean"
        explicit_controls = (
            ("symbol", lambda: symbol_module_file(
                test_root, out_and_back, "self-test.symbol"
            )),
            ("owner", lambda: owner_module_file(
                test_root, out_and_back, "self-test.owner"
            )),
            ("canonical", lambda: canonical_example_file(
                test_root, out_and_back, "self-test.canonical"
            )),
            ("aggregate", lambda: lean_sources(test_root, out_and_back)),
        )
        for label, action in explicit_controls:
            try:
                action()
            except RecipeError as error:
                if "symbolic-link" not in str(error):
                    raise
            else:
                raise RecipeError(
                    f"self-test out-and-back {label}: invalid path passed"
                )
        print(
            "OK — proof recipe explicit module paths: 4/4 symbol, owner, "
            "canonical-example, and root-aggregate out-and-back controls live"
        )
        alias_root = Path(directory) / "aggregate-alias"
        (alias_root / "Blanc").mkdir(parents=True)
        (alias_root / "Blanc" / "Inside.lean").write_text(
            "def inside := True\n", encoding="utf-8"
        )
        (alias_root / "blanc.lean").write_text(
            "import Blanc.Inside\n", encoding="utf-8"
        )
        try:
            lean_sources(alias_root)
        except RecipeError as error:
            if "exact directory entry" not in str(error):
                raise
        else:
            raise RecipeError("self-test root-aggregate wrong-case alias passed")
        print("OK — proof recipe root aggregate: 1/1 wrong-case alias control live")
    if controls != 25:
        raise RecipeError(f"self-test accounting: expected 25 controls, ran {controls}")


def coverage_phrase(registry: Registry) -> str:
    """Say what the trigger-soundness checks actually covered on this run."""
    surface, resolved, recipes, triggers = registry.coverage
    resolution = (
        f"{resolved}/{surface} resolved against the pinned Jaune"
        if resolved
        else f"0/{surface} resolved (pinned Jaune not materialized)"
    )
    return (
        f"Jaune dispatch surface {resolution}; "
        f"{recipes}/{len(registry.recipes)} recipes exercised by the suggestions "
        f"harness; {triggers} trigger(s) with a reachability witness"
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="repository root (default: parent of scripts/)",
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="validate and byte-compare surfaces")
    mode.add_argument("--write", action="store_true", help="validate and regenerate surfaces")
    mode.add_argument("--self-test", action="store_true", help="run drift/schema/symbol controls")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    root = args.root.resolve()
    try:
        audit_census(Path(__file__).resolve().parents[1])
        if args.self_test:
            self_test(root)
            print(
                "OK — proof recipes self-test: 25/25 drift, schema, trigger, "
                "trigger-dispatch, Jaune-dispatch, harness-enumeration, and symbol "
                "controls live"
            )
            return 0
        registry = load_and_validate(root)
        surfaces = generated_surfaces(registry)
        if args.write:
            for relative, text in surfaces.items():
                path = resolve_bound_file(
                    root, relative, allow_missing=True,
                    site="proof-recipe-generated-write",
                )
                write_atomic(path, text)
            print(
                f"OK — proof recipes: {len(registry.recipes)} recipes validated; "
                f"{coverage_phrase(registry)}; "
                "generated Markdown and Lean lookup written"
            )
            return 0
        failures = compare_surfaces(root, surfaces)
        if failures:
            for failure in failures:
                print(f"PROOF-RECIPES — {failure}")
            print(f"REGRESSION — proof recipes: {len(failures)} generated surface mismatch(es)")
            return 1
        print(
            f"OK — proof recipes: {len(registry.recipes)} recipes validated; "
            f"{coverage_phrase(registry)}; "
            "generated Markdown and Lean lookup match"
        )
        return 0
    except RecipeError as exc:
        print(f"REGRESSION — proof recipes: {exc}")
        return 1
    except ModulePathPolicyError as exc:
        print(f"REGRESSION — proof recipes: module-path policy: {exc}")
        return 1
    except OSError as exc:
        print(f"REGRESSION — proof recipes: filesystem failure: {exc}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
