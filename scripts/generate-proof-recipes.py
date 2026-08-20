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
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple


REGISTRY_PATH = Path("scripts/proof-recipes.toml")
MARKDOWN_PATH = Path("docs/PROOF_RECIPES.md")
LEAN_PATH = Path("Blanc/ProofRecipesGenerated.lean")
TACTICS_PATH = Path("Blanc/Tactics.lean")

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
MODULE_RE = re.compile(r"Blanc/[A-Za-z_][A-Za-z0-9_]*\.lean\Z")
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


def lean_sources(root: Path) -> List[Path]:
    paths = sorted((root / "Blanc").glob("*.lean"))
    if (root / "Blanc.lean").is_file():
        paths.append(root / "Blanc.lean")
    if not paths:
        raise RecipeError(f"no Blanc Lean sources found under {root}")
    return paths


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


def proof_recipe_trigger_inventory(root: Path) -> Set[str]:
    """Read the explicit fail-closed trigger dispatch from Blanc/Tactics.lean."""
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
    triggers: Set[str] = set()
    wildcard_count = 0
    saw_wildcard = False
    for line in body[match_index + 1 :]:
        arm = arm_re.match(line)
        if not arm:
            continue
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
        triggers.add(trigger)
    if wildcard_count != 1:
        raise RecipeError(
            f"{TACTICS_PATH}: proofRecipeTriggerMatches must have exactly one "
            f"fail-closed wildcard, found {wildcard_count}"
        )
    if not triggers:
        raise RecipeError(f"{TACTICS_PATH}: proofRecipeTriggerMatches has no explicit triggers")
    return triggers


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
        if not MODULE_RE.fullmatch(value):
            raise RecipeError(f"{where}: module {value!r} must be a Blanc/*.lean path")
        if not (root / value).is_file():
            raise RecipeError(f"{where}: module {value!r} does not exist")


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
        if not MODULE_RE.fullmatch(owner_module) or not (root / owner_module).is_file():
            raise RecipeError(f"{where}.owner_module: missing Blanc module {owner_module!r}")
        canonical_example = expect_string(raw, "canonical_example", where)
        example_file, separator, example_decl = canonical_example.partition(":")
        if not separator or not MODULE_RE.fullmatch(example_file) or not LEAN_NAME_RE.fullmatch(example_decl):
            raise RecipeError(
                f"{where}.canonical_example: expected Blanc/File.lean:Declaration.Name"
            )
        example_path = (root / example_file).resolve()
        if not example_path.is_file():
            raise RecipeError(f"{where}.canonical_example: file {example_file!r} does not exist")
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
    return Registry(1, top["generated_notice"], tuple(recipes))


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
        "  boundary : String",
        "  deriving Repr, Inhabited",
        "",
        "/-- Recipes generated from `scripts/proof-recipes.toml`, in registry order. -/",
        "def recipes : List Recipe := [",
    ]
    for recipe in registry.recipes:
        trigger_text = ", ".join(lean_string(trigger) for trigger in recipe.triggers)
        out.extend(
            [
                "  {",
                f"    id := {lean_string(recipe.id)}",
                f"    status := {lean_string(recipe.status)}",
                f"    triggers := [{trigger_text}]",
                f"    preferredPath := {lean_string(recipe.preferred_path)}",
                f"    boundary := {lean_string(recipe.boundary)}",
                "  },",
            ]
        )
    out.extend(["]", "", "end Blanc.ProofRecipes", ""])
    return "\n".join(out)


def generated_surfaces(registry: Registry) -> Dict[Path, str]:
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


def compare_surfaces(root: Path, expected: Dict[Path, str]) -> List[str]:
    failures: List[str] = []
    for relative, wanted in expected.items():
        path = root / relative
        try:
            actual = path.read_text(encoding="utf-8")
        except OSError as exc:
            failures.append(f"{relative}: cannot read generated surface: {exc}")
            continue
        if actual != wanted:
            failures.append(
                f"{relative}: generated surface drift; run "
                "python3 scripts/generate-proof-recipes.py --write"
            )
    return failures


def make_self_test_root(root: Path, target: Path) -> None:
    (target / "scripts").mkdir(parents=True)
    (target / "docs").mkdir()
    shutil.copy2(root / REGISTRY_PATH, target / REGISTRY_PATH)
    shutil.copytree(root / "Blanc", target / "Blanc")
    if (root / "Blanc.lean").is_file():
        shutil.copy2(root / "Blanc.lean", target / "Blanc.lean")


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
        if not drift or MARKDOWN_PATH.as_posix() not in drift[0]:
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
            "does not exist",
        )
    if controls != 9:
        raise RecipeError(f"self-test accounting: expected 9 controls, ran {controls}")


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
        if args.self_test:
            self_test(root)
            print("OK — proof recipes self-test: 9/9 drift, schema, trigger, and symbol controls live")
            return 0
        registry = load_and_validate(root)
        surfaces = generated_surfaces(registry)
        if args.write:
            for relative, text in surfaces.items():
                write_atomic(root / relative, text)
            print(
                f"OK — proof recipes: {len(registry.recipes)} recipes validated; "
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
            "generated Markdown and Lean lookup match"
        )
        return 0
    except RecipeError as exc:
        print(f"REGRESSION — proof recipes: {exc}")
        return 1
    except OSError as exc:
        print(f"REGRESSION — proof recipes: filesystem failure: {exc}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
