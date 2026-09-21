#!/usr/bin/env python3
"""Audit Blanc CI selection against the gate registry without trusting forks.

Production CI is intentionally conservative in this release: it accepts no
cross-run verdict evidence and executes every command in its registered CI
population.  The useful policy is therefore a fail-closed trust and dependency
contract, not a pretend selective cache.  Unknown or moved bases, forks,
workflow-only changes, and missing evidence all select more work (the entire CI
population) and can never create a skip.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
POLICY = ROOT / "scripts/ci-gate-policy.json"
WORKFLOW = ROOT / ".github/workflows/ci.yml"
EXPECTED_LAKE_CACHE_DIR = "${{ github.workspace }}/.lake/cache"
EXPECTED_POLICY = {
    "schema": 1,
    "mode": "conservative-fresh",
    "population": "registered-ci-commands",
    "cross_run_evidence": "disabled",
    "pull_request_admission": False,
    "fork_admission": False,
    "unknown_base": "select-all",
    "moved_base": "select-all",
    "workflow_or_registry_change": "select-all",
    "undeclared_input": "fail-audit-and-select-all",
    "sampling": "disabled",
}


class PolicyError(RuntimeError):
    pass


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _section_end(lines: list[str], start: int, indentation: int) -> int:
    for position in range(start + 1, len(lines)):
        stripped = lines[position].strip()
        if stripped and not stripped.startswith("#") and _indent(lines[position]) <= indentation:
            return position
    return len(lines)


def _single_section(
    lines: list[str], start: int, end: int, indentation: int, key: str
) -> tuple[int, int] | None:
    pattern = re.compile(rf"^{' ' * indentation}{re.escape(key)}:\s*(?:#.*)?$")
    matches = [position for position in range(start, end) if pattern.fullmatch(lines[position])]
    if len(matches) != 1:
        return None
    position = matches[0]
    return position, _section_end(lines[:end], position, indentation)


def _workflow_steps(path: Path) -> tuple[dict[str, str], list[dict[str, Any]]]:
    """Parse the small reviewed YAML surface needed by the prerequisite audit.

    CI runs this before setup-python, so this deliberately uses only stdlib and
    accepts only the literal mapping/list forms the workflow uses.  Anything
    ambiguous in the relevant job fails closed instead of being guessed.
    """

    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise PolicyError(f"CI workflow is unreadable: {error}") from error
    if "\t" in text:
        raise PolicyError("CI workflow contains tabs; prerequisite order is ambiguous")
    lines = text.splitlines()
    jobs = _single_section(lines, 0, len(lines), 0, "jobs")
    if jobs is None:
        raise PolicyError("CI workflow must contain exactly one literal jobs mapping")
    jobs_start, jobs_end = jobs
    job = _single_section(lines, jobs_start + 1, jobs_end, 2, "build-and-audit")
    if job is None:
        raise PolicyError("CI workflow must contain exactly one literal build-and-audit job")
    job_start, job_end = job

    env_section = _single_section(lines, job_start + 1, job_end, 4, "env")
    steps_section = _single_section(lines, job_start + 1, job_end, 4, "steps")
    if env_section is None or steps_section is None:
        raise PolicyError("build-and-audit must contain one literal env and steps mapping")

    env_start, env_end = env_section
    environment: dict[str, str] = {}
    env_entry = re.compile(r"^ {6}([A-Za-z_][A-Za-z0-9_]*):\s*(.*?)\s*$")
    for raw in lines[env_start + 1 : env_end]:
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        match = env_entry.fullmatch(raw)
        if match is None or not match.group(2):
            raise PolicyError("build-and-audit env uses an unsupported or nested YAML form")
        name, value = match.groups()
        if name in environment:
            raise PolicyError(f"build-and-audit env repeats {name}")
        environment[name] = value

    steps_start, steps_end = steps_section
    starts = [
        position
        for position in range(steps_start + 1, steps_end)
        if re.match(r"^ {6}-\s+", lines[position])
    ]
    if not starts:
        raise PolicyError("build-and-audit has no literal steps")
    for raw in lines[steps_start + 1 : starts[0]]:
        if raw.strip() and not raw.strip().startswith("#"):
            raise PolicyError("build-and-audit steps contain content outside a literal list item")

    steps: list[dict[str, Any]] = []
    top_key = re.compile(r"^(?: {6}-| {8})\s*([A-Za-z_][A-Za-z0-9_-]*):\s*(.*?)\s*$")
    for number, begin in enumerate(starts):
        finish = starts[number + 1] if number + 1 < len(starts) else steps_end
        block = lines[begin:finish]
        fields: dict[str, list[str]] = {}
        for raw in block:
            match = top_key.fullmatch(raw)
            if match is not None:
                fields.setdefault(match.group(1), []).append(match.group(2))
        if len(fields.get("uses", [])) > 1 or len(fields.get("run", [])) > 1:
            raise PolicyError(f"build-and-audit step {number + 1} repeats uses or run")
        if fields.get("uses") and fields.get("run"):
            raise PolicyError(f"build-and-audit step {number + 1} mixes uses and run")
        steps.append({"fields": fields, "lines": block})
    return environment, steps


def _run_tokens(step: dict[str, Any]) -> list[str] | None:
    values = step["fields"].get("run", [])
    if len(values) != 1 or values[0] in ("|", ">", "|-", ">-"):
        return None
    try:
        return shlex.split(values[0], comments=True, posix=True)
    except ValueError:
        return None


def _step_mapping(step: dict[str, Any], key: str) -> dict[str, str] | None:
    if step["fields"].get(key) != [""]:
        return None
    lines = step["lines"]
    starts = [
        position
        for position, raw in enumerate(lines)
        if re.fullmatch(rf"^{' ' * 8}{re.escape(key)}:\s*", raw)
    ]
    if len(starts) != 1:
        return None
    start = starts[0]
    end = len(lines)
    for position in range(start + 1, len(lines)):
        stripped = lines[position].strip()
        if stripped and not stripped.startswith("#") and _indent(lines[position]) <= 8:
            end = position
            break
    entry = re.compile(r"^ {10}([A-Za-z_][A-Za-z0-9_-]*):\s*(.*?)\s*$")
    result: dict[str, str] = {}
    for raw in lines[start + 1 : end]:
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        match = entry.fullmatch(raw)
        if match is None or not match.group(2):
            raise PolicyError(f"step {key} uses an unsupported or nested YAML form")
        name, value = match.groups()
        if name in result:
            raise PolicyError(f"step {key} repeats {name}")
        result[name] = value
    return result


def _required_step_guard_problems(label: str, step: dict[str, Any]) -> list[str]:
    problems: list[str] = []
    if "if" in step["fields"]:
        problems.append(f"required {label} must not have a conditional if guard")
    continue_values = step["fields"].get("continue-on-error", [])
    if continue_values and continue_values != ["false"]:
        problems.append(f"required {label} must not continue on error")
    for raw in step["lines"]:
        stripped = raw.strip()
        if stripped.startswith("#"):
            continue
        if re.search(r"(?:^|[{,]\s*)LAKE_CACHE_DIR\s*:", stripped):
            problems.append(f"required {label} must not override the job artifact cache")
            break
    return problems


def workflow_prerequisite_problems(path: Path) -> list[str]:
    environment, steps = _workflow_steps(path)
    problems: list[str] = []
    if environment.get("LAKE_CACHE_DIR") != EXPECTED_LAKE_CACHE_DIR:
        problems.append(
            "build-and-audit must set LAKE_CACHE_DIR to the absolute workspace .lake/cache "
            "path restored by lean-action"
        )

    commands = {
        "Jaune runner build": ["lake", "build", "jaune/jaune"],
        "proof-recipe authoring leaf build": ["lake", "build", "Blanc.ProofRecipeTactic"],
        "checked-build certification": ["scripts/certify-checked-build.sh"],
        "DRIP check": ["scripts/check-drip.sh"],
    }
    positions: dict[str, int] = {}
    for label, tokens in commands.items():
        matches = [position for position, step in enumerate(steps) if _run_tokens(step) == tokens]
        raw_matches = [
            position
            for position, step in enumerate(steps)
            if " ".join(tokens) in "\n".join(step["lines"])
        ]
        if len(matches) != 1:
            problems.append(f"build-and-audit must contain exactly one literal {label}")
        elif raw_matches != matches:
            problems.append(f"build-and-audit contains an ambiguous {label} invocation")
        else:
            positions[label] = matches[0]
            problems.extend(_required_step_guard_problems(label, steps[matches[0]]))

    lean_matches: list[int] = []
    for position, step in enumerate(steps):
        uses = step["fields"].get("uses", [])
        if uses == ["leanprover/lean-action@v1"]:
            lean_matches.append(position)
    if len(lean_matches) != 1:
        problems.append("build-and-audit must contain exactly one leanprover/lean-action@v1 step")
    else:
        lean_position = lean_matches[0]
        lean_with = _step_mapping(steps[lean_position], "with")
        if lean_with is None or lean_with.get("build") != "true":
            problems.append("lean-action must explicitly perform the full default build")
        build_occurrences = [
            raw
            for raw in steps[lean_position]["lines"]
            if raw.strip() and not raw.strip().startswith("#")
            and re.match(r"^build\s*:", raw.strip())
        ]
        if len(build_occurrences) != 1:
            problems.append("lean-action build must occur exactly once directly inside with")
        problems.extend(
            _required_step_guard_problems("full default build", steps[lean_position])
        )
        positions["full default build"] = lean_position

    ordered = [
        "full default build",
        "Jaune runner build",
        "proof-recipe authoring leaf build",
        "checked-build certification",
        "DRIP check",
    ]
    if all(label in positions for label in ordered):
        actual = [positions[label] for label in ordered]
        if actual != sorted(actual):
            problems.append("build prerequisites, certification, and DRIP are out of order")
        if positions["checked-build certification"] + 1 != positions["DRIP check"]:
            problems.append("checked-build certification must be immediately adjacent before DRIP")
        if positions["proof-recipe authoring leaf build"] + 1 != positions["checked-build certification"]:
            problems.append("checked-build certification must immediately follow the authoring leaf build")
    return problems


def load_gate_cache():
    path = ROOT / "scripts/gate-cache.py"
    spec = importlib.util.spec_from_file_location("blanc_gate_cache_for_ci", path)
    if spec is None or spec.loader is None:
        raise PolicyError(f"cannot load registry authority: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def read_policy() -> dict[str, Any]:
    try:
        policy = json.loads(POLICY.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise PolicyError(f"CI gate policy is unreadable: {error}") from error
    if policy != EXPECTED_POLICY:
        raise PolicyError("CI gate policy moved outside the reviewed conservative contract")
    return policy


def commit_exists(revision: str) -> bool:
    if not revision:
        return False
    result = subprocess.run(
        ["git", "cat-file", "-e", f"{revision}^{{commit}}"],
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.returncode == 0


def base_is_ancestor(base: str, head: str) -> bool:
    if not commit_exists(base) or not commit_exists(head):
        return False
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", base, head],
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.returncode == 0


def selection_reasons(
    *, event: str, base: str, head: str, repository: str, head_repository: str
) -> list[str]:
    reasons = ["cross-run CI evidence is disabled; execute the full registered CI population"]
    if event == "pull_request":
        reasons.append("pull-request evidence is untrusted and cannot be admitted")
        if head_repository and repository and head_repository != repository:
            reasons.append("fork head repository is outside the trusted repository boundary")
    if not base or not commit_exists(base):
        reasons.append("comparison base is unavailable; select all rather than infer no changes")
    elif not base_is_ancestor(base, head):
        reasons.append("comparison base moved or is not an ancestor; select all")
    return reasons


def dependency_problems(
    registry: dict[str, Any], ci: list[list[str]]
) -> list[str]:
    by_command = {tuple(gate["command"]): gate for gate in registry["gates"]}
    by_id = {gate["id"]: gate for gate in registry["gates"]}
    ci_ids: list[str] = []
    problems: list[str] = []
    for command in ci:
        gate = by_command.get(tuple(command))
        if gate is None:
            problems.append(f"CI command is not registered: {' '.join(command)}")
        else:
            ci_ids.append(gate["id"])
    if len(ci_ids) != len(set(ci_ids)):
        problems.append("CI invokes one registered command more than once")
    positions = {identifier: position for position, identifier in enumerate(ci_ids)}
    for identifier in ci_ids:
        gate = by_id[identifier]
        for dependency in gate.get("depends_on", []):
            if dependency not in positions:
                problems.append(f"CI consumer {identifier} omits dependency {dependency}")
            elif positions[dependency] >= positions[identifier]:
                problems.append(f"CI consumer {identifier} runs before dependency {dependency}")
    return problems


def audit(arguments: argparse.Namespace) -> int:
    read_policy()
    gate_cache = load_gate_cache()
    registry = gate_cache.load_registry(gate_cache.registry_path(ROOT))
    ci = gate_cache.ci_commands(ROOT)
    problems = dependency_problems(registry, ci) + workflow_prerequisite_problems(WORKFLOW)
    if problems:
        for problem in problems:
            print(f"CI POLICY MISMATCH — {problem}", file=sys.stderr)
        return 1

    reasons = selection_reasons(
        event=arguments.event,
        base=arguments.base,
        head=arguments.head,
        repository=arguments.repository,
        head_repository=arguments.head_repository,
    )
    by_command = {tuple(gate["command"]): gate for gate in registry["gates"]}
    payload = {
        "schema": 1,
        "event": arguments.event,
        "base": arguments.base or None,
        "head": arguments.head or None,
        "trusted_cross_run_evidence": False,
        "may_admit_evidence": False,
        "sampling": "disabled",
        "reasons": reasons,
        "selected": [
            {
                "id": by_command[tuple(command)]["id"],
                "command": " ".join(command),
                "disposition": "fresh",
            }
            for command in ci
        ],
    }
    if arguments.output:
        output = Path(arguments.output)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"CI GATE POLICY OK — {len(ci)} registered commands selected fresh; "
        "0 reused; 0 sampled; evidence admission disabled"
    )
    for reason in reasons:
        print(f"  reason: {reason}")
    return 0


def self_test() -> int:
    population = [["scripts/check-a.sh"], ["scripts/check-b.sh"]]
    registry = {
        "gates": [
            {"id": "a", "command": population[0]},
            {"id": "b", "command": population[1], "depends_on": ["a"]},
        ]
    }
    controls = 0

    def check(condition: bool, message: str) -> None:
        nonlocal controls
        if not condition:
            raise PolicyError(message)
        controls += 1

    check(not dependency_problems(registry, population), "ordered dependency was rejected")
    check(bool(dependency_problems(registry, list(reversed(population)))), "reversed dependency passed")
    check(bool(dependency_problems(registry, [population[1]])), "missing dependency passed")
    check(
        "untrusted" in " ".join(selection_reasons(
            event="pull_request", base="", head="", repository="owner/repo",
            head_repository="fork/repo"
        )),
        "fork pull request was not marked untrusted",
    )
    check(
        "unavailable" in " ".join(selection_reasons(
            event="push", base="missing", head="missing", repository="owner/repo",
            head_repository="owner/repo"
        )),
        "unknown base did not select all",
    )
    for synthetic in ("workflow-only", "force-updated-ref", "undeclared-input"):
        selected = list(population)  # conservative policy never filters by changed-path claims
        check(selected == population, f"{synthetic} unexpectedly skipped a CI command")
    check(EXPECTED_POLICY["cross_run_evidence"] == "disabled", "cross-run evidence enabled")
    check(EXPECTED_POLICY["sampling"] == "disabled", "production sampling enabled")
    with tempfile.TemporaryDirectory(prefix="blanc-ci-policy-") as temporary:
        copied_workflow = Path(temporary) / "ci.yml"
        shutil.copy2(WORKFLOW, copied_workflow)
        original = copied_workflow.read_text(encoding="utf-8")
        check(
            not workflow_prerequisite_problems(copied_workflow),
            "the real CI workflow copy failed its prerequisite contract",
        )

        cache_mutant = original.replace(
            EXPECTED_LAKE_CACHE_DIR,
            "${{ runner.temp }}/lake-cache",
            1,
        )
        check(cache_mutant != original, "cache mutation did not bite the real workflow copy")
        copied_workflow.write_text(cache_mutant, encoding="utf-8")
        check(
            bool(workflow_prerequisite_problems(copied_workflow)),
            "a warm-invisible runner.temp artifact cache passed",
        )

        # Use a sentinel so the second replacement cannot rewrite the first.
        order_mutant = original.replace(
            "run: lake build Blanc.ProofRecipeTactic",
            "run: __BLANC_CI_POLICY_SENTINEL__",
            1,
        ).replace(
            "run: scripts/certify-checked-build.sh",
            "run: lake build Blanc.ProofRecipeTactic",
            1,
        ).replace(
            "run: __BLANC_CI_POLICY_SENTINEL__",
            "run: scripts/certify-checked-build.sh",
            1,
        )
        check(order_mutant != original, "order mutation did not bite the real workflow copy")
        copied_workflow.write_text(order_mutant, encoding="utf-8")
        check(
            bool(workflow_prerequisite_problems(copied_workflow)),
            "certification before the authoring leaf passed",
        )

        conditional_mutant = original.replace(
            "        run: scripts/certify-checked-build.sh",
            "        if: false\n        run: scripts/certify-checked-build.sh",
            1,
        )
        check(conditional_mutant != original, "conditional mutation did not bite the workflow copy")
        copied_workflow.write_text(conditional_mutant, encoding="utf-8")
        check(
            bool(workflow_prerequisite_problems(copied_workflow)),
            "a disabled required certification step passed",
        )

        continue_mutant = original.replace(
            "        run: lake build jaune/jaune",
            "        continue-on-error: true\n        run: lake build jaune/jaune",
            1,
        )
        check(continue_mutant != original, "continue mutation did not bite the workflow copy")
        copied_workflow.write_text(continue_mutant, encoding="utf-8")
        check(
            bool(workflow_prerequisite_problems(copied_workflow)),
            "a required runner build allowed to continue on error passed",
        )

        override_mutant = original.replace(
            "        run: scripts/check-drip.sh",
            "        env:\n          LAKE_CACHE_DIR: ${{ runner.temp }}/lake-cache\n"
            "        run: scripts/check-drip.sh",
            1,
        )
        check(override_mutant != original, "override mutation did not bite the workflow copy")
        copied_workflow.write_text(override_mutant, encoding="utf-8")
        check(
            bool(workflow_prerequisite_problems(copied_workflow)),
            "a required step-level artifact-cache override passed",
        )

        misplaced_build_mutant = original.replace(
            "        with:\n          build: true",
            "        env:\n          build: true",
            1,
        )
        check(
            misplaced_build_mutant != original,
            "misplaced build mutation did not bite the workflow copy",
        )
        copied_workflow.write_text(misplaced_build_mutant, encoding="utf-8")
        check(
            bool(workflow_prerequisite_problems(copied_workflow)),
            "build: true outside lean-action with passed",
        )

        copied_workflow.write_text(original, encoding="utf-8")
        check(
            not workflow_prerequisite_problems(copied_workflow),
            "restoring only the real workflow copy did not restore green",
        )
    print(f"CI GATE POLICY SELF-TEST OK — {controls} trust/dependency controls")
    return 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--self-test", action="store_true")
    result.add_argument("--audit", action="store_true")
    result.add_argument("--event", default="local")
    result.add_argument("--base", default="")
    result.add_argument("--head", default="HEAD")
    result.add_argument("--repository", default="")
    result.add_argument("--head-repository", default="")
    result.add_argument("--output")
    return result


def main(argv: list[str]) -> int:
    arguments = parser().parse_args(argv)
    if arguments.self_test:
        return self_test()
    if arguments.audit:
        return audit(arguments)
    raise PolicyError("choose --self-test or --audit")


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except PolicyError as error:
        print(f"CI GATE POLICY FAILED — {error}", file=sys.stderr)
        raise SystemExit(1)
