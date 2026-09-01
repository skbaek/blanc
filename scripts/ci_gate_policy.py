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
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
POLICY = ROOT / "scripts/ci-gate-policy.json"
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
    problems = dependency_problems(registry, ci)
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
