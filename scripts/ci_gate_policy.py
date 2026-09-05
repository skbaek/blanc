#!/usr/bin/env python3
"""Fail-closed trust, population, and topology policy for pinned-main CI."""

from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import re
import shlex
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
POLICY = ROOT / "scripts/ci-gate-policy.json"
TOPOLOGY = ROOT / "scripts/ci-topology.json"
WORKFLOW = ROOT / ".github/workflows/ci.yml"

CACHE_KEY = (
    "lake-${{ runner.os }}-${{ runner.arch}}-"
    "${{ hashFiles('lean-toolchain') }}-"
    "${{ hashFiles('lake-manifest.json') }}-${{ github.sha }}"
)
LEAN_ACTION = "leanprover/lean-action@50fcf42d2e460296f1a34b402e990d1b24f8b596"

REQUIRED_GATE_IDS = [
    "doc-counts",
    "lido-circuit-breaker-assurance",
    "beacon-deposit-assurance",
    "proof-recipes",
    "proof-debt",
    "proof-module-size",
    "proof-duplication",
    "proof-residue",
    "layering",
    "extraction-ownership",
    "trust-surface",
    "weth10-reference",
    "lido-reference",
    "lido-twg-census",
    "lido-twg-reference",
    "lido-ossifiable-proxy-reference",
    "lido-ossifiable-proxy-performance",
    "lido-ossifiable-proxy-artifacts",
    "weth-coverage",
    "fmint-coverage",
    "transient-settlement-static",
    "execution-occurrence-static",
    "lido-registry-static",
    "proxy-pair-upgrade-static",
    "cycle-write-free-static",
    "execution-settlement",
    "execution-occurrence-semantic",
    "cycle-write-free-semantic",
    "transient-settlement-semantic",
    "proxy-pair-upgrade-semantic",
    "lido-registry-semantic",
    "lido-enumeration",
    "lido-access",
    "lido-history",
    "lido-artifact-profile",
    "lido-constructor",
    "lido-runtime-errors",
    "error-data",
    "axiom-audit",
    "claims",
    "lido-deployment",
    "weth-fixtures",
    "prorata-fixtures",
    "fmint-fixtures",
]

EXPECTED_JOBS = {
    "policy": ("CI policy", "policy", [], 10),
    "source-trust": ("Source and trust static checks", "static-independent", ["policy"], 10),
    "reference-locks": ("Offline reference and artifact locks", "static-independent", ["policy"], 10),
    "execution-static": ("Execution static assurances", "static-independent", ["policy"], 10),
    "cycle-static": ("Cycle-safe static assurance", "static-independent", ["policy"], 10),
    "build": (
        "Single shared Lean and Jaune build",
        "single-build",
        ["source-trust", "reference-locks", "execution-static", "cycle-static"],
        60,
    ),
    "execution-semantic": ("Execution semantic regressions", "semantic-independent", ["build"], 30),
    "contract-semantic": (
        "Contract proofs and generated artifact semantics",
        "semantic-independent",
        ["build"],
        30,
    ),
    "deployment-fixtures": (
        "Pinned EELS deployment and Jaune fixture replays",
        "semantic-independent",
        ["build"],
        30,
    ),
}

EXPECTED_POLICY = {
    "schema": 2,
    "mode": "conservative-fresh",
    "population": "scripts/ci-topology.json",
    "cross_run_evidence": "disabled",
    "pull_request_admission": False,
    "fork_admission": False,
    "unknown_base": "select-all",
    "moved_base": "select-all",
    "workflow_or_registry_change": "fail-audit-and-select-all",
    "undeclared_input": "fail-audit-and-select-all",
    "sampling": "disabled",
    "artifact_transfer": "exact-commit-cache-fail-closed",
    "full_build_count": 1,
    "required_jobs": list(EXPECTED_JOBS),
    "required_gate_ids": REQUIRED_GATE_IDS,
}

PURPOSES = {
    "required-per-change-trust",
    "build-proof",
    "compiled-semantic-regression",
    "offline-fixture-replay",
    "infrastructure",
}

EXPECTED_WORKFLOW_PREFIX = """name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]
  workflow_dispatch:
    inputs:
      cold_build:
        description: Rebuild Blanc and Jaune without the GitHub build cache
        type: boolean
        default: false
        required: false

permissions:
  contents: read

concurrency:
  group: ${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true

jobs:""".splitlines()


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


def read_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise PolicyError(f"{label} is unreadable: {error}") from error
    if not isinstance(value, dict):
        raise PolicyError(f"{label} is not a JSON object")
    return value


def read_policy() -> dict[str, Any]:
    policy = read_json(POLICY, "CI gate policy")
    if policy != EXPECTED_POLICY:
        raise PolicyError("CI gate policy moved outside the reviewed conservative contract")
    return policy


def read_topology() -> dict[str, Any]:
    topology = read_json(TOPOLOGY, "CI topology")
    expected_keys = {
        "schema",
        "workflow",
        "purpose",
        "input_authority",
        "cost_authority",
        "cache_key",
        "required_gate_count",
        "jobs",
        "forward_composition",
    }
    if set(topology) != expected_keys or topology.get("schema") != 1:
        raise PolicyError("CI topology schema/keys are not exact")
    if topology["workflow"] != ".github/workflows/ci.yml":
        raise PolicyError("CI topology points at an unexpected workflow")
    if topology["input_authority"] != "scripts/gate-registry.json":
        raise PolicyError("CI topology moved its input authority")
    if topology["cost_authority"] != "scripts/GATES.md":
        raise PolicyError("CI topology moved its cost authority")
    if topology["cache_key"] != CACHE_KEY:
        raise PolicyError("CI topology moved its exact build-cache key")
    if not isinstance(topology.get("jobs"), list) or not topology["jobs"]:
        raise PolicyError("CI topology has no jobs")
    return topology


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
    reasons = ["cross-run CI verdict evidence is disabled; execute every topology gate fresh"]
    if event == "pull_request":
        reasons.append("pull-request verdict evidence is untrusted and cannot be admitted")
        if head_repository and repository and head_repository != repository:
            reasons.append("fork head repository is outside the trusted repository boundary")
    if not base or not commit_exists(base):
        reasons.append("comparison base is unavailable; select all rather than infer no changes")
    elif not base_is_ancestor(base, head):
        reasons.append("comparison base moved or is not an ancestor; select all")
    return reasons


def catalogue_costs() -> dict[tuple[str, ...], str]:
    result: dict[tuple[str, ...], str] = {}
    try:
        lines = (ROOT / "scripts/GATES.md").read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as error:
        raise PolicyError(f"cannot read gate catalogue costs: {error}") from error
    for line in lines:
        if not line.startswith("| `"):
            continue
        columns = [column.strip() for column in line.split("|")[1:-1]]
        if len(columns) < 4:
            continue
        match = re.fullmatch(r"`([^`]+)`", columns[0])
        if match:
            result[tuple(shlex.split(match.group(1)))] = columns[-1]
    return result


def expected_infrastructure(identifier: str) -> dict[str, Any] | None:
    values: dict[str, dict[str, Any]] = {
        "checkout": {
            "name": "Checkout exact candidate",
            "kind": "action",
            "uses": "actions/checkout@v6",
            "with": {"fetch-depth": "0"},
        },
        "policy-self-test": {
            "name": "CI topology mutation controls",
            "kind": "command",
            "run": "python3 scripts/ci_gate_policy.py --self-test",
        },
        "policy-audit": {
            "name": "CI topology audit and fresh selection",
            "kind": "command",
            "run": (
                'python3 scripts/ci_gate_policy.py --audit --event "$BLANC_CI_EVENT" '
                '--base "$BLANC_CI_BASE" --head "$BLANC_CI_HEAD" '
                '--repository "$BLANC_CI_REPOSITORY" '
                '--head-repository "$BLANC_CI_HEAD_REPOSITORY" '
                "--output .lake/ci-gate-selection.json"
            ),
            "env": {
                "BLANC_CI_EVENT": "${{ github.event_name }}",
                "BLANC_CI_BASE": "${{ github.event.pull_request.base.sha || github.event.before }}",
                "BLANC_CI_HEAD": "${{ github.sha }}",
                "BLANC_CI_REPOSITORY": "${{ github.repository }}",
                "BLANC_CI_HEAD_REPOSITORY": (
                    "${{ github.event.pull_request.head.repo.full_name || github.repository }}"
                ),
            },
        },
        "recipe-base": {
            "name": "Bind recipe comparison base",
            "kind": "command",
            "run": "git show-ref --verify --quiet refs/heads/main || git branch main refs/remotes/origin/main",
        },
        "full-build": {
            "name": "Build Blanc and the Jaune fixture runner once",
            "kind": "action",
            "uses": LEAN_ACTION,
            "with": {"build": "true", "build-args": "Blanc Blanc.ProofRecipeTactic jaune/jaune",
                     "use-github-cache": "${{ !(github.event_name == 'workflow_dispatch' && inputs.cold_build) }}"},
        },
        "save-cold-build": {
            "name": "Save exact cold build output",
            "kind": "action",
            "if": "${{ github.event_name == 'workflow_dispatch' && inputs.cold_build }}",
            "uses": "actions/cache/save@v5",
            "with": {"path": ".lake", "key": CACHE_KEY},
        },
        "restore-build": {
            "name": "Restore exact build output",
            "kind": "action",
            "uses": "actions/cache/restore@v5",
            "with": {"path": ".lake", "key": CACHE_KEY, "fail-on-cache-miss": "true"},
        },
        "install-toolchain": {
            "name": "Install Lean toolchain without rebuilding",
            "kind": "action",
            "uses": LEAN_ACTION,
            "with": {
                "build": "false",
                "use-github-cache": "false",
                "use-mathlib-cache": "false",
            },
        },
        "python-runtime": {
            "name": "Install Python 3.11",
            "kind": "action",
            "uses": "actions/setup-python@v6",
            "with": {"python-version": "3.11"},
        },
        "eels-checkout": {
            "name": "Checkout pinned execution-specs",
            "kind": "action",
            "uses": "actions/checkout@v6",
            "with": {
                "repository": "ethereum/execution-specs",
                "ref": "4198b9c5996713b268aed602739d5aa40e277694",
                "path": "execution-specs",
                "fetch-depth": "1",
            },
        },
        "eels-venv": {
            "name": "Create pinned EELS virtual environment",
            "kind": "command",
            "run": "python -m venv execution-specs/venv",
        },
        "eels-install": {
            "name": "Install pinned execution-specs environment",
            "kind": "command",
            "run": (
                "execution-specs/venv/bin/python -m pip install "
                "--disable-pip-version-check -e execution-specs"
            ),
        },
    }
    return values.get(identifier)


def semantic_step(step: dict[str, Any]) -> dict[str, Any]:
    """Fields that can change execution, excluding census prose."""
    return {
        key: step[key]
        for key in ("name", "kind", "uses", "with", "run", "env", "if")
        if key in step
    }


def job_ancestors(jobs: dict[str, dict[str, Any]]) -> tuple[dict[str, set[str]], list[str]]:
    result: dict[str, set[str]] = {}
    visiting: set[str] = set()
    problems: list[str] = []

    def visit(identifier: str) -> set[str]:
        if identifier in result:
            return result[identifier]
        if identifier in visiting:
            problems.append(f"job dependency cycle reaches {identifier}")
            return set()
        visiting.add(identifier)
        found: set[str] = set()
        for dependency in jobs[identifier].get("needs", []):
            if dependency not in jobs:
                problems.append(f"job {identifier} needs absent job {dependency}")
                continue
            found.add(dependency)
            found.update(visit(dependency))
        visiting.remove(identifier)
        result[identifier] = found
        return found

    for identifier in jobs:
        visit(identifier)
    return result, problems


def topology_problems(
    topology: dict[str, Any], registry: dict[str, Any], policy: dict[str, Any]
) -> list[str]:
    problems: list[str] = []
    jobs_list = topology.get("jobs", [])
    jobs = {
        job.get("id"): job
        for job in jobs_list
        if isinstance(job, dict) and isinstance(job.get("id"), str)
    }
    if len(jobs) != len(jobs_list):
        problems.append("topology has a missing or duplicate job id")
        return problems
    if list(jobs) != policy["required_jobs"]:
        problems.append("topology job population/order differs from the policy authority")

    for identifier, expected in EXPECTED_JOBS.items():
        job = jobs.get(identifier)
        if job is None:
            continue
        name, role, needs, timeout = expected
        expected_header = {
            "name": name,
            "role": role,
            "runs_on": "ubuntu-24.04",
            "timeout_minutes": timeout,
            "needs": needs,
            "surface": "pinned-main-per-change",
        }
        actual_header = {key: job.get(key) for key in expected_header}
        if actual_header != expected_header:
            problems.append(f"job {identifier} header/dependencies moved: {actual_header}")
        if set(job) != {
            "id", "name", "role", "runs_on", "timeout_minutes", "needs", "surface", "steps"
        }:
            problems.append(f"job {identifier} schema/keys are not exact")
        if not isinstance(job.get("steps"), list) or not job["steps"]:
            problems.append(f"job {identifier} has no steps")

    by_id = {gate["id"]: gate for gate in registry["gates"]}
    costs = catalogue_costs()
    gate_locations: dict[str, tuple[str, int]] = {}
    gate_sequence: list[str] = []
    full_builds = 0

    for job_id, job in jobs.items():
        seen_step_ids: set[str] = set()
        for position, step in enumerate(job.get("steps", [])):
            if not isinstance(step, dict) or not isinstance(step.get("id"), str):
                problems.append(f"job {job_id} has a step without an id")
                continue
            step_id = step["id"]
            if step_id in seen_step_ids:
                problems.append(f"job {job_id} duplicates step id {step_id}")
            seen_step_ids.add(step_id)
            if step.get("purpose") not in PURPOSES:
                problems.append(f"step {job_id}/{step_id} has unknown purpose {step.get('purpose')}")
            kind = step.get("kind")
            if kind == "gate":
                gate_id = step.get("gate_id")
                gate_sequence.append(gate_id)
                if gate_id in gate_locations:
                    problems.append(f"topology invokes gate {gate_id} more than once")
                gate_locations[gate_id] = (job_id, position)
                gate = by_id.get(gate_id)
                if gate is None:
                    problems.append(f"topology invokes unknown gate {gate_id}")
                    continue
                if step_id != gate_id:
                    problems.append(f"gate step {job_id}/{step_id} does not use its gate id")
                if step.get("input_authority") != "scripts/gate-registry.json":
                    problems.append(f"gate {gate_id} moved its input authority")
                if step.get("cost_authority") != "scripts/GATES.md":
                    problems.append(f"gate {gate_id} moved its cost authority")
                expected_gate_keys = {
                    "id", "name", "kind", "purpose", "gate_id",
                    "input_authority", "cost_authority",
                }
                if "env" in step:
                    expected_gate_keys.add("env")
                if set(step) != expected_gate_keys:
                    problems.append(f"gate step {job_id}/{step_id} schema/keys are not exact")
                if tuple(gate["command"]) not in costs:
                    problems.append(f"gate {gate_id} has no catalogue cost row")
                if job.get("role") == "static-independent":
                    input_kinds = set(gate.get("inputs", {}))
                    if input_kinds & {"lean_entries", "lean_modules", "material_output"}:
                        problems.append(f"static job {job_id} contains build-dependent gate {gate_id}")
            elif kind in {"action", "command"}:
                expected = expected_infrastructure(step_id)
                if expected is None:
                    problems.append(f"unregistered CI infrastructure step {job_id}/{step_id}")
                elif semantic_step(step) != expected:
                    problems.append(f"infrastructure step {job_id}/{step_id} moved")
                if step_id == "full-build":
                    full_builds += 1
            else:
                problems.append(f"step {job_id}/{step_id} has unknown kind {kind}")

    if topology.get("required_gate_count") != len(REQUIRED_GATE_IDS):
        problems.append("topology required-gate count moved")
    if gate_sequence != policy["required_gate_ids"]:
        missing = [gate for gate in policy["required_gate_ids"] if gate not in gate_sequence]
        extra = [gate for gate in gate_sequence if gate not in policy["required_gate_ids"]]
        problems.append(
            f"topology gate population/order differs from policy: missing={missing}, extra={extra}"
        )
    if len(gate_sequence) != topology.get("required_gate_count"):
        problems.append("topology gate population does not match its pinned count")
    if full_builds != policy["full_build_count"]:
        problems.append(f"topology performs {full_builds} full builds, expected one")

    # Infrastructure is load-bearing too: coordinated workflow/inventory deletion
    # cannot erase a prerequisite while leaving every gate row present.
    infrastructure_ids = {
        "policy": ["checkout", "policy-self-test", "policy-audit"],
        "source-trust": ["checkout", "recipe-base"],
        "reference-locks": ["checkout"],
        "execution-static": ["checkout"],
        "cycle-static": ["checkout"],
        "build": ["checkout", "full-build", "save-cold-build"],
        "execution-semantic": ["checkout", "restore-build", "install-toolchain"],
        "contract-semantic": ["checkout", "restore-build", "install-toolchain"],
        "deployment-fixtures": ["checkout", "restore-build", "install-toolchain", "python-runtime",
                                "eels-checkout", "eels-venv", "eels-install"],
    }
    for job_id, required in infrastructure_ids.items():
        steps = jobs.get(job_id, {}).get("steps", [])
        actual_ids = [step.get("id") for step in steps if step.get("kind") != "gate"]
        if actual_ids != required:
            problems.append(f"job {job_id} infrastructure population/order moved")
    source_ids = [step.get("id") for step in jobs.get("source-trust", {}).get("steps", [])]
    if source_ids[:2] != ["checkout", "recipe-base"]:
        problems.append("recipe comparison base is not bound before source gates")

    ancestors, dag_problems = job_ancestors(jobs)
    problems.extend(dag_problems)
    for gate_id, (job_id, position) in gate_locations.items():
        gate = by_id.get(gate_id)
        if gate is None:
            continue
        for dependency in gate.get("depends_on", []):
            location = gate_locations.get(dependency)
            if location is None:
                problems.append(f"CI consumer {gate_id} omits dependency {dependency}")
                continue
            dep_job, dep_position = location
            if dep_job == job_id and dep_position >= position:
                problems.append(f"CI consumer {gate_id} runs before dependency {dependency}")
            elif dep_job != job_id and dep_job not in ancestors.get(job_id, set()):
                problems.append(
                    f"CI consumer {gate_id} is not downstream of dependency {dependency}"
                )

    static_jobs = {
        identifier for identifier, job in jobs.items()
        if job.get("role") == "static-independent"
    }
    for identifier in static_jobs:
        if jobs[identifier].get("needs") != ["policy"]:
            problems.append(f"independent static lane {identifier} is coupled to a sibling")
    if jobs.get("build", {}).get("needs") != [
        "source-trust", "reference-locks", "execution-static", "cycle-static"
    ]:
        problems.append("build does not wait for every independent static lane")

    for identifier, job in jobs.items():
        if job.get("role") != "semantic-independent":
            continue
        if job.get("needs") != ["build"]:
            problems.append(f"semantic lane {identifier} can run without the single build")
        ids = [step.get("id") for step in job.get("steps", [])]
        if ids[:3] != ["checkout", "restore-build", "install-toolchain"]:
            problems.append(f"semantic lane {identifier} does not restore before consuming")
        restore = next((step for step in job["steps"] if step.get("id") == "restore-build"), None)
        if not restore or restore.get("with") != {
            "path": ".lake", "key": CACHE_KEY, "fail-on-cache-miss": "true"
        }:
            problems.append(f"semantic lane {identifier} has a permissive or non-exact cache restore")
        toolchain = next(
            (step for step in job["steps"] if step.get("id") == "install-toolchain"), None
        )
        if not toolchain or toolchain.get("with") != {
            "build": "false",
            "use-github-cache": "false",
            "use-mathlib-cache": "false",
        }:
            problems.append(f"semantic lane {identifier} can rebuild or admit fallback cache state")

    return problems


def parse_scalar(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
        return value[1:-1]
    return value


def parse_needs(value: str) -> list[str]:
    value = value.strip()
    if not (value.startswith("[") and value.endswith("]")):
        raise PolicyError(f"workflow needs must be an explicit inline list: {value}")
    inside = value[1:-1].strip()
    return [] if not inside else [item.strip() for item in inside.split(",")]


def parse_workflow(source: str | None = None) -> list[dict[str, Any]]:
    if source is None:
        try:
            source = WORKFLOW.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise PolicyError(f"cannot read CI workflow: {error}") from error
    lines = source.splitlines()
    try:
        jobs_line = lines.index("jobs:")
    except ValueError as error:
        raise PolicyError("CI workflow has no exact jobs block") from error
    if lines[: jobs_line + 1] != EXPECTED_WORKFLOW_PREFIX:
        raise PolicyError(
            "CI workflow trigger, permissions, or concurrency envelope moved"
        )
    start = jobs_line + 1

    jobs: list[dict[str, Any]] = []
    job: dict[str, Any] | None = None
    step: dict[str, Any] | None = None
    nested: str | None = None

    def finish_step() -> None:
        nonlocal step, nested
        if step is not None and job is not None:
            job["steps"].append(step)
        step = None
        nested = None

    for lineno, raw in enumerate(lines[start:], start + 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        match = re.fullmatch(r"  ([a-z][a-z0-9-]*):", raw)
        if match:
            finish_step()
            if job is not None:
                jobs.append(job)
            job = {"id": match.group(1), "needs": [], "steps": []}
            continue
        if job is None:
            raise PolicyError(f"unexpected workflow content at line {lineno}: {raw}")
        if raw.startswith("    ") and not raw.startswith("      "):
            finish_step()
            key, separator, value = raw.strip().partition(":")
            if not separator:
                raise PolicyError(f"invalid job property at line {lineno}")
            if key == "steps":
                if value.strip():
                    raise PolicyError(f"steps must be a block at line {lineno}")
            elif key == "name":
                job["name"] = parse_scalar(value)
            elif key == "runs-on":
                job["runs_on"] = parse_scalar(value)
            elif key == "timeout-minutes":
                try:
                    job["timeout_minutes"] = int(value.strip())
                except ValueError as error:
                    raise PolicyError(f"invalid timeout at line {lineno}") from error
            elif key == "needs":
                job["needs"] = parse_needs(value)
            else:
                raise PolicyError(f"unknown job property {key} at line {lineno}")
            continue
        match = re.fullmatch(r"      - name: (.+)", raw)
        if match:
            finish_step()
            step = {"name": parse_scalar(match.group(1))}
            continue
        if step is None:
            raise PolicyError(f"workflow step lacks an exact name at line {lineno}")
        if raw.startswith("        ") and not raw.startswith("          "):
            key, separator, value = raw.strip().partition(":")
            if not separator:
                raise PolicyError(f"invalid step property at line {lineno}")
            if key in {"with", "env"}:
                if value.strip():
                    raise PolicyError(f"{key} must be a block at line {lineno}")
                nested = key
                step[key] = {}
            elif key in {"uses", "run", "if"}:
                nested = None
                step[key] = parse_scalar(value)
            else:
                raise PolicyError(f"unknown step property {key} at line {lineno}")
            continue
        if raw.startswith("          ") and nested in {"with", "env"}:
            key, separator, value = raw.strip().partition(":")
            if not separator:
                raise PolicyError(f"invalid {nested} entry at line {lineno}")
            step[nested][key] = parse_scalar(value)
            continue
        raise PolicyError(f"unsupported workflow syntax at line {lineno}: {raw}")
    finish_step()
    if job is not None:
        jobs.append(job)
    return jobs


def expected_workflow(
    topology: dict[str, Any], registry: dict[str, Any]
) -> list[dict[str, Any]]:
    by_id = {gate["id"]: gate for gate in registry["gates"]}
    result: list[dict[str, Any]] = []
    for job in topology["jobs"]:
        rendered = {
            "id": job["id"],
            "name": job["name"],
            "runs_on": job["runs_on"],
            "timeout_minutes": job["timeout_minutes"],
            "needs": job["needs"],
            "steps": [],
        }
        for step in job["steps"]:
            value: dict[str, Any] = {"name": step["name"]}
            if step["kind"] == "gate":
                gate = by_id.get(step["gate_id"])
                if gate is None:
                    value["run"] = "<unknown gate>"
                else:
                    value["run"] = " ".join(gate["command"])
                if step.get("env"):
                    value["env"] = step["env"]
            elif step["kind"] == "action":
                value["uses"] = step["uses"]
                if step.get("with"):
                    value["with"] = step["with"]
            elif step["kind"] == "command":
                value["run"] = step["run"]
                if step.get("env"):
                    value["env"] = step["env"]
            if "if" in step:
                value["if"] = step["if"]
            rendered["steps"].append(value)
        result.append(rendered)
    return result


def workflow_problems(
    expected: list[dict[str, Any]], actual: list[dict[str, Any]]
) -> list[str]:
    problems: list[str] = []
    expected_ids = [job["id"] for job in expected]
    actual_ids = [job["id"] for job in actual]
    if actual_ids != expected_ids:
        return [f"workflow job population/order moved: expected={expected_ids}, actual={actual_ids}"]
    for wanted, got in zip(expected, actual):
        job_id = wanted["id"]
        for key in ("name", "runs_on", "timeout_minutes", "needs"):
            if got.get(key) != wanted.get(key):
                problems.append(
                    f"workflow job {job_id} {key} moved: expected={wanted.get(key)!r}, "
                    f"actual={got.get(key)!r}"
                )
        if len(got["steps"]) != len(wanted["steps"]):
            problems.append(
                f"workflow job {job_id} step count moved: "
                f"expected={len(wanted['steps'])}, actual={len(got['steps'])}"
            )
            continue
        for position, (wanted_step, got_step) in enumerate(
            zip(wanted["steps"], got["steps"]), 1
        ):
            if got_step != wanted_step:
                problems.append(
                    f"workflow job {job_id} step {position} moved: "
                    f"expected={wanted_step!r}, actual={got_step!r}"
                )
    return problems


def validate() -> tuple[
    dict[str, Any], dict[str, Any], dict[str, Any], list[str]
]:
    policy = read_policy()
    topology = read_topology()
    gate_cache = load_gate_cache()
    try:
        registry = gate_cache.load_registry(gate_cache.registry_path(ROOT))
    except Exception as error:  # registry parser already supplies exact failure text
        raise PolicyError(f"cannot load gate registry: {error}") from error
    problems = topology_problems(topology, registry, policy)
    try:
        actual = parse_workflow()
    except PolicyError as error:
        problems.append(str(error))
    else:
        problems.extend(workflow_problems(expected_workflow(topology, registry), actual))
    return policy, topology, registry, problems


def audit(arguments: argparse.Namespace) -> int:
    policy, topology, registry, problems = validate()
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
    by_id = {gate["id"]: gate for gate in registry["gates"]}
    costs = catalogue_costs()
    selected: list[dict[str, Any]] = []
    for job in topology["jobs"]:
        for step in job["steps"]:
            if step["kind"] != "gate":
                continue
            gate = by_id[step["gate_id"]]
            selected.append(
                {
                    "id": gate["id"],
                    "command": " ".join(gate["command"]),
                    "job": job["id"],
                    "purpose": step["purpose"],
                    "execution_surface": job["surface"],
                    "depends_on": gate.get("depends_on", []),
                    "input_kinds": sorted(gate.get("inputs", {})),
                    "expected_cost": costs[tuple(gate["command"])],
                    "disposition": "fresh",
                }
            )
    payload = {
        "schema": 2,
        "event": arguments.event,
        "base": arguments.base or None,
        "head": arguments.head or None,
        "trusted_cross_run_evidence": False,
        "may_admit_evidence": False,
        "sampling": "disabled",
        "topology": "scripts/ci-topology.json",
        "full_build_count": 1,
        "artifact_transfer": "exact-commit-cache-fail-closed",
        "reasons": reasons,
        "selected": selected,
    }
    if arguments.output:
        output = Path(arguments.output)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"CI GATE POLICY OK — {len(selected)} registered commands in "
        f"{len(topology['jobs'])} jobs selected fresh; 0 reused; 0 sampled; "
        "one full build; exact-cache consumers fail closed"
    )
    for reason in reasons:
        print(f"  reason: {reason}")
    return 0


def self_test() -> int:
    policy = read_policy()
    topology = read_topology()
    gate_cache = load_gate_cache()
    registry = gate_cache.load_registry(gate_cache.registry_path(ROOT))
    baseline = topology_problems(topology, registry, policy)
    if baseline:
        raise PolicyError("production topology baseline is invalid: " + "; ".join(baseline))
    expected = expected_workflow(topology, registry)
    actual = parse_workflow()
    drift = workflow_problems(expected, actual)
    if drift:
        raise PolicyError("production workflow baseline is invalid: " + "; ".join(drift))

    controls = 0

    def check_rejected(label: str, changed: dict[str, Any], fragment: str) -> None:
        nonlocal controls
        found = topology_problems(changed, registry, policy)
        if not any(fragment in problem for problem in found):
            raise PolicyError(f"{label} was not rejected for {fragment!r}: {found}")
        controls += 1

    def find_step(value: dict[str, Any], identifier: str) -> tuple[dict[str, Any], dict[str, Any]]:
        for job in value["jobs"]:
            for step in job["steps"]:
                if step["id"] == identifier:
                    return job, step
        raise PolicyError(f"self-test cannot find step {identifier}")

    changed = copy.deepcopy(topology)
    _, step = find_step(changed, "doc-counts")
    step["gate_id"] = "unknown-gate"
    check_rejected("unknown gate", changed, "unknown gate")

    changed = copy.deepcopy(topology)
    job, step = find_step(changed, "execution-settlement")
    job["steps"].remove(step)
    check_rejected("missing gate", changed, "missing=['execution-settlement']")

    changed = copy.deepcopy(topology)
    job, first = find_step(changed, "execution-settlement")
    _, second = find_step(changed, "execution-occurrence-semantic")
    a, b = job["steps"].index(first), job["steps"].index(second)
    job["steps"][a], job["steps"][b] = job["steps"][b], job["steps"][a]
    check_rejected("reversed dependency", changed, "runs before dependency")

    changed = copy.deepcopy(topology)
    job, step = find_step(changed, "doc-counts")
    job["steps"].append(copy.deepcopy(step))
    check_rejected("duplicate gate", changed, "more than once")

    changed = copy.deepcopy(topology)
    job, step = find_step(changed, "eels-venv")
    step["id"] = "unknown-command"
    check_rejected("unregistered command", changed, "unregistered CI infrastructure")

    changed = copy.deepcopy(topology)
    job, step = find_step(changed, "full-build")
    job["steps"].append(copy.deepcopy(step))
    check_rejected("duplicate full build", changed, "full builds")

    changed = copy.deepcopy(topology)
    _, step = find_step(changed, "restore-build")
    step["with"]["fail-on-cache-miss"] = "false"
    check_rejected("permissive cache miss", changed, "permissive or non-exact")

    changed = copy.deepcopy(topology)
    _, step = find_step(changed, "restore-build")
    step["with"]["key"] = "previous-commit-prefix"
    check_rejected("non-exact cache key", changed, "permissive or non-exact")

    changed = copy.deepcopy(topology)
    _, step = find_step(changed, "restore-build")
    step["with"]["path"] = ".lake/build"
    check_rejected("partial/corrupt cache surface", changed, "permissive or non-exact")

    changed = copy.deepcopy(topology)
    job = next(item for item in changed["jobs"] if item["id"] == "source-trust")
    job["needs"] = ["policy", "reference-locks"]
    check_rejected("independent-lane coupling", changed, "coupled to a sibling")

    changed = copy.deepcopy(topology)
    job = next(item for item in changed["jobs"] if item["id"] == "execution-semantic")
    job["needs"] = ["policy"]
    check_rejected("semantic lane without build", changed, "can run without")

    changed = copy.deepcopy(topology)
    _, step = find_step(changed, "install-toolchain")
    step["with"]["build"] = "true"
    check_rejected("downstream rebuild", changed, "can rebuild or admit fallback")

    changed = copy.deepcopy(topology)
    job, step = find_step(changed, "recipe-base")
    job["steps"].remove(step)
    check_rejected("missing recipe base setup", changed, "infrastructure population/order")

    changed = copy.deepcopy(topology)
    job, step = find_step(changed, "recipe-base")
    job["steps"].remove(step)
    job["steps"].append(step)
    check_rejected("late recipe base setup", changed, "not bound before")

    changed = copy.deepcopy(topology)
    _, step = find_step(changed, "full-build")
    step["with"]["build-args"] = "Blanc jaune/jaune"
    check_rejected("omitted unimported proof recipe leaf", changed, "infrastructure step")

    changed = copy.deepcopy(topology)
    job, step = find_step(changed, "save-cold-build")
    job["steps"].remove(step)
    check_rejected("missing cold build save", changed, "infrastructure population/order")

    changed = copy.deepcopy(topology)
    _, step = find_step(changed, "full-build")
    step["with"]["use-github-cache"] = "true"
    check_rejected("cold build silently restores", changed, "infrastructure step")

    changed = copy.deepcopy(topology)
    _, step = find_step(changed, "save-cold-build")
    step["if"] = "always()"
    check_rejected("failed or untrusted cold save", changed, "infrastructure step")

    changed_actual = copy.deepcopy(actual)
    changed_actual[0]["steps"][0]["name"] = "Renamed checkout"
    if not workflow_problems(expected, changed_actual):
        raise PolicyError("renamed workflow step escaped the topology audit")
    controls += 1

    changed_actual = copy.deepcopy(actual)
    changed_actual[0]["steps"].append(
        {"name": "Unmodelled action", "uses": "vendor/unknown@v1"}
    )
    if not workflow_problems(expected, changed_actual):
        raise PolicyError("unmodelled workflow action escaped the topology audit")
    controls += 1

    changed_source = WORKFLOW.read_text(encoding="utf-8").replace(
        "branches: [main]", "branches: [release]", 1
    )
    try:
        parse_workflow(changed_source)
    except PolicyError as error:
        if "trigger, permissions, or concurrency" not in str(error):
            raise PolicyError(f"workflow trigger drift failed for the wrong reason: {error}")
    else:
        raise PolicyError("workflow trigger drift escaped the topology audit")
    controls += 1

    changed_registry = copy.deepcopy(registry)
    next(
        gate for gate in changed_registry["gates"] if gate["id"] == "doc-counts"
    )["command"] = ["scripts/unregistered-catalogue-command.sh"]
    if not any(
        "has no catalogue cost row" in problem
        for problem in topology_problems(topology, changed_registry, policy)
    ):
        raise PolicyError("registry/catalogue command drift escaped the topology audit")
    controls += 1

    fork_reasons = " ".join(
        selection_reasons(
            event="pull_request",
            base="",
            head="",
            repository="owner/repo",
            head_repository="fork/repo",
        )
    )
    if "untrusted" not in fork_reasons or "outside the trusted" not in fork_reasons:
        raise PolicyError("fork evidence was not rejected")
    controls += 1

    unknown_reasons = " ".join(
        selection_reasons(
            event="push",
            base="missing",
            head="missing",
            repository="owner/repo",
            head_repository="owner/repo",
        )
    )
    if "unavailable" not in unknown_reasons:
        raise PolicyError("unknown base did not select all")
    controls += 1

    if policy["cross_run_evidence"] != "disabled" or policy["sampling"] != "disabled":
        raise PolicyError("production policy can reuse or sample gate verdicts")
    controls += 1

    print(
        f"CI GATE POLICY SELF-TEST OK — {controls} population, dependency, "
        "topology, cache-transfer and trust controls"
    )
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
