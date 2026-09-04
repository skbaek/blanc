#!/usr/bin/env python3
"""Fail when a BPO2 consumer credits less than its Prague counterpart.

Blanc runs two evidence lanes against every deployed reference it credits: a
preserved Prague differential and a current-mainnet BPO2 consumer.  Where the
BPO2 lane executes fewer rows, or credits fewer channels on a shared row, the
difference is a claim that the behaviour cannot have changed across the fork.
That is a hypothesis an evidence lane exists to test, not a premise it may
assume, so this gate makes every such difference name itself.

The check is containment, not equality: the Prague population must be contained
in the BPO2 population under a declared channel equivalence and row alias map.
Extra BPO2 coverage is never a divergence.  Every uncontained row or channel
must be covered by exactly one registered exception carrying a real basis, and
an exception that covers nothing is itself a failure -- a register that keeps
stale entries stops being a control.

The gate is static: it reads committed generated artifacts and the frozen
Prague corpus identity.  It builds no Lean, runs no t8n, and needs no external
checkout.
"""

from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable, NoReturn, Sequence

ROOT = Path(__file__).resolve().parents[1]
REGISTER = ROOT / "scripts" / "current-mainnet-parity.json"

CONSUMER_KEYS = {"id", "prague", "bpo2", "channelEquivalence", "rowAliases"}
EXCEPTION_KEYS = {
    "id",
    "consumer",
    "kind",
    "rows",
    "channels",
    "reason",
    "basis",
    "decision",
}
EXCEPTION_KINDS = ("missing-row", "missing-channel")
BASIS_KINDS = ("measurement", "expressibility")


class ParityError(RuntimeError):
    """A malformed register, an uncovered asymmetry, or a dead exception."""


def fail(message: str) -> NoReturn:
    raise ParityError(message)


def exact_keys(value: Any, expected: set[str], where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{where} is not an object")
    if set(value) != expected:
        missing = sorted(expected - set(value))
        extra = sorted(set(value) - expected)
        fail(f"{where} keys differ: missing={missing}, extra={extra}")
    return value


def dotted(document: Any, path: str, where: str) -> Any:
    cursor = document
    for step in path.split("."):
        if not isinstance(cursor, dict) or step not in cursor:
            fail(f"{where}: no value at {path!r}")
        cursor = cursor[step]
    return cursor


def read_json(relative: str) -> Any:
    path = ROOT / relative
    if not path.is_file():
        fail(f"parity source is absent: {relative}")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail(f"parity source {relative} is not readable JSON: {exc}")


def python_constant(relative: str, attribute: str) -> Any:
    path = ROOT / relative
    if not path.is_file():
        fail(f"parity source is absent: {relative}")
    name = f"current_mainnet_parity_{path.stem}"
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        fail(f"cannot load parity source {relative}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    try:
        spec.loader.exec_module(module)
    except Exception as exc:  # noqa: BLE001 - any import failure is a gate failure
        fail(f"parity source {relative} did not import: {exc!r}")
    if not hasattr(module, attribute):
        fail(f"parity source {relative} has no {attribute}")
    return getattr(module, attribute)


def population(side: dict[str, Any], where: str) -> dict[str, set[str]]:
    """Return {row name: credited channel set} for one side of one consumer."""

    kind = side.get("kind")
    if kind == "python-constant":
        names = python_constant(side["source"], side["attribute"])
        if not isinstance(names, (list, tuple)) or not names:
            fail(f"{where}: {side['attribute']} is not a non-empty sequence")
        return {str(name): set() for name in names}
    if kind == "json-keys":
        rows = dotted(read_json(side["source"]), side["rowsPath"], where)
        if not isinstance(rows, dict) or not rows:
            fail(f"{where}: {side['rowsPath']} is not a non-empty object")
        return {str(name): set() for name in rows}
    if kind != "json":
        fail(f"{where}: unknown source kind {kind!r}")
    rows = dotted(read_json(side["source"]), side["rowsPath"], where)
    if not isinstance(rows, list) or not rows:
        fail(f"{where}: {side['rowsPath']} is not a non-empty list")
    name_key, channels_key = side["nameKey"], side["channelsKey"]
    result: dict[str, set[str]] = {}
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or name_key not in row:
            fail(f"{where}: row {index} has no {name_key!r}")
        name = str(row[name_key])
        if name in result:
            fail(f"{where}: duplicate row name {name!r}")
        channels = row.get(channels_key, [])
        if not isinstance(channels, list):
            fail(f"{where}: row {name!r} has a non-list {channels_key!r}")
        result[name] = {str(channel) for channel in channels}
    return result


def asymmetries(consumer: dict[str, Any]) -> list[dict[str, Any]]:
    """Every Prague row or channel the BPO2 lane does not contain."""

    identifier = consumer["id"]
    prague = population(consumer["prague"], f"{identifier} Prague")
    bpo2 = population(consumer["bpo2"], f"{identifier} BPO2")
    aliases = consumer["rowAliases"]
    if not isinstance(aliases, dict):
        fail(f"{identifier}: rowAliases is not an object")
    for source, target in aliases.items():
        if source not in prague:
            fail(f"{identifier}: row alias {source!r} names no Prague row")
        if target not in bpo2:
            fail(f"{identifier}: row alias {source!r} targets absent BPO2 row {target!r}")
    equivalence = consumer["channelEquivalence"]
    if not isinstance(equivalence, dict):
        fail(f"{identifier}: channelEquivalence is not an object")

    found: list[dict[str, Any]] = []
    for name, channels in sorted(prague.items()):
        target = aliases.get(name, name)
        if target not in bpo2:
            found.append({"consumer": identifier, "kind": "missing-row", "row": name})
            continue
        credited = bpo2[target]
        if not channels:
            continue
        for channel in sorted(channels):
            if channel not in equivalence:
                fail(
                    f"{identifier}: Prague row {name!r} credits {channel!r}, "
                    "which channelEquivalence does not map"
                )
            mapped = equivalence[channel]
            if mapped is None or mapped not in credited:
                found.append(
                    {
                        "consumer": identifier,
                        "kind": "missing-channel",
                        "row": name,
                        "channel": channel,
                    }
                )
    return found


def validate_exception(entry: Any, consumers: set[str], index: int) -> dict[str, Any]:
    exact_keys(entry, EXCEPTION_KEYS, f"exception {index}")
    identifier = entry["id"]
    if not isinstance(identifier, str) or not identifier:
        fail(f"exception {index} has no id")
    if entry["consumer"] not in consumers:
        fail(f"exception {identifier!r} names unknown consumer {entry['consumer']!r}")
    if entry["kind"] not in EXCEPTION_KINDS:
        fail(f"exception {identifier!r} has unknown kind {entry['kind']!r}")
    for key in ("rows", "channels"):
        if not isinstance(entry[key], list):
            fail(f"exception {identifier!r} has a non-list {key}")
    if not entry["rows"]:
        fail(f"exception {identifier!r} selects no rows")
    if entry["kind"] == "missing-channel" and not entry["channels"]:
        fail(f"exception {identifier!r} is a channel exception selecting no channel")
    if entry["kind"] == "missing-row" and entry["channels"]:
        fail(f"exception {identifier!r} is a row exception selecting channels")
    reason = entry["reason"]
    if not isinstance(reason, str) or len(reason.strip()) < 24:
        fail(f"exception {identifier!r} has no substantive reason")
    basis = entry["basis"]
    if not isinstance(basis, dict) or basis.get("kind") not in BASIS_KINDS:
        fail(
            f"exception {identifier!r} has no basis of kind "
            f"{' or '.join(BASIS_KINDS)}"
        )
    if basis["kind"] == "measurement":
        for key in ("gate", "wallSeconds", "rows"):
            if key not in basis:
                fail(f"exception {identifier!r} measurement basis has no {key!r}")
        if not isinstance(basis["wallSeconds"], (int, float)) or basis["wallSeconds"] <= 0:
            fail(f"exception {identifier!r} measurement basis has no positive wall time")
        if not isinstance(basis["rows"], int) or basis["rows"] <= 0:
            fail(f"exception {identifier!r} measurement basis has no positive row count")
    else:
        obstacle = basis.get("obstacle")
        if not isinstance(obstacle, str) or len(obstacle.strip()) < 24:
            fail(f"exception {identifier!r} expressibility basis names no obstacle")
    if not isinstance(entry["decision"], str) or not entry["decision"]:
        fail(f"exception {identifier!r} records no owner decision")
    return entry


def covers(entry: dict[str, Any], item: dict[str, Any]) -> bool:
    if entry["consumer"] != item["consumer"] or entry["kind"] != item["kind"]:
        return False
    rows = entry["rows"]
    if "*" not in rows and item["row"] not in rows:
        return False
    if entry["kind"] == "missing-channel":
        channels = entry["channels"]
        if "*" not in channels and item["channel"] not in channels:
            return False
    return True


def evaluate(register: dict[str, Any]) -> dict[str, Any]:
    exact_keys(register, {"schema", "consumers", "exceptions"}, "register")
    if register["schema"] != 1:
        fail(f"register schema is {register['schema']!r}, expected 1")
    consumers = register["consumers"]
    if not isinstance(consumers, list) or not consumers:
        fail("register declares no consumer")
    identifiers: set[str] = set()
    found: list[dict[str, Any]] = []
    per_consumer: dict[str, int] = {}
    for index, consumer in enumerate(consumers):
        exact_keys(consumer, CONSUMER_KEYS, f"consumer {index}")
        if consumer["id"] in identifiers:
            fail(f"duplicate consumer {consumer['id']!r}")
        identifiers.add(consumer["id"])
        items = asymmetries(consumer)
        per_consumer[consumer["id"]] = len(items)
        found.extend(items)

    entries = register["exceptions"]
    if not isinstance(entries, list):
        fail("register exceptions is not a list")
    seen: set[str] = set()
    validated = []
    for index, entry in enumerate(entries):
        validate_exception(entry, identifiers, index)
        if entry["id"] in seen:
            fail(f"duplicate exception {entry['id']!r}")
        seen.add(entry["id"])
        validated.append(entry)

    uncovered: list[dict[str, Any]] = []
    used: dict[str, int] = {entry["id"]: 0 for entry in validated}
    for item in found:
        matches = [entry for entry in validated if covers(entry, item)]
        if not matches:
            uncovered.append(item)
            continue
        if len(matches) > 1:
            fail(
                "asymmetry "
                f"{item['consumer']}/{item['row']}"
                + (f"/{item['channel']}" if "channel" in item else "")
                + " is claimed by "
                + ", ".join(sorted(entry["id"] for entry in matches))
            )
        used[matches[0]["id"]] += 1

    orphans = sorted(name for name, count in used.items() if count == 0)
    if orphans:
        fail(
            "registered exception covers no live asymmetry (remove it): "
            + ", ".join(orphans)
        )
    if uncovered:
        rendered = [
            f"{item['consumer']}/{item['row']}"
            + (f"/{item['channel']}" if "channel" in item else "")
            for item in uncovered[:8]
        ]
        more = f" (+{len(uncovered) - 8} more)" if len(uncovered) > 8 else ""
        fail(
            f"{len(uncovered)} unregistered fork asymmetr"
            + ("y" if len(uncovered) == 1 else "ies")
            + ": "
            + ", ".join(rendered)
            + more
        )
    return {
        "consumers": per_consumer,
        "asymmetries": len(found),
        "exceptions": used,
    }


SYNTHETIC_PRAGUE = {
    "rows": [
        {"name": "alpha", "channels": ["outcome", "returndata"]},
        {"name": "beta", "channels": ["outcome"]},
        {"name": "gamma", "channels": ["outcome"]},
        {"name": "delta", "channels": ["outcome"]},
    ]
}
SYNTHETIC_BPO2 = {
    "rows": [
        {"name": "alpha", "creditedChannels": ["status"]},
        {"name": "beta-renamed", "creditedChannels": ["status"]},
        {"name": "delta", "creditedChannels": ["status"]},
    ]
}


def synthetic_register(directory: Path) -> dict[str, Any]:
    """A tiny two-lane pair with one missing row and one missing channel.

    The controls run against this rather than against the live register so that
    they prove the gate's logic whatever state the real migration is in.  A
    control campaign that only works while production happens to be green is
    not a control.
    """

    prague = directory / "synthetic-prague.json"
    bpo2 = directory / "synthetic-bpo2.json"
    prague.write_text(json.dumps(SYNTHETIC_PRAGUE), encoding="utf-8")
    bpo2.write_text(json.dumps(SYNTHETIC_BPO2), encoding="utf-8")
    return {
        "schema": 1,
        "consumers": [
            {
                "id": "synthetic",
                "prague": {
                    "kind": "json",
                    "source": str(prague.relative_to(ROOT)),
                    "rowsPath": "rows",
                    "nameKey": "name",
                    "channelsKey": "channels",
                },
                "bpo2": {
                    "kind": "json",
                    "source": str(bpo2.relative_to(ROOT)),
                    "rowsPath": "rows",
                    "nameKey": "name",
                    "channelsKey": "creditedChannels",
                },
                "channelEquivalence": {"outcome": "status", "returndata": "returndata"},
                "rowAliases": {"beta": "beta-renamed"},
            }
        ],
        "exceptions": [
            {
                "id": "synthetic-missing-row",
                "consumer": "synthetic",
                "kind": "missing-row",
                "rows": ["gamma"],
                "channels": [],
                "reason": "control fixture: gamma is deliberately absent from the BPO2 side",
                "basis": {
                    "kind": "expressibility",
                    "obstacle": "control fixture obstacle, present so the basis validator has something real to accept",
                },
                "decision": "control fixture",
            },
            {
                "id": "synthetic-missing-channel",
                "consumer": "synthetic",
                "kind": "missing-channel",
                "rows": ["alpha"],
                "channels": ["returndata"],
                "reason": "control fixture: alpha credits returndata at Prague only",
                "basis": {
                    "kind": "measurement",
                    "gate": "synthetic",
                    "wallSeconds": 1.0,
                    "rows": 3,
                },
                "decision": "control fixture",
            },
        ],
    }


def self_test() -> int:
    """Three-control campaign on a synthetic pair: green, mutant red, revert green."""

    with tempfile.TemporaryDirectory(dir=ROOT / "scripts") as temporary:
        register = synthetic_register(Path(temporary))
        evaluate(copy.deepcopy(register))
        print("CONTROL  unchanged synthetic register: accepted")

        def control(label: str, mutate) -> None:
            mutant = copy.deepcopy(register)
            mutate(mutant)
            try:
                evaluate(mutant)
            except ParityError as exc:
                print(f"CONTROL  {label}: rejected — {str(exc)[:110]}")
                return
            raise ParityError(f"parity control survived: {label}")

        def deleted_bpo2_row(mutant: dict[str, Any]) -> None:
            document = json.loads(
                (ROOT / mutant["consumers"][0]["bpo2"]["source"]).read_text()
            )
            document["rows"] = [row for row in document["rows"] if row["name"] != "delta"]
            (ROOT / mutant["consumers"][0]["bpo2"]["source"]).write_text(
                json.dumps(document), encoding="utf-8"
            )

        def restore_bpo2_rows() -> None:
            (ROOT / register["consumers"][0]["bpo2"]["source"]).write_text(
                json.dumps(SYNTHETIC_BPO2), encoding="utf-8"
            )

        control("deleted BPO2 row", deleted_bpo2_row)
        restore_bpo2_rows()
        evaluate(copy.deepcopy(register))
        print("CONTROL  deleted BPO2 row: sole reversion restores green")

        control(
            "exception removed while the asymmetry stands",
            lambda mutant: mutant["exceptions"].pop(0),
        )
        control(
            "exception that covers nothing",
            lambda mutant: mutant["exceptions"].append(
                {
                    "id": "control-orphan",
                    "consumer": "synthetic",
                    "kind": "missing-row",
                    "rows": ["a-row-no-lane-declares"],
                    "channels": [],
                    "reason": "an orphan entry the control adds so the gate can reject it",
                    "basis": {
                        "kind": "expressibility",
                        "obstacle": "this entry exists only so the control can observe its rejection",
                    },
                    "decision": "control",
                }
            ),
        )
        control(
            "exception with no basis",
            lambda mutant: mutant["exceptions"][0].update({"basis": {}}),
        )
        control(
            "exception whose measurement has no wall time",
            lambda mutant: mutant["exceptions"][1]["basis"].update({"wallSeconds": 0}),
        )
        control(
            "row alias naming no Prague row",
            lambda mutant: mutant["consumers"][0]["rowAliases"].update(
                {"no-such-prague-row": "beta-renamed"}
            ),
        )
        control(
            "widened exception that swallows a second asymmetry",
            lambda mutant: mutant["exceptions"][0].update({"rows": ["*"]})
            or mutant["exceptions"].append(
                {
                    "id": "control-overlap",
                    "consumer": "synthetic",
                    "kind": "missing-row",
                    "rows": ["gamma"],
                    "channels": [],
                    "reason": "a second entry claiming the same asymmetry as the widened one",
                    "basis": {
                        "kind": "expressibility",
                        "obstacle": "control overlap entry, present so double coverage is observable",
                    },
                    "decision": "control",
                }
            ),
        )

        evaluate(copy.deepcopy(register))
        print("CONTROL  unchanged synthetic register: accepted again")
    return 7


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--register", default=str(REGISTER))
    # The wrapper writes its own copy of the consumer inventory and the two
    # closed vocabularies.  A Python-only weakening that drops a consumer or
    # invents an exception kind therefore has to be made twice, in two files,
    # to earn credit.
    parser.add_argument("--wrapper-consumers", default=None)
    parser.add_argument("--wrapper-exception-kinds", default=None)
    parser.add_argument("--wrapper-basis-kinds", default=None)
    args = parser.parse_args(list(argv) if argv is not None else None)

    declared = {
        "--wrapper-exception-kinds": (args.wrapper_exception_kinds, EXCEPTION_KINDS),
        "--wrapper-basis-kinds": (args.wrapper_basis_kinds, BASIS_KINDS),
    }
    for flag, (supplied, expected) in declared.items():
        if supplied is None:
            continue
        if tuple(supplied.split(",")) != tuple(expected):
            print(
                f"REGRESSION — current-mainnet parity: {flag} is {supplied!r}, "
                f"expected {','.join(expected)!r}",
                file=sys.stderr,
            )
            return 1

    path = Path(args.register)
    try:
        register = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"REGRESSION — current-mainnet parity: register unreadable: {exc}", file=sys.stderr)
        return 1

    if args.wrapper_consumers is not None:
        declared_ids = tuple(args.wrapper_consumers.split(","))
        actual_ids = tuple(
            str(consumer.get("id"))
            for consumer in register.get("consumers", [])
            if isinstance(consumer, dict)
        )
        if declared_ids != actual_ids:
            print(
                "REGRESSION — current-mainnet parity: wrapper declares consumers "
                f"{','.join(declared_ids)!r}, register declares {','.join(actual_ids)!r}",
                file=sys.stderr,
            )
            return 1

    try:
        controls = self_test() if args.self_test else 0
        summary = evaluate(register)
    except ParityError as exc:
        print(f"REGRESSION — current-mainnet parity: {exc}", file=sys.stderr)
        return 1

    consumers = summary["consumers"]
    covered = sum(summary["exceptions"].values())
    detail = ", ".join(f"{name} {count}" for name, count in sorted(consumers.items()))
    control_note = f", {controls} register controls live" if controls else ""
    print(
        f"OK — current-mainnet parity: {len(consumers)} consumers checked "
        f"({detail} asymmetries), {covered} covered by "
        f"{len(summary['exceptions'])} registered exceptions, "
        f"0 unregistered{control_note}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
