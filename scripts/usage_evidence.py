#!/usr/bin/env python3
"""Hash-bound resolved-reference transport and immutable historical reconciliation.

No Lean elaboration, lexical name resolution, static script execution, published
count generation, or semantic value judgement occurs here. See interface-v1.md.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path

from module_path_policy import resolve_bound_file

SCHEMA = "blanc-resolved-usage-v1"
NATIVE_SCHEMA = "blanc-resolved-usage-v2"
IMPORTED_SCHEMA = "blanc-resolved-usage-v3"
REQUEST_DIGEST_SCHEME = "json-sort-compact-ascii-sha256"
KINDS = {"term-reference", "rewrite-positive", "rewrite-remove", "checked-name",
         "checked-type", "checked-axioms", "macro-reference", "script-check"}


class UsageEvidenceError(ValueError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise UsageEvidenceError(message)


def _read(root: Path, path: str) -> bytes:
    try:
        return resolve_bound_file(root, path, allow_missing=False,
                                  site="usage-evidence-candidate-input").read_bytes()
    except (OSError, ValueError, RuntimeError) as error:
        raise UsageEvidenceError(f"unsafe/unreadable evidence input {path}: {error}") from error


def _span(value: object, size: int) -> tuple[int, int]:
    _require(isinstance(value, list) and len(value) == 2
             and all(type(x) is int for x in value), "invalid UTF-8 byte span")
    start, end = value
    _require(0 <= start < end <= size, "reference/command span outside captured source")
    return start, end


def declaration_index(rows: list[dict]) -> dict[str, dict]:
    _require(isinstance(rows, list) and bool(rows), "empty/malformed declaration identities")
    indexed = {}
    for row in rows:
        _require(isinstance(row, dict), "malformed declaration row")
        name = row.get("name")
        _require(isinstance(name, str) and bool(name) and name not in indexed,
                 "empty/duplicate kernel declaration identity")
        _require(all(isinstance(row.get(k), str) and row[k] for k in ("display_name", "module"))
                 and type(row.get("private")) is bool and type(row.get("theorem")) is bool
                 and row.get("kind") in {"theorem", "def", "opaque", "axiom", "constructor", "recursor", "inductive", "instance"},
                 f"malformed declaration metadata: {name}")
        _require("owner" in row and (row["owner"] is None or isinstance(row["owner"], str)),
                 f"missing declaration owner: {name}")
        indexed[name] = row
    for name, row in indexed.items():
        owner = row["owner"]
        _require(owner is None or owner in indexed, f"unknown canonical owner of {name}")
        if owner is not None:
            _require(indexed[owner]["owner"] == owner, f"noncanonical owner of {name}")
    return indexed


def validate_and_index(root: Path, receipt: dict, expected_sources: dict[str, str],
                       expected_bindings: dict[str, str], requests: list[dict] = ()) -> dict:
    """Reject incomplete/stale receipts and index theorem references by kernel owner.

    Expected inventories are authoritative inputs captured by the runtime launcher.
    Native controls must independently establish their parser/adapter completeness.
    """
    root = root.resolve(strict=True)
    _require(receipt.get("schema") == SCHEMA, "unsupported usage evidence schema")
    _require(bool(expected_sources) and bool(expected_bindings), "empty candidate inventories")
    _require(receipt.get("source_hashes") == expected_sources, "source coverage/hash mismatch")
    _require(receipt.get("bindings") == expected_bindings, "candidate setup/import binding mismatch")
    _require(receipt.get("errors") == [] and receipt.get("sorry") is False
             and receipt.get("unresolved") == [], "failed/sorry/unresolved usage evidence")
    raw = {}
    for path, digest in {**expected_bindings, **expected_sources}.items():
        _require(path not in expected_bindings or path not in expected_sources
                 or expected_bindings[path] == expected_sources[path], "conflicting input hashes")
        data = _read(root, path)
        _require(hashlib.sha256(data).hexdigest() == digest, f"stale candidate bytes: {path}")
        raw[path] = data
    declarations = declaration_index(receipt.get("declarations"))
    sources = receipt.get("sources")
    _require(isinstance(sources, list), "missing resolved source records")
    _require(len(sources) == len(expected_sources)
             and {r.get("path") for r in sources} == set(expected_sources),
             "incomplete/duplicate resolved source coverage")
    uses: dict[str, list[dict]] = {}
    for source in sources:
        path = source["path"]
        commands = source.get("commands")
        _require(isinstance(commands, list) and bool(commands), f"missing parsed commands: {path}")
        command_index = {}
        for command in commands:
            cid = command.get("id")
            _require(isinstance(cid, str) and cid and cid not in command_index,
                     f"invalid/duplicate command identity: {path}")
            start, end = _span(command.get("span"), len(raw[path]))
            _require(command.get("mode") in {"elaborated", "reference-adapter"},
                     f"unresolved command execution role: {path}:{cid}")
            if command["mode"] == "reference-adapter":
                adapter = command.get("adapter")
                _require(isinstance(adapter, str) and adapter in expected_bindings,
                         f"unbound command adapter: {path}:{cid}")
            command_index[cid] = (start, end)
        references = source.get("references")
        _require(isinstance(references, list), f"missing reference collection: {path}")
        for reference in references:
            cid, target = reference.get("command"), reference.get("resolved_name")
            _require(cid in command_index and target in declarations,
                     f"unknown command/resolved declaration: {path}")
            start, end = _span(reference.get("span"), len(raw[path]))
            lo, hi = command_index[cid]
            _require(lo <= start < end <= hi, f"reference outside owner command: {path}")
            _require(reference.get("kind") in KINDS, f"unknown reference kind: {path}")
            _require("parent" in reference, f"missing explicit parent attribution: {path}")
            parent = reference["parent"]
            _require(parent is None or parent in declarations, f"unknown parent identity: {path}")
            owner = declarations[target]["owner"]
            if owner is not None and declarations[owner]["theorem"]:
                if parent is None or declarations[parent]["owner"] != owner:
                    uses.setdefault(owner, []).append({"path": path, **reference})
    request_index = {r["id"]: r for r in requests}
    _require(len(request_index) == len(requests), "duplicate static consumer request ID")
    responses = receipt.get("static_resolutions")
    _require(isinstance(responses, list) and len(responses) == len(request_index)
             and {r.get("id") for r in responses} == set(request_index),
             "unanswered/duplicate static consumer requests")
    for response in responses:
        request = request_index[response["id"]]
        _require(request["path"] in expected_bindings
                 and request["source_sha256"] == expected_bindings[request["path"]]
                 and request["target_source"] in expected_sources,
                 "unbound static consumer source/context")
        target = response.get("resolved_name")
        _require(target in declarations and response.get("requested_name") == request["name"]
                 and response.get("target_source") == request["target_source"],
                 "unresolved/mismatched static consumer")
        owner = declarations[target]["owner"]
        if owner is not None and declarations[owner]["theorem"]:
            uses.setdefault(owner, []).append({"kind": request["kind"], **request,
                                              "resolved_name": target})
    return {"declarations": declarations, "uses": uses}


def _json_identity(value: object) -> bytes:
    """Typed JSON equality/digest; True must never impersonate integer request 1."""
    try:
        return json.dumps(value, sort_keys=True, ensure_ascii=True,
                          allow_nan=False, separators=(",", ":")).encode("utf-8")
    except (TypeError, ValueError) as error:
        raise UsageEvidenceError(f"invalid JSON identity: {error}") from error


def _same_json(left: object, right: object) -> bool:
    return _json_identity(left) == _json_identity(right)


def _migration_environment_helpers():
    """Reuse the existing launcher implementation without launching any process."""
    path = Path(__file__).with_name("run-simp-migration.py")
    spec = importlib.util.spec_from_file_location("usage_migration_environment", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def capture_native_environment(root: Path, setup: dict) -> dict:
    """Launcher capture: exact existing environment_identity plus original setup.

    The caller must obtain setup through the admitted existing Lake launcher;
    this function never invokes Lake or establishes setup/source authenticity.
    """
    root = root.resolve(strict=True)
    helpers = _migration_environment_helpers()
    try:
        return {"setup": setup, "identity": helpers.environment_identity(root, setup)}
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise UsageEvidenceError(f"native environment capture failed: {error}") from error


def _request_id(value: object) -> tuple[type, object]:
    _require((type(value) is int and value >= 0) or
             (type(value) is str and bool(value)), "invalid original static request ID")
    return type(value), value


def _digest(value):
    return hashlib.sha256(_json_identity(value)).hexdigest()


def _native_capture(value, bindings, environment):
    _require(isinstance(value, dict) and value.get("adapter") in bindings
             and value.get("environment") == environment
             and isinstance(value.get("context_id"), str) and value["context_id"],
             "unbound independent native capture")


def _range_attachment(value, raw, owner):
    _require(isinstance(value, dict) and value.get("kind") in {"direct", "owner", "absent"}
             and "span" in value and "owner" in value, "missing honest range provenance")
    if value["kind"] == "absent":
        _require(value["span"] is None and value["owner"] is None, "fabricated absent range")
    else:
        _span(value["span"], len(raw))
        _require((value["kind"] == "direct" and value["owner"] is None) or
                 (value["kind"] == "owner" and owner is not None and value["owner"] == owner),
                 "range owner differs from actual canonical owner")


def _imported_origin(row, environments, raw, bindings):
    imported = row.get("imported")
    _require(row.get("population") == "nonproduction" and "origin_role" not in row
             and isinstance(imported, dict), "foreign origin bypasses production/local command coverage")
    eid = row["environment"]
    _native_capture(imported.get("capture"), bindings, eid)
    setup = environments[eid]["setup"]
    parts = setup.get("importArts", {}).get(row["module"])
    _require(parts is not None and _same_json(imported.get("parts"), parts)
             and imported.get("module") == row["module"]
             and isinstance(parts, list) and parts
             and all(isinstance(g, list) and all(isinstance(p, str) for p in g) for g in parts)
             and any(parts),
             "unbound imported module key/ordered artifact parts")
    hashes = environments[eid]["identity"]["file_sha256"]
    _require(all(p in hashes for g in parts for p in g), "imported part missing environment byte identity")
    package = imported.get("package")
    _require(isinstance(package, dict) and all(isinstance(package.get(k), str) and package[k]
             for k in ("name", "rev", "source_root", "manifest_path", "manifest_sha256"))
             and "module_source" in package and package["manifest_path"] in raw
             and hashlib.sha256(raw[package["manifest_path"]]).hexdigest() == package["manifest_sha256"],
             "unbound actual imported package/pin witness")
    try:
        manifest = json.loads(raw[package["manifest_path"]])
        matches = [p for p in manifest["packages"] if p.get("name") == package["name"]]
    except (ValueError, KeyError, TypeError) as error:
        raise UsageEvidenceError(f"invalid bound dependency manifest: {error}") from error
    _require(len(matches) == 1 and matches[0].get("type") == "git"
             and matches[0].get("rev") == package["rev"], "imported package pin differs from bound manifest")
    # Native capture must establish the actual checkout/artifact relationship;
    # matching the manifest's requested revision alone cannot establish it.
    attachment = row.get("source")
    _require("source" in row, "missing explicit foreign source attachment/absence")
    if attachment is not None:
        _require(isinstance(attachment, dict) and attachment.get("path") in raw
                 and attachment.get("sha256") == hashlib.sha256(raw[attachment["path"]]).hexdigest()
                 and isinstance(package["module_source"], str) and package["module_source"]
                 and attachment["path"] == package["source_root"] + "/" + package["module_source"],
                 "unbound actual Lake source/artifact relation")
        _range_attachment(attachment.get("range"), raw[attachment["path"]], row["owner"])
    _require("defining_kind" in row and (row["defining_kind"] is None or row["defining_kind"] in
             {"theorem", "def", "opaque", "axiom", "constructor", "recursor", "inductive", "instance"}),
             "missing honest imported defining-kind provenance")
    _require(row["defining_kind"] is None or row["defining_kind"] == row["kind"] or
             (row["kind"] == "axiom" and row["defining_kind"] == "theorem"),
             "imported defining/observed kind contradiction")


def validate_native_and_index(
        root: Path, receipt: dict, expected_sources: dict[str, str],
        expected_bindings: dict[str, str], expected_roles: list[dict],
        expected_declarations: list[dict], expected_environments: dict[str, dict],
        expected_visibility: list[dict], requests: list[dict] = (),
        static_contexts: list[dict] = (), static_provenance: list[dict] = ()) -> dict:
    """V2 transport checks only, never a certificate of native completeness.

    Roles/command inventories, declaration origins and original static requests
    must be independently captured by the launcher/compiled graph, not copied
    from receipt fields. Unsupported native provenance remains unresolved and
    fails acceptance. IDs distinguish declarations across source environments;
    a kernel-name string alone is not an identity. V1 remains preparation only.
    """
    return _validate_native(root, receipt, expected_sources, expected_bindings, expected_roles,
                            expected_declarations, expected_environments, expected_visibility,
                            requests, static_contexts, static_provenance)


def validate_imported_and_index(
        root: Path, receipt: dict, expected_sources: dict[str, str],
        expected_bindings: dict[str, str], expected_roles: list[dict],
        expected_declarations: list[dict], expected_environments: dict[str, dict],
        expected_visibility: list[dict], expected_observations: list[dict],
        requests: list[dict] = (), static_contexts: list[dict] = (),
        static_provenance: list[dict] = (), owner_supplements: list[dict] = ()) -> dict:
    """Opt-in v3 transport, not native capture or proof of complete resolution.

    Expected origins, observations and owner supplements must come independently
    from actual saved contexts/compiled graph and bound adapters. In particular,
    native Expr.equal plus ordered levelParams, selected Lake artifact/source/pin
    relations and operation semantics cannot be established by Python receipt
    metadata or fingerprints. Unsupported native capture remains unresolved.
    """
    return _validate_native(root, receipt, expected_sources, expected_bindings, expected_roles,
                            expected_declarations, expected_environments, expected_visibility,
                            requests, static_contexts, static_provenance, v3=True,
                            expected_observations=expected_observations,
                            owner_supplements=owner_supplements)


def _validate_native(root, receipt, expected_sources, expected_bindings, expected_roles,
                     expected_declarations, expected_environments, expected_visibility,
                     requests, static_contexts, static_provenance, *, v3=False,
                     expected_observations=(), owner_supplements=()):
    root = root.resolve(strict=True)
    schema = IMPORTED_SCHEMA if v3 else NATIVE_SCHEMA
    _require(isinstance(receipt, dict) and receipt.get("schema") == schema,
             f"native transport requires {schema}; v1 is preparation only")
    _require(bool(expected_sources) and bool(expected_bindings), "empty native input inventories")
    _require(_same_json(receipt.get("source_hashes"), expected_sources)
             and _same_json(receipt.get("bindings"), expected_bindings),
             "native source/input coverage mismatch")
    _require(receipt.get("errors") == [] and receipt.get("sorry") is False
             and receipt.get("unresolved") == [], "failed/sorry/unresolved native evidence")
    raw = {}
    for path, digest in {**expected_bindings, **expected_sources}.items():
        _require(path not in expected_bindings or path not in expected_sources
                 or expected_bindings[path] == expected_sources[path], "conflicting native input hashes")
        data = _read(root, path)
        _require(hashlib.sha256(data).hexdigest() == digest, f"stale native input: {path}")
        raw[path] = data
    helper_path = "scripts/run-simp-migration.py"
    _require(helper_path in expected_bindings and
             hashlib.sha256(Path(__file__).with_name("run-simp-migration.py").read_bytes()).hexdigest()
             == expected_bindings[helper_path], "unbound/mismatched environment helper implementation")
    _require(isinstance(expected_environments, dict) and bool(expected_environments),
             "missing independently captured native environments")
    identities = {eid: row.get("identity") for eid, row in expected_environments.items()}
    _require(all(isinstance(eid, str) and eid for eid in identities), "invalid environment ID")
    _require(_same_json(receipt.get("environments"), expected_environments), "native environment coverage/identity mismatch")
    helpers = _migration_environment_helpers()
    for eid, captured in expected_environments.items():
        try:
            helpers.verify_environment(captured["identity"], root)
            actual = helpers.environment_identity(root, captured["setup"])
            _require(_same_json(actual, captured["identity"]), f"incomplete captured environment: {eid}")
        except (OSError, ValueError, KeyError, TypeError) as error:
            raise UsageEvidenceError(f"stale/invalid native environment {eid}: {error}") from error

    _require(isinstance(expected_roles, list) and bool(expected_roles), "missing expected source roles")
    roles = {}
    for role in expected_roles:
        _require(isinstance(role, dict), "malformed expected role")
        rid, path = role.get("id"), role.get("path")
        _require(isinstance(rid, str) and rid and rid not in roles,
                 "invalid/duplicate expected role ID")
        _require(path in expected_sources and role.get("environment") in identities
                 and isinstance(role.get("role"), str) and role["role"], "unbound source role/context")
        commands = role.get("commands")
        _require(isinstance(commands, list), "missing independent command inventory")
        _require(role.get("coverage") in {"commands", "import-only"}, "unresolved source coverage role")
        _require(bool(commands) == (role["coverage"] == "commands"),
                 "import-only/missing declaration-command mismatch")
        command_ids = set()
        for command in commands:
            _require(isinstance(command, dict), "malformed command inventory")
            cid = command.get("id")
            _require(isinstance(cid, str) and cid and cid not in command_ids,
                     "invalid/duplicate native command identity")
            command_ids.add(cid)
            _span(command.get("span"), len(raw[path]))
            _require(command.get("mode") in {"elaborated", "reference-adapter"},
                     "unresolved native command mode")
            if command["mode"] == "reference-adapter":
                _require(command.get("adapter") in expected_bindings, "unbound native role adapter")
        roles[rid] = role
    _require({r["path"] for r in roles.values()} == set(expected_sources), "omitted source role coverage")
    received_roles = receipt.get("roles")
    _require(isinstance(received_roles, list) and len(received_roles) == len(roles),
             "omitted/duplicate native role coverage")
    received_ids = set()
    for role in received_roles:
        _require(isinstance(role, dict) and role.get("id") in roles
                 and role["id"] not in received_ids, "unknown/duplicate native source role")
        received_ids.add(role["id"])
        _require(_same_json({k: v for k, v in role.items() if k != "references"}, roles[role["id"]]),
                 "native role/command coverage mismatch")

    _require(isinstance(expected_declarations, list) and bool(expected_declarations),
             "missing independently captured declaration provenance")
    _require(_same_json(receipt.get("declarations"), expected_declarations),
             "declaration provenance differs from independent candidate graph")
    declarations = {}
    environment_names = set()
    for row in expected_declarations:
        _require(isinstance(row, dict), "malformed native declaration provenance")
        did = row.get("id")
        _require(isinstance(did, str) and did and did not in declarations, "duplicate declaration origin ID")
        # Reuse the v1 metadata language without conflating repeated public names.
        declaration_index([{**row, "owner": row.get("name")}])
        _require(row["theorem"] == (row["kind"] == "theorem"), "inconsistent native theorem/kind metadata")
        _require(row.get("environment") in identities
                 and row.get("population") in {"production", "nonproduction"}, "unbound declaration origin")
        environment_name = (row["environment"], row["name"])
        _require(environment_name not in environment_names, "conflicting same-name declaration in one environment")
        environment_names.add(environment_name)
        if v3:
            _require(row.get("origin_kind") in {"analysis-source", "imported-module"}, "missing tagged native origin")
            levels = row.get("level_params")
            _require(isinstance(levels, list) and all(isinstance(n, str) and n for n in levels)
                     and len(set(levels)) == len(levels), "missing ordered native universe parameters")
        if v3 and row["origin_kind"] == "imported-module":
            _imported_origin(row, expected_environments, raw, expected_bindings)
        else:
            _require(row.get("origin_role") in roles, "unbound declaration origin")
            origin_role = roles[row["origin_role"]]
            source = row.get("source")
            _require(isinstance(source, dict) and source.get("path") == origin_role["path"]
                     and source.get("sha256") == expected_sources[origin_role["path"]]
                     and row["environment"] == origin_role["environment"], "declaration source/environment impostor")
            _span(source.get("span"), len(raw[source["path"]]))
            _require(origin_role["coverage"] == "commands" and any(
                c["span"][0] <= source["span"][0] < source["span"][1] <= c["span"][1]
                for c in origin_role["commands"]), "declaration missing from original command inventory")
            _require(row["population"] != "production" or origin_role["role"] == "production",
                     "nonproduction source impersonates production declaration")
            if v3:
                _require("imported" not in row, "local origin carries foreign exemption")
                _range_attachment(source.get("range"), raw[source["path"]], row["owner"])
        fingerprint = row.get("type_identity")
        _require(isinstance(fingerprint, dict) and fingerprint.get("scheme") == "lean4.34-expr-hash64"
                 and isinstance(fingerprint.get("value"), str) and len(fingerprint["value"]) == 16
                 and all(c in "0123456789abcdef" for c in fingerprint["value"]),
                 "missing structural type identity; pretty text is insufficient")
        declarations[did] = row
    for row in declarations.values():
        owner = row.get("owner")
        _require("owner" in row and (owner is None or owner in declarations), "unknown native declaration owner")
        if owner is not None:
            _require(declarations[owner]["owner"] == owner and
                     declarations[owner]["population"] == row["population"], "noncanonical/cross-population owner")

    observations = {}
    if v3:
        _require(isinstance(expected_observations, list) and bool(expected_observations)
                 and _same_json(receipt.get("observations"), expected_observations),
                 "missing/mismatched independent saved-context observations")
        for observation in expected_observations:
            _require(isinstance(observation, dict), "malformed native observation")
            oid, rid, did = observation.get("id"), observation.get("role"), observation.get("declaration")
            _require(isinstance(oid, str) and oid and oid not in observations and rid in roles
                     and did in declarations, "unknown/duplicate native observation")
            role = roles[rid]
            command = observation.get("command")
            _require("command" in observation and (command is None or command in {c["id"] for c in role["commands"]})
                     and observation.get("environment") == role["environment"]
                     and observation.get("scope") in {"use", "defining-metadata"}, "unbound native observation context")
            _native_capture(observation.get("capture"), expected_bindings, role["environment"])
            origin = declarations[did]
            binding = observation.get("origin_binding")
            setup = expected_environments[role["environment"]]["setup"]
            _require(isinstance(binding, dict) and binding.get("module") == origin["module"],
                     "missing actual observation module/artifact binding")
            if binding.get("kind") == "local":
                _require(origin["origin_kind"] == "analysis-source" and origin["environment"] == role["environment"]
                         and setup.get("name") == origin["module"] and binding.get("parts") is None,
                         "observation substituted local defining context")
            else:
                parts = setup.get("importArts", {}).get(origin["module"])
                _require(binding.get("kind") == "imported-module" and parts is not None
                         and _same_json(binding.get("parts"), parts),
                         "observation target absent from actual imported module/artifacts")
            _require(observation.get("observed_kind") in {"theorem", "def", "opaque", "axiom", "constructor", "recursor", "inductive", "instance"}
                     and _same_json(observation.get("level_params"), origin["level_params"])
                     and _same_json(observation.get("type_identity"), origin["type_identity"])
                     and observation.get("type_comparison") == "lean4.34-expr.equal+ordered-levelParams",
                     "missing bound native full-type/universe comparison")
            same_kind = observation["observed_kind"] == origin["kind"]
            _require((same_kind and observation.get("view_relation") == "same-kind") or
                     (not same_kind and {observation["observed_kind"], origin["kind"]} == {"theorem", "axiom"}
                      and observation.get("view_relation") == "theorem-axiom-export"),
                     "unbound observed/defining-kind view relation")
            observations[oid] = observation

    _require(isinstance(expected_visibility, list) and bool(expected_visibility),
             "missing independent native visibility/origin capture")
    _require(_same_json(receipt.get("visibility"), expected_visibility), "native visibility/origin mismatch")
    visibility = {}
    for context in expected_visibility:
        _require(isinstance(context, dict), "malformed native visibility context")
        vid, rid = context.get("id"), context.get("role")
        _require(isinstance(vid, str) and vid and vid not in visibility and rid in roles,
                 "unknown/duplicate visibility context")
        _require("command" in context and (context["command"] is None or
                 context["command"] in {c["id"] for c in roles[rid]["commands"]}),
                 "unbound visibility command context")
        visible = context.get("declarations")
        _require(isinstance(visible, list) and all(isinstance(d, str) and d in declarations for d in visible)
                 and len(set(visible)) == len(visible), "unknown/duplicate visible declaration origin")
        # One actual Environment cannot contain two different constants at one Name.
        _require(len({declarations[d]["name"] for d in visible}) == len(visible),
                 "conflicting same-name origins in native visibility context")
        if v3:
            observed = context.get("observations")
            _require(isinstance(observed, list) and all(isinstance(o, str) for o in observed)
                     and len(set(observed)) == len(observed)
                     and all(o in observations and observations[o]["role"] == rid
                             and observations[o]["command"] == context["command"] for o in observed)
                     and len(observed) == len(visible)
                     and {observations[o]["declaration"] for o in observed} == set(visible),
                     "visibility lacks exact independent observation/origin mapping")
        visibility[vid] = context

    uses = {}
    def credit(did, evidence, parent=None):
        owner = declarations[did]["owner"]
        if owner is not None and declarations[owner]["theorem"] and declarations[owner]["population"] == "production":
            if parent is None or declarations[parent]["owner"] != owner:
                uses.setdefault(owner, []).append(evidence)

    for role in received_roles:
        refs = role.get("references")
        _require(isinstance(refs, list), "missing native references")
        _require(role["coverage"] != "import-only" or not refs, "reference in import-only source")
        commands = {c["id"]: c for c in role["commands"]}
        for ref in refs:
            _require(isinstance(ref, dict) and ref.get("command") in commands
                     and ref.get("declaration") in declarations, "unknown native reference identity")
            vid = ref.get("visibility")
            _require(vid in visibility and visibility[vid]["role"] == role["id"]
                     and visibility[vid]["command"] == ref["command"]
                     and ref["declaration"] in visibility[vid]["declarations"],
                     "resolved declaration invisible in actual native reference context")
            if v3:
                oid = ref.get("observation")
                _require(oid in visibility[vid]["observations"]
                         and observations[oid]["declaration"] == ref["declaration"]
                         and observations[oid]["scope"] == "use", "reference substituted metadata/use observation")
            _require(ref.get("kind") in KINDS and "parent" in ref,
                     "missing native reference kind/explicit parent")
            parent = ref["parent"]
            _require(parent is None or parent in declarations, "unknown native parent origin")
            if parent is not None:
                _require(declarations[parent].get("origin_role") == role["id"], "parent from a different source context")
            lo, hi = _span(ref.get("span"), len(raw[role["path"]]))
            command = commands[ref["command"]]
            _require(command["span"][0] <= lo < hi <= command["span"][1], "native reference outside command")
            credit(ref["declaration"], {"path": role["path"], "context": role["id"], **ref}, parent)

    request_index = {}
    for request in requests:
        _require(isinstance(request, dict), "malformed original static request")
        key = _request_id(request.get("id"))
        _require(key not in request_index, "duplicate original static request ID")
        if "data_origin" in request or "check_operation" in request:
            for field in ("data_origin", "check_operation"):
                origin = request.get(field)
                _require(isinstance(origin, dict) and origin.get("path") in raw
                         and origin.get("sha256") == hashlib.sha256(raw[origin["path"]]).hexdigest(),
                         "unbound original static request provenance")
                lo, hi = origin.get("line"), origin.get("end_line")
                _require(type(lo) is int and type(hi) is int and
                         1 <= lo <= hi <= len(raw[origin["path"]].splitlines()),
                         "original static request line span outside source")
            _require(isinstance(request.get("name_request"), str) and request["name_request"],
                     "missing original static name request")
        else:
            path = request.get("path")
            _require(path in raw and request.get("source_sha256") == hashlib.sha256(raw[path]).hexdigest(),
                     "unbound original AST static request")
            _span(request.get("span"), len(raw[path]))
            _require(isinstance(request.get("name"), str) and request["name"], "missing AST static name request")
        request_index[key] = request
    contexts = {}
    for context in static_contexts:
        key = _request_id(context.get("id"))
        vid, did = context.get("visibility"), context.get("declaration")
        _require(key in request_index and key not in contexts and context.get("context") in roles
                 and vid in visibility and visibility[vid]["role"] == context["context"]
                 and did in declarations and did in visibility[vid]["declarations"],
                 "unknown/duplicate/unresolved independent static context")
        if v3:
            oid = context.get("observation")
            _require(oid in visibility[vid]["observations"] and observations[oid]["declaration"] == did
                     and context.get("owner_requirement") in {"source", "compiled-origin"}
                     and type(context.get("requires_defining_kind")) is bool,
                     "missing exact static observation/operation owner requirements")
            if context["requires_defining_kind"] and declarations[did]["origin_kind"] == "imported-module":
                _require(declarations[did]["defining_kind"] is not None,
                         "required actual imported defining kind unresolved")
        contexts[key] = context
    _require(set(contexts) == set(request_index), "missing actual resolved static contexts")
    provenance = {}
    for captured in static_provenance:
        _require(isinstance(captured, dict), "malformed validated static provenance witness")
        key = _request_id(captured.get("id"))
        _require(key in request_index and key not in provenance, "unknown/duplicate static provenance witness")
        witness = captured.get("witness")
        _require(isinstance(witness, dict) and
                 captured.get("request_digest_scheme") == REQUEST_DIGEST_SCHEME and
                 _request_id(witness.get("original_request_id")) == key and
                 witness.get("original_request_sha256") == hashlib.sha256(_json_identity(request_index[key])).hexdigest(),
                 "validated witness/raw request identity mismatch")
        request = request_index[key]
        if "check_operation" in request:
            _require(_same_json(witness.get("original_check_operation"), request["check_operation"])
                     and _same_json(witness.get("original_owner_candidates"), request.get("owner_candidates"))
                     and witness.get("name_request") == request["name_request"],
                     "validated witness lost original static provenance")
        _require(isinstance(captured.get("overlay_sha256"), str) and len(captured["overlay_sha256"]) == 64
                 and all(c in "0123456789abcdef" for c in captured["overlay_sha256"]),
                 "missing independently validated overlay binding")
        operation = witness.get("effective_check_operation")
        _require(isinstance(operation, dict) and operation.get("path") in raw and
                 operation.get("sha256") == hashlib.sha256(raw[operation["path"]]).hexdigest(),
                 "unbound effective static checker operation")
        lo, hi = operation.get("line"), operation.get("end_line")
        _require(type(lo) is int and type(hi) is int and
                 1 <= lo <= hi <= len(raw[operation["path"]].splitlines()), "effective operation span outside source")
        did = contexts[key]["declaration"]
        if not v3:
            _require(declarations[did]["source"]["path"] in witness.get("effective_owner_candidates", []),
                     "actual static target outside validated effective owner candidates")
        provenance[key] = captured
    _require(set(provenance) == set(request_index), "missing validated static provenance witness")
    supplements = {}
    if v3:
        _require(isinstance(owner_supplements, list) and
                 _same_json(receipt.get("owner_supplements"), owner_supplements),
                 "missing/mismatched independent native owner supplements")
        for supplement in owner_supplements:
            _require(isinstance(supplement, dict), "malformed native owner supplement")
            key = _request_id(supplement.get("id"))
            _require(key in contexts and key not in supplements, "unknown/duplicate owner supplement ID")
            context, prepared = contexts[key], provenance[key]
            did, oid = context["declaration"], context["observation"]
            origin = declarations[did]
            _require(supplement.get("request_digest_scheme") == REQUEST_DIGEST_SCHEME
                     and supplement.get("request_sha256") == _digest(request_index[key])
                     and supplement.get("overlay_sha256") == prepared["overlay_sha256"]
                     and supplement.get("overlay_row_sha256") == _digest(prepared["witness"])
                     and supplement.get("declaration") == did and supplement.get("observation") == oid
                     and "owner" in supplement and supplement["owner"] == origin["owner"],
                     "owner supplement lost immutable lineage/exact target")
            _native_capture(supplement.get("capture"), expected_bindings, observations[oid]["environment"])
            owner = declarations[origin["owner"]] if origin["owner"] is not None else origin
            source = owner.get("source")
            actual_path = source["path"] if source is not None else None
            witness = supplement.get("owner_witness")
            _require(isinstance(witness, dict) and witness.get("declaration") == owner["id"]
                     and witness.get("module") == owner["module"]
                     and "source_path" in witness and witness["source_path"] == actual_path,
                     "owner supplement lacks actual canonical source/module witness")
            if context["owner_requirement"] == "source":
                _require(actual_path is not None, "required actual source owner unresolved")
            hints = prepared["witness"].get("effective_owner_candidates")
            _require(isinstance(hints, list), "missing unchanged preparation owner hints")
            relation = "confirmed" if actual_path is not None and actual_path in hints else "discovered-outside-hints"
            _require(supplement.get("hint_relation") == relation, "owner supplement rewrites/prejudges hint relation")
            supplements[key] = supplement
        _require(set(supplements) == set(request_index), "missing independently resolved owner supplement")
    responses = receipt.get("static_resolutions")
    _require(isinstance(responses, list) and len(responses) == len(request_index),
             "unanswered/duplicate native static requests")
    answered = set()
    for response in responses:
        key = _request_id(response.get("id"))
        _require(key in request_index and key not in answered, "unknown/duplicate original static response ID")
        answered.add(key)
        request = request_index[key]
        expected_context = contexts[key]
        _require(response.get("context") == expected_context["context"]
                 and response.get("declaration") == expected_context["declaration"]
                 and response.get("visibility") == expected_context["visibility"]
                 and response.get("request_digest_scheme") == REQUEST_DIGEST_SCHEME
                 and response.get("request_sha256") == hashlib.sha256(_json_identity(request)).hexdigest()
                 and response.get("provenance_sha256") == hashlib.sha256(_json_identity(provenance[key])).hexdigest(),
                 "static request provenance/resolved-context mismatch")
        if v3:
            _require(response.get("observation") == expected_context["observation"]
                     and response.get("supplement_sha256") == _digest(supplements[key]),
                     "static response substituted owner supplement/observation")
        credit(response["declaration"], {"kind": "script-check", "request": request,
                                       "provenance": provenance[key], **response})
    # Recheck actual bytes at acceptance, not only before indexing.
    for captured in expected_environments.values():
        try:
            helpers.verify_environment(captured["identity"], root)
        except (OSError, ValueError) as error:
            raise UsageEvidenceError(f"native environment changed during acceptance: {error}") from error
    for path, data in raw.items():
        _require(_read(root, path) == data, f"native input changed during acceptance: {path}")
    return {"schema": schema, "scope": "transport-only; native resolution controls required",
            "declarations": declarations, "uses": uses}


def reconcile_historical(original_keys: list[str], aliases: dict[str, dict],
                         declarations: dict[str, dict], used: set[str]) -> list[dict]:
    """Keep every historical row, including distinct spellings of one declaration."""
    _require(len(set(original_keys)) == len(original_keys), "duplicate original historical row")
    _require(set(aliases) == set(original_keys), "missing/extra historical identity accounting")
    current = [r for r in declarations.values() if r["theorem"] and r["owner"] == r["name"]]
    rows = []
    for key in original_keys:
        old = aliases[key]
        exact = declarations.get(old["name"])
        matches = [exact] if exact is not None else [r for r in current if
            (r["display_name"], r["module"], r["private"]) ==
            (old["display_name"], old["module"], old["private"])]
        _require(len(matches) <= 1, f"ambiguous current historical identity: {key}")
        if matches:
            actual = matches[0]["name"]
            _require(matches[0]["theorem"] and matches[0]["owner"] == actual,
                     f"historical theorem changed declaration kind: {key}")
            rows.append({"original": key, "historical_name": old["name"],
                         "current_name": actual, "status": "used" if actual in used else "unused"})
        else:
            rows.append({"original": key, "historical_name": old["name"],
                         "current_name": None, "status": "absent"})
    return rows
