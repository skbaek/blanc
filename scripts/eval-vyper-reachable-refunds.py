#!/usr/bin/env python3
"""Generate finite V6 refund evidence; never builds, edits, or certifies Lean.

First obtain an owned build of the two observer imports. Coordinate one registered
artifact-integrity sweep with the master, then reuse that exact receipt only while
its source/compiler/imported-artifact snapshot remains unchanged. All Lean CLI
processes acquire/release their own host admission. No semantic fixture campaign.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OBSERVER = "scripts/eval-vyper-reachable-refunds.lean"
DRIVER = "scripts/eval-vyper-reachable-refunds.py"
SCHEMA = "vyper-reachable-refunds-v1"
FORKS = ("prague", "osaka", "bpo1", "bpo2")
MINUS = ("implCreateMsg", "cloneCreateMsg", "initMsg", "tokenCreateMsg",
         "attackerCreateMsg", "approveMsg", "addMsg", "Viol.violMsg")
PLUS = ("Reach.implCreateMsg", "Reach.cloneCreateMsg", "Fund.tokenCreateMsg",
        "Fund.receiverCreateMsg")
TIMEOUT = 300  # First-attempt operational bound, not a registered gate timeout.
INPUT_FILES = (
    "Blanc.lean", "lean-toolchain", "lakefile.lean", "lake-manifest.json", OBSERVER, DRIVER,
    "scripts/lift/certificates.json", "scripts/check-layering.py", "scripts/gate-semaphore.sh",
    "scripts/check-lake-artifact-cache.sh", "scripts/check-lake-artifact-cache.lean",
)
INPUT_TREES = ("Blanc", "scripts/lift/inputs")


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def digest(path: Path) -> str:
    require(path.is_file() and not path.is_symlink(), f"regular file required: {path}")
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        require(key not in obj, "duplicate JSON key")
        obj[key] = value
    return obj


def decode(text: str):
    try:
        return json.loads(text, object_pairs_hook=unique_object,
                          parse_constant=lambda _: (_ for _ in ()).throw(Refused("nonfinite JSON")))
    except (json.JSONDecodeError, UnicodeError) as exc:
        raise Refused("malformed or partial JSON") from exc


def validate_output(text: str, fork: str) -> dict:
    require(fork in FORKS, "unknown covered fork")
    obj = decode(text)
    require(type(obj) is dict and set(obj) == {
        "schema", "fork", "completed", "prerequisiteMessages", "Vminus", "Vplus"},
        "observer envelope keys differ")
    require(obj["schema"] == SCHEMA and obj["fork"] == fork, "observer schema/fork differs")
    require(obj["completed"] is True and obj["prerequisiteMessages"] == "17",
            "observer chain incomplete")
    for side, expected in (("Vminus", MINUS), ("Vplus", PLUS)):
        rows = obj[side]
        require(type(rows) is list and len(rows) == len(expected), "refund row population differs")
        labels = []
        for row in rows:
            require(type(row) is dict and set(row) == {"message", "refundCounter"},
                    "refund row keys differ")
            require(type(row["message"]) is str, "refund message label malformed")
            labels.append(row["message"])
            counter = row["refundCounter"]
            require(type(counter) is str and re.fullmatch(r"0|-?[1-9][0-9]*", counter) is not None,
                    "refund counter is not canonical signed decimal")
        require(tuple(labels) == expected, "refund message order/duplicates differ")
    return obj


def validate_population(rows: list[dict]) -> None:
    require(type(rows) is list and len(rows) == 4, "fork receipt population differs")
    require(tuple(row.get("fork") for row in rows) == FORKS, "fork receipt order/duplicates differ")
    for row, fork in zip(rows, FORKS):
        validate_output(json.dumps(row), fork)


def git(directory: Path, *args: str) -> str:
    env = environment()
    command = [str(executable("git", env["PATH"])), "-c", "core.fsmonitor=false",
               "-c", "core.untrackedCache=false", "-c", "core.excludesFile=/dev/null", *args]
    result = subprocess.run(command, cwd=directory, capture_output=True, text=True, env=env)
    require(result.returncode == 0, "Git provenance command failed")
    return result.stdout.strip()


def compiler_directory() -> Path:
    name = (ROOT / "lean-toolchain").read_text().strip()
    require(re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+", name) is not None,
            "unsupported pinned compiler")
    directory = Path.home() / ".elan/toolchains" / name.replace("/", "--").replace(":", "---")
    require(directory.is_dir() and not directory.is_symlink(), "pinned compiler missing or aliased")
    return directory


def executable(name: str, search_path: str | None = None) -> Path:
    selected = shutil.which(name, path=search_path)
    require(selected is not None, f"required executable unresolved: {name}")
    path = Path(selected).resolve(strict=True)
    require(path.is_file() and os.access(path, os.X_OK), f"required executable unavailable: {name}")
    return path


def timeout_command() -> list[str]:
    path = executable("timeout")
    # The host shim uses env python3. Dispatch that script with this exact,
    # fingerprinted interpreter rather than relying on another child PATH.
    header = path.read_bytes()[:128]
    if header.startswith(b"#!"):
        require(header.startswith(b"#!/usr/bin/env python3\n"), "unsupported timeout interpreter")
        return [str(Path(sys.executable).resolve(strict=True)), str(path)]
    return [str(path)]


def environment() -> dict[str, str]:
    cache = os.environ.get("LAKE_CACHE_DIR", "")
    require(cache and Path(cache).is_absolute(), "absolute LAKE_CACHE_DIR required")
    require(Path(cache).is_dir() and not Path(cache).is_symlink(), "active cache missing or aliased")
    require((Path(cache) / "artifacts").is_dir(), "active cache artifacts absent")
    require(os.environ.get("BLANC_GATE_SEMAPHORE", "") == "", "host admission override refused")
    require(not os.environ.get("BLANC_GATE_SEMAPHORE_MEMORY_GIB"), "memory admission override refused")
    python = Path(sys.executable).resolve(strict=True)
    child_path = os.pathsep.join((str(compiler_directory() / "bin"), str(python.parent), os.defpath))
    require(executable("python3", child_path) == python, "admission Python resolution differs")
    return {"HOME": str(Path.home()), "PATH": child_path, "LANG": "C.UTF-8", "LAKE_CACHE_DIR": cache,
            "BLANC_GATE_SEMAPHORE_WAIT": "60", "PYTHONDONTWRITEBYTECODE": "1",
            "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null",
            "GIT_CONFIG_SYSTEM": "/dev/null", "GIT_CONFIG_COUNT": "0"}


def load_header_parser():
    spec = importlib.util.spec_from_file_location("vyper_refund_header", ROOT / "scripts/check-layering.py")
    require(spec is not None and spec.loader is not None, "repository import parser unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    # imports_of intentionally filters to Blanc and strips its namespace for
    # architecture checks. Reuse the validated header grammar while retaining
    # every package-qualified import needed by this artifact-closure contract.
    class FullHeaderScanner(module.HeaderScanner):
        @staticmethod
        def local_module(components):
            return ".".join(components)

    return lambda path: FullHeaderScanner(path.read_text(encoding="utf-8")).imports()


def imported_files(toolchain: Path) -> dict[str, str]:
    """Fingerprint actual source and compiled closure; depHash alone is insufficient."""
    imports = load_header_parser()
    packages = sorted((ROOT / ".lake/packages").iterdir())
    locations = [(ROOT, ROOT / ".lake/build/lib/lean")]
    locations += [(p, p / ".lake/build/lib/lean") for p in packages if p.is_dir()]
    locations += [(toolchain / "src/lean", toolchain / "lib/lean")]
    locations += [(toolchain / "src/lean/lake", toolchain / "lib/lean")]
    todo = ["Init", *imports(ROOT / OBSERVER)]
    seen = set()
    result = {}
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        relative = Path(*name.split("."))
        candidates = [(source / relative.with_suffix(".lean"), compiled / relative)
                      for source, compiled in locations
                      if (source / relative.with_suffix(".lean")).is_file()]
        require(len(candidates) == 1, f"import source missing or ambiguous: {name}")
        source, stem = candidates[0]
        result[str(source)] = digest(source)
        require(stem.with_suffix(".olean").is_file(), f"compiled import absent: {name}")
        artifacts = sorted(stem.parent.glob(stem.name + ".*"))
        require(artifacts, f"compiled import population absent: {name}")
        for artifact in artifacts:
            result[str(artifact)] = digest(artifact)
        todo.extend(imports(source))
    return result


def snapshot() -> dict:
    toolchain = compiler_directory()
    files = {}
    for name in INPUT_FILES:
        files[str(ROOT / name)] = digest(ROOT / name)
    # Membership and bytes, including untracked production modules. Unrelated
    # documents and Git commit metadata are not observation validity inputs.
    for tree in INPUT_TREES:
        paths = sorted((ROOT / tree).rglob("*.lean" if tree == "Blanc" else "*"))
        population = [path for path in paths if path.is_file() or path.is_symlink()]
        require(population, f"declared input population empty: {tree}")
        for path in population:
            files[str(path)] = digest(path)
    manifest = decode((ROOT / "lake-manifest.json").read_text())
    packages = {}
    for row in manifest["packages"]:
        package = ROOT / ".lake/packages" / row["name"]
        require(package.is_dir() and not package.is_symlink(), "locked package missing or aliased")
        head = git(package, "rev-parse", "HEAD")
        require(head == row["rev"] and git(package, "status", "--porcelain") == "",
                "locked package pin/source differs")
        packages[row["name"]] = head
    libraries = sorted((toolchain / "lib/lean").glob("*shared*"))
    require(libraries, "compiler shared libraries absent")
    for path in (toolchain / "bin/lake", toolchain / "bin/lean", *libraries):
        if path.is_file():
            files[str(path)] = digest(path)
    env = environment()
    python = Path(sys.executable).resolve(strict=True)
    bash = executable("bash", env["PATH"])
    timeout = timeout_command()
    tools = {"Python": {"path": str(python), "version": sys.version},
             "Bash": {"path": str(bash), "version": subprocess.run(
                 [str(bash), "--version"], capture_output=True, text=True, check=True).stdout},
             "Lean/Lake": {"toolchain": (ROOT / "lean-toolchain").read_text().strip()},
             "timeout": {"command": timeout}}
    for path in {python, bash, *(Path(part) for part in timeout)}:
        files[str(path)] = digest(path)
    # Exact shell tools called by the admitted wrappers; no OS-wide fingerprint.
    for name in ("git", "printenv", "dirname", "basename"):
        path = executable(name, env["PATH"])
        tools[name] = {"path": str(path)}
        files[str(path)] = digest(path)
    python_libs = sorted((Path(sys.base_prefix) / "lib").glob("libpython*.*"))
    for path in python_libs:
        if path.is_file():
            resolved = path.resolve(strict=True)
            files[str(resolved)] = digest(resolved)
    closure = imported_files(toolchain)
    # Bound the actual loaded Python module closure supporting protocol/receipt
    # validation and admission, not the complete OS or Python installation.
    python_modules = {}
    for name, module in sorted(tuple(sys.modules.items())):
        filename = getattr(module, "__file__", None)
        if filename:
            path = Path(filename).resolve(strict=True)
            if path.is_file():
                python_modules[name] = {"path": str(path), "sha256": digest(path)}
                cached = getattr(module, "__cached__", None)
                if cached and Path(cached).is_file():
                    cache_path = Path(cached).resolve(strict=True)
                    python_modules[name]["bytecode_cache"] = {
                        "path": str(cache_path), "sha256": digest(cache_path)}
        else:
            spec = getattr(module, "__spec__", None)
            origin = getattr(spec, "origin", None)
            if origin in ("built-in", "frozen"):
                python_modules[name] = {"origin": origin, "runtime": str(python)}
    host = Path.home() / "creme"
    entry = host / ".semaphore/semaphore"
    require(entry.is_file() and os.access(entry, os.X_OK), "host semaphore entrypoint missing")
    files[str(entry)] = digest(entry)
    # The entrypoint imports Creme's Python admission implementation. Mutable
    # semaphore state is deliberately excluded from byte validity.
    for path in sorted((host / "creme").rglob("*.py")):
        files[str(path)] = digest(path)
    return {"validity_inputs": {"contract": "vyper-refund-inputs-v2", "files": files,
            "packages": packages, "imported_files": closure, "tools": tools,
            "python_modules": python_modules, "environment": env}, "provenance": {"head": git(ROOT, "rev-parse", "HEAD"),
            "branch": git(ROOT, "branch", "--show-current"), "worktree": str(ROOT)}}


def same_inputs(left: dict, right: dict) -> bool:
    require(type(left) is dict and set(left) == {"validity_inputs", "provenance"} and
            type(right) is dict and set(right) == {"validity_inputs", "provenance"},
            "snapshot validity/provenance split malformed")
    return left["validity_inputs"] == right["validity_inputs"]


ADMITTED_SHELL = r'''set -euo pipefail
. scripts/gate-semaphore.sh
test -x "$GATE_SEMAPHORE_ENTRY" || { echo 'REFUSED: host admission unavailable' >&2; exit 2; }
trap 'gate_semaphore_release' EXIT
gs_class="$1"
shift
gate_semaphore_acquire "Vyper reachable refund observations" 4 "$gs_class" || exit 2
test -n "$GATE_SEMAPHORE_HELD" || { echo 'REFUSED: process-owned admission required' >&2; exit 2; }
printf 'admission-begin\n%s\nadmission-end\n' "$gs_out" >&2
"$@"
'''


def admission_status(text: str) -> str:
    blocks = re.findall(r"(?ms)^admission-begin\n(.*?)\nadmission-end$", text)
    require(len(blocks) == 1, "admission block absent or duplicate")
    statuses = re.findall(r"(?m)^OK — (ADMITTED_(?:SOFT|HARD)) — ", blocks[0])
    require(len(statuses) == 1, "successful admitted process receipt absent")
    return statuses[0]


def admitted(command: list[str], directory: Path, name: str, contention: str = "tolerant") -> dict:
    require(contention in ("tolerant", "exclusive"), "unsupported admission class")
    env = environment()
    timeout = timeout_command()
    actual = [str(executable("bash", env["PATH"])), "-c", ADMITTED_SHELL, "vyper-refunds", contention,
              *timeout, str(TIMEOUT), *command]
    stdout, stderr = directory / (name + ".stdout"), directory / (name + ".stderr")
    print(f"process {name}: requesting admission; timeout {TIMEOUT}s after admission", flush=True)
    with stdout.open("xb") as out, stderr.open("xb") as err:
        result = subprocess.run(actual, cwd=ROOT, stdout=out, stderr=err, env=env)
    record = {"command": command, "admitted_shell": ADMITTED_SHELL, "cwd": str(ROOT),
              "invocation": actual, "contention": contention,
              "timeout_seconds": TIMEOUT, "timeout_command": timeout, "exit": result.returncode,
              "stdout": str(stdout), "stderr": str(stderr),
              "stdout_sha256": digest(stdout), "stderr_sha256": digest(stderr)}
    write_json(directory / (name + ".process.json"), record)
    require(result.returncode == 0, f"subprocess failure: {name} exit {result.returncode}")
    admission_status(stderr.read_text())
    return record


def write_json(path: Path, value) -> None:
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def integrity(directory: Path) -> None:
    directory.mkdir(parents=True, exist_ok=False)
    before = snapshot()
    process = admitted([str(executable("bash", environment()["PATH"])), "scripts/check-lake-artifact-cache.sh"],
                       directory, "integrity", "exclusive")
    after = snapshot()
    require(same_inputs(before, after), "source/compiler/artifact drift during integrity check")
    stdout = Path(process["stdout"]).read_text()
    require(re.fullmatch(r"OK — Lake artifact cache: verified [1-9][0-9]* cache artifacts and [1-9][0-9]* materialized outputs\n", stdout) is not None,
            "registered integrity verdict absent or vacuous")
    write_json(directory / "integrity.json", {"schema": "vyper-refund-integrity-v1",
               "status": "OK", "snapshot": before, "process": process})


def check_integrity(receipt: Path, current: dict) -> dict:
    data = decode(receipt.read_text())
    require(type(data) is dict and set(data) == {"schema", "status", "snapshot", "process"},
            "integrity receipt keys differ")
    require(data["schema"] == "vyper-refund-integrity-v1" and data["status"] == "OK",
            "successful integrity receipt absent")
    require(same_inputs(data["snapshot"], current), "integrity receipt source/compiler/artifact drift")
    process = data["process"]
    require(type(process) is dict and set(process) == {
        "command", "admitted_shell", "cwd", "invocation", "contention", "timeout_seconds", "timeout_command", "exit", "stdout", "stderr",
        "stdout_sha256", "stderr_sha256"}, "integrity process keys differ")
    bash = str(executable("bash", environment()["PATH"]))
    expected_command = [bash, "scripts/check-lake-artifact-cache.sh"]
    expected_invocation = [bash, "-c", ADMITTED_SHELL, "vyper-refunds", "exclusive",
                           *timeout_command(), str(TIMEOUT), *expected_command]
    require(process["command"] == expected_command and process["invocation"] == expected_invocation and
            process["contention"] == "exclusive" and
            process["cwd"] == str(ROOT) and type(process["exit"]) is int and process["exit"] == 0 and
            process["timeout_seconds"] == TIMEOUT and process["timeout_command"] == timeout_command() and
            process["admitted_shell"] == ADMITTED_SHELL,
            "registered integrity process differs")
    for channel in ("stdout", "stderr"):
        require(digest(Path(process[channel])) == process[channel + "_sha256"], "integrity raw output drift")
    require(re.fullmatch(r"OK — Lake artifact cache: verified [1-9][0-9]* cache artifacts and [1-9][0-9]* materialized outputs\n",
                         Path(process["stdout"]).read_text()) is not None,
            "registered integrity verdict absent or vacuous")
    admission_status(Path(process["stderr"]).read_text())
    return data


def observe(directory: Path, integrity_path: Path) -> None:
    directory.mkdir(parents=True, exist_ok=False)
    before = snapshot()
    check_integrity(integrity_path, before)
    compiler = compiler_directory()
    rows, processes = [], []
    for fork in FORKS:
        require(same_inputs(snapshot(), before), "source/compiler/artifact drift before observer")
        command = [str(compiler / "bin/lake"), "env", str(compiler / "bin/lean"), "--run", OBSERVER, fork]
        process = admitted(command, directory, fork)
        require(same_inputs(snapshot(), before), "source/compiler/artifact drift after observer")
        rows.append(validate_output(Path(process["stdout"]).read_text(), fork))
        processes.append(process)
    validate_population(rows)
    require(same_inputs(snapshot(), before), "source/compiler/artifact drift before receipt")
    write_json(directory / "refunds.json", {"schema": "vyper-refund-receipt-v1", "completed": True,
               "scope": "finite signed message-level refund observations; not transaction reimbursement or a universal theorem",
               "prerequisiteMessages": 68, "refundObservations": 48, "snapshot": before,
               "integrity_receipt": str(integrity_path), "integrity_receipt_sha256": digest(integrity_path),
               "processes": processes, "forks": rows})


def validate_receipt(path: Path) -> None:
    data = decode(path.read_text())
    require(type(data) is dict and set(data) == {
        "schema", "completed", "scope", "prerequisiteMessages", "refundObservations", "snapshot",
        "integrity_receipt", "integrity_receipt_sha256", "processes", "forks"},
        "refund receipt keys differ")
    require(data["schema"] == "vyper-refund-receipt-v1" and data["completed"] is True and
            type(data["prerequisiteMessages"]) is int and data["prerequisiteMessages"] == 68 and
            type(data["refundObservations"]) is int and data["refundObservations"] == 48,
            "refund receipt incomplete")
    current = snapshot()
    require(same_inputs(data["snapshot"], current), "refund receipt source/compiler/artifact drift")
    integrity_path = Path(data["integrity_receipt"])
    require(digest(integrity_path) == data["integrity_receipt_sha256"], "integrity receipt bytes drift")
    check_integrity(integrity_path, current)
    processes = data["processes"]
    require(type(processes) is list and len(processes) == 4, "fork process population differs")
    compiler = compiler_directory()
    observed = []
    for process, fork in zip(processes, FORKS):
        command = [str(compiler / "bin/lake"), "env", str(compiler / "bin/lean"), "--run", OBSERVER, fork]
        require(type(process) is dict and set(process) == {
            "command", "admitted_shell", "cwd", "invocation", "contention", "timeout_seconds", "timeout_command", "exit", "stdout", "stderr",
            "stdout_sha256", "stderr_sha256"}, "fork process keys differ")
        invocation = [str(executable("bash", environment()["PATH"])), "-c", ADMITTED_SHELL,
                      "vyper-refunds", "tolerant", *timeout_command(), str(TIMEOUT), *command]
        require(process["command"] == command and process["invocation"] == invocation and
                process["contention"] == "tolerant" and process["cwd"] == str(ROOT) and
                process["admitted_shell"] == ADMITTED_SHELL and process["timeout_seconds"] == TIMEOUT and
                process["timeout_command"] == timeout_command() and
                type(process["exit"]) is int and process["exit"] == 0,
                "fork process command/exit/admission differs")
        for channel in ("stdout", "stderr"):
            require(digest(Path(process[channel])) == process[channel + "_sha256"], "fork raw output drift")
        admission_status(Path(process["stderr"]).read_text())
        observed.append(validate_output(Path(process["stdout"]).read_text(), fork))
    validate_population(data["forks"])
    require(data["forks"] == observed, "refund rows differ from immutable raw output")
    require(same_inputs(snapshot(), current), "source/compiler/artifact drift during receipt validation")
    print("OK — Vyper refund receipt: 68 successful prerequisite messages; 48 signed finite observations")


def self_test() -> None:
    # Protocol-only data; deliberately no claimed execution or EVM assertion.
    valid = {"schema": SCHEMA, "fork": "prague", "completed": True, "prerequisiteMessages": "17",
             "Vminus": [{"message": name, "refundCounter": "0"} for name in MINUS],
             "Vplus": [{"message": name, "refundCounter": "-1"} for name in PLUS]}
    text = json.dumps(valid)
    validate_output(text, "prague")
    changes = []
    for key, value, diagnostic in [
        ("fork", "unknown", "observer schema/fork differs"),
        ("completed", False, "observer chain incomplete"),
        ("prerequisiteMessages", "16", "observer chain incomplete")]:
        bad = copy.deepcopy(valid)
        bad[key] = value
        changes.append((json.dumps(bad), diagnostic))
    for bad_counter in ("-0", "+1", "01", 1):
        bad = copy.deepcopy(valid)
        bad["Vminus"][0]["refundCounter"] = bad_counter
        changes.append((json.dumps(bad), "refund counter is not canonical signed decimal"))
    bad = copy.deepcopy(valid)
    bad["Vminus"].pop()
    changes.append((json.dumps(bad), "refund row population differs"))
    bad = copy.deepcopy(valid)
    bad["Vminus"][1]["message"] = MINUS[0]
    changes.append((json.dumps(bad), "refund message order/duplicates differ"))
    changes += [(text[:-1], "malformed or partial JSON"),
                (text + text, "malformed or partial JSON"),
                (text.replace('"completed": true', '"completed": true, "completed": true'), "duplicate JSON key")]
    for altered, expected in changes:
        try:
            validate_output(altered, "prague")
        except Refused as exc:
            require(str(exc) == expected, "control failed at unexpected diagnostic")
            print("CONTROL — " + expected)
        else:
            raise Refused("protocol control did not bite")
    require(json.dumps(valid) == text, "protocol baseline restoration differs")
    original = {"validity_inputs": {"source": "checked-bytes", "members": ["owner.lean"]},
                "provenance": {"head": "old-head"}}
    moved = copy.deepcopy(original)
    moved["provenance"]["head"] = "new-head"
    require(same_inputs(original, moved), "commit-only provenance movement invalidated inputs")
    original_bytes = json.dumps(original)
    for key, changed in (("source", "changed-bytes"), ("members", [])):
        mutated = copy.deepcopy(original)
        mutated["validity_inputs"][key] = changed
        try:
            require(same_inputs(original, mutated), "source/compiler/artifact drift")
        except Refused as exc:
            require(str(exc) == "source/compiler/artifact drift", "input drift control diagnostic differs")
            print("CONTROL — source/compiler/artifact drift (" + key + ")")
        else:
            raise Refused("input drift control did not bite")
    require(json.dumps(original) == original_bytes, "input contract baseline restoration differs")
    for status in ("ADMITTED_SOFT", "ADMITTED_HARD"):
        sample = f"admission-begin\nfit: queued\nOK — {status} — exact requested reservation\nadmission-end\n"
        require(admission_status(sample) == status, "valid returned admission status refused")
    try:
        admission_status("admission-begin\nREFUSED — no reservation\nadmission-end\n")
    except Refused as exc:
        require(str(exc) == "successful admitted process receipt absent", "admission control diagnostic differs")
        print("CONTROL — successful admitted process receipt absent")
    else:
        raise Refused("admission control did not bite")
    print(f"OK — refund protocol: {len(changes)} malformed/partial, 2 input-drift and 1 admission controls bite; "
          "commit-only provenance accepted; baseline bytes unchanged")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--check-integrity", type=Path, metavar="NEW_DIRECTORY")
    mode.add_argument("--run", type=Path, metavar="NEW_DIRECTORY")
    mode.add_argument("--validate-receipt", type=Path, metavar="REFUNDS_JSON")
    mode.add_argument("--inspect-inputs", type=Path, metavar="NEW_JSON")
    parser.add_argument("--integrity-receipt", type=Path)
    args = parser.parse_args()
    try:
        if args.self_test:
            self_test()
        elif args.check_integrity:
            require(args.integrity_receipt is None, "integrity mode has no receipt input")
            integrity(args.check_integrity.resolve())
        elif args.validate_receipt:
            require(args.integrity_receipt is None, "validation mode reads its receipt's integrity link")
            validate_receipt(args.validate_receipt.resolve(strict=True))
        elif args.inspect_inputs:
            require(args.integrity_receipt is None, "input inspection has no receipt input")
            write_json(args.inspect_inputs.resolve(), snapshot())
            print("OK — input snapshot only; no Lean execution or integrity certification")
        else:
            require(args.integrity_receipt is not None, "exact integrity receipt required")
            observe(args.run.resolve(), args.integrity_receipt.resolve(strict=True))
    except (Refused, OSError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print("REFUSED — Vyper refund observations: " + str(exc), file=sys.stderr)
        raise SystemExit(2)


if __name__ == "__main__":
    main()
