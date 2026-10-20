#!/usr/bin/env python3
"""Synthetic instrument/launcher/helper controls; no real runtime gate is run."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import os
import subprocess
import sys
import tempfile
from pathlib import Path


SCRIPT = Path(__file__).with_name("gate-read-audit.py")
HOOK = Path(__file__).with_name("read-audit")


def load_audit():
    spec = importlib.util.spec_from_file_location("gate_read_audit_tested", SCRIPT)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def exercise(arguments: list[str], *, unknown: bool = False, failed: bool = False) -> tuple[int, list[str], list[str], str, str]:
    module = load_audit()
    cache_calls: list[str] = []
    audited: list[str] = []
    registry = {
        "gates": [
            {"id": "alpha", "kind": "cacheable", "command": ["alpha"]},
            {"id": "beta", "kind": "cacheable", "command": ["beta"]},
        ]
    }
    module.ensure_cold_bytecode_cache = lambda: cache_calls.append("cold") or "cold"
    module.gc.load_registry = lambda _path: registry
    module.interesting_roots = lambda: []
    module.runner_binding_files = lambda: set()
    module.gc.atomic_json = lambda *_args, **_kwargs: None

    def fake_audit(gate, _roots, _bindings):
        audited.append(gate["id"])
        return {
            "id": gate["id"], "command": gate["id"], "exit": 17 if failed and gate["id"] == "alpha" else 0,
            "elapsed_s": 0.0, "reads_observed": 0, "covered": 0,
            "runner_identity": [], "runner_bindings": [], "lake_artifacts": [],
            "in_declared_subtree": [], "declared_untracked": [], "undeclared": [],
            "enumerated_undeclared": [],
            "unverified": ["synthetic unresolved descriptor"] if unknown and gate["id"] == "alpha" else [],
        }

    module.audit_gate = fake_audit
    stdout, stderr = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
        try:
            code = module.main(arguments)
        except SystemExit as error:
            code = int(error.code)
    return code, cache_calls, audited, stdout.getvalue(), stderr.getvalue()


def hook_control() -> None:
    """FD-relative cleanup stays in scratch; real reads and unknowns remain visible."""

    with tempfile.TemporaryDirectory(prefix="gate-read-dirfd-control-") as directory:
        base = Path(directory)
        repo = base / "repo"
        repo.mkdir()
        (repo / ".git").write_text("gitdir: actual-worktree-pointer\n", encoding="utf-8")
        (repo / "subject.txt").write_text("subject\n", encoding="utf-8")
        fixture = base / "fixture"
        (fixture / ".git").mkdir(parents=True)
        (fixture / ".git/config").write_text("fixture\n", encoding="utf-8")
        repo_real, fixture_real = repo.resolve(), fixture.resolve()
        log = base / "opens.log"
        env = dict(os.environ, GATE_READ_AUDIT=str(log), PYTHONPATH=str(HOOK),
                   FIXTURE=str(fixture), PYTHONDONTWRITEBYTECODE="1")
        plain_env = dict(env)
        plain_env.pop("GATE_READ_AUDIT")
        plain = subprocess.run([sys.executable, "-B", "-c",
                                "import shutil; print(shutil.rmtree.avoids_symlink_attacks)"],
                               cwd=repo, env=plain_env, capture_output=True, text=True, check=False)
        assert plain.returncode == 0 and plain.stdout.strip() == "True", plain.stderr

        source = (
            "import os, shutil\n"
            "assert shutil.rmtree.avoids_symlink_attacks\n"
            "with open('subject.txt') as stream: assert stream.read() == 'subject\\n'\n"
            "base = os.open(os.environ['FIXTURE'], os.O_RDONLY)\n"
            "git = os.open('.git', os.O_RDONLY, dir_fd=base)\n"
            "item = os.open('config', os.O_RDONLY, dir_fd=git)\n"
            "assert os.read(item, 7) == b'fixture'\n"
            "with os.scandir(git) as entries: assert [e.name for e in entries] == ['config']\n"
            "os.close(item); os.close(git); os.close(base)\n"
            "shutil.rmtree(os.environ['FIXTURE'])\n"
        )
        result = subprocess.run([sys.executable, "-B", "-c", source], cwd=repo, env=env,
                                capture_output=True, text=True, check=False)
        assert result.returncode == 0, result.stderr
        lines = log.read_text(encoding="utf-8").splitlines()
        assert f"R\t{repo_real / 'subject.txt'}" in lines, lines
        assert f"R\t{fixture_real / '.git/config'}" in lines, lines
        assert f"L\t{fixture_real / '.git'}" in lines, lines
        assert f"R\t{repo_real / '.git'}" not in lines, lines
        assert not any(line.startswith("U\t") for line in lines), lines

        log.unlink()
        direct = subprocess.run([sys.executable, "-B", "-c", "open('.git').read()"],
                                cwd=repo, env=env, capture_output=True, text=True, check=False)
        assert direct.returncode == 0, direct.stderr
        assert f"R\t{repo_real / '.git'}" in log.read_text(encoding="utf-8").splitlines()

        for scenario in ("unknown", "reused", "drift", "unwrapped"):
            log.unlink()
            first, second = base / "first", base / "second"
            first.mkdir(exist_ok=True)
            second.mkdir(exist_ok=True)
            (first / "item").write_text("first", encoding="utf-8")
            (second / "item").write_text("second", encoding="utf-8")
            code = (
                "import os, sitecustomize\n"
                "a = os.open(os.environ['FIRST'], os.O_RDONLY)\n"
                "b = os.open(os.environ['SECOND'], os.O_RDONLY)\n"
                "if os.environ['SCENARIO'] == 'unknown':\n"
                "    d = os.dup(a)\n"
                "elif os.environ['SCENARIO'] == 'reused':\n"
                "    os.dup2(b, a); d = a\n"
                "elif os.environ['SCENARIO'] == 'drift':\n"
                "    os.rename(os.environ['FIRST'], os.environ['FIRST'] + '-old')\n"
                "    os.mkdir(os.environ['FIRST']); d = a\n"
                "else:\n"
                "    d = a\n"
                "if os.environ['SCENARIO'] == 'unwrapped':\n"
                "    item = sitecustomize._OS_OPEN('item', os.O_RDONLY, dir_fd=d)\n"
                "else:\n"
                "    item = os.open('item', os.O_RDONLY, dir_fd=d)\n"
                "os.read(item, 5)\n"
            )
            case_env = dict(env, FIRST=str(first), SECOND=str(second), SCENARIO=scenario)
            result = subprocess.run([sys.executable, "-B", "-c", code], cwd=repo,
                                    env=case_env, capture_output=True, text=True, check=False)
            assert result.returncode == 0, (scenario, result.stderr)
            assert any(line.startswith("U\t") for line in log.read_text(encoding="utf-8").splitlines()), scenario
            if scenario == "drift":
                (base / "first-old/item").unlink()
                (base / "first-old").rmdir()

        log.unlink()
        failed = subprocess.run([sys.executable, "-B", "-c",
                                 "import os\ntry: os.open('missing', os.O_RDONLY, dir_fd=-1)\n"
                                 "except OSError: pass"],
                                cwd=repo, env=env, capture_output=True, text=True, check=False)
        assert failed.returncode == 0, failed.stderr
        assert any(line.startswith("U\t") for line in log.read_text(encoding="utf-8").splitlines())


def declared_untracked_control() -> None:
    """A declared untracked read is reported, not flagged; an undeclared one is.

    Runs the real `audit_gate` against a synthetic root: the gate is a Python
    one-liner that reads two files.  With `subject.txt` declared under
    `inputs.untracked_reads`, only `other.txt` is a hole.  Without the
    declaration both are holes, so the allowance provably does the work.
    """

    module = load_audit()
    with tempfile.TemporaryDirectory(prefix="gate-read-audit-control-") as directory:
        root = Path(directory)
        (root / "subject.txt").write_text("subject\n", encoding="utf-8")
        (root / "other.txt").write_text("other\n", encoding="utf-8")
        module.ROOT = root
        module.OUT_DIR = root / ".lake/read-audit"
        module.gc.ROOT = root
        command = [
            sys.executable, "-c",
            "open('subject.txt').read(); open('other.txt').read()",
        ]
        gate = {
            "id": "synthetic", "kind": "cacheable", "command": command,
            "inputs": {
                "files": ["gate.py"],
                "untracked_reads": [
                    {"path": "subject.txt", "reason": "mutation subject"}
                ],
            },
        }
        (root / "gate.py").write_text("# stand-in harness file\n", encoding="utf-8")
        result = module.audit_gate(gate, [root], set())
        assert result["exit"] == 0, result
        assert result["undeclared"] == ["other.txt"], result
        assert result["declared_untracked"] == [
            {"path": "subject.txt", "reason": "mutation subject"}
        ], result

        undeclared_gate = dict(gate, inputs={"files": ["gate.py"]})
        result = module.audit_gate(undeclared_gate, [root], set())
        assert result["undeclared"] == ["other.txt", "subject.txt"], result
        assert result["declared_untracked"] == [], result

        unknown_gate = dict(gate, id="unresolved-descriptor", command=[
            sys.executable, "-c",
            "import os; fd = os.open('.', os.O_RDONLY); "
            "unknown = os.dup(fd); os.listdir(unknown)",
        ])
        result = module.audit_gate(unknown_gate, [root], set())
        assert result["exit"] == 0 and result["unverified"], result

        # A future Lean subject within the named glob is declared, while a
        # harness read outside that boundary remains a HOLE.
        (root / "Blanc").mkdir()
        (root / "Blanc/SubjectOne.lean").write_text("one\n", encoding="utf-8")
        (root / "Blanc/SubjectTwo.lean").write_text("two\n", encoding="utf-8")
        (root / "Blanc/Other.txt").write_text("other\n", encoding="utf-8")
        (root / "scripts").mkdir()
        (root / "scripts/extra.py").write_text("# harness dependency\n", encoding="utf-8")
        glob_gate = dict(gate, command=[
            sys.executable, "-c",
            "open('Blanc/SubjectOne.lean').read(); "
            "open('Blanc/SubjectTwo.lean').read(); "
            "open('Blanc/Other.txt').read(); open('scripts/extra.py').read()",
        ], inputs={
            "files": ["gate.py"],
            "untracked_reads": [{"root": "Blanc", "pattern": "Subject*.lean",
                                 "reason": "Lean mutation subjects"}],
            "populations": [{"root": "Blanc", "pattern": "Subject*.lean",
                             "mode": "traversable"}],
        })
        result = module.audit_gate(glob_gate, [root], set())
        assert result["undeclared"] == ["Blanc/Other.txt", "scripts/extra.py"], result
        assert result["declared_untracked"] == [
            {"path": "Blanc/SubjectOne.lean", "reason": "Lean mutation subjects"},
            {"path": "Blanc/SubjectTwo.lean", "reason": "Lean mutation subjects"},
        ], result


def tracked_population_coverage_control() -> None:
    module = load_audit()
    with tempfile.TemporaryDirectory(prefix="gate-read-tracked-control-") as directory:
        root = Path(directory).resolve()
        (root / "future").mkdir()
        for name in ("future/Selected.lean", "future/Unselected.lean", "Exempt.lean"):
            (root / name).write_text("example : True := trivial\n", encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "add", "--", "future/Selected.lean", "Exempt.lean"], cwd=root, check=True)
        module.ROOT = root
        module.OUT_DIR = root / "audit"
        module.HOOK_DIR = HOOK
        module.OUT_DIR.mkdir()
        gate = {"id": "tracked", "command": [sys.executable, "-B", "-c",
                "open('future/Selected.lean').read(); open('future/Unselected.lean').read(); open('Exempt.lean').read()"],
                "inputs": {"populations": [
                    {"root": ".", "pattern": "*.lean", "tracked": True, "exclude": ["Exempt.lean"]},
                    {"root": ".", "pattern": "Exempt.lean", "tracked": True, "mode": "membership"},
                ]}}
        result = module.audit_gate(gate, [root], set())
        assert result["exit"] == 0 and result["undeclared"] == ["Exempt.lean", "future/Unselected.lean"], result
        assert not result["unverified"], result
        original = module.gc.glob_population
        def refused(_root, spec):
            if spec.get("tracked"):
                raise module.gc.Unresolvable("synthetic unavailable Git index")
            return original(_root, spec)
        module.gc.glob_population = refused
        try:
            result = module.audit_gate(gate, [root], set())
            assert any("unavailable Git index" in text for text in result["unverified"]), result
            membership_gate = dict(gate, inputs={"populations": [
                {"root": ".", "pattern": "Exempt.lean", "tracked": True, "mode": "membership"},
            ]})
            result = module.audit_gate(membership_gate, [root], set())
            assert any("unavailable Git index" in text for text in result["unverified"]), result
        finally:
            module.gc.glob_population = original


def observer_removal_control() -> None:
    """Green baseline, sole-control loss, then byte-identical restoration only."""
    import hashlib
    import shutil

    with tempfile.TemporaryDirectory(prefix="gate-read-observer-removal-") as directory:
        root = Path(directory)
        copied = root / "observer/scripts/read-audit"
        shutil.copytree(HOOK, copied, ignore=shutil.ignore_patterns("__pycache__"))
        (root / "hidden.txt").write_text("actual hidden input\n")
        module = load_audit()
        module.ROOT, module.OUT_DIR, module.gc.ROOT, module.HOOK_DIR = root, root / "audit", root, copied
        shell = 'SCRIPT_DIR="$1"; . "$SCRIPT_DIR/read-audit/launch.sh"; shift; gate_audit_python "$@"'
        command = ["bash", "-c", shell, "observer-removal", str(copied.parent),
                   "/usr/bin/env", "-i", "PATH=/usr/bin:/bin", sys.executable, "-I", "-c",
                   "assert open('hidden.txt').read() == 'actual hidden input\\n'"]

        def audit(name):
            return module.audit_gate({"id": name, "command": command, "inputs": {}}, [root], set())

        def assert_hole(result):
            assert result["exit"] == 0 and not result["unverified"], result
            assert "hidden.txt" in result["undeclared"], result

        baseline = audit("observer-green-baseline")
        assert_hole(baseline)
        print("CONTROL observer green baseline: actual env-i/-I hidden.txt read is HOLE with matching receipts")
        bootstrap = copied / "bootstrap.py"
        original = bootstrap.read_bytes()
        original_sha = hashlib.sha256(original).hexdigest()
        mutant = original.replace(b'emit = hook.install(config["log"])', b'emit = lambda *_: None', 1)
        assert mutant != original
        try:
            bootstrap.write_bytes(mutant)
            lost = audit("observer-sole-removal")
            assert lost["exit"] == 0 and lost["unverified"], lost
            try:
                assert_hole(lost)
            except AssertionError:
                print("CONTROL sole observer removal bites: underlying read succeeds but required observed HOLE assertion refuses")
            else:
                raise AssertionError("sole observer removal escaped the control")
        finally:
            bootstrap.write_bytes(original)
        assert hashlib.sha256(bootstrap.read_bytes()).hexdigest() == original_sha
        # Restoration is byte-identical to the green baseline; do not rerun.
        print("CONTROL observer restored SHA256 " + original_sha + "; no identical restored rerun")


def descendant_observation_controls() -> None:
    """Actual sanitized/isolated child reads, identity, receipts and biting loss controls."""
    import hashlib
    import json
    import shutil

    def record(name, result):
        print("CONTROL " + json.dumps({"name": name, "gate_exit": result["exit"],
              "coverage": result["coverage_status"], "holes": result["undeclared"],
              "processes": len(result["python_processes"]),
              "launches": len(result["explicit_launches"]),
              "unverified": result["unverified"]}, sort_keys=True))

    with tempfile.TemporaryDirectory(prefix="gate-read-descendants-") as directory:
        root = Path(directory).resolve()
        (root / "hidden.txt").write_text("real undeclared input\n", encoding="utf-8")
        module = load_audit()
        module.ROOT, module.OUT_DIR, module.gc.ROOT = root, root / "audit", root
        source = Path(__file__).resolve().parent
        copied = root / "observer/scripts/read-audit"
        shutil.copytree(HOOK, copied, ignore=shutil.ignore_patterns("__pycache__"))
        module.HOOK_DIR = copied

        def wrapped(command, *, scripts=copied.parent):
            text = 'SCRIPT_DIR="$1"; . "$SCRIPT_DIR/read-audit/launch.sh"; shift; gate_audit_python "$@"'
            return ["bash", "-c", text, "read-audit-control", str(scripts), *command]

        def audit(name, command, files=()):
            result = module.audit_gate({"id": name, "command": command,
                                       "inputs": {"files": list(files)}}, [root], set())
            record(name, result)
            return result

        def assert_hole(result):
            assert result["exit"] == 0, result
            assert result["coverage_status"] == "observed-python-path" and not result["unverified"], result
            assert "hidden.txt" in result["undeclared"], result

        clean = ["/usr/bin/env", "-i", "PATH=/usr/bin:/bin"]
        payload = "assert open('hidden.txt').read() == 'real undeclared input\\n'"
        for flags in (("-B", "-s"), ("-I", "-s")):
            command = [*clean, sys.executable, *flags, "-c", payload]
            assert_hole(audit("env-i-" + flags[0][1:], wrapped(command)))
        poison = root / "exact-eels-src"
        poison.mkdir()
        (poison / "unused_poison.py").write_text("raise AssertionError('ambient hook path leaked')\n")
        # The explicit adapter accepts the original inherited exact PYTHONPATH;
        # /usr/bin/env without -i is handled by the surrounding shell, not guessed.
        env_text = 'SCRIPT_DIR="$1"; . "$SCRIPT_DIR/read-audit/launch.sh"; PYTHONPATH="$2" gate_audit_python "$3" -B -s -c "$4"'
        clobber_command = ["bash", "-c", env_text, "clobber", str(copied.parent), str(poison), sys.executable, payload]
        assert_hole(audit("exact-pythonpath", clobber_command))

        # Compare the actual target-visible identity against unmodified Python.
        identity = (
            "import json,os,sys; print(json.dumps(dict(environment=dict(os.environ), "
            "path=sys.path, flags=repr(sys.flags), argv=sys.argv, orig=sys.orig_argv, "
            "executable=sys.executable, prefix=sys.prefix, base_prefix=sys.base_prefix, "
            "name=__name__, package=__package__, spec=repr(__spec__), "
            "file=globals().get('__file__'), cached=globals().get('__cached__'), "
            "loader_type=type(__loader__).__name__, loader_name=getattr(__loader__,'name',None), "
            "loader_path=getattr(__loader__,'path',None), code=sys._getframe().f_code.co_filename), sort_keys=True))"
        )
        subject = root / "identity.py"
        subject.write_text(identity + "\n", encoding="utf-8")
        (root / "real").mkdir()
        (root / "real/identity.py").write_text(identity + "\n", encoding="utf-8")
        (root / "identity-link.py").symlink_to(root / "real/identity.py")
        identities = ((("-B", "-s"), [str(subject), "argument"]),
                      (("-I", "-s"), [str(subject), "argument"]),
                      (("-I", "-s"), ["-c", identity, "argument"]),
                      (("-B", "-s"), ["identity.py", "argument"]),
                      (("-B", "-s"), ["./identity-link.py", "argument"]),
                      (("-I", "-s"), ["./identity-link.py", "argument"]))
        for index, (flags, target) in enumerate(identities):
            command = [*clean, sys.executable, *flags, *target]
            baseline = subprocess.run(command, cwd=root, capture_output=True, text=True, check=True)
            result = audit("identity-" + str(index), wrapped(command), ["identity.py", "identity-link.py", "real/identity.py"])
            assert result["exit"] == 0 and not result["unverified"], result
            observed = (module.OUT_DIR / (result["id"] + ".stdout.log")).read_text()
            assert json.loads(baseline.stdout) == json.loads(observed), (baseline.stdout, observed)
        print("CONTROL target-visible environment/path/flags/argv/main identity equals native clean baseline")

        # Exercise the production shared helper's callback, with a real -I -c
        # child and a real Python-shebang executable. No EELS import/transition.
        fake_t8n = root / "synthetic-t8n"
        fake_t8n.write_text("#!" + sys.executable + "\n" + payload + "\n", encoding="utf-8")
        fake_t8n.chmod(0o755)
        (root / "real/hidden.txt").write_text("real undeclared input\n", encoding="utf-8")
        parent = root / "current-parent.py"
        parent.write_text(
            "import importlib.util,sys\nfrom pathlib import Path\n"
            f"spec=importlib.util.spec_from_file_location('current_mainnet', {str(source / 'current_mainnet.py')!r})\n"
            "lane=importlib.util.module_from_spec(spec);sys.modules[spec.name]=lane;spec.loader.exec_module(lane)\n"
            f"commands=[[sys.executable,'-I','-s','-c',{payload!r}],[{str(fake_t8n)!r}]]\n"
            "for command in commands:\n"
            " result=lane._run(command,cwd=Path.cwd(),env={'PATH':'/usr/bin:/bin'})\n"
            " assert result.returncode==0,result.stderr\n"
            "result=lane._run(['../synthetic-t8n'],cwd=Path('real'),env={'PATH':'/usr/bin:/bin'})\n"
            "assert result.returncode==0,result.stderr\n", encoding="utf-8")
        result = audit("current-recursive", wrapped([*clean, sys.executable, "-I", "-s", str(parent)]), ["current-parent.py", "synthetic-t8n"])
        assert_hole(result)
        assert len(result["explicit_launches"]) == 4, result

        # An observed declared read cannot hide an uninstrumented grandchild.
        parent.write_text("import subprocess,sys\nopen('current-parent.py').read()\n"
                          f"subprocess.run(['/usr/bin/env','-i','PATH=/usr/bin:/bin',sys.executable,'-I','-c',{payload!r}],check=True)\n")
        lost = audit("observed-parent-lost-grandchild", wrapped([*clean, sys.executable, "-I", str(parent)]), ["current-parent.py"])
        assert lost["exit"] == 0 and lost["reads_observed"] > 0 and lost["unverified"], lost
        assert any("descendant has no matching" in text for text in lost["unverified"]), lost

        # A marker-looking target argument is never a transport receipt.
        parent.write_text("import subprocess,sys\n" +
                          f"subprocess.run(['/usr/bin/env','-i','PATH=/usr/bin:/bin',sys.executable,'-I','-c',{payload!r},'--read-audit','untrusted-marker'],check=True)\n")
        marker = audit("fake-transport-marker", wrapped([*clean, sys.executable, "-I", str(parent)]), ["current-parent.py"])
        assert marker["exit"] == 0 and marker["unverified"], marker

        # Malformed and truncated log records, and a short write, fail closed.
        for name, damage in (
            ("malformed-log", "open(os.environ['GATE_READ_AUDIT'],'a').write('Z\\tbad\\n')"),
            ("malformed-receipt", 'open(os.environ[\'GATE_READ_AUDIT\'],\'a\').write(\'N\\t{"nonce": "bad"}\\n\')'),
            ("truncated-log", "open(os.environ['GATE_READ_AUDIT'],'a').write('R\\ttruncated');os._exit(0)"),
            ("short-write", "real=os.write;os.write=lambda fd,data:real(fd,data[:1]);\\ntry:open('hidden.txt').read()\\nexcept RuntimeError:pass".replace("\\n", "\n")),
        ):
            damaged = audit(name, [sys.executable, "-B", "-c", "import os\n" + damage])
            assert damaged["unverified"], damaged
        # A single caught failure followed by recovered writes remains sticky.
        transient = ("import os\nreal=os.write\nfailed=[False]\n"
                     "def once(fd,data):\n"
                     " if not failed[0]:\n  failed[0]=True;raise OSError('one transient write failure')\n"
                     " return real(fd,data)\n"
                     "os.write=once\ntry:open('hidden.txt').read()\nexcept RuntimeError:pass\nos.write=real\n")
        sticky = audit("caught-transient-write", [sys.executable, "-B", "-c", transient])
        assert sticky["exit"] == 0 and any("log failed earlier" in text for text in sticky["unverified"]), sticky
        # Remove only the latch in a disposable hook; the refusal assertion must
        # fail although startup/completion and recovered writes look ordinary.
        hook = copied / "sitecustomize.py"
        original_hook = hook.read_bytes()
        without_latch = original_hook.replace(b'log_state["failed"] = True', b'log_state["failed"] = False')
        assert without_latch != original_hook
        hook.write_bytes(without_latch)
        # These child launches use the copied hook through PYTHONPATH directly.
        previous_hook = module.HOOK_DIR
        try:
            missing_latch = audit("missing-log-failure-latch", [sys.executable, "-B", "-c", transient])
            assert not missing_latch["unverified"], missing_latch
            assert not any("log failed earlier" in text for text in missing_latch["unverified"])
        finally:
            hook.write_bytes(original_hook)
            module.HOOK_DIR = previous_hook
        assert hook.read_bytes() == original_hook
        print("CONTROL caught transient log failure refuses; sole sticky-latch removal bites and original bytes restored")
        # Missing log/open failure is not a silent hook installation success.
        failure = subprocess.run([sys.executable, "-I", "-B", "-c",
                                  "import importlib.util; s=importlib.util.spec_from_file_location('h', " + repr(str(copied / 'sitecustomize.py')) + ");m=importlib.util.module_from_spec(s);s.loader.exec_module(m);m.install(" + repr(str(root)) + ")"], capture_output=True, text=True)
        assert failure.returncode != 0 and "IsADirectoryError" in failure.stderr, failure
        print("CONTROL hook log-open failure raises; malformed/truncated/short writes refuse")

        # A new file beside the observer is not silently granted authority.
        unlisted = copied / "unlisted.py"
        unlisted.write_text("new observer-neighbour input\n", encoding="utf-8")
        result = audit("unlisted-observer-neighbour", [sys.executable, "-B", "-c", f"open({str(unlisted)!r}).read()"])
        assert any(path.endswith("read-audit/unlisted.py") for path in result["undeclared"]), result
        assert str(source / "gate-read-audit.py") in result["observer_source_sha256"], result
        assert str(unlisted) not in result["observer_source_sha256"], result
        print("CONTROL fixed observer closure binds dirty parser; new neighbouring source read remains HOLE")

        # Required target/native roots are admitted precisely, never all HOME.
        for label in ("t8n_target", "t8n_python_base"):
            (root / label).mkdir()
            (root / label / "hidden.txt").write_text("native-root input")
        original_resolve = module.gc.resolve_path
        module.gc.resolve_path = lambda base, value: root / value[1:] if value.startswith("@t8n_") else original_resolve(base, value)
        root_payload = ";".join(f"open({str(root / label / 'hidden.txt')!r}).read()" for label in ("t8n_target", "t8n_python_base"))
        result = module.audit_gate({"id": "native-roots", "command": [sys.executable, "-B", "-c", root_payload],
                                   "inputs": {"files": ["@t8n_target/declared.txt", "@t8n_python_base/declared.txt"]}}, [root / "unrelated"], set())
        record("native-roots", result)
        assert len(result["undeclared"]) == 2 and not result["unverified"], result
        module.gc.resolve_path = lambda base, value: (_ for _ in ()).throw(ValueError("synthetic missing native root")) if value.startswith("@t8n_") else original_resolve(base, value)
        result = module.audit_gate({"id": "missing-native-roots", "command": [sys.executable, "-B", "-c", "pass"],
                                   "inputs": {"files": ["@t8n_python_base/declared.txt"]}}, [root], set())
        assert any("required @t8n_" in text for text in result["unverified"]), result
        print("CONTROL undeclared target/base reads classified; unresolved required roots refuse")


def legacy_descendant_controls() -> None:
    with tempfile.TemporaryDirectory(prefix='gate-read-legacy-') as directory:
        import ast, contextlib, hashlib, importlib.util, io, json, os, shlex, subprocess, sys
        from pathlib import Path
        SOURCE = Path(__file__).resolve().parents[1]
        WORK = Path(directory)
        WORK.mkdir(exist_ok=True)
        HOOK = SOURCE / 'scripts/read-audit'
        PYTHON = sys.executable

        def write(path, text):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            return path

        def load_audit():
            spec = importlib.util.spec_from_file_location('legacy_actual_audit', SOURCE / 'scripts/gate-read-audit.py')
            m = importlib.util.module_from_spec(spec)
            sys.modules[spec.name] = m
            spec.loader.exec_module(m)
            return m
        PROBE = 'import json,os,sys\nfrom pathlib import Path\nprobe={"environment":dict(os.environ),"path":sys.path,"argv":sys.argv,"orig_argv":sys.orig_argv,"executable":sys.executable,"prefix":sys.prefix,"base_prefix":sys.base_prefix,"flags":repr(sys.flags),"file":globals().get("__file__"),"package":globals().get("__package__"),"spec":({k:getattr(__spec__,k) for k in ["name","origin","parent","has_location","cached"]} if globals().get("__spec__") is not None else None),"loader":repr(type(globals().get("__loader__"))),"dont_write_bytecode":sys.dont_write_bytecode}\nassert Path(os.environ["HOLE"]).read_text()=="undeclared payload\\n"\n'
        PARENT = 'import ast,importlib.util,json,os,sys,subprocess\nfrom pathlib import Path\nfrom typing import Mapping\nsource=Path(os.environ["SOURCE"])\nPath(os.environ["DECLARED"]).read_text()\nspec=importlib.util.spec_from_file_location("prague_actual", source/"scripts/prague_fixture.py")\np=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)\npost,result,body=p.run_t8n({}, {}, [], eels_root=Path(os.environ["EELS_ROOT"]))\nassert (post,result,body)==({}, {}, [])\ns=source.joinpath("scripts/gen-lido-twg-differential.py").read_text()\ntree=ast.parse(s)\nnode=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=="compatibility_contract")\ntemplates=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=="PLACEHOLDER_TEMPLATE_DIGESTS" for t in n.targets))\nPLACEHOLDER_TEMPLATE_DIGESTS=ast.literal_eval(templates.value)\nCOMPATIBILITY_TOOL=Path(os.environ["SCHEMA_TOOL"])\nREPO=Path(os.environ["SYNTHETIC_ROOT"])\ndef expect(condition,message):\n    assert condition,message\nexec(compile(ast.Module(body=[node],type_ignores=[]),str(source/"scripts/gen-lido-twg-differential.py"),"exec"))\ntry:\n    contract=compatibility_contract()\n    assert contract=={"templates":PLACEHOLDER_TEMPLATE_DIGESTS}\n    print("legacy descendant success")\nexcept subprocess.CalledProcessError as e:\n    print(json.dumps({"type":type(e).__name__,"returncode":e.returncode,"cmd":e.cmd,"output":e.output.hex(),"stderr":e.stderr}))\n    raise SystemExit(23)\n'

        def setup(name, failure=False):
            root = WORK / name
            root.mkdir(exist_ok=True)
            eels = root / 'eels'
            src = eels / 'src'
            package = src / 'ethereum_spec_tools/evm_tools'
            write(src / 'ethereum_spec_tools/__init__.py', '')
            write(package / '__init__.py', '')
            write(root / 'declared.txt', 'declared parent input\n')
            write(root / 'undeclared.txt', 'undeclared payload\n')
            write(package / '__main__.py', PROBE + 'Path(os.environ["T8N_PROBE"]).write_text(json.dumps(probe,sort_keys=True))\na=sys.argv[1:];out=Path(a[a.index("--output.basedir")+1])\nfor n,v in [("out-alloc.json",{}),("out-result.json",{}),("out-body.txt",[])]:\n    (out/n).write_text(json.dumps(v))\n')
            tree = ast.parse((SOURCE / 'scripts/gen-lido-twg-differential.py').read_text())
            n = next((n for n in tree.body if isinstance(n, ast.Assign) and any((isinstance(t, ast.Name) and t.id == 'PLACEHOLDER_TEMPLATE_DIGESTS' for t in n.targets))))
            templates = ast.literal_eval(n.value)
            schema = write(root / 'schema.py', PROBE + 'Path(os.environ["SCHEMA_PROBE"]).write_text(json.dumps(probe,sort_keys=True))\n' + ('print("failure stdout");print("failure stderr",file=sys.stderr);raise SystemExit(7)\n' if failure else 'print(' + repr(json.dumps({'documentFill': {'templates': templates}})) + ')\n'))
            parent = write(root / 'parent.py', PARENT)
            wrapper = write(root / 'wrapper.sh', '#!/usr/bin/env bash\nset -eu\nSCRIPT_DIR=' + shlex.quote(str(SOURCE / 'scripts')) + '\n. "$SCRIPT_DIR/read-audit/launch.sh"\nPYTHONPATH="$EELS_ROOT/src" gate_audit_python ' + shlex.quote(PYTHON) + ' ' + shlex.quote(str(parent)) + '\n')
            env = dict(os.environ, SOURCE=str(SOURCE), SYNTHETIC_ROOT=str(root), DECLARED=str(root / 'declared.txt'), EELS_ROOT=str(eels), HOLE=str(root / 'undeclared.txt'), SCHEMA_TOOL=str(schema), T8N_PROBE=str(root / 't8n-probe.json'), SCHEMA_PROBE=str(root / 'schema-probe.json'), PYTHONDONTWRITEBYTECODE='1')
            return (root, parent, wrapper, env)
        summaries = []

        def audit_case(name, failure=False, disable_callback=False):
            root, parent, wrapper, env = setup(name, failure)
            m = load_audit()
            m.ROOT = root
            m.HOOK_DIR = HOOK
            m.OUT_DIR = root / 'observation'
            m.OUT_DIR.mkdir(exist_ok=True)
            log = m.OUT_DIR / (name + '.log')
            baseline_env = dict(env, PYTHONPATH=env['EELS_ROOT'] + '/src', GATE_READ_AUDIT=str(log))
            ordinary = write(root / 'ordinary-wrapper.sh', wrapper.read_text().replace('gate_audit_python ', ''))
            plain = subprocess.run(['bash', str(ordinary)], cwd=root, env=baseline_env, capture_output=True, text=True)
            assert plain.returncode == (23 if failure else 0), (plain.stdout, plain.stderr)
            probes = {n: json.loads((root / (n + '-probe.json')).read_text()) for n in ['t8n', 'schema']}
            if disable_callback:
                parent.write_text('import sys\nif hasattr(sys,"_blanc_gate_read_audit_run"): del sys._blanc_gate_read_audit_run\n' + parent.read_text())
            files = [p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p.name not in ['undeclared.txt', 't8n-probe.json', 'schema-probe.json'] and ('observation' not in p.parts)]
            gate = {'id': name, 'kind': 'cacheable', 'command': ['bash', str(wrapper)], 'inputs': {'files': files}}
            m.gc.load_registry = lambda _: {'gates': [gate]}
            m.interesting_roots = lambda: [root]
            old = dict(os.environ)
            os.environ.update(env)
            try:
                out, err = (io.StringIO(), io.StringIO())
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    code = m.main([])
            finally:
                os.environ.clear()
                os.environ.update(old)
            (root / 'cli.stdout').write_text(out.getvalue())
            (root / 'cli.stderr').write_text(err.getvalue())
            actual = json.loads((m.OUT_DIR / 'audit.json').read_text())['gates'][0]
            if disable_callback:
                assert code == 2 and actual['unverified'], (code, actual)
                assert actual['covered'] > 0, actual
            else:
                assert code == 1 and 'HOLE' in out.getvalue(), (code, out.getvalue(), err.getvalue())
                assert actual['coverage_status'] == 'observed-python-path' and (not actual['unverified']), actual
                assert 'undeclared.txt' in actual['undeclared'], actual
                assert len(actual['explicit_launches']) == 3, actual
                assert len(actual['bootstrap_receipts']) == 3, actual
                for n, expected in probes.items():
                    got = json.loads((root / (n + '-probe.json')).read_text())
                    for k in ['argv', 'orig_argv']:
                        if n == 't8n':

                            def norm(v):
                                return [x if not x.startswith('/tmp/tmp') else '<actual-temporary-path>/' + Path(x).name if x.endswith('.json') else '<actual-temporary-path>' for x in v]
                            expected[k] = norm(expected[k])
                            got[k] = norm(got[k])
                    assert got == expected, (n, {k: (expected[k], got[k]) for k in got if got[k] != expected[k]})
                if failure:
                    audited = (m.OUT_DIR / (name + '.stdout.log')).read_text()
                    assert audited == plain.stdout, (audited, plain.stdout)
                    assert (m.OUT_DIR / (name + '.stderr.log')).read_text() == plain.stderr
            restoration = None
            if disable_callback:
                mutated = hashlib.sha256(parent.read_bytes()).hexdigest()
                parent.write_text(PARENT)
                restored = hashlib.sha256(parent.read_bytes()).hexdigest()
                green = hashlib.sha256((WORK / 'legacy-grandchildren/parent.py').read_bytes()).hexdigest()
                assert restored == green
                restoration = {'mutated_parent_sha256': mutated, 'restored_parent_sha256': restored, 'byte_identical_positive_parent_sha256': green, 'rerun_after_restore': False}
            summaries.append({'restoration': restoration, 'name': name, 'cli_exit': code, 'command': gate['command'], 'gate_exit': actual['exit'], 'coverage': actual['coverage_status'], 'explicit_launches': len(actual['explicit_launches']), 'hole': 'undeclared.txt' in actual['undeclared'], 'unverified': actual['unverified'], 'stdout': str(root / 'cli.stdout'), 'stderr': str(root / 'cli.stderr'), 'audit': str(m.OUT_DIR / 'audit.json')})
            print(name, code, actual['exit'], actual['coverage_status'], actual['unverified'])

        def timeout_case():
            root, parent, wrapper, env = setup('legacy-check-output-timeout')
            child = Path(env['SCHEMA_TOOL'])
            child.write_text(PROBE + 'import time\nprint("timeout stdout",flush=True)\nprint("timeout stderr",file=sys.stderr,flush=True)\ntime.sleep(3)\n')
            source = PARENT.replace('try:\n    contract=compatibility_contract()', 'original_run=subprocess.run\ncallback=getattr(sys,"_blanc_gate_read_audit_run",None)\nif callback is None:\n    def limited_run(*args,**kwargs):\n        kwargs["timeout"]=0.4\n        return original_run(*args,**kwargs)\n    subprocess.run=limited_run\nelse:\n    def limited_callback(*args,**kwargs):\n        kwargs["timeout"]=0.4\n        return callback(*args,**kwargs)\n    sys._blanc_gate_read_audit_run=limited_callback\ntry:\n    contract=compatibility_contract()')
            source = source.replace('except subprocess.CalledProcessError as e:', 'except subprocess.TimeoutExpired as e:').replace('"returncode":e.returncode', '"timeout":e.timeout')
            parent.write_text(source)
            log = root / 'timeout.log'
            same_env = dict(env, PYTHONPATH=env['EELS_ROOT'] + '/src', GATE_READ_AUDIT=str(log))
            ordinary = write(root / 'ordinary-wrapper.sh', wrapper.read_text().replace('gate_audit_python ', ''))
            plain = subprocess.run(['bash', str(ordinary)], cwd=root, env=same_env, capture_output=True, text=True)
            actual = subprocess.run(['bash', str(wrapper)], cwd=root, env=same_env, capture_output=True, text=True)
            assert plain.returncode == actual.returncode == 23, (plain.returncode, actual.returncode, actual.stderr)
            assert plain.stdout == actual.stdout and plain.stderr == actual.stderr, (plain.stdout, actual.stdout, plain.stderr, actual.stderr)
            value = json.loads(actual.stdout)
            assert value['cmd'] == [PYTHON, env['SCHEMA_TOOL'], 'schema'] and value['output'] == b'timeout stdout\n'.hex(), value
            assert value['type'] == 'TimeoutExpired' and value['timeout'] == 0.4, value
            result = {'name': 'legacy-check-output-timeout', 'ordinary_exit': plain.returncode, 'audited_exit': actual.returncode, 'cmd': value['cmd'], 'bytes_output': True, 'stderr_equal': True, 'receipt_limit': 'Interrupted timeout receipt is not certified child completion; parser must refuse.'}
            summaries.append(result)
            print(result['name'], 'OK exact TimeoutExpired cmd/timeout/bytes/stderr parity')
        audit_case('legacy-grandchildren')
        audit_case('legacy-check-output-error', failure=True)
        audit_case('legacy-missing-callback', disable_callback=True)
        timeout_case()
        print('OK focused actual-core legacy controls')


def launch_event_regression_controls() -> None:
    """Real launch/receipt controls; only unavailable native mechanics may skip."""
    import ast
    import hashlib
    import json
    import shutil

    with tempfile.TemporaryDirectory(prefix="gate-read-launch-events-") as directory:
        root = Path(directory).resolve()
        copied = root / "observer/scripts/read-audit"
        shutil.copytree(HOOK, copied, ignore=shutil.ignore_patterns("__pycache__"))
        module = load_audit()
        module.ROOT, module.gc.ROOT = root, root
        module.OUT_DIR, module.HOOK_DIR = root / "audit", copied
        (root / "hidden.txt").write_text("undeclared input\n")
        # Capability probes must not inherit an outer read observer or ambient
        # import overrides. This is a declared probe environment, not a claim
        # that the inherited-hook path preserves native sys.path/sys.modules.
        native_env = {key: value for key, value in os.environ.items()
                      if key not in {"GATE_READ_AUDIT", "PYTHONPATH", "PYTHONHOME"}}
        native_env["PYTHONDONTWRITEBYTECODE"] = "1"
        clean_expression = ("{key:value for key,value in os.environ.items() "
                            "if key not in {'GATE_READ_AUDIT','PYTHONPATH','PYTHONHOME'}}")

        def native(code):
            result = subprocess.run([sys.executable, "-B", "-c", code], cwd=root,
                                    env=native_env, capture_output=True, text=True, check=True)
            return json.loads(result.stdout)

        def audit(name, command, files=()):
            result = module.audit_gate({"id": name, "command": command,
                                       "inputs": {"files": list(files)}}, [root], set())
            print("CONTROL " + json.dumps({"name": name, "gate_exit": result["exit"],
                  "coverage": result["coverage_status"], "holes": result["undeclared"],
                  "unverified": result["unverified"]}, sort_keys=True))
            return result

        def python(name, code, files=()):
            return audit(name, [sys.executable, "-B", "-c", code], files)

        def hole(result):
            assert result["exit"] == 0 and not result["unverified"], result
            assert result["coverage_status"] == "observed-python-path", result
            assert "hidden.txt" in result["undeclared"], result

        def raw(name, kind):
            return [json.loads(line.partition("\t")[2])
                    for line in (module.OUT_DIR / (name + ".log")).read_text().splitlines()
                    if line.startswith(kind + "\t")]

        def sole_mutation(path, before, after, failure):
            original = path.read_bytes()
            assert original.count(before) == 1
            try:
                path.write_bytes(original.replace(before, after, 1))
                result = failure()
                assert result["exit"] == 0 and result["unverified"], result
            finally:
                path.write_bytes(original)
            assert path.read_bytes() == original
            print("CONTROL restored exact green bytes SHA256 " + hashlib.sha256(original).hexdigest()
                  + "; no identical restored rerun")

        payload = "assert open('hidden.txt').read()=='undeclared input\\n'"
        child = [sys.executable, "-B", "-c", payload]
        prefix = ("import subprocess,sys,os,json\nevents=[]\n"
                  "sys.addaudithook(lambda event,args:events.append(event) "
                  "if event in ('subprocess.Popen','os.posix_spawn') else None)\n")
        one = prefix + f"subprocess.run({child!r},check=True,close_fds=False)\nprint(json.dumps(events))"
        events = native(one)
        print("CAPABILITY " + json.dumps({"python": sys.executable, "popen_events": events}, sort_keys=True))
        # A valid older/platform-specific Popen backend can emit only Popen.
        # Unknown traces and execution failures are failures, never skips.
        assert events in (["subprocess.Popen"], ["subprocess.Popen", "os.posix_spawn"]), events
        hole(python("popen-one", one))
        assert json.loads((module.OUT_DIR / "popen-one.stdout.log").read_text()) == events
        assert len(raw("popen-one", "P")) == 1 and len(raw("popen-one", "S")) == 2
        two = prefix + (f"subprocess.run({child!r},check=True,close_fds=False)\n" * 2) + "print(json.dumps(events))"
        hole(python("popen-identical-two", two))
        assert json.loads((module.OUT_DIR / "popen-identical-two.stdout.log").read_text()) == events * 2
        assert len(raw("popen-identical-two", "P")) == 2 and len(raw("popen-identical-two", "S")) == 3
        if events == ["subprocess.Popen", "os.posix_spawn"]:
            sole_mutation(copied / "sitecustomize.py",
                          b'if frame is not None and getattr(_LOCAL, "popen_event", None) == (frame, tuple(command)):',
                          b'if False and frame is not None and getattr(_LOCAL, "popen_event", None) == (frame, tuple(command)):',
                          lambda: python("nested-sole-correlation-removal", one))
        else:
            print("SKIP nested-correlation mutation only: native selected Popen backend emitted no nested os.posix_spawn; trace=" + repr(events))

        # Detect actual syscall availability. Only absent API, NotImplemented,
        # ENOSYS or ENOTSUP are unavailable mechanics; other failures propagate.
        spawn_probe = (prefix + "import errno\n"
                       "if not hasattr(os,'posix_spawn'):\n"
                       " print(json.dumps({'available':False,'reason':'os.posix_spawn absent'}))\n"
                       "else:\n"
                       " try:\n"
                       + f"  pid=os.posix_spawn({sys.executable!r},{child!r},dict(os.environ))\n"
                       " except NotImplementedError:\n"
                       "  print(json.dumps({'available':False,'reason':'posix_spawn NotImplementedError'}))\n"
                       " except OSError as error:\n"
                       "  if error.errno not in {errno.ENOSYS,getattr(errno,'ENOTSUP',errno.ENOSYS)}: raise\n"
                       "  print(json.dumps({'available':False,'reason':'posix_spawn errno '+str(error.errno)}))\n"
                       " else:\n"
                       "  assert os.waitpid(pid,0)[1]==0\n"
                       "  print(json.dumps({'available':True,'events':events}))\n")
        spawn = native(spawn_probe)
        print("CAPABILITY " + json.dumps({"direct_posix_spawn": spawn}, sort_keys=True))
        if spawn["available"]:
            assert spawn["events"] == ["os.posix_spawn"], spawn
            direct = prefix + f"pid=os.posix_spawn({sys.executable!r},{child!r},dict(os.environ));assert os.waitpid(pid,0)[1]==0\n"
            hole(python("direct-posix", direct))
            assert len(raw("direct-posix", "P")) == 1
            assert raw("direct-posix", "P")[0]["event"] == "os.posix_spawn"
            missing = (prefix + f"subprocess.run({child!r},check=True,close_fds=False)\n"
                       + f"pid=os.posix_spawn({sys.executable!r},{child!r},{clean_expression});assert os.waitpid(pid,0)[1]==0\n")
            result = python("direct-identical-missing-receipt", missing)
            assert result["exit"] == 0 and result["unverified"] and result["reads_observed"] > 0, result
            assert len(raw("direct-identical-missing-receipt", "P")) == 2
        else:
            print("SKIP direct-posix controls only: " + spawn["reason"])

        # The fixed shebang is the supported subject. Choose this interpreter,
        # never a host's possibly different /usr/bin/python3. Disposable aliases
        # also make the unsupported env-python spelling independently runnable.
        if os.name != "posix" or not os.access("/usr/bin/env", os.X_OK):
            print("SKIP env-python shebang controls only: POSIX /usr/bin/env execution unavailable")
        else:
            binary = root / "selected-native-bin"
            binary.mkdir()
            for name in ("python3", "python"):
                (binary / name).symlink_to(sys.executable)
            target_path = str(binary) + os.pathsep + os.defpath
            subject = root / "env-python.py"
            subject.write_text("#!/usr/bin/env python3\nimport sys,json,os\n" + payload + "\n"
                               "print(json.dumps({'argv':sys.argv,'orig':sys.orig_argv,'executable':sys.executable,'file':__file__,'cwd':os.getcwd()},sort_keys=True))\n")
            subject.chmod(0o755)
            arguments = [str(subject), "unchanged argument"]
            environment_setup = f"env=dict(os.environ);env['PATH']={target_path!r}"
            parent = ("import subprocess,os\n" + environment_setup + "\n"
                      + f"r=subprocess.run({arguments!r},cwd={str(root)!r},env=env,capture_output=True,text=True,check=True);print(r.stdout,end='')")
            baseline = subprocess.run(arguments, cwd=root, env=dict(native_env, PATH=target_path),
                                      capture_output=True, text=True, check=True)
            probe = json.loads(baseline.stdout)
            assert Path(probe["executable"]).resolve() == Path(sys.executable).resolve(), probe
            assert probe["orig"] == ["python3", *arguments], probe
            hole(python("env-python-recognized", parent, [subject.name]))
            # Inherited hook PYTHONPATH is deliberately an observer intervention;
            # compare command identity only, not native full env/sys.path parity.
            assert (module.OUT_DIR / "env-python-recognized.stdout.log").read_text() == baseline.stdout
            result = python("env-python-missing-receipt", parent.replace(environment_setup, f"env={clean_expression};env['PATH']={target_path!r}"), [subject.name])
            assert result["exit"] == 0 and result["unverified"], result
            unsupported = root / "env-python-unsupported.py"
            unsupported.write_text(subject.read_text().replace("#!/usr/bin/env python3", "#!/usr/bin/env python"))
            unsupported.chmod(0o755)
            result = python("env-python-unsupported", parent.replace(str(subject), str(unsupported)), [unsupported.name])
            assert result["exit"] == 0 and any("unsupported Python shebang" in message for message in result["unverified"]), result
            sole_mutation(copied / "sitecustomize.py", b'elif first == "#!/usr/bin/env python3":',
                          b'elif False and first == "#!/usr/bin/env python3":',
                          lambda: python("env-python-sole-recognition-removal", parent, [subject.name]))

        # Extract the actual helper with a synthetic generator. Its clean child
        # env strips PYTHONPATH, so full target probe parity is meaningful here.
        source = Path(__file__).with_name("test-lido-ossifiable-proxy-artifact-falsifiers.py")
        node = next(node for node in ast.parse(source.read_text()).body
                    if isinstance(node, ast.FunctionDef) and node.name == "generator_process")
        generator = root / "generator.py"
        generator.write_text("import os,sys,json\n" + payload + "\n"
                             "print(json.dumps({'environment':dict(os.environ),'argv':sys.argv,'orig':sys.orig_argv,'path':sys.path,'flags':repr(sys.flags),'cwd':os.getcwd()},sort_keys=True))\n")
        parent_file = root / "artifact-parent.py"
        parent_file.write_text("import os,subprocess,sys\nfrom pathlib import Path\nGENERATOR=Path('generator.py')\n"
                               + ast.unparse(node) + f"\nr=generator_process(Path({str(root)!r}),'unchanged');assert r.returncode==0,r.stderr;print(r.stdout,end='')\n")
        shell = 'SCRIPT_DIR="$1"; . "$SCRIPT_DIR/read-audit/launch.sh"; shift; gate_audit_python "$@"'
        command = ["bash", "-c", shell, "artifact-control", str(copied.parent), sys.executable, str(parent_file)]
        baseline = subprocess.run([sys.executable, str(parent_file)], cwd=root,
                                  env=native_env, capture_output=True, text=True, check=True)
        result = audit("artifact-sanitized-observed", command, [parent_file.name, generator.name])
        hole(result)
        output = (module.OUT_DIR / "artifact-sanitized-observed.stdout.log").read_text()
        assert output == baseline.stdout
        assert set(json.loads(output)["environment"]) == {"LANG", "LC_ALL", "PATH", "PYTHONDONTWRITEBYTECODE"}
        assert len(result["explicit_launches"]) == 2
        sole_mutation(parent_file, b"run = getattr(sys, '_blanc_gate_read_audit_run', subprocess.run)",
                      b"run = subprocess.run",
                      lambda: audit("artifact-sole-callback-removal", command, [parent_file.name, generator.name]))


def material_authority_coverage_controls() -> None:
    """Hashed producer authority is covered; adjacent unregistered reads are not."""
    import ast
    import hashlib

    module = load_audit()
    source = SCRIPT.read_bytes()
    addition = b'''    # Material-output producer sources are independently content-hashed by
    # component_material_output, even when their emitted bytes stay unchanged.
    for spec in inputs.get("material_output", []):
        for given in spec["authority"]:
            exact.add(gc.resolve_path(ROOT, given).resolve())

'''
    assert source.count(addition) == 1, "Install exact reviewed material-authority classifier correction first"
    with tempfile.TemporaryDirectory(prefix="gate-read-material-authority-") as directory:
        root = Path(directory).resolve()
        authority = root / "authority.py"
        original = b"print('constant')\n"
        authority.write_bytes(original)
        (root / "neighbor.txt").write_text("independent undeclared input\n")
        module.ROOT, module.gc.ROOT, module.OUT_DIR = root, root, root / "audit"
        producer = {"id": "constant-output", "authority": ["authority.py"],
                    "command": [sys.executable, "authority.py"]}
        gate = {"id": "material-authority", "command": [sys.executable, "-B", "-c",
                "open('authority.py').read();open('neighbor.txt').read()"],
                "inputs": {"material_output": [producer]}}

        def observed(name, selected=gate):
            result = module.audit_gate(dict(selected, id=name), [root], set())
            assert result["exit"] == 0 and not result["unverified"], result
            return result

        def correct(result):
            assert result["undeclared"] == ["neighbor.txt"] and result["covered"] == 1, result

        correct(observed("authority-green"))
        baseline, detail = module.gc.component_material_output(root, [producer])
        try:
            authority.write_bytes(original + b"# changed authority, identical output\n")
            changed, changed_detail = module.gc.component_material_output(root, [producer])
            assert changed != baseline
            assert changed_detail["constant-output::output"] == detail["constant-output::output"]
            assert changed_detail["constant-output::authority"] != detail["constant-output::authority"]
        finally:
            authority.write_bytes(original)
        assert authority.read_bytes() == original
        print("CONTROL material authority fingerprint changes despite identical output; exact original authority restored, no identical restored rerun")
        assert observed("authority-not-registered", dict(gate, inputs={}))['undeclared'] == ["authority.py", "neighbor.txt"]

        # Remove only the classifier loop, keeping the production parser,
        # actual observed reads and registered material producer unchanged.
        parser = root / "classifier.py"
        parser.write_bytes(source)
        green_sha = hashlib.sha256(source).hexdigest()
        mutated = source.replace(addition, b"", 1)
        parser.write_bytes(mutated)
        node = next(node for node in ast.parse(mutated).body
                    if isinstance(node, ast.FunctionDef) and node.name == "declared_coverage")
        namespace = dict(module.__dict__)
        exec(compile(ast.Module(body=[node], type_ignores=[]), str(parser), "exec"), namespace)
        green = module.declared_coverage
        try:
            module.declared_coverage = namespace["declared_coverage"]
            lost = observed("sole-authority-classifier-removal")
            assert lost["undeclared"] == ["authority.py", "neighbor.txt"]
            try:
                correct(lost)
            except AssertionError:
                print("CONTROL sole material-authority classifier removal bites at missing coverage")
            else:
                raise AssertionError("sole classifier removal escaped regression control")
        finally:
            module.declared_coverage = green
            parser.write_bytes(source)
        assert module.declared_coverage is green and hashlib.sha256(parser.read_bytes()).hexdigest() == green_sha
        print("CONTROL exact green classifier/function restored SHA256 " + green_sha + "; no identical restored rerun")


def current_wrapper_source_controls() -> None:
    source = Path(__file__).resolve().parent
    wrappers = ("check-current-mainnet.sh", "check-weth10-current-mainnet.sh",
                "check-beacon-deposit-current-mainnet.sh", "check-prorata-current-mainnet.sh",
                "check-lido-ossifiable-proxy-current-mainnet.sh", "check-drip-current-mainnet.sh",
                "check-lido-twg-pinned-target-current-mainnet.sh")
    for name in wrappers:
        result = subprocess.run(["bash", "-n", str(source / name)], capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
    for name in ("check-beacon-deposit-current-mainnet.sh", "check-lido-twg-pinned-target-current-mainnet.sh"):
        text = (source / name).read_text()
        branch = text[text.index('if [[ "${1:-}" == "--static-self-check" ]]'):]
        branch = branch[:branch.index("\nfi") + 3]
        # Run the actual early-return branch with a synthetic Python launcher;
        # any fallthrough is a failure, and original child status is preserved.
        for child_exit in (0, 19):
            control = ('set -euo pipefail\nSCRIPT_DIR=/unused\nWRAPPER_ARGS=()\nSTATIC_ENV=()\n'
                       'gate_audit_python() { return ' + str(child_exit) + '; }\n'
                       'gate_audit_exec_python() { return ' + str(child_exit) + '; }\n'
                       + branch + '\nexit 77\n')
            result = subprocess.run(["bash", "-c", control, "static-branch", "--static-self-check"], capture_output=True, text=True)
            assert result.returncode == child_exit, (name, child_exit, result.returncode, result.stderr)
    with tempfile.TemporaryDirectory(prefix="gate-read-ordinary-") as directory:
        root = Path(directory)
        script = root / "ordinary.py"
        script.write_text("import os,sys;print(repr(sys.argv));print(os.environ['EXACT']);raise SystemExit(5)\n")
        env = dict(os.environ, EXACT="unchanged")
        env.pop("GATE_READ_AUDIT", None)
        plain = subprocess.run([sys.executable, "-B", str(script), "a b"], env=env, capture_output=True, text=True)
        command = 'SCRIPT_DIR="$1"; . "$SCRIPT_DIR/read-audit/launch.sh"; shift; gate_audit_python "$@"'
        observed = subprocess.run(["bash", "-c", command, "ordinary", str(source), sys.executable, "-B", str(script), "a b"], env=env, capture_output=True, text=True)
        assert (observed.returncode, observed.stdout, observed.stderr) == (plain.returncode, plain.stdout, plain.stderr)
        for code in ("raise SystemExit(5)", "import os,signal;os.kill(os.getpid(),signal.SIGTERM)"):
            original = [sys.executable, "-B", "-c", code]
            baseline = subprocess.run(original, env=env, capture_output=True, text=True)
            exec_command = command.replace('gate_audit_python "$@"', 'gate_audit_exec_python "$@"')
            direct = subprocess.run(["bash", "-c", exec_command, "exec-control", str(source), *original], env=env, capture_output=True, text=True)
            assert (direct.returncode, direct.stdout, direct.stderr) == (baseline.returncode, baseline.stdout, baseline.stderr)
            instrumented = subprocess.run(["bash", "-c", exec_command, "exec-control", str(source), *original], env=dict(env, GATE_READ_AUDIT=str(root / "exec.log")), capture_output=True, text=True)
            assert (instrumented.returncode, instrumented.stdout, instrumented.stderr) == (baseline.returncode, baseline.stdout, baseline.stderr)
    print("CONTROL current wrappers bash syntax, static-only return/status, and ordinary adapter exact argv/env/output/status")


def main() -> int:
    current_wrapper_source_controls()
    observer_removal_control()
    descendant_observation_controls()
    legacy_descendant_controls()
    launch_event_regression_controls()
    material_authority_coverage_controls()
    tracked_population_coverage_control()
    hook_control()
    declared_untracked_control()
    code, cold, audited, output, _ = exercise([])
    assert code == 0 and cold == ["cold"] and audited == ["alpha", "beta"]
    assert "2 gates executed" in output

    code, cold, audited, output, _ = exercise(["--only", "beta"])
    assert code == 0 and cold == ["cold"] and audited == ["beta"]
    assert "1 gates executed" in output

    code, cold, audited, output, error = exercise([], unknown=True)
    assert code == 2 and audited == ["alpha", "beta"] and cold == ["cold"]
    assert "UNVERIFIED OBSERVATION: synthetic unresolved descriptor" in output
    assert "REFUSED — gate read audit" in error

    code, _, _, _, error = exercise([], failed=True)
    assert code == 1 and "gates that did not exit 0: alpha" in error

    for arguments, diagnostic in (
        (["--only"], "expected at least one argument"),
        (["--only", "missing"], "unknown cacheable gate id(s): missing"),
        (["--only", "alpha", "missing"], "unknown cacheable gate id(s): missing"),
    ):
        code, cold, audited, output, error = exercise(arguments)
        assert code == 2 and not cold and not audited and not output
        assert diagnostic in error

    print("OK — gate read audit controls: real sanitized/isolated/legacy descendants and identity parity, loss/receipt/short-write refusals, sole-removal restoration, dir_fd paths and cleanup attributed, unknown descriptors refused, "
          "declared untracked read honoured and its absence flagged; "
          "CLI default/all, explicit selection, empty and unknown refusal")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
