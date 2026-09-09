#!/usr/bin/env python3
"""Fail-closed control suite for the selective gate runner.

WHY THIS EXISTS
---------------

The runner's whole value is that it *skips* work, so every bug in it has the
same shape: a gate that should have run did not, and a stale verdict was
credited to a candidate it does not describe.  That failure is silent by
construction -- a wrongly skipped gate prints nothing and the checkpoint goes
green -- so it cannot be caught by using the tool.  It has to be caught by
controls that deliberately move one input at a time and insist the gate runs.

Every control therefore proves *both halves*: that a relevant change forces
execution, and that an irrelevant one does not.  A selector that reran
everything would pass the first half and fail the second; one that skipped
everything would pass the second and fail the first.

The suite runs against scratch repositories, never against Blanc's own tree,
so it is safe to run at any time and asserts on the real engine rather than on
a reimplementation of it.

Scratch means more than the tree.  The runner also asks the host for admission
before it elaborates its build prerequisite, and these controls answer that
request themselves (`Coordination`) instead of putting it to the machine.  A
suite that consulted the live host would take a real hold sized for a real Lean
build in order to run a shell script that echoes, and would inherit whatever
else was running as a hidden input -- reddening at random and telling nobody
why.  That is not hypothetical: it is the defect this stand-in was written for.

NEGATIVE CONTROLS
-----------------

`control_negative_*` are controls on the controls.  Each one breaks the engine
in the exact way a careless change would -- laundering an unidentifiable input
into "unchanged", dropping the post-execution drift check, caching a failed
run -- and requires that some earlier control then FAILS.  Without them a
control suite can rot into a set of assertions that hold vacuously.
"""

from __future__ import annotations

import contextlib
import copy
import datetime as dt
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

import importlib.util
import gate_sampling as gs
import gate_semaphore
import worktree_seed as ws

_SPEC = importlib.util.spec_from_file_location(
    "gate_cache", Path(__file__).resolve().parent / "gate-cache.py"
)
assert _SPEC and _SPEC.loader
gc = importlib.util.module_from_spec(_SPEC)
sys.modules["gate_cache"] = gc
_SPEC.loader.exec_module(gc)


class ControlFailure(AssertionError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ControlFailure(message)


# --- the coordination environment -------------------------------------------

#: Every environment variable `gate-semaphore.sh` and `gate_semaphore.py` read.
#: They are inputs to the admission exchange exactly as the host's answer is.
SEMAPHORE_ENVIRONMENT = (
    "BLANC_GATE_SEMAPHORE",
    "BLANC_GATE_SEMAPHORE_LABEL",
    "BLANC_GATE_SEMAPHORE_WAIT",
    "BLANC_GATE_SEMAPHORE_MEMORY_GIB",
)


@contextmanager
def environment(values: dict[str, str | None]):
    """Set, or with ``None`` clear, environment variables for the block."""

    saved = {name: os.environ.get(name) for name in values}
    try:
        for name, value in values.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value
        yield
    finally:
        for name, value in saved.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value


@contextmanager
def declared_coordination(mode: str | None):
    """Run under exactly the coordination mode a control declares.

    `Coordination` took the live *host* out of this suite's inputs.  The
    *environment* stayed in, and it is the same class of hidden input: with
    `BLANC_GATE_SEMAPHORE=off` -- which `scripts/GATES.md` and
    `gate-semaphore.sh` document as the supported CI setting -- `acquire_once`
    returns before the entry point is ever spawned, so a suite that inherited
    it would assert the coordinated contract while exercising the
    uncoordinated branch: green on a developer's machine, red in CI, with
    nothing in the suite naming what it was sensitive to.

    So no control here reads the environment it was started with.  Each states
    the mode it is about, and each of the four modes -- coordinated, `off`,
    `inherited`, and no entry point at all -- has a control asserting what that
    mode is supposed to do.  ``None`` is the coordinated mode: every variable
    absent.
    """

    with environment(dict.fromkeys(SEMAPHORE_ENVIRONMENT, None)):
        with environment({"BLANC_GATE_SEMAPHORE": mode} if mode is not None else {}):
            yield


def declared_label(mode: str | None = None) -> str:
    """The goal label a run under `mode` acquires under.

    Read inside the declared environment, never the ambient one: a control that
    compared a request made under `declared_coordination` against a label
    computed under whatever `BLANC_GATE_SEMAPHORE_LABEL` happened to be set to
    would be asserting across two different environments.
    """

    with declared_coordination(mode):
        return gate_semaphore.label()


# --- scratch repository -----------------------------------------------------


class Scratch:
    """A throwaway repository with real files, real traces and a real git."""

    def __init__(self, root: Path, coordination: "Coordination") -> None:
        self.root = root
        self.coordination = coordination
        self.output = ""
        # The coordination mode this scratch's runs declare, and the entry
        # point they see.  Stated per control rather than inherited: see
        # `declared_coordination`.  `None` is the coordinated mode; a control
        # about the absent-entry-point branch points `semaphore_entry` at a
        # path that does not exist.
        self.semaphore_mode: str | None = None
        self.semaphore_entry: Path | None = None
        (root / "scripts").mkdir(parents=True, exist_ok=True)
        (root / "Blanc").mkdir(parents=True, exist_ok=True)
        (root / ".lake/build/lib/lean/Blanc").mkdir(parents=True, exist_ok=True)
        self.git("init", "-q")
        self.git("config", "user.email", "control@example.invalid")
        self.git("config", "user.name", "control")

    def write(self, relative: str, text: str) -> Path:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def gate(self, name: str, body: str, mode: int = 0o755) -> str:
        relative = f"scripts/{name}"
        path = self.write(relative, body)
        path.chmod(mode)
        return relative

    def passing_gate(self, name: str, marker: str) -> str:
        """A gate that succeeds and records that it ran.

        The marker file is how a control proves a body did *not* execute:
        asserting on a printed disposition would only test the report's own
        vocabulary, not whether the process started.
        """

        return self.gate(
            name,
            "#!/bin/sh\n"
            f'printf "%s\\n" "ran" >> "$(dirname "$0")/../{marker}"\n'
            f'echo "OK — {name}: 1/1 fine"\n',
        )

    def trace(self, module: str, dep_hash: str) -> Path:
        path = self.root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".trace")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"depHash": dep_hash}), encoding="utf-8")
        return path

    def registry(self, gates: list[dict[str, Any]], catalogue: bool = True) -> None:
        """Write the registry and, by default, a catalogue that reconciles.

        `run()` reconciles the registry against the catalogue before planning,
        so a scratch repository needs both.  Passing `catalogue=False` writes
        only the registry, which is how a control creates the drift that
        reconciliation is supposed to catch.
        """

        gc.atomic_json(gc.registry_path(self.root), {"schema": 1, "gates": gates})
        if not catalogue:
            return
        self.catalogue([" ".join(g["command"]) for g in gates], [])
        try:
            gc.atomic_write(self.root / gc.INVENTORY_RELATIVE, gc.render_inventory(self.root))
        except gc.GateCacheError:
            pass          # a deliberately malformed registry has no inventory

    def catalogue(self, commands: list[str], ci: list[str]) -> None:
        block = "\n".join(commands)
        self.write(
            "scripts/GATES.md",
            "# Verification gates\n\n"
            "**The full set, in order.** This is what a checkpoint runs:\n\n"
            f"```\n{block}\n```\n",
        )
        self.write(
            ".github/workflows/ci.yml",
            "jobs:\n  gates:\n    steps:\n"
            + "".join(f"      - run: {command}\n" for command in ci),
        )

    def load(self) -> dict[str, Any]:
        return gc.load_registry(gc.registry_path(self.root))

    def cache(self) -> tuple[dict[str, Any], str | None]:
        return gc.read_cache(gc.cache_path(self.root))

    def run(self, fresh: bool = False) -> int:
        """Drive the real runner, capturing its output.

        Captured rather than silenced: a control that fails needs the run's own
        words, and forty scratch runs printing to the terminal would bury the
        one line that matters.
        """

        gc.forget_digests()
        arguments = type("A", (), {"fresh": fresh, "echo": False})()
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            # The runner asks the host for admission before it elaborates the
            # build prerequisite.  Pointed at the real entry point, every
            # scratch run here would take a live host-wide hold sized for a
            # Lean build in order to run a shell script that echoes: it would
            # charge the host for work that is not Lean, starve whatever else
            # was running, and redden this suite whenever the machine happened
            # to be busy.  The exchange still happens in full; it happens
            # against a stand-in that this control owns and can answer.
            entry = self.semaphore_entry or self.coordination.entry
            with declared_coordination(self.semaphore_mode):
                with patched(gate_semaphore, "ENTRY", entry):
                    code = gc.run(self.root, arguments)
        self.output = out.getvalue() + err.getvalue()
        return code

    def plan(self, fresh: bool = False) -> list[dict[str, Any]]:
        gc.forget_digests()
        cache, _ = self.cache()
        return gc.plan(self.root, self.load(), cache, fresh=fresh)

    def disposition(self, identifier: str, fresh: bool = False) -> str:
        for row in self.plan(fresh=fresh):
            if row["id"] == identifier:
                return row["disposition"]
        raise ControlFailure(f"no planned row for {identifier}")

    def ran(self, marker: str) -> int:
        path = self.root / marker
        return len(path.read_text().splitlines()) if path.is_file() else 0

    def git(self, *arguments: str) -> str:
        result = subprocess.run(
            ["git", *arguments], cwd=self.root, capture_output=True, text=True, check=True
        )
        return result.stdout.strip()

    def git_init(self) -> None:
        self.git("add", "-A")
        self.git("-c", "commit.gpgsign=false", "commit", "-q", "-m", "one")


class Coordination:
    """A scratch stand-in for the host coordination entry point.

    It is a real executable answering the real protocol, not a patched-out
    call: the runner still spawns it, still parses its answer, and still
    releases against it.  What it removes is the dependency on the live host,
    which is not an input this suite is entitled to depend on -- and what it
    adds is a host whose answers a control can choose, which is what makes the
    admission contract falsifiable at all.
    """

    def __init__(self, directory: Path) -> None:
        directory.mkdir(parents=True, exist_ok=True)
        self.directory = directory
        self.calls = directory / "calls.log"
        self.verdict = directory / "verdict"
        self.entry = directory / "semaphore"
        self.answer("admit")
        self.entry.write_text(
            "#!/bin/sh\n"
            f'printf "%s\\n" "$*" >> "{self.calls}"\n'
            f'verdict=$(cat "{self.verdict}")\n'
            'case "$1:$verdict" in\n'
            "  adaptive-acquire:refuse)\n"
            '    echo "REFUSED DEFER_HEAVY: another session holds the host"; exit 3 ;;\n'
            "  adaptive-acquire:already-held)\n"
            '    echo "ALREADY_HELD: this label already holds the host"; exit 4 ;;\n'
            "  adaptive-acquire:already-held-soft)\n"
            '    echo "ALREADY_HELD: label already owns a soft hold; use renew"; exit 4 ;;\n'
            "  adaptive-acquire:already-held-hard)\n"
            '    echo "ALREADY_HELD: label already owns the hard hold; use renew"; exit 4 ;;\n'
            "esac\n"
            "echo OK\n",
            encoding="utf-8",
        )
        self.entry.chmod(0o755)

    def answer(self, verdict: str) -> None:
        """Choose what the host says to the next admission request."""
        self.verdict.write_text(verdict + "\n", encoding="utf-8")

    def calls_made(self) -> list[str]:
        if not self.calls.is_file():
            return []
        return self.calls.read_text(encoding="utf-8").splitlines()

    def forget(self) -> None:
        self.calls.unlink(missing_ok=True)


@contextmanager
def scratch():
    directory = Path(tempfile.mkdtemp(prefix="gate-cache-control-"))
    # Outside the scratch repository: a coordination trace inside it would be
    # an input the controls digest.
    coordination = Path(tempfile.mkdtemp(prefix="gate-cache-coordination-"))
    try:
        yield Scratch(directory, Coordination(coordination))
    finally:
        shutil.rmtree(directory, ignore_errors=True)
        shutil.rmtree(coordination, ignore_errors=True)


@contextmanager
def seed_pair():
    directory = Path(tempfile.mkdtemp(prefix="worktree-seed-control-"))
    source = directory / "source"
    target = directory / "target"
    source.mkdir()
    s = Scratch(source, Coordination(directory / "coordination"))
    s.write(".gitignore", ".lake/\nscripts/baseline-elab.txt\n")
    prepare_build_state(s)
    s.write(
        "scripts/baseline-elab.txt",
        "# host-local control baseline\nOK\t1.0\tBlanc.lean\nOK\t1.0\tBlanc/A.lean\n",
    )
    s.git("worktree", "add", "-q", "-b", "target-control", str(target), "HEAD")
    try:
        with patched(
            gc,
            "component_tools",
            lambda root, tools: (gc.digest_of({"tool": "one"}), {"tool": "one"}),
        ):
            gc.write_build_certificate(source)
            yield s, source, target
    finally:
        shutil.rmtree(directory, ignore_errors=True)


def simple_gate(
    identifier: str,
    command: list[str],
    inputs: dict[str, Any],
    pattern: str,
    order: int = 1,
) -> dict[str, Any]:
    return {
        "id": identifier,
        "order": order,
        "command": command,
        "kind": "cacheable",
        "inputs": inputs,
        "verdict": {"expect_exit": 0, "summary_patterns": [pattern]},
    }


def prepare_build_state(s: Scratch) -> Path:
    """Give a scratch checkout the minimum exact state a build may certify."""

    s.write("lean-toolchain", "leanprover/lean4:v4.32.0\n")
    s.write("lakefile.lean", "import Lake\nopen Lake DSL\npackage blanc\n")
    s.write("Blanc.lean", "import Blanc.A\n")
    s.write("Blanc/A.lean", "theorem a : True := trivial\n")
    s.trace("Blanc", "root-dep-hash")
    s.trace("Blanc.A", "a-dep-hash")

    package = s.root / ".lake/packages/jaune"
    package.mkdir(parents=True)
    subprocess.run(["git", "init", "-q"], cwd=package, check=True)
    subprocess.run(["git", "config", "user.email", "control@example.invalid"], cwd=package, check=True)
    subprocess.run(["git", "config", "user.name", "control"], cwd=package, check=True)
    (package / "Jaune.lean").write_text("def jaune := 1\n", encoding="utf-8")
    runner = package / ".lake/build/bin/jaune"
    runner.parent.mkdir(parents=True, exist_ok=True)
    runner.write_text("runner-one\n", encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=package, check=True)
    subprocess.run(
        ["git", "-c", "commit.gpgsign=false", "commit", "-q", "-m", "pin"],
        cwd=package,
        check=True,
    )
    pin = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=package, capture_output=True, text=True, check=True
    ).stdout.strip()
    gc.atomic_json(
        s.root / "lake-manifest.json",
        {"version": "1.1.0", "packages": [{"name": "jaune", "rev": pin}]},
    )
    s.git_init()
    return package


# --- controls: the reuse decision itself ------------------------------------


def control_first_run_executes_and_second_reuses() -> None:
    """Both halves at once: nothing is credited before it is earned, and an
    unchanged candidate does not pay twice."""

    with scratch() as s:
        s.write("Blanc/A.lean", "theorem a : True := trivial\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        require(s.run() == 0, "first run should be green")
        require(s.ran("ran.txt") == 1, "first run must execute the body")
        require(s.run() == 0, "second run should be green")
        require(s.ran("ran.txt") == 1, "second run must NOT execute the body")
        require(s.disposition("g") == "reused", "second plan should reuse")


def control_content_change_invalidates() -> None:
    with scratch() as s:
        s.write("Blanc/A.lean", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        s.run()
        s.write("Blanc/A.lean", "two\n")
        require(s.disposition("g") == "fresh", "a content change must force execution")
        s.run()
        require(s.ran("ran.txt") == 2, "the body must actually have run again")


def control_population_membership_invalidates() -> None:
    """Adding and deleting a file both count.

    An absence gate depends on membership far more than on content, and a
    corpus scanner that gains a module has gained a claim it never checked.
    """

    with scratch() as s:
        s.write("Blanc/A.lean", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        s.run()
        s.write("Blanc/B.lean", "two\n")
        require(s.disposition("g") == "fresh", "an added file must force execution")
        s.run()
        # Delete a *different* member, so the surviving population is one this
        # cache has never seen.  Deleting the file just added would return the
        # corpus to a state that already has its own record, and reuse there is
        # correct rather than a defect.
        (s.root / "Blanc/A.lean").unlink()
        require(s.disposition("g") == "fresh", "a deleted file must force execution")

        # A rename moves a claim from one module to another while the corpus's
        # contents, taken as a bag, are identical.  A digest over content alone
        # cannot see it, which is why paths are part of the digested structure.
        for path in (s.root / "Blanc").glob("*.lean"):
            path.unlink()
        s.write("Blanc/A.lean", "one\n")
        s.run()
        (s.root / "Blanc/A.lean").unlink()
        s.write("Blanc/Renamed.lean", "one\n")
        require(s.disposition("g") == "fresh", "a rename must force execution")


def control_unrelated_change_still_reuses() -> None:
    """The anti-vacuity half: a selector that reruns everything is worthless."""

    with scratch() as s:
        s.write("Blanc/A.lean", "one\n")
        s.write("docs/unrelated.md", "prose\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        s.run()
        s.write("docs/unrelated.md", "different prose\n")
        require(s.disposition("g") == "reused", "an undeclared, unread file must not invalidate")


def control_membership_mode_ignores_content() -> None:
    with scratch() as s:
        s.write("tree/x.txt", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command],
            {"populations": [{"root": "tree", "pattern": "*", "mode": "membership"}]},
            "^OK — g.sh: ")])
        s.run()
        s.write("tree/x.txt", "two\n")
        require(s.disposition("g") == "reused", "membership mode must ignore content")
        s.write("tree/y.txt", "new\n")
        require(s.disposition("g") == "fresh", "membership mode must catch a new member")


def control_implementation_change_invalidates() -> None:
    """Changing the checker is changing the claim."""

    with scratch() as s:
        helper = s.write("scripts/helper.py", "# v1\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"files": ["scripts/helper.py"]}, "^OK — g.sh: ")])
        s.run()
        helper.write_text("# v2\n", encoding="utf-8")
        require(s.disposition("g") == "fresh", "a helper edit must force execution")


def control_command_arguments_invalidate() -> None:
    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"files": ["scripts/x.txt"]}, "^OK — g.sh: ")])
        s.run()
        before = s.disposition("g")
        require(before == "reused", "unchanged command should reuse")
        s.registry([simple_gate(
            "g", ["scripts/g.sh", "--base", "main"], {"files": ["scripts/x.txt"]},
            "^OK — g.sh: ")])
        require(s.disposition("g") == "fresh", "a different argv is a different command")


def control_registry_declaration_invalidates() -> None:
    """Evidence recorded under a narrower declaration cannot be credited to a
    wider one: the earlier run never looked at the newly declared input."""

    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        s.write("scripts/y.txt", "two\n")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate("g", ["scripts/g.sh"], {"files": ["scripts/x.txt"]},
                                "^OK — g.sh: ")])
        s.run()
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"files": ["scripts/x.txt", "scripts/y.txt"]},
            "^OK — g.sh: ")])
        require(s.disposition("g") == "fresh", "a widened declaration must force execution")


def control_lock_implementation_is_not_gate_evidence_identity() -> None:
    gate = simple_gate("g", ["scripts/g.sh"], {}, "^OK — g: ")
    sources = gc.runner_identity_sources(gate)
    require("gate-cache.py#soundness" in sources,
            "the soundness authority must remain identified")
    require(
        "gate_cache_lock.py" not in sources,
        "serialization-only lock code must not invalidate gate evidence",
    )


def control_presentation_edits_preserve_soundness_identity() -> None:
    source = Path(gc.__file__).read_text(encoding="utf-8")
    baseline = gc.semantic_authority_digest(Path(gc.__file__))
    mutations = (
        source.replace("# Blanc selective gate checkpoint", "# Reformatted checkpoint", 1),
        source.replace("report what would run, without running it",
                       "preview candidate dispositions", 1),
        source + "\n# presentation-only trailing comment\n",
    )
    with tempfile.TemporaryDirectory(prefix="gate-runner-presentation-") as temp:
        for index, text in enumerate(mutations):
            path = Path(temp) / f"runner-{index}.py"
            path.write_text(text, encoding="utf-8")
            require(gc.semantic_authority_digest(path) == baseline,
                    "comments, CLI help, and report formatting must preserve verdict identity")


def control_soundness_edit_invalidates_every_cacheable_row() -> None:
    source = Path(gc.__file__).read_text(encoding="utf-8")
    changed = source.replace(
        "if result.returncode != expected:",
        "if result.returncode == expected:",
        1,
    )
    require(changed != source, "soundness mutation did not apply")
    with tempfile.TemporaryDirectory(prefix="gate-runner-soundness-") as temp:
        path = Path(temp) / "runner.py"
        path.write_text(changed, encoding="utf-8")
        require(gc.semantic_authority_digest(path) !=
                gc.semantic_authority_digest(Path(gc.__file__)),
                "verdict validation movement must change global soundness identity")


def control_scheduling_metadata_is_not_substantive_verdict_identity() -> None:
    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        gate = simple_gate("g", ["scripts/g.sh"], {"files": ["scripts/x.txt"]},
                           "^OK — g: ")
        before, _ = gc.fingerprint(s.root, gate)
        moved = copy.deepcopy(gate)
        moved["order"] = 99
        moved["ci_only"] = True
        moved["prerequisite"] = False
        after, _ = gc.fingerprint(s.root, moved)
        require(after == before,
                "order and CI placement must not retroactively change a substantive verdict")


def control_t8n_resolver_invalidates_only_its_consumers() -> None:
    ordinary = simple_gate(
        "ordinary",
        ["scripts/ordinary.sh"],
        {"files": ["scripts/x.txt"]},
        "^OK — ordinary: ",
    )
    current = simple_gate(
        "current",
        ["scripts/current.sh"],
        {"files": ["@t8n_python_base/bin/python3.11"]},
        "^OK — current: ",
    )
    before_ordinary, _ = gc.runner_identity(ordinary)
    before_current, _ = gc.runner_identity(current)
    original = gc.file_digest

    def changed_t8n_only(path: Path) -> str:
        if path.name == gc.RUNNER_T8N_SOURCE:
            return "f" * 64
        return original(path)

    with patched(gc, "file_digest", changed_t8n_only):
        after_ordinary, _ = gc.runner_identity(ordinary)
        after_current, _ = gc.runner_identity(current)
    require(
        after_ordinary == before_ordinary,
        "a t8n resolver change must preserve unrelated gate fingerprints",
    )
    require(
        after_current != before_current,
        "a t8n resolver change must invalidate current-mainnet consumers",
    )


def control_unparsable_import_cannot_hide_a_dependency() -> None:
    """An import the parser does not understand must raise, not be dropped.

    The hole this closes is narrow and entirely silent.  An entry file's own
    source is always digested, so any edit to it invalidates the gate anyway --
    which is why a control that merely edits the file proves nothing.  The real
    exposure is a *stable* entry carrying an import the parser skips: the
    imported module's depHash then never reaches the fingerprint, and the gate
    is reused for ever afterwards no matter how that module moves.
    """

    with scratch() as s:
        s.trace("Blanc.A", "aaaa000000000000")
        s.trace("Blanc.B", "bbbb000000000000")
        s.write("scripts/Eval.lean",
                "import Blanc.A\nimport Blanc.B -- a trailing comment\n"
                "example : True := trivial\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"lean_entries": ["scripts/Eval.lean"]}, "^OK — g.sh: ")])
        s.run()
        # The entry file itself never changes from here on.
        s.trace("Blanc.B", "cccc111111111111")
        require(
            s.disposition("g") == "fresh",
            "a module imported on an unparsed line must not become invisible to "
            "the fingerprint",
        )


# --- controls: the Lake boundary --------------------------------------------


def control_lean_module_dep_hash_invalidates() -> None:
    with scratch() as s:
        s.trace("Blanc.A", "aaaa000000000000")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"lean_modules": ["Blanc.A"]}, "^OK — g.sh: ")])
        s.run()
        require(s.disposition("g") == "reused", "an unmoved depHash should reuse")
        s.trace("Blanc.A", "bbbb111111111111")
        require(s.disposition("g") == "fresh", "a moved depHash must force execution")


def control_missing_trace_forces_execution() -> None:
    """A stale or absent trace is not evidence.

    This is the whole reason the Lean closure is delegated rather than
    duplicated: if Lake cannot say what a module depends on right now, nothing
    else in this repository is entitled to guess.
    """

    with scratch() as s:
        s.trace("Blanc.A", "aaaa000000000000")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"lean_modules": ["Blanc.A"]}, "^OK — g.sh: ")])
        s.run()
        (s.root / ".lake/build/lib/lean/Blanc/A.trace").unlink()
        require(s.disposition("g") == "fresh", "a missing trace must force execution")


def control_malformed_trace_forces_execution() -> None:
    with scratch() as s:
        s.trace("Blanc.A", "aaaa000000000000")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"lean_modules": ["Blanc.A"]}, "^OK — g.sh: ")])
        s.run()
        for text in ("not json at all", '{"depHash": ""}', '{"other": 1}', "[]"):
            (s.root / ".lake/build/lib/lean/Blanc/A.trace").write_text(text, encoding="utf-8")
            require(
                s.disposition("g") == "fresh",
                f"a trace of {text!r} must force execution, not reuse",
            )


def control_lean_entry_source_and_imports_invalidate() -> None:
    """An ad-hoc evaluator has two halves: its own text, and what it imports."""

    with scratch() as s:
        s.trace("Blanc.A", "aaaa000000000000")
        s.trace("Blanc.B", "bbbb000000000000")
        s.write("scripts/Eval.lean", "import Blanc.A\nexample : True := trivial\n")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"lean_entries": ["scripts/Eval.lean"]}, "^OK — g.sh: ")])
        s.run()
        require(s.disposition("g") == "reused", "an unchanged evaluator should reuse")

        s.write("scripts/Eval.lean", "import Blanc.A\nexample : True := by trivial\n")
        require(s.disposition("g") == "fresh", "evaluator source must invalidate")
        s.run()

        s.trace("Blanc.A", "cccc222222222222")
        require(s.disposition("g") == "fresh", "an imported module's depHash must invalidate")
        s.run()

        s.write("scripts/Eval.lean",
                "import Blanc.A\nimport Blanc.B\nexample : True := by trivial\n")
        require(s.disposition("g") == "fresh", "a new import must invalidate")
        s.run()

        s.write("scripts/Eval.lean",
                "import Blanc.A\nimport Blanc.Missing\nexample : True := by trivial\n")
        require(
            s.disposition("g") == "fresh",
            "an import with no trace must force execution rather than be skipped",
        )



def control_transitive_edit_reaches_the_gate() -> None:
    """The point of delegating to Lake: a gate naming only a root still
    invalidates when something deep beneath that root moves, because the root's
    depHash moved with it."""

    with scratch() as s:
        s.trace("Blanc", "root0000000000000")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"lean_modules": ["Blanc"]}, "^OK — g.sh: ")])
        s.run()
        # Lake recomputes the root's depHash when any transitive import moves.
        s.trace("Blanc", "root1111111111111")
        require(s.disposition("g") == "fresh", "a moved root depHash must force execution")


# --- controls: dynamic inputs ----------------------------------------------


def control_git_ref_movement_invalidates() -> None:
    with scratch() as s:
        s.write("Blanc/A.lean", "one\n")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"git_refs": ["HEAD"]}, "^OK — g.sh: ")])
        s.git_init()
        s.run()
        require(s.disposition("g") == "reused", "an unmoved ref should reuse")
        s.write("Blanc/A.lean", "two\n")
        s.git("add", "-A")
        s.git("-c", "commit.gpgsign=false", "commit", "-q", "-m", "two")
        require(
            s.disposition("g") == "fresh",
            "a moved base ref must force execution even though no declared file changed",
        )


def control_unresolvable_ref_forces_execution() -> None:
    with scratch() as s:
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"git_refs": ["no-such-ref"]}, "^OK — g.sh: ")])
        s.git_init()
        require(s.disposition("g") == "fresh", "an unresolvable ref must force execution")
        require(s.run() == 0, "the gate should still run and pass")
        require(
            s.disposition("g") == "fresh",
            "a gate with no fingerprint can never be credited from a record",
        )


def control_external_checkout_identity() -> None:
    """A clean pinned checkout can be fingerprinted; a dirty, absent or
    off-pin one cannot, because its commit stops summarising its content."""

    with scratch() as s, scratch() as outside:
        outside.write("payload.txt", "one\n")
        outside.git_init()
        head = outside.git("rev-parse", "HEAD")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        spec = {"id": "ext", "path": str(outside.root), "pin": head}
        s.registry([simple_gate("g", ["scripts/g.sh"], {"external": [spec]}, "^OK — g.sh: ")])
        s.run()
        require(s.disposition("g") == "reused", "a clean pinned checkout should reuse")

        spec_short = dict(spec, pin=head[:1])
        s.registry([simple_gate("g", ["scripts/g.sh"], {"external": [spec_short]},
                                "^OK — g.sh: ")])
        try:
            s.load()
        except gc.GateCacheError:
            pass
        else:
            raise ControlFailure("an abbreviated external pin must be refused")

        s.registry([simple_gate("g", ["scripts/g.sh"], {"external": [spec]},
                                "^OK — g.sh: ")])

        outside.write("payload.txt", "dirty\n")
        require(s.disposition("g") == "fresh", "a dirty external checkout must force execution")

        outside.git("checkout", "-q", "--", "payload.txt")
        require(s.disposition("g") == "reused", "a restored checkout should reuse again")

        spec_wrong = dict(spec, pin="0" * 40)
        s.registry([simple_gate("g", ["scripts/g.sh"], {"external": [spec_wrong]},
                                "^OK — g.sh: ")])
        require(s.disposition("g") == "fresh", "an off-pin checkout must force execution")

        spec_absent = dict(spec, path=str(outside.root / "nowhere"))
        s.registry([simple_gate("g", ["scripts/g.sh"], {"external": [spec_absent]},
                                "^OK — g.sh: ")])
        require(s.disposition("g") == "fresh", "an absent checkout must force execution")


def control_oracle_lanes_are_disjoint_and_exact() -> None:
    """The historical Prague and current-mainnet roots cannot be cross-wired."""

    with scratch() as s:
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')

        def gate(inputs: dict[str, Any]) -> dict[str, Any]:
            return simple_gate("g", ["scripts/g.sh"], inputs, "^OK — g.sh: ")

        legacy_external = {
            "id": "eels",
            "path": "~/execution-specs",
            "path_env": "EELS_ROOT",
            "pin": gc.LEGACY_EELS_PIN,
        }
        current_external = {
            "id": "t8n_target",
            "path": "~/execution-specs-t8n-amsterdam",
            "path_env": "JAUNE_T8N_TARGET",
            "pin": gc.CURRENT_T8N_PIN,
        }
        shared_files = [
            "scripts/current-mainnet-target.json",
            "scripts/current-mainnet-runtime-lock.json",
            "scripts/current_mainnet.py",
        ]
        for path in shared_files:
            s.write(path, "fixture\n")

        valid_legacy = {
            "env": ["EELS_ROOT", "HOME"],
            "external": [legacy_external],
            "files": ["@eels/venv/bin/python"],
        }
        s.registry([gate(valid_legacy)])
        s.load()

        valid_current = {
            "env": ["JAUNE_T8N_TARGET", "HOME"],
            "external": [current_external],
            "files": shared_files + ["@t8n_target/.venv/bin/python"],
        }
        s.registry([gate(valid_current)])
        s.load()

        mutants = []
        changed = copy.deepcopy(valid_legacy)
        changed["external"] = [current_external]
        mutants.append(("legacy repointed", changed))
        changed = copy.deepcopy(valid_current)
        changed["external"][0]["pin"] = gc.LEGACY_EELS_PIN
        mutants.append(("pins swapped", changed))
        changed = copy.deepcopy(valid_current)
        changed["env"].append("EELS_ROOT")
        mutants.append(("shared environment", changed))
        changed = copy.deepcopy(valid_current)
        changed["external"][0]["pin"] = gc.CURRENT_T8N_PIN[:1]
        mutants.append(("short pin", changed))
        changed = copy.deepcopy(valid_current)
        changed["files"].remove("scripts/current_mainnet.py")
        mutants.append(("helper omitted", changed))
        changed = copy.deepcopy(valid_current)
        changed["files"].remove("scripts/current-mainnet-runtime-lock.json")
        mutants.append(("runtime lock omitted", changed))

        for label, inputs in mutants:
            s.registry([gate(inputs)])
            try:
                s.load()
            except gc.GateCacheError:
                continue
            raise ControlFailure(f"{label} oracle-lane mutant was accepted")


def control_symlink_file_target_invalidates() -> None:
    """A file symlink's selector is identity, not only its target bytes."""

    with scratch() as s:
        first = s.write("runtime/a", "same\n")
        second = s.write("runtime/b", "same\n")
        link = s.root / "runtime/python"
        link.symlink_to(first)
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"files": ["runtime/python"]}, "^OK — g.sh: ")])
        s.run()
        require(s.disposition("g") == "reused", "unchanged file symlink should reuse")
        link.unlink()
        link.symlink_to(second)
        require(
            s.disposition("g") == "fresh",
            "retargeting a file symlink must invalidate even with equal target bytes",
        )


def control_current_mainnet_python_base_is_native() -> None:
    """The CPython root follows the venv selector instead of one OS literal."""

    with scratch() as s:
        target = s.root / "target"
        selector = target / ".venv/bin/python"
        selector.parent.mkdir(parents=True)
        bases = [s.root / "uv/a", s.root / "uv/b"]
        for base in bases:
            executable = base / "bin/python3.11"
            executable.parent.mkdir(parents=True)
            executable.write_text("same runtime\n", encoding="utf-8")
            (base / "lib/python3.11").mkdir(parents=True)
        selector.symlink_to(bases[0] / "bin/python3.11")
        old = os.environ.get("JAUNE_T8N_TARGET")
        os.environ["JAUNE_T8N_TARGET"] = str(target)
        try:
            resolved = gc.resolve_path(s.root, "@t8n_python_base/lib/python3.11")
            require(
                resolved == (bases[0] / "lib/python3.11").resolve(strict=True),
                "derived CPython root did not follow the first native selector",
            )
            selector.unlink()
            selector.symlink_to(bases[1] / "bin/python3.11")
            resolved = gc.resolve_path(s.root, "@t8n_python_base/lib/python3.11")
            require(
                resolved == (bases[1] / "lib/python3.11").resolve(strict=True),
                "derived CPython root did not follow a retargeted native selector",
            )
            selector.unlink()
            selector.write_text("not a selector\n", encoding="utf-8")
            try:
                gc.resolve_path(s.root, "@t8n_python_base/lib/python3.11")
            except gc.Unresolvable:
                pass
            else:
                raise ControlFailure("a non-symlink CPython selector was accepted")
        finally:
            if old is None:
                os.environ.pop("JAUNE_T8N_TARGET", None)
            else:
                os.environ["JAUNE_T8N_TARGET"] = old


def control_symlink_directory_selector_invalidates() -> None:
    """A stable runtime alias is identity even when contents are separate."""

    with scratch() as s:
        first = s.root / "runtime/a"
        second = s.root / "runtime/b"
        first.mkdir(parents=True)
        second.mkdir(parents=True)
        alias = s.root / "runtime/current"
        alias.symlink_to(first, target_is_directory=True)
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"files": ["runtime/current"]}, "^OK — g.sh: ")])
        s.run()
        require(s.disposition("g") == "reused", "unchanged directory alias should reuse")
        alias.unlink()
        alias.symlink_to(second, target_is_directory=True)
        require(s.disposition("g") == "fresh", "retargeting a directory alias must invalidate")


def control_environment_variable_invalidates() -> None:
    with scratch() as s:
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"env": ["GATE_CACHE_CONTROL"]}, "^OK — g.sh: ")])
        os.environ.pop("GATE_CACHE_CONTROL", None)
        s.run()
        require(s.disposition("g") == "reused", "an unset variable should reuse")
        os.environ["GATE_CACHE_CONTROL"] = "stage-2"
        try:
            require(s.disposition("g") == "fresh", "a set variable must force execution")
        finally:
            os.environ.pop("GATE_CACHE_CONTROL", None)


def control_expiry_clock_moves_only_at_semantic_transition() -> None:
    with scratch() as s:
        registry = s.write("scripts/exceptions.json", json.dumps({"exceptions": []}))
        spec = {"kind": "expiry-transitions", "files": ["scripts/exceptions.json"]}
        plus_nine = dt.timezone(dt.timedelta(hours=9))
        minus_eight = dt.timezone(dt.timedelta(hours=-8))
        early = dt.datetime(2026, 9, 1, 0, 1, tzinfo=plus_nine)
        late = dt.datetime(2026, 9, 30, 23, 59, tzinfo=minus_eight)
        require(gc.component_clock(s.root, spec, early)[0] ==
                gc.component_clock(s.root, spec, late)[0],
                "an empty exception registry must survive every civil-date rollover")

        registry.write_text(json.dumps({"exceptions": [{"expires": "2026-09-01"}]}),
                            encoding="utf-8")
        before_utc = dt.datetime(2026, 9, 1, 14, 30, tzinfo=dt.timezone.utc)
        after_utc = dt.datetime(2026, 9, 1, 15, 30, tzinfo=dt.timezone.utc)
        before_plus = before_utc.astimezone(plus_nine)
        after_plus = after_utc.astimezone(plus_nine)
        before_minus = before_utc.astimezone(minus_eight)
        require(gc.component_clock(s.root, spec, before_plus)[0] ==
                gc.component_clock(s.root, spec, before_minus)[0],
                "positive and negative offsets before their local boundary must agree")
        require(gc.component_clock(s.root, spec, before_plus)[0] !=
                gc.component_clock(s.root, spec, after_plus)[0],
                "UTC+9 must invalidate at its first local date after expiry")
        require(gc.component_clock(s.root, spec, before_minus)[0] ==
                gc.component_clock(s.root, spec, after_utc.astimezone(minus_eight))[0],
                "a negative offset must not invalidate before its own local boundary")

        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate("g", ["scripts/g.sh"], {"clock": spec},
                                "^OK — g.sh: ")])
        real = gc.component_clock
        with patched(gc, "component_clock",
                     lambda root, contract: real(root, contract, before_plus)):
            s.run()
            require(s.disposition("g") == "reused",
                    "evidence must reuse before the semantic boundary")
        with patched(gc, "component_clock",
                     lambda root, contract: real(root, contract, after_plus)):
            require(s.disposition("g") == "fresh",
                    "evidence must invalidate exactly at the semantic boundary")


def control_tool_identity_invalidates() -> None:
    with scratch() as s:
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate("g", ["scripts/g.sh"], {"tools": ["python3"]}, "^OK — g.sh: ")])
        s.run()
        require(s.disposition("g") == "reused", "the same interpreter should reuse")
        original = dict(gc.TOOL_COMMANDS)
        gc.TOOL_COMMANDS["python3"] = ["python3", "-c", "print('Python 9.9.9')"]
        try:
            require(s.disposition("g") == "fresh", "a different tool identity must force execution")
        finally:
            gc.TOOL_COMMANDS.clear()
            gc.TOOL_COMMANDS.update(original)


def control_unknown_tool_is_a_registry_fault() -> None:
    with scratch() as s:
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate("g", ["scripts/g.sh"], {"tools": ["solc"]}, "^OK — g.sh: ")])
        try:
            s.plan()
        except gc.GateCacheError:
            return
        raise ControlFailure("an unidentifiable tool must be a fault, not a silent pass")


def control_exact_build_certificate_skips_only_the_authoritative_build() -> None:
    with scratch() as s:
        prepare_build_state(s)
        command = s.passing_gate("build.sh", "build-ran.txt")
        gate = {
            "id": "lake-build",
            "order": 1,
            "command": [command],
            "kind": "composition",
            "prerequisite": True,
            "reason": "authoritative build prerequisite",
            "inputs": {},
            "verdict": {"expect_exit": 0, "summary_patterns": ["^OK — build.sh: "]},
        }
        s.registry([gate])
        with patched(
            gc,
            "component_tools",
            lambda root, tools: (gc.digest_of({"tool": "one"}), {"tool": "one"}),
        ):
            require(s.run() == 0, "the first run should execute and certify the build")
            require(s.ran("build-ran.txt") == 1, "the first run must execute the build")
            require(s.run() == 0, "an exact certificate should satisfy the next run")
            require(s.ran("build-ran.txt") == 1, "an exact certificate must skip the body")
            require(
                s.disposition("lake-build") == "certified",
                "the plan must distinguish a certified build from reused gate evidence",
            )
            require(
                s.disposition("lake-build", fresh=True) == "fresh",
                "--fresh must still require the authoritative build",
            )


def build_prerequisite_repository(s: Scratch) -> None:
    """A scratch repository whose first row is the build prerequisite.

    The prerequisite is the one row the runner elaborates itself, so it is the
    one row whose admission exchange exists at all.  The planned row that
    follows it writes into the coordination trace, which is what lets a control
    read the acquire, the release and the planned execution as one ordered
    sequence rather than three separate facts.
    """

    prepare_build_state(s)
    build = s.passing_gate("build.sh", "build-ran.txt")
    planned = s.gate(
        "planned.sh",
        "#!/bin/sh\n"
        f'printf "%s\\n" "planned-row-ran" >> "{s.coordination.calls}"\n'
        'echo "OK — planned.sh: 1/1 fine"\n',
    )
    s.write("docs.md", "one\n")
    s.registry(
        [
            {
                "id": "lake-build",
                "order": 1,
                "command": [build],
                "kind": "composition",
                "prerequisite": True,
                "reason": "authoritative build prerequisite",
                "inputs": {},
                "verdict": {"expect_exit": 0, "summary_patterns": ["^OK — build.sh: "]},
            },
            simple_gate(
                "planned", [planned], {"files": ["docs.md"]},
                "^OK — planned.sh: ", order=2,
            ),
        ]
    )


def admission_requests(s: Scratch) -> list[str]:
    return [line for line in s.coordination.calls_made() if line.startswith("adaptive-acquire")]


def admission_releases(s: Scratch) -> list[str]:
    return [line for line in s.coordination.calls_made() if line.startswith("release")]


def control_build_prerequisite_coordinates_the_host_and_fails_closed() -> None:
    """The build prerequisite is the one row this runner elaborates itself, so
    it is the one row that has to ask the host for admission.  Three properties
    of that exchange are load-bearing and none of them was falsifiable before
    this control existed: a refusal must stop the build rather than let it
    elaborate on a machine that just said no, an inherited hold must be used
    and never released by the borrower, and the hold must be dropped before the
    planned rows so a selective run does not own the host end to end.
    """

    with scratch() as s:
        build_prerequisite_repository(s)
        with patched(
            gc,
            "component_tools",
            lambda root, tools: (gc.digest_of({"tool": "one"}), {"tool": "one"}),
        ):
            # A refusal is a refusal to run, not a gate failure and not a
            # licence to run anyway.
            s.coordination.answer("refuse")
            require(s.run() != 0, "a refused host must redden the run")
            require(s.ran("build-ran.txt") == 0, "a refused host must elaborate nothing")
            require(
                "planned-row-ran" not in s.coordination.calls_made(),
                "a refused prerequisite leaves no sound identity, so nothing may be planned",
            )
            require("REFUSED" in s.output, "the refusal must be reported, not swallowed")
            require(
                s.disposition("lake-build") == "fresh",
                "a build that never ran must never be certified",
            )

            # Admitted: the request is made, and the hold is let go of before
            # the planned rows rather than kept for the whole selective run.
            s.coordination.forget()
            s.coordination.answer("admit")
            require(s.run() == 0, "an admitted host lets the build run")
            require(s.ran("build-ran.txt") == 1, "an admitted prerequisite elaborates once")
            trace = s.coordination.calls_made()
            acquires = [i for i, line in enumerate(trace) if line.startswith("adaptive-acquire")]
            releases = [i for i, line in enumerate(trace) if line.startswith("release")]
            require(len(acquires) == 1, "the prerequisite must ask for admission exactly once")
            require(
                declared_label() in trace[acquires[0]]
                and "--memory-gib" in trace[acquires[0]],
                "the request must name this goal and a peak estimate",
            )
            require(len(releases) == 1, "an admitted hold must be released")
            require(
                "planned-row-ran" in trace,
                "the planned rows must still run after the prerequisite",
            )
            require(
                releases[0] < trace.index("planned-row-ran"),
                "the hold must be dropped before the planned rows, not held across the run",
            )

            # ALREADY_HELD: someone else's hold covers this elaboration.
            # Proceed under it, charge nothing twice, release nothing.
            s.coordination.forget()
            s.write("Blanc/A.lean", "theorem a : True := by trivial\n")
            s.coordination.answer("already-held")
            require(s.run() == 0, "an inherited hold lets the build run")
            require(s.ran("build-ran.txt") == 2, "the prerequisite still elaborates under it")
            trace = s.coordination.calls_made()
            require(
                [line for line in trace if line.startswith("adaptive-acquire")] != [],
                "an inherited hold is still asked for, not assumed",
            )
            require(
                [line for line in trace if line.startswith("release")] == [],
                "a hold this runner did not take must not be released by it",
            )


def control_coordination_off_never_asks_the_host_and_says_so() -> None:
    """`BLANC_GATE_SEMAPHORE=off` is the setting CI runs under.

    `scripts/GATES.md` and `gate-semaphore.sh` both name it: Creme is not a
    Blanc build dependency and a dedicated runner has nothing to coordinate
    with.  What `off` promises is not "ask and ignore the answer" but "do not
    ask": the entry point is never spawned, whatever it would have said.  A
    host answering `refuse` is therefore the sharpest way to state it -- under
    `off` that refusal must never reach the run.

    It promises one more thing.  An uncoordinated elaboration nobody can see is
    the failure this coordination exists to end, so `off` says so out loud, in
    a line shaped so that no gate's verdict pattern can match it.
    """

    with scratch() as s:
        build_prerequisite_repository(s)
        s.semaphore_mode = "off"
        s.coordination.answer("refuse")
        with patched(
            gc,
            "component_tools",
            lambda root, tools: (gc.digest_of({"tool": "one"}), {"tool": "one"}),
        ):
            require(s.run() == 0, "off must run the prerequisite without consulting the host")
            require(s.ran("build-ran.txt") == 1, "off must still elaborate the prerequisite once")
            require(admission_requests(s) == [], "off must make no admission request at all")
            require(admission_releases(s) == [], "off holds nothing, so it releases nothing")
            require(
                "planned-row-ran" in s.coordination.calls_made(),
                "the planned rows must run under off like any other mode",
            )
            require("REFUSED" not in s.output, "off must not let a refusal it never asked for in")
            notes = [
                line for line in s.output.splitlines()
                if "BLANC_GATE_SEMAPHORE=off" in line
            ]
            require(len(notes) == 1, "off must announce itself exactly once")
            require(
                notes[0].startswith("NOTE — ") and declared_label("off") in notes[0],
                "the announcement must name this goal and be shaped as a note, not a verdict",
            )


def control_coordination_inherited_borrows_and_releases_nothing() -> None:
    """`BLANC_GATE_SEMAPHORE=inherited` is a caller stating that it already
    holds the host for this work.  Taking a second hold would charge one unit
    twice; releasing at the end would drop a hold this process never took and
    hand the host away underneath its owner.  So the mode asks nothing and
    releases nothing, and a host that would refuse proves the first half.
    """

    with scratch() as s:
        build_prerequisite_repository(s)
        s.semaphore_mode = "inherited"
        s.coordination.answer("refuse")
        with patched(
            gc,
            "component_tools",
            lambda root, tools: (gc.digest_of({"tool": "one"}), {"tool": "one"}),
        ):
            require(s.run() == 0, "an inherited hold must let the prerequisite run")
            require(s.ran("build-ran.txt") == 1, "the prerequisite still elaborates under it")
            require(admission_requests(s) == [], "inherited must not ask for a second hold")
            require(
                admission_releases(s) == [],
                "a hold this process did not take must never be released by it",
            )
            require(
                "BLANC_GATE_SEMAPHORE=off" not in s.output
                and "no host coordination at" not in s.output,
                "inherited is neither the off branch nor the absent-entry-point branch",
            )


def control_absent_coordination_entry_point_announces_once_and_runs() -> None:
    """Blanc is standalone, and that is a promise about clones, not a setting.

    Where there is no Creme checkout there is nothing to ask, and the gate must
    run rather than refuse -- but it must not run quietly.  One announcement,
    naming the path that was looked for, so an uncoordinated elaboration is
    visible in the transcript of the run that performed it.
    """

    with scratch() as s:
        build_prerequisite_repository(s)
        s.semaphore_entry = s.coordination.directory / "no-semaphore-installed-here"
        require(not s.semaphore_entry.exists(), "the control needs an entry point that is absent")
        with patched(
            gc,
            "component_tools",
            lambda root, tools: (gc.digest_of({"tool": "one"}), {"tool": "one"}),
        ):
            require(s.run() == 0, "an absent entry point must not stop the prerequisite")
            require(s.ran("build-ran.txt") == 1, "the prerequisite still elaborates without it")
            require(
                admission_requests(s) == [] and admission_releases(s) == [],
                "an absent entry point cannot have been asked anything",
            )
            notes = [
                line for line in s.output.splitlines()
                if "no host coordination at" in line
            ]
            require(len(notes) == 1, "the absence must be announced exactly once")
            require(
                notes[0].startswith("NOTE — ") and str(s.semaphore_entry) in notes[0],
                "the announcement must name the path that was looked for",
            )


def control_coordination_controls_declare_their_own_environment() -> None:
    """The regression this whole group exists for.

    The admission controls were written against a stand-in host and an
    inherited environment, and `BLANC_GATE_SEMAPHORE=off` -- the supported CI
    setting -- makes `acquire_once` return before the stand-in is ever spawned.
    The result was a suite that passed 87/87 unset and failed 1/87 in CI while
    naming no input it was sensitive to: exactly the defect its own
    `Coordination` stand-in had just removed for the host.

    So the controls above are run again here under an ambient environment that
    sets every one of those variables to something hostile.  They must reach
    the same verdicts, because each declares the mode it is about.
    """

    hostile = {
        "BLANC_GATE_SEMAPHORE": "off",
        "BLANC_GATE_SEMAPHORE_LABEL": "somebody-elses-goal",
        "BLANC_GATE_SEMAPHORE_WAIT": "600",
        "BLANC_GATE_SEMAPHORE_MEMORY_GIB": "64",
    }
    with environment(hostile):
        with declared_coordination(None):
            for name in SEMAPHORE_ENVIRONMENT:
                require(
                    name not in os.environ,
                    f"{name} must not survive into a run that declared the coordinated mode",
                )
        with declared_coordination("inherited"):
            require(
                os.environ.get("BLANC_GATE_SEMAPHORE") == "inherited"
                and "BLANC_GATE_SEMAPHORE_WAIT" not in os.environ,
                "a declared mode must replace the ambient one, not be merged with it",
            )
        control_build_prerequisite_coordinates_the_host_and_fails_closed()
        control_coordination_off_never_asks_the_host_and_says_so()
    with environment(dict(hostile, BLANC_GATE_SEMAPHORE="inherited")):
        control_build_prerequisite_coordinates_the_host_and_fails_closed()


# --- the shell half of the same contract ------------------------------------
#
# `gate_semaphore.py` is one of two implementations of the admission contract.
# The other is `scripts/gate-semaphore.sh`, sourced by twenty gate wrappers,
# and until these controls existed the four mode controls above asserted the
# contract only where the Python driver implements it.  A shell `case` arm is
# exactly as easy to delete as a Python `if`, and its deletion turns the
# supported CI setting into a red run on a machine with nothing to coordinate
# with -- or, in the `inherited` direction, releases a hold the gate never took
# out from under the session that owns it.

GATE_SEMAPHORE_SHELL = Path(__file__).resolve().parent / "gate-semaphore.sh"


def gate_semaphore_shell_source() -> str:
    """`scripts/gate-semaphore.sh` exactly as committed.

    Read through a function so that a negative control can hand the harness a
    mutated shell half and require these controls to notice, which is the only
    way to know they are asserting the branches and not the outcome.
    """

    return GATE_SEMAPHORE_SHELL.read_text(encoding="utf-8")


class ShellAdmission:
    """A disposable tree that sources the real `gate-semaphore.sh`.

    What runs is the committed file, sourced by bash, spawning the same
    `Coordination` stand-in host the Python controls use -- not a description
    of it and not a re-implementation.

    It is deliberately not a `Scratch`.  `Scratch` is built around the gate
    runner's registry, report, build state and git history, none of which a
    sourced shell function reads; reusing it would mean carrying that whole
    apparatus in order to call one function, and every assertion would then be
    about the runner rather than about the shell.  What is reused is what the
    two halves genuinely share: the stand-in host, `declared_coordination`, and
    the rule that a control states the mode it is about rather than inheriting
    one.
    """

    #: The goal a gate run inside `<repo>/.worktrees/<goal>` belongs to.
    GOAL = "blanc-shell-admission-control"

    def __init__(self, root: Path, coordination: Coordination) -> None:
        self.root = root
        self.coordination = coordination
        source = gate_semaphore_shell_source()
        # Two placements, because the label the shell derives is a function of
        # where the gate is: inside a goal worktree, and in a plain clone.
        self.worktree = root / "blanc" / ".worktrees" / self.GOAL
        self.clone = root / "blanc-clone"
        for repository in (self.worktree, self.clone):
            (repository / "scripts").mkdir(parents=True, exist_ok=True)
            (repository / "scripts" / "gate-semaphore.sh").write_text(
                source, encoding="utf-8")
        # A Creme checkout whose entry point is the stand-in host, and one
        # with no entry point at all.
        self.creme = root / "creme"
        (self.creme / ".semaphore").mkdir(parents=True, exist_ok=True)
        entry = self.creme / ".semaphore" / "semaphore"
        entry.write_text(coordination.entry.read_text(encoding="utf-8"), encoding="utf-8")
        entry.chmod(0o755)
        self.creme_without_entry = root / "creme-without-a-semaphore"
        (self.creme_without_entry / ".semaphore").mkdir(parents=True, exist_ok=True)

    @property
    def absent_entry(self) -> Path:
        return self.creme_without_entry / ".semaphore" / "semaphore"

    def acquire(
        self,
        mode: str | None = None,
        *,
        clone: bool = False,
        creme: Path | None = None,
        extra: dict[str, str] | None = None,
        what: str = "the control's elaboration",
        estimate: str | None = None,
        contention: str | None = None,
    ) -> tuple[int, str]:
        """Source the shell half in `mode` and take one hold through it.

        Returns the acquire status and everything the shell wrote, stdout and
        stderr together, the way an operator reading a gate's transcript sees
        it.
        """

        scripts = (self.clone if clone else self.worktree) / "scripts"
        arguments = f' "{what}"{(" " + estimate) if estimate is not None else ""}'
        if contention is not None:
            arguments += f" {contention}"
        script = (
            'set -u\n'
            f'. "{scripts / "gate-semaphore.sh"}"\n'
            f"gate_semaphore_acquire{arguments}\n"
            'gs_status=$?\n'
            'gate_semaphore_release\n'
            'exit $gs_status\n'
        )
        with declared_coordination(mode):
            environment = dict(os.environ, CREME_ROOT=str(self.creme if creme is None else creme))
            environment.update(extra or {})
            done = subprocess.run(
                ["bash", "-c", script],
                capture_output=True, text=True, env=environment, cwd=str(self.root),
            )
        return done.returncode, done.stdout + done.stderr

    def requests(self) -> list[str]:
        return [line for line in self.coordination.calls_made()
                if line.startswith("adaptive-acquire")]

    def releases(self) -> list[str]:
        return [line for line in self.coordination.calls_made()
                if line.startswith("release")]


@contextmanager
def shell_admission():
    directory = Path(tempfile.mkdtemp(prefix="gate-semaphore-shell-control-"))
    coordination = Path(tempfile.mkdtemp(prefix="gate-semaphore-shell-host-"))
    try:
        yield ShellAdmission(directory, Coordination(coordination))
    finally:
        shutil.rmtree(directory, ignore_errors=True)
        shutil.rmtree(coordination, ignore_errors=True)


def control_shell_coordination_asks_the_host_and_fails_closed() -> None:
    """The coordinated mode, in the half twenty wrappers actually source.

    Three things are load-bearing and none of them was falsifiable before this
    control existed.  A refusal must reach the caller as a non-zero status and
    a `REFUSED` verdict -- the gate did not fail, it did not run -- and must
    leave no release behind, because nothing was taken.  An admission must ask
    once, naming the goal and a peak estimate, and must give the hold back.  And
    `ALREADY_HELD` must be read as inheritance: asked for, proceeded under,
    never released, because the hold belongs to the caller.
    """

    with shell_admission() as s:
        s.coordination.answer("refuse")
        status, output = s.acquire()
        require(status != 0, "a refused host must stop the gate")
        require("REFUSED — " in output, "the refusal must be reported as a verdict, not swallowed")
        require(ShellAdmission.GOAL in output, "the refusal must name the goal it was refused for")
        require(
            "nothing was elaborated and nothing was written" in output,
            "the refusal must say that the gate did not run rather than failed",
        )
        require(s.releases() == [], "a refused request holds nothing, so it releases nothing")

        s.coordination.forget()
        s.coordination.answer("admit")
        status, output = s.acquire()
        require(status == 0, "an admitted host lets the gate elaborate")
        requests = s.requests()
        require(len(requests) == 1, "the gate must ask for admission exactly once")
        require(
            ShellAdmission.GOAL in requests[0] and "--memory-gib" in requests[0],
            "the request must name this goal and a peak estimate",
        )
        require(len(s.releases()) == 1, "an admitted hold must be released when the gate exits")
        require("REFUSED" not in output, "an admitted gate must report no refusal")

        s.coordination.forget()
        s.coordination.answer("already-held")
        status, output = s.acquire()
        require(status == 0, "an inherited hold lets the gate elaborate")
        require(len(s.requests()) == 1, "an inherited hold is still asked for, not assumed")
        require(
            s.releases() == [],
            "a hold this process did not take must never be released by it",
        )
        require("REFUSED" not in output, "ALREADY_HELD is inheritance, not a refusal")


def control_shell_coordination_off_never_asks_the_host_and_says_so() -> None:
    """`BLANC_GATE_SEMAPHORE=off` in the shell half.

    Same promise as the Python driver's, and the same way of stating it: the
    host is made to answer `refuse`, so that a mode which merely ignored the
    answer would be indistinguishable from one that never asked -- and only
    the second is what `off` means.  A `REFUSED` reaching the caller here would
    be a refusal nobody requested.

    And it says so out loud, once, in a `NOTE` no gate's verdict pattern can
    match, because an uncoordinated elaboration nobody can see is the failure
    this file exists to end.
    """

    with shell_admission() as s:
        s.coordination.answer("refuse")
        status, output = s.acquire("off")
        require(status == 0, "off must let the gate run without consulting the host")
        require(s.coordination.calls_made() == [], "off must not spawn the entry point at all")
        require("REFUSED" not in output, "off must not let in a refusal it never asked for")
        notes = [line for line in output.splitlines() if "BLANC_GATE_SEMAPHORE=off" in line]
        require(len(notes) == 1, "off must announce itself exactly once")
        require(
            notes[0].startswith("NOTE — ") and ShellAdmission.GOAL in notes[0],
            "the announcement must name this goal and be shaped as a note, not a verdict",
        )


def control_shell_coordination_inherited_borrows_and_releases_nothing() -> None:
    """`BLANC_GATE_SEMAPHORE=inherited` in the shell half.

    The caller states that it already holds the host for this work.  Asking
    again would charge one unit twice; releasing at the end would hand the host
    away underneath its owner.  So the mode asks nothing and releases nothing,
    and a host that would refuse proves the first half: the refusal must never
    arrive.
    """

    with shell_admission() as s:
        s.coordination.answer("refuse")
        status, output = s.acquire("inherited")
        require(status == 0, "an inherited hold must let the gate run")
        require(s.coordination.calls_made() == [], "inherited must not ask for a second hold")
        require("REFUSED" not in output, "inherited must not let in a refusal it never asked for")
        require(
            "BLANC_GATE_SEMAPHORE=off" not in output
            and "no host coordination at" not in output,
            "inherited is neither the off branch nor the absent-entry-point branch",
        )


def control_shell_absent_coordination_entry_point_announces_once_and_runs() -> None:
    """Blanc is standalone, and that is a promise about clones, not a setting.

    Where there is no Creme checkout there is nothing to ask, so the gate runs
    rather than refusing -- but not quietly.  One announcement, naming the path
    that was looked for, so that an uncoordinated elaboration is visible in the
    transcript of the run that performed it.
    """

    with shell_admission() as s:
        require(not s.absent_entry.exists(), "the control needs an entry point that is absent")
        s.coordination.answer("refuse")
        status, output = s.acquire(creme=s.creme_without_entry)
        require(status == 0, "an absent entry point must not stop the gate")
        require(
            s.coordination.calls_made() == [],
            "an absent entry point cannot have been asked anything",
        )
        require("REFUSED" not in output, "a missing Creme checkout is not a refusal")
        notes = [line for line in output.splitlines() if "no host coordination at" in line]
        require(len(notes) == 1, "the absence must be announced exactly once")
        require(
            notes[0].startswith("NOTE — ") and str(s.absent_entry) in notes[0],
            "the announcement must name the path that was looked for",
        )


def control_shell_admission_request_states_the_goal_the_estimate_and_the_wait() -> None:
    """What the shell half puts in the request, which is what the host sees.

    The label is not cosmetic: the semaphore attributes a `lake`/`lean` process
    to a hold by asking whether it is working inside that goal's worktrees, so
    a hold named for anything else is one whose own work cannot be recognised
    as its own.  It is derived from the worktree, stated by
    `BLANC_GATE_SEMAPHORE_LABEL`, and falls back to `blanc-gates` in a plain
    clone.  The estimate is the documented narrow default unless the caller
    passes a larger one or the environment overrides it, and `--wait` appears
    only when a caller asked to queue.
    """

    with shell_admission() as s:
        s.coordination.answer("admit")
        s.acquire()
        request = s.requests()[0]
        require(
            f"adaptive-acquire {ShellAdmission.GOAL} " in request,
            "a gate in a goal worktree must acquire under that goal's name",
        )
        require("--memory-gib 4" in request, "the default estimate is the documented narrow one")
        require("--contention tolerant" in request, "the default admission class is stated explicitly")
        require("--wait" not in request, "an unset wait must not queue")

        s.coordination.forget()
        s.acquire(clone=True)
        require(
            "adaptive-acquire blanc-gates " in s.requests()[0],
            "a gate outside a goal worktree falls back to blanc-gates",
        )

        s.coordination.forget()
        s.acquire(extra={"BLANC_GATE_SEMAPHORE_LABEL": "somebody-elses-goal"})
        require(
            "adaptive-acquire somebody-elses-goal " in s.requests()[0],
            "an explicit label must be what is acquired under",
        )

        s.coordination.forget()
        s.acquire(estimate="9", extra={"BLANC_GATE_SEMAPHORE_WAIT": "600"})
        request = s.requests()[0]
        require("--memory-gib 9" in request, "a caller that builds states its own estimate")
        require("--wait 600" in request, "a caller that asked to queue must queue")

        s.coordination.forget()
        s.acquire(estimate="9", extra={"BLANC_GATE_SEMAPHORE_MEMORY_GIB": "2"})
        require(
            "--memory-gib 2" in s.requests()[0],
            "the environment override must reach the request",
        )


def control_shell_authoritative_admission_requires_a_hard_inheritance() -> None:
    """An automatic timing inheritance must prove the caller's hard hold.

    `adaptive-acquire --contention exclusive` either creates the hard hold or,
    for a same-label owner, returns the entry point's explicit hard-hold answer.
    A soft or unclassified `ALREADY_HELD` response cannot establish timing
    isolation, so it is a refusal.  The explicit `inherited` mode remains the
    route for an enclosing caller that has already made the required admission.
    """

    with shell_admission() as s:
        s.coordination.answer("admit")
        status, _output = s.acquire(estimate="8", contention="exclusive")
        require(status == 0, "an exclusive request must be admitted when the host admits it")
        require(
            "--contention exclusive" in s.requests()[0],
            "a timing-authoritative caller must request exclusive admission",
        )
        require(len(s.releases()) == 1, "an exclusive hold this gate took must be released")

        for answer in ("already-held", "already-held-soft"):
            s.coordination.forget()
            s.coordination.answer(answer)
            status, output = s.acquire(estimate="8", contention="exclusive")
            require(status != 0, f"{answer} must not authorize a timing run")
            require("REFUSED — " in output, "insufficient inheritance must be a refusal verdict")
            require(s.releases() == [], "an unproved inherited hold must not be released")

        s.coordination.forget()
        s.coordination.answer("already-held-hard")
        status, output = s.acquire(estimate="8", contention="exclusive")
        require(status == 0, "the entry point's hard-hold answer may cover a timing run")
        require("REFUSED" not in output, "a proved hard inheritance is not a refusal")
        require(s.releases() == [], "a caller-owned hard hold remains caller-owned")

        s.coordination.forget()
        s.coordination.answer("refuse")
        status, output = s.acquire("inherited", estimate="8", contention="exclusive")
        require(status == 0, "an explicitly declared enclosing admission remains supported")
        require(s.coordination.calls_made() == [], "explicit inheritance must not acquire again")
        require("REFUSED" not in output, "explicit inheritance must not expose a host refusal")


# --- production wrapper lifetime --------------------------------------------

BEACON_CURRENT_MAINNET_WRAPPER = (
    Path(__file__).resolve().parent / "check-beacon-deposit-current-mainnet.sh"
)


def beacon_current_mainnet_wrapper_source() -> str:
    """The production wrapper, read through a seam for the biting control."""

    return BEACON_CURRENT_MAINNET_WRAPPER.read_text(encoding="utf-8")


def run_beacon_current_mainnet_lifecycle(child_exit: int) -> tuple[int, list[str]]:
    """Run the production shell path against harmless admission and children.

    The disposable `lake` and isolated-target Python stand-ins never elaborate
    or inspect a target.  They append their completion to the admission trace,
    so the control can prove that the shell releases only after the final child
    returns while preserving that child's status.
    """

    directory = Path(tempfile.mkdtemp(prefix="beacon-mainnet-lifecycle-"))
    coordination_directory = Path(tempfile.mkdtemp(prefix="beacon-mainnet-host-"))
    try:
        coordination = Coordination(coordination_directory)
        repository = directory / "blanc" / ".worktrees" / "blanc-mainnet-lifecycle-control"
        scripts = repository / "scripts"
        scripts.mkdir(parents=True)
        (scripts / "gate-semaphore.sh").write_text(
            gate_semaphore_shell_source(), encoding="utf-8"
        )
        wrapper = scripts / "check-beacon-deposit-current-mainnet.sh"
        wrapper.write_text(beacon_current_mainnet_wrapper_source(), encoding="utf-8")
        wrapper.chmod(0o755)
        # The wrapper's mandatory static preflight is pure Python.  Its real
        # semantic body is outside this lifetime control, so a harmless child
        # lets the production shell advance to the admitted path.
        (scripts / "gen-beacon-deposit-current-mainnet.py").write_text(
            "raise SystemExit(0)\n", encoding="utf-8"
        )

        fake_bin = directory / "bin"
        fake_bin.mkdir()
        (fake_bin / "lake").write_text(
            "#!/bin/sh\n"
            f'printf "%s\\n" "lean-child" >> "{coordination.calls}"\n',
            encoding="utf-8",
        )
        (fake_bin / "lake").chmod(0o755)

        target = directory / "target"
        target_python = target / ".venv" / "bin" / "python"
        target_python.parent.mkdir(parents=True)
        child_status = directory / "child-status"
        child_status.write_text(f"{child_exit}\n", encoding="utf-8")
        target_python.write_text(
            "#!/bin/sh\n"
            f'printf "%s\\n" "generator-child" >> "{coordination.calls}"\n'
            f'exit "$(cat "{child_status}")"\n',
            encoding="utf-8",
        )
        target_python.chmod(0o755)

        creme = directory / "creme"
        entry = creme / ".semaphore" / "semaphore"
        entry.parent.mkdir(parents=True)
        entry.write_text(coordination.entry.read_text(encoding="utf-8"), encoding="utf-8")
        entry.chmod(0o755)
        with declared_coordination(None):
            completed = subprocess.run(
                ["bash", str(wrapper)],
                cwd=repository,
                capture_output=True,
                text=True,
                env={
                    **os.environ,
                    "CREME_ROOT": str(creme),
                    "JAUNE_T8N_TARGET": str(target),
                    "PATH": f"{fake_bin}{os.pathsep}{os.environ.get('PATH', '')}",
                },
            )
        return completed.returncode, coordination.calls_made()
    finally:
        shutil.rmtree(directory, ignore_errors=True)
        shutil.rmtree(coordination_directory, ignore_errors=True)


def control_beacon_current_mainnet_releases_after_its_final_child() -> None:
    """The production wrapper keeps its EXIT trap past the generator child."""

    for child_exit in (0, 17):
        status, trace = run_beacon_current_mainnet_lifecycle(child_exit)
        require(status == child_exit, "the final generator exit status must reach the gate caller")
        require(
            trace == [
                "adaptive-acquire blanc-mainnet-lifecycle-control --note Blanc gate: the BeaconDeposit current-mainnet artifacts --memory-gib 4 --contention tolerant",
                "lean-child",
                "generator-child",
                "release blanc-mainnet-lifecycle-control",
            ],
            "the real wrapper must release exactly once, after its harmless final child",
        )


def control_build_certificate_refuses_every_identity_and_trace_uncertainty() -> None:
    with scratch() as s:
        package = prepare_build_state(s)
        s.write("docs.md", "one\n")
        tools = {"identity": "one"}

        def fake_tools(root: Path, names: list[str]):
            detail = {name: tools["identity"] for name in names}
            return gc.digest_of(detail), detail

        with patched(gc, "component_tools", fake_tools):
            gc.write_build_certificate(s.root)
            require(gc.build_certificate_status(s.root)[0], "fresh certificate should match")

            s.write("docs.md", "two\n")
            require(
                gc.build_certificate_status(s.root)[0],
                "documentation movement must not invalidate the build",
            )

            s.write("Blanc/A.lean", "theorem a : True := by trivial\n")
            require(
                not gc.build_certificate_status(s.root)[0],
                "direct Lean source movement must invalidate the certificate",
            )
            s.write("Blanc/A.lean", "theorem a : True := trivial\n")
            require(gc.build_certificate_status(s.root)[0], "restoring source should restore identity")

            tools["identity"] = "two"
            require(
                not gc.build_certificate_status(s.root)[0],
                "toolchain movement must invalidate the certificate",
            )
            tools["identity"] = "one"

            runner = s.root / ".lake/packages/jaune/.lake/build/bin/jaune"
            runner.write_text("runner-two\n", encoding="utf-8")
            gc.forget_digests()
            require(
                not gc.build_certificate_status(s.root)[0],
                "Jaune runner movement must invalidate the certificate",
            )
            runner.write_text("runner-one\n", encoding="utf-8")
            gc.forget_digests()
            require(gc.build_certificate_status(s.root)[0], "restoring the runner should match")
            runner.unlink()
            gc.forget_digests()
            require(
                not gc.build_certificate_status(s.root)[0],
                "a missing Jaune runner must invalidate the certificate",
            )
            runner.parent.mkdir(parents=True, exist_ok=True)
            runner.write_text("runner-one\n", encoding="utf-8")
            gc.forget_digests()
            require(gc.build_certificate_status(s.root)[0], "restoring the runner should match")

            s.write("lakefile.lean", "import Lake\nopen Lake DSL\npackage blanc where\n")
            require(
                not gc.build_certificate_status(s.root)[0],
                "Lake configuration movement must invalidate the certificate",
            )
            s.write("lakefile.lean", "import Lake\nopen Lake DSL\npackage blanc\n")

            (package / "Jaune.lean").write_text("def jaune := 2\n", encoding="utf-8")
            subprocess.run(["git", "add", "Jaune.lean"], cwd=package, check=True)
            subprocess.run(
                ["git", "-c", "commit.gpgsign=false", "commit", "-q", "-m", "move"],
                cwd=package,
                check=True,
            )
            require(
                not gc.build_certificate_status(s.root)[0],
                "an installed dependency moving off its exact pin must invalidate",
            )
            subprocess.run(["git", "reset", "--hard", "HEAD^", "-q"], cwd=package, check=True)
            require(gc.build_certificate_status(s.root)[0], "restoring the dependency pin should match")

            s.trace("Blanc.A", "moved-dep-hash")
            require(
                not gc.build_certificate_status(s.root)[0],
                "transitive trace movement must invalidate the certificate",
            )
            s.trace("Blanc.A", "a-dep-hash")
            (s.root / ".lake/build/lib/lean/Blanc/A.trace").unlink()
            require(
                not gc.build_certificate_status(s.root)[0],
                "a missing trace must invalidate the certificate",
            )


def control_corrupt_build_certificate_forces_authoritative_build() -> None:
    with scratch() as s:
        prepare_build_state(s)
        with patched(
            gc,
            "component_tools",
            lambda root, tools: (gc.digest_of({"tool": "one"}), {"tool": "one"}),
        ):
            gc.write_build_certificate(s.root)
            gc.build_certificate_path(s.root).write_text("{broken", encoding="utf-8")
            current, reason, _ = gc.build_certificate_status(s.root)
            require(not current, "a corrupt certificate must never be credited")
            require("corrupt" in reason, "the refusal should identify certificate corruption")


def control_material_output_reuses_proof_only_and_refuses_every_material_uncertainty() -> None:
    with scratch() as s:
        s.write("material.bin", "A")
        s.write("scenario.json", "one\n")
        s.write("generated.json", "A\n")
        s.write("Proof.lean", "theorem p : True := trivial\n")
        material = s.write(
            "scripts/material.py",
            "from pathlib import Path\n"
            "print(Path('material.bin').read_text(), end='')\n",
        )
        command = s.passing_gate("expensive.sh", "expensive-ran.txt")
        inputs = {
            "files": ["scenario.json", "generated.json"],
            "material_output": [{
                "id": "compiled-bytes",
                "command": [sys.executable, "scripts/material.py"],
                "authority": ["scripts/material.py"],
            }],
        }
        s.registry([simple_gate("expensive", [command], inputs, "^OK — expensive.sh: ")])
        require(s.run() == 0, "the first material certificate should execute the gate")

        s.write("Proof.lean", "theorem p : True := by trivial\n")
        require(
            s.disposition("expensive") == "reused",
            "proof-only movement with identical material output should reuse",
        )

        s.write("material.bin", "B")
        require(s.disposition("expensive") == "fresh", "one output byte must invalidate")
        s.write("material.bin", "A")
        require(s.disposition("expensive") == "reused", "restoring output should restore identity")

        s.write("scenario.json", "two\n")
        require(s.disposition("expensive") == "fresh", "scenario/oracle movement must invalidate")
        s.write("scenario.json", "one\n")
        s.write("generated.json", "stale\n")
        require(s.disposition("expensive") == "fresh", "stale generated evidence must invalidate")
        s.write("generated.json", "A\n")

        material.write_text(
            "# lying output producer\nprint('A', end='')\n", encoding="utf-8"
        )
        require(
            s.disposition("expensive") == "fresh",
            "a changed producer that lies with the same output must invalidate through authority",
        )

        material.write_text("raise SystemExit(3)\n", encoding="utf-8")
        require(
            s.disposition("expensive") == "fresh",
            "a failed certificate derivation must conservatively execute",
        )


def control_worktree_seed_previews_then_publishes_isolated_exact_state() -> None:
    with seed_pair() as (_s, source, target):
        (source / ".lake/gate-report.md").write_text("source admission\n", encoding="utf-8")

        def copy(_creme: Path, origin: Path, destination: Path, execute: bool):
            if execute:
                shutil.copytree(origin, destination, symlinks=True)
            return {
                "status": "OK" if execute else "PREVIEW",
                "detail": "control copy",
                "data": {"method": "copytree"},
            }

        with patched(ws, "load_gate_cache", lambda _directory: gc):
            preview = ws.seed(source, target, Path("/unused"), False, copier=copy)
            require(preview["status"] == "PREVIEW", "the first operation must be a preview")
            require(not (target / ".lake").exists(), "preview must not create target state")
            result = ws.seed(source, target, Path("/unused"), True, copier=copy)
        require(result["status"] == "OK", "exact staged state should publish")
        require((target / ".lake/blanc-build-certificate.json").is_file(),
                "the exact build certificate must be copied")
        require((target / ".lake/blanc-seed-receipt.json").is_file(),
                "the target must record copy provenance")
        require((target / ".lake/baseline-elab.txt").is_file(),
                "the staged Lake state must retain the validated baseline")
        require((target / "scripts/baseline-elab.txt").is_file(),
                "the gate's established host-local baseline path must be populated")
        require(result["elab_baseline"]["rows"] == 2,
                "the receipt must identify the exact baseline population")
        require(not (target / ".lake/gate-report.md").exists(),
                "source candidate admissions must not be copied")
        require(not (target / ".lake").is_symlink(),
                "worktrees must never share a live writable .lake")


def control_worktree_seed_refuses_missing_stale_or_different_state() -> None:
    with seed_pair() as (_s, source, target):
        (source / "scripts/baseline-elab.txt").unlink()
        with patched(ws, "load_gate_cache", lambda _directory: gc):
            try:
                ws.seed(source, target, Path("/unused"), False)
            except ws.SeedRefusal as error:
                require("baseline" in str(error), "missing baseline needs an exact refusal")
            else:
                raise ControlFailure("missing elaboration baseline must refuse")

    with seed_pair() as (_s, source, target):
        gc.build_certificate_path(source).unlink()
        with patched(ws, "load_gate_cache", lambda _directory: gc):
            try:
                ws.seed(source, target, Path("/unused"), False)
            except ws.SeedRefusal:
                pass
            else:
                raise ControlFailure("missing source state must refuse")

    with seed_pair() as (s, source, target):
        s.write("Blanc/New.lean", "theorem n : True := trivial\n")
        s.git("add", "Blanc/New.lean")
        s.git("-c", "commit.gpgsign=false", "commit", "-q", "-m", "move-source")
        with patched(ws, "load_gate_cache", lambda _directory: gc):
            try:
                ws.seed(source, target, Path("/unused"), False)
            except ws.SeedRefusal as error:
                require("same source base" in str(error), "different bases need an exact refusal")
            else:
                raise ControlFailure("different source bases must refuse")

    with seed_pair() as (s, source, target):
        s.write("lakefile.lean", "import Lake\nopen Lake DSL\npackage changed\n")
        s.git("add", "lakefile.lean")
        s.git("-c", "commit.gpgsign=false", "commit", "-q", "-m", "move-config")
        head = s.git("rev-parse", "HEAD")
        subprocess.run(["git", "reset", "--hard", head], cwd=target, check=True,
                       capture_output=True)
        with patched(ws, "load_gate_cache", lambda _directory: gc):
            try:
                ws.seed(source, target, Path("/unused"), False)
            except ws.SeedRefusal as error:
                require("not certifiable" in str(error), "stale config must fail the certificate")
            else:
                raise ControlFailure("stale configuration must refuse")


def control_worktree_seed_never_publishes_partial_or_racing_state() -> None:
    with seed_pair() as (_s, source, target):
        def partial(_creme: Path, _origin: Path, destination: Path, _execute: bool):
            destination.mkdir()
            (destination / "partial").write_text("partial", encoding="utf-8")
            return {"status": "ERROR", "detail": "unsupported", "data": {}}

        with patched(ws, "load_gate_cache", lambda _directory: gc):
            try:
                ws.seed(source, target, Path("/unused"), True, copier=partial)
            except ws.SeedRefusal:
                pass
            else:
                raise ControlFailure("an unsupported/partial copy must refuse")
        require(not (target / ".lake").exists(), "partial state must never be published")

    with seed_pair() as (_s, source, target):
        def racing(_creme: Path, origin: Path, destination: Path, _execute: bool):
            shutil.copytree(origin, destination, symlinks=True)
            (source / "lean-toolchain").write_text("moved-during-copy\n", encoding="utf-8")
            return {"status": "OK", "detail": "racing copy", "data": {"method": "copytree"}}

        with patched(ws, "load_gate_cache", lambda _directory: gc):
            try:
                ws.seed(source, target, Path("/unused"), True, copier=racing)
            except ws.SeedRefusal as error:
                require("moved during copy" in str(error), "the race should be diagnosed")
            else:
                raise ControlFailure("source movement during copy must refuse")
        require(not (target / ".lake").exists(), "racing state must never be published")

    with seed_pair() as (_s, source, target):
        def build_racing(_creme: Path, origin: Path, destination: Path, _execute: bool):
            shutil.copytree(origin, destination, symlinks=True)
            gc.atomic_json(
                source / ".lake/build/lib/lean/Blanc/A.trace",
                {"depHash": "moved-build-state"},
            )
            return {"status": "OK", "detail": "build race", "data": {"method": "copytree"}}

        with patched(ws, "load_gate_cache", lambda _directory: gc):
            try:
                ws.seed(source, target, Path("/unused"), True, copier=build_racing)
            except ws.SeedRefusal as error:
                require("build state moved during copy" in str(error),
                        "a trace race should be diagnosed")
            else:
                raise ControlFailure("source build-state movement during copy must refuse")
        require(not (target / ".lake").exists(),
                "racing build state must never be published")


def control_dependency_evidence_is_consumed_without_rerunning_its_body() -> None:
    with scratch() as s:
        s.write("dep.txt", "one\n")
        s.write("consumer.txt", "one\n")
        dep = s.passing_gate("dep.sh", "dep-ran.txt")
        consumer = s.passing_gate("consumer.sh", "consumer-ran.txt")
        dependent = simple_gate(
            "consumer", [consumer], {"files": ["consumer.txt"]},
            "^OK — consumer.sh: ", order=2,
        )
        dependent["depends_on"] = ["dep"]
        s.registry([
            simple_gate("dep", [dep], {"files": ["dep.txt"]}, "^OK — dep.sh: "),
            dependent,
        ])
        require(s.run() == 0, "the complete conjunction should start green")
        s.write("consumer.txt", "two\n")
        require(s.run() == 0, "a fresh consumer may consume exact reused prerequisite evidence")
        require(s.ran("dep-ran.txt") == 1, "the prerequisite body must start only once")
        require(s.ran("consumer-ran.txt") == 2, "the changed consumer must execute")


def control_missing_or_failing_dependency_never_yields_a_green_consumer() -> None:
    with scratch() as s:
        dep = s.gate("dep.sh", "#!/bin/sh\nexit 1\n")
        consumer = s.passing_gate("consumer.sh", "consumer-ran.txt")
        dependent = simple_gate(
            "consumer", [consumer], {"files": ["scripts/consumer.sh"]},
            "^OK — consumer.sh: ", order=2,
        )
        dependent["depends_on"] = ["dep"]
        s.registry([
            simple_gate("dep", [dep], {"files": ["scripts/dep.sh"]}, "^OK — dep.sh: "),
            dependent,
        ])
        require(s.run() != 0, "a failed prerequisite must redden the conjunction")
        require(s.ran("consumer-ran.txt") == 0, "a blocked consumer body must not start")

        broken = copy.deepcopy(dependent)
        broken["depends_on"] = ["absent"]
        s.registry([broken])
        try:
            s.load()
        except gc.GateCacheError:
            pass
        else:
            raise ControlFailure("a dependency removed from the registry must be refused")


# --- controls: what may enter the cache -------------------------------------


def control_failed_run_is_never_cached() -> None:
    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\nexit 1\n')
        s.registry([simple_gate("g", ["scripts/g.sh"], {"files": ["scripts/x.txt"]},
                                "^OK — g.sh: ")])
        require(s.run() != 0, "a failing gate must make the run red")
        cache, _ = s.cache()
        require(not cache["gates"].get("g"), "a failed run must not seed a record")
        require(s.disposition("g") == "fresh", "and must not be reusable afterwards")


def control_missing_summary_is_never_cached() -> None:
    """Exit zero is not a pass.

    A gate killed mid-stream, or one whose harness stopped printing its
    terminal line, exits zero often enough that the summary is the real
    evidence.
    """

    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        s.gate("g.sh", '#!/bin/sh\necho "some progress output"\n')
        s.registry([simple_gate("g", ["scripts/g.sh"], {"files": ["scripts/x.txt"]},
                                "^OK — g.sh: ")])
        require(s.run() != 0, "a missing terminal summary must make the run red")
        cache, _ = s.cache()
        require(not cache["gates"].get("g"), "and must not seed a record")


def control_duplicated_summary_is_never_cached() -> None:
    """Two interleaved runs writing one report is the failure `gate-lock.sh`
    exists for; a doubled summary must not be read as a pass."""

    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate("g", ["scripts/g.sh"], {"files": ["scripts/x.txt"]},
                                "^OK — g.sh: ")])
        require(s.run() != 0, "a doubled terminal summary must make the run red")
        cache, _ = s.cache()
        require(not cache["gates"].get("g"), "and must not seed a record")


def control_drift_during_the_run_is_not_cached() -> None:
    """A verdict is credited to the inputs the gate actually saw.

    A gate that edits a declared input while running would otherwise attach its
    verdict to a tree that never produced it.
    """

    with scratch() as s:
        s.write("Blanc/A.lean", "one\n")
        s.gate("g.sh",
               '#!/bin/sh\nprintf "two\\n" > "$(dirname "$0")/../Blanc/A.lean"\n'
               'echo "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        require(s.run() == 0, "the gate itself passed")
        cache, _ = s.cache()
        require(
            not cache["gates"].get("g"),
            "a verdict produced while its declared inputs moved must not be cached",
        )


def control_drift_on_a_reused_row_reddens_the_run() -> None:
    with scratch() as s:
        s.write("Blanc/A.lean", "one\n")
        quiet = s.gate("q.sh", '#!/bin/sh\necho "OK — q.sh: 1/1 fine"\n')
        noisy = s.gate("n.sh",
                       '#!/bin/sh\nprintf "two\\n" > "$(dirname "$0")/../Blanc/A.lean"\n'
                       'echo "OK — n.sh: 1/1 fine"\n')
        population = {"populations": [{"root": "Blanc", "pattern": "*.lean"}]}
        s.registry([
            simple_gate("q", [quiet], population, "^OK — q.sh: ", order=1),
            {"id": "n", "order": 2, "command": [noisy], "kind": "always-fresh",
             "reason": "this control needs a row that executes on every run",
             "inputs": {},
             "verdict": {"expect_exit": 0, "summary_patterns": ["^OK — n.sh: "]}},
        ])
        require(s.run() == 0, "seed run should be green")
        s.write("Blanc/A.lean", "one\n")
        require(s.run() != 0, "a row reused against a tree that then moved must redden the run")


def control_corrupt_cache_costs_a_run_not_correctness() -> None:
    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate("g", [command], {"files": ["scripts/x.txt"]}, "^OK — g.sh: ")])
        s.run()
        for damage in (
            "}{ not json",
            json.dumps({"schema": 99, "gates": {}, "details": {}}),
            json.dumps({"schema": 1, "gates": "not a table", "details": {}}),
            json.dumps({"schema": 1, "gates": {"g": [{"fingerprint": "x"}]}, "details": {}}),
            json.dumps({"schema": 1, "details": {}}),
        ):
            gc.cache_path(s.root).write_text(damage, encoding="utf-8")
            cache, reason = s.cache()
            require(reason is not None, f"damaged cache must report a reason: {damage[:30]}")
            require(not cache["gates"], "a damaged cache must be treated as empty")
            require(s.disposition("g") == "fresh", "and must force execution")


def control_nonzero_record_poisons_nothing() -> None:
    """A hand-written record claiming a failing verdict is refused wholesale,
    rather than being read for the fields that happen to look right."""

    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate("g", [command], {"files": ["scripts/x.txt"]}, "^OK — g.sh: ")])
        s.run()
        cache = json.loads(gc.cache_path(s.root).read_text(encoding="utf-8"))
        cache["gates"]["g"][0]["verdict"]["exit"] = 1
        gc.cache_path(s.root).write_text(json.dumps(cache), encoding="utf-8")
        _, reason = s.cache()
        require(reason is not None, "a non-passing record must invalidate the cache")
        require(s.disposition("g") == "fresh", "and must force execution")


def control_deleted_cache_forces_everything() -> None:
    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate("g", [command], {"files": ["scripts/x.txt"]}, "^OK — g.sh: ")])
        s.run()
        gc.cache_path(s.root).unlink()
        require(s.disposition("g") == "fresh", "a cold cache must execute everything")
        s.run()
        require(s.ran("ran.txt") == 2, "and the body must really have run")


def control_historical_record_is_recoverable() -> None:
    """Lookup is content-addressed, not "last result".

    Going away and coming back is the ordinary shape of a checkpoint: try a
    change, measure it, revert it.  The evidence for the original tree is still
    evidence for it.
    """

    with scratch() as s:
        s.write("Blanc/A.lean", "state-A\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        s.run()
        s.write("Blanc/A.lean", "state-B\n")
        s.run()
        require(s.ran("ran.txt") == 2, "the excursion executed the body")
        s.write("Blanc/A.lean", "state-A\n")
        require(
            s.disposition("g") == "reused",
            "returning to an earlier tree must recover its own record, not only the newest",
        )
        s.run()
        require(s.ran("ran.txt") == 2, "and must not execute the body again")


def control_eviction_costs_time_only() -> None:
    with scratch() as s:
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        s.write("Blanc/A.lean", "state-0\n")
        s.run()
        for index in range(1, gc.RECORDS_PER_GATE + 3):
            s.write("Blanc/A.lean", f"state-{index}\n")
            s.run()
        cache, _ = s.cache()
        require(
            len(cache["gates"]["g"]) == gc.RECORDS_PER_GATE,
            "the cache must prune to its retention bound",
        )
        s.write("Blanc/A.lean", "state-0\n")
        require(s.disposition("g") == "fresh", "an evicted record must cost a run, not a wrong pass")


def control_pruned_details_do_not_break_explain() -> None:
    with scratch() as s:
        s.write("Blanc/A.lean", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        s.run()
        s.write("Blanc/A.lean", "two\n")
        cache, _ = s.cache()
        rows = s.plan()
        lines = gc.explain_row(cache, rows[0])
        require(any("populations" in line for line in lines),
                "explain must name the component that moved")
        require(any("Blanc/A.lean" in line for line in lines),
                "explain must name the exact path that moved")


# --- controls: registry discipline and concurrency ---------------------------


def control_registry_faults_are_refused() -> None:
    """Every one of these is a registry the runner would only half understand,
    and a half-understood registry cannot be the basis of a skip."""

    cases: list[tuple[str, list[dict[str, Any]]]] = [
        ("unknown input kind",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "cacheable",
           "inputs": {"sources": ["a"]},
           "verdict": {"summary_patterns": ["^OK"]}}]),
        ("unknown gate key",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "cacheable",
           "inputs": {"files": ["a"]}, "cache_me": True,
           "verdict": {"summary_patterns": ["^OK"]}}]),
        ("duplicate id",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "cacheable",
           "inputs": {"files": ["a"]}, "verdict": {"summary_patterns": ["^OK"]}},
          {"id": "g", "order": 2, "command": ["y"], "kind": "cacheable",
           "inputs": {"files": ["a"]}, "verdict": {"summary_patterns": ["^OK"]}}]),
        ("duplicate order",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "cacheable",
           "inputs": {"files": ["a"]}, "verdict": {"summary_patterns": ["^OK"]}},
          {"id": "h", "order": 1, "command": ["y"], "kind": "cacheable",
           "inputs": {"files": ["a"]}, "verdict": {"summary_patterns": ["^OK"]}}]),
        ("duplicate command instance",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "cacheable",
           "inputs": {"files": ["a"]}, "verdict": {"summary_patterns": ["^OK"]}},
          {"id": "h", "order": 2, "command": ["x"], "kind": "cacheable",
           "inputs": {"files": ["a"]}, "verdict": {"summary_patterns": ["^OK"]}}]),
        ("cacheable with no inputs",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "cacheable",
           "inputs": {}, "verdict": {"summary_patterns": ["^OK"]}}]),
        ("cacheable with no summary pattern",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "cacheable",
           "inputs": {"files": ["a"]}, "verdict": {"summary_patterns": []}}]),
        ("unknown kind",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "maybe",
           "inputs": {"files": ["a"]}, "verdict": {"summary_patterns": ["^OK"]}}]),
        ("always-fresh with no reason",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "always-fresh",
           "inputs": {}, "verdict": {"summary_patterns": ["^OK"]}}]),
        ("prerequisite declared cacheable",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "cacheable",
           "prerequisite": True, "inputs": {"files": ["a"]},
           "verdict": {"summary_patterns": ["^OK"]}}]),
        ("summary pattern is not a regex",
         [{"id": "g", "order": 1, "command": ["x"], "kind": "cacheable",
           "inputs": {"files": ["a"]}, "verdict": {"summary_patterns": ["^OK ("]}}]),
    ]
    for label, gates in cases:
        with scratch() as s:
            s.registry(gates)
            try:
                s.load()
            except gc.GateCacheError:
                continue
            raise ControlFailure(f"registry fault accepted: {label}")


def control_registry_schema_version_is_enforced() -> None:
    with scratch() as s:
        gc.atomic_json(gc.registry_path(s.root), {"schema": 99, "gates": []})
        try:
            s.load()
        except gc.GateCacheError:
            return
        raise ControlFailure("a foreign registry schema must be refused")


def control_lock_refuses_a_second_run() -> None:
    """Two selective runs would interleave their cache writes and their report;
    the second is refused with the holder named, not queued."""

    with scratch() as s:
        path = gc.lock_path(s.root)
        require(gc.acquire_lock(path), "the first run should take the lock")
        require(not gc.acquire_lock(path), "a contending run must be refused")
        gc.release_lock(path)
        require(gc.acquire_lock(path), "the lock must be retakeable after release")
        gc.release_lock(path)


def control_kernel_lock_refuses_another_process() -> None:
    """The mutex, not same-process bookkeeping or PID metadata, must bite."""

    with scratch() as s:
        path = gc.lock_path(s.root)
        require(gc.acquire_lock(path), "the parent should take the lock")
        probe = (
            "import fcntl, sys\n"
            "with open(sys.argv[1], 'a+') as handle:\n"
            "    try:\n"
            "        fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)\n"
            "    except BlockingIOError:\n"
            "        raise SystemExit(73)\n"
        )
        blocked = subprocess.run(
            [sys.executable, "-c", probe, str(path / "mutex")], check=False
        )
        require(blocked.returncode == 73,
                f"another process must be refused by the kernel, got {blocked.returncode}")
        gc.release_lock(path)
        free = subprocess.run(
            [sys.executable, "-c", probe, str(path / "mutex")], check=False
        )
        require(free.returncode == 0,
                f"the kernel lock must release with its process, got {free.returncode}")


def control_stale_owner_metadata_does_not_block_an_unlocked_mutex() -> None:
    """PID metadata is diagnostic only, because PIDs are namespace-relative."""

    with scratch() as s:
        path = gc.lock_path(s.root)
        path.mkdir(parents=True)
        (path / "pid").write_text("999999999\n", encoding="utf-8")
        require(gc.acquire_lock(path),
                "stale PID metadata must not override an unlocked kernel mutex")
        require(gc.read_lock_pid(path / "pid") == os.getpid(),
                "the new holder must replace stale diagnostic metadata")
        gc.release_lock(path)
        require(path.is_dir() and (path / "mutex").is_file(),
                "the stable mutex inode must persist after release")
        require(not (path / "pid").exists(),
                "released diagnostic owner metadata must not persist")


def control_same_repository_worktrees_share_records_and_lock() -> None:
    """The Git common directory, not a worktree-local `.lake`, is the trust root."""

    with scratch() as s:
        s.write(".gitignore", "/.worktrees/\n")
        s.write("Blanc/A.lean", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        s.git_init()
        require(s.run() == 0 and s.ran("ran.txt") == 1,
                "the first worktree must earn one record")

        second = s.root / ".worktrees/second"
        s.git("worktree", "add", "-q", "-b", "control-second", str(second), "HEAD")
        require(gc.cache_path(s.root) == gc.cache_path(second),
                "two worktrees of one repository must resolve one shared store")
        require(gc.lock_path(s.root) == gc.lock_path(second),
                "two worktrees of one repository must resolve one shared lock")
        cache, reason = gc.read_cache(gc.cache_path(second))
        require(reason is None, f"the second worktree must read the first record: {reason}")
        rows = gc.plan(second, gc.load_registry(gc.registry_path(second)), cache, fresh=False)
        require(rows[0]["disposition"] == "reused",
                "exact content in a second worktree must reuse")

        require(gc.acquire_lock(gc.lock_path(s.root)), "the first worktree takes the lock")
        require(not gc.acquire_lock(gc.lock_path(second)),
                "the second worktree must contend on the same lock")
        gc.release_lock(gc.lock_path(s.root))


def control_other_physical_clone_never_inherits_shared_records() -> None:
    """Identical content in another clone is outside the local trust domain."""

    with scratch() as s:
        s.write("Blanc/A.lean", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        s.git_init()
        require(s.run() == 0 and s.ran("ran.txt") == 1,
                "the source clone must earn one record")

        container = Path(tempfile.mkdtemp(prefix="gate-cache-other-clone-"))
        clone = container / "clone"
        try:
            subprocess.run(
                ["git", "clone", "-q", str(s.root), str(clone)], check=True
            )
            require(gc.cache_path(s.root) != gc.cache_path(clone),
                    "another physical clone must resolve a different evidence store")
            cache, reason = gc.read_cache(gc.cache_path(clone))
            require(reason == "no prior cache" and not cache["gates"],
                    "another clone must start without the source clone's evidence")
            rows = gc.plan(
                clone, gc.load_registry(gc.registry_path(clone)), cache, fresh=False
            )
            require(rows[0]["disposition"] == "fresh",
                    "identical content in another clone must execute fresh")
        finally:
            shutil.rmtree(container, ignore_errors=True)


def control_foreign_host_store_never_yields_reuse() -> None:
    with scratch() as s:
        cache = gc.empty_cache()
        cache["host"] = "foreign-host"
        gc.atomic_json(gc.cache_path(s.root), cache)
        loaded, reason = s.cache()
        require(reason == "cache belongs to a different host identity",
                "a foreign host store must be refused explicitly")
        require(not loaded["gates"], "a foreign host store must become empty work")


def control_dirty_worktree_does_not_seed_shared_evidence() -> None:
    with scratch() as s:
        s.write("Blanc/A.lean", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command], {"populations": [{"root": "Blanc", "pattern": "*.lean"}]},
            "^OK — g.sh: ")])
        s.git_init()
        s.write("Blanc/A.lean", "dirty\n")
        require(s.run() == 0, "a dirty candidate may execute safely")
        cache, reason = s.cache()
        require(reason is None, "a structurally valid empty shared store is still readable")
        require(not cache["gates"], "a dirty candidate must not seed shared evidence")
        require("dirty worktree" in s.output,
                "the manifest path must explain why admission was refused")


def control_atomic_write_leaves_no_debris() -> None:
    with scratch() as s:
        target = s.root / ".lake/atomic.json"
        gc.atomic_json(target, {"a": 1})
        original = json.dumps
        json.dumps = lambda *a, **k: (_ for _ in ()).throw(RuntimeError("boom"))
        try:
            gc.atomic_json(target, {"b": 2})
        except RuntimeError:
            pass
        finally:
            json.dumps = original
        leftovers = [p.name for p in target.parent.iterdir() if p.name.startswith(".atomic")]
        require(not leftovers, f"a failed atomic write left debris: {leftovers}")
        require(json.loads(target.read_text()) == {"a": 1},
                "a failed atomic write must leave the previous file intact")


def control_there_is_no_force() -> None:
    """`--force` is the catalogue's named prohibition, and the reason is that a
    bypass hollows a gate out entirely.  `--fresh` adds work; nothing removes
    it."""

    wrapper = (Path(__file__).resolve().parent / "check-gates.sh").read_text(encoding="utf-8")
    require("there is no --force" in wrapper, "the wrapper must refuse --force explicitly")
    engine = (Path(__file__).resolve().parent / "gate-cache.py").read_text(encoding="utf-8")
    require('"--force"' not in engine, "the engine must not accept a --force option")
    result = subprocess.run(
        [str(Path(__file__).resolve().parent / "check-gates.sh"), "--force"],
        capture_output=True, text=True, check=False,
    )
    require(result.returncode == 2, "--force must exit 2")


def control_fresh_mode_adds_work_and_refreshes() -> None:
    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate("g", [command], {"files": ["scripts/x.txt"]}, "^OK — g.sh: ")])
        s.run()
        require(s.ran("ran.txt") == 1, "seed run executed once")
        require(s.run(fresh=True) == 0, "fresh mode should be green")
        require(s.ran("ran.txt") == 2, "fresh mode must execute even a valid row")
        require(s.disposition("g") == "reused", "and must refresh the record it executed")


def control_always_fresh_rows_never_reuse() -> None:
    with scratch() as s:
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([{
            "id": "g", "order": 1, "command": [command], "kind": "always-fresh",
            "reason": "declared always fresh for this control",
            "inputs": {}, "verdict": {"expect_exit": 0, "summary_patterns": ["^OK — g.sh: "]},
        }])
        s.run()
        s.run()
        require(s.ran("ran.txt") == 2, "an always-fresh row must execute every time")


def control_report_and_manifest_are_self_contained() -> None:
    with scratch() as s:
        s.write("scripts/x.txt", "one\n")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate("g", [command], {"files": ["scripts/x.txt"]}, "^OK — g.sh: ")])
        s.run()
        s.run()
        manifest = json.loads(gc.manifest_path(s.root).read_text(encoding="utf-8"))
        row = manifest["rows"][0]
        require(row["disposition"] == "reused", "the manifest must record the disposition")
        require(row["evidence_from"]["commit"] is not None,
                "a reused row must name the execution it is credited from")
        require(row["verdict"]["summary"], "a reused row must retain the original verdict")
        report = gc.report_path(s.root).read_text(encoding="utf-8")
        rows = [line for line in report.splitlines() if line.startswith("| 1 |")]
        require(len(rows) == 1, f"expected exactly one row line, got {rows}")
        require("reused successful evidence" in rows[0],
                "a credited row must say so in the report")
        require("executed now" not in rows[0],
                "and must not also claim it executed here")
        require(row["verdict"]["summary"][0] in rows[0],
                "the report must carry the original verdict verbatim")
        require(row["evidence_from"]["recorded_utc"] in rows[0],
                "and must name when that evidence was produced")


# --- controls: the population audit ------------------------------------------


def audit_scratch(s: "Scratch", commands: list[str], gates: list[dict], ci: list[str]) -> int:
    """Wire a scratch repository with a catalogue, a CI workflow and a registry."""

    s.registry(gates, catalogue=False)
    s.catalogue(commands, ci)
    gc.atomic_write(s.root / gc.INVENTORY_RELATIVE, gc.render_inventory(s.root))
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = gc.audit(s.root)
    s.output = out.getvalue() + err.getvalue()
    return code


def audit_gate(identifier: str, command: list[str], order: int) -> dict[str, Any]:
    return simple_gate(identifier, command, {"files": ["scripts/x.txt"]},
                       "^OK — " + identifier, order=order)


def control_audit_accepts_a_reconciled_registry() -> None:
    with scratch() as s:
        code = audit_scratch(
            s,
            ["scripts/check-a.sh", "scripts/check-b.sh --no-build"],
            [audit_gate("a", ["scripts/check-a.sh"], 1),
             audit_gate("b", ["scripts/check-b.sh", "--no-build"], 2)],
            ["scripts/check-a.sh"],
        )
        require(code == 0, f"a reconciled registry must pass:\n{s.output}")


def control_audit_fails_on_catalogue_drift() -> None:
    """Adding, deleting, renaming or re-arguing a catalogued command must fail
    the audit until the registry is reconciled -- otherwise the registry is its
    own authority for what exists, which is no authority at all."""

    base = ["scripts/check-a.sh", "scripts/check-b.sh --no-build"]
    gates = [audit_gate("a", ["scripts/check-a.sh"], 1),
             audit_gate("b", ["scripts/check-b.sh", "--no-build"], 2)]
    cases = {
        "command added to the catalogue":
            (base + ["scripts/check-c.sh"], gates, ["scripts/check-a.sh"]),
        "command removed from the catalogue":
            (base[:1], gates, ["scripts/check-a.sh"]),
        "command renamed in the catalogue":
            (["scripts/check-renamed.sh", base[1]], gates, ["scripts/check-a.sh"]),
        "command arguments changed":
            ([base[0], "scripts/check-b.sh --full"], gates, ["scripts/check-a.sh"]),
        "commands reordered":
            (list(reversed(base)), gates, ["scripts/check-a.sh"]),
        "CI runs an unregistered command":
            (base, gates, ["scripts/check-a.sh", "scripts/check-z.sh"]),
    }
    for label, (commands, entries, ci) in cases.items():
        with scratch() as s:
            code = audit_scratch(s, commands, [dict(g) for g in entries], ci)
            require(code != 0, f"audit accepted {label}:\n{s.output}")


def control_audit_fails_on_a_stale_generated_inventory() -> None:
    with scratch() as s:
        commands = ["scripts/check-a.sh"]
        gates = [audit_gate("a", ["scripts/check-a.sh"], 1)]
        require(audit_scratch(s, commands, gates, []) == 0, "baseline audit should pass")
        (s.root / gc.INVENTORY_RELATIVE).write_text("hand edited\n", encoding="utf-8")
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = gc.audit(s.root)
        require(code != 0, "a hand-edited inventory must fail the audit")


def control_audit_needs_a_catalogue_block() -> None:
    with scratch() as s:
        s.write("scripts/GATES.md", "# Verification gates\n\nno block here\n")
        s.write(".github/workflows/ci.yml", "jobs: {}\n")
        s.registry([audit_gate("a", ["scripts/check-a.sh"], 1)], catalogue=False)
        s.write("scripts/GATES.md", "# Verification gates\n\nno block here\n")
        try:
            gc.audit(s.root)
        except gc.GateCacheError:
            return
        raise ControlFailure("a catalogue with no ordered block must be a fault")


# --- controls: findings from adversarial review ------------------------------


def control_every_import_spelling_is_parsed_or_refused() -> None:
    """Lean's import grammar, not three literal prefixes.

    The first guard here enumerated `import `, `import\t` and `public import`.
    This toolchain's own packages carry 734 `public meta import`, 10
    `meta import` and 64 `import all` lines, so a modifier the enumeration
    missed would have dropped that module's depHash silently -- and silence is
    the whole failure mode.
    """

    understood = (
        "import Blanc.A",
        "public import Blanc.A",
        "private import Blanc.A",
        "meta import Blanc.A",
        "public meta import Blanc.A",
        "import all Blanc.A",
    )
    for line in understood:
        with scratch() as s:
            s.trace("Blanc.A", "aaaa000000000000")
            s.write("scripts/Eval.lean", line + "\nexample : True := trivial\n")
            command = s.passing_gate("g.sh", "ran.txt")
            s.registry([simple_gate(
                "g", [command], {"lean_entries": ["scripts/Eval.lean"]}, "^OK — g.sh: ")])
            s.run()
            require(s.disposition("g") == "reused",
                    f"{line!r} should parse and reuse while unchanged")
            s.trace("Blanc.A", "bbbb111111111111")
            require(s.disposition("g") == "fresh",
                    f"{line!r} must expose Blanc.A to the fingerprint")

    for line in ("import Blanc.A -- trailing", "public meta import Blanc.A;"):
        with scratch() as s:
            s.trace("Blanc.A", "aaaa000000000000")
            s.write("scripts/Eval.lean", line + "\nexample : True := trivial\n")
            command = s.passing_gate("g.sh", "ran.txt")
            s.registry([simple_gate(
                "g", [command], {"lean_entries": ["scripts/Eval.lean"]}, "^OK — g.sh: ")])
            s.run()
            require(s.disposition("g") == "fresh",
                    f"{line!r} is import-like and unparsed, so it must refuse to reuse")


def control_run_refuses_a_registry_that_lost_a_gate() -> None:
    """Deleting a registry entry must not silently shrink the audited set.

    This is the cheapest attack on the whole design: it forges no fingerprint
    and needs no timing.  Without the run-time reconciliation the checkpoint
    simply reports one row fewer, every remaining row green, and the gate that
    vanished is indistinguishable from one that passed.
    """

    with scratch() as s:
        first = s.passing_gate("check-a.sh", "a.txt")
        second = s.passing_gate("check-b.sh", "b.txt")
        s.write("scripts/x.txt", "one\n")
        gates = [simple_gate("a", [first], {"files": ["scripts/x.txt"]},
                             "^OK — check-a.sh: ", order=1),
                 simple_gate("b", [second], {"files": ["scripts/x.txt"]},
                             "^OK — check-b.sh: ", order=2)]
        require(audit_scratch(s, [first, second], gates, []) == 0, "baseline audit")
        require(s.run() == 0, f"seed run should be green:\n{s.output}")
        require(s.ran("a.txt") == 1 and s.ran("b.txt") == 1, "both bodies ran")

        s.registry(gates[:1], catalogue=False)
        require(s.run() != 0, f"a shrunken registry must refuse to run:\n{s.output}")
        require("--audit" in s.output, "and must say how to diagnose it")
        require(s.ran("b.txt") == 1, "the dropped gate's body must not have run either")


def control_named_root_follows_its_override() -> None:
    """A variable that repoints what a gate reads must repoint what is hashed.

    Declaring the variable under `env` catches it *changing*.  It does not help
    at all when the variable is held at a non-default value across two runs: the
    declared paths were the wrong ones both times.
    """

    with scratch() as s, scratch() as elsewhere:
        (elsewhere.root / "venv/bin").mkdir(parents=True)
        (elsewhere.root / "venv/bin/python").write_text("#!/bin/sh\n", encoding="utf-8")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"files": ["@weth10ref/venv/bin/python"]},
            "^OK — g.sh: ")])
        os.environ["WETH10_REFERENCE_DIR"] = str(elsewhere.root)
        try:
            s.run()
            require(s.disposition("g") == "reused", "unchanged redirected tree should reuse")
            (elsewhere.root / "venv/bin/python").write_text("#!/bin/bash\n", encoding="utf-8")
            require(s.disposition("g") == "fresh",
                    "editing the redirected tree must force execution")
        finally:
            os.environ.pop("WETH10_REFERENCE_DIR", None)


def control_environment_value_cannot_imitate_absence() -> None:
    with scratch() as s:
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"], {"env": ["GATE_CACHE_CONTROL"]}, "^OK — g.sh: ")])
        os.environ.pop("GATE_CACHE_CONTROL", None)
        s.run()
        os.environ["GATE_CACHE_CONTROL"] = "<unset>"
        try:
            require(s.disposition("g") == "fresh",
                    "a variable set to the string meaning absence is not absent")
        finally:
            os.environ.pop("GATE_CACHE_CONTROL", None)


def control_symlinked_directory_refuses_rather_than_hides_files() -> None:
    with scratch() as s:
        (s.root / "corpus/real").mkdir(parents=True)
        (s.root / "corpus/real/a.lean").write_text("one\n", encoding="utf-8")
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate(
            "g", ["scripts/g.sh"],
            {"populations": [{"root": "corpus", "pattern": "**/*.lean"}]}, "^OK — g.sh: ")])
        s.run()
        require(s.disposition("g") == "reused", "an ordinary corpus should reuse")
        (s.root / "corpus/link").symlink_to(s.root / "corpus/real")
        require(s.disposition("g") == "fresh",
                "a symlinked directory hides files from the glob, so it must refuse")


def control_non_zero_expected_exit_is_refused() -> None:
    """A gate registered to expect a non-zero exit would store a legal record
    that `read_cache` then treats as corruption, emptying the whole cache on
    every subsequent read -- silent, total loss of reuse with no diagnosis."""

    with scratch() as s:
        s.registry([{
            "id": "g", "order": 1, "command": ["scripts/g.sh"], "kind": "cacheable",
            "inputs": {"files": ["scripts/x.txt"]},
            "verdict": {"expect_exit": 1, "summary_patterns": ["^OK"]},
        }])
        try:
            s.load()
        except gc.GateCacheError:
            return
        raise ControlFailure("a non-zero expected exit must be refused")


def control_traversable_population_refuses_what_a_copy_cannot_read() -> None:
    """The hazard, not the corpus.

    An ordinary added file must not invalidate -- that was the cost of both
    earlier attempts. A dangling symlink or an unreadable file must refuse --
    that is the case both earlier attempts missed, membership included, because
    a dangling symlink is not `is_file()`.
    """

    with scratch() as s:
        (s.root / "tree").mkdir()
        (s.root / "tree/a.txt").write_text("one\n", encoding="utf-8")
        command = s.passing_gate("g.sh", "ran.txt")
        s.registry([simple_gate(
            "g", [command],
            {"populations": [{"root": "tree", "pattern": "**/*", "mode": "traversable"}]},
            "^OK — g.sh: ")])
        s.run()
        require(s.disposition("g") == "reused", "a readable tree should reuse")

        (s.root / "tree/b.txt").write_text("two\n", encoding="utf-8")
        require(s.disposition("g") == "reused",
                "an ordinary added file must not invalidate this mode")
        (s.root / "tree/b.txt").write_text("changed\n", encoding="utf-8")
        require(s.disposition("g") == "reused",
                "nor must an ordinary edit")

        (s.root / "tree/dangling").symlink_to(s.root / "nowhere")
        require(s.disposition("g") == "fresh",
                "a dangling symlink makes the tree uncopyable, so it must refuse")
        (s.root / "tree/dangling").unlink()
        require(s.disposition("g") == "reused", "and reuse again once it is gone")

        (s.root / "tree/b.txt").chmod(0o000)
        try:
            require(s.disposition("g") == "fresh", "an unreadable file must refuse")
        finally:
            (s.root / "tree/b.txt").chmod(0o644)


# --- negative controls ------------------------------------------------------
#
# Each one breaks the engine in the exact way a careless change would and
# requires a named control to FAIL.  A control suite whose assertions hold
# vacuously is worse than none: it reports safety it never checked.


@contextmanager
def patched(target: Any, name: str, replacement: Any):
    original = getattr(target, name)
    setattr(target, name, replacement)
    try:
        yield
    finally:
        setattr(target, name, original)


def must_fail(control: Callable[[], None], label: str) -> None:
    try:
        control()
    except ControlFailure:
        return
    raise ControlFailure(f"negative control did not bite: {label}")


def control_negative_laundering_unknown_into_unchanged() -> None:
    """If an unidentifiable input were quietly digested as a constant instead
    of raising, a missing Lake trace would read as "nothing moved"."""

    def unchanged(root: Path, modules: list[str]):
        return gc.digest_of("<lean deps assumed unchanged>"), {}

    with patched(gc, "component_lean_modules", unchanged):
        must_fail(control_missing_trace_forces_execution, "missing trace laundered to unchanged")
        must_fail(control_malformed_trace_forces_execution, "malformed trace laundered")


def control_negative_dropping_the_post_execution_drift_check() -> None:
    """Without the recompute-after-execution step, a gate that edits its own
    declared inputs while running would have its verdict cached against the
    tree it left behind rather than the one it saw."""

    real = gc.fingerprint
    memo: dict[str, Any] = {}

    def frozen(root: Path, gate: dict[str, Any]):
        if gate["id"] not in memo:
            memo[gate["id"]] = real(root, gate)
        return memo[gate["id"]]

    with patched(gc, "fingerprint", frozen):
        must_fail(control_drift_during_the_run_is_not_cached, "drift check removed")


def control_negative_caching_a_failed_run() -> None:
    """If `passed` were computed from the exit code alone, a gate that stopped
    printing its terminal line would seed a passing record."""

    real = gc.capture_verdict

    def lenient(gate: dict[str, Any], result: subprocess.CompletedProcess) -> dict[str, Any]:
        verdict = real(gate, result)
        verdict["passed"] = result.returncode == 0
        verdict["problems"] = []
        return verdict

    with patched(gc, "capture_verdict", lenient):
        must_fail(control_missing_summary_is_never_cached, "summary requirement removed")
        must_fail(control_duplicated_summary_is_never_cached, "duplicate summary tolerated")


def control_negative_accepting_a_damaged_cache() -> None:
    """If `read_cache` returned whatever parsed, a record claiming a failing
    verdict would be credited as a pass."""

    def permissive(path: Path) -> tuple[dict[str, Any], str | None]:
        try:
            cache = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            return gc.empty_cache(), "unreadable"
        if not isinstance(cache, dict) or "gates" not in cache:
            return gc.empty_cache(), "shape"
        cache.setdefault("details", {})
        return cache, None

    with patched(gc, "read_cache", permissive):
        must_fail(control_nonzero_record_poisons_nothing, "cache validation removed")


def control_negative_last_record_only_lookup() -> None:
    """A lookup restricted to the newest record would silently stop crediting
    a return to an earlier tree -- the ordinary shape of measuring a change and
    reverting it."""

    def newest_only(cache: dict[str, Any], identifier: str, print_: str):
        records = cache["gates"].get(identifier, [])
        if records and records[-1]["fingerprint"] == print_:
            return records[-1]
        return None

    with patched(gc, "lookup", newest_only):
        must_fail(control_historical_record_is_recoverable, "historical lookup removed")


def control_negative_ignoring_population_membership() -> None:
    """If a population digested content without paths, adding or removing a
    file from a scanned corpus would look like no change at all."""

    real = gc.component_populations

    def content_only(root: Path, specs: list[dict[str, Any]]):
        _, detail = real(root, specs)
        return gc.digest_of(sorted(detail.values())), detail

    with patched(gc, "component_populations", content_only):
        must_fail(control_population_membership_invalidates, "membership dropped from the digest")


def control_negative_lenient_import_parser() -> None:
    """If the import parser skipped what it could not parse -- the obvious,
    tolerant-looking choice -- a module imported on an unrecognised line would
    become permanently invisible to the fingerprint."""

    def lenient(path: Path) -> list[str]:
        modules: list[str] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            match = gc.IMPORT_LINE.match(line)
            if match:
                modules.extend(match.group(1).split())
        return modules

    with patched(gc, "imports_of", lenient):
        must_fail(control_unparsable_import_cannot_hide_a_dependency,
                  "unparsable imports silently skipped")


def control_negative_trusting_the_registry_at_run_time() -> None:
    """Without the run-time reconciliation, the registry is its own authority
    for what exists -- and an audit nobody is required to run is no authority
    at all."""

    def unchecked(root: Path, quiet: bool = False) -> int:
        return 0

    with patched(gc, "audit", unchecked):
        must_fail(control_run_refuses_a_registry_that_lost_a_gate,
                  "run-time registry reconciliation removed")


def control_negative_running_the_build_uncoordinated() -> None:
    """If the prerequisite elaborated without asking the host -- or asked and
    then ignored the answer -- a refusal would become an uncoordinated build on
    a machine that had just said it had no room for one."""

    @contextlib.contextmanager
    def uncoordinated(what: str, memory_gib: int = 0):
        yield

    with patched(gate_semaphore, "admitted", uncoordinated):
        must_fail(
            control_build_prerequisite_coordinates_the_host_and_fails_closed,
            "host admission removed from the build prerequisite",
        )


def control_negative_never_releasing_the_build_hold() -> None:
    """An acquisition with no matching release leaves the host owned by a
    process that has finished with it.  That is what the release *count*
    requirement is for, and it is a different failure from keeping the hold too
    long: here the hold is never given back at all."""

    @contextlib.contextmanager
    def never_released(what: str, memory_gib: int = 0):
        completed = subprocess.run(
            [str(gate_semaphore.ENTRY), "adaptive-acquire", gate_semaphore.label(),
             "--note", what, "--memory-gib", str(memory_gib)],
            capture_output=True, text=True, check=False,
        )
        detail = completed.stdout + completed.stderr
        if completed.returncode != 0 and "ALREADY_HELD" not in detail:
            raise gate_semaphore.Refused(detail.strip())
        yield

    with patched(gate_semaphore, "admitted", never_released):
        must_fail(
            control_build_prerequisite_coordinates_the_host_and_fails_closed,
            "the build hold never released",
        )


def control_negative_holding_the_host_across_the_selective_run() -> None:
    """`admitted` exists so the runner drops the host between the build and the
    rows it plans.  The competing design -- one hold taken before the first row
    and let go after the last -- is not a hold that leaks: it acquires once,
    releases once, names the goal, states an estimate, and satisfies every
    count.  What it does is own the host for the length of a selective run,
    which is the 22-minute starvation this coordination exists to avoid, and
    the *ordering* requirement is the only assertion that can see it.

    So the mutation here is that design rather than a broken version of it: the
    real `admitted` wrapped around the whole run, with the runner's own
    per-build acquisition made inert inside it.  It fails on ordering alone.
    """

    real_run = gc.run
    real_admitted = gate_semaphore.admitted

    @contextlib.contextmanager
    def already_covered(what: str, memory_gib: int = 0):
        yield

    def one_hold_for_the_whole_run(root: Path, arguments: Any) -> int:
        what = "the whole selective run"
        try:
            with real_admitted(what, 8):
                with patched(gate_semaphore, "admitted", already_covered):
                    return real_run(root, arguments)
        except gate_semaphore.Refused as refusal:
            for line in gate_semaphore.refusal_lines(gate_semaphore.label(), what, refusal):
                print(line, file=sys.stderr)
            print("GATES FAILED: prerequisite refresh failed; nothing was planned",
                  file=sys.stderr)
            return 1

    with patched(gc, "run", one_hold_for_the_whole_run):
        must_fail(
            control_build_prerequisite_coordinates_the_host_and_fails_closed,
            "the build hold kept across the planned rows",
        )


def control_negative_ignoring_the_declared_coordination_mode() -> None:
    """`off`, `inherited` and an absent entry point are decisions, not
    conveniences: they are how Blanc stays standalone and how a caller's own
    hold is honoured.  A helper that consulted the host regardless -- or that
    treated a missing Creme checkout as a refusal -- would turn the supported
    CI setting into a red run on a machine with nothing to coordinate with."""

    real = gate_semaphore.acquire_once

    def always_coordinates(what: str, memory_gib: int = gate_semaphore.NARROW_GIB) -> None:
        if not os.access(gate_semaphore.ENTRY, os.X_OK):
            raise gate_semaphore.Refused(f"no coordination entry point at {gate_semaphore.ENTRY}")
        with declared_coordination(None):
            real(what, memory_gib)

    with patched(gate_semaphore, "acquire_once", always_coordinates):
        must_fail(control_coordination_off_never_asks_the_host_and_says_so,
                  "the off branch removed")
        must_fail(control_coordination_inherited_borrows_and_releases_nothing,
                  "the inherited branch removed")
        must_fail(control_absent_coordination_entry_point_announces_once_and_runs,
                  "an absent entry point turned into a refusal")


def control_negative_shell_ignoring_the_declared_coordination_mode() -> None:
    """The shell half's mode branches, deleted one class at a time.

    `off`, `inherited` and an absent entry point are decisions, not
    conveniences: they are how Blanc stays standalone, how the supported CI
    setting stays green on a runner with nothing to coordinate with, and how a
    caller's own hold is honoured instead of being taken twice and then given
    away.  A `case` arm is a line; this requires its deletion to be noticed.
    """

    committed = gate_semaphore_shell_source()

    branches = (
        '  case "${BLANC_GATE_SEMAPHORE:-}" in\n'
        '    off)\n'
        '      echo "NOTE — $gs_label: BLANC_GATE_SEMAPHORE=off; $gs_what elaborates without host admission"\n'
        '      return 0\n'
        '      ;;\n'
        '    inherited)\n'
        '      return 0\n'
        '      ;;\n'
        '  esac\n'
    )
    require(committed.count(branches) == 1,
            "the negative control no longer matches the mode branches it deletes")
    without_modes = committed.replace(branches, "  :\n")
    with patched(sys.modules[__name__], "gate_semaphore_shell_source",
                 lambda: without_modes):
        must_fail(control_shell_coordination_off_never_asks_the_host_and_says_so,
                  "the shell off branch removed")
        must_fail(control_shell_coordination_inherited_borrows_and_releases_nothing,
                  "the shell inherited branch removed")

    standalone = (
        '    echo "NOTE — $gs_label: no host coordination at $GATE_SEMAPHORE_ENTRY;'
        ' $gs_what elaborates uncoordinated"\n'
        '    return 0\n'
    )
    require(committed.count(standalone) == 1,
            "the negative control no longer matches the standalone branch it breaks")
    refusing = committed.replace(
        standalone,
        '    echo "REFUSED — $gs_label: no host coordination at $GATE_SEMAPHORE_ENTRY"\n'
        '    return 1\n',
    )
    with patched(sys.modules[__name__], "gate_semaphore_shell_source",
                 lambda: refusing):
        must_fail(control_shell_absent_coordination_entry_point_announces_once_and_runs,
                  "a missing Creme checkout turned into a refusal")

    always_releases = committed.replace(
        '        tolerant:*) return 0 ;;\n',
        '        tolerant:*) GATE_SEMAPHORE_HELD="$gs_label"; return 0 ;;\n',
    )
    require(always_releases != committed,
            "the negative control no longer matches the inheritance branch it breaks")
    with patched(sys.modules[__name__], "gate_semaphore_shell_source",
                 lambda: always_releases):
        must_fail(control_shell_coordination_asks_the_host_and_fails_closed,
                  "an inherited hold released by the process that never took it")

    unproved_authoritative_inheritance = committed.replace(
        '      case "$gs_contention:$gs_out" in\n'
        '        tolerant:*) return 0 ;;\n'
        '        sensitive:*"hard hold"*|exclusive:*"hard hold"*) return 0 ;;\n'
        '        *) gs_out="$gs_out"$\'\\n\'"ALREADY_HELD response did not prove a hard hold for contention=$gs_contention" ;;\n'
        '      esac\n',
        '      return 0\n',
    )
    require(unproved_authoritative_inheritance != committed,
            "the negative control no longer matches the authoritative inheritance guard")
    with patched(sys.modules[__name__], "gate_semaphore_shell_source",
                 lambda: unproved_authoritative_inheritance):
        must_fail(control_shell_authoritative_admission_requires_a_hard_inheritance,
                  "an unproved timing inheritance was accepted")


def control_negative_beacon_current_mainnet_exec_leaks_the_gate_hold() -> None:
    """Replacing the final child call with `exec` must fail the lifetime control."""

    committed = beacon_current_mainnet_wrapper_source()
    final_child = '\n/usr/bin/env -i "${CHILD_ENV[@]}" "$TARGET_PYTHON" -B -s \\\n'
    require(committed.count(final_child) == 1,
            "the negative control no longer matches the final current-mainnet child")
    with_exec = committed.replace(final_child, "\nexec" + final_child[1:])
    with patched(sys.modules[__name__], "beacon_current_mainnet_wrapper_source",
                 lambda: with_exec):
        must_fail(control_beacon_current_mainnet_releases_after_its_final_child,
                  "an exec that bypasses the wrapper EXIT trap was accepted")


def control_campaign_sampling_is_deterministic_and_fail_closed() -> None:
    gs.self_test()
    policy, harness = gs.validate_policy()
    require(policy["enabled_families"] == [], "production sampling was enabled")
    require(bool(harness), "the economic inventory exposed no harness families")


NEGATIVE_CONTROLS = (
    control_negative_laundering_unknown_into_unchanged,
    control_negative_dropping_the_post_execution_drift_check,
    control_negative_caching_a_failed_run,
    control_negative_accepting_a_damaged_cache,
    control_negative_last_record_only_lookup,
    control_negative_ignoring_population_membership,
    control_negative_lenient_import_parser,
    control_negative_trusting_the_registry_at_run_time,
    control_negative_running_the_build_uncoordinated,
    control_negative_never_releasing_the_build_hold,
    control_negative_holding_the_host_across_the_selective_run,
    control_negative_ignoring_the_declared_coordination_mode,
    control_negative_shell_ignoring_the_declared_coordination_mode,
    control_negative_beacon_current_mainnet_exec_leaks_the_gate_hold,
)

CONTROLS = (
    control_first_run_executes_and_second_reuses,
    control_content_change_invalidates,
    control_population_membership_invalidates,
    control_unrelated_change_still_reuses,
    control_membership_mode_ignores_content,
    control_implementation_change_invalidates,
    control_command_arguments_invalidate,
    control_registry_declaration_invalidates,
    control_lock_implementation_is_not_gate_evidence_identity,
    control_presentation_edits_preserve_soundness_identity,
    control_soundness_edit_invalidates_every_cacheable_row,
    control_scheduling_metadata_is_not_substantive_verdict_identity,
    control_t8n_resolver_invalidates_only_its_consumers,
    control_lean_module_dep_hash_invalidates,
    control_missing_trace_forces_execution,
    control_malformed_trace_forces_execution,
    control_lean_entry_source_and_imports_invalidate,
    control_transitive_edit_reaches_the_gate,
    control_unparsable_import_cannot_hide_a_dependency,
    control_git_ref_movement_invalidates,
    control_unresolvable_ref_forces_execution,
    control_external_checkout_identity,
    control_oracle_lanes_are_disjoint_and_exact,
    control_symlink_file_target_invalidates,
    control_current_mainnet_python_base_is_native,
    control_symlink_directory_selector_invalidates,
    control_environment_variable_invalidates,
    control_expiry_clock_moves_only_at_semantic_transition,
    control_tool_identity_invalidates,
    control_unknown_tool_is_a_registry_fault,
    control_exact_build_certificate_skips_only_the_authoritative_build,
    control_build_prerequisite_coordinates_the_host_and_fails_closed,
    control_coordination_off_never_asks_the_host_and_says_so,
    control_coordination_inherited_borrows_and_releases_nothing,
    control_absent_coordination_entry_point_announces_once_and_runs,
    control_coordination_controls_declare_their_own_environment,
    control_shell_coordination_asks_the_host_and_fails_closed,
    control_shell_coordination_off_never_asks_the_host_and_says_so,
    control_shell_coordination_inherited_borrows_and_releases_nothing,
    control_shell_absent_coordination_entry_point_announces_once_and_runs,
    control_shell_admission_request_states_the_goal_the_estimate_and_the_wait,
    control_shell_authoritative_admission_requires_a_hard_inheritance,
    control_beacon_current_mainnet_releases_after_its_final_child,
    control_build_certificate_refuses_every_identity_and_trace_uncertainty,
    control_corrupt_build_certificate_forces_authoritative_build,
    control_material_output_reuses_proof_only_and_refuses_every_material_uncertainty,
    control_worktree_seed_previews_then_publishes_isolated_exact_state,
    control_worktree_seed_refuses_missing_stale_or_different_state,
    control_worktree_seed_never_publishes_partial_or_racing_state,
    control_dependency_evidence_is_consumed_without_rerunning_its_body,
    control_missing_or_failing_dependency_never_yields_a_green_consumer,
    control_failed_run_is_never_cached,
    control_missing_summary_is_never_cached,
    control_duplicated_summary_is_never_cached,
    control_drift_during_the_run_is_not_cached,
    control_drift_on_a_reused_row_reddens_the_run,
    control_corrupt_cache_costs_a_run_not_correctness,
    control_nonzero_record_poisons_nothing,
    control_deleted_cache_forces_everything,
    control_historical_record_is_recoverable,
    control_eviction_costs_time_only,
    control_pruned_details_do_not_break_explain,
    control_registry_faults_are_refused,
    control_registry_schema_version_is_enforced,
    control_lock_refuses_a_second_run,
    control_kernel_lock_refuses_another_process,
    control_stale_owner_metadata_does_not_block_an_unlocked_mutex,
    control_same_repository_worktrees_share_records_and_lock,
    control_other_physical_clone_never_inherits_shared_records,
    control_foreign_host_store_never_yields_reuse,
    control_dirty_worktree_does_not_seed_shared_evidence,
    control_atomic_write_leaves_no_debris,
    control_there_is_no_force,
    control_fresh_mode_adds_work_and_refreshes,
    control_always_fresh_rows_never_reuse,
    control_report_and_manifest_are_self_contained,
    control_audit_accepts_a_reconciled_registry,
    control_audit_fails_on_catalogue_drift,
    control_audit_fails_on_a_stale_generated_inventory,
    control_audit_needs_a_catalogue_block,
    control_every_import_spelling_is_parsed_or_refused,
    control_run_refuses_a_registry_that_lost_a_gate,
    control_named_root_follows_its_override,
    control_environment_value_cannot_imitate_absence,
    control_symlinked_directory_refuses_rather_than_hides_files,
    control_traversable_population_refuses_what_a_copy_cannot_read,
    control_non_zero_expected_exit_is_refused,
    control_campaign_sampling_is_deterministic_and_fail_closed,
) + NEGATIVE_CONTROLS


def self_test() -> int:
    failures: list[str] = []
    # Nothing in this suite is entitled to read the coordination environment it
    # was started with: `BLANC_GATE_SEMAPHORE=off` is a supported setting, and
    # a control that silently changed meaning under it would be reporting on a
    # branch it never named.  Controls declare their own mode on top of this.
    with declared_coordination(None):
        for control in CONTROLS:
            name = control.__name__.removeprefix("control_")
            try:
                control()
            except Exception as error:  # noqa: BLE001 - a control fault is a failure
                failures.append(f"{name}: {error}")
                print(f"  FAIL {name}: {error}", file=sys.stderr)
    total = len(CONTROLS)
    if failures:
        print(
            f"REGRESSION — gate cache self-test: {len(failures)}/{total} controls failed",
            file=sys.stderr,
        )
        return 1
    print(
        f"OK — gate cache self-test: {total}/{total} invalidation, cache, registry, "
        f"concurrency and negative controls passed "
        f"({len(NEGATIVE_CONTROLS)} of them controls on the controls)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(self_test())
