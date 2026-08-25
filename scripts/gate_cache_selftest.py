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


# --- scratch repository -----------------------------------------------------


class Scratch:
    """A throwaway repository with real files, real traces and a real git."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.output = ""
        (root / "scripts").mkdir(parents=True, exist_ok=True)
        (root / "Blanc").mkdir(parents=True, exist_ok=True)
        (root / ".lake/build/lib/lean/Blanc").mkdir(parents=True, exist_ok=True)

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

    def registry(self, gates: list[dict[str, Any]]) -> None:
        gc.atomic_json(gc.registry_path(self.root), {"schema": 1, "gates": gates})

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
        self.git("init", "-q")
        self.git("config", "user.email", "control@example.invalid")
        self.git("config", "user.name", "control")
        self.git("add", "-A")
        self.git("-c", "commit.gpgsign=false", "commit", "-q", "-m", "one")


@contextmanager
def scratch():
    directory = Path(tempfile.mkdtemp(prefix="gate-cache-control-"))
    try:
        yield Scratch(directory)
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


def control_clock_rollover_invalidates() -> None:
    """A gate holding an expiring exception reads the clock whether it says so
    or not, so yesterday's pass must stop counting tomorrow."""

    with scratch() as s:
        s.gate("g.sh", '#!/bin/sh\necho "OK — g.sh: 1/1 fine"\n')
        s.registry([simple_gate("g", ["scripts/g.sh"], {"clock": "utc-date"}, "^OK — g.sh: ")])
        s.run()
        require(s.disposition("g") == "reused", "the same day should reuse")
        original = time.gmtime
        time.gmtime = lambda *arguments: original(0)  # 1970-01-01
        try:
            require(s.disposition("g") == "fresh", "a different date must force execution")
        finally:
            time.gmtime = original


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


def control_stale_lock_is_reclaimed_and_announced() -> None:
    with scratch() as s:
        path = gc.lock_path(s.root)
        path.mkdir(parents=True)
        (path / "pid").write_text("999999999\n", encoding="utf-8")
        require(gc.acquire_lock(path), "a lock held by a dead process must be reclaimed")
        gc.release_lock(path)


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
        require("reused successful evidence" in report,
                "the report must not imply a reused gate's body ran")
        require("executed now" not in report.split("| reused successful evidence |")[0]
                .split("\n")[-1], "dispositions must not be conflated")


# --- controls: the population audit ------------------------------------------


def audit_scratch(s: "Scratch", commands: list[str], gates: list[dict], ci: list[str]) -> int:
    """Wire a scratch repository with a catalogue, a CI workflow and a registry."""

    block = "\n".join(commands)
    s.write(
        "scripts/GATES.md",
        "# Verification gates\n\n"
        "**The full set, in order.** This is what a checkpoint runs:\n\n"
        f"```\n{block}\n```\n",
    )
    s.write(
        ".github/workflows/ci.yml",
        "jobs:\n  gates:\n    steps:\n"
        + "".join(f"      - run: {command}\n" for command in ci),
    )
    s.registry(gates)
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
        s.registry([audit_gate("a", ["scripts/check-a.sh"], 1)])
        try:
            gc.audit(s.root)
        except gc.GateCacheError:
            return
        raise ControlFailure("a catalogue with no ordered block must be a fault")


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


NEGATIVE_CONTROLS = (
    control_negative_laundering_unknown_into_unchanged,
    control_negative_dropping_the_post_execution_drift_check,
    control_negative_caching_a_failed_run,
    control_negative_accepting_a_damaged_cache,
    control_negative_last_record_only_lookup,
    control_negative_ignoring_population_membership,
    control_negative_lenient_import_parser,
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
    control_lean_module_dep_hash_invalidates,
    control_missing_trace_forces_execution,
    control_malformed_trace_forces_execution,
    control_lean_entry_source_and_imports_invalidate,
    control_transitive_edit_reaches_the_gate,
    control_unparsable_import_cannot_hide_a_dependency,
    control_git_ref_movement_invalidates,
    control_unresolvable_ref_forces_execution,
    control_external_checkout_identity,
    control_environment_variable_invalidates,
    control_clock_rollover_invalidates,
    control_tool_identity_invalidates,
    control_unknown_tool_is_a_registry_fault,
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
    control_stale_lock_is_reclaimed_and_announced,
    control_atomic_write_leaves_no_debris,
    control_there_is_no_force,
    control_fresh_mode_adds_work_and_refreshes,
    control_always_fresh_rows_never_reuse,
    control_report_and_manifest_are_self_contained,
    control_audit_accepts_a_reconciled_registry,
    control_audit_fails_on_catalogue_drift,
    control_audit_fails_on_a_stale_generated_inventory,
    control_audit_needs_a_catalogue_block,
) + NEGATIVE_CONTROLS


def self_test() -> int:
    failures: list[str] = []
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
