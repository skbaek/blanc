#!/usr/bin/env python3
"""Guard and run one repository Python entrypoint under isolated CPython.

CPython's ``-I`` mode intentionally removes the script directory from
``sys.path``. Prague oracle entrypoints still need their repository-local
helpers, so their shell owners invoke this bootstrap under ``-I -s -B``. The
bootstrap admits one sibling ``.py`` file, restores only this repository's
``scripts/`` directory, installs the pinned EELS loader guard, and then gives
that entrypoint ordinary ``__main__`` semantics.
"""

from __future__ import annotations

import runpy
import sys
from pathlib import Path


def main() -> None:
    if len(sys.argv) < 3:
        raise SystemExit(
            "usage: run-isolated-python.py EELS_ROOT ENTRYPOINT.py [ARG ...] "
            "| EELS_ROOT --check"
        )
    scripts = Path(__file__).resolve().parent
    checkout = Path(sys.argv[1]).expanduser().resolve()
    requested = Path(sys.argv[2])
    check_only = sys.argv[2:] == ["--check"]
    if not check_only and (
        requested.is_absolute() or requested.name != str(requested)
        or requested.suffix != ".py"
    ):
        raise SystemExit("isolated Python entrypoint must name one sibling .py file")
    target = (scripts / requested).resolve()
    if not check_only and (target.parent != scripts or not target.is_file()):
        raise SystemExit("isolated Python entrypoint is absent or outside scripts/")
    sys.path.insert(0, str(scripts))
    import eels_semantic_closure

    admission = eels_semantic_closure.assert_prague_environment(
        lambda message: (_ for _ in ()).throw(RuntimeError(message)),
        checkout_root=checkout,
    )
    if check_only:
        print(f"OK — pinned EELS Prague fresh-interpreter admission: {admission}")
        return
    sys.argv = [str(target), *sys.argv[3:]]
    runpy.run_path(str(target), run_name="__main__")


if __name__ == "__main__":
    main()
