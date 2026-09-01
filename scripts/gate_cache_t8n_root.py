#!/usr/bin/env python3
"""Native CPython-root resolution for Blanc's current-mainnet gate inputs.

Only gates whose declarations consume the current-mainnet target include this
module in their runner identity. Keeping the resolver separate means a native
runtime/platform improvement invalidates those gates without discarding valid
evidence for unrelated proof and contract families.
"""

from __future__ import annotations

import os
from pathlib import Path


T8N_TARGET_ROOT = ("JAUNE_T8N_TARGET", "~/execution-specs-t8n-amsterdam")


class T8nPythonBaseError(RuntimeError):
    """The target venv does not identify one exact native CPython base."""


def resolve_t8n_python_base(root: Path) -> Path:
    variable, default = T8N_TARGET_ROOT
    target = Path(os.path.expanduser(os.environ.get(variable) or default))
    if not target.is_absolute():
        target = root / target
    selector = target / ".venv/bin/python"
    if not selector.is_symlink():
        raise T8nPythonBaseError(
            "current-mainnet Python selector is not a symlink: "
            "@t8n_target/.venv/bin/python"
        )
    try:
        selected = selector.resolve(strict=True)
    except OSError as error:
        raise T8nPythonBaseError(
            f"cannot resolve current-mainnet Python selector: {error}"
        ) from error
    if (
        not selected.is_file()
        or selected.name != "python3.11"
        or selected.parent.name != "bin"
    ):
        raise T8nPythonBaseError(
            f"current-mainnet Python selector has unexpected target: {selected}"
        )
    return selected.parent.parent
