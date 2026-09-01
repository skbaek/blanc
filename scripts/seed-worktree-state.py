#!/usr/bin/env python3
"""CLI shim for the importable Blanc worktree seeder."""

from worktree_seed import main


if __name__ == "__main__":
    import sys

    raise SystemExit(main(sys.argv[1:]))
