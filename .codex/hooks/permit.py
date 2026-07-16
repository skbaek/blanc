#!/usr/bin/env python3
"""Codex adapter for the shared Claude command policy.

All control logic lives in the canonical policy at
`~/blanc/.claude/permit.py` — the single source of truth. This file holds NO
policy of its own; it only translates Codex's hook I/O to and from that policy's
`decide(command, cwd) -> (decision, reason)` interface. It is byte-identical in
both the blanc and elevm repos.

`PreToolUse` blocks unsafe commands early; `PermissionRequest` auto-allows
commands the shared policy proves read-only. Anything the policy returns "ask"
for emits nothing, so Codex's normal permission prompt still fires. It never
fails open: any load/parse error also results in "ask".
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
from typing import Optional


# This wrapper's own project root — used only as a cwd fallback when Codex
# omits cwd. The policy itself always comes from the blanc repo below.
ROOT = pathlib.Path(__file__).resolve().parents[2]
# The one canonical policy. Both repos' wrappers point here on purpose.
CANONICAL_POLICY = pathlib.Path("/Users/bsk/blanc/.claude/permit.py")


def _load_policy():
    spec = importlib.util.spec_from_file_location("blanc_claude_permit", CANONICAL_POLICY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load policy from {CANONICAL_POLICY}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _emit_pre_tool_deny(reason: str) -> None:
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": "permit.py: " + reason,
        }
    }))


def _emit_permission_decision(behavior: str, reason: Optional[str] = None) -> None:
    decision = {"behavior": behavior}
    if reason:
        decision["message"] = "permit.py: " + reason
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PermissionRequest",
            "decision": decision,
        }
    }))


def main() -> None:
    try:
        data = json.load(sys.stdin)
    except Exception:
        return

    if data.get("tool_name") != "Bash":
        return

    command = (data.get("tool_input") or {}).get("command", "")
    cwd = data.get("cwd") or str(ROOT)
    event = data.get("hook_event_name")

    try:
        policy = _load_policy()
    except Exception:
        # Can't load the policy — stay silent so Codex prompts (never fail open).
        return

    try:
        decision, reason = policy.decide(command, cwd)
    except policy.Unsafe as exc:
        decision, reason = exc.decision, exc.reason
    except Exception as exc:
        decision, reason = "ask", "permit.py error: " + type(exc).__name__

    if event == "PreToolUse":
        # Codex PreToolUse can only block early; approval/ask happens later.
        if decision == "deny":
            _emit_pre_tool_deny(reason)
    elif event == "PermissionRequest":
        if decision == "allow":
            _emit_permission_decision("allow")
        elif decision == "deny":
            _emit_permission_decision("deny", reason)
        # "ask" -> emit nothing; Codex falls through to its normal prompt.


if __name__ == "__main__":
    main()
