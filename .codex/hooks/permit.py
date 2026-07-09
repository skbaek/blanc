#!/usr/bin/env python3
"""Codex adapter for the existing Claude command policy.

The policy logic stays in `.claude/permit.py`; this file only translates Codex
hook input/output. `PreToolUse` can block unsafe commands, while
`PermissionRequest` can auto-allow commands the shared policy proves read-only.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
from typing import Optional


ROOT = pathlib.Path(__file__).resolve().parents[2]
CLAUDE_PERMIT = ROOT / ".claude" / "permit.py"


def _load_policy():
    spec = importlib.util.spec_from_file_location("blanc_claude_permit", CLAUDE_PERMIT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load policy from {CLAUDE_PERMIT}")
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
        decision, reason = policy.decide(command, cwd)
    except Exception as exc:
        decision, reason = "ask", "permit.py error: " + type(exc).__name__

    if event == "PreToolUse":
        # Codex PreToolUse cannot approve or ask for the original input. Silence
        # means normal Codex permission handling continues; deny blocks early.
        if decision == "deny":
            _emit_pre_tool_deny(reason)
    elif event == "PermissionRequest":
        if decision == "allow":
            _emit_permission_decision("allow")
        elif decision == "deny":
            _emit_permission_decision("deny", reason)
        # For "ask", emit nothing so Codex falls through to its normal prompt.


if __name__ == "__main__":
    main()
