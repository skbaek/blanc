#!/usr/bin/env python3
import sys
import json
import os

# Add the directory containing permit.py to the path
permit_dir = os.path.expanduser("~/blanc/.claude")
if permit_dir not in sys.path:
    sys.path.insert(0, permit_dir)

try:
    from permit import Unsafe, decide
except Exception as e:
    print(json.dumps({
        "decision": "force_ask",
        "reason": f"Wrapper error: Could not import permit.py from .claude - {e}",
    }))
    sys.exit(0)


def emit(decision, reason, command=""):
    """Translate the shared policy decision to Antigravity's hook protocol."""
    # Antigravity's ordinary `ask` decision still respects its cached
    # "Always Proceed" permission.  The shared policy's `ask` means that the
    # user must actually be prompted, so use Antigravity's stronger spelling.
    antigravity_decision = "force_ask" if decision == "ask" else decision
    output = {"decision": antigravity_decision, "reason": reason}
    if decision == "allow" and command:
        # Antigravity applies its project permission engine after PreToolUse.
        # Supply a temporary grant for this exact command so a project-level
        # `command(*)` Ask rule does not prompt after the hook allowed it.
        output["permissionOverrides"] = [f"command({command})"]
    print(json.dumps(output))

def main():
    try:
        # 1. Read Antigravity's payload from stdin
        payload = sys.stdin.read().strip()
        if not payload:
            emit("force_ask", "Wrapper error: Empty stdin payload")
            sys.exit(0)
            
        data = json.loads(payload)
        
        # 2. Extract the bash command and cwd
        tool_call = data.get("toolCall", {})
        args = tool_call.get("args", {})
        command = args.get("CommandLine", "")
        cwd = args.get("Cwd", "")
        
        # 3. Use your existing logic to get a decision
        try:
            decision, reason = decide(command, cwd)
        except Unsafe as e:
            # The canonical policy uses Unsafe to short-circuit some ask/deny
            # decisions. Preserve that decision instead of treating it as a
            # wrapper failure.
            decision, reason = e.decision, e.reason

        # 4. Translate the canonical policy's `ask` to Antigravity's
        # `force_ask`; an ordinary `ask` is bypassed by "Always Proceed".
        emit(decision, reason, command)
        sys.exit(0)
        
    except Exception as e:
        # Fall-safe: Always force an ask prompt if the script crashes
        emit("force_ask", f"Wrapper error: {e}")
        sys.exit(0)

if __name__ == "__main__":
    main()
