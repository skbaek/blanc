#!/usr/bin/env python3
import sys
import json
import os

# Add the directory containing permit.py to the path
permit_dir = os.path.expanduser("~/blanc/.claude")
if permit_dir not in sys.path:
    sys.path.insert(0, permit_dir)

try:
    from permit import decide
except ImportError as e:
    print(json.dumps({"force_ask": True, "reason": f"Wrapper error: Could not import permit.py from .claude - {e}"}))
    sys.exit(0)

def main():
    try:
        # 1. Read Antigravity's payload from stdin
        payload = sys.stdin.read().strip()
        if not payload:
            print(json.dumps({"force_ask": True, "reason": "Wrapper error: Empty stdin payload"}))
            sys.exit(0)
            
        data = json.loads(payload)
        
        # 2. Extract the bash command and cwd
        tool_call = data.get("toolCall", {})
        args = tool_call.get("args", {})
        command = args.get("CommandLine", "")
        cwd = args.get("Cwd", "")
        
        # 3. Use your existing logic to get a decision
        decision, reason = decide(command, cwd)
        
        # 4. Map to Antigravity's expected JSON output
        output = {}
        if decision == "allow":
            output = {"allow_tool": True}
        elif decision == "deny":
            output = {"allow_tool": False, "error": f"permit.py denied: {reason}"}
        else: # "ask"
            output = {"force_ask": True, "reason": reason}
            
        print(json.dumps(output))
        sys.exit(0)
        
    except Exception as e:
        # Fall-safe: Always force an ask prompt if the script crashes
        print(json.dumps({"force_ask": True, "reason": f"Wrapper error: {e}"}))
        sys.exit(0)

if __name__ == "__main__":
    main()
