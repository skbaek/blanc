#!/usr/bin/env python3
"""
permit.py — sole arbiter for Bash commands under a Claude Code PreToolUse hook.

Wire-up (in .claude/settings.json):
    "hooks": { "PreToolUse": [ { "matcher": "Bash", "hooks": [
        { "type": "command", "command": "python3 \"$CLAUDE_PROJECT_DIR/.claude/permit.py\"" }
    ] } ] }

Protocol:
    stdin : JSON  {"tool_name":"Bash","tool_input":{"command":"..."}, ...}
    stdout: JSON  {"hookSpecificOutput":{"hookEventName":"PreToolUse",
                   "permissionDecision":"allow"|"deny"|"ask",
                   "permissionDecisionReason":"..."}}

    allow -> runs with NO prompt (bypasses Claude Code's built-in allow/deny)
    ask   -> falls through to the normal permission prompt  (the safe default)
    deny  -> blocked outright, reason shown to Claude

You have 100% control here. The default policy AUTO-ALLOWS only what it can prove
is non-state-altering: a whitelist of read-only tools, freely composed with
pipes / && / ; / || and with output redirected only to /dev/null (or fd dups).
Everything it cannot prove safe returns "ask" so you still decide by hand. Any
parse error or exception also returns "ask" — it never fails open.

Edit READONLY, the write-mode guards, or ALLOWED_ROOTS to taste.
"""

import sys, json, os, re

# --- policy knobs -----------------------------------------------------------

# Tools with no state-altering mode (modulo the guarded exceptions below).
READONLY = {
    "grep", "egrep", "fgrep", "rg", "ripgrep",
    "ls", "cat", "head", "tail", "wc", "nl", "tac",
    "sort", "uniq", "cut", "tr", "column", "rev", "fold", "comm", "diff",
    "pwd", "basename", "dirname", "realpath", "readlink",
    "stat", "file", "find", "sed", "awk", "gawk", "mawk",
    "echo", "printf", "true", "false", "test", "seq", "expr", "date",
    "jq", "yq", "xxd", "od", "hexdump", "strings", "tree",
    "which", "type", "cksum", "md5sum", "sha1sum", "sha256sum", "sha512sum",
}

# Output-redirect targets that don't write real files.
SAFE_REDIR_TARGETS = {"/dev/null", "/dev/stdout", "/dev/stderr", "/dev/tty"}

# `find` primaries that mutate the filesystem or execute programs.
FIND_WRITE = {
    "-delete", "-exec", "-execdir", "-ok", "-okdir",
    "-fprint", "-fprint0", "-fprintf", "-fls",
}

# Optional directory fence: if set, any *absolute* path argument must live under
# one of these roots, else -> ask. Relative paths are fine (they resolve under
# the project cwd). Set to None to disable the fence entirely.
ALLOWED_ROOTS = ("/Users/bsk/blanc", "/Users/bsk/elevm")

CTRL_OPS = {"|", "||", "&&", ";", "&", "\n"}


class Unsafe(Exception):
    """Raised to short-circuit to a non-allow decision."""
    def __init__(self, decision, reason):
        self.decision = decision
        self.reason = reason


def parse_segments(cmd: str):
    """Quote-aware split of a command line into simple-command segments.

    Returns a list of segments, each a list of literal word strings, with
    redirects already validated and stripped. Raises Unsafe on anything we
    won't auto-allow (command substitution, subshells, writing redirects, ...).
    """
    i, n = 0, len(cmd)
    words, segments = [], []
    cur, have_word = [], False
    pending_redir = None  # None | 'out' | 'in'

    def push_char(c):
        nonlocal have_word
        cur.append(c)
        have_word = True

    def flush_word():
        nonlocal cur, have_word, pending_redir
        if not have_word:
            return
        w = "".join(cur)
        cur, have_word = [], False
        if pending_redir == "out":
            pending_redir = None
            if w not in SAFE_REDIR_TARGETS:
                raise Unsafe("ask", "writes to file: " + w)
            return  # consumed as redirect target, not a word
        if pending_redir == "in":
            pending_redir = None
            return  # input redirect target: reading is harmless
        words.append(w)

    def flush_segment():
        nonlocal words
        flush_word()
        if words:
            segments.append(words)
        words = []

    while i < n:
        c = cmd[i]

        if c == "'":  # single quote: fully literal
            j = cmd.find("'", i + 1)
            if j == -1:
                raise Unsafe("ask", "unbalanced single quote")
            for ch in cmd[i + 1:j]:
                push_char(ch)
            have_word = True
            i = j + 1
            continue

        if c == '"':  # double quote: literal, but $() and ` stay active
            i += 1
            while i < n and cmd[i] != '"':
                ch = cmd[i]
                if ch == "\\" and i + 1 < n and cmd[i + 1] in '"\\$`':
                    push_char(cmd[i + 1]); i += 2; continue
                if ch == "$" and i + 1 < n and cmd[i + 1] == "(":
                    raise Unsafe("ask", "command substitution")
                if ch == "`":
                    raise Unsafe("ask", "command substitution")
                push_char(ch); i += 1
            if i >= n:
                raise Unsafe("ask", "unbalanced double quote")
            have_word = True
            i += 1
            continue

        if c == "\\":
            if i + 1 < n:
                push_char(cmd[i + 1]); i += 2; continue
            i += 1; continue

        if c == "$" and i + 1 < n and cmd[i + 1] == "(":
            raise Unsafe("ask", "command substitution")
        if c == "`":
            raise Unsafe("ask", "command substitution")
        if c in "()":
            raise Unsafe("ask", "subshell")

        if c.isspace():
            flush_word(); i += 1; continue

        if c in "|&;<>":
            flush_word()
            op, i = _read_operator(cmd, i)
            if op in CTRL_OPS:
                flush_segment()
                continue
            # a redirect operator
            if op in ("<", "<<", "<<<"):
                pending_redir = "in"
                continue
            # output redirect: check for an fd-dup (>&1, >&-) first
            k = i
            while k < n and cmd[k] == " ":
                k += 1
            if k < n and cmd[k] == "&":
                k += 1
                while k < n and (cmd[k].isdigit() or cmd[k] == "-"):
                    k += 1
                i = k  # fd duplication, no file written
                continue
            pending_redir = "out"
            continue

        push_char(c); i += 1

    flush_segment()
    return segments


def _read_operator(cmd: str, i: int):
    """Consume one shell operator starting at i; return (op_string, new_index)."""
    n = len(cmd)
    if cmd[i] == "&" and i + 1 < n and cmd[i + 1] == ">":
        if cmd[i:i + 3] == "&>>":
            return "&>>", i + 3
        return "&>", i + 2
    for two in ("||", "&&", ">>", "<<", "<>"):
        if cmd[i:i + 2] == two:
            if two == "<<" and cmd[i:i + 3] == "<<<":
                return "<<<", i + 3
            return two, i + 2
    return cmd[i], i + 1


def _outside_roots(word: str, cwd: str) -> bool:
    if ALLOWED_ROOTS is None:
        return False
    if word.startswith("-"):
        return False  # option flag, not a path
    base = cwd or os.getcwd()
    word = os.path.expanduser(word)  # leading ~ / ~user, like the shell
    p = word if os.path.isabs(word) else os.path.join(base, word)
    real = os.path.normpath(p)  # collapses ../ ; escapes leave the roots
    return not any(real == r or real.startswith(r + os.sep) for r in ALLOWED_ROOTS)


def decide(command: str, cwd: str = ""):
    """Return (decision, reason) for a raw Bash command string."""
    command = command.strip()
    if not command:
        return "ask", "empty command"

    segments = parse_segments(command)  # may raise Unsafe
    if not segments:
        return "ask", "no command"

    for seg in segments:
        w = list(seg)
        # drop leading VAR=val environment assignments
        while w and re.match(r"^[A-Za-z_][A-Za-z0-9_]*=", w[0]):
            w.pop(0)
        if not w:
            continue  # assignment-only / redirect-only segment
        prog = os.path.basename(w[0])
        if prog not in READONLY:
            return "ask", "not on read-only allowlist: " + prog

        # guard the write/exec modes of otherwise read-only tools
        if prog == "sed":
            for t in w[1:]:
                if t == "-i" or t.startswith("-i") or t.startswith("--in-place"):
                    return "ask", "sed in-place edit"
        if prog == "find":
            for t in w[1:]:
                if t in FIND_WRITE:
                    return "ask", "find " + t
        if prog in ("awk", "gawk", "mawk"):
            prog_src = " ".join(w[1:])
            if "system(" in prog_src or re.search(r'>\s*"', prog_src) or re.search(r'\|\s*"', prog_src):
                return "ask", "awk exec/redirect"

        # optional directory fence: every path argument must resolve inside roots
        for t in w[1:]:
            if _outside_roots(t, cwd):
                return "ask", "path outside allowed roots: " + t

    return "allow", "read-only composition"


def main():
    try:
        data = json.load(sys.stdin)
    except Exception:
        return _emit("ask", "unreadable hook input")

    if data.get("tool_name") != "Bash":
        return _emit("ask", "non-Bash tool")

    command = (data.get("tool_input") or {}).get("command", "")
    cwd = data.get("cwd") or ""
    try:
        decision, reason = decide(command, cwd)
    except Unsafe as u:
        decision, reason = u.decision, u.reason
    except Exception as e:
        decision, reason = "ask", "permit.py error: " + type(e).__name__
    _emit(decision, reason)


def _emit(decision: str, reason: str):
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": decision,
            "permissionDecisionReason": "permit.py: " + reason,
        }
    }))


if __name__ == "__main__":
    main()
