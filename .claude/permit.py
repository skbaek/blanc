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
is non-state-altering: a whitelist of read-only tools plus read-only git
subcommands, freely composed with pipes / && / ; / || and with output redirected
only to /dev/null (or fd dups). Everything it cannot prove safe returns "ask" so
you still decide by hand. Any parse error or exception also returns "ask" — it
never fails open.

Edit READONLY, GIT_READONLY, the write-mode guards, or ALLOWED_ROOTS to taste.
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
    "echo", "printf", "true", "false", "test", "seq", "expr", "date", "sleep",
    "jq", "yq", "xxd", "od", "hexdump", "strings", "tree",
    "which", "type", "cksum", "md5sum", "shasum",
    "sha1sum", "sha224sum", "sha256sum", "sha384sum", "sha512sum",
}

# Output-redirect targets that don't write real files. Any output redirect to a
# real file is not provably state-free, so it falls through to "ask".
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

# When True, a command substitution $(...) or `...` is allowed IFF the command
# inside it is itself a read-only "allow" (validated recursively). When False,
# any substitution -> ask. The no-state-change guarantee is preserved either way.
ALLOW_READONLY_SUBST = True

# Tools whose FIRST bare operand is a pattern/script (not a path), so the fence
# must not mistake e.g. a sed address `/re/,/re/p` for an absolute path.
GREP_FAMILY = {"grep", "egrep", "fgrep", "rg", "ripgrep"}
SED_FAMILY = {"sed"}
AWK_FAMILY = {"awk", "gawk", "mawk"}
# Options that consume the *next* token as their value (so it isn't the pattern).
VALUE_OPTS = {
    "grep": {"-e", "-f", "-m", "-A", "-B", "-C", "-d", "-D", "--regexp", "--file",
             "--max-count", "--after-context", "--before-context", "--context",
             "--include", "--exclude", "--include-dir", "--exclude-dir",
             "--color", "--colour", "--devices", "--binary-files", "--label"},
    "sed": {"-e", "--expression", "-f", "--file", "-l", "--line-length"},
    "awk": {"-F", "-v", "-f", "--field-separator", "--assign", "--file"},
}
# Flags whose presence means there is NO positional pattern/script operand.
EXPR_FLAGS = {
    "grep": {"-e", "-f", "--regexp", "--file"},
    "sed": {"-e", "--expression", "-f", "--file"},
    "awk": {"-f", "--file"},
}

# --- git: fine-grained read-only gate ----------------------------------------
# `git` is not in READONLY; it is admitted only through _git_gate below, which
# parses the global options (fencing any -C/--git-dir path), then requires the
# subcommand to be provably read-only. Env-assignment prefixes before git are
# refused in decide(): GIT_PAGER / GIT_EXTERNAL_DIFF / GIT_SSH_COMMAND etc. can
# make even `git diff` execute an arbitrary program.

# git global options (before the subcommand) that cannot change what runs.
# Notably ABSENT: -c / --config-env (can set core.pager, diff.external, ...)
# and --exec-path (redirects which git-* binaries get executed).
GIT_GLOBAL_OK = {
    "-P", "--no-pager", "-p", "--paginate", "--literal-pathspecs",
    "--no-optional-locks", "--no-replace-objects", "--bare",
    "--no-lazy-fetch", "--no-advice",
}

# Subcommands with no state-altering mode (modulo the arg guards in _git_gate).
GIT_READONLY = {
    "show", "log", "whatchanged", "diff", "status", "blame", "annotate",
    "shortlog", "describe", "grep", "rev-parse", "rev-list", "ls-files",
    "ls-tree", "cat-file", "merge-base", "name-rev", "for-each-ref",
    "show-ref", "cherry", "range-diff", "diff-tree", "diff-index",
    "diff-files", "show-branch", "count-objects", "check-ignore",
    "check-attr", "verify-commit", "verify-tag", "var", "version",
}

# Subcommands read-only only in specific modes: the first non-flag argument
# must be in the set (None = bare invocation, e.g. `git remote -v`).
GIT_MODAL = {
    "stash": {"list", "show"},          # bare `git stash` is a push!
    "remote": {None, "show", "get-url"},
    "worktree": {"list"},
    "submodule": {"status", "summary"},
}

# branch/tag: list-y invocations are allowed; these flags mean a write.
GIT_BRANCH_WRITE = {
    "-d", "-D", "--delete", "-m", "-M", "--move", "-c", "-C", "--copy",
    "-f", "--force", "-u", "--set-upstream-to", "--unset-upstream",
    "--edit-description", "-t", "--track",
}
GIT_TAG_WRITE = {
    "-a", "--annotate", "-s", "--sign", "-u", "--local-user", "-f",
    "--force", "-d", "--delete", "-e", "--edit", "-m", "--message",
    "-F", "--file", "--cleanup", "--trailer",
}

# branch/tag listing filters that consume the NEXT token as their value. Verified
# against git's own usage output, which spells them `--contains <commit>` — a
# detached argument — not `--contains[=<commit>]`. So in `git branch --contains
# <sha>` the sha is the filter's value, NOT a branch name to create, and the
# operand scan must skip it. Deliberately excludes the `--no-` forms git does not
# document as taking a value (--no-sort/--no-points-at/--no-format): over-skipping
# could swallow a real create operand. (Only the operand scan skips; the write-flag
# scan below still reads every token, so `--contains -D foo` still trips on -D.)
GIT_REF_LIST_VALUE_OPTS = {
    "--contains", "--no-contains", "--merged", "--no-merged",
    "--points-at", "--sort", "--format",
}

# config: allowed only with an explicit read flag (or new-style `get`/`list`
# verb) and none of the write flags/verbs.
GIT_CONFIG_READ = {
    "--get", "--get-all", "--get-regexp", "--get-urlmatch",
    "--get-color", "--get-colorbool", "--list", "-l",
}
GIT_CONFIG_WRITE = {
    "--edit", "-e", "--unset", "--unset-all", "--add", "--replace-all",
    "--rename-section", "--remove-section",
}
GIT_CONFIG_WRITE_VERBS = {  # new-style (git >= 2.46) subcommand verbs
    "set", "unset", "edit", "rename-section", "remove-section",
}
GIT_CONFIG_VALUE_OPTS = {"--file", "-f", "--blob", "--type", "-t",
                         "--default", "--comment"}

CTRL_OPS = {"|", "||", "&&", ";", "&", "\n"}

# Shell reserved words that introduce a command (loops, conditionals, timing,
# negation). They alter no state themselves, and any command they wrap still
# lands in its own `;`/`&&`/... segment and is validated against READONLY on its
# own. So we strip them from the front of each segment before the read-only
# check: `until grep -q done log; do sleep 1; done` is allowed iff every command
# it wraps (grep, sleep, ...) is independently allowed, and a body like
# `do rm x; done` still trips on `rm` and falls through to "ask".
SHELL_KEYWORDS = {
    "if", "then", "else", "elif", "fi",
    "while", "until", "do", "done", "time", "!",
}


class Unsafe(Exception):
    """Raised to short-circuit to a non-allow decision."""
    def __init__(self, decision, reason):
        self.decision = decision
        self.reason = reason


def parse_segments(cmd: str, cwd: str = ""):
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


def _fence_targets(prog: str, args: list) -> list:
    """Return the subset of args that are in *path* position (to be fenced).
    For grep/sed/awk the leading pattern/script operand is excluded, so a regex
    like `/def foo/,/^$/p` is never mistaken for an absolute path."""
    fam = ("grep" if prog in GREP_FAMILY else
           "sed" if prog in SED_FAMILY else
           "awk" if prog in AWK_FAMILY else None)
    if fam is None:
        return [a for a in args if not (a.startswith("-") and a != "-")]

    vopts = VALUE_OPTS[fam]
    # if an -e/-f expression flag is present there is no positional pattern
    pattern_taken = any(a.split("=", 1)[0] in EXPR_FLAGS[fam] for a in args)
    targets, skip_next = [], False
    for a in args:
        if skip_next:
            skip_next = False
            continue
        if a.startswith("-") and a != "-":
            if a.split("=", 1)[0] in vopts and "=" not in a:
                skip_next = True
            continue
        if not pattern_taken:
            pattern_taken = True  # the pattern/script operand — not a path
            continue
        if fam == "awk" and "=" in a:
            continue  # var=value assignment, not a path
        targets.append(a)
    return targets


def _resolve_path(word: str, cwd: str) -> str:
    """Resolve a path token the shell's way: ~ expanded, relative joined to cwd,
    ../ collapsed. (No symlink resolution — avoids touching the filesystem.)"""
    base = cwd or os.getcwd()
    word = os.path.expanduser(word)
    p = word if os.path.isabs(word) else os.path.join(base, word)
    return os.path.normpath(p)


def _under_roots(real: str) -> bool:
    if ALLOWED_ROOTS is None:
        return True
    return any(real == r or real.startswith(r + os.sep) for r in ALLOWED_ROOTS)


def _outside_roots(word: str, cwd: str) -> bool:
    if ALLOWED_ROOTS is None:
        return False
    if word.startswith("-"):
        return False  # option flag, not a path
    return not _under_roots(_resolve_path(word, cwd))


def _match_paren(s, i):
    """s[i] is just past '$('; return index of the matching ')', or -1."""
    depth, n = 1, len(s)
    in_s = in_d = False
    while i < n:
        c = s[i]
        if in_s:
            if c == "'":
                in_s = False
        elif in_d:
            if c == "\\" and i + 1 < n:
                i += 2; continue
            if c == '"':
                in_d = False
        elif c == "'":
            in_s = True
        elif c == '"':
            in_d = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def _match_arith(s, i):
    """s[i] is just past '$(('; return index just after the closing '))', or -1."""
    depth, n = 2, len(s)
    while i < n:
        if s[i] == "(":
            depth += 1
        elif s[i] == ")":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return -1


def _find_backtick_end(s, i):
    n = len(s)
    while i < n:
        if s[i] == "\\" and i + 1 < n:
            i += 2; continue
        if s[i] == "`":
            return i
        i += 1
    return -1


def resolve_substitutions(command: str, cwd: str):
    """Replace $(...) / `...` / $((...)) with placeholders, recursively requiring
    each command substitution to be a read-only 'allow'. Returns
    (stripped_command, None) on success, or ("", (decision, reason)) to abort.
    Single-quoted regions are inert (substitutions there are literal)."""
    out, i, n = [], 0, len(command)
    in_s = in_d = False
    while i < n:
        c = command[i]
        if in_s:
            out.append(c)
            if c == "'":
                in_s = False
            i += 1; continue
        active = True  # $() and ` are active outside quotes and inside "..."
        if in_d:
            if c == "\\" and i + 1 < n:
                out.append(command[i:i + 2]); i += 2; continue
            if c == '"':
                in_d = False; out.append(c); i += 1; continue
        else:
            if c == "'":
                in_s = True; out.append(c); i += 1; continue
            if c == '"':
                in_d = True; out.append(c); i += 1; continue
        if active and command[i:i + 3] == "$((":
            k = _match_arith(command, i + 3)
            if k == -1:
                return "", ("ask", "unbalanced arithmetic")
            out.append("1"); i = k; continue
        if active and c == "$" and i + 1 < n and command[i + 1] == "(":
            k = _match_paren(command, i + 2)
            if k == -1:
                return "", ("ask", "unbalanced command substitution")
            d, r = decide(command[i + 2:k], cwd)
            if d != "allow":
                return "", ("ask", "substitution not read-only: " + r)
            out.append("SUBST"); i = k + 1; continue
        if active and c == "`":
            j = _find_backtick_end(command, i + 1)
            if j == -1:
                return "", ("ask", "unbalanced backtick substitution")
            d, r = decide(command[i + 1:j], cwd)
            if d != "allow":
                return "", ("ask", "substitution not read-only: " + r)
            out.append("SUBST"); i = j + 1; continue
        out.append(c); i += 1
    return "".join(out), None


def _operands(args: list, value_opts: set) -> list:
    """Positional operands of a git subcommand: non-flag tokens, skipping the
    values consumed by detached `--opt <value>` options. `--opt=<value>` needs no
    skip (the value rides in the same token)."""
    ops, skip = [], False
    for a in args:
        if skip:
            skip = False
            continue
        if a.startswith("-") and a != "-":
            if a in value_opts:
                skip = True
            continue
        ops.append(a)
    return ops


def _git_gate(args: list, cwd: str):
    """Decide whether one `git <args>` segment is provably read-only.
    Returns None to allow, or a reason string (-> ask). Path arguments in
    plain positional position are NOT checked here — the generic directory
    fence in decide() already covers them; this handles what the fence
    can't see (global-option values, --flag=/abs/path) plus subcommand modes."""
    i, n = 0, len(args)
    while i < n and args[i].startswith("-"):  # global options
        a = args[i]
        if a in GIT_GLOBAL_OK:
            i += 1; continue
        if a in ("-C", "--git-dir", "--work-tree") and i + 1 < n:
            if _outside_roots(args[i + 1], cwd):
                return "git %s path outside allowed roots: %s" % (a, args[i + 1])
            i += 2; continue
        if a.startswith("--git-dir=") or a.startswith("--work-tree="):
            v = a.split("=", 1)[1]
            if _outside_roots(v, cwd):
                return "git path outside allowed roots: " + v
            i += 1; continue
        return "git global option not auto-allowed: " + a
    if i >= n:
        return "bare git"
    sub, rest = args[i], args[i + 1:]

    # guards that apply to every subcommand
    for a in rest:
        if a.startswith("--output"):  # --output / --output-directory write files
            return "git --output writes a file"
        if a.startswith("-") and "=" in a:  # fence --flag=/abs/path values,
            v = a.split("=", 1)[1]          # which the generic fence skips
            if v[:1] in ("/", "~") and _outside_roots(v, cwd):
                return "git option path outside allowed roots: " + v

    if sub in GIT_READONLY:
        if sub == "grep":
            for a in rest:
                if a.startswith("-O") or a.startswith("--open-files-in-pager"):
                    return "git grep -O launches a program"
        return None

    mode = next((a for a in rest if not a.startswith("-")), None)

    if sub in GIT_MODAL:
        if mode in GIT_MODAL[sub]:
            return None
        return "git %s %s is not read-only" % (sub, mode or "(bare)")

    if sub == "reflog":  # read-only except the pruning verbs
        if mode in ("expire", "delete"):
            return "git reflog %s rewrites reflogs" % mode
        return None

    if sub in ("branch", "tag"):
        write = GIT_BRANCH_WRITE if sub == "branch" else GIT_TAG_WRITE
        for a in rest:  # scans every token, no value-skipping: conservative
            if a.split("=", 1)[0] in write:
                return "git %s write flag: %s" % (sub, a)
        # a leftover positional means create/rename/delete — unless forced into
        # list mode, where it is just a match pattern
        listish = any(a == "-l" or a.startswith("--list")
                      or (sub == "tag" and re.match(r"-n\d*$", a))
                      for a in rest)
        ops = _operands(rest, GIT_REF_LIST_VALUE_OPTS)
        if ops and not listish:
            return "git %s with operand %r: possible create/modify" % (sub, ops[0])
        return None

    if sub == "config":
        for a in rest:
            if a.split("=", 1)[0] in GIT_CONFIG_WRITE:
                return "git config write flag: " + a
        ops = _operands(rest, GIT_CONFIG_VALUE_OPTS)
        if ops and ops[0] in GIT_CONFIG_WRITE_VERBS:
            return "git config %s writes config" % ops[0]
        if ops[:1] in (["get"], ["list"]) or \
                any(a.split("=", 1)[0] in GIT_CONFIG_READ for a in rest):
            return None
        if len(ops) == 1:
            # `git config <key>` reads, `git config <key> <value>` writes — telling
            # them apart means trusting an operand count, and a miscount silently
            # WRITES config. Don't prove it; bounce it to the agent, which has an
            # exactly-equivalent provable spelling (`--get`). DENY not ask: this is
            # a fix-your-command case, not a human-judgment one. Real writes (two
            # operands, or a write flag/verb) still route to the human above.
            raise Unsafe("deny", "`git config %s` is ambiguous to the policy (read vs "
                                 "write depends on operand count) — to READ it, use "
                                 "`git config --get %s`, which is unambiguous and "
                                 "auto-allowed" % (ops[0], ops[0]))
        return "git config without a read-only flag"

    return "git subcommand not on read-only allowlist: " + sub


def decide(command: str, cwd: str = ""):
    """Return (decision, reason) for a raw Bash command string."""
    command = command.strip()
    if not command:
        return "ask", "empty command"

    if ALLOW_READONLY_SUBST and ("$(" in command or "`" in command):
        stripped, aborted = resolve_substitutions(command, cwd)
        if aborted:
            return aborted
        command = stripped

    segments = parse_segments(command, cwd)  # may raise Unsafe
    if not segments:
        return "ask", "no command"

    # normalize segments: drop leading `VAR=val` assignments and leading shell
    # reserved words (until/while/do/done/if/then/... and !/time), so the real
    # command each construct wraps is what gets checked. Keep non-empty ones,
    # remembering whether env assignments preceded the command (git cares).
    norm = []
    for seg in segments:
        w = list(seg)
        had_assign = False
        while w and (re.match(r"^[A-Za-z_][A-Za-z0-9_]*=", w[0])
                     or w[0] in SHELL_KEYWORDS):
            if "=" in w[0]:
                had_assign = True
            w.pop(0)
        if w:
            norm.append((w, had_assign))
    if not norm:
        return "ask", "no command"

    # `cd` is allowed ONLY standalone. On its own it just moves the shell, and the
    # next command's hook cwd reflects the move (verified), so the fence catches
    # any out-of-root access then. Chained into a compound, permit.py sees only the
    # pre-cd cwd and can't tell — so refuse, forcing cds to stand alone.
    if any(os.path.basename(w[0]) in ("cd", "pushd", "popd") for w, _ in norm):
        if len(norm) == 1:
            return "allow", "standalone cd"
        # DENY (not ask) so the reason routes back to the agent to reformulate,
        # instead of surfacing as a user prompt. This is a fix-your-command case:
        # the agent should split it, not the human approve it.
        return "deny", ("chained cd is not allowed — send the cd as its own separate "
                        "command (or omit it: the shell already starts in the project "
                        "root), then send the rest as a second command")

    # If the shell is parked outside the roots (only reachable via a prior
    # standalone cd), refuse: relative and implicit-cwd (e.g. bare `ls`) reads
    # would land there. This closes the deferred-catch gap.
    if not _under_roots(_resolve_path(".", cwd)):
        return "ask", "shell cwd outside allowed roots: " + (cwd or os.getcwd())

    for w, had_assign in norm:
        prog = os.path.basename(w[0])
        if prog == "git":
            if had_assign:
                return "ask", "env assignment before git (GIT_* vars can run programs)"
            reason = _git_gate(w[1:], cwd)
            if reason is not None:
                return "ask", reason
        elif prog not in READONLY:
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

        # directory fence: every *path* argument must resolve inside roots
        for t in _fence_targets(prog, w[1:]):
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
