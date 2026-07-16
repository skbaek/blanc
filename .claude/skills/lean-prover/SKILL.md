---
name: lean-prover
description: Actively writes, finishes, or repairs Lean 4 proofs, lemmas, and tactics. Use whenever the user asks to "prove", "finish", "solve", or "fill in" a lemma or a `sorry`.
---
# Lean 4 Interactive Prover

## When to use this skill
- When requested to complete or author a Lean 4 proof.
- When tasked with eliminating a `sorry` by finding a valid tactic sequence.

All Lean tools below come from the `lean-lsp-mcp` MCP server (full names are prefixed `mcp__lean-lsp-mcp__`, e.g. `mcp__lean-lsp-mcp__lean_goal`).

**Cursor positioning for `lean_goal`:** Both `line` and `column` are 1-indexed. Query at the START of a token to see the goal state before it executes. A position past the end of a tactic silently returns an empty `goals` list — never interpret an empty list as proof completion without confirming via `lean_diagnostic_messages` and a correctly placed cursor.

## The Read-Think-Write-Look Workflow
You must strictly follow this closed feedback loop for every single tactic step. Do not batch multiple speculative lines together.

1. **Read (Locate and Inspect):**
   - Open the target `.lean` file. Locate the `sorry` or line position requested.
   - Run the `lean_goal` tool at that precise line and character position. Read the exact hypotheses and target goal.

2. **Think (Plan the Next Tactic):**
   - Formulate exactly *one* logical tactic step (e.g., `intro h`, `induction n`, `rw [my_lemma]`) based on the active goal state.
   - Cross-reference `.claude/skills/lean-prover/resources/proof-checklist.md` to ensure your tactic choice aligns with mathlib4 conventions.
   - Before using any lemma name, verify it exists with `lean_local_search` (or `lean_loogle` / `lean_leansearch` for Mathlib discovery). Never invent lemma names.
   - When unsure between candidate tactics, use `lean_multi_attempt` to test several at once WITHOUT modifying the file, and pick the best resulting goal state.

3. **Write (Apply Change):**
   - Modify the `.lean` file. Replace the target `sorry` (or append to the block) with your single chosen tactic.
   - Ensure you leave a trailing newline or valid spacing so the Lean LSP can parse it cleanly.

4. **Look (Observe & Course-Correct):**
   - **Do not assume success.** Immediately run the `lean_goal` tool at the character position *immediately following* your new tactic line.
   - **CRITICAL:** Before evaluating the goals, you must ensure the file is free of severe compilation errors. If a tactic causes a syntax error, Lean may falsely report "No goals".
   - Evaluate the return value using this strict priority queue:
     - **Case A (Error / Backtrack):** If the tool returns a compile error, or if you notice new errors in `lean_diagnostic_messages`, or if the goal state is unfavorable, **undo your last file modification immediately**. Treat it as a failed branch, think of an alternative tactic, and retry Step 3.
     - **Case B (Progress):** If the goals change, simplify, or branch cleanly without errors, update your mental state and loop back to Step 2 for the remaining goals.
     - **Case C (Proof Complete?):** If the tool returns an empty goal list ("No goals"), **you must double-check**. Run the `lean_diagnostic_messages` tool on the file.
       - If `lean_diagnostic_messages` returns *any* errors (errors, not warnings) anywhere in the current proof block, treat this as **Case A (Error / Backtrack)**. Undo the change.
       - If `lean_diagnostic_messages` is completely clean of errors for this proof, only then proceed to Step 5.

5. **Finalize:**
   - Once all goals are closed cleanly AND `lean_diagnostic_messages` confirms there are zero compilation errors in the proof block, declare success to the user and present the final sequence of tactics used.
