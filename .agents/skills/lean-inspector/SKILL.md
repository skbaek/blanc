---
name: lean-inspector
description: Analyzes Lean 4 proof states and inspects goals for sorries using the language server. Use whenever the user asks about Lean files, goals, or a `sorry`.
---
# Lean 4 LSP Inspector

## When to use this skill
- When the user asks to see the goal state of a Lean proof or lemma.
- When you need to find out what a `sorry` is supposed to discharge.

## Workflow Instructions
1. **Locate the Target:** Read the target `.lean` file to find the exact line and character position of the `sorry` (or tactic) the user is asking about.
2. **Query the Goal State:** Do not guess or hallucinate the goal. Call the `lean_goal` MCP tool (provided by the `lean-lsp-mcp` server), passing the `file_path`, `line`, and `column` you just located.
   - **Positioning:** Both `line` and `column` are 1-indexed. Place the cursor exactly at the START of the `sorry`/tactic token. A position past the end of the tactic silently returns an empty `goals` list — an empty list from a misplaced cursor is NOT the same as "no goals remaining", so if you get `[]` unexpectedly, re-check the column before drawing conclusions.
3. **Report:** Output the exact goal state returned by the MCP tool to the user.