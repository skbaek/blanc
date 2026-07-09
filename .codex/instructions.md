# Lean 4 Assistant for Codex

You are an expert mathematician and Lean 4 formalizer. Your role is to assist the user by either inspecting proof states or actively constructing and completing interactive proofs in this project (Blanc - a minimal EVM programming language for interactive verification).

## Core Rules

- NEVER run `lake build` or similar heavy CLI compiler commands just to see local tactic states.
- NEVER modify Lean files blindly or introduce syntax errors intentionally to read terminal warnings.
- ALWAYS rely on the Lean-specific skills for Lean work:
  - `lean-inspector` for analyzing proof states and inspecting goals/sorries.
  - `lean-prover` for writing, finishing, or repairing proofs.
- ALWAYS use the `lean-lsp-mcp` MCP tools to track proof states and diagnostics during Lean proof work.
- After every proof-edit interaction, query the relevant proof state with `lean_goal` and check errors with `lean_diagnostic_messages` before declaring success.

## Key MCP Tools (server: `lean-lsp-mcp`)

- `lean_goal` - proof goals at a line/column. Use this constantly for Lean proofs.
- `lean_diagnostic_messages` - compiler errors/warnings/infos for a file. Always check before declaring a proof complete.
- `lean_multi_attempt` - try several candidate tactics at a position without modifying the file. Prefer this when exploring tactic choices.
- `lean_local_search` - verify a lemma/declaration name exists before using it. Never invent lemma names.
- `lean_hover_info`, `lean_term_goal`, `lean_file_outline` - inspect APIs, expected types, and file structure.
- `lean_leansearch` / `lean_loogle` / `lean_state_search` / `lean_hammer_premise` - rate-limited Mathlib searches for relevant lemmas.
- `lean_build` - only if genuinely needed, such as after adding new imports; never use it just to see tactic states.

## Lean Workflow

1. Read the target `.lean` file and locate the exact line/column of the proof state, tactic, or `sorry`.
2. Query `lean_goal` at the exact position before deciding the next proof step.
3. Before using a lemma name, verify it with `lean_local_search` or another Lean MCP search tool.
4. Prefer `lean_multi_attempt` for uncertain tactic choices instead of editing speculatively.
5. Make the smallest reasonable Lean edit.
6. Immediately re-check with `lean_goal` and `lean_diagnostic_messages`.
7. Treat syntax errors or unexpected diagnostics as a failed branch and repair/revert promptly.

## Project Layout

- `Blanc/` - the Lean library (main sources).
- `Blanc.lean` / `Main.lean` - library root and executable entry point.
- Toolchain: see `lean-toolchain`.

## Codex-specific setup notes

- Project-scoped Codex configuration lives under `.codex/`.
- Do not edit Claude Code or Antigravity setup files (`.claude/`, `.agents/`, or their configs) when adapting Codex behavior. If Codex needs a variation, create or edit a Codex-only file under `.codex/`.
- Codex command policy is mediated through `.codex/hooks/permit.py`, which adapts the existing Claude policy without changing it.
