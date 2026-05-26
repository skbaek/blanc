---
name: lean-prover
description: Actively writes, finishes, or repairs Lean 4 proofs, lemmas, and tactics. Use whenever the user asks to "prove", "finish", "solve", or "fill in" a lemma or a `sorry`.
---
# Lean 4 Interactive Prover

## When to use this skill
- When requested to complete or author a Lean 4 proof.
- When tasked with eliminating a `sorry` by finding a valid tactic sequence.

## The Read-Think-Write-Look Workflow
You must strictly follow this closed feedback loop for every single tactic step. Do not batch multiple speculative lines together.

1. **Read (Locate and Inspect):**
   - Open the target `.lean` file. Locate the `sorry` or line position requested.
   - Run the `lean_goal` MCP tool at that precise line and character position. Read the exact hypotheses and target goal.

2. **Think (Plan the Next Tactic):**
   - Formulate exactly *one* logical tactic step (e.g., `intro h`, `induction n`, `rw [my_lemma]`) based on the active goal state.
   - Cross-reference `.agents/skills/lean-prover/resources/proof-checklist.md` to ensure your tactic choice aligns with mathlib4 conventions.

3. **Write (Apply Change):**
   - Modify the `.lean` file. Replace the target `sorry` (or append to the block) with your single chosen tactic.
   - Ensure you leave a trailing newline or valid spacing so the Lean LSP can parse it cleanly.

4. **Look (Observe & Course-Correct):**
   - **Do not assume success.** Immediately run the `lean_goal` (and if necessary, `lean_diagnostics`) MCP tool at the character position *immediately following* your new tactic line.
   - Evaluate the return value:
     - **Case A (Success / Progress):** If the goals change or simplify, update your mental state and loop back to Step 2 for the remaining goals.
     - **Case B (Proof Complete):** If the tool returns an empty goal list ("No goals"), the proof is closed. Proceed to Step 5.
     - **Case C (Error / Backtrack):** If the tool returns a compile error or an unfavorable goal state, undo your last file modification immediately. Treat it as a failed branch, think of an alternative tactic, and retry Step 3.

5. **Finalize:**
   - Once all goals are closed cleanly according to the language server, declare success to the user and present the final sequence of tactics used.